//! A lightweight library for writing parsers that work on token streams.
//!
//! # Example
//!
//! ```
//! use logos::Logos;
//! use hinku::{
//!     BufferedStream,
//!     Either,
//!     ParseError,
//!     ParseResult,
//!     ParseResultExt,
//!     TokenStream,
//!     TokenStreamExt,
//! };
//!
//! #[derive(Logos, Debug, Clone, PartialEq)]
//! enum Token {
//!     #[token("foo")]
//!     Foo,
//!
//!     #[token("bar")]
//!     Bar,
//!
//!     #[error]
//!     #[regex(r"[ \n\r\f\t]+", logos::skip)]
//!     Error,
//! }
//!
//! /// A function that either consumes a Foo token or returns an error.
//! fn foo(stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
//!     match stream.advance() {
//!         None => Err(ParseError::EndOfStream),
//!         Some((Token::Foo, _)) => Ok(Token::Foo),
//!         Some((other, span)) => Err(ParseError::custom(span, "expected a foo".into())),
//!     }
//! }
//!
//! /// A function that either consumes a Bar token or returns an error.
//! fn bar(stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
//!     match stream.advance() {
//!         None => Err(ParseError::EndOfStream),
//!         Some((Token::Bar, _)) => Ok(Token::Bar),
//!         Some((other, span)) => Err(ParseError::custom(span, "expected a bar".into())),
//!     }
//! }
//!
//! /// A function that consumes either one of the tokens.
//! fn foo_or_bar(mut stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
//!     stream.either(foo, bar)
//!         .map(Either::merge)
//!         .expected("expected either a foo or a bar")
//! }
//!
//! /// A function that expects a Foo token, followed by a Bar token.
//! fn foobar(mut stream: &mut dyn TokenStream<Token>) -> ParseResult<(Token, Token), String> {
//!     let f = stream.take(foo)?;
//!     let b = stream.take(bar)?;
//!
//!     Ok((f, b))
//! }
//!
//! let lex = Token::lexer("foo bar bar foo bar");
//! let mut stream = BufferedStream::new(lex.spanned());
//!
//! assert_eq!(stream.take(foo), Ok(Token::Foo));
//! assert_eq!(stream.take(bar), Ok(Token::Bar));
//! assert_eq!(stream.take(foo_or_bar), Ok(Token::Bar));
//! assert_eq!(stream.take(foobar), Ok((Token::Foo, Token::Bar)));
//! ```

mod buffered_stream;
pub use buffered_stream::BufferedStream;

pub type Span = std::ops::Range<usize>;

/// Token stream with backtracking support.
pub trait TokenStream<T> {
    /// Returns the token and it's span from the current position in the token stream.
    fn advance(&mut self) -> Option<(T, Span)>;

    /// Backtracks `n` tokens in the stream.
    fn backtrack(&mut self, n: usize);

    /// Mark the tokens before the current position in the stream as unneeded.
    /// The stream cannot be backtracked past this in the future.
    fn commit(&mut self);
}

/// Represents a parsing error.
#[derive(Debug, PartialEq)]
pub enum ParseError<E> {
    /// The end of the stream was reached unexpectedly.
    EndOfStream,

    /// An unexpected token was encountered.
    UnexpectedToken {
        /// Span of the unexpected token.
        span: Span,
    },

    /// An user-defined error occurred.
    Custom {
        /// Part of the input that caused the error.
        span: Span,

        /// List of error context. The first element is "deeper"
        /// into the parser and the last more "general."
        error: Vec<E>,
    },
}

impl<E> ParseError<E> {
    /// A convinience function for creating a [ParseError::Custom] variant.
    pub fn custom(span: Span, error: E) -> ParseError<E> {
        ParseError::Custom {
            span,
            error: vec![error],
        }
    }
}

/// A [TokenStream] that keeps track of the span advanced while parsing.
pub struct SpanningStream<'a, S> {
    parent: &'a mut S,
    span: Option<Span>,
}

impl<'a, S> SpanningStream<'a, S> {
    /// Create a new [SpanningStream] by wrapping a mutable reference to a parent TokenStream.
    pub fn new(parent: &'a mut S) ->  SpanningStream<'a, S> {
        SpanningStream {
            parent,
            span: None,
        }
    }

    /// Return the part of the input parsed since creating the [SpanningStream].
    pub fn span(self) -> Option<Span> {
        self.span
    }
}

impl<'a, S, T> TokenStream<T> for SpanningStream<'a, S>
where
    S: TokenStream<T>,
{
    fn advance(&mut self) -> Option<(T, Span)> {
        match self.parent.advance() {
            None => None,
            Some((token, span)) => {
                if let Some(ref mut self_span) = self.span {
                    self_span.end = span.end;
                } else {
                    self.span = Some(span.clone());
                }

                Some((token, span))
            },
        }
    }

    fn backtrack(&mut self, n: usize) {
        self.parent.backtrack(n)
    }

    fn commit(&mut self) {
        self.parent.commit()
    }
}

pub type ParseResult<R,E> = Result<R, ParseError<E>>;

impl<T,S> TokenStreamExt<T> for S where S: TokenStream<T> {}

pub enum Either<L,R> {
    Left(L),
    Right(R),
}

impl<T> Either<T,T> {
    pub fn merge(self) -> T {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => r,
        }
    }
}

pub trait TokenStreamExt<T>: TokenStream<T> + Sized {
    fn take<P,R,E>(&mut self, parser: P) -> ParseResult<R,E>
    where
        P: Fn(&mut dyn TokenStream<T>) -> ParseResult<R,E>,
    {
        let mut fork = self.fork();

        let result = parser(&mut fork);

        if result.is_ok() {
            fork.commit();
        }

        result
    }

    fn assert_token(&mut self, token: T) -> ParseResult<(), String> where T: PartialEq<T> {
        match self.advance() {
            Some((t, _)) if t == token => Ok(()),
            Some((_, span)) => Err(ParseError::UnexpectedToken { span }),
            None => Err(ParseError::EndOfStream),
        }
    }

    fn fork(&mut self) -> TokenStreamFork<T> {
        println!("Fork!");
        TokenStreamFork {
            parent: self,
            ahead: 0,
        }
    }

    fn either<P1, P2, R1, R2>(&mut self, parser1: P1, parser2: P2) -> ParseResult<Either<R1,R2>, String>
    where
        P1: Fn(&mut dyn TokenStream<T>) -> ParseResult<R1,String>,
        P2: Fn(&mut dyn TokenStream<T>) -> ParseResult<R2,String>,
    {
        let mut spanning = SpanningStream::new(self);

        if let Some(res) = spanning.take(parser1).optional() {
            return Ok(Either::Left(res));
        } else if let Some(res) = spanning.take(parser2).optional() {
            return Ok(Either::Right(res));
        } else {
            let span = spanning.span();

            Err(ParseError::UnexpectedToken {
                span: span.unwrap_or(0..0),
            })
        }
    }
}

impl<'a, T> TokenStream<T> for &mut dyn TokenStream<T> {
    fn advance(&mut self) -> Option<(T, Span)> {
        (*self).advance()
    }

    fn backtrack(&mut self, n: usize) {
        (*self).backtrack(n)
    }

    fn commit(&mut self) {
        (*self).commit()
    }
}

/// Fork of a token stream.
///
/// Any tokens consumed after the latest [commit](TokenStream::commit) are backtracked when the
/// fork is dropped.
pub struct TokenStreamFork<'a, T> {
    parent: &'a mut dyn TokenStream<T>,
    ahead: usize,
}

impl<'a, T> TokenStream<T> for TokenStreamFork<'a, T> {
    fn advance(&mut self) -> Option<(T, Span)> {
        match self.parent.advance() {
            None => None,
            Some(t) => {
                self.ahead += 1;
                Some(t)
            }
        }
    }

    fn backtrack(&mut self, n: usize) {
        if n > self.ahead {
            panic!();
        }

        self.ahead -= n;
        self.parent.backtrack(n);
    }

    fn commit(&mut self) {
        self.ahead = 0;
        self.parent.commit();
    }
}

impl<'a, T> Drop for TokenStreamFork<'a, T> {
    fn drop(&mut self) {
        self.parent.backtrack(self.ahead);
        // self.parent.commit();
    }
}

/// Implements convinience methods related to error handling for [ParseResult].
pub trait ParseResultExt<T,E>: Sized {
    /// Appends error context to the error if the [ParseResult] represents an error.
    fn expected<C>(self, context: C) -> ParseResult<T,E> where E: From<C>;

    /// Transmutes the type into an [Option], dismissing any possible errors.
    fn optional(self) -> Option<T>;
}

impl<T,E> ParseResultExt<T,E> for ParseResult<T,E> {
    fn expected<C>(self, context: C) -> ParseResult<T,E> where E: From<C> {
        match self {
            Ok(t) => Ok(t),
            Err(ParseError::EndOfStream) => Err(ParseError::EndOfStream),
            Err(ParseError::UnexpectedToken { span }) => {
                Err(ParseError::Custom { span, error: vec![context.into()] })
            },
            Err(ParseError::Custom { span, mut error }) => {
                error.push(context.into());
                Err(ParseError::Custom { span, error })
            }
        }
    }

    fn optional(self) -> Option<T> {
        self.ok()
    }
}

#[cfg(all(test, feature = "logos"))]
mod tests {
    use super::{
        BufferedStream,
        Either,
        ParseError,
        ParseResult,
        ParseResultExt,
        Span,
        TokenStream,
        TokenStreamExt,
    };
    use logos::{Logos, Lexer};

    #[derive(Debug, Clone, PartialEq)]
    enum Modifier {
        Indirect,
        Immediate,
    }

    fn modifier_callback(lex: &mut Lexer<Token>) -> Result<Modifier> {
        match lex.slice() {
            "@" => Ok(Modifier::Indirect),
            "=" => Ok(Modifier::Immediate),
            _ => Err(ParseError::EndOfStream),
        }
    }

    #[derive(Logos, Clone, Debug, PartialEq)]
    enum Token {
        #[error]
        #[regex(r"[ \t\r\f\n]+", logos::skip)]
        Error,

        #[regex("=|@", modifier_callback)]
        Modifier(Modifier),

        #[regex("[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())] Symbol(String),

        #[regex("[0-9]+", |lex| lex.slice().parse())]
        Number(i32),

        #[token("(")]
        IndexBegin,

        #[token(")")]
        IndexEnd,
    }

    #[derive(Debug)]
    enum Mode {
        Immediate,
        Direct,
        Indirect,
    }

    #[derive(Debug)]
    enum Value {
        Symbol(String),
        Number(i32),
    }

    #[derive(Debug)]
    struct Operand {
        mode: Mode,
        value: Value,
        index: Option<i32>,
    }

    type Result<T> = ParseResult<T, String>;

    fn symbol(stream: &mut dyn TokenStream<Token>) -> Result<String> {
        match stream.advance() {
            Some((Token::Symbol(sym), _span)) => Ok(sym),
            Some((_other, span)) => Err(ParseError::custom(span, "expected a symbol".into())),
            None => Err(ParseError::EndOfStream),
        }
    }

    fn number(stream: &mut dyn TokenStream<Token>) -> Result<i32> {
        match stream.advance() {
            Some((Token::Number(num), _span)) => Ok(num),
            Some((_other, span)) => Err(ParseError::custom(span, "expected a number".into())),
            None => Err(ParseError::EndOfStream),
        }
    }

    fn modifier(stream: &mut dyn TokenStream<Token>) -> Result<Mode> {
        match stream.advance() {
            Some((Token::Modifier(Modifier::Indirect), _span)) => Ok(Mode::Indirect),
            Some((Token::Modifier(Modifier::Immediate), _span)) => Ok(Mode::Immediate),
            Some((other, span)) => {
                let msg = format!("expected a modifier (= or @), got: {:?}", other);
                Err(ParseError::custom(span, msg))
            },
            None => Err(ParseError::EndOfStream),
        }
    }

    fn value(mut stream: &mut dyn TokenStream<Token>) -> Result<Value> {
        let res = stream.either(symbol, number).expected("expected a symbol or a number")?;

        match res {
            Either::Left(sym) => Ok(Value::Symbol(sym)),
            Either::Right(num) => Ok(Value::Number(num)),
        }
    }

    fn index_register(mut stream: &mut dyn TokenStream<Token>) -> Result<Option<i32>> {
        println!("Assert IndexBegin");
        if stream.assert_token(Token::IndexBegin).optional().is_some() {
            println!("Index Begin");
            stream.commit();
            let index = stream.take(number)?;
            stream.assert_token(Token::IndexEnd).expected("expected a closing parenthesis")?;

            return Ok(Some(index));
        }

        Ok(None)
    }

    fn operand(mut stream: &mut dyn TokenStream<Token>) -> Result<Operand> {
        let mode = stream.take(modifier)
            .optional()
            .unwrap_or(Mode::Direct);

        let value = stream.take(value)
            .expected("invalid base operand")?;

        let index = stream.take(index_register)
            .expected("errorneous index register notation")?;

        Ok(Operand {
            mode,
            value,
            index,
        })
    }

    fn calculate_position(input: &str, span: &Span) -> (usize, usize) {
        input[..span.start].lines()
            .fold((0, 0), |(line_nr, _column), line| {
                (line_nr + 1, line.len())
            })
    }

    #[test]
    fn it_works() {
        let input = r#"
            @symbol(10)
            symbol(12=34)
        "#;

        let lex = Token::lexer(&input);
        let mut stream = BufferedStream::new(lex.spanned());

        let err;

        loop {
            match stream.take(operand) {
                Ok(op) => println!("Operand: {:?}", op),
                Err(e) => {
                    err = Some(e);
                    break;
                }
            }
        }


        if let Some(ParseError::Custom { span, mut error }) = err {
            println!("{:?}", input.lines().collect::<Vec<_>>());

            let (line_nr, column) = calculate_position(input, &span);
            let line_orig = input.lines().skip(line_nr-1).next().unwrap();

            let line = line_orig.trim();

            let prefix = format!("Line {}: Error: ", line_nr);

            println!("{}{}", prefix, line);

            for _ in 0..column + prefix.len() - line_orig.len() + line.len() {
                print!(" ");
            }

            for _ in 0..span.end - span.start {
                print!("^");
            }

            error.reverse();

            println!(" {}", error.join(": "));
        }
    }
}
