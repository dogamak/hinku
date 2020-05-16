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
//!         Some((other, span)) => Err(ParseError::other(span, "expected a foo")),
//!     }
//! }
//!
//! /// A function that either consumes a Bar token or returns an error.
//! fn bar(stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
//!     match stream.advance() {
//!         None => Err(ParseError::EndOfStream),
//!         Some((Token::Bar, _)) => Ok(Token::Bar),
//!         Some((other, span)) => Err(ParseError::other(span, "expected a bar")),
//!     }
//! }
//!
//! /// A function that consumes either one of the tokens.
//! fn foo_or_bar(mut stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
//!     stream.either(foo, bar)
//!         .map(Either::merge)
//!         .context("expected either a foo or a bar")
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

mod error;
mod buffered_stream;

pub use error::{ParseResult, ParseError, ParseResultExt};
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

#[macro_export]
macro_rules! match_token {
    ($stream:expr, { $( $token:pat => $arm:expr ),* $(,)* }) => {
        match $stream.advance() {
            None => Err($crate::ParseError::EndOfStream),
            $( Some(($token, _span)) => $arm, )*
            Some((_token, span)) => Err($crate::ParseError::new(span)),
        }
    };
}

/// A [TokenStream] that keeps track of the span advanced while parsing.
pub struct SpanningStream<'a, S> {
    parent: &'a mut S,
    span: Option<Span>,
}

impl<'a, S> SpanningStream<'a, S> {
    /// Create a new [SpanningStream] by wrapping a mutable reference to a parent TokenStream.
    pub fn new(parent: &'a mut S) -> SpanningStream<'a, S> {
        SpanningStream { parent, span: None }
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
            }
        }
    }

    fn backtrack(&mut self, n: usize) {
        self.parent.backtrack(n)
    }

    fn commit(&mut self) {
        self.parent.commit()
    }
}

impl<T, S> TokenStreamExt<T> for S where S: TokenStream<T> {}

pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<T> Either<T, T> {
    pub fn merge(self) -> T {
        match self {
            Either::Left(l) => l,
            Either::Right(r) => r,
        }
    }
}

pub fn either<T, P1, P2, R1, R2>(
    parser1: P1,
    parser2: P2,
) -> impl FnOnce(&mut dyn TokenStream<T>) -> ParseResult<Either<R1, R2>, String>
where
    P1: FnOnce(&mut dyn TokenStream<T>) -> ParseResult<R1, String>,
    P2: FnOnce(&mut dyn TokenStream<T>) -> ParseResult<R2, String>,
{
    move |mut stream: &mut dyn TokenStream<T>| {
        let mut spanning = SpanningStream::new(&mut stream);

        let error;

        match spanning.take(parser1) {
            Ok(res) => return Ok(Either::Left(res)),
            Err(_err) => (),
        }

        match spanning.take(parser2) {
            Ok(res) => return Ok(Either::Right(res)),
            Err(err) => error = err,
        }

        Err(error)
    }
}

pub trait TokenStreamExt<T>: TokenStream<T> + Sized {
    fn take<P, R, E>(&mut self, parser: P) -> ParseResult<R, E>
    where
        P: FnOnce(&mut dyn TokenStream<T>) -> ParseResult<R, E>,
    {
        let mut fork = self.fork();

        let result = parser(&mut fork);

        if result.is_ok() {
            fork.commit();
        }

        result
    }

    fn assert_token(&mut self, token: T) -> ParseResult<(), String>
    where
        T: PartialEq<T>,
    {
        let err = match self.advance() {
            Some((t, _)) if t == token => {
                self.commit();
                return Ok(());
            }
            Some((_, span)) => {
                self.backtrack(1);
                ParseError::new(span)
            }
            None => ParseError::EndOfStream,
        };

        Err(err)
    }

    fn fork(&mut self) -> TokenStreamFork<T> {
        TokenStreamFork {
            parent: self,
            ahead: 0,
        }
    }

    fn either<P1, P2, R1, R2>(
        &mut self,
        parser1: P1,
        parser2: P2,
    ) -> ParseResult<Either<R1, R2>, String>
    where
        P1: Fn(&mut dyn TokenStream<T>) -> ParseResult<R1, String>,
        P2: Fn(&mut dyn TokenStream<T>) -> ParseResult<R2, String>,
    {
        self.take(either(parser1, parser2))
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

#[cfg(test)]
mod tests {
    use super::{
        BufferedStream, Either, ParseError, ParseResult, ParseResultExt, Span, TokenStream,
        TokenStreamExt,
    };
    use logos::{Lexer, Logos};

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

        #[regex("[A-Za-z_][A-Za-z0-9_]*", |lex| lex.slice().to_string())]
        Symbol(String),

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
        match_token!(stream, {
            Token::Symbol(sym) => Ok(sym),
        })
        .context("expected a symbol")
    }

    fn number(stream: &mut dyn TokenStream<Token>) -> Result<i32> {
        match_token!(stream, {
            Token::Number(num) => Ok(num),
        })
        .context("expected a number")
    }

    fn modifier(stream: &mut dyn TokenStream<Token>) -> Result<Mode> {
        match_token!(stream, {
            Token::Modifier(Modifier::Indirect) => Ok(Mode::Indirect),
            Token::Modifier(Modifier::Immediate) => Ok(Mode::Immediate),
        })
        .context("expected a modifier (= or @)")
    }

    fn value(mut stream: &mut dyn TokenStream<Token>) -> Result<Value> {
        let res = stream
            .either(symbol, number)
            .context("expected a symbol or a number")?;

        match res {
            Either::Left(sym) => Ok(Value::Symbol(sym)),
            Either::Right(num) => Ok(Value::Number(num)),
        }
    }

    fn index_register(mut stream: &mut dyn TokenStream<Token>) -> Result<Option<i32>> {
        if stream.assert_token(Token::IndexBegin).optional().is_some() {
            stream.commit();
            let index = stream.take(number)?;
            stream
                .assert_token(Token::IndexEnd)
                .context("expected a closing parenthesis")?;

            return Ok(Some(index));
        }

        Ok(None)
    }

    fn operand(mut stream: &mut dyn TokenStream<Token>) -> Result<Operand> {
        let mode = stream.take(modifier).optional().unwrap_or(Mode::Direct);

        let value = stream.take(value).context("invalid base operand")?;

        let index = stream
            .take(index_register)
            .context("errorneous index register notation")?;

        Ok(Operand { mode, value, index })
    }

    fn calculate_position(input: &str, span: &Span) -> (usize, usize) {
        input[..span.start]
            .lines()
            .fold((0, 0), |(line_nr, _column), line| (line_nr + 1, line.len()))
    }

    #[test]
    fn it_works() {
        let input = r#"
            @symbol(10)
            123(321)
            =ARR(0)
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

        if let Some(ParseError::Other { span, mut context }) = err {
            let (line_nr, column) = calculate_position(input, &span);
            let line_orig = input.lines().skip(line_nr - 1).next().unwrap();

            let line = line_orig.trim();

            let prefix = format!("Line {}: Error: ", line_nr);

            println!("{}{}", prefix, line);

            for _ in 0..column + prefix.len() - line_orig.len() + line.len() {
                print!(" ");
            }

            for _ in 0..span.end - span.start {
                print!("^");
            }

            context.reverse();

            println!(" {}", context.join(": "));
        }
    }
}
