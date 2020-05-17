use crate::Span;
use std::fmt;

/// Represents a parsing error.
#[derive(Debug, PartialEq, Clone)]
pub enum ErrorKind<E> {
    /// The end of the stream was reached unexpectedly.
    EndOfStream,

    UnexpectedToken {
        token: Option<String>,
    },

    /// An user-defined error occurred.
    Other(E),
}

impl<E> fmt::Display for ErrorKind<E> where E: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::EndOfStream => write!(f, "unexpected end of stream"),
            ErrorKind::UnexpectedToken { token: None } => write!(f, "unexpected token"),
            ErrorKind::UnexpectedToken { token: Some(token) } => write!(f, "unexpected token: {}", token),
            ErrorKind::Other(ctx) => ctx.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParseError<E,P=Position> {
    position: P,
    context: Vec<ErrorKind<E>>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Position {
    EndOfStream,
    Span(Span),
}

impl<E, P> ParseError<E, P> {
    pub fn context(&self) -> &[ErrorKind<E>] {
        &self.context[..]
    }

    pub fn position(&self) -> &P {
        &self.position
    }

    pub fn root_cause(&self) -> &ErrorKind<E> {
        self.context.first().unwrap_or(&ErrorKind::UnexpectedToken { token: None })
    }
}

impl<E> ParseError<E> {
    pub fn new(span: Span) -> ParseError<E> {
        ParseError {
            position: Position::Span(span),
            context: vec![ErrorKind::UnexpectedToken { token: None }],
        }
    }

    pub fn eos() -> ParseError<E> {
        ParseError {
            position: Position::EndOfStream,
            context: vec![ErrorKind::EndOfStream],
        }
    }

    /// A convinience function for creating a [ParseError::Custom] variant.
    pub fn other<C>(span: Span, ctx: C) -> ParseError<E>
    where
        E: From<C>,
    {
        ParseError {
            position: Position::Span(span),
            context: vec![ErrorKind::Other(ctx.into())],
        }
    }

    pub fn verbose(mut self, input: &str) -> ParseError<E, Location> {
        let leading = match self.position {
            Position::EndOfStream => &input[..],
            Position::Span(ref span) => &input[..span.start],
        };

        let (line, column) = leading
            .split('\n')
            .fold((0, 0), |(line_nr, _column), line| (line_nr + 1, line.len()));

        let position = Location {
            line,
            column,
            length: match self.position {
                Position::Span(ref span) => span.len(),
                Position::EndOfStream => 1,
            },
        };

        if let Position::Span(span) = self.position {
            let span = span.clone();
            for ctx in &mut self.context {
                match ctx {
                    ErrorKind::UnexpectedToken { token: token @ None } => {
                        *token = Some(input[span.clone()].to_string());
                    },
                    _ => (),
                }
            }
        }

        ParseError {
            position,
            context: self.context,
        }
    }
}

impl<E,L> fmt::Display for ParseError<E,L> where E: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = self.context.iter()
            .rev()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(": ");

        write!(f, "{}", s)
    }
}

pub type ParseResult<R, E, L=Position> = Result<R, ParseError<E,L>>;

pub struct Location {
    pub line: usize,
    pub column: usize,
    pub length: usize,
}

/// Implements convinience methods related to error handling for [ParseResult].
pub trait ParseResultExt<T, E>: Sized {
    /// Appends error context to the error if the [ParseResult] represents an error.
    fn context<C>(self, context: C) -> ParseResult<T, E>
    where
        E: From<C>;

    /// Transmutes the type into an [Option], dismissing any possible errors.
    fn optional(self) -> Option<T>;
}

impl<T, E> ParseResultExt<T, E> for ParseResult<T, E> {
    fn context<C>(mut self, additional: C) -> ParseResult<T, E>
    where
        E: From<C>,
    {
        if let Err(ref mut err) = self {
            err.context.push(ErrorKind::Other(additional.into()));
        }

        self
    }

    fn optional(self) -> Option<T> {
        self.ok()
    }
}
