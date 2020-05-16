use crate::Span;
use std::ops::Range;

/// Represents a parsing error.
#[derive(Debug, PartialEq, Clone)]
pub enum ErrorKind<E> {
    /// The end of the stream was reached unexpectedly.
    EndOfStream,

    /// An user-defined error occurred.
    Other {
        /// List of error context. The first element is "deeper"
        /// into the parser and the last more "general."
        context: Vec<E>,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParseError<E, P=Span> {
    position: P,
    kind: ErrorKind<E>,
}

impl<E, P> ParseError<E, P> {
    pub fn position(&self) -> &P {
        &self.position
    }
    
    pub fn kind(&self) -> &ErrorKind<E> {
        &self.kind
    }
}

impl<E> ParseError<E> {
    pub fn new(position: Span) -> ParseError<E> {
        ParseError {
            position,
            kind: ErrorKind::Other {
                context: vec![],
            },
        }
    }

    pub fn eos(position: Span) -> ParseError<E> {
        ParseError {
            position,
            kind: ErrorKind::EndOfStream,
        }
    }

    /// A convinience function for creating a [ParseError::Custom] variant.
    pub fn other<C>(position: Span, ctx: C) -> ParseError<E>
    where
        E: From<C>,
    {
        ParseError {
            position,
            kind: ErrorKind::Other {
                context: vec![ctx.into()],
            },
        }
    }

    pub fn verbose(self, input: &str) -> ParseError<E, Location> {
        let (line, column) = input[..self.position.start]
            .lines()
            .fold((0, 0), |(line_nr, _column), line| (line_nr + 1, line.len()));

        let position = Location {
            line,
            column,
            length: self.position.len(),
        };

        ParseError {
            position,
            kind: self.kind,
        }
    }
}

pub type ParseResult<R, E, L=Span> = Result<R, ParseError<E,L>>;

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
            if let ErrorKind::Other { ref mut context } = err.kind {
                context.push(additional.into());
            }
        }

        self
    }

    fn optional(self) -> Option<T> {
        self.ok()
    }
}
