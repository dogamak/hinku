use crate::Span;

/// Represents a parsing error.
#[derive(Debug, PartialEq)]
pub enum ParseError<E> {
    /// The end of the stream was reached unexpectedly.
    EndOfStream,

    /// An user-defined error occurred.
    Other {
        /// Part of the input that caused the error.
        span: Span,

        /// List of error context. The first element is "deeper"
        /// into the parser and the last more "general."
        context: Vec<E>,
    },
}

impl<E> ParseError<E> {
    pub fn new(span: Span) -> ParseError<E> {
        ParseError::Other {
            span,
            context: vec![],
        }
    }

    /// A convinience function for creating a [ParseError::Custom] variant.
    pub fn other<C>(span: Span, ctx: C) -> ParseError<E>
    where
        E: From<C>,
    {
        ParseError::Other {
            span,
            context: vec![ctx.into()],
        }
    }
}

pub type ParseResult<R, E> = Result<R, ParseError<E>>;

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
    fn context<C>(self, additional: C) -> ParseResult<T, E>
    where
        E: From<C>,
    {
        match self {
            Ok(t) => Ok(t),
            Err(ParseError::EndOfStream) => Err(ParseError::EndOfStream),
            Err(ParseError::Other { span, mut context }) => {
                context.push(additional.into());
                Err(ParseError::Other { span, context })
            }
        }
    }

    fn optional(self) -> Option<T> {
        self.ok()
    }
}


