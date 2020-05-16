<p align="center"><img src="assets/hinku.svg" /></p>
<p align="center">
  <a href="https://docs.rs/hinku">
    <img src="https://docs.rs/hinku/badge.svg" />
  </a>
  <a href="https://crates.io/crates/hinku">
    <img src="https://img.shields.io/crates/v/hinku.svg" />
  </a>
</p>

# Overview

**Hinku** is a small library for writing parsers based on token streams.
It provides an integration for lexers created with the [logos](https://github.com/maciejhirsz/logos) crate
but provedes flexible trait based interface for integration with other token streams.

# Example

Below you can find a rudimentary parser implemented using this library and the Logos crate.

```rust
use logos::Logos;
use hinku::{
    logos::BufferedLexer,
    Either,
    ParseError,
    ParseResult,
    TokenStream,
    TokenStreamExt,
};

#[derive(Logos, Debug, Clone, PartialEq)]
enum Token {
    #[token("foo")]
    Foo,

    #[token("bar")]
    Bar,

    #[error]
    #[regex(r"[ \n\r\f\t]+", logos::skip)]
    Error,
}

/// A function that either consumes a Foo token or returns an error.
fn foo(stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
    match stream.advance() {
        None => Err(ParseError::EndOfStream),
        Some((Token::Foo, _)) => Ok(Token::Foo),
        Some((other, span)) => Err(ParseError::custom(span, "expected a foo".into())),
    }
}

/// A function that either consumes a Bar token or returns an error.
fn bar(stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
    match stream.advance() {
        None => Err(ParseError::EndOfStream),
        Some((Token::Bar, _)) => Ok(Token::Bar),
        Some((other, span)) => Err(ParseError::custom(span, "expected a bar".into())),
    }
}

/// A function that consumes either one of the tokens.
fn foo_or_bar(mut stream: &mut dyn TokenStream<Token>) -> ParseResult<Token, String> {
    stream.either(foo, bar)
        .map(Either::merge)
        .expected("expected either a foo or a bar")
}

/// A function that expects a Foo token, followed by a Bar token.
fn foobar(mut stream: &mut dyn TokenStream<Token>) -> ParseResult<(Token, Token), String> {
    let f = stream.take(foo)?;
    let b = stream.take(bar)?;

    Ok((f, b))
}

let lex = Token::lexer("foo bar bar foo bar");
let mut stream = BufferedLexer::new(lex);

assert_eq!(stream.take(foo), Ok(Token::Foo));
assert_eq!(stream.take(bar), Ok(Token::Bar));
assert_eq!(stream.take(foo_or_bar), Ok(Token::Bar));
assert_eq!(stream.take(foobar), Ok((Token::Foo, Token::Bar)));
```
