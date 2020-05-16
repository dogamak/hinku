<p align="center"><img src="assets/hinku.svg" /></p>
<p align="center">
  <a href="https://github.com/dogamak/hinku/actions">
    <img src="https://github.com/dogamak/hinku/workflows/Rust/badge.svg" />
   </a>
  <a href="https://docs.rs/hinku">
    <img src="https://docs.rs/hinku/badge.svg" />
  </a>
  <a href="https://crates.io/crates/hinku">
    <img src="https://img.shields.io/crates/v/hinku.svg" />
  </a>
</p>

# Overview

**Hinku** is a small library for writing token stream based parsers with a focus on error handling
ergonomics and informative error messages. The crate and it's API is under heavy development and
experimentation — do not expect any kind of stability from version to version. 

# Quick Start

Parsers written with hinku are built on backtrack-capable token streams. These streams are *forked*
whenever a parsing subroutine is called.  If a parsing operation is successful, progress on the token
stream is *committed* to it's parent stream.  Alternatively, when an operation fails, the stream can
be *backtracked* to an earlier point in the stream and an alternative operation can be attempted.
When a sub-stream is dropped, it's parent stream is automatically backtracked to it's position before the
fork or to the point of latest *commit*.

Parsing operations are functions with the following signature:

```rust
FnOnce(stream: &mut dyn TokenStream<T>) -> ParseResult<R, E>
```

They can be called either directly passing a stream as an argument, or by passing the function to
`TokenStreamExt::take`, which handles forking and committing on your behalf. A simple parser for
matchematical expressions consisting of `+`, `-`, `*`, `/` and number literals can be written as follows:

```rust
fn factor(mut stream: &mut dyn TokenStream<Token>) -> Result<Factor> {
  let lhs = stream.take(literal)?;
  
  let operation = 
  
  if let Some(operation) = stream.take(either(multiplication, division)).optional() {
    Ok(Factor::Operation {
      lhs,
      operation: operation.merge(),
      rhs: Box::new(stream.take(factor)?),
    })
  } else {
    Ok(Factor::Literal(lhs))
  }
}

fn expr(mut stream: &mut dyn TokenStream<Token>) -> Result<Expr> {
  let lhs = stream.take(factor)?;
  
  if let Some(operation) = stream.take(either(addition, subtraction)).optional() {
    Ok(Expr::Operation {
      lhs,
      operation: operation.merge(),
      rhs: Box::new(stream.take(expr)?),
    })
  } else {
    Ok(Expr::Factor(lhs))
  }
}
```

A complete version of this example and others can be found from the `tests/` subdirectory.
