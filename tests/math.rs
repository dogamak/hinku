use logos::{Lexer, Logos};

use hinku::{
    either, match_token, BufferedStream, ParseResult, ParseResultExt,
    TokenStream, TokenStreamExt,
};

type Result<T> = ParseResult<T, String>;

#[derive(Logos, Debug, Clone, PartialEq)]
enum Token {
    #[regex("[ \t\n\r]+", logos::skip)]
    #[error]
    Error,

    #[token("*")]
    Multiply,

    #[token("/")]
    Divide,

    #[token("-")]
    Subtract,

    #[token("+")]
    Add,

    #[regex("[0-9]+", |lex| lex.slice().parse())]
    Literal(i32),
}

fn literal(mut stream: &mut dyn TokenStream<Token>) -> Result<i32> {
    let sign = match stream.assert_token(Token::Subtract) {
        Ok(()) => -1,
        Err(_) => 1,
    };

    match_token!(stream, {
        Token::Literal(num) => Ok(num * sign),
    }).expected("expected a number literal")
}

fn multiplication(stream: &mut dyn TokenStream<Token>) -> Result<Token> {
    match_token!(stream, {
        token @ Token::Multiply => Ok(token),
    }).expected("expected multiplication operator")
}

fn division(stream: &mut dyn TokenStream<Token>) -> Result<Token> {
    match_token!(stream, {
        token @ Token::Divide => Ok(token),
    }).expected("expected division operator")
}

fn addition(stream: &mut dyn TokenStream<Token>) -> Result<Token> {
    match_token!(stream, {
        token @ Token::Add => Ok(token),
    }).expected("expected addition operator")
}

fn subtraction(stream: &mut dyn TokenStream<Token>) -> Result<Token> {
    match_token!(stream, {
        token @ Token::Subtract => Ok(token),
    }).expected("expected subtraction operator")
}

#[derive(Debug, PartialEq)]
enum Factor {
    Literal(i32),
    Operation {
        lhs: i32,
        operation: Token,
        rhs: Box<Factor>,
    },
}

fn factor(mut stream: &mut dyn TokenStream<Token>) -> Result<Factor> {
  let lhs = stream.take(literal)?;
  
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

#[derive(Debug, PartialEq)]
enum Expr {
    Factor(Factor),
    Operation {
        lhs: Factor,
        operation: Token,
        rhs: Box<Expr>,
    },
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

#[test]
fn math() {
    let lex = Token::lexer("1/2+3*-4/5-6*7");
    let mut stream = BufferedStream::new(lex.spanned());

    let expr = stream.take(expr);

    assert_eq!(
        expr,
        Ok(Expr::Operation {
            lhs: Factor::Operation {
                lhs: 1,
                operation: Token::Divide,
                rhs: Box::new(Factor::Literal(2))
            },
            operation: Token::Add,
            rhs: Box::new(Expr::Operation {
                lhs: Factor::Operation {
                    lhs: 3,
                    operation: Token::Multiply,
                    rhs: Box::new(Factor::Operation {
                        lhs: -4,
                        operation: Token::Divide,
                        rhs: Box::new(Factor::Literal(5)),
                    }),
                }, 
                operation: Token::Subtract,
                rhs: Box::new(Expr::Factor(Factor::Operation {
                    lhs: 6,
                    operation: Token::Multiply,
                    rhs: Box::new(Factor::Literal(7)),
                }))
            })
        })
    );

    println!("{:?}", expr);
}
