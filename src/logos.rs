use logos::{Logos, Lexer};
use crate::{
    TokenStream,
    Span,
};
use std::collections::VecDeque;

pub struct BufferedLexer<'a, T: Logos<'a>> {
    lexer: Lexer<'a, T>,
    position: usize,
    buffer: VecDeque<(T, Span)>,
}

impl<'a, T> BufferedLexer<'a, T>
where
    T: Logos<'a>,
{
    pub fn new(lexer: Lexer<'a, T>) -> Self {
        BufferedLexer {
            lexer,
            position: 0,
            buffer: VecDeque::new(),
        }
    }
}

impl<'a, T> TokenStream<T> for BufferedLexer<'a, T>
where
    T: Logos<'a> + Clone + std::fmt::Debug,
{
    fn advance(&mut self) -> Option<(T, Span)> {
        if self.position == 0 {
            if let Some(token) = self.lexer.next() {
                let span = self.lexer.span();

                self.buffer.push_front((token.clone(), span.clone()));


                println!("Buf: {:?} Pos: {}", self.buffer, self.position);

                return Some((token, span));
            }
        }

        println!("Buf: {:?} Pos: {}", self.buffer, self.position);
        self.position -= 1;
        self.buffer.get(self.position).map(Clone::clone)
    }

    fn backtrack(&mut self, n: usize) {
        println!("Backtracking: {} + {} = {} / {}", self.position, n, self.position + n, self.buffer.len());

        if self.position + n > self.buffer.len() + 1 {
            panic!();
        }

        self.position += n;
        // self.buffer.truncate(self.buffer.len() - n);
    }

    fn commit(&mut self) {
        println!("Commit! {:?}", self.buffer);
        self.buffer.truncate(self.position);
    }
}

