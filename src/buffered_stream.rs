use std::collections::VecDeque;

use crate::{
    Span,
    TokenStream,
};

pub struct BufferedStream<S, T> {
    buffer: VecDeque<(T, Span)>,
    position: usize,
    stream: S,
}

impl<S,T> BufferedStream<S,T> {
    pub fn new<I>(stream: I) -> BufferedStream<S,T>
    where
        S: Iterator<Item=(T, Span)>,
        I: IntoIterator<Item=(T, Span), IntoIter=S>,
    {
        BufferedStream {
            buffer: VecDeque::new(),
            position: 0,
            stream: stream.into_iter(),
        }
    }
}

impl<S,T> TokenStream<T> for BufferedStream<S, T>
where
    S: Iterator<Item=(T, Span)>,
    T: Clone,
{
    fn advance(&mut self) -> Option<(T, Span)> {
        if self.position == 0 {
            if let Some((token, span)) = self.stream.next() {
                self.buffer.push_front((token.clone(), span.clone()));
                return Some((token, span));
            }
        }

        self.position -= 1;
        self.buffer.get(self.position).map(Clone::clone)
    }

    fn backtrack(&mut self, n: usize) {
        if self.position + n > self.buffer.len() + 1 {
            panic!();
        }

        self.position += n;
    }

    fn commit(&mut self) {
        self.buffer.truncate(self.position);
    }
}
