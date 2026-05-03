//! Lexer and S-expression parser for the SMT-LIB subset used in this workspace.
//!
//! The parser preserves byte spans on every parsed node so later stages can
//! report syntax and command errors against the original input.

use std::fmt;

/// Half-open byte range within the original input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// First byte covered by the span.
    pub start: usize,
    /// First byte after the span.
    pub end: usize,
}

impl Span {
    /// Creates a span from a start and end byte offset.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

/// One lexical token from the SMT-LIB input stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// Token category and payload.
    pub kind: TokenKind,
    /// Location of the token in the original input.
    pub span: Span,
}

/// Token categories recognized by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    /// `(`.
    OpenParen,
    /// `)`.
    CloseParen,
    /// Any non-parenthesis atom after SMT-LIB quoting rules are applied.
    Atom(Box<str>),
}

/// Parsed SMT-LIB S-expression tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExpr {
    /// Atomic leaf expression.
    Atom {
        /// Atom text after SMT-LIB quoting rules are applied.
        text: Box<str>,
        /// Source span covering the atom.
        span: Span,
    },
    /// Proper list expression.
    List {
        /// Child expressions in source order.
        items: Box<[SExpr]>,
        /// Source span covering the full list, including parentheses.
        span: Span,
    },
}

impl SExpr {
    /// Returns the source span covering this entire expression.
    pub fn span(&self) -> Span {
        match self {
            Self::Atom { span, .. } | Self::List { span, .. } => *span,
        }
    }

    /// Returns the atom text when this expression is atomic.
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Self::Atom { text, .. } => Some(text),
            Self::List { .. } => None,
        }
    }

    /// Returns the list items when this expression is a list.
    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            Self::Atom { .. } => None,
            Self::List { items, .. } => Some(items),
        }
    }
}

/// Parse failure with a byte span into the original input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Span of the offending input.
    pub span: Span,
    /// Human-readable error description.
    pub message: Box<str>,
}

impl ParseError {
    /// Builds a parse failure at `span` with the given explanatory message.
    fn new(span: Span, message: impl Into<Box<str>>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at bytes {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

/// Parses zero or more top-level SMT-LIB S-expressions from `input`.
pub fn parse_many(input: &str) -> Result<Box<[SExpr]>, ParseError> {
    Parser::new(input).parse_many()
}

/// Incremental tokenizer for UTF-8 SMT-LIB S-expressions in `input`.
struct Parser<'a> {
    /// Full source slice being scanned.
    input: &'a str,
    /// Current byte cursor into `input`.
    pos: usize,
}

impl<'a> Parser<'a> {
    /// Starts scanning from the beginning of `input`.
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    /// Consumes trivia and parses expressions until EOF.
    fn parse_many(mut self) -> Result<Box<[SExpr]>, ParseError> {
        let mut exprs = Vec::new();
        loop {
            self.skip_trivia();
            if self.is_eof() {
                return Ok(exprs.into_boxed_slice());
            }
            exprs.push(self.parse_expr()?);
        }
    }

    /// Parses a single expression after trimming leading trivia at the cursor.
    fn parse_expr(&mut self) -> Result<SExpr, ParseError> {
        self.skip_trivia();
        let start = self.pos;
        match self.peek_char() {
            Some('(') => self.parse_list(),
            Some(')') => Err(ParseError::new(
                Span::new(start, start + 1),
                "unexpected close parenthesis",
            )),
            Some('|') => self.parse_bar_atom(),
            Some('"') => self.parse_string_atom(),
            Some(_) => self.parse_plain_atom(),
            None => Err(ParseError::new(
                Span::new(start, start),
                "unexpected end of input",
            )),
        }
    }

    /// Parses `(` ... `)` producing a nested [`SExpr::List`] with span bounds.
    fn parse_list(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        self.consume_char();
        let mut items = Vec::new();
        loop {
            self.skip_trivia();
            match self.peek_char() {
                Some(')') => {
                    self.consume_char();
                    return Ok(SExpr::List {
                        items: items.into_boxed_slice(),
                        span: Span::new(start, self.pos),
                    });
                }
                Some(_) => items.push(self.parse_expr()?),
                None => {
                    return Err(ParseError::new(
                        Span::new(start, self.pos),
                        "unterminated list",
                    ));
                }
            }
        }
    }

    /// Parses a `|` ... `|` quoted atom and returns [`SExpr::Atom`].
    fn parse_bar_atom(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        self.consume_char();
        let content_start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch == '|' {
                let text = self.input[content_start..self.pos].into();
                self.consume_char();
                return Ok(SExpr::Atom {
                    text,
                    span: Span::new(start, self.pos),
                });
            }
            self.consume_char();
        }
        Err(ParseError::new(
            Span::new(start, self.pos),
            "unterminated vertical-bar atom",
        ))
    }

    /// Parses `"` ... `"` strings with doubled-quote escapes into an atom payload.
    fn parse_string_atom(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        self.consume_char();
        let mut text = String::new();
        loop {
            match self.peek_char() {
                Some('"') => {
                    self.consume_char();
                    if self.peek_char() == Some('"') {
                        text.push('"');
                        self.consume_char();
                    } else {
                        return Ok(SExpr::Atom {
                            text: text.into_boxed_str(),
                            span: Span::new(start, self.pos),
                        });
                    }
                }
                Some(ch) => {
                    text.push(ch);
                    self.consume_char();
                }
                None => {
                    return Err(ParseError::new(
                        Span::new(start, self.pos),
                        "unterminated string",
                    ));
                }
            }
        }
    }

    /// Reads a maximal run of atom characters stopping at whitespace or delimiters.
    fn parse_plain_atom(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() || ch == '(' || ch == ')' || ch == ';' {
                break;
            }
            self.consume_char();
        }
        if self.pos == start {
            return Err(ParseError::new(Span::new(start, start), "expected atom"));
        }
        Ok(SExpr::Atom {
            text: self.input[start..self.pos].into(),
            span: Span::new(start, self.pos),
        })
    }

    /// Advances past whitespace and `; ...` line comments.
    fn skip_trivia(&mut self) {
        loop {
            while matches!(self.peek_char(), Some(ch) if ch.is_whitespace()) {
                self.consume_char();
            }
            if self.peek_char() == Some(';') {
                while let Some(ch) = self.peek_char() {
                    self.consume_char();
                    if ch == '\n' {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    /// Returns the UTF-8 code point at [`Self::pos`], if still inside `input`.
    fn peek_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    /// Advances [`Self::pos`] by one full UTF-8 scalar and returns it.
    fn consume_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.pos += ch.len_utf8();
        Some(ch)
    }

    /// True when the cursor is at or past the end of `input`.
    fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_comments_strings_and_bar_atoms() {
        let exprs = parse_many(
            r#"; x
            (set-info :source |a
            b|)
            (set-info :license "x""y")
        "#,
        )
        .expect("valid input");
        assert_eq!(exprs.len(), 2);
        assert_eq!(
            exprs[0].as_list().expect("list")[2].as_atom(),
            Some("a\n            b")
        );
        assert_eq!(exprs[1].as_list().expect("list")[2].as_atom(), Some("x\"y"));
    }
}
