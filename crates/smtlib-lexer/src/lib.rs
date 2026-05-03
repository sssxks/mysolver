//! Lexer and S-expression parser for the SMT-LIB subset used in this workspace.
//!
//! The parser preserves byte spans on every parsed node so later stages can
//! report syntax and command errors against the original input.

use std::borrow::Cow;
use std::fmt;

/// Half-open byte range within the original input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    /// First byte covered by the span.
    pub start: u32,
    /// First byte after the span.
    pub end: u32,
}

impl Span {
    /// Creates a span from a start and end byte offset.
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    /// Returns the exact source slice covered by this span.
    pub fn slice(self, input: &str) -> &str {
        &input[self.start as usize..self.end as usize]
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
    /// Any non-parenthesis atom.
    Atom,
}

/// Parsed SMT-LIB S-expression tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExpr {
    /// Atomic leaf expression.
    Atom {
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
            Self::Atom { span } | Self::List { span, .. } => *span,
        }
    }

    /// Returns the decoded atom text when this expression is atomic.
    pub fn as_atom<'a>(&self, input: &'a str) -> Option<Cow<'a, str>> {
        match self {
            Self::Atom { span } => Some(decode_atom_text(span.slice(input))),
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
    let input_len = input.len();
    let max_len = u32::MAX as usize;
    if input_len > max_len {
        return Err(ParseError::new(
            Span::new(u32::MAX, u32::MAX),
            "input exceeds supported 4 GiB span range",
        ));
    }
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
                self.span(start, start + 1),
                "unexpected close parenthesis",
            )),
            Some('|') => self.parse_bar_atom(),
            Some('"') => self.parse_string_atom(),
            Some(_) => self.parse_plain_atom(),
            None => Err(ParseError::new(
                self.span(start, start),
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
                        span: self.span(start, self.pos),
                    });
                }
                Some(_) => items.push(self.parse_expr()?),
                None => {
                    return Err(ParseError::new(
                        self.span(start, self.pos),
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
        while let Some(ch) = self.peek_char() {
            if ch == '|' {
                self.consume_char();
                return Ok(SExpr::Atom {
                    span: self.span(start, self.pos),
                });
            }
            self.consume_char();
        }
        Err(ParseError::new(
            self.span(start, self.pos),
            "unterminated vertical-bar atom",
        ))
    }

    /// Parses `"` ... `"` strings with doubled-quote escapes.
    fn parse_string_atom(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        self.consume_char();
        loop {
            match self.peek_char() {
                Some('"') => {
                    self.consume_char();
                    if self.peek_char() == Some('"') {
                        self.consume_char();
                    } else {
                        return Ok(SExpr::Atom {
                            span: self.span(start, self.pos),
                        });
                    }
                }
                Some(_) => {
                    self.consume_char();
                }
                None => {
                    return Err(ParseError::new(
                        self.span(start, self.pos),
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
            return Err(ParseError::new(self.span(start, start), "expected atom"));
        }
        Ok(SExpr::Atom {
            span: self.span(start, self.pos),
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

    /// Converts byte offsets known to fit into the public span representation.
    fn span(&self, start: usize, end: usize) -> Span {
        let Ok(start) = u32::try_from(start) else {
            unreachable!("input length was validated before parsing")
        };
        let Ok(end) = u32::try_from(end) else {
            unreachable!("input length was validated before parsing")
        };
        Span::new(start, end)
    }
}

/// Decodes one atom slice according to SMT-LIB quoting rules.
fn decode_atom_text(raw: &str) -> Cow<'_, str> {
    match raw.as_bytes().first().copied() {
        Some(b'|') => Cow::Borrowed(&raw[1..raw.len() - 1]),
        Some(b'"') => decode_string_atom_text(raw),
        _ => Cow::Borrowed(raw),
    }
}

/// Decodes one SMT-LIB string atom, collapsing doubled-quote escapes on demand.
fn decode_string_atom_text(raw: &str) -> Cow<'_, str> {
    let inner = &raw[1..raw.len() - 1];
    if !inner.contains("\"\"") {
        return Cow::Borrowed(inner);
    }

    let mut text = String::with_capacity(inner.len());
    let mut chars = inner.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '"' && chars.peek() == Some(&'"') {
            let _ = chars.next();
        }
        text.push(ch);
    }
    Cow::Owned(text)
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
            exprs[0].as_list().expect("list")[2]
                .as_atom(
                    r#"; x
            (set-info :source |a
            b|)
            (set-info :license "x""y")
        "#,
                )
                .as_deref(),
            Some("a\n            b")
        );
        assert_eq!(
            exprs[1].as_list().expect("list")[2]
                .as_atom(
                    r#"; x
            (set-info :source |a
            b|)
            (set-info :license "x""y")
        "#,
                )
                .as_deref(),
            Some("x\"y")
        );
    }
}
