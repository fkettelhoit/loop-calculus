use std::{iter, vec::IntoIter};

pub fn eval(code: &str) -> String {
    format!("{:?}", parse(code))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'code> {
    Ident(&'code str),
    String(&'code str),
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Semicolon,
    Comma,
    DoubleEq,
    Keyword(&'code str),
}

impl std::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("'")?;
        match self {
            Tok::Keyword(s) | Tok::Ident(s) => f.write_str(s),
            Tok::String(s) => write!(f, "\"{s}\""),
            Tok::LParen => f.write_str("("),
            Tok::RParen => f.write_str(")"),
            Tok::LBracket => f.write_str("["),
            Tok::RBracket => f.write_str("]"),
            Tok::Colon => f.write_str(":"),
            Tok::Semicolon => f.write_str(";"),
            Tok::Comma => f.write_str(","),
            Tok::DoubleEq => f.write_str("=="),
        }?;
        f.write_str("'")
    }
}

fn scan(code: &str) -> Vec<(Tok, usize)> {
    let mut toks = vec![];
    let mut i = 0;
    let mut chars = code.char_indices().chain(iter::once((code.len(), ' ')));
    while let Some((j, c)) = chars.next() {
        let tok = match c {
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '[' => Some(Tok::LBracket),
            ']' => Some(Tok::RBracket),
            ':' => Some(Tok::Colon),
            ';' => Some(Tok::Semicolon),
            ',' => Some(Tok::Comma),
            _ => None,
        };
        let is_comment = c == '#';
        let is_str_literal = c == '"';
        if tok.is_some() || c.is_whitespace() || is_comment || is_str_literal {
            if !code[i..j].is_empty() {
                let tok = match &code[i..j] {
                    "==" => Tok::DoubleEq,
                    kw @ ("if" | "else") => Tok::Keyword(kw),
                    _ => Tok::Ident(&code[i..j]),
                };
                toks.push((tok, i));
            }
            i = j + 1;
        }
        if let Some(tok) = tok {
            toks.push((tok, j));
        } else if is_comment {
            let (j, _) = chars.find(|(_, c)| *c == '\n').unwrap_or_default();
            i = j + 1;
        } else if is_str_literal {
            let s = chars.by_ref().take_while(|(_, c)| *c != '"').count();
            toks.push((Tok::String(&code[j + 1..j + 1 + s]), i));
            i = j + s + 2;
        }
    }
    toks
}

#[derive(Debug, Clone)]
enum Expr {
    Var(String),
    String(String),
    Eq([Box<Expr>; 2]),
    Conditional([Box<Expr>; 3]),
    TimeLoop(Vec<Expr>),
}

fn pos_at(i: usize, code: &str) -> String {
    let (mut line, mut col) = (1, 1);
    for c in code.chars().take(i) {
        if c == '\n' {
            line += 1;
            col = 0;
        }
        col += 1;
    }
    format!("line {line}, col {col}")
}

fn parse(code: &str) -> Result<Expr, String> {
    type Toks<'c> = iter::Peekable<IntoIter<(Tok<'c>, usize)>>;
    fn expect(toks: &mut Toks<'_>, t: Tok<'_>) -> Result<(), (String, Option<usize>)> {
        match toks.next() {
            Some((tok, _)) if tok == t => Ok(()),
            Some((tok, i)) => Err((format!("Expected {t}, but found {tok}"), Some(i))),
            None => Err((format!("Expected {t}, but the code just ended"), None)),
        }
    }
    fn parse_expr(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        match toks.peek() {
            Some((Tok::Keyword("if"), _)) => {
                toks.next();
                let p = parse_infix(toks)?;
                expect(toks, Tok::Colon)?;
                let t = parse_expr(toks)?;
                expect(toks, Tok::Keyword("else"))?;
                expect(toks, Tok::Colon)?;
                let f = parse_expr(toks)?;
                Ok(Expr::Conditional([Box::new(p), Box::new(t), Box::new(f)]))
            }
            _ => parse_infix(toks),
        }
    }
    fn parse_infix(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        let x = parse_arg(toks)?;
        match toks.peek() {
            Some((Tok::DoubleEq, _)) => {
                toks.next();
                let y = parse_arg(toks)?;
                Ok(Expr::Eq([Box::new(x), Box::new(y)]))
            }
            _ => Ok(x),
        }
    }
    fn parse_arg(toks: &mut Toks<'_>) -> Result<Expr, (String, Option<usize>)> {
        let Some((tok, i)) = toks.next() else {
            return Err(("Expected an expression, but found nothing".into(), None));
        };
        match tok {
            Tok::Ident(v) => Ok(Expr::Var(v.into())),
            Tok::String(s) => Ok(Expr::String(s.into())),
            Tok::LParen => {
                let expr = parse_expr(toks)?;
                expect(toks, Tok::RParen)?;
                Ok(expr)
            }
            Tok::LBracket => {
                let mut exprs = vec![parse_expr(toks)?];
                while let Some((Tok::Semicolon, _)) = toks.peek() {
                    toks.next();
                    exprs.push(parse_expr(toks)?);
                }
                expect(toks, Tok::RBracket)?;
                Ok(Expr::TimeLoop(exprs))
            }
            Tok::RParen
            | Tok::RBracket
            | Tok::Colon
            | Tok::Semicolon
            | Tok::Comma
            | Tok::DoubleEq
            | Tok::Keyword(_) => Err((format!("Expected an expression, found {tok}"), Some(i))),
        }
    }
    let mut toks = scan(code).into_iter().peekable();
    match parse_expr(&mut toks) {
        Ok(expr) => match toks.next() {
            Some((tok, i)) => Err(format!(
                "Expected the code to end, but found {tok} at {}",
                pos_at(i, code)
            )),
            None => Ok(expr),
        },
        Err((e, Some(i))) => Err(format!("{e} at {}", pos_at(i, code))),
        Err((e, None)) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn liar() {
        let v = r#"["x"; "y"]"#;
        let liar = format!(
            r#"
        if {v} == "x":
            "y"
        else:
            "x"
        "#
        );
        assert_eq!(eval(&liar), v);
    }
}
