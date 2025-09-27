use std::{iter, rc::Rc, vec::IntoIter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'code> {
    Num(usize),
    Ident(&'code str),
    String(&'code str),
    Keyword(&'code str),
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Semicolon,
    Comma,
    DoubleEq,
    At,
    Slash,
}

impl std::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("'")?;
        match self {
            Tok::Num(n) => write!(f, "{n}"),
            Tok::Keyword(s) | Tok::Ident(s) => f.write_str(s),
            Tok::String(s) => write!(f, "'{s}'"),
            Tok::LParen => f.write_str("("),
            Tok::RParen => f.write_str(")"),
            Tok::LBracket => f.write_str("["),
            Tok::RBracket => f.write_str("]"),
            Tok::Colon => f.write_str(":"),
            Tok::Semicolon => f.write_str(";"),
            Tok::Comma => f.write_str(","),
            Tok::DoubleEq => f.write_str("=="),
            Tok::At => f.write_str("@"),
            Tok::Slash => f.write_str("/"),
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
            '@' => Some(Tok::At),
            '/' => Some(Tok::Slash),
            _ => None,
        };
        let is_comment = c == '#';
        let is_str_literal = c == '\'';
        if tok.is_some() || c.is_whitespace() || is_comment || is_str_literal {
            if !code[i..j].is_empty() {
                let tok = match &code[i..j] {
                    "==" => Tok::DoubleEq,
                    kw @ ("if" | "else") => Tok::Keyword(kw),
                    _ => match &code[i..j].parse::<usize>() {
                        Ok(n) => Tok::Num(*n),
                        Err(_) => Tok::Ident(&code[i..j]),
                    },
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
            let s = chars.by_ref().take_while(|(_, c)| *c != '\'').count();
            toks.push((Tok::String(&code[j + 1..j + 1 + s]), i));
            i = j + s + 2;
        }
    }
    toks
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Expr {
    Var(String),
    String(String),
    Eq([Box<Expr>; 2]),
    TimeLoop(Vec<Expr>, usize, usize),
    Lambda(String, Box<Expr>),
    App([Box<Expr>; 2]),
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
                Ok(Expr::App([
                    Box::new(Expr::App([Box::new(p), Box::new(t)])),
                    Box::new(f),
                ]))
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
                let mut step = 0;
                let mut phase = 0;
                if let Some((Tok::At, _)) = toks.peek() {
                    toks.next();
                    step = match toks.next() {
                        Some((Tok::Num(step), _)) => step,
                        Some((t, i)) => {
                            return Err((format!("Expected a number, but found {t}"), Some(i)));
                        }
                        None => {
                            return Err((format!("Expected a number, but the code ended"), None));
                        }
                    };
                    expect(toks, Tok::Slash)?;
                    phase = match toks.next() {
                        Some((Tok::Num(phase), _)) => phase,
                        Some((t, i)) => {
                            return Err((format!("Expected a number, but found {t}"), Some(i)));
                        }
                        None => {
                            return Err((format!("Expected a number, but the code ended"), None));
                        }
                    };
                }
                Ok(Expr::TimeLoop(exprs, step, phase))
            }
            Tok::RParen
            | Tok::RBracket
            | Tok::Colon
            | Tok::Semicolon
            | Tok::Comma
            | Tok::DoubleEq
            | Tok::At
            | Tok::Slash
            | Tok::Num(_)
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum Env {
    Nil,
    Entry(String, Val, Rc<Env>),
}

impl Env {
    fn set(self: &Rc<Self>, k: String, v: Val) -> Env {
        Env::Entry(k, v, Rc::clone(&self))
    }

    fn get(&self, var: &str) -> Result<&Val, String> {
        match self {
            Env::Nil => Err(format!("Unbound variable {var}")),
            Env::Entry(k, val, _) if k == var => Ok(val),
            Env::Entry(_, _, env) => env.get(var),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    String(String),
    Lambda(String, Box<Expr>, Rc<Env>),
    TimeLoop {
        vals: Vec<Val>,
        step: usize,
        phase: usize,
    },
}

fn simplify_time_loop(vals: Vec<Val>) -> Vec<Val> {
    if vals.is_empty() {
        return vals;
    }
    let n = vals.len();
    let mut period_len = 1;
    for i in 1..n {
        if vals[i] != vals[i % period_len] {
            period_len = i + 1;
        }
    }
    if n % period_len == 0 {
        vals[0..period_len].to_vec()
    } else {
        vals
    }
}

impl Val {
    fn depth(&self) -> usize {
        match self {
            Val::String(_) | Val::Lambda(_, _, _) => 0,
            Val::TimeLoop { vals, .. } => {
                vals.iter().map(|v| v.depth()).max().unwrap_or_default() + 1
            }
        }
    }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::String(s) => write!(f, "'{s}'"),
            Val::TimeLoop { vals, step, phase } => {
                f.write_str("[")?;
                for (i, val) in vals.iter().enumerate() {
                    if i != 0 {
                        f.write_str("; ")?;
                    }
                    write!(f, "{val}")?;
                }
                f.write_str("]")?;
                if *step != 0 || *phase != 0 {
                    write!(f, "@{step}/{phase}")?;
                }
                Ok(())
            }
            Val::Lambda(v, body, env) => write!(f, "{v} => {body:?}@{env:?}"),
        }
    }
}

fn eq(a: &Val, b: &Val) -> Result<Val, String> {
    fn _true() -> Val {
        Val::Lambda(
            "x".into(),
            Box::new(Expr::Lambda("y".into(), Box::new(Expr::Var("x".into())))),
            Rc::new(Env::Nil),
        )
    }
    fn _false() -> Val {
        Val::Lambda(
            "x".into(),
            Box::new(Expr::Lambda("y".into(), Box::new(Expr::Var("y".into())))),
            Rc::new(Env::Nil),
        )
    }
    let depth_a = a.depth();
    let depth_b = b.depth();
    match (a, b) {
        (Val::String(a), Val::String(b)) if a == b => Ok(_true()),
        (Val::String(_), Val::String(_)) => Ok(_false()),
        (a @ Val::String(_), Val::TimeLoop { vals, step, phase }) => Ok(Val::TimeLoop {
            step: *step,
            phase: *phase,
            vals: simplify_time_loop(vals.iter().map(|b| eq(a, b)).collect::<Result<_, _>>()?),
        }),
        (Val::TimeLoop { vals, step, phase }, b @ Val::String(_)) => Ok(Val::TimeLoop {
            step: *step,
            phase: *phase,
            vals: simplify_time_loop(vals.iter().map(|a| eq(a, b)).collect::<Result<_, _>>()?),
        }),
        (
            Val::TimeLoop {
                vals: vals_a,
                step: step_a,
                phase: phase_a,
            },
            Val::TimeLoop {
                vals: vals_b,
                step: step_b,
                phase: phase_b,
            },
        ) => {
            if *step_a != 0 || *step_b != 0 {
                return Err(format!(
                    "Cannot compare time loops at steps {step_a} and {step_b}"
                ));
            }
            let (vals, phase) = if depth_a > depth_b {
                (
                    vals_a.iter().map(|a| eq(a, b)).collect::<Result<_, _>>()?,
                    *phase_a,
                )
            } else if depth_a < depth_b {
                (
                    vals_b.iter().map(|b| eq(a, b)).collect::<Result<_, _>>()?,
                    *phase_b,
                )
            } else {
                let n = vals_a.len() * vals_b.len();
                let x: Vec<&Val> = vals_a.into_iter().cycle().take(n).collect();
                let y: Vec<&Val> = vals_b.into_iter().cycle().take(n).collect();
                (
                    x.into_iter()
                        .zip(y.into_iter())
                        .map(|(x, y)| eq(x, y))
                        .collect::<Result<_, _>>()?,
                    0,
                )
            };
            let vals = simplify_time_loop(vals);
            Ok(Val::TimeLoop {
                step: 0,
                phase,
                vals,
            })
        }
        (a @ Val::Lambda(_, _, _), b) | (a, b @ Val::Lambda(_, _, _)) => {
            Err(format!("Cannot compare {a} with {b}"))
        }
    }
}

fn app(f: Val, arg: Val) -> Result<Val, String> {
    let depth_f = f.depth();
    let depth_arg = arg.depth();
    match (f, arg) {
        (Val::Lambda(v, body, env), arg) => {
            let env = env.set(v, arg);
            body.eval(&Rc::new(env))
        }

        (fs @ Val::TimeLoop { .. }, Val::TimeLoop { vals, step, phase }) if depth_f < depth_arg => {
            let vals = simplify_time_loop(
                vals.into_iter()
                    .map(|arg| app(fs.clone(), arg))
                    .collect::<Result<_, _>>()?,
            );
            Ok(Val::TimeLoop { vals, step, phase })
        }
        (
            Val::TimeLoop {
                vals: fs,
                step,
                phase,
            },
            Val::TimeLoop { vals: args, .. },
        ) if depth_f == depth_arg => {
            let n = fs.len() * args.len();
            let x: Vec<Val> = fs.into_iter().cycle().take(n).collect();
            let y: Vec<Val> = args.into_iter().cycle().take(n).collect();
            let vals = simplify_time_loop(
                x.into_iter()
                    .zip(y.into_iter())
                    .map(|(f, arg)| app(f, arg))
                    .collect::<Result<_, _>>()?,
            );
            Ok(Val::TimeLoop { vals, step, phase })
        }
        (Val::TimeLoop { vals, step, phase }, arg) => {
            let vals = simplify_time_loop(
                vals.into_iter()
                    .map(|f| app(f, arg.clone()))
                    .collect::<Result<_, _>>()?,
            );
            Ok(Val::TimeLoop { vals, step, phase })
        }
        (s @ Val::String(_), arg) => Err(format!("Cannot apply the string {s} to the value {arg}")),
    }
}

impl Expr {
    fn eval(self, env: &Rc<Env>) -> Result<Val, String> {
        match self {
            Expr::Var(v) => env.get(&v).cloned(),
            Expr::String(s) => Ok(Val::String(s)),
            Expr::Eq([a, b]) => {
                let a = a.eval(env)?;
                let b = b.eval(env)?;
                eq(&a, &b)
            }
            Expr::TimeLoop(vals, step, phase) => Ok(Val::TimeLoop {
                step,
                phase,
                vals: vals
                    .into_iter()
                    .map(|v| v.eval(env))
                    .collect::<Result<_, _>>()?,
            }),
            Expr::Lambda(v, body) => Ok(Val::Lambda(v, body, Rc::clone(env))),
            Expr::App([f, arg]) => {
                let f = f.eval(env)?;
                let mut arg = arg.eval(env)?;
                if let Val::TimeLoop { vals, step, phase } = &mut arg {
                    if *phase != 0 && *step == 0 {
                        vals.rotate_left(1);
                        *step = *phase;
                    }
                }
                let mut result = app(f, arg)?;
                if let Val::TimeLoop { vals, step, phase } = &mut result {
                    if *phase != 0 {
                        *step += 1;
                        if step == phase {
                            *step = 0;
                            vals.rotate_right(1);
                        }
                    }
                }
                Ok(result)
            }
        }
    }
}

pub fn eval(code: &str) -> Result<String, String> {
    let expr = parse(code)?;
    let val = expr.eval(&Rc::new(Env::Nil))?;
    Ok(format!("{val}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whatever1() -> Result<(), String> {
        let v = "'x'";
        let code = format!(
            "
        if {v} == 'x':
            'x'
        else:
            'y'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn whatever2() -> Result<(), String> {
        let v = "'y'";
        let code = format!(
            "
        if {v} == 'x':
            'x'
        else:
            'y'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn simple_liar() -> Result<(), String> {
        let v = "['x'; 'y']@0/2";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn captured_liar() -> Result<(), String> {
        let v = "[['x']; ['y'; 'x']]@0/2";
        let code = format!(
            "
        if {v} == ['x'; 'y']:
            'y'
        else:
            'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar1() -> Result<(), String> {
        let v = "[['x']; ['x'; 'y']]@0/2";
        let code = format!(
            "
        if {v} == ['x'; 'y']:
            'x'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar2() -> Result<(), String> {
        let v = "[['y']; ['x'; 'y']]@0/2";
        let code = format!(
            "
        if {v} == ['x'; 'y']:
            'y'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn escaped_liar3() -> Result<(), String> {
        let v = "[['x']; ['z'; 'y']; ['x'; 'z']; ['z'; 'x']; ['x'; 'y']; ['z']]@0/2";
        let code = format!(
            "
        if {v} == ['x'; 'y']:
            'z'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn liar_twin1() -> Result<(), String> {
        let v = "['x'; 'y']@0/2";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            if {v} == 'x':
                'y'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }

    #[test]
    fn liar_twin2() -> Result<(), String> {
        let v = "['x'; 'y']@0/2";
        let code = format!(
            "
        if {v} == 'x':
            'y'
        else:
            if {v} == 'x':
                'z'
            else:
                'x'
        "
        );
        assert_eq!(eval(&code)?, v);
        Ok(())
    }
}
