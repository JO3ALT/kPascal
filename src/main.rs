use pest::Parser;
use pest_derive::Parser;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

mod ast;
mod sema;
mod codegen;

use ast::*;
use sema::*;
use codegen::ForthGen;

#[derive(Parser)]
#[grammar = "kpascal.pest"]
struct PascalParser;

fn main() {
    // 最小：標準入力からPascalを読む（ファイルI/Oなし）
    let src_in = read_stdin();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let src = match preprocess_includes(&src_in, &cwd) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };
    let res = (|| -> Result<String, String> {
        let p = parse_program(&src).map_err(|e| with_source_hint(&src, &e))?;
        let env = build_env(&p).map_err(|e| with_source_hint(&src, &e))?;
        check_program(&env, &p).map_err(|e| with_source_hint(&src, &e))?;
        ForthGen::new(&env)
            .gen_program(&p)
            .map_err(|e| with_source_hint(&src, &e))
    })();
    match res {
        Ok(forth) => {
            print!("{forth}");
        }
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    }
}

fn read_stdin() -> String {
    use std::io::Read;
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    s
}

fn parse_program(src: &str) -> Result<Program, String> {
    let mut pairs = PascalParser::parse(Rule::program, src).map_err(|e| {
        let (line, col) = match e.line_col {
            pest::error::LineColLocation::Pos((l, c)) => (l, c),
            pest::error::LineColLocation::Span((l, c), _) => (l, c),
        };
        format!("parse error at line {line}, column {col}: {e}")
    })?;
    let p = pairs.next().ok_or("no program")?;
    build_program(p)
}

fn with_source_hint(src: &str, err: &str) -> String {
    if err.contains("line ") && err.contains("column ") {
        return err.to_string();
    }
    if let Some(sym) = extract_symbol_from_error(err) {
        if let Some((line, col)) = find_symbol(src, &sym) {
            return format!("{err} at line {line}, column {col}");
        }
    }
    err.to_string()
}

fn extract_symbol_from_error(err: &str) -> Option<String> {
    let prefixes = [
        "unknown type: ",
        "unknown identifier: ",
        "unknown field: ",
        "unknown var: ",
        "unknown routine in scope: ",
        "unknown const: ",
    ];
    for p in prefixes {
        if let Some(rest) = err.strip_prefix(p) {
            return Some(rest.trim().to_string());
        }
    }
    if let Some(pos) = err.find("call to ") {
        let tail = &err[pos + "call to ".len()..];
        let name = tail
            .split(|c: char| c == ':' || c.is_whitespace())
            .next()
            .unwrap_or("")
            .trim();
        if !name.is_empty() {
            return Some(name.to_string());
        }
    }
    None
}

fn find_symbol(src: &str, sym: &str) -> Option<(usize, usize)> {
    if sym.is_empty() {
        return None;
    }
    for (li, line) in src.lines().enumerate() {
        if let Some(ci) = line.find(sym) {
            return Some((li + 1, ci + 1));
        }
    }
    None
}

fn build_program(p: pest::iterators::Pair<Rule>) -> Result<Program, String> {
    let mut it = p.into_inner();
    let name = it
        .next()
        .ok_or("missing program name")?
        .as_str()
        .to_string();
    let block_pair = it.next().ok_or("missing block")?;
    let block = build_block(block_pair)?;
    Ok(Program { name, block })
}

fn build_block(p: pest::iterators::Pair<Rule>) -> Result<Block, String> {
    let mut b = Block::default();
    for item in p.into_inner() {
        match item.as_rule() {
            Rule::const_section => b.consts = build_consts(item)?,
            Rule::type_section => b.types = build_types(item)?,
            Rule::var_section => b.vars = build_vars(item)?,
            Rule::procedure_decl | Rule::function_decl => b.routines.push(build_routine_decl(item)?),
            Rule::compound_stmt => b.body = build_compound(item)?,
            _ => {}
        }
    }
    Ok(b)
}

fn build_routine_decl(p: pest::iterators::Pair<Rule>) -> Result<RoutineDecl, String> {
    match p.as_rule() {
        Rule::procedure_decl => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let mut params = vec![];
            let mut block: Option<Block> = None;
            for x in it {
                match x.as_rule() {
                    Rule::formal_params => params = build_formal_params(x)?,
                    Rule::block => block = Some(build_block(x)?),
                    _ => {}
                }
            }
            Ok(RoutineDecl::Procedure(ProcedureDecl {
                name,
                params,
                block: block.ok_or("missing procedure block")?,
            }))
        }
        Rule::function_decl => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let mut params = vec![];
            let mut ret_ty: Option<TypeRef> = None;
            let mut block: Option<Block> = None;
            for x in it {
                match x.as_rule() {
                    Rule::formal_params => params = build_formal_params(x)?,
                    Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                        ret_ty = Some(build_typeref(x)?)
                    }
                    Rule::block => block = Some(build_block(x)?),
                    _ => {}
                }
            }
            Ok(RoutineDecl::Function(FunctionDecl {
                name,
                params,
                ret_ty: ret_ty.ok_or("missing function return type")?,
                block: block.ok_or("missing function block")?,
            }))
        }
        _ => Err(format!("unexpected routine decl: {:?}", p.as_rule())),
    }
}

fn build_formal_params(p: pest::iterators::Pair<Rule>) -> Result<Vec<ParamDecl>, String> {
    let mut params = vec![];
    for g in p.into_inner() {
        if g.as_rule() != Rule::formal_param_group {
            continue;
        }
        let group_text = g.as_str().trim_start();
        let mut names = vec![];
        let by_ref = group_text.starts_with("var");
        let mut ty: Option<TypeRef> = None;
        for x in g.into_inner() {
            match x.as_rule() {
                Rule::ident => names.push(x.as_str().to_string()),
                Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                    ty = Some(build_typeref(x)?)
                }
                _ => {}
            }
        }
        let ty = ty.ok_or("missing parameter type")?;
        for n in names {
            params.push(ParamDecl {
                name: n,
                ty: ty.clone(),
                by_ref,
            });
        }
    }
    Ok(params)
}

fn build_consts(p: pest::iterators::Pair<Rule>) -> Result<Vec<ConstDecl>, String> {
    let mut v = vec![];
    for cd in p.into_inner() {
        if cd.as_rule() != Rule::const_decl {
            continue;
        }
        let mut it = cd.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let expr = build_const_expr(it.next().unwrap())?;
        v.push(ConstDecl { name, expr });
    }
    Ok(v)
}

fn build_types(p: pest::iterators::Pair<Rule>) -> Result<Vec<TypeDecl>, String> {
    let mut v = vec![];
    for td in p.into_inner() {
        if td.as_rule() != Rule::type_decl {
            continue;
        }
        let mut it = td.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let spec = build_type_spec(it.next().unwrap())?;
        v.push(TypeDecl { name, spec });
    }
    Ok(v)
}

fn build_vars(p: pest::iterators::Pair<Rule>) -> Result<Vec<VarDecl>, String> {
    let mut v = vec![];
    for vd in p.into_inner() {
        if vd.as_rule() != Rule::var_decl {
            continue;
        }
        let mut it = vd.into_inner();
        let name = it.next().unwrap().as_str().to_string();
        let ty = build_typeref(it.next().unwrap())?;
        v.push(VarDecl { name, ty });
    }
    Ok(v)
}

fn build_type_spec(p: pest::iterators::Pair<Rule>) -> Result<TypeSpec, String> {
    match p.as_rule() {
        Rule::type_spec => build_type_spec(p.into_inner().next().unwrap()),
        Rule::basic_type => Ok(TypeSpec::Basic(parse_basic(p.as_str())?)),
        Rule::type_ref => Ok(TypeSpec::Alias(TypeRef::Named(p.as_str().to_string()))),
        Rule::record_type => {
            let mut fields = vec![];
            for fd in p.into_inner() {
                if fd.as_rule() != Rule::field_decl {
                    continue;
                }
                let mut it = fd.into_inner();
                let name = it.next().unwrap().as_str().to_string();
                let ty = build_typeref(it.next().unwrap())?;
                fields.push(FieldDecl { name, ty });
            }
            Ok(TypeSpec::Record(fields))
        }
        Rule::array_type => {
            let mut lens = vec![];
            let mut elem: Option<TypeRef> = None;
            for x in p.into_inner() {
                match x.as_rule() {
                    Rule::type_ref_or_basic | Rule::type_ref | Rule::basic_type => {
                        elem = Some(build_typeref(x)?)
                    }
                    _ => lens.push(build_const_expr(x)?),
                }
            }
            if lens.is_empty() || lens.len() > 3 {
                return Err("array dimensions must be 1..3".into());
            }
            Ok(TypeSpec::Array {
                lens,
                elem: elem.ok_or("array elem type missing")?,
            })
        }
        _ => Err(format!("unexpected type spec: {:?}", p.as_rule())),
    }
}

fn build_typeref(p: pest::iterators::Pair<Rule>) -> Result<TypeRef, String> {
    match p.as_rule() {
        Rule::type_ref_or_basic => build_typeref(p.into_inner().next().unwrap()),
        Rule::basic_type => Ok(TypeRef::Basic(parse_basic(p.as_str())?)),
        Rule::type_ref => Ok(TypeRef::Named(p.as_str().to_string())),
        _ => Err(format!("unexpected typeref: {:?}", p.as_rule())),
    }
}

fn parse_basic(s: &str) -> Result<BasicType, String> {
    match s {
        "integer" => Ok(BasicType::Integer),
        "boolean" => Ok(BasicType::Boolean),
        "char" => Ok(BasicType::Char),
        _ => Err(format!("unknown basic type: {s}")),
    }
}

fn build_compound(p: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
    // compound_stmt -> begin stmt_list? end
    let mut stmts = vec![];
    for it in p.into_inner() {
        if it.as_rule() == Rule::stmt_list {
            stmts = build_stmt_list(it)?;
        }
    }
    Ok(Stmt::Compound(stmts))
}

fn build_stmt_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<Stmt>, String> {
    let mut v = vec![];
    for s in p.into_inner() {
        v.push(build_stmt(s)?);
    }
    Ok(v)
}

fn build_stmt(p: pest::iterators::Pair<Rule>) -> Result<Stmt, String> {
    match p.as_rule() {
        Rule::compound_stmt => build_compound(p),
        Rule::assign_stmt => {
            let mut it = p.into_inner();
            let lv = build_lvalue(it.next().unwrap())?;
            let rhs = build_expr(it.next().unwrap())?;
            Ok(Stmt::Assign(lv, rhs))
        }
        Rule::read_stmt => {
            let lvs = build_lvalue_list(p.into_inner().next().unwrap())?;
            Ok(Stmt::Read(lvs))
        }
        Rule::readln_stmt => Ok(Stmt::ReadLn),
        Rule::for_stmt => {
            let mut it = p.into_inner();
            let var = it.next().unwrap().as_str().to_string();
            let init = build_expr(it.next().unwrap())?;
            let dir = it.next().unwrap().as_str().to_string();
            let limit = build_expr(it.next().unwrap())?;
            let body = build_stmt(it.next().unwrap())?;
            Ok(Stmt::For {
                var,
                init,
                limit,
                downto: dir == "downto",
                body: Box::new(body),
            })
        }
        Rule::case_stmt => {
            let mut it = p.into_inner();
            let expr = build_expr(it.next().unwrap())?;
            let mut arms = vec![];
            let mut else_stmt = None;
            for x in it {
                match x.as_rule() {
                    Rule::case_arm => {
                        let mut jt = x.into_inner();
                        let c = build_const_expr(jt.next().unwrap())?;
                        let s = build_stmt(jt.next().unwrap())?;
                        arms.push((c, s));
                    }
                    _ => else_stmt = Some(Box::new(build_stmt(x)?)),
                }
            }
            Ok(Stmt::Case {
                expr,
                arms,
                else_stmt,
            })
        }
        Rule::proc_call_stmt => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                vec![]
            };
            Ok(Stmt::ProcCall(name, args))
        }
        Rule::if_stmt => {
            let mut it = p.into_inner();
            let cond = build_expr(it.next().unwrap())?;
            let then_s = build_stmt(it.next().unwrap())?;
            let else_s = if let Some(e) = it.next() {
                Some(Box::new(build_stmt(e)?))
            } else {
                None
            };
            Ok(Stmt::If(cond, Box::new(then_s), else_s))
        }
        Rule::while_stmt => {
            let mut it = p.into_inner();
            let cond = build_expr(it.next().unwrap())?;
            let body = build_stmt(it.next().unwrap())?;
            Ok(Stmt::While(cond, Box::new(body)))
        }
        Rule::repeat_stmt => {
            let mut stmts = vec![];
            let mut cond: Option<Expr> = None;
            for x in p.into_inner() {
                if x.as_rule() == Rule::stmt_list {
                    stmts = build_stmt_list(x)?;
                } else {
                    cond = Some(build_expr(x)?);
                }
            }
            Ok(Stmt::Repeat(stmts, cond.ok_or("repeat missing cond")?))
        }
        Rule::write_stmt => {
            let mut it = p.into_inner();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                vec![]
            };
            Ok(Stmt::Write(args))
        }
        Rule::writeln_stmt => {
            let mut it = p.into_inner();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                vec![]
            };
            Ok(Stmt::WriteLn(args))
        }
        Rule::empty_stmt => Ok(Stmt::Empty),
        _ => Err(format!("unexpected stmt: {:?}", p.as_rule())),
    }
}

fn build_lvalue_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<LValue>, String> {
    let mut v = vec![];
    for x in p.into_inner() {
        v.push(build_lvalue(x)?);
    }
    Ok(v)
}

fn build_expr_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<Expr>, String> {
    let mut v = vec![];
    for x in p.into_inner() {
        v.push(build_expr(x)?);
    }
    Ok(v)
}

fn build_lvalue(p: pest::iterators::Pair<Rule>) -> Result<LValue, String> {
    let mut it = p.into_inner();
    let base = it.next().unwrap().as_str().to_string();
    let mut sels = vec![];
    for s in it {
        match s.as_rule() {
            Rule::field_access => {
                let mut jt = s.into_inner();
                let name = jt.next().unwrap().as_str().to_string();
                sels.push(Selector::Field(name));
            }
            Rule::index_access => {
                let mut idxs = vec![];
                for ie in s.into_inner() {
                    idxs.push(build_expr(ie)?);
                }
                if idxs.is_empty() || idxs.len() > 3 {
                    return Err("index dimensions must be 1..3".into());
                }
                sels.push(Selector::Index(idxs));
            }
            _ => return Err(format!("unexpected selector: {:?}", s.as_rule())),
        }
    }
    Ok(LValue { base, sels })
}

fn build_expr(p: pest::iterators::Pair<Rule>) -> Result<Expr, String> {
    match p.as_rule() {
        Rule::expr => build_expr(p.into_inner().next().unwrap()),
        Rule::rel => {
            let mut it = p.into_inner();
            let left = build_expr(it.next().unwrap())?;
            if let Some(op) = it.next() {
                let right = build_expr(it.next().unwrap())?;
                Ok(Expr::Binary(
                    Box::new(left),
                    parse_relop(op.as_str())?,
                    Box::new(right),
                ))
            } else {
                Ok(left)
            }
        }
        Rule::add => {
            let mut it = p.into_inner();
            let mut e = build_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_expr(it.next().unwrap())?;
                let bop = match op.as_str() {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    _ => return Err("unknown add op".into()),
                };
                e = Expr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::mul => {
            let mut it = p.into_inner();
            let mut e = build_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_expr(it.next().unwrap())?;
                let bop = match op.as_str() {
                    "*" => BinOp::Mul,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    _ => return Err("unknown mul op".into()),
                };
                e = Expr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::unary => {
            let mut it = p.clone().into_inner();
            let first = it.next().unwrap();
            if first.as_rule() == Rule::unary_op {
                let op = match first.as_str() {
                    "-" => UnOp::Neg,
                    "not" => UnOp::Not,
                    _ => return Err("unknown unary op".into()),
                };
                let inner = build_expr(it.next().unwrap())?;
                Ok(Expr::Unary(op, Box::new(inner)))
            } else {
                build_expr(first)
            }
        }
        Rule::primary => build_expr(p.into_inner().next().unwrap()),
        Rule::bool_lit => Ok(Expr::Bool(p.as_str() == "true")),
        Rule::number => Ok(Expr::Int(parse_int_literal(p.as_str())?)),
        Rule::string_lit => {
            let s = decode_pascal_string(p.as_str())?;
            if s.chars().count() == 1 {
                Ok(Expr::Char(s.chars().next().unwrap() as u32))
            } else {
                Ok(Expr::Str(s))
            }
        }
        Rule::char_code => {
            let mut it = p.into_inner();
            let n = it.next().unwrap().as_str().parse::<u32>().map_err(|e| e.to_string())?;
            if n > 0x10FFFF {
                return Err("char code > 0x10FFFF".into());
            }
            Ok(Expr::Char(n))
        }
        Rule::func_call => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_expr_list(list)?
            } else {
                vec![]
            };
            Ok(Expr::Call(name, args))
        }
        Rule::ident => Ok(Expr::Var(p.as_str().to_string())),
        Rule::lvalue => {
            // allow lvalue in expr context: treat as rvalue (load), field chain handled by Expr::Field
            let lv = build_lvalue(p)?;
            let mut e = Expr::Var(lv.base);
            for sel in lv.sels {
                e = match sel {
                    Selector::Field(f) => Expr::Field(Box::new(e), f),
                    Selector::Index(ixs) => {
                        let mut acc = e;
                        for ix in ixs {
                            acc = Expr::Index(Box::new(acc), Box::new(ix));
                        }
                        acc
                    }
                };
            }
            Ok(e)
        }
        _ => Err(format!("unexpected expr node: {:?}", p.as_rule())),
    }
}

fn parse_relop(s: &str) -> Result<BinOp, String> {
    match s {
        "=" => Ok(BinOp::Eq),
        "<>" => Ok(BinOp::Ne),
        "<" => Ok(BinOp::Lt),
        "<=" => Ok(BinOp::Le),
        ">" => Ok(BinOp::Gt),
        ">=" => Ok(BinOp::Ge),
        _ => Err(format!("unknown relop: {s}")),
    }
}

fn build_const_expr(p: pest::iterators::Pair<Rule>) -> Result<ConstExpr, String> {
    match p.as_rule() {
        Rule::const_expr => build_const_expr(p.into_inner().next().unwrap()),
        Rule::const_rel => {
            let mut it = p.into_inner();
            let left = build_const_expr(it.next().unwrap())?;
            if let Some(op) = it.next() {
                let right = build_const_expr(it.next().unwrap())?;
                Ok(ConstExpr::Binary(
                    Box::new(left),
                    parse_relop(op.as_str())?,
                    Box::new(right),
                ))
            } else {
                Ok(left)
            }
        }
        Rule::const_add => {
            let mut it = p.into_inner();
            let mut e = build_const_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_const_expr(it.next().unwrap())?;
                let bop = match op.as_str() {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    _ => return Err("unknown const add op".into()),
                };
                e = ConstExpr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::const_mul => {
            let mut it = p.into_inner();
            let mut e = build_const_expr(it.next().unwrap())?;
            while let Some(op) = it.next() {
                let rhs = build_const_expr(it.next().unwrap())?;
                let bop = match op.as_str() {
                    "*" => BinOp::Mul,
                    "div" => BinOp::Div,
                    "mod" => BinOp::Mod,
                    _ => return Err("unknown const mul op".into()),
                };
                e = ConstExpr::Binary(Box::new(e), bop, Box::new(rhs));
            }
            Ok(e)
        }
        Rule::const_unary => {
            let mut it = p.clone().into_inner();
            let first = it.next().unwrap();
            if first.as_rule() == Rule::unary_op {
                let op = match first.as_str() {
                    "-" => UnOp::Neg,
                    "not" => UnOp::Not,
                    _ => return Err("unknown const unary op".into()),
                };
                let inner = build_const_expr(it.next().unwrap())?;
                Ok(ConstExpr::Unary(op, Box::new(inner)))
            } else {
                build_const_expr(first)
            }
        }
        Rule::const_primary => build_const_expr(p.into_inner().next().unwrap()),
        Rule::bool_lit => Ok(ConstExpr::Bool(p.as_str() == "true")),
        Rule::number => Ok(ConstExpr::Int(parse_int_literal(p.as_str())?)),
        Rule::string_lit => {
            let s = decode_pascal_string(p.as_str())?;
            if s.chars().count() != 1 {
                return Err("string literal is not allowed in const expr".into());
            }
            Ok(ConstExpr::Char(s.chars().next().unwrap() as u32))
        }
        Rule::char_code => {
            let mut it = p.into_inner();
            let n = it.next().unwrap().as_str().parse::<u32>().map_err(|e| e.to_string())?;
            if n > 0x10FFFF {
                return Err("char code > 0x10FFFF".into());
            }
            Ok(ConstExpr::Char(n))
        }
        Rule::const_func_call => {
            let mut it = p.into_inner();
            let name = it.next().unwrap().as_str().to_string();
            let args = if let Some(list) = it.next() {
                build_const_expr_list(list)?
            } else {
                vec![]
            };
            Ok(ConstExpr::Call(name, args))
        }
        Rule::ident => Ok(ConstExpr::Const(p.as_str().to_string())),
        _ => Err(format!("unexpected const expr node: {:?}", p.as_rule())),
    }
}

fn build_const_expr_list(p: pest::iterators::Pair<Rule>) -> Result<Vec<ConstExpr>, String> {
    let mut v = vec![];
    for x in p.into_inner() {
        v.push(build_const_expr(x)?);
    }
    Ok(v)
}

fn decode_pascal_string(src: &str) -> Result<String, String> {
    if !src.starts_with('\'') || !src.ends_with('\'') || src.len() < 2 {
        return Err("invalid string literal".into());
    }
    let inner = &src[1..src.len() - 1];
    let mut out = String::new();
    let mut it = inner.chars().peekable();
    while let Some(ch) = it.next() {
        if ch == '\'' {
            if it.peek() == Some(&'\'') {
                it.next();
                out.push('\'');
            } else {
                return Err("invalid quote in string literal".into());
            }
        } else {
            out.push(ch);
        }
    }
    Ok(out)
}

fn parse_int_literal(s: &str) -> Result<i32, String> {
    if let Some(rest) = s.strip_prefix("0x") {
        let u = i64::from_str_radix(rest, 16).map_err(|e| e.to_string())?;
        return i32::try_from(u).map_err(|_| "hex literal out of i32 range".to_string());
    }
    if let Some(rest) = s.strip_prefix('$') {
        let u = i64::from_str_radix(rest, 16).map_err(|e| e.to_string())?;
        return i32::try_from(u).map_err(|_| "hex literal out of i32 range".to_string());
    }
    s.parse::<i32>().map_err(|e| e.to_string())
}

fn preprocess_includes(src: &str, base_dir: &Path) -> Result<String, String> {
    let mut stack = HashSet::new();
    expand_includes(src, base_dir, &mut stack)
}

fn expand_includes(
    src: &str,
    base_dir: &Path,
    stack: &mut HashSet<PathBuf>,
) -> Result<String, String> {
    let mut out = String::with_capacity(src.len());
    let mut pos = 0usize;
    while let Some(rel) = src[pos..].find("(*") {
        let start = pos + rel;
        out.push_str(&src[pos..start]);
        let after = start + 2;
        let Some(end_rel) = src[after..].find("*)") else {
            out.push_str(&src[start..]);
            return Ok(out);
        };
        let end = after + end_rel;
        let body = &src[after..end];
        if let Some(path) = parse_include_directive(body) {
            let full = base_dir.join(path);
            let canon = full.canonicalize().unwrap_or(full.clone());
            if stack.contains(&canon) {
                return Err(format!("include cycle detected: {}", canon.display()));
            }
            let text = std::fs::read_to_string(&full)
                .map_err(|e| format!("include read failed ({}): {e}", full.display()))?;
            stack.insert(canon.clone());
            let parent = full.parent().unwrap_or(base_dir);
            let expanded = expand_includes(&text, parent, stack)?;
            stack.remove(&canon);
            out.push_str(&expanded);
        } else {
            out.push_str(&src[start..end + 2]);
        }
        pos = end + 2;
    }
    out.push_str(&src[pos..]);
    Ok(out)
}

fn parse_include_directive(body: &str) -> Option<String> {
    let t = body.trim();
    if t.len() < 2 {
        return None;
    }
    let u = t.to_ascii_uppercase();
    if !u.starts_with("$I") {
        return None;
    }
    let mut rest = t[2..].trim();
    if rest.is_empty() {
        return None;
    }
    if (rest.starts_with('\'') && rest.ends_with('\'')) || (rest.starts_with('"') && rest.ends_with('"')) {
        if rest.len() >= 2 {
            rest = &rest[1..rest.len() - 1];
        }
    }
    if rest.is_empty() {
        return None;
    }
    Some(rest.to_string())
}
