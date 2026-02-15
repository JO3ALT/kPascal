use std::collections::{HashMap, HashSet};

use crate::ast::*;

#[derive(Debug, Clone)]
pub enum TypeInfo {
    Basic(BasicType),
    Record(RecordInfo),
    Array(ArrayInfo),
}

#[derive(Debug, Clone)]
pub struct RecordInfo {
    pub fields: HashMap<String, FieldInfo>,
    #[allow(dead_code)]
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub offset_bytes: u32,
    pub ty: TypeInfo,
}

#[derive(Debug, Clone)]
pub struct ArrayInfo {
    pub len: u32,
    pub elem_ty: Box<TypeInfo>,
    pub elem_size_bytes: u32,
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct ParamSig {
    pub ty: TypeInfo,
    pub by_ref: bool,
}

#[derive(Debug, Clone)]
pub struct RoutineSig {
    pub params: Vec<ParamSig>,
    pub ret: Option<TypeInfo>,
}

#[derive(Debug, Clone)]
pub struct Env {
    pub consts: HashMap<String, ConstVal>,
    pub types: HashMap<String, TypeInfo>,
    pub vars: HashMap<String, TypeInfo>,
    // Key is scoped name, e.g. "program::Outer::Inner"
    pub routines: HashMap<String, RoutineSig>,
}

#[derive(Debug, Clone)]
pub enum ConstVal {
    I32(i32),
    U32(u32),
    Bool(bool),
}

impl Env {
    pub fn new() -> Self {
        let mut types = HashMap::new();
        types.insert("integer".to_string(), TypeInfo::Basic(BasicType::Integer));
        types.insert("boolean".to_string(), TypeInfo::Basic(BasicType::Boolean));
        types.insert("char".to_string(), TypeInfo::Basic(BasicType::Char));
        Self {
            consts: HashMap::new(),
            types,
            vars: HashMap::new(),
            routines: HashMap::new(),
        }
    }
}

fn tyref_to_info(env: &Env, tr: &TypeRef) -> Result<TypeInfo, String> {
    match tr {
        TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
        TypeRef::Named(n) => env
            .types
            .get(n)
            .cloned()
            .ok_or_else(|| format!("unknown type: {n}")),
    }
}

pub fn build_env(prog: &Program) -> Result<Env, String> {
    let mut env = Env::new();
    collect_block_decls(&mut env, &prog.block, true, "program")?;
    Ok(env)
}

fn collect_block_decls(
    env: &mut Env,
    block: &Block,
    collect_vars: bool,
    scope: &str,
) -> Result<(), String> {
    for td in &block.types {
        if env.types.contains_key(&td.name) {
            return Err(format!("type redefined in {scope}: {}", td.name));
        }
        env.types
            .insert(td.name.clone(), TypeInfo::Basic(BasicType::Integer));
    }
    for td in &block.types {
        let info = match &td.spec {
            TypeSpec::Basic(b) => TypeInfo::Basic(b.clone()),
            TypeSpec::Alias(r) => tyref_to_info(env, r)?,
            TypeSpec::Record(fields) => {
                let mut ftab = HashMap::new();
                let mut offset = 0u32;
                for f in fields {
                    let fty = tyref_to_info(env, &f.ty)?;
                    let finfo = FieldInfo {
                        offset_bytes: offset,
                        ty: fty,
                    };
                    if ftab.insert(f.name.clone(), finfo).is_some() {
                        return Err(format!("duplicate field name in {scope}: {}", f.name));
                    }
                    offset += 4;
                }
                TypeInfo::Record(RecordInfo {
                    fields: ftab,
                    size_bytes: offset,
                })
            }
            TypeSpec::Array { lens, elem } => {
                let mut dims = vec![];
                for len in lens {
                    let lv = eval_const(env, len)?;
                    let n = match lv {
                        ConstVal::I32(i) if i > 0 => i as u32,
                        _ => {
                            return Err(format!(
                                "array length in {scope} must be positive integer constant"
                            ))
                        }
                    };
                    dims.push(n);
                }
                let mut t = tyref_to_info(env, elem)?;
                for &n in dims.iter().rev() {
                    let esz = sizeof_type(&t)?;
                    let sz = n
                        .checked_mul(esz)
                        .ok_or_else(|| format!("array size overflow in {scope}"))?;
                    t = TypeInfo::Array(ArrayInfo {
                        len: n,
                        elem_ty: Box::new(t),
                        elem_size_bytes: esz,
                        size_bytes: sz,
                    });
                }
                t
            }
        };
        env.types.insert(td.name.clone(), info);
    }

    for cd in &block.consts {
        if env.consts.contains_key(&cd.name) {
            return Err(format!("const redefined in {scope}: {}", cd.name));
        }
        let v = eval_const(env, &cd.expr)?;
        env.consts.insert(cd.name.clone(), v);
    }

    if collect_vars {
        for vd in &block.vars {
            if env.vars.contains_key(&vd.name) {
                return Err(format!("var redefined in {scope}: {}", vd.name));
            }
            let t = tyref_to_info(env, &vd.ty)?;
            env.vars.insert(vd.name.clone(), t);
        }
    }

    let mut local_routine_names = HashSet::new();
    for r in &block.routines {
        let (name, params, ret_ty) = match r {
            RoutineDecl::Procedure(p) => (&p.name, &p.params, None),
            RoutineDecl::Function(f) => (&f.name, &f.params, Some(&f.ret_ty)),
        };
        if !local_routine_names.insert(name.clone()) {
            return Err(format!("routine redefined in {scope}: {name}"));
        }
        let scoped = format!("{scope}::{name}");
        let mut ptab = vec![];
        for p in params {
            ptab.push(ParamSig {
                ty: tyref_to_info(env, &p.ty)?,
                by_ref: p.by_ref,
            });
        }
        let ret = if let Some(rt) = ret_ty {
            Some(tyref_to_info(env, rt)?)
        } else {
            None
        };
        env.routines.insert(scoped, RoutineSig { params: ptab, ret });
    }

    for r in &block.routines {
        match r {
            RoutineDecl::Procedure(p) => {
                let child = format!("{scope}::{}", p.name);
                collect_block_decls(env, &p.block, false, &child)?;
            }
            RoutineDecl::Function(f) => {
                let child = format!("{scope}::{}", f.name);
                collect_block_decls(env, &f.block, false, &child)?;
            }
        }
    }

    Ok(())
}

#[allow(dead_code)]
pub fn type_of_expr(env: &Env, e: &Expr) -> Result<TypeInfo, String> {
    type_of_expr_scoped(env, &env.vars, &HashMap::new(), e)
}

pub fn type_of_expr_scoped(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    e: &Expr,
) -> Result<TypeInfo, String> {
    match e {
        Expr::Int(_) => Ok(TypeInfo::Basic(BasicType::Integer)),
        Expr::Char(_) => Ok(TypeInfo::Basic(BasicType::Char)),
        Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
        Expr::Var(n) => {
            if let Some(t) = vars.get(n) {
                Ok(t.clone())
            } else if let Some(c) = env.consts.get(n) {
                Ok(match c {
                    ConstVal::I32(_) => TypeInfo::Basic(BasicType::Integer),
                    ConstVal::U32(_) => TypeInfo::Basic(BasicType::Char),
                    ConstVal::Bool(_) => TypeInfo::Basic(BasicType::Boolean),
                })
            } else {
                Err(format!("unknown identifier: {n}"))
            }
        }
        Expr::Call(name, args) => {
            if let Some(t) = builtin_expr_type(env, vars, visible_routines, name, args)? {
                return Ok(t);
            }
            let key = visible_routines
                .get(name)
                .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
            let sig = env
                .routines
                .get(key)
                .ok_or_else(|| format!("internal: missing routine signature for {key}"))?;
            let ret = sig
                .ret
                .clone()
                .ok_or_else(|| format!("procedure used as expression: {name}"))?;
            check_call_args_scoped(env, vars, visible_routines, name, sig, args)?;
            Ok(ret)
        }
        Expr::Field(base, fname) => {
            let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
            match bt {
                TypeInfo::Record(r) => r
                    .fields
                    .get(fname)
                    .map(|fi| fi.ty.clone())
                    .ok_or_else(|| format!("unknown field {fname}")),
                _ => Err("field access on non-record".into()),
            }
        }
        Expr::Index(base, idx) => {
            let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
            let it = type_of_expr_scoped(env, vars, visible_routines, idx)?;
            expect_basic(&it, BasicType::Integer, "array index")?;
            match bt {
                TypeInfo::Array(a) => Ok((*a.elem_ty).clone()),
                _ => Err("index access on non-array".into()),
            }
        }
        Expr::Unary(op, inner) => {
            let it = type_of_expr_scoped(env, vars, visible_routines, inner)?;
            match op {
                UnOp::Neg => {
                    expect_basic(&it, BasicType::Integer, "NEG")?;
                    Ok(TypeInfo::Basic(BasicType::Integer))
                }
                UnOp::Not => {
                    expect_basic(&it, BasicType::Boolean, "NOT")?;
                    Ok(TypeInfo::Basic(BasicType::Boolean))
                }
            }
        }
        Expr::Binary(a, op, b) => {
            let ta = type_of_expr_scoped(env, vars, visible_routines, a)?;
            let tb = type_of_expr_scoped(env, vars, visible_routines, b)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => {
                    expect_basic(&ta, BasicType::Integer, "arithmetic lhs")?;
                    expect_basic(&tb, BasicType::Integer, "arithmetic rhs")?;
                    Ok(TypeInfo::Basic(BasicType::Integer))
                }
                BinOp::Eq | BinOp::Ne => {
                    if !same_type(&ta, &tb) {
                        return Err("type mismatch in equality comparison".into());
                    }
                    Ok(TypeInfo::Basic(BasicType::Boolean))
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    if !same_type(&ta, &tb) {
                        return Err("type mismatch in order comparison".into());
                    }
                    match ta {
                        TypeInfo::Basic(BasicType::Integer) | TypeInfo::Basic(BasicType::Char) => {
                            Ok(TypeInfo::Basic(BasicType::Boolean))
                        }
                        _ => Err("order comparison requires integer or char".into()),
                    }
                }
            }
        }
    }
}

fn check_call_args_scoped(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    sig: &RoutineSig,
    args: &[Expr],
) -> Result<(), String> {
    if sig.params.len() != args.len() {
        return Err(format!(
            "argument count mismatch for {name}: expected {}, got {}",
            sig.params.len(),
            args.len()
        ));
    }
    for (idx, (p, a)) in sig.params.iter().zip(args).enumerate() {
        let arg_no = idx + 1;
        if p.by_ref && expr_to_lvalue(a).is_none() {
            return Err(format!(
                "argument #{arg_no} in call to {name} must be lvalue for var parameter"
            ));
        }
        let at = type_of_expr_scoped(env, vars, visible_routines, a)?;
        if !same_type(&p.ty, &at) {
            return Err(format!(
                "argument #{arg_no} type mismatch in call to {name}: expected {}, got {}",
                type_desc(&p.ty),
                type_desc(&at)
            ));
        }
    }
    Ok(())
}

fn sizeof_type(t: &TypeInfo) -> Result<u32, String> {
    match t {
        TypeInfo::Basic(_) => Ok(4),
        TypeInfo::Record(r) => Ok(r.size_bytes),
        TypeInfo::Array(a) => Ok(a.size_bytes),
    }
}

pub fn eval_const(env: &Env, e: &ConstExpr) -> Result<ConstVal, String> {
    match e {
        ConstExpr::Int(i) => Ok(ConstVal::I32(*i)),
        ConstExpr::Char(u) => Ok(ConstVal::U32(*u)),
        ConstExpr::Const(n) => env
            .consts
            .get(n)
            .cloned()
            .ok_or_else(|| format!("unknown const: {n}")),
        ConstExpr::Call(name, args) => {
            let u = name.to_ascii_lowercase();
            match u.as_str() {
                "ord" => {
                    if args.len() != 1 {
                        return Err("Ord requires 1 argument in const expr".into());
                    }
                    match eval_const(env, &args[0])? {
                        ConstVal::I32(i) => Ok(ConstVal::I32(i)),
                        ConstVal::U32(u) => Ok(ConstVal::I32(u as i32)),
                        ConstVal::Bool(b) => Ok(ConstVal::I32(if b { 1 } else { 0 })),
                    }
                }
                "chr" => {
                    if args.len() != 1 {
                        return Err("Chr requires 1 argument in const expr".into());
                    }
                    let i = to_i32(eval_const(env, &args[0])?)?;
                    if i < 0 {
                        return Err("Chr const argument must be non-negative".into());
                    }
                    Ok(ConstVal::U32(i as u32))
                }
                _ => Err(format!("unsupported const function: {name}")),
            }
        }
        ConstExpr::Unary(UnOp::Neg, inner) => match eval_const(env, inner)? {
            ConstVal::I32(i) => Ok(ConstVal::I32(-i)),
            _ => Err("NEG on non-integer const".into()),
        },
        ConstExpr::Unary(UnOp::Not, inner) => match eval_const(env, inner)? {
            ConstVal::Bool(b) => Ok(ConstVal::Bool(!b)),
            ConstVal::I32(i) => Ok(ConstVal::Bool(i == 0)),
            _ => Err("NOT on unsupported const".into()),
        },
        ConstExpr::Binary(a, op, b) => {
            let av = eval_const(env, a)?;
            let bv = eval_const(env, b)?;
            use BinOp::*;
            match op {
                Add | Sub | Mul => {
                    let ai = to_i32(av)?;
                    let bi = to_i32(bv)?;
                    Ok(ConstVal::I32(match op {
                        Add => ai + bi,
                        Sub => ai - bi,
                        Mul => ai * bi,
                        _ => unreachable!(),
                    }))
                }
                Eq | Ne | Lt | Le | Gt | Ge => {
                    let ai = to_i32(av)?;
                    let bi = to_i32(bv)?;
                    let r = match op {
                        Eq => ai == bi,
                        Ne => ai != bi,
                        Lt => ai < bi,
                        Le => ai <= bi,
                        Gt => ai > bi,
                        Ge => ai >= bi,
                        _ => unreachable!(),
                    };
                    Ok(ConstVal::Bool(r))
                }
            }
        }
    }
}

fn to_i32(v: ConstVal) -> Result<i32, String> {
    match v {
        ConstVal::I32(i) => Ok(i),
        ConstVal::Bool(b) => Ok(if b { 1 } else { 0 }),
        ConstVal::U32(u) => Ok(i32::try_from(u).map_err(|_| "u32 too large for i32".to_string())?),
    }
}

#[allow(dead_code)]
pub fn resolve_lvalue_addr(env: &Env, lv: &LValue) -> Result<(String, u32, TypeInfo), String> {
    let ty = resolve_lvalue_type_scoped(env, &env.vars, &HashMap::new(), lv)?;
    Ok((lv.base.clone(), 0, ty))
}

#[allow(dead_code)]
pub fn resolve_lvalue_addr_with_vars(
    vars: &HashMap<String, TypeInfo>,
    lv: &LValue,
) -> Result<(String, u32, TypeInfo), String> {
    let t = vars
        .get(&lv.base)
        .cloned()
        .ok_or_else(|| format!("unknown var: {}", lv.base))?;
    if lv.sels.is_empty() {
        return Ok((lv.base.clone(), 0, t));
    }
    Err("resolve_lvalue_addr_with_vars does not support selectors; use scoped checker".into())
}

fn resolve_lvalue_type_scoped(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    lv: &LValue,
) -> Result<TypeInfo, String> {
    let mut t = vars
        .get(&lv.base)
        .cloned()
        .ok_or_else(|| format!("unknown var: {}", lv.base))?;
    for sel in &lv.sels {
        match sel {
            Selector::Field(f) => match t {
                TypeInfo::Record(ref r) => {
                    let fi = r
                        .fields
                        .get(f)
                        .ok_or_else(|| format!("unknown field: {f}"))?;
                    t = fi.ty.clone();
                }
                _ => return Err("field on non-record lvalue".into()),
            },
            Selector::Index(idxs) => {
                for ix in idxs {
                    let it = type_of_expr_scoped(env, vars, visible_routines, ix)?;
                    expect_basic(&it, BasicType::Integer, "array index")?;
                    match t {
                        TypeInfo::Array(ref a) => {
                            t = (*a.elem_ty).clone();
                        }
                        _ => return Err("index on non-array lvalue".into()),
                    }
                }
            }
        }
    }
    Ok(t)
}

pub fn expr_to_lvalue(e: &Expr) -> Option<LValue> {
    match e {
        Expr::Var(n) => Some(LValue {
            base: n.clone(),
            sels: vec![],
        }),
        Expr::Field(_, _) | Expr::Index(_, _) => {
            let mut sels = vec![];
            let mut cur = e;
            loop {
                match cur {
                    Expr::Field(inner, f) => {
                        sels.push(Selector::Field(f.clone()));
                        cur = inner;
                    }
                    Expr::Index(inner, ix) => {
                        sels.push(Selector::Index(vec![(**ix).clone()]));
                        cur = inner;
                    }
                    _ => break,
                }
            }
            if let Expr::Var(base) = cur {
                sels.reverse();
                Some(LValue {
                    base: base.clone(),
                    sels,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn check_program(env: &Env, prog: &Program) -> Result<(), String> {
    check_block(env, &prog.block, &HashMap::new(), &HashMap::new(), "program")
}

fn check_block(
    env: &Env,
    block: &Block,
    outer_vars: &HashMap<String, TypeInfo>,
    outer_routines: &HashMap<String, String>,
    scope: &str,
) -> Result<(), String> {
    let mut vars = outer_vars.clone();
    for v in &block.vars {
        if vars.contains_key(&v.name) {
            return Err(format!(
                "name conflict in {scope}: local variable '{}' shadows an outer name (shadowing is not allowed)",
                v.name
            ));
        }
        vars.insert(v.name.clone(), tyref_to_info(env, &v.ty)?);
    }

    let mut visible_routines = outer_routines.clone();
    let mut local_names = HashSet::new();
    for r in &block.routines {
        let name = match r {
            RoutineDecl::Procedure(p) => &p.name,
            RoutineDecl::Function(f) => &f.name,
        };
        if !local_names.insert(name.clone()) {
            return Err(format!("routine redefined in {scope}: {name}"));
        }
        let key = format!("{scope}::{name}");
        visible_routines.insert(name.clone(), key);
    }

    check_stmt_with_vars(env, &vars, &visible_routines, &block.body)?;

    for r in &block.routines {
        match r {
            RoutineDecl::Procedure(p) => {
                let mut rvars = vars.clone();
                for prm in &p.params {
                    if rvars.contains_key(&prm.name) {
                        return Err(format!(
                            "name conflict in procedure {}: parameter '{}' duplicates or shadows an existing name",
                            p.name, prm.name
                        ));
                    }
                    rvars.insert(prm.name.clone(), tyref_to_info(env, &prm.ty)?);
                }
                let child = format!("{scope}::{}", p.name);
                check_block(env, &p.block, &rvars, &visible_routines, &child)?;
            }
            RoutineDecl::Function(f) => {
                let mut rvars = vars.clone();
                for prm in &f.params {
                    if rvars.contains_key(&prm.name) {
                        return Err(format!(
                            "name conflict in function {}: parameter '{}' duplicates or shadows an existing name",
                            f.name, prm.name
                        ));
                    }
                    rvars.insert(prm.name.clone(), tyref_to_info(env, &prm.ty)?);
                }
                rvars.insert(f.name.clone(), tyref_to_info(env, &f.ret_ty)?);
                let child = format!("{scope}::{}", f.name);
                check_block(env, &f.block, &rvars, &visible_routines, &child)?;
            }
        }
    }

    Ok(())
}

fn check_stmt_with_vars(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    s: &Stmt,
) -> Result<(), String> {
    match s {
        Stmt::Empty => Ok(()),
        Stmt::Compound(v) => {
            for st in v {
                check_stmt_with_vars(env, vars, visible_routines, st)?;
            }
            Ok(())
        }
        Stmt::Assign(lv, rhs) => {
            let lt = resolve_lvalue_type_scoped(env, vars, visible_routines, lv)?;
            if let Expr::Str(_) = rhs {
                if char_array_len(&lt).is_none() {
                    return Err("string literal assignment requires array of char lhs".into());
                }
                return Ok(());
            }
            let rt = type_of_expr_scoped(env, vars, visible_routines, rhs)?;
            if !same_type(&lt, &rt) {
                return Err("type mismatch in assignment".into());
            }
            if !is_basic_type(&lt) && expr_to_lvalue(rhs).is_none() {
                return Err("aggregate assignment requires lvalue rhs".into());
            }
            Ok(())
        }
        Stmt::Read(lvs) => {
            for lv in lvs {
                let t = resolve_lvalue_type_scoped(env, vars, visible_routines, lv)?;
                if !is_basic_type(&t) {
                    return Err("Read on aggregate type is not supported".into());
                }
            }
            Ok(())
        }
        Stmt::ReadLn => Ok(()),
        Stmt::For {
            var,
            init,
            limit,
            downto: _,
            body,
        } => {
            let vt = vars
                .get(var)
                .ok_or_else(|| format!("unknown var: {var}"))?;
            expect_basic(vt, BasicType::Integer, "for variable")?;
            expect_basic(
                &type_of_expr_scoped(env, vars, visible_routines, init)?,
                BasicType::Integer,
                "for init",
            )?;
            expect_basic(
                &type_of_expr_scoped(env, vars, visible_routines, limit)?,
                BasicType::Integer,
                "for limit",
            )?;
            check_stmt_with_vars(env, vars, visible_routines, body)
        }
        Stmt::Case {
            expr,
            arms,
            else_stmt,
        } => {
            let et = type_of_expr_scoped(env, vars, visible_routines, expr)?;
            let mut used = HashSet::new();
            for (ce, st) in arms {
                let cv = eval_const(env, ce)?;
                let token = match &cv {
                    ConstVal::I32(i) => format!("I:{i}"),
                    ConstVal::U32(u) => format!("U:{u}"),
                    ConstVal::Bool(b) => format!("B:{b}"),
                };
                if !used.insert(token) {
                    return Err("duplicate case label".into());
                }
                let ct = const_type_from_val(cv);
                if !same_type(&et, &ct) {
                    return Err("case arm constant type mismatch".into());
                }
                check_stmt_with_vars(env, vars, visible_routines, st)?;
            }
            if let Some(es) = else_stmt {
                check_stmt_with_vars(env, vars, visible_routines, es)?;
            }
            Ok(())
        }
        Stmt::ProcCall(name, args) => {
            if name == "ReadArr" || name == "WriteArr" {
                return check_builtin_array_io(env, vars, visible_routines, name, args);
            }
            if name == "ReadStr" || name == "WriteStr" {
                return check_builtin_str_io(env, vars, visible_routines, name, args);
            }
            if name == "WriteHex" {
                return check_builtin_writehex(env, vars, visible_routines, args);
            }
            let key = visible_routines
                .get(name)
                .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
            let sig = env
                .routines
                .get(key)
                .ok_or_else(|| format!("internal: missing routine signature for {key}"))?;
            if sig.ret.is_some() {
                return Err(format!("function used as procedure: {name}"));
            }
            check_call_args_scoped(env, vars, visible_routines, name, sig, args)
        }
        Stmt::If(cond, then_s, else_s) => {
            expect_basic(
                &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                BasicType::Boolean,
                "if condition",
            )?;
            check_stmt_with_vars(env, vars, visible_routines, then_s)?;
            if let Some(es) = else_s {
                check_stmt_with_vars(env, vars, visible_routines, es)?;
            }
            Ok(())
        }
        Stmt::While(cond, body) => {
            expect_basic(
                &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                BasicType::Boolean,
                "while condition",
            )?;
            check_stmt_with_vars(env, vars, visible_routines, body)
        }
        Stmt::Repeat(stmts, cond) => {
            for st in stmts {
                check_stmt_with_vars(env, vars, visible_routines, st)?;
            }
            expect_basic(
                &type_of_expr_scoped(env, vars, visible_routines, cond)?,
                BasicType::Boolean,
                "repeat condition",
            )
        }
        Stmt::Write(args) | Stmt::WriteLn(args) => {
            for e in args {
                match e {
                    Expr::Str(_) => {}
                    _ => {
                        let t = type_of_expr_scoped(env, vars, visible_routines, e)?;
                        if !is_basic_type(&t) {
                            return Err("Write/WriteLn supports only scalar values".into());
                        }
                    }
                }
            }
            Ok(())
        }
    }
}

fn builtin_expr_type(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    args: &[Expr],
) -> Result<Option<TypeInfo>, String> {
    let n = name.to_ascii_lowercase();
    match n.as_str() {
        "ord" => {
            if args.len() != 1 {
                return Err("Ord requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            match t {
                TypeInfo::Basic(BasicType::Integer)
                | TypeInfo::Basic(BasicType::Boolean)
                | TypeInfo::Basic(BasicType::Char) => Ok(Some(TypeInfo::Basic(BasicType::Integer))),
                _ => Err("Ord argument must be scalar".into()),
            }
        }
        "chr" => {
            if args.len() != 1 {
                return Err("Chr requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_basic(&t, BasicType::Integer, "Chr argument")?;
            Ok(Some(TypeInfo::Basic(BasicType::Char)))
        }
        "length" | "high" | "low" => {
            if args.len() != 1 {
                return Err(format!("{name} requires 1 argument"));
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if let TypeInfo::Array(_) = t {
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            } else {
                Err(format!("{name} argument must be array"))
            }
        }
        _ => Ok(None),
    }
}

fn check_builtin_array_io(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 2 {
        return Err(format!("{name} requires 2 arguments"));
    }
    let lv = expr_to_lvalue(&args[0]).ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
    let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    let arr = match at {
        TypeInfo::Array(a) => a,
        _ => return Err(format!("{name} first argument must be array")),
    };
    if !is_basic_type(&arr.elem_ty) {
        return Err(format!("{name} supports only scalar element arrays"));
    }
    let nt = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
    expect_basic(&nt, BasicType::Integer, &format!("{name} length"))?;
    Ok(())
}

fn check_builtin_str_io(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    args: &[Expr],
) -> Result<(), String> {
    let want = if name == "ReadStr" { 2 } else { 1 };
    if args.len() != want {
        return Err(format!("{name} requires {want} arguments"));
    }
    let lv = expr_to_lvalue(&args[0]).ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
    let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    let Some(_n) = char_array_len(&at) else {
        return Err(format!("{name} first argument must be array of char"));
    };
    if name == "ReadStr" {
        let nt = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
        expect_basic(&nt, BasicType::Integer, "ReadStr length")?;
    }
    Ok(())
}

fn check_builtin_writehex(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 1 {
        return Err("WriteHex requires 1 argument".into());
    }
    let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
    expect_basic(&t, BasicType::Integer, "WriteHex argument")
}

fn const_type_from_val(v: ConstVal) -> TypeInfo {
    match v {
        ConstVal::I32(_) => TypeInfo::Basic(BasicType::Integer),
        ConstVal::U32(_) => TypeInfo::Basic(BasicType::Char),
        ConstVal::Bool(_) => TypeInfo::Basic(BasicType::Boolean),
    }
}

fn expect_basic(t: &TypeInfo, want: BasicType, what: &str) -> Result<(), String> {
    match t {
        TypeInfo::Basic(b) if std::mem::discriminant(b) == std::mem::discriminant(&want) => Ok(()),
        _ => Err(format!("type error in {what}")),
    }
}

fn same_type(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (a, b) {
        (TypeInfo::Basic(x), TypeInfo::Basic(y)) => std::mem::discriminant(x) == std::mem::discriminant(y),
        (TypeInfo::Record(rx), TypeInfo::Record(ry)) => same_record(rx, ry),
        (TypeInfo::Array(ax), TypeInfo::Array(ay)) => {
            ax.len == ay.len && same_type(&ax.elem_ty, &ay.elem_ty)
        }
        _ => false,
    }
}

fn same_record(a: &RecordInfo, b: &RecordInfo) -> bool {
    if a.fields.len() != b.fields.len() {
        return false;
    }
    for (k, fa) in &a.fields {
        let Some(fb) = b.fields.get(k) else {
            return false;
        };
        if fa.offset_bytes != fb.offset_bytes || !same_type(&fa.ty, &fb.ty) {
            return false;
        }
    }
    true
}

fn is_basic_type(t: &TypeInfo) -> bool {
    matches!(t, TypeInfo::Basic(_))
}

fn char_array_len(t: &TypeInfo) -> Option<u32> {
    match t {
        TypeInfo::Array(a) => match a.elem_ty.as_ref() {
            TypeInfo::Basic(BasicType::Char) => Some(a.len),
            _ => None,
        },
        _ => None,
    }
}

fn type_desc(t: &TypeInfo) -> String {
    match t {
        TypeInfo::Basic(BasicType::Integer) => "integer".into(),
        TypeInfo::Basic(BasicType::Boolean) => "boolean".into(),
        TypeInfo::Basic(BasicType::Char) => "char".into(),
        TypeInfo::Record(_) => "record".into(),
        TypeInfo::Array(a) => format!("array[{}] of {}", a.len, type_desc(&a.elem_ty)),
    }
}
