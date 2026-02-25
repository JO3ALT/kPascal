use std::collections::{HashMap, HashSet};

use crate::ast::*;

#[derive(Debug, Clone)]
pub enum TypeInfo {
    Basic(BasicType),
    Nil,
    Pointer(String),
    Enum(EnumInfo),
    Record(RecordInfo),
    Sum(SumInfo),
    Array(ArrayInfo),
}

#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub name: String,
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
    pub low_bound: i32,
    pub high_bound: i32,
    pub len: u32,
    pub elem_ty: Box<TypeInfo>,
    pub elem_size_bytes: u32,
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct SumInfo {
    pub arms: Vec<SumArmInfo>,
    pub payload_size_bytes: u32,
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct SumArmInfo {
    pub name: String,
    pub tag: u32,
    pub fields: Vec<SumFieldInfo>,
    pub payload_size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct SumFieldInfo {
    pub name: String,
    pub offset_bytes: u32,
    pub ty: TypeInfo,
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
    pub immutables: HashSet<String>,
    // Key is scoped name, e.g. "program::Outer::Inner"
    pub routines: HashMap<String, RoutineSig>,
}

#[derive(Debug, Clone)]
pub enum ConstVal {
    I32(i32),
    U32(u32),
    Bool(bool),
    F32(u32),
    EnumTag { enum_name: String, ordinal: i32 },
}

fn const_val_type(v: &ConstVal) -> TypeInfo {
    match v {
        ConstVal::I32(_) => TypeInfo::Basic(BasicType::Integer),
        ConstVal::U32(_) => TypeInfo::Basic(BasicType::Char),
        ConstVal::Bool(_) => TypeInfo::Basic(BasicType::Boolean),
        ConstVal::F32(_) => TypeInfo::Basic(BasicType::Float),
        ConstVal::EnumTag { enum_name, .. } => TypeInfo::Enum(EnumInfo {
            name: enum_name.clone(),
        }),
    }
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
            immutables: HashSet::new(),
            routines: HashMap::new(),
        }
    }
}

fn tyref_to_info(env: &Env, tr: &TypeRef) -> Result<TypeInfo, String> {
    match tr {
        TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
        TypeRef::PointerNamed(n) => Ok(TypeInfo::Pointer(n.clone())),
        TypeRef::Option(inner) => {
            let inner_ty = tyref_to_info(env, inner)?;
            Ok(make_option_type(inner_ty)?)
        }
        TypeRef::Result(ok_ty, err_ty) => {
            let ok = tyref_to_info(env, ok_ty)?;
            let err = tyref_to_info(env, err_ty)?;
            Ok(make_result_type(ok, err)?)
        }
        TypeRef::Array { dims, elem } => {
            let mut bounds = vec![];
            for d in dims {
                let lo = to_i32(eval_const(env, &d.low)?)?;
                let hi = to_i32(eval_const(env, &d.high)?)?;
                if hi < lo {
                    return Err("array high bound must be >= low bound".into());
                }
                bounds.push((lo, hi));
            }
            let mut t = tyref_to_info(env, elem)?;
            for &(lo, hi) in bounds.iter().rev() {
                let n = (hi - lo + 1) as u32;
                let esz = sizeof_type(&t)?;
                let sz = n
                    .checked_mul(esz)
                    .ok_or_else(|| "array size overflow".to_string())?;
                t = TypeInfo::Array(ArrayInfo {
                    low_bound: lo,
                    high_bound: hi,
                    len: n,
                    elem_ty: Box::new(t),
                    elem_size_bytes: esz,
                    size_bytes: sz,
                });
            }
            Ok(t)
        }
        TypeRef::Named(n) => env
            .types
            .get(n)
            .cloned()
            .ok_or_else(|| format!("unknown type: {n}")),
    }
}

fn make_option_type(inner: TypeInfo) -> Result<TypeInfo, String> {
    let payload_size = sizeof_type(&inner)?;
    Ok(TypeInfo::Sum(SumInfo {
        arms: vec![
            SumArmInfo {
                name: "none".into(),
                tag: 0,
                fields: vec![],
                payload_size_bytes: 0,
            },
            SumArmInfo {
                name: "some".into(),
                tag: 1,
                fields: vec![SumFieldInfo {
                    name: "value".into(),
                    offset_bytes: 0,
                    ty: inner,
                }],
                payload_size_bytes: payload_size,
            },
        ],
        payload_size_bytes: payload_size,
        size_bytes: 4 + payload_size,
    }))
}

fn make_result_type(ok_ty: TypeInfo, err_ty: TypeInfo) -> Result<TypeInfo, String> {
    let ok_sz = sizeof_type(&ok_ty)?;
    let err_sz = sizeof_type(&err_ty)?;
    let payload_size = ok_sz.max(err_sz);
    Ok(TypeInfo::Sum(SumInfo {
        arms: vec![
            SumArmInfo {
                name: "ok".into(),
                tag: 0,
                fields: vec![SumFieldInfo {
                    name: "value".into(),
                    offset_bytes: 0,
                    ty: ok_ty,
                }],
                payload_size_bytes: ok_sz,
            },
            SumArmInfo {
                name: "err".into(),
                tag: 1,
                fields: vec![SumFieldInfo {
                    name: "error".into(),
                    offset_bytes: 0,
                    ty: err_ty,
                }],
                payload_size_bytes: err_sz,
            },
        ],
        payload_size_bytes: payload_size,
        size_bytes: 4 + payload_size,
    }))
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
            TypeSpec::Enum(labels) => {
                let mut seen = HashSet::new();
                for (i, label) in labels.iter().enumerate() {
                    if !seen.insert(label.to_ascii_lowercase()) {
                        return Err(format!("duplicate enum label in {scope}: {label}"));
                    }
                    if env.consts.contains_key(label) {
                        return Err(format!("const redefined in {scope}: {label}"));
                    }
                    env.consts.insert(
                        label.clone(),
                        ConstVal::EnumTag {
                            enum_name: td.name.clone(),
                            ordinal: i as i32,
                        },
                    );
                }
                TypeInfo::Enum(EnumInfo {
                    name: td.name.clone(),
                })
            }
            TypeSpec::Alias(r) => tyref_to_info(env, r)?,
            TypeSpec::Record(fields) => {
                let mut ftab = HashMap::new();
                let mut offset = 0u32;
                for f in fields {
                    let fty = tyref_to_info(env, &f.ty)?;
                    let fsz = sizeof_type(&fty)?;
                    let finfo = FieldInfo {
                        offset_bytes: offset,
                        ty: fty,
                    };
                    if ftab.insert(f.name.clone(), finfo).is_some() {
                        return Err(format!("duplicate field name in {scope}: {}", f.name));
                    }
                    offset += fsz;
                }
                TypeInfo::Record(RecordInfo {
                    fields: ftab,
                    size_bytes: offset,
                })
            }
            TypeSpec::SumRecord(arms) => {
                let mut out_arms = vec![];
                let mut arm_names = HashSet::new();
                let mut max_payload = 0u32;
                for (tag, arm) in arms.iter().enumerate() {
                    if !arm_names.insert(arm.name.clone()) {
                        return Err(format!("duplicate sum arm name in {scope}: {}", arm.name));
                    }
                    let mut fields = vec![];
                    let mut field_names = HashSet::new();
                    let mut offset = 0u32;
                    for f in &arm.fields {
                        if !field_names.insert(f.name.clone()) {
                            return Err(format!(
                                "duplicate field name in {scope} arm {}: {}",
                                arm.name, f.name
                            ));
                        }
                        let ty = tyref_to_info(env, &f.ty)?;
                        let fsz = sizeof_type(&ty)?;
                        fields.push(SumFieldInfo {
                            name: f.name.clone(),
                            offset_bytes: offset,
                            ty,
                        });
                        offset += fsz;
                    }
                    max_payload = max_payload.max(offset);
                    out_arms.push(SumArmInfo {
                        name: arm.name.clone(),
                        tag: tag as u32,
                        fields,
                        payload_size_bytes: offset,
                    });
                }
                TypeInfo::Sum(SumInfo {
                    arms: out_arms,
                    payload_size_bytes: max_payload,
                    size_bytes: 4 + max_payload,
                })
            }
            TypeSpec::Array { dims, elem } => {
                let mut bounds = vec![];
                for d in dims {
                    let lo = to_i32(eval_const(env, &d.low)?)?;
                    let hi = to_i32(eval_const(env, &d.high)?)?;
                    if hi < lo {
                        return Err(format!("array bounds in {scope} are invalid (high < low)"));
                    }
                    bounds.push((lo, hi));
                }
                let mut t = tyref_to_info(env, elem)?;
                for &(lo, hi) in bounds.iter().rev() {
                    let n = (hi - lo + 1) as u32;
                    let esz = sizeof_type(&t)?;
                    let sz = n
                        .checked_mul(esz)
                        .ok_or_else(|| format!("array size overflow in {scope}"))?;
                    t = TypeInfo::Array(ArrayInfo {
                        low_bound: lo,
                        high_bound: hi,
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
        if let Some(tyref) = &cd.ty {
            let expected = tyref_to_info(env, tyref)?;
            let actual = const_val_type(&v);
            if !same_type(&expected, &actual) {
                return Err(format!(
                    "const type mismatch for {}: expected {}, got {}",
                    cd.name,
                    type_desc(&expected),
                    type_desc(&actual)
                ));
            }
        }
        env.consts.insert(cd.name.clone(), v);
    }

    if collect_vars {
        for vd in &block.vars {
            if env.vars.contains_key(&vd.name) {
                return Err(format!("var redefined in {scope}: {}", vd.name));
            }
            let t = tyref_to_info(env, &vd.ty)?;
            env.vars.insert(vd.name.clone(), t);
            if vd.immutable {
                env.immutables.insert(vd.name.clone());
            }
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
        env.routines
            .insert(scoped, RoutineSig { params: ptab, ret });
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
        Expr::Bool(_) => Ok(TypeInfo::Basic(BasicType::Boolean)),
        Expr::Char(_) => Ok(TypeInfo::Basic(BasicType::Char)),
        Expr::Float(_) => Ok(TypeInfo::Basic(BasicType::Float)),
        Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
        Expr::Nil => Ok(TypeInfo::Nil),
        Expr::Ctor(_, _) => Err("constructor expression requires target type context".into()),
        Expr::ArrayLit(_) => Err("array literal requires array target type context".into()),
        Expr::RecordUpdate(base, _) => type_of_expr_scoped(env, vars, visible_routines, base),
        Expr::ArrayUpdate(base, _) => type_of_expr_scoped(env, vars, visible_routines, base),
        Expr::OptionNone => Err("NONE requires OPTION target type context".into()),
        Expr::OptionSome(_) => Err("SOME requires OPTION target type context".into()),
        Expr::Cond { .. } => Err("COND expression requires target type context".into()),
        Expr::Cast(tr, inner) => {
            let src = type_of_expr_scoped(env, vars, visible_routines, inner)?;
            let dst = tyref_to_info(env, tr)?;
            let src_sz = sizeof_type(&src)?;
            let dst_sz = sizeof_type(&dst)?;
            if src_sz != dst_sz {
                return Err(format!(
                    "cast size mismatch: {} bytes -> {} bytes",
                    src_sz, dst_sz
                ));
            }
            let ok = matches!(
                (&src, &dst),
                (TypeInfo::Pointer(_), TypeInfo::Pointer(_))
                    | (TypeInfo::Pointer(_), TypeInfo::Basic(BasicType::Integer))
                    | (TypeInfo::Basic(BasicType::Integer), TypeInfo::Pointer(_))
                    | (
                        TypeInfo::Basic(BasicType::Integer),
                        TypeInfo::Basic(BasicType::Integer)
                    )
            );
            if !ok {
                return Err(format!(
                    "unsafe cast is only supported for pointer/integer 32-bit values (got {} -> {})",
                    type_desc(&src),
                    type_desc(&dst)
                ));
            }
            Ok(dst)
        }
        Expr::Deref(base) => {
            let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
            match bt {
                TypeInfo::Pointer(target) => env
                    .types
                    .get(&target)
                    .cloned()
                    .ok_or_else(|| format!("unknown pointed type: {target}")),
                _ => Err("deref on non-pointer".into()),
            }
        }
        Expr::Var(n) => {
            if let Some(t) = vars.get(n) {
                Ok(t.clone())
            } else if let Some(c) = env.consts.get(n) {
                Ok(const_val_type(c))
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
                UnOp::Neg => match it {
                    TypeInfo::Basic(BasicType::Integer) => Ok(TypeInfo::Basic(BasicType::Integer)),
                    TypeInfo::Basic(BasicType::Float) => Ok(TypeInfo::Basic(BasicType::Float)),
                    _ => Err("NEG requires integer or float".into()),
                },
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
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    match (&ta, &tb, op) {
                        (
                            TypeInfo::Basic(BasicType::Integer),
                            TypeInfo::Basic(BasicType::Integer),
                            _,
                        ) => Ok(TypeInfo::Basic(BasicType::Integer)),
                        (
                            TypeInfo::Basic(BasicType::Float),
                            TypeInfo::Basic(BasicType::Float),
                            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div,
                        ) => Ok(TypeInfo::Basic(BasicType::Float)),
                        (
                            TypeInfo::Basic(BasicType::Float),
                            TypeInfo::Basic(BasicType::Float),
                            BinOp::Mod,
                        ) => Err("mod is not supported for float".into()),
                        _ => {
                            Err("arithmetic operands must both be integer or both be float".into())
                        }
                    }
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
                        TypeInfo::Basic(BasicType::Integer)
                        | TypeInfo::Basic(BasicType::Char)
                        | TypeInfo::Basic(BasicType::Float)
                        | TypeInfo::Enum(_) => Ok(TypeInfo::Basic(BasicType::Boolean)),
                        _ => Err("order comparison requires integer, char, enum, or float".into()),
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
        if !p.by_ref
            && matches!(p.ty, TypeInfo::Record(_) | TypeInfo::Array(_))
            && expr_to_lvalue(a).is_none()
        {
            return Err(format!(
                "argument #{arg_no} in call to {name} must be lvalue for aggregate value parameter"
            ));
        }
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
        TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_) | TypeInfo::Nil => Ok(4),
        TypeInfo::Record(r) => Ok(r.size_bytes),
        TypeInfo::Sum(s) => Ok(s.size_bytes),
        TypeInfo::Array(a) => Ok(a.size_bytes),
    }
}

pub fn eval_const(env: &Env, e: &ConstExpr) -> Result<ConstVal, String> {
    match e {
        ConstExpr::Int(i) => Ok(ConstVal::I32(*i)),
        ConstExpr::Bool(b) => Ok(ConstVal::Bool(*b)),
        ConstExpr::Char(u) => Ok(ConstVal::U32(*u)),
        ConstExpr::Float(f) => Ok(ConstVal::F32(*f)),
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
                        ConstVal::F32(_) => Err("Ord(float) is not allowed in const expr".into()),
                        ConstVal::EnumTag { ordinal, .. } => Ok(ConstVal::I32(ordinal)),
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
                "float" => {
                    if args.len() != 1 {
                        return Err("Float requires 1 argument in const expr".into());
                    }
                    let i = to_i32(eval_const(env, &args[0])?)?;
                    Ok(ConstVal::F32((i as f32).to_bits()))
                }
                "trunc" => {
                    if args.len() != 1 {
                        return Err("Trunc requires 1 argument in const expr".into());
                    }
                    let f = to_f32(eval_const(env, &args[0])?)?;
                    if !f.is_finite() {
                        return Err("Trunc const argument must be finite float".into());
                    }
                    Ok(ConstVal::I32(f32_to_i32_checked(
                        f.trunc(),
                        "Trunc const result",
                    )?))
                }
                "round" => {
                    if args.len() != 1 {
                        return Err("Round requires 1 argument in const expr".into());
                    }
                    let f = to_f32(eval_const(env, &args[0])?)?;
                    if !f.is_finite() {
                        return Err("Round const argument must be finite float".into());
                    }
                    Ok(ConstVal::I32(f32_to_i32_checked(
                        f.round(),
                        "Round const result",
                    )?))
                }
                _ => Err(format!("unsupported const function: {name}")),
            }
        }
        ConstExpr::Unary(UnOp::Neg, inner) => match eval_const(env, inner)? {
            ConstVal::I32(i) => Ok(ConstVal::I32(-i)),
            ConstVal::F32(bits) => Ok(ConstVal::F32(bits ^ (1u32 << 31))),
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
                Add | Sub | Mul | Div | Mod => {
                    if matches!(av, ConstVal::F32(_)) || matches!(bv, ConstVal::F32(_)) {
                        let af = to_f32(av)?;
                        let bf = to_f32(bv)?;
                        if matches!(op, Div) && bf == 0.0 {
                            return Err("division by zero in const expr".into());
                        }
                        if matches!(op, Mod) {
                            return Err("mod is not supported for float const expr".into());
                        }
                        let r = match op {
                            Add => af + bf,
                            Sub => af - bf,
                            Mul => af * bf,
                            Div => af / bf,
                            _ => unreachable!(),
                        };
                        return Ok(ConstVal::F32(r.to_bits()));
                    }
                    let ai = to_i32(av)?;
                    let bi = to_i32(bv)?;
                    if matches!(op, Div | Mod) && bi == 0 {
                        return Err("division by zero in const expr".into());
                    }
                    Ok(ConstVal::I32(match op {
                        Add => ai + bi,
                        Sub => ai - bi,
                        Mul => ai * bi,
                        Div => ai / bi,
                        Mod => ai % bi,
                        _ => unreachable!(),
                    }))
                }
                Eq | Ne | Lt | Le | Gt | Ge => {
                    if matches!(av, ConstVal::F32(_)) || matches!(bv, ConstVal::F32(_)) {
                        let af = to_f32(av)?;
                        let bf = to_f32(bv)?;
                        let r = match op {
                            Eq => af == bf,
                            Ne => af != bf,
                            Lt => af < bf,
                            Le => af <= bf,
                            Gt => af > bf,
                            Ge => af >= bf,
                            _ => unreachable!(),
                        };
                        return Ok(ConstVal::Bool(r));
                    }
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
        ConstVal::F32(_) => Err("float cannot be converted to i32 in const expr".into()),
        ConstVal::EnumTag { ordinal, .. } => Ok(ordinal),
    }
}

fn to_f32(v: ConstVal) -> Result<f32, String> {
    match v {
        ConstVal::F32(bits) => Ok(f32_from_bits(bits)),
        _ => Err("mixed float/non-float const expression is not supported".into()),
    }
}

fn f32_from_bits(bits: u32) -> f32 {
    f32::from_bits(bits)
}

fn f32_to_i32_checked(v: f32, what: &str) -> Result<i32, String> {
    if !v.is_finite() {
        return Err(format!("{what} is not finite"));
    }
    if v < i32::MIN as f32 || v > i32::MAX as f32 {
        return Err(format!("{what} out of i32 range"));
    }
    Ok(v as i32)
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
            Selector::Deref => match t {
                TypeInfo::Pointer(ref target) => {
                    t = env
                        .types
                        .get(target)
                        .cloned()
                        .ok_or_else(|| format!("unknown pointed type: {target}"))?;
                }
                _ => return Err("deref on non-pointer lvalue".into()),
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
        Expr::Deref(_) | Expr::Field(_, _) | Expr::Index(_, _) => {
            let mut sels = vec![];
            let mut cur = e;
            loop {
                match cur {
                    Expr::Deref(inner) => {
                        sels.push(Selector::Deref);
                        cur = inner;
                    }
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

fn sum_arm_by_name<'a>(sum: &'a SumInfo, name: &str) -> Option<&'a SumArmInfo> {
    let lname = name.to_ascii_lowercase();
    sum.arms
        .iter()
        .find(|a| a.name.eq_ignore_ascii_case(&lname) || a.name.eq_ignore_ascii_case(name))
}

fn check_expr_matches_type_scoped(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    e: &Expr,
    expected: &TypeInfo,
) -> Result<(), String> {
    match e {
        Expr::OptionNone => match expected {
            TypeInfo::Sum(sum) => {
                let arm = sum_arm_by_name(sum, "none")
                    .ok_or("NONE used with non-OPTION compatible sum type")?;
                if !arm.fields.is_empty() {
                    return Err("NONE arm must have no fields".into());
                }
                Ok(())
            }
            _ => Err("NONE requires OPTION target type".into()),
        },
        Expr::OptionSome(inner) => match expected {
            TypeInfo::Sum(sum) => {
                let arm = sum_arm_by_name(sum, "some")
                    .ok_or("SOME used with non-OPTION compatible sum type")?;
                if arm.fields.len() != 1 {
                    return Err("SOME arm must have exactly 1 field".into());
                }
                check_expr_matches_type_scoped(
                    env,
                    vars,
                    visible_routines,
                    inner,
                    &arm.fields[0].ty,
                )
            }
            _ => Err("SOME requires OPTION target type".into()),
        },
        Expr::Ctor(name, named_args) => match expected {
            TypeInfo::Record(rec) => {
                if !ctor_name_matches_record_type(env, name, rec) {
                    return Err(format!(
                        "constructor {name} does not match target record type"
                    ));
                }
                if rec.fields.len() != named_args.len() {
                    return Err(format!(
                        "constructor {name} argument count mismatch: expected {}, got {}",
                        rec.fields.len(),
                        named_args.len()
                    ));
                }
                for (fname, finfo) in &rec.fields {
                    let (_, expr) = named_args
                        .iter()
                        .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                        .ok_or_else(|| format!("constructor {name} missing field {fname}"))?;
                    check_expr_matches_type_scoped(env, vars, visible_routines, expr, &finfo.ty)?;
                }
                for (n, _) in named_args {
                    if !rec.fields.keys().any(|f| f.eq_ignore_ascii_case(n)) {
                        return Err(format!("constructor {name} has no field {n}"));
                    }
                }
                Ok(())
            }
            TypeInfo::Sum(sum) => {
                let arm = sum_arm_by_name(sum, name)
                    .ok_or_else(|| format!("unknown constructor for sum type: {name}"))?;
                if arm.fields.len() != named_args.len() {
                    return Err(format!(
                        "constructor {name} argument count mismatch: expected {}, got {}",
                        arm.fields.len(),
                        named_args.len()
                    ));
                }
                for f in &arm.fields {
                    let (_, expr) = named_args
                        .iter()
                        .find(|(n, _)| n.eq_ignore_ascii_case(&f.name))
                        .ok_or_else(|| format!("constructor {name} missing field {}", f.name))?;
                    check_expr_matches_type_scoped(env, vars, visible_routines, expr, &f.ty)?;
                }
                for (n, _) in named_args {
                    if !arm.fields.iter().any(|f| f.name.eq_ignore_ascii_case(n)) {
                        return Err(format!("constructor {name} has no field {n}"));
                    }
                }
                Ok(())
            }
            _ => Err("constructor expression requires record/sum target type".into()),
        },
        Expr::ArrayLit(elems) => match expected {
            TypeInfo::Array(arr) => {
                if elems.len() != arr.len as usize {
                    return Err(format!(
                        "array literal length mismatch: expected {}, got {}",
                        arr.len,
                        elems.len()
                    ));
                }
                for (i, e) in elems.iter().enumerate() {
                    check_expr_matches_type_scoped(env, vars, visible_routines, e, &arr.elem_ty)
                        .map_err(|er| format!("array literal element #{}: {er}", i + 1))?;
                }
                Ok(())
            }
            _ => Err("array literal requires array target type".into()),
        },
        Expr::RecordUpdate(base, updates) => match expected {
            TypeInfo::Record(rec) => {
                let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
                if !same_type(&bt, expected) {
                    return Err(format!(
                        "record update base type mismatch: expected {}, got {}",
                        type_desc(expected),
                        type_desc(&bt)
                    ));
                }
                if updates.is_empty() {
                    return Err("record update requires at least one field assignment".into());
                }
                let mut seen = HashSet::new();
                for (fname, expr) in updates {
                    let key = fname.to_ascii_lowercase();
                    if !seen.insert(key) {
                        return Err("duplicate record update field".into());
                    }
                    let (_, finfo) = rec
                        .fields
                        .iter()
                        .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                        .ok_or_else(|| format!("record update has no field {fname}"))?;
                    check_expr_matches_type_scoped(env, vars, visible_routines, expr, &finfo.ty)?;
                }
                Ok(())
            }
            _ => Err("record update requires record target type".into()),
        },
        Expr::ArrayUpdate(base, updates) => match expected {
            TypeInfo::Array(arr) => {
                let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
                if !same_type(&bt, expected) {
                    return Err(format!(
                        "array update base type mismatch: expected {}, got {}",
                        type_desc(expected),
                        type_desc(&bt)
                    ));
                }
                if updates.is_empty() {
                    return Err("array update requires at least one element assignment".into());
                }
                for (idx, val) in updates {
                    let it = type_of_expr_scoped(env, vars, visible_routines, idx)?;
                    expect_basic(&it, BasicType::Integer, "array update index")?;
                    check_expr_matches_type_scoped(env, vars, visible_routines, val, &arr.elem_ty)?;
                }
                Ok(())
            }
            _ => Err("array update requires array target type".into()),
        },
        Expr::Call(name, args) if matches!(expected, TypeInfo::Sum(_)) && args.is_empty() => {
            // zero-field constructor sugar, e.g. C()
            match expected {
                TypeInfo::Sum(sum) => {
                    let arm = sum_arm_by_name(sum, name).ok_or_else(|| {
                        format!("unknown zero-field constructor for sum type: {name}")
                    })?;
                    if !arm.fields.is_empty() {
                        return Err(format!(
                            "constructor {name} requires named fields ({} field(s))",
                            arm.fields.len()
                        ));
                    }
                    Ok(())
                }
                _ => unreachable!(),
            }
        }
        Expr::Cond { arms, else_block } => {
            for arm in arms {
                let ct = type_of_expr_scoped(env, vars, visible_routines, &arm.cond)?;
                expect_basic(&ct, BasicType::Boolean, "cond arm condition")?;
                for st in &arm.block.stmts {
                    check_stmt_with_vars(env, vars, visible_routines, st)?;
                }
                check_expr_matches_type_scoped(
                    env,
                    vars,
                    visible_routines,
                    &arm.block.value,
                    expected,
                )?;
            }
            for st in &else_block.stmts {
                check_stmt_with_vars(env, vars, visible_routines, st)?;
            }
            check_expr_matches_type_scoped(env, vars, visible_routines, &else_block.value, expected)
        }
        Expr::Nil => match expected {
            TypeInfo::Pointer(_) => Ok(()),
            _ => Err(format!(
                "type mismatch: expected {}, got nil",
                type_desc(expected)
            )),
        },
        _ => {
            let actual = type_of_expr_scoped(env, vars, visible_routines, e)?;
            if same_type(&actual, expected) {
                Ok(())
            } else {
                Err(format!(
                    "type mismatch: expected {}, got {}",
                    type_desc(expected),
                    type_desc(&actual)
                ))
            }
        }
    }
}

pub fn check_program(env: &Env, prog: &Program) -> Result<(), String> {
    check_block(
        env,
        &prog.block,
        &HashMap::new(),
        &HashMap::new(),
        "program",
    )
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
    check_imut_block(env, block, &vars, &visible_routines)?;

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

fn check_imut_block(
    env: &Env,
    block: &Block,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
) -> Result<(), String> {
    let mut local_imuts = HashSet::new();
    for v in &block.vars {
        if v.immutable {
            local_imuts.insert(v.name.clone());
        }
    }
    let mut initialized = HashSet::new();
    let mut assigned = HashSet::new();
    check_imut_stmt(
        env,
        vars,
        visible_routines,
        &local_imuts,
        &mut initialized,
        &mut assigned,
        &block.body,
    )?;
    for name in local_imuts {
        if !initialized.contains(&name) {
            return Err(format!(
                "imut variable must be initialized exactly once: {name}"
            ));
        }
    }
    Ok(())
}

fn check_imut_stmt(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    local_imuts: &HashSet<String>,
    initialized: &mut HashSet<String>,
    assigned: &mut HashSet<String>,
    s: &Stmt,
) -> Result<(), String> {
    match s {
        Stmt::Empty | Stmt::ReadLn => Ok(()),
        Stmt::Compound(v) => {
            for st in v {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    st,
                )?;
            }
            Ok(())
        }
        Stmt::Assign(lv, rhs) => {
            check_imut_reads_in_lvalue(env, vars, visible_routines, local_imuts, initialized, lv)?;
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, rhs)?;
            if local_imuts.contains(&lv.base) {
                if !lv.sels.is_empty() {
                    return Err(format!(
                        "imut variable cannot be mutated via field/index: {}",
                        lv.base
                    ));
                }
                if !assigned.insert(lv.base.clone()) {
                    return Err(format!("imut variable cannot be reassigned: {}", lv.base));
                }
                initialized.insert(lv.base.clone());
            }
            Ok(())
        }
        Stmt::Read(lvs) => {
            for lv in lvs {
                check_imut_reads_in_lvalue(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    lv,
                )?;
                if local_imuts.contains(&lv.base) {
                    return Err(format!(
                        "imut variable cannot be assigned by Read: {}",
                        lv.base
                    ));
                }
            }
            Ok(())
        }
        Stmt::For {
            var,
            init,
            limit,
            body,
            ..
        } => {
            if local_imuts.contains(var) {
                return Err(format!(
                    "imut variable cannot be used as for loop variable: {var}"
                ));
            }
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, init)?;
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, limit)?;
            check_imut_stmt(
                env,
                vars,
                visible_routines,
                local_imuts,
                initialized,
                assigned,
                body,
            )
        }
        Stmt::If(cond, then_s, else_s) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, cond)?;
            check_imut_stmt(
                env,
                vars,
                visible_routines,
                local_imuts,
                initialized,
                assigned,
                then_s,
            )?;
            if let Some(es) = else_s {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    es,
                )?;
            }
            Ok(())
        }
        Stmt::While(cond, body) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, cond)?;
            check_imut_stmt(
                env,
                vars,
                visible_routines,
                local_imuts,
                initialized,
                assigned,
                body,
            )
        }
        Stmt::Repeat(stmts, cond) => {
            for st in stmts {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    st,
                )?;
            }
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, cond)
        }
        Stmt::Case {
            expr,
            arms,
            else_stmt,
        } => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, expr)?;
            for (_, st) in arms {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    st,
                )?;
            }
            if let Some(es) = else_stmt {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    es,
                )?;
            }
            Ok(())
        }
        Stmt::SumCase {
            expr,
            arms,
            else_stmt,
        } => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, expr)?;
            for arm in arms {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    &arm.body,
                )?;
            }
            if let Some(es) = else_stmt {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    assigned,
                    es,
                )?;
            }
            Ok(())
        }
        Stmt::ProcCall(name, args) => check_imut_call_args(
            env,
            vars,
            visible_routines,
            local_imuts,
            initialized,
            name,
            args,
        ),
        Stmt::Write(args) | Stmt::WriteLn(args) => {
            for e in args {
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, e)?;
            }
            Ok(())
        }
    }
}

fn check_imut_reads_in_lvalue(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    local_imuts: &HashSet<String>,
    initialized: &HashSet<String>,
    lv: &LValue,
) -> Result<(), String> {
    for sel in &lv.sels {
        if let Selector::Index(idxs) = sel {
            for ix in idxs {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    ix,
                )?;
            }
        }
    }
    Ok(())
}

fn check_imut_reads_in_expr(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    local_imuts: &HashSet<String>,
    initialized: &HashSet<String>,
    e: &Expr,
) -> Result<(), String> {
    match e {
        Expr::Var(n) => {
            if local_imuts.contains(n) && !initialized.contains(n) {
                return Err(format!("imut variable used before initialization: {n}"));
            }
            Ok(())
        }
        Expr::Call(name, args) => check_imut_call_args(
            env,
            vars,
            visible_routines,
            local_imuts,
            initialized,
            name,
            args,
        ),
        Expr::Ctor(_, named) => {
            for (_, e) in named {
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, e)?;
            }
            Ok(())
        }
        Expr::ArrayLit(elems) => {
            for e in elems {
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, e)?;
            }
            Ok(())
        }
        Expr::RecordUpdate(base, updates) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, base)?;
            for (_, e) in updates {
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, e)?;
            }
            Ok(())
        }
        Expr::ArrayUpdate(base, updates) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, base)?;
            for (i, v) in updates {
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, i)?;
                check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, v)?;
            }
            Ok(())
        }
        Expr::OptionSome(inner) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, inner)
        }
        Expr::Cond { arms, else_block } => {
            for arm in arms {
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    &arm.cond,
                )?;
                for st in &arm.block.stmts {
                    check_imut_stmt(
                        env,
                        vars,
                        visible_routines,
                        local_imuts,
                        &mut initialized.clone(),
                        &mut HashSet::new(),
                        st,
                    )?;
                }
                check_imut_reads_in_expr(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    initialized,
                    &arm.block.value,
                )?;
            }
            for st in &else_block.stmts {
                check_imut_stmt(
                    env,
                    vars,
                    visible_routines,
                    local_imuts,
                    &mut initialized.clone(),
                    &mut HashSet::new(),
                    st,
                )?;
            }
            check_imut_reads_in_expr(
                env,
                vars,
                visible_routines,
                local_imuts,
                initialized,
                &else_block.value,
            )
        }
        Expr::Deref(base) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, base)
        }
        Expr::Field(base, _) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, base)
        }
        Expr::Index(base, idx) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, base)?;
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, idx)
        }
        Expr::Cast(_, inner) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, inner)
        }
        Expr::Unary(_, inner) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, inner)
        }
        Expr::Binary(a, _, b) => {
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, a)?;
            check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, b)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Char(_)
        | Expr::Float(_)
        | Expr::Str(_)
        | Expr::Nil
        | Expr::OptionNone => Ok(()),
    }
}

fn check_imut_call_args(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    local_imuts: &HashSet<String>,
    initialized: &HashSet<String>,
    name: &str,
    args: &[Expr],
) -> Result<(), String> {
    for a in args {
        check_imut_reads_in_expr(env, vars, visible_routines, local_imuts, initialized, a)?;
    }
    let Some(key) = visible_routines.get(name) else {
        return Ok(());
    };
    let Some(sig) = env.routines.get(key) else {
        return Ok(());
    };
    for (p, a) in sig.params.iter().zip(args) {
        if p.by_ref {
            if let Some(lv) = expr_to_lvalue(a) {
                if local_imuts.contains(&lv.base) {
                    return Err(format!(
                        "imut variable cannot be passed to var parameter: {}",
                        lv.base
                    ));
                }
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
            check_expr_matches_type_scoped(env, vars, visible_routines, rhs, &lt)
                .map_err(|e| format!("type mismatch in assignment: {e}"))?;
            let is_aggregate_call_result = matches!(rhs, Expr::Call(_, _) | Expr::Ctor(_, _))
                || matches!(rhs, Expr::ArrayLit(_))
                || matches!(rhs, Expr::RecordUpdate(_, _) | Expr::ArrayUpdate(_, _))
                || matches!(rhs, Expr::OptionNone | Expr::OptionSome(_))
                || matches!(rhs, Expr::Cond { .. });
            if !is_scalar_type(&lt) && expr_to_lvalue(rhs).is_none() && !is_aggregate_call_result {
                return Err("aggregate assignment requires lvalue rhs".into());
            }
            Ok(())
        }
        Stmt::Read(lvs) => {
            for lv in lvs {
                let t = resolve_lvalue_type_scoped(env, vars, visible_routines, lv)?;
                if !is_scalar_type(&t) || matches!(t, TypeInfo::Pointer(_)) {
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
            let vt = vars.get(var).ok_or_else(|| format!("unknown var: {var}"))?;
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
            if matches!(et, TypeInfo::Basic(BasicType::Float)) {
                return Err("case on float is not supported".into());
            }
            let mut used = HashSet::new();
            let mut enum_ordinals = HashSet::new();
            for (ce, st) in arms {
                let cv = eval_const(env, ce)?;
                let token = match &cv {
                    ConstVal::I32(i) => format!("I:{i}"),
                    ConstVal::U32(u) => format!("U:{u}"),
                    ConstVal::Bool(b) => format!("B:{b}"),
                    ConstVal::F32(bits) => format!("F:{bits}"),
                    ConstVal::EnumTag { enum_name, ordinal } => {
                        enum_ordinals.insert((enum_name.clone(), *ordinal));
                        format!("E:{enum_name}:{ordinal}")
                    }
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
            } else if let TypeInfo::Enum(einfo) = &et {
                let mut all = HashSet::new();
                for v in env.consts.values() {
                    if let ConstVal::EnumTag { enum_name, ordinal } = v {
                        if enum_name.eq_ignore_ascii_case(&einfo.name) {
                            all.insert((enum_name.clone(), *ordinal));
                        }
                    }
                }
                if !all.is_empty() && all != enum_ordinals {
                    return Err("enum case must be exhaustive or include else".into());
                }
            }
            Ok(())
        }
        Stmt::SumCase {
            expr,
            arms,
            else_stmt,
        } => {
            let et = type_of_expr_scoped(env, vars, visible_routines, expr)?;
            let sum = match et {
                TypeInfo::Sum(s) => s,
                _ => return Err("sum-case requires sum-record expression".into()),
            };
            let mut seen = HashSet::new();
            for arm in arms {
                let sinfo = sum_arm_by_name(&sum, &arm.ctor)
                    .ok_or_else(|| format!("unknown sum-case arm constructor: {}", arm.ctor))?;
                if !seen.insert(sinfo.name.to_ascii_lowercase()) {
                    return Err("duplicate sum-case arm".into());
                }
                if arm.binds.len() != sinfo.fields.len() {
                    return Err(format!(
                        "sum-case bind count mismatch for {}: expected {}, got {}",
                        arm.ctor,
                        sinfo.fields.len(),
                        arm.binds.len()
                    ));
                }
                let mut inner_vars = vars.clone();
                for (idx, b) in arm.binds.iter().enumerate() {
                    if inner_vars.contains_key(b) {
                        return Err(format!("sum-case binding shadows existing name: {b}"));
                    }
                    inner_vars.insert(b.clone(), sinfo.fields[idx].ty.clone());
                }
                check_stmt_with_vars(env, &inner_vars, visible_routines, &arm.body)?;
            }
            let exhaustive = sum
                .arms
                .iter()
                .all(|a| seen.contains(&a.name.to_ascii_lowercase()));
            if !exhaustive && else_stmt.is_none() {
                return Err("sum-case must be exhaustive or include else".into());
            }
            if let Some(es) = else_stmt {
                check_stmt_with_vars(env, vars, visible_routines, es)?;
            }
            Ok(())
        }
        Stmt::ProcCall(name, args) => {
            let lname = name.to_ascii_lowercase();
            if lname == "new" || lname == "dispose" {
                return check_builtin_new_dispose(env, vars, visible_routines, name, args);
            }
            if lname == "readarr" || lname == "writearr" {
                return check_builtin_array_io(env, vars, visible_routines, name, args);
            }
            if lname == "readstr" || lname == "writestr" {
                return check_builtin_str_io(env, vars, visible_routines, name, args);
            }
            if lname == "writehex" {
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
                        if !is_scalar_type(&t) || matches!(t, TypeInfo::Pointer(_) | TypeInfo::Nil)
                        {
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
    if let Some(t) = builtin_list_fn_expr_type(env, vars, visible_routines, name, args)? {
        return Ok(Some(t));
    }
    match n.as_str() {
        "ord" => {
            if args.len() != 1 {
                return Err("Ord requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            match t {
                TypeInfo::Basic(BasicType::Integer)
                | TypeInfo::Basic(BasicType::Boolean)
                | TypeInfo::Basic(BasicType::Char)
                | TypeInfo::Enum(_) => Ok(Some(TypeInfo::Basic(BasicType::Integer))),
                _ => Err(format!(
                    "Ord argument must be scalar, got {}",
                    type_desc(&t)
                )),
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
        "float" => {
            if args.len() != 1 {
                return Err("Float requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_basic(&t, BasicType::Integer, "Float argument #1")?;
            Ok(Some(TypeInfo::Basic(BasicType::Float)))
        }
        "trunc" => {
            if args.len() != 1 {
                return Err("Trunc requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_basic(&t, BasicType::Float, "Trunc argument #1")?;
            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
        }
        "round" => {
            if args.len() != 1 {
                return Err("Round requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_basic(&t, BasicType::Float, "Round argument #1")?;
            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
        }
        "length" | "high" | "low" => {
            if args.len() != 1 {
                return Err(format!("{name} requires 1 argument"));
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if let TypeInfo::Array(_) = t {
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            } else {
                Err(format!(
                    "{name} argument must be array, got {}",
                    type_desc(&t)
                ))
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
    let lv = expr_to_lvalue(&args[0])
        .ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
    let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    let arr = match at {
        TypeInfo::Array(a) => a,
        _ => return Err(format!("{name} first argument must be array")),
    };
    if !is_scalar_type(&arr.elem_ty) {
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
    let is_read = name.eq_ignore_ascii_case("ReadStr");
    let want = if is_read { 2 } else { 1 };
    if args.len() != want {
        return Err(format!("{name} requires {want} arguments"));
    }
    let lv = expr_to_lvalue(&args[0])
        .ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
    let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    let Some(_n) = char_array_len(&at) else {
        return Err(format!("{name} first argument must be array of char"));
    };
    if is_read {
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

fn expr_routine_name_arg(e: &Expr) -> Option<&str> {
    match e {
        Expr::Var(n) => Some(n.as_str()),
        _ => None,
    }
}

fn lookup_visible_routine_sig<'a>(
    env: &'a Env,
    visible_routines: &HashMap<String, String>,
    name: &str,
) -> Result<&'a RoutineSig, String> {
    let key = visible_routines
        .get(name)
        .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
    env.routines
        .get(key)
        .ok_or_else(|| format!("internal: missing routine signature for {key}"))
}

fn lookup_list_ptr_layout(
    env: &Env,
    t: &TypeInfo,
    what: &str,
) -> Result<(String, RecordInfo, FieldInfo), String> {
    let ptr_name = match t {
        TypeInfo::Pointer(n) => n.clone(),
        _ => return Err(format!("{what} must be pointer to list node record")),
    };
    let rec = match env.types.get(&ptr_name) {
        Some(TypeInfo::Record(r)) => r.clone(),
        Some(_) => return Err(format!("{what} points to non-record type")),
        None => return Err(format!("{what} points to unknown type: {ptr_name}")),
    };
    let Some(nf) = rec.fields.get("next") else {
        return Err(format!("{what} node record must have field 'next: ^self'"));
    };
    if nf.offset_bytes != 0 {
        return Err(format!("{what} node field 'next' must be first"));
    }
    match &nf.ty {
        TypeInfo::Pointer(n) if n.eq_ignore_ascii_case(&ptr_name) => {}
        _ => return Err(format!("{what} node field 'next' must be ^{ptr_name}")),
    }
    let Some(vf) = rec.fields.get("value") else {
        return Err(format!("{what} node record must have field 'value'"));
    };
    if vf.offset_bytes < 4 {
        return Err(format!("{what} node field 'value' must come after next"));
    }
    Ok((ptr_name, rec.clone(), vf.clone()))
}

fn check_builtin_new_dispose(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 1 {
        return Err(format!("{name} requires 1 argument"));
    }
    let lv = expr_to_lvalue(&args[0])
        .ok_or_else(|| format!("{name} argument must be lvalue pointer"))?;
    let t = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    match t {
        TypeInfo::Pointer(_) => Ok(()),
        _ => Err(format!("{name} argument must be pointer")),
    }
}

fn builtin_list_fn_expr_type(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    name: &str,
    args: &[Expr],
) -> Result<Option<TypeInfo>, String> {
    let lname = name.to_ascii_lowercase();
    match lname.as_str() {
        "map" => {
            if args.len() != 2 {
                return Err("Map requires 2 arguments".into());
            }
            let st = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            let (_ptr_name, _rec, vf) = lookup_list_ptr_layout(env, &st, "Map src")?;
            let cb = expr_routine_name_arg(&args[1])
                .ok_or("Map callback must be a function name identifier")?;
            let sig = lookup_visible_routine_sig(env, visible_routines, cb)?;
            if sig.params.len() != 2 || !sig.params[0].by_ref || !sig.params[1].by_ref {
                return Err(
                    "Map callback must have signature procedure(var src: T; var dst: T)".into(),
                );
            }
            if !same_type(&sig.params[0].ty, &vf.ty) {
                return Err("Map callback arg #1 must match payload type".into());
            }
            if !same_type(&sig.params[1].ty, &vf.ty) {
                return Err("Map callback arg #2 must match payload type".into());
            }
            if sig.ret.is_some() {
                return Err("Map callback must be procedure".into());
            }
            Ok(Some(st))
        }
        "filter" => {
            if args.len() != 2 {
                return Err("Filter requires 2 arguments".into());
            }
            let st = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            let (_ptr_name, _rec, vf) = lookup_list_ptr_layout(env, &st, "Filter src")?;
            let cb = expr_routine_name_arg(&args[1])
                .ok_or("Filter predicate must be a function name identifier")?;
            let sig = lookup_visible_routine_sig(env, visible_routines, cb)?;
            if sig.params.len() != 1 || !sig.params[0].by_ref {
                return Err("Filter predicate must have signature fn(var v: T): boolean".into());
            }
            if !same_type(&sig.params[0].ty, &vf.ty) {
                return Err("Filter predicate arg #1 must match payload type".into());
            }
            let ret = sig.ret.clone().ok_or("Filter predicate must be function")?;
            expect_basic(&ret, BasicType::Boolean, "Filter predicate return")?;
            Ok(Some(st))
        }
        "fold" => {
            if args.len() != 3 {
                return Err("Fold requires 3 arguments".into());
            }
            let st = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            let (_ptr_name, _rec, vf) = lookup_list_ptr_layout(env, &st, "Fold src")?;
            let it = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
            expect_basic(&it, BasicType::Integer, "Fold init")?;
            let cb = expr_routine_name_arg(&args[2])
                .ok_or("Fold callback must be a function name identifier")?;
            let sig = lookup_visible_routine_sig(env, visible_routines, cb)?;
            if sig.params.len() != 2 || sig.params[0].by_ref || !sig.params[1].by_ref {
                return Err(
                    "Fold callback must have signature fn(integer, var v: T): integer".into(),
                );
            }
            expect_basic(
                &sig.params[0].ty,
                BasicType::Integer,
                "Fold callback arg #1",
            )?;
            if !same_type(&sig.params[1].ty, &vf.ty) {
                return Err("Fold callback arg #2 must match payload type".into());
            }
            let ret = sig.ret.clone().ok_or("Fold callback must be function")?;
            expect_basic(&ret, BasicType::Integer, "Fold callback return")?;
            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
        }
        _ => Ok(None),
    }
}

fn const_type_from_val(v: ConstVal) -> TypeInfo {
    const_val_type(&v)
}

fn expect_basic(t: &TypeInfo, want: BasicType, what: &str) -> Result<(), String> {
    match t {
        TypeInfo::Basic(b) if std::mem::discriminant(b) == std::mem::discriminant(&want) => Ok(()),
        _ => Err(format!(
            "type mismatch in {what}: expected {}, got {}",
            type_desc(&TypeInfo::Basic(want)),
            type_desc(t)
        )),
    }
}

fn ctor_name_matches_record_type(env: &Env, ctor_name: &str, expected: &RecordInfo) -> bool {
    env.types.iter().any(|(name, ty)| {
        if !name.eq_ignore_ascii_case(ctor_name) {
            return false;
        }
        match ty {
            TypeInfo::Record(r) => same_record(r, expected),
            _ => false,
        }
    })
}

fn same_type(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (a, b) {
        (TypeInfo::Nil, TypeInfo::Nil) => true,
        (TypeInfo::Pointer(_), TypeInfo::Nil) | (TypeInfo::Nil, TypeInfo::Pointer(_)) => true,
        (TypeInfo::Pointer(x), TypeInfo::Pointer(y)) => x.eq_ignore_ascii_case(y),
        (TypeInfo::Basic(x), TypeInfo::Basic(y)) => {
            std::mem::discriminant(x) == std::mem::discriminant(y)
        }
        (TypeInfo::Enum(x), TypeInfo::Enum(y)) => x.name.eq_ignore_ascii_case(&y.name),
        (TypeInfo::Record(rx), TypeInfo::Record(ry)) => same_record(rx, ry),
        (TypeInfo::Sum(sx), TypeInfo::Sum(sy)) => same_sum(sx, sy),
        (TypeInfo::Array(ax), TypeInfo::Array(ay)) => {
            ax.low_bound == ay.low_bound
                && ax.high_bound == ay.high_bound
                && ax.len == ay.len
                && same_type(&ax.elem_ty, &ay.elem_ty)
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

fn same_sum(a: &SumInfo, b: &SumInfo) -> bool {
    if a.arms.len() != b.arms.len() {
        return false;
    }
    for (aa, bb) in a.arms.iter().zip(&b.arms) {
        if !aa.name.eq_ignore_ascii_case(&bb.name) || aa.fields.len() != bb.fields.len() {
            return false;
        }
        for (fa, fb) in aa.fields.iter().zip(&bb.fields) {
            if !fa.name.eq_ignore_ascii_case(&fb.name)
                || fa.offset_bytes != fb.offset_bytes
                || !same_type(&fa.ty, &fb.ty)
            {
                return false;
            }
        }
    }
    true
}

fn is_scalar_type(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_)
    )
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
        TypeInfo::Nil => "nil".into(),
        TypeInfo::Pointer(n) => format!("^{}", n),
        TypeInfo::Basic(BasicType::Integer) => "integer".into(),
        TypeInfo::Basic(BasicType::Boolean) => "boolean".into(),
        TypeInfo::Basic(BasicType::Char) => "char".into(),
        TypeInfo::Basic(BasicType::Float) => "float".into(),
        TypeInfo::Enum(e) => format!("enum {}", e.name),
        TypeInfo::Record(_) => "record".into(),
        TypeInfo::Sum(_) => "record of".into(),
        TypeInfo::Array(a) => {
            format!(
                "array[{}..{}] of {}",
                a.low_bound,
                a.high_bound,
                type_desc(&a.elem_ty)
            )
        }
    }
}
