use std::collections::{HashMap, HashSet};

use crate::ast::*;

#[derive(Debug, Clone)]
pub enum TypeInfo {
    Basic(BasicType),
    Enum(EnumInfo),
    Subrange(SubrangeInfo),
    Set(SetInfo),
    Pointer(String),
    Nil,
    Record(RecordInfo),
    Array(ArrayInfo),
}

#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub name: String,
    pub low: i32,
    pub high: i32,
}

#[derive(Debug, Clone)]
pub struct SubrangeInfo {
    pub base: Box<TypeInfo>,
    pub low: i32,
    pub high: i32,
}

#[derive(Debug, Clone)]
pub struct SetInfo {
    pub elem_ty: Box<TypeInfo>,
    pub low: i32,
}

#[derive(Debug, Clone)]
pub struct RecordInfo {
    pub fields: HashMap<String, FieldInfo>,
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub offset_bytes: u32,
    pub ty: TypeInfo,
    pub variant_checks: Vec<VariantCheckInfo>,
}

#[derive(Debug, Clone)]
pub struct VariantCheckInfo {
    pub tag_offset_bytes: u32,
    pub allowed_ranges: Vec<(i32, i32)>,
}

#[derive(Debug, Clone)]
pub struct ArrayInfo {
    pub low: i32,
    pub high: i32,
    pub len: u32,
    pub elem_ty: Box<TypeInfo>,
    pub elem_size_bytes: u32,
    pub size_bytes: u32,
}

#[derive(Debug, Clone)]
pub struct ParamSig {
    pub ty: TypeInfo,
    pub by_ref: bool,
    pub conformant: Option<ConformantArrayParam>,
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
    pub routines: HashMap<String, RoutineSig>,
}

#[derive(Debug, Clone)]
pub enum ConstVal {
    I32(i32),
    U32(u32),
    Bool(bool),
    Real(u32),
    EnumVal { type_name: String, ordinal: i32 },
}

impl Env {
    pub fn new() -> Self {
        let mut types = HashMap::new();
        types.insert("integer".to_string(), TypeInfo::Basic(BasicType::Integer));
        types.insert("boolean".to_string(), TypeInfo::Basic(BasicType::Boolean));
        types.insert("char".to_string(), TypeInfo::Basic(BasicType::Char));
        types.insert("real".to_string(), TypeInfo::Basic(BasicType::Real));
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
        TypeRef::PointerNamed(n) => Ok(TypeInfo::Pointer(n.clone())),
        TypeRef::Subrange { low, high } => build_subrange_info(env, low, high),
        TypeRef::Set(elem) => build_set_info(env, elem),
        TypeRef::Array { dims, elem } => build_array_info(env, dims, elem),
    }
}

fn conformant_param_type(env: &Env, c: &ConformantArrayParam) -> Result<TypeInfo, String> {
    let mut ty = tyref_to_info(env, &c.elem_ty)?;
    for _ in c.dims.iter().rev() {
        let elem_size_bytes = sizeof_type(&ty)?;
        ty = TypeInfo::Array(ArrayInfo {
            low: 0,
            high: 0,
            len: 0,
            elem_ty: Box::new(ty),
            elem_size_bytes,
            size_bytes: 0,
        });
    }
    Ok(ty)
}

pub fn build_subrange_info(
    env: &Env,
    low: &ConstExpr,
    high: &ConstExpr,
) -> Result<TypeInfo, String> {
    let lv = eval_const(env, low)?;
    let hv = eval_const(env, high)?;
    let base = match (&lv, &hv) {
        (ConstVal::I32(_), ConstVal::I32(_)) => TypeInfo::Basic(BasicType::Integer),
        (ConstVal::U32(_), ConstVal::U32(_)) => TypeInfo::Basic(BasicType::Char),
        (ConstVal::EnumVal { type_name: a, .. }, ConstVal::EnumVal { type_name: b, .. })
            if a == b =>
        {
            env.types
                .get(a)
                .cloned()
                .ok_or_else(|| format!("unknown type: {a}"))?
        }
        _ => return Err("subrange bounds must share the same ordinal type".into()),
    };
    let low_i = ordinal_const_value(&lv)?;
    let high_i = ordinal_const_value(&hv)?;
    if low_i > high_i {
        return Err("subrange low bound must be <= high bound".into());
    }
    Ok(TypeInfo::Subrange(SubrangeInfo {
        base: Box::new(base),
        low: low_i,
        high: high_i,
    }))
}

pub fn build_set_info(env: &Env, elem: &TypeRef) -> Result<TypeInfo, String> {
    let elem_ty = tyref_to_info(env, elem)?;
    let (low, high) = ordinal_bounds(&elem_ty)?;
    if low < 0 || high > 31 {
        return Err("set base type must fit within 0..31".into());
    }
    Ok(TypeInfo::Set(SetInfo {
        elem_ty: Box::new(elem_ty),
        low,
    }))
}

pub fn build_array_info(env: &Env, dims: &[ArrayDim], elem: &TypeRef) -> Result<TypeInfo, String> {
    let mut t = tyref_to_info(env, elem)?;
    for d in dims.iter().rev() {
        let dim_ty = build_subrange_info(env, &d.low, &d.high)?;
        let (low, high) = ordinal_bounds(&dim_ty)?;
        let len = (high - low + 1) as u32;
        let esz = sizeof_type(&t)?;
        let sz = len
            .checked_mul(esz)
            .ok_or_else(|| "array size overflow".to_string())?;
        t = TypeInfo::Array(ArrayInfo {
            low,
            high,
            len,
            elem_ty: Box::new(t),
            elem_size_bytes: esz,
            size_bytes: sz,
        });
    }
    Ok(t)
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
            TypeSpec::Enum(members) => {
                let mut variants = HashMap::new();
                for (idx, name) in members.iter().enumerate() {
                    if variants.insert(name.clone(), idx as i32).is_some() {
                        return Err(format!("duplicate enum value in {scope}: {name}"));
                    }
                    env.consts.insert(
                        name.clone(),
                        ConstVal::EnumVal {
                            type_name: td.name.clone(),
                            ordinal: idx as i32,
                        },
                    );
                }
                TypeInfo::Enum(EnumInfo {
                    name: td.name.clone(),
                    low: 0,
                    high: members.len() as i32 - 1,
                })
            }
            TypeSpec::Subrange { low, high } => build_subrange_info(env, low, high)?,
            TypeSpec::Set(elem) => build_set_info(env, elem)?,
            TypeSpec::Record { fields, variant } => {
                let mut ftab = HashMap::new();
                let offset = layout_record_members(env, fields, variant, &mut ftab, 0, scope)?;
                TypeInfo::Record(RecordInfo {
                    fields: ftab,
                    size_bytes: offset,
                })
            }
            TypeSpec::Array { dims, elem } => build_array_info(env, dims, elem)?,
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
            env.vars
                .insert(vd.name.clone(), tyref_to_info(env, &vd.ty)?);
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
        let params = params
            .iter()
            .map(|p| {
                Ok(ParamSig {
                    ty: if let Some(c) = &p.conformant {
                        conformant_param_type(env, c)?
                    } else {
                        tyref_to_info(env, &p.ty)?
                    },
                    by_ref: p.by_ref || p.conformant.is_some(),
                    conformant: p.conformant.clone(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let ret = ret_ty.map(|t| tyref_to_info(env, t)).transpose()?;
        env.routines.insert(scoped, RoutineSig { params, ret });
    }

    for r in &block.routines {
        match r {
            RoutineDecl::Procedure(p) => {
                collect_block_decls(env, &p.block, false, &format!("{scope}::{}", p.name))?
            }
            RoutineDecl::Function(f) => {
                collect_block_decls(env, &f.block, false, &format!("{scope}::{}", f.name))?
            }
        }
    }

    Ok(())
}

fn layout_record_members(
    env: &Env,
    fields: &[FieldDecl],
    variant: &Option<VariantPart>,
    ftab: &mut HashMap<String, FieldInfo>,
    offset: u32,
    scope: &str,
) -> Result<u32, String> {
    layout_record_members_checked(env, fields, variant, ftab, offset, scope, &[])
}

fn layout_record_members_checked(
    env: &Env,
    fields: &[FieldDecl],
    variant: &Option<VariantPart>,
    ftab: &mut HashMap<String, FieldInfo>,
    mut offset: u32,
    scope: &str,
    active_checks: &[VariantCheckInfo],
) -> Result<u32, String> {
    for f in fields {
        let fty = tyref_to_info(env, &f.ty)?;
        let finfo = FieldInfo {
            offset_bytes: offset,
            ty: fty.clone(),
            variant_checks: active_checks.to_vec(),
        };
        if ftab.insert(f.name.clone(), finfo).is_some() {
            return Err(format!("duplicate field name in {scope}: {}", f.name));
        }
        offset += sizeof_type(&fty)?;
    }
    if let Some(variant) = variant {
        if let Some(tag_name) = &variant.tag_name {
            let tag_ty = tyref_to_info(env, &variant.tag_ty)?;
            let finfo = FieldInfo {
                offset_bytes: offset,
                ty: tag_ty.clone(),
                variant_checks: active_checks.to_vec(),
            };
            if ftab.insert(tag_name.clone(), finfo).is_some() {
                return Err(format!("duplicate field name in {scope}: {tag_name}"));
            }
            offset += sizeof_type(&tag_ty)?;
        }
        let union_ofs = offset;
        let mut max_case = 0u32;
        let tag_offset = if variant.tag_name.is_some() {
            Some(union_ofs - sizeof_type(&tyref_to_info(env, &variant.tag_ty)?)?)
        } else {
            None
        };
        for case in &variant.cases {
            let mut case_checks = active_checks.to_vec();
            if let Some(tag_offset_bytes) = tag_offset {
                case_checks.push(VariantCheckInfo {
                    tag_offset_bytes,
                    allowed_ranges: case_label_ranges(env, &case.labels)?,
                });
            }
            let case_sz = layout_record_members_checked(
                env,
                &case.fields,
                &case.variant,
                ftab,
                union_ofs,
                scope,
                &case_checks,
            )? - union_ofs;
            max_case = max_case.max(case_sz);
        }
        offset += max_case;
    }
    Ok(offset)
}

fn case_label_ranges(env: &Env, labels: &[CaseLabel]) -> Result<Vec<(i32, i32)>, String> {
    let mut out = Vec::new();
    for label in labels {
        match label {
            CaseLabel::Single(c) => {
                let v = ordinal_const_value(&eval_const(env, c)?)?;
                out.push((v, v));
            }
            CaseLabel::Range(lo, hi) => {
                let lo_v = ordinal_const_value(&eval_const(env, lo)?)?;
                let hi_v = ordinal_const_value(&eval_const(env, hi)?)?;
                out.push((lo_v, hi_v));
            }
        }
    }
    Ok(out)
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
        Expr::Real(_) => Ok(TypeInfo::Basic(BasicType::Real)),
        Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
        Expr::SetLit(items) => {
            let mut elem_ty: Option<TypeInfo> = None;
            for item in items {
                match item {
                    SetItem::Single(expr) => {
                        let t = type_of_expr_scoped(env, vars, visible_routines, expr)?;
                        if !is_ordinal_type(&t) {
                            return Err("set literal items must be ordinal".into());
                        }
                        if let Some(prev) = &elem_ty {
                            if !same_type(prev, &t) {
                                return Err("set literal items must have the same type".into());
                            }
                        } else {
                            elem_ty = Some(t);
                        }
                    }
                    SetItem::Range(lo, hi) => {
                        let lt = type_of_expr_scoped(env, vars, visible_routines, lo)?;
                        let ht = type_of_expr_scoped(env, vars, visible_routines, hi)?;
                        if !is_ordinal_type(&lt) || !same_type(&lt, &ht) {
                            return Err("set range bounds must share the same ordinal type".into());
                        }
                        if let Some(prev) = &elem_ty {
                            if !same_type(prev, &lt) {
                                return Err("set literal items must have the same type".into());
                            }
                        } else {
                            elem_ty = Some(lt);
                        }
                    }
                }
            }
            let elem_ty = elem_ty.unwrap_or(TypeInfo::Basic(BasicType::Integer));
            let (low, high) = ordinal_bounds(&elem_ty)?;
            if low < 0 || high > 31 {
                return Err("set base type must fit within 0..31".into());
            }
            Ok(TypeInfo::Set(SetInfo {
                elem_ty: Box::new(elem_ty),
                low,
            }))
        }
        Expr::Var(n) => {
            if let Some(t) = vars.get(n) {
                Ok(t.clone())
            } else if let Some(c) = env.consts.get(n) {
                Ok(const_type_from_val(c.clone(), env)?)
            } else {
                Err(format!("unknown identifier: {n}"))
            }
        }
        Expr::Nil => Ok(TypeInfo::Nil),
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
        Expr::Deref(base) => match type_of_expr_scoped(env, vars, visible_routines, base)? {
            TypeInfo::Pointer(target) => env
                .types
                .get(&target)
                .cloned()
                .ok_or_else(|| format!("unknown pointed type: {target}")),
            _ => Err("deref on non-pointer".into()),
        },
        Expr::Field(base, fname) => match type_of_expr_scoped(env, vars, visible_routines, base)? {
            TypeInfo::Record(r) => r
                .fields
                .get(fname)
                .map(|fi| fi.ty.clone())
                .ok_or_else(|| format!("unknown field {fname}")),
            _ => Err("field access on non-record".into()),
        },
        Expr::Index(base, idx) => {
            let bt = type_of_expr_scoped(env, vars, visible_routines, base)?;
            let it = type_of_expr_scoped(env, vars, visible_routines, idx)?;
            expect_array_index_type(&it, "array index")?;
            match bt {
                TypeInfo::Array(a) => Ok((*a.elem_ty).clone()),
                _ => Err("index access on non-array".into()),
            }
        }
        Expr::Unary(op, inner) => {
            let it = type_of_expr_scoped(env, vars, visible_routines, inner)?;
            match op {
                UnOp::Neg => {
                    if is_real_type(&it) {
                        Ok(TypeInfo::Basic(BasicType::Real))
                    } else {
                        expect_integer_like(&it, "NEG")?;
                        Ok(TypeInfo::Basic(BasicType::Integer))
                    }
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
            use BinOp::*;
            match op {
                Add | Sub | Mul => {
                    if is_set_type(&ta) || is_set_type(&tb) {
                        if same_type(&ta, &tb) {
                            Ok(ta)
                        } else {
                            Err("set operands must have the same type".into())
                        }
                    } else if is_real_type(&ta) || is_real_type(&tb) {
                        if is_numeric_type(&ta) && is_numeric_type(&tb) {
                            Ok(TypeInfo::Basic(BasicType::Real))
                        } else {
                            Err("arithmetic operands must be numeric".into())
                        }
                    } else {
                        expect_integer_like(&ta, "arithmetic lhs")?;
                        expect_integer_like(&tb, "arithmetic rhs")?;
                        Ok(TypeInfo::Basic(BasicType::Integer))
                    }
                }
                RealDiv => {
                    if is_numeric_type(&ta) && is_numeric_type(&tb) {
                        Ok(TypeInfo::Basic(BasicType::Real))
                    } else {
                        Err("real division operands must be numeric".into())
                    }
                }
                Div | Mod => {
                    expect_integer_like(&ta, "integer arithmetic lhs")?;
                    expect_integer_like(&tb, "integer arithmetic rhs")?;
                    Ok(TypeInfo::Basic(BasicType::Integer))
                }
                And | Or | Xor => {
                    if is_set_type(&ta) || is_set_type(&tb) {
                        if same_type(&ta, &tb) {
                            Ok(ta)
                        } else {
                            Err("set operands must have the same type".into())
                        }
                    } else {
                        expect_basic(&ta, BasicType::Boolean, "boolean lhs")?;
                        expect_basic(&tb, BasicType::Boolean, "boolean rhs")?;
                        Ok(TypeInfo::Basic(BasicType::Boolean))
                    }
                }
                In => {
                    let set = match &tb {
                        TypeInfo::Set(s) => s,
                        _ => return Err("right-hand side of 'in' must be a set".into()),
                    };
                    if ordinal_compatible(&ta, &set.elem_ty) {
                        Ok(TypeInfo::Basic(BasicType::Boolean))
                    } else {
                        Err("set membership type mismatch".into())
                    }
                }
                Eq | Ne => {
                    if equality_compatible(&ta, &tb) {
                        Ok(TypeInfo::Basic(BasicType::Boolean))
                    } else {
                        Err("type mismatch in equality comparison".into())
                    }
                }
                Lt | Le | Gt | Ge => {
                    if order_compatible(&ta, &tb) {
                        Ok(TypeInfo::Basic(BasicType::Boolean))
                    } else {
                        Err("type mismatch in order comparison".into())
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
        if (p.by_ref || p.conformant.is_some()) && expr_to_lvalue(a).is_none() {
            return Err(format!(
                "argument #{arg_no} in call to {name} must be lvalue for var parameter"
            ));
        }
        let at = type_of_expr_scoped(env, vars, visible_routines, a)?;
        if let Some(conf) = &p.conformant {
            let Some((actual_dims, actual_elem)) = array_rank_and_elem(&at) else {
                return Err(format!(
                    "argument #{arg_no} type mismatch in call to {name}: expected conformant array, got {}",
                    type_desc(&at)
                ));
            };
            let declared_elem = tyref_to_info(env, &conf.elem_ty)?;
            if actual_dims != conf.dims.len() || !same_type(&declared_elem, actual_elem) {
                return Err(format!(
                    "argument #{arg_no} type mismatch in call to {name}: expected conformant array"
                ));
            }
            for dim in &conf.dims {
                let _ = tyref_to_info(env, &dim.index_ty)?;
            }
            continue;
        }
        if !assignment_compatible(&p.ty, &at) {
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
        TypeInfo::Basic(_)
        | TypeInfo::Enum(_)
        | TypeInfo::Subrange(_)
        | TypeInfo::Set(_)
        | TypeInfo::Pointer(_)
        | TypeInfo::Nil => Ok(4),
        TypeInfo::Record(r) => Ok(r.size_bytes),
        TypeInfo::Array(a) => Ok(a.size_bytes),
    }
}

pub fn eval_const(env: &Env, e: &ConstExpr) -> Result<ConstVal, String> {
    match e {
        ConstExpr::Int(i) => Ok(ConstVal::I32(*i)),
        ConstExpr::Bool(b) => Ok(ConstVal::Bool(*b)),
        ConstExpr::Char(u) => Ok(ConstVal::U32(*u)),
        ConstExpr::Real(bits) => Ok(ConstVal::Real(*bits)),
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
                    Ok(ConstVal::I32(ordinal_const_value(&eval_const(
                        env, &args[0],
                    )?)?))
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
            ConstVal::Real(bits) => Ok(ConstVal::Real((-(f32::from_bits(bits))).to_bits())),
            _ => Err("NEG on unsupported const".into()),
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
                Add | Sub | Mul | Div | Mod | And | Or | Xor => {
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
                        And => ai & bi,
                        Or => ai | bi,
                        Xor => ai ^ bi,
                        _ => unreachable!(),
                    }))
                }
                RealDiv => {
                    let af = to_f32(av)?;
                    let bf = to_f32(bv)?;
                    Ok(ConstVal::Real((af / bf).to_bits()))
                }
                Eq | Ne | Lt | Le | Gt | Ge => {
                    if matches!(av, ConstVal::Real(_)) || matches!(bv, ConstVal::Real(_)) {
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
                        Ok(ConstVal::Bool(r))
                    } else {
                        let ai = ordinal_const_value(&av)?;
                        let bi = ordinal_const_value(&bv)?;
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
                In => Err("'in' is not supported in const expr".into()),
            }
        }
    }
}

fn to_i32(v: ConstVal) -> Result<i32, String> {
    match v {
        ConstVal::I32(i) => Ok(i),
        ConstVal::Bool(b) => Ok(if b { 1 } else { 0 }),
        ConstVal::U32(u) => Ok(i32::try_from(u).map_err(|_| "u32 too large for i32".to_string())?),
        ConstVal::EnumVal { ordinal, .. } => Ok(ordinal),
        ConstVal::Real(_) => Err("real const is not integer".into()),
    }
}

fn to_f32(v: ConstVal) -> Result<f32, String> {
    match v {
        ConstVal::Real(bits) => Ok(f32::from_bits(bits)),
        ConstVal::I32(i) => Ok(i as f32),
        _ => Err("const is not numeric".into()),
    }
}

fn ordinal_const_value(v: &ConstVal) -> Result<i32, String> {
    match v {
        ConstVal::I32(i) => Ok(*i),
        ConstVal::Bool(b) => Ok(if *b { 1 } else { 0 }),
        ConstVal::U32(u) => Ok(*u as i32),
        ConstVal::EnumVal { ordinal, .. } => Ok(*ordinal),
        _ => Err("const is not ordinal".into()),
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
                    expect_array_index_type(&it, "array index")?;
                    match t {
                        TypeInfo::Array(ref a) => t = (*a.elem_ty).clone(),
                        _ => return Err("index on non-array lvalue".into()),
                    }
                }
            }
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
        visible_routines.insert(name.clone(), format!("{scope}::{name}"));
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
                    let pty = if let Some(c) = &prm.conformant {
                        for dim in &c.dims {
                            if rvars.contains_key(&dim.low_name)
                                || rvars.contains_key(&dim.high_name)
                            {
                                return Err(format!(
                                    "name conflict in procedure {}: conformant bounds conflict with an existing name",
                                    p.name
                                ));
                            }
                            let bty = tyref_to_info(env, &dim.index_ty)?;
                            rvars.insert(dim.low_name.clone(), bty.clone());
                            rvars.insert(dim.high_name.clone(), bty);
                        }
                        conformant_param_type(env, c)?
                    } else {
                        tyref_to_info(env, &prm.ty)?
                    };
                    rvars.insert(prm.name.clone(), pty);
                }
                check_block(
                    env,
                    &p.block,
                    &rvars,
                    &visible_routines,
                    &format!("{scope}::{}", p.name),
                )?;
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
                    let pty = if let Some(c) = &prm.conformant {
                        for dim in &c.dims {
                            if rvars.contains_key(&dim.low_name)
                                || rvars.contains_key(&dim.high_name)
                            {
                                return Err(format!(
                                    "name conflict in function {}: conformant bounds conflict with an existing name",
                                    f.name
                                ));
                            }
                            let bty = tyref_to_info(env, &dim.index_ty)?;
                            rvars.insert(dim.low_name.clone(), bty.clone());
                            rvars.insert(dim.high_name.clone(), bty);
                        }
                        conformant_param_type(env, c)?
                    } else {
                        tyref_to_info(env, &prm.ty)?
                    };
                    rvars.insert(prm.name.clone(), pty);
                }
                rvars.insert(f.name.clone(), tyref_to_info(env, &f.ret_ty)?);
                check_block(
                    env,
                    &f.block,
                    &rvars,
                    &visible_routines,
                    &format!("{scope}::{}", f.name),
                )?;
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
            if !assignment_compatible(&lt, &rt) {
                return Err("type mismatch in assignment".into());
            }
            if !is_scalar_like(&lt)
                && expr_to_lvalue(rhs).is_none()
                && !matches!(rhs, Expr::SetLit(_))
            {
                return Err("aggregate assignment requires lvalue rhs".into());
            }
            Ok(())
        }
        Stmt::Read(args) => {
            let mut i = 0usize;
            while i < args.len() {
                let Some(lv) = expr_to_lvalue(&args[i]) else {
                    return Err("Read arguments must be lvalues, except string max length".into());
                };
                let t = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
                if char_array_len(&t).is_some() {
                    if i + 1 >= args.len() {
                        return Err("Read on array of char requires max length".into());
                    }
                    let nt = type_of_expr_scoped(env, vars, visible_routines, &args[i + 1])?;
                    expect_integer_like(&nt, "Read string max length")?;
                    i += 2;
                    continue;
                }
                if !is_readable_scalar(&t) {
                    return Err("Read on aggregate type is not supported".into());
                }
                i += 1;
            }
            Ok(())
        }
        Stmt::ReadLn => Ok(()),
        Stmt::For {
            var,
            init,
            limit,
            body,
            ..
        } => {
            let vt = vars.get(var).ok_or_else(|| format!("unknown var: {var}"))?;
            expect_integer_like(vt, "for variable")?;
            expect_integer_like(
                &type_of_expr_scoped(env, vars, visible_routines, init)?,
                "for init",
            )?;
            expect_integer_like(
                &type_of_expr_scoped(env, vars, visible_routines, limit)?,
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
            for (labels, st) in arms {
                for label in labels {
                    match label {
                        CaseLabel::Single(ce) => {
                            let cv = eval_const(env, ce)?;
                            let token = format!(
                                "{}:{}",
                                type_desc(&const_type_from_val(cv.clone(), env)?),
                                ordinal_const_value(&cv)?
                            );
                            if !used.insert(token) {
                                return Err("duplicate case label".into());
                            }
                            let ct = const_type_from_val(cv, env)?;
                            if !assignment_compatible(&et, &ct) {
                                return Err("case arm constant type mismatch".into());
                            }
                        }
                        CaseLabel::Range(lo, hi) => {
                            let lv = eval_const(env, lo)?;
                            let hv = eval_const(env, hi)?;
                            let lt = const_type_from_val(lv.clone(), env)?;
                            let ht = const_type_from_val(hv.clone(), env)?;
                            if !assignment_compatible(&lt, &ht) || !assignment_compatible(&et, &lt)
                            {
                                return Err("case arm range type mismatch".into());
                            }
                            let lo_i = ordinal_const_value(&lv)?;
                            let hi_i = ordinal_const_value(&hv)?;
                            if lo_i > hi_i {
                                return Err("case label range low must be <= high".into());
                            }
                            for i in lo_i..=hi_i {
                                let token = format!("{}:{i}", type_desc(&lt));
                                if !used.insert(token) {
                                    return Err("duplicate case label".into());
                                }
                            }
                        }
                    }
                }
                check_stmt_with_vars(env, vars, visible_routines, st)?;
            }
            if let Some(es) = else_stmt {
                check_stmt_with_vars(env, vars, visible_routines, es)?;
            }
            Ok(())
        }
        Stmt::ProcCall(name, args) => {
            if name == "Copy" {
                return check_builtin_copy(env, vars, visible_routines, args);
            }
            if name == "Concat" {
                return check_builtin_concat(env, vars, visible_routines, args);
            }
            if name == "Delete" {
                return check_builtin_delete(env, vars, visible_routines, args);
            }
            if name == "Insert" {
                return check_builtin_insert(env, vars, visible_routines, args);
            }
            if name == "IntToHex" {
                return check_builtin_inttohex(env, vars, visible_routines, args);
            }
            if name == "SetAddr" {
                return check_builtin_setaddr(env, vars, visible_routines, args);
            }
            if name.eq_ignore_ascii_case("new") || name.eq_ignore_ascii_case("dispose") {
                return check_builtin_new_dispose(env, vars, visible_routines, name, args);
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
        Stmt::With(bases, body) => {
            let rewritten = rewrite_stmt_with(env, vars, visible_routines, body, bases)?;
            check_stmt_with_vars(env, vars, visible_routines, &rewritten)
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
                        if !is_writable_scalar(&t) && char_array_len(&t).is_none() {
                            return Err("Write/WriteLn supports only scalar values".into());
                        }
                    }
                }
            }
            Ok(())
        }
    }
}

fn rewrite_stmt_with(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    stmt: &Stmt,
    bases: &[LValue],
) -> Result<Stmt, String> {
    Ok(match stmt {
        Stmt::Empty => Stmt::Empty,
        Stmt::Compound(v) => Stmt::Compound(
            v.iter()
                .map(|s| rewrite_stmt_with(env, vars, visible_routines, s, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Stmt::Assign(lv, rhs) => Stmt::Assign(
            rewrite_lvalue_with(env, vars, visible_routines, lv, bases)?,
            rewrite_expr_with(env, vars, visible_routines, rhs, bases)?,
        ),
        Stmt::Read(args) => Stmt::Read(
            args.iter()
                .map(|e| rewrite_expr_with(env, vars, visible_routines, e, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Stmt::ReadLn => Stmt::ReadLn,
        Stmt::For {
            var,
            init,
            limit,
            downto,
            body,
        } => Stmt::For {
            var: var.clone(),
            init: rewrite_expr_with(env, vars, visible_routines, init, bases)?,
            limit: rewrite_expr_with(env, vars, visible_routines, limit, bases)?,
            downto: *downto,
            body: Box::new(rewrite_stmt_with(env, vars, visible_routines, body, bases)?),
        },
        Stmt::If(c, t, e) => Stmt::If(
            rewrite_expr_with(env, vars, visible_routines, c, bases)?,
            Box::new(rewrite_stmt_with(env, vars, visible_routines, t, bases)?),
            e.as_ref()
                .map(|s| rewrite_stmt_with(env, vars, visible_routines, s, bases).map(Box::new))
                .transpose()?,
        ),
        Stmt::With(inner, body) => {
            let mut merged = bases.to_vec();
            merged.extend(inner.iter().cloned());
            rewrite_stmt_with(env, vars, visible_routines, body, &merged)?
        }
        Stmt::While(c, b) => Stmt::While(
            rewrite_expr_with(env, vars, visible_routines, c, bases)?,
            Box::new(rewrite_stmt_with(env, vars, visible_routines, b, bases)?),
        ),
        Stmt::Repeat(v, c) => Stmt::Repeat(
            v.iter()
                .map(|s| rewrite_stmt_with(env, vars, visible_routines, s, bases))
                .collect::<Result<Vec<_>, _>>()?,
            rewrite_expr_with(env, vars, visible_routines, c, bases)?,
        ),
        Stmt::Case {
            expr,
            arms,
            else_stmt,
        } => Stmt::Case {
            expr: rewrite_expr_with(env, vars, visible_routines, expr, bases)?,
            arms: arms.clone(),
            else_stmt: else_stmt
                .as_ref()
                .map(|s| rewrite_stmt_with(env, vars, visible_routines, s, bases).map(Box::new))
                .transpose()?,
        },
        Stmt::ProcCall(name, args) => Stmt::ProcCall(
            name.clone(),
            args.iter()
                .map(|e| rewrite_expr_with(env, vars, visible_routines, e, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Stmt::Write(args) => Stmt::Write(
            args.iter()
                .map(|e| rewrite_expr_with(env, vars, visible_routines, e, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Stmt::WriteLn(args) => Stmt::WriteLn(
            args.iter()
                .map(|e| rewrite_expr_with(env, vars, visible_routines, e, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
    })
}

fn rewrite_expr_with(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    expr: &Expr,
    bases: &[LValue],
) -> Result<Expr, String> {
    Ok(match expr {
        Expr::Var(name)
            if !vars.contains_key(name)
                && !env.consts.contains_key(name)
                && !visible_routines.contains_key(name) =>
        {
            lvalue_to_expr(rewrite_lvalue_with(
                env,
                vars,
                visible_routines,
                &LValue {
                    base: name.clone(),
                    sels: vec![],
                },
                bases,
            )?)
        }
        Expr::Call(name, args) => Expr::Call(
            name.clone(),
            args.iter()
                .map(|e| rewrite_expr_with(env, vars, visible_routines, e, bases))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Expr::Field(_, _) | Expr::Index(_, _) | Expr::Deref(_) => {
            if let Some(lv) = expr_to_lvalue(expr) {
                lvalue_to_expr(rewrite_lvalue_with(
                    env,
                    vars,
                    visible_routines,
                    &lv,
                    bases,
                )?)
            } else {
                expr.clone()
            }
        }
        Expr::Unary(op, inner) => Expr::Unary(
            *op,
            Box::new(rewrite_expr_with(
                env,
                vars,
                visible_routines,
                inner,
                bases,
            )?),
        ),
        Expr::Binary(a, op, b) => Expr::Binary(
            Box::new(rewrite_expr_with(env, vars, visible_routines, a, bases)?),
            *op,
            Box::new(rewrite_expr_with(env, vars, visible_routines, b, bases)?),
        ),
        Expr::SetLit(items) => Expr::SetLit(
            items
                .iter()
                .map(|item| match item {
                    SetItem::Single(e) => rewrite_expr_with(env, vars, visible_routines, e, bases)
                        .map(SetItem::Single),
                    SetItem::Range(lo, hi) => Ok(SetItem::Range(
                        rewrite_expr_with(env, vars, visible_routines, lo, bases)?,
                        rewrite_expr_with(env, vars, visible_routines, hi, bases)?,
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?,
        ),
        _ => expr.clone(),
    })
}

fn rewrite_lvalue_with(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    lv: &LValue,
    bases: &[LValue],
) -> Result<LValue, String> {
    if vars.contains_key(&lv.base) {
        return Ok(lv.clone());
    }
    for base in bases.iter().rev() {
        let bt = resolve_lvalue_type_scoped(env, vars, visible_routines, base)?;
        if let TypeInfo::Record(r) = bt {
            if r.fields.contains_key(&lv.base) {
                let mut sels = base.sels.clone();
                sels.push(Selector::Field(lv.base.clone()));
                sels.extend(lv.sels.clone());
                return Ok(LValue {
                    base: base.base.clone(),
                    sels,
                });
            }
        }
    }
    Ok(lv.clone())
}

fn lvalue_to_expr(lv: LValue) -> Expr {
    let mut e = Expr::Var(lv.base);
    for sel in lv.sels {
        e = match sel {
            Selector::Deref => Expr::Deref(Box::new(e)),
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
    e
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
            if is_ordinal_type(&t) {
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            } else {
                Err("Ord argument must be ordinal".into())
            }
        }
        "chr" => {
            if args.len() != 1 {
                return Err("Chr requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_integer_like(&t, "Chr argument")?;
            Ok(Some(TypeInfo::Basic(BasicType::Char)))
        }
        "abs" => {
            if args.len() != 1 {
                return Err("Abs requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if is_numeric_type(&t) {
                Ok(Some(t))
            } else {
                Err("Abs argument must be numeric".into())
            }
        }
        "sqr" => {
            if args.len() != 1 {
                return Err("Sqr requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if is_numeric_type(&t) {
                Ok(Some(t))
            } else {
                Err("Sqr argument must be numeric".into())
            }
        }
        "round" | "trunc" => {
            if args.len() != 1 {
                return Err(format!("{name} requires 1 argument"));
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if is_numeric_type(&t) {
                Ok(Some(TypeInfo::Basic(BasicType::Integer)))
            } else {
                Err(format!("{name} argument must be numeric"))
            }
        }
        "succ" | "pred" => {
            if args.len() != 1 {
                return Err(format!("{name} requires 1 argument"));
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            if is_ordinal_type(&t) {
                Ok(Some(t))
            } else {
                Err(format!("{name} argument must be ordinal"))
            }
        }
        "odd" => {
            if args.len() != 1 {
                return Err("Odd requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_integer_like(&t, "Odd argument")?;
            Ok(Some(TypeInfo::Basic(BasicType::Boolean)))
        }
        "hextoint" => {
            if args.len() != 1 {
                return Err("HexToInt requires 1 argument".into());
            }
            match &args[0] {
                Expr::Str(_) => Ok(Some(TypeInfo::Basic(BasicType::Integer))),
                _ => {
                    let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
                    if char_array_len(&t).is_some() {
                        Ok(Some(TypeInfo::Basic(BasicType::Integer)))
                    } else {
                        Err("HexToInt argument must be array of char or string literal".into())
                    }
                }
            }
        }
        "addr" => {
            if args.len() != 1 {
                return Err("Addr requires 1 argument".into());
            }
            let _ = expr_to_lvalue(&args[0]).ok_or("Addr argument must be an lvalue")?;
            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
        }
        "pos" => {
            if args.len() != 2 {
                return Err("Pos requires 2 arguments".into());
            }
            expect_string_like_expr(env, vars, visible_routines, &args[0], "Pos first argument")?;
            expect_string_like_expr(env, vars, visible_routines, &args[1], "Pos second argument")?;
            Ok(Some(TypeInfo::Basic(BasicType::Integer)))
        }
        "upcase" => {
            if args.len() != 1 {
                return Err("UpCase requires 1 argument".into());
            }
            let t = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
            expect_basic(&t, BasicType::Char, "UpCase argument")?;
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

fn check_builtin_inttohex(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 4 {
        return Err("IntToHex requires 4 arguments".into());
    }
    let vt = type_of_expr_scoped(env, vars, visible_routines, &args[0])?;
    expect_integer_like(&vt, "IntToHex value")?;
    let lv =
        expr_to_lvalue(&args[1]).ok_or("IntToHex second argument must be lvalue char array")?;
    let at = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    let Some(_) = char_array_len(&at) else {
        return Err("IntToHex second argument must be array of char".into());
    };
    let mt = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
    expect_integer_like(&mt, "IntToHex max length")?;
    let ft = type_of_expr_scoped(env, vars, visible_routines, &args[3])?;
    expect_basic(&ft, BasicType::Boolean, "IntToHex zero-fill flag")?;
    Ok(())
}

fn check_builtin_copy(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 2 {
        return Err("Copy requires 2 arguments".into());
    }
    expect_string_like_expr(env, vars, visible_routines, &args[0], "Copy source")?;
    expect_char_array_lvalue_expr(env, vars, visible_routines, &args[1], "Copy destination")
}

fn check_builtin_concat(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 3 {
        return Err("Concat requires 3 arguments".into());
    }
    expect_string_like_expr(env, vars, visible_routines, &args[0], "Concat first source")?;
    expect_string_like_expr(
        env,
        vars,
        visible_routines,
        &args[1],
        "Concat second source",
    )?;
    expect_char_array_lvalue_expr(env, vars, visible_routines, &args[2], "Concat destination")
}

fn check_builtin_delete(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 3 {
        return Err("Delete requires 3 arguments".into());
    }
    expect_char_array_lvalue_expr(env, vars, visible_routines, &args[0], "Delete target")?;
    let idx_ty = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
    expect_integer_like(&idx_ty, "Delete index")?;
    let count_ty = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
    expect_integer_like(&count_ty, "Delete count")
}

fn check_builtin_insert(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 3 {
        return Err("Insert requires 3 arguments".into());
    }
    expect_string_like_expr(env, vars, visible_routines, &args[0], "Insert source")?;
    expect_char_array_lvalue_expr(env, vars, visible_routines, &args[1], "Insert destination")?;
    let idx_ty = type_of_expr_scoped(env, vars, visible_routines, &args[2])?;
    expect_integer_like(&idx_ty, "Insert index")
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

fn check_builtin_setaddr(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    args: &[Expr],
) -> Result<(), String> {
    if args.len() != 2 {
        return Err("SetAddr requires 2 arguments".into());
    }
    let lv = expr_to_lvalue(&args[0]).ok_or("SetAddr first argument must be lvalue pointer")?;
    let ptr_ty = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    match ptr_ty {
        TypeInfo::Pointer(_) => {}
        _ => return Err("SetAddr first argument must be pointer".into()),
    }
    let addr_ty = type_of_expr_scoped(env, vars, visible_routines, &args[1])?;
    expect_integer_like(&addr_ty, "SetAddr address")
}

fn const_type_from_val(v: ConstVal, env: &Env) -> Result<TypeInfo, String> {
    Ok(match v {
        ConstVal::I32(_) => TypeInfo::Basic(BasicType::Integer),
        ConstVal::U32(_) => TypeInfo::Basic(BasicType::Char),
        ConstVal::Bool(_) => TypeInfo::Basic(BasicType::Boolean),
        ConstVal::Real(_) => TypeInfo::Basic(BasicType::Real),
        ConstVal::EnumVal { type_name, .. } => env
            .types
            .get(&type_name)
            .cloned()
            .ok_or_else(|| format!("unknown type: {type_name}"))?,
    })
}

fn expect_basic(t: &TypeInfo, want: BasicType, what: &str) -> Result<(), String> {
    match scalar_base_type(t) {
        Some(b) if std::mem::discriminant(&b) == std::mem::discriminant(&want) => Ok(()),
        _ => Err(format!("type error in {what}")),
    }
}

fn expect_integer_like(t: &TypeInfo, what: &str) -> Result<(), String> {
    if is_integer_like(t) {
        Ok(())
    } else {
        Err(format!("type error in {what}"))
    }
}

fn expect_array_index_type(t: &TypeInfo, what: &str) -> Result<(), String> {
    if is_array_index_type(t) {
        Ok(())
    } else {
        Err(format!("type error in {what}"))
    }
}

fn same_type(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (a, b) {
        (TypeInfo::Basic(x), TypeInfo::Basic(y)) => {
            std::mem::discriminant(x) == std::mem::discriminant(y)
        }
        (TypeInfo::Enum(x), TypeInfo::Enum(y)) => x.name == y.name,
        (TypeInfo::Pointer(x), TypeInfo::Pointer(y)) => x.eq_ignore_ascii_case(y),
        (TypeInfo::Nil, TypeInfo::Nil) => true,
        (TypeInfo::Subrange(x), TypeInfo::Subrange(y)) => {
            x.low == y.low && x.high == y.high && same_type(&x.base, &y.base)
        }
        (TypeInfo::Set(x), TypeInfo::Set(y)) => same_type(&x.elem_ty, &y.elem_ty),
        (TypeInfo::Record(rx), TypeInfo::Record(ry)) => same_record(rx, ry),
        (TypeInfo::Array(ax), TypeInfo::Array(ay)) => {
            ax.low == ay.low && ax.high == ay.high && same_type(&ax.elem_ty, &ay.elem_ty)
        }
        _ => false,
    }
}

fn assignment_compatible(lhs: &TypeInfo, rhs: &TypeInfo) -> bool {
    same_type(lhs, rhs)
        || (is_real_type(lhs) && is_numeric_type(rhs))
        || (is_integer_like(lhs) && is_integer_like(rhs) && ordinal_compatible(lhs, rhs))
        || matches!((lhs, rhs), (TypeInfo::Pointer(_), TypeInfo::Nil))
}

fn equality_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
    same_type(a, b)
        || (is_numeric_type(a) && is_numeric_type(b))
        || (is_integer_like(a) && is_integer_like(b) && ordinal_compatible(a, b))
        || matches!(
            (a, b),
            (TypeInfo::Pointer(_), TypeInfo::Nil) | (TypeInfo::Nil, TypeInfo::Pointer(_))
        )
}

fn order_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
    (is_numeric_type(a) && is_numeric_type(b))
        || (is_integer_like(a) && is_integer_like(b) && ordinal_compatible(a, b))
        || (is_set_type(a) && is_set_type(b) && same_type(a, b))
}

fn ordinal_compatible(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (ordinal_root(a), ordinal_root(b)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

fn ordinal_root(t: &TypeInfo) -> Option<String> {
    match t {
        TypeInfo::Basic(BasicType::Integer) => Some("integer".into()),
        TypeInfo::Basic(BasicType::Boolean) => Some("boolean".into()),
        TypeInfo::Basic(BasicType::Char) => Some("char".into()),
        TypeInfo::Enum(e) => Some(format!("enum:{}", e.name)),
        TypeInfo::Subrange(s) => ordinal_root(&s.base),
        _ => None,
    }
}

fn ordinal_bounds(t: &TypeInfo) -> Result<(i32, i32), String> {
    match t {
        TypeInfo::Basic(BasicType::Boolean) => Ok((0, 1)),
        TypeInfo::Basic(BasicType::Char) => Ok((0, 255)),
        TypeInfo::Basic(BasicType::Integer) => Ok((i32::MIN, i32::MAX)),
        TypeInfo::Enum(e) => Ok((e.low, e.high)),
        TypeInfo::Subrange(s) => Ok((s.low, s.high)),
        _ => Err("type is not ordinal".into()),
    }
}

fn scalar_base_type(t: &TypeInfo) -> Option<BasicType> {
    match t {
        TypeInfo::Basic(b) => Some(b.clone()),
        TypeInfo::Subrange(s) => scalar_base_type(&s.base),
        _ => None,
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

fn is_set_type(t: &TypeInfo) -> bool {
    matches!(t, TypeInfo::Set(_))
}

fn array_rank_and_elem(t: &TypeInfo) -> Option<(usize, &TypeInfo)> {
    let mut rank = 0usize;
    let mut cur = t;
    while let TypeInfo::Array(a) = cur {
        rank += 1;
        cur = a.elem_ty.as_ref();
    }
    if rank == 0 {
        None
    } else {
        Some((rank, cur))
    }
}

fn is_real_type(t: &TypeInfo) -> bool {
    matches!(t, TypeInfo::Basic(BasicType::Real))
}

fn is_numeric_type(t: &TypeInfo) -> bool {
    is_integer_like(t) || is_real_type(t)
}

fn is_integer_like(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(BasicType::Integer)
            | TypeInfo::Basic(BasicType::Boolean)
            | TypeInfo::Basic(BasicType::Char)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
    )
}

fn is_array_index_type(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(BasicType::Integer)
            | TypeInfo::Basic(BasicType::Char)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
    )
}

fn is_ordinal_type(t: &TypeInfo) -> bool {
    is_integer_like(t)
}

fn is_scalar_like(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Subrange(_) | TypeInfo::Set(_)
    )
}

fn is_readable_scalar(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Subrange(_)
    )
}

fn is_writable_scalar(t: &TypeInfo) -> bool {
    matches!(
        t,
        TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Subrange(_)
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

fn expect_string_like_expr(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    expr: &Expr,
    what: &str,
) -> Result<(), String> {
    if matches!(expr, Expr::Str(_)) {
        return Ok(());
    }
    let t = type_of_expr_scoped(env, vars, visible_routines, expr)?;
    if char_array_len(&t).is_some() {
        Ok(())
    } else {
        Err(format!("{what} must be array of char"))
    }
}

fn expect_char_array_lvalue_expr(
    env: &Env,
    vars: &HashMap<String, TypeInfo>,
    visible_routines: &HashMap<String, String>,
    expr: &Expr,
    what: &str,
) -> Result<(), String> {
    let lv = expr_to_lvalue(expr).ok_or_else(|| format!("{what} must be lvalue array of char"))?;
    let t = resolve_lvalue_type_scoped(env, vars, visible_routines, &lv)?;
    if char_array_len(&t).is_some() {
        Ok(())
    } else {
        Err(format!("{what} must be array of char"))
    }
}

fn type_desc(t: &TypeInfo) -> String {
    match t {
        TypeInfo::Basic(BasicType::Integer) => "integer".into(),
        TypeInfo::Basic(BasicType::Boolean) => "boolean".into(),
        TypeInfo::Basic(BasicType::Char) => "char".into(),
        TypeInfo::Basic(BasicType::Real) => "real".into(),
        TypeInfo::Enum(e) => format!("enum {}", e.name),
        TypeInfo::Subrange(s) => format!("{}..{}", s.low, s.high),
        TypeInfo::Set(s) => format!("set of {}", type_desc(&s.elem_ty)),
        TypeInfo::Pointer(n) => format!("^{n}"),
        TypeInfo::Nil => "nil".into(),
        TypeInfo::Record(_) => "record".into(),
        TypeInfo::Array(a) => format!("array[{}..{}] of {}", a.low, a.high, type_desc(&a.elem_ty)),
    }
}
