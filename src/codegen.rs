use std::collections::HashMap;

use crate::ast::*;
use crate::sema::*;

#[derive(Clone)]
struct VarAccess {
    slot: String,
    ty: TypeInfo,
    by_ref: bool,
}

#[derive(Clone)]
struct Ctx {
    vars: HashMap<String, VarAccess>,
    // simple name -> scoped key (program::Outer::Inner)
    routines: HashMap<String, String>,
}

#[derive(Clone)]
struct AddrRef {
    base_expr: String,
    offset: u32,
    dynamic_addr_expr: Option<String>,
    ty: TypeInfo,
}

pub struct ForthGen<'a> {
    env: &'a Env,
    out: String,
    indent: usize,
}

impl<'a> ForthGen<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self {
            env,
            out: String::new(),
            indent: 0,
        }
    }

    fn wln(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(s);
        self.out.push('\n');
    }

    pub fn finish(self) -> String {
        self.out
    }

    pub fn gen_program(mut self, prog: &Program) -> Result<String, String> {
        self.emit_debug_name_map(&prog.block.routines, "program");
        self.wln("");

        for c in &prog.block.consts {
            let v = eval_const(self.env, &c.expr)?;
            match v {
                ConstVal::I32(i) => self.wln(&format!("{i} CONSTANT {}", c.name)),
                ConstVal::U32(u) => self.wln(&format!("{u} CONSTANT {}", c.name)),
                ConstVal::Bool(b) => self.wln(&format!("{} CONSTANT {}", if b { 1 } else { 0 }, c.name)),
            }
        }

        for v in &prog.block.vars {
            let t = self
                .env
                .vars
                .get(&v.name)
                .ok_or_else(|| format!("internal: missing var type for {}", v.name))?;
            self.emit_storage_decl(&v.name, t)?;
        }
        self.wln("CREATE __CASE_MATCH 0 ,");
        self.wln("CREATE __WSTR_STOP 0 ,");
        self.wln("CREATE __CP_SRC 0 ,");
        self.wln("CREATE __CP_DST 0 ,");
        self.wln("CREATE __CP_N 0 ,");
        self.wln("CREATE __CP_I 0 ,");

        self.emit_slots_recursive(&prog.block.routines, "program")?;

        self.wln("");

        let main_ctx = self.main_ctx(&prog.block.routines, "program");
        self.emit_routines_recursive(&prog.block.routines, "program", &main_ctx)?;

        self.wln(": MAIN");
        self.indent += 1;
        self.gen_stmt_with_ctx(&prog.block.body, &main_ctx)?;
        self.indent -= 1;
        self.wln(";");
        self.wln("MAIN");
        Ok(self.finish())
    }

    fn emit_debug_name_map(&mut self, routines: &[RoutineDecl], scope: &str) {
        self.wln("( DEBUG NAME MAP: Pascal scoped name => generated word )");
        self.emit_debug_name_map_recursive(routines, scope);
    }

    fn emit_debug_name_map_recursive(&mut self, routines: &[RoutineDecl], scope: &str) {
        for r in routines {
            let (name, block, params, has_ret) = match r {
                RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, false),
                RoutineDecl::Function(f) => (&f.name, &f.block, &f.params, true),
            };
            let scoped = format!("{scope}::{name}");
            self.wln(&format!("( ROUTINE {scoped} => {} )", self.routine_word(&scoped)));
            for prm in params {
                self.wln(&format!(
                    "( SLOT {scoped}::{} => {} )",
                    prm.name,
                    self.slot_name(&scoped, &prm.name)
                ));
            }
            for lv in &block.vars {
                self.wln(&format!(
                    "( SLOT {scoped}::{} => {} )",
                    lv.name,
                    self.slot_name(&scoped, &lv.name)
                ));
            }
            if has_ret {
                self.wln(&format!(
                    "( SLOT {scoped}::{name} => {} )",
                    self.slot_name(&scoped, name)
                ));
            }
            self.emit_debug_name_map_recursive(&block.routines, &scoped);
        }
    }

    fn emit_slots_recursive(&mut self, routines: &[RoutineDecl], scope: &str) -> Result<(), String> {
        for r in routines {
            let (name, block, params, has_ret) = match r {
                RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, false),
                RoutineDecl::Function(f) => (&f.name, &f.block, &f.params, true),
            };
            let scoped = format!("{scope}::{name}");
            for prm in params {
                let ty = self.ty_of_typeref(&prm.ty)?;
                self.emit_storage_decl(&self.slot_name(&scoped, &prm.name), &ty)?;
            }
            for lv in &block.vars {
                let ty = self.ty_of_typeref(&lv.ty)?;
                self.emit_storage_decl(&self.slot_name(&scoped, &lv.name), &ty)?;
            }
            if has_ret {
                let ty = match r {
                    RoutineDecl::Function(f) => self.ty_of_typeref(&f.ret_ty)?,
                    _ => TypeInfo::Basic(BasicType::Integer),
                };
                self.emit_storage_decl(&self.slot_name(&scoped, name), &ty)?;
            }
            self.emit_slots_recursive(&block.routines, &scoped)?;
        }
        Ok(())
    }

    fn emit_routines_recursive(&mut self, routines: &[RoutineDecl], scope: &str, parent_ctx: &Ctx) -> Result<(), String> {
        let visible = self.extend_routine_visibility(&parent_ctx.routines, routines, scope);

        for r in routines {
            let (name, block) = match r {
                RoutineDecl::Procedure(p) => (&p.name, &p.block),
                RoutineDecl::Function(f) => (&f.name, &f.block),
            };
            let scoped = format!("{scope}::{name}");
            let mut routine_ctx = Ctx {
                vars: parent_ctx.vars.clone(),
                routines: visible.clone(),
            };
            self.extend_vars_for_routine(r, &scoped, &mut routine_ctx)?;
            let body_routines = self.extend_routine_visibility(&routine_ctx.routines, &block.routines, &scoped);
            let body_ctx = Ctx {
                vars: routine_ctx.vars.clone(),
                routines: body_routines,
            };

            self.emit_routines_recursive(&block.routines, &scoped, &routine_ctx)?;
            self.gen_routine_scoped(r, &scoped, &body_ctx)?;
            self.wln("");
        }
        Ok(())
    }

    fn gen_routine_scoped(&mut self, r: &RoutineDecl, scoped: &str, ctx: &Ctx) -> Result<(), String> {
        match r {
            RoutineDecl::Procedure(p) => {
                self.wln(&format!(": {}", self.routine_word(scoped)));
                self.indent += 1;
                for prm in p.params.iter().rev() {
                    let slot = self.slot_name(scoped, &prm.name);
                    self.wln(&format!("{slot} PVAR!"));
                }
                self.gen_stmt_with_ctx(&p.block.body, ctx)?;
                self.indent -= 1;
                self.wln(";");
            }
            RoutineDecl::Function(f) => {
                self.wln(&format!(": {}", self.routine_word(scoped)));
                self.indent += 1;
                for prm in f.params.iter().rev() {
                    let slot = self.slot_name(scoped, &prm.name);
                    self.wln(&format!("{slot} PVAR!"));
                }
                self.gen_stmt_with_ctx(&f.block.body, ctx)?;
                self.wln(&format!("{} PVAR@", self.slot_name(scoped, &f.name)));
                self.indent -= 1;
                self.wln(";");
            }
        }
        Ok(())
    }

    fn gen_stmt_with_ctx(&mut self, s: &Stmt, ctx: &Ctx) -> Result<(), String> {
        match s {
            Stmt::Empty => Ok(()),
            Stmt::Compound(stmts) => {
                for st in stmts {
                    self.gen_stmt_with_ctx(st, ctx)?;
                }
                Ok(())
            }
            Stmt::Assign(lv, rhs) => {
                let dst = self.resolve_lvalue_addr_ctx(lv, ctx)?;
                if let Expr::Str(s) = rhs {
                    self.emit_char_array_assign(&dst, s)?;
                    return Ok(());
                }
                if matches!(dst.ty, TypeInfo::Basic(_)) {
                    let rhs_code = self.gen_expr_inline_ctx(rhs, ctx)?;
                    self.emit_store(&rhs_code, &dst);
                } else {
                    let rlv = expr_to_lvalue(rhs)
                        .ok_or("aggregate assignment requires lvalue rhs in codegen")?;
                    let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                    let size = self.type_size_bytes(&dst.ty)?;
                    self.emit_aggregate_copy(&src, &dst, size);
                }
                Ok(())
            }
            Stmt::Read(lvs) => {
                for lv in lvs {
                    let dst = self.resolve_lvalue_addr_ctx(lv, ctx)?;
                    let read_word = match dst.ty {
                        TypeInfo::Basic(BasicType::Integer) => "PREAD-I32",
                        TypeInfo::Basic(BasicType::Boolean) => "PREAD-BOOL",
                        TypeInfo::Basic(BasicType::Char) => "PREAD-CHAR",
                        TypeInfo::Record(_) | TypeInfo::Array(_) => {
                            return Err("Read on aggregate type is not supported".into())
                        }
                    };
                    self.emit_store(read_word, &dst);
                }
                Ok(())
            }
            Stmt::ReadLn => {
                self.wln("PREADLN");
                Ok(())
            }
            Stmt::For {
                var,
                init,
                limit,
                downto,
                body,
            } => {
                let lv = LValue {
                    base: var.clone(),
                    sels: vec![],
                };
                let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                self.emit_store(&self.gen_expr_inline_ctx(init, ctx)?, &dst);

                self.wln("BEGIN");
                self.indent += 1;
                let cur = self.emit_load_inline(&dst);
                let lim = self.gen_expr_inline_ctx(limit, ctx)?;
                if *downto {
                    self.wln(&format!("{cur} {lim} >= WHILE"));
                } else {
                    self.wln(&format!("{cur} {lim} <= WHILE"));
                }
                self.indent += 1;
                self.gen_stmt_with_ctx(body, ctx)?;
                let step = if *downto { "1 -" } else { "1 +" };
                let upd = format!("{} {step}", self.emit_load_inline(&dst));
                self.emit_store(&upd, &dst);
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                Ok(())
            }
            Stmt::Case {
                expr,
                arms,
                else_stmt,
            } => {
                self.wln(&format!("{} >R", self.gen_expr_inline_ctx(expr, ctx)?));
                self.wln("0 __CASE_MATCH PVAR!");
                for (c, st) in arms {
                    let ctoken = self.const_to_token(c)?;
                    self.wln("__CASE_MATCH PVAR@ 0= IF");
                    self.indent += 1;
                    self.wln(&format!("R@ {ctoken} = IF"));
                    self.indent += 1;
                    self.wln("1 __CASE_MATCH PVAR!");
                    self.gen_stmt_with_ctx(st, ctx)?;
                    self.indent -= 1;
                    self.wln("THEN");
                    self.indent -= 1;
                    self.wln("THEN");
                }
                if let Some(es) = else_stmt {
                    self.wln("__CASE_MATCH PVAR@ 0= IF");
                    self.indent += 1;
                    self.gen_stmt_with_ctx(es, ctx)?;
                    self.indent -= 1;
                    self.wln("THEN");
                }
                self.wln("R> DROP");
                Ok(())
            }
            Stmt::ProcCall(name, args) => {
                if name == "ReadArr" || name == "WriteArr" {
                    return self.gen_builtin_array_io(name, args, ctx);
                }
                if name == "ReadStr" || name == "WriteStr" {
                    return self.gen_builtin_str_io(name, args, ctx);
                }
                if name == "WriteHex" {
                    if args.len() != 1 {
                        return Err("WriteHex requires 1 argument".into());
                    }
                    self.wln(&format!("{} PWRITE-HEX", self.gen_expr_inline_ctx(&args[0], ctx)?));
                    return Ok(());
                }
                let (word, _) = self.resolve_call_target(ctx, name)?;
                self.gen_call_args(name, args, ctx)?;
                self.wln(&word);
                Ok(())
            }
            Stmt::If(cond, then_s, else_s) => {
                self.wln(&format!("{} IF", self.gen_expr_inline_ctx(cond, ctx)?));
                self.indent += 1;
                self.gen_stmt_with_ctx(then_s, ctx)?;
                self.indent -= 1;
                if let Some(es) = else_s {
                    self.wln("ELSE");
                    self.indent += 1;
                    self.gen_stmt_with_ctx(es, ctx)?;
                    self.indent -= 1;
                }
                self.wln("THEN");
                Ok(())
            }
            Stmt::While(cond, body) => {
                self.wln("BEGIN");
                self.indent += 1;
                self.wln(&format!("{} WHILE", self.gen_expr_inline_ctx(cond, ctx)?));
                self.indent += 1;
                self.gen_stmt_with_ctx(body, ctx)?;
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                Ok(())
            }
            Stmt::Repeat(stmts, cond) => {
                self.wln("BEGIN");
                self.indent += 1;
                for st in stmts {
                    self.gen_stmt_with_ctx(st, ctx)?;
                }
                self.wln(&format!("{} UNTIL", self.gen_expr_inline_ctx(cond, ctx)?));
                self.indent -= 1;
                Ok(())
            }
            Stmt::Write(args) => {
                for e in args {
                    match e {
                        Expr::Str(s) => {
                            self.emit_string_write(s);
                        }
                        _ => {
                            let t = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, e)?;
                            match t {
                                TypeInfo::Basic(BasicType::Char) => {
                                    self.wln(&format!("{} PWRITE-CHAR", self.gen_expr_inline_ctx(e, ctx)?));
                                }
                                TypeInfo::Basic(BasicType::Boolean) => {
                                    self.wln(&format!("{} PWRITE-BOOL", self.gen_expr_inline_ctx(e, ctx)?));
                                }
                                _ => {
                                    self.wln(&format!("{} PWRITE-I32", self.gen_expr_inline_ctx(e, ctx)?));
                                }
                            }
                        }
                    }
                }
                Ok(())
            }
            Stmt::WriteLn(args) => {
                self.gen_stmt_with_ctx(&Stmt::Write(args.clone()), ctx)?;
                self.wln("PWRITELN");
                Ok(())
            }
        }
    }

    fn gen_expr_inline_ctx(&self, e: &Expr, ctx: &Ctx) -> Result<String, String> {
        match e {
            Expr::Int(i) => Ok(i.to_string()),
            Expr::Char(u) => Ok(u.to_string()),
            Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
            Expr::Var(n) => {
                if let Some(c) = self.env.consts.get(n) {
                    Ok(match c {
                        ConstVal::I32(i) => i.to_string(),
                        ConstVal::U32(u) => u.to_string(),
                        ConstVal::Bool(b) => {
                            if *b {
                                "1".to_string()
                            } else {
                                "0".to_string()
                            }
                        }
                    })
                } else {
                    let lv = LValue {
                        base: n.clone(),
                        sels: vec![],
                    };
                    let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    Ok(self.emit_load_inline(&a))
                }
            }
            Expr::Call(name, args) => {
                if let Some(b) = self.gen_builtin_expr_call(name, args, ctx)? {
                    return Ok(b);
                }
                let (word, _) = self.resolve_call_target(ctx, name)?;
                let mut parts = vec![];
                let argc = self.gen_call_args_inline(name, args, ctx)?;
                if !argc.is_empty() {
                    parts.push(argc);
                }
                parts.push(word);
                Ok(parts.join(" "))
            }
            Expr::Field(_, _) => {
                let lv = expr_to_lvalue(e).ok_or("field base must be variable")?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                Ok(self.emit_load_inline(&a))
            }
            Expr::Index(_, _) => {
                let lv = expr_to_lvalue(e).ok_or("index base must be variable")?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                Ok(self.emit_load_inline(&a))
            }
            Expr::Unary(op, inner) => {
                let a = self.gen_expr_inline_ctx(inner, ctx)?;
                match op {
                    UnOp::Neg => Ok(format!("{a} NEGATE")),
                    UnOp::Not => Ok(format!("{a} 0=")),
                }
            }
            Expr::Binary(a, op, b) => {
                let la = self.gen_expr_inline_ctx(a, ctx)?;
                let lb = self.gen_expr_inline_ctx(b, ctx)?;
                use BinOp::*;
                let w = match op {
                    Add => "+",
                    Sub => "-",
                    Mul => "*",
                    Eq => "=",
                    Ne => "<>",
                    Lt => "<",
                    Le => "<=",
                    Gt => ">",
                    Ge => ">=",
                };
                Ok(format!("{la} {lb} {w}"))
            }
        }
    }

    fn gen_builtin_expr_call(&self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<Option<String>, String> {
        let n = name.to_ascii_lowercase();
        match n.as_str() {
            "ord" => {
                if args.len() != 1 {
                    return Err("Ord requires 1 argument".into());
                }
                let t = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, &args[0])?;
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                let out = match t {
                    TypeInfo::Basic(BasicType::Boolean) => format!("{v} PBOOL"),
                    _ => v,
                };
                Ok(Some(out))
            }
            "chr" => {
                if args.len() != 1 {
                    return Err("Chr requires 1 argument".into());
                }
                Ok(Some(self.gen_expr_inline_ctx(&args[0], ctx)?))
            }
            "length" => {
                if args.len() != 1 {
                    return Err("Length requires 1 argument".into());
                }
                let t = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, &args[0])?;
                if let TypeInfo::Array(a) = t {
                    Ok(Some(a.len.to_string()))
                } else {
                    Err("Length argument must be array".into())
                }
            }
            "high" => {
                if args.len() != 1 {
                    return Err("High requires 1 argument".into());
                }
                let t = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, &args[0])?;
                if let TypeInfo::Array(a) = t {
                    Ok(Some((a.len as i32 - 1).to_string()))
                } else {
                    Err("High argument must be array".into())
                }
            }
            "low" => {
                if args.len() != 1 {
                    return Err("Low requires 1 argument".into());
                }
                let t = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, &args[0])?;
                if let TypeInfo::Array(_) = t {
                    Ok(Some("0".into()))
                } else {
                    Err("Low argument must be array".into())
                }
            }
            _ => Ok(None),
        }
    }

    fn resolve_call_target(&self, ctx: &Ctx, name: &str) -> Result<(String, RoutineSig), String> {
        let key = ctx
            .routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let sig = self
            .env
            .routines
            .get(key)
            .cloned()
            .ok_or_else(|| format!("internal: missing routine signature for {key}"))?;
        Ok((self.routine_word(key), sig))
    }

    fn gen_call_args(&mut self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        let (_, sig) = self.resolve_call_target(ctx, name)?;
        for (arg, p) in args.iter().zip(&sig.params) {
            if p.by_ref {
                let lv = expr_to_lvalue(arg)
                    .ok_or_else(|| format!("by-ref argument must be lvalue in call to {name}"))?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                self.wln(&self.emit_addr_inline(&a));
            } else {
                self.wln(&self.gen_expr_inline_ctx(arg, ctx)?);
            }
        }
        Ok(())
    }

    fn gen_call_args_inline(&self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<String, String> {
        let (_, sig) = self.resolve_call_target(ctx, name)?;
        let mut out = vec![];
        for (arg, p) in args.iter().zip(&sig.params) {
            if p.by_ref {
                let lv = expr_to_lvalue(arg)
                    .ok_or_else(|| format!("by-ref argument must be lvalue in call to {name}"))?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                out.push(self.emit_addr_inline(&a));
            } else {
                out.push(self.gen_expr_inline_ctx(arg, ctx)?);
            }
        }
        Ok(out.join(" "))
    }

    fn emit_store(&mut self, rhs: &str, dst: &AddrRef) {
        if let Some(addr) = &dst.dynamic_addr_expr {
            self.wln(&format!("{rhs} {addr} PVAR!"));
        } else if dst.offset == 0 {
            self.wln(&format!("{rhs} {} PVAR!", dst.base_expr));
        } else {
            self.wln(&format!("{rhs} {} {} PFIELD!", dst.base_expr, dst.offset));
        }
    }

    fn emit_load_inline(&self, src: &AddrRef) -> String {
        if let Some(addr) = &src.dynamic_addr_expr {
            format!("{addr} PVAR@")
        } else if src.offset == 0 {
            format!("{} PVAR@", src.base_expr)
        } else {
            format!("{} {} PFIELD@", src.base_expr, src.offset)
        }
    }

    fn emit_addr_inline(&self, a: &AddrRef) -> String {
        if let Some(addr) = &a.dynamic_addr_expr {
            addr.clone()
        } else if a.offset == 0 {
            a.base_expr.clone()
        } else {
            format!("{} {} +", a.base_expr, a.offset)
        }
    }

    fn resolve_lvalue_addr_ctx(&self, lv: &LValue, ctx: &Ctx) -> Result<AddrRef, String> {
        let v = ctx
            .vars
            .get(&lv.base)
            .ok_or_else(|| format!("unknown var: {}", lv.base))?;
        let base_expr = if v.by_ref {
            format!("{} PVAR@", v.slot)
        } else {
            v.slot.clone()
        };
        let mut t = v.ty.clone();
        let mut offset = 0u32;
        let mut dynamic_addr_expr: Option<String> = None;
        for sel in &lv.sels {
            match sel {
                Selector::Field(f) => match t {
                    TypeInfo::Record(ref r) => {
                        let fi = r
                            .fields
                            .get(f)
                            .ok_or_else(|| format!("unknown field: {f}"))?;
                        if let Some(cur) = dynamic_addr_expr.take() {
                            dynamic_addr_expr = Some(format!("{cur} {} +", fi.offset_bytes));
                        } else {
                            offset += fi.offset_bytes;
                        }
                        t = fi.ty.clone();
                    }
                    _ => return Err("field on non-record lvalue".into()),
                },
                Selector::Index(idxs) => {
                    for ix in idxs {
                    let (len, elem_size, elem_ty) = match t {
                        TypeInfo::Array(ref a) => (a.len, a.elem_size_bytes, (*a.elem_ty).clone()),
                        _ => return Err("index on non-array lvalue".into()),
                    };
                    let idx_expr = self.gen_expr_inline_ctx(ix, ctx)?;
                    // Minimal runtime bounds check hook point can be inserted here if needed.
                    let _ = len;
                    let scaled = if elem_size == 1 {
                        idx_expr
                    } else {
                        format!("{idx_expr} {elem_size} *")
                    };
                    let base_addr = if let Some(cur) = dynamic_addr_expr.take() {
                        cur
                    } else if offset == 0 {
                        base_expr.clone()
                    } else {
                        format!("{base_expr} {offset} +")
                    };
                    dynamic_addr_expr = Some(format!("{base_addr} {scaled} +"));
                    offset = 0;
                    t = elem_ty;
                    }
                }
            }
        }
        Ok(AddrRef {
            base_expr,
            offset,
            dynamic_addr_expr,
            ty: t,
        })
    }

    fn emit_string_write(&mut self, s: &str) {
        let safe = s
            .chars()
            .all(|c| c != '"' && !c.is_control() && (c as u32) <= 0x7E);
        if safe {
            self.wln(&format!("S\" {s}\" PWRITE-STR"));
            return;
        }
        for ch in s.chars() {
            self.wln(&format!("{} PWRITE-CHAR", ch as u32));
        }
    }

    fn emit_aggregate_copy(&mut self, src: &AddrRef, dst: &AddrRef, size_bytes: u32) {
        let cells = size_bytes / 4;
        if cells > 8 {
            self.wln(&format!("{} __CP_SRC PVAR!", self.emit_addr_inline(src)));
            self.wln(&format!("{} __CP_DST PVAR!", self.emit_addr_inline(dst)));
            self.wln(&format!("{cells} __CP_N PVAR!"));
            self.wln("0 __CP_I PVAR!");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln("__CP_I PVAR@ __CP_N PVAR@ < WHILE");
            self.indent += 1;
            self.wln("__CP_SRC PVAR@ __CP_I PVAR@ 4 * + PVAR@");
            self.wln("__CP_DST PVAR@ __CP_I PVAR@ 4 * + PVAR!");
            self.wln("__CP_I PVAR@ 1 + __CP_I PVAR!");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            return;
        }
        for i in 0..cells {
            let ofs = i * 4;
            let rhs = self.emit_load_at(src, ofs);
            self.emit_store_at(&rhs, dst, ofs);
        }
    }

    fn emit_load_at(&self, src: &AddrRef, add_ofs: u32) -> String {
        if let Some(addr) = &src.dynamic_addr_expr {
            if add_ofs == 0 {
                format!("{addr} PVAR@")
            } else {
                format!("{addr} {add_ofs} + PVAR@")
            }
        } else {
            let total = src.offset + add_ofs;
            if total == 0 {
                format!("{} PVAR@", src.base_expr)
            } else {
                format!("{} {total} PFIELD@", src.base_expr)
            }
        }
    }

    fn emit_store_at(&mut self, rhs: &str, dst: &AddrRef, add_ofs: u32) {
        if let Some(addr) = &dst.dynamic_addr_expr {
            if add_ofs == 0 {
                self.wln(&format!("{rhs} {addr} PVAR!"));
            } else {
                self.wln(&format!("{rhs} {addr} {add_ofs} + PVAR!"));
            }
        } else {
            let total = dst.offset + add_ofs;
            if total == 0 {
                self.wln(&format!("{rhs} {} PVAR!", dst.base_expr));
            } else {
                self.wln(&format!("{rhs} {} {total} PFIELD!", dst.base_expr));
            }
        }
    }

    fn emit_char_array_assign(&mut self, dst: &AddrRef, s: &str) -> Result<(), String> {
        let len = match &dst.ty {
            TypeInfo::Array(a) => match a.elem_ty.as_ref() {
                TypeInfo::Basic(BasicType::Char) => a.len,
                _ => {
                    return Err("string literal assignment requires array of char lhs".into());
                }
            },
            _ => return Err("string literal assignment requires array of char lhs".into()),
        };
        if len == 0 {
            return Ok(());
        }
        let chars: Vec<u32> = s.chars().map(|c| c as u32).collect();
        let body = len - 1;
        for i in 0..body {
            let v = chars.get(i as usize).copied().unwrap_or(0);
            self.emit_store_at(&v.to_string(), dst, i * 4);
        }
        self.emit_store_at("0", dst, (len - 1) * 4);
        Ok(())
    }

    fn emit_storage_decl(&mut self, name: &str, ty: &TypeInfo) -> Result<(), String> {
        let sz = self.type_size_bytes(ty)?;
        if sz <= 4 {
            self.wln(&format!("CREATE {name} 0 ,"));
        } else {
            self.wln(&format!("CREATE {name} 0 , {} ALLOT", sz - 4));
        }
        Ok(())
    }

    fn type_size_bytes(&self, ty: &TypeInfo) -> Result<u32, String> {
        match ty {
            TypeInfo::Basic(_) => Ok(4),
            TypeInfo::Record(r) => Ok(r.size_bytes),
            TypeInfo::Array(a) => Ok(a.size_bytes),
        }
    }

    fn gen_builtin_array_io(&mut self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 2 {
            return Err(format!("{name} requires 2 arguments"));
        }
        let lv = expr_to_lvalue(&args[0]).ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let ainfo = match &a.ty {
            TypeInfo::Array(x) => x.clone(),
            _ => return Err(format!("{name} first argument must be array")),
        };
        let elem_ty = (*ainfo.elem_ty).clone();
        match elem_ty {
            TypeInfo::Basic(_) => {}
            _ => return Err(format!("{name} supports only scalar element arrays")),
        }
        let len_expr = self.gen_expr_inline_ctx(&args[1], ctx)?;
        let base_addr = self.emit_addr_inline(&a);

        self.wln("0 >R");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln(&format!("R@ {len_expr} < WHILE"));
        self.indent += 1;
        let cell_addr = if ainfo.elem_size_bytes == 1 {
            format!("{base_addr} R@ +")
        } else {
            format!("{base_addr} R@ {} * +", ainfo.elem_size_bytes)
        };
        if name == "ReadArr" {
            let rw = match elem_ty {
                TypeInfo::Basic(BasicType::Integer) => "PREAD-I32",
                TypeInfo::Basic(BasicType::Boolean) => "PREAD-BOOL",
                TypeInfo::Basic(BasicType::Char) => "PREAD-CHAR",
                _ => unreachable!(),
            };
            self.wln(&format!("{rw} {cell_addr} PVAR!"));
        } else {
            let ww = match elem_ty {
                TypeInfo::Basic(BasicType::Integer) => "PWRITE-I32",
                TypeInfo::Basic(BasicType::Boolean) => "PWRITE-BOOL",
                TypeInfo::Basic(BasicType::Char) => "PWRITE-CHAR",
                _ => unreachable!(),
            };
            self.wln(&format!("{cell_addr} PVAR@ {ww}"));
            self.wln("PWRITELN");
        }
        self.wln("R> 1 + >R");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("R> DROP");
        Ok(())
    }

    fn gen_builtin_str_io(&mut self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        let lv = expr_to_lvalue(&args[0]).ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let arr_len = match &a.ty {
            TypeInfo::Array(ai) => match ai.elem_ty.as_ref() {
                TypeInfo::Basic(BasicType::Char) => ai.len,
                _ => return Err(format!("{name} first argument must be array of char")),
            },
            _ => return Err(format!("{name} first argument must be array of char")),
        };
        let base_addr = self.emit_addr_inline(&a);
        if name == "ReadStr" {
            let n = self.gen_expr_inline_ctx(&args[1], ctx)?;
            let cap = arr_len.saturating_sub(1);
            self.wln("0 >R");
            self.wln("BEGIN");
            self.indent += 1;
            self.wln(&format!("R@ {n} < R@ {cap} < AND WHILE"));
            self.indent += 1;
            self.wln(&format!("PREAD-CHAR {base_addr} R@ 4 * + PVAR!"));
            self.wln("R> 1 + >R");
            self.indent -= 1;
            self.indent -= 1;
            self.wln("REPEAT");
            self.wln(&format!("0 {base_addr} R@ 4 * + PVAR!"));
            self.wln("R> DROP");
            return Ok(());
        }

        self.wln("0 __WSTR_STOP PVAR!");
        self.wln("0 >R");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln(&format!("__WSTR_STOP PVAR@ 0= R@ {arr_len} < AND WHILE"));
        self.indent += 1;
        self.wln(&format!("{base_addr} R@ 4 * + PVAR@ DUP 0= IF"));
        self.indent += 1;
        self.wln("DROP");
        self.wln("1 __WSTR_STOP PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("PWRITE-CHAR");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("R> 1 + >R");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("R> DROP");
        Ok(())
    }

    fn const_to_token(&self, c: &ConstExpr) -> Result<String, String> {
        Ok(match eval_const(self.env, c)? {
            ConstVal::I32(i) => i.to_string(),
            ConstVal::U32(u) => u.to_string(),
            ConstVal::Bool(b) => {
                if b {
                    "1".to_string()
                } else {
                    "0".to_string()
                }
            }
        })
    }

    fn routine_word(&self, scoped: &str) -> String {
        format!("R_{}", self.short_symbol(scoped, 12))
    }

    fn slot_name(&self, scoped: &str, vname: &str) -> String {
        format!("S_{}", self.short_symbol(&format!("{scoped}::{vname}"), 12))
    }

    fn short_symbol(&self, raw: &str, max_len: usize) -> String {
        let cleaned: String = raw
            .chars()
            .map(|c| {
                if c.is_ascii_alphanumeric() {
                    c.to_ascii_uppercase()
                } else {
                    '_'
                }
            })
            .collect();
        if cleaned.len() <= max_len {
            return cleaned;
        }
        let mut h: u32 = 2166136261;
        for b in cleaned.as_bytes() {
            h ^= *b as u32;
            h = h.wrapping_mul(16777619);
        }
        let suffix = format!("{:06X}", h & 0x00FF_FFFF);
        let head_len = max_len.saturating_sub(7);
        let head = &cleaned[..head_len];
        format!("{head}_{suffix}")
    }

    fn main_ctx(&self, top_routines: &[RoutineDecl], scope: &str) -> Ctx {
        let mut vars = HashMap::new();
        for (n, t) in &self.env.vars {
            vars.insert(
                n.clone(),
                VarAccess {
                    slot: n.clone(),
                    ty: t.clone(),
                    by_ref: false,
                },
            );
        }
        let routines = self.extend_routine_visibility(&HashMap::new(), top_routines, scope);
        Ctx { vars, routines }
    }

    fn extend_vars_for_routine(&self, r: &RoutineDecl, scoped: &str, ctx: &mut Ctx) -> Result<(), String> {
        match r {
            RoutineDecl::Procedure(p) => {
                for prm in &p.params {
                    let ty = self.ty_of_typeref(&prm.ty)?;
                    ctx.vars.insert(
                        prm.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &prm.name),
                            ty,
                            by_ref: prm.by_ref,
                        },
                    );
                }
                for lv in &p.block.vars {
                    let ty = self.ty_of_typeref(&lv.ty)?;
                    ctx.vars.insert(
                        lv.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &lv.name),
                            ty,
                            by_ref: false,
                        },
                    );
                }
            }
            RoutineDecl::Function(f) => {
                for prm in &f.params {
                    let ty = self.ty_of_typeref(&prm.ty)?;
                    ctx.vars.insert(
                        prm.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &prm.name),
                            ty,
                            by_ref: prm.by_ref,
                        },
                    );
                }
                for lv in &f.block.vars {
                    let ty = self.ty_of_typeref(&lv.ty)?;
                    ctx.vars.insert(
                        lv.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &lv.name),
                            ty,
                            by_ref: false,
                        },
                    );
                }
                ctx.vars.insert(
                    f.name.clone(),
                    VarAccess {
                        slot: self.slot_name(scoped, &f.name),
                        ty: self.ty_of_typeref(&f.ret_ty)?,
                        by_ref: false,
                    },
                );
            }
        }
        Ok(())
    }

    fn extend_routine_visibility(
        &self,
        parent: &HashMap<String, String>,
        routines: &[RoutineDecl],
        scope: &str,
    ) -> HashMap<String, String> {
        let mut out = parent.clone();
        for r in routines {
            let name = match r {
                RoutineDecl::Procedure(p) => &p.name,
                RoutineDecl::Function(f) => &f.name,
            };
            out.insert(name.clone(), format!("{scope}::{name}"));
        }
        out
    }

    fn ty_of_typeref(&self, tr: &TypeRef) -> Result<TypeInfo, String> {
        match tr {
            TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
            TypeRef::Named(n) => self
                .env
                .types
                .get(n)
                .cloned()
                .ok_or_else(|| format!("unknown type: {n}")),
        }
    }

    fn ctx_to_types(&self, ctx: &Ctx) -> HashMap<String, TypeInfo> {
        let mut m = HashMap::new();
        for (k, v) in &ctx.vars {
            m.insert(k.clone(), v.ty.clone());
        }
        m
    }
}
