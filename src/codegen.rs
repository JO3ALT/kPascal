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
    routine_frames: HashMap<String, Vec<String>>,
    sum_case_bind_sp: usize,
}

impl<'a> ForthGen<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self {
            env,
            out: String::new(),
            indent: 0,
            routine_frames: HashMap::new(),
            sum_case_bind_sp: 0,
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
        self.collect_routine_frames(&prog.block.routines, "program");
        let max_agg_ret_bytes = self.max_aggregate_return_bytes(&prog.block.routines)?;
        self.emit_debug_name_map(&prog.block.routines, "program");
        self.wln("");

        for c in &prog.block.consts {
            let v = eval_const(self.env, &c.expr)?;
            match v {
                ConstVal::I32(i) => self.wln(&format!("{i} CONSTANT {}", c.name)),
                ConstVal::U32(u) => self.wln(&format!("{u} CONSTANT {}", c.name)),
                ConstVal::Bool(b) => {
                    self.wln(&format!("{} CONSTANT {}", if b { 1 } else { 0 }, c.name))
                }
                ConstVal::F32(bits) => self.wln(&format!("{bits} CONSTANT {}", c.name)),
                ConstVal::EnumTag { ordinal, .. } => {
                    self.wln(&format!("{ordinal} CONSTANT {}", c.name))
                }
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
        self.wln("CREATE __AF_SRC 0 ,");
        self.wln("CREATE __AF_DST 0 ,");
        self.wln("CREATE __AF_N 0 ,");
        self.wln("CREATE __AF_I 0 ,");
        self.wln("CREATE __AF_ACC 0 ,");
        self.wln("CREATE __AF_CNT 0 ,");
        self.wln("CREATE __NEWP 0 ,");
        self.wln("CREATE __LF_SRC 0 ,");
        self.wln("CREATE __LF_HEAD 0 ,");
        self.wln("CREATE __LF_TAIL 0 ,");
        self.wln("CREATE __LF_NODE 0 ,");
        self.wln("CREATE __EQ_A 0 ,");
        self.wln("CREATE __EQ_B 0 ,");
        self.wln("CREATE __EQ_N 0 ,");
        self.wln("CREATE __EQ_I 0 ,");
        self.wln("CREATE __EQ_OK 0 ,");
        self.wln("CREATE __CALL_RET 0 ,");
        self.wln("CREATE __CRS 0 ,");
        self.emit_storage_bytes_decl("__CRA", max_agg_ret_bytes.max(4));
        for i in 0..32 {
            self.wln(&format!("CREATE __SCB{i} 0 ,"));
        }
        self.wln(": PAGG-EQ");
        self.indent += 1;
        self.wln("__EQ_N PVAR!");
        self.wln("__EQ_B PVAR!");
        self.wln("__EQ_A PVAR!");
        self.wln("1 __EQ_OK PVAR!");
        self.wln("0 __EQ_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__EQ_OK PVAR@ 0 <> __EQ_I PVAR@ __EQ_N PVAR@ < AND WHILE");
        self.indent += 1;
        self.wln("__EQ_A PVAR@ __EQ_I PVAR@ 4 * + PVAR@");
        self.wln("__EQ_B PVAR@ __EQ_I PVAR@ 4 * + PVAR@");
        self.wln("= 0= IF");
        self.indent += 1;
        self.wln("0 __EQ_OK PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__EQ_I PVAR@ 1 + __EQ_I PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("__EQ_OK PVAR@");
        self.indent -= 1;
        self.wln(";");

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
            self.wln(&format!(
                "( ROUTINE {scoped} => {} )",
                self.routine_word(&scoped)
            ));
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

    fn emit_slots_recursive(
        &mut self,
        routines: &[RoutineDecl],
        scope: &str,
    ) -> Result<(), String> {
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

    fn emit_routines_recursive(
        &mut self,
        routines: &[RoutineDecl],
        scope: &str,
        parent_ctx: &Ctx,
    ) -> Result<(), String> {
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
            let body_routines =
                self.extend_routine_visibility(&routine_ctx.routines, &block.routines, &scoped);
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

    fn gen_routine_scoped(
        &mut self,
        r: &RoutineDecl,
        scoped: &str,
        ctx: &Ctx,
    ) -> Result<(), String> {
        match r {
            RoutineDecl::Procedure(p) => {
                self.wln(&format!(": {}", self.routine_word(scoped)));
                self.indent += 1;
                for prm in p.params.iter().rev() {
                    let slot = self.slot_name(scoped, &prm.name);
                    let ty = self.ty_of_typeref(&prm.ty)?;
                    self.emit_param_store_from_stack(&slot, &ty, prm.by_ref)?;
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
                    let ty = self.ty_of_typeref(&prm.ty)?;
                    self.emit_param_store_from_stack(&slot, &ty, prm.by_ref)?;
                }
                self.gen_stmt_with_ctx(&f.block.body, ctx)?;
                let ret_ty = self.ty_of_typeref(&f.ret_ty)?;
                let ret_slot = self.slot_name(scoped, &f.name);
                match ret_ty {
                    TypeInfo::Basic(_)
                    | TypeInfo::Enum(_)
                    | TypeInfo::Pointer(_)
                    | TypeInfo::Nil => self.wln(&format!("{ret_slot} PVAR@")),
                    TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                        self.wln(&ret_slot)
                    }
                }
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
                self.gen_assign_expr_to_dst(&dst, rhs, ctx)
            }
            Stmt::Read(lvs) => {
                for lv in lvs {
                    let dst = self.resolve_lvalue_addr_ctx(lv, ctx)?;
                    let read_word = match dst.ty {
                        TypeInfo::Basic(BasicType::Integer) => "PREAD-I32",
                        TypeInfo::Basic(BasicType::Boolean) => "PREAD-BOOL",
                        TypeInfo::Basic(BasicType::Char) => "PREAD-CHAR",
                        TypeInfo::Basic(BasicType::Float) => "PREAD-F32",
                        TypeInfo::Enum(_) => "PREAD-I32",
                        TypeInfo::Pointer(_) | TypeInfo::Nil => {
                            return Err("Read on pointer is not supported".into())
                        }
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
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
            Stmt::SumCase {
                expr,
                arms,
                else_stmt,
            } => self.gen_sum_case_stmt(expr, arms, else_stmt.as_deref(), ctx),
            Stmt::ProcCall(name, args) => {
                let lname = name.to_ascii_lowercase();
                if lname == "new" || lname == "dispose" {
                    return self.gen_builtin_new_dispose(name, args, ctx);
                }
                if lname == "readarr" || lname == "writearr" {
                    return self.gen_builtin_array_io(name, args, ctx);
                }
                if lname == "readstr" || lname == "writestr" {
                    return self.gen_builtin_str_io(name, args, ctx);
                }
                if lname == "writehex" {
                    if args.len() != 1 {
                        return Err("WriteHex requires 1 argument".into());
                    }
                    self.wln(&format!(
                        "{} PWRITE-HEX",
                        self.gen_expr_inline_ctx(&args[0], ctx)?
                    ));
                    return Ok(());
                }
                self.wln(&self.gen_call_inline_ctx(name, args, ctx)?);
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
                            let t = type_of_expr_scoped(
                                self.env,
                                &self.ctx_to_types(ctx),
                                &ctx.routines,
                                e,
                            )?;
                            match t {
                                TypeInfo::Basic(BasicType::Char) => {
                                    self.wln(&format!(
                                        "{} PWRITE-CHAR",
                                        self.gen_expr_inline_ctx(e, ctx)?
                                    ));
                                }
                                TypeInfo::Basic(BasicType::Boolean) => {
                                    self.wln(&format!(
                                        "{} PWRITE-BOOL",
                                        self.gen_expr_inline_ctx(e, ctx)?
                                    ));
                                }
                                TypeInfo::Basic(BasicType::Float) => {
                                    self.wln(&format!(
                                        "{} PWRITE-F32",
                                        self.gen_expr_inline_ctx(e, ctx)?
                                    ));
                                }
                                _ => {
                                    self.wln(&format!(
                                        "{} PWRITE-I32",
                                        self.gen_expr_inline_ctx(e, ctx)?
                                    ));
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

    fn gen_assign_expr_to_dst(
        &mut self,
        dst: &AddrRef,
        rhs: &Expr,
        ctx: &Ctx,
    ) -> Result<(), String> {
        if let Expr::Str(s) = rhs {
            self.emit_char_array_assign(dst, s)?;
            return Ok(());
        }
        if let Expr::Cond { arms, else_block } = rhs {
            return self.gen_cond_assign(dst, arms, else_block, ctx);
        }
        if let Expr::Call(name, args) = rhs {
            let lname = name.to_ascii_lowercase();
            if lname == "map" || lname == "filter" || lname == "fold" {
                return self.gen_builtin_list_fn_assign(name, args, dst, ctx);
            }
        }
        match &dst.ty {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_) | TypeInfo::Nil => {
                let rhs_code = self.gen_expr_inline_ctx(rhs, ctx)?;
                self.emit_store(&rhs_code, dst);
                Ok(())
            }
            TypeInfo::Record(rec) => {
                if let Expr::Ctor(name, named) = rhs {
                    return self.emit_record_ctor_into(dst, rec, name, named, ctx);
                }
                if let Expr::RecordUpdate(base, updates) = rhs {
                    return self.emit_record_update_into(dst, rec, base, updates, ctx);
                }
                if let Expr::Call(name, args) = rhs {
                    return self.gen_aggregate_call_assign(name, args, dst, ctx);
                }
                let rlv = expr_to_lvalue(rhs)
                    .ok_or("aggregate assignment requires lvalue rhs in codegen")?;
                let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                let size = self.type_size_bytes(&dst.ty)?;
                self.emit_aggregate_copy(&src, dst, size);
                Ok(())
            }
            TypeInfo::Array(_) => {
                if let Expr::ArrayLit(elems) = rhs {
                    return self.emit_array_literal_into(dst, elems, ctx);
                }
                if let Expr::ArrayUpdate(base, updates) = rhs {
                    return self.emit_array_update_into(dst, base, updates, ctx);
                }
                if let Expr::Call(name, args) = rhs {
                    return self.gen_aggregate_call_assign(name, args, dst, ctx);
                }
                let rlv = expr_to_lvalue(rhs)
                    .ok_or("aggregate assignment requires lvalue rhs in codegen")?;
                let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                let size = self.type_size_bytes(&dst.ty)?;
                self.emit_aggregate_copy(&src, dst, size);
                Ok(())
            }
            TypeInfo::Sum(sum) => self.gen_sum_assign(dst, sum, rhs, ctx),
        }
    }

    fn gen_cond_assign(
        &mut self,
        dst: &AddrRef,
        arms: &[CondExprArm],
        else_block: &CondValueBlock,
        ctx: &Ctx,
    ) -> Result<(), String> {
        if arms.is_empty() {
            return Err("COND requires at least one arm".into());
        }
        let cond0 = self.gen_expr_inline_ctx(&arms[0].cond, ctx)?;
        self.wln(&format!("{cond0} IF"));
        self.indent += 1;
        for st in &arms[0].block.stmts {
            self.gen_stmt_with_ctx(st, ctx)?;
        }
        self.gen_assign_expr_to_dst(dst, &arms[0].block.value, ctx)?;
        self.indent -= 1;
        if arms.len() == 1 {
            self.wln("ELSE");
            self.indent += 1;
            for st in &else_block.stmts {
                self.gen_stmt_with_ctx(st, ctx)?;
            }
            self.gen_assign_expr_to_dst(dst, &else_block.value, ctx)?;
            self.indent -= 1;
            self.wln("THEN");
            return Ok(());
        }
        self.wln("ELSE");
        self.indent += 1;
        self.gen_cond_assign(dst, &arms[1..], else_block, ctx)?;
        self.indent -= 1;
        self.wln("THEN");
        Ok(())
    }

    fn gen_sum_assign(
        &mut self,
        dst: &AddrRef,
        sum: &SumInfo,
        rhs: &Expr,
        ctx: &Ctx,
    ) -> Result<(), String> {
        match rhs {
            Expr::Ctor(name, named) => self.emit_sum_ctor_into(dst, sum, name, named, ctx),
            Expr::OptionNone => self.emit_sum_ctor_into(dst, sum, "none", &[], ctx),
            Expr::OptionSome(v) => self.emit_sum_ctor_into(
                dst,
                sum,
                "some",
                &[("value".to_string(), (**v).clone())],
                ctx,
            ),
            Expr::Call(name, args) if args.is_empty() => {
                self.emit_sum_ctor_into(dst, sum, name, &[], ctx)
            }
            Expr::Call(name, args) => self.gen_aggregate_call_assign(name, args, dst, ctx),
            _ => {
                let rlv = expr_to_lvalue(rhs).ok_or(
                    "sum-record assignment requires lvalue/constructor/COND rhs in codegen",
                )?;
                let src = self.resolve_lvalue_addr_ctx(&rlv, ctx)?;
                let size = self.type_size_bytes(&dst.ty)?;
                self.emit_aggregate_copy(&src, dst, size);
                Ok(())
            }
        }
    }

    fn emit_sum_ctor_into(
        &mut self,
        dst: &AddrRef,
        sum: &SumInfo,
        ctor_name: &str,
        named_args: &[(String, Expr)],
        ctx: &Ctx,
    ) -> Result<(), String> {
        let arm = sum
            .arms
            .iter()
            .find(|a| a.name.eq_ignore_ascii_case(ctor_name))
            .ok_or_else(|| format!("unknown sum constructor: {ctor_name}"))?;
        if arm.fields.len() != named_args.len() {
            return Err(format!(
                "constructor {ctor_name} argument count mismatch: expected {}, got {}",
                arm.fields.len(),
                named_args.len()
            ));
        }
        if arm.payload_size_bytes > sum.payload_size_bytes {
            return Err(format!(
                "internal: sum arm payload larger than sum payload (ctor {ctor_name})"
            ));
        }
        // Zero-fill tag + max payload so inactive bytes are deterministic.
        let total = 4 + sum.payload_size_bytes;
        for ofs in (0..total).step_by(4usize) {
            self.emit_store_at("0", dst, ofs);
        }
        self.emit_store_at(&arm.tag.to_string(), dst, 0);
        for f in &arm.fields {
            let (_, expr) = named_args
                .iter()
                .find(|(n, _)| n.eq_ignore_ascii_case(&f.name))
                .ok_or_else(|| format!("constructor {ctor_name} missing field {}", f.name))?;
            match &f.ty {
                TypeInfo::Basic(_) | TypeInfo::Enum(_) => {
                    let rhs = self.gen_expr_inline_ctx(expr, ctx)?;
                    self.emit_store_at(&rhs, dst, 4 + f.offset_bytes);
                }
                TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                    let lv = expr_to_lvalue(expr).ok_or_else(|| {
                        format!(
                            "aggregate constructor field {} must be lvalue in codegen",
                            f.name
                        )
                    })?;
                    let src = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    let field_dst = AddrRef {
                        base_expr: dst.base_expr.clone(),
                        offset: dst.offset + 4 + f.offset_bytes,
                        dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                        ty: f.ty.clone(),
                    };
                    let sz = self.type_size_bytes(&f.ty)?;
                    self.emit_aggregate_copy(&src, &field_dst, sz);
                }
                TypeInfo::Pointer(_) | TypeInfo::Nil => {
                    let rhs = self.gen_expr_inline_ctx(expr, ctx)?;
                    self.emit_store_at(&rhs, dst, 4 + f.offset_bytes);
                }
            }
        }
        Ok(())
    }

    fn emit_record_ctor_into(
        &mut self,
        dst: &AddrRef,
        rec: &RecordInfo,
        ctor_name: &str,
        named_args: &[(String, Expr)],
        ctx: &Ctx,
    ) -> Result<(), String> {
        if rec.fields.len() != named_args.len() {
            return Err(format!(
                "constructor {ctor_name} argument count mismatch: expected {}, got {}",
                rec.fields.len(),
                named_args.len()
            ));
        }
        for (fname, finfo) in &rec.fields {
            let (_, expr) = named_args
                .iter()
                .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                .ok_or_else(|| format!("constructor {ctor_name} missing field {fname}"))?;
            let field_dst = AddrRef {
                base_expr: dst.base_expr.clone(),
                offset: dst.offset + finfo.offset_bytes,
                dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                ty: finfo.ty.clone(),
            };
            self.gen_assign_expr_to_dst(&field_dst, expr, ctx)?;
        }
        for (n, _) in named_args {
            if !rec.fields.keys().any(|f| f.eq_ignore_ascii_case(n)) {
                return Err(format!("constructor {ctor_name} has no field {n}"));
            }
        }
        Ok(())
    }

    fn emit_array_literal_into(
        &mut self,
        dst: &AddrRef,
        elems: &[Expr],
        ctx: &Ctx,
    ) -> Result<(), String> {
        let arr = match &dst.ty {
            TypeInfo::Array(a) => a.clone(),
            _ => return Err("internal: array literal destination is not array".into()),
        };
        if elems.len() != arr.len as usize {
            return Err(format!(
                "array literal length mismatch in codegen: expected {}, got {}",
                arr.len,
                elems.len()
            ));
        }
        for (i, e) in elems.iter().enumerate() {
            let elem_dst = AddrRef {
                base_expr: dst.base_expr.clone(),
                offset: dst.offset + (i as u32) * arr.elem_size_bytes,
                dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                ty: (*arr.elem_ty).clone(),
            };
            self.gen_assign_expr_to_dst(&elem_dst, e, ctx)?;
        }
        Ok(())
    }

    fn emit_record_update_into(
        &mut self,
        dst: &AddrRef,
        rec: &RecordInfo,
        base: &Expr,
        updates: &[(String, Expr)],
        ctx: &Ctx,
    ) -> Result<(), String> {
        let blv = expr_to_lvalue(base).ok_or("record update base must be lvalue in codegen")?;
        let src = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
        let size = self.type_size_bytes(&dst.ty)?;
        self.emit_aggregate_copy(&src, dst, size);
        for (fname, expr) in updates {
            let (_, finfo) = rec
                .fields
                .iter()
                .find(|(n, _)| n.eq_ignore_ascii_case(fname))
                .ok_or_else(|| format!("record update has no field {fname}"))?;
            let field_dst = AddrRef {
                base_expr: dst.base_expr.clone(),
                offset: dst.offset + finfo.offset_bytes,
                dynamic_addr_expr: dst.dynamic_addr_expr.clone(),
                ty: finfo.ty.clone(),
            };
            self.gen_assign_expr_to_dst(&field_dst, expr, ctx)?;
        }
        Ok(())
    }

    fn emit_array_update_into(
        &mut self,
        dst: &AddrRef,
        base: &Expr,
        updates: &[(Expr, Expr)],
        ctx: &Ctx,
    ) -> Result<(), String> {
        let blv = expr_to_lvalue(base).ok_or("array update base must be lvalue in codegen")?;
        let src = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
        let size = self.type_size_bytes(&dst.ty)?;
        self.emit_aggregate_copy(&src, dst, size);
        let arr = match &dst.ty {
            TypeInfo::Array(a) => a.clone(),
            _ => return Err("internal: array update destination is not array".into()),
        };
        for (idx_expr, val_expr) in updates {
            let idx_code = self.gen_expr_inline_ctx(idx_expr, ctx)?;
            let logical_idx = if arr.low_bound == 0 {
                idx_code
            } else if arr.low_bound > 0 {
                format!("{idx_code} {} -", arr.low_bound)
            } else {
                format!("{idx_code} {} +", -arr.low_bound)
            };
            let scaled = if arr.elem_size_bytes == 1 {
                logical_idx
            } else {
                format!("{logical_idx} {} *", arr.elem_size_bytes)
            };
            let elem_dst = AddrRef {
                base_expr: dst.base_expr.clone(),
                offset: 0,
                dynamic_addr_expr: Some(format!("{} {scaled} +", self.emit_addr_inline(dst))),
                ty: (*arr.elem_ty).clone(),
            };
            self.gen_assign_expr_to_dst(&elem_dst, val_expr, ctx)?;
        }
        Ok(())
    }

    fn gen_sum_case_stmt(
        &mut self,
        expr: &Expr,
        arms: &[SumCaseArm],
        else_stmt: Option<&Stmt>,
        ctx: &Ctx,
    ) -> Result<(), String> {
        let et = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, expr)?;
        let sum = match et {
            TypeInfo::Sum(s) => s,
            _ => return Err("sum-case requires sum-record expression".into()),
        };
        let lv = expr_to_lvalue(expr).ok_or("sum-case expression must be lvalue in codegen")?;
        let src = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let tag_expr = self.emit_load_at(&src, 0);
        self.wln("0 __CASE_MATCH PVAR!");
        for arm in arms {
            let sinfo = sum
                .arms
                .iter()
                .find(|a| a.name.eq_ignore_ascii_case(&arm.ctor))
                .ok_or_else(|| format!("unknown sum-case arm constructor: {}", arm.ctor))?;
            self.wln("__CASE_MATCH PVAR@ 0= IF");
            self.indent += 1;
            self.wln(&format!("{tag_expr} {} = IF", sinfo.tag));
            self.indent += 1;
            self.wln("1 __CASE_MATCH PVAR!");
            let base = self.sum_case_bind_sp;
            if base + arm.binds.len() > 32 {
                return Err("sum-case bind temp overflow".into());
            }
            self.sum_case_bind_sp += arm.binds.len();
            let mut arm_ctx = ctx.clone();
            for (idx, bind) in arm.binds.iter().enumerate() {
                let slot = format!("__SCB{}", base + idx);
                let fi = &sinfo.fields[idx];
                match &fi.ty {
                    TypeInfo::Basic(_) | TypeInfo::Enum(_) => {
                        let rhs = self.emit_load_at(&src, 4 + fi.offset_bytes);
                        self.wln(&format!("{rhs} {slot} PVAR!"));
                        arm_ctx.vars.insert(
                            bind.clone(),
                            VarAccess {
                                slot,
                                ty: fi.ty.clone(),
                                by_ref: false,
                            },
                        );
                    }
                    TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                        let field_src = AddrRef {
                            base_expr: src.base_expr.clone(),
                            offset: src.offset + 4 + fi.offset_bytes,
                            dynamic_addr_expr: src.dynamic_addr_expr.clone(),
                            ty: fi.ty.clone(),
                        };
                        let addr = self.emit_addr_inline(&field_src);
                        self.wln(&format!("{addr} {slot} PVAR!"));
                        arm_ctx.vars.insert(
                            bind.clone(),
                            VarAccess {
                                slot,
                                ty: fi.ty.clone(),
                                by_ref: true,
                            },
                        );
                    }
                    TypeInfo::Pointer(_) | TypeInfo::Nil => {
                        let rhs = self.emit_load_at(&src, 4 + fi.offset_bytes);
                        self.wln(&format!("{rhs} {slot} PVAR!"));
                        arm_ctx.vars.insert(
                            bind.clone(),
                            VarAccess {
                                slot,
                                ty: fi.ty.clone(),
                                by_ref: false,
                            },
                        );
                    }
                }
            }
            self.gen_stmt_with_ctx(&arm.body, &arm_ctx)?;
            self.sum_case_bind_sp = base;
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
        Ok(())
    }

    fn gen_expr_inline_ctx(&self, e: &Expr, ctx: &Ctx) -> Result<String, String> {
        match e {
            Expr::Int(i) => Ok(i.to_string()),
            Expr::Bool(b) => Ok(if *b { "1".to_string() } else { "0".to_string() }),
            Expr::Char(u) => Ok(u.to_string()),
            Expr::Float(bits) => Ok(bits.to_string()),
            Expr::Nil => Ok("0".to_string()),
            Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
            Expr::Ctor(_, _) => {
                Err("constructor expression codegen requires assignment context".into())
            }
            Expr::ArrayLit(_) => Err("array literal codegen requires assignment context".into()),
            Expr::RecordUpdate(_, _) => {
                Err("record update codegen requires assignment context".into())
            }
            Expr::ArrayUpdate(_, _) => {
                Err("array update codegen requires assignment context".into())
            }
            Expr::OptionNone => Err("NONE codegen requires assignment context".into()),
            Expr::OptionSome(_) => Err("SOME codegen requires assignment context".into()),
            Expr::Cond { .. } => Err("COND codegen requires assignment context".into()),
            Expr::Cast(_, inner) => self.gen_expr_inline_ctx(inner, ctx),
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
                        ConstVal::F32(bits) => bits.to_string(),
                        ConstVal::EnumTag { ordinal, .. } => ordinal.to_string(),
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
                self.gen_call_inline_ctx(name, args, ctx)
            }
            Expr::Deref(_) => {
                let lv = expr_to_lvalue(e).ok_or("deref base must be variable")?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                Ok(self.emit_load_inline(&a))
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
                let t =
                    type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, inner)?;
                match op {
                    UnOp::Neg if matches!(t, TypeInfo::Basic(BasicType::Float)) => {
                        Ok(format!("{a} FNEGATE"))
                    }
                    UnOp::Neg => Ok(format!("{a} NEGATE")),
                    UnOp::Not => Ok(format!("{a} 0=")),
                }
            }
            Expr::Binary(a, op, b) => {
                if matches!(op, BinOp::Eq | BinOp::Ne) {
                    let ta =
                        type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, a)?;
                    if matches!(
                        ta,
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_)
                    ) {
                        let alv = expr_to_lvalue(a)
                            .ok_or("aggregate comparison requires lvalue lhs in codegen")?;
                        let blv = expr_to_lvalue(b)
                            .ok_or("aggregate comparison requires lvalue rhs in codegen")?;
                        let aa = self.resolve_lvalue_addr_ctx(&alv, ctx)?;
                        let bb = self.resolve_lvalue_addr_ctx(&blv, ctx)?;
                        let cells = self.type_size_bytes(&ta)? / 4;
                        let mut out = format!(
                            "{} {} {} PAGG-EQ",
                            self.emit_addr_inline(&aa),
                            self.emit_addr_inline(&bb),
                            cells
                        );
                        if matches!(op, BinOp::Ne) {
                            out.push_str(" 0=");
                        }
                        return Ok(out);
                    }
                }
                let la = self.gen_expr_inline_ctx(a, ctx)?;
                let lb = self.gen_expr_inline_ctx(b, ctx)?;
                let ta = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, a)?;
                let tb = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, b)?;
                if matches!(ta, TypeInfo::Nil) || matches!(tb, TypeInfo::Nil) {
                    use BinOp::*;
                    let w = match op {
                        Eq => "=",
                        Ne => "<>",
                        _ => return Err("nil supports only equality comparison".into()),
                    };
                    return Ok(format!("{la} {lb} {w}"));
                }
                if matches!(ta, TypeInfo::Basic(BasicType::Float))
                    && matches!(tb, TypeInfo::Basic(BasicType::Float))
                {
                    use BinOp::*;
                    return Ok(match op {
                        Add => format!("{la} {lb} FADD"),
                        Sub => format!("{la} {lb} FSUB"),
                        Mul => format!("{la} {lb} FMUL"),
                        Div => format!("{la} {lb} FDIV"),
                        Mod => return Err("float MOD codegen is not supported".into()),
                        Eq => format!("{la} {lb} F="),
                        Ne => format!("{la} {lb} F= 0="),
                        Lt => format!("{la} {lb} F<"),
                        Le => format!("{la} {lb} F<="),
                        Gt => format!("{la} {lb} SWAP F<"),
                        Ge => format!("{la} {lb} SWAP F<="),
                    });
                }
                use BinOp::*;
                let w = match op {
                    Add => "+",
                    Sub => "-",
                    Mul => "*",
                    Div => "/",
                    Mod => "MOD",
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

    fn gen_builtin_expr_call(
        &self,
        name: &str,
        args: &[Expr],
        ctx: &Ctx,
    ) -> Result<Option<String>, String> {
        let n = name.to_ascii_lowercase();
        match n.as_str() {
            "map" | "filter" | "fold" => Err(format!("{name} codegen requires assignment context")),
            "ord" => {
                if args.len() != 1 {
                    return Err("Ord requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
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
            "float" => {
                if args.len() != 1 {
                    return Err("Float requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} S>F",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "trunc" => {
                if args.len() != 1 {
                    return Err("Trunc requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} F>S",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "round" => {
                if args.len() != 1 {
                    return Err("Round requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} FROUND-I32",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "length" => {
                if args.len() != 1 {
                    return Err("Length requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
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
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                if let TypeInfo::Array(a) = t {
                    Ok(Some(a.high_bound.to_string()))
                } else {
                    Err("High argument must be array".into())
                }
            }
            "low" => {
                if args.len() != 1 {
                    return Err("Low requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                if let TypeInfo::Array(a) = t {
                    Ok(Some(a.low_bound.to_string()))
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
                match &p.ty {
                    TypeInfo::Basic(_)
                    | TypeInfo::Enum(_)
                    | TypeInfo::Pointer(_)
                    | TypeInfo::Nil => out.push(self.gen_expr_inline_ctx(arg, ctx)?),
                    TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                        let lv = expr_to_lvalue(arg).ok_or_else(|| {
                            format!("aggregate value argument must be lvalue in call to {name}")
                        })?;
                        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                        let size = self.type_size_bytes(&p.ty)?;
                        for ofs in (0..size).step_by(4) {
                            out.push(self.emit_load_at(&a, ofs));
                        }
                    }
                }
            }
        }
        Ok(out.join(" "))
    }

    fn emit_param_store_from_stack(
        &mut self,
        slot: &str,
        ty: &TypeInfo,
        by_ref: bool,
    ) -> Result<(), String> {
        if by_ref
            || matches!(
                ty,
                TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_) | TypeInfo::Nil
            )
        {
            self.wln(&format!("{slot} PVAR!"));
            return Ok(());
        }
        let size = self.type_size_bytes(ty)?;
        for ofs in (0..size).step_by(4).rev() {
            if ofs == 0 {
                self.wln(&format!("{slot} PVAR!"));
            } else {
                self.wln(&format!("{slot} {ofs} PFIELD!"));
            }
        }
        Ok(())
    }

    fn gen_call_inline_ctx(&self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<String, String> {
        let key = ctx
            .routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let (word, sig) = self.resolve_call_target(ctx, name)?;
        if matches!(
            sig.ret,
            Some(TypeInfo::Record(_)) | Some(TypeInfo::Sum(_)) | Some(TypeInfo::Array(_))
        ) {
            return Err("aggregate function result is only supported in assignment".into());
        }
        let mut parts = vec![];
        let frame_slots = self.routine_frames.get(key).cloned().unwrap_or_default();
        for slot in &frame_slots {
            parts.push(format!("{slot} PVAR@ >R"));
        }
        let argc = self.gen_call_args_inline(name, args, ctx)?;
        if !argc.is_empty() {
            parts.push(argc);
        }
        parts.push(word);
        if sig.ret.is_some() {
            parts.push("__CALL_RET PVAR!".into());
        }
        for slot in frame_slots.iter().rev() {
            parts.push(format!("R> {slot} PVAR!"));
        }
        if sig.ret.is_some() {
            parts.push("__CALL_RET PVAR@".into());
        }
        Ok(parts.join(" "))
    }

    fn gen_aggregate_call_assign(
        &mut self,
        name: &str,
        args: &[Expr],
        dst: &AddrRef,
        ctx: &Ctx,
    ) -> Result<(), String> {
        let key = ctx
            .routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let (word, sig) = self.resolve_call_target(ctx, name)?;
        let ret_ty = sig
            .ret
            .clone()
            .ok_or_else(|| format!("procedure used as expression: {name}"))?;
        if matches!(ret_ty, TypeInfo::Basic(_) | TypeInfo::Enum(_)) {
            return Err("internal: scalar function routed to aggregate assignment path".into());
        }

        let frame_slots = self.routine_frames.get(key).cloned().unwrap_or_default();
        for slot in &frame_slots {
            self.wln(&format!("{slot} PVAR@ >R"));
        }
        let argc = self.gen_call_args_inline(name, args, ctx)?;
        if !argc.is_empty() {
            self.wln(&argc);
        }
        self.wln(&word);
        self.wln("__CRS PVAR!");

        let size = self.type_size_bytes(&ret_ty)?;
        let src_tmp = AddrRef {
            base_expr: "__CRS".into(),
            offset: 0,
            dynamic_addr_expr: Some("__CRS PVAR@".into()),
            ty: ret_ty.clone(),
        };
        let dst_tmp = AddrRef {
            base_expr: "__CRA".into(),
            offset: 0,
            dynamic_addr_expr: None,
            ty: ret_ty.clone(),
        };
        self.emit_aggregate_copy(&src_tmp, &dst_tmp, size);

        for slot in frame_slots.iter().rev() {
            self.wln(&format!("R> {slot} PVAR!"));
        }

        self.emit_aggregate_copy(&dst_tmp, dst, size);
        Ok(())
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
                Selector::Deref => {
                    let target = match &t {
                        TypeInfo::Pointer(n) => n.clone(),
                        _ => return Err("deref on non-pointer lvalue".into()),
                    };
                    let cur_load = if let Some(cur) = dynamic_addr_expr.take() {
                        format!("{cur} PVAR@")
                    } else if offset == 0 {
                        format!("{base_expr} PVAR@")
                    } else {
                        format!("{base_expr} {offset} PFIELD@")
                    };
                    dynamic_addr_expr = Some(cur_load);
                    offset = 0;
                    t = self
                        .env
                        .types
                        .get(&target)
                        .cloned()
                        .ok_or_else(|| format!("unknown pointed type: {target}"))?;
                }
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
                        let (low_bound, len, elem_size, elem_ty) = match t {
                            TypeInfo::Array(ref a) => {
                                (a.low_bound, a.len, a.elem_size_bytes, (*a.elem_ty).clone())
                            }
                            _ => return Err("index on non-array lvalue".into()),
                        };
                        let idx_expr = self.gen_expr_inline_ctx(ix, ctx)?;
                        // Minimal runtime bounds check hook point can be inserted here if needed.
                        let _ = len;
                        let logical_idx = if low_bound == 0 {
                            idx_expr
                        } else if low_bound > 0 {
                            format!("{idx_expr} {} -", low_bound)
                        } else {
                            format!("{idx_expr} {} +", -low_bound)
                        };
                        let scaled = if elem_size == 1 {
                            logical_idx
                        } else {
                            format!("{logical_idx} {elem_size} *")
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
        // Emit chars directly to avoid implementation-specific S" parsing quirks.
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
        self.emit_storage_bytes_decl(name, sz);
        Ok(())
    }

    fn emit_storage_bytes_decl(&mut self, name: &str, sz: u32) {
        if sz <= 4 {
            self.wln(&format!("CREATE {name} 0 ,"));
        } else {
            self.wln(&format!("CREATE {name} 0 , {} ALLOT", sz - 4));
        }
    }

    fn type_size_bytes(&self, ty: &TypeInfo) -> Result<u32, String> {
        match ty {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_) | TypeInfo::Nil => Ok(4),
            TypeInfo::Record(r) => Ok(r.size_bytes),
            TypeInfo::Sum(s) => Ok(s.size_bytes),
            TypeInfo::Array(a) => Ok(a.size_bytes),
        }
    }

    fn max_aggregate_return_bytes(&self, routines: &[RoutineDecl]) -> Result<u32, String> {
        let mut max_bytes = 0;
        for r in routines {
            match r {
                RoutineDecl::Procedure(p) => {
                    max_bytes = max_bytes.max(self.max_aggregate_return_bytes(&p.block.routines)?);
                }
                RoutineDecl::Function(f) => {
                    let ty = self.ty_of_typeref(&f.ret_ty)?;
                    if matches!(
                        ty,
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_)
                    ) {
                        max_bytes = max_bytes.max(self.type_size_bytes(&ty)?);
                    }
                    max_bytes = max_bytes.max(self.max_aggregate_return_bytes(&f.block.routines)?);
                }
            }
        }
        Ok(max_bytes)
    }

    fn gen_builtin_array_io(&mut self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 2 {
            return Err(format!("{name} requires 2 arguments"));
        }
        let lv = expr_to_lvalue(&args[0])
            .ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let ainfo = match &a.ty {
            TypeInfo::Array(x) => x.clone(),
            _ => return Err(format!("{name} first argument must be array")),
        };
        let elem_ty = (*ainfo.elem_ty).clone();
        match elem_ty {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) => {}
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
                TypeInfo::Enum(_) => "PREAD-I32",
                _ => unreachable!(),
            };
            self.wln(&format!("{rw} {cell_addr} PVAR!"));
        } else {
            let ww = match elem_ty {
                TypeInfo::Basic(BasicType::Integer) => "PWRITE-I32",
                TypeInfo::Basic(BasicType::Boolean) => "PWRITE-BOOL",
                TypeInfo::Basic(BasicType::Char) => "PWRITE-CHAR",
                TypeInfo::Enum(_) => "PWRITE-I32",
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

    fn callback_name_arg<'b>(&self, e: &'b Expr, what: &str) -> Result<&'b str, String> {
        match e {
            Expr::Var(n) => Ok(n.as_str()),
            _ => Err(format!("{what} must be function name identifier")),
        }
    }

    fn gen_call_inline_values(
        &self,
        name: &str,
        arg_values: &[String],
        ctx: &Ctx,
    ) -> Result<String, String> {
        let key = ctx
            .routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let (word, sig) = self.resolve_call_target(ctx, name)?;
        let mut parts = vec![];
        let frame_slots = self.routine_frames.get(key).cloned().unwrap_or_default();
        for slot in &frame_slots {
            parts.push(format!("{slot} PVAR@ >R"));
        }
        parts.extend(arg_values.iter().cloned());
        parts.push(word);
        if sig.ret.is_some() {
            parts.push("__CALL_RET PVAR!".into());
        }
        for slot in frame_slots.iter().rev() {
            parts.push(format!("R> {slot} PVAR!"));
        }
        if sig.ret.is_some() {
            parts.push("__CALL_RET PVAR@".into());
        }
        Ok(parts.join(" "))
    }

    fn gen_builtin_new_dispose(
        &mut self,
        name: &str,
        args: &[Expr],
        ctx: &Ctx,
    ) -> Result<(), String> {
        if args.len() != 1 {
            return Err(format!("{name} requires 1 argument"));
        }
        let lv =
            expr_to_lvalue(&args[0]).ok_or_else(|| format!("{name} argument must be lvalue"))?;
        let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let target_name = match &dst.ty {
            TypeInfo::Pointer(n) => n.clone(),
            _ => return Err(format!("{name} argument must be pointer")),
        };
        if name.eq_ignore_ascii_case("Dispose") {
            // Pragmatic initial implementation: no-op deallocation.
            return Ok(());
        }
        let pointee = self
            .env
            .types
            .get(&target_name)
            .cloned()
            .ok_or_else(|| format!("unknown pointed type: {target_name}"))?;
        let sz = self.type_size_bytes(&pointee)?;
        self.wln("HERE __NEWP PVAR!");
        self.emit_store("__NEWP PVAR@", &dst);
        self.wln(&format!("{sz} ALLOT"));
        for ofs in (0..sz).step_by(4usize) {
            if ofs == 0 {
                self.wln("0 __NEWP PVAR@ PVAR!");
            } else {
                self.wln(&format!("0 __NEWP PVAR@ {ofs} + PVAR!"));
            }
        }
        Ok(())
    }

    fn raw_load_ptr_field(addr_expr: &str, ofs: u32) -> String {
        if ofs == 0 {
            format!("{addr_expr} PVAR@")
        } else {
            format!("{addr_expr} {ofs} + PVAR@")
        }
    }

    fn raw_store_ptr_field(&mut self, rhs: &str, addr_expr: &str, ofs: u32) {
        if ofs == 0 {
            self.wln(&format!("{rhs} {addr_expr} PVAR!"));
        } else {
            self.wln(&format!("{rhs} {addr_expr} {ofs} + PVAR!"));
        }
    }

    fn list_payload_layout_from_ptr_type(
        &self,
        t: &TypeInfo,
    ) -> Result<(String, u32, u32, TypeInfo, u32, u32), String> {
        let ptr_name = match t {
            TypeInfo::Pointer(n) => n.clone(),
            _ => return Err("list builtin requires pointer source".into()),
        };
        let rec = match self.env.types.get(&ptr_name) {
            Some(TypeInfo::Record(r)) => r,
            Some(_) => return Err("list builtin pointer target must be record".into()),
            None => return Err(format!("unknown pointed type: {ptr_name}")),
        };
        let nf = rec
            .fields
            .get("next")
            .ok_or("list builtin node record needs field next")?;
        let vf = rec
            .fields
            .get("value")
            .ok_or("list builtin node record needs field value")?;
        if nf.offset_bytes != 0 {
            return Err("list builtin node.next must be first field".into());
        }
        match &nf.ty {
            TypeInfo::Pointer(n) if n.eq_ignore_ascii_case(&ptr_name) => {}
            _ => return Err("list builtin node.next must be ^self".into()),
        }
        let payload_ty = vf.ty.clone();
        let payload_size = self.type_size_bytes(&payload_ty)?;
        if vf.offset_bytes < 4 {
            return Err("list builtin node.value must follow next".into());
        }
        Ok((
            ptr_name,
            vf.offset_bytes,
            nf.offset_bytes,
            payload_ty,
            payload_size,
            rec.size_bytes,
        ))
    }

    fn ptr_field_addr(addr_expr: &str, ofs: u32) -> String {
        if ofs == 0 {
            addr_expr.to_string()
        } else {
            format!("{addr_expr} {ofs} +")
        }
    }

    fn emit_copy_between_ptr_fields(
        &mut self,
        src_addr_expr: &str,
        src_ofs: u32,
        dst_addr_expr: &str,
        dst_ofs: u32,
        payload_ty: &TypeInfo,
        payload_size: u32,
    ) {
        match payload_ty {
            TypeInfo::Basic(_) | TypeInfo::Enum(_) | TypeInfo::Pointer(_) | TypeInfo::Nil => {
                let rhs = Self::raw_load_ptr_field(src_addr_expr, src_ofs);
                self.raw_store_ptr_field(&rhs, dst_addr_expr, dst_ofs);
            }
            TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                let src = AddrRef {
                    base_expr: "__LF_SRCPAY".into(),
                    offset: 0,
                    dynamic_addr_expr: Some(Self::ptr_field_addr(src_addr_expr, src_ofs)),
                    ty: payload_ty.clone(),
                };
                let dst = AddrRef {
                    base_expr: "__LF_DSTPAY".into(),
                    offset: 0,
                    dynamic_addr_expr: Some(Self::ptr_field_addr(dst_addr_expr, dst_ofs)),
                    ty: payload_ty.clone(),
                };
                self.emit_aggregate_copy(&src, &dst, payload_size);
            }
        }
    }

    fn gen_builtin_list_fn_assign(
        &mut self,
        name: &str,
        args: &[Expr],
        dst: &AddrRef,
        ctx: &Ctx,
    ) -> Result<(), String> {
        let lname = name.to_ascii_lowercase();
        match lname.as_str() {
            "map" => {
                if args.len() != 2 {
                    return Err("Map requires 2 arguments".into());
                }
                let src_t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let (_, value_ofs, next_ofs, _payload_ty, _payload_sz, node_sz) =
                    self.list_payload_layout_from_ptr_type(&src_t)?;
                let cb = self.callback_name_arg(&args[1], "Map callback")?;
                let src_expr = self.gen_expr_inline_ctx(&args[0], ctx)?;

                self.wln(&format!("{src_expr} __LF_SRC PVAR!"));
                self.wln("0 __LF_HEAD PVAR!");
                self.wln("0 __LF_TAIL PVAR!");
                self.wln("BEGIN");
                self.indent += 1;
                self.wln("__LF_SRC PVAR@ 0 <> WHILE");
                self.indent += 1;
                self.wln("HERE __LF_NODE PVAR!");
                self.wln(&format!("{node_sz} ALLOT"));
                for ofs in (0..node_sz).step_by(4usize) {
                    if ofs == 0 {
                        self.wln("0 __LF_NODE PVAR@ PVAR!");
                    } else {
                        self.wln(&format!("0 __LF_NODE PVAR@ {ofs} + PVAR!"));
                    }
                }
                self.raw_store_ptr_field("0", "__LF_NODE PVAR@", next_ofs);
                let src_payload_addr = Self::ptr_field_addr("__LF_SRC PVAR@", value_ofs);
                let dst_payload_addr = Self::ptr_field_addr("__LF_NODE PVAR@", value_ofs);
                let map_call =
                    self.gen_call_inline_values(cb, &[src_payload_addr, dst_payload_addr], ctx)?;
                self.wln(&map_call);
                self.wln("__LF_HEAD PVAR@ 0= IF");
                self.indent += 1;
                self.wln("__LF_NODE PVAR@ __LF_HEAD PVAR!");
                self.wln("__LF_NODE PVAR@ __LF_TAIL PVAR!");
                self.indent -= 1;
                self.wln("ELSE");
                self.indent += 1;
                self.raw_store_ptr_field("__LF_NODE PVAR@", "__LF_TAIL PVAR@", next_ofs);
                self.wln("__LF_NODE PVAR@ __LF_TAIL PVAR!");
                self.indent -= 1;
                self.wln("THEN");
                self.wln(&format!(
                    "{} __LF_SRC PVAR!",
                    Self::raw_load_ptr_field("__LF_SRC PVAR@", next_ofs)
                ));
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                self.emit_store("__LF_HEAD PVAR@", dst);
                Ok(())
            }
            "filter" => {
                if args.len() != 2 {
                    return Err("Filter requires 2 arguments".into());
                }
                let src_t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let (_, value_ofs, next_ofs, payload_ty, payload_sz, node_sz) =
                    self.list_payload_layout_from_ptr_type(&src_t)?;
                let cb = self.callback_name_arg(&args[1], "Filter predicate")?;
                let src_expr = self.gen_expr_inline_ctx(&args[0], ctx)?;

                self.wln(&format!("{src_expr} __LF_SRC PVAR!"));
                self.wln("0 __LF_HEAD PVAR!");
                self.wln("0 __LF_TAIL PVAR!");
                self.wln("BEGIN");
                self.indent += 1;
                self.wln("__LF_SRC PVAR@ 0 <> WHILE");
                self.indent += 1;
                let src_payload_addr = Self::ptr_field_addr("__LF_SRC PVAR@", value_ofs);
                let pred = self.gen_call_inline_values(cb, &[src_payload_addr], ctx)?;
                self.wln(&format!("{pred} IF"));
                self.indent += 1;
                self.wln("HERE __LF_NODE PVAR!");
                self.wln(&format!("{node_sz} ALLOT"));
                for ofs in (0..node_sz).step_by(4usize) {
                    if ofs == 0 {
                        self.wln("0 __LF_NODE PVAR@ PVAR!");
                    } else {
                        self.wln(&format!("0 __LF_NODE PVAR@ {ofs} + PVAR!"));
                    }
                }
                self.raw_store_ptr_field("0", "__LF_NODE PVAR@", next_ofs);
                self.emit_copy_between_ptr_fields(
                    "__LF_SRC PVAR@",
                    value_ofs,
                    "__LF_NODE PVAR@",
                    value_ofs,
                    &payload_ty,
                    payload_sz,
                );
                self.wln("__LF_HEAD PVAR@ 0= IF");
                self.indent += 1;
                self.wln("__LF_NODE PVAR@ __LF_HEAD PVAR!");
                self.wln("__LF_NODE PVAR@ __LF_TAIL PVAR!");
                self.indent -= 1;
                self.wln("ELSE");
                self.indent += 1;
                self.raw_store_ptr_field("__LF_NODE PVAR@", "__LF_TAIL PVAR@", next_ofs);
                self.wln("__LF_NODE PVAR@ __LF_TAIL PVAR!");
                self.indent -= 1;
                self.wln("THEN");
                self.indent -= 1;
                self.wln("THEN");
                self.wln(&format!(
                    "{} __LF_SRC PVAR!",
                    Self::raw_load_ptr_field("__LF_SRC PVAR@", next_ofs)
                ));
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                self.emit_store("__LF_HEAD PVAR@", dst);
                Ok(())
            }
            "fold" => {
                if args.len() != 3 {
                    return Err("Fold requires 3 arguments".into());
                }
                let src_t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let (_, value_ofs, next_ofs, _payload_ty, _payload_sz, _) =
                    self.list_payload_layout_from_ptr_type(&src_t)?;
                let init_expr = self.gen_expr_inline_ctx(&args[1], ctx)?;
                let cb = self.callback_name_arg(&args[2], "Fold callback")?;
                let src_expr = self.gen_expr_inline_ctx(&args[0], ctx)?;
                self.wln(&format!("{src_expr} __LF_SRC PVAR!"));
                self.wln(&format!("{init_expr} __AF_ACC PVAR!"));
                self.wln("BEGIN");
                self.indent += 1;
                self.wln("__LF_SRC PVAR@ 0 <> WHILE");
                self.indent += 1;
                let src_payload_addr = Self::ptr_field_addr("__LF_SRC PVAR@", value_ofs);
                let call = self.gen_call_inline_values(
                    cb,
                    &["__AF_ACC PVAR@".into(), src_payload_addr],
                    ctx,
                )?;
                self.wln(&format!("{call} __AF_ACC PVAR!"));
                self.wln(&format!(
                    "{} __LF_SRC PVAR!",
                    Self::raw_load_ptr_field("__LF_SRC PVAR@", next_ofs)
                ));
                self.indent -= 1;
                self.indent -= 1;
                self.wln("REPEAT");
                self.emit_store("__AF_ACC PVAR@", dst);
                Ok(())
            }
            _ => Err(format!("unknown list function builtin: {name}")),
        }
    }

    fn gen_builtin_str_io(&mut self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        let lv = expr_to_lvalue(&args[0])
            .ok_or_else(|| format!("{name} first argument must be lvalue array"))?;
        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        let arr_len = match &a.ty {
            TypeInfo::Array(ai) => match ai.elem_ty.as_ref() {
                TypeInfo::Basic(BasicType::Char) => ai.len,
                _ => return Err(format!("{name} first argument must be array of char")),
            },
            _ => return Err(format!("{name} first argument must be array of char")),
        };
        let base_addr = self.emit_addr_inline(&a);
        if name.eq_ignore_ascii_case("ReadStr") {
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
            ConstVal::F32(bits) => bits.to_string(),
            ConstVal::EnumTag { ordinal, .. } => ordinal.to_string(),
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

    fn extend_vars_for_routine(
        &self,
        r: &RoutineDecl,
        scoped: &str,
        ctx: &mut Ctx,
    ) -> Result<(), String> {
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

    fn collect_routine_frames(&mut self, routines: &[RoutineDecl], scope: &str) {
        for r in routines {
            let (name, block, params, ret_name) = match r {
                RoutineDecl::Procedure(p) => (&p.name, &p.block, &p.params, None),
                RoutineDecl::Function(f) => (&f.name, &f.block, &f.params, Some(f.name.as_str())),
            };
            let scoped = format!("{scope}::{name}");
            let mut slots = Vec::new();
            for prm in params {
                slots.push(self.slot_name(&scoped, &prm.name));
            }
            for lv in &block.vars {
                slots.push(self.slot_name(&scoped, &lv.name));
            }
            if let Some(ret) = ret_name {
                slots.push(self.slot_name(&scoped, ret));
            }
            self.routine_frames.insert(scoped.clone(), slots);
            self.collect_routine_frames(&block.routines, &scoped);
        }
    }

    fn ty_of_typeref(&self, tr: &TypeRef) -> Result<TypeInfo, String> {
        match tr {
            TypeRef::Basic(b) => Ok(TypeInfo::Basic(b.clone())),
            TypeRef::PointerNamed(n) => Ok(TypeInfo::Pointer(n.clone())),
            TypeRef::Option(inner) => {
                let inner_ty = self.ty_of_typeref(inner)?;
                let payload = self.type_size_bytes(&inner_ty)?;
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
                                ty: inner_ty,
                            }],
                            payload_size_bytes: payload,
                        },
                    ],
                    payload_size_bytes: payload,
                    size_bytes: 4 + payload,
                }))
            }
            TypeRef::Result(ok_ty, err_ty) => {
                let ok = self.ty_of_typeref(ok_ty)?;
                let err = self.ty_of_typeref(err_ty)?;
                let ok_sz = self.type_size_bytes(&ok)?;
                let err_sz = self.type_size_bytes(&err)?;
                let payload = ok_sz.max(err_sz);
                Ok(TypeInfo::Sum(SumInfo {
                    arms: vec![
                        SumArmInfo {
                            name: "ok".into(),
                            tag: 0,
                            fields: vec![SumFieldInfo {
                                name: "value".into(),
                                offset_bytes: 0,
                                ty: ok,
                            }],
                            payload_size_bytes: ok_sz,
                        },
                        SumArmInfo {
                            name: "err".into(),
                            tag: 1,
                            fields: vec![SumFieldInfo {
                                name: "error".into(),
                                offset_bytes: 0,
                                ty: err,
                            }],
                            payload_size_bytes: err_sz,
                        },
                    ],
                    payload_size_bytes: payload,
                    size_bytes: 4 + payload,
                }))
            }
            TypeRef::Array { dims, elem } => {
                let mut bounds = vec![];
                for d in dims {
                    let lo = match eval_const(self.env, &d.low)? {
                        ConstVal::I32(i) => i,
                        ConstVal::EnumTag { ordinal, .. } => ordinal,
                        _ => return Err("array low bound must be integer constant".into()),
                    };
                    let hi = match eval_const(self.env, &d.high)? {
                        ConstVal::I32(i) => i,
                        ConstVal::EnumTag { ordinal, .. } => ordinal,
                        _ => return Err("array high bound must be integer constant".into()),
                    };
                    if hi < lo {
                        return Err("array high bound must be >= low bound".into());
                    }
                    bounds.push((lo, hi));
                }
                let mut t = self.ty_of_typeref(elem)?;
                for &(lo, hi) in bounds.iter().rev() {
                    let n = (hi - lo + 1) as u32;
                    let esz = self.type_size_bytes(&t)?;
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
