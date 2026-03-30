use std::collections::HashMap;

use crate::ast::*;
use crate::sema::*;

const KFORTHC_RUNTIME_DATA_BYTES: u32 = 524_288 * 4;

#[derive(Clone)]
struct VarAccess {
    slot: String,
    ty: TypeInfo,
    by_ref: bool,
    conformant_bounds: Option<Vec<(String, String)>>,
}

#[derive(Clone)]
struct Ctx {
    vars: HashMap<String, VarAccess>,
    // simple name -> scoped key (program::Outer::Inner)
    routines: HashMap<String, String>,
    current_frame_slots: Vec<String>,
}

#[derive(Clone)]
struct AddrRef {
    base_expr: String,
    offset: u32,
    dynamic_addr_expr: Option<String>,
    ty: TypeInfo,
    variant_checks: Vec<RuntimeVariantCheck>,
}

#[derive(Clone)]
struct RuntimeVariantCheck {
    tag_addr_expr: String,
    allowed_ranges: Vec<(i32, i32)>,
}

pub struct ForthGen<'a> {
    env: &'a Env,
    out: String,
    indent: usize,
    static_data_bytes: u32,
    routine_frames: HashMap<String, Vec<String>>,
    string_literals: Vec<(String, String)>,
    sum_case_bind_sp: usize,
}

impl<'a> ForthGen<'a> {
    pub fn new(env: &'a Env) -> Self {
        Self {
            env,
            out: String::new(),
            indent: 0,
            static_data_bytes: 0,
            routine_frames: HashMap::new(),
            string_literals: Vec::new(),
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
        self.collect_string_literals_program(prog);
        self.collect_routine_frames(&prog.block.routines, "program");
        self.emit_debug_name_map(&prog.block.routines, "program");
        let max_agg_ret_bytes = self.max_aggregate_return_bytes(prog)?;
        self.wln("");

        for c in &prog.block.consts {
            let v = eval_const(self.env, &c.expr)?;
            match v {
                ConstVal::I32(i) => self.wln(&format!("{i} CONSTANT {}", c.name)),
                ConstVal::U32(u) => self.wln(&format!("{u} CONSTANT {}", c.name)),
                ConstVal::Real(bits) => self.wln(&format!("{bits} CONSTANT {}", c.name)),
                ConstVal::EnumVal { ordinal, .. } => {
                    self.wln(&format!("{ordinal} CONSTANT {}", c.name))
                }
                ConstVal::Bool(b) => {
                    self.wln(&format!("{} CONSTANT {}", if b { 1 } else { 0 }, c.name))
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
        self.emit_string_literal_storage()?;
        self.emit_storage_bytes_decl("__CASE_MATCH", 4)?;
        self.emit_storage_bytes_decl("__WSTR_STOP", 4)?;
        self.emit_storage_bytes_decl("__CP_SRC", 4)?;
        self.emit_storage_bytes_decl("__CP_DST", 4)?;
        self.emit_storage_bytes_decl("__CP_N", 4)?;
        self.emit_storage_bytes_decl("__CP_I", 4)?;
        self.emit_storage_bytes_decl("__CALL_RET", 4)?;
        self.emit_storage_bytes_decl("__EQ_A", 4)?;
        self.emit_storage_bytes_decl("__EQ_B", 4)?;
        self.emit_storage_bytes_decl("__EQ_N", 4)?;
        self.emit_storage_bytes_decl("__EQ_I", 4)?;
        self.emit_storage_bytes_decl("__EQ_OK", 4)?;
        self.emit_storage_bytes_decl("__CRS", 4)?;
        self.emit_storage_bytes_decl("__CRA", max_agg_ret_bytes.max(4))?;
        for i in 0..32 {
            self.emit_storage_bytes_decl(&format!("__SCB{i}"), 4)?;
        }
        self.emit_storage_bytes_decl("__NEWP", 4)?;
        self.emit_storage_bytes_decl("__HEX_PTR", 4)?;
        self.emit_storage_bytes_decl("__HEX_LEN", 4)?;
        self.emit_storage_bytes_decl("__HEX_ACC", 4)?;
        self.emit_storage_bytes_decl("__HEX_I", 4)?;
        self.emit_storage_bytes_decl("__HEX_STOP", 4)?;
        self.emit_storage_bytes_decl("__I2H_VAL", 4)?;
        self.emit_storage_bytes_decl("__I2H_PTR", 4)?;
        self.emit_storage_bytes_decl("__I2H_MAX", 4)?;
        self.emit_storage_bytes_decl("__I2H_FILL", 4)?;
        self.emit_storage_bytes_decl("__I2H_REQ", 4)?;
        self.emit_storage_bytes_decl("__I2H_WIDTH", 4)?;
        self.emit_storage_bytes_decl("__I2H_I", 4)?;
        self.emit_storage_bytes_decl("__I2H_SRC", 4)?;
        self.emit_storage_bytes_decl("__STR_SRC", 4)?;
        self.emit_storage_bytes_decl("__STR_DST", 4)?;
        self.emit_storage_bytes_decl("__STR_A", 4)?;
        self.emit_storage_bytes_decl("__STR_B", 4)?;
        self.emit_storage_bytes_decl("__STR_I", 4)?;
        self.emit_storage_bytes_decl("__STR_J", 4)?;
        self.emit_storage_bytes_decl("__STR_K", 4)?;
        self.emit_storage_bytes_decl("__STR_LEN", 4)?;
        self.emit_storage_bytes_decl("__STR_IDX", 4)?;
        self.emit_storage_bytes_decl("__STR_CNT", 4)?;
        self.emit_storage_bytes_decl("__STR_POS", 4)?;
        self.emit_storage_bytes_decl("__STR_MATCH", 4)?;
        self.emit_storage_bytes_decl("__VAR_TAG", 4)?;
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

        self.wln(": __HEX_TO_I32");
        self.indent += 1;
        self.wln("0 __HEX_ACC PVAR!");
        self.wln("0 __HEX_I PVAR!");
        self.wln("0 __HEX_STOP PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__HEX_STOP PVAR@ 0= __HEX_I PVAR@ __HEX_LEN PVAR@ < AND WHILE");
        self.indent += 1;
        self.wln("__HEX_PTR PVAR@ __HEX_I PVAR@ 4 * + PVAR@ DUP 0= IF");
        self.indent += 1;
        self.wln("DROP");
        self.wln("1 __HEX_STOP PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("DUP 48 >= OVER 57 <= AND IF");
        self.indent += 1;
        self.wln("48 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("DUP 65 >= OVER 70 <= AND IF");
        self.indent += 1;
        self.wln("55 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("DUP 97 >= OVER 102 <= AND IF");
        self.indent += 1;
        self.wln("87 - __HEX_ACC PVAR@ 16 * + __HEX_ACC PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("DROP");
        self.wln("1 __HEX_STOP PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__HEX_I PVAR@ 1 + __HEX_I PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("__HEX_ACC PVAR@");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __HEX_DIGIT");
        self.indent += 1;
        self.wln("DUP 10 < IF");
        self.indent += 1;
        self.wln("48 +");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("55 +");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __I32_TO_HEX_STR");
        self.indent += 1;
        self.wln("__I2H_MAX PVAR@ 0< IF");
        self.indent += 1;
        self.wln("0 __I2H_MAX PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("1 __I2H_REQ PVAR!");
        self.wln("7 __I2H_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__I2H_I PVAR@ 0 >= WHILE");
        self.indent += 1;
        self.wln("__I2H_VAL PVAR@ __I2H_I PVAR@ 4 * RSHIFT 15 AND DUP 0= 0= IF");
        self.indent += 1;
        self.wln("__I2H_I PVAR@ 1 + __I2H_REQ PVAR!");
        self.wln("DROP");
        self.wln("-1 __I2H_I PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("DROP");
        self.wln("__I2H_I PVAR@ 1 - __I2H_I PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("__I2H_FILL PVAR@ IF");
        self.indent += 1;
        self.wln("__I2H_MAX PVAR@ __I2H_WIDTH PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__I2H_REQ PVAR@ __I2H_MAX PVAR@ < IF");
        self.indent += 1;
        self.wln("__I2H_REQ PVAR@ __I2H_WIDTH PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__I2H_MAX PVAR@ __I2H_WIDTH PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("0 __I2H_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__I2H_I PVAR@ __I2H_WIDTH PVAR@ < WHILE");
        self.indent += 1;
        self.wln("__I2H_FILL PVAR@ IF");
        self.indent += 1;
        self.wln("__I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - __I2H_SRC PVAR!");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__I2H_REQ PVAR@ __I2H_WIDTH PVAR@ - __I2H_WIDTH PVAR@ __I2H_I PVAR@ 1 + - + __I2H_SRC PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__I2H_SRC PVAR@ 8 >= IF");
        self.indent += 1;
        self.wln("48");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__I2H_VAL PVAR@ __I2H_SRC PVAR@ 4 * RSHIFT 15 AND __HEX_DIGIT");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__I2H_PTR PVAR@ __I2H_I PVAR@ 4 * + PVAR!");
        self.wln("__I2H_I PVAR@ 1 + __I2H_I PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("0 __I2H_PTR PVAR@ __I2H_WIDTH PVAR@ 4 * + PVAR!");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __STRLEN");
        self.indent += 1;
        self.wln("0 __STR_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= IF");
        self.indent += 1;
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
        self.wln("0");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("UNTIL");
        self.wln("__STR_I PVAR@");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __STRCPY");
        self.indent += 1;
        self.wln("0 __STR_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_SRC PVAR@ __STR_I PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!");
        self.wln("0= IF");
        self.indent += 1;
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
        self.wln("0");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("UNTIL");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __STRPOS");
        self.indent += 1;
        self.wln("__STR_A PVAR@ __STR_SRC PVAR!");
        self.wln("__STRLEN __STR_LEN PVAR!");
        self.wln("__STR_LEN PVAR@ 0= IF");
        self.indent += 1;
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("0 __STR_POS PVAR!");
        self.wln("0 __STR_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_POS PVAR@ 0= __STR_B PVAR@ __STR_I PVAR@ 4 * + PVAR@ 0= 0= AND WHILE");
        self.indent += 1;
        self.wln("0 __STR_J PVAR!");
        self.wln("1 __STR_MATCH PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= 0= AND WHILE");
        self.indent += 1;
        self.wln("__STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@");
        self.wln("__STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ = 0= IF");
        self.indent += 1;
        self.wln("0 __STR_MATCH PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_B PVAR@ __STR_I PVAR@ __STR_J PVAR@ + 4 * + PVAR@ 0= IF");
        self.indent += 1;
        self.wln("0 __STR_MATCH PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_J PVAR@ 1 + __STR_J PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("__STR_MATCH PVAR@ __STR_A PVAR@ __STR_J PVAR@ 4 * + PVAR@ 0= AND IF");
        self.indent += 1;
        self.wln("__STR_I PVAR@ 1 + __STR_POS PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln("__STR_POS PVAR@");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __STRDELETE");
        self.indent += 1;
        self.wln("__STR_CNT PVAR@ 0 <= IF");
        self.indent += 1;
        self.wln("( no-op )");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_IDX PVAR@ 1 < IF");
        self.indent += 1;
        self.wln("1 __STR_IDX PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_IDX PVAR@ 1 - __STR_I PVAR!");
        self.wln("__STR_I PVAR@ __STR_CNT PVAR@ + __STR_J PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_DST PVAR@ __STR_J PVAR@ 4 * + PVAR@ DUP __STR_DST PVAR@ __STR_I PVAR@ 4 * + PVAR!");
        self.wln("0= IF");
        self.indent += 1;
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_I PVAR@ 1 + __STR_I PVAR!");
        self.wln("__STR_J PVAR@ 1 + __STR_J PVAR!");
        self.wln("0");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("UNTIL");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __STRINSERT");
        self.indent += 1;
        self.wln("__STR_SRC PVAR@ __STR_A PVAR!");
        self.wln("__STR_DST PVAR@ __STR_B PVAR!");
        self.wln("__STR_A PVAR@ __STR_SRC PVAR!");
        self.wln("__STRLEN __STR_LEN PVAR!");
        self.wln("__STR_IDX PVAR@ 1 < IF");
        self.indent += 1;
        self.wln("1 __STR_IDX PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_B PVAR@ __STR_SRC PVAR!");
        self.wln("__STRLEN __STR_J PVAR!");
        self.wln("__STR_IDX PVAR@ 1 - __STR_I PVAR!");
        self.wln("__STR_I PVAR@ __STR_J PVAR@ > IF");
        self.indent += 1;
        self.wln("__STR_J PVAR@ __STR_I PVAR!");
        self.indent -= 1;
        self.wln("THEN");
        self.wln("__STR_J PVAR@ __STR_K PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_DST PVAR@ __STR_K PVAR@ 4 * + PVAR@ __STR_DST PVAR@ __STR_K PVAR@ __STR_LEN PVAR@ + 4 * + PVAR!");
        self.wln("__STR_K PVAR@ __STR_I PVAR@ = IF");
        self.indent += 1;
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_K PVAR@ 1 - __STR_K PVAR!");
        self.wln("0");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("UNTIL");
        self.wln("0 __STR_K PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__STR_A PVAR@ __STR_K PVAR@ 4 * + PVAR@ DUP 0= IF");
        self.indent += 1;
        self.wln("DROP");
        self.wln("1");
        self.indent -= 1;
        self.wln("ELSE");
        self.indent += 1;
        self.wln("__STR_DST PVAR@ __STR_I PVAR@ __STR_K PVAR@ + 4 * + PVAR!");
        self.wln("__STR_K PVAR@ 1 + __STR_K PVAR!");
        self.wln("0");
        self.indent -= 1;
        self.wln("THEN");
        self.indent -= 1;
        self.wln("UNTIL");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __VARIANT_MISMATCH");
        self.indent += 1;
        self.wln("S\" Variant tag mismatch\" PWRITE-STR");
        self.wln("PWRITELN");
        self.wln("1 0 / DROP");
        self.indent -= 1;
        self.wln(";");

        self.wln(": __SUBRANGE_MISMATCH");
        self.indent += 1;
        self.wln("S\" Subrange check failed\" PWRITE-STR");
        self.wln("PWRITELN");
        self.wln("1 0 / DROP");
        self.indent -= 1;
        self.wln(";");

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
                if let Some(c) = &prm.conformant {
                    for dim in &c.dims {
                        self.emit_storage_decl(
                            &self.slot_name(&scoped, &dim.low_name),
                            &self.ty_of_typeref(&dim.index_ty)?,
                        )?;
                        self.emit_storage_decl(
                            &self.slot_name(&scoped, &dim.high_name),
                            &self.ty_of_typeref(&dim.index_ty)?,
                        )?;
                    }
                    self.emit_storage_decl(
                        &self.slot_name(&scoped, &prm.name),
                        &TypeInfo::Pointer("__conformant_array".into()),
                    )?;
                    continue;
                }
                let ty = if prm.by_ref {
                    TypeInfo::Pointer("__byref_param".into())
                } else {
                    self.ty_of_typeref(&prm.ty)?
                };
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
                current_frame_slots: parent_ctx.current_frame_slots.clone(),
            };
            self.extend_vars_for_routine(r, &scoped, &mut routine_ctx)?;
            let body_routines =
                self.extend_routine_visibility(&routine_ctx.routines, &block.routines, &scoped);
            let body_ctx = Ctx {
                vars: routine_ctx.vars.clone(),
                routines: body_routines,
                current_frame_slots: self
                    .routine_frames
                    .get(&scoped)
                    .cloned()
                    .unwrap_or_default(),
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
                    for slot in self
                        .runtime_param_slots(scoped, std::slice::from_ref(prm))
                        .iter()
                        .rev()
                    {
                        if slot == &self.slot_name(scoped, &prm.name)
                            && !prm.by_ref
                            && prm.conformant.is_none()
                        {
                            let prm_ty = self.ty_of_typeref(&prm.ty)?;
                            if self.is_aggregate_type(&prm_ty) {
                                self.emit_aggregate_param_store(slot, &prm_ty)?;
                            } else {
                                self.emit_param_store(slot, &prm_ty);
                            }
                        } else {
                            self.wln(&format!("{slot} PVAR!"));
                        }
                    }
                }
                self.gen_stmt_with_ctx(&p.block.body, ctx)?;
                self.indent -= 1;
                self.wln(";");
            }
            RoutineDecl::Function(f) => {
                self.wln(&format!(": {}", self.routine_word(scoped)));
                self.indent += 1;
                let ret_ty = self.ty_of_typeref(&f.ret_ty)?;
                for prm in f.params.iter().rev() {
                    for slot in self
                        .runtime_param_slots(scoped, std::slice::from_ref(prm))
                        .iter()
                        .rev()
                    {
                        if slot == &self.slot_name(scoped, &prm.name)
                            && !prm.by_ref
                            && prm.conformant.is_none()
                        {
                            let prm_ty = self.ty_of_typeref(&prm.ty)?;
                            if self.is_aggregate_type(&prm_ty) {
                                self.emit_aggregate_param_store(slot, &prm_ty)?;
                            } else {
                                self.emit_param_store(slot, &prm_ty);
                            }
                        } else {
                            self.wln(&format!("{slot} PVAR!"));
                        }
                    }
                }
                self.gen_stmt_with_ctx(&f.block.body, ctx)?;
                if self.is_aggregate_type(&ret_ty) {
                    self.wln(&self.slot_name(scoped, &f.name));
                } else {
                    self.wln(&format!("{} PVAR@", self.slot_name(scoped, &f.name)));
                }
                self.indent -= 1;
                self.wln(";");
            }
        }
        Ok(())
    }

    fn is_aggregate_type(&self, ty: &TypeInfo) -> bool {
        matches!(
            ty,
            TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_)
        )
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
            Stmt::Read(args) => {
                let mut i = 0usize;
                while i < args.len() {
                    let lv = expr_to_lvalue(&args[i])
                        .ok_or("Read arguments must be lvalues, except string max length")?;
                    let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                    if matches!(&dst.ty, TypeInfo::Array(ai) if matches!(ai.elem_ty.as_ref(), TypeInfo::Basic(BasicType::Char)))
                    {
                        if i + 1 >= args.len() {
                            return Err("Read on array of char requires max length".into());
                        }
                        self.emit_char_array_read(
                            &dst,
                            &self.gen_expr_inline_ctx(&args[i + 1], ctx)?,
                            ctx,
                            lv.base.as_str(),
                        )?;
                        i += 2;
                        continue;
                    }
                    let read_word = match dst.ty {
                        TypeInfo::Basic(BasicType::Integer) => "PREAD-I32",
                        TypeInfo::Basic(BasicType::Boolean) => "PREAD-BOOL",
                        TypeInfo::Basic(BasicType::Char) => "PREAD-CHAR",
                        TypeInfo::Basic(BasicType::Real) => "PREAD-F32",
                        TypeInfo::Enum(_) | TypeInfo::Subrange(_) => "PREAD-I32",
                        TypeInfo::Pointer(_) | TypeInfo::Nil => "PREAD-I32",
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                            return Err("Read on aggregate type is not supported".into())
                        }
                        TypeInfo::Set(_) => return Err("Read on set type is not supported".into()),
                    };
                    self.emit_store(read_word, &dst);
                    i += 1;
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
                for (labels, st) in arms {
                    self.wln("__CASE_MATCH PVAR@ 0= IF");
                    self.indent += 1;
                    self.wln(&format!("{} IF", self.case_labels_inline(labels)?));
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
                if name == "Copy" {
                    return self.gen_builtin_copy(args, ctx);
                }
                if name == "Concat" {
                    return self.gen_builtin_concat(args, ctx);
                }
                if name == "Delete" {
                    return self.gen_builtin_delete(args, ctx);
                }
                if name == "Insert" {
                    return self.gen_builtin_insert(args, ctx);
                }
                if name == "IntToHex" {
                    return self.gen_builtin_inttohex(args, ctx);
                }
                if name == "SetAddr" {
                    return self.gen_builtin_setaddr(args, ctx);
                }
                if name.eq_ignore_ascii_case("new") || name.eq_ignore_ascii_case("dispose") {
                    return self.gen_builtin_new_dispose(name, args, ctx);
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
            Stmt::With(bases, body) => {
                let rewritten = self.rewrite_stmt_with_ctx(body, bases, ctx)?;
                self.gen_stmt_with_ctx(&rewritten, ctx)
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
                            if matches!(&t, TypeInfo::Array(ai) if matches!(ai.elem_ty.as_ref(), TypeInfo::Basic(BasicType::Char)))
                            {
                                let lv = expr_to_lvalue(e)
                                    .ok_or("char array write requires lvalue in codegen")?;
                                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                                self.emit_char_array_write(&a, ctx, lv.base.as_str())?;
                                continue;
                            }
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
                                TypeInfo::Basic(BasicType::Real) => {
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
        match &dst.ty {
            TypeInfo::Basic(_)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
            | TypeInfo::Set(_)
            | TypeInfo::Pointer(_)
            | TypeInfo::Nil => {
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
                if let Expr::SetLit(items) = rhs {
                    let mut elems = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            SetItem::Single(e) => elems.push(e.clone()),
                            SetItem::Range(_, _) => {
                                return Err("array literal does not allow ranges".into());
                            }
                        }
                    }
                    return self.emit_array_literal_into(dst, &elems, ctx);
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
        self.wln("ELSE");
        self.indent += 1;
        if arms.len() == 1 {
            for st in &else_block.stmts {
                self.gen_stmt_with_ctx(st, ctx)?;
            }
            self.gen_assign_expr_to_dst(dst, &else_block.value, ctx)?;
        } else {
            self.gen_cond_assign(dst, &arms[1..], else_block, ctx)?;
        }
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
                TypeInfo::Basic(_)
                | TypeInfo::Enum(_)
                | TypeInfo::Subrange(_)
                | TypeInfo::Set(_)
                | TypeInfo::Pointer(_)
                | TypeInfo::Nil => {
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
                        variant_checks: Vec::new(),
                    };
                    let sz = self.type_size_bytes(&f.ty)?;
                    self.emit_aggregate_copy(&src, &field_dst, sz);
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
                variant_checks: Vec::new(),
            };
            self.gen_assign_expr_to_dst(&field_dst, expr, ctx)?;
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
                variant_checks: Vec::new(),
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
                variant_checks: Vec::new(),
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
            let logical_idx = if arr.low == 0 {
                idx_code
            } else if arr.low > 0 {
                format!("{idx_code} {} -", arr.low)
            } else {
                format!("{idx_code} {} +", -arr.low)
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
                variant_checks: Vec::new(),
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
                    TypeInfo::Basic(_)
                    | TypeInfo::Enum(_)
                    | TypeInfo::Subrange(_)
                    | TypeInfo::Set(_)
                    | TypeInfo::Pointer(_)
                    | TypeInfo::Nil => {
                        let rhs = self.emit_load_at(&src, 4 + fi.offset_bytes);
                        self.wln(&format!("{rhs} {slot} PVAR!"));
                        arm_ctx.vars.insert(
                            bind.clone(),
                            VarAccess {
                                slot,
                                ty: fi.ty.clone(),
                                by_ref: false,
                                conformant_bounds: None,
                            },
                        );
                    }
                    TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_) => {
                        let field_src = AddrRef {
                            base_expr: src.base_expr.clone(),
                            offset: src.offset + 4 + fi.offset_bytes,
                            dynamic_addr_expr: src.dynamic_addr_expr.clone(),
                            ty: fi.ty.clone(),
                            variant_checks: Vec::new(),
                        };
                        let addr = self.emit_addr_inline(&field_src);
                        self.wln(&format!("{addr} {slot} PVAR!"));
                        arm_ctx.vars.insert(
                            bind.clone(),
                            VarAccess {
                                slot,
                                ty: fi.ty.clone(),
                                by_ref: true,
                                conformant_bounds: None,
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
            Expr::Real(bits) => Ok(bits.to_string()),
            Expr::Str(_) => Err("string literal is only allowed in Write/WriteLn".into()),
            Expr::Ctor(_, _)
            | Expr::ArrayLit(_)
            | Expr::RecordUpdate(_, _)
            | Expr::ArrayUpdate(_, _)
            | Expr::OptionNone
            | Expr::OptionSome(_)
            | Expr::Cond { .. } => {
                Err("expression codegen is not integrated for this form yet".into())
            }
            Expr::Cast(_, inner) => self.gen_expr_inline_ctx(inner, ctx),
            Expr::SetLit(items) => self.gen_set_lit_inline(items, ctx),
            Expr::Nil => Ok("0".into()),
            Expr::Var(n) => {
                if let Some(c) = self.env.consts.get(n) {
                    Ok(match c {
                        ConstVal::I32(i) => i.to_string(),
                        ConstVal::U32(u) => u.to_string(),
                        ConstVal::Real(bits) => bits.to_string(),
                        ConstVal::EnumVal { ordinal, .. } => ordinal.to_string(),
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
                match op {
                    UnOp::Neg => {
                        let t = type_of_expr_scoped(
                            self.env,
                            &self.ctx_to_types(ctx),
                            &ctx.routines,
                            inner,
                        )?;
                        Ok(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
                            format!("{a} FNEGATE")
                        } else {
                            format!("{a} NEGATE")
                        })
                    }
                    UnOp::Not => Ok(format!("{a} 0=")),
                }
            }
            Expr::Binary(a, op, b) => {
                let la = self.gen_expr_inline_ctx(a, ctx)?;
                let lb = self.gen_expr_inline_ctx(b, ctx)?;
                use BinOp::*;
                let ta = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, a)?;
                let tb = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, b)?;
                let both_realish = matches!(ta, TypeInfo::Basic(BasicType::Real))
                    || matches!(tb, TypeInfo::Basic(BasicType::Real))
                    || matches!(op, RealDiv);
                let la = if both_realish {
                    self.coerce_real_inline(a, &ta, ctx)?
                } else {
                    la
                };
                let lb = if both_realish {
                    self.coerce_real_inline(b, &tb, ctx)?
                } else {
                    lb
                };
                if matches!(op, BinOp::Eq | BinOp::Ne)
                    && matches!(
                        ta,
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_)
                    )
                {
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
                let s = match op {
                    Add => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} OR")
                        } else if both_realish {
                            format!("{la} {lb} FADD")
                        } else {
                            format!("{la} {lb} +")
                        }
                    }
                    Sub => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{lb} -1 XOR {la} AND")
                        } else if both_realish {
                            format!("{la} {lb} FSUB")
                        } else {
                            format!("{la} {lb} -")
                        }
                    }
                    Mul => {
                        if both_realish {
                            format!("{la} {lb} FMUL")
                        } else if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} AND")
                        } else {
                            format!("{la} {lb} *")
                        }
                    }
                    RealDiv => format!("{la} {lb} FDIV"),
                    Div => format!("{la} {lb} /"),
                    Mod => format!("{la} {lb} MOD"),
                    And => format!("{la} {lb} AND"),
                    Or => format!("{la} {lb} OR"),
                    Xor => format!("{la} {lb} XOR"),
                    In => format!(
                        "1 {} {} - LSHIFT {} AND 0= 0=",
                        self.ordinal_inline(a, ctx)?,
                        self.set_low_bound_expr(b, ctx)?,
                        self.gen_expr_inline_ctx(b, ctx)?
                    ),
                    Eq => {
                        if both_realish {
                            format!("{la} {lb} F=")
                        } else {
                            format!("{la} {lb} =")
                        }
                    }
                    Ne => {
                        if both_realish {
                            format!("{la} {lb} F= 0=")
                        } else {
                            format!("{la} {lb} <>")
                        }
                    }
                    Lt => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} AND {la} = {la} {lb} <> AND")
                        } else if both_realish {
                            format!("{la} {lb} F<")
                        } else {
                            format!("{la} {lb} <")
                        }
                    }
                    Le => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} AND {la} =")
                        } else if both_realish {
                            format!("{la} {lb} F<=")
                        } else {
                            format!("{la} {lb} <=")
                        }
                    }
                    Gt => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} AND {lb} = {la} {lb} <> AND")
                        } else if both_realish {
                            format!("{lb} {la} F<")
                        } else {
                            format!("{la} {lb} >")
                        }
                    }
                    Ge => {
                        if matches!(ta, TypeInfo::Set(_)) {
                            format!("{la} {lb} AND {lb} =")
                        } else if both_realish {
                            format!("{lb} {la} F<=")
                        } else {
                            format!("{la} {lb} >=")
                        }
                    }
                };
                Ok(s)
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
            "abs" => {
                if args.len() != 1 {
                    return Err("Abs requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                Ok(Some(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
                    format!("{v} FABS")
                } else {
                    format!("{v} DUP 0< IF NEGATE THEN")
                }))
            }
            "sqr" => {
                if args.len() != 1 {
                    return Err("Sqr requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                Ok(Some(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
                    format!("{v} DUP FMUL")
                } else {
                    format!("{v} DUP *")
                }))
            }
            "round" => {
                if args.len() != 1 {
                    return Err("Round requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                Ok(Some(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
                    format!("{v} FROUND-I32")
                } else {
                    v
                }))
            }
            "trunc" => {
                if args.len() != 1 {
                    return Err("Trunc requires 1 argument".into());
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                Ok(Some(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
                    format!("{v} F>S")
                } else {
                    v
                }))
            }
            "succ" => {
                if args.len() != 1 {
                    return Err("Succ requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} 1 +",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "pred" => {
                if args.len() != 1 {
                    return Err("Pred requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} 1 -",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "odd" => {
                if args.len() != 1 {
                    return Err("Odd requires 1 argument".into());
                }
                Ok(Some(format!(
                    "{} 1 AND 0= 0=",
                    self.gen_expr_inline_ctx(&args[0], ctx)?
                )))
            }
            "hextoint" => {
                if args.len() != 1 {
                    return Err("HexToInt requires 1 argument".into());
                }
                match &args[0] {
                    Expr::Str(s) => Ok(Some(parse_hex_text(s)?.to_string())),
                    _ => {
                        let lv = expr_to_lvalue(&args[0])
                            .ok_or("HexToInt argument must be lvalue char array in codegen")?;
                        let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                        let arr_len = match &a.ty {
                            TypeInfo::Array(ai) => match ai.elem_ty.as_ref() {
                                TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                                _ => return Err("HexToInt argument must be array of char".into()),
                            },
                            _ => return Err("HexToInt argument must be array of char".into()),
                        };
                        let arr_len = if let Some(v) = ctx.vars.get(&lv.base) {
                            if let Some(bounds) = &v.conformant_bounds {
                                let (low_name, high_name) =
                                    bounds.first().ok_or("missing conformant string bounds")?;
                                let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                                let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                                format!("{high} {low} - 1 +")
                            } else {
                                arr_len
                            }
                        } else {
                            arr_len
                        };
                        Ok(Some(format!(
                            "{} __HEX_PTR PVAR! {} __HEX_LEN PVAR! __HEX_TO_I32",
                            self.emit_addr_inline(&a),
                            arr_len
                        )))
                    }
                }
            }
            "addr" => {
                if args.len() != 1 {
                    return Err("Addr requires 1 argument".into());
                }
                let lv = expr_to_lvalue(&args[0]).ok_or("Addr argument must be an lvalue")?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                Ok(Some(self.emit_addr_inline(&a)))
            }
            "pos" => {
                if args.len() != 2 {
                    return Err("Pos requires 2 arguments".into());
                }
                let needle = self.resolve_char_array_arg(&args[0], ctx, "Pos first argument")?;
                let hay = self.resolve_char_array_arg(&args[1], ctx, "Pos second argument")?;
                Ok(Some(format!(
                    "{} __STR_A PVAR! {} __STR_B PVAR! __STRPOS",
                    self.emit_addr_inline(&needle),
                    self.emit_addr_inline(&hay)
                )))
            }
            "upcase" => {
                if args.len() != 1 {
                    return Err("UpCase requires 1 argument".into());
                }
                let v = self.gen_expr_inline_ctx(&args[0], ctx)?;
                Ok(Some(format!("{v} DUP 97 >= OVER 122 <= AND IF 32 - THEN")))
            }
            "length" => {
                if args.len() != 1 {
                    return Err("Length requires 1 argument".into());
                }
                if let Some((low, high)) = self.runtime_array_bounds_for_expr(&args[0], ctx) {
                    return Ok(Some(format!("{high} {low} - 1 +")));
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
                if let Some((_, high)) = self.runtime_array_bounds_for_expr(&args[0], ctx) {
                    return Ok(Some(high));
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                if let TypeInfo::Array(a) = t {
                    Ok(Some(a.high.to_string()))
                } else {
                    Err("High argument must be array".into())
                }
            }
            "low" => {
                if args.len() != 1 {
                    return Err("Low requires 1 argument".into());
                }
                if let Some((low, _)) = self.runtime_array_bounds_for_expr(&args[0], ctx) {
                    return Ok(Some(low));
                }
                let t = type_of_expr_scoped(
                    self.env,
                    &self.ctx_to_types(ctx),
                    &ctx.routines,
                    &args[0],
                )?;
                if let TypeInfo::Array(_) = t {
                    if let TypeInfo::Array(a) = t {
                        Ok(Some(a.low.to_string()))
                    } else {
                        unreachable!()
                    }
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
            if let Some(_c) = &p.conformant {
                let lv = expr_to_lvalue(arg).ok_or_else(|| {
                    format!("conformant array argument must be lvalue in call to {name}")
                })?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                let mut cur = &a.ty;
                let mut rank = 0usize;
                while let TypeInfo::Array(ai) = cur {
                    out.push(ai.low.to_string());
                    out.push(ai.high.to_string());
                    cur = ai.elem_ty.as_ref();
                    rank += 1;
                }
                if rank == 0 {
                    return Err(format!(
                        "conformant array argument must be array in call to {name}"
                    ));
                }
                out.push(self.emit_addr_inline(&a));
            } else if p.by_ref {
                let lv = expr_to_lvalue(arg)
                    .ok_or_else(|| format!("by-ref argument must be lvalue in call to {name}"))?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                out.push(self.emit_addr_inline(&a));
            } else if self.is_aggregate_type(&p.ty) {
                let lv = expr_to_lvalue(arg).ok_or_else(|| {
                    format!("aggregate by-value argument must be lvalue in call to {name}")
                })?;
                let a = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
                out.push(self.emit_addr_inline(&a));
            } else {
                out.push(self.gen_expr_inline_ctx(arg, ctx)?);
            }
        }
        Ok(out.join(" "))
    }

    fn gen_call_inline_ctx(&self, name: &str, args: &[Expr], ctx: &Ctx) -> Result<String, String> {
        ctx.routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let (word, sig) = self.resolve_call_target(ctx, name)?;
        let mut parts = vec![];
        for slot in &ctx.current_frame_slots {
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
        for slot in ctx.current_frame_slots.iter().rev() {
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
        ctx.routines
            .get(name)
            .ok_or_else(|| format!("unknown routine in scope: {name}"))?;
        let (word, sig) = self.resolve_call_target(ctx, name)?;
        let ret_ty = sig
            .ret
            .clone()
            .ok_or_else(|| format!("procedure used as expression: {name}"))?;
        if matches!(
            ret_ty,
            TypeInfo::Basic(_)
                | TypeInfo::Enum(_)
                | TypeInfo::Subrange(_)
                | TypeInfo::Set(_)
                | TypeInfo::Pointer(_)
                | TypeInfo::Nil
        ) {
            return Err("internal: scalar function routed to aggregate assignment path".into());
        }

        for slot in &ctx.current_frame_slots {
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
            variant_checks: Vec::new(),
        };
        let dst_tmp = AddrRef {
            base_expr: "__CRA".into(),
            offset: 0,
            dynamic_addr_expr: None,
            ty: ret_ty.clone(),
            variant_checks: Vec::new(),
        };
        self.emit_aggregate_copy(&src_tmp, &dst_tmp, size);

        for slot in ctx.current_frame_slots.iter().rev() {
            self.wln(&format!("R> {slot} PVAR!"));
        }

        self.emit_aggregate_copy(&dst_tmp, dst, size);
        Ok(())
    }

    fn emit_store(&mut self, rhs: &str, dst: &AddrRef) {
        let checks = self.variant_check_prefix(dst);
        let rhs_checked = self.checked_rhs_for_type(rhs, &dst.ty);
        if let Some(addr) = &dst.dynamic_addr_expr {
            self.wln(&format!("{checks}{rhs_checked} {addr} PVAR!"));
        } else if dst.offset == 0 {
            self.wln(&format!("{checks}{rhs_checked} {} PVAR!", dst.base_expr));
        } else {
            self.wln(&format!(
                "{checks}{rhs_checked} {} {} PFIELD!",
                dst.base_expr, dst.offset
            ));
        }
    }

    fn emit_load_inline(&self, src: &AddrRef) -> String {
        let checks = self.variant_check_prefix(src);
        if let Some(addr) = &src.dynamic_addr_expr {
            format!("{checks}{addr} __SCB0 PVAR! __SCB0 PVAR@ PVAR@")
        } else if src.offset == 0 {
            format!("{checks}{} PVAR@", src.base_expr)
        } else {
            format!("{checks}{} {} PFIELD@", src.base_expr, src.offset)
        }
    }

    fn emit_addr_inline(&self, a: &AddrRef) -> String {
        let checks = self.variant_check_prefix(a);
        if let Some(addr) = &a.dynamic_addr_expr {
            format!("{checks}{addr}")
        } else if a.offset == 0 {
            format!("{checks}{}", a.base_expr)
        } else {
            format!("{checks}{} {} +", a.base_expr, a.offset)
        }
    }

    fn variant_check_prefix(&self, addr: &AddrRef) -> String {
        let mut out = String::new();
        for check in &addr.variant_checks {
            out.push_str(&format!("{} PVAR@ __VAR_TAG PVAR! ", check.tag_addr_expr));
            let mut first = true;
            for (lo, hi) in &check.allowed_ranges {
                let cond = if lo == hi {
                    format!("__VAR_TAG PVAR@ {lo} =")
                } else {
                    format!("__VAR_TAG PVAR@ {lo} >= __VAR_TAG PVAR@ {hi} <= AND")
                };
                if first {
                    out.push_str(&cond);
                    first = false;
                } else {
                    out.push(' ');
                    out.push_str(&cond);
                    out.push_str(" OR");
                }
                out.push(' ');
            }
            if first {
                out.push_str("0 ");
            }
            out.push_str("0= IF __VARIANT_MISMATCH THEN ");
        }
        out
    }

    fn checked_rhs_for_type(&self, rhs: &str, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Subrange(s) => format!(
                "{rhs} DUP {} >= OVER {} <= AND 0= IF __SUBRANGE_MISMATCH THEN",
                s.low, s.high
            ),
            _ => rhs.to_string(),
        }
    }

    fn emit_param_store(&mut self, slot: &str, ty: &TypeInfo) {
        match ty {
            TypeInfo::Subrange(s) => self.wln(&format!(
                "DUP {} >= OVER {} <= AND 0= IF __SUBRANGE_MISMATCH THEN {slot} PVAR!",
                s.low, s.high
            )),
            _ => self.wln(&format!("{slot} PVAR!")),
        }
    }

    fn emit_aggregate_param_store(&mut self, slot: &str, ty: &TypeInfo) -> Result<(), String> {
        let size = self.type_size_bytes(ty)?;
        self.wln("__CP_SRC PVAR!");
        self.wln(&format!("{slot} __CP_DST PVAR!"));
        self.wln(&format!("{size} __CP_N PVAR!"));
        self.wln("0 __CP_I PVAR!");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln("__CP_I PVAR@ __CP_N PVAR@ < WHILE");
        self.indent += 1;
        self.wln("__CP_SRC PVAR@ __CP_I PVAR@ + PVAR@");
        self.wln("__CP_DST PVAR@ __CP_I PVAR@ + PVAR!");
        self.wln("__CP_I PVAR@ 4 + __CP_I PVAR!");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        Ok(())
    }

    fn resolve_lvalue_addr_ctx(&self, lv: &LValue, ctx: &Ctx) -> Result<AddrRef, String> {
        let v = ctx
            .vars
            .get(&lv.base)
            .ok_or_else(|| format!("unknown var: {}", lv.base))?;
        let base_expr = v.slot.clone();
        let mut t = v.ty.clone();
        let mut offset = 0u32;
        let mut dynamic_addr_expr: Option<String> = if v.by_ref {
            Some(format!("{} PVAR@", v.slot))
        } else {
            None
        };
        let mut conformant_bounds = v.conformant_bounds.clone();
        let mut variant_checks = Vec::new();
        for sel in &lv.sels {
            match sel {
                Selector::Deref => match t {
                    TypeInfo::Pointer(ref target) => {
                        let cur = AddrRef {
                            base_expr: base_expr.clone(),
                            offset,
                            dynamic_addr_expr: dynamic_addr_expr.clone(),
                            ty: t.clone(),
                            variant_checks: variant_checks.clone(),
                        };
                        dynamic_addr_expr = Some(self.emit_load_inline(&cur));
                        offset = 0;
                        t = lookup_type(self.env, target)
                            .ok_or_else(|| format!("unknown pointed type: {target}"))?;
                    }
                    _ => return Err("deref on non-pointer lvalue".into()),
                },
                Selector::Field(f) => match t {
                    TypeInfo::Record(ref r) => {
                        let fi = r
                            .fields
                            .get(f)
                            .ok_or_else(|| format!("unknown field: {f}"))?;
                        let record_base = if let Some(cur) = &dynamic_addr_expr {
                            if offset == 0 {
                                cur.clone()
                            } else {
                                format!("{cur} {offset} +")
                            }
                        } else if offset == 0 {
                            base_expr.clone()
                        } else {
                            format!("{base_expr} {offset} +")
                        };
                        for check in &fi.variant_checks {
                            let tag_addr_expr = if check.tag_offset_bytes == 0 {
                                record_base.clone()
                            } else {
                                format!("{record_base} {} +", check.tag_offset_bytes)
                            };
                            variant_checks.push(RuntimeVariantCheck {
                                tag_addr_expr,
                                allowed_ranges: check.allowed_ranges.clone(),
                            });
                        }
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
                        let (low, len, elem_size, elem_ty) = match t {
                            TypeInfo::Array(ref a) => {
                                (a.low, a.len, a.elem_size_bytes, (*a.elem_ty).clone())
                            }
                            _ => return Err("index on non-array lvalue".into()),
                        };
                        let idx_expr = self.gen_expr_inline_ctx(ix, ctx)?;
                        // Minimal runtime bounds check hook point can be inserted here if needed.
                        let _ = len;
                        let scaled = if let Some((low_name, high_name)) =
                            conformant_bounds.as_mut().and_then(|bounds| {
                                if bounds.is_empty() {
                                    None
                                } else {
                                    Some(bounds.remove(0))
                                }
                            }) {
                            let low = self.runtime_bound_slot_expr(&low_name, ctx)?;
                            let stride = self.runtime_conformant_size_expr(
                                &elem_ty,
                                conformant_bounds.as_deref().unwrap_or(&[]),
                                ctx,
                            )?;
                            let _ = high_name;
                            if stride == "1" {
                                format!("{idx_expr} {low} -")
                            } else {
                                format!("{idx_expr} {low} - {stride} *")
                            }
                        } else if elem_size == 1 {
                            if low == 0 {
                                idx_expr
                            } else {
                                format!("{idx_expr} {low} -")
                            }
                        } else if low == 0 {
                            format!("{idx_expr} {elem_size} *")
                        } else {
                            format!("{idx_expr} {low} - {elem_size} *")
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
            variant_checks,
        })
    }

    fn emit_string_write(&mut self, s: &str) {
        // Use compact S" ... " output when the literal is safe for Forth parsing.
        if !s.is_empty()
            && s.is_ascii()
            && !s.contains('"')
            && !s.contains('\n')
            && !s.contains('\r')
        {
            self.wln(&format!("S\" {}\" PWRITE-STR", s));
            return;
        }
        for ch in s.chars() {
            self.wln(&format!("{} PWRITE-CHAR", ch as u32));
        }
    }

    fn emit_string_literal_storage(&mut self) -> Result<(), String> {
        for (name, value) in self.string_literals.clone() {
            let len = value.chars().count() as u32 + 1;
            let ty = TypeInfo::Array(ArrayInfo {
                low: 0,
                high: len as i32 - 1,
                len,
                elem_ty: Box::new(TypeInfo::Basic(BasicType::Char)),
                elem_size_bytes: 4,
                size_bytes: len * 4,
            });
            self.emit_storage_decl(&name, &ty)?;
            let addr = AddrRef {
                base_expr: name,
                offset: 0,
                dynamic_addr_expr: None,
                ty,
                variant_checks: Vec::new(),
            };
            self.emit_char_array_assign(&addr, &value)?;
        }
        Ok(())
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
                format!("{addr} __SCB0 PVAR! __SCB0 PVAR@ PVAR@")
            } else {
                format!("{addr} {add_ofs} + __SCB0 PVAR! __SCB0 PVAR@ PVAR@")
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
                self.wln(&format!("{addr} __SCB0 PVAR! {rhs} __SCB0 PVAR@ PVAR!"));
            } else {
                self.wln(&format!(
                    "{addr} {add_ofs} + __SCB0 PVAR! {rhs} __SCB0 PVAR@ PVAR!"
                ));
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
        let copied = body.min(chars.len() as u32);
        for i in 0..copied {
            let v = chars[i as usize];
            self.emit_store_at(&v.to_string(), dst, i * 4);
        }
        self.emit_store_at("0", dst, copied * 4);
        Ok(())
    }

    fn emit_char_array_write(
        &mut self,
        a: &AddrRef,
        ctx: &Ctx,
        base_name: &str,
    ) -> Result<(), String> {
        let arr_len = match &a.ty {
            TypeInfo::Array(ai) => match ai.elem_ty.as_ref() {
                TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                _ => return Err("Write/WriteLn char array requires array of char".into()),
            },
            _ => return Err("Write/WriteLn char array requires array of char".into()),
        };
        let arr_len = if let Some(v) = ctx.vars.get(base_name) {
            if let Some(bounds) = &v.conformant_bounds {
                let (low_name, high_name) =
                    bounds.first().ok_or("missing conformant string bounds")?;
                let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                format!("{high} {low} - 1 +")
            } else {
                arr_len
            }
        } else {
            arr_len
        };
        let base_addr = self.emit_addr_inline(a);
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

    fn emit_char_array_read(
        &mut self,
        dst: &AddrRef,
        max_len_expr: &str,
        ctx: &Ctx,
        base_name: &str,
    ) -> Result<(), String> {
        let arr_len = match &dst.ty {
            TypeInfo::Array(ai) => match ai.elem_ty.as_ref() {
                TypeInfo::Basic(BasicType::Char) => ai.len.to_string(),
                _ => return Err("Read char array requires array of char".into()),
            },
            _ => return Err("Read char array requires array of char".into()),
        };
        let arr_len = if let Some(v) = ctx.vars.get(base_name) {
            if let Some(bounds) = &v.conformant_bounds {
                let (low_name, high_name) =
                    bounds.first().ok_or("missing conformant string bounds")?;
                let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                format!("{high} {low} - 1 +")
            } else {
                arr_len
            }
        } else {
            arr_len
        };
        let cap = format!("{arr_len} 1 -");
        let base_addr = self.emit_addr_inline(dst);
        self.wln("0 >R");
        self.wln("BEGIN");
        self.indent += 1;
        self.wln(&format!("R@ {max_len_expr} < R@ {cap} < AND WHILE"));
        self.indent += 1;
        self.wln(&format!("PREAD-CHAR {base_addr} R@ 4 * + PVAR!"));
        self.wln("R> 1 + >R");
        self.indent -= 1;
        self.indent -= 1;
        self.wln("REPEAT");
        self.wln(&format!("0 {base_addr} R@ 4 * + PVAR!"));
        self.wln("R> DROP");
        Ok(())
    }

    fn emit_storage_decl(&mut self, name: &str, ty: &TypeInfo) -> Result<(), String> {
        let sz = self.type_size_bytes(ty)?;
        self.emit_storage_bytes_decl(name, sz)?;
        Ok(())
    }

    fn emit_storage_bytes_decl(&mut self, name: &str, sz: u32) -> Result<(), String> {
        let next = self
            .static_data_bytes
            .checked_add(sz)
            .ok_or_else(|| format!("static data layout overflow while allocating {name}"))?;
        if next > KFORTHC_RUNTIME_DATA_BYTES {
            return Err(format!(
                "static data {} bytes exceeds kforthc runtime limit {} bytes while allocating {name}; shrink global storage or add packed-char/runtime-frame support",
                next, KFORTHC_RUNTIME_DATA_BYTES
            ));
        }
        if sz <= 4 {
            self.wln(&format!("CREATE {name} 0 ,"));
        } else {
            self.wln(&format!("CREATE {name} 0 , {} ALLOT", sz - 4));
        }
        self.static_data_bytes = next;
        Ok(())
    }

    fn max_aggregate_return_bytes(&self, prog: &Program) -> Result<u32, String> {
        self.max_aggregate_return_bytes_in_routines(&prog.block.routines)
    }

    fn max_aggregate_return_bytes_in_routines(
        &self,
        routines: &[RoutineDecl],
    ) -> Result<u32, String> {
        let mut max = 0;
        for routine in routines {
            match routine {
                RoutineDecl::Procedure(p) => {
                    max = max.max(self.max_aggregate_return_bytes_in_routines(&p.block.routines)?);
                }
                RoutineDecl::Function(f) => {
                    let ty = self.ty_of_typeref(&f.ret_ty)?;
                    if matches!(
                        ty,
                        TypeInfo::Record(_) | TypeInfo::Sum(_) | TypeInfo::Array(_)
                    ) {
                        max = max.max(self.type_size_bytes(&ty)?);
                    }
                    max = max.max(self.max_aggregate_return_bytes_in_routines(&f.block.routines)?);
                }
            }
        }
        Ok(max)
    }

    fn type_size_bytes(&self, ty: &TypeInfo) -> Result<u32, String> {
        match ty {
            TypeInfo::Basic(_)
            | TypeInfo::Enum(_)
            | TypeInfo::Subrange(_)
            | TypeInfo::Set(_)
            | TypeInfo::Pointer(_)
            | TypeInfo::Nil => Ok(4),
            TypeInfo::Record(r) => Ok(r.size_bytes),
            TypeInfo::Sum(s) => Ok(s.size_bytes),
            TypeInfo::Array(a) => Ok(a.size_bytes),
        }
    }

    fn const_to_token(&self, c: &ConstExpr) -> Result<String, String> {
        Ok(match eval_const(self.env, c)? {
            ConstVal::I32(i) => i.to_string(),
            ConstVal::U32(u) => u.to_string(),
            ConstVal::Real(bits) => bits.to_string(),
            ConstVal::EnumVal { ordinal, .. } => ordinal.to_string(),
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

    fn runtime_param_slots(&self, scoped: &str, params: &[ParamDecl]) -> Vec<String> {
        let mut slots = Vec::new();
        for prm in params {
            if let Some(c) = &prm.conformant {
                for dim in &c.dims {
                    slots.push(self.slot_name(scoped, &dim.low_name));
                    slots.push(self.slot_name(scoped, &dim.high_name));
                }
            }
            slots.push(self.slot_name(scoped, &prm.name));
        }
        slots
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
                    conformant_bounds: None,
                },
            );
        }
        let routines = self.extend_routine_visibility(&HashMap::new(), top_routines, scope);
        Ctx {
            vars,
            routines,
            current_frame_slots: Vec::new(),
        }
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
                    let ty = self.ty_of_param_decl(prm)?;
                    ctx.vars.insert(
                        prm.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &prm.name),
                            ty,
                            by_ref: prm.by_ref || prm.conformant.is_some(),
                            conformant_bounds: prm.conformant.as_ref().map(|c| {
                                c.dims
                                    .iter()
                                    .map(|d| (d.low_name.clone(), d.high_name.clone()))
                                    .collect()
                            }),
                        },
                    );
                    if let Some(c) = &prm.conformant {
                        for dim in &c.dims {
                            let bound_ty = self.ty_of_typeref(&dim.index_ty)?;
                            ctx.vars.insert(
                                dim.low_name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &dim.low_name),
                                    ty: bound_ty.clone(),
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                            ctx.vars.insert(
                                dim.high_name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &dim.high_name),
                                    ty: bound_ty,
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                        }
                    }
                }
                for lv in &p.block.vars {
                    let ty = self.ty_of_typeref(&lv.ty)?;
                    ctx.vars.insert(
                        lv.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &lv.name),
                            ty,
                            by_ref: false,
                            conformant_bounds: None,
                        },
                    );
                }
            }
            RoutineDecl::Function(f) => {
                for prm in &f.params {
                    let ty = self.ty_of_param_decl(prm)?;
                    ctx.vars.insert(
                        prm.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &prm.name),
                            ty,
                            by_ref: prm.by_ref || prm.conformant.is_some(),
                            conformant_bounds: prm.conformant.as_ref().map(|c| {
                                c.dims
                                    .iter()
                                    .map(|d| (d.low_name.clone(), d.high_name.clone()))
                                    .collect()
                            }),
                        },
                    );
                    if let Some(c) = &prm.conformant {
                        for dim in &c.dims {
                            let bound_ty = self.ty_of_typeref(&dim.index_ty)?;
                            ctx.vars.insert(
                                dim.low_name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &dim.low_name),
                                    ty: bound_ty.clone(),
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                            ctx.vars.insert(
                                dim.high_name.clone(),
                                VarAccess {
                                    slot: self.slot_name(scoped, &dim.high_name),
                                    ty: bound_ty,
                                    by_ref: false,
                                    conformant_bounds: None,
                                },
                            );
                        }
                    }
                }
                for lv in &f.block.vars {
                    let ty = self.ty_of_typeref(&lv.ty)?;
                    ctx.vars.insert(
                        lv.name.clone(),
                        VarAccess {
                            slot: self.slot_name(scoped, &lv.name),
                            ty,
                            by_ref: false,
                            conformant_bounds: None,
                        },
                    );
                }
                ctx.vars.insert(
                    f.name.clone(),
                    VarAccess {
                        slot: self.slot_name(scoped, &f.name),
                        ty: self.ty_of_typeref(&f.ret_ty)?,
                        by_ref: false,
                        conformant_bounds: None,
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
                slots.extend(self.runtime_param_slots(&scoped, std::slice::from_ref(prm)));
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
                        },
                        SumArmInfo {
                            name: "some".into(),
                            tag: 1,
                            fields: vec![SumFieldInfo {
                                name: "value".into(),
                                offset_bytes: 0,
                                ty: inner_ty,
                            }],
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
                        },
                        SumArmInfo {
                            name: "err".into(),
                            tag: 1,
                            fields: vec![SumFieldInfo {
                                name: "error".into(),
                                offset_bytes: 0,
                                ty: err,
                            }],
                        },
                    ],
                    payload_size_bytes: payload,
                    size_bytes: 4 + payload,
                }))
            }
            TypeRef::Array { dims, elem } => build_array_info(self.env, dims, elem),
            TypeRef::Subrange { low, high } => build_subrange_info(self.env, low, high),
            TypeRef::Set(elem) => build_set_info(self.env, elem),
            TypeRef::Named(n) => {
                lookup_type(self.env, n).ok_or_else(|| format!("unknown type: {n}"))
            }
        }
    }

    fn ty_of_param_decl(&self, prm: &ParamDecl) -> Result<TypeInfo, String> {
        if let Some(c) = &prm.conformant {
            let mut ty = self.ty_of_typeref(&c.elem_ty)?;
            for _ in c.dims.iter().rev() {
                let elem_size_bytes = self.type_size_bytes(&ty)?;
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
        } else {
            self.ty_of_typeref(&prm.ty)
        }
    }

    fn ctx_to_types(&self, ctx: &Ctx) -> HashMap<String, TypeInfo> {
        let mut m = HashMap::new();
        for (k, v) in &ctx.vars {
            m.insert(k.clone(), v.ty.clone());
        }
        m
    }

    fn runtime_array_bounds_for_lvalue(&self, lv: &LValue, ctx: &Ctx) -> Option<(String, String)> {
        if !lv.sels.is_empty() {
            return None;
        }
        let v = ctx.vars.get(&lv.base)?;
        let bounds = v.conformant_bounds.as_ref()?;
        let (low_name, high_name) = bounds.first()?;
        let low_slot = ctx.vars.get(low_name)?.slot.clone();
        let high_slot = ctx.vars.get(high_name)?.slot.clone();
        Some((format!("{low_slot} PVAR@"), format!("{high_slot} PVAR@")))
    }

    fn runtime_array_bounds_for_expr(&self, expr: &Expr, ctx: &Ctx) -> Option<(String, String)> {
        let lv = expr_to_lvalue(expr)?;
        self.runtime_array_bounds_for_lvalue(&lv, ctx)
    }

    fn runtime_bound_slot_expr(&self, name: &str, ctx: &Ctx) -> Result<String, String> {
        let slot = ctx
            .vars
            .get(name)
            .ok_or_else(|| format!("unknown var: {name}"))?
            .slot
            .clone();
        Ok(format!("{slot} PVAR@"))
    }

    fn runtime_conformant_size_expr(
        &self,
        ty: &TypeInfo,
        bounds: &[(String, String)],
        ctx: &Ctx,
    ) -> Result<String, String> {
        if let TypeInfo::Array(a) = ty {
            if !bounds.is_empty() {
                let (low_name, high_name) = &bounds[0];
                let low = self.runtime_bound_slot_expr(low_name, ctx)?;
                let high = self.runtime_bound_slot_expr(high_name, ctx)?;
                let inner =
                    self.runtime_conformant_size_expr(a.elem_ty.as_ref(), &bounds[1..], ctx)?;
                return Ok(format!("{high} {low} - 1 + {inner} *"));
            }
            if a.size_bytes != 0 {
                return Ok(a.size_bytes.to_string());
            }
            return self.runtime_conformant_size_expr(a.elem_ty.as_ref(), &[], ctx);
        }
        Ok(self.type_size_bytes(ty)?.to_string())
    }

    fn rewrite_stmt_with_ctx(
        &self,
        stmt: &Stmt,
        bases: &[LValue],
        ctx: &Ctx,
    ) -> Result<Stmt, String> {
        Ok(match stmt {
            Stmt::Empty => Stmt::Empty,
            Stmt::Compound(v) => Stmt::Compound(
                v.iter()
                    .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Stmt::Assign(lv, rhs) => Stmt::Assign(
                self.rewrite_lvalue_with_ctx(lv, bases, ctx)?,
                self.rewrite_expr_with_ctx(rhs, bases, ctx)?,
            ),
            Stmt::Read(args) => Stmt::Read(
                args.iter()
                    .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
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
                init: self.rewrite_expr_with_ctx(init, bases, ctx)?,
                limit: self.rewrite_expr_with_ctx(limit, bases, ctx)?,
                downto: *downto,
                body: Box::new(self.rewrite_stmt_with_ctx(body, bases, ctx)?),
            },
            Stmt::If(c, t, e) => Stmt::If(
                self.rewrite_expr_with_ctx(c, bases, ctx)?,
                Box::new(self.rewrite_stmt_with_ctx(t, bases, ctx)?),
                e.as_ref()
                    .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx).map(Box::new))
                    .transpose()?,
            ),
            Stmt::With(inner, body) => {
                let mut merged = bases.to_vec();
                merged.extend(inner.iter().cloned());
                self.rewrite_stmt_with_ctx(body, &merged, ctx)?
            }
            Stmt::While(c, b) => Stmt::While(
                self.rewrite_expr_with_ctx(c, bases, ctx)?,
                Box::new(self.rewrite_stmt_with_ctx(b, bases, ctx)?),
            ),
            Stmt::Repeat(v, c) => Stmt::Repeat(
                v.iter()
                    .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
                self.rewrite_expr_with_ctx(c, bases, ctx)?,
            ),
            Stmt::Case {
                expr,
                arms,
                else_stmt,
            } => Stmt::Case {
                expr: self.rewrite_expr_with_ctx(expr, bases, ctx)?,
                arms: arms.clone(),
                else_stmt: else_stmt
                    .as_ref()
                    .map(|s| self.rewrite_stmt_with_ctx(s, bases, ctx).map(Box::new))
                    .transpose()?,
            },
            Stmt::ProcCall(name, args) => Stmt::ProcCall(
                name.clone(),
                args.iter()
                    .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Stmt::Write(args) => Stmt::Write(
                args.iter()
                    .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Stmt::WriteLn(args) => Stmt::WriteLn(
                args.iter()
                    .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Stmt::SumCase { .. } => stmt.clone(),
        })
    }

    fn rewrite_expr_with_ctx(
        &self,
        expr: &Expr,
        bases: &[LValue],
        ctx: &Ctx,
    ) -> Result<Expr, String> {
        Ok(match expr {
            Expr::Var(name)
                if !ctx.vars.contains_key(name)
                    && !self.env.consts.contains_key(name)
                    && !ctx.routines.contains_key(name) =>
            {
                Self::lvalue_to_expr(self.rewrite_lvalue_with_ctx(
                    &LValue {
                        base: name.clone(),
                        sels: vec![],
                    },
                    bases,
                    ctx,
                )?)
            }
            Expr::Call(name, args) => Expr::Call(
                name.clone(),
                args.iter()
                    .map(|e| self.rewrite_expr_with_ctx(e, bases, ctx))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Expr::Field(_, _) | Expr::Index(_, _) | Expr::Deref(_) => {
                if let Some(lv) = expr_to_lvalue(expr) {
                    Self::lvalue_to_expr(self.rewrite_lvalue_with_ctx(&lv, bases, ctx)?)
                } else {
                    expr.clone()
                }
            }
            Expr::Unary(op, inner) => Expr::Unary(
                *op,
                Box::new(self.rewrite_expr_with_ctx(inner, bases, ctx)?),
            ),
            Expr::Binary(a, op, b) => Expr::Binary(
                Box::new(self.rewrite_expr_with_ctx(a, bases, ctx)?),
                *op,
                Box::new(self.rewrite_expr_with_ctx(b, bases, ctx)?),
            ),
            Expr::SetLit(items) => Expr::SetLit(
                items
                    .iter()
                    .map(|item| match item {
                        SetItem::Single(e) => self
                            .rewrite_expr_with_ctx(e, bases, ctx)
                            .map(SetItem::Single),
                        SetItem::Range(lo, hi) => Ok(SetItem::Range(
                            self.rewrite_expr_with_ctx(lo, bases, ctx)?,
                            self.rewrite_expr_with_ctx(hi, bases, ctx)?,
                        )),
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Expr::Ctor(_, _)
            | Expr::ArrayLit(_)
            | Expr::RecordUpdate(_, _)
            | Expr::ArrayUpdate(_, _)
            | Expr::OptionNone
            | Expr::OptionSome(_)
            | Expr::Cond { .. }
            | Expr::Cast(_, _)
            | Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Char(_)
            | Expr::Real(_)
            | Expr::Str(_)
            | Expr::Var(_)
            | Expr::Nil => expr.clone(),
        })
    }

    fn rewrite_lvalue_with_ctx(
        &self,
        lv: &LValue,
        bases: &[LValue],
        ctx: &Ctx,
    ) -> Result<LValue, String> {
        if ctx.vars.contains_key(&lv.base) {
            return Ok(lv.clone());
        }
        for base in bases.iter().rev() {
            let bt = self.resolve_lvalue_addr_ctx(base, ctx)?.ty;
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

    fn coerce_real_inline(&self, e: &Expr, t: &TypeInfo, ctx: &Ctx) -> Result<String, String> {
        let v = self.gen_expr_inline_ctx(e, ctx)?;
        Ok(if matches!(t, TypeInfo::Basic(BasicType::Real)) {
            v
        } else {
            format!("{v} S>F")
        })
    }

    fn ordinal_inline(&self, e: &Expr, ctx: &Ctx) -> Result<String, String> {
        self.gen_expr_inline_ctx(e, ctx)
    }

    fn set_low_bound_expr(&self, set_expr: &Expr, ctx: &Ctx) -> Result<String, String> {
        let ty = type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, set_expr)?;
        match ty {
            TypeInfo::Set(s) => Ok(s.low.to_string()),
            _ => Err("right-hand side of 'in' must be a set".into()),
        }
    }

    fn gen_set_lit_inline(&self, items: &[SetItem], ctx: &Ctx) -> Result<String, String> {
        if items.is_empty() {
            return Ok("0".into());
        }
        let first_expr = match &items[0] {
            SetItem::Single(e) => e,
            SetItem::Range(lo, _) => lo,
        };
        let first_ty =
            type_of_expr_scoped(self.env, &self.ctx_to_types(ctx), &ctx.routines, first_expr)?;
        let low = match first_ty {
            TypeInfo::Enum(ref e) => e.low,
            TypeInfo::Subrange(ref s) => s.low,
            TypeInfo::Basic(BasicType::Boolean) => 0,
            TypeInfo::Basic(BasicType::Char) => 0,
            TypeInfo::Basic(BasicType::Integer) => 0,
            _ => return Err("set literal items must be ordinal".into()),
        };
        let mut parts = Vec::new();
        for item in items {
            match item {
                SetItem::Single(expr) => {
                    let iv = self.ordinal_inline(expr, ctx)?;
                    parts.push(format!("1 {iv} {low} - LSHIFT"));
                }
                SetItem::Range(lo_expr, hi_expr) => {
                    let lo = self.ordinal_inline(lo_expr, ctx)?;
                    let hi = self.ordinal_inline(hi_expr, ctx)?;
                    parts.push(format!("1 {hi} {lo} - 1 + LSHIFT 1 - {lo} {low} - LSHIFT"));
                }
            }
        }
        let mut out = String::new();
        for (idx, part) in parts.iter().enumerate() {
            if idx > 0 {
                out.push(' ');
            }
            out.push_str(part);
            if idx > 0 {
                out.push_str(" OR");
            }
        }
        Ok(out)
    }

    fn case_labels_inline(&self, labels: &[CaseLabel]) -> Result<String, String> {
        let mut parts = Vec::new();
        for label in labels {
            match label {
                CaseLabel::Single(c) => parts.push(format!("R@ {} =", self.const_to_token(c)?)),
                CaseLabel::Range(lo, hi) => {
                    parts.push(format!(
                        "R@ {} >= R@ {} <= AND",
                        self.const_to_token(lo)?,
                        self.const_to_token(hi)?
                    ));
                }
            }
        }
        if parts.is_empty() {
            return Ok("0".into());
        }
        let mut out = String::new();
        for (idx, part) in parts.iter().enumerate() {
            if idx > 0 {
                out.push(' ');
            }
            out.push_str(part);
            if idx > 0 {
                out.push_str(" OR");
            }
        }
        Ok(out)
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
        let lv = expr_to_lvalue(&args[0])
            .ok_or_else(|| format!("{name} argument must be lvalue pointer"))?;
        let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        if name.eq_ignore_ascii_case("dispose") {
            self.emit_store("0", &dst);
            return Ok(());
        }
        let target = match &dst.ty {
            TypeInfo::Pointer(n) => n.clone(),
            _ => return Err("new argument must be pointer".into()),
        };
        let pointee = lookup_type(self.env, &target)
            .ok_or_else(|| format!("unknown pointed type: {target}"))?;
        let sz = self.type_size_bytes(&pointee)?;
        self.wln("HERE __NEWP PVAR!");
        self.wln(&format!("{sz} ALLOT"));
        self.emit_store("__NEWP PVAR@", &dst);
        Ok(())
    }

    fn gen_builtin_inttohex(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 4 {
            return Err("IntToHex requires 4 arguments".into());
        }
        let value = self.gen_expr_inline_ctx(&args[0], ctx)?;
        let lv =
            expr_to_lvalue(&args[1]).ok_or("IntToHex second argument must be lvalue char array")?;
        let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        match &dst.ty {
            TypeInfo::Array(ai)
                if matches!(ai.elem_ty.as_ref(), TypeInfo::Basic(BasicType::Char)) => {}
            _ => return Err("IntToHex second argument must be array of char".into()),
        }
        let max_len = self.gen_expr_inline_ctx(&args[2], ctx)?;
        let zero_fill = self.gen_expr_inline_ctx(&args[3], ctx)?;
        self.wln(&format!("{value} __I2H_VAL PVAR!"));
        self.wln(&format!("{} __I2H_PTR PVAR!", self.emit_addr_inline(&dst)));
        self.wln(&format!("{max_len} __I2H_MAX PVAR!"));
        self.wln(&format!("{zero_fill} __I2H_FILL PVAR!"));
        self.wln("__I32_TO_HEX_STR");
        Ok(())
    }

    fn gen_builtin_setaddr(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 2 {
            return Err("SetAddr requires 2 arguments".into());
        }
        let lv = expr_to_lvalue(&args[0]).ok_or("SetAddr first argument must be lvalue pointer")?;
        let dst = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        match dst.ty {
            TypeInfo::Pointer(_) => {}
            _ => return Err("SetAddr first argument must be pointer".into()),
        }
        let addr = self.gen_expr_inline_ctx(&args[1], ctx)?;
        self.emit_store(&addr, &dst);
        Ok(())
    }

    fn gen_builtin_copy(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 2 {
            return Err("Copy requires 2 arguments".into());
        }
        let src = self.resolve_char_array_arg(&args[0], ctx, "Copy source")?;
        let dst = self.resolve_char_array_lvalue_arg(&args[1], ctx, "Copy destination")?;
        self.wln(&format!("{} __STR_SRC PVAR!", self.emit_addr_inline(&src)));
        self.wln(&format!("{} __STR_DST PVAR!", self.emit_addr_inline(&dst)));
        self.wln("__STRCPY");
        Ok(())
    }

    fn gen_builtin_concat(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Concat requires 3 arguments".into());
        }
        let a = self.resolve_char_array_arg(&args[0], ctx, "Concat first source")?;
        let b = self.resolve_char_array_arg(&args[1], ctx, "Concat second source")?;
        let dst = self.resolve_char_array_lvalue_arg(&args[2], ctx, "Concat destination")?;
        self.wln(&format!("{} __STR_SRC PVAR!", self.emit_addr_inline(&a)));
        self.wln(&format!("{} __STR_DST PVAR!", self.emit_addr_inline(&dst)));
        self.wln("__STRCPY");
        self.wln(&format!("{} __STR_SRC PVAR!", self.emit_addr_inline(&a)));
        self.wln("__STRLEN __STR_LEN PVAR!");
        self.wln(&format!("{} __STR_SRC PVAR!", self.emit_addr_inline(&b)));
        self.wln(&format!(
            "{} __STR_LEN PVAR@ 4 * + __STR_DST PVAR!",
            self.emit_addr_inline(&dst)
        ));
        self.wln("__STRCPY");
        Ok(())
    }

    fn gen_builtin_delete(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Delete requires 3 arguments".into());
        }
        let dst = self.resolve_char_array_lvalue_arg(&args[0], ctx, "Delete target")?;
        let idx = self.gen_expr_inline_ctx(&args[1], ctx)?;
        let cnt = self.gen_expr_inline_ctx(&args[2], ctx)?;
        self.wln(&format!("{} __STR_DST PVAR!", self.emit_addr_inline(&dst)));
        self.wln(&format!("{idx} __STR_IDX PVAR!"));
        self.wln(&format!("{cnt} __STR_CNT PVAR!"));
        self.wln("__STRDELETE");
        Ok(())
    }

    fn gen_builtin_insert(&mut self, args: &[Expr], ctx: &Ctx) -> Result<(), String> {
        if args.len() != 3 {
            return Err("Insert requires 3 arguments".into());
        }
        let src = self.resolve_char_array_arg(&args[0], ctx, "Insert source")?;
        let dst = self.resolve_char_array_lvalue_arg(&args[1], ctx, "Insert destination")?;
        let idx = self.gen_expr_inline_ctx(&args[2], ctx)?;
        self.wln(&format!("{} __STR_SRC PVAR!", self.emit_addr_inline(&src)));
        self.wln(&format!("{} __STR_DST PVAR!", self.emit_addr_inline(&dst)));
        self.wln(&format!("{idx} __STR_IDX PVAR!"));
        self.wln("__STRINSERT");
        Ok(())
    }

    fn resolve_char_array_arg(
        &self,
        expr: &Expr,
        ctx: &Ctx,
        what: &str,
    ) -> Result<AddrRef, String> {
        if let Expr::Str(s) = expr {
            let Some((name, _)) = self.string_literals.iter().find(|(_, value)| value == s) else {
                return Err(format!(
                    "internal: missing string literal backing storage for {what}"
                ));
            };
            let len = s.chars().count() as u32 + 1;
            return Ok(AddrRef {
                base_expr: name.clone(),
                offset: 0,
                dynamic_addr_expr: None,
                ty: TypeInfo::Array(ArrayInfo {
                    low: 0,
                    high: len as i32 - 1,
                    len,
                    elem_ty: Box::new(TypeInfo::Basic(BasicType::Char)),
                    elem_size_bytes: 4,
                    size_bytes: len * 4,
                }),
                variant_checks: Vec::new(),
            });
        }
        let lv = expr_to_lvalue(expr).ok_or_else(|| format!("{what} must be array of char"))?;
        let addr = self.resolve_lvalue_addr_ctx(&lv, ctx)?;
        match &addr.ty {
            TypeInfo::Array(ai)
                if matches!(ai.elem_ty.as_ref(), TypeInfo::Basic(BasicType::Char)) =>
            {
                Ok(addr)
            }
            _ => Err(format!("{what} must be array of char")),
        }
    }

    fn resolve_char_array_lvalue_arg(
        &self,
        expr: &Expr,
        ctx: &Ctx,
        what: &str,
    ) -> Result<AddrRef, String> {
        self.resolve_char_array_arg(expr, ctx, what)
    }

    fn collect_string_literals_program(&mut self, prog: &Program) {
        self.collect_string_literals_block(&prog.block);
    }

    fn collect_string_literals_block(&mut self, block: &Block) {
        for decl in &block.consts {
            self.collect_string_literals_const_expr(&decl.expr);
        }
        for routine in &block.routines {
            match routine {
                RoutineDecl::Procedure(p) => self.collect_string_literals_block(&p.block),
                RoutineDecl::Function(f) => self.collect_string_literals_block(&f.block),
            }
        }
        self.collect_string_literals_stmt(&block.body);
    }

    fn collect_string_literals_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Empty | Stmt::ReadLn => {}
            Stmt::Compound(stmts) => {
                for stmt in stmts {
                    self.collect_string_literals_stmt(stmt);
                }
            }
            Stmt::Assign(_, expr) => self.collect_string_literals_expr(expr),
            Stmt::Read(args) | Stmt::Write(args) | Stmt::WriteLn(args) => {
                for expr in args {
                    self.collect_string_literals_expr(expr);
                }
            }
            Stmt::For {
                init, limit, body, ..
            } => {
                self.collect_string_literals_expr(init);
                self.collect_string_literals_expr(limit);
                self.collect_string_literals_stmt(body);
            }
            Stmt::If(cond, then_s, else_s) => {
                self.collect_string_literals_expr(cond);
                self.collect_string_literals_stmt(then_s);
                if let Some(else_s) = else_s {
                    self.collect_string_literals_stmt(else_s);
                }
            }
            Stmt::With(_, body) | Stmt::While(_, body) => {
                if let Stmt::While(cond, _) = stmt {
                    self.collect_string_literals_expr(cond);
                }
                self.collect_string_literals_stmt(body);
            }
            Stmt::Repeat(stmts, cond) => {
                for stmt in stmts {
                    self.collect_string_literals_stmt(stmt);
                }
                self.collect_string_literals_expr(cond);
            }
            Stmt::Case {
                expr,
                arms,
                else_stmt,
            } => {
                self.collect_string_literals_expr(expr);
                for (_, stmt) in arms {
                    self.collect_string_literals_stmt(stmt);
                }
                if let Some(stmt) = else_stmt {
                    self.collect_string_literals_stmt(stmt);
                }
            }
            Stmt::ProcCall(_, args) => {
                for expr in args {
                    self.collect_string_literals_expr(expr);
                }
            }
            Stmt::SumCase {
                expr,
                arms,
                else_stmt,
            } => {
                self.collect_string_literals_expr(expr);
                for arm in arms {
                    self.collect_string_literals_stmt(&arm.body);
                }
                if let Some(stmt) = else_stmt {
                    self.collect_string_literals_stmt(stmt);
                }
            }
        }
    }

    fn collect_string_literals_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Str(s) => self.intern_string_literal(s),
            Expr::Call(_, args) => {
                for expr in args {
                    self.collect_string_literals_expr(expr);
                }
            }
            Expr::Ctor(_, named) => {
                for (_, expr) in named {
                    self.collect_string_literals_expr(expr);
                }
            }
            Expr::ArrayLit(items) => {
                for expr in items {
                    self.collect_string_literals_expr(expr);
                }
            }
            Expr::RecordUpdate(base, named) => {
                self.collect_string_literals_expr(base);
                for (_, expr) in named {
                    self.collect_string_literals_expr(expr);
                }
            }
            Expr::ArrayUpdate(base, pairs) => {
                self.collect_string_literals_expr(base);
                for (idx, expr) in pairs {
                    self.collect_string_literals_expr(idx);
                    self.collect_string_literals_expr(expr);
                }
            }
            Expr::OptionSome(expr) | Expr::Cast(_, expr) => self.collect_string_literals_expr(expr),
            Expr::Cond { arms, else_block } => {
                for arm in arms {
                    self.collect_string_literals_expr(&arm.cond);
                    for stmt in &arm.block.stmts {
                        self.collect_string_literals_stmt(stmt);
                    }
                    self.collect_string_literals_expr(&arm.block.value);
                }
                for stmt in &else_block.stmts {
                    self.collect_string_literals_stmt(stmt);
                }
                self.collect_string_literals_expr(&else_block.value);
            }
            Expr::Deref(expr) | Expr::Field(expr, _) | Expr::Unary(_, expr) => {
                self.collect_string_literals_expr(expr)
            }
            Expr::Index(base, index) | Expr::Binary(base, _, index) => {
                self.collect_string_literals_expr(base);
                self.collect_string_literals_expr(index);
            }
            Expr::SetLit(items) => {
                for item in items {
                    match item {
                        SetItem::Single(expr) => self.collect_string_literals_expr(expr),
                        SetItem::Range(lo, hi) => {
                            self.collect_string_literals_expr(lo);
                            self.collect_string_literals_expr(hi);
                        }
                    }
                }
            }
            Expr::Int(_)
            | Expr::Bool(_)
            | Expr::Char(_)
            | Expr::Real(_)
            | Expr::Nil
            | Expr::OptionNone
            | Expr::Var(_) => {}
        }
    }

    fn collect_string_literals_const_expr(&mut self, expr: &ConstExpr) {
        match expr {
            ConstExpr::Call(_, args) => {
                for expr in args {
                    self.collect_string_literals_const_expr(expr);
                }
            }
            ConstExpr::Unary(_, expr) => self.collect_string_literals_const_expr(expr),
            ConstExpr::Binary(a, _, b) => {
                self.collect_string_literals_const_expr(a);
                self.collect_string_literals_const_expr(b);
            }
            ConstExpr::Int(_)
            | ConstExpr::Bool(_)
            | ConstExpr::Char(_)
            | ConstExpr::Real(_)
            | ConstExpr::Const(_) => {}
        }
    }

    fn intern_string_literal(&mut self, value: &str) {
        if self
            .string_literals
            .iter()
            .any(|(_, existing)| existing == value)
        {
            return;
        }
        let name = format!("__STRLIT_{}", self.string_literals.len());
        self.string_literals.push((name, value.to_string()));
    }
}

fn parse_hex_text(s: &str) -> Result<i32, String> {
    let raw = s.trim();
    let raw = raw
        .strip_prefix("0x")
        .or_else(|| raw.strip_prefix("0X"))
        .or_else(|| raw.strip_prefix('$'))
        .unwrap_or(raw);
    if raw.is_empty() {
        return Ok(0);
    }
    i32::from_str_radix(raw, 16).map_err(|_| "invalid hex string literal for HexToInt".into())
}
