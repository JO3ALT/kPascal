type
  ident_buf = array[0..37] of char;
  lit_buf = array[0..95] of char;

const
  IDENT_LAST = 37;
  LIT_LAST = 95;
  MAX_CAPTURED_WRITELNS = 128;
  MAX_AST_VARS = 8192;
  MAX_AST_STMTS = 131072;
  MAX_AST_ARGS = 65536;
  MAX_AST_EXPRS = 131072;
  MAX_AST_TYPES = 2048;
  MAX_AST_FIELDS = 16384;
  MAX_AST_ROUTINES = 4096;
  MAX_AST_PARAMS = 16384;
  MAX_AST_TEXT_LITS = 16384;
  MAX_AST_IDENTS = 65536;
  MAX_AST_ENUM_CONSTS = 8192;
  CAPTURE_KIND_NONE = 0;
  CAPTURE_KIND_INT = 1;
  CAPTURE_KIND_TEXT = 2;
  CAPTURE_KIND_CHAR = 3;
  AST_STMT_NONE = 0;
  AST_STMT_WRITELN = 1;
  AST_STMT_ASSIGN = 2;
  AST_STMT_COMPOUND = 3;
  AST_STMT_IF = 4;
  AST_STMT_WHILE = 5;
  AST_STMT_REPEAT = 6;
  AST_STMT_FOR = 7;
  AST_STMT_CALL = 8;
  AST_STMT_WRITE = 9;
  AST_STMT_READ = 10;
  AST_ARG_NONE = 0;
  AST_ARG_INT = 1;
  AST_ARG_TEXT = 2;
  AST_ARG_CHAR = 3;
  AST_ARG_BOOL = 4;
  AST_ARG_IDENT = 5;
  AST_ARG_EXPR = 6;
  AST_EXPR_NONE = 0;
  AST_EXPR_INT = 1;
  AST_EXPR_BOOL = 2;
  AST_EXPR_CHAR = 3;
  AST_EXPR_IDENT = 4;
  AST_EXPR_BINOP = 5;
  AST_EXPR_UNARY = 6;
  AST_EXPR_FIELD = 7;
  AST_EXPR_INDEX = 8;
  AST_EXPR_CALL = 9;
  AST_EXPR_DEREF = 10;
  AST_EXPR_NIL = 11;
  AST_TYPE_UNKNOWN = 0;
  AST_TYPE_INTEGER = 1;
  AST_TYPE_BOOLEAN = 2;
  AST_TYPE_CHAR = 3;
  AST_TYPE_REAL = 4;
  AST_TYPE_RECORD = 5;
  AST_TYPE_ARRAY = 6;
  AST_TYPE_POINTER = 7;
  AST_DECL_NONE = 0;
  AST_DECL_RECORD = 1;
  AST_DECL_ARRAY = 2;
  AST_DECL_ENUM = 3;
  AST_DECL_SET = 4;
  AST_DECL_SUBRANGE = 5;
  AST_ROUTINE_NONE = 0;
  AST_ROUTINE_PROCEDURE = 1;
  AST_ROUTINE_FUNCTION = 2;
  TOK_EOF = 0;
  TOK_IDENT = 1;
  TOK_INT = 2;
  TOK_STR = 3;
  TOK_LPAREN = 10;
  TOK_RPAREN = 11;
  TOK_LBRACK = 12;
  TOK_RBRACK = 13;
  TOK_SEMI = 14;
  TOK_COLON = 15;
  TOK_COMMA = 16;
  TOK_DOT = 17;
  TOK_DOTDOT = 18;
  TOK_ASSIGN = 19;
  TOK_CARET = 20;
  TOK_EQ = 21;
  TOK_NE = 22;
  TOK_LT = 23;
  TOK_LE = 24;
  TOK_GT = 25;
  TOK_GE = 26;
  TOK_PLUS = 27;
  TOK_MINUS = 28;
  TOK_STAR = 29;
  TOK_SLASH = 30;
  TOK_KW_PROGRAM = 40;
  TOK_KW_CONST = 41;
  TOK_KW_TYPE = 42;
  TOK_KW_VAR = 43;
  TOK_KW_PROCEDURE = 44;
  TOK_KW_FUNCTION = 45;
  TOK_KW_BEGIN = 46;
  TOK_KW_END = 47;
  TOK_KW_READ = 48;
  TOK_KW_READLN = 49;
  TOK_KW_WRITE = 50;
  TOK_KW_WRITELN = 51;
  TOK_KW_FOR = 52;
  TOK_KW_TO = 53;
  TOK_KW_DOWNTO = 54;
  TOK_KW_DO = 55;
  TOK_KW_CASE = 56;
  TOK_KW_OF = 57;
  TOK_KW_ELSE = 58;
  TOK_KW_IF = 59;
  TOK_KW_THEN = 60;
  TOK_KW_WITH = 61;
  TOK_KW_WHILE = 62;
  TOK_KW_REPEAT = 63;
  TOK_KW_UNTIL = 64;
  TOK_KW_RECORD = 65;
  TOK_KW_SET = 66;
  TOK_KW_ARRAY = 67;
  TOK_KW_TRUE = 68;
  TOK_KW_FALSE = 69;
  TOK_KW_NIL = 70;
  TOK_KW_IN = 71;
  TOK_KW_DIV = 72;
  TOK_KW_MOD = 73;
  TOK_KW_AND = 74;
  TOK_KW_OR = 75;
  TOK_KW_XOR = 76;
  TOK_KW_NOT = 77;
  TOK_KW_INTEGER = 78;
  TOK_KW_BOOLEAN = 79;
  TOK_KW_CHAR = 80;
  TOK_KW_REAL = 81;
  TOK_REAL_LIT = 82;

var
  token_text: text_buf;
  program_name: text_buf;
  kw_program: text_buf;
  kw_const: text_buf;
  kw_type: text_buf;
  kw_var: text_buf;
  kw_procedure: text_buf;
  kw_function: text_buf;
  kw_begin: text_buf;
  kw_end: text_buf;
  kw_read: text_buf;
  kw_readln: text_buf;
  kw_write: text_buf;
  kw_writeln: text_buf;
  kw_for: text_buf;
  kw_to: text_buf;
  kw_downto: text_buf;
  kw_do: text_buf;
  kw_case: text_buf;
  kw_of: text_buf;
  kw_else: text_buf;
  kw_if: text_buf;
  kw_then: text_buf;
  kw_with: text_buf;
  kw_while: text_buf;
  kw_repeat: text_buf;
  kw_until: text_buf;
  kw_record: text_buf;
  kw_array: text_buf;
  kw_set: text_buf;
  kw_true: text_buf;
  kw_false: text_buf;
  kw_nil: text_buf;
  kw_in: text_buf;
  kw_div: text_buf;
  kw_mod: text_buf;
  kw_and: text_buf;
  kw_or: text_buf;
  kw_xor: text_buf;
  kw_not: text_buf;
  kw_integer: text_buf;
  kw_boolean: text_buf;
  kw_char: text_buf;
  kw_real: text_buf;
  stream_current_char: char;
  stream_has_char: boolean;
  stream_eof: boolean;
  stream_remaining: integer;
  source_next_code: integer;
  source_buffered_char: char;
  source_has_buffered_char: boolean;
  token_kind: integer;
  token_value: integer;
  saw_probe_read_prefix: boolean;
  saw_probe_builtin_prefix: boolean;
  saw_probe_step_proc: boolean;
  saw_seed_char_decl: boolean;
  saw_seed_char_assign: boolean;
  saw_seed_char_writeln: boolean;
  bootstrap_has_non_writeln_stmt: boolean;
  bootstrap_capture_failed: boolean;
  parse_error_reason: integer;
  parse_error_stmt_idx: integer;
  parse_error_routine_idx: integer;
  captured_writeln_count: integer;
  captured_writeln_kind: array[0..127] of integer;
  captured_writeln_int: array[0..127] of integer;
  captured_writeln_text: array[0..127] of text_buf;
  ast_capture_enabled: boolean;
  ast_capture_var_names: boolean;
  ast_with_var: integer;
  ast_with_type_ref: integer;
  ast_var_count: integer;
  ast_var_name: array[0..8191] of ident_buf;
  ast_var_type: array[0..8191] of integer;
  ast_var_type_ref: array[0..8191] of integer;
  ast_var_owner_routine: array[0..8191] of integer;
  ast_type_count: integer;
  ast_type_name: array[0..2047] of ident_buf;
  ast_type_kind: array[0..2047] of integer;
  ast_type_elem_type: array[0..2047] of integer;
  ast_type_elem_type_ref: array[0..2047] of integer;
  ast_type_array_low: array[0..2047] of integer;
  ast_type_array_high: array[0..2047] of integer;
  ast_type_array_len: array[0..2047] of integer;
  ast_type_array_size: array[0..2047] of integer;
  ast_type_field_start: array[0..2047] of integer;
  ast_type_field_count: array[0..2047] of integer;
  ast_enum_const_count: integer;
  ast_enum_const_name: array[0..8191] of ident_buf;
  ast_enum_const_value: array[0..8191] of integer;
  ast_enum_const_type_ref: array[0..8191] of integer;
  ast_field_count: integer;
  ast_field_name: array[0..16383] of ident_buf;
  ast_field_type: array[0..16383] of integer;
  ast_field_offset: array[0..16383] of integer;
  ast_root_stmt_start: integer;
  ast_root_stmt_count: integer;
  ast_stmt_count: integer;
  ast_stmt_kind: array[0..131071] of integer;
  ast_stmt_name: array[0..131071] of ident_buf;
  ast_stmt_value_kind: array[0..131071] of integer;
  ast_stmt_value_int: array[0..131071] of integer;
  ast_stmt_value_text_ref: array[0..131071] of integer;
  ast_stmt_expr: array[0..131071] of integer;
  ast_stmt_aux_expr: array[0..131071] of integer;
  ast_stmt_arg_start: array[0..131071] of integer;
  ast_stmt_arg_count: array[0..131071] of integer;
  ast_stmt_child_start: array[0..131071] of integer;
  ast_stmt_child_count: array[0..131071] of integer;
  ast_stmt_else_start: array[0..131071] of integer;
  ast_stmt_else_count: array[0..131071] of integer;
  ast_arg_count: integer;
  ast_arg_kind: array[0..65535] of integer;
  ast_arg_int: array[0..65535] of integer;
  ast_arg_text_ref: array[0..65535] of integer;
  ast_arg_expr: array[0..65535] of integer;
  ast_expr_count: integer;
  ast_expr_kind: array[0..131071] of integer;
  ast_expr_int: array[0..131071] of integer;
  ast_expr_text_ref: array[0..131071] of integer;
  ast_expr_op: array[0..131071] of integer;
  ast_expr_left: array[0..131071] of integer;
  ast_expr_right: array[0..131071] of integer;
  ast_routine_count: integer;
  ast_routine_name: array[0..4095] of ident_buf;
  ast_routine_kind: array[0..4095] of integer;
  ast_routine_param_start: array[0..4095] of integer;
  ast_routine_param_count: array[0..4095] of integer;
  ast_routine_stmt_start: array[0..4095] of integer;
  ast_routine_stmt_count: array[0..4095] of integer;
  ast_routine_var_start: array[0..4095] of integer;
  ast_routine_var_count: array[0..4095] of integer;
  ast_routine_ret_type: array[0..4095] of integer;
  ast_param_count: integer;
  ast_param_name: array[0..16383] of ident_buf;
  ast_param_type: array[0..16383] of integer;
  ast_param_type_ref: array[0..16383] of integer;
  ast_param_by_ref: array[0..16383] of integer;
  ast_param_hidden: array[0..16383] of integer;
  ast_param_conformant_bound_start: array[0..16383] of integer;
  ast_param_conformant_dim_count: array[0..16383] of integer;
  ast_text_lit_count: integer;
  ast_text_lit: array[0..16383] of lit_buf;
  ast_ident_count: integer;
  ast_ident_pool: array[0..65535] of ident_buf;
  ast_current_routine: integer;
  ast_emit_routine: integer;

procedure ClearIdent(var s: ident_buf);
var i: integer;
    p: text_cell_ptr;
    addr: integer;
begin
  addr := Addr(s);
  for i := 0 to IDENT_LAST do
    begin
      SetAddr(p, addr);
      p^ := 0;
      addr := addr + 4
    end
end;

procedure CopyTextToIdent(var src: text_buf; var dst: ident_buf);
var i: integer;
begin
  for i := 0 to IDENT_LAST do
    begin
      if i < IDENT_LAST then
        begin
          dst[i] := src[i]
        end
      else
        begin
          dst[i] := #0
        end
    end
end;

procedure CopyTextToLit(var src: text_buf; var dst: lit_buf);
var i: integer;
begin
  for i := 0 to LIT_LAST do
    begin
      if i < LIT_LAST then
        begin
          dst[i] := src[i]
        end
      else
        begin
          dst[i] := #0
        end
    end
end;

function StrCmpTextIdent(var text: text_buf; var ident: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpTextIdent := 0;
  done := false;
  for i := 0 to IDENT_LAST do
    begin
      if done = false then
        begin
          if text[i] <> ident[i] then
            begin
              StrCmpTextIdent := Ord(text[i]) - Ord(ident[i]);
              done := true
            end
          else if text[i] = #0 then
            begin
              done := true
            end
        end
    end;
  if done = false then
    begin
      if text[IDENT_LAST + 1] <> #0 then
        begin
          StrCmpTextIdent := Ord(text[IDENT_LAST + 1])
        end
    end
end;

function StrCmpTextIdentTail(var text: text_buf; var ident: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpTextIdentTail := 0;
  done := false;
  for i := 1 to IDENT_LAST do
    begin
      if done = false then
        begin
          if text[i] <> ident[i] then
            begin
              StrCmpTextIdentTail := Ord(text[i]) - Ord(ident[i]);
              done := true
            end
          else if text[i] = #0 then
            begin
              done := true
            end
        end
    end
end;

function StrCmpTextIdentShifted(var text: text_buf; var ident: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpTextIdentShifted := 0;
  done := false;
  for i := 0 to IDENT_LAST - 1 do
    begin
      if done = false then
        begin
          if text[i] <> ident[i + 1] then
            begin
              StrCmpTextIdentShifted := Ord(text[i]) - Ord(ident[i + 1]);
              done := true
            end
          else if text[i] = #0 then
            begin
              done := true
            end
        end
    end;
  if done = false then
    begin
      if text[IDENT_LAST] <> #0 then
        begin
          StrCmpTextIdentShifted := Ord(text[IDENT_LAST])
        end
    end
end;

function TextIdentEq(var text: text_buf; var ident: ident_buf): boolean;
begin
  TextIdentEq := StrCmpTextIdent(text, ident) = 0;
  if not TextIdentEq then
    begin
      if text[0] = #0 then
        begin
          TextIdentEq := StrCmpTextIdentTail(text, ident) = 0
        end
      else if ident[0] = #0 then
        begin
          TextIdentEq := StrCmpTextIdentShifted(text, ident) = 0
        end
    end
end;

function TextEqIgnoreCaseOrTail(var text: text_buf; var expected: text_buf): boolean;
var i: integer;
    done: boolean;
begin
  TextEqIgnoreCaseOrTail := true;
  done := false;
  i := 0;
  if text[0] = #0 then
    begin
      i := 1
    end;
  while i <= 255 do
    begin
      if done = false then
        begin
          if ToLowerChar(text[i]) <> ToLowerChar(expected[i]) then
            begin
              TextEqIgnoreCaseOrTail := false;
              done := true
            end
          else if expected[i] = #0 then
            begin
              done := true
            end;
          i := i + 1
        end
      else
        begin
          i := 256
        end
    end
end;

function MaybeBuiltinConstName(var name: text_buf): boolean;
begin
  MaybeBuiltinConstName := false;
  if name[0] = 'a' then
    begin
      if name[1] = 's' then
        begin
          if name[2] = 't' then
            begin
              if name[3] = '_' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
  else if name[0] = 't' then
    begin
      if name[1] = 'o' then
        begin
          if name[2] = 'k' then
            begin
              if name[3] = '_' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
  else if name[0] = 'm' then
    begin
      if name[1] = 'a' then
        begin
          if name[2] = 'x' then
            begin
              if name[3] = '_' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
  else if name[0] = 'c' then
    begin
      if name[1] = 'a' then
        begin
          if name[2] = 'p' then
            begin
              if name[3] = 't' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
  else if name[0] = 'i' then
    begin
      if name[1] = 'd' then
        begin
          if name[2] = 'e' then
            begin
              if name[3] = 'n' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
  else if name[0] = 'l' then
    begin
      if name[1] = 'i' then
        begin
          if name[2] = 't' then
            begin
              if name[3] = '_' then
                begin
                  MaybeBuiltinConstName := true
                end
            end
        end
    end
end;

function TryResolveBuiltinConst(var name: text_buf; var value: integer): boolean;
var expected: text_buf;
    expected_ident: ident_buf;
    normalized: text_buf;
    i: integer;
begin
  TryResolveBuiltinConst := false;
  value := 0;
  ClearText(normalized);
  for i := 0 to 255 do
    begin
      normalized[i] := ToLowerChar(name[i])
    end;
  StrCopy(normalized, name);
  if not MaybeBuiltinConstName(name) then
    begin
      value := 0
    end
  else

    begin
      ClearText(expected);
      expected := 'ident_last';
      CopyTextToIdent(expected, expected_ident);
      if TextEqIgnoreCaseOrTail(name, expected) then
        begin
          value := 37;
          TryResolveBuiltinConst := true
        end
      else if TextIdentEq(name, expected_ident) then
        begin
          value := 37;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'lit_last';
      CopyTextToIdent(expected, expected_ident);
      if TextEqIgnoreCaseOrTail(name, expected) then
        begin
          value := 95;
          TryResolveBuiltinConst := true
        end
      else if TextIdentEq(name, expected_ident) then
        begin
          value := 95;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_writeln';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_assign';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_compound';
      if StrCmp(name, expected) = 0 then
        begin
          value := 3;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_if';
      if StrCmp(name, expected) = 0 then
        begin
          value := 4;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_while';
      if StrCmp(name, expected) = 0 then
        begin
          value := 5;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_repeat';
      if StrCmp(name, expected) = 0 then
        begin
          value := 6;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_for';
      if StrCmp(name, expected) = 0 then
        begin
          value := 7;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_call';
      if StrCmp(name, expected) = 0 then
        begin
          value := 8;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_write';
      if StrCmp(name, expected) = 0 then
        begin
          value := 9;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_stmt_read';
      if StrCmp(name, expected) = 0 then
        begin
          value := 10;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_none';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_int';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_text';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_char';
      if StrCmp(name, expected) = 0 then
        begin
          value := 3;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_bool';
      if StrCmp(name, expected) = 0 then
        begin
          value := 4;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_ident';
      if StrCmp(name, expected) = 0 then
        begin
          value := 5;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_arg_expr';
      if StrCmp(name, expected) = 0 then
        begin
          value := 6;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_none';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_int';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_bool';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_char';
      if StrCmp(name, expected) = 0 then
        begin
          value := 3;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_ident';
      if StrCmp(name, expected) = 0 then
        begin
          value := 4;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_binop';
      if StrCmp(name, expected) = 0 then
        begin
          value := 5;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_unary';
      if StrCmp(name, expected) = 0 then
        begin
          value := 6;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_field';
      if StrCmp(name, expected) = 0 then
        begin
          value := 7;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_index';
      if StrCmp(name, expected) = 0 then
        begin
          value := 8;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_call';
      if StrCmp(name, expected) = 0 then
        begin
          value := 9;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_expr_deref';
      if StrCmp(name, expected) = 0 then
        begin
          value := 10;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_unknown';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_integer';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_boolean';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_char';
      if StrCmp(name, expected) = 0 then
        begin
          value := 3;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_real';
      if StrCmp(name, expected) = 0 then
        begin
          value := 4;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_record';
      if StrCmp(name, expected) = 0 then
        begin
          value := 5;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_type_array';
      if StrCmp(name, expected) = 0 then
        begin
          value := 6;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_decl_none';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_decl_record';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_decl_array';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_routine_none';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_routine_procedure';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'ast_routine_function';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_eof';
      if StrCmp(name, expected) = 0 then
        begin
          value := 0;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_ident';
      if StrCmp(name, expected) = 0 then
        begin
          value := 1;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_int';
      if StrCmp(name, expected) = 0 then
        begin
          value := 2;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_str';
      if StrCmp(name, expected) = 0 then
        begin
          value := 3;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_lparen';
      if StrCmp(name, expected) = 0 then
        begin
          value := 10;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_rparen';
      if StrCmp(name, expected) = 0 then
        begin
          value := 11;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_lbrack';
      if StrCmp(name, expected) = 0 then
        begin
          value := 12;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_rbrack';
      if StrCmp(name, expected) = 0 then
        begin
          value := 13;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_semi';
      if StrCmp(name, expected) = 0 then
        begin
          value := 14;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_colon';
      if StrCmp(name, expected) = 0 then
        begin
          value := 15;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_comma';
      if StrCmp(name, expected) = 0 then
        begin
          value := 16;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_dot';
      if StrCmp(name, expected) = 0 then
        begin
          value := 17;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_dotdot';
      if StrCmp(name, expected) = 0 then
        begin
          value := 18;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_assign';
      if StrCmp(name, expected) = 0 then
        begin
          value := 19;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_caret';
      if StrCmp(name, expected) = 0 then
        begin
          value := 20;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_eq';
      if StrCmp(name, expected) = 0 then
        begin
          value := 21;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_ne';
      if StrCmp(name, expected) = 0 then
        begin
          value := 22;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_lt';
      if StrCmp(name, expected) = 0 then
        begin
          value := 23;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_le';
      if StrCmp(name, expected) = 0 then
        begin
          value := 24;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_gt';
      if StrCmp(name, expected) = 0 then
        begin
          value := 25;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_ge';
      if StrCmp(name, expected) = 0 then
        begin
          value := 26;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_plus';
      if StrCmp(name, expected) = 0 then
        begin
          value := 27;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_minus';
      if StrCmp(name, expected) = 0 then
        begin
          value := 28;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_star';
      if StrCmp(name, expected) = 0 then
        begin
          value := 29;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_slash';
      if StrCmp(name, expected) = 0 then
        begin
          value := 30;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_program';
      if StrCmp(name, expected) = 0 then
        begin
          value := 40;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_const';
      if StrCmp(name, expected) = 0 then
        begin
          value := 41;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_type';
      if StrCmp(name, expected) = 0 then
        begin
          value := 42;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_var';
      if StrCmp(name, expected) = 0 then
        begin
          value := 43;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_procedure';
      if StrCmp(name, expected) = 0 then
        begin
          value := 44;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_function';
      if StrCmp(name, expected) = 0 then
        begin
          value := 45;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_begin';
      if StrCmp(name, expected) = 0 then
        begin
          value := 46;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_end';
      if StrCmp(name, expected) = 0 then
        begin
          value := 47;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_read';
      if StrCmp(name, expected) = 0 then
        begin
          value := 48;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_readln';
      if StrCmp(name, expected) = 0 then
        begin
          value := 49;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_write';
      if StrCmp(name, expected) = 0 then
        begin
          value := 50;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_writeln';
      if StrCmp(name, expected) = 0 then
        begin
          value := 51;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_for';
      if StrCmp(name, expected) = 0 then
        begin
          value := 52;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_to';
      if StrCmp(name, expected) = 0 then
        begin
          value := 53;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_downto';
      if StrCmp(name, expected) = 0 then
        begin
          value := 54;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_do';
      if StrCmp(name, expected) = 0 then
        begin
          value := 55;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_case';
      if StrCmp(name, expected) = 0 then
        begin
          value := 56;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_of';
      if StrCmp(name, expected) = 0 then
        begin
          value := 57;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_else';
      if StrCmp(name, expected) = 0 then
        begin
          value := 58;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_if';
      if StrCmp(name, expected) = 0 then
        begin
          value := 59;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_then';
      if StrCmp(name, expected) = 0 then
        begin
          value := 60;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_with';
      if StrCmp(name, expected) = 0 then
        begin
          value := 61;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_while';
      if StrCmp(name, expected) = 0 then
        begin
          value := 62;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_repeat';
      if StrCmp(name, expected) = 0 then
        begin
          value := 63;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_until';
      if StrCmp(name, expected) = 0 then
        begin
          value := 64;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_record';
      if StrCmp(name, expected) = 0 then
        begin
          value := 65;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_set';
      if StrCmp(name, expected) = 0 then
        begin
          value := 66;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_array';
      if StrCmp(name, expected) = 0 then
        begin
          value := 67;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_true';
      if StrCmp(name, expected) = 0 then
        begin
          value := 68;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_false';
      if StrCmp(name, expected) = 0 then
        begin
          value := 69;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_nil';
      if StrCmp(name, expected) = 0 then
        begin
          value := 70;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_in';
      if StrCmp(name, expected) = 0 then
        begin
          value := 71;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_div';
      if StrCmp(name, expected) = 0 then
        begin
          value := 72;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_mod';
      if StrCmp(name, expected) = 0 then
        begin
          value := 73;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_and';
      if StrCmp(name, expected) = 0 then
        begin
          value := 74;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_or';
      if StrCmp(name, expected) = 0 then
        begin
          value := 75;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_xor';
      if StrCmp(name, expected) = 0 then
        begin
          value := 76;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_not';
      if StrCmp(name, expected) = 0 then
        begin
          value := 77;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_integer';
      if StrCmp(name, expected) = 0 then
        begin
          value := 78;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_boolean';
      if StrCmp(name, expected) = 0 then
        begin
          value := 79;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_char';
      if StrCmp(name, expected) = 0 then
        begin
          value := 80;
          TryResolveBuiltinConst := true
        end
    end;
  if not TryResolveBuiltinConst then
    begin
      ClearText(expected);
      expected := 'tok_kw_real';
      if StrCmp(name, expected) = 0 then
        begin
          value := 81;
          TryResolveBuiltinConst := true
        end
    end
end;

function StrCmpIdentIdent(var a: ident_buf; var b: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpIdentIdent := 0;
  done := false;
  for i := 0 to IDENT_LAST do
    begin
      if done = false then
        begin
          if a[i] <> b[i] then
            begin
              StrCmpIdentIdent := Ord(a[i]) - Ord(b[i]);
              done := true
            end
          else if a[i] = #0 then
            begin
              done := true
            end
        end
    end
end;

function StrCmpIdentIdentTail(var a: ident_buf; var b: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpIdentIdentTail := 0;
  done := false;
  for i := 1 to IDENT_LAST do
    begin
      if done = false then
        begin
          if a[i] <> b[i] then
            begin
              StrCmpIdentIdentTail := Ord(a[i]) - Ord(b[i]);
              done := true
            end
          else if a[i] = #0 then
            begin
              done := true
            end
        end
    end
end;

function StrCmpIdentIdentShifted(var shifted: ident_buf; var normal: ident_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpIdentIdentShifted := 0;
  done := false;
  for i := 0 to IDENT_LAST - 1 do
    begin
      if done = false then
        begin
          if shifted[i + 1] <> normal[i] then
            begin
              StrCmpIdentIdentShifted := Ord(shifted[i + 1]) - Ord(normal[i]);
              done := true
            end
          else if normal[i] = #0 then
            begin
              done := true
            end
        end
    end;
  if done = false then
    begin
      if shifted[IDENT_LAST] <> #0 then
        begin
          StrCmpIdentIdentShifted := Ord(shifted[IDENT_LAST])
        end
    end
end;

function IdentEq(var a: ident_buf; var b: ident_buf): boolean;
begin
  IdentEq := StrCmpIdentIdent(a, b) = 0;
  if not IdentEq then
    begin
      if a[0] = #0 then
        begin
          IdentEq := StrCmpIdentIdentTail(a, b) = 0;
          if not IdentEq then
            begin
              IdentEq := StrCmpIdentIdentShifted(a, b) = 0
            end
        end
      else if b[0] = #0 then
        begin
          IdentEq := StrCmpIdentIdentTail(b, a) = 0;
          if not IdentEq then
            begin
              IdentEq := StrCmpIdentIdentShifted(b, a) = 0
            end
        end
    end
end;

function StrCmpTextLit(var text: text_buf; var lit: lit_buf): integer;
var i: integer;
    done: boolean;
begin
  StrCmpTextLit := 0;
  done := false;
  for i := 0 to LIT_LAST do
    begin
      if done = false then
        begin
          if text[i] <> lit[i] then
            begin
              StrCmpTextLit := Ord(text[i]) - Ord(lit[i]);
              done := true
            end
          else if text[i] = #0 then
            begin
              done := true
            end
        end
    end;
  if done = false then
    begin
      if text[LIT_LAST + 1] <> #0 then
        begin
          StrCmpTextLit := Ord(text[LIT_LAST + 1])
        end
    end
end;

function FindAstRoutineByName(var name: text_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstRoutineByName := -1;
  while idx < ast_routine_count do
    begin
      if TextIdentEq(name, ast_routine_name[idx]) then
        begin
          FindAstRoutineByName := idx;
          idx := ast_routine_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function FindAstRoutineByIdent(var name: ident_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstRoutineByIdent := -1;
  while idx < ast_routine_count do
    begin
      if IdentEq(ast_routine_name[idx], name) then
        begin
          FindAstRoutineByIdent := idx;
          idx := ast_routine_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

procedure RegisterAstVar(var name: text_buf);
begin
  if not ast_capture_var_names then
    begin
    end
  else if ast_var_count >= MAX_AST_VARS then
    begin
      parse_error_reason := 101;
      FailParse()
    end
  else
    begin
      CopyTextToIdent(name, ast_var_name[ast_var_count]);
      ast_var_type[ast_var_count] := AST_TYPE_UNKNOWN;
      ast_var_type_ref[ast_var_count] := -1;
      ast_var_owner_routine[ast_var_count] := ast_current_routine;
      ast_var_count := ast_var_count + 1
    end
end;

procedure SetRecentAstVarTypes(start_idx: integer; type_code: integer);
var idx: integer;
begin
  idx := start_idx;
  while idx < ast_var_count do
    begin
      ast_var_type[idx] := type_code;
      idx := idx + 1
    end
end;

procedure SetRecentAstVarTypeRefs(start_idx: integer; type_ref: integer);
var idx: integer;
begin
  idx := start_idx;
  while idx < ast_var_count do
    begin
      ast_var_type_ref[idx] := type_ref;
      idx := idx + 1
    end
end;

function FindAstVar(var name: text_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstVar := -1;
  while idx < ast_var_count do
    begin
      if TextIdentEq(name, ast_var_name[idx]) then
        begin
          FindAstVar := idx;
          idx := ast_var_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function IsRoutineLocalVar(idx_value: integer): boolean;
begin
  if idx_value < 0 then
    begin
      IsRoutineLocalVar := false
    end
  else if idx_value >= ast_var_count then
    begin
      IsRoutineLocalVar := false
    end
  else
    begin
      IsRoutineLocalVar := ast_var_owner_routine[idx_value] >= 0
    end
end;

function FindScopedAstVar(var name: text_buf): integer;
var idx: integer;
    limit: integer;
begin
  FindScopedAstVar := -1;
  if ast_current_routine >= 0 then
    begin
      idx := ast_routine_var_start[ast_current_routine];
      limit := ast_var_count;
      while idx < limit do
        begin
          if TextIdentEq(name, ast_var_name[idx]) then
            begin
              FindScopedAstVar := idx;
              idx := limit
            end
          else
            begin
              if name[0] = #0 then
                begin
                  if StrCmpTextIdentTail(name, ast_var_name[idx]) = 0 then
                    begin
                      FindScopedAstVar := idx;
                      idx := limit
                    end
                  else
                    begin
                      idx := idx + 1
                    end
                end
              else
                begin
                  idx := idx + 1
                end
            end
        end
    end;
  if FindScopedAstVar < 0 then
    begin
      idx := 0;
      limit := ast_var_count;
      while idx < limit do
        begin
          if IsRoutineLocalVar(idx) then
            begin
              idx := idx + 1
            end
          else if TextIdentEq(name, ast_var_name[idx]) then
            begin
              FindScopedAstVar := idx;
              idx := limit
            end
          else
            begin
              if name[0] = #0 then
                begin
                  if StrCmpTextIdentTail(name, ast_var_name[idx]) = 0 then
                    begin
                      FindScopedAstVar := idx;
                      idx := limit
                    end
                  else
                    begin
                      idx := idx + 1
                    end
                end
              else
                begin
                  idx := idx + 1
                end
            end
        end
    end
end;

function FindAstVarByIdent(var name: ident_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstVarByIdent := -1;
  while idx < ast_var_count do
    begin
      if IdentEq(ast_var_name[idx], name) then
        begin
          FindAstVarByIdent := idx;
          idx := ast_var_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function FindAstType(var name: text_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstType := -1;
  while idx < ast_type_count do
    begin
      if TextIdentEq(name, ast_type_name[idx]) then
        begin
          FindAstType := idx;
          idx := ast_type_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function FindAstField(type_idx: integer; var name: text_buf): integer;
var idx: integer;
    limit: integer;
begin
  FindAstField := -1;
  if type_idx < 0 then
    begin
    end
  else
    begin
      idx := ast_type_field_start[type_idx];
      limit := idx + ast_type_field_count[type_idx];
      while idx < limit do
        begin
          if TextIdentEq(name, ast_field_name[idx]) then
            begin
              FindAstField := idx;
              idx := limit
            end
          else
            begin
              idx := idx + 1
            end
        end
    end
end;

function FindAstFieldByIdent(type_idx: integer; var name: ident_buf): integer;
var idx: integer;
    limit: integer;
begin
  FindAstFieldByIdent := -1;
  if type_idx < 0 then
    begin
    end
  else
    begin
      idx := ast_type_field_start[type_idx];
      limit := idx + ast_type_field_count[type_idx];
      while idx < limit do
        begin
          if IdentEq(ast_field_name[idx], name) then
            begin
              FindAstFieldByIdent := idx;
              idx := limit
            end
          else
            begin
              idx := idx + 1
            end
        end
    end
end;

function FindAstEnumConst(var name: text_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstEnumConst := -1;
  while idx < ast_enum_const_count do
    begin
      if TextIdentEq(name, ast_enum_const_name[idx]) then
        begin
          FindAstEnumConst := idx;
          idx := ast_enum_const_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function FindAstEnumConstByIdent(var name: ident_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstEnumConstByIdent := -1;
  while idx < ast_enum_const_count do
    begin
      if IdentEq(ast_enum_const_name[idx], name) then
        begin
          FindAstEnumConstByIdent := idx;
          idx := ast_enum_const_count
        end
      else
        begin
          idx := idx + 1
        end
    end
end;

function AstTypeCellCount(type_code: integer; type_ref: integer): integer;
begin
  AstTypeCellCount := 1;
  if type_code = AST_TYPE_ARRAY then
    begin
      if type_ref >= 0 then
        begin
          if ast_type_array_size[type_ref] > 0 then
            begin
              AstTypeCellCount := ast_type_array_size[type_ref]
            end
        end
    end
  else if type_code = AST_TYPE_RECORD then
    begin
      if type_ref >= 0 then
        begin
          if ast_type_field_count[type_ref] > 0 then
            begin
              AstTypeCellCount := ast_type_field_count[type_ref]
            end
        end
    end
end;

function NewAstType(var name: text_buf; kind: integer): integer;
var idx: integer;
begin
  if ast_type_count >= MAX_AST_TYPES then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 102;
      FailParse()
    end;
  idx := ast_type_count;
  ast_type_count := ast_type_count + 1;
  CopyTextToIdent(name, ast_type_name[idx]);
  ast_type_kind[idx] := kind;
  ast_type_elem_type[idx] := AST_TYPE_UNKNOWN;
  ast_type_elem_type_ref[idx] := -1;
  ast_type_array_low[idx] := 0;
  ast_type_array_high[idx] := 0;
  ast_type_array_len[idx] := 0;
  ast_type_array_size[idx] := 0;
  ast_type_field_start[idx] := ast_field_count;
  ast_type_field_count[idx] := 0;
  NewAstType := idx
end;

procedure AppendAstEnumConst(type_idx: integer; var name: text_buf; value: integer);
var idx: integer;
begin
  if ast_enum_const_count >= MAX_AST_ENUM_CONSTS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 110;
      FailParse()
    end;
  idx := ast_enum_const_count;
  ast_enum_const_count := ast_enum_const_count + 1;
  CopyTextToIdent(name, ast_enum_const_name[idx]);
  ast_enum_const_value[idx] := value;
  ast_enum_const_type_ref[idx] := type_idx
end;

procedure AppendAstField(type_idx: integer; var name: text_buf; field_type: integer);
var idx: integer;
begin
  if ast_field_count >= MAX_AST_FIELDS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 103;
      FailParse()
    end;
  idx := ast_field_count;
  ast_field_count := ast_field_count + 1;
  CopyTextToIdent(name, ast_field_name[idx]);
  ast_field_type[idx] := field_type;
  ast_field_offset[idx] := ast_type_field_count[type_idx] * 4;
  ast_type_field_count[type_idx] := ast_type_field_count[type_idx] + 1
end;

function NewAstStmt(kind: integer): integer;
var idx: integer;
begin
  if ast_stmt_count >= MAX_AST_STMTS then
    begin
      parse_error_reason := 104;
      FailParse()
    end;
  idx := ast_stmt_count;
  ast_stmt_count := ast_stmt_count + 1;
  ast_stmt_kind[idx] := kind;
  ClearIdent(ast_stmt_name[idx]);
  ast_stmt_value_kind[idx] := AST_ARG_NONE;
  ast_stmt_value_int[idx] := 0;
  ast_stmt_value_text_ref[idx] := -1;
  ast_stmt_arg_start[idx] := ast_arg_count;
  ast_stmt_arg_count[idx] := 0;
  ast_stmt_expr[idx] := -1;
  ast_stmt_aux_expr[idx] := -1;
  ast_stmt_child_start[idx] := 0;
  ast_stmt_child_count[idx] := 0;
  ast_stmt_else_start[idx] := 0;
  ast_stmt_else_count[idx] := 0;
  NewAstStmt := idx
end;

function NewAstExpr(kind: integer): integer;
var idx: integer;
begin
  if ast_expr_count >= MAX_AST_EXPRS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 105;
      FailParse()
    end;
  idx := ast_expr_count;
  ast_expr_count := ast_expr_count + 1;
  ast_expr_kind[idx] := kind;
  ast_expr_int[idx] := 0;
  ast_expr_text_ref[idx] := -1;
  ast_expr_op[idx] := TOK_EOF;
  ast_expr_left[idx] := -1;
  ast_expr_right[idx] := -1;
  NewAstExpr := idx
end;

procedure AppendAstArg(stmt_idx: integer; kind: integer; value: integer; var text: text_buf);
var idx: integer;
begin
  if ast_arg_count >= MAX_AST_ARGS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 106;
      FailParse()
    end;
  idx := ast_arg_count;
  ast_arg_count := ast_arg_count + 1;
  ast_arg_kind[idx] := kind;
  ast_arg_int[idx] := value;
  if kind = AST_ARG_TEXT then
    begin
      ast_arg_text_ref[idx] := NewAstTextLit(text)
    end
  else
    begin
      ast_arg_text_ref[idx] := -1
    end;
  ast_arg_expr[idx] := -1;
  if ast_stmt_arg_count[stmt_idx] = 0 then
    begin
      ast_stmt_arg_start[stmt_idx] := idx
    end;
  ast_stmt_arg_count[stmt_idx] := ast_stmt_arg_count[stmt_idx] + 1
end;

procedure AppendAstExprArg(stmt_idx: integer; expr_idx: integer);
var temp_text: text_buf;
    idx: integer;
begin
  ClearText(temp_text);
  if ast_arg_count >= MAX_AST_ARGS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 106;
      FailParse()
    end;
  idx := ast_arg_count;
  ast_arg_count := ast_arg_count + 1;
  ast_arg_kind[idx] := AST_ARG_EXPR;
  ast_arg_int[idx] := 0;
  ast_arg_text_ref[idx] := -1;
  ast_arg_expr[idx] := expr_idx;
  if ast_stmt_arg_count[stmt_idx] = 0 then
    begin
      ast_stmt_arg_start[stmt_idx] := idx
    end;
  ast_stmt_arg_count[stmt_idx] := ast_stmt_arg_count[stmt_idx] + 1
end;

procedure AppendAstCallExprArg(call_expr_idx: integer; arg_expr_idx: integer);
var temp_text: text_buf;
    idx: integer;
begin
  ClearText(temp_text);
  if ast_arg_count >= MAX_AST_ARGS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 106;
      FailParse()
    end;
  idx := ast_arg_count;
  ast_arg_count := ast_arg_count + 1;
  ast_arg_kind[idx] := AST_ARG_EXPR;
  ast_arg_int[idx] := 0;
  ast_arg_text_ref[idx] := -1;
  ast_arg_expr[idx] := arg_expr_idx;
  ast_expr_right[call_expr_idx] := ast_expr_right[call_expr_idx] + 1
end;

function NewAstRoutine(var name: text_buf; kind: integer): integer;
var idx: integer;
begin
  if ast_routine_count >= MAX_AST_ROUTINES then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 107;
      FailParse()
    end;
  idx := ast_routine_count;
  ast_routine_count := ast_routine_count + 1;
  CopyTextToIdent(name, ast_routine_name[idx]);
  ast_routine_kind[idx] := kind;
  ast_routine_param_start[idx] := ast_param_count;
  ast_routine_param_count[idx] := 0;
  ast_routine_stmt_start[idx] := 0;
  ast_routine_stmt_count[idx] := 0;
  ast_routine_var_start[idx] := ast_var_count;
  ast_routine_var_count[idx] := 0;
  ast_routine_ret_type[idx] := AST_TYPE_UNKNOWN;
  NewAstRoutine := idx
end;

procedure AppendAstParam(routine_idx: integer; var name: text_buf; type_code: integer; by_ref: boolean);
var idx: integer;
begin
  if ast_param_count >= MAX_AST_PARAMS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 108;
      FailParse()
    end;
  idx := ast_param_count;
  ast_param_count := ast_param_count + 1;
  CopyTextToIdent(name, ast_param_name[idx]);
  ast_param_type[idx] := type_code;
  ast_param_type_ref[idx] := -1;
  ast_param_hidden[idx] := 0;
  ast_param_conformant_bound_start[idx] := -1;
  ast_param_conformant_dim_count[idx] := 0;
  if by_ref then
    begin
      ast_param_by_ref[idx] := 1
    end
  else
    begin
      ast_param_by_ref[idx] := 0
    end;
  ast_routine_param_count[routine_idx] := ast_routine_param_count[routine_idx] + 1
end;

function NewAstTextLit(var text: text_buf): integer;
var idx: integer;
    found: boolean;
begin
  found := false;
  idx := 0;
  while idx < ast_text_lit_count do
    begin
      if StrCmpTextLit(text, ast_text_lit[idx]) = 0 then
        begin
          NewAstTextLit := idx;
          found := true;
          idx := ast_text_lit_count
        end
      else
        begin
          idx := idx + 1
        end
    end;
  if not found then
    begin
      if ast_text_lit_count >= MAX_AST_TEXT_LITS then
        begin
          bootstrap_capture_failed := true;
          parse_error_reason := 109;
          FailParse()
        end;
      idx := ast_text_lit_count;
      ast_text_lit_count := ast_text_lit_count + 1;
      CopyTextToLit(text, ast_text_lit[idx]);
      NewAstTextLit := idx
    end
end;

function NewAstIdent(var text: text_buf): integer;
var idx: integer;
begin
  if ast_ident_count >= MAX_AST_IDENTS then
    begin
      bootstrap_capture_failed := true;
      parse_error_reason := 110;
      FailParse()
    end;
  idx := ast_ident_count;
  ast_ident_count := ast_ident_count + 1;
  CopyTextToIdent(text, ast_ident_pool[idx]);
  NewAstIdent := idx
end;

procedure InitCompilerState;
begin
  stream_current_char := #0;
  stream_has_char := false;
  stream_eof := false;
  stream_remaining := 0;
  source_next_code := 0;
  source_buffered_char := #0;
  source_has_buffered_char := false;
  token_kind := TOK_EOF;
  token_value := 0;
  saw_probe_read_prefix := false;
  saw_probe_builtin_prefix := false;
  saw_probe_step_proc := false;
  saw_seed_char_decl := false;
  saw_seed_char_assign := false;
  saw_seed_char_writeln := false;
  bootstrap_has_non_writeln_stmt := false;
  bootstrap_capture_failed := false;
  parse_error_reason := 0;
  parse_error_stmt_idx := -1;
  parse_error_routine_idx := -1;
  captured_writeln_count := 0;
  ast_capture_enabled := true;
  ast_capture_var_names := false;
  ast_with_var := -1;
  ast_with_type_ref := -1;
  ast_var_count := 0;
  while ast_var_count <= MAX_AST_VARS - 1 do
    begin
      ast_var_owner_routine[ast_var_count] := -1;
      ast_var_count := ast_var_count + 1
    end;
  ast_var_count := 0;
  ast_type_count := 0;
  while ast_type_count <= MAX_AST_TYPES - 1 do
    begin
      ast_type_elem_type_ref[ast_type_count] := -1;
      ast_type_array_low[ast_type_count] := 0;
      ast_type_array_high[ast_type_count] := 0;
      ast_type_array_len[ast_type_count] := 0;
      ast_type_array_size[ast_type_count] := 0;
      ast_type_count := ast_type_count + 1
    end;
  ast_type_count := 0;
  ast_field_count := 0;
  ast_enum_const_count := 0;
  ast_root_stmt_start := 0;
  ast_root_stmt_count := 0;
  ast_stmt_count := 0;
  ast_arg_count := 0;
  ast_expr_count := 0;
  ast_routine_count := 0;
  ast_param_count := 0;
  while ast_param_count <= MAX_AST_PARAMS - 1 do
    begin
      ast_param_hidden[ast_param_count] := 0;
      ast_param_conformant_bound_start[ast_param_count] := -1;
      ast_param_conformant_dim_count[ast_param_count] := 0;
      ast_param_count := ast_param_count + 1
    end;
  ast_param_count := 0;
  ast_text_lit_count := 0;
  ast_ident_count := 0;
  ast_current_routine := -1;
  ast_emit_routine := -1;
  ClearText(token_text);
  ClearText(program_name)
end;
