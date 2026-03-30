const
  MAX_CAPTURED_WRITELNS = 32;
  MAX_AST_VARS = 64;
  MAX_AST_STMTS = 64;
  MAX_AST_ARGS = 128;
  MAX_AST_EXPRS = 256;
  MAX_AST_TYPES = 64;
  MAX_AST_FIELDS = 256;
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
  AST_TYPE_UNKNOWN = 0;
  AST_TYPE_INTEGER = 1;
  AST_TYPE_BOOLEAN = 2;
  AST_TYPE_CHAR = 3;
  AST_TYPE_REAL = 4;
  AST_TYPE_RECORD = 5;
  AST_TYPE_ARRAY = 6;
  AST_DECL_NONE = 0;
  AST_DECL_RECORD = 1;
  AST_DECL_ARRAY = 2;
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
  captured_writeln_count: integer;
  captured_writeln_kind: array[0..31] of integer;
  captured_writeln_int: array[0..31] of integer;
  captured_writeln_text: array[0..31] of text_buf;
  ast_capture_enabled: boolean;
  ast_capture_var_names: boolean;
  ast_var_count: integer;
  ast_var_name: array[0..63] of text_buf;
  ast_var_type: array[0..63] of integer;
  ast_var_type_ref: array[0..63] of integer;
  ast_type_count: integer;
  ast_type_name: array[0..63] of text_buf;
  ast_type_kind: array[0..63] of integer;
  ast_type_elem_type: array[0..63] of integer;
  ast_type_field_start: array[0..63] of integer;
  ast_type_field_count: array[0..63] of integer;
  ast_field_count: integer;
  ast_field_name: array[0..255] of text_buf;
  ast_field_type: array[0..255] of integer;
  ast_field_offset: array[0..255] of integer;
  ast_root_stmt_start: integer;
  ast_root_stmt_count: integer;
  ast_stmt_count: integer;
  ast_stmt_kind: array[0..63] of integer;
  ast_stmt_name: array[0..63] of text_buf;
  ast_stmt_value_kind: array[0..63] of integer;
  ast_stmt_value_int: array[0..63] of integer;
  ast_stmt_value_text: array[0..63] of text_buf;
  ast_stmt_expr: array[0..63] of integer;
  ast_stmt_aux_expr: array[0..63] of integer;
  ast_stmt_arg_start: array[0..63] of integer;
  ast_stmt_arg_count: array[0..63] of integer;
  ast_stmt_child_start: array[0..63] of integer;
  ast_stmt_child_count: array[0..63] of integer;
  ast_stmt_else_start: array[0..63] of integer;
  ast_stmt_else_count: array[0..63] of integer;
  ast_arg_count: integer;
  ast_arg_kind: array[0..127] of integer;
  ast_arg_int: array[0..127] of integer;
  ast_arg_text: array[0..127] of text_buf;
  ast_arg_expr: array[0..127] of integer;
  ast_expr_count: integer;
  ast_expr_kind: array[0..255] of integer;
  ast_expr_int: array[0..255] of integer;
  ast_expr_text: array[0..255] of text_buf;
  ast_expr_op: array[0..255] of integer;
  ast_expr_left: array[0..255] of integer;
  ast_expr_right: array[0..255] of integer;

procedure RegisterAstVar(var name: text_buf);
begin
  if not ast_capture_var_names then
    begin
    end
  else if ast_var_count >= MAX_AST_VARS then
    begin
      FailParse()
    end
  else
    begin
      StrCopy(name, ast_var_name[ast_var_count]);
      ast_var_type[ast_var_count] := AST_TYPE_UNKNOWN;
      ast_var_type_ref[ast_var_count] := -1;
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
      if StrCmp(ast_var_name[idx], name) = 0 then
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

function FindAstType(var name: text_buf): integer;
var idx: integer;
begin
  idx := 0;
  FindAstType := -1;
  while idx < ast_type_count do
    begin
      if StrCmp(ast_type_name[idx], name) = 0 then
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
          if StrCmp(ast_field_name[idx], name) = 0 then
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

function NewAstType(var name: text_buf; kind: integer): integer;
var idx: integer;
begin
  if ast_type_count >= MAX_AST_TYPES then
    begin
      bootstrap_capture_failed := true;
      FailParse()
    end;
  idx := ast_type_count;
  ast_type_count := ast_type_count + 1;
  StrCopy(name, ast_type_name[idx]);
  ast_type_kind[idx] := kind;
  ast_type_elem_type[idx] := AST_TYPE_UNKNOWN;
  ast_type_field_start[idx] := ast_field_count;
  ast_type_field_count[idx] := 0;
  NewAstType := idx
end;

procedure AppendAstField(type_idx: integer; var name: text_buf; field_type: integer);
var idx: integer;
begin
  if ast_field_count >= MAX_AST_FIELDS then
    begin
      bootstrap_capture_failed := true;
      FailParse()
    end;
  idx := ast_field_count;
  ast_field_count := ast_field_count + 1;
  StrCopy(name, ast_field_name[idx]);
  ast_field_type[idx] := field_type;
  ast_field_offset[idx] := ast_type_field_count[type_idx] * 4;
  ast_type_field_count[type_idx] := ast_type_field_count[type_idx] + 1
end;

function NewAstStmt(kind: integer): integer;
var idx: integer;
begin
  if ast_stmt_count >= MAX_AST_STMTS then
    begin
      FailParse()
    end;
  idx := ast_stmt_count;
  ast_stmt_count := ast_stmt_count + 1;
  ast_stmt_kind[idx] := kind;
  ClearText(ast_stmt_name[idx]);
  ast_stmt_value_kind[idx] := AST_ARG_NONE;
  ast_stmt_value_int[idx] := 0;
  ClearText(ast_stmt_value_text[idx]);
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
      FailParse()
    end;
  idx := ast_expr_count;
  ast_expr_count := ast_expr_count + 1;
  ast_expr_kind[idx] := kind;
  ast_expr_int[idx] := 0;
  ClearText(ast_expr_text[idx]);
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
      FailParse()
    end;
  idx := ast_arg_count;
  ast_arg_count := ast_arg_count + 1;
  ast_arg_kind[idx] := kind;
  ast_arg_int[idx] := value;
  StrCopy(text, ast_arg_text[idx]);
  ast_arg_expr[idx] := -1;
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
      FailParse()
    end;
  idx := ast_arg_count;
  ast_arg_count := ast_arg_count + 1;
  ast_arg_kind[idx] := AST_ARG_EXPR;
  ast_arg_int[idx] := 0;
  StrCopy(temp_text, ast_arg_text[idx]);
  ast_arg_expr[idx] := expr_idx;
  ast_stmt_arg_count[stmt_idx] := ast_stmt_arg_count[stmt_idx] + 1
end;

procedure InitCompilerState;
begin
  stream_current_char := #0;
  stream_has_char := false;
  stream_eof := false;
  stream_remaining := 0;
  source_next_code := 0;
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
  captured_writeln_count := 0;
  ast_capture_enabled := true;
  ast_capture_var_names := false;
  ast_var_count := 0;
  ast_type_count := 0;
  ast_field_count := 0;
  ast_root_stmt_start := 0;
  ast_root_stmt_count := 0;
  ast_stmt_count := 0;
  ast_arg_count := 0;
  ast_expr_count := 0;
  ClearText(token_text);
  ClearText(program_name)
end;
