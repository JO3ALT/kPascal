const
  MAX_SOURCE_LEN = 4096;
  MAX_TOKEN_LEN = 127;
  TOK_EOF = 0;
  TOK_IDENT = 1;
  TOK_INT = 2;
  TOK_STR = 3;
  TOK_SYMBOL = 4;
  TOK_BEGIN = 10;
  TOK_END = 11;
  TOK_PROGRAM = 12;
  TOK_VAR = 13;
  TOK_TYPE = 14;
  TOK_CONST = 15;
  TOK_SEMI = 16;
  EXPR_KIND_INT = 0;
  EXPR_KIND_STR = 1;
  MAX_VARS = 16;

type
  token_buf = array[0..MAX_TOKEN_LEN] of char;
  source_buf = array[0..MAX_SOURCE_LEN] of char;
  expr_buf = array[0..MAX_VARS - 1] of integer;

var
  source_len: integer;
  source_text: source_buf;
  source_pos: integer;
  token_pos: integer;
  current_kind: integer;
  current_text: token_buf;
  current_value: integer;
  var_count: integer;
  var_names: array[0..MAX_VARS - 1, 0..MAX_TOKEN_LEN] of char;
  var_values: expr_buf;
  last_expr_kind: integer;
  enum_values: array[0..MAX_VARS - 1] of integer;
