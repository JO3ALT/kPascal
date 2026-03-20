# codex_parser_reference_min.md

目的: `expanded.rs` 全体を Codex に渡さず、Pascal 手書き再帰下降パーサ移植に必要な最小参照だけを渡す。

## このファイルの使い方

Codex には毎回このファイル全体と、今回対象の Pascal 側ファイル断片だけを渡す。  
`expanded.rs` 全量は渡さない。  
1 セッションで扱う対象は **1規則、多くても2規則まで** とする。

---

## 1. 参照対象として残すべき情報

`expanded.rs` から見るべき本質は次の4群だけである。

### A. AST 形
最低限、以下の型の形だけ参照する。

- `Program { name, block }`
- `Block { consts, types, vars, routines, body }`
- `RoutineDecl = Procedure | Function`
- `TypeSpec`
- `TypeRef`
- `Stmt`
- `Expr`
- `ConstExpr`
- `LValue`
- `Selector`
- `BinOp`
- `UnOp`

### B. 規則の列構造
pest 展開コードでは、各規則は `sequence / optional / repeat / or_else` に分解されている。  
Pascal 側ではこれをそのまま一般化せず、**個別の手書き再帰下降**に落とす。

対応は次の通り。

- `sequence(A, B, C)` → `ParseA; ParseB; ParseC;`
- `optional(X)` → `if CanStartX then ParseX;`
- `repeat(X)` → `while CanStartX do ParseX;`
- `or_else(A, B, C)` → `case` / `if` による分岐

### C. stmt の分岐順
`expanded.rs` 上の `stmt` は次の順で分岐している。

1. `compound_stmt`
2. `assign_stmt`
3. `read_stmt`
4. `readln_stmt`
5. `for_stmt`
6. `write_stmt`
7. `writeln_stmt`
8. `sum_case_stmt`
9. `case_stmt`
10. `proc_call_stmt`
11. `if_stmt`
12. `with_stmt`
13. `while_stmt`
14. `repeat_stmt`
15. `empty_stmt`

Pascal 側でも **statement 判定の優先順** としてこの順を参考にする。

### D. section / decl の列構造
確認できる範囲では、以下の規則は典型的な列である。

- `const_decl = ident [ ":" type_ref_or_basic ] "=" const_expr ";"`
- `type_section = "type" type_decl { type_decl }`
- `type_decl = ident "=" type_spec ";"`

Pascal 側ではこのまま手書きでよい。

---

## 2. AST 最小要約

### Program / Block

```text
Program
  - name: String
  - block: Block

Block
  - consts: Vec<ConstDecl>
  - types: Vec<TypeDecl>
  - vars: Vec<VarDecl>
  - routines: Vec<RoutineDecl>
  - body: Stmt
```

### RoutineDecl

```text
RoutineDecl
  - Procedure(ProcedureDecl)
  - Function(FunctionDecl)

ProcedureDecl
  - name
  - params
  - block

FunctionDecl
  - name
  - params
  - ret_ty
  - block
```

### TypeSpec

```text
TypeSpec
  - Basic(BasicType)
  - Enum(Vec<String>)
  - Record { fields, variant }
  - SumRecord(Vec<SumArmDecl>)
  - Array { dims, elem }
  - Subrange { low, high }
  - Set(TypeRef)
  - Alias(TypeRef)
```

### TypeRef

```text
TypeRef
  - Basic(BasicType)
  - Named(String)
  - PointerNamed(String)
  - Option(TypeRef)
  - Result(TypeRef, TypeRef)
  - Array { dims, elem }
  - Subrange { low, high }
  - Set(TypeRef)
```

### Stmt

```text
Stmt
  - Empty
  - Compound(Vec<Stmt>)
  - Assign(LValue, Expr)
  - Read(Vec<Expr>)
  - ReadLn
  - For { var, init, limit, downto, body }
  - If(cond, then_stmt, else_stmt)
  - With(Vec<LValue>, body)
  - While(cond, body)
  - Repeat(Vec<Stmt>, until_expr)
  - Case { expr, arms, else_stmt }
  - SumCase { expr, arms, else_stmt }
  - ProcCall(name, args)
  - Write(Vec<Expr>)
  - WriteLn(Vec<Expr>)
```

### Expr

```text
Expr
  - Int / Bool / Char / Real / Str
  - SetLit(Vec<SetItem>)
  - Nil
  - Var(String)
  - Call(String, Vec<Expr>)
  - Ctor(String, Vec<(String, Expr)>)
  - ArrayLit(Vec<Expr>)
  - RecordUpdate(Box<Expr>, Vec<(String, Expr)>)
  - ArrayUpdate(Box<Expr>, Vec<(Expr, Expr)>)
  - OptionNone
  - OptionSome(Box<Expr>)
  - Cond { arms, else_block }
  - Deref(Box<Expr>)
  - Field(Box<Expr>, String)
  - Index(Box<Expr>, Box<Expr>)
  - Cast(TypeRef, Box<Expr>)
  - Unary(UnOp, Box<Expr>)
  - Binary(Box<Expr>, BinOp, Box<Expr>)
```

### LValue / Selector

```text
LValue
  - base: String
  - sels: Vec<Selector>

Selector
  - Field(String)
  - Index(Vec<Expr>)
  - Deref
```

### 演算子

```text
UnOp = Neg | Not

BinOp =
  Add | Sub | Mul | RealDiv | Div | Mod |
  And | Or | Xor | In |
  Eq | Ne | Lt | Le | Gt | Ge
```

---

## 3. Pascal 側で固定すべき実装原則

### 原則1
pest の内部表現は移植しない。  
移植するのは **受理言語** と **AST 形** のみ。

### 原則2
式は通常規則と分離し、**precedence climbing** で実装する。

### 原則3
statement は `ParseStatement` 一箇所で分岐し、必要なら `ParseAssignOrCall` を分ける。

### 原則4
`expanded.rs` の全文をコンテキストに入れない。  
必要な規則断片だけ引用する。

### 原則5
Pascal の独自拡張は標準 Pascal に正規化しない。

---

## 4. まず実装・修正すべき単位

優先順位は次の通り。

1. `ParsePrimary`
2. `ParseExpr`
3. `ParseAssignOrCall`
4. `ParseStatement`
5. `ParseStmtList`
6. `ParseCompoundStmt`
7. `ParseConstDecl`
8. `ParseTypeDecl`
9. `ParseTypeSpec`
10. `ParseBlock`

---

## 5. 規則ごとの変換テンプレート

### stmt

`expanded.rs` の `stmt` は `or_else` 連鎖である。  
Pascal 側では次のように書く。

```pascal
function ParseStatement: PAst;
begin
  case Cur.Kind of
    tkBegin:   Result := ParseCompoundStmt;
    tkIf:      Result := ParseIfStmt;
    tkWhile:   Result := ParseWhileStmt;
    tkRepeat:  Result := ParseRepeatStmt;
    tkCase:    Result := ParseCaseStmt;
    tkWith:    Result := ParseWithStmt;
    tkRead:    Result := ParseReadStmt;
    tkReadLn:  Result := ParseReadLnStmt;
    tkWrite:   Result := ParseWriteStmt;
    tkWriteLn: Result := ParseWriteLnStmt;
    tkFor:     Result := ParseForStmt;
    tkIdent:   Result := ParseAssignOrCall;
  else
    Result := MakeEmptyStmt;
  end;
end;
```

### stmt_list

`stmt_list = stmt { ";" stmt } [";"]`

```pascal
function ParseStmtList: PStmtList;
begin
  Result := NewStmtList;
  AddStmt(Result, ParseStatement);
  while Accept(tkSemicolon) do
  begin
    if not IsStatementStart(Cur.Kind) then
      Break;
    AddStmt(Result, ParseStatement);
  end;
end;
```

### const_decl

`ident [ ":" type_ref_or_basic ] "=" const_expr ";"`

```pascal
function ParseConstDecl: PConstDecl;
var
  Name: string;
  Ty: PTypeRef;
  E: PConstExpr;
begin
  Name := ExpectIdent;
  Ty := nil;
  if Accept(tkColon) then
    Ty := ParseTypeRefOrBasic;
  Expect(tkEq);
  E := ParseConstExpr;
  Expect(tkSemicolon);
  Result := MakeConstDecl(Name, Ty, E);
end;
```

### type_decl

`ident "=" type_spec ";"`

```pascal
function ParseTypeDecl: PTypeDecl;
var
  Name: string;
  Spec: PTypeSpec;
begin
  Name := ExpectIdent;
  Expect(tkEq);
  Spec := ParseTypeSpec;
  Expect(tkSemicolon);
  Result := MakeTypeDecl(Name, Spec);
end;
```

### type_section

`"type" type_decl { type_decl }`

```pascal
procedure ParseTypeSection(var Types: PTypeDeclList);
begin
  Expect(tkType);
  AddTypeDecl(Types, ParseTypeDecl);
  while Cur.Kind = tkIdent do
    AddTypeDecl(Types, ParseTypeDecl);
end;
```

---

## 6. Codex に毎回渡す入力の最小セット

毎回渡すのは以下のみ。

1. このファイル
2. 今回対象の Pascal 側ソース断片
3. 対象規則の pest/expand 断片
4. 代表入力 2〜3 個
5. 期待 AST の概形

渡してはいけないもの:

- `expanded.rs` 全文
- AGENT.md 全文
- 過去ログ全文
- 無関係な parser ファイル全体

---

## 7. Codex 指示テンプレート

```text
目的:
Rust+pest の参照実装をもとに、Pascal 手書き再帰下降パーサの対象規則を実装または修正する。

制約:
- pest の一般機構を Pascal に移植しない
- 受理言語と AST 形だけを合わせる
- 標準 Pascal に勝手に正規化しない
- 変更は対象規則周辺だけに限定する
- 説明は短く、コードを優先する

今回の対象規則:
<rule name>

参照:
1. codex_parser_reference_min.md
2. Pascal 側の現行コード断片
3. expanded.rs から抜いた対象規則断片
4. 代表入力
5. 期待AST概要

出力要求:
- 変更後の Pascal コードのみ
- 必要最小限の補助関数のみ
- 無関係な大規模書き換えをしない
```

---

## 8. 今回の expanded.rs から読み取れる最小結論

- AST はかなり豊富だが、パーサ移植で最重要なのは `Stmt`, `Expr`, `TypeSpec`, `TypeRef`, `LValue` の形である。
- `stmt` は `or_else` 連鎖であり、Pascal 側では `case` 分岐に落とすのが自然である。
- `stmt_list` は `stmt { ";" stmt } [";"]` である。
- `const_decl`, `type_decl`, `type_section` は列構造が明瞭で、再帰下降へ直接落とせる。
- よって、全文を参照する必要はない。局所断片だけで十分である。
