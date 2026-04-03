# Selfhost AST Builder Ordering Notes

## Goal

`src/main.rs` の `build_stmt` / `build_expr` / `build_lvalue` / `build_type_spec` を、`selfhost/` 側でも処理単位ベースで 1:1 に保ちながら実装する。

このメモの目的は、`forward` なしで Pascal 側に並べるために、
- どこが自己再帰か
- どこが相互再帰か
- どの順序で置けばよいか

を整理すること。

## Rust Side Entry Points

対象の主な Rust 側関数:
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L328) `build_type_spec`
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L575) `build_stmt_list`
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L583) `build_stmt`
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L752) `build_expr_list`
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L760) `build_lvalue`
- [src/main.rs](/home/kamitani/kpascal/src/main.rs#L788) `build_expr`

## Dependency Cutout

### `build_stmt_list`

Rust:
- `build_stmt_list -> build_stmt`

性質:
- 自己再帰なし
- `build_stmt` への片方向依存

Pascal 側:
- 単独 helper に切り出せる
- ただし `build_stmt` より前に置くなら、`build_stmt_list` 自体は `build_stmt` を呼べない
- したがって Pascal 側では `StmtList` を独立 helper にするより、`BuildStmt` 内の局所ループへ寄せる方が安全

### `build_stmt`

Rust での依存:
- `build_stmt -> build_compound`
- `build_stmt -> build_lvalue`
- `build_stmt -> build_expr`
- `build_stmt -> build_expr_list`
- `build_stmt -> build_case_label_list`
- `build_stmt -> build_stmt`（`for/if/case/sum_case/with/while` の body）
- `build_stmt -> build_stmt_list`（`repeat` の body）

性質:
- 強い自己再帰あり
- `build_expr` と相互依存ではない
- `build_stmt_list` を別 helper にすると `build_stmt <-> build_stmt_list` の循環が増える

Pascal 側の含意:
- `BuildStmt` は中核の自己再帰 routine に寄せる
- `BuildStmtList` を別の public helper にするより、`compound` / `repeat` 用のローカルな末尾処理へ畳み込む方が並べやすい
- `build_compound` も別 routine にすると依存順が増えるので、可能なら `BuildStmt` の `compound_stmt` 分岐に内包する

### `build_expr_list`

Rust:
- `build_expr_list -> build_expr`

性質:
- 自己再帰なし
- `build_expr` にだけ依存

Pascal 側:
- `BuildExpr` の後に置けばそのまま実装可能
- ただし `build_stmt` からも使うので、Pascal では `BuildExprList` を `BuildStmt` より前に置く必要がある

### `build_lvalue`

Rust:
- `build_lvalue -> build_expr`（添字 selector の中）

性質:
- 自己再帰なし
- `build_expr` に依存

Pascal 側:
- `BuildExpr` の後に置く
- `BuildStmt` より前に置く
- これで `assign_stmt` / `with_stmt` の構築が一方向依存になる

### `build_expr`

Rust での依存:
- `build_expr -> build_expr`（`rel/add/mul/unary` で自己再帰）
- `build_expr -> build_typeref`（cast）
- `build_expr -> build_cond_expr`
- `build_expr -> build_expr_list`
- `build_expr -> build_set_items`
- `build_expr -> build_lvalue`

補助側の依存:
- `build_set_items -> build_expr`
- `build_cond_expr -> build_expr`
- `build_cond_expr -> build_cond_block`
- `build_cond_block -> build_stmt`
- `build_cond_block -> build_expr`

性質:
- `build_expr` 単体は自己再帰で閉じる
- ただし `cond_expr` を入れると `build_expr -> build_cond_expr -> build_cond_block -> build_stmt -> build_expr` となり、`Stmt` 系との大きな循環を作る
- `lvalue in expr context` により `build_expr -> build_lvalue -> build_expr` の循環もある

Pascal 側の含意:
- `cond_expr` を含めた完全一致は、`BuildExpr` と `BuildStmt` の相互再帰を前提に整理する必要がある
- 最初の stage2 では `cond_expr` を後回しにするのが安全
- `lvalue` を expr 文脈で使う処理は、`BuildLValueFromExprSuffix` のような共通 selector reader に切ると依存を減らせる

### `build_type_spec`

Rust での依存:
- `build_type_spec -> build_typeref`
- `build_type_spec -> build_type_spec` 相当の入れ子は薄いが、record/array/variant/subrange で補助 builder を多く呼ぶ
- `build_type_spec` 自体は `build_stmt` / `build_expr` 系とは独立

Pascal 側:
- `TypeSpec` 系は `Stmt` / `Expr` より前でも後でもよい
- 宣言部でのみ使うので、`BuildBlock` の前にまとまっていれば十分

## Recursion Classification

### 自己再帰だけで閉じるもの
- `build_stmt`
- `build_expr`

### 補助を挟んで自己再帰へ戻るもの
- `build_stmt -> build_stmt_list -> build_stmt`
- `build_expr -> build_set_items -> build_expr`

### `Stmt` と `Expr` の相互再帰を作るもの
- `build_stmt -> build_expr`
- `build_expr -> build_cond_expr -> build_cond_block -> build_stmt`
- `build_expr -> build_lvalue -> build_expr`

## Pascal Side Ordering Strategy

### 最小循環で進める段階

#### Phase 1
対象:
- `assign`
- `write` / `writeln`
- `if`
- `while`
- `repeat`
- `for`
- `compound`
- 基本式
- field/index/deref 付き lvalue

この段階では後回しにするもの:
- `cond_expr`
- `sum_case`
- `case` の完全 AST 化
- `proc_call` の完全 AST 化
- `with`
- `record_update` / `array_update` / `ctor` の完全 AST 化

理由:
- Rust と 1:1 で寄せるべき優先部分は main statement builders
- `cond_expr` を先に入れると `Stmt`/`Expr` 相互再帰が重くなる

### Pascal での推奨配置順

#### 1. Expr leaf helpers
- `IsUnaryToken`
- `IsMulOpToken`
- `IsAddOpToken`
- `IsRelOpToken`
- literal / selector 判定
- selector 読み取りの共通 helper

#### 2. Expr core
- `BuildExpr`
- その内部で `rel/add/mul/unary/primary` を分岐処理
- 可能なら public helper を増やさず、`BuildExpr` 本体か private tail helper に寄せる

狙い:
- `BuildExprList` より前に自己完結させる

#### 3. Expr-adjacent helpers
- `BuildExprList`
- `BuildLValue`
- `BuildCaseLabelList` など

#### 4. Stmt core
- `BuildStmt`
- `compound` / `repeat` の stmt-list 走査は `BuildStmt` 内のループとして持つ
- `BuildStmtList` を別 top-level routine にしない

#### 5. Decl / block layer
- `BuildTypeSpec`
- `BuildBlock`
- `BuildProgram`

## Practical Rule For `forward`-Free Pascal

Pascal 側では次のルールで分解すると安全。

- rule 1: `BuildStmtList` は独立 public routine にしない
- rule 2: `BuildCompoundStmt` も独立 routine にせず、`BuildStmt` 分岐へ寄せる
- rule 3: `BuildExpr` は public entry を 1 つに絞り、`rel/add/mul/unary/primary` は tail helper か本体内分岐で処理する
- rule 4: `BuildCondExpr` は別フェーズに送る
- rule 5: `BuildLValue` は `BuildExpr` 後、`BuildStmt` 前に置く

## Direct Mapping Table

### Rust `build_stmt` arm to Pascal target

- `compound_stmt`: `BuildStmt` 内で `begin ... end` を直接処理
- `assign_stmt`: `BuildLValue` + `BuildExpr`
- `read_stmt`: phase 2
- `readln_stmt`: phase 2
- `for_stmt`: `BuildExpr` + `BuildStmt`
- `case_stmt`: phase 2 or AST fallback
- `sum_case_stmt`: phase 3
- `proc_call_stmt`: phase 2
- `if_stmt`: `BuildExpr` + `BuildStmt` (+ optional else `BuildStmt`)
- `with_stmt`: phase 2
- `while_stmt`: `BuildExpr` + `BuildStmt`
- `repeat_stmt`: `BuildStmt` loop + `BuildExpr`
- `write_stmt`: `BuildExprList`
- `writeln_stmt`: `BuildExprList`
- `empty_stmt`: direct

### Rust `build_expr` arm to Pascal target

- `rel/add/mul/unary`: phase 1 core
- `bool_lit/nil/number/string/char_code`: phase 1 core
- `func_call`: phase 2
- `set_lit`: phase 2
- `array_lit`: phase 2
- `record_update/array_update`: phase 3
- `cast_expr`: phase 2
- `cond_expr`: separate phase because it re-enters `BuildStmt`
- `lvalue`: phase 1 via `BuildLValue` and selector lowering

## Recommended Next Implementation Slice

最初に合わせる対象は以下。
- `build_expr` の phase 1 subset
- `build_lvalue`
- `build_stmt` の `compound/assign/if/while/repeat/for/write/writeln/empty`

この集合なら、Rust 側の主制御構文をかなりカバーしつつ、`cond_expr` と `case` を後回しにできる。

## Main Risk

最大のリスクは「Rust と同じ関数名で Pascal に分けた結果、依存順だけ Pascal で破綻する」こと。

したがって実装時は、関数境界の一致よりも優先順位を次のように置く。
- 1. Rust と同じ処理順
- 2. Rust と同じデータ流れ
- 3. Pascal 側で合法な宣言順
- 4. その上で可能な範囲で関数境界も近づける

この順なら repository policy と矛盾しない。
