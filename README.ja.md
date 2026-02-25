# kpascal

[English README](README.md)

Rust で実装した、Rust-friendly な Pascal → Forth コンパイラ試作です。

Pascal/0 を基礎に、Rust からの移植をしやすくする実用拡張を追加した Rust-friendly Pascal として、32bit Forth VM 向けコードを生成します。

## 位置づけ

- 完全な ISO Pascal 実装ではありません。
- 純粋/完全な関数型言語でもありません。
- 目的は Rust-friendly Pascal です。つまり、Forth ターゲット環境へコードを移植しやすいように、制御構文・データ配置・明示的な型付けを重視した実用的な Pascal サブセット/拡張を提供します。

## 主な機能

- Pascal風文法のパース（`pest`）と意味解析
- 32bit 基本型: `integer`, `boolean`, `char`, `float`（`float` は IEEE754 binary32 bit pattern）
- `TYPE`、`RECORD`、固定長 `ARRAY`（1〜3次元）
- `enum` 型（`type color = (red, green, blue);`、内部的には序数定数）
- `result of T, E` 型糖衣（`ok(...)` / `err(...)` コンストラクタ）
- 同型 `record/array` の一括代入
- aggregate の copy-update（`p with (x := 1)`, `xs with [i := v]`）
- 制御構文: `if`, `case`, `while`, `repeat`, `for`
- 手続き/関数、値引数と `var` 参照引数
- `(* $I ファイル名 *)` インクルード（Turbo Pascal v3 風）
- 型付き `const`（スカラー）: `const x: integer = 1;`
- 組み込み: `Read`, `ReadLn`, `Write`, `WriteLn`, `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, `WriteHex`, `Ord`, `Chr`, `Length`, `Low`, `High`
- リスト向け関数型風 builtin（list node ABI）: `Map`, `Filter`, `Fold`
- `math.pas`（浮動小数点の算術関数群。`abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil` など）
- `math_fixed.pas`（整数/固定小数近似の算術関数群。`fx_*`）

## 構成

- `src/ast.rs`: AST定義
- `src/kpascal.pest`: 文法
- `src/main.rs`: コンパイルパイプライン + include前処理
- `src/sema.rs`: 意味解析/型検査
- `src/codegen.rs`: Forthコード生成
- `math.pas`: Pascal浮動小数点数学ライブラリ（`abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil`）
- `math_fixed.pas`: Pascal固定小数点数学ライブラリ（`fx_sqrt`, `fx_sin`, `fx_cos`, `fx_tan`, `fx_asin`, `fx_acos`, `fx_atan`, `fx_ln`, `fx_log`）
- `math_float.pas`: `math.pas` を include する後方互換エイリアス（非推奨）
- `tests/`: コンパイラ/実行テスト
- `AVAILABLE_WORDS.txt`: 使用可能Forthワード

## ビルド・テスト

```bash
cargo build
cargo test -q --test e2e_kforth
cargo test -q --test auto_fixture_e2e
scripts/verify_backends.py
```

補足: この環境でまれに出る Rust incremental artifact 破損警告を避けるため、`.cargo/config.toml` で `dev`/`test` の incremental を無効化しています。

`scripts/verify_backends.py` は `tests/fixtures/*.pas` を `kforth` と `kFORTHc(native)` の両方で実行して比較します。
出力完全一致なら `PASS`、差分があっても数学関数の結果が Python オラクルと一致/十分近ければ `PASS` と判定します（native の `libm` 数学パス向け）。
実行には兄弟リポジトリ `../kforth`, `../kFORTHc` と `llc`, `clang` が必要です（native リンク時に `-lm` を使用）。

標準入力からコンパイル:

```bash
cargo run -q < tests/fixtures/all_features.pas
```

生成コードを kforth で実行（このリポジトリ直下から）:

```bash
(cargo run -q < tests/fixtures/all_features.pas; echo BYE) \
  | cat ../kforth/bootstrap.fth - \
  | ( ../kforth/build/kforth 2>/dev/null || ../kforth/kforth )
```

拡張機能の総合サンプル（型付き `const` / `enum` / `imut` / `option` / `cond` / sum `case`）:

```bash
cargo run -q < tests/fixtures/extensions_showcase_annotated.pas
```

このファイルには、意図的なコンパイルエラー例（`enum` と `integer` の不一致、`imut` 再代入）もコメントとして併記しています。

期待出力（正規化後）:

```text
42
TRUE
!
1
GREEN
100
42
15
EXT
```

`result` / copy-update / 実用的な制御フロー置換のサンプル:

```bash
cargo run -q < tests/fixtures/functional_ops_result_demo.pas
```

`list.pas` + `Map` / `Filter` / `Fold` のサンプル:

```bash
cargo run -q < tests/fixtures/list_pipeline_demo.pas
```

## 注意

- ISO Pascal 完全互換ではなく、実用サブセット＋拡張です。
- 現在のスコープ規則は厳格（シャドー禁止方針）です。
- `math_fixed.pas` の三角/対数系は近似計算です。
- `float` 値は IEEE754 binary32 のビット列として生成され、kforth の `FADD` / `FDIV` / `F.` などを使って実行されます。
- 明示的な数値変換 builtin を追加: `Float(integer) -> float`, `Trunc(float) -> integer`, `Round(float) -> integer`
- named record constructor を代入/初期化文脈で使用可能: `p := point(x := 1; y := 2.5)`
- 配列リテラルを代入/初期化文脈で使用可能（左辺の配列型で長さ・要素型を検査）: `xs := [1, 2, 3]`
- `result of T, E` は名義的 sum 型の糖衣として利用可能（`ok(...)` / `err(...)`）
- `enum` に対する `case` は、`else` が無い場合は網羅的である必要があります
- aggregate の copy-update を利用可能: `p2 := p with (y := 99)`, `ys := xs with [1 := 20]`
- `Map` / `Filter` / `Fold` は list node ABI（`next` が先頭、`value` が後続 payload）のリスト builtin です
- `Map(xs, f)` の callback: `procedure(var src: T; var dst: T)`
- `Filter(xs, pred)` の callback: `function(var v: T): boolean`
- `Fold(xs, init, f)` の callback: `function(acc: integer; var v: T): integer`

## ライセンス

MIT License（`LICENSE` を参照）。
