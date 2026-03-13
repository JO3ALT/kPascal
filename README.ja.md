# kpascal

[English README](README.md)

Rust で実装した、実用寄りの Pascal → Forth コンパイラ試作です。

Pascal/0 を基礎に、32bit Forth VM 向けの Standard Pascal 寄りコアへ kPascal 独自拡張を統合した実装です。

## 主な機能

- Pascal風文法のパース（`pest`）と意味解析
- 32bit 基本型: `integer`, `boolean`, `char`（UTF-32 code point）
- `TYPE`、`RECORD`、条件レコード、固定長 `ARRAY`（任意次元）
- 多次元 conformant array parameter
- `real`（単精度浮動小数点）、subrange、enum、`set of`
- 同型 `record/array` の一括代入
- 制御構文: `if`, `case`, `while`, `repeat`, `for`
- `with`、ポインタ、`new`、`dispose`、`nil`
- 手続き/関数、値引数と `var` 参照引数
- `(* $I ファイル名 *)` インクルード（Turbo Pascal v3 風）
- 組み込み: `Read`, `ReadLn`, `Write`, `WriteLn`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `UpCase`, `IntToHex`, `HexToInt`, `Addr`, `SetAddr`, `Ord`, `Chr`, `Length`, `Low`, `High`, `Abs`, `Sqr`, `Round`, `Trunc`, `Succ`, `Pred`, `Odd`
- `math.pas`
- `string_utils.pas` 固定長 `array[...] of char` 向け文字列補助ライブラリ
- Standard Pascal コアへ統合済みの拡張: typed `const`、`imut`、`option of`、`result of`、`record of`、`cond(...)`、名前付きコンストラクタ、sum-case destructuring、record update、array update、list/functional 系 builtin

## 構成

- `src/ast.rs`: AST定義
- `src/kpascal.pest`: 文法
- `src/main.rs`: コンパイルパイプライン + include前処理
- `src/sema.rs`: 意味解析/型検査
- `src/codegen.rs`: Forthコード生成
- `math.pas`: Pascal数学ライブラリ
- `string_utils.pas`: 固定長文字列向け Pascal 補助ライブラリ
- `tests/`: コンパイラ/実行テスト
- `AVAILABLE_WORDS.txt`: 使用可能Forthワード

## ビルド・テスト

```bash
cargo build
cargo test -q
cargo clippy -- -D warnings
```

実装上の前提条件と統合状況は `STANDARD_PASCAL_PRECONDITIONS.md` に記録しています。

`kforthc` を使うネイティブ end-to-end テスト:

```bash
cargo test --test e2e_kforth -- --nocapture
```

`tests/samples/` 以下のサンプル群を回す回帰テスト:

```bash
cargo test --test sample_regression -- --nocapture
```

標準入力からコンパイル:

```bash
cargo run -q < tests/fixtures/all_features.pas
```

生成コードを kforth で実行（このリポジトリ直下から）:

```bash
(cargo run -q < tests/fixtures/all_features.pas; echo BYE) \
  | cat ../kforth/bootstrap.fth - \
  | ../kforth/build/kforth
```

## 注意

- ISO Pascal 完全互換ではなく、実用サブセット＋拡張です。
- 浮動小数点のソース表記は `real` のみです。旧 `float` 型名や `Float(...)` 関数は受理しません。
- 現在の Standard Pascal 寄りコアには、削除済み補助 I/O 拡張 `ReadArr`、`WriteArr`、`ReadStr`、`WriteStr`、`WriteHex` は含みません。
- 文字列は `array[...] of char` として扱い、独立した `string` 型は持ちません。
- 文字列処理では `array[...] of char` を C 言語風の `#0` 終端文字列として扱います。
- 文字列リテラル代入は `len - 1` 文字まで書き込み、最後に必ず `#0` を入れます。あふれた分はエラーではなく切り捨てです。
- `Write(s)` / `WriteLn(s)`, `Read(s, max_len)`, `Copy`, `Concat`, `Delete`, `Insert`, `Pos`, `HexToInt`, `IntToHex` はすべて `#0` 終端前提で動作します。
- `Copy`, `Concat`, `Insert`, `Pos` は `array[...] of char` だけでなく文字列リテラルも受けられます。
- 一方で `dst := src` のような配列代入は固定長配列の丸ごとコピーであり、`#0` 停止の文字列コピーではありません。
- `Addr(x)` は lvalue の実アドレスを `integer` で返し、`SetAddr(p, addr)` はその生アドレスをポインタ変数へ格納します。これは、その機能を公開しているブランチでのメモリマップド I/O 向け非標準拡張です。
- `SetAddr` は意図的に unsafe です。コンパイラが検査するのは「代入先がポインタ lvalue であること」と「アドレスが整数であること」までで、その値が実際に有効・整列済み・読書き可能・型に適合するアドレスかどうかは検査しません。
- メモリマップド I/O の利用例:
  `var reg: ^integer;`
  `SetAddr(reg, $FFFF0000);`
  `reg^ := 1;`
- `dispose(p)` は現状メモリ解放を行わず、`p` に `nil` を書き戻すだけです。
- 現在のスコープ規則は厳格（シャドー禁止方針）です。
- `enum` に対する `case` は、`else` が無い場合は網羅的である必要があります。
- `math.pas` は `real` ベースの数学関数群（`abs`, `sqrt`, `pow`, `sin`, `cos`, `f_trunc`, `f_round`, `floor`, `ceil`）を提供します。
- `string_utils.pas` は、コンパイラ実装で使う固定長文字列補助として `ClearStr`, `AppendChar`, `AppendStr`, `StrCopy`, `StrEq`, `StrEqLit`, `StrEqIgnoreCase`, `StrEqIgnoreCaseLit`, `HasNameEqIgnoreCase`, `StrCmp`, `StartsWith`, `TrimLeft`, `TrimRight`, `ParseInt` を提供します。
- 固定長バッファでの比較例:
  `name := 'Pascal'; lit := 'Pascal';`
  `WriteLn(StrEqLit(name, lit));`
  `WriteLn(StrEqIgnoreCaseLit(name, lit));`
  `WriteLn(HasNameEqIgnoreCase(name, lit));`
- セルフホスティング初期版という前提なら、現行の言語機能は概ね足りています。前提は 1 プロセス・stdin/stdout・固定長バッファ設計です。引き続き意図的に未実装なのは主に `forward`、本当の `dispose` 解放、Pascal の file I/O です。
- テストはコンパイラ単体、kforth end-to-end、復元した Standard Pascal sample regression を含めて `main` で通る状態です。
- セルフホスティング系では、外部プリプロセッサ `prekpascal` で `selfhost/kpsc_main.pas` を単一ソース化した経路も検証済みです。前処理済み `kpsc_main` は、少なくとも sample 群の `01_hello` から `20_scalar_builtins` までを direct にコンパイルできることを確認しています。

## ライセンス

MIT License（`LICENSE` を参照）。
