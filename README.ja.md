# kpascal

[English README](README.md)

Rust で実装した、実用寄りの Pascal → Forth コンパイラ試作です。

Pascal/0 を基礎に、`TYPE`、`RECORD`、配列（最大3次元）、ネストした手続き/関数、型付きI/Oを追加し、32bit Forth VM 向け中間コードを生成します。

## 主な機能

- Pascal風文法のパース（`pest`）と意味解析
- 32bit 基本型: `integer`, `boolean`, `char`（UTF-32 code point）
- `TYPE`、`RECORD`、固定長 `ARRAY`（1〜3次元）
- 同型 `record/array` の一括代入
- 制御構文: `if`, `case`, `while`, `repeat`, `for`
- 手続き/関数、値引数と `var` 参照引数
- `(* $I ファイル名 *)` インクルード（Turbo Pascal v3 風）
- 組み込み: `Read`, `ReadLn`, `Write`, `WriteLn`, `ReadArr`, `WriteArr`, `ReadStr`, `WriteStr`, `WriteHex`, `Ord`, `Chr`, `Length`, `Low`, `High`
- `math.pas`（整数/固定小数近似の算術関数群）

## 構成

- `src/ast.rs`: AST定義
- `src/kpascal.pest`: 文法
- `src/main.rs`: コンパイルパイプライン + include前処理
- `src/sema.rs`: 意味解析/型検査
- `src/codegen.rs`: Forthコード生成
- `math.pas`: Pascal数学ライブラリ
- `tests/`: コンパイラ/実行テスト
- `AVAILABLE_WORDS.txt`: 使用可能Forthワード

## ビルド・テスト

```bash
cargo build
cargo test -q
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
- 現在のスコープ規則は厳格（シャドー禁止方針）です。
- `math.pas` の三角/対数系は近似計算です。

## ライセンス

MIT License（`LICENSE` を参照）。
