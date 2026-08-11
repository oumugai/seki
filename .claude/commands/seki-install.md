---
description: 現在のソースから release ビルドし、グローバル install (~/.local/bin/seki) を更新する
---

このリポジトリのソースを、このマシンにグローバルインストールされている
`seki` (`~/.local/bin/seki`, PATH 上) に反映してください。グローバル版の
`seki-run` / `seki-check` / `seki-new-theorem` / `seki-tactics` /
`seki-reference` (`~/.claude/` 配下) はこのバイナリを使うので、ソースを
変更したら更新しておく必要がある。

## 手順

1. リポジトリルートで `cargo build --release --bin seki --quiet` を実行する。
   エラーが出たら止めて見せる。
2. `cargo test` (または直近の変更に関係するテストだけ) を通して
   回帰がないことを確認してから次に進む — 壊れたバイナリを
   グローバルに配布しない。
3. `cp target/release/seki ~/.local/bin/seki` でコピーする。
4. `~/.seki/lib` が `<このリポジトリ>/lib` への symlink になっているか
   確認する (`ls -la ~/.seki/lib`)。無ければ
   `mkdir -p ~/.seki && ln -sfn "$(pwd)/lib" ~/.seki/lib` で作る。
5. `seki --version` で更新後のコミットハッシュが反映されたことを確認する。
6. 軽くサニティチェックする (例:
   `cd /tmp && seki -e 'theorem t : 2 + 2 == 4 := by eval'`)。

## 注意

- `~/.local/bin` が PATH に無いと `seki` コマンドとして呼べない
  (`echo $PATH | tr ':' '\n' | grep local/bin` で確認)。
- これは **個人環境の更新** であり、リポジトリ自体には影響しない
  (`.claude/` のコマンド/skill だけが git 管理下で他の利用者と共有される —
  `seki-dev` skill 参照)。
