# degree 57・直径2の仮想 Moore graph の自己同型群メモ

このディレクトリは、degree-diameter problem の未解決ケース

\[
D=2,\qquad k=57
\]

に対応する仮想 Moore graph \(\Gamma\) が存在すると仮定し、その自己同型群の位数を絞るための作業メモである。

## ファイル構成

- [`00-basic-facts.md`](00-basic-facts.md): 基本パラメータと隣接行列の関係式。
- [`01-fixed-subgraph-lemma.md`](01-fixed-subgraph-lemma.md): 素数位数自己同型の固定点部分グラフに関する補題。
- [`02-prime-order-obstructions.md`](02-prime-order-obstructions.md): 素数位数から来る候補排除。
- [`03-composite-order-obstructions.md`](03-composite-order-obstructions.md): 正規 Sylow 部分群と involution を使う排除。
- [`04-order-70-analysis.md`](04-order-70-analysis.md): 位数 \(70\) の詳細解析。
- [`05-current-status.md`](05-current-status.md): 現在残っている候補一覧。

## 現在の到達点

初期候補は

\[
2,6,10,14,18,22,26,30,34,38,42,46,50,54,
58,62,66,70,74,78,82,86,90,94,98,102,106,110.
\]

現在までに排除した候補は

\[
\boxed{26,34,46,58,62,66,74,78,82,86,94,102,106}.
\]

従って、現時点で残る候補は

\[
\boxed{2,6,10,14,18,22,30,38,42,50,54,70,90,98,110}.
\]

特に位数 \(70\) については完全排除ではないが、残るなら

\[
G\cong C_5\times D_{14}
\]

に限られる、というところまで絞っている。
