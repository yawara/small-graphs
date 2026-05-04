import SmallGraphs.Moore57.BasicFacts
import SmallGraphs.Moore57.FixedSubgraphLemma
import SmallGraphs.Moore57.PrimeOrderObstructions
import SmallGraphs.Moore57.CompositeOrderObstructions
import SmallGraphs.Moore57.Order70Analysis
import SmallGraphs.Moore57.CurrentStatus

/-!
# 仮想 Moore graph $(D=2,k=57)$ — モジュール集

degree-diameter problem の未解決ケース $(D=2,k=57)$ に対応する仮想 Moore graph
$\Gamma$ について、その自己同型群 $G=\operatorname{Aut}(\Gamma)$ の偶数位数候補
リストを Lean 上で扱うためのモジュール群。

各サブモジュールは自然言語メモ
[`notes/moore-57/`](../notes/moore-57/) のファイルと一対一に対応する。

## 対応表 (notes ↔ SmallGraphs/Moore57)

| 自然言語メモ | Lean モジュール |
|---|---|
| [`00-basic-facts.md`](../notes/moore-57/00-basic-facts.md) | [`BasicFacts`](Moore57/BasicFacts.lean) |
| [`01-fixed-subgraph-lemma.md`](../notes/moore-57/01-fixed-subgraph-lemma.md) | [`FixedSubgraphLemma`](Moore57/FixedSubgraphLemma.lean) |
| [`02-prime-order-obstructions.md`](../notes/moore-57/02-prime-order-obstructions.md) | [`PrimeOrderObstructions`](Moore57/PrimeOrderObstructions.lean) |
| [`03-composite-order-obstructions.md`](../notes/moore-57/03-composite-order-obstructions.md) | [`CompositeOrderObstructions`](Moore57/CompositeOrderObstructions.lean) |
| [`04-order-70-analysis.md`](../notes/moore-57/04-order-70-analysis.md) | [`Order70Analysis`](Moore57/Order70Analysis.lean) |
| [`05-current-status.md`](../notes/moore-57/05-current-status.md) | [`CurrentStatus`](Moore57/CurrentStatus.lean) |

## 形式化の現状

* 公理 (証明無しで受け入れている):
  * `BasicFacts.aut_card_in_initialCandidates` — 偶数位数なら
    `initialCandidates` に属する。
  * `PrimeOrderObstructions.aut_card_coprime_badPrimes` — 偶数位数は
    $\{17,23,29,31,37,41,43,47,53\}=$ `badPrimes` のどの素数でも割れない。
  * `CompositeOrderObstructions.aut_card_coprime_thirteen` — 偶数位数は
    $13$ で割れない。
  * `CompositeOrderObstructions.aut_card_ne_66` — 偶数位数は $66$ ではない。
* 形式的に証明済みの定理:
  * `PrimeOrderObstructions.aut_card_notin_primeEliminated` —
    `aut_card_coprime_badPrimes` から各候補 $n\in$ `primeEliminated` を
    その素因数で割って排除。
  * `CompositeOrderObstructions.aut_card_notin_compositeEliminated` —
    `aut_card_coprime_thirteen` と `aut_card_ne_66` から
    $\{26,66,78\}$ を排除。
  * `CurrentStatus.aut_card_in_remainingCandidates` —
    上記三つの定理を組合せて
    $|G|\in$ `remainingCandidates` を結論。
* 未形式化:
  * `FixedSubgraphLemma` の各補題 (素数位数自己同型の固定点部分グラフ構造).
  * `PrimeOrderObstructions` および `CompositeOrderObstructions` 内の
    各公理の根拠 (固定点部分グラフ補題と Moore graph スペクトル整数性, Sylow + involution).
  * `Order70Analysis` の群構造解析.
-/
