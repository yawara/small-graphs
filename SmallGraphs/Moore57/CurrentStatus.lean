import SmallGraphs.Moore57.Order70Analysis

/-!
# 仮想 Moore graph $(D=2,k=57)$: 現在の候補一覧

対応するメモ:
[`notes/moore-57/05-current-status.md`](../../notes/moore-57/05-current-status.md).

これまでに自然言語メモで排除済みとされている候補集合 `eliminatedCandidates` と、
現時点で残る候補集合 `remainingCandidates` を集約する。

## 候補集合の関係

* `initialCandidates` (`BasicFacts`): $\{2,6,10,\dots,110\}$, 計 $28$ 個。
* `primeEliminated` (`PrimeOrderObstructions`):
  $\{34,46,58,62,74,82,86,94,102,106\}$, 計 $10$ 個。
* `compositeEliminated` (`CompositeOrderObstructions`):
  $\{26,66,78\}$, 計 $3$ 個。
* `eliminatedCandidates`: 上二つの和集合, 計 $13$ 個。
* `remainingCandidates`: `initialCandidates \ eliminatedCandidates`, 計 $15$ 個。

## このファイルの内容

* `SmallGraphs.Moore57.eliminatedCandidates` — 排除済み候補の和集合.
* `SmallGraphs.Moore57.remainingCandidates` — 残存候補.
* `SmallGraphs.Moore57.eliminatedCandidates_eq` — 明示的な列挙.
* `SmallGraphs.Moore57.remainingCandidates_eq` — 明示的な列挙.
* `SmallGraphs.Moore57.aut_card_in_remainingCandidates` —
  $|G|$ が偶数なら $|G|\in$ `remainingCandidates`. これは
  `BasicFacts.aut_card_in_initialCandidates`,
  `PrimeOrderObstructions.aut_card_notin_primeEliminated`,
  `CompositeOrderObstructions.aut_card_notin_compositeEliminated`
  の三つを組合せた純粋な集合論的帰結。
-/

namespace SmallGraphs.Moore57

open SimpleGraph

/-- これまでに自然言語メモで排除済みとされている候補集合
$= $ `primeEliminated` $\cup$ `compositeEliminated`
$= \{26,34,46,58,62,66,74,78,82,86,94,102,106\}$. -/
def eliminatedCandidates : Finset ℕ :=
  primeEliminated ∪ compositeEliminated

/-- 現時点で残っている候補集合
$= $ `initialCandidates` $\setminus$ `eliminatedCandidates`
$= \{2,6,10,14,18,22,30,38,42,50,54,70,90,98,110\}$. -/
def remainingCandidates : Finset ℕ :=
  initialCandidates \ eliminatedCandidates

/-! ### 候補集合の明示形 -/

theorem eliminatedCandidates_eq :
    eliminatedCandidates =
      ({26, 34, 46, 58, 62, 66, 74, 78, 82, 86, 94, 102, 106} : Finset ℕ) := by
  decide

theorem remainingCandidates_eq :
    remainingCandidates =
      ({2, 6, 10, 14, 18, 22, 30, 38, 42, 50, 54, 70, 90, 98, 110} : Finset ℕ) := by
  decide

theorem card_eliminatedCandidates : eliminatedCandidates.card = 13 := by decide

theorem card_remainingCandidates : remainingCandidates.card = 15 := by decide

theorem eliminatedCandidates_subset_initialCandidates :
    eliminatedCandidates ⊆ initialCandidates := by decide

/-! ### 残存候補定理 (`aut_card_in_remainingCandidates`)

`BasicFacts.aut_card_in_initialCandidates` (公理),
`PrimeOrderObstructions.aut_card_notin_primeEliminated` (定理),
`CompositeOrderObstructions.aut_card_notin_compositeEliminated` (定理)
の三つを合わせれば、$|G|$ が偶数のとき
$|G|\in$ `remainingCandidates` が形式的に従う。 -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、
それは現時点で残っている候補集合 `remainingCandidates` に属する。

これは `BasicFacts`, `PrimeOrderObstructions`, `CompositeOrderObstructions`
の結果を純粋に集合演算で組合せたものである。 -/
theorem aut_card_in_remainingCandidates
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    Fintype.card (Γ ≃g Γ) ∈ remainingCandidates := by
  have h1 := aut_card_in_initialCandidates h heven
  have h2 := aut_card_notin_primeEliminated h heven
  have h3 := aut_card_notin_compositeEliminated h heven
  refine Finset.mem_sdiff.mpr ⟨h1, ?_⟩
  intro hmem
  rcases Finset.mem_union.mp hmem with hp | hc
  · exact h2 hp
  · exact h3 hc

end SmallGraphs.Moore57
