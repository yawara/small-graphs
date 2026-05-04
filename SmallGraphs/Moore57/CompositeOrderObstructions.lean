import SmallGraphs.Moore57.PrimeOrderObstructions

/-!
# 仮想 Moore graph $(D=2,k=57)$: 合成数位数の排除

対応するメモ:
[`notes/moore-57/03-composite-order-obstructions.md`](../../notes/moore-57/03-composite-order-obstructions.md).

正規 Sylow 部分群と involution の相互作用から、追加で次の候補を排除する。

| 候補 $|G|$ | 排除理由の概略 |
|---:|---|
| $26=2\cdot 13$ | 正規 $C_{13}$ と involution 固定星 $K_{1,55}$ の矛盾 |
| $78=2\cdot 3\cdot 13$ | 同様 ($26$ の $3$ 倍) |
| $66=2\cdot 3\cdot 11$ | 正規 $C_{11}$ と位数 $3$ の元の固定 Petersen graph の矛盾 |

合わせて $\{26,66,78\}$ ($3$ 個) が初期候補から追加で除外される。

## このファイルでの形式化方針

$26$ と $78$ は共に $13$ を含むので、

* 公理 `aut_card_coprime_thirteen`: $|G|$ が偶数なら $13\nmid|G|$

を受け入れれば $|G|\ne 26, 78$ が直ちに従う。

$66$ の排除は固有の議論 (Sylow $11$ の中心化と Petersen graph 固定) によるため、
ここでは

* 公理 `aut_card_ne_66`: $|G|$ が偶数なら $|G|\ne 66$

として受け入れる。

両者を合わせて `aut_card_notin_compositeEliminated` を定理として証明する。
-/

namespace SmallGraphs.Moore57

open SimpleGraph

/-! ### 排除される候補集合 `compositeEliminated` -/

/-- 合成数位数の排除で除かれる候補集合 $\{26,66,78\}$. -/
def compositeEliminated : Finset ℕ :=
  ({26, 66, 78} : Finset ℕ)

theorem card_compositeEliminated : compositeEliminated.card = 3 := by decide

theorem compositeEliminated_subset_initialCandidates :
    compositeEliminated ⊆ initialCandidates := by decide

/-! ### 公理 -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、$13\nmid|G|$.

これは「正規 $C_{13}$ + involution は $\Gamma$ 上で矛盾」という $03$ メモの
議論の結論であり、本リポジトリでは公理として受け入れる。 -/
axiom aut_card_coprime_thirteen
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    ¬ (13 ∣ Fintype.card (Γ ≃g Γ))

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、$|G|\ne 66$.

これは「位数 $66$ に対する正規 $C_{11}$ + 位数 $3$ の固定 Petersen graph」という
$03$ メモの議論の結論であり、本リポジトリでは公理として受け入れる。 -/
axiom aut_card_ne_66
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    Fintype.card (Γ ≃g Γ) ≠ 66

/-! ### 排除定理 (`aut_card_notin_compositeEliminated`) -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、
それは合成数位数排除集合 `compositeEliminated` には属さない。 -/
theorem aut_card_notin_compositeEliminated
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    Fintype.card (Γ ≃g Γ) ∉ compositeEliminated := by
  intro hmem
  simp only [compositeEliminated, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hc | hc | hc
  · -- $|G|=26=2\cdot 13$
    apply aut_card_coprime_thirteen h heven
    rw [hc]; decide
  · -- $|G|=66$
    exact aut_card_ne_66 h heven hc
  · -- $|G|=78=2\cdot 3\cdot 13$
    apply aut_card_coprime_thirteen h heven
    rw [hc]; decide

end SmallGraphs.Moore57
