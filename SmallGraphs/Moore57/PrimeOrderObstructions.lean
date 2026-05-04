import SmallGraphs.Moore57.FixedSubgraphLemma

/-!
# 仮想 Moore graph $(D=2,k=57)$: 素数位数からの排除

対応するメモ:
[`notes/moore-57/02-prime-order-obstructions.md`](../../notes/moore-57/02-prime-order-obstructions.md).

素数位数自己同型の固定点部分グラフ補題 (`FixedSubgraphLemma`) と Moore graph の
スペクトル整数性を組合せると、いくつかの素数 $p$ について $p\nmid|G|$ が示せる。

| 素数 $p$ | 排除される偶数候補 |
|---:|---|
| $17$ | $34, 102$ |
| $23$ | $46$ |
| $29$ | $58$ |
| $31$ | $62$ |
| $37$ | $74$ |
| $41$ | $82$ |
| $43$ | $86$ |
| $47$ | $94$ |
| $53$ | $106$ |

合わせて $\{34,46,58,62,74,82,86,94,102,106\}$ ($10$ 個) が初期候補から除外される。

## このファイルでの形式化方針

各素数 $p\in\{17,23,29,31,37,41,43,47,53\}=$ `badPrimes` について
$p\nmid|G|$ となるという主張 (固定点部分グラフ補題と Moore graph 整数性の
帰結) を、ここでは公理 `aut_card_coprime_badPrimes` として受け入れる。

そこから各候補 $n\in$ `primeEliminated` が排除されることは、$n$ を割り切る
素数 $p\in$ `badPrimes` を選び、`aut_card_coprime_badPrimes` を適用する
だけで導かれる。これは `aut_card_notin_primeEliminated` として定理の形で
形式化する。
-/

namespace SmallGraphs.Moore57

open SimpleGraph

/-! ### 「悪い」素数集合 `badPrimes` -/

/-- 素数位数排除に使う「悪い」素数の集合
$\{17,23,29,31,37,41,43,47,53\}$.

各 $p\in$ `badPrimes` は固定点部分グラフ補題の帰結により $|G|$ を割れない. -/
def badPrimes : Finset ℕ :=
  ({17, 23, 29, 31, 37, 41, 43, 47, 53} : Finset ℕ)

theorem card_badPrimes : badPrimes.card = 9 := by decide

/-! ### 排除される候補集合 `primeEliminated` -/

/-- 素数位数からの排除で除かれる候補集合
$\{34,46,58,62,74,82,86,94,102,106\}$. -/
def primeEliminated : Finset ℕ :=
  ({34, 46, 58, 62, 74, 82, 86, 94, 102, 106} : Finset ℕ)

theorem card_primeEliminated : primeEliminated.card = 10 := by decide

theorem primeEliminated_subset_initialCandidates :
    primeEliminated ⊆ initialCandidates := by decide

/-! ### `badPrimes` についての公理

固定点部分グラフ補題と Moore graph の固有値整数性を組合せると、
任意の $p\in$ `badPrimes` について $p\nmid|G|$ が示せる。
本リポジトリでは現時点でこれら下層の議論を形式化していないため、
ここでは結論部分を公理として受け入れる。 -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、任意の
$p\in$ `badPrimes` について $p\nmid|G|$. -/
axiom aut_card_coprime_badPrimes
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    ∀ p ∈ badPrimes, ¬ (p ∣ Fintype.card (Γ ≃g Γ))

/-! ### 排除定理 (`aut_card_notin_primeEliminated`)

各 $n\in$ `primeEliminated` について、それを割る素数 $p\in$ `badPrimes` を選ぶ
だけで `aut_card_coprime_badPrimes` から $n\ne|G|$ が従う。 -/

/-- 仮想 Moore graph $\Gamma$ の自己同型群の位数が偶数なら、
それは素数位数排除集合 `primeEliminated` には属さない。 -/
theorem aut_card_notin_primeEliminated
    {V : Type*} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj]
    (h : IsMoore57 Γ)
    (heven : Even (Fintype.card (Γ ≃g Γ))) :
    Fintype.card (Γ ≃g Γ) ∉ primeEliminated := by
  intro hmem
  simp only [primeEliminated, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · -- $|G|=34=2\cdot 17$
    apply aut_card_coprime_badPrimes h heven 17 (by decide)
    rw [hc]; decide
  · -- $|G|=46=2\cdot 23$
    apply aut_card_coprime_badPrimes h heven 23 (by decide)
    rw [hc]; decide
  · -- $|G|=58=2\cdot 29$
    apply aut_card_coprime_badPrimes h heven 29 (by decide)
    rw [hc]; decide
  · -- $|G|=62=2\cdot 31$
    apply aut_card_coprime_badPrimes h heven 31 (by decide)
    rw [hc]; decide
  · -- $|G|=74=2\cdot 37$
    apply aut_card_coprime_badPrimes h heven 37 (by decide)
    rw [hc]; decide
  · -- $|G|=82=2\cdot 41$
    apply aut_card_coprime_badPrimes h heven 41 (by decide)
    rw [hc]; decide
  · -- $|G|=86=2\cdot 43$
    apply aut_card_coprime_badPrimes h heven 43 (by decide)
    rw [hc]; decide
  · -- $|G|=94=2\cdot 47$
    apply aut_card_coprime_badPrimes h heven 47 (by decide)
    rw [hc]; decide
  · -- $|G|=102=2\cdot 3\cdot 17$
    apply aut_card_coprime_badPrimes h heven 17 (by decide)
    rw [hc]; decide
  · -- $|G|=106=2\cdot 53$
    apply aut_card_coprime_badPrimes h heven 53 (by decide)
    rw [hc]; decide

end SmallGraphs.Moore57
