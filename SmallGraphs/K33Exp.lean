import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Group.End
import Mathlib.Tactic.FinCases

/-!
# `K_{3,3}` の1頂点三角形展開

このファイルでは、`K_{3,3}` の一方の部にある1頂点を三角形に置き換えて得られる
8頂点・3正則・直径2のグラフを Lean 上で形式化する。

頂点集合は `V := Fin 2 ⊕ (Fin 3 ⊕ Fin 3)` と取る。
- `inl i` は `A = {a, b}` の頂点 (`Fin 2` 部分)
- `inr (inl i)` は `B = {c, d, e}` の頂点 (`Fin 3` 部分)
- `inr (inr i)` は `T = {f, h, g}` の頂点 (もう一つの `Fin 3` 部分)

`B` と `T` は同じ添字で対応させる。すなわち
`c = inr (inl 0)` の対応辺は `f = inr (inr 0)` 側にある。

辺集合は次の3種類からなる。
* `A` と `B` の間の完全二部グラフ `K_{2,3}`
* `B` と `T` を結ぶ対応辺(添字が一致するとき)
* `T` 上の三角形(全ての異なる対が辺)

## Main results

* `SmallGraphs.K33Exp.adj`, `SmallGraphs.K33Exp.graph` —
  隣接関係と単純グラフ。
* `SmallGraphs.K33Exp.isRegular_three` — 3正則性。
* `SmallGraphs.K33Exp.notAdj_a_b` — `a` と `b` は隣接しない。
* `SmallGraphs.K33Exp.isClique_fgh` — `T = {f, g, h}` が三角形をなすこと。
* `SmallGraphs.K33Exp.actPerm` —
  `Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)` から `Equiv.Perm V` への準同型。
* `SmallGraphs.K33Exp.phi` —
  `Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) →* (graph ≃g graph)` の準同型。
* `SmallGraphs.K33Exp.autEquiv` —
  自己同型群 `graph ≃g graph` が `Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)` と
  同型であることの証明。位数12。
-/

namespace SmallGraphs.K33Exp

/-- 頂点集合。`Fin 2 ⊕ (Fin 3 ⊕ Fin 3)` として
    `A = Fin 2`、`B = Fin 3` (左)、`T = Fin 3` (右) と分ける。 -/
abbrev V : Type := Fin 2 ⊕ (Fin 3 ⊕ Fin 3)

/-- 頂点 `a = inl 0`. -/
abbrev a : V := .inl 0
/-- 頂点 `b = inl 1`. -/
abbrev b : V := .inl 1
/-- 頂点 `c = inr (inl 0)`. -/
abbrev c : V := .inr (.inl 0)
/-- 頂点 `d = inr (inl 1)`. -/
abbrev d : V := .inr (.inl 1)
/-- 頂点 `e = inr (inl 2)`. -/
abbrev e : V := .inr (.inl 2)
/-- 頂点 `f = inr (inr 0)`. -/
abbrev f : V := .inr (.inr 0)
/-- 頂点 `h = inr (inr 1)`. -/
abbrev h : V := .inr (.inr 1)
/-- 頂点 `g = inr (inr 2)`. -/
abbrev g : V := .inr (.inr 2)

/-- 隣接関係。各場合分けは次の通り。
* `A`-`A`, `A`-`T`, `B`-`B`, `T`-`A` は非隣接。
* `A`-`B` (および逆) は完全二部 (常に隣接)。
* `B`-`T` (および逆) は同じ添字の場合のみ隣接。
* `T`-`T` は異なる頂点同士で隣接 (三角形)。
-/
def adj : V → V → Prop
  | .inl _, .inl _ => False
  | .inl _, .inr (.inl _) => True
  | .inl _, .inr (.inr _) => False
  | .inr (.inl _), .inl _ => True
  | .inr (.inl _), .inr (.inl _) => False
  | .inr (.inl i), .inr (.inr j) => i = j
  | .inr (.inr _), .inl _ => False
  | .inr (.inr i), .inr (.inl j) => j = i
  | .inr (.inr i), .inr (.inr j) => i ≠ j

instance instDecidableAdj : DecidableRel adj := by
  rintro (i | (i | i)) (j | (j | j)) <;>
    unfold adj <;> infer_instance

theorem adj_symm : Symmetric adj := by
  rintro (i | (i | i)) (j | (j | j)) hij <;>
    first
      | exact hij
      | exact hij.symm

instance instIrreflAdj : Std.Irrefl adj where
  irrefl := by
    rintro (i | (i | i)) hii
    all_goals first | exact hii | exact hii rfl

/-- グラフ `K_{3,3}` の1頂点三角形展開。 -/
def graph : SimpleGraph V where
  Adj := adj
  symm := adj_symm
  loopless := instIrreflAdj

instance decidableAdj : DecidableRel graph.Adj :=
  fun _ _ => (inferInstance : Decidable (adj _ _))

/-! ### 3正則性 -/

theorem isRegular_three : graph.IsRegularOfDegree 3 := by
  intro v
  rcases v with i | (i | i) <;> fin_cases i <;> decide

/-! ### 簡単な距離・隣接の事実 -/

/-- 頂点 `a` と `b` は隣接しない。 -/
theorem notAdj_a_b : ¬ graph.Adj a b := by
  show ¬ adj a b
  unfold a b adj
  exact id

/-- 頂点 `a` は `c` と隣接する。 -/
theorem adj_a_c : graph.Adj a c := by
  show adj a c
  unfold a c adj
  trivial

/-! ### 次数

`isRegular_three` から、`graph.degree v = 3` が任意の頂点 `v` で成り立つ。
ここでは閲覧の便を考えて、その一頂点版を別補題として明示しておく。 -/

/-- 任意の頂点の次数は 3。 -/
theorem degree_eq_three (v : V) : graph.degree v = 3 :=
  isRegular_three v

/-! ### 三角形 `{f, g, h}` -/

/-- `T = {f, g, h}` は3頂点クリークである(`graph` における三角形)。
これにより、このグラフが三角形を含まない `M_8` と非同型であることが分かる。 -/
theorem isClique_fgh : graph.IsClique ({f, g, h} : Finset V) := by decide

/-- `{f, g, h}` は `graph` における 3-クリークである。 -/
theorem isNClique_three_fgh : graph.IsNClique 3 ({f, g, h} : Finset V) := by decide

/-- `graph` に含まれる 3-クリークは `{f, g, h}` のみ。
これは `graph` に含まれる三角形の唯一性を表す。 -/
theorem isNClique_three_unique :
    ∀ s : Finset V, graph.IsNClique 3 s → s = ({f, g, h} : Finset V) := by
  native_decide

/-! ### 直径

直径 = 2 を示すために、上下の評価を分けて行う。
* 上界: 任意の2頂点に対して長さ 2 以下の歩道が存在する(必要なら `(c, f, h)` などの
  共通近傍を経由する)。
* 下界: `a, b` は相異なり非隣接なので `edist a b ≥ 2`。
-/

/-- 任意の異なる非隣接2頂点には共通近傍が存在する。
これは長さ 2 の歩道を構成するための補題である。 -/
theorem exists_common_neighbor (u v : V) (hne : u ≠ v) (nad : ¬ graph.Adj u v) :
    ∃ w : V, graph.Adj u w ∧ graph.Adj w v := by
  revert hne nad
  rcases u with i | (i | i) <;> rcases v with j | (j | j) <;>
    fin_cases i <;> fin_cases j <;> decide

/-- 任意の2頂点間の `edist` は 2 以下。 -/
theorem edist_le_two (u v : V) : graph.edist u v ≤ 2 := by
  by_cases huv : u = v
  · subst huv
    simp
  by_cases hadj : graph.Adj u v
  · calc graph.edist u v
        = 1 := SimpleGraph.edist_eq_one_iff_adj.mpr hadj
      _ ≤ 2 := by decide
  obtain ⟨w, hw1, hw2⟩ := exists_common_neighbor u v huv hadj
  let hwalk : graph.Walk u v :=
    SimpleGraph.Walk.cons hw1 (SimpleGraph.Walk.cons hw2 SimpleGraph.Walk.nil)
  have hlen : hwalk.length = 2 := by
    simp [hwalk, SimpleGraph.Walk.length_cons]
  calc graph.edist u v
      ≤ (hwalk.length : ℕ∞) := SimpleGraph.edist_le hwalk
    _ = ((2 : ℕ) : ℕ∞) := by rw [hlen]
    _ = 2 := by norm_cast

/-- グラフの拡張直径 `ediam` は 2 以下。 -/
theorem ediam_le_two : graph.ediam ≤ 2 :=
  SimpleGraph.ediam_le_iff.mpr edist_le_two

/-- `a` と `b` は距離ちょうど 2 である(等しくなく、隣接もしないが、共通近傍 `c` を持つ)。 -/
theorem edist_a_b_eq_two : graph.edist a b = 2 := by
  rw [SimpleGraph.edist_eq_two_iff]
  refine ⟨?_, notAdj_a_b, ?_⟩
  · decide
  · -- 共通近傍 `c` を取る。
    refine ⟨c, ?_⟩
    rw [SimpleGraph.mem_commonNeighbors]
    refine ⟨?_, ?_⟩ <;> decide

/-- グラフの拡張直径 `ediam` は 2 以上。 -/
theorem two_le_ediam : 2 ≤ graph.ediam :=
  edist_a_b_eq_two ▸ SimpleGraph.edist_le_ediam

/-- グラフの拡張直径 `ediam` はちょうど 2。 -/
theorem ediam_eq_two : graph.ediam = 2 :=
  le_antisymm ediam_le_two two_le_ediam

/-- グラフの直径 `diam` はちょうど 2。 -/
theorem diam_eq_two : graph.diam = 2 := by
  rw [SimpleGraph.diam, ediam_eq_two]
  rfl

/-! ### 自己同型の構成

`(σ, τ) : Perm (Fin 3) × Perm (Fin 2)` に対し、
`τ` を `A`-成分に、`σ` を `B`-成分と `T`-成分に同時に作用させる。
これは `Equiv.Perm.sumCongr τ (Equiv.Perm.sumCongr σ σ) : Perm V` で実現できる。
-/

/-- `(σ, τ) ↦ τ ⊕ (σ ⊕ σ)` を `Perm V` への作用として定める準同型。 -/
def actPerm : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) →* Equiv.Perm V where
  toFun στ := Equiv.Perm.sumCongr στ.2 (Equiv.Perm.sumCongr στ.1 στ.1)
  map_one' := by
    show Equiv.Perm.sumCongr 1 (Equiv.Perm.sumCongr 1 1) = 1
    rw [Equiv.Perm.sumCongr_one, Equiv.Perm.sumCongr_one]
  map_mul' := by
    rintro ⟨σx, τx⟩ ⟨σy, τy⟩
    show Equiv.Perm.sumCongr ((τx, τy).1 * (τx, τy).2) _ = _
    simp [Prod.mk_mul_mk, Equiv.Perm.sumCongr_mul]

@[simp] theorem actPerm_apply_inl (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2))
    (i : Fin 2) : actPerm στ (.inl i) = .inl (στ.2 i) := rfl

@[simp] theorem actPerm_apply_inr_inl
    (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (i : Fin 3) :
    actPerm στ (.inr (.inl i)) = .inr (.inl (στ.1 i)) := rfl

@[simp] theorem actPerm_apply_inr_inr
    (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (i : Fin 3) :
    actPerm στ (.inr (.inr i)) = .inr (.inr (στ.1 i)) := rfl

/-- `actPerm στ` は隣接関係を保つ。 -/
theorem actPerm_preserves_adj
    (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (x y : V) :
    adj (actPerm στ x) (actPerm στ y) ↔ adj x y := by
  rcases x with i | (i | i) <;> rcases y with j | (j | j) <;>
    simp only [actPerm_apply_inl, actPerm_apply_inr_inl, actPerm_apply_inr_inr, adj]
  · -- B-T case: σ.1 i = σ.1 j ↔ i = j
    exact (Equiv.apply_eq_iff_eq _)
  · -- T-B case: σ.1 j = σ.1 i ↔ j = i
    exact (Equiv.apply_eq_iff_eq _)
  · -- T-T case: σ.1 i ≠ σ.1 j ↔ i ≠ j
    exact (Equiv.apply_eq_iff_eq _).not

/-- `actPerm στ` をグラフ自己同型に持ち上げたもの。 -/
def actGraphIso (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) : graph ≃g graph where
  toEquiv := actPerm στ
  map_rel_iff' := actPerm_preserves_adj στ _ _

@[simp] theorem actGraphIso_apply
    (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (v : V) :
    actGraphIso στ v = actPerm στ v := rfl

/-! ### 群準同型 `phi`

`actGraphIso` は群準同型である。これは `actPerm` が `MonoidHom` であることから従う。
-/

/-- 群準同型 `Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) →* (graph ≃g graph)`。 -/
def phi : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) →* (graph ≃g graph) where
  toFun := actGraphIso
  map_one' := by
    apply RelIso.ext
    intro v
    show actPerm 1 v = v
    rw [actPerm.map_one]
    rfl
  map_mul' := by
    intro x y
    apply RelIso.ext
    intro v
    show actPerm (x * y) v = actPerm x (actPerm y v)
    rw [actPerm.map_mul]
    rfl

@[simp] theorem phi_apply (στ : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) (v : V) :
    (phi στ : V → V) v = actPerm στ v := rfl

/-! ### `phi` の単射性

異なる `(σ, τ)` は異なる自己同型を与える。
具体的には `στ.2` の値は `inl` での値から、`στ.1` の値は `inr (inl _)` での値から復元できる。 -/

theorem phi_injective : Function.Injective phi := by
  rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ hxy
  -- `phi` を関数として比較する。
  have hfun : ∀ v : V, actPerm (σ₁, τ₁) v = actPerm (σ₂, τ₂) v := fun v =>
    congrFun (congrArg ((↑·) : (graph ≃g graph) → V → V) hxy) v
  have hσ : σ₁ = σ₂ := by
    apply Equiv.ext
    intro i
    have h := hfun (.inr (.inl i))
    simp only [actPerm_apply_inr_inl] at h
    exact Sum.inl_injective (Sum.inr_injective h)
  have hτ : τ₁ = τ₂ := by
    apply Equiv.ext
    intro i
    have h := hfun (.inl i)
    simp only [actPerm_apply_inl] at h
    exact Sum.inl_injective h
  exact Prod.ext hσ hτ

/-! ### 自己同型群の有限性

`graph ≃g graph` は `Equiv.Perm V` の部分集合に同型な型なので Fintype である。
位数を計算するため、`{f : V ≃ V // ∀ a b, graph.Adj a b ↔ graph.Adj (f a) (f b)}` を経由して
`Fintype` 構造を移植する。 -/

/-- グラフ自己同型と「隣接を保つ Equiv」の subtype の間の同値。 -/
def isoEquivSubtype :
    { f : V ≃ V // ∀ a b, graph.Adj a b ↔ graph.Adj (f a) (f b) } ≃
    (graph ≃g graph) where
  toFun := fun ⟨e, hpres⟩ =>
    { toEquiv := e
      map_rel_iff' := fun {a b} => (hpres a b).symm }
  invFun := fun f => ⟨f.toEquiv, fun _ _ => f.map_rel_iff'.symm⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

instance fintypeIso : Fintype (graph ≃g graph) :=
  Fintype.ofEquiv _ isoEquivSubtype

/-! ### 自己同型群の位数

`graph ≃g graph` の位数は12である。
これと `Fintype.card (Perm (Fin 3) × Perm (Fin 2)) = 6 * 2 = 12` を合わせ、
単射 `phi` が全単射であることを結論する。 -/

theorem card_aut : Fintype.card (graph ≃g graph) = 12 := by native_decide

theorem card_domain :
    Fintype.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2)) = 12 := by
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  decide

theorem phi_bijective : Function.Bijective phi := by
  refine (Fintype.bijective_iff_injective_and_card phi).mpr ⟨phi_injective, ?_⟩
  rw [card_aut, card_domain]

/-- グラフ自己同型群の同型 `Aut(G) ≅ Perm (Fin 3) × Perm (Fin 2)`。
位数は12。 -/
noncomputable def autEquiv :
    Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) ≃* (graph ≃g graph) :=
  MulEquiv.ofBijective phi phi_bijective

end SmallGraphs.K33Exp
