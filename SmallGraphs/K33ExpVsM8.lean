import SmallGraphs.K33Exp
import SmallGraphs.M8
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# `K_{3,3}` の1頂点三角形展開と `M₈` の非同型性

8頂点・3正則・直径2のグラフは少なくとも 2 種類存在する。
このことを示すために、ここでは `SmallGraphs.K33Exp.graph` と
`SmallGraphs.M8.graph` が同型でないことを Lean 上で証明する。

## 証明の概略

* `M₈` は三角形を含まない (`SmallGraphs.M8.cliqueFree_three`)。
  これは `native_decide` による有限的計算で確認する。
* 一方 `K33Exp` は 3-クリーク `{f, g, h}` を含む (`SmallGraphs.K33Exp.isNClique_three_fgh`)。
* 単射な隣接保存写像は 3-クリークを 3-クリークに送るので、
  もし両者が同型ならば `M₈` も 3-クリークを含むことになり矛盾する。

## Main results

* `SmallGraphs.M8.cliqueFree_three` — `M₈` は 3-クリークフリー。
* `SmallGraphs.isNClique_image_of_iso` — グラフ同型は `IsNClique` を保つ。
* `SmallGraphs.K33Exp_notIso_M8` — `K33Exp.graph` と `M8.graph` は同型ではない。
-/

namespace SmallGraphs

open SimpleGraph

/-! ### `M₈` は三角形を含まない -/

/-- `M₈` (Möbius ladder / Wagner graph) は 3-クリークを含まない。
有限的計算により確認する。 -/
theorem M8.cliqueFree_three : SmallGraphs.M8.graph.CliqueFree 3 := by
  show ∀ t : Finset (ZMod 8), ¬ SmallGraphs.M8.graph.IsNClique 3 t
  native_decide

/-! ### グラフ同型による `IsNClique` の保存

任意のグラフ同型 `e : G ≃g H` は、`G` の `n`-クリーク `s` を `H` の `n`-クリーク `s.image e` に
送る。これは「同型は隣接関係を双方向に保つ」「同型は単射」という基本事実から従う。 -/

/-- グラフ同型は `IsNClique` を保つ。 -/
theorem isNClique_image_of_iso {V₁ V₂ : Type*}
    {G : SimpleGraph V₁} {H : SimpleGraph V₂} [DecidableEq V₂]
    (e : G ≃g H) {n : ℕ} {s : Finset V₁}
    (h : G.IsNClique n s) : H.IsNClique n (s.image (e : V₁ → V₂)) := by
  refine ⟨?_, ?_⟩
  · -- `image` 上のクリーク性。
    intro x hx y hy hne
    rw [Finset.coe_image, Set.mem_image] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hxy' : x' ≠ y' := fun heq => hne (by rw [heq])
    exact e.map_rel_iff'.mpr (h.isClique hx' hy' hxy')
  · -- `image` のサイズは元のサイズに等しい。
    rw [Finset.card_image_of_injective _ e.injective, h.card_eq]

/-! ### 非同型性 -/

/-- `K_{3,3}` の1頂点三角形展開と `M₈` は同型ではない。 -/
theorem K33Exp_notIso_M8 : IsEmpty (SmallGraphs.K33Exp.graph ≃g SmallGraphs.M8.graph) := by
  refine ⟨fun e => ?_⟩
  -- K33Exp 上の 3-クリーク {f, g, h}。
  have h_clique : SmallGraphs.K33Exp.graph.IsNClique 3
      ({SmallGraphs.K33Exp.f, SmallGraphs.K33Exp.g, SmallGraphs.K33Exp.h} : Finset _) :=
    SmallGraphs.K33Exp.isNClique_three_fgh
  -- これを e で送ると M8 上の 3-クリークが得られる。
  have h_image : SmallGraphs.M8.graph.IsNClique 3 _ :=
    isNClique_image_of_iso e h_clique
  -- ところが M8 は 3-クリークを含まない。
  exact SmallGraphs.M8.cliqueFree_three _ h_image

/-- `K_{3,3}` の1頂点三角形展開から `M₈` への同型は存在しない(逆向きの形)。 -/
theorem K33Exp_notIso_M8' : ¬ Nonempty (SmallGraphs.K33Exp.graph ≃g SmallGraphs.M8.graph) := by
  rw [not_nonempty_iff]
  exact K33Exp_notIso_M8

end SmallGraphs
