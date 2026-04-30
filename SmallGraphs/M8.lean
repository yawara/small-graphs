import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.Basic

/-!
# The Möbius ladder / Wagner graph `M₈`

The Möbius ladder on 8 vertices, also known as the Wagner graph, is the
simple graph on `ZMod 8` with adjacency
`i ~ j ↔ j - i ∈ {1, -1, 4}`.

## Contents

* `SmallGraphs.M8.adj`, `SmallGraphs.M8.graph` —
  the adjacency relation and the resulting `SimpleGraph`.
* `SmallGraphs.M8.r`, `SmallGraphs.M8.s` —
  the rotation `i ↦ i + 1` and the reflection `i ↦ -i`,
  packaged as graph automorphisms.

## Future work

The diameter, the explicit description `N(0) = {1, 7, 4}`,
3-regularity, and the order of `Aut(M₈)` (which equals 16) are listed
as Lean targets in `notes/mobius-ladder-m8.md` and remain to be
formalized here.
-/

namespace SmallGraphs.M8

/-- Vertex set of `M₈`, identified with `ZMod 8`. -/
abbrev V : Type := ZMod 8

/-- Adjacency relation: `i ~ j` iff `j - i ∈ {1, -1, 4}` in `ZMod 8`. -/
def adj (i j : V) : Prop :=
  j - i = 1 ∨ j - i = -1 ∨ j - i = 4

instance : DecidableRel adj := fun _ _ => by unfold adj; infer_instance

theorem adj_symm : Symmetric adj := by
  intro i j h
  have hsub : (i - j : V) = -(j - i) := by ring
  rcases h with h | h | h
  · -- j - i = 1, so i - j = -1.
    right; left; rw [hsub, h]; ring
  · -- j - i = -1, so i - j = 1.
    left; rw [hsub, h]; ring
  · -- j - i = 4, and -4 = 4 in ZMod 8.
    right; right; rw [hsub, h]; decide

theorem adj_loopless : Irreflexive adj := by
  intro i h
  have h0 : (i - i : V) = 0 := by ring
  rcases h with h | h | h <;> rw [h0] at h <;> exact absurd h (by decide)

/-- The Möbius ladder `M₈` as a `SimpleGraph` on `ZMod 8`. -/
def graph : SimpleGraph V where
  Adj := adj
  symm := adj_symm
  loopless := adj_loopless

instance : DecidableRel graph.Adj :=
  fun _ _ => (inferInstance : Decidable (adj _ _))

/-! ### Automorphisms

We exhibit two automorphisms: the rotation `r(i) = i + 1` and the
reflection `s(i) = -i`. Together these generate the dihedral group of
order 16, which (proved elsewhere) is the full automorphism group.
-/

/-- Rotation `i ↦ i + 1` as an `Equiv`. -/
def rEquiv : V ≃ V where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := by ring
  right_inv i := by ring

@[simp]
theorem rEquiv_apply (i : V) : rEquiv i = i + 1 := rfl

theorem r_map_adj_iff (i j : V) : adj (rEquiv i) (rEquiv j) ↔ adj i j := by
  simp only [rEquiv_apply]
  unfold adj
  have h : ((j + 1) - (i + 1) : V) = j - i := by ring
  rw [h]

/-- The rotation `i ↦ i + 1` as an automorphism of `M₈`. -/
def r : graph ≃g graph where
  toEquiv := rEquiv
  map_rel_iff' := r_map_adj_iff _ _

/-- Reflection `i ↦ -i` as an `Equiv`. -/
def sEquiv : V ≃ V where
  toFun i := -i
  invFun i := -i
  left_inv i := by ring
  right_inv i := by ring

@[simp]
theorem sEquiv_apply (i : V) : sEquiv i = -i := rfl

theorem s_map_adj_iff (i j : V) : adj (sEquiv i) (sEquiv j) ↔ adj i j := by
  simp only [sEquiv_apply]
  unfold adj
  have h : ((-j) - (-i) : V) = -(j - i) := by ring
  rw [h]
  constructor
  · rintro (h₁ | h₁ | h₁)
    · -- -(j - i) = 1, so j - i = -1.
      right; left
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]; ring
    · -- -(j - i) = -1, so j - i = 1.
      left
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]; ring
    · -- -(j - i) = 4, so j - i = -4 = 4 in ZMod 8.
      right; right
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]; decide
  · rintro (h₁ | h₁ | h₁)
    · right; left; rw [h₁]; ring
    · left; rw [h₁]; ring
    · right; right; rw [h₁]; decide

/-- The reflection `i ↦ -i` as an automorphism of `M₈`. -/
def s : graph ≃g graph where
  toEquiv := sEquiv
  map_rel_iff' := s_map_adj_iff _ _

/-! ### Dihedral relations on `r` and `s`

`s` has order 2, and `s ∘ r ∘ s = r⁻¹`. Together with `r` having order
8, these are the defining relations of the dihedral group `D₁₆`, so
`⟨r, s⟩` is a copy of `D₁₆` inside `Aut(M₈)`. The order relation for
`r` and the equality `Aut(M₈) = ⟨r, s⟩` are deferred to future work.
-/

theorem sEquiv_involutive : Function.Involutive sEquiv := fun i => by
  show -(-i) = i; ring

theorem s_r_s_eq_r_symm (i : V) :
    sEquiv (rEquiv (sEquiv i)) = rEquiv.symm i := by
  show (-((-i) + 1) : V) = i - 1
  ring

end SmallGraphs.M8
