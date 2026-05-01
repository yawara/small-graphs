import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Order.Group.End

/-!
# The Möbius ladder / Wagner graph `M₈`

The Möbius ladder on 8 vertices, also known as the Wagner graph, is the
simple graph on `ZMod 8` with adjacency
`i ~ j ↔ j - i ∈ {1, -1, 4}`.

## Main results

* `SmallGraphs.M8.adj`, `SmallGraphs.M8.graph` —
  the adjacency relation and the resulting `SimpleGraph`.
* `SmallGraphs.M8.rot`, `SmallGraphs.M8.refl` —
  the rotation `i ↦ i + k` and the affine reflection `i ↦ -i - k`,
  packaged as graph automorphisms.
* `SmallGraphs.M8.phi : DihedralGroup 8 →* (graph ≃g graph)` —
  the homomorphism sending `r k ↦ rot k` and `sr k ↦ refl k`.
* `SmallGraphs.M8.autEquiv : DihedralGroup 8 ≃* (graph ≃g graph)` —
  the resulting group isomorphism, witnessing `Aut(M₈) ≅ D₁₆`.
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
  · right; left; rw [hsub, h]
  · left; rw [hsub, h]; ring
  · right; right; rw [hsub, h]; decide

theorem adj_loopless : ∀ i : V, ¬ adj i i := by
  intro i h
  have h0 : (i - i : V) = 0 := by ring
  rcases h with h | h | h <;> rw [h0] at h <;> exact absurd h (by decide)

/-- The Möbius ladder `M₈` as a `SimpleGraph` on `ZMod 8`. -/
def graph : SimpleGraph V where
  Adj := adj
  symm := adj_symm
  loopless := ⟨adj_loopless⟩

instance decidableAdj : DecidableRel graph.Adj :=
  fun _ _ => (inferInstance : Decidable (adj _ _))

/-! ### Parameterized automorphisms

For each shift `k : V`, we define two graph automorphisms:
the rotation `rot k : i ↦ i + k` and the affine reflection
`refl k : i ↦ -i - k = -(i + k)`. The reflection convention is chosen
so that under multiplication on `RelIso` (where `(f * g) x = f (g x)`)
the obvious map `r k ↦ rot k`, `sr k ↦ refl k` is a homomorphism from
`DihedralGroup 8`.
-/

/-- Rotation `i ↦ i + k` as an `Equiv`. -/
def rotEquiv (k : V) : V ≃ V where
  toFun i := i + k
  invFun i := i - k
  left_inv i := by ring
  right_inv i := by ring

@[simp] theorem rotEquiv_apply (k i : V) : rotEquiv k i = i + k := rfl

theorem rot_preserves_adj (k i j : V) :
    adj (rotEquiv k i) (rotEquiv k j) ↔ adj i j := by
  simp only [rotEquiv_apply]
  unfold adj
  have h : ((j + k) - (i + k) : V) = j - i := by ring
  rw [h]

/-- Rotation by `k` as an automorphism of `M₈`. -/
def rot (k : V) : graph ≃g graph where
  toEquiv := rotEquiv k
  map_rel_iff' := rot_preserves_adj k _ _

@[simp] theorem rot_apply (k i : V) : rot k i = i + k := rfl

/-- Affine reflection `i ↦ -i - k = -(i + k)` as an `Equiv`. (Self-inverse.) -/
def reflEquiv (k : V) : V ≃ V where
  toFun i := -i - k
  invFun i := -i - k
  left_inv i := by ring
  right_inv i := by ring

@[simp] theorem reflEquiv_apply (k i : V) : reflEquiv k i = -i - k := rfl

theorem refl_preserves_adj (k i j : V) :
    adj (reflEquiv k i) (reflEquiv k j) ↔ adj i j := by
  simp only [reflEquiv_apply]
  unfold adj
  have h : ((-j - k) - (-i - k) : V) = -(j - i) := by ring
  rw [h]
  constructor
  · rintro (h₁ | h₁ | h₁)
    · right; left
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]
    · left
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]; ring
    · right; right
      have : (j - i : V) = -(-(j - i)) := by ring
      rw [this, h₁]; decide
  · rintro (h₁ | h₁ | h₁)
    · right; left; rw [h₁]
    · left; rw [h₁]; ring
    · right; right; rw [h₁]; decide

/-- Affine reflection `i ↦ -i - k` as an automorphism of `M₈`. -/
def refl (k : V) : graph ≃g graph where
  toEquiv := reflEquiv k
  map_rel_iff' := refl_preserves_adj k _ _

@[simp] theorem refl_apply (k i : V) : refl k i = -i - k := rfl

/-! ### The homomorphism `phi : DihedralGroup 8 →* (graph ≃g graph)`

Multiplication in `graph ≃g graph` (inherited from `RelIso`) satisfies
`(f * g) x = f (g x)`. We send `r k ↦ rot k` and `sr k ↦ refl k`,
and verify that this is a monoid homomorphism by case analysis on
the four products in `DihedralGroup 8`.
-/

/-- The underlying function of `phi`. -/
def phiFn : DihedralGroup 8 → (graph ≃g graph)
  | DihedralGroup.r k => rot k
  | DihedralGroup.sr k => refl k

@[simp] theorem phiFn_r (k : V) : phiFn (DihedralGroup.r k) = rot k := rfl
@[simp] theorem phiFn_sr (k : V) : phiFn (DihedralGroup.sr k) = refl k := rfl

theorem phiFn_one : phiFn (1 : DihedralGroup 8) = 1 := by
  show phiFn (DihedralGroup.r 0) = 1
  ext i
  simp only [phiFn_r, rot_apply, RelIso.coe_one, id_eq, add_zero]

theorem phiFn_mul (a b : DihedralGroup 8) : phiFn (a * b) = phiFn a * phiFn b := by
  rcases a with k | k <;> rcases b with m | m
  · -- r k * r m = r (k + m)
    rw [DihedralGroup.r_mul_r, phiFn_r, phiFn_r, phiFn_r]
    ext x
    simp only [RelIso.coe_mul, Function.comp_apply, rot_apply]
    ring
  · -- r k * sr m = sr (m - k)
    rw [DihedralGroup.r_mul_sr, phiFn_sr, phiFn_r, phiFn_sr]
    ext x
    simp only [RelIso.coe_mul, Function.comp_apply, rot_apply, refl_apply]
    ring
  · -- sr k * r m = sr (k + m)
    rw [DihedralGroup.sr_mul_r, phiFn_sr, phiFn_sr, phiFn_r]
    ext x
    simp only [RelIso.coe_mul, Function.comp_apply, rot_apply, refl_apply]
    ring
  · -- sr k * sr m = r (m - k)
    rw [DihedralGroup.sr_mul_sr, phiFn_r, phiFn_sr, phiFn_sr]
    ext x
    simp only [RelIso.coe_mul, Function.comp_apply, rot_apply, refl_apply]
    ring

/-- The monoid homomorphism `DihedralGroup 8 →* (graph ≃g graph)`. -/
def phi : DihedralGroup 8 →* (graph ≃g graph) where
  toFun := phiFn
  map_one' := phiFn_one
  map_mul' := phiFn_mul

@[simp] theorem phi_r (k : V) : phi (DihedralGroup.r k) = rot k := rfl
@[simp] theorem phi_sr (k : V) : phi (DihedralGroup.sr k) = refl k := rfl

/-! ### Injectivity of `phi`

We compare `phi a` and `phi b` pointwise at `0` (and, when needed, at `1`).
The only nontrivial cross cases (rotation versus reflection) reduce to
`2 = 0` in `ZMod 8`, which is false.
-/

theorem phi_injective : Function.Injective phi := by
  intro a b hab
  rcases a with k | k <;> rcases b with m | m
  · -- r k = r m
    have h0 : (phi (DihedralGroup.r k) : V → V) 0 =
              (phi (DihedralGroup.r m) : V → V) 0 := by rw [hab]
    simp [phi_r, rot_apply] at h0
    exact congrArg DihedralGroup.r h0
  · -- r k = sr m: contradiction
    exfalso
    have h0 : (phi (DihedralGroup.r k) : V → V) 0 =
              (phi (DihedralGroup.sr m) : V → V) 0 := by rw [hab]
    have h1 : (phi (DihedralGroup.r k) : V → V) 1 =
              (phi (DihedralGroup.sr m) : V → V) 1 := by rw [hab]
    simp [phi_r, phi_sr, rot_apply, refl_apply] at h0 h1
    -- h0 : k = -m, h1 : 1 + k = -1 - m
    rw [h0] at h1
    have h2 : (2 : V) = 0 := by linear_combination h1
    exact absurd h2 (by decide)
  · -- sr k = r m: contradiction
    exfalso
    have h0 : (phi (DihedralGroup.sr k) : V → V) 0 =
              (phi (DihedralGroup.r m) : V → V) 0 := by rw [hab]
    have h1 : (phi (DihedralGroup.sr k) : V → V) 1 =
              (phi (DihedralGroup.r m) : V → V) 1 := by rw [hab]
    simp [phi_r, phi_sr, rot_apply, refl_apply] at h0 h1
    -- h0 : -k = m, h1 : -1 - k = 1 + m
    rw [← h0] at h1
    have h2 : (2 : V) = 0 := by linear_combination -h1
    exact absurd h2 (by decide)
  · -- sr k = sr m
    have h0 : (phi (DihedralGroup.sr k) : V → V) 0 =
              (phi (DihedralGroup.sr m) : V → V) 0 := by rw [hab]
    simp [phi_sr, refl_apply] at h0
    -- h0 : k = m  (`simp` collapses `-k = -m` via `neg_inj`)
    exact congrArg DihedralGroup.sr h0

/-! ### Finiteness and cardinality of `Aut(M₈)`

`graph ≃g graph` injects into `V ≃ V` (= `Equiv.Perm V`), which is a
`Fintype`, so `graph ≃g graph` is itself a `Fintype`. Its cardinality
turns out to be 16, which we verify by `native_decide`. Since
`DihedralGroup 8` also has cardinality 16 and `phi` is injective,
`phi` is bijective.
-/

/-- Bijection between `graph ≃g graph` and the subtype of `V ≃ V`
that preserves adjacency. Used to transport the (computable) `Fintype`
instance from `Equiv.Perm V`. -/
def isoEquivSubtype :
    { f : V ≃ V // ∀ a b, graph.Adj a b ↔ graph.Adj (f a) (f b) } ≃
    (graph ≃g graph) where
  toFun := fun ⟨e, h⟩ =>
    { toEquiv := e
      map_rel_iff' := fun {a b} => (h a b).symm }
  invFun := fun f => ⟨f.toEquiv, fun _ _ => f.map_rel_iff'.symm⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

instance fintypeIso : Fintype (graph ≃g graph) :=
  Fintype.ofEquiv _ isoEquivSubtype

theorem card_aut : Fintype.card (graph ≃g graph) = 16 := by native_decide

/-! ### The group isomorphism `Aut(M₈) ≅ DihedralGroup 8` -/

theorem phi_bijective : Function.Bijective phi := by
  refine (Fintype.bijective_iff_injective_and_card phi).mpr ⟨phi_injective, ?_⟩
  rw [card_aut, DihedralGroup.card]

/-- The group isomorphism `Aut(M₈) ≅ DihedralGroup 8`,
witnessing that the automorphism group of the Möbius ladder is the
dihedral group of order 16 (i.e. `D₈` in the convention where `Dₙ`
denotes the symmetries of a regular `n`-gon). -/
noncomputable def autEquiv : DihedralGroup 8 ≃* (graph ≃g graph) :=
  MulEquiv.ofBijective phi phi_bijective

end SmallGraphs.M8
