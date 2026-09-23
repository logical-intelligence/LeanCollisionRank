import Mathlib

set_option autoImplicit false

/-!
# Symbolic orbit actions and half-line defects

This file isolates the symbolic/permutation interface needed by the periodic
window argument.  It does not construct a Sturmian subshift or a topological
full group.
-/

namespace CollisionRank

universe u v w

/-- Equality of the radius-`rho` windows centered at `m` and `n`. -/
def SameWindow {X : Type v} {Sigma : Type w}
    (coord : X → ℤ → Sigma) (x : X) (rho : ℕ) (m n : ℤ) : Prop :=
  ∀ t : ℤ, |t| ≤ (rho : ℤ) → coord x (m + t) = coord x (n + t)

/-- Periodicity on the closed integer interval `[lo, hi]`. -/
def PeriodicOn {X : Type v} {Sigma : Type w}
    (coord : X → ℤ → Sigma) (x : X) (p : ℕ) (lo hi : ℤ) : Prop :=
  ∀ i j : ℤ,
    lo ≤ i → i ≤ hi → lo ≤ j → j ≤ hi →
    i ≡ j [ZMOD (p : ℤ)] → coord x i = coord x j

/-- The exact symbolic and permutation data used by the verified proof. -/
structure SymbolicOrbitData (G : Type u) [Group G] where
  Alphabet : Type w
  alphabetFintype : Fintype Alphabet
  alphabetDecidableEq : DecidableEq Alphabet
  Point : Type v
  coord : Point → ℤ → Alphabet
  shift : ℤ → Point → Point
  coord_shift : ∀ q x n, coord (shift q x) n = coord x (n + q)
  orbitPerm : Point → G →* Equiv.Perm ℤ
  displacementBound : G → ℕ
  displacement_bound : ∀ x g n,
    |orbitPerm x g n - n| ≤ (displacementBound g : ℤ)
  localityRadius : G → ℕ
  locality : ∀ x g m n,
    SameWindow coord x (localityRadius g) m n →
      orbitPerm x g m - m = orbitPerm x g n - n

attribute [instance] SymbolicOrbitData.alphabetFintype
attribute [instance] SymbolicOrbitData.alphabetDecidableEq

variable {G : Type u} [Group G]

namespace SymbolicOrbitData

variable (D : SymbolicOrbitData G)

/-- Displacement of `g` at the integer coordinate `n`. -/
def displacement (x : D.Point) (g : G) (n : ℤ) : ℤ :=
  D.orbitPerm x g n - n

/-- The preimage of the nonnegative half-line under the orbit permutation. -/
def defect (x : D.Point) (g : G) : Set ℤ :=
  {n | 0 ≤ D.orbitPerm x g n}

@[simp] theorem mem_defect {x : D.Point} {g : G} {n : ℤ} :
    n ∈ D.defect x g ↔ 0 ≤ D.orbitPerm x g n := Iff.rfl

/-- The subgroup preserving the cut between `-1` and `0`.  The carrier is
written pointwise; for a permutation this is equivalent to preserving the
set of nonnegative integers. -/
def halfLineStabilizer (x : D.Point) : Subgroup G where
  carrier := {g | ∀ n : ℤ, 0 ≤ D.orbitPerm x g n ↔ 0 ≤ n}
  one_mem' := by
    intro n
    simp
  mul_mem' := by
    intro f g hf hg n
    have hfg := (hf (D.orbitPerm x g n)).trans (hg n)
    simpa using hfg
  inv_mem' := by
    intro g hg n
    have hinv := (hg (D.orbitPerm x g⁻¹ n)).symm
    simpa using hinv

@[simp] theorem mem_halfLineStabilizer {x : D.Point} {g : G} :
    g ∈ D.halfLineStabilizer x ↔
      ∀ n : ℤ, 0 ≤ D.orbitPerm x g n ↔ 0 ≤ n := Iff.rfl

/-- Equality of half-line defects is exactly membership of `f * g⁻¹` in the
half-line stabilizer.  This is the orientation used by the paper. -/
theorem defect_eq_iff_mul_inv_mem (x : D.Point) (f g : G) :
    D.defect x f = D.defect x g ↔
      f * g⁻¹ ∈ D.halfLineStabilizer x := by
  constructor
  · intro h
    change ∀ n : ℤ, 0 ≤ D.orbitPerm x (f * g⁻¹) n ↔ 0 ≤ n
    intro n
    have hn := Set.ext_iff.mp h ((D.orbitPerm x g)⁻¹ n)
    change
      (0 ≤ D.orbitPerm x f ((D.orbitPerm x g)⁻¹ n)) ↔
      (0 ≤ D.orbitPerm x g ((D.orbitPerm x g)⁻¹ n)) at hn
    simpa using hn
  · intro h
    change (∀ n : ℤ, 0 ≤ D.orbitPerm x (f * g⁻¹) n ↔ 0 ≤ n) at h
    apply Set.ext
    intro n
    change (0 ≤ D.orbitPerm x f n) ↔ (0 ≤ D.orbitPerm x g n)
    have hn := h (D.orbitPerm x g n)
    simpa using hn

/-- Far enough below the cut, membership in the defect is forced to be false. -/
theorem not_mem_defect_of_lt_neg (x : D.Point) (g : G) (R : ℕ)
    (hbound : ∀ n : ℤ, |D.displacement x g n| ≤ (R : ℤ))
    {n : ℤ} (hn : n < -(R : ℤ)) : n ∉ D.defect x g := by
  intro hmem
  have hdisp := (abs_le.mp (hbound n)).2
  change 0 ≤ D.orbitPerm x g n at hmem
  dsimp [displacement] at hdisp
  omega

/-- Far enough above the cut, membership in the defect is forced to be true. -/
theorem mem_defect_of_gt (x : D.Point) (g : G) (R : ℕ)
    (hbound : ∀ n : ℤ, |D.displacement x g n| ≤ (R : ℤ))
    {n : ℤ} (hn : (R : ℤ) < n) : n ∈ D.defect x g := by
  have hdisp := (abs_le.mp (hbound n)).1
  change 0 ≤ D.orbitPerm x g n
  dsimp [displacement] at hdisp
  omega

end SymbolicOrbitData

/-! ## Permutation-orientation regression test

The generic defect lemma above depends on the multiplication convention for
`Equiv.Perm`.  This finite three-point calculation records that convention:
equal defects force `f * g⁻¹`, while the reversed expression need not
preserve the distinguished subset. -/

namespace DefectOrientationTest

abbrev Omega := Fin 3

def isNonnegative (i : Omega) : Bool := decide (i ≠ 0)
def g : Equiv.Perm Omega := Equiv.swap 0 1
def h : Equiv.Perm Omega := Equiv.swap 1 2
def f : Equiv.Perm Omega := h * g

example : ∀ i : Omega,
    isNonnegative (f i) = isNonnegative (g i) := by
  decide

example : ∀ i : Omega,
    isNonnegative ((f * g⁻¹) i) = isNonnegative i := by
  decide

example : ¬ ∀ i : Omega,
    isNonnegative ((f⁻¹ * g) i) = isNonnegative i := by
  decide

end DefectOrientationTest

/-! ## External interface -/

/-- Precisely the two inputs added to the symbolic orbit data.  The first is
local finiteness of the half-line stabilizer; the second is the
exponent-scaled periodic-window property. -/
structure ExternalInputs (G : Type u) [Group G] where
  data : SymbolicOrbitData.{u, v, w} G
  halfLine_local_finite :
    ∀ (x : data.Point) (C : Finset G),
      (∀ g ∈ C, g ∈ data.halfLineStabilizer x) →
      Finite ↥(Subgroup.closure (↑C : Set G))
  scaled_periodic_window :
    ∀ E : ℕ, 1 ≤ E →
      ∃ (x : data.Point) (p : ℕ) (a : ℤ),
        1 ≤ p ∧
        PeriodicOn data.coord x p a (a + (p : ℤ) * (E : ℤ) - 1)

/-!
The explicit `ExternalInputs` models are intentionally kept out of the
trusted interface.  The nontrivial period-four fixture is implemented in
`Regression.lean`.
-/

end CollisionRank
