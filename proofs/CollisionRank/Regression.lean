import CollisionRank.Orbit

set_option autoImplicit false

/-!
# Regression models for the symbolic-orbit interface

This file is deliberately independent of the collision-rank argument.  Its
main object is a completely explicit period-four model.  The model makes the
radius-one locality hypothesis nonvacuous: the displacement alternates
between `+1` and `-1`, while the central symbols alone do not determine it.
-/

namespace CollisionRank

namespace PeriodFourModel

/-- The two-element group, written multiplicatively. -/
abbrev G := Multiplicative (ZMod 2)

/-- Every element of `ZMod 2` is either zero or one. -/
lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hval : a.val = 0 ∨ a.val = 1 := by omega
  rcases hval with hval | hval
  · exact Or.inl ((ZMod.val_eq_zero a).mp hval)
  · exact Or.inr ((ZMod.val_eq_one (by omega) a).mp hval)

@[simp] lemma zmod_two_one_add_one : (1 + 1 : ZMod 2) = 0 := by
  decide

/-- The bi-infinite word `0011`, shifted by the point parameter `q`. -/
def coord (q n : ℤ) : Bool :=
  decide (2 ≤ (n + q) % 4)

/-- The adjacent-pair involution whose pairing is shifted by `q`. -/
def swapPoint (q n : ℤ) : ℤ :=
  if (n + q) % 2 = 0 then n + 1 else n - 1

lemma swapPoint_involutive (q n : ℤ) :
    swapPoint q (swapPoint q n) = n := by
  simp only [swapPoint]
  split_ifs <;> omega

/-- `swapPoint q` as a permutation of the integer orbit. -/
def swapPerm (q : ℤ) : Equiv.Perm ℤ where
  toFun := swapPoint q
  invFun := swapPoint q
  left_inv := swapPoint_involutive q
  right_inv := swapPoint_involutive q

@[simp] lemma swapPerm_apply (q n : ℤ) : swapPerm q n = swapPoint q n := rfl

@[simp] lemma swapPerm_mul_self (q : ℤ) : swapPerm q * swapPerm q = 1 := by
  ext n
  exact swapPoint_involutive q n

/-- The generator of `G` acts by `swapPerm q`. -/
def orbitPerm (q : ℤ) : G →* Equiv.Perm ℤ where
  toFun g := if g.toAdd = 0 then 1 else swapPerm q
  map_one' := by simp
  map_mul' := by
    intro g h
    rcases zmod_two_eq_zero_or_one g.toAdd with hg | hg <;>
      rcases zmod_two_eq_zero_or_one h.toAdd with hh | hh <;>
      simp [hg, hh]

@[simp] lemma orbitPerm_zero (q : ℤ) :
    orbitPerm q (Multiplicative.ofAdd 0) = 1 := by
  simp [orbitPerm]

@[simp] lemma orbitPerm_one (q : ℤ) :
    orbitPerm q (Multiplicative.ofAdd 1) = swapPerm q := by
  simp [orbitPerm]

/-- Equal radius-one windows force equal parity, and hence equal generator
displacements.  We phrase the conclusion directly as equality of the two
`swapPoint` displacements because this is the form used in `locality`. -/
lemma swap_displacement_of_sameWindow (q m n : ℤ)
    (h : SameWindow coord q 1 m n) :
    swapPoint q m - m = swapPoint q n - n := by
  have hmnext : (m + 1 + q) % 4 = ((m + q) % 4 + 1) % 4 := by
    rw [show m + 1 + q = (m + q) + 1 by ring, Int.add_emod]
    norm_num
  have hnnext : (n + 1 + q) % 4 = ((n + q) % 4 + 1) % 4 := by
    rw [show n + 1 + q = (n + q) + 1 by ring, Int.add_emod]
    norm_num
  have hmpar : ((m + q) % 4) % 2 = (m + q) % 2 :=
    Int.emod_emod_of_dvd (m + q) (by norm_num)
  have hnpar : ((n + q) % 4) % 2 = (n + q) % 2 :=
    Int.emod_emod_of_dvd (n + q) (by norm_num)
  have hzero := h 0 (by norm_num)
  have hone := h 1 (by norm_num)
  simp only [add_zero, coord] at hzero
  simp only [coord] at hone
  by_cases hm0 : 2 ≤ (m + q) % 4
  all_goals
    by_cases hn0 : 2 ≤ (n + q) % 4
  all_goals
    simp [hm0, hn0] at hzero
  all_goals
    by_cases hm1 : 2 ≤ (m + 1 + q) % 4
  all_goals
    by_cases hn1 : 2 ≤ (n + 1 + q) % 4
  all_goals
    simp [hm1, hn1] at hone
  all_goals
    simp only [swapPoint]
    -- The four length-three windows of `0011` are `100`, `001`, `011`,
    -- and `110`; consequently `hzero` and `hone` determine the parity.
    split_ifs <;> omega

/-- The symbolic orbit data for the period-four fixture. -/
def data : SymbolicOrbitData G where
  Alphabet := Bool
  alphabetFintype := inferInstance
  alphabetDecidableEq := inferInstance
  Point := ℤ
  coord := coord
  shift q x := q + x
  coord_shift := by
    intro q x n
    simp only [coord, add_assoc]
  orbitPerm := orbitPerm
  displacementBound := fun _ ↦ 1
  displacement_bound := by
    intro q g n
    rcases zmod_two_eq_zero_or_one g.toAdd with hg | hg
    · have hg' : g = 1 := by
        apply Multiplicative.ext
        simpa using hg
      subst g
      simp [orbitPerm]
    · have hg' : g = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa using hg
      subst g
      simp only [orbitPerm_one, swapPerm_apply, swapPoint]
      split_ifs <;> simp_all
  localityRadius := fun _ ↦ 1
  locality := by
    intro q g m n hwindow
    rcases zmod_two_eq_zero_or_one g.toAdd with hg | hg
    · have hg' : g = 1 := by
        apply Multiplicative.ext
        simpa using hg
      subst g
      simp [orbitPerm]
    · have hg' : g = Multiplicative.ofAdd 1 := by
        apply Multiplicative.ext
        simpa using hg
      subst g
      simpa [orbitPerm_one, swapPerm_apply] using
        swap_displacement_of_sameWindow q m n hwindow

/-- The sequence is globally periodic modulo four. -/
lemma coord_of_modEq (q i j : ℤ) (h : i ≡ j [ZMOD 4]) :
    coord q i = coord q j := by
  unfold coord
  rw [(Int.ModEq.add_right q h).eq]

/-- The full, axiom-free period-four interface instance. -/
def inputs : ExternalInputs.{0, 0, 0} G where
  data := PeriodFourModel.data
  halfLine_local_finite := by
    intro _ _ _
    exact Finite.of_injective Subtype.val Subtype.val_injective
  scaled_periodic_window := by
    intro E _
    refine ⟨(0 : ℤ), 4, 0, by norm_num, ?_⟩
    intro i j _ _ _ _ hij
    exact coord_of_modEq 0 i j hij

/-! ## Nonvacuity and convention fixtures -/

/-- At the base point, equal central symbols do not determine displacement:
positions `0` and `1` both carry `0`, but move in opposite directions. -/
example : coord 0 0 = coord 0 1 := by decide

example : swapPoint 0 0 - 0 = 1 := by decide

example : swapPoint 0 1 - 1 = -1 := by decide

/-- Thus radius zero is genuinely insufficient for the generator. -/
theorem radius_zero_fails :
    ¬ (∀ m n : ℤ, SameWindow coord 0 0 m n →
        swapPoint 0 m - m = swapPoint 0 n - n) := by
  intro h
  have hw : SameWindow coord 0 0 0 1 := by
    intro t ht
    have habs : |t| = 0 := le_antisymm ht (abs_nonneg t)
    have : t = 0 := abs_eq_zero.mp habs
    subst t
    decide
  have := h 0 1 hw
  norm_num [swapPoint] at this

/-- Radius one does determine the displacement everywhere. -/
theorem radius_one_works :
    ∀ m n : ℤ, SameWindow coord 0 1 m n →
      swapPoint 0 m - m = swapPoint 0 n - n := by
  intro m n
  exact swap_displacement_of_sameWindow 0 m n

/-- A concrete trajectory check used to guard the action convention. -/
example :
    swapPoint 0 (-4) = -3 ∧ swapPoint 0 (-3) = -4 ∧
      swapPoint 0 0 = 1 ∧ swapPoint 0 1 = 0 := by
  decide

end PeriodFourModel

end CollisionRank
