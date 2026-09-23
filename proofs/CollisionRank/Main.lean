import CollisionRank.Axioms
import CollisionRank.Periodic
import CollisionRank.Symmetric
import CollisionRank.Regression

set_option autoImplicit false

/-!
# External Sturmian inputs and the final theorem

The paper-facing generic mathematical content is
`relative_symmetric_rank_at_most_two`: from an `ExternalInputs G` structure it
deduces symmetric collision rank at most two.  The earlier unrestricted
theorem `relative_fixed_rank_at_most_two` is retained as an auxiliary result.
The declarations concerning the named Sturmian group below form the intended
structural realization/literature boundary used to instantiate these theorems.

This project proves the upper bound only.  It does not formalize the lower
bound needed to conclude that the named Sturmian group has collision rank
exactly two, or the application to four-dimensional topology.

Membership in `SG` is deliberately not formalized internally.  The predicate
`InSG` and the assertion `sturmian_not_in_SG` are a separate opaque
classification boundary.  Thus the final existential theorem packages the
derived rank bound together with an externally supplied nonmembership claim;
its collision-rank content is already contained in the relative theorem.
-/

namespace CollisionRank

universe u

/-! ## Period-four regression model

The period-four model is not used in the Sturmian theorem.  It is an
axiom-free regression fixture intended to exercise the same interface and
relative pipeline in a concrete setting where locality is genuinely active.
-/

theorem periodFour_smoke :
    FixedCollisionRankAtMost (Multiplicative (ZMod 2)) 2 :=
  relative_fixed_rank_at_most_two PeriodFourModel.inputs

/-- The same regression instance run through the symmetric paper-facing
theorem.  Its axiom list must also contain only Lean's standard axioms. -/
theorem periodFour_symmetric_smoke :
    SymmetricCollisionRankAtMost (Multiplicative (ZMod 2)) 2 :=
  relative_symmetric_rank_at_most_two PeriodFourModel.inputs

/-! ## Expanded relative theorems -/

/-- The retained unrestricted rank-two conclusion with the recursive rank and
stage predicates fully unfolded.  For every finite nonempty initial set `A₀`,
it displays the intermediate and terminal finite sets, both tree depths, both
universal labeling quantifiers, the incomparable vertex pairs, the oriented
differences, and the final equality `A₂ = {1}`.  The paper-facing symmetric
statement follows below.

Only the address types, incomparability relation, and path-product functions
remain named; those are separately specified and regression-tested in
`CollisionRank.Collision`.  The one-line proof makes this declaration a
definitional restatement of `relative_fixed_rank_at_most_two`, rather than an
independent formulation that could drift away from the theorem used by Lean.
-/
theorem relative_fixed_rank_at_most_two_expanded
    {G : Type u} [Group G] (I : ExternalInputs G) :
    ∀ A₀ : Finset G, A₀.Nonempty →
      ∃ A₁ : Finset G,
        A₁.Nonempty ∧
        (A₀.Nonempty ∧ A₁.Nonempty ∧
          ∃ d₀ : ℕ,
            ∀ l₀ : EdgeLabeling A₀,
              ∃ v₀ w₀ : Vertex d₀,
                Incomparable v₀ w₀ ∧
                vertexPathProduct l₀ v₀ *
                    (vertexPathProduct l₀ w₀)⁻¹ ∈ A₁) ∧
        ∃ A₂ : Finset G,
          A₂.Nonempty ∧
          (A₁.Nonempty ∧ A₂.Nonempty ∧
            ∃ d₁ : ℕ,
              ∀ l₁ : EdgeLabeling A₁,
                ∃ v₁ w₁ : Vertex d₁,
                  Incomparable v₁ w₁ ∧
                  vertexPathProduct l₁ v₁ *
                      (vertexPathProduct l₁ w₁)⁻¹ ∈ A₂) ∧
          A₂ = ({1} : Finset G) := by
  simpa only [FixedCollisionRankAtMost, FixedReducesIn, FixedStage,
    FixedStageAt] using relative_fixed_rank_at_most_two I

/-- The paper-facing symmetric rank-two conclusion, with the recursive rank,
stage, and label-set predicates unfolded.  The identity and inverse-closure
conditions are displayed for the initial, intermediate, and terminal sets.
Only the tree addresses, incomparability relation, and path products remain
named.  The one-line proof makes this a definitional restatement of
`relative_symmetric_rank_at_most_two`. -/
theorem relative_symmetric_rank_at_most_two_expanded
    {G : Type u} [Group G] (I : ExternalInputs G) :
    ∀ A₀ : Finset G, ((1 : G) ∈ A₀ ∧ ∀ g ∈ A₀, g⁻¹ ∈ A₀) →
      ∃ A₁ : Finset G,
        ((1 : G) ∈ A₁ ∧ ∀ g ∈ A₁, g⁻¹ ∈ A₁) ∧
        (A₀.Nonempty ∧ A₁.Nonempty ∧
          ∃ d₀ : ℕ,
            ∀ l₀ : EdgeLabeling A₀,
              ∃ v₀ w₀ : Vertex d₀,
                Incomparable v₀ w₀ ∧
                vertexPathProduct l₀ v₀ *
                    (vertexPathProduct l₀ w₀)⁻¹ ∈ A₁) ∧
        ∃ A₂ : Finset G,
          ((1 : G) ∈ A₂ ∧ ∀ g ∈ A₂, g⁻¹ ∈ A₂) ∧
          (A₁.Nonempty ∧ A₂.Nonempty ∧
            ∃ d₁ : ℕ,
              ∀ l₁ : EdgeLabeling A₁,
                ∃ v₁ w₁ : Vertex d₁,
                  Incomparable v₁ w₁ ∧
                  vertexPathProduct l₁ v₁ *
                      (vertexPathProduct l₁ w₁)⁻¹ ∈ A₂) ∧
          A₂ = ({1} : Finset G) := by
  simpa only [SymmetricCollisionRankAtMost, SymmetricReducesIn, FixedStage,
    FixedStageAt, IsLabelSet] using relative_symmetric_rank_at_most_two I

/-! ## Named external Sturmian inputs -/













/-- The three collision-rank inputs assembled into one interface value. -/
noncomputable def sturmianInputs : ExternalInputs.{0, 0, 0} SturmianGroup where
  data := sturmianRealization
  halfLine_local_finite := sturmianHalfLineLocalFinite
  scaled_periodic_window := sturmianScaledPeriodicWindow





/-! ## Deductions from the stated structural inputs -/

theorem sturmian_leaf_rank_at_most_two :
    LeafCollisionRankAtMost SturmianGroup 2 :=
  relative_leaf_rank_at_most_two sturmianInputs

theorem sturmian_fixed_rank_at_most_two :
    FixedCollisionRankAtMost SturmianGroup 2 :=
  relative_fixed_rank_at_most_two sturmianInputs

/-- The paper-facing specialization: the named Sturmian group has symmetric
collision rank at most two. -/
theorem sturmian_symmetric_rank_at_most_two :
    SymmetricCollisionRankAtMost SturmianGroup 2 :=
  relative_symmetric_rank_at_most_two sturmianInputs

/-- The retained unrestricted existence theorem: some group outside `SG` has
unrestricted collision rank at most two.  The rank bound is the specialization
of the generic relative theorem above; the `SG` clause merely
appends the separate opaque assertion `sturmian_not_in_SG`.  This statement
does not assert the independent lower bound needed for exact rank two. -/
theorem exists_group_rank_at_most_two_not_in_SG :
    ∃ (G : Type) (inst : Group G),
      @FixedCollisionRankAtMost G inst 2 ∧ ¬ @InSG G inst := by
  exact ⟨SturmianGroup, sturmianGroupStructure,
    sturmian_fixed_rank_at_most_two, sturmian_not_in_SG⟩

/-- The paper-facing existence statement, in the symmetric formulation of the
final manuscript: some group outside `SG` has symmetric collision rank at most
two.  As above, the `SG` clause merely appends the separate opaque assertion
`sturmian_not_in_SG`; the verified content is the rank bound. -/
theorem exists_group_symmetric_rank_at_most_two_given_assumed_non_SG :
    ∃ (G : Type) (inst : Group G),
      @SymmetricCollisionRankAtMost G inst 2 ∧ ¬ @InSG G inst := by
  exact ⟨SturmianGroup, sturmianGroupStructure,
    sturmian_symmetric_rank_at_most_two, sturmian_not_in_SG⟩

/-! The centralized axiom audit is in `proofs/verification/Audit.lean`. -/

end CollisionRank
