import CollisionRank.Periodic

set_option autoImplicit false

/-!
# Symmetric label sets and symmetric collision rank

The paper defines a *label set* to be a finite symmetric subset containing `1`,
and requires every set in a collision chain to be a label set.  Symmetry is
needed geometrically: reversing a double point loop inverts its label.

This file adds that specification layer on top of the existing development.
Nothing below changes the stage relation `FixedStage`, which remains defined
for arbitrary finite nonempty sets; symmetry is imposed at the level of the
rank predicate only.  Consequently none of `pairedWordInvariant`,
`periodicSeparationCertificate`, `periodicCoreWitness`, or `abstractCore` is
modified or reproved.

The mathematical content of the patch is that the collision set constructed by
the existing certificate,

  `C = {f * g⁻¹ : Φ f = Φ g}`,

is automatically a label set: `1 ∈ C` by taking `f = g`, and `C` is closed
under inversion because code equality is symmetric.
-/

namespace CollisionRank

universe u

variable {G : Type u} [Group G]

/-! ## Label sets -/

/-- A *label set*: a finite subset containing `1` and closed under inversion.
This is the paper's standing hypothesis on every set in a collision chain. -/
def IsLabelSet (A : Finset G) : Prop :=
  (1 : G) ∈ A ∧ ∀ g ∈ A, g⁻¹ ∈ A

theorem IsLabelSet.nonempty {A : Finset G} (h : IsLabelSet A) : A.Nonempty :=
  ⟨1, h.1⟩

theorem isLabelSet_singleton_one : IsLabelSet ({1} : Finset G) := by
  constructor
  · simp
  · intro g hg
    simp only [Finset.mem_singleton] at hg ⊢
    simp [hg]

/-! ### Specification tests for `IsLabelSet`

A specification predicate that is accidentally too weak need not be detected
by the axiom audit.  The following two negative instances in `ZMod 3` test the
two defining clauses separately; the positive control excludes an identically
false predicate.
In `ZMod 3` the inverse of `ofAdd 1` is `ofAdd 2`, so `{1, ofAdd 1}` satisfies
the identity clause but not symmetry, and `{ofAdd 1, ofAdd 2}` satisfies
symmetry but not the identity clause. -/

section LabelSetTests

/-- Fails if the inverse-closure clause is removed from `IsLabelSet`. -/
theorem isLabelSet_needs_symmetry :
    ¬ IsLabelSet
      ({1, Multiplicative.ofAdd (1 : ZMod 3)} :
        Finset (Multiplicative (ZMod 3))) := by
  unfold IsLabelSet
  decide

/-- Fails if the `1 ∈ A` clause is removed from `IsLabelSet`. -/
theorem isLabelSet_needs_one :
    ¬ IsLabelSet
      ({Multiplicative.ofAdd (1 : ZMod 3),
        Multiplicative.ofAdd (2 : ZMod 3)} :
        Finset (Multiplicative (ZMod 3))) := by
  unfold IsLabelSet
  decide

/-- Positive control: the predicate is not vacuously false. -/
theorem isLabelSet_univ_zmod_three :
    IsLabelSet (Finset.univ : Finset (Multiplicative (ZMod 3))) := by
  unfold IsLabelSet
  decide

end LabelSetTests

/-! ## The certificate collision set is a label set -/

/-- `1` lies in the collision set, by taking `f = g`. -/
theorem certificateCollisionSet_one_mem {A : Finset G} {d : ℕ}
    {H : Subgroup G} (hA : A.Nonempty) (c : SeparationCertificate A d H) :
    (1 : G) ∈ certificateCollisionSet c := by
  classical
  obtain ⟨x, hx⟩ := exactProducts_nonempty (G := G) hA (d + 1)
  have h := certificateCollisionSet_mem c ⟨x, hx⟩ ⟨x, hx⟩ rfl
  simpa using h

/-- The collision set is closed under inversion, because code equality is
symmetric: if `Φ f = Φ g` then `Φ g = Φ f`, and `(f * g⁻¹)⁻¹ = g * f⁻¹`. -/
theorem certificateCollisionSet_inv_mem {A : Finset G} {d : ℕ}
    {H : Subgroup G} (c : SeparationCertificate A d H) :
    ∀ g ∈ certificateCollisionSet c, g⁻¹ ∈ certificateCollisionSet c := by
  classical
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨z, hz, rfl⟩
  have hcode := (Finset.mem_filter.mp hz).2
  have hrev : ((z.1 : G) * (z.2 : G)⁻¹)⁻¹ = (z.2 : G) * (z.1 : G)⁻¹ := by
    simp [mul_inv_rev]
  rw [hrev]
  exact certificateCollisionSet_mem c z.2 z.1 hcode.symm

theorem certificateCollisionSet_isLabelSet {A : Finset G} {d : ℕ}
    {H : Subgroup G} (hA : A.Nonempty) (c : SeparationCertificate A d H) :
    IsLabelSet (certificateCollisionSet c) :=
  ⟨certificateCollisionSet_one_mem hA c, certificateCollisionSet_inv_mem c⟩

/-! ## The two-stage chain in label-set form -/

/-- The chain produced by the abstract core, with the intermediate set
retained and certified to be a label set.  The proof is the body of
`abstractCore`, stopping before the rank predicate discards `C`. -/
theorem abstractCore_chain
    (h : ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H))
    (A : Finset G) (hA : A.Nonempty) :
    ∃ C : Finset G,
      IsLabelSet C ∧ FixedStage A C ∧ FixedStage C ({1} : Finset G) := by
  classical
  obtain ⟨d, H, hlocal, hc⟩ := h A hA
  let c : SeparationCertificate A d H := hc.some
  let C : Finset G := certificateCollisionSet c
  have hlabel : IsLabelSet C := certificateCollisionSet_isLabelSet hA c
  have hC : C.Nonempty := hlabel.nonempty
  have hCH : ∀ g ∈ C, g ∈ H := certificateCollisionSet_subset c
  let F : Subgroup G := Subgroup.closure (↑C : Set G)
  have hfinite : Finite F := by
    simpa [F] using hlocal C hCH
  have hCF : ∀ g ∈ C, g ∈ F := fun g hg => Subgroup.subset_closure hg
  refine ⟨C, hlabel, ?_, ?_⟩
  · exact leafStage_to_fixedStage (leafStage_of_certificate hA c)
  · exact leafStage_to_fixedStage
      (leafStage_singleton_of_finite_subgroup hC F hfinite hCF)

/-! ## Symmetric collision rank -/

/-- `SymmetricReducesIn r A` records an exact `r`-stage chain from `A` to `{1}`
whose successive target sets are label sets.  When `A` is itself a label set,
as required by `SymmetricCollisionRankAtMost`, every set in the chain is a
label set. -/
def SymmetricReducesIn : ℕ → Finset G → Prop
  | 0, A => A = ({1} : Finset G)
  | r + 1, A => ∃ B : Finset G,
      IsLabelSet B ∧ FixedStage A B ∧ SymmetricReducesIn r B

/-- Every label set admits an exact `r`-stage chain through label sets ending
at `{1}`.  The padding lemma below allows shorter chains to be extended, so
this implements the paper's "rank at most `r`" convention. -/
def SymmetricCollisionRankAtMost (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ A : Finset G, IsLabelSet A → SymmetricReducesIn r A

/-- Append the stage `{1} ⇒ {1}` while retaining all label-set conditions. -/
theorem symmetricReducesIn_padding {r : ℕ} {A : Finset G}
    (h : SymmetricReducesIn r A) : SymmetricReducesIn (r + 1) A := by
  induction r generalizing A with
  | zero =>
      simp only [SymmetricReducesIn] at h ⊢
      subst A
      exact ⟨{1}, isLabelSet_singleton_one, singleton_fixedStage, rfl⟩
  | succ r ih =>
      simp only [SymmetricReducesIn] at h ⊢
      rcases h with ⟨B, hB, hAB, hred⟩
      exact ⟨B, hB, hAB, ih hred⟩

/-- A symmetric rank bound remains valid when the allowed number of stages
is increased by one. -/
theorem symmetricCollisionRankAtMost_succ {r : ℕ}
    (h : SymmetricCollisionRankAtMost G r) :
    SymmetricCollisionRankAtMost G (r + 1) := by
  intro A hA
  exact symmetricReducesIn_padding (h A hA)

/-- A nontrivial group does not have symmetric rank zero.  The witness is a
genuine label set `{1, g, g⁻¹}`, not a singleton. -/
theorem not_symmetricCollisionRankAtMost_zero [Nontrivial G] :
    ¬ SymmetricCollisionRankAtMost G 0 := by
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  intro hrank
  have hlabel : IsLabelSet ({1, g, g⁻¹} : Finset G) := by
    constructor
    · simp
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · simp
      · simp
      · simp
  have heq : ({1, g, g⁻¹} : Finset G) = ({1} : Finset G) :=
    hrank _ hlabel
  have hmem : g ∈ ({1, g, g⁻¹} : Finset G) := by simp
  rw [heq] at hmem
  simp only [Finset.mem_singleton] at hmem
  exact hg hmem

/-- The abstract core in symmetric form. -/
theorem abstractCore_symmetric
    (h : ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H)) :
    SymmetricCollisionRankAtMost G 2 := by
  intro A hA
  obtain ⟨C, hC, hAC, hC1⟩ := abstractCore_chain h A hA.nonempty
  exact ⟨C, hC, hAC, ⟨({1} : Finset G), isLabelSet_singleton_one, hC1, rfl⟩⟩

/-- The paper-facing relative theorem: the orbit interface implies symmetric
collision rank at most two.  Same hypothesis and same periodic-window proof as
`relative_fixed_rank_at_most_two`; only the packaging differs. -/
theorem relative_symmetric_rank_at_most_two {G : Type u} [Group G]
    (I : ExternalInputs G) : SymmetricCollisionRankAtMost G 2 :=
  abstractCore_symmetric (periodicCoreWitness I)

end CollisionRank
