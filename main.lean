import axioms

set_option autoImplicit false

/-! Public statements, compiled as the independent Comparator challenge.
The seven intentional `sorry` bodies are placeholders for statements only.
Actual proofs are in proofs/ and are checked against these types; `sorryAx`
is forbidden in every solution declaration. See README.md for the exact checks. -/

namespace CollisionRank
universe u v w

/--
T01. For any group G, any nonempty finite A, any natural d, any subgroup H, and
any separation certificate c for A,d,H, the finite set of differences f*g^(-1)
of exact products with equal codes contains the identity and is closed under
inversion. A itself need not contain the identity or be inverse-closed.
-/
theorem certificateCollisionSet_isLabelSet {G : Type u} [Group G] {A : Finset G} {d : ℕ}
    {H : Subgroup G} (hA : A.Nonempty) (c : SeparationCertificate A d H) :
    IsLabelSet (certificateCollisionSet c) := by
  sorry

/--
T02. Let G be any group. Suppose every nonempty finite subset A has some natural
d and some locally finite subgroup H admitting a separation certificate for
A,d,H. Then every finite label set in G admits a two-stage fixed-tree chain
through label sets ending at {1}; equivalently, G has symmetric collision rank
at most two. The hypothesis is for every nonempty finite A, even those that are
not label sets. No named Sturmian assumptions are used.
-/
theorem abstractCore_symmetric {G : Type u} [Group G]
    (h : ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H)) :
    SymmetricCollisionRankAtMost G 2 := by
  sorry

/--
T03. Let G be any group with symbolic orbit data D, and let A be any nonempty
finite subset. Fix a point x and natural numbers M,rho,R,p,K. Assume p>=1 and
K>=1; all a in A have displacementBound(a)<=M and localityRadius(a)<=rho;
R=M*(K*p); and 2*M*K+2<2^K. Suppose x is p-periodic on the closed integer
interval [-(2*R+rho),2*R+rho]. Then there is a natural d with d+1=K*p and a
separation certificate for A,d and the setwise stabilizer of the nonnegative
half-line at x. This theorem needs neither local finiteness of that stabilizer
nor the full ExternalInputs hypotheses.
-/
theorem periodicSeparationCertificate {G : Type u} [Group G] (D : SymbolicOrbitData G) (A : Finset G) (hA : A.Nonempty)
    (x : D.Point) (M rho R p K : ℕ)
    (hp : 1 ≤ p) (hK : 1 ≤ K)
    (hM : ∀ a ∈ A, D.displacementBound a ≤ M)
    (hrho : ∀ a ∈ A, D.localityRadius a ≤ rho)
    (hR : R = M * (K * p))
    (hsmall : 2 * M * K + 2 < 2 ^ K)
    (hperiodic : PeriodicOn D.coord x p
      (-((2 * R + rho : ℕ) : ℤ)) ((2 * R + rho : ℕ) : ℤ)) :
    ∃ (d : ℕ), d + 1 = K * p ∧
      Nonempty
        (SeparationCertificate A d (D.halfLineStabilizer x)) := by
  sorry

/--
T04. For every group G and every value I of ExternalInputs G, G has symmetric
collision rank at most two. That is, every finite set containing the identity
and closed under inversion admits a two-stage fixed-tree chain through such sets
ending at {1}. The two external hypotheses are arguments packaged in I; this
generic theorem uses no project axioms.
-/
theorem relative_symmetric_rank_at_most_two {G : Type u} [Group G]
    (I : ExternalInputs G) : SymmetricCollisionRankAtMost G 2 := by
  sorry

/--
T05. For every group G equipped with ExternalInputs, and every finite A0
containing the identity and closed under inversion, there is a finite A1 with
these properties and a fixed-tree stage A0 to A1. There is also a finite A2 with
these properties, a fixed-tree stage A1 to A2, and A2={1}. Each stage explicitly
requires its source and target to be nonempty. For each stage there is a natural
depth parameter chosen before all source labelings; for each labeling there are
incomparable vertices v,w whose ordered difference path(v)*path(w)^(-1) lies in
the target. The geometric tree depth is the parameter plus one. Target sets do
not depend on the labeling. This is the expanded form of T04; it asserts an
upper bound, not exact rank two.
-/
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
  sorry

/--
T06. The carrier named SturmianGroup, equipped with the group structure supplied
by A02, has symmetric collision rank at most two. This follows using the
unproved data and structural assumptions A01-A05. Identification of that carrier
and data with a concrete Sturmian derived full group is external to this
formalization. No SG membership assumption is needed for this bound.
-/
theorem sturmian_symmetric_rank_at_most_two :
    SymmetricCollisionRankAtMost SturmianGroup 2 := by
  sorry

/--
T07. There exist a type G in universe zero and a group structure on that same
type such that G has symmetric collision rank at most two and the opaque
proposition InSG G is false for that structure. The rank bound comes from T06 
and uses A01-A05. The second conjunct is not derived: InSG has no defining 
properties, so A07 supplies it directly at the witness. T07 records a weakened,
conditional form of the paper's existence result: an upper bound of two,
without asserting finite generation, and with nonmembership supplied by A07.
This does not internally define SG or construct the actual Sturmian group,
and it does not claim rank exactly two.
-/
theorem exists_group_symmetric_rank_at_most_two_given_assumed_non_SG :
    ∃ (G : Type) (inst : Group G),
      @SymmetricCollisionRankAtMost G inst 2 ∧ ¬ @InSG G inst := by
  sorry

end CollisionRank
