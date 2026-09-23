import Mathlib

set_option autoImplicit false

/-! Public reference definitions used by the main statements and external axioms.
This file imports only Mathlib. The implementation, including auxiliary definitions,
is under proofs/. -/

namespace CollisionRank
universe u v w
variable {G : Type u} [Group G]

/--
D01. An edge address consists of one of three first branches and a finite list
of binary branches. The empty list addresses a root edge; a tail of length k
addresses an edge ending at geometric depth k+1.
-/
abbrev EdgeAddress := Fin 3 × List (Fin 2)

/--
D02. A vertex other than the root in the tree of geometric depth d+1 consists of
a first branch in Fin 3, a finite binary tail, and a proof that its length is at
most d. Its geometric depth is tail.length+1. The root cannot witness
incomparability and is omitted.
-/
structure Vertex (d : ℕ) where
  first : Fin 3
  tail : List (Fin 2)
  tail_length_le : tail.length ≤ d

/--
D03. An A-labeling assigns to every edge address an element of the finite set A
(the subtype carries its membership proof). This is a total labeling of the
infinite address space. A depth-d+1 stage reads only addresses with tails of
length at most d.
-/
abbrev EdgeLabeling (A : Finset G) := EdgeAddress → ↥A

/--
D04. A word of exact length h over A is a function from Fin h to the elements of
A. No additional inverse letters are inserted; h may be zero.
-/
abbrev ExactWord (A : Finset G) (h : ℕ) := Fin h → ↥A

/--
D05. The product of an exact word w is w(0)*w(1)*...*w(h-1), in increasing index
order. At h=0 it is the identity. The group need not be commutative.
-/
def exactWordProduct {A : Finset G} {h : ℕ} (w : ExactWord A h) : G :=
  (List.ofFn (fun j => (w j : G))).prod

/--
D06. The finite set of group elements obtained as products of all words of exact
length h over A, in the order of D05. Equal products are identified by the
finite-set image. At h=0 this is {1}, including when A is empty.
-/
noncomputable def exactProducts (A : Finset G) (h : ℕ) : Finset G := by
  classical
  exact Finset.univ.image (fun w : ExactWord A h => exactWordProduct w)

/--
D07. For a non-root vertex v and j in Fin (v.tail.length+1), return the first
branch and the prefix of its tail of length v.tail.length-j. The addresses run
from the vertex back to a root edge.
-/
def vertexAddress {d : ℕ} (v : Vertex d) (j : Fin (v.tail.length + 1)) :
    EdgeAddress :=
  (v.first, v.tail.take (v.tail.length - j.1))

/--
D08. Multiply the edge labels on the path from the root to the non-root vertex v
in reverse order: the last edge label is the leftmost factor and the first edge
label the rightmost factor.
-/
def vertexPathProduct {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Vertex d) : G :=
  (List.ofFn (fun j : Fin (v.tail.length + 1) =>
    (l (vertexAddress v j) : G))).prod

/--
D09. v is an ancestor of w, allowing v=w, exactly when they have the same first
branch and the binary tail of v is a prefix of the tail of w.
-/
def Ancestor {d : ℕ} (v w : Vertex d) : Prop :=
  v.first = w.first ∧ v.tail.IsPrefix w.tail

/--
D10. Neither vertex is an ancestor of the other, with ancestry as in D09. In
particular, incomparable vertices are distinct.
-/
def Incomparable {d : ℕ} (v w : Vertex d) : Prop :=
  ¬ Ancestor v w ∧ ¬ Ancestor w v

/--
D11. At parameter d (geometric depth d+1), every total A-labeling has two
incomparable non-root vertices v,w with path(v)*path(w)^(-1) in B. Vertices may
have different depths. The pair is ordered; this raw predicate imposes no
nonemptiness or symmetry.
-/
def FixedStageAt (d : ℕ) (A B : Finset G) : Prop :=
  ∀ l : EdgeLabeling A, ∃ v w : Vertex d,
    Incomparable v w ∧
      vertexPathProduct l v * (vertexPathProduct l w)⁻¹ ∈ B

/--
D12. A and B are nonempty finite sets, and there is a natural d, chosen before
all labelings, such that D11 holds. Thus each labeling may have its own
incomparable witnesses, but all use the same tree depth and the same target B.
This predicate itself imposes neither identity membership nor inverse closure.
-/
def FixedStage (A B : Finset G) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ ∃ d : ℕ, FixedStageAt d A B

/--
D13. Every finite subset C of G whose elements lie in H generates a subgroup of
G with a finite carrier. The empty C is allowed. The definition does not assert
that H itself is finite.
-/
def LocallyFiniteSubgroup (H : Subgroup G) : Prop :=
  ∀ C : Finset G, (∀ g ∈ C, g ∈ H) →
    Finite ↥(Subgroup.closure (↑C : Set G))

/--
D14. A finite coding certificate at parameter d for A and subgroup H. Code is a
type in universe zero, codeFintype supplies a finite enumeration, and code
assigns a code to every element of exactProducts A (d+1). card_lt requires
strictly fewer than 3*2^d codes in the entire code type. separates states that
equal codes imply f*g^(-1) belongs to H. Neither a converse nor injectivity or
surjectivity of code is required.
-/
structure SeparationCertificate (A : Finset G) (d : ℕ) (H : Subgroup G) where
  Code : Type
  [codeFintype : Fintype Code]
  code : ↥(exactProducts A (d + 1)) → Code
  card_lt : Fintype.card Code < 3 * 2 ^ d
  separates : ∀ f g, code f = code g → (f : G) * (g : G)⁻¹ ∈ H

/--
D15. In one point x, the coordinate windows centered at integers m and n agree
at every integer offset t with |t| <= rho, including both endpoints. This
compares two positions within the same point, not different points.
-/
def SameWindow {X : Type v} {Sigma : Type w}
    (coord : X → ℤ → Sigma) (x : X) (rho : ℕ) (m n : ℤ) : Prop :=
  ∀ t : ℤ, |t| ≤ (rho : ℤ) → coord x (m + t) = coord x (n + t)

/--
D16. On the closed integer interval [lo,hi], any two positions i,j congruent
modulo the natural p have equal coordinates in x. This definition alone does not
require p>0 or a nonempty interval, and it does not assert global periodicity or
minimality of p.
-/
def PeriodicOn {X : Type v} {Sigma : Type w}
    (coord : X → ℤ → Sigma) (x : X) (p : ℕ) (lo hi : ℤ) : Prop :=
  ∀ i j : ℤ,
    lo ≤ i → i ≤ hi → lo ≤ j → j ≤ hi →
    i ≡ j [ZMOD (p : ℤ)] → coord x i = coord x j

/--
D17. Symbolic coordinates and bounded local permutation data for a group G.
Alphabet is a finite type with decidable equality; Point is an arbitrary type;
coord gives an integer-indexed coordinate sequence for each point. shift and
coord_shift give coord(shift q x,n)=coord(x,n+q). For each point, orbitPerm is a
group homomorphism into permutations of the integers. displacementBound(g)
bounds |orbitPerm(x,g,n)-n| uniformly over x,n. localityRadius(g) is uniform
over x,m,n: equal windows of that radius within x imply equal displacements at
m,n. Only the listed fields and laws are required. In particular, Point may be
empty, coordinates need not determine a point, the homomorphisms need not be
faithful, and no additional shift action law, cross-point locality, or
covariance of orbitPerm under shifts is supplied.
-/
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

namespace SymbolicOrbitData
variable (D : SymbolicOrbitData G)

/--
D18. For symbolic data D and a point x, the subgroup consisting of g such that
for every integer n, orbitPerm(x,g,n) is nonnegative if and only if n is
nonnegative. Thus it preserves {0,1,2,...} setwise. It need not fix these
integers individually. The law proofs below establish that this set is a
subgroup.
-/
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

end SymbolicOrbitData

/--
D19. The hypotheses for the relative theorem: symbolic orbit data plus two
properties. First, for every point x and every finite C contained in its
nonnegative-half-line stabilizer, the subgroup of G generated by C is finite.
Second, for every natural E>=1 there exist a point x, a natural p>=1, and an
integer a such that the coordinates are p-periodic on [a,a+p*E-1]. The interval
has p*E positions; x,p,a may all depend on E. A single common point or period
for all E, global periodicity, and finiteness of the entire stabilizer are not
asserted.
-/
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

/--
D20. For a certificate c, take all ordered pairs f,g of elements of
exactProducts A (d+1) having the same code, and form the finite set of their
oriented differences f*g^(-1). This uses equality of codes, not just the
condition f*g^(-1) in H. Each such difference lies in H by the certificate law,
but the larger set of all H-valued differences need not coincide with this set.
-/
noncomputable def certificateCollisionSet {A : Finset G} {d : ℕ}
    {H : Subgroup G} (c : SeparationCertificate A d H) : Finset G := by
  classical
  let P := ↥(exactProducts A (d + 1))
  exact (Finset.univ.filter (fun z : P × P => c.code z.1 = c.code z.2)).image
    (fun z => (z.1 : G) * (z.2 : G)⁻¹)

/--
D21. A finite label set contains the identity and is closed under inversion: for
every g in A, its inverse also lies in A. This implies nonemptiness, but does
not require closure under multiplication and does not make A a subgroup.
-/
def IsLabelSet (A : Finset G) : Prop :=
  (1 : G) ∈ A ∧ ∀ g ∈ A, g⁻¹ ∈ A

-- Generate this reference matcher independently, as in the implementation's
-- Symmetric module. This option only disables executable code generation for
-- auxiliary matchers; it leaves the logical definition available to the kernel.
set_option bootstrap.genMatcherCode false in
/--
D22. An exact r-stage chain of fixed-tree stages from A to {1}, with every
successive target set containing the identity and closed under inversion. At r=0
this means A={1}; at r+1 choose a finite label set B with FixedStage A B and an
exact r-stage chain from B. The initial A is not separately required to be a
label set by this predicate. D23 imposes that additional condition.
-/
def SymmetricReducesIn : ℕ → Finset G → Prop
  | 0, A => A = ({1} : Finset G)
  | r + 1, A => ∃ B : Finset G,
      IsLabelSet B ∧ FixedStage A B ∧ SymmetricReducesIn r B

/--
D23. For every finite subset A of the given group containing the identity and
closed under inversion, there is an exact r-stage fixed-tree chain from A to {1}
through sets with those same two properties. The recursive formula is
exact-length; symmetricReducesIn_padding, proved in proofs, extends shorter
chains, which justifies "rank at most r". The group and its chosen structure are
explicit parameters; no nontriviality, countability, or finite generation
assumption is made.
-/
def SymmetricCollisionRankAtMost (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ A : Finset G, IsLabelSet A → SymmetricReducesIn r A

end CollisionRank
