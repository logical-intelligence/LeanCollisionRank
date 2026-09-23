import Mathlib

set_option autoImplicit false

/-!
# Collision trees and the abstract two-stage argument

This file contains no literature input.  It formalizes the finite trivalent
leaf certificates used in the companion paper, their transfer to the
incomparable-vertex relation, and the abstract separator argument.

The natural number `d` always denotes *one less* than the geometric depth.
Thus `Leaf 0` is the set of the three leaves at depth one, while `Leaf d` has
`3 * 2 ^ d` elements.
-/

namespace CollisionRank

universe u

variable {G : Type u} [Group G]

/-! ## Addresses and path products -/

/-- An edge is determined by its root branch and the binary address below it. -/
abbrev EdgeAddress := Fin 3 × List (Fin 2)

/--
A leaf of the complete rooted tree of geometric depth d+1 is a first branch
in Fin 3 followed by exactly d binary choices, represented as a function Fin d
-> Fin 2. The tree has 3*2^d leaves.
-/
abbrev Leaf (d : ℕ) := Fin 3 × (Fin d → Fin 2)

/-- A finite vertex other than the root.  Omitting the root does not change
the fixed-tree collision predicate, since the root is comparable with every
vertex and therefore can never be a witness. -/
structure Vertex (d : ℕ) where
  first : Fin 3
  tail : List (Fin 2)
  tail_length_le : tail.length ≤ d

/-- A total labeling of the infinite address space.  A depth-`d+1` stage reads
only addresses whose binary tail has length at most `d`. -/
abbrev EdgeLabeling (A : Finset G) := EdgeAddress → ↥A

/-- The edges which actually occur in the complete tree of geometric depth
`d + 1`. -/
abbrev FiniteEdgeAddress (d : ℕ) :=
  {e : EdgeAddress // e.2.length ≤ d}

/-- A labeling of precisely the finite tree used at a depth-`d+1` stage. -/
abbrev FiniteEdgeLabeling (A : Finset G) (d : ℕ) :=
  FiniteEdgeAddress d → ↥A

/-- Restrict a total address labeling to the finite depth-`d+1` tree. -/
def restrictLabeling {A : Finset G} (d : ℕ) (l : EdgeLabeling A) :
    FiniteEdgeLabeling A d :=
  fun e => l e.1

/-- Extend a finite tree labeling to the total address space, using a fixed
label away from the finite tree. -/
def extendFiniteLabeling {A : Finset G} {d : ℕ} (a₀ : ↥A)
    (l : FiniteEdgeLabeling A d) : EdgeLabeling A :=
  fun e => if he : e.2.length ≤ d then l ⟨e, he⟩ else a₀

/-- Exact words are indexed from the leaf toward the root. -/
abbrev ExactWord (A : Finset G) (h : ℕ) := Fin h → ↥A

/-- The list underlying an exact word. -/
def exactWordList {A : Finset G} {h : ℕ} (w : ExactWord A h) : List ↥A :=
  List.ofFn w

@[simp] theorem exactWordList_length {A : Finset G} {h : ℕ}
    (w : ExactWord A h) : (exactWordList w).length = h := by
  simp [exactWordList]

/-- Product of an exact word, in its stored leaf-to-root order. -/
def exactWordProduct {A : Finset G} {h : ℕ} (w : ExactWord A h) : G :=
  (List.ofFn (fun j => (w j : G))).prod

@[simp] theorem exactWordProduct_eq_list {A : Finset G} {h : ℕ}
    (w : ExactWord A h) :
    exactWordProduct w =
      (List.map (fun a : ↥A => (a : G)) (exactWordList w)).prod := by
  unfold exactWordProduct exactWordList
  rw [List.ofFn_comp']

/-- The finite set `A^h` of products of words having exactly `h` letters. -/
noncomputable def exactProducts (A : Finset G) (h : ℕ) : Finset G := by
  classical
  exact Finset.univ.image (fun w : ExactWord A h => exactWordProduct w)

/-- An element of `A^h`, carrying its membership proof. -/
abbrev ExactProduct (A : Finset G) (h : ℕ) := ↥(exactProducts A h)

theorem exists_exactWord_eq {A : Finset G} {h : ℕ}
    (f : ↥(exactProducts A h)) :
    ∃ w : ExactWord A h, exactWordProduct w = (f : G) := by
  classical
  rcases Finset.mem_image.mp f.2 with ⟨w, _, hw⟩
  exact ⟨w, hw⟩

/--
For a leaf v and j in Fin (d+1), return its first branch and the first d-j
entries of its binary tail. As j increases from zero to d, these addresses run
from the edge ending at v back to a root edge.
-/
def leafAddress {d : ℕ} (v : Leaf d) (j : Fin (d + 1)) : EdgeAddress :=
  (v.1, (List.ofFn v.2).take (d - j.1))

theorem leafAddress_tail_length_le {d : ℕ} (v : Leaf d)
    (j : Fin (d + 1)) : (leafAddress v j).2.length ≤ d := by
  change ((List.ofFn v.2).take (d - j.1)).length ≤ d
  rw [List.length_take]
  simp

/--
Read an edge labeling at the d+1 addresses in `leafAddress`, in increasing j order,
obtaining a word of exact length d+1 from the leaf toward the root.
-/
def leafWord {A : Finset G} {d : ℕ} (l : EdgeLabeling A) (v : Leaf d) :
    ExactWord A (d + 1) :=
  fun j => l (leafAddress v j)

/--
Multiply the labels along a root-to-leaf path in reverse order: if the
labels encountered from root to leaf are a1,...,a(d+1), the value is
a(d+1)*...*a1.
-/
def leafPathProduct {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Leaf d) : G :=
  exactWordProduct (leafWord l v)

/-- The path product computed from a labeling of only the finite tree. -/
def finiteLeafPathProduct {A : Finset G} {d : ℕ}
    (l : FiniteEdgeLabeling A d) (v : Leaf d) : G :=
  exactWordProduct (fun j => l ⟨leafAddress v j, leafAddress_tail_length_le v j⟩)

/-- The edge read at leaf-to-root index `j` along a nonroot vertex. -/
def vertexAddress {d : ℕ} (v : Vertex d) (j : Fin (v.tail.length + 1)) :
    EdgeAddress :=
  (v.first, v.tail.take (v.tail.length - j.1))

theorem vertexAddress_tail_length_le {d : ℕ} (v : Vertex d)
    (j : Fin (v.tail.length + 1)) : (vertexAddress v j).2.length ≤ d := by
  change (v.tail.take (v.tail.length - j.1)).length ≤ d
  rw [List.length_take]
  exact (Nat.min_le_right _ _).trans v.tail_length_le

/-- Product along a nonroot vertex, again in leaf-to-root order. -/
def vertexPathProduct {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Vertex d) : G :=
  (List.ofFn (fun j : Fin (v.tail.length + 1) =>
    (l (vertexAddress v j) : G))).prod

/-- The vertex path product computed from a labeling of only the finite tree. -/
def finiteVertexPathProduct {A : Finset G} {d : ℕ}
    (l : FiniteEdgeLabeling A d) (v : Vertex d) : G :=
  (List.ofFn (fun j : Fin (v.tail.length + 1) =>
    (l ⟨vertexAddress v j, vertexAddress_tail_length_le v j⟩ : G))).prod

@[simp] theorem finiteLeafPathProduct_restrictLabeling {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Leaf d) :
    finiteLeafPathProduct (restrictLabeling d l) v = leafPathProduct l v := by
  rfl

@[simp] theorem leafPathProduct_extendFiniteLabeling {A : Finset G} {d : ℕ}
    (a₀ : ↥A) (l : FiniteEdgeLabeling A d) (v : Leaf d) :
    leafPathProduct (extendFiniteLabeling a₀ l) v = finiteLeafPathProduct l v := by
  apply congrArg exactWordProduct
  funext j
  simp [leafWord, extendFiniteLabeling, leafAddress_tail_length_le]

@[simp] theorem finiteVertexPathProduct_restrictLabeling {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Vertex d) :
    finiteVertexPathProduct (restrictLabeling d l) v = vertexPathProduct l v := by
  rfl

@[simp] theorem vertexPathProduct_extendFiniteLabeling {A : Finset G} {d : ℕ}
    (a₀ : ↥A) (l : FiniteEdgeLabeling A d) (v : Vertex d) :
    vertexPathProduct (extendFiniteLabeling a₀ l) v = finiteVertexPathProduct l v := by
  unfold vertexPathProduct finiteVertexPathProduct
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  simp [extendFiniteLabeling, vertexAddress_tail_length_le]

/-- Embed a leaf as a vertex at maximal depth. -/
def leafToVertex {d : ℕ} (v : Leaf d) : Vertex d :=
  { first := v.1
    tail := List.ofFn v.2
    tail_length_le := by simp }

/-- Oriented ancestry between nonroot vertices. -/
def Ancestor {d : ℕ} (v w : Vertex d) : Prop :=
  v.first = w.first ∧ v.tail.IsPrefix w.tail

/-- The witness relation in the fixed-tree definition. -/
def Incomparable {d : ℕ} (v w : Vertex d) : Prop :=
  ¬ Ancestor v w ∧ ¬ Ancestor w v

/-! The following three structural tests distinguish incomparability from
mere inequality.  They deliberately use geometric depth two, where a proper
ancestor pair exists. -/

/-- A proper ancestor pair consists of distinct vertices which are not
incomparable.  This fails if `Incomparable` is weakened to mere inequality. -/
theorem properAncestor_not_incomparable_test :
    ∃ v w : Vertex 1, v ≠ w ∧ ¬ Incomparable v w := by
  let v : Vertex 1 := ⟨0, [], by simp⟩
  let w : Vertex 1 := ⟨0, [0], by simp⟩
  refine ⟨v, w, by simp [v, w], ?_⟩
  simp [Incomparable, Ancestor, v, w]

/-- Vertices in different root branches are incomparable. -/
theorem incomparable_vertices_exist_test :
    ∃ v w : Vertex 1, Incomparable v w := by
  let v : Vertex 1 := ⟨0, [], by simp⟩
  let w : Vertex 1 := ⟨1, [], by simp⟩
  refine ⟨v, w, ?_⟩
  simp [Incomparable, Ancestor, v, w]

/-- Incomparability is irreflexive. -/
theorem incomparable_irrefl_test :
    ∀ v : Vertex 1, ¬ Incomparable v v := by
  intro v
  simp [Incomparable, Ancestor]

theorem leafPathProduct_mem_exactProducts {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Leaf d) :
    leafPathProduct l v ∈ exactProducts A (d + 1) := by
  classical
  exact Finset.mem_image.mpr ⟨leafWord l v, Finset.mem_univ _, rfl⟩

theorem leafToVertex_pathProduct {A : Finset G} {d : ℕ}
    (l : EdgeLabeling A) (v : Leaf d) :
    vertexPathProduct l (leafToVertex v) = leafPathProduct l v := by
  rcases v with ⟨i, b⟩
  simp [vertexPathProduct, vertexAddress, leafPathProduct, exactWordProduct,
    leafWord, leafAddress, leafToVertex]

theorem leafToVertex_incomparable_of_ne {d : ℕ} {v w : Leaf d}
    (hvw : v ≠ w) : Incomparable (leafToVertex v) (leafToVertex w) := by
  constructor
  · rintro ⟨hfirst, hprefix⟩
    apply hvw
    apply Prod.ext hfirst
    exact List.ofFn_injective
      (hprefix.eq_of_length (by simp [leafToVertex]))
  · rintro ⟨hfirst, hprefix⟩
    apply hvw
    apply Prod.ext hfirst.symm
    exact List.ofFn_injective
      (hprefix.eq_of_length (by simp [leafToVertex])).symm

/-! The first two convention checks.  These are deliberately public: a
change in address order should break them immediately. -/

theorem leafPathProduct_depth_one {A : Finset G} (l : EdgeLabeling A)
    (i : Fin 3) :
    leafPathProduct l (i, Fin.elim0) = (l (i, []) : G) := by
  simp [leafPathProduct, exactWordProduct, leafWord, leafAddress]

theorem leafPathProduct_depth_two {A : Finset G} (l : EdgeLabeling A)
    (i : Fin 3) (b : Fin 2) :
    leafPathProduct l (i, fun _ : Fin 1 => b) =
      (l (i, [b]) : G) * (l (i, []) : G) := by
  simp [leafPathProduct, exactWordProduct, leafWord, leafAddress]

/-- The same depth-two multiplication convention, stated directly for the
vertex path product used by `FixedStageAt`. -/
theorem vertexPathProduct_depth_two {A : Finset G} (l : EdgeLabeling A)
    (i : Fin 3) (b : Fin 2) :
    vertexPathProduct l
        ({ first := i, tail := [b], tail_length_le := by simp } : Vertex 1) =
      (l (i, [b]) : G) * (l (i, []) : G) := by
  simp [vertexPathProduct, vertexAddress]

/-- For an injective depth-one root labeling, equality of path products forces
equality of leaves.  The stage-level acceptance test below applies this lemma
directly to `LeafStageAt`. -/
theorem depth_one_pathMap_injective {A : Finset G} (a : Fin 3 → G)
    (ha : ∀ i, a i ∈ A) (hinj : Function.Injective a) :
    let l : EdgeLabeling A := fun e => ⟨a e.1, ha e.1⟩
    ∀ v w : Leaf 0,
      leafPathProduct l v * (leafPathProduct l w)⁻¹ = 1 → v = w := by
  dsimp
  intro v w h
  rcases v with ⟨i, vi⟩
  rcases w with ⟨j, vj⟩
  have hvi : vi = Fin.elim0 := Subsingleton.elim _ _
  have hvj : vj = Fin.elim0 := Subsingleton.elim _ _
  subst vi
  subst vj
  have hp : a i = a j := by
    apply eq_of_mul_inv_eq_one
    simpa only [leafPathProduct_depth_one] using h
  apply Prod.ext (hinj hp)
  exact Subsingleton.elim _ _

/-! ## One-stage relations -/

/--
At a specified parameter d (geometric depth d+1), every total A-labeling
has two distinct leaves v,w such that path(v)*path(w)^(-1) lies in B. The pair
is ordered. Nonemptiness of A and B is not imposed by this raw predicate.
-/
def LeafStageAt (d : ℕ) (A B : Finset G) : Prop :=
  ∀ l : EdgeLabeling A, ∃ v w : Leaf d,
    v ≠ w ∧ leafPathProduct l v * (leafPathProduct l w)⁻¹ ∈ B

/--
A and B are nonempty finite sets, and there exists a single natural d such
that every A-labeling has the distinct-leaf collision into B specified by `LeafStageAt`.
The depth is chosen before the labeling; the leaves may depend on the labeling.
-/
def LeafStage (A B : Finset G) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ ∃ d : ℕ, LeafStageAt d A B

/-- Raw incomparable-vertex predicate at geometric depth `d + 1`. -/
def FixedStageAt (d : ℕ) (A B : Finset G) : Prop :=
  ∀ l : EdgeLabeling A, ∃ v w : Vertex d,
    Incomparable v w ∧
      vertexPathProduct l v * (vertexPathProduct l w)⁻¹ ∈ B

/-- The leaf-stage predicate using labelings of precisely the finite tree. -/
def FiniteLeafStageAt (d : ℕ) (A B : Finset G) : Prop :=
  ∀ l : FiniteEdgeLabeling A d, ∃ v w : Leaf d,
    v ≠ w ∧ finiteLeafPathProduct l v * (finiteLeafPathProduct l w)⁻¹ ∈ B

/-- The incomparable-vertex predicate using labelings of precisely the finite
tree. -/
def FiniteFixedStageAt (d : ℕ) (A B : Finset G) : Prop :=
  ∀ l : FiniteEdgeLabeling A d, ∃ v w : Vertex d,
    Incomparable v w ∧
      finiteVertexPathProduct l v * (finiteVertexPathProduct l w)⁻¹ ∈ B

/-- Total labelings are faithful to finite tree labelings for leaf stages.
The only use of `A.Nonempty` is to choose an irrelevant label outside the
finite tree. -/
theorem leafStageAt_iff_finiteLeafStageAt {d : ℕ} {A B : Finset G}
    (hA : A.Nonempty) : LeafStageAt d A B ↔ FiniteLeafStageAt d A B := by
  constructor
  · intro htotal l
    obtain ⟨a, ha⟩ := hA
    let a₀ : ↥A := ⟨a, ha⟩
    obtain ⟨v, w, hvw, hB⟩ := htotal (extendFiniteLabeling a₀ l)
    exact ⟨v, w, hvw, by simpa using hB⟩
  · intro hfinite l
    obtain ⟨v, w, hvw, hB⟩ := hfinite (restrictLabeling d l)
    exact ⟨v, w, hvw, by simpa using hB⟩

/-- Total labelings are faithful to finite tree labelings for fixed-tree
stages. -/
theorem fixedStageAt_iff_finiteFixedStageAt {d : ℕ} {A B : Finset G}
    (hA : A.Nonempty) : FixedStageAt d A B ↔ FiniteFixedStageAt d A B := by
  constructor
  · intro htotal l
    obtain ⟨a, ha⟩ := hA
    let a₀ : ↥A := ⟨a, ha⟩
    obtain ⟨v, w, hvw, hB⟩ := htotal (extendFiniteLabeling a₀ l)
    exact ⟨v, w, hvw, by simpa using hB⟩
  · intro hfinite l
    obtain ⟨v, w, hvw, hB⟩ := hfinite (restrictLabeling d l)
    exact ⟨v, w, hvw, by simpa using hB⟩

/-- A genuinely stage-level depth-one test: an injective assignment to the
three root edges prevents a collision with target `{1}`.  Unlike the path-map
lemma above, this theorem fails immediately if the `v ≠ w` requirement is
removed from `LeafStageAt`. -/
theorem not_leafStageAt_zero_singleton_of_injective {A : Finset G}
    (a : Fin 3 → G) (ha : ∀ i, a i ∈ A) (hinj : Function.Injective a) :
    ¬ LeafStageAt 0 A ({1} : Finset G) := by
  intro hstage
  let l : EdgeLabeling A := fun e => ⟨a e.1, ha e.1⟩
  obtain ⟨v, w, hvw, hB⟩ := hstage l
  have hidentity :
      leafPathProduct l v * (leafPathProduct l w)⁻¹ = 1 := by
    simpa using hB
  exact hvw (depth_one_pathMap_injective a ha hinj v w hidentity)

/-- Concrete acceptance test for the distinct-leaf requirement.  The three
root labels are the three distinct elements of the cyclic group of order
three. -/
theorem depth_one_distinct_leaf_acceptance_test :
    ¬ LeafStageAt (G := Multiplicative (ZMod 3)) 0
      (Finset.univ : Finset (Multiplicative (ZMod 3)))
      ({1} : Finset (Multiplicative (ZMod 3))) := by
  apply not_leafStageAt_zero_singleton_of_injective
    (a := fun i : Fin 3 => Multiplicative.ofAdd (ZMod.finEquiv 3 i))
  · intro i
    simp
  · exact Multiplicative.ofAdd.injective.comp (ZMod.finEquiv 3).injective

/-- At geometric depth one, the vertex path product is just the label of the
corresponding root edge. -/
theorem vertexPathProduct_depth_one {A : Finset G} (l : EdgeLabeling A)
    (v : Vertex 0) :
    vertexPathProduct l v = (l (v.first, []) : G) := by
  rcases v with ⟨i, t, ht⟩
  have htail : t = [] := by
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero ht)
  subst t
  simp [vertexPathProduct, vertexAddress]

/-- For an injective depth-one root labeling, equality of vertex path products
forces equality of vertices. -/
theorem depth_one_vertex_pathMap_injective {A : Finset G} (a : Fin 3 → G)
    (ha : ∀ i, a i ∈ A) (hinj : Function.Injective a) :
    let l : EdgeLabeling A := fun e => ⟨a e.1, ha e.1⟩
    ∀ v w : Vertex 0,
      vertexPathProduct l v * (vertexPathProduct l w)⁻¹ = 1 → v = w := by
  dsimp
  intro v w h
  have hp : a v.first = a w.first := by
    apply eq_of_mul_inv_eq_one
    simpa only [vertexPathProduct_depth_one] using h
  rcases v with ⟨vi, vt, hvt⟩
  rcases w with ⟨wi, wt, hwt⟩
  have hi : vi = wi := hinj hp
  subst wi
  have hvt_nil : vt = [] :=
    List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hvt)
  have hwt_nil : wt = [] :=
    List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hwt)
  subst vt
  subst wt
  rfl

/-- A direct fixed-stage depth-one test.  In particular, this theorem fails if
the `Incomparable` requirement is removed from `FixedStageAt`, since then one
could choose the same vertex twice. -/
theorem not_fixedStageAt_zero_singleton_of_injective {A : Finset G}
    (a : Fin 3 → G) (ha : ∀ i, a i ∈ A) (hinj : Function.Injective a) :
    ¬ FixedStageAt 0 A ({1} : Finset G) := by
  intro hstage
  let l : EdgeLabeling A := fun e => ⟨a e.1, ha e.1⟩
  obtain ⟨v, w, hinc, hB⟩ := hstage l
  have hidentity :
      vertexPathProduct l v * (vertexPathProduct l w)⁻¹ = 1 := by
    simpa using hB
  have hvw := depth_one_vertex_pathMap_injective a ha hinj v w hidentity
  subst w
  exact hinc.1 (by simp [Ancestor])

/-- Concrete acceptance test protecting the witness relation appearing in the
public fixed-tree collision rank. -/
theorem fixedStageAt_zero_acceptance_test :
    ¬ FixedStageAt (G := Multiplicative (ZMod 3)) 0
      (Finset.univ : Finset (Multiplicative (ZMod 3)))
      ({1} : Finset (Multiplicative (ZMod 3))) := by
  apply not_fixedStageAt_zero_singleton_of_injective
    (a := fun i : Fin 3 => Multiplicative.ofAdd (ZMod.finEquiv 3 i))
  · intro i
    simp
  · exact Multiplicative.ofAdd.injective.comp (ZMod.finEquiv 3).injective

/-- Auxiliary unrestricted fixed-tree relation on finite nonempty sets.
The paper-facing symmetric rank predicate restricts every source and target
to a label set. -/
def FixedStage (A B : Finset G) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ ∃ d : ℕ, FixedStageAt d A B

theorem leafStageAt_to_fixedStageAt {d : ℕ} {A B : Finset G}
    (h : LeafStageAt d A B) : FixedStageAt d A B := by
  intro l
  obtain ⟨v, w, hvw, hB⟩ := h l
  refine ⟨leafToVertex v, leafToVertex w,
    leafToVertex_incomparable_of_ne hvw, ?_⟩
  simpa [leafToVertex_pathProduct] using hB

theorem leafStage_to_fixedStage {A B : Finset G}
    (h : LeafStage A B) : FixedStage A B := by
  rcases h with ⟨hA, hB, d, hd⟩
  exact ⟨hA, hB, d, leafStageAt_to_fixedStageAt hd⟩

/-- Constant labelings show that a leaf stage cannot avoid the identity. -/
theorem leaf_guard {A B : Finset G} (hA : A.Nonempty) (h1 : 1 ∉ B) :
    ¬ LeafStage A B := by
  intro hstage
  rcases hstage with ⟨_, _, d, hd⟩
  obtain ⟨a, ha⟩ := hA
  let l : EdgeLabeling A := fun _ => ⟨a, ha⟩
  obtain ⟨v, w, _, hB⟩ := hd l
  have hp : leafPathProduct l v = leafPathProduct l w := by
    rfl
  rw [hp] at hB
  exact h1 (by simpa using hB)

/-- The fixed-tree analogue of the guard uses the identity labeling.  Unlike
the leaf guard, a constant nonidentity label is not sufficient because
incomparable vertices may have different depths. -/
theorem fixed_guard {A B : Finset G} (h1A : 1 ∈ A) (h1B : 1 ∉ B) :
    ¬ FixedStage A B := by
  intro hstage
  rcases hstage with ⟨_, _, d, hd⟩
  let l : EdgeLabeling A := fun _ => ⟨1, h1A⟩
  obtain ⟨v, w, _, hB⟩ := hd l
  have hv : vertexPathProduct l v = 1 := by
    simp [vertexPathProduct, l]
  have hw : vertexPathProduct l w = 1 := by
    simp [vertexPathProduct, l]
  rw [hv, hw] at hB
  exact h1B (by simpa using hB)

theorem singleton_leafStage :
    LeafStage ({1} : Finset G) ({1} : Finset G) := by
  classical
  refine ⟨by simp, by simp, 0, ?_⟩
  intro l
  let v : Leaf 0 := (0, Fin.elim0)
  let w : Leaf 0 := (1, Fin.elim0)
  refine ⟨v, w, ?_, ?_⟩
  · intro hvw
    have hfirst := congrArg Prod.fst hvw
    norm_num [v, w] at hfirst
  · have hl (e : EdgeAddress) : (l e : G) = 1 := by
      exact Finset.mem_singleton.mp (l e).2
    simp [leafPathProduct, exactWordProduct, leafWord, hl]

theorem singleton_fixedStage :
    FixedStage ({1} : Finset G) ({1} : Finset G) :=
  leafStage_to_fixedStage singleton_leafStage

/-! ## Recursive rank predicates -/

/--
An exact r-stage chain of leaf stages starting at A and ending at {1}. At
r=0 this means A={1}; at r+1 there is a finite nonempty B with a leaf stage from
A to B and an exact r-stage chain from B. No symmetry is required.
-/
def LeafReducesIn : ℕ → Finset G → Prop
  | 0, A => A = {1}
  | r + 1, A => ∃ B : Finset G,
      B.Nonempty ∧ LeafStage A B ∧ LeafReducesIn r B

/--
An exact r-stage chain of fixed-tree stages starting at A and ending at
{1}. At r=0 this means A={1}; at r+1 there is a finite nonempty B with a
fixed-tree stage from A to B and an exact r-stage chain from B. No symmetry is
required.
-/
def FixedReducesIn : ℕ → Finset G → Prop
  | 0, A => A = {1}
  | r + 1, A => ∃ B : Finset G,
      B.Nonempty ∧ FixedStage A B ∧ FixedReducesIn r B

def LeafCollisionRankAtMost (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ A : Finset G, A.Nonempty → LeafReducesIn r A

/--
Every finite nonempty subset A of the given group has an exact r-stage
fixed-tree chain ending at {1}, as in `FixedReducesIn`. This is the unrestricted auxiliary
rank. The proved padding lemma fixedReducesIn_padding makes shorter chains
extendible, justifying the name "at most".
-/
def FixedCollisionRankAtMost (G : Type u) [Group G] (r : ℕ) : Prop :=
  ∀ A : Finset G, A.Nonempty → FixedReducesIn r A

/-- Rank zero is genuinely nontrivial: a nontrivial group has a nonidentity
singleton which does not reduce in zero stages. -/
theorem not_fixedCollisionRankAtMost_zero [Nontrivial G] :
    ¬ FixedCollisionRankAtMost G 0 := by
  intro hrank
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hred : FixedReducesIn 0 ({g} : Finset G) := hrank {g} (by simp)
  have heq : ({g} : Finset G) = {1} := by
    simpa [FixedReducesIn] using hred
  have hg_mem : g ∈ ({1} : Finset G) := by
    rw [← heq]
    simp
  exact hg (by simpa using hg_mem)

theorem leafReducesIn_padding {r : ℕ} {A : Finset G}
    (h : LeafReducesIn r A) : LeafReducesIn (r + 1) A := by
  induction r generalizing A with
  | zero =>
      simp only [LeafReducesIn] at h ⊢
      subst A
      exact ⟨{1}, by simp, singleton_leafStage, rfl⟩
  | succ r ih =>
      simp only [LeafReducesIn] at h ⊢
      rcases h with ⟨B, hB, hAB, hred⟩
      exact ⟨B, hB, hAB, ih hred⟩

theorem fixedReducesIn_padding {r : ℕ} {A : Finset G}
    (h : FixedReducesIn r A) : FixedReducesIn (r + 1) A := by
  induction r generalizing A with
  | zero =>
      simp only [FixedReducesIn] at h ⊢
      subst A
      exact ⟨{1}, by simp, singleton_fixedStage, rfl⟩
  | succ r ih =>
      simp only [FixedReducesIn] at h ⊢
      rcases h with ⟨B, hB, hAB, hred⟩
      exact ⟨B, hB, hAB, ih hred⟩

theorem leafReducesIn_to_fixedReducesIn {r : ℕ} {A : Finset G}
    (h : LeafReducesIn r A) : FixedReducesIn r A := by
  induction r generalizing A with
  | zero => simpa [LeafReducesIn, FixedReducesIn] using h
  | succ r ih =>
      simp only [LeafReducesIn] at h
      simp only [FixedReducesIn]
      rcases h with ⟨B, hB, hAB, hred⟩
      exact ⟨B, hB, leafStage_to_fixedStage hAB, ih hred⟩

theorem leafRankAtMost_to_fixedRankAtMost {r : ℕ}
    (h : LeafCollisionRankAtMost G r) : FixedCollisionRankAtMost G r := by
  intro A hA
  exact leafReducesIn_to_fixedReducesIn (h A hA)

/-! ## Finite separating certificates -/

/-- The local-finiteness formulation used by the two-stage proof: the subgroup
generated by every finite subset of `H` is finite. -/
def LocallyFiniteSubgroup (H : Subgroup G) : Prop :=
  ∀ C : Finset G, (∀ g ∈ C, g ∈ H) →
    Finite ↥(Subgroup.closure (↑C : Set G))

/-- A finite code on exact products whose equal fibers differ inside `H`. -/
structure SeparationCertificate (A : Finset G) (d : ℕ) (H : Subgroup G) where
  Code : Type
  [codeFintype : Fintype Code]
  code : ↥(exactProducts A (d + 1)) → Code
  card_lt : Fintype.card Code < 3 * 2 ^ d
  separates : ∀ f g, code f = code g → (f : G) * (g : G)⁻¹ ∈ H

/-- Differences of pairs in the same code fiber. -/
noncomputable def certificateCollisionSet {A : Finset G} {d : ℕ}
    {H : Subgroup G} (c : SeparationCertificate A d H) : Finset G := by
  classical
  let P := ↥(exactProducts A (d + 1))
  exact (Finset.univ.filter (fun z : P × P => c.code z.1 = c.code z.2)).image
    (fun z => (z.1 : G) * (z.2 : G)⁻¹)

/-- The named orientation lemma for the collision set. -/
theorem certificateCollisionSet_mem {A : Finset G} {d : ℕ}
    {H : Subgroup G} (c : SeparationCertificate A d H)
    (f g : ExactProduct A (d + 1)) (hcode : c.code f = c.code g) :
    (f : G) * (g : G)⁻¹ ∈ certificateCollisionSet c := by
  classical
  refine Finset.mem_image.mpr ⟨(f, g), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcode⟩

theorem exactProducts_nonempty {A : Finset G} (hA : A.Nonempty) (h : ℕ) :
    (exactProducts A h).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := hA
  let w : ExactWord A h := fun _ => ⟨a, ha⟩
  exact ⟨exactWordProduct w,
    Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩⟩

theorem certificateCollisionSet_nonempty {A : Finset G} {d : ℕ}
    {H : Subgroup G} (hA : A.Nonempty) (c : SeparationCertificate A d H) :
    (certificateCollisionSet c).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := exactProducts_nonempty (G := G) hA (d + 1)
  let f : ↥(exactProducts A (d + 1)) := ⟨x, hx⟩
  refine ⟨1, ?_⟩
  refine Finset.mem_image.mpr ⟨(f, f), ?_, by simp⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem certificateCollisionSet_subset {A : Finset G} {d : ℕ}
    {H : Subgroup G} (c : SeparationCertificate A d H) :
    ∀ g ∈ certificateCollisionSet c, g ∈ H := by
  classical
  intro g hg
  rcases Finset.mem_image.mp hg with ⟨z, hz, rfl⟩
  have hcode := (Finset.mem_filter.mp hz).2
  exact c.separates z.1 z.2 hcode

private theorem leaf_card (d : ℕ) : Fintype.card (Leaf d) = 3 * 2 ^ d := by
  simp [Leaf, Fintype.card_prod]

theorem leafStage_of_certificate {A : Finset G} {d : ℕ} {H : Subgroup G}
    (hA : A.Nonempty) (c : SeparationCertificate A d H) :
    LeafStage A (certificateCollisionSet c) := by
  classical
  letI : Fintype c.Code := c.codeFintype
  refine ⟨hA, certificateCollisionSet_nonempty hA c, d, ?_⟩
  intro l
  let codeLeaf : Leaf d → c.Code := fun v =>
    c.code ⟨leafPathProduct l v, leafPathProduct_mem_exactProducts l v⟩
  have hcard : Fintype.card c.Code < Fintype.card (Leaf d) := by
    simpa [leaf_card] using c.card_lt
  obtain ⟨v, w, hvw, hcode⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt codeLeaf hcard
  refine ⟨v, w, hvw, ?_⟩
  exact certificateCollisionSet_mem c
    ⟨leafPathProduct l v, leafPathProduct_mem_exactProducts l v⟩
    ⟨leafPathProduct l w, leafPathProduct_mem_exactProducts l w⟩ hcode

theorem leafPathProduct_mem_subgroup {C : Finset G} {d : ℕ}
    {F : Subgroup G} (hCF : ∀ g ∈ C, g ∈ F)
    (l : EdgeLabeling C) (v : Leaf d) : leafPathProduct l v ∈ F := by
  change (List.ofFn (fun j : Fin (d + 1) =>
    (l (leafAddress v j) : G))).prod ∈ F
  refine list_prod_mem ?_
  rw [List.forall_mem_ofFn_iff]
  intro j
  exact hCF _ (l (leafAddress v j)).2

private theorem card_lt_leaf_card (n : ℕ) : n < Fintype.card (Leaf n) := by
  rw [leaf_card]
  have hpow : n < 2 ^ n := Nat.lt_two_pow_self
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  omega

theorem leafStage_singleton_of_finite_subgroup {C : Finset G}
    (hC : C.Nonempty) (F : Subgroup G) (hfinite : Finite F)
    (hCF : ∀ g ∈ C, g ∈ F) : LeafStage C ({1} : Finset G) := by
  classical
  letI : Finite F := hfinite
  letI : Fintype F := Fintype.ofFinite F
  let n := Fintype.card F
  refine ⟨hC, by simp, n, ?_⟩
  intro l
  let value : Leaf n → F := fun v =>
    ⟨leafPathProduct l v, leafPathProduct_mem_subgroup hCF l v⟩
  obtain ⟨v, w, hvw, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt value (card_lt_leaf_card n)
  refine ⟨v, w, hvw, ?_⟩
  have hp : leafPathProduct l v = leafPathProduct l w :=
    congrArg Subtype.val heq
  simp [hp]

/-- The abstract core of the paper: a small finite separating code whose
fibers differ in a locally finite subgroup gives two leaf-collision stages. -/
theorem abstractCore
    (h : ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H)) :
    LeafCollisionRankAtMost G 2 := by
  intro A hA
  obtain ⟨d, H, hlocal, hc⟩ := h A hA
  let c : SeparationCertificate A d H := hc.some
  let C : Finset G := certificateCollisionSet c
  have hC : C.Nonempty := certificateCollisionSet_nonempty hA c
  have hCH : ∀ g ∈ C, g ∈ H := certificateCollisionSet_subset c
  let F : Subgroup G := Subgroup.closure (↑C : Set G)
  have hfinite : Finite F := by
    simpa [F] using hlocal C hCH
  have hCF : ∀ g ∈ C, g ∈ F := by
    intro g hg
    exact Subgroup.subset_closure hg
  have hAC : LeafStage A C := leafStage_of_certificate hA c
  have hC1 : LeafStage C ({1} : Finset G) :=
    leafStage_singleton_of_finite_subgroup hC F hfinite hCF
  exact ⟨C, hC, hAC, ⟨{1}, by simp, hC1, rfl⟩⟩

theorem abstractCore_fixed
    (h : ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H)) :
    FixedCollisionRankAtMost G 2 :=
  leafRankAtMost_to_fixedRankAtMost (abstractCore h)

end CollisionRank
