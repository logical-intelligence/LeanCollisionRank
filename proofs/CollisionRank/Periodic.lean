import CollisionRank.Collision
import CollisionRank.Orbit

set_option autoImplicit false

/-!
# Periodic-window separator

This file connects the symbolic orbit interface to the abstract collision
core.  The definitions and elementary list lemmas are written out.
-/

namespace CollisionRank

universe u v w

variable {G : Type u} [Group G]

/-- Common displacement bound for a finite label set. -/
def commonDisplacement (D : SymbolicOrbitData G)
    (A : Finset G) : ℕ :=
  A.sup D.displacementBound

/-- Common locality radius for a finite label set. -/
def commonRadius (D : SymbolicOrbitData G)
    (A : Finset G) : ℕ :=
  A.sup D.localityRadius

theorem displacementBound_le_common {D : SymbolicOrbitData G}
    {A : Finset G} {g : G} (hg : g ∈ A) :
    D.displacementBound g ≤ commonDisplacement D A :=
  Finset.le_sup hg

theorem localityRadius_le_common {D : SymbolicOrbitData G}
    {A : Finset G} {g : G} (hg : g ∈ A) :
    D.localityRadius g ≤ commonRadius D A :=
  Finset.le_sup hg

theorem SameWindow.mono {X : Type v} {Sigma : Type w}
    {coord : X → ℤ → Sigma} {x : X} {r rho : ℕ} {m n : ℤ}
    (h : SameWindow coord x rho m n) (hr : r ≤ rho) :
    SameWindow coord x r m n := by
  intro t ht
  apply h t
  exact ht.trans (by exact_mod_cast hr)

/-! ## Word actions -/

/-- The tail acts first, matching `List.prod` and the leaf-to-root convention. -/
def wordAct (D : SymbolicOrbitData G) (x : D.Point) :
    List G → ℤ → ℤ
  | [], n => n
  | a :: word, n => D.orbitPerm x a (wordAct D x word n)

@[simp] theorem wordAct_nil (D : SymbolicOrbitData G) (x : D.Point) (n : ℤ) :
    wordAct D x [] n = n := rfl

@[simp] theorem wordAct_cons (D : SymbolicOrbitData G) (x : D.Point)
    (a : G) (word : List G) (n : ℤ) :
    wordAct D x (a :: word) n = D.orbitPerm x a (wordAct D x word n) := rfl

/-- Acting by a list agrees with acting by its group product. -/
theorem wordAct_eq_prod (D : SymbolicOrbitData G) (x : D.Point)
    (word : List G) (n : ℤ) :
    wordAct D x word n = D.orbitPerm x word.prod n := by
  induction word with
  | nil => simp [wordAct]
  | cons a word ih => simp [wordAct, ih]

/-- Global displacement grows at most linearly with word length. -/
theorem wordAct_displacement_bound (D : SymbolicOrbitData G)
    (x : D.Point) (word : List G) (M : ℕ)
    (hM : ∀ a ∈ word, D.displacementBound a ≤ M) (n : ℤ) :
    |wordAct D x word n - n| ≤ (M * word.length : ℕ) := by
  induction word generalizing n with
  | nil => simp [wordAct]
  | cons a word ih =>
      have ha : D.displacementBound a ≤ M := hM a (by simp)
      have htail : ∀ b ∈ word, D.displacementBound b ≤ M := by
        intro b hb
        exact hM b (by simp [hb])
      have hhead := D.displacement_bound x a (wordAct D x word n)
      have hrest := ih htail n
      calc
        |wordAct D x (a :: word) n - n| =
            |(D.orbitPerm x a (wordAct D x word n) - wordAct D x word n) +
              (wordAct D x word n - n)| := by
                congr 1
                simp [wordAct]
        _ ≤ |D.orbitPerm x a (wordAct D x word n) - wordAct D x word n| +
              |wordAct D x word n - n| := abs_add_le _ _
        _ ≤ (M : ℤ) + (M * word.length : ℕ) := by
              exact add_le_add
                (hhead.trans (by exact_mod_cast ha)) hrest
        _ = (M * (a :: word).length : ℕ) := by
              (simp only [List.length_cons, Nat.cast_mul, Nat.cast_add,
                Nat.cast_one]; ring)




/-- The strengthened induction invariant used in the periodic-window proof.

Its proof is ordinary structural induction on `word`, generalized over `m,n`; the tail
acts first, the global bound keeps both trajectories inside `[-2R,2R]`, and
locality handles the head letter.  The uniform bounds and the equation
`R = M * (K * p)` are explicit inputs, and congruence is carried by
`Int.ModEq` rather than by raw remainder equalities. -/
theorem pairedWordInvariant (D : SymbolicOrbitData G) (A : Finset G) (x : D.Point)
    (M rho R p K : ℕ) (hp : 1 ≤ p)
    (hM : ∀ a ∈ A, D.displacementBound a ≤ M)
    (hrho : ∀ a ∈ A, D.localityRadius a ≤ rho)
    (hR : R = M * (K * p))
    (hperiodic :
      PeriodicOn D.coord x p
        (-((2 * R + rho : ℕ) : ℤ)) ((2 * R + rho : ℕ) : ℤ))
    (word : List ↥A)
    (hlen : word.length ≤ K * p)
    (m n : ℤ)
    (hm : |m| ≤ (R : ℤ))
    (hn : |n| ≤ (R : ℤ))
    (hcong : Int.ModEq (p : ℤ) m n) :
    wordAct D x (word.map (fun a => (a : G))) m - m =
      wordAct D x (word.map (fun a => (a : G))) n - n := by
  induction word generalizing m n with
  | nil => simp
  | cons a word ih =>
      have hlen_cons : word.length + 1 ≤ K * p := by
        simpa only [List.length_cons] using hlen
      have hlen_tail : word.length ≤ K * p := by omega
      have htail := ih hlen_tail m n hm hn hcong
      have htail' :
          wordAct D x word.unattach m - m =
            wordAct D x word.unattach n - n := by
        simpa using htail
      have hM_tail :
          ∀ b ∈ word.unattach, D.displacementBound b ≤ M := by
        intro b hb
        have hb' : ∃ h : b ∈ A, (⟨b, h⟩ : ↥A) ∈ word := by
          simpa using hb
        rcases hb' with ⟨hbA, _⟩
        exact hM b hbA
      have hMR : M * word.length ≤ R := by
        calc
          M * word.length ≤ M * (K * p) := Nat.mul_le_mul_left M hlen_tail
          _ = R := hR.symm
      have hMR' : M * word.unattach.length ≤ R := by
        simpa using hMR
      have hdisp_m :
          |wordAct D x word.unattach m - m| ≤ (R : ℤ) := by
        have h := wordAct_displacement_bound D x word.unattach M hM_tail m
        exact h.trans (by exact_mod_cast hMR')
      have hdisp_n :
          |wordAct D x word.unattach n - n| ≤ (R : ℤ) := by
        have h := wordAct_displacement_bound D x word.unattach M hM_tail n
        exact h.trans (by exact_mod_cast hMR')
      have hm_lo := (abs_le.mp hm).1
      have hm_hi := (abs_le.mp hm).2
      have hn_lo := (abs_le.mp hn).1
      have hn_hi := (abs_le.mp hn).2
      have hdm_lo := (abs_le.mp hdisp_m).1
      have hdm_hi := (abs_le.mp hdisp_m).2
      have hdn_lo := (abs_le.mp hdisp_n).1
      have hdn_hi := (abs_le.mp hdisp_n).2
      have hm'_lo : -(((2 * R : ℕ) : ℤ)) ≤ wordAct D x word.unattach m := by
        push_cast
        omega
      have hm'_hi : wordAct D x word.unattach m ≤ ((2 * R : ℕ) : ℤ) := by
        push_cast
        omega
      have hn'_lo : -(((2 * R : ℕ) : ℤ)) ≤ wordAct D x word.unattach n := by
        push_cast
        omega
      have hn'_hi : wordAct D x word.unattach n ≤ ((2 * R : ℕ) : ℤ) := by
        push_cast
        omega
      have hcong' : Int.ModEq (p : ℤ)
          (wordAct D x word.unattach m) (wordAct D x word.unattach n) := by
        calc
          wordAct D x word.unattach m =
              m + (wordAct D x word.unattach m - m) := by ring
          _ ≡ n + (wordAct D x word.unattach m - m) [ZMOD (p : ℤ)] :=
            Int.ModEq.add_right _ hcong
          _ = wordAct D x word.unattach n := by
            rw [htail']
            ring
      have hwindow : SameWindow D.coord x rho
          (wordAct D x word.unattach m) (wordAct D x word.unattach n) := by
        intro t ht
        have ht_lo := (abs_le.mp ht).1
        have ht_hi := (abs_le.mp ht).2
        apply hperiodic
        · push_cast
          omega
        · push_cast
          omega
        · push_cast
          omega
        · push_cast
          omega
        · exact Int.ModEq.add_right t hcong'
      have hsame : SameWindow D.coord x (D.localityRadius (a : G))
          (wordAct D x word.unattach m) (wordAct D x word.unattach n) :=
        SameWindow.mono hwindow (hrho a a.property)
      have hlocal := D.locality x (a : G)
        (wordAct D x word.unattach m) (wordAct D x word.unattach n) hsame
      have hresult :
          D.orbitPerm x (a : G) (wordAct D x word.unattach m) - m =
            D.orbitPerm x (a : G) (wordAct D x word.unattach n) - n := by
        calc
          D.orbitPerm x (a : G) (wordAct D x word.unattach m) - m =
              (D.orbitPerm x (a : G) (wordAct D x word.unattach m) -
                wordAct D x word.unattach m) +
              (wordAct D x word.unattach m - m) := by ring
          _ = (D.orbitPerm x (a : G) (wordAct D x word.unattach n) -
                wordAct D x word.unattach n) +
              (wordAct D x word.unattach n - n) := by
                rw [hlocal, htail']
          _ = D.orbitPerm x (a : G) (wordAct D x word.unattach n) - n := by ring
      simpa [wordAct] using hresult

/-! ## Two reusable finite/arithmetic lemmas -/

/-- Two terminal filters of the same finite linear order are determined by
their cardinality. -/
theorem terminalFilter_eq_of_card_eq {alpha : Type*} [LinearOrder alpha]
    (s : Finset alpha) (a b : alpha)
    (hcard :
      (s.filter fun x => a ≤ x).card =
        (s.filter fun x => b ≤ x).card) :
    (s.filter fun x => a ≤ x) = (s.filter fun x => b ≤ x) := by
  classical
  rcases le_total a b with hab | hba
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hab.trans hx.2⟩
    · exact le_of_eq hcard
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hba.trans hx.2⟩
    · exact le_of_eq hcard.symm

theorem sq_le_two_pow_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by
        nlinarith
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := hstep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by
          simp [Nat.pow_add_one, Nat.mul_comm]

theorem highPower_base (M : ℕ) :
    2 * M * (2 * M + 4) + 2 < 2 ^ (2 * M + 4) := by
  let K := 2 * M + 4
  have hK : 4 ≤ K := by omega
  have hstrict : 2 * M * K + 2 < K ^ 2 := by
    dsimp [K]
    nlinarith
  exact hstrict.trans_le (sq_le_two_pow_of_four_le K hK)

theorem twoPow_succ_lt_three_mul (d : ℕ) :
    2 ^ (d + 1) < 3 * 2 ^ d := by
  simpa [Nat.pow_add_one, Nat.mul_comm] using
    Nat.mul_lt_mul_of_pos_right (show 2 < 3 by omega) (Nat.two_pow_pos d)

theorem recenter_gap (M K rho p : ℤ) :
    p * (4 * M * K + 2 * rho + 1) - 1
        - (2 * M * K * p + rho)
        - (2 * M * K * p + rho) =
      (p - 1) * (2 * rho + 1) := by
  ring

theorem recenter_right_bound (M K rho p : ℤ)
    (hrho : 0 ≤ rho) (hp : 1 ≤ p) :
    2 * M * K * p + rho ≤
      p * (4 * M * K + 2 * rho + 1) - 1
        - (2 * M * K * p + rho) := by
  have hp0 : 0 ≤ p - 1 := by omega
  have hrho0 : 0 ≤ 2 * rho + 1 := by omega
  have hprod : 0 ≤ (p - 1) * (2 * rho + 1) :=
    mul_nonneg hp0 hrho0
  nlinarith [recenter_gap M K rho p]

/-! ## From a periodic block to a finite separator -/

/-- Specialized periodic-window certificate.  The code is the vector, over
the `p` residue classes, of cardinalities of defect intersections with
`[-R,R]`.  The bound `2*M*K+2 < 2^K` is the only numerical input needed here.

The common bounds `M`, `rho`, and the derived radius `R` are explicit so that
the proof does not have to unfold nested `let` expressions in hypotheses.


-/
theorem periodicSeparationCertificate (D : SymbolicOrbitData G) (A : Finset G) (hA : A.Nonempty)
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
  classical
  letI : NeZero p := ⟨by omega⟩
  let h := K * p
  let d := h - 1
  have hh : 1 ≤ h := by
    dsimp [h]
    calc
      1 = 1 * 1 := by omega
      _ ≤ K * p := Nat.mul_le_mul hK hp
  have hd : d + 1 = h := by
    dsimp [d]
    exact Nat.sub_add_cancel hh
  refine ⟨d, hd, ?_⟩
  let fiber (r : Fin p) : Finset ℤ :=
    (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter
      (fun n => Int.ModEq (p : ℤ) n (r : ℤ))
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp
  have hspan : (2 * R : ℤ) = (2 * M * K : ℕ) * (p : ℤ) := by
    rw [hR]
    push_cast
    ring
  have fiber_card (r : Fin p) : (fiber r).card ≤ 2 * M * K + 1 := by
    let q : ℤ → ℤ := fun n => (n + (R : ℤ)) / (p : ℤ)
    have hqinj : Set.InjOn q (↑(fiber r) : Set ℤ) := by
      intro a ha b hb hab
      change a ∈ fiber r at ha
      change b ∈ fiber r at hb
      have ha_mod := (Finset.mem_filter.mp ha).2
      have hb_mod := (Finset.mem_filter.mp hb).2
      have hab_mod : Int.ModEq (p : ℤ) (a + (R : ℤ)) (b + (R : ℤ)) :=
        Int.ModEq.add_right (R : ℤ) (ha_mod.trans hb_mod.symm)
      have heq : a + (R : ℤ) = b + (R : ℤ) :=
        Int.ext_ediv_modEq hab hab_mod
      omega
    have hsub : (fiber r).image q ⊆
        Finset.Icc (0 : ℤ) (2 * M * K : ℕ) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
      have hnIcc := (Finset.mem_filter.mp hn).1
      have hnlo := (Finset.mem_Icc.mp hnIcc).1
      have hnhi := (Finset.mem_Icc.mp hnIcc).2
      rw [Finset.mem_Icc]
      constructor
      · exact Int.ediv_nonneg (by omega) (by omega)
      · apply Int.ediv_le_of_le_mul hpz
        rw [← hspan]
        omega
    calc
      (fiber r).card = ((fiber r).image q).card :=
        (Finset.card_image_of_injOn hqinj).symm
      _ ≤ (Finset.Icc (0 : ℤ) (2 * M * K : ℕ)).card :=
        Finset.card_le_card hsub
      _ = 2 * M * K + 1 := by
        rw [Int.card_Icc]
        change ((2 * M * K + 1 : ℕ) : ℤ).toNat = 2 * M * K + 1
        rfl
  let Code := Fin p → Fin (2 * M * K + 2)
  let defectPart (f : ExactProduct A (d + 1)) (r : Fin p) : Finset ℤ :=
    (fiber r).filter (fun n => n ∈ D.defect x (f : G))
  let code : ExactProduct A (d + 1) → Code := fun f r =>
    ⟨(defectPart f r).card, by
      have hfilter : (defectPart f r).card ≤ (fiber r).card := by
        dsimp [defectPart]
        exact Finset.card_filter_le _ _
      exact lt_of_le_of_lt (hfilter.trans (fiber_card r)) (by omega)⟩
  have product_bound (f : ExactProduct A (d + 1)) :
      ∀ n : ℤ, |D.displacement x (f : G) n| ≤ (R : ℤ) := by
    obtain ⟨w, hw⟩ := exists_exactWord_eq f
    intro n
    let word : List G :=
      (exactWordList w).map (fun a : ↥A => (a : G))
    have hwordM : ∀ a ∈ word, D.displacementBound a ≤ M := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
      exact hM b b.property
    have hb := wordAct_displacement_bound D x word M hwordM n
    change |D.orbitPerm x (f : G) n - n| ≤ (R : ℤ)
    calc
      |D.orbitPerm x (f : G) n - n| = |wordAct D x word n - n| := by
        rw [wordAct_eq_prod]
        dsimp [word]
        rw [← exactWordProduct_eq_list, hw]
      _ ≤ (M * word.length : ℕ) := hb
      _ = (R : ℕ) := by
        dsimp [word]
        rw [List.length_map, exactWordList_length, hd]
        dsimp [h]
        exact_mod_cast hR.symm
  have defectPart_terminal (f : ExactProduct A (d + 1)) (r : Fin p) :
      ∃ a : ℤ, defectPart f r = (fiber r).filter (fun n => a ≤ n) := by
    by_cases hne : (fiber r).Nonempty
    · rcases hne with ⟨m, hm⟩
      obtain ⟨w, hw⟩ := exists_exactWord_eq f
      let word : List ↥A := exactWordList w
      have hlen : word.length ≤ K * p := by
        dsimp [word]
        rw [exactWordList_length, hd]
      have hmIcc := (Finset.mem_filter.mp hm).1
      have hmlo := (Finset.mem_Icc.mp hmIcc).1
      have hmhi := (Finset.mem_Icc.mp hmIcc).2
      have hmabs : |m| ≤ (R : ℤ) := abs_le.mpr ⟨hmlo, hmhi⟩
      let delta : ℤ := D.orbitPerm x (f : G) m - m
      refine ⟨-delta, ?_⟩
      apply Finset.ext
      intro n
      have hdisp (hn : n ∈ fiber r) :
          D.orbitPerm x (f : G) m - m =
            D.orbitPerm x (f : G) n - n := by
        have hnIcc := (Finset.mem_filter.mp hn).1
        have hnlo := (Finset.mem_Icc.mp hnIcc).1
        have hnhi := (Finset.mem_Icc.mp hnIcc).2
        have hnabs : |n| ≤ (R : ℤ) := abs_le.mpr ⟨hnlo, hnhi⟩
        have hm_mod := (Finset.mem_filter.mp hm).2
        have hn_mod := (Finset.mem_filter.mp hn).2
        have hcong : Int.ModEq (p : ℤ) m n := hm_mod.trans hn_mod.symm
        have hinv := pairedWordInvariant D A x M rho R p K hp hM hrho hR
          hperiodic word hlen m n hmabs hnabs hcong
        have hunattach : word.unattach.prod = (f : G) := by
          change (List.map (fun a : ↥A => (a : G)) (exactWordList w)).prod = (f : G)
          rw [← exactWordProduct_eq_list, hw]
        rw [wordAct_eq_prod, wordAct_eq_prod] at hinv
        simpa [hunattach] using hinv
      simp only [defectPart, Finset.mem_filter]
      constructor
      · rintro ⟨hnfib, hndef⟩
        refine ⟨hnfib, ?_⟩
        have hdsp := hdisp hnfib
        change 0 ≤ D.orbitPerm x (f : G) n at hndef
        dsimp [delta]
        omega
      · rintro ⟨hnfib, hnthreshold⟩
        refine ⟨hnfib, ?_⟩
        have hdsp := hdisp hnfib
        change 0 ≤ D.orbitPerm x (f : G) n
        dsimp [delta] at hnthreshold
        omega
    · have hempty : fiber r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      refine ⟨0, ?_⟩
      simp [defectPart, hempty]
  have defectPart_eq (f g : ExactProduct A (d + 1))
      (hcodeeq : code f = code g) (r : Fin p) :
      defectPart f r = defectPart g r := by
    rcases defectPart_terminal f r with ⟨a, hfa⟩
    rcases defectPart_terminal g r with ⟨b, hgb⟩
    rw [hfa, hgb]
    apply terminalFilter_eq_of_card_eq
    rw [← hfa, ← hgb]
    have hcoord := congrFun hcodeeq r
    exact congrArg Fin.val hcoord
  have hcard : Fintype.card Code < 3 * 2 ^ d := by
    dsimp [Code]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hpow : (2 * M * K + 2) ^ p < (2 ^ K) ^ p := by
      exact Nat.pow_lt_pow_left hsmall (by omega)
    have heq : (2 ^ K) ^ p = 2 ^ h := by
      dsimp [h]
      rw [← pow_mul]
    have hfinal : 2 ^ h < 3 * 2 ^ d := by
      rw [← hd]
      exact twoPow_succ_lt_three_mul d
    exact hpow.trans (heq ▸ hfinal)
  let cert : SeparationCertificate A d (D.halfLineStabilizer x) :=
    { Code := Code
      code := code
      card_lt := hcard
      separates := by
        intro f g hcodeeq
        apply (D.defect_eq_iff_mul_inv_mem x (f : G) (g : G)).mp
        apply Set.ext
        intro n
        by_cases hnlo : n < -(R : ℤ)
        · have hnf := D.not_mem_defect_of_lt_neg x (f : G) R (product_bound f) hnlo
          have hng := D.not_mem_defect_of_lt_neg x (g : G) R (product_bound g) hnlo
          exact iff_of_false hnf hng
        · by_cases hnhi : (R : ℤ) < n
          · have hnf := D.mem_defect_of_gt x (f : G) R (product_bound f) hnhi
            have hng := D.mem_defect_of_gt x (g : G) R (product_bound g) hnhi
            exact iff_of_true hnf hng
          · have hnIcc : n ∈ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
              exact Finset.mem_Icc.mpr ⟨not_lt.mp hnlo, not_lt.mp hnhi⟩
            let r : Fin p := ⟨(n : ZMod p).val, ZMod.val_lt (n : ZMod p)⟩
            have hrval : (r : ℤ) = n % (p : ℤ) := by
              dsimp [r]
              exact ZMod.val_intCast n
            have hrmod : Int.ModEq (p : ℤ) n (r : ℤ) := by
              rw [hrval]
              exact (Int.mod_modEq n (p : ℤ)).symm
            have hnfiber : n ∈ fiber r := by
              exact Finset.mem_filter.mpr ⟨hnIcc, hrmod⟩
            have heqmem : n ∈ defectPart f r ↔ n ∈ defectPart g r := by
              rw [defectPart_eq f g hcodeeq r]
            simpa only [defectPart, Finset.mem_filter, hnfiber, true_and] using heqmem }
  exact ⟨cert⟩

/-- The local-finiteness field of `ExternalInputs` supplies precisely the
wrapper expected by the abstract collision core. -/
theorem halfLine_locallyFinite (I : ExternalInputs G) (x : I.data.Point) :
    LocallyFiniteSubgroup (I.data.halfLineStabilizer x) := by
  intro C hC
  exact I.halfLine_local_finite x C hC

/-- For every finite nonempty `A`, the external inputs yield the witness
required by `abstractCore`.  Here `K=2M+4`, `E=4MK+2rho+1`, and the periodic
occurrence is shifted by `a+2MKp+rho`.

 -/
theorem periodicCoreWitness (I : ExternalInputs G) :
    ∀ A : Finset G, A.Nonempty →
      ∃ (d : ℕ) (H : Subgroup G),
        LocallyFiniteSubgroup H ∧ Nonempty (SeparationCertificate A d H) := by
  intro A hA
  let D := I.data
  let M := commonDisplacement D A
  let rho := commonRadius D A
  let K := 2 * M + 4
  let E := 4 * M * K + 2 * rho + 1
  have hE : 1 ≤ E := by
    dsimp [E]
    omega
  obtain ⟨x, p, a, hp, hperiodic0⟩ := I.scaled_periodic_window E hE
  let R := M * (K * p)
  have hM : ∀ g ∈ A, D.displacementBound g ≤ M := by
    intro g hg
    exact displacementBound_le_common hg
  have hrho : ∀ g ∈ A, D.localityRadius g ≤ rho := by
    intro g hg
    exact localityRadius_le_common hg
  have hK : 1 ≤ K := by
    dsimp [K]
    omega
  have hsmall : 2 * M * K + 2 < 2 ^ K := by
    dsimp [K]
    exact highPower_base M
  have hcenter :
      ((2 * R + rho : ℕ) : ℤ) =
        2 * (M : ℤ) * (K : ℤ) * (p : ℤ) + (rho : ℤ) := by
    dsimp [R]
    ring
  have hpz : (1 : ℤ) ≤ (p : ℤ) := by
    exact_mod_cast hp
  have hright := recenter_right_bound
    (M : ℤ) (K : ℤ) (rho : ℤ) (p : ℤ) (by positivity) hpz
  have hspan :
      2 * ((2 * R + rho : ℕ) : ℤ) ≤ (p : ℤ) * (E : ℤ) - 1 := by
    rw [hcenter]
    dsimp [E]
    nlinarith [hright]
  let y : D.Point := D.shift (a + ((2 * R + rho : ℕ) : ℤ)) x
  have hperiodic : PeriodicOn D.coord y p
      (-((2 * R + rho : ℕ) : ℤ)) ((2 * R + rho : ℕ) : ℤ) := by
    intro i j hi_lo hi_hi hj_lo hj_hi hij
    dsimp [y]
    rw [D.coord_shift, D.coord_shift]
    apply hperiodic0
    · omega
    · omega
    · omega
    · omega
    · exact Int.ModEq.add_right _ hij
  obtain ⟨d, hd, hcert⟩ := periodicSeparationCertificate
    D A hA y M rho R p K hp hK hM hrho rfl hsmall hperiodic
  exact ⟨d, D.halfLineStabilizer y, halfLine_locallyFinite I y, hcert⟩

/-- Relative theorem: the three explicit interface inputs imply leaf
collision rank at most two. -/
theorem relative_leaf_rank_at_most_two (I : ExternalInputs G) :
    LeafCollisionRankAtMost G 2 :=
  abstractCore (periodicCoreWitness I)

/-- The theorem in the paper's incomparable-vertex formulation. -/
theorem relative_fixed_rank_at_most_two (I : ExternalInputs G) :
    FixedCollisionRankAtMost G 2 :=
  abstractCore_fixed (periodicCoreWitness I)

end CollisionRank
