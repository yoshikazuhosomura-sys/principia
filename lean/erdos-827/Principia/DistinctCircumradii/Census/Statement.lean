import Principia.DistinctCircumradii.Basic

/-!
# 八面体型・二つの星 — 全数調査が悪い 6 点に与える形

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

/-- A six-point configuration is *octahedral*: its points split into three pairs
and the eight triangles that pick one point out of each pair have a common
circumradius.  (This is the shape that the lattice census finds in every bad
six-point configuration.) -/
def OctahedralSix (q : Fin 6 → Pt) : Prop :=
  ∃ (e : Fin 3 → Fin 2 → Fin 6) (r : ℝ),
    Function.Bijective (fun p : Fin 3 × Fin 2 => e p.1 p.2) ∧
    ∀ a b c : Fin 2, CircumRadiusSq (q (e 0 a)) (q (e 1 b)) (q (e 2 c)) r

/-- A six-point configuration carries **two stars**: its points split into three
pairs, the four triangles through the first point of the first pair and one point
of each of the other two pairs have a common circumradius, and the four triangles
through the first point of the second pair and one point of each of the other two
pairs have a common circumradius -- possibly a different one. -/
def TwoStars (q : Fin 6 → Pt) : Prop :=
  ∃ (e : Fin 3 → Fin 2 → Fin 6) (r s : ℝ),
    Function.Bijective (fun p : Fin 3 × Fin 2 => e p.1 p.2) ∧
    (∀ b c : Fin 2, CircumRadiusSq (q (e 0 0)) (q (e 1 b)) (q (e 2 c)) r) ∧
    (∀ a c : Fin 2, CircumRadiusSq (q (e 0 a)) (q (e 1 0)) (q (e 2 c)) s)

theorem twoStars_of_octahedral {q : Fin 6 → Pt} (h : OctahedralSix q) : TwoStars q := by
  obtain ⟨e, r, hbij, hR⟩ := h
  exact ⟨e, r, r, hbij, fun b c => hR 0 b c, fun a c => hR a 0 c⟩

/-! ## General position is a statement about unordered subsets -/

theorem generalPosition_comp {p : Fin 6 → Pt} (hgp : GeneralPosition p)
    (σ : Equiv.Perm (Fin 6)) : GeneralPosition (fun i => p (σ i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij; exact ne_of_gp hgp (σ.injective.ne (ne_of_lt hij))
  · intro i j k h1 h2
    exact ncol_of_gp hgp (σ.injective.ne (ne_of_lt h1))
      (σ.injective.ne (ne_of_lt (h1.trans h2))) (σ.injective.ne (ne_of_lt h2))
  · intro i j k l h1 h2 h3
    exact ncyc_of_gp hgp (σ.injective.ne (ne_of_lt h1))
      (σ.injective.ne (ne_of_lt (h1.trans h2)))
      (σ.injective.ne (ne_of_lt (h1.trans (h2.trans h3))))
      (σ.injective.ne (ne_of_lt h2)) (σ.injective.ne (ne_of_lt (h2.trans h3)))
      (σ.injective.ne (ne_of_lt h3))

/-! ## The circumcentre exists, and the squared radius does not see the order -/

/-- The three pairs of the octahedral representative. -/
def k0Pairs : Fin 3 → Fin 2 → Fin 6
  | 0, 0 => 0
  | 0, 1 => 5
  | 1, 0 => 1
  | 1, 1 => 4
  | 2, 0 => 2
  | 2, 1 => 3

theorem k0Pairs_bijective :
    Function.Bijective (fun x : Fin 3 × Fin 2 => k0Pairs x.1 x.2) := by decide

theorem bitAt_censusK0_54 : bitAt censusK0 54 = true := by decide

theorem bitAt_censusK0_42 : bitAt censusK0 42 = true := by decide

theorem bitAt_censusK0_24 : bitAt censusK0 24 = true := by decide

theorem bitAt_censusK0_55 : bitAt censusK0 55 = true := by decide

theorem bitAt_censusK0_28 : bitAt censusK0 28 = true := by decide

theorem bitAt_censusK0_58 : bitAt censusK0 58 = true := by decide

theorem bitAt_censusK0_59 : bitAt censusK0 59 = true := by decide

theorem cellPsi_54 (q : Fin 6 → Pt) :
    cellPsi q 54 = Psi (q 0) (q 1) (q 2) (q 3) := rfl

theorem cellPsi_42 (q : Fin 6 → Pt) :
    cellPsi q 42 = Psi (q 0) (q 2) (q 1) (q 4) := rfl

theorem cellPsi_24 (q : Fin 6 → Pt) :
    cellPsi q 24 = Psi (q 1) (q 2) (q 0) (q 5) := rfl

theorem cellPsi_55 (q : Fin 6 → Pt) :
    cellPsi q 55 = Psi (q 0) (q 4) (q 2) (q 3) := rfl

theorem cellPsi_28 (q : Fin 6 → Pt) :
    cellPsi q 28 = Psi (q 2) (q 4) (q 0) (q 5) := rfl

theorem cellPsi_58 (q : Fin 6 → Pt) :
    cellPsi q 58 = Psi (q 1) (q 5) (q 2) (q 3) := rfl

theorem cellPsi_59 (q : Fin 6 → Pt) :
    cellPsi q 59 = Psi (q 4) (q 5) (q 2) (q 3) := rfl

set_option maxHeartbeats 1000000 in
/-- **The octahedral class is octahedral.**  A six-point configuration in
general position that supports the mask `censusK0` splits into the three pairs
`{0,5}`, `{1,4}`, `{2,3}`, and the eight transversal triangles have one common
circumradius. -/
theorem octahedralSix_of_supports_K0 {q : Fin 6 → Pt} (hgp : GeneralPosition q)
    (hw : Supports q censusK0) : OctahedralSix q := by
  have hne : ∀ i j : Fin 6, i ≠ j → q i ≠ q j := fun i j h => ne_of_gp hgp h
  have hcr : ∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear3 (q i) (q j) (q k) :=
    fun i j k h1 h2 h3 => ncol_of_gp hgp h1 h2 h3
  have key : ∀ i j k l : Fin 6, ∀ r s : ℝ,
      i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      CircumRadiusSq (q i) (q j) (q k) r → CircumRadiusSq (q i) (q j) (q l) s →
      Psi (q i) (q j) (q k) (q l) = 0 → r = s := by
    intro i j k l r s h1 h2 h3 h4 h5 h6 hr hs hp
    exact (eqRadSq_iff_psi (hne i j h1) (hcr i j k h1 h2 h4) (hcr i j l h1 h3 h5)
      (ncyc_of_gp hgp h1 h2 h3 h4 h5 h6) hr hs).2 hp
  have w54 : Psi (q 0) (q 1) (q 2) (q 3) = 0 := by
    rw [← cellPsi_54]; exact hw 54 (by norm_num) bitAt_censusK0_54
  have w42 : Psi (q 0) (q 2) (q 1) (q 4) = 0 := by
    rw [← cellPsi_42]; exact hw 42 (by norm_num) bitAt_censusK0_42
  have w24 : Psi (q 1) (q 2) (q 0) (q 5) = 0 := by
    rw [← cellPsi_24]; exact hw 24 (by norm_num) bitAt_censusK0_24
  have w55 : Psi (q 0) (q 4) (q 2) (q 3) = 0 := by
    rw [← cellPsi_55]; exact hw 55 (by norm_num) bitAt_censusK0_55
  have w28 : Psi (q 2) (q 4) (q 0) (q 5) = 0 := by
    rw [← cellPsi_28]; exact hw 28 (by norm_num) bitAt_censusK0_28
  have w58 : Psi (q 1) (q 5) (q 2) (q 3) = 0 := by
    rw [← cellPsi_58]; exact hw 58 (by norm_num) bitAt_censusK0_58
  have w59 : Psi (q 4) (q 5) (q 2) (q 3) = 0 := by
    rw [← cellPsi_59]; exact hw 59 (by norm_num) bitAt_censusK0_59
  obtain ⟨r012, hR012⟩ := exists_circumRadiusSq (a := q 0) (b := q 1) (c := q 2)
    (hcr 0 1 2 (by decide) (by decide) (by decide))
  obtain ⟨r013, hR013⟩ := exists_circumRadiusSq (a := q 0) (b := q 1) (c := q 3)
    (hcr 0 1 3 (by decide) (by decide) (by decide))
  obtain ⟨r042, hR042⟩ := exists_circumRadiusSq (a := q 0) (b := q 4) (c := q 2)
    (hcr 0 4 2 (by decide) (by decide) (by decide))
  obtain ⟨r043, hR043⟩ := exists_circumRadiusSq (a := q 0) (b := q 4) (c := q 3)
    (hcr 0 4 3 (by decide) (by decide) (by decide))
  obtain ⟨r512, hR512⟩ := exists_circumRadiusSq (a := q 5) (b := q 1) (c := q 2)
    (hcr 5 1 2 (by decide) (by decide) (by decide))
  obtain ⟨r513, hR513⟩ := exists_circumRadiusSq (a := q 5) (b := q 1) (c := q 3)
    (hcr 5 1 3 (by decide) (by decide) (by decide))
  obtain ⟨r542, hR542⟩ := exists_circumRadiusSq (a := q 5) (b := q 4) (c := q 2)
    (hcr 5 4 2 (by decide) (by decide) (by decide))
  obtain ⟨r543, hR543⟩ := exists_circumRadiusSq (a := q 5) (b := q 4) (c := q 3)
    (hcr 5 4 3 (by decide) (by decide) (by decide))
  have eq0 : r013 = r012 :=
    (key 0 1 2 3 r012 r013 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hR012 hR013 w54).symm
  have eq1 : r042 = r012 :=
    (key 0 2 1 4 r012 r042 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (circumRadiusSq_perm hR012).1 (circumRadiusSq_perm hR042).1 w42).symm
  have eq2 : r512 = r012 :=
    (key 1 2 0 5 r012 r512 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (circumRadiusSq_perm hR012).2.2.1 (circumRadiusSq_perm hR512).2.2.1 w24).symm
  have eq3 : r043 = r042 :=
    (key 0 4 2 3 r042 r043 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hR042 hR043 w55).symm
  have eq4 : r542 = r042 :=
    (key 2 4 0 5 r042 r542 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (circumRadiusSq_perm hR042).2.2.2.2 (circumRadiusSq_perm hR542).2.2.2.2 w28).symm
  have eq5 : r513 = r512 :=
    (key 1 5 2 3 r512 r513 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (circumRadiusSq_perm hR512).2.1 (circumRadiusSq_perm hR513).2.1 w58).symm
  have eq6 : r543 = r542 :=
    (key 4 5 2 3 r542 r543 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (circumRadiusSq_perm hR542).2.1 (circumRadiusSq_perm hR543).2.1 w59).symm
  have H012 : CircumRadiusSq (q 0) (q 1) (q 2) r012 := hR012
  have H013 : CircumRadiusSq (q 0) (q 1) (q 3) r012 := by
    rw [← eq0]; exact hR013
  have H042 : CircumRadiusSq (q 0) (q 4) (q 2) r012 := by
    rw [← eq1]; exact hR042
  have H043 : CircumRadiusSq (q 0) (q 4) (q 3) r012 := by
    rw [← (eq3.trans eq1)]; exact hR043
  have H512 : CircumRadiusSq (q 5) (q 1) (q 2) r012 := by
    rw [← eq2]; exact hR512
  have H513 : CircumRadiusSq (q 5) (q 1) (q 3) r012 := by
    rw [← (eq5.trans eq2)]; exact hR513
  have H542 : CircumRadiusSq (q 5) (q 4) (q 2) r012 := by
    rw [← (eq4.trans eq1)]; exact hR542
  have H543 : CircumRadiusSq (q 5) (q 4) (q 3) r012 := by
    rw [← (eq6.trans (eq4.trans eq1))]; exact hR543
  refine ⟨k0Pairs, r012, k0Pairs_bijective, ?_⟩
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
      | exact H012 | exact H013 | exact H042 | exact H043
      | exact H512 | exact H513 | exact H542 | exact H543

/-- Being octahedral does not see a relabelling of the six points. -/
theorem octahedralSix_comp {p : Fin 6 → Pt} {σ : Equiv.Perm (Fin 6)}
    (h : OctahedralSix (fun i => p (σ i))) : OctahedralSix p := by
  obtain ⟨e, r, hbij, hR⟩ := h
  refine ⟨fun k t => σ (e k t), r, ?_, fun a b c => hR a b c⟩
  have hcomp : (fun x : Fin 3 × Fin 2 => σ (e x.1 x.2))
      = σ ∘ (fun x : Fin 3 × Fin 2 => e x.1 x.2) := rfl
  rw [hcomp]
  exact σ.bijective.comp hbij

/-! ## The two hypotheses, and the bridge -/

/-- **Non-realizability of the other 34 representatives.**  No configuration in
general position has all the cells of one of the 34 masks as witnesses.  (Only
the cells *in* the mask are constrained, which is the form in which the
class-by-class arguments deliver their conclusion.)

This is **not** proved in this file. -/
def RestUnrealizable : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w ∈ censusRest, ¬ Supports p w

/-- **The bridge.**  The enumeration together with the non-realizability of the
34 classes makes every bad six-point configuration octahedral. -/
theorem octahedralSix_of_census (hc : CensusComplete) (hr : RestUnrealizable)
    (p : Fin 6 → Pt) (hgp : GeneralPosition p) (hrep : EveryQuadrupleRepeats p) :
    OctahedralSix p := by
  obtain ⟨w, hwlt, hw⟩ := exists_carries p
  obtain ⟨σ, hmem⟩ := hc p hgp hrep w hwlt hw
  have hmem2 : permMask σ w = censusK0 ∨ permMask σ w ∈ censusRest := by
    simpa [censusList] using hmem
  rcases hmem2 with heq | hmem'
  · refine octahedralSix_comp (σ := σ)
      (octahedralSix_of_supports_K0 (generalPosition_comp hgp σ) ?_)
    rw [← heq]
    exact supports_comp σ hw
  · exact absurd (supports_comp σ hw) (hr _ (generalPosition_comp hgp σ) _ hmem')

/-- **The hypothesis of the conditional theorem, verbatim.**  The type of this
theorem's conclusion is the type of the hypothesis `H` of
`isGood_seven_of_octahedral_six`, so the two compose. -/
theorem octahedral_hypothesis (hc : CensusComplete) (hr : RestUnrealizable) :
    ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q :=
  fun q hgp hrep => octahedralSix_of_census hc hr q hgp hrep

/-- The same in the weaker two-star form, which is the hypothesis of
`isGood_seven_of_two_stars`. -/
theorem twoStars_hypothesis (hc : CensusComplete) (hr : RestUnrealizable) :
    ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → TwoStars q :=
  fun q hgp hrep => twoStars_of_octahedral (octahedral_hypothesis hc hr q hgp hrep)






























































end DistinctCircumradii

#print axioms DistinctCircumradii.twoStars_of_octahedral
#print axioms DistinctCircumradii.generalPosition_comp
#print axioms DistinctCircumradii.k0Pairs_bijective
#print axioms DistinctCircumradii.bitAt_censusK0_54
#print axioms DistinctCircumradii.bitAt_censusK0_42
#print axioms DistinctCircumradii.bitAt_censusK0_24
#print axioms DistinctCircumradii.bitAt_censusK0_55
#print axioms DistinctCircumradii.bitAt_censusK0_28
#print axioms DistinctCircumradii.bitAt_censusK0_58
#print axioms DistinctCircumradii.bitAt_censusK0_59
#print axioms DistinctCircumradii.cellPsi_54
#print axioms DistinctCircumradii.cellPsi_42
#print axioms DistinctCircumradii.cellPsi_24
#print axioms DistinctCircumradii.cellPsi_55
#print axioms DistinctCircumradii.cellPsi_28
#print axioms DistinctCircumradii.cellPsi_58
#print axioms DistinctCircumradii.cellPsi_59
#print axioms DistinctCircumradii.octahedralSix_of_supports_K0
#print axioms DistinctCircumradii.octahedralSix_comp
#print axioms DistinctCircumradii.octahedralSix_of_census
#print axioms DistinctCircumradii.octahedral_hypothesis
#print axioms DistinctCircumradii.twoStars_hypothesis
