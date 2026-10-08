import Principia.DistinctCircumradii.SixPoints

/-!
# 七点の段 — 中心対称な 6 点から `n_4 ≤ 7` へ

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

/-- The point reflection of `x` in the centre `O`. -/
def refl2 (O x : Pt) : Pt := (2 * O.1 - x.1, 2 * O.2 - x.2)

@[simp] theorem refl2_refl2 (O x : Pt) : refl2 O (refl2 O x) = x := by
  refine Prod.ext ?_ ?_ <;> simp only [refl2] <;> ring

theorem eq_centre_of_refl2_eq_self {O x : Pt} (h : refl2 O x = x) : O = x := by
  rw [refl2, Prod.ext_iff] at h
  refine Prod.ext ?_ ?_ <;> [linarith [h.1]; linarith [h.2]]

/-- A set whose one-point deletion is symmetric about `O` has its centre inside
the set only in the trivial way: if `refl2 O u` belongs to the set, `O = u`. -/
theorem centre_eq_of_stable {S : Finset Pt} {u O : Pt}
    (h : ∀ x ∈ S.erase u, refl2 O x ∈ S.erase u) (hmem : refl2 O u ∈ S) :
    O = u := by
  by_cases hEq : refl2 O u = u
  · exact eq_centre_of_refl2_eq_self hEq
  · have h1 : refl2 O u ∈ S.erase u := Finset.mem_erase.mpr ⟨hEq, hmem⟩
    have h2 := h _ h1
    rw [refl2_refl2] at h2
    exact absurd (Finset.mem_erase.mp h2).1 (by simp)

/-! ### Seven points cannot have all six-point subsets centrally symmetric -/

/-- **No seven points with all six-point subsets centrally symmetric.**
If `S` has seven points, no three of them collinear, then the seven sets
`S.erase v` cannot all be invariant under a point reflection. -/
theorem not_all_erase_central (S : Finset Pt) (hcard : S.card = 7)
    (hncol : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → ¬ Collinear3 a b c)
    (hsym : ∀ v ∈ S, ∃ O : Pt, ∀ x ∈ S.erase v, refl2 O x ∈ S.erase v) : False := by
  classical
  -- two distinct points of `S`
  obtain ⟨v, hv, w, hw, hvw⟩ : ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
    rw [← Finset.one_lt_card, hcard]; omega
  obtain ⟨Ov, hOv⟩ := hsym v hv
  obtain ⟨Ow, hOw⟩ := hsym w hw
  -- the image of `v` under the reflection centred at `Ow`
  have hvw' : v ∈ S.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
  have hwv' : w ∈ S.erase v := Finset.mem_erase.mpr ⟨Ne.symm hvw, hw⟩
  have hz : refl2 Ow v ∈ S := Finset.mem_of_mem_erase (hOw _ hvw')
  -- the two centres are different
  have hcentre : Ov ≠ Ow := by
    intro h
    have h1 : Ov = v := centre_eq_of_stable hOv (by rw [h]; exact hz)
    have h2 : Ow = w := by
      refine centre_eq_of_stable hOw ?_
      have : refl2 Ov w ∈ S := Finset.mem_of_mem_erase (hOv _ hwv')
      rw [h] at this; exact this
    exact hvw (h1.symm.trans (h.trans h2))
  -- the composition of the two reflections is the translation by `t`
  set t : Pt := (2 * (Ov.1 - Ow.1), 2 * (Ov.2 - Ow.2)) with ht
  have hcomp : ∀ x : Pt, refl2 Ov (refl2 Ow x) = x + t := by
    intro x
    refine Prod.ext ?_ ?_ <;>
      simp only [refl2, ht, Prod.fst_add, Prod.snd_add] <;> ring
  have htne : t ≠ 0 := by
    intro h
    rw [ht, Prod.ext_iff] at h
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    exact hcentre (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  -- at least four points are moved into `S` by the translation
  set A : Finset Pt := S.filter (fun x => x + t ∈ S) with hA
  have hAsub : A ⊆ S := Finset.filter_subset _ _
  have hAmem : ∀ x ∈ S, x ≠ v → x ≠ w → x ≠ refl2 Ow v → x ∈ A := by
    intro x hx hxv hxw hxz
    have h1 : x ∈ S.erase w := Finset.mem_erase.mpr ⟨hxw, hx⟩
    have h2 : refl2 Ow x ∈ S.erase w := hOw _ h1
    have h3 : refl2 Ow x ≠ v := by
      intro h
      apply hxz
      have := refl2_refl2 Ow x
      rw [h] at this
      exact this.symm
    have h4 : refl2 Ow x ∈ S.erase v :=
      Finset.mem_erase.mpr ⟨h3, Finset.mem_of_mem_erase h2⟩
    have h5 : refl2 Ov (refl2 Ow x) ∈ S := Finset.mem_of_mem_erase (hOv _ h4)
    rw [hcomp] at h5
    exact Finset.mem_filter.mpr ⟨hx, h5⟩
  have hbig : 4 ≤ A.card := by
    have hsub : S \ ({v, w, refl2 Ow v} : Finset Pt) ⊆ A := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have h := hx.2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact hAmem x hx.1 h.1 h.2.1 h.2.2
    have hT : ({v, w, refl2 Ow v} : Finset Pt).card ≤ 3 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have : ({w, refl2 Ow v} : Finset Pt).card ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp
      omega
    have hge : 4 ≤ (S \ ({v, w, refl2 Ow v} : Finset Pt)).card := by
      have := Finset.card_le_card_sdiff_add_card (s := S)
        (t := ({v, w, refl2 Ow v} : Finset Pt))
      omega
    exact le_trans hge (Finset.card_le_card hsub)
  -- two four-element subsets of a seven-element set meet
  have hhit : ∃ x ∈ A, x + t ∈ A := by
    by_contra hcon
    push Not at hcon
    set B : Finset Pt := A.image (fun x => x + t) with hB
    have hBsub : B ⊆ S := by
      intro y hy
      rw [hB, Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (Finset.mem_filter.mp hx).2
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_right]
      intro y hy hyA
      rw [hB, Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hcon x hx hyA
    have hBcard : B.card = A.card := by
      rw [hB]
      exact Finset.card_image_of_injective _ (add_left_injective t)
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
    have h2 : (A ∪ B).card ≤ S.card := Finset.card_le_card (Finset.union_subset hAsub hBsub)
    omega
  obtain ⟨x, hxA, hxtA⟩ := hhit
  have hx : x ∈ S := hAsub hxA
  have hxt : x + t ∈ S := (Finset.mem_filter.mp hxA).2
  have hxtt : x + t + t ∈ S := (Finset.mem_filter.mp hxtA).2
  -- the three points are distinct and collinear
  have h1 : x ≠ x + t := fun h => htne (left_eq_add.mp h)
  have h2 : x + t ≠ x + t + t := fun h => htne (left_eq_add.mp h)
  have h3 : x ≠ x + t + t := by
    intro h
    rw [add_assoc] at h
    have h0 : t + t = 0 := left_eq_add.mp h
    have h2t : (2 : ℝ) • t = 0 := by rw [two_smul]; exact h0
    rcases smul_eq_zero.mp h2t with h' | h'
    · norm_num at h'
    · exact htne h'
  have hcol : Collinear3 x (x + t) (x + t + t) := by
    simp only [Collinear3, cross, Prod.fst_add, Prod.snd_add]
    ring
  exact hncol x hx (x + t) hxt (x + t + t) hxtt h1 h2 h3 hcol

/-! ### Permutation invariance of collinearity (copied from the six-point file) -/

/-- A six-point configuration is centrally symmetric: one point reflection
permutes its six points. -/
def CentralSix (q : Fin 6 → Pt) : Prop :=
  ∃ O : Pt, ∀ i : Fin 6, ∃ j : Fin 6, q j = refl2 O (q i)

/-- **Conditional decision of `n_4`.**  If every six-point configuration in
general position all of whose four-point subsets repeat a circumradius is
centrally symmetric, then seven points in general position always contain four
points with four different circumradii, i.e. `n_4 ≤ 7`. -/
theorem isGood_seven_of_central_six
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → CentralSix q) :
    IsGood 7 := by
  classical
  by_contra hgood
  obtain ⟨p, hgp, hrep⟩ : ∃ p : Fin 7 → Pt, GeneralPosition p ∧ EveryQuadrupleRepeats p := by
    simp only [IsGood, not_forall] at hgood
    obtain ⟨p, hp⟩ := hgood
    obtain ⟨hgp, hp⟩ := hp
    refine ⟨p, hgp, ?_⟩
    intro i j k l h1 h2 h3 hd
    exact hp ⟨i, j, k, l, h1, h2, h3, hd⟩
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hgp.1 i j h hij
    · exact hgp.1 j i h hij.symm
  set S : Finset Pt := Finset.image p Finset.univ with hS
  have hcard : S.card = 7 := by
    rw [hS, Finset.card_image_of_injective _ hinj]
    simp
  refine not_all_erase_central S hcard ?_ ?_
  · intro a ha b hb c hc hab hbc hac
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hc
    exact ncol_of_gp hgp (fun h => hab (by rw [h])) (fun h => hac (by rw [h]))
      (fun h => hbc (by rw [h]))
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    have hmono : StrictMono (Fin.succAbove i) := Fin.strictMono_succAbove i
    set q : Fin 6 → Pt := fun m => p (i.succAbove m) with hq
    have hgpq : GeneralPosition q := by
      refine ⟨?_, ?_, ?_⟩
      · intro a b hab; exact hgp.1 _ _ (hmono hab)
      · intro a b c h1 h2; exact hgp.2.1 _ _ _ (hmono h1) (hmono h2)
      · intro a b c d h1 h2 h3; exact hgp.2.2 _ _ _ _ (hmono h1) (hmono h2) (hmono h3)
    have hrepq : EveryQuadrupleRepeats q := by
      intro a b c d h1 h2 h3
      exact hrep _ _ _ _ (hmono h1) (hmono h2) (hmono h3)
    obtain ⟨O, hO⟩ := H q hgpq hrepq
    refine ⟨O, ?_⟩
    intro x hx
    obtain ⟨hxne, hxS⟩ := Finset.mem_erase.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hxS
    have hji : j ≠ i := fun h => hxne (by rw [h])
    obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq hji
    obtain ⟨m', hm'⟩ := hO m
    have hval : refl2 O (p j) = p (i.succAbove m') := by
      rw [← hm]
      exact hm'.symm
    rw [hval]
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · exact fun h => (Fin.succAbove_ne i m') (hinj h)
    · exact Finset.mem_image.mpr ⟨i.succAbove m', Finset.mem_univ _, rfl⟩

/-- In the form used for the infimum: under the same hypothesis, `n_4 ≤ 7`. -/
theorem sInf_isGood_le_seven_of_central_six
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → CentralSix q) :
    sInf {N | IsGood N} ≤ 7 :=
  Nat.sInf_le (isGood_seven_of_central_six H)

/-! ### Two points on one circle: the centre-sum identity

The whole of this section is elementary: two circles of the same radius `R`
centred at `u ≠ v` meet in at most two points, and those two points are
symmetric about the midpoint of `u v`; so their SUM is `u + v`.  Read the other
way round: if two triangles share the edge `u v` and have the same circumradius,
their circumcentres add up to `u + v`.  Four triangles through a common vertex
then give the same total in two ways, and a linear relation between the six
points drops out. -/

/-- Two points of the plane at the same distance from each of two distinct
points are symmetric about their midpoint, in coordinates. -/
theorem centre_sum_aux {x₁ x₂ y₁ y₂ a₁ a₂ b₁ b₂ r : ℝ}
    (h1x : (a₁ - x₁) ^ 2 + (a₂ - x₂) ^ 2 = r)
    (h1y : (a₁ - y₁) ^ 2 + (a₂ - y₂) ^ 2 = r)
    (h2x : (b₁ - x₁) ^ 2 + (b₂ - x₂) ^ 2 = r)
    (h2y : (b₁ - y₁) ^ 2 + (b₂ - y₂) ^ 2 = r)
    (hxy : x₁ ≠ y₁ ∨ x₂ ≠ y₂) (hab : a₁ ≠ b₁ ∨ a₂ ≠ b₂) :
    a₁ + b₁ = x₁ + y₁ ∧ a₂ + b₂ = x₂ + y₂ := by
  -- the difference of the two centres is orthogonal to `y - x`
  have hA : (a₁ - b₁) * (y₁ - x₁) + (a₂ - b₂) * (y₂ - x₂) = 0 := by
    linear_combination (h1x - h1y - h2x + h2y) / 2
  -- so is the deviation of the sum from `x + y`
  have hB : (a₁ + b₁ - x₁ - y₁) * (y₁ - x₁) + (a₂ + b₂ - x₂ - y₂) * (y₂ - x₂) = 0 := by
    linear_combination (h1x - h1y + h2x - h2y) / 2
  -- and the two are orthogonal to each other
  have hC : (a₁ - b₁) * (a₁ + b₁ - x₁ - y₁) + (a₂ - b₂) * (a₂ + b₂ - x₂ - y₂) = 0 := by
    linear_combination (h1x - h2x + h1y - h2y) / 2
  -- two vectors orthogonal to one nonzero vector of the plane are parallel
  have hdet : (a₁ - b₁) * (a₂ + b₂ - x₂ - y₂) - (a₂ - b₂) * (a₁ + b₁ - x₁ - y₁) = 0 := by
    rcases hxy with h | h
    · have hne : y₁ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      have hz : ((a₁ - b₁) * (a₂ + b₂ - x₂ - y₂) - (a₂ - b₂) * (a₁ + b₁ - x₁ - y₁))
          * (y₁ - x₁) = 0 := by
        linear_combination (a₂ + b₂ - x₂ - y₂) * hA - (a₂ - b₂) * hB
      exact (mul_eq_zero.mp hz).resolve_right hne
    · have hne : y₂ - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      have hz : ((a₁ - b₁) * (a₂ + b₂ - x₂ - y₂) - (a₂ - b₂) * (a₁ + b₁ - x₁ - y₁))
          * (y₂ - x₂) = 0 := by
        linear_combination (-(a₁ + b₁ - x₁ - y₁)) * hA + (a₁ - b₁) * hB
      exact (mul_eq_zero.mp hz).resolve_right hne
  have hpos : 0 < (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2 := by
    rcases hab with h | h
    · have h' : a₁ - b₁ ≠ 0 := sub_ne_zero_of_ne h; positivity
    · have h' : a₂ - b₂ ≠ 0 := sub_ne_zero_of_ne h; positivity
  -- Lagrange's identity turns the three orthogonalities into a vanishing product
  have hzero : ((a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2)
      * ((a₁ + b₁ - x₁ - y₁) ^ 2 + (a₂ + b₂ - x₂ - y₂) ^ 2) = 0 := by
    linear_combination ((a₁ - b₁) * (a₁ + b₁ - x₁ - y₁) + (a₂ - b₂) * (a₂ + b₂ - x₂ - y₂)) * hC
      + ((a₁ - b₁) * (a₂ + b₂ - x₂ - y₂) - (a₂ - b₂) * (a₁ + b₁ - x₁ - y₁)) * hdet
  have hsum : (a₁ + b₁ - x₁ - y₁) ^ 2 + (a₂ + b₂ - x₂ - y₂) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hpos.ne'
  clear hzero hA hB hC hdet hpos h1x h1y h2x h2y
  have n1 : (0 : ℝ) ≤ (a₁ + b₁ - x₁ - y₁) ^ 2 := sq_nonneg _
  have n2 : (0 : ℝ) ≤ (a₂ + b₂ - x₂ - y₂) ^ 2 := sq_nonneg _
  have e1 : (a₁ + b₁ - x₁ - y₁) ^ 2 = 0 := le_antisymm (by linarith) n1
  have e2 : (a₂ + b₂ - x₂ - y₂) ^ 2 = 0 := le_antisymm (by linarith) n2
  have f1 : a₁ + b₁ - x₁ - y₁ = 0 := by
    have := sq_eq_zero_iff.mp e1; exact this
  have f2 : a₂ + b₂ - x₂ - y₂ = 0 := by
    have := sq_eq_zero_iff.mp e2; exact this
  exact ⟨by linarith, by linarith⟩

/-- **The centre-sum identity.**  If `o₁` and `o₂` are both at squared distance
`r` from `x` and from `y`, with `x ≠ y` and `o₁ ≠ o₂`, then `o₁ + o₂ = x + y`. -/
theorem centre_sum {x y o₁ o₂ : Pt} {r : ℝ}
    (h1x : sqdist o₁ x = r) (h1y : sqdist o₁ y = r)
    (h2x : sqdist o₂ x = r) (h2y : sqdist o₂ y = r)
    (hxy : x ≠ y) (ho : o₁ ≠ o₂) :
    o₁.1 + o₂.1 = x.1 + y.1 ∧ o₁.2 + o₂.2 = x.2 + y.2 := by
  simp only [sqdist] at h1x h1y h2x h2y
  refine centre_sum_aux h1x h1y h2x h2y ?_ ?_
  · rcases eq_or_ne x.1 y.1 with h | h
    · rcases eq_or_ne x.2 y.2 with h' | h'
      · exact absurd (Prod.ext h h') hxy
      · exact Or.inr h'
    · exact Or.inl h
  · rcases eq_or_ne o₁.1 o₂.1 with h | h
    · rcases eq_or_ne o₁.2 o₂.2 with h' | h'
      · exact absurd (Prod.ext h h') ho
      · exact Or.inr h'
    · exact Or.inl h

/-- Two triangles sharing an edge, with equal circumradius, have distinct
circumcentres -- unless the four points are concyclic. -/
theorem centre_ne_of_not_concyclic {a b c d o₁ o₂ : Pt} {r : ℝ}
    (h1a : sqdist o₁ a = r) (h1b : sqdist o₁ b = r) (h1c : sqdist o₁ c = r)
    (h2d : sqdist o₂ d = r) (hnc : ¬ Concyclic4 a b c d) : o₁ ≠ o₂ := by
  intro h
  exact hnc (concyclic4_of_common_center h1a h1b h1c (by rw [h]; exact h2d))

/-! ### The star lemma -/

/-- **The star lemma.**  Let `x` be a point and `{y, y'}`, `{z, z'}` two pairs of
points.  If the four triangles `x y z`, `x y z'`, `x y' z`, `x y' z'` have the
same circumradius, then `y + y' = z + z'`: the two pairs have a common midpoint.

The proof adds the four circumcentres in two ways.  The centres of `x y z` and
`x y z'` are the two centres of circles of that radius through `x` and `y`, so
they add up to `x + y`; likewise for `x y' z` and `x y' z'` (total `x + y'`),
for `x y z` and `x y' z` (total `x + z`) and for `x y z'` and `x y' z'`
(total `x + z'`).  Hence `2x + y + y' = 2x + z + z'`. -/
theorem star_sum {x y y' z z' o₁ o₂ o₃ o₄ : Pt} {r : ℝ}
    (h1x : sqdist o₁ x = r) (h1y : sqdist o₁ y = r) (h1z : sqdist o₁ z = r)
    (h2x : sqdist o₂ x = r) (h2y : sqdist o₂ y = r) (h2z : sqdist o₂ z' = r)
    (h3x : sqdist o₃ x = r) (h3y : sqdist o₃ y' = r) (h3z : sqdist o₃ z = r)
    (h4x : sqdist o₄ x = r) (h4y : sqdist o₄ y' = r) (h4z : sqdist o₄ z' = r)
    (hxy : x ≠ y) (hxy' : x ≠ y') (hxz : x ≠ z) (hxz' : x ≠ z')
    (h12 : o₁ ≠ o₂) (h34 : o₃ ≠ o₄) (h13 : o₁ ≠ o₃) (h24 : o₂ ≠ o₄) :
    y.1 + y'.1 = z.1 + z'.1 ∧ y.2 + y'.2 = z.2 + z'.2 := by
  obtain ⟨a1, a2⟩ := centre_sum h1x h1y h2x h2y hxy h12
  obtain ⟨b1, b2⟩ := centre_sum h3x h3y h4x h4y hxy' h34
  obtain ⟨c1, c2⟩ := centre_sum h1x h1z h3x h3z hxz h13
  obtain ⟨d1, d2⟩ := centre_sum h2x h2z h4x h4z hxz' h24
  exact ⟨by linarith, by linarith⟩

/-! ### Three equal circumradii in a four-point set force the fourth

If three of the four triangles of `a b c d` have the same circumradius then the
centre-sum identity pins the fourth point down: `d` is the orthocentre of
`a b c`, and then the fourth triangle has that circumradius as well.  So the
four circumradii of a four-point set in general position are never of the shape
"three equal, one different". -/

theorem fourth_eqRad_of_three {a b c d o₁ o₂ o₃ : Pt} {r : ℝ}
    (h1a : sqdist o₁ a = r) (h1b : sqdist o₁ b = r) (h1c : sqdist o₁ c = r)
    (h2a : sqdist o₂ a = r) (h2b : sqdist o₂ b = r) (h2d : sqdist o₂ d = r)
    (h3a : sqdist o₃ a = r) (h3c : sqdist o₃ c = r) (h3d : sqdist o₃ d = r)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (h12 : o₁ ≠ o₂) (h13 : o₁ ≠ o₃) (h23 : o₂ ≠ o₃) :
    CircumRadiusSq b c d r := by
  obtain ⟨p1, p2⟩ := centre_sum h1a h1b h2a h2b hab h12
  obtain ⟨q1, q2⟩ := centre_sum h1a h1c h3a h3c hac h13
  obtain ⟨s1, s2⟩ := centre_sum h2a h2d h3a h3d had h23
  refine ⟨(b.1 + c.1 - o₁.1, b.2 + c.2 - o₁.2), ?_, ?_, ?_⟩
  · simp only [sqdist] at h1c ⊢; linear_combination h1c
  · simp only [sqdist] at h1b ⊢; linear_combination h1b
  · -- `d = a + b + c - 2 o₁`, so the new centre is at distance `r` from `d` too
    have hd1 : d.1 = a.1 + b.1 + c.1 - 2 * o₁.1 := by linarith
    have hd2 : d.2 = a.2 + b.2 + c.2 - 2 * o₁.2 := by linarith
    simp only [sqdist] at h1a ⊢
    rw [hd1, hd2]; linear_combination h1a

/-! ### Octahedral six-point configurations are centrally symmetric -/

/-- No point of the plane is equidistant from four points of a configuration in
general position. -/
theorem centre_ne_of_gp {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p)
    {i j k l : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {o₁ o₂ : Pt} {r : ℝ}
    (h1i : sqdist o₁ (p i) = r) (h1j : sqdist o₁ (p j) = r) (h1k : sqdist o₁ (p k) = r)
    (h2l : sqdist o₂ (p l) = r) : o₁ ≠ o₂ := by
  intro h
  refine no_common_center_of_gp hgp (S := {i, j, k, l})
    (card_four hij hik hil hjk hjl hkl) (o := o₁) (r := r) ?_
  intro m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact h1i
  · exact h1j
  · exact h1k
  · rw [h]; exact h2l

/-- **Octahedral implies centrally symmetric.**  A six-point configuration in
general position whose three pairs carry eight transversal triangles of one
circumradius is symmetric about a point.  Only six of the eight triangles are
used: the four through one point of the first pair and the four through one
point of the second. -/
theorem central_six_of_octahedral {q : Fin 6 → Pt} (hgp : GeneralPosition q)
    (hoct : OctahedralSix q) : CentralSix q := by
  obtain ⟨e, r, hbij, hR⟩ := hoct
  -- the six indices are pairwise distinct
  have hne : ∀ k k' : Fin 3, ∀ a a' : Fin 2, (k, a) ≠ (k', a') → e k a ≠ e k' a' := by
    intro k k' a a' h he
    exact h (hbij.1 (show (fun p : Fin 3 × Fin 2 => e p.1 p.2) (k, a) = _ from he))
  -- circumcentres of the eight transversal triangles
  choose o ho1 ho2 ho3 using hR
  -- the star at `e 0 0`
  have key1 : (q (e 1 0)).1 + (q (e 1 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e 1 0)).2 + (q (e 1 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    refine star_sum (o₁ := o 0 0 0) (o₂ := o 0 0 1) (o₃ := o 0 1 0) (o₄ := o 0 1 1)
      (ho1 0 0 0) (ho2 0 0 0) (ho3 0 0 0)
      (ho1 0 0 1) (ho2 0 0 1) (ho3 0 0 1)
      (ho1 0 1 0) (ho2 0 1 0) (ho3 0 1 0)
      (ho1 0 1 1) (ho2 0 1 1) (ho3 0 1 1)
      (ne_of_gp hgp (hne 0 1 0 0 (by decide)))
      (ne_of_gp hgp (hne 0 1 0 1 (by decide)))
      (ne_of_gp hgp (hne 0 2 0 0 (by decide)))
      (ne_of_gp hgp (hne 0 2 0 1 (by decide))) ?_ ?_ ?_ ?_
    · exact centre_ne_of_gp hgp (hne 0 1 0 0 (by decide)) (hne 0 2 0 0 (by decide))
        (hne 0 2 0 1 (by decide)) (hne 1 2 0 0 (by decide)) (hne 1 2 0 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ho1 0 0 0) (ho2 0 0 0) (ho3 0 0 0) (ho3 0 0 1)
    · exact centre_ne_of_gp hgp (hne 0 1 0 1 (by decide)) (hne 0 2 0 0 (by decide))
        (hne 0 2 0 1 (by decide)) (hne 1 2 1 0 (by decide)) (hne 1 2 1 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ho1 0 1 0) (ho2 0 1 0) (ho3 0 1 0) (ho3 0 1 1)
    · exact centre_ne_of_gp hgp (hne 0 2 0 0 (by decide)) (hne 0 1 0 0 (by decide))
        (hne 0 1 0 1 (by decide)) (hne 2 1 0 0 (by decide)) (hne 2 1 0 1 (by decide))
        (hne 1 1 0 1 (by decide)) (ho1 0 0 0) (ho3 0 0 0) (ho2 0 0 0) (ho2 0 1 0)
    · exact centre_ne_of_gp hgp (hne 0 2 0 1 (by decide)) (hne 0 1 0 0 (by decide))
        (hne 0 1 0 1 (by decide)) (hne 2 1 1 0 (by decide)) (hne 2 1 1 1 (by decide))
        (hne 1 1 0 1 (by decide)) (ho1 0 0 1) (ho3 0 0 1) (ho2 0 0 1) (ho2 0 1 1)
  -- the star at `e 1 0`
  have key2 : (q (e 0 0)).1 + (q (e 0 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e 0 0)).2 + (q (e 0 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    refine star_sum (o₁ := o 0 0 0) (o₂ := o 0 0 1) (o₃ := o 1 0 0) (o₄ := o 1 0 1)
      (ho2 0 0 0) (ho1 0 0 0) (ho3 0 0 0)
      (ho2 0 0 1) (ho1 0 0 1) (ho3 0 0 1)
      (ho2 1 0 0) (ho1 1 0 0) (ho3 1 0 0)
      (ho2 1 0 1) (ho1 1 0 1) (ho3 1 0 1)
      (ne_of_gp hgp (hne 1 0 0 0 (by decide)))
      (ne_of_gp hgp (hne 1 0 0 1 (by decide)))
      (ne_of_gp hgp (hne 1 2 0 0 (by decide)))
      (ne_of_gp hgp (hne 1 2 0 1 (by decide))) ?_ ?_ ?_ ?_
    · exact centre_ne_of_gp hgp (hne 1 0 0 0 (by decide)) (hne 1 2 0 0 (by decide))
        (hne 1 2 0 1 (by decide)) (hne 0 2 0 0 (by decide)) (hne 0 2 0 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ho2 0 0 0) (ho1 0 0 0) (ho3 0 0 0) (ho3 0 0 1)
    · exact centre_ne_of_gp hgp (hne 1 0 0 1 (by decide)) (hne 1 2 0 0 (by decide))
        (hne 1 2 0 1 (by decide)) (hne 0 2 1 0 (by decide)) (hne 0 2 1 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ho2 1 0 0) (ho1 1 0 0) (ho3 1 0 0) (ho3 1 0 1)
    · exact centre_ne_of_gp hgp (hne 1 2 0 0 (by decide)) (hne 1 0 0 0 (by decide))
        (hne 1 0 0 1 (by decide)) (hne 2 0 0 0 (by decide)) (hne 2 0 0 1 (by decide))
        (hne 0 0 0 1 (by decide)) (ho2 0 0 0) (ho3 0 0 0) (ho1 0 0 0) (ho1 1 0 0)
    · exact centre_ne_of_gp hgp (hne 1 2 0 1 (by decide)) (hne 1 0 0 0 (by decide))
        (hne 1 0 0 1 (by decide)) (hne 2 0 1 0 (by decide)) (hne 2 0 1 1 (by decide))
        (hne 0 0 0 1 (by decide)) (ho2 0 0 1) (ho3 0 0 1) (ho1 0 0 1) (ho1 1 0 1)
  -- the common centre
  set O : Pt := ((((q (e 2 0)).1 + (q (e 2 1)).1) / 2), (((q (e 2 0)).2 + (q (e 2 1)).2) / 2))
    with hO
  have hpair : ∀ k : Fin 3, (q (e k 0)).1 + (q (e k 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e k 0)).2 + (q (e k 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    intro k
    fin_cases k
    · exact key2
    · exact key1
    · exact ⟨rfl, rfl⟩
  -- each pair is swapped by the point reflection in `O`
  have hswap : ∀ (k : Fin 3) (b c : Fin 2),
      (q (e k b)).1 + (q (e k c)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 →
      (q (e k b)).2 + (q (e k c)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 →
      q (e k c) = refl2 O (q (e k b)) := by
    intro k b c h1 h2
    refine Prod.ext ?_ ?_
    · simp only [refl2, hO]; linarith
    · simp only [refl2, hO]; linarith
  refine ⟨O, ?_⟩
  intro i
  obtain ⟨⟨k, a⟩, hp⟩ := hbij.2 i
  have hp' : e k a = i := hp
  subst hp'
  fin_cases a
  · exact ⟨e k 1, hswap k 0 1 (hpair k).1 (hpair k).2⟩
  · exact ⟨e k 0, hswap k 1 0 (by linarith [(hpair k).1]) (by linarith [(hpair k).2])⟩

/-- **Conditional decision of `n_4`, with the octahedral hypothesis.**  If every
six-point configuration in general position all of whose four-point subsets
repeat a circumradius is octahedral, then `n_4 ≤ 7`.  This is weaker than the
hypothesis of `isGood_seven_of_central_six`: central symmetry is now proved
rather than assumed. -/
theorem isGood_seven_of_octahedral_six
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q) :
    IsGood 7 :=
  isGood_seven_of_central_six
    (fun q hgp hrep => central_six_of_octahedral hgp (H q hgp hrep))

theorem sInf_isGood_le_seven_of_octahedral_six
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q) :
    sInf {N | IsGood N} ≤ 7 :=
  Nat.sInf_le (isGood_seven_of_octahedral_six H)


















/-!
# The pair relation

Everything above works with circumcentres.  This part adds the *algebraic* form
of "two triangles on one edge have the same circumradius" and the transitivity
that it brings.

For a four-point set the equal-circumradius form of the edge `a b` is the
polynomial `Psi a b c d`, and the difference of the two squared circumradii
factors as the circle determinant times `Psi` (`circum_diff_factor`).  Read the
plane as `ℂ` and put `w z = (z - c)(z - d)`.  Then

    Psi a b c d = cross2 (w a) (w b),

so, for a fixed pair `c d`, `Psi · · c d = 0` says that the two complex numbers
`w a` and `w b` are parallel -- that `arg[(a-c)(a-d)]` and `arg[(b-c)(b-d)]`
agree modulo `π`.  Parallelism is transitive through a nonzero vector, and
`w b` is nonzero as soon as `b` differs from `c` and from `d`.  Hence the
relation "the two triangles on the edge `· ·` cut out by `c` and `d` have the
same circumradius" is, for a fixed pair `c d`, an equivalence relation on the
remaining points (`eqRadSq_trans`).  This is a constraint on the witness
structure of a bad configuration that the centre-sum identity does not see.

Two further consequences are recorded.  If a four-point set has the two
witnesses "edge `u v`, pair `c d`" and "edge `c d`, pair `u v`" at once, then
the lines `u c` and `v d` are parallel or perpendicular
(`par_or_perp_of_psi`).  And the octahedral hypothesis of
`central_six_of_octahedral` can be weakened to two stars with two different
radii (`central_six_of_two_stars`), which shrinks what remains to be proved for
`n_4 = 7`.
-/


/-- The cross product of two vectors of the plane. -/
def cross2 (u v : Pt) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The scalar product of two vectors of the plane. -/
def dot2 (u v : Pt) : ℝ := u.1 * v.1 + u.2 * v.2

/-- The difference of two points, as a vector. -/
def vsub (p q : Pt) : Pt := (p.1 - q.1, p.2 - q.2)

/-- The product of two vectors read as complex numbers. -/
def cmul (z w : Pt) : Pt := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The complex product `(z - c) * (z - d)`. -/
def wprod (c d z : Pt) : Pt :=
  ((z.1 - c.1) * (z.1 - d.1) - (z.2 - c.2) * (z.2 - d.2),
   (z.1 - c.1) * (z.2 - d.2) + (z.2 - c.2) * (z.1 - d.1))

/-- **The complex form of `Psi`.**  With `w z = (z - c)(z - d)` read as a product
of complex numbers, the equal-circumradius form of the edge `a b` is the cross
product of `w a` and `w b`.  So `Psi a b c d = 0` says that `w a` and `w b` are
parallel: the arguments of `(a-c)(a-d)` and of `(b-c)(b-d)` agree modulo `π`. -/
theorem psi_eq_cross2_wprod (a b c d : Pt) :
    Psi a b c d = cross2 (wprod c d a) (wprod c d b) := by
  simp only [Psi, qq, cross, cross2, wprod]
  ring

/-- The modulus of the complex product is the product of the moduli. -/
theorem normSq_wprod (c d z : Pt) :
    (wprod c d z).1 ^ 2 + (wprod c d z).2 ^ 2 = sqdist z c * sqdist z d := by
  simp only [wprod, sqdist]
  ring

theorem sqdist_ne_zeroSeven {p q : Pt} (h : p ≠ q) : sqdist p q ≠ 0 := by
  intro h0
  simp only [sqdist] at h0
  have h1 : p.1 - q.1 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have h2 : p.2 - q.2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  exact h (Prod.ext (by linarith) (by linarith))

theorem wprod_ne_zero {c d z : Pt} (hc : z ≠ c) (hd : z ≠ d) : wprod c d z ≠ (0, 0) := by
  intro h
  have h0 : sqdist z c * sqdist z d = 0 := by
    rw [← normSq_wprod c d z, h]; norm_num
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact sqdist_ne_zeroSeven hc h'
  · exact sqdist_ne_zeroSeven hd h'

/-- Parallelism of plane vectors is transitive through a nonzero vector. -/
theorem cross2_trans {u v w : Pt} (hv : v ≠ (0, 0))
    (h1 : cross2 u v = 0) (h2 : cross2 v w = 0) : cross2 u w = 0 := by
  simp only [cross2] at h1 h2 ⊢
  rcases eq_or_ne v.1 0 with hv1 | hv1
  · have hv2 : v.2 ≠ 0 := by
      intro h
      exact hv (Prod.ext (by simpa using hv1) (by simpa using h))
    have hu1 : u.1 = 0 := by
      have hz : u.1 * v.2 = 0 := by rw [hv1] at h1; linarith
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h hv2
    have hw1 : w.1 = 0 := by
      have hz : v.2 * w.1 = 0 := by rw [hv1] at h2; linarith
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hv2
      · exact h
    rw [hu1, hw1]; ring
  · have hz : (u.1 * w.2 - u.2 * w.1) * v.1 = 0 := by
      linear_combination u.1 * h2 + w.1 * h1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hv1

/-- **Transitivity of the pair relation** (algebraic form).  For a fixed pair
`c d`, the relation `Psi · · c d = 0` is transitive through any point `b`
different from `c` and from `d`. -/
theorem psi_transImplicit {a b e c d : Pt} (hbc : b ≠ c) (hbd : b ≠ d)
    (h1 : Psi a b c d = 0) (h2 : Psi b e c d = 0) : Psi a e c d = 0 := by
  rw [psi_eq_cross2_wprod] at h1 h2 ⊢
  exact cross2_trans (wprod_ne_zero hbc hbd) h1 h2

/-! ### From the circumradius to `Psi` and back -/

/-- **Transitivity of the pair relation** (geometric form).  If the two triangles
on the edge `a b` cut out by `c` and `d` have the same circumradius, and so do
the two on the edge `b e`, then so do the two on the edge `a e`.  All three
statements are about the same pair `c d`. -/
theorem eqRadSq_trans {a b e c d : Pt} {r₁ r₂ s₁ s₂ t₁ t₂ : ℝ}
    (hab : a ≠ b) (hbe : b ≠ e) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hc1 : ¬ Collinear3 a b c) (hd1 : ¬ Collinear3 a b d)
    (hc2 : ¬ Collinear3 b e c) (hd2 : ¬ Collinear3 b e d)
    (hc3 : ¬ Collinear3 a e c) (hd3 : ¬ Collinear3 a e d)
    (hy1 : ¬ Concyclic4 a b c d) (hy2 : ¬ Concyclic4 b e c d)
    (hy3 : ¬ Concyclic4 a e c d)
    (hA : CircumRadiusSq a b c r₁) (hB : CircumRadiusSq a b d r₂)
    (hC : CircumRadiusSq b e c s₁) (hD : CircumRadiusSq b e d s₂)
    (hE : CircumRadiusSq a e c t₁) (hF : CircumRadiusSq a e d t₂)
    (h1 : r₁ = r₂) (h2 : s₁ = s₂) : t₁ = t₂ :=
  (eqRadSq_iff_psi hae hc3 hd3 hy3 hE hF).2
    (psi_transImplicit hbc hbd ((eqRadSq_iff_psi hab hc1 hd1 hy1 hA hB).1 h1)
      ((eqRadSq_iff_psi hbe hc2 hd2 hy2 hC hD).1 h2))

/-! ### Two witnesses in one four-point set force a right or a zero angle -/

/-- The identity behind `par_or_perp_of_psi`: with `A = c - u`, `B = d - u`,
`C = c - v`, `D = d - v` read as complex numbers, `Psi u v c d` and `Psi c d u v`
are the imaginary parts of `conj(A B) C D` and of `conj(A C) B D`, whose product
is `|B|²|C|²  conj(A²) D²`; the imaginary part of a product of two reals is
zero. -/
theorem par_perp_identity (u v c d : Pt) :
    sqdist d u * sqdist c v * (2 * dot2 (vsub c u) (vsub d v)
        * cross2 (vsub c u) (vsub d v))
      = dot2 (cmul (vsub c u) (vsub d u)) (cmul (vsub c v) (vsub d v)) * Psi c d u v
        + dot2 (cmul (vsub c u) (vsub c v)) (cmul (vsub d u) (vsub d v)) * Psi u v c d := by
  simp only [sqdist, dot2, cross2, vsub, cmul, Psi, qq, cross]
  ring

/-- **Two complementary witnesses force a right or a zero angle.**  If the
four-point set `u v c d` carries both the witness "edge `u v`, pair `c d`" and
the witness "edge `c d`, pair `u v`", then the lines `u c` and `v d` are
parallel or perpendicular. -/
theorem par_or_perp_of_psi {u v c d : Pt} (hdu : d ≠ u) (hcv : c ≠ v)
    (h1 : Psi u v c d = 0) (h2 : Psi c d u v = 0) :
    dot2 (vsub c u) (vsub d v) * cross2 (vsub c u) (vsub d v) = 0 := by
  have hid := par_perp_identity u v c d
  rw [h1, h2, mul_zero, mul_zero, add_zero] at hid
  have h1' : sqdist d u ≠ 0 := sqdist_ne_zeroSeven hdu
  have h2' : sqdist c v ≠ 0 := sqdist_ne_zeroSeven hcv
  have key : sqdist d u * sqdist c v * 2
      * (dot2 (vsub c u) (vsub d v) * cross2 (vsub c u) (vsub d v)) = 0 := by
    linear_combination hid
  have hne : sqdist d u * sqdist c v * 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h1' h2') (by norm_num)
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

/-! ### Two stars are enough -/

/-- **Two stars imply centrally symmetric.**  Same conclusion as
`central_six_of_octahedral` from a weaker hypothesis. -/
theorem central_six_of_two_stars {q : Fin 6 → Pt} (hgp : GeneralPosition q)
    (hts : TwoStars q) : CentralSix q := by
  obtain ⟨e, r, s, hbij, hR1, hR2⟩ := hts
  have hne : ∀ k k' : Fin 3, ∀ a a' : Fin 2, (k, a) ≠ (k', a') → e k a ≠ e k' a' := by
    intro k k' a a' h he
    exact h (hbij.1 (show (fun p : Fin 3 × Fin 2 => e p.1 p.2) (k, a) = _ from he))
  choose o1 ha1 hb1 hc1 using hR1
  choose o2 ha2 hb2 hc2 using hR2
  -- the star at `e 0 0`
  have key1 : (q (e 1 0)).1 + (q (e 1 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e 1 0)).2 + (q (e 1 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    refine star_sum (o₁ := o1 0 0) (o₂ := o1 0 1) (o₃ := o1 1 0) (o₄ := o1 1 1)
      (ha1 0 0) (hb1 0 0) (hc1 0 0)
      (ha1 0 1) (hb1 0 1) (hc1 0 1)
      (ha1 1 0) (hb1 1 0) (hc1 1 0)
      (ha1 1 1) (hb1 1 1) (hc1 1 1)
      (ne_of_gp hgp (hne 0 1 0 0 (by decide)))
      (ne_of_gp hgp (hne 0 1 0 1 (by decide)))
      (ne_of_gp hgp (hne 0 2 0 0 (by decide)))
      (ne_of_gp hgp (hne 0 2 0 1 (by decide))) ?_ ?_ ?_ ?_
    · exact centre_ne_of_gp hgp (hne 0 1 0 0 (by decide)) (hne 0 2 0 0 (by decide))
        (hne 0 2 0 1 (by decide)) (hne 1 2 0 0 (by decide)) (hne 1 2 0 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ha1 0 0) (hb1 0 0) (hc1 0 0) (hc1 0 1)
    · exact centre_ne_of_gp hgp (hne 0 1 0 1 (by decide)) (hne 0 2 0 0 (by decide))
        (hne 0 2 0 1 (by decide)) (hne 1 2 1 0 (by decide)) (hne 1 2 1 1 (by decide))
        (hne 2 2 0 1 (by decide)) (ha1 1 0) (hb1 1 0) (hc1 1 0) (hc1 1 1)
    · exact centre_ne_of_gp hgp (hne 0 2 0 0 (by decide)) (hne 0 1 0 0 (by decide))
        (hne 0 1 0 1 (by decide)) (hne 2 1 0 0 (by decide)) (hne 2 1 0 1 (by decide))
        (hne 1 1 0 1 (by decide)) (ha1 0 0) (hc1 0 0) (hb1 0 0) (hb1 1 0)
    · exact centre_ne_of_gp hgp (hne 0 2 0 1 (by decide)) (hne 0 1 0 0 (by decide))
        (hne 0 1 0 1 (by decide)) (hne 2 1 1 0 (by decide)) (hne 2 1 1 1 (by decide))
        (hne 1 1 0 1 (by decide)) (ha1 0 1) (hc1 0 1) (hb1 0 1) (hb1 1 1)
  -- the star at `e 1 0`
  have key2 : (q (e 0 0)).1 + (q (e 0 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e 0 0)).2 + (q (e 0 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    refine star_sum (o₁ := o2 0 0) (o₂ := o2 0 1) (o₃ := o2 1 0) (o₄ := o2 1 1)
      (hb2 0 0) (ha2 0 0) (hc2 0 0)
      (hb2 0 1) (ha2 0 1) (hc2 0 1)
      (hb2 1 0) (ha2 1 0) (hc2 1 0)
      (hb2 1 1) (ha2 1 1) (hc2 1 1)
      (ne_of_gp hgp (hne 1 0 0 0 (by decide)))
      (ne_of_gp hgp (hne 1 0 0 1 (by decide)))
      (ne_of_gp hgp (hne 1 2 0 0 (by decide)))
      (ne_of_gp hgp (hne 1 2 0 1 (by decide))) ?_ ?_ ?_ ?_
    · exact centre_ne_of_gp hgp (hne 1 0 0 0 (by decide)) (hne 1 2 0 0 (by decide))
        (hne 1 2 0 1 (by decide)) (hne 0 2 0 0 (by decide)) (hne 0 2 0 1 (by decide))
        (hne 2 2 0 1 (by decide)) (hb2 0 0) (ha2 0 0) (hc2 0 0) (hc2 0 1)
    · exact centre_ne_of_gp hgp (hne 1 0 0 1 (by decide)) (hne 1 2 0 0 (by decide))
        (hne 1 2 0 1 (by decide)) (hne 0 2 1 0 (by decide)) (hne 0 2 1 1 (by decide))
        (hne 2 2 0 1 (by decide)) (hb2 1 0) (ha2 1 0) (hc2 1 0) (hc2 1 1)
    · exact centre_ne_of_gp hgp (hne 1 2 0 0 (by decide)) (hne 1 0 0 0 (by decide))
        (hne 1 0 0 1 (by decide)) (hne 2 0 0 0 (by decide)) (hne 2 0 0 1 (by decide))
        (hne 0 0 0 1 (by decide)) (hb2 0 0) (hc2 0 0) (ha2 0 0) (ha2 1 0)
    · exact centre_ne_of_gp hgp (hne 1 2 0 1 (by decide)) (hne 1 0 0 0 (by decide))
        (hne 1 0 0 1 (by decide)) (hne 2 0 1 0 (by decide)) (hne 2 0 1 1 (by decide))
        (hne 0 0 0 1 (by decide)) (hb2 0 1) (hc2 0 1) (ha2 0 1) (ha2 1 1)
  set O : Pt := ((((q (e 2 0)).1 + (q (e 2 1)).1) / 2), (((q (e 2 0)).2 + (q (e 2 1)).2) / 2))
    with hO
  have hpair : ∀ k : Fin 3, (q (e k 0)).1 + (q (e k 1)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 ∧
      (q (e k 0)).2 + (q (e k 1)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 := by
    intro k
    fin_cases k
    · exact key2
    · exact key1
    · exact ⟨rfl, rfl⟩
  have hswap : ∀ (k : Fin 3) (b c : Fin 2),
      (q (e k b)).1 + (q (e k c)).1 = (q (e 2 0)).1 + (q (e 2 1)).1 →
      (q (e k b)).2 + (q (e k c)).2 = (q (e 2 0)).2 + (q (e 2 1)).2 →
      q (e k c) = refl2 O (q (e k b)) := by
    intro k b c h1 h2
    refine Prod.ext ?_ ?_
    · simp only [refl2, hO]; linarith
    · simp only [refl2, hO]; linarith
  refine ⟨O, ?_⟩
  intro i
  obtain ⟨⟨k, a⟩, hp⟩ := hbij.2 i
  have hp' : e k a = i := hp
  subst hp'
  fin_cases a
  · exact ⟨e k 1, hswap k 0 1 (hpair k).1 (hpair k).2⟩
  · exact ⟨e k 0, hswap k 1 0 (by linarith [(hpair k).1]) (by linarith [(hpair k).2])⟩

/-- **Conditional decision of `n_4`, with the two-star hypothesis.**  If every
six-point configuration in general position all of whose four-point subsets
repeat a circumradius carries two stars, then `n_4 ≤ 7`.  The hypothesis is
weaker than the one of `isGood_seven_of_octahedral_six`. -/
theorem isGood_seven_of_two_stars
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → TwoStars q) :
    IsGood 7 :=
  isGood_seven_of_central_six
    (fun q hgp hrep => central_six_of_two_stars hgp (H q hgp hrep))

theorem sInf_isGood_le_seven_of_two_stars
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → TwoStars q) :
    sInf {N | IsGood N} ≤ 7 :=
  Nat.sInf_le (isGood_seven_of_two_stars H)

/-- The two-star hypothesis really is weaker: the octahedral one implies it. -/
theorem isGood_seven_of_octahedral_six'
    (H : ∀ q : Fin 6 → Pt, GeneralPosition q → EveryQuadrupleRepeats q → OctahedralSix q) :
    IsGood 7 :=
  isGood_seven_of_two_stars (fun q hgp hrep => twoStars_of_octahedral (H q hgp hrep))




















/-! ## The witness is the centre of the rectangular circum-conic

A witness of the four-point set `{u,v,c,d}` with shared edge `u v` says that the
unique rectangular conic through the four points is centred at the midpoint of
`c d`; equivalently the midpoint of `c d` lies on the nine-point circle of the
triangle `u v c`.  The identity below is the algebraic form of that statement,
and the two special quadruples of the classification -- the parallelogram and the
orthocentric quadruple -- are the two ways for a four-point set to carry more
than one witness. -/


/-! ### The midpoint form of the witness condition -/

/-- The midpoint of two points. -/
noncomputable def mid2 (p q : Pt) : Pt := ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- **The nine-point form of `Psi`.**  The quantity whose vanishing says that
the triangles `u v c` and `u v d` have the same circumradius is, up to the factor
16, the concyclicity determinant of the four midpoints `mid u v`, `mid u c`,
`mid v c`, `mid c d`.  Geometrically: the midpoint of `c d` lies on the
nine-point circle of the triangle `u v c`. -/
theorem psi_eq_sixteen_det4_mid (u v c d : Pt) :
    Psi u v c d = 16 * det4 (mid2 u v) (mid2 u c) (mid2 v c) (mid2 c d) := by
  simp only [Psi, qq, cross, det4, mid2]
  ring

theorem psi_eq_zero_iff_concyclic_mid (u v c d : Pt) :
    Psi u v c d = 0 ↔ Concyclic4 (mid2 u v) (mid2 u c) (mid2 v c) (mid2 c d) := by
  rw [Concyclic4, psi_eq_sixteen_det4_mid]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### The two special quadruples -/

/-- **A parallelogram carries the witness.**  If `u + v = c + d` then the
triangles `u v c` and `u v d` have the same circumradius. -/
theorem psi_of_parallelogram {u v c d : Pt} (h1 : u.1 + v.1 = c.1 + d.1)
    (h2 : u.2 + v.2 = c.2 + d.2) : Psi u v c d = 0 := by
  have hd1 : d.1 = u.1 + v.1 - c.1 := by linarith
  have hd2 : d.2 = u.2 + v.2 - c.2 := by linarith
  simp only [Psi, qq, cross, hd1, hd2]
  ring

/-- Both complementary witnesses of a parallelogram. -/
theorem psi_of_parallelogram_both {u v c d : Pt} (h1 : u.1 + v.1 = c.1 + d.1)
    (h2 : u.2 + v.2 = c.2 + d.2) : Psi u v c d = 0 ∧ Psi c d u v = 0 :=
  ⟨psi_of_parallelogram h1 h2, psi_of_parallelogram h1.symm h2.symm⟩

/-- **An orthocentric quadruple carries the witness.**  If the opposite sides
`u v`, `c d` and `u c`, `v d` are perpendicular -- which is what it means for one
of the four points to be the orthocentre of the other three -- then `Psi`
vanishes.  The proof is the explicit certificate

`Psi = -D1 * cross(c-d, c-u) + D2 * cross(v-u, d-u) + (D2 - D1) * cross(v-u, c-u)`

with `D1 = (u-v).(c-d)` and `D2 = (u-c).(v-d)`. -/
theorem psi_of_orthocentric {u v c d : Pt}
    (h1 : dot2 (vsub u v) (vsub c d) = 0) (h2 : dot2 (vsub u c) (vsub v d) = 0) :
    Psi u v c d = 0 := by
  simp only [dot2, vsub] at h1 h2
  simp only [Psi, qq, cross]
  linear_combination
    (-((c.1 - d.1) * (c.2 - u.2) - (c.2 - d.2) * (c.1 - u.1))
      - ((v.1 - u.1) * (c.2 - u.2) - (v.2 - u.2) * (c.1 - u.1))) * h1
    + (((v.1 - u.1) * (d.2 - u.2) - (v.2 - u.2) * (d.1 - u.1))
      + ((v.1 - u.1) * (c.2 - u.2) - (v.2 - u.2) * (c.1 - u.1))) * h2

/-- The third perpendicularity of an orthocentric quadruple is implied by the
other two:  `(u-v).(c-d) - (u-c).(v-d) + (u-d).(v-c) = 0` is an identity. -/
theorem dot2_sum_identity (u v c d : Pt) :
    dot2 (vsub u v) (vsub c d) - dot2 (vsub u c) (vsub v d)
      + dot2 (vsub u d) (vsub v c) = 0 := by
  simp only [dot2, vsub]; ring

/-- **All six witnesses of an orthocentric quadruple.** -/
theorem psi_six_of_orthocentric {u v c d : Pt}
    (h1 : dot2 (vsub u v) (vsub c d) = 0) (h2 : dot2 (vsub u c) (vsub v d) = 0) :
    Psi u v c d = 0 ∧ Psi c d u v = 0 ∧ Psi u c v d = 0 ∧ Psi v d u c = 0
      ∧ Psi u d v c = 0 ∧ Psi v c u d = 0 := by
  have h3 : dot2 (vsub u d) (vsub v c) = 0 := by
    have := dot2_sum_identity u v c d; simp only [h1, h2] at this ⊢; linarith
  have e1 : dot2 (vsub c d) (vsub u v) = 0 := by
    simp only [dot2, vsub] at h1 ⊢; linarith
  have e2 : dot2 (vsub c u) (vsub d v) = 0 := by
    simp only [dot2, vsub] at h2 ⊢; linarith
  have e3 : dot2 (vsub v d) (vsub u c) = 0 := by
    simp only [dot2, vsub] at h2 ⊢; linarith
  have e4 : dot2 (vsub v u) (vsub d c) = 0 := by
    simp only [dot2, vsub] at h1 ⊢; linarith
  have e5 : dot2 (vsub u v) (vsub d c) = 0 := by
    simp only [dot2, vsub] at h1 ⊢; linarith
  have e6 : dot2 (vsub v c) (vsub u d) = 0 := by
    simp only [dot2, vsub] at h3 ⊢; linarith
  refine ⟨psi_of_orthocentric h1 h2, psi_of_orthocentric e1 e2,
    psi_of_orthocentric h2 h1, psi_of_orthocentric e3 e4,
    psi_of_orthocentric h3 e5, psi_of_orthocentric e6 ?_⟩
  simp only [dot2, vsub] at h1 ⊢; linarith

/-- The circumradius form of the parallelogram case. -/
theorem eqRadSq_of_parallelogram {u v c d : Pt} {r s : ℝ}
    (hab : u ≠ v) (hc : ¬ Collinear3 u v c) (hd : ¬ Collinear3 u v d)
    (hcyc : ¬ Concyclic4 u v c d)
    (hr : CircumRadiusSq u v c r) (hs : CircumRadiusSq u v d s)
    (h1 : u.1 + v.1 = c.1 + d.1) (h2 : u.2 + v.2 = c.2 + d.2) : r = s :=
  (eqRadSq_iff_psi hab hc hd hcyc hr hs).mpr (psi_of_parallelogram h1 h2)

/-- The circumradius form of the orthocentric case. -/
theorem eqRadSq_of_orthocentric {u v c d : Pt} {r s : ℝ}
    (hab : u ≠ v) (hc : ¬ Collinear3 u v c) (hd : ¬ Collinear3 u v d)
    (hcyc : ¬ Concyclic4 u v c d)
    (hr : CircumRadiusSq u v c r) (hs : CircumRadiusSq u v d s)
    (h1 : dot2 (vsub u v) (vsub c d) = 0) (h2 : dot2 (vsub u c) (vsub v d) = 0) :
    r = s :=
  (eqRadSq_iff_psi hab hc hd hcyc hr hs).mpr (psi_of_orthocentric h1 h2)













end DistinctCircumradii

#print axioms DistinctCircumradii.eq_centre_of_refl2_eq_self
#print axioms DistinctCircumradii.centre_eq_of_stable
#print axioms DistinctCircumradii.not_all_erase_central
#print axioms DistinctCircumradii.isGood_seven_of_central_six
#print axioms DistinctCircumradii.sInf_isGood_le_seven_of_central_six
#print axioms DistinctCircumradii.centre_sum_aux
#print axioms DistinctCircumradii.centre_sum
#print axioms DistinctCircumradii.centre_ne_of_not_concyclic
#print axioms DistinctCircumradii.star_sum
#print axioms DistinctCircumradii.fourth_eqRad_of_three
#print axioms DistinctCircumradii.centre_ne_of_gp
#print axioms DistinctCircumradii.central_six_of_octahedral
#print axioms DistinctCircumradii.isGood_seven_of_octahedral_six
#print axioms DistinctCircumradii.sInf_isGood_le_seven_of_octahedral_six
#print axioms DistinctCircumradii.psi_eq_cross2_wprod
#print axioms DistinctCircumradii.normSq_wprod
#print axioms DistinctCircumradii.sqdist_ne_zeroSeven
#print axioms DistinctCircumradii.wprod_ne_zero
#print axioms DistinctCircumradii.cross2_trans
#print axioms DistinctCircumradii.psi_transImplicit
#print axioms DistinctCircumradii.eqRadSq_trans
#print axioms DistinctCircumradii.par_perp_identity
#print axioms DistinctCircumradii.par_or_perp_of_psi
#print axioms DistinctCircumradii.central_six_of_two_stars
#print axioms DistinctCircumradii.isGood_seven_of_two_stars
#print axioms DistinctCircumradii.sInf_isGood_le_seven_of_two_stars
#print axioms DistinctCircumradii.isGood_seven_of_octahedral_six'
#print axioms DistinctCircumradii.psi_eq_sixteen_det4_mid
#print axioms DistinctCircumradii.psi_eq_zero_iff_concyclic_mid
#print axioms DistinctCircumradii.psi_of_parallelogram
#print axioms DistinctCircumradii.psi_of_parallelogram_both
#print axioms DistinctCircumradii.psi_of_orthocentric
#print axioms DistinctCircumradii.dot2_sum_identity
#print axioms DistinctCircumradii.psi_six_of_orthocentric
#print axioms DistinctCircumradii.eqRadSq_of_parallelogram
#print axioms DistinctCircumradii.eqRadSq_of_orthocentric
