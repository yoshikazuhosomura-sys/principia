import Principia.DistinctCircumradii.Census.Statement

/-!
# 六点の段 — `IsGood`・悪い 6 点の配置・`7 ≤ n_4 ≤ 9`

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

/-- `N` points in general position always contain four points spanning four
triangles of pairwise different circumradii. -/
def IsGood (N : ℕ) : Prop :=
  ∀ p : Fin N → Pt, GeneralPosition p →
    ∃ i j k l : Fin N, i < j ∧ j < k ∧ k < l ∧ FourDistinct (p i) (p j) (p k) (p l)

theorem isGood_mono {N M : ℕ} (hNM : N ≤ M) (h : IsGood N) : IsGood M := by
  intro p hgp
  have hmono : ∀ i j : Fin N, i < j → Fin.castLE hNM i < Fin.castLE hNM j := by
    intro i j hij; exact Fin.strictMono_castLE hNM hij
  have hgp' : GeneralPosition (fun i : Fin N => p (Fin.castLE hNM i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij; exact hgp.1 _ _ (hmono i j hij)
    · intro i j k h1 h2; exact hgp.2.1 _ _ _ (hmono i j h1) (hmono j k h2)
    · intro i j k l h1 h2 h3
      exact hgp.2.2 _ _ _ _ (hmono i j h1) (hmono j k h2) (hmono k l h3)
  obtain ⟨i, j, k, l, h1, h2, h3, hd⟩ := h _ hgp'
  exact ⟨_, _, _, _, hmono i j h1, hmono j k h2, hmono k l h3, hd⟩

theorem not_isGood_of_repeats {N : ℕ} (p : Fin N → Pt) (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) : ¬ IsGood N := by
  intro h
  obtain ⟨i, j, k, l, h1, h2, h3, hd⟩ := h p hgp
  exact hrep i j k l h1 h2 h3 hd

/-- Two of the four triangles sharing a squared circumradius rules out
`FourDistinct`. -/
theorem not_fourDistinct_of_repeat {a b c d : Pt} {t u : Fin 4} {r : ℝ}
    (htu : t ≠ u) (ht : face a b c d t r) (hu : face a b c d u r) :
    ¬ FourDistinct a b c d :=
  fun hd => hd t u htu r r ht hu rfl

/-! ## The configuration -/

/-- Six points with integer coordinates. -/
noncomputable def cfg6 : Fin 6 → Pt
  | 0 => (0, 0)
  | 1 => (1, 2)
  | 2 => (1, 3)
  | 3 => (3, 3)
  | 4 => (3, 4)
  | 5 => (4, 6)

/-! ### General position -/

theorem cfg6_ne : ∀ i j : Fin 6, i < j → cfg6 i ≠ cfg6 j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [cfg6, Prod.ext_iff]

theorem cfg6_ncol_012 : ¬ Collinear3 (cfg6 0) (cfg6 1) (cfg6 2) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_013 : ¬ Collinear3 (cfg6 0) (cfg6 1) (cfg6 3) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_014 : ¬ Collinear3 (cfg6 0) (cfg6 1) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_015 : ¬ Collinear3 (cfg6 0) (cfg6 1) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_023 : ¬ Collinear3 (cfg6 0) (cfg6 2) (cfg6 3) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_024 : ¬ Collinear3 (cfg6 0) (cfg6 2) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_025 : ¬ Collinear3 (cfg6 0) (cfg6 2) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_034 : ¬ Collinear3 (cfg6 0) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_035 : ¬ Collinear3 (cfg6 0) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_045 : ¬ Collinear3 (cfg6 0) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_123 : ¬ Collinear3 (cfg6 1) (cfg6 2) (cfg6 3) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_124 : ¬ Collinear3 (cfg6 1) (cfg6 2) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_125 : ¬ Collinear3 (cfg6 1) (cfg6 2) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_134 : ¬ Collinear3 (cfg6 1) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_135 : ¬ Collinear3 (cfg6 1) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_145 : ¬ Collinear3 (cfg6 1) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_234 : ¬ Collinear3 (cfg6 2) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_235 : ¬ Collinear3 (cfg6 2) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_245 : ¬ Collinear3 (cfg6 2) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_ncol_345 : ¬ Collinear3 (cfg6 3) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Collinear3, cross]

theorem cfg6_noncollinear : ∀ i j k : Fin 6, i < j → j < k →
    ¬ Collinear3 (cfg6 i) (cfg6 j) (cfg6 k) := by
  intro i j k h1 h2
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl | rfl | rfl
      · exact cfg6_ncol_012
      · exact cfg6_ncol_013
      · exact cfg6_ncol_014
      · exact cfg6_ncol_015
    · have hk : k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl | rfl
      · exact cfg6_ncol_023
      · exact cfg6_ncol_024
      · exact cfg6_ncol_025
    · have hk : k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl
      · exact cfg6_ncol_034
      · exact cfg6_ncol_035
    · have hk : k = 5 := by omega
      rcases hk with rfl
      · exact cfg6_ncol_045
  · have hj : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl | rfl
    · have hk : k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl | rfl
      · exact cfg6_ncol_123
      · exact cfg6_ncol_124
      · exact cfg6_ncol_125
    · have hk : k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl
      · exact cfg6_ncol_134
      · exact cfg6_ncol_135
    · have hk : k = 5 := by omega
      rcases hk with rfl
      · exact cfg6_ncol_145
  · have hj : j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl
    · have hk : k = 4 ∨ k = 5 := by omega
      rcases hk with rfl | rfl
      · exact cfg6_ncol_234
      · exact cfg6_ncol_235
    · have hk : k = 5 := by omega
      rcases hk with rfl
      · exact cfg6_ncol_245
  · have hj : j = 4 := by omega
    rcases hj with rfl
    · have hk : k = 5 := by omega
      rcases hk with rfl
      · exact cfg6_ncol_345

theorem cfg6_ncyc_0123 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 3) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0124 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 4) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0125 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0134 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0135 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0145 : ¬ Concyclic4 (cfg6 0) (cfg6 1) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0234 : ¬ Concyclic4 (cfg6 0) (cfg6 2) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0235 : ¬ Concyclic4 (cfg6 0) (cfg6 2) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0245 : ¬ Concyclic4 (cfg6 0) (cfg6 2) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_0345 : ¬ Concyclic4 (cfg6 0) (cfg6 3) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_1234 : ¬ Concyclic4 (cfg6 1) (cfg6 2) (cfg6 3) (cfg6 4) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_1235 : ¬ Concyclic4 (cfg6 1) (cfg6 2) (cfg6 3) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_1245 : ¬ Concyclic4 (cfg6 1) (cfg6 2) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_1345 : ¬ Concyclic4 (cfg6 1) (cfg6 3) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_ncyc_2345 : ¬ Concyclic4 (cfg6 2) (cfg6 3) (cfg6 4) (cfg6 5) := by
  norm_num [cfg6, Concyclic4, det4, cross]

theorem cfg6_nonconcyclic : ∀ i j k l : Fin 6, i < j → j < k → k < l →
    ¬ Concyclic4 (cfg6 i) (cfg6 j) (cfg6 k) (cfg6 l) := by
  intro i j k l h1 h2 h3
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl
    · have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl | rfl
      · have hl : l = 3 ∨ l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl | rfl
        · exact cfg6_ncyc_0123
        · exact cfg6_ncyc_0124
        · exact cfg6_ncyc_0125
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_ncyc_0134
        · exact cfg6_ncyc_0135
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_0145
    · have hk : k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_ncyc_0234
        · exact cfg6_ncyc_0235
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_0245
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_0345
  · have hj : j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl
    · have hk : k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_ncyc_1234
        · exact cfg6_ncyc_1235
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_1245
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_1345
  · have hj : j = 3 := by omega
    rcases hj with rfl
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_ncyc_2345

theorem cfg6_generalPosition : GeneralPosition cfg6 :=
  ⟨cfg6_ne, cfg6_noncollinear, cfg6_nonconcyclic⟩

/-! ### Every quadruple repeats a circumradius -/

/-- In the four-point subset {0,1,2,3} the triangles omitting the vertices 2 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0123 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 3) :=
  not_fourDistinct_of_repeat (t := 2) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((7 / 2), (-1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((-5 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,1,2,4} the triangles omitting the vertices 1 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0124 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 4) :=
  not_fourDistinct_of_repeat (t := 1) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((7 / 2), (1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((-5 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,1,2,5} the triangles omitting the vertices 0 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0125 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 2) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((9 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((-5 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,1,3,4} the triangles omitting the vertices 1 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0134 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 3) (cfg6 4) :=
  not_fourDistinct_of_repeat (t := 1) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((-1 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((7 / 2), (-1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,1,3,5} the triangles omitting the vertices 0 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0135 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 3) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((1 / 2), (11 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((7 / 2), (-1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,1,4,5} the triangles omitting the vertices 0 and 3 have squared circumradius `125/2`. -/
theorem cfg6_rep_0145 :
    ¬ FourDistinct (cfg6 0) (cfg6 1) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (125 / 2)) (by decide)
    ⟨((-7 / 2), (17 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((15 / 2), (-5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,2,3,4} the triangles omitting the vertices 1 and 2 have squared circumradius `25/2`. -/
theorem cfg6_rep_0234 :
    ¬ FourDistinct (cfg6 0) (cfg6 2) (cfg6 3) (cfg6 4) :=
  not_fourDistinct_of_repeat (t := 1) (u := 2) (r := (25 / 2)) (by decide)
    ⟨((-1 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((7 / 2), (1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,2,3,5} the triangles omitting the vertices 0 and 3 have squared circumradius `5`. -/
theorem cfg6_rep_0235 :
    ¬ FourDistinct (cfg6 0) (cfg6 2) (cfg6 3) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := 5) (by decide)
    ⟨(2, 5), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨(2, 1), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,2,4,5} the triangles omitting the vertices 0 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0245 :
    ¬ FourDistinct (cfg6 0) (cfg6 2) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((1 / 2), (13 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((7 / 2), (1 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {0,3,4,5} the triangles omitting the vertices 0 and 3 have squared circumradius `25/2`. -/
theorem cfg6_rep_0345 :
    ¬ FourDistinct (cfg6 0) (cfg6 3) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (25 / 2)) (by decide)
    ⟨((13 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((-1 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {1,2,3,4} the triangles omitting the vertices 0 and 3 have squared circumradius `5/4`. -/
theorem cfg6_rep_1234 :
    ¬ FourDistinct (cfg6 1) (cfg6 2) (cfg6 3) (cfg6 4) :=
  not_fourDistinct_of_repeat (t := 0) (u := 3) (r := (5 / 4)) (by decide)
    ⟨(2, (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨(2, (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {1,2,3,5} the triangles omitting the vertices 1 and 2 have squared circumradius `25/2`. -/
theorem cfg6_rep_1235 :
    ¬ FourDistinct (cfg6 1) (cfg6 2) (cfg6 3) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 1) (u := 2) (r := (25 / 2)) (by decide)
    ⟨((1 / 2), (11 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((9 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {1,2,4,5} the triangles omitting the vertices 0 and 2 have squared circumradius `25/2`. -/
theorem cfg6_rep_1245 :
    ¬ FourDistinct (cfg6 1) (cfg6 2) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 2) (r := (25 / 2)) (by decide)
    ⟨((1 / 2), (13 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((9 / 2), (5 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {1,3,4,5} the triangles omitting the vertices 0 and 2 have squared circumradius `25/2`. -/
theorem cfg6_rep_1345 :
    ¬ FourDistinct (cfg6 1) (cfg6 3) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 2) (r := (25 / 2)) (by decide)
    ⟨((13 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((1 / 2), (11 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

/-- In the four-point subset {2,3,4,5} the triangles omitting the vertices 0 and 1 have squared circumradius `25/2`. -/
theorem cfg6_rep_2345 :
    ¬ FourDistinct (cfg6 2) (cfg6 3) (cfg6 4) (cfg6 5) :=
  not_fourDistinct_of_repeat (t := 0) (u := 1) (r := (25 / 2)) (by decide)
    ⟨((13 / 2), (7 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩
    ⟨((1 / 2), (13 / 2)), by norm_num [cfg6, sqdist], by norm_num [cfg6, sqdist],
      by norm_num [cfg6, sqdist]⟩

theorem cfg6_repeats : EveryQuadrupleRepeats cfg6 := by
  intro i j k l h1 h2 h3
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · have hj : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl | rfl
    · have hk : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl | rfl
      · have hl : l = 3 ∨ l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl | rfl
        · exact cfg6_rep_0123
        · exact cfg6_rep_0124
        · exact cfg6_rep_0125
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_rep_0134
        · exact cfg6_rep_0135
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_0145
    · have hk : k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_rep_0234
        · exact cfg6_rep_0235
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_0245
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_0345
  · have hj : j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl
    · have hk : k = 3 ∨ k = 4 := by omega
      rcases hk with rfl | rfl
      · have hl : l = 4 ∨ l = 5 := by omega
        rcases hl with rfl | rfl
        · exact cfg6_rep_1234
        · exact cfg6_rep_1235
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_1245
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_1345
  · have hj : j = 3 := by omega
    rcases hj with rfl
    · have hk : k = 4 := by omega
      rcases hk with rfl
      · have hl : l = 5 := by omega
        rcases hl with rfl
        · exact cfg6_rep_2345

/-! ### The lower bound -/

theorem not_isGood_six : ¬ IsGood 6 :=
  not_isGood_of_repeats cfg6 cfg6_generalPosition cfg6_repeats

/-- Six points do not suffice: the least `N` is at least `7`. -/
theorem seven_le_of_isGood {N : ℕ} (h : IsGood N) : 7 ≤ N := by
  by_contra hc
  exact not_isGood_six (isGood_mono (by omega) h)

/-! ## Uniqueness of the squared circumradius, and the determinant test -/

theorem circumRadiusSq_uniqueSix {a b c : Pt} {r s : ℝ} (h : ¬ Collinear3 a b c)
    (hr : CircumRadiusSq a b c r) (hs : CircumRadiusSq a b c s) : r = s := by
  obtain ⟨o, ha, hb, hc⟩ := hr
  obtain ⟨o', ha', hb', hc'⟩ := hs
  have hcr : cross a b c ≠ 0 := fun hh => h hh
  simp only [sqdist] at ha hb hc ha' hb' hc'
  have e1 : (o.1 - o'.1) * (b.1 - a.1) + (o.2 - o'.2) * (b.2 - a.2) = 0 := by
    linear_combination (ha - hb - ha' + hb') / 2
  have e2 : (o.1 - o'.1) * (c.1 - a.1) + (o.2 - o'.2) * (c.2 - a.2) = 0 := by
    linear_combination (ha - hc - ha' + hc') / 2
  have hx : (o.1 - o'.1) * cross a b c = 0 := by
    simp only [cross]
    linear_combination (c.2 - a.2) * e1 - (b.2 - a.2) * e2
  have hy : (o.2 - o'.2) * cross a b c = 0 := by
    simp only [cross]
    linear_combination (b.1 - a.1) * e2 - (c.1 - a.1) * e1
  have h1 : o.1 = o'.1 := by
    rcases mul_eq_zero.mp hx with h' | h'
    · linarith
    · exact absurd h' hcr
  have h2 : o.2 = o'.2 := by
    rcases mul_eq_zero.mp hy with h' | h'
    · linarith
    · exact absurd h' hcr
  rw [← ha, ← ha', h1, h2]

theorem concyclic4_of_common_center {a b c d o : Pt} {r : ℝ}
    (ha : sqdist o a = r) (hb : sqdist o b = r) (hc : sqdist o c = r)
    (hd : sqdist o d = r) : Concyclic4 a b c d := by
  simp only [sqdist] at ha hb hc hd
  simp only [Concyclic4, det4, cross]
  linear_combination ((c.1 - b.1) * (d.2 - b.2) - (c.2 - b.2) * (d.1 - b.1)) * ha
    - ((c.1 - a.1) * (d.2 - a.2) - (c.2 - a.2) * (d.1 - a.1)) * hb
    + ((b.1 - a.1) * (d.2 - a.2) - (b.2 - a.2) * (d.1 - a.1)) * hc
    - ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) * hd

/-! ## Permutations -/

theorem circumRadiusSq_swap₂₃ {a b c : Pt} {r : ℝ} (h : CircumRadiusSq a b c r) :
    CircumRadiusSq a c b r := by obtain ⟨o, h1, h2, h3⟩ := h; exact ⟨o, h1, h3, h2⟩

theorem circumRadiusSq_rot {a b c : Pt} {r : ℝ} (h : CircumRadiusSq a b c r) :
    CircumRadiusSq b c a r := by obtain ⟨o, h1, h2, h3⟩ := h; exact ⟨o, h2, h3, h1⟩

theorem no_common_center_of_gp {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p)
    {S : Finset (Fin N)} (hS : S.card = 4) {o : Pt} {r : ℝ}
    (h : ∀ m ∈ S, sqdist o (p m) = r) : False := by
  have hm : ∀ i : Fin 4, S.orderEmbOfFin hS i ∈ S := fun i => S.orderEmbOfFin_mem hS i
  exact hgp.2.2 _ _ _ _ ((S.orderEmbOfFin hS).strictMono (show (0 : Fin 4) < 1 by decide))
    ((S.orderEmbOfFin hS).strictMono (show (1 : Fin 4) < 2 by decide))
    ((S.orderEmbOfFin hS).strictMono (show (2 : Fin 4) < 3 by decide))
    (concyclic4_of_common_center (h _ (hm 0)) (h _ (hm 1)) (h _ (hm 2)) (h _ (hm 3)))

/-! ## Three points equidistant from two given points -/

theorem center_pair_aux {p q u₂ v₂ u₃ v₃ A B : ℝ} (hW : p ^ 2 + q ^ 2 ≠ 0)
    (A2 : u₂ * p + v₂ * q = 0) (A3 : u₃ * p + v₃ * q = 0)
    (B2 : u₂ ^ 2 + v₂ ^ 2 + 2 * (u₂ * A + v₂ * B) = 0)
    (B3 : u₃ ^ 2 + v₃ ^ 2 + 2 * (u₃ * A + v₃ * B) = 0) :
    (u₂ = 0 ∧ v₂ = 0) ∨ (u₃ = 0 ∧ v₃ = 0) ∨ (u₂ = u₃ ∧ v₂ = v₃) := by
  have f2 : (v₂ * p - u₂ * q) * ((v₂ * p - u₂ * q) + 2 * (p * B - q * A)) = 0 := by
    linear_combination (p ^ 2 + q ^ 2) * B2
      - (u₂ * p + v₂ * q + 2 * (p * A + q * B)) * A2
  have f3 : (v₃ * p - u₃ * q) * ((v₃ * p - u₃ * q) + 2 * (p * B - q * A)) = 0 := by
    linear_combination (p ^ 2 + q ^ 2) * B3
      - (u₃ * p + v₃ * q + 2 * (p * A + q * B)) * A3
  rcases mul_eq_zero.mp f2 with hL2 | hL2
  · refine Or.inl ⟨?_, ?_⟩
    · have h0 : (p ^ 2 + q ^ 2) * u₂ = 0 := by linear_combination p * A2 - q * hL2
      exact (mul_eq_zero.mp h0).resolve_left hW
    · have h0 : (p ^ 2 + q ^ 2) * v₂ = 0 := by linear_combination q * A2 + p * hL2
      exact (mul_eq_zero.mp h0).resolve_left hW
  · rcases mul_eq_zero.mp f3 with hL3 | hL3
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have h0 : (p ^ 2 + q ^ 2) * u₃ = 0 := by linear_combination p * A3 - q * hL3
        exact (mul_eq_zero.mp h0).resolve_left hW
      · have h0 : (p ^ 2 + q ^ 2) * v₃ = 0 := by linear_combination q * A3 + p * hL3
        exact (mul_eq_zero.mp h0).resolve_left hW
    · have hLeq : v₂ * p - u₂ * q = v₃ * p - u₃ * q := by linarith
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · have h0 : (p ^ 2 + q ^ 2) * (u₂ - u₃) = 0 := by
          linear_combination p * A2 - p * A3 - q * hLeq
        have := (mul_eq_zero.mp h0).resolve_left hW
        linarith
      · have h0 : (p ^ 2 + q ^ 2) * (v₂ - v₃) = 0 := by
          linear_combination q * A2 - q * A3 + p * hLeq
        have := (mul_eq_zero.mp h0).resolve_left hW
        linarith

theorem center_pair {a b o₁ o₂ o₃ : Pt} {r : ℝ} (hab : a ≠ b)
    (h₁a : sqdist o₁ a = r) (h₁b : sqdist o₁ b = r)
    (h₂a : sqdist o₂ a = r) (h₂b : sqdist o₂ b = r)
    (h₃a : sqdist o₃ a = r) (h₃b : sqdist o₃ b = r) :
    o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃ := by
  simp only [sqdist] at h₁a h₁b h₂a h₂b h₃a h₃b
  have hW : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h
    exact hab (Prod.ext_iff.mpr
      ⟨by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)],
       by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]⟩)
  have A2 : (o₂.1 - o₁.1) * (b.1 - a.1) + (o₂.2 - o₁.2) * (b.2 - a.2) = 0 := by
    linear_combination (h₂a - h₂b - h₁a + h₁b) / 2
  have A3 : (o₃.1 - o₁.1) * (b.1 - a.1) + (o₃.2 - o₁.2) * (b.2 - a.2) = 0 := by
    linear_combination (h₃a - h₃b - h₁a + h₁b) / 2
  have B2 : (o₂.1 - o₁.1) ^ 2 + (o₂.2 - o₁.2) ^ 2
      + 2 * ((o₂.1 - o₁.1) * (o₁.1 - a.1) + (o₂.2 - o₁.2) * (o₁.2 - a.2)) = 0 := by
    linear_combination h₂a - h₁a
  have B3 : (o₃.1 - o₁.1) ^ 2 + (o₃.2 - o₁.2) ^ 2
      + 2 * ((o₃.1 - o₁.1) * (o₁.1 - a.1) + (o₃.2 - o₁.2) * (o₁.2 - a.2)) = 0 := by
    linear_combination h₃a - h₁a
  rcases center_pair_aux hW A2 A3 B2 B3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl (Prod.ext_iff.mpr ⟨by linarith, by linarith⟩)
  · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨by linarith, by linarith⟩))
  · exact Or.inr (Or.inr (Prod.ext_iff.mpr ⟨by linarith, by linarith⟩))

/-! ## The shared edge of a repeated circumradius -/

def EqRad (a b c d : Pt) : Prop :=
  ∃ r : ℝ, CircumRadiusSq a b c r ∧ CircumRadiusSq a b d r

theorem eqRad_symm {a b c d : Pt} (h : EqRad a b c d) : EqRad a b d c := by
  obtain ⟨r, h1, h2⟩ := h; exact ⟨r, h2, h1⟩

theorem eqRad_of_not_fourDistinct {a b c d : Pt} (h : ¬ FourDistinct a b c d) :
    EqRad c d a b ∨ EqRad b d a c ∨ EqRad b c a d ∨
      EqRad a d b c ∨ EqRad a c b d ∨ EqRad a b c d := by
  rw [FourDistinct] at h
  push Not at h
  obtain ⟨t, u, htu, r, s, ht, hs, hrs⟩ := h
  rw [hrs] at ht
  fin_cases t <;> fin_cases u <;> simp only [face] at ht hs <;>
    first
      | exact absurd rfl htu
      | exact Or.inl ⟨s, circumRadiusSq_rot hs, circumRadiusSq_rot ht⟩
      | exact Or.inl ⟨s, circumRadiusSq_rot ht, circumRadiusSq_rot hs⟩
      | exact Or.inr (Or.inl ⟨s, circumRadiusSq_rot hs, circumRadiusSq_swap₂₃ ht⟩)
      | exact Or.inr (Or.inl ⟨s, circumRadiusSq_rot ht, circumRadiusSq_swap₂₃ hs⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨s, circumRadiusSq_rot hs, ht⟩))
      | exact Or.inr (Or.inr (Or.inl ⟨s, circumRadiusSq_rot ht, hs⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, circumRadiusSq_swap₂₃ hs, circumRadiusSq_swap₂₃ ht⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, circumRadiusSq_swap₂₃ ht, circumRadiusSq_swap₂₃ hs⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, circumRadiusSq_swap₂₃ hs, ht⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, circumRadiusSq_swap₂₃ ht, hs⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, hs, ht⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ht, hs⟩))))

/-! ## The shared edge, and two points that cannot share a partner -/

theorem card_four {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]),
    Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- On one edge, two different points cannot both be the mirror partner of a third:
that would put four of the points on one circle. -/
theorem not_two_eqRad {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p)
    {x y c w w' : Fin N} (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxw : x ≠ w) (hyw : y ≠ w) (hcw : c ≠ w)
    (hxw' : x ≠ w') (hyw' : y ≠ w') (hcw' : c ≠ w') (hww' : w ≠ w')
    (h1 : EqRad (p x) (p y) (p c) (p w)) (h2 : EqRad (p x) (p y) (p c) (p w')) :
    False := by
  obtain ⟨r, hc1, ow, how1, how2, how3⟩ := h1
  obtain ⟨r', hc2, ow', how1', how2', how3'⟩ := h2
  have hrr : r = r' := circumRadiusSq_uniqueSix (ncol_of_gp hgp hxy hxc hyc) hc1 hc2
  subst hrr
  obtain ⟨oc, hoc1, hoc2, hoc3⟩ := hc1
  have hab : p x ≠ p y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact hgp.1 x y h
    · exact (hgp.1 y x h).symm
  rcases center_pair hab hoc1 hoc2 how1 how2 how1' how2' with h | h | h
  · exact no_common_center_of_gp hgp (S := {x, y, c, w})
      (card_four hxy hxc hxw hyc hyw hcw) (o := oc) (r := r)
      (by intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          · exact hoc1
          · exact hoc2
          · exact hoc3
          · rw [h]; exact how3)
  · exact no_common_center_of_gp hgp (S := {x, y, c, w'})
      (card_four hxy hxc hxw' hyc hyw' hcw') (o := oc) (r := r)
      (by intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          · exact hoc1
          · exact hoc2
          · exact hoc3
          · rw [h]; exact how3')
  · exact no_common_center_of_gp hgp (S := {x, y, w, w'})
      (card_four hxy hxw hxw' hyw hyw' hww') (o := ow) (r := r)
      (by intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl | rfl
          · exact how1
          · exact how2
          · exact how3
          · rw [h]; exact how3')

/-- Nine points in general position always contain four whose four triangles have
pairwise different circumradii. -/
theorem isGood_nine : IsGood 9 := by
  classical
  intro P hgp
  by_contra hno
  push Not at hno
  have hex : ∀ Q ∈ (Finset.univ : Finset (Fin 9)).powersetCard 4,
      ∃ x y z w : Fin 9, x < y ∧ z < w ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧
        ({x, y, z, w} : Finset (Fin 9)) = Q ∧ EqRad (P x) (P y) (P z) (P w) := by
    intro Q hQ
    have hQ4 : Q.card = 4 := (Finset.mem_powersetCard.mp hQ).2
    set g := Q.orderEmbOfFin hQ4 with hgdef
    have h01 : g 0 < g 1 := g.strictMono (by decide)
    have h12 : g 1 < g 2 := g.strictMono (by decide)
    have h23 : g 2 < g 3 := g.strictMono (by decide)
    have h02 : g 0 < g 2 := lt_trans h01 h12
    have h13 : g 1 < g 3 := lt_trans h12 h23
    have h03 : g 0 < g 3 := lt_trans h02 h23
    have himg : ({g 0, g 1, g 2, g 3} : Finset (Fin 9)) = Q := by
      have hu : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
      have hh := Finset.image_orderEmbOfFin_univ Q hQ4
      rw [hu] at hh
      simpa [← hgdef] using hh
    rcases eqRad_of_not_fourDistinct (hno (g 0) (g 1) (g 2) (g 3) h01 h12 h23) with
      h | h | h | h | h | h
    · exact ⟨g 2, g 3, g 0, g 1, h23, h01, h02.ne', h12.ne', h03.ne', h13.ne',
        by rw [← himg]; ext u; simp; tauto, h⟩
    · exact ⟨g 1, g 3, g 0, g 2, h13, h02, h01.ne', h12.ne, h03.ne', h23.ne',
        by rw [← himg]; ext u; simp; tauto, h⟩
    · exact ⟨g 1, g 2, g 0, g 3, h12, h03, h01.ne', h13.ne, h02.ne', h23.ne,
        by rw [← himg]; ext u; simp; tauto, h⟩
    · exact ⟨g 0, g 3, g 1, g 2, h03, h12, h01.ne, h02.ne, h13.ne', h23.ne',
        by rw [← himg]; ext u; simp; tauto, h⟩
    · exact ⟨g 0, g 2, g 1, g 3, h02, h13, h01.ne, h03.ne, h12.ne', h23.ne,
        by rw [← himg]; ext u; simp; tauto, h⟩
    · exact ⟨g 0, g 1, g 2, g 3, h01, h23, h02.ne, h03.ne, h12.ne, h13.ne, himg, h⟩
  choose! X Y Z W hXY hZW hXZ hXW hYZ hYW hQset hEq using hex
  have hScard : ((Finset.univ : Finset (Fin 9)).powersetCard 4).card = 126 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rfl
  have hTcard :
      ((Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun e => e.1 < e.2)).card = 36 := by
    decide
  obtain ⟨e, heT, hlt⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := fun Q : Finset (Fin 9) => (X Q, Y Q))
      (s := (Finset.univ : Finset (Fin 9)).powersetCard 4)
      (t := (Finset.univ : Finset (Fin 9 × Fin 9)).filter (fun e => e.1 < e.2))
      (n := 3)
      (by intro Q hQ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hXY Q hQ)
      (by rw [hTcard, hScard]; norm_num)
  have he12 : e.1 < e.2 := (Finset.mem_filter.mp heT).2
  set F := ((Finset.univ : Finset (Fin 9)).powersetCard 4).filter
    (fun Q => (X Q, Y Q) = e) with hFdef
  have hmemF : ∀ Q ∈ F, Q ∈ (Finset.univ : Finset (Fin 9)).powersetCard 4 ∧ X Q = e.1 ∧ Y Q = e.2 := by
    intro Q hQ
    rw [hFdef, Finset.mem_filter] at hQ
    exact ⟨hQ.1, by rw [← hQ.2], by rw [← hQ.2]⟩
  have hFcard : 3 < F.card := by rw [hFdef]; exact hlt
  set G := F.image (fun Q => ({Z Q, W Q} : Finset (Fin 9))) with hGdef
  -- the map is injective on the fibre
  have hinj : Set.InjOn (fun Q => ({Z Q, W Q} : Finset (Fin 9))) F := by
    intro Q hQ Q' hQ' heq
    obtain ⟨hQs, hx, hy⟩ := hmemF Q hQ
    obtain ⟨hQs', hx', hy'⟩ := hmemF Q' hQ'
    have heq' : ({Z Q, W Q} : Finset (Fin 9)) = {Z Q', W Q'} := heq
    rw [← hQset Q hQs, ← hQset Q' hQs', hx, hy, hx', hy', heq']
  have hGcard : 3 < G.card := by
    rw [hGdef, Finset.card_image_of_injOn hinj]; exact hFcard
  -- each element of G is a pair, and two of them are disjoint
  have key : ∀ Q ∈ F, ∀ cc ∈ ({Z Q, W Q} : Finset (Fin 9)),
      ∃ v : Fin 9, ({Z Q, W Q} : Finset (Fin 9)) = {cc, v} ∧ cc ≠ v ∧
        e.1 ≠ cc ∧ e.2 ≠ cc ∧ e.1 ≠ v ∧ e.2 ≠ v ∧
        EqRad (P e.1) (P e.2) (P cc) (P v) := by
    intro Q hQ cc hcc
    obtain ⟨hQs, hx, hy⟩ := hmemF Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcc
    rcases hcc with rfl | rfl
    · exact ⟨W Q, rfl, (hZW Q hQs).ne, hx ▸ hXZ Q hQs, hy ▸ hYZ Q hQs,
        hx ▸ hXW Q hQs, hy ▸ hYW Q hQs, by rw [← hx, ← hy]; exact hEq Q hQs⟩
    · exact ⟨Z Q, Finset.pair_comm _ _, (hZW Q hQs).ne', hx ▸ hXW Q hQs, hy ▸ hYW Q hQs,
        hx ▸ hXZ Q hQs, hy ▸ hYZ Q hQs,
        by rw [← hx, ← hy]; exact eqRad_symm (hEq Q hQs)⟩
  have hdisj : (G : Set (Finset (Fin 9))).PairwiseDisjoint id := by
    intro m₁ hm₁ m₂ hm₂ hne
    simp only [Function.onFun, id]
    rw [Finset.disjoint_left]
    intro cc hc1 hc2
    rw [hGdef] at hm₁ hm₂
    obtain ⟨Q₁, hQ₁, rfl⟩ := Finset.mem_image.mp hm₁
    obtain ⟨Q₂, hQ₂, rfl⟩ := Finset.mem_image.mp hm₂
    obtain ⟨v₁, hm1, hne1, hx1, hy1, hxv1, hyv1, hE1⟩ := key Q₁ hQ₁ cc hc1
    obtain ⟨v₂, hm2, hne2, _, _, hxv2, hyv2, hE2⟩ := key Q₂ hQ₂ cc hc2
    have hvv : v₁ ≠ v₂ := by
      intro hv
      apply hne
      rw [hm1, hm2, hv]
    exact not_two_eqRad hgp he12.ne hx1 hy1 hxv1 hyv1 hne1 hxv2 hyv2 hne2 hvv hE1 hE2
  -- the pairs live in the seven indices off the edge
  have hsub : G.biUnion id ⊆ (Finset.univ : Finset (Fin 9)) \ {e.1, e.2} := by
    intro u hu
    rw [Finset.mem_biUnion] at hu
    obtain ⟨m, hm, hum⟩ := hu
    rw [hGdef] at hm
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨v, _, _, hx1, hy1, hxv1, hyv1, _⟩ := key Q hQ u hum
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm⟩
  have hcard2 : ∀ m ∈ G, m.card = 2 := by
    intro m hm
    rw [hGdef] at hm
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hQs, _, _⟩ := hmemF Q hQ
    rw [Finset.card_insert_of_notMem (by simp [(hZW Q hQs).ne]), Finset.card_singleton]
  have h7 : ((Finset.univ : Finset (Fin 9)) \ {e.1, e.2}).card = 7 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin, Finset.card_insert_of_notMem (by simp [he12.ne]),
      Finset.card_singleton]
  have hsum : (G.biUnion id).card = 2 * G.card := by
    rw [Finset.card_biUnion hdisj]
    simp only [id_eq]
    rw [Finset.sum_congr rfl (fun m hm => hcard2 m hm), Finset.sum_const, smul_eq_mul]
    ring
  have := Finset.card_le_card hsub
  rw [hsum, h7] at this
  omega


/-! ## The two bounds together -/

/-- The least `N` such that every `N` points of the plane in general position
contain four points spanning four triangles of pairwise different circumradii
lies between `7` and `9`. -/
theorem seven_le_sInf_isGood_and_sInf_isGood_le_nine :
    7 ≤ sInf {N : ℕ | IsGood N} ∧ sInf {N : ℕ | IsGood N} ≤ 9 := by
  have hne : {N : ℕ | IsGood N}.Nonempty := ⟨9, isGood_nine⟩
  exact ⟨seven_le_of_isGood (Nat.sInf_mem hne), Nat.sInf_le isGood_nine⟩























end DistinctCircumradii

#print axioms DistinctCircumradii.isGood_mono
#print axioms DistinctCircumradii.not_isGood_of_repeats
#print axioms DistinctCircumradii.not_fourDistinct_of_repeat
#print axioms DistinctCircumradii.cfg6_ne
#print axioms DistinctCircumradii.cfg6_ncol_012
#print axioms DistinctCircumradii.cfg6_ncol_013
#print axioms DistinctCircumradii.cfg6_ncol_014
#print axioms DistinctCircumradii.cfg6_ncol_015
#print axioms DistinctCircumradii.cfg6_ncol_023
#print axioms DistinctCircumradii.cfg6_ncol_024
#print axioms DistinctCircumradii.cfg6_ncol_025
#print axioms DistinctCircumradii.cfg6_ncol_034
#print axioms DistinctCircumradii.cfg6_ncol_035
#print axioms DistinctCircumradii.cfg6_ncol_045
#print axioms DistinctCircumradii.cfg6_ncol_123
#print axioms DistinctCircumradii.cfg6_ncol_124
#print axioms DistinctCircumradii.cfg6_ncol_125
#print axioms DistinctCircumradii.cfg6_ncol_134
#print axioms DistinctCircumradii.cfg6_ncol_135
#print axioms DistinctCircumradii.cfg6_ncol_145
#print axioms DistinctCircumradii.cfg6_ncol_234
#print axioms DistinctCircumradii.cfg6_ncol_235
#print axioms DistinctCircumradii.cfg6_ncol_245
#print axioms DistinctCircumradii.cfg6_ncol_345
#print axioms DistinctCircumradii.cfg6_noncollinear
#print axioms DistinctCircumradii.cfg6_ncyc_0123
#print axioms DistinctCircumradii.cfg6_ncyc_0124
#print axioms DistinctCircumradii.cfg6_ncyc_0125
#print axioms DistinctCircumradii.cfg6_ncyc_0134
#print axioms DistinctCircumradii.cfg6_ncyc_0135
#print axioms DistinctCircumradii.cfg6_ncyc_0145
#print axioms DistinctCircumradii.cfg6_ncyc_0234
#print axioms DistinctCircumradii.cfg6_ncyc_0235
#print axioms DistinctCircumradii.cfg6_ncyc_0245
#print axioms DistinctCircumradii.cfg6_ncyc_0345
#print axioms DistinctCircumradii.cfg6_ncyc_1234
#print axioms DistinctCircumradii.cfg6_ncyc_1235
#print axioms DistinctCircumradii.cfg6_ncyc_1245
#print axioms DistinctCircumradii.cfg6_ncyc_1345
#print axioms DistinctCircumradii.cfg6_ncyc_2345
#print axioms DistinctCircumradii.cfg6_nonconcyclic
#print axioms DistinctCircumradii.cfg6_generalPosition
#print axioms DistinctCircumradii.cfg6_rep_0123
#print axioms DistinctCircumradii.cfg6_rep_0124
#print axioms DistinctCircumradii.cfg6_rep_0125
#print axioms DistinctCircumradii.cfg6_rep_0134
#print axioms DistinctCircumradii.cfg6_rep_0135
#print axioms DistinctCircumradii.cfg6_rep_0145
#print axioms DistinctCircumradii.cfg6_rep_0234
#print axioms DistinctCircumradii.cfg6_rep_0235
#print axioms DistinctCircumradii.cfg6_rep_0245
#print axioms DistinctCircumradii.cfg6_rep_0345
#print axioms DistinctCircumradii.cfg6_rep_1234
#print axioms DistinctCircumradii.cfg6_rep_1235
#print axioms DistinctCircumradii.cfg6_rep_1245
#print axioms DistinctCircumradii.cfg6_rep_1345
#print axioms DistinctCircumradii.cfg6_rep_2345
#print axioms DistinctCircumradii.cfg6_repeats
#print axioms DistinctCircumradii.not_isGood_six
#print axioms DistinctCircumradii.seven_le_of_isGood
#print axioms DistinctCircumradii.circumRadiusSq_uniqueSix
#print axioms DistinctCircumradii.concyclic4_of_common_center
#print axioms DistinctCircumradii.circumRadiusSq_swap₂₃
#print axioms DistinctCircumradii.circumRadiusSq_rot
#print axioms DistinctCircumradii.no_common_center_of_gp
#print axioms DistinctCircumradii.center_pair_aux
#print axioms DistinctCircumradii.center_pair
#print axioms DistinctCircumradii.eqRad_symm
#print axioms DistinctCircumradii.eqRad_of_not_fourDistinct
#print axioms DistinctCircumradii.card_four
#print axioms DistinctCircumradii.not_two_eqRad
#print axioms DistinctCircumradii.isGood_nine
#print axioms DistinctCircumradii.seven_le_sInf_isGood_and_sInf_isGood_le_nine
