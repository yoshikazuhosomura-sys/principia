import Mathlib

/-!
# Algebraic ingredients of the trace computation for a time–band operator

Let `P` be the orthogonal projection onto the functions supported in a window and `B` the
orthogonal projection onto the functions whose Fourier transform is supported in a band.
The compressed operator `A = P B P` satisfies `0 ≤ A ≤ 1`, and the defect `tr (A - A²)`
measures how far the window and the band are from commuting.  Several separate steps of
the computation of `tr (A - A²)` and of `tr (A² - A³)` are pure algebra, and those steps
are what this file contains.

* `TimeBand.compress_sub_sq`, `TimeBand.trace_compress_sub_sq` — the operator identity
  `A - A² = (P B (1 - P)) (P B (1 - P))ᵀ`, which turns the defect into a sum of squares.
  Stated for matrices, i.e. in finite dimensions.
* `TimeBand.range_three`, `TimeBand.window_inter`, `TimeBand.window_length` — the geometry
  behind the reduction of `tr A³` to a two-dimensional integral: the three translated
  windows that occur in `tr A³` meet in an interval of length
  `2L - max |u| (max |v| |u + v|)`.
* `TimeBand.sin_mul_sin_mul_sin`, `TimeBand.sin_shift_decomp` — the two trigonometric
  identities that make the resulting oscillatory integral separate: the first turns the
  product of the three sines into a sum of three sines, the second is what lets the inner
  integral over the simplex be evaluated as a sine integral and a cosine integral.
* `TimeBand.card_gt_ge_trace_sub` — the counting step: if `0 ≤ f i ≤ 1` then the number of
  `i` with `f i > 1 - u` is at least `∑ f i - (∑ f i (1 - f i)) / u`, stated without
  division.
-/

namespace TimeBand

open Finset

/-! ### The trace identity in finite dimensions -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `P` and `B` are idempotent then the compression `A = P B P` satisfies
`A - A² = (P B (1 - P)) ((1 - P) B P)`. -/
theorem compress_sub_sq (P B : Matrix n n ℝ) (hP : P * P = P) (hB : B * B = B) :
    P * B * P - (P * B * P) * (P * B * P)
      = (P * B * (1 - P)) * ((1 - P) * B * P) := by
  have e2 : ((1 : Matrix n n ℝ) - P) * (1 - P) = 1 - P := by
    have h : ((1 : Matrix n n ℝ) - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [h, hP]; noncomm_ring
  have h1 : (P * B * P) * (P * B * P) = P * B * (P * P) * B * P := by noncomm_ring
  have h2 : (P * B * (1 - P)) * ((1 - P) * B * P)
      = P * B * ((1 - P) * (1 - P)) * B * P := by noncomm_ring
  have h3 : P * B * ((1 : Matrix n n ℝ) - P) * B * P
      = P * (B * B) * P - P * B * P * B * P := by noncomm_ring
  rw [h1, hP, h2, e2, h3, hB]

omit [DecidableEq n] in
/-- The trace of a matrix times its transpose is the sum of the squares of its entries. -/
theorem trace_mul_transpose (M : Matrix n n ℝ) :
    (M * Matrix.transpose M).trace = ∑ i, ∑ j, M i j * M i j := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]

/-- For symmetric idempotents `P`, `B` the defect `tr (A - A²)` of the compression
`A = P B P` is the sum of the squares of the entries of `P B (1 - P)`, i.e. the squared
Hilbert–Schmidt norm of the part of `B` that leaks out of the window. -/
theorem trace_compress_sub_sq (P B : Matrix n n ℝ) (hP : P * P = P) (hB : B * B = B)
    (hPs : Matrix.transpose P = P) (hBs : Matrix.transpose B = B) :
    (P * B * P - (P * B * P) * (P * B * P)).trace
      = ∑ i, ∑ j, (P * B * (1 - P)) i j * (P * B * (1 - P)) i j := by
  have ht : ((1 : Matrix n n ℝ) - P) * B * P = Matrix.transpose (P * B * (1 - P)) := by
    simp [Matrix.transpose_mul, Matrix.transpose_sub, hPs, hBs, Matrix.mul_assoc]
  rw [compress_sub_sq P B hP hB, ht, trace_mul_transpose]

end Matrices

/-! ### The geometry of the three windows -/

private theorem abs_eq_max (a : ℝ) : |a| = max a (-a) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]

/-- The range of three real numbers is the largest of their three pairwise distances. -/
theorem range_three (x y z : ℝ) :
    max (max x y) z - min (min x y) z = max (max |x - y| |y - z|) |x - z| := by
  simp only [abs_eq_max, max_def, min_def]
  split_ifs <;> linarith

/-- The three translated windows that occur in `tr A³` meet in an interval. -/
theorem window_inter (L u v : ℝ) :
    Set.Icc (-L) L ∩ Set.Icc (u - L) (u + L) ∩ Set.Icc (u + v - L) (u + v + L)
      = Set.Icc (max (max 0 u) (u + v) - L) (min (min 0 u) (u + v) + L) := by
  have hmax : max (max (-L) (u - L)) (u + v - L) = max (max 0 u) (u + v) - L := by
    simp only [max_def]; split_ifs <;> linarith
  have hmin : min (min L (u + L)) (u + v + L) = min (min 0 u) (u + v) + L := by
    simp only [min_def]; split_ifs <;> linarith
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
    rw [← hmax, ← hmin]
    exact ⟨max_le (max_le h1 h3) h5, le_min (le_min h2 h4) h6⟩
  · rintro ⟨h1, h2⟩
    rw [← hmax] at h1
    rw [← hmin] at h2
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    · exact le_trans h2 (le_trans (min_le_left _ _) (min_le_left _ _))
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
    · exact le_trans h2 (le_trans (min_le_left _ _) (min_le_right _ _))
    · exact le_trans (le_max_right _ _) h1
    · exact le_trans h2 (min_le_right _ _)

/-- The length of that intersection is `2L - max |u| (max |v| |u + v|)`. -/
theorem window_length (L u v : ℝ) :
    (min (min 0 u) (u + v) + L) - (max (max 0 u) (u + v) - L)
      = 2 * L - max (max |u| |v|) |u + v| := by
  have h := range_three 0 u (u + v)
  have e1 : |(0 : ℝ) - u| = |u| := by rw [zero_sub, abs_neg]
  have e2 : |u - (u + v)| = |v| := by rw [show u - (u + v) = -v by ring, abs_neg]
  have e3 : |(0 : ℝ) - (u + v)| = |u + v| := by rw [zero_sub, abs_neg]
  rw [e1, e2, e3] at h
  linarith

/-! ### The two trigonometric identities -/

/-- The product of the three sines occurring in `tr A³` is a sum of three sines. -/
theorem sin_mul_sin_mul_sin (p q : ℝ) :
    Real.sin p * Real.sin q * Real.sin (p + q)
      = (Real.sin (2 * p) + Real.sin (2 * q) - Real.sin (2 * (p + q))) / 4 := by
  have h1 := Real.sin_sq_add_cos_sq p
  have h2 := Real.sin_sq_add_cos_sq q
  simp only [Real.sin_two_mul, Real.sin_add, Real.cos_add]
  linear_combination (Real.sin p * Real.cos p / 2) * h2 + (Real.sin q * Real.cos q / 2) * h1

/-- The separation used for the inner integral over the simplex: the combination
`sin (2tx) + sin (2t(1-x)) - sin (2t)` splits into a multiple of `sin (2tx)` and a multiple
of `1 - cos (2tx)`. -/
theorem sin_shift_decomp (t x : ℝ) :
    Real.sin (2 * t * x) + Real.sin (2 * t * (1 - x)) - Real.sin (2 * t)
      = Real.sin (2 * t * x) * (1 - Real.cos (2 * t))
        - Real.sin (2 * t) * (1 - Real.cos (2 * t * x)) := by
  rw [show 2 * t * (1 - x) = 2 * t - 2 * t * x by ring, Real.sin_sub]
  ring

/-! ### The counting step -/

/-- The counting step (Chebyshev), stated without division: if `0 ≤ f i ≤ 1` on a finite
set `s`, then `u` times the number of `i` with `f i > 1 - u` is at least
`u * ∑ f i - ∑ f i (1 - f i)`. -/
theorem card_gt_ge_trace_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (u : ℝ)
    (hu : 0 < u) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    u * (∑ i ∈ s, f i) - (∑ i ∈ s, f i * (1 - f i))
      ≤ u * ((s.filter (fun i => 1 - u < f i)).card : ℝ) := by
  classical
  set S := s.filter (fun i => 1 - u < f i) with hS
  set T := s.filter (fun i => ¬ (1 - u < f i)) with hT
  have hsplit : (∑ i ∈ S, f i) + (∑ i ∈ T, f i) = ∑ i ∈ s, f i :=
    Finset.sum_filter_add_sum_filter_not s _ f
  have hSle : u * (∑ i ∈ S, f i) ≤ u * (S.card : ℝ) := by
    have : (∑ i ∈ S, f i) ≤ (S.card : ℝ) := by
      calc (∑ i ∈ S, f i) ≤ ∑ _i ∈ S, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => h1 i (Finset.mem_of_mem_filter i hi))
        _ = (S.card : ℝ) := by simp
    exact mul_le_mul_of_nonneg_left this (le_of_lt hu)
  have hTle : u * (∑ i ∈ T, f i) ≤ ∑ i ∈ T, f i * (1 - f i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hmem : i ∈ s := Finset.mem_of_mem_filter i hi
    have hlt : ¬ (1 - u < f i) := (Finset.mem_filter.mp hi).2
    have hle : f i ≤ 1 - u := not_lt.mp hlt
    have hf0 : 0 ≤ f i := h0 i hmem
    nlinarith
  have hmono : (∑ i ∈ T, f i * (1 - f i)) ≤ ∑ i ∈ s, f i * (1 - f i) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi _ => ?_
    have ha := h0 i hi
    have hb := h1 i hi
    nlinarith
  have hexp : u * (∑ i ∈ s, f i) = u * (∑ i ∈ S, f i) + u * (∑ i ∈ T, f i) := by
    rw [← hsplit]; ring
  linarith

end TimeBand

#print axioms TimeBand.compress_sub_sq
#print axioms TimeBand.trace_mul_transpose
#print axioms TimeBand.trace_compress_sub_sq
#print axioms TimeBand.range_three
#print axioms TimeBand.window_inter
#print axioms TimeBand.window_length
#print axioms TimeBand.sin_mul_sin_mul_sin
#print axioms TimeBand.sin_shift_decomp
#print axioms TimeBand.card_gt_ge_trace_sub
