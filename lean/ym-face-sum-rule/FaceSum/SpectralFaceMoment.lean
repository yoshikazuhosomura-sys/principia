import Mathlib

/-!
# Moments of a set of faces, bounded by one number: the largest eigenvalue of a principal submatrix of the projection

At the level of the free (Gaussian) field, the moment generating function of the sum of the angles of a set `X` of faces is
`log M_X(t) = (3/2) Σ_i (-log (1 - t μ_i))` (`μ_i` the eigenvalues of the principal submatrix `P_X` of the projection).
Here the eigenvalues are treated as a family of numbers in `[0, m]`, and we close

* for one number, `-log(1 - tμ) ≤ (μ/m)(-log(1 - tm))` (concavity of log),
* for the sum over the family, `Σ (-log(1 - tμ_i)) ≤ (Σ μ_i / m) (-log(1 - tm))`,
* when the trace is `n/2` (diagonal entries 1/2), the log-moment per face is at most `(3/(4m))(-log(1 - tm))`,
* `μ ↦ -log(1 - tμ)/μ` is monotone (a larger top eigenvalue gives a worse bound),
* the seam to the Chernoff bound.

The eigenvalues and the trace themselves are computed outside Lean.
-/

namespace FaceSpectrum

open Real

/-- Concavity of log: if `0 ≤ s ≤ 1` and `0 ≤ a < 1` then `s log(1-a) ≤ log(1 - s a)`. -/
theorem smul_log_le_log (s a : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (_ha0 : 0 ≤ a) (ha1 : a < 1) :
    s * Real.log (1 - a) ≤ Real.log (1 - s * a) := by
  have hmem1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by simp
  have hmem2 : (1 - a) ∈ Set.Ioi (0:ℝ) := by simp; linarith
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 hmem1 hmem2 (by linarith : (0:ℝ) ≤ 1 - s) hs0
    (by ring : (1 - s) + s = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  have he : (1 - s) * 1 + s * (1 - a) = 1 - s * a := by ring
  rw [he] at h
  exact h

/-- Chord bound for one eigenvalue: for `0 ≤ μ ≤ m`, `0 < m`, `0 ≤ t`, `t m < 1`,
`-log(1 - tμ) ≤ (μ/m) (-log(1 - tm))`. -/
theorem neg_log_le_chord (t μ m : ℝ) (hm : 0 < m) (hμ0 : 0 ≤ μ) (hμm : μ ≤ m) (ht : 0 ≤ t)
    (htm : t * m < 1) :
    -Real.log (1 - t * μ) ≤ (μ / m) * (-Real.log (1 - t * m)) := by
  have hs0 : 0 ≤ μ / m := div_nonneg hμ0 hm.le
  have hs1 : μ / m ≤ 1 := (div_le_one hm).2 hμm
  have h := smul_log_le_log (μ / m) (t * m) hs0 hs1 (mul_nonneg ht hm.le) htm
  have he : μ / m * (t * m) = t * μ := by field_simp
  rw [he] at h
  linarith

/-- Sum over a family: if each `μ i ∈ [0, m]` then `Σ -log(1 - tμ_i) ≤ (Σ μ_i / m)(-log(1 - tm))`. -/
theorem sum_neg_log_le {ι : Type*} (s : Finset ι) (μ : ι → ℝ) (t m : ℝ) (hm : 0 < m)
    (hμ0 : ∀ i ∈ s, 0 ≤ μ i) (hμm : ∀ i ∈ s, μ i ≤ m) (ht : 0 ≤ t) (htm : t * m < 1) :
    ∑ i ∈ s, -Real.log (1 - t * μ i) ≤ (∑ i ∈ s, μ i) / m * (-Real.log (1 - t * m)) := by
  calc ∑ i ∈ s, -Real.log (1 - t * μ i)
      ≤ ∑ i ∈ s, (μ i / m) * (-Real.log (1 - t * m)) :=
        Finset.sum_le_sum (fun i hi => neg_log_le_chord t (μ i) m hm (hμ0 i hi) (hμm i hi) ht htm)
    _ = (∑ i ∈ s, μ i) / m * (-Real.log (1 - t * m)) := by
        rw [← Finset.sum_mul, Finset.sum_div]

/-- If the trace is `n/2`, the Gaussian log-moment `(3/2) Σ -log(1-tμ_i)` is at most
`n · (3/(4m)) (-log(1 - tm))` (the bound per face depends only on the upper bound `m` of the top eigenvalue). -/
theorem logMoment_le_per_face {ι : Type*} (s : Finset ι) (μ : ι → ℝ) (t m : ℝ) (hm : 0 < m)
    (hμ0 : ∀ i ∈ s, 0 ≤ μ i) (hμm : ∀ i ∈ s, μ i ≤ m) (ht : 0 ≤ t) (htm : t * m < 1)
    (htr : ∑ i ∈ s, μ i = (s.card : ℝ) / 2) :
    (3 / 2) * ∑ i ∈ s, -Real.log (1 - t * μ i)
      ≤ (s.card : ℝ) * ((3 / (4 * m)) * (-Real.log (1 - t * m))) := by
  have h := sum_neg_log_le s μ t m hm hμ0 hμm ht htm
  rw [htr] at h
  have hpos : 0 ≤ (3:ℝ) / 2 := by norm_num
  have h2 := mul_le_mul_of_nonneg_left h hpos
  have he : (3:ℝ) / 2 * ((s.card : ℝ) / 2 / m * (-Real.log (1 - t * m)))
      = (s.card : ℝ) * ((3 / (4 * m)) * (-Real.log (1 - t * m))) := by
    field_simp; ring
  linarith

/-- Monotonicity: if `0 < μ ≤ m` and `t m < 1` then `-log(1-tμ)/μ ≤ -log(1-tm)/m`.
The larger the top eigenvalue of a shape, the larger the bound per face. -/
theorem chord_slope_mono (t μ m : ℝ) (hμ : 0 < μ) (hμm : μ ≤ m) (ht : 0 ≤ t) (htm : t * m < 1) :
    -Real.log (1 - t * μ) / μ ≤ -Real.log (1 - t * m) / m := by
  have hm : 0 < m := lt_of_lt_of_le hμ hμm
  have h := neg_log_le_chord t μ m hm hμ.le hμm ht htm
  rw [div_le_div_iff₀ hμ hm]
  have : μ / m * -Real.log (1 - t * m) * m = μ * -Real.log (1 - t * m) := by field_simp
  nlinarith [h, hm]

/-- Back to a single face, `m = 1/2` (its own diagonal): for `m = 1/2` the bound per face is
`(3/2)(-log(1 - t/2))`, i.e. the logarithm of the single-face moment `(1 - t/2)^{-3/2}`. -/
theorem single_face_case (t : ℝ) :
    (3 / (4 * (1/2 : ℝ))) * (-Real.log (1 - t * (1/2))) = (3/2) * (-Real.log (1 - t / 2)) := by
  ring_nf

/-- Seam to Chernoff: if `P ≤ exp(-t n y) M`, `log M ≤ n B` and `M > 0` then
`P ≤ exp(n(-t y + B))`. -/
theorem chernoff_glue (P M t y B n : ℝ) (hM : 0 < M) (hP : P ≤ Real.exp (-t * n * y) * M)
    (hlog : Real.log M ≤ n * B) :
    P ≤ Real.exp (n * (-t * y + B)) := by
  have hM' : M ≤ Real.exp (n * B) := by
    rw [← Real.exp_log hM]; exact Real.exp_le_exp.2 hlog
  calc P ≤ Real.exp (-t * n * y) * M := hP
    _ ≤ Real.exp (-t * n * y) * Real.exp (n * B) :=
        mul_le_mul_of_nonneg_left hM' (Real.exp_pos _).le
    _ = Real.exp (n * (-t * y + B)) := by rw [← Real.exp_add]; ring_nf

/-- The star wall: the bound is finite only for `t < 1/m`. For `m = 1` (sets containing the star of six faces of a link) this is `t < 1`.
Here we only record that `t m < 1` is equivalent to `t < 1/m`. -/
theorem tilt_range (t m : ℝ) (hm : 0 < m) : t * m < 1 ↔ t < 1 / m := by
  rw [lt_div_iff₀ hm]

end FaceSpectrum

#print axioms FaceSpectrum.smul_log_le_log
#print axioms FaceSpectrum.neg_log_le_chord
#print axioms FaceSpectrum.sum_neg_log_le
#print axioms FaceSpectrum.logMoment_le_per_face
#print axioms FaceSpectrum.chord_slope_mono
#print axioms FaceSpectrum.single_face_case
#print axioms FaceSpectrum.chernoff_glue
#print axioms FaceSpectrum.tilt_range
