import Mathlib

/-!
# A sum rule for face correlations of a lattice coboundary

Let `d : Matrix F E ℝ` be the face–link incidence (coboundary) matrix and `P` a matrix with
`P * d = d` (for instance the orthogonal projector onto the column space of `d`).
For a face `p` and a link `l` with `d p l = ±1`,

  `∑ q, d p l * d q l * P p q = 1`.

Separating the diagonal term gives `P p p + ∑_{q ≠ p} ε ε' P p q = 1`.
For the Gaussian (free) measure with covariance `P / β`, dividing by `P p p` gives the
statement "the oriented correlations of the faces sharing one link sum to `1 / P p p - 1`";
with `P p p = 2 / n` (dimension `n`) this is `n / 2 - 1` (in dimension four: `1`).
-/

open Matrix BigOperators

namespace FaceSumRule

variable {F E : Type*} [Fintype F] [Fintype E] [DecidableEq F]

omit [Fintype E] [DecidableEq F] in
/-- Row identity from `P * d = d`. -/
theorem row_identity (d : Matrix F E ℝ) (P : Matrix F F ℝ) (hP : P * d = d) (p : F) (l : E) :
    ∑ q, P p q * d q l = d p l := by
  have h := congrFun (congrFun hP p) l
  simpa [Matrix.mul_apply] using h

omit [Fintype E] [DecidableEq F] in
/-- The sum rule. -/
theorem sum_rule (d : Matrix F E ℝ) (P : Matrix F F ℝ) (hP : P * d = d) (p : F) (l : E)
    (hsq : d p l * d p l = 1) :
    ∑ q, d p l * d q l * P p q = 1 := by
  have h := row_identity d P hP p l
  calc ∑ q, d p l * d q l * P p q = d p l * ∑ q, P p q * d q l := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro q _; ring
    _ = d p l * d p l := by rw [h]
    _ = 1 := hsq

omit [Fintype E] in
/-- Diagonal term separated. -/
theorem sum_rule_split (d : Matrix F E ℝ) (P : Matrix F F ℝ) (hP : P * d = d) (p : F) (l : E)
    (hsq : d p l * d p l = 1) :
    P p p + ∑ q ∈ Finset.univ.erase p, d p l * d q l * P p q = 1 := by
  have h := sum_rule d P hP p l hsq
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h
  have hpp : d p l * d p l * P p p = P p p := by rw [hsq, one_mul]
  linarith [hpp]

omit [Fintype E] in
/-- Normalized form: `1 + ∑_{q ≠ p} ε ε' ρ_{pq} = 1 / P p p`, where `ρ_{pq} = P p q / P p p`. -/
theorem normalized (d : Matrix F E ℝ) (P : Matrix F F ℝ) (hP : P * d = d) (p : F) (l : E)
    (hsq : d p l * d p l = 1) (hpos : 0 < P p p) :
    1 + ∑ q ∈ Finset.univ.erase p, d p l * d q l * (P p q / P p p) = 1 / P p p := by
  have h := sum_rule_split d P hP p l hsq
  have hne : P p p ≠ 0 := ne_of_gt hpos
  have : ∑ q ∈ Finset.univ.erase p, d p l * d q l * (P p q / P p p)
      = (∑ q ∈ Finset.univ.erase p, d p l * d q l * P p q) / P p p := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl ?_; intro q _; ring
  rw [this]
  field_simp
  linarith

omit [DecidableEq F] in
/-- Columns of `d` lie in the image when `P = d G dᵀ` and `G (dᵀ d) = 1`
(no zero modes; the gauge-fixed case). -/
theorem proj_fixes (d : Matrix F E ℝ) (G : Matrix E E ℝ) [DecidableEq E]
    (hG : G * (dᵀ * d) = 1) : (d * G * dᵀ) * d = d := by
  calc (d * G * dᵀ) * d = d * (G * (dᵀ * d)) := by simp only [Matrix.mul_assoc]
    _ = d := by rw [hG, Matrix.mul_one]

/-- With `P p p = 2 / n` the oriented sum of the neighbour correlations is `n / 2 - 1`. -/
theorem dimension_value (n : ℝ) (hn : 0 < n) (S : ℝ) (h : 1 + S = 1 / (2 / n)) :
    S = n / 2 - 1 := by
  have : 1 / (2 / n) = n / 2 := by field_simp
  linarith

/-- In dimension four the neighbour sum equals the self term. -/
theorem four_dim (S : ℝ) (h : 1 + S = 1 / (2 / (4 : ℝ))) : S = 1 := by
  have := dimension_value 4 (by norm_num) S h
  linarith

/-- Gaussian Schwinger–Dyson: `var · (1 + Γ) = 1/β` gives `var = 1/(β (1+Γ))`; at `Γ = 1` the
variance is half of the independent value `1/β`. -/
theorem variance_halved (β var : ℝ) (h : var * (1 + 1) = 1 / β) :
    var = (1 / β) / 2 := by
  linarith

end FaceSumRule

#print axioms FaceSumRule.row_identity
#print axioms FaceSumRule.sum_rule
#print axioms FaceSumRule.sum_rule_split
#print axioms FaceSumRule.normalized
#print axioms FaceSumRule.proj_fixes
#print axioms FaceSumRule.dimension_value
#print axioms FaceSumRule.four_dim
#print axioms FaceSumRule.variance_halved
