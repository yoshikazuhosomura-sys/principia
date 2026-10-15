import Mathlib

/-!
# Shape-coefficient flow of the hierarchical (Migdal–Kadanoff) step: the algebra

Leading-order bookkeeping for the hierarchical step on one plaquette weight written as
`heat kernel × exp(Σ σ_k θ^{2k})`.  The bond move multiplies the shape by `4` and adds the
source `3 ℓ_k θ^{2k}` (from `log (θ / sin θ)`), the four-fold decimation rescales
`θ ↦ θ / 4` and multiplies by `4`, so the coefficient of `θ^{2k}` moves by
`σ ↦ (16 σ + 12 ℓ_k) / 4^(2k)`.  Nothing here concerns measures or the saddle-point
approximation that produces this map; only the elementary algebra and the affine
contraction recursion are formalised.
-/

namespace LatticeGaugeHierarchicalShapeFlow

/-- The quartic shape map (`k = 2`, `ℓ_2 = 1/180`). -/
noncomputable def quarticStep (σ : ℝ) : ℝ := σ / 16 + 1 / 3840

theorem quarticStep_fixed : quarticStep (1 / 3600) = 1 / 3600 := by
  unfold quarticStep; norm_num

/-- The distance to the fixed point `1/3600` shrinks by exactly `1/16` per step. -/
theorem quarticStep_iterate (σ : ℝ) (k : ℕ) :
    quarticStep^[k] σ - 1 / 3600 = (σ - 1 / 3600) / 16 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : quarticStep^[k] σ = 1 / 3600 + (σ - 1 / 3600) / 16 ^ k := by linarith
    rw [Function.iterate_succ_apply', hy]
    unfold quarticStep
    rw [pow_succ]
    field_simp
    ring

/-- General shape map for the coefficient of `θ^{2k}`. -/
noncomputable def shapeStep (k : ℕ) (ℓ σ : ℝ) : ℝ := (16 * σ + 12 * ℓ) / 4 ^ (2 * k)

theorem four_pow_ge (k : ℕ) (hk : 2 ≤ k) : (256 : ℝ) ≤ 4 ^ (2 * k) := by
  have h1 : (256 : ℝ) = 4 ^ (2 * 2) := by norm_num
  rw [h1]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Fixed point `σ*_k = 12 ℓ / (4^(2k) - 16)` for `k ≥ 2`. -/
theorem shapeStep_fixed (k : ℕ) (hk : 2 ≤ k) (ℓ : ℝ) :
    shapeStep k ℓ (12 * ℓ / (4 ^ (2 * k) - 16)) = 12 * ℓ / (4 ^ (2 * k) - 16) := by
  have h := four_pow_ge k hk
  have hne : (4 : ℝ) ^ (2 * k) - 16 ≠ 0 := by linarith
  have hne2 : (4 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  unfold shapeStep
  field_simp
  ring

/-- Contraction towards the fixed point by the factor `16 / 4^(2k)` (`= 16^(1-k)`). -/
theorem shapeStep_contract (k : ℕ) (hk : 2 ≤ k) (ℓ σ : ℝ) :
    shapeStep k ℓ σ - 12 * ℓ / (4 ^ (2 * k) - 16)
      = 16 / 4 ^ (2 * k) * (σ - 12 * ℓ / (4 ^ (2 * k) - 16)) := by
  have h := four_pow_ge k hk
  have hne : (4 : ℝ) ^ (2 * k) - 16 ≠ 0 := by linarith
  have hne2 : (4 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  unfold shapeStep
  field_simp
  ring

theorem shapeStep_ratio_le (k : ℕ) (hk : 2 ≤ k) : 16 / (4 : ℝ) ^ (2 * k) ≤ 1 / 16 := by
  have h := four_pow_ge k hk
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The quartic case is the general map with `k = 2`, `ℓ = 1/180`. -/
theorem shapeStep_quartic (σ : ℝ) : shapeStep 2 (1 / 180) σ = quarticStep σ := by
  unfold shapeStep quarticStep; norm_num; ring

/-- The sextic fixed point `1/963900` (`ℓ_3 = 1/2835`). -/
theorem sextic_fixed : 12 * (1 / 2835 : ℝ) / (4 ^ (2 * 3) - 16) = 1 / 963900 := by norm_num

/-- The `1/β` coefficient of the β-flow, `c(σ) = 1/48 - 15 σ`, at `σ = 1/3600`. -/
theorem flow_coefficient : (1 / 48 : ℝ) - 15 * (1 / 3600) = 1 / 60 := by norm_num

/-- Affine contraction recursion: `d (k+1) ≤ λ d k + ε` with `0 ≤ λ < 1` gives
`d k ≤ λ^k d 0 + ε / (1 - λ)` for every `k` (uniform in the number of steps). -/
theorem affine_contraction (d : ℕ → ℝ) (lam eps : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1)
    (he : 0 ≤ eps) (h : ∀ k, d (k + 1) ≤ lam * d k + eps) (k : ℕ) :
    d k ≤ lam ^ k * d 0 + eps / (1 - lam) := by
  have hpos : 0 < 1 - lam := by linarith
  induction k with
  | zero =>
    simp
    exact div_nonneg he hpos.le
  | succ k ih =>
    calc d (k + 1) ≤ lam * d k + eps := h k
      _ ≤ lam * (lam ^ k * d 0 + eps / (1 - lam)) + eps := by
          have := mul_le_mul_of_nonneg_left ih h0; linarith
      _ = lam ^ (k + 1) * d 0 + eps / (1 - lam) := by
          field_simp
          ring

/-- Tube invariance iterated: if `d 0 ≤ r` and `ε ≤ (1 - λ) r`, then `d k ≤ r` for all `k`. -/
theorem tube_iterate (d : ℕ → ℝ) (lam eps r : ℝ) (h0 : 0 ≤ lam)
    (hr : eps ≤ (1 - lam) * r) (h : ∀ k, d (k + 1) ≤ lam * d k + eps) (hd : d 0 ≤ r) (k : ℕ) :
    d k ≤ r := by
  induction k with
  | zero => exact hd
  | succ k ih =>
    have := mul_le_mul_of_nonneg_left ih h0
    linarith [h k]

end LatticeGaugeHierarchicalShapeFlow

#print axioms LatticeGaugeHierarchicalShapeFlow.quarticStep_fixed
#print axioms LatticeGaugeHierarchicalShapeFlow.quarticStep_iterate
#print axioms LatticeGaugeHierarchicalShapeFlow.shapeStep_fixed
#print axioms LatticeGaugeHierarchicalShapeFlow.shapeStep_contract
#print axioms LatticeGaugeHierarchicalShapeFlow.shapeStep_ratio_le
#print axioms LatticeGaugeHierarchicalShapeFlow.shapeStep_quartic
#print axioms LatticeGaugeHierarchicalShapeFlow.sextic_fixed
#print axioms LatticeGaugeHierarchicalShapeFlow.flow_coefficient
#print axioms LatticeGaugeHierarchicalShapeFlow.affine_contraction
#print axioms LatticeGaugeHierarchicalShapeFlow.tube_iterate
