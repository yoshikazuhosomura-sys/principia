/-
Chain fields for the case where the large-field contribution to the coupling grows proportionally to u (|r^ℓ_k| ≤ D₁·u_k·z_k).
  §1 Moving invariant interval: if W is decreasing on the domain, ρW(s) + AΦ(s) + BW(s)² ≤ W(s) for each s, and u
     decreases along the steps, then z_k ≤ W(u_k) is preserved by induction (in place of a constant Z).
  §2 If u·W(u) ≤ Y, then |r^ℓ_k| ≤ D₁·Y (a form that fails with constant D is absorbed by the product uW).
  §3 With threshold y_h(u) = (log u)/σ + c, u·A·e^{−σ y_h(u)} = A·e^{−σ c} (independent of u).
  §4 The constant-D form breaks for large u when the contribution is D₁ u z and z is bounded below.
Single file; checks with `import Mathlib` only.
-/
import Mathlib

namespace MovingActivity

/-- §1: moving invariant interval. -/
theorem activity_le_moving (u z w : ℕ → ℝ) (W Φ : ℝ → ℝ) (ρ A B ustar : ℝ)
    (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdec : ∀ k, u (k + 1) ≤ u k) (hdom : ∀ k, ustar ≤ u k)
    (hW : ∀ s t, ustar ≤ s → s ≤ t → W t ≤ W s)
    (hfix : ∀ s, ustar ≤ s → ρ * W s + A * Φ s + B * W s ^ 2 ≤ W s)
    (hrec : ∀ k, z (k + 1) ≤ ρ * z k + A * w k + B * z k ^ 2)
    (hsup : ∀ k, w k ≤ Φ (u k)) (hnn : ∀ k, 0 ≤ z k) (h0 : z 0 ≤ W (u 0)) :
    ∀ k, z k ≤ W (u k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have h1 : ρ * z k ≤ ρ * W (u k) := mul_le_mul_of_nonneg_left ih hρ
    have h2 : A * w k ≤ A * Φ (u k) := mul_le_mul_of_nonneg_left (hsup k) hA
    have h3 : z k ^ 2 ≤ W (u k) ^ 2 := pow_le_pow_left₀ (hnn k) ih 2
    have h4 : B * z k ^ 2 ≤ B * W (u k) ^ 2 := mul_le_mul_of_nonneg_left h3 hB
    have h5 := hfix (u k) (hdom k)
    have h6 := hW (u (k + 1)) (u k) (hdom (k + 1)) (hdec k)
    linarith [hrec k]

/-- §2: |r^ℓ_k| ≤ D₁ u_k z_k, z_k ≤ W(u_k), u W(u) ≤ Y ⇒ |r^ℓ_k| ≤ D₁ Y. -/
theorem large_rem_moving (rl u z : ℕ → ℝ) (W : ℝ → ℝ) (D₁ Y ustar : ℝ) (hD : 0 ≤ D₁)
    (hus : 0 < ustar) (hdom : ∀ k, ustar ≤ u k)
    (hrl : ∀ k, |rl k| ≤ D₁ * u k * z k) (hz : ∀ k, z k ≤ W (u k))
    (hY : ∀ s, ustar ≤ s → s * W s ≤ Y) : ∀ k, |rl k| ≤ D₁ * Y := by
  intro k
  have hu : 0 ≤ u k := le_trans hus.le (hdom k)
  have h1 : D₁ * u k * z k ≤ D₁ * u k * W (u k) :=
    mul_le_mul_of_nonneg_left (hz k) (mul_nonneg hD hu)
  have h2 : D₁ * (u k * W (u k)) ≤ D₁ * Y := mul_le_mul_of_nonneg_left (hY _ (hdom k)) hD
  calc |rl k| ≤ D₁ * u k * z k := hrl k
    _ ≤ D₁ * u k * W (u k) := h1
    _ = D₁ * (u k * W (u k)) := by ring
    _ ≤ D₁ * Y := h2

/-- §3: a logarithmic threshold absorbs u. -/
theorem log_threshold (A σ c u : ℝ) (hσ : σ ≠ 0) (hu : 0 < u) :
    u * (A * Real.exp (-(σ * (Real.log u / σ + c)))) = A * Real.exp (-(σ * c)) := by
  have e : -(σ * (Real.log u / σ + c)) = -Real.log u + -(σ * c) := by field_simp; ring
  rw [e, Real.exp_add, Real.exp_neg, Real.exp_log hu]
  field_simp

/-- §4: constant D fails: if the contribution is `D₁ u z₀` (`D₁, z₀ > 0`), then for every constant `D` there is `u` with
`D z₀ < D₁ u z₀`. -/
theorem constant_D_fails (D D₁ z₀ : ℝ) (hD₁ : 0 < D₁) (hz : 0 < z₀) :
    ∃ u : ℝ, D * z₀ < D₁ * u * z₀ := by
  refine ⟨D / D₁ + 1, ?_⟩
  have e : D₁ * (D / D₁ + 1) * z₀ = D * z₀ + D₁ * z₀ := by field_simp
  rw [e]; nlinarith

/-- §5: run the coupling steps and the activity induction together (untangling the circularity): with flow
`u_{k+1} = u_k − b + rs_k + rl_k`, `|rs_k| ≤ S`, `|rl_k| ≤ D₁ u_k z_k` and `S + D₁ Y ≤ b/2`, for all k
`z_k ≤ W(u_k)` and `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2` (the domain `u⋆ ≤ u_k` is given). -/
theorem chain_moving (u z w rs rl : ℕ → ℝ) (W Φ : ℝ → ℝ) (ρ A B ustar b S D₁ Y : ℝ)
    (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D₁) (hus : 0 < ustar) (hb : 0 ≤ b)
    (hdom : ∀ k, ustar ≤ u k)
    (hW : ∀ s t, ustar ≤ s → s ≤ t → W t ≤ W s)
    (hfix : ∀ s, ustar ≤ s → ρ * W s + A * Φ s + B * W s ^ 2 ≤ W s)
    (hrec : ∀ k, z (k + 1) ≤ ρ * z k + A * w k + B * z k ^ 2)
    (hsup : ∀ k, w k ≤ Φ (u k)) (hnn : ∀ k, 0 ≤ z k) (h0 : z 0 ≤ W (u 0))
    (hflow : ∀ k, u (k + 1) = u k - b + rs k + rl k)
    (hrs : ∀ k, |rs k| ≤ S) (hrl : ∀ k, |rl k| ≤ D₁ * u k * z k)
    (hY : ∀ s, ustar ≤ s → s * W s ≤ Y) (hm : S + D₁ * Y ≤ b / 2) :
    ∀ k, z k ≤ W (u k) ∧ u k - 3 * b / 2 ≤ u (k + 1) ∧ u (k + 1) ≤ u k - b / 2 := by
  have step : ∀ k, z k ≤ W (u k) → u k - 3 * b / 2 ≤ u (k + 1) ∧ u (k + 1) ≤ u k - b / 2 := by
    intro k hz
    have hu : 0 ≤ u k := le_trans hus.le (hdom k)
    have h1 : D₁ * u k * z k ≤ D₁ * u k * W (u k) :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg hD hu)
    have h2 : D₁ * (u k * W (u k)) ≤ D₁ * Y := mul_le_mul_of_nonneg_left (hY _ (hdom k)) hD
    have hl : |rl k| ≤ D₁ * Y := by
      calc |rl k| ≤ D₁ * u k * z k := hrl k
        _ ≤ D₁ * u k * W (u k) := h1
        _ = D₁ * (u k * W (u k)) := by ring
        _ ≤ D₁ * Y := h2
    have hs := abs_le.mp (hrs k)
    have hl' := abs_le.mp hl
    have hf := hflow k
    constructor <;> linarith [hs.1, hs.2, hl'.1, hl'.2]
  intro k
  induction k with
  | zero => exact ⟨h0, step 0 h0⟩
  | succ k ih =>
    obtain ⟨hz, _, hdown⟩ := ih
    have h1 : ρ * z k ≤ ρ * W (u k) := mul_le_mul_of_nonneg_left hz hρ
    have h2 : A * w k ≤ A * Φ (u k) := mul_le_mul_of_nonneg_left (hsup k) hA
    have h3 : z k ^ 2 ≤ W (u k) ^ 2 := pow_le_pow_left₀ (hnn k) hz 2
    have h4 : B * z k ^ 2 ≤ B * W (u k) ^ 2 := mul_le_mul_of_nonneg_left h3 hB
    have h5 := hfix (u k) (hdom k)
    have h6 := hW (u (k + 1)) (u k) (hdom (k + 1)) (by linarith)
    have hz' : z (k + 1) ≤ W (u (k + 1)) := by linarith [hrec k]
    exact ⟨hz', step (k + 1) hz'⟩

end MovingActivity

#print axioms MovingActivity.activity_le_moving
#print axioms MovingActivity.large_rem_moving
#print axioms MovingActivity.log_threshold
#print axioms MovingActivity.constant_D_fails
#print axioms MovingActivity.chain_moving
