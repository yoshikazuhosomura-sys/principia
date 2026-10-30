import Mathlib

/-!
# Window with vertex coordinates added to the classes (arithmetic of (P1-vert))

  §1 Pull-back of vertices along the tree map: for the one-step minimisation map `E` (`‖E‖ ≤ s`, with s² = τ in the chosen weights),
     carrying a degree-n vertex `V` to `V ∘ E` gives `‖V ∘ E‖ ≤ ‖V‖ s^n`. Vertices without a quadratic symbol (n ≥ 3)
     contract with `τ_v ≤ s³ = τ^{3/2}`.
  §2 Two-component estimate: if `x' ≤ C + αx + βy`, `y' ≤ D + δx + γy`, then in the norm `x + w y` with weight `w > 0`,
     `≤ (C + wD) + Λ (x + w y)`, `Λ = max(α + wδ, γ + β/w)`.
  §3 Numbers: `s ≤ 0.8339` (`s² ≤ 0.6954`) implies `s³ ≤ 0.58`.
-/

namespace LatticeGauge.VertexClassWindow

/-! ## 1. Pull-back of vertices -/

section Pullback
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- General degree: `‖(p ∘ u)_n‖ ≤ ‖p_n‖ ‖u‖^n` (Mathlib form). -/
theorem pullback_le (p : FormalMultilinearSeries ℝ F G) (u : E →L[ℝ] F) (n : ℕ) :
    ‖p.compContinuousLinearMap u n‖ ≤ ‖p n‖ * ‖u‖ ^ n :=
  p.norm_compContinuousLinearMap_le u n

/-- Vertices without a quadratic symbol (`n ≥ 3`) contract by `s³` when `‖u‖ ≤ s ≤ 1`. -/
theorem pullback_vertex_le (p : FormalMultilinearSeries ℝ F G) (u : E →L[ℝ] F) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu : ‖u‖ ≤ s) (n : ℕ) (hn : 3 ≤ n) :
    ‖p.compContinuousLinearMap u n‖ ≤ ‖p n‖ * s ^ 3 := by
  refine (pullback_le p u n).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ‖u‖ ^ n ≤ s ^ n := pow_le_pow_left₀ (norm_nonneg _) hu n
    _ ≤ s ^ 3 := pow_le_pow_of_le_one hs0 hs1 hn

end Pullback

/-! ## 2. Two-component estimate -/

/-- If `x' ≤ C + αx + βy`, `y' ≤ D + δx + γy` (all nonnegative), then `x' + w y' ≤ (C + wD) + Λ(x + w y)`,
`Λ = max(α + wδ, γ + β/w)`. -/
theorem two_component_step {x y x' y' C D α β γ δ w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 < w)
    (h1 : x' ≤ C + α * x + β * y) (h2 : y' ≤ D + δ * x + γ * y) :
    x' + w * y' ≤ (C + w * D) + max (α + w * δ) (γ + β / w) * (x + w * y) := by
  set Λ := max (α + w * δ) (γ + β / w)
  have hA : α + w * δ ≤ Λ := le_max_left _ _
  have hB : γ + β / w ≤ Λ := le_max_right _ _
  have e : w * (γ + β / w) = w * γ + β := by field_simp
  have h3 : (α + w * δ) * x ≤ Λ * x := mul_le_mul_of_nonneg_right hA hx
  have h4 : w * (γ + β / w) * y ≤ w * Λ * y := by
    have := mul_le_mul_of_nonneg_left hB hw.le
    exact mul_le_mul_of_nonneg_right this hy
  rw [e] at h4
  have h5 : w * y' ≤ w * D + w * δ * x + w * γ * y := by
    have := mul_le_mul_of_nonneg_left h2 hw.le; linarith
  nlinarith

/-- Choice of weight: with `τ_v < 1`, the smallest weight satisfying `γ + β/w ≤ Λ` is `w = β/(Λ − γ)`. Then
`α + wδ ≤ Λ` is equivalent to `α + βδ/(Λ − γ) ≤ Λ`. -/
theorem weight_choice {α β γ δ Λ : ℝ} (hγ : γ < Λ) (hβ : 0 < β)
    (h : α + β * δ / (Λ - γ) ≤ Λ) :
    α + β / (Λ - γ) * δ ≤ Λ ∧ γ + β / (β / (Λ - γ)) ≤ Λ := by
  have hpos : 0 < Λ - γ := by linarith
  refine ⟨by rw [div_mul_eq_mul_div]; exact h, ?_⟩
  rw [div_div_eq_mul_div, mul_comm β (Λ - γ), mul_div_assoc, div_self hβ.ne', mul_one]
  linarith

/-! ## 3. Numbers -/

/-- If `s² ≤ 0.6954` and `0 ≤ s`, then `s ≤ 0.8340` and `s³ ≤ 0.5801`. -/
theorem tau_v_number {s : ℝ} (hs : 0 ≤ s) (h : s ^ 2 ≤ 0.6954) : s ^ 3 ≤ 0.5801 := by
  have h1 : s ≤ 0.834 := by nlinarith
  have h2 : s ^ 3 = s * s ^ 2 := by ring
  rw [h2]
  calc s * s ^ 2 ≤ 0.834 * 0.6954 := mul_le_mul h1 h (sq_nonneg s) (by norm_num)
    _ ≤ 0.5801 := by norm_num

theorem tau_v_number_tau3 {s : ℝ} (hs : 0 ≤ s) (h : s ^ 2 ≤ 0.6805) : s ^ 3 ≤ 0.5614 := by
  have h1 : s ≤ 0.82493 := by nlinarith
  have h2 : s ^ 3 = s * s ^ 2 := by ring
  rw [h2]
  calc s * s ^ 2 ≤ 0.82493 * 0.6805 := mul_le_mul h1 h (sq_nonneg s) (by norm_num)
    _ ≤ 0.5614 := by norm_num

end LatticeGauge.VertexClassWindow

open LatticeGauge.VertexClassWindow
#print axioms pullback_le
#print axioms pullback_vertex_le
#print axioms two_component_step
#print axioms weight_choice
#print axioms tau_v_number
#print axioms tau_v_number_tau3
