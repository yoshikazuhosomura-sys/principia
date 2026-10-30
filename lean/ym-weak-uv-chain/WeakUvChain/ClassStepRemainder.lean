/-
The small-field step: from an orbit of the effective action staying in a class ball, derive the bound on the small-field remainder of
the coupling flow `|r^s_k| ≤ C_s / u_k` (the form of `CouplingSteps.small_rem` in the chain UltravioletChain).
Single file; checks with `import Mathlib` only.

  §1 For the norm recursion n_{k+1} ≤ C + λ n_k (λ < 1), a two-sided infinite orbit bounded by r satisfies
     n_k ≤ C/(1 − λ) for all k (an orbit in a large ball lies in the small ball of the source size)
  §2 From a quadratic-type remainder ‖R v‖ ≤ C + a‖v‖² and contraction ‖T v‖ ≤ τ‖v‖, inside the ball of radius r
     ‖v_{k+1}‖ ≤ C + (τ + a r)‖v_k‖
  §3 The coupling remainder read through the projection φ onto the β coordinate (continuous linear): |φ(R v)| ≤ ‖φ‖ (C + a ρ²)
  §4 With source C = c₀ g² = c₀/u, |r^s| ≤ C_s/u (u ≥ u⋆)
  §5 #print axioms

Existence and uniqueness of a two-sided infinite orbit staying in the class ball is the conclusion of LocProjectionAType
(`window_from_loc_A`) and is taken here as a premise (the orbit lies in the ball of radius r). That the remainder can be written in
terms of dimension 6 and 8 (the values of the quadratic constant a and the source c₀) is left to work on paper and floating-point computation.
-/
import Mathlib

namespace ClassStepRemainder

open Filter Topology

/-! ## 1. A bounded two-sided infinite orbit lies in a small ball -/

/-- If a nonnegative sequence `n : ℤ → ℝ` satisfies `n (k+1) ≤ C + λ n k` (`0 ≤ λ < 1`, `C ≥ 0`) and `n k ≤ r` for all `k`,
then `n k ≤ C/(1−λ)` for all `k`. -/
theorem bounded_orbit_small (n : ℤ → ℝ) (C lam r : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (hrec : ∀ k, n (k + 1) ≤ C + lam * n k) (hbd : ∀ k, n k ≤ r) :
    ∀ k, n k ≤ C / (1 - lam) := by
  intro k
  have h1 : 0 < 1 - lam := by linarith
  -- estimate going back j steps: n k ≤ C (1 − λ^j)/(1 − λ) + λ^j r
  have key : ∀ j : ℕ, n k ≤ C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r := by
    intro j
    induction j generalizing k with
    | zero =>
      simp only [pow_zero, sub_self, mul_zero, zero_div, one_mul, zero_add]
      exact hbd k
    | succ j ih =>
      have hk := hrec (k - 1)
      simp only [sub_add_cancel] at hk
      have ih' := ih (k - 1)
      have hlj : 0 ≤ lam ^ j := pow_nonneg hl0 j
      have e : C * (1 - lam ^ (j + 1)) / (1 - lam) + lam ^ (j + 1) * r =
          C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
        field_simp; ring
      rw [e]
      calc n k ≤ C + lam * n (k - 1) := hk
        _ ≤ C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
            have := mul_le_mul_of_nonneg_left ih' hl0; linarith
  have hlim : Tendsto (fun j : ℕ => C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) atTop
      (𝓝 (C * (1 - 0) / (1 - lam) + 0 * r)) := by
    have hp : Tendsto (fun j : ℕ => lam ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1
    exact ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)).div_const _).add
      (hp.mul tendsto_const_nhds)
  have := ge_of_tendsto hlim (Eventually.of_forall key)
  simpa using this

/-! ## 2. Norm recursion inside the ball from a quadratic-type remainder -/

section Step

variable {E : Type*} [NormedAddCommGroup E]

/-- If `‖T v‖ ≤ τ ‖v‖`, `‖R v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ r`, then `‖T v + R v‖ ≤ C + (τ + a r) ‖v‖`. -/
theorem norm_step_le (T R : E → E) (τ a C r : ℝ) (ha : 0 ≤ a)
    (hT : ∀ v, ‖T v‖ ≤ τ * ‖v‖) (hR : ∀ v, ‖R v‖ ≤ C + a * ‖v‖ ^ 2)
    (v : E) (hv : ‖v‖ ≤ r) : ‖T v + R v‖ ≤ C + (τ + a * r) * ‖v‖ := by
  have h1 := norm_add_le (T v) (R v)
  have h2 := hT v
  have h3 := hR v
  have h4 : a * ‖v‖ ^ 2 ≤ a * r * ‖v‖ := by
    have : ‖v‖ ^ 2 ≤ r * ‖v‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hv (norm_nonneg v)
    nlinarith
  nlinarith

/-- A two-sided infinite orbit `v (k+1) = T k (v k) + R k (v k)` staying in the class ball of radius `r` satisfies
`‖v k‖ ≤ C/(1−λ)` at every step, if `λ = τ + a r < 1`. -/
theorem orbit_in_small_ball (T R : ℤ → E → E) (v : ℤ → E) (τ a C r : ℝ)
    (hτ : 0 ≤ τ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hlt : τ + a * r < 1)
    (hT : ∀ k w, ‖T k w‖ ≤ τ * ‖w‖) (hR : ∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2)
    (horbit : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hball : ∀ k, ‖v k‖ ≤ r) :
    ∀ k, ‖v k‖ ≤ C / (1 - (τ + a * r)) := by
  apply bounded_orbit_small (fun k => ‖v k‖) C (τ + a * r) r (by positivity) hlt _ hball
  intro k
  show ‖v (k + 1)‖ ≤ C + (τ + a * r) * ‖v k‖
  rw [horbit k]
  exact norm_step_le (T k) (R k) τ a C r ha (hT k) (hR k) (v k) (hball k)

end Step

/-! ## 3. The coupling remainder read in the β coordinate -/

section Coupling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The component of the one-step remainder `Rf` (full-space valued) along the β coordinate `φ` (continuous linear) is the small-field
remainder of the coupling flow. If `‖Rf v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ ρ`, then `|φ (Rf v)| ≤ ‖φ‖ (C + a ρ²)`. -/
theorem coupling_remainder_le (φ : E →L[ℝ] ℝ) (Rf : E → E) (C a ρ : ℝ) (ha : 0 ≤ a)
    (hR : ∀ v, ‖Rf v‖ ≤ C + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ ρ) :
    |φ (Rf v)| ≤ ‖φ‖ * (C + a * ρ ^ 2) := by
  have h1 : |φ (Rf v)| ≤ ‖φ‖ * ‖Rf v‖ := by
    have := φ.le_opNorm (Rf v); rwa [Real.norm_eq_abs] at this
  have h2 : ‖v‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have h3 : ‖Rf v‖ ≤ C + a * ρ ^ 2 := le_trans (hR v) (by nlinarith)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (norm_nonneg φ))

/-- §1–§3 combined: with source `C = c₀ / u` (`c₀ g²`, `g² = 1/u`) and `u ≥ u⋆ > 0`, the coupling remainder read at the radius
`ρ = C/(1 − λ)` of the orbit's small ball satisfies
`|r^s| ≤ ‖φ‖ c₀ (1 + a c₀ / ((1−λ)² u⋆)) / u` (the chain's `small_rem` form `C_s / u`). -/
theorem small_rem_form (φ : E →L[ℝ] ℝ) (Rf : E → E) (c₀ a lam u ustar : ℝ)
    (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hl1 : lam < 1) (hus : 0 < ustar) (hu : ustar ≤ u)
    (hR : ∀ v, ‖Rf v‖ ≤ c₀ / u + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ (c₀ / u) / (1 - lam)) :
    |φ (Rf v)| ≤ (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) / u := by
  have hu0 : 0 < u := lt_of_lt_of_le hus hu
  have hl : 0 < 1 - lam := by linarith
  have h := coupling_remainder_le φ Rf (c₀ / u) a ((c₀ / u) / (1 - lam)) ha hR v hv
  refine le_trans h ?_
  have e : ‖φ‖ * (c₀ / u + a * ((c₀ / u) / (1 - lam)) ^ 2) =
      (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * u))) / u := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hu0.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : a * c₀ / ((1 - lam) ^ 2 * u) ≤ a * c₀ / ((1 - lam) ^ 2 * ustar) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hu (by positivity))
  linarith

end Coupling

/-! ## 5. Axiom check -/

#print axioms bounded_orbit_small
#print axioms norm_step_le
#print axioms orbit_in_small_ball
#print axioms coupling_remainder_le
#print axioms small_rem_form

end ClassStepRemainder
