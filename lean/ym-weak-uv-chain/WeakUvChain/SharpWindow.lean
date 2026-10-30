import Mathlib

/-!
# Sharp form of the window — saddle-node of a quadratic majorant

`KernelMarginStages.WindowCond` builds an invariant closed ball from Lipschitz constants: `c + (τ + ℓ/u + 2ar) r ≤ r`.
If the remainder has a size bound `‖R v‖ ≤ c + ℓ'‖v‖ + a‖v‖²`, the invariant ball only needs `c + (τ + ℓ') r + a r² ≤ r`,
and the existence condition for the window becomes the discriminant `4ac ≤ κ²` (`κ = 1 − τ − ℓ'`), half the constraint `8ac ≤ κ²` of the Lipschitz form.
-/

namespace SharpWindow

/-- Sharp window condition: contraction `τ + ℓ' + 2ar < 1` and invariance in size form `c + (τ + ℓ') r + a r² ≤ r`. -/
def SharpCond (τ ℓ' a c r : ℝ) : Prop :=
  τ + (ℓ' + 2 * a * r) < 1 ∧ c + (τ + ℓ') * r + a * r ^ 2 ≤ r

/-- Necessity: the sharp condition implies `4 a c ≤ κ²`. -/
theorem sharp_necessary (τ ℓ' a c r : ℝ) (ha : 0 < a) (h : SharpCond τ ℓ' a c r) :
    4 * a * c ≤ (1 - τ - ℓ') ^ 2 := by
  obtain ⟨_, h2⟩ := h
  have hsq : 0 ≤ ((1 - τ - ℓ') - 2 * a * r) ^ 2 := sq_nonneg _
  nlinarith

/-- Sufficiency: if `0 < κ`, `0 < θ < 1`, `c ≤ θ(2−θ) κ²/(4a)`, the sharp condition holds at `r = θκ/(2a)`.
As `θ → 1` this approaches the discriminant edge `κ²/(4a)`. `θ = 1/2` gives `3κ²/(16a)` (same form as the closed-ball condition of MarginRatioTwo). -/
theorem sharp_sufficient (τ ℓ' a c θ : ℝ) (ha : 0 < a) (hκ : 0 < 1 - τ - ℓ')
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (h : c ≤ θ * (2 - θ) * (1 - τ - ℓ') ^ 2 / (4 * a)) :
    SharpCond τ ℓ' a c (θ * (1 - τ - ℓ') / (2 * a)) := by
  set κ := 1 - τ - ℓ' with hk
  have e1 : 2 * a * (θ * κ / (2 * a)) = θ * κ := by field_simp
  have e2 : (τ + ℓ') * (θ * κ / (2 * a)) + a * (θ * κ / (2 * a)) ^ 2
      = θ * κ / (2 * a) - θ * (2 - θ) * κ ^ 2 / (4 * a) := by
    have : τ + ℓ' = 1 - κ := by rw [hk]; ring
    rw [this]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [e1]; nlinarith
  · have := e2; linarith

/-- The Lipschitz-form window (same expression as `KernelMarginStages.WindowCond`) implies the sharp form. -/
theorem lipschitz_form_implies_sharp (τ ℓ' a c r : ℝ) (ha : 0 ≤ a)
    (h : τ + (ℓ' + 2 * a * r) < 1 ∧ c + (τ + (ℓ' + 2 * a * r)) * r ≤ r) :
    SharpCond τ ℓ' a c r := by
  refine ⟨h.1, ?_⟩
  have : 0 ≤ a * r ^ 2 := by positivity
  nlinarith [h.2]

/-! ## Existence and uniqueness of the orbit (size-form remainder) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One step: `T` contracts by `τ`, and on the closed ball the remainder `R` is `L`-Lipschitz with size `‖R x‖ ≤ c + ℓ'‖x‖ + a‖x‖²`.
If `c + (τ + ℓ') r + a r² ≤ r`, then `T + R` maps the closed ball of radius `r` into itself. -/
theorem maps_ball_sharp (T : E →L[ℝ] E) (R : E → E) {τ ℓ' a c r : ℝ}
    (hT : ∀ y, ‖T y‖ ≤ τ * ‖y‖) (hℓ : 0 ≤ ℓ') (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hsize : ∀ x, ‖x‖ ≤ r → ‖R x‖ ≤ c + ℓ' * ‖x‖ + a * ‖x‖ ^ 2)
    (hball : c + (τ + ℓ') * r + a * r ^ 2 ≤ r) :
    ∀ x, ‖x‖ ≤ r → ‖T x + R x‖ ≤ r := by
  intro x hx
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : ‖T x + R x‖ ≤ τ * ‖x‖ + (c + ℓ' * ‖x‖ + a * ‖x‖ ^ 2) :=
    le_trans (norm_add_le _ _) (add_le_add (hT x) (hsize x hx))
  have h2 : a * ‖x‖ ^ 2 ≤ a * r ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ ha
    exact pow_le_pow_left₀ h0 hx 2
  have h3 : τ * ‖x‖ ≤ τ * r := mul_le_mul_of_nonneg_left hx hτ
  have h4 : ℓ' * ‖x‖ ≤ ℓ' * r := mul_le_mul_of_nonneg_left hx hℓ
  nlinarith

/-- One-step contraction: on the closed ball `‖(T+R)x − (T+R)y‖ ≤ (τ + L)‖x − y‖`. -/
theorem lipschitz_step (T : E →L[ℝ] E) (R : E → E) {τ L r : ℝ}
    (hT : ∀ y, ‖T y‖ ≤ τ * ‖y‖)
    (hR : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖R x - R y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖(T x + R x) - (T y + R y)‖ ≤ (τ + L) * ‖x - y‖ := by
  intro x y hx hy
  have e : (T x + R x) - (T y + R y) = T (x - y) + (R x - R y) := by
    rw [map_sub]; abel
  rw [e]
  calc ‖T (x - y) + (R x - R y)‖ ≤ ‖T (x - y)‖ + ‖R x - R y‖ := norm_add_le _ _
    _ ≤ τ * ‖x - y‖ + L * ‖x - y‖ := add_le_add (hT _) (hR x y hx hy)
    _ = (τ + L) * ‖x - y‖ := by ring

/-! ## Numerical instances (τ₁ = 0.6953, a = 4.3348, c₀ = 0.022, ℓ = 0) -/

/-- β = 28 (u = 7): the sharp condition holds at r = 0.0127 (outside the window for the Lipschitz-form `WindowCond`). -/
theorem sharp_beta28_tau1 : SharpCond 0.6953 0 4.3348 (0.022 / 7) 0.0127 := by
  unfold SharpCond; norm_num

/-- Margin at β = 28: `0.022 + u·a·r² + DZ ≤ b/2 = (22/(48π²)) ln 2`, with DZ ≤ 0.0052. -/
theorem margin_beta28_sharp (DZ : ℝ) (hDZ : DZ ≤ 0.0052) :
    0.022 + 7 * (4.3348 * 0.0127 ^ 2) + DZ ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 := by
  -- b/2 ≥ 0.03218 from π < 3.1416 and ln 2 > 0.6931
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hden : 48 * Real.pi ^ 2 < 48 * 3.1416 ^ 2 := by nlinarith
  have hpos : 0 < 48 * Real.pi ^ 2 := by positivity
  have h1 : 22 / (48 * 3.1416 ^ 2) < 22 / (48 * Real.pi ^ 2) :=
    div_lt_div_of_pos_left (by norm_num) hpos hden
  have h2 : (0.03218 : ℝ) ≤ 22 / (48 * 3.1416 ^ 2) * 0.6931471803 := by norm_num
  have h3 : 22 / (48 * 3.1416 ^ 2) * 0.6931471803 ≤ 22 / (48 * Real.pi ^ 2) * Real.log 2 := by
    apply mul_le_mul h1.le hlog.le (by norm_num) (by positivity)
  have h4 : 0.022 + 7 * (4.3348 * 0.0127 ^ 2) + 0.0052 ≤ (0.03218 : ℝ) := by norm_num
  linarith

/-- β = 20 (u = 5), τ₃ = 0.6804, ℓ = 0: the sharp condition holds at r = 0.0186. -/
theorem sharp_beta20_tau3 : SharpCond 0.6804 0 4.3348 (0.022 / 5) 0.0186 := by
  unfold SharpCond; norm_num

/-- β = 16 (u = 4), τ₁, ℓ = 0: even the sharp condition fails (discriminant `4ac > κ²`). -/
theorem sharp_beta16_tau1_fails (r : ℝ) : ¬ SharpCond 0.6953 0 4.3348 (0.022 / 4) r := by
  intro h
  have := sharp_necessary 0.6953 0 4.3348 (0.022 / 4) r (by norm_num) h
  norm_num at this

end SharpWindow

#print axioms SharpWindow.sharp_necessary
#print axioms SharpWindow.sharp_sufficient
#print axioms SharpWindow.lipschitz_form_implies_sharp
#print axioms SharpWindow.maps_ball_sharp
#print axioms SharpWindow.lipschitz_step
#print axioms SharpWindow.sharp_beta28_tau1
#print axioms SharpWindow.margin_beta28_sharp
#print axioms SharpWindow.sharp_beta20_tau3
#print axioms SharpWindow.sharp_beta16_tau1_fails

/-! ## Copy: section Entire of UltravioletAssembly (two-sided infinite orbits; unchanged up to comments) -/

namespace EntireCopy

open Function Filter Topology

section Entire

variable {X : Type*} [MetricSpace X]

/-- The `m`-step composition ending at time `n`: `F (n−1) ∘ ⋯ ∘ F (n−m)`. -/
noncomputable def pull (F : ℤ → X → X) : ℤ → ℕ → X → X
  | _, 0, x => x
  | n, m + 1, x => F (n - 1) (pull F (n - 1) m x)

theorem pull_succ' (F : ℤ → X → X) (m : ℕ) : ∀ (n : ℤ) (x : X),
    pull F n (m + 1) x = pull F n m (F (n - m - 1) x) := by
  induction m with
  | zero => intro n x; simp [pull]
  | succ m ih =>
    intro n x
    show F (n - 1) (pull F (n - 1) (m + 1) x) = F (n - 1) (pull F (n - 1) m _)
    rw [ih]
    congr 3
    push_cast; ring

theorem pull_mem (F : ℤ → X → X) {S : Set X} (hS : ∀ k, Set.MapsTo (F k) S S) (m : ℕ) :
    ∀ (n : ℤ) (x : X), x ∈ S → pull F n m x ∈ S := by
  induction m with
  | zero => intro n x hx; exact hx
  | succ m ih => intro n x hx; exact hS _ (ih _ _ hx)

theorem dist_pull_le (F : ℤ → X → X) {S : Set X} (hS : ∀ k, Set.MapsTo (F k) S S) {K : ℝ}
    (hK0 : 0 ≤ K) (hF : ∀ k, ∀ a ∈ S, ∀ b ∈ S, dist (F k a) (F k b) ≤ K * dist a b) (m : ℕ) :
    ∀ (n : ℤ) (x y : X), x ∈ S → y ∈ S → dist (pull F n m x) (pull F n m y) ≤ K ^ m * dist x y := by
  induction m with
  | zero => intro n x y _ _; simp [pull]
  | succ m ih =>
    intro n x y hx hy
    refine (hF _ _ (pull_mem F hS m _ x hx) _ (pull_mem F hS m _ y hy)).trans ?_
    rw [pow_succ]
    nlinarith [ih (n - 1) x y hx hy]

theorem pull_orbit (F : ℤ → X → X) (u : ℤ → X) (hu : ∀ k, u (k + 1) = F k (u k)) (m : ℕ) :
    ∀ n : ℤ, u n = pull F n m (u (n - m)) := by
  induction m with
  | zero => intro n; simp [pull]
  | succ m ih =>
    intro n
    rw [pull_succ', ih n]
    congr 1
    have : n - (m : ℤ) = (n - m - 1) + 1 := by ring
    rw [this, hu]
    congr 2
    push_cast; ring

theorem exists_unique_entire_orbit [CompleteSpace X] (F : ℤ → X → X) {S : Set X}
    (hSc : IsClosed S) {x₀ : X} (hx₀ : x₀ ∈ S) {D : ℝ} (hD : ∀ a ∈ S, ∀ b ∈ S, dist a b ≤ D)
    (hS : ∀ k, Set.MapsTo (F k) S S) {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hF : ∀ k, ∀ a ∈ S, ∀ b ∈ S, dist (F k a) (F k b) ≤ K * dist a b) :
    ∃! u : ℤ → X, (∀ k, u k ∈ S) ∧ ∀ k, u (k + 1) = F k (u k) := by
  have hcauchy : ∀ n : ℤ, CauchySeq (fun m : ℕ => pull F n m x₀) := by
    intro n
    refine cauchySeq_of_le_geometric K D hK1 (fun m => ?_)
    rw [pull_succ']
    have := dist_pull_le F hS hK0 hF m n x₀ (F (n - m - 1) x₀) hx₀ (hS _ hx₀)
    have hd := hD x₀ hx₀ _ (hS (n - m - 1) hx₀)
    have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
    calc _ ≤ K ^ m * dist x₀ (F (n - m - 1) x₀) := this
      _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
      _ = D * K ^ m := by ring
  choose h hh using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hmemS : ∀ n, h n ∈ S := fun n =>
    hSc.mem_of_tendsto (hh n) (Eventually.of_forall fun m => pull_mem F hS m n x₀ hx₀)
  have huniq : ∀ u : ℤ → X, (∀ k, u k ∈ S) → (∀ k, u (k + 1) = F k (u k)) → ∀ n, u n = h n := by
    intro u huS hu n
    have hlim : Tendsto (fun m : ℕ => pull F n m x₀) atTop (𝓝 (u n)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K ^ m * D) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const D
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      rw [pull_orbit F u hu m n, dist_comm]
      have := dist_pull_le F hS hK0 hF m n _ _ (huS (n - m)) hx₀
      have hd := hD _ (huS (n - m)) x₀ hx₀
      have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
      calc _ ≤ K ^ m * dist (u (n - m)) x₀ := this
        _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
    exact tendsto_nhds_unique hlim (hh n)
  have hinv : ∀ n, h (n + 1) = F n (h n) := by
    intro n
    have h1 : Tendsto (fun m : ℕ => pull F (n + 1) (m + 1) x₀) atTop (𝓝 (h (n + 1))) :=
      (hh (n + 1)).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun m : ℕ => pull F (n + 1) (m + 1) x₀) atTop (𝓝 (F n (h n))) := by
      have e : ∀ m, pull F (n + 1) (m + 1) x₀ = F n (pull F n m x₀) := by
        intro m; simp [pull]
      simp only [e]
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K * dist (pull F n m x₀) (h n)) atTop (𝓝 0) := by
        simpa using ((tendsto_iff_dist_tendsto_zero.1 (hh n)).const_mul K)
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      exact hF n _ (pull_mem F hS m n x₀ hx₀) _ (hmemS n)
    exact tendsto_nhds_unique h1 h2
  refine ⟨h, ⟨hmemS, hinv⟩, fun u ⟨huS, hu⟩ => funext (huniq u huS hu)⟩

end Entire

end EntireCopy

namespace SharpWindow

/-! ## From the sharp window: a unique two-sided infinite orbit staying in the closed ball -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Per-step `T k` (contraction `τ`) and remainder `R k` (`L`-Lipschitz on the closed ball of radius `r`, size `c + ℓ'‖x‖ + a‖x‖²`).
If `τ + L < 1` and `c + (τ + ℓ') r + a r² ≤ r`, there is a unique two-sided infinite orbit `v (k+1) = T k (v k) + R k (v k)` staying in the ball.
(The Lipschitz-form `window_from_loc_A` takes invariance as `c + (τ + L) r ≤ r`; here it is taken in size form.) -/
theorem sharp_entire_orbit [CompleteSpace E] (T : ℤ → E →L[ℝ] E) (R : ℤ → E → E)
    {τ ℓ' a c r L : ℝ} (hτ : 0 ≤ τ) (hℓ : 0 ≤ ℓ') (ha : 0 ≤ a) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hT : ∀ k y, ‖T k y‖ ≤ τ * ‖y‖)
    (hsize : ∀ k x, ‖x‖ ≤ r → ‖R k x‖ ≤ c + ℓ' * ‖x‖ + a * ‖x‖ ^ 2)
    (hlip : ∀ k x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖R k x - R k y‖ ≤ L * ‖x - y‖)
    (hlt : τ + L < 1) (hball : c + (τ + ℓ') * r + a * r ^ 2 ≤ r) :
    ∃! v : ℤ → E, (∀ k, v k ∈ Metric.closedBall (0 : E) r) ∧
      ∀ k, v (k + 1) = T k (v k) + R k (v k) := by
  refine EntireCopy.exists_unique_entire_orbit
    (fun k x => T k x + R k x) Metric.isClosed_closedBall (Metric.mem_closedBall_self hr)
    (D := 2 * r) ?_ ?_ (by linarith) hlt ?_
  · intro x hx y hy
    have hx' : ‖x‖ ≤ r := by simpa using hx
    have hy' : ‖y‖ ≤ r := by simpa using hy
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
      _ ≤ 2 * r := by linarith
  · intro k x hx
    have hx' : ‖x‖ ≤ r := by simpa using hx
    have := maps_ball_sharp (T k) (R k) (hT k) hℓ ha hτ (hsize k) hball x hx'
    simpa using this
  · intro k x hx y hy
    have hx' : ‖x‖ ≤ r := by simpa using hx
    have hy' : ‖y‖ ≤ r := by simpa using hy
    have := lipschitz_step (T k) (R k) (hT k) (hlip k) x y hx' hy'
    rw [dist_eq_norm, dist_eq_norm]; exact this

end SharpWindow

#print axioms SharpWindow.sharp_entire_orbit
