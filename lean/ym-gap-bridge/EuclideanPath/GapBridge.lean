/-
  EuclideanPath.GapBridge

  Algebraic skeleton of the lower bound `C_P ≥ κ ħ²/Δ²` for the Langevin Poincaré
  constant of a stationary Euclidean path measure.  Only real algebra, finite sums
  and elementary inequalities are checked here.  The path measure, the covariance
  formula, the ground-state identity and the fact that `C_P` is a supremum are
  outside Lean; they enter as named real hypotheses.
-/
import Mathlib

namespace EuclideanPath.GapBridge

open Finset

/-! ### Discrete windows: `S_N(q) = Σ_{s,t<N} q^{|s-t|}` (used only in a remark) -/

/-- `Σ_{s<N} Σ_{t<N} q^{|s-t|}`, the absolute value written as `(s-t)+(t-s)` in `ℕ`. -/
noncomputable def pairSum (q : ℝ) (N : ℕ) : ℝ :=
  ∑ s ∈ range N, ∑ t ∈ range N, q ^ ((s - t) + (t - s))

lemma edge_sum (q : ℝ) (N : ℕ) :
    ∑ s ∈ range N, q ^ ((s - N) + (N - s)) = ∑ d ∈ range N, q ^ (d + 1) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  omega

lemma edge_sum' (q : ℝ) (N : ℕ) :
    ∑ t ∈ range N, q ^ ((N - t) + (t - N)) = ∑ d ∈ range N, q ^ (d + 1) := by
  rw [← edge_sum q N]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  omega

/-- One step (no hypotheses): `S_{N+1} = S_N + 2 Σ_{d<N} q^{d+1} + 1`. -/
theorem pair_sum_succ (q : ℝ) (N : ℕ) :
    pairSum q (N + 1) = pairSum q N + 2 * ∑ d ∈ range N, q ^ (d + 1) + 1 := by
  unfold pairSum
  rw [Finset.sum_range_succ]
  simp only [Finset.sum_range_succ]
  rw [Finset.sum_add_distrib, edge_sum q N, edge_sum' q N]
  simp only [Nat.sub_self, add_zero, pow_zero]
  ring

/-- Geometric sum (no hypotheses): `(1-q) Σ_{d<N} q^{d+1} = q (1 - q^N)`. -/
theorem geom_shift (q : ℝ) (N : ℕ) :
    (1 - q) * ∑ d ∈ range N, q ^ (d + 1) = q * (1 - q ^ N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- Closed form (no hypotheses): `(1-q)² S_N(q) = N(1+q)(1-q) - 2q(1-q^N)`. -/
theorem pair_sum_closed (q : ℝ) (N : ℕ) :
    (1 - q) ^ 2 * pairSum q N = N * (1 + q) * (1 - q) - 2 * q * (1 - q ^ N) := by
  induction N with
  | zero => simp [pairSum]
  | succ n ih =>
    rw [pair_sum_succ]
    have hg := geom_shift q n
    have hsplit : (1 - q) ^ 2 * (pairSum q n + 2 * ∑ d ∈ range n, q ^ (d + 1) + 1)
        = (1 - q) ^ 2 * pairSum q n + 2 * (1 - q) * ((1 - q) * ∑ d ∈ range n, q ^ (d + 1))
          + (1 - q) ^ 2 := by ring
    rw [hsplit, ih, hg]
    push_cast
    ring

/-- Limit of the discrete-time ratio (hypotheses `0<Δ`, `0<c`):
    `(1+e^{-Δ})/(c(1-e^{-Δ})²) ≥ 1/(cΔ²)`. -/
theorem discrete_limit_ge {Δ cD : ℝ} (hΔ : 0 < Δ) (hc : 0 < cD) :
    1 / (cD * Δ ^ 2) ≤ (1 + Real.exp (-Δ)) / (cD * (1 - Real.exp (-Δ)) ^ 2) := by
  have hq : 0 < Real.exp (-Δ) := Real.exp_pos _
  have hq1 : Real.exp (-Δ) < 1 := by
    have := Real.exp_lt_exp.mpr (show -Δ < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hle : 1 - Real.exp (-Δ) ≤ Δ := by
    have := Real.add_one_le_exp (-Δ)
    linarith
  have hpos : 0 < 1 - Real.exp (-Δ) := by linarith
  have hsq : (1 - Real.exp (-Δ)) ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hpos.le hle 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hc.le, mul_nonneg (mul_nonneg hq.le hc.le) (sq_nonneg Δ)]

/-! ### The continuous-time window (Theorem 3.1) -/

/-- Closed form of the window ratio (hypotheses `0<m`, `0<T`):
    `(2T/m - 2(1-e^{-mT})/m²)/(2mT) = 1/m² - (1-e^{-mT})/(T m³)`. -/
theorem window_ratio_closed {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    (2 * T / m - 2 * (1 - Real.exp (-(m * T))) / m ^ 2) / (2 * m * T)
      = 1 / m ^ 2 - (1 - Real.exp (-(m * T))) / (T * m ^ 3) := by
  field_simp

/-- The window factor (hypothesis `0<x`): `0 < 1 - (1-e^{-x})/x < 1`. -/
theorem window_factor_bounds {x : ℝ} (hx : 0 < x) :
    0 < 1 - (1 - Real.exp (-x)) / x ∧ 1 - (1 - Real.exp (-x)) / x < 1 := by
  have hlt : -x + 1 < Real.exp (-x) := Real.add_one_lt_exp (by linarith)
  have hexp1 : Real.exp (-x) < 1 := by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
    rwa [Real.exp_zero] at this
  constructor
  · have : (1 - Real.exp (-x)) / x < 1 := by
      rw [div_lt_one hx]; linarith
    linarith
  · have : 0 < (1 - Real.exp (-x)) / x := div_pos (by linarith) hx
    linarith

/-- **Abstract form of Theorem 3.1** (hypotheses: `0<p` for `‖φ‖²`, `0<m` for the gap,
    `0<κ`, `0<E`; the variance lower bound `2p/m ≤ V`; the Dirichlet-form upper bound
    `E ≤ 2mp/κ`; and `V/E ≤ C_P`).  Conclusion: `κ/m² ≤ C_P`. -/
theorem poincare_lower_of_gap {CP V E p m κ : ℝ} (hp : 0 < p) (hm : 0 < m) (hκ : 0 < κ)
    (hE : 0 < E) (hV : 2 * p / m ≤ V) (hEle : E ≤ 2 * m * p / κ) (hCP : V / E ≤ CP) :
    κ / m ^ 2 ≤ CP := by
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  calc κ / m ^ 2 = (2 * p / m) / (2 * m * p / κ) := by field_simp
    _ ≤ V / (2 * m * p / κ) := div_le_div_of_nonneg_right hV (by positivity)
    _ ≤ V / E := div_le_div_of_nonneg_left hV0 hE hEle
    _ ≤ CP := hCP

/-! ### Optimality among time-local functionals (Proposition 4.1) -/

/-- Finite-sum skeleton of `⟨φ,A⁻¹φ⟩ m² ≤ ⟨φ,Aφ⟩` (hypotheses `0<m`, `m ≤ a_k`, `0 ≤ c_k`). -/
theorem local_rayleigh_le {ι : Type*} (s : Finset ι) (c a : ι → ℝ) {m : ℝ}
    (hm : 0 < m) (ha : ∀ k ∈ s, m ≤ a k) (hc : ∀ k ∈ s, 0 ≤ c k) :
    (∑ k ∈ s, c k / a k) * m ^ 2 ≤ ∑ k ∈ s, c k * a k := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hak := ha k hk
  have hck := hc k hk
  have ha0 : 0 < a k := lt_of_lt_of_le hm hak
  rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
  have hsq : m ^ 2 ≤ a k * a k := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hck]

/-- Pointwise spectral weight (hypotheses `0<m≤a`): `2a/(a²+k²) ≤ 2a/m²`. -/
theorem fourier_weight_le {m a : ℝ} (k : ℝ) (hm : 0 < m) (ha : m ≤ a) :
    2 * a / (a ^ 2 + k ^ 2) ≤ 2 * a / m ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg k]

/-- Oscillating factor (hypotheses `0<m≤a`): `1/(a²+θ²) ≤ 1/m²`. -/
theorem oscillating_ratio_le {m a : ℝ} (θ : ℝ) (hm : 0 < m) (ha : m ≤ a) :
    1 / (a ^ 2 + θ ^ 2) ≤ 1 / m ^ 2 := by
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg θ]

/-! ### Corollary 3.6 and the exponent -/

/-- **Corollary 3.6** (hypotheses `0<m`, `κ/m² ≤ C_P`, `C_P ≤ K L²`):
    `κ ≤ K (m L)²`. -/
theorem gap_lower_of_poincare_upper {CP L m K κ : ℝ}
    (hm : 0 < m) (hCP : κ / m ^ 2 ≤ CP) (h : CP ≤ K * L ^ 2) :
    κ ≤ K * (m * L) ^ 2 := by
  have hm2 : (0:ℝ) < m ^ 2 := by positivity
  have h' : κ / m ^ 2 ≤ K * L ^ 2 := hCP.trans h
  rw [div_le_iff₀ hm2] at h'
  have : K * (m * L) ^ 2 = K * L ^ 2 * m ^ 2 := by ring
  rw [this]
  exact h'

/-- Lower half of the exponent (hypotheses `0<κ`, `1<ξ`, `κξ² ≤ C_P`):
    `2 + ln κ/ln ξ ≤ ln C_P/ln ξ`. -/
theorem power_lower_half {κ xi CP : ℝ} (hκ : 0 < κ) (hxi : 1 < xi)
    (h : κ * xi ^ 2 ≤ CP) :
    2 + Real.log κ / Real.log xi ≤ Real.log CP / Real.log xi := by
  have hl : 0 < Real.log xi := Real.log_pos hxi
  have hx0 : 0 < xi := by linarith
  have hpos : 0 < κ * xi ^ 2 := by positivity
  have h1 : Real.log (κ * xi ^ 2) ≤ Real.log CP := Real.log_le_log hpos h
  rw [Real.log_mul hκ.ne' (by positivity), Real.log_pow] at h1
  have heq : 2 + Real.log κ / Real.log xi = (Real.log κ + 2 * Real.log xi) / Real.log xi := by
    field_simp
    ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hl.le
  push_cast at h1
  linarith

/-! ### Negative control and the rotor -/

/-- **Negative control**: an exponent-one bound `1/m ≤ C_P` together with `C_P ≤ L²` does not
    bound `m L` from below: for every `κ>0` there are numbers with `(m L)² < κ`. -/
theorem linear_exponent_does_not_bridge (κ : ℝ) (hκ : 0 < κ) :
    ∃ m L CP : ℝ, 0 < m ∧ 1 / m ≤ CP ∧ CP ≤ 1 * L ^ 2 ∧ (m * L) ^ 2 < κ := by
  have hx : 0 < 1 + 1 / κ := by positivity
  refine ⟨1 / (1 + 1 / κ) ^ 2, 1 + 1 / κ, (1 + 1 / κ) ^ 2, by positivity, ?_, ?_, ?_⟩
  · rw [one_div_one_div]
  · rw [one_mul]
  · have e1 : (1 / (1 + 1 / κ) ^ 2 * (1 + 1 / κ)) ^ 2 = 1 / (1 + 1 / κ) ^ 2 := by
      field_simp
    rw [e1, div_lt_iff₀ (by positivity)]
    have e2 : κ * (1 + 1 / κ) ^ 2 = κ + 2 + 1 / κ := by
      field_simp
      ring
    have : 0 < 1 / κ := by positivity
    nlinarith [e2]

/-- Rotor (Proposition 5.1), arithmetic part (hypothesis `0<r`): for every `B` there is
    `L>0` with `B < L² r`. -/
theorem rotor_ratio_unbounded {r : ℝ} (hr : 0 < r) (B : ℝ) :
    ∃ L : ℝ, 0 < L ∧ B < L ^ 2 * r := by
  have hL1 : 1 ≤ |B| / r + 1 := by
    have : 0 ≤ |B| / r := div_nonneg (abs_nonneg B) hr.le
    linarith
  have hLr : (|B| / r + 1) * r = |B| + r := by
    field_simp
  refine ⟨|B| / r + 1, by positivity, ?_⟩
  have hprod : 0 ≤ ((|B| / r + 1) - 1) * ((|B| / r + 1) * r) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [le_abs_self B, hLr, hprod]

/-- Rotor gap (hypothesis `0<ħ`): `0 < ħ²/2`. -/
theorem rotor_gap_pos {hbar : ℝ} (h : 0 < hbar) : 0 < hbar ^ 2 / 2 := by positivity

end EuclideanPath.GapBridge

#print axioms EuclideanPath.GapBridge.edge_sum
#print axioms EuclideanPath.GapBridge.edge_sum'
#print axioms EuclideanPath.GapBridge.pair_sum_succ
#print axioms EuclideanPath.GapBridge.geom_shift
#print axioms EuclideanPath.GapBridge.pair_sum_closed
#print axioms EuclideanPath.GapBridge.discrete_limit_ge
#print axioms EuclideanPath.GapBridge.window_ratio_closed
#print axioms EuclideanPath.GapBridge.window_factor_bounds
#print axioms EuclideanPath.GapBridge.poincare_lower_of_gap
#print axioms EuclideanPath.GapBridge.local_rayleigh_le
#print axioms EuclideanPath.GapBridge.fourier_weight_le
#print axioms EuclideanPath.GapBridge.oscillating_ratio_le
#print axioms EuclideanPath.GapBridge.gap_lower_of_poincare_upper
#print axioms EuclideanPath.GapBridge.power_lower_half
#print axioms EuclideanPath.GapBridge.linear_exponent_does_not_bridge
#print axioms EuclideanPath.GapBridge.rotor_ratio_unbounded
#print axioms EuclideanPath.GapBridge.rotor_gap_pos
