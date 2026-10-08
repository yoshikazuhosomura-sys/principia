/-
  Second batch of elementary ingredients for the "transfer" estimate of a
  time-band operator, and for the trace form of the Landau-Widom input.

  Background.  For `f` supported in `[-L,L]` with Fourier transform `F` one puts

      Θ(w) = (1/2π) ∫_{|x|>T} F(x+w) conj (F(x-w)) dx ,

  an entire function of exponential type `2L` whose value at `w = iδ` is the
  tail of `F(· + iδ)` outside the band.  The transfer estimate is a
  Phragmén-Lindelöf argument whose only real input is an upper bound for `|Θ|`
  on the real axis.  Two ways of producing such a bound are formalised here in
  their finite / one-variable form:

  * termwise Cauchy-Schwarz after Taylor expanding both factors,
      `|Θ(s)| ≤ (∑ₖ √Dₖ sᵏ/k!)²`  with  `Dₖ = (1/2π)∫_{|x|>T}|F⁽ᵏ⁾|²`
      (`termwise_bound`, `termwise_bound_of_profile`);
  * the harmonic measure computation that turns a piecewise bound on the real
      axis into a power of the smallness (`poisson_kernel_integral`,
      `poisson_linear_integral`, `poisson_profile_integral`,
      `poisson_exponent_lower`).

  For the trace side, `Σ_j φ_K(u_j) = tr Q - tr Q^{K+1}` with
  `φ_K(u) = (1-u)(1-(1-u)^K)`; the lemmas `phiK_eq`, `phiK_le_mul`,
  `deep_tail_negligible` show that eigenvalues below a cut `u_d` contribute at
  most `card * K * u_d`, and `sum_pow_ge_card_mul` is the one-sided
  (counting-lower-bound) route to `tr Q^{m}` from a trial subspace.

  No `sorry`, no `native_decide`.
-/
import Mathlib

open Finset

namespace TimeBand

/-! ### Termwise Cauchy-Schwarz (Taylor route) -/

/-- If every entry of a bilinear array is dominated by `√(D k) * √(D m)`, the
whole weighted double sum is dominated by the square of a single sum.  This is
the termwise form of Cauchy-Schwarz used for `Θ` after Taylor expansion. -/
theorem termwise_bound (n : ℕ) (c D : ℕ → ℝ) (X : ℕ → ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hX : ∀ k m, |X k m| ≤ Real.sqrt (D k) * Real.sqrt (D m)) :
    |∑ k ∈ range n, ∑ m ∈ range n, c k * c m * X k m|
      ≤ (∑ k ∈ range n, c k * Real.sqrt (D k)) ^ 2 := by
  have h1 : |∑ k ∈ range n, ∑ m ∈ range n, c k * c m * X k m|
      ≤ ∑ k ∈ range n, ∑ m ∈ range n, (c k * Real.sqrt (D k)) * (c m * Real.sqrt (D m)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro k _
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro m _
    have : |c k * c m * X k m| = (c k * c m) * |X k m| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hc k) (hc m))]
    rw [this]
    have := mul_le_mul_of_nonneg_left (hX k m) (mul_nonneg (hc k) (hc m))
    calc (c k * c m) * |X k m| ≤ (c k * c m) * (Real.sqrt (D k) * Real.sqrt (D m)) := this
      _ = (c k * Real.sqrt (D k)) * (c m * Real.sqrt (D m)) := by ring
  calc |∑ k ∈ range n, ∑ m ∈ range n, c k * c m * X k m|
      ≤ ∑ k ∈ range n, ∑ m ∈ range n, (c k * Real.sqrt (D k)) * (c m * Real.sqrt (D m)) := h1
    _ = (∑ k ∈ range n, c k * Real.sqrt (D k)) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]

/-- The bound produced by `termwise_bound` is `≤ C * u` as soon as every
`D k` is `≤ C k * u` with `∑ c k * √(C k) ≤ A`: the smallness `u` survives with
exponent one, the whole loss being in the constant `A ^ 2`. -/
theorem termwise_bound_of_profile (n : ℕ) (c C D : ℕ → ℝ) (u A : ℝ)
    (hc : ∀ k, 0 ≤ c k) (hu : 0 ≤ u) (hD : ∀ k, D k ≤ C k * u) (hC : ∀ k, 0 ≤ C k)
    (hA : ∑ k ∈ range n, c k * Real.sqrt (C k) ≤ A) (_hA0 : 0 ≤ A) :
    (∑ k ∈ range n, c k * Real.sqrt (D k)) ^ 2 ≤ A ^ 2 * u := by
  have h1 : ∑ k ∈ range n, c k * Real.sqrt (D k)
      ≤ (∑ k ∈ range n, c k * Real.sqrt (C k)) * Real.sqrt u := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro k _
    have : Real.sqrt (D k) ≤ Real.sqrt (C k) * Real.sqrt u := by
      rw [← Real.sqrt_mul (hC k)]
      exact Real.sqrt_le_sqrt (hD k)
    calc c k * Real.sqrt (D k) ≤ c k * (Real.sqrt (C k) * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left this (hc k)
      _ = c k * Real.sqrt (C k) * Real.sqrt u := by ring
  have h2 : (0:ℝ) ≤ ∑ k ∈ range n, c k * Real.sqrt (D k) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (Real.sqrt_nonneg _)
  have h3 : ∑ k ∈ range n, c k * Real.sqrt (D k) ≤ A * Real.sqrt u :=
    h1.trans (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg u))
  calc (∑ k ∈ range n, c k * Real.sqrt (D k)) ^ 2 ≤ (A * Real.sqrt u) ^ 2 := by
        exact pow_le_pow_left₀ h2 h3 2
    _ = A ^ 2 * u := by
        rw [mul_pow, Real.sq_sqrt hu]

/-! ### The harmonic measure of a profile -/

/-- `arctan y ≤ y` for `y ≥ 0`. -/
theorem arctan_le_self {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  by_contra hcon
  rw [not_le] at hcon
  have h1 : 0 < Real.arctan y := lt_of_le_of_lt hy hcon
  have h2 : Real.arctan y < Real.pi / 2 := Real.arctan_lt_pi_div_two y
  have h3 := Real.lt_tan h1 h2
  rw [Real.tan_arctan] at h3
  linarith


/-- `∫₀ˢ δ/(s²+δ²) ds = arctan (S/δ)`: the harmonic measure of `[0,S]` seen
from `iδ`, up to the factor `1/π`. -/
theorem poisson_kernel_integral {δ : ℝ} (hδ : 0 < δ) (S : ℝ) :
    (∫ s in (0:ℝ)..S, δ / (s ^ 2 + δ ^ 2)) = Real.arctan (S / δ) := by
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have key : ∀ s : ℝ, HasDerivAt (fun x : ℝ => Real.arctan (x / δ)) (δ / (s ^ 2 + δ ^ 2)) s := by
    intro s
    have hd : (0:ℝ) < s ^ 2 + δ ^ 2 := by positivity
    have hne1 : (1 + (s / δ) ^ 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => x / δ) (1 / δ) s := by
      simpa using (hasDerivAt_id s).div_const δ
    have h2 : HasDerivAt (Real.arctan ∘ fun x : ℝ => x / δ)
        (1 / (1 + (s / δ) ^ 2) * (1 / δ)) s := (Real.hasDerivAt_arctan (s / δ)).comp s h1
    have heq : 1 / (1 + (s / δ) ^ 2) * (1 / δ) = δ / (s ^ 2 + δ ^ 2) := by
      rw [div_pow]
      field_simp
      try ring
    rw [heq] at h2
    simpa [Function.comp_def] using h2
  have hcont : IntervalIntegrable (fun s : ℝ => δ / (s ^ 2 + δ ^ 2)) MeasureTheory.volume 0 S := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by continuity)
    intro x; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => key s) hcont]
  simp

/-- `∫₀ˢ s·δ/(s²+δ²) ds = (δ/2)·log((S²+δ²)/δ²)`. -/
theorem poisson_linear_integral {δ : ℝ} (hδ : 0 < δ) (S : ℝ) :
    (∫ s in (0:ℝ)..S, s * δ / (s ^ 2 + δ ^ 2))
      = δ / 2 * Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2) := by
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  have key : ∀ s : ℝ, HasDerivAt (fun x : ℝ => δ / 2 * Real.log ((x ^ 2 + δ ^ 2) / δ ^ 2))
      (s * δ / (s ^ 2 + δ ^ 2)) s := by
    intro s
    have hd : (0:ℝ) < s ^ 2 + δ ^ 2 := by positivity
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have hbase : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * s) s := hp.add_const _
    have h1 : HasDerivAt (fun x : ℝ => (x ^ 2 + δ ^ 2) / δ ^ 2) (2 * s / δ ^ 2) s :=
      hbase.div_const _
    have hne : ((s ^ 2 + δ ^ 2) / δ ^ 2) ≠ 0 := by positivity
    have h2 := HasDerivAt.const_mul (δ / 2) (h1.log hne)
    have heq : δ / 2 * (2 * s / δ ^ 2 / ((s ^ 2 + δ ^ 2) / δ ^ 2)) = s * δ / (s ^ 2 + δ ^ 2) := by
      field_simp
      try ring
    rw [heq] at h2
    exact h2
  have hcont : IntervalIntegrable (fun s : ℝ => s * δ / (s ^ 2 + δ ^ 2))
      MeasureTheory.volume 0 S := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by continuity) (by continuity)
    intro x; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => key s) hcont]
  simp

/-- The exponent produced by a profile that decays linearly from `1` at `0` to
`0` at `S`:  `(2/π) ∫₀ˢ (1 - s/S)·δ/(s²+δ²) ds`. -/
theorem poisson_profile_integral {δ S : ℝ} (hδ : 0 < δ) (hS : 0 < S) :
    (∫ s in (0:ℝ)..S, (1 - s / S) * (δ / (s ^ 2 + δ ^ 2)))
      = Real.arctan (S / δ) - δ / (2 * S) * Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2) := by
  have h1 : IntervalIntegrable (fun s : ℝ => δ / (s ^ 2 + δ ^ 2)) MeasureTheory.volume 0 S := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by continuity)
    intro x; positivity
  have h2 : IntervalIntegrable (fun s : ℝ => s / S * (δ / (s ^ 2 + δ ^ 2)))
      MeasureTheory.volume 0 S := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul (by continuity)
    apply Continuous.div continuous_const (by continuity)
    intro x; positivity
  have hsplit : (∫ s in (0:ℝ)..S, (1 - s / S) * (δ / (s ^ 2 + δ ^ 2)))
      = (∫ s in (0:ℝ)..S, δ / (s ^ 2 + δ ^ 2))
        - ∫ s in (0:ℝ)..S, s / S * (δ / (s ^ 2 + δ ^ 2)) := by
    rw [← intervalIntegral.integral_sub h1 h2]
    congr 1; funext s; ring
  have h3 : (∫ s in (0:ℝ)..S, s / S * (δ / (s ^ 2 + δ ^ 2)))
      = (1 / S) * ∫ s in (0:ℝ)..S, s * δ / (s ^ 2 + δ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s
    field_simp
    try ring
  rw [hsplit, poisson_kernel_integral hδ S, h3, poisson_linear_integral hδ S]
  field_simp
  try ring

/-- A clean lower bound for that exponent: it is `1` up to `O((δ/S) log (S/δ))`.
So a profile that is flat (exponent one) on `[-S,S]` loses only a logarithmic
amount of the exponent when `δ ≪ S`. -/
theorem poisson_exponent_lower {δ S : ℝ} (hδ : 0 < δ) (hS : δ ≤ S) :
    1 - (2 * δ / (Real.pi * S)) * (3 / 2 + Real.log (S / δ))
      ≤ (2 / Real.pi) * (Real.arctan (S / δ)
          - δ / (2 * S) * Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2)) := by
  have hS0 : 0 < S := lt_of_lt_of_le hδ hS
  have hx : 0 < S / δ := div_pos hS0 hδ
  have h1 : Real.pi / 2 - δ / S ≤ Real.arctan (S / δ) := by
    have hinv : Real.arctan (δ / S) = Real.pi / 2 - Real.arctan (S / δ) := by
      rw [← Real.arctan_inv_of_pos hx]
      congr 1
      field_simp
    have h2 : Real.arctan (δ / S) ≤ δ / S := arctan_le_self (by positivity)
    linarith [hinv ▸ h2]
  have hlog : Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2) ≤ 2 * Real.log (S / δ) + 1 := by
    have hle : (S ^ 2 + δ ^ 2) / δ ^ 2 ≤ 2 * (S / δ) ^ 2 := by
      have hid : (S ^ 2 + δ ^ 2) / δ ^ 2 = (S / δ) ^ 2 + 1 := by
        field_simp
      have hge : (1:ℝ) ≤ (S / δ) ^ 2 := by
        have : (1:ℝ) ≤ S / δ := (one_le_div hδ).mpr hS
        nlinarith
      rw [hid]; linarith
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    push_cast at this
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hstep : Real.arctan (S / δ) - δ / (2 * S) * Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2)
      ≥ Real.pi / 2 - δ / S - δ / (2 * S) * (2 * Real.log (S / δ) + 1) := by
    have hpos : 0 < δ / (2 * S) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog hpos.le]
  have hexp : (2 / Real.pi) * (Real.pi / 2 - δ / S - δ / (2 * S) * (2 * Real.log (S / δ) + 1))
      = 1 - (2 * δ / (Real.pi * S)) * (3 / 2 + Real.log (S / δ)) := by
    field_simp
    ring
  calc 1 - (2 * δ / (Real.pi * S)) * (3 / 2 + Real.log (S / δ))
      = (2 / Real.pi) * (Real.pi / 2 - δ / S - δ / (2 * S) * (2 * Real.log (S / δ) + 1)) :=
        hexp.symm
    _ ≤ (2 / Real.pi) * (Real.arctan (S / δ)
          - δ / (2 * S) * Real.log ((S ^ 2 + δ ^ 2) / δ ^ 2)) := by
        have : (0:ℝ) < 2 / Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hstep this.le

/-! ### The trace side: `φ_K` and the deep cut -/

/-- `φ_K u = (1-u)(1-(1-u)^K)`, the weight whose spectral sum is
`tr Q - tr Q^{K+1}`. -/
noncomputable def phiK (K : ℕ) (u : ℝ) : ℝ := (1 - u) * (1 - (1 - u) ^ K)

theorem phiK_eq (K : ℕ) (u : ℝ) : phiK K u = (1 - u) - (1 - u) ^ (K + 1) := by
  unfold phiK; ring

theorem phiK_nonneg {K : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ phiK K u := by
  unfold phiK
  have hu : 0 ≤ 1 - u := by linarith
  have : (1 - u) ^ K ≤ 1 := pow_le_one₀ hu (by linarith)
  exact mul_nonneg hu (by linarith)

theorem phiK_le_one {K : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : phiK K u ≤ 1 := by
  unfold phiK
  have hu : 0 ≤ 1 - u := by linarith
  have hp : 0 ≤ (1 - u) ^ K := pow_nonneg hu K
  nlinarith

/-- Bernoulli: on `[0,1]`, `φ_K u ≤ K * u`.  This is what makes the eigenvalues
below a cut `u_d` contribute nothing once `K * u_d` is small. -/
theorem phiK_le_mul {K : ℕ} {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : phiK K u ≤ K * u := by
  have hber : 1 - K * u ≤ (1 - u) ^ K := by
    have := one_add_mul_le_pow (a := -u) (by linarith) K
    simpa [sub_eq_add_neg, mul_comm] using this
  have hu : 0 ≤ 1 - u := by linarith
  have hKu : 0 ≤ (K : ℝ) * u := by positivity
  unfold phiK
  nlinarith [pow_nonneg hu K]

/-- The eigenvalues below the cut contribute at most `card * K * u_d`. -/
theorem deep_tail_negligible {ι : Type*} (s : Finset ι) (K : ℕ) (ud : ℝ) (u : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ u j) (hcut : ∀ j ∈ s, u j ≤ ud) (hud : ud ≤ 1) :
    ∑ j ∈ s, phiK K (u j) ≤ s.card * (K * ud) := by
  have : ∀ j ∈ s, phiK K (u j) ≤ K * ud := by
    intro j hj
    have h1 : u j ≤ 1 := le_trans (hcut j hj) hud
    refine (phiK_le_mul (h0 j hj) h1).trans ?_
    exact mul_le_mul_of_nonneg_left (hcut j hj) (by positivity)
  calc ∑ j ∈ s, phiK K (u j) ≤ ∑ _j ∈ s, (K * ud) := Finset.sum_le_sum this
    _ = s.card * (K * ud) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- One-sided route to `(LW∞)`: a trial subspace on which the deficiency is at
most `u` forces `tr Q^m ≥ (dimension) * (1-u)^m`.  Only a *lower* bound on the
number of deep eigenvalues is needed, never a two-sided Landau-Widom remainder. -/
theorem sum_pow_ge_card_mul {ι : Type*} (s : Finset ι) (m : ℕ) (lam : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ j ∈ s, c ≤ lam j) :
    (s.card : ℝ) * c ^ m ≤ ∑ j ∈ s, (lam j) ^ m := by
  calc (s.card : ℝ) * c ^ m = ∑ _j ∈ s, c ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ s, (lam j) ^ m :=
        Finset.sum_le_sum fun j hj => pow_le_pow_left₀ hc (h j hj) m

/-- Splitting the spectral sum at a cut.  Together with `deep_tail_negligible`
this is the corrected form of the Stieltjes step: what is needed is a bound on
the counting function *inside a window*, the part below the cut being harmless. -/
theorem sum_split_at_cut {ι : Type*} (s : Finset ι) (K : ℕ) (ud : ℝ) (u : ι → ℝ)
    [DecidablePred fun j => u j ≤ ud] :
    ∑ j ∈ s, phiK K (u j)
      = (∑ j ∈ s.filter (fun j => u j ≤ ud), phiK K (u j))
        + ∑ j ∈ s.filter (fun j => ¬ u j ≤ ud), phiK K (u j) :=
  (Finset.sum_filter_add_sum_filter_not s _ _).symm

end TimeBand

#print axioms TimeBand.termwise_bound
#print axioms TimeBand.termwise_bound_of_profile
#print axioms TimeBand.arctan_le_self
#print axioms TimeBand.poisson_kernel_integral
#print axioms TimeBand.poisson_linear_integral
#print axioms TimeBand.poisson_profile_integral
#print axioms TimeBand.poisson_exponent_lower
#print axioms TimeBand.phiK_eq
#print axioms TimeBand.phiK_nonneg
#print axioms TimeBand.phiK_le_one
#print axioms TimeBand.phiK_le_mul
#print axioms TimeBand.deep_tail_negligible
#print axioms TimeBand.sum_pow_ge_card_mul
#print axioms TimeBand.sum_split_at_cut
