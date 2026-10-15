import Mathlib

/-!
# Ledger for the averaged blocking: fixed point of an affine flow, geometric tails, multi-step cone sums

Scalar facts used for the covariance flow `G_{k+1} = Φ(G_k)` of the averaged (transverse) blocking.
* `affine_iter` / `affine_dist`: if `g (k+1) = r * g k + s` with `r ≠ 1`, then
  `g n - s/(1-r) = r^n * (g 0 - s/(1-r))`, and for `0 ≤ r` the distance to the fixed point is `r^n` times the initial one.
* `tail_sum` / `tail_bound`: if successive differences obey `|g (k+1) - g k| ≤ δ * r^k` (`0 ≤ r < 1`, `0 ≤ δ`),
  then `|g (m+j) - g m| ≤ δ * r^m / (1-r)` (a Cauchy certificate for convergence from a contraction ratio).
* `axis_flow_closed`: `G k = 1/3 + (2/3) (1/4)^k` solves `G (k+1) = (G k + 1)/4`, `1/G k < 3`,
  and `3 - 1/G k ≤ 6 (1/4)^k`; `axis_flow_values`: `1/G 1 = 2`, `1/G 2 = 8/3`, `1/G 3 = 32/11`, `1/G 4 = 128/43`.
* `cone_series`: if `0 ≤ x (k+1) ≤ c * x k` with `0 ≤ c < 1`, then `∑_{k<n} x k ≤ x 0 / (1 - c)`
  (the geometric series of the multi-step cone; compare `cone_chain_uniform` in
  `LatticeGaugeBlockCovarianceLedger.lean`, which gives `x n ≤ x 0 * c^n`).
No lattice, Fourier transform or minimisation is formalised here; that the lattice flow obeys these
hypotheses is a computation, not part of this file.
-/

namespace LatticeGauge.AveragedBlockFlow

open Finset

theorem affine_iter (r s : ℝ) (hr : r ≠ 1) (g : ℕ → ℝ) (h : ∀ k, g (k + 1) = r * g k + s) (n : ℕ) :
    g n - s / (1 - r) = r ^ n * (g 0 - s / (1 - r)) := by
  have h1 : (1 - r) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have key : ∀ k, g (k + 1) - s / (1 - r) = r * (g k - s / (1 - r)) := by
    intro k
    rw [h k]
    field_simp
    ring
  induction n with
  | zero => simp
  | succ n ih => rw [key n, ih]; ring

theorem affine_dist (r s : ℝ) (hr0 : 0 ≤ r) (hr : r ≠ 1) (g : ℕ → ℝ)
    (h : ∀ k, g (k + 1) = r * g k + s) (n : ℕ) :
    |g n - s / (1 - r)| = r ^ n * |g 0 - s / (1 - r)| := by
  rw [affine_iter r s hr g h n, abs_mul, abs_pow, abs_of_nonneg hr0]

theorem tail_sum (g : ℕ → ℝ) (δ r : ℝ) (h : ∀ k, |g (k + 1) - g k| ≤ δ * r ^ k) (m j : ℕ) :
    |g (m + j) - g m| ≤ δ * ∑ i ∈ range j, r ^ (m + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, mul_add, show m + (j + 1) = m + j + 1 by omega]
    calc |g (m + j + 1) - g m| ≤ |g (m + j + 1) - g (m + j)| + |g (m + j) - g m| :=
          abs_sub_le _ _ _
      _ ≤ δ * r ^ (m + j) + δ * ∑ i ∈ range j, r ^ (m + i) := add_le_add (h (m + j)) ih
      _ = δ * ∑ i ∈ range j, r ^ (m + i) + δ * r ^ (m + j) := by ring

theorem tail_bound (g : ℕ → ℝ) (δ r : ℝ) (hδ : 0 ≤ δ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, |g (k + 1) - g k| ≤ δ * r ^ k) (m j : ℕ) :
    |g (m + j) - g m| ≤ δ * r ^ m / (1 - r) := by
  have h1 := tail_sum g δ r h m j
  have hS : ∑ i ∈ range j, r ^ (m + i) = r ^ m * ∑ i ∈ range j, r ^ i := by
    rw [mul_sum]; exact sum_congr rfl (fun i _ => pow_add r m i)
  have hg : (∑ i ∈ range j, r ^ i) * (r - 1) = r ^ j - 1 := geom_sum_mul r j
  have hpos : 0 < 1 - r := by linarith
  have hrj : 0 ≤ r ^ j := pow_nonneg hr0 j
  have hmul : (∑ i ∈ range j, r ^ i) * (1 - r) = 1 - r ^ j := by linear_combination (-1 : ℝ) * hg
  have hsum : ∑ i ∈ range j, r ^ i ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hpos, hmul]; linarith
  calc |g (m + j) - g m| ≤ δ * ∑ i ∈ range j, r ^ (m + i) := h1
    _ = δ * r ^ m * ∑ i ∈ range j, r ^ i := by rw [hS]; ring
    _ ≤ δ * r ^ m * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hδ (pow_nonneg hr0 m))
    _ = δ * r ^ m / (1 - r) := by ring

/-- the closed form of the (π,0,0,0) covariance eigenvalue sequence (numbers from the flow) -/
noncomputable def axisG (k : ℕ) : ℝ := 1 / 3 + 2 / 3 * (1 / 4 : ℝ) ^ k

theorem axis_flow_closed (k : ℕ) :
    axisG (k + 1) = (axisG k + 1) / 4 ∧ 1 / axisG k < 3 ∧ 3 - 1 / axisG k ≤ 6 * (1 / 4 : ℝ) ^ k := by
  have hp : 0 < (1 / 4 : ℝ) ^ k := pow_pos (by norm_num) k
  have hG : 0 < axisG k := by unfold axisG; positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold axisG; rw [pow_succ]; ring
  · rw [div_lt_iff₀ hG]; unfold axisG; nlinarith
  · have h3 : 3 - 1 / axisG k = 9 * (2 / 3 * (1 / 4 : ℝ) ^ k) / (1 + 3 * (2 / 3 * (1 / 4 : ℝ) ^ k)) := by
      unfold axisG; field_simp; ring
    rw [h3, div_le_iff₀ (by positivity)]
    nlinarith

theorem axis_flow_values :
    1 / axisG 1 = 2 ∧ 1 / axisG 2 = 8 / 3 ∧ 1 / axisG 3 = 32 / 11 ∧ 1 / axisG 4 = 128 / 43 := by
  unfold axisG; norm_num

theorem cone_series (x : ℕ → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hx : ∀ k, 0 ≤ x k)
    (hstep : ∀ k, x (k + 1) ≤ c * x k) (n : ℕ) :
    ∑ k ∈ range n, x k ≤ x 0 / (1 - c) := by
  have hpow : ∀ k, x k ≤ x 0 * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x (k + 1) ≤ c * x k := hstep k
        _ ≤ c * (x 0 * c ^ k) := mul_le_mul_of_nonneg_left ih hc0
        _ = x 0 * c ^ (k + 1) := by ring
  have hpos : 0 < 1 - c := by linarith
  have hg : (∑ i ∈ range n, c ^ i) * (c - 1) = c ^ n - 1 := geom_sum_mul c n
  have hmul : (∑ i ∈ range n, c ^ i) * (1 - c) = 1 - c ^ n := by linear_combination (-1 : ℝ) * hg
  have hsum : ∑ i ∈ range n, c ^ i ≤ 1 / (1 - c) := by
    rw [le_div_iff₀ hpos, hmul]; linarith [pow_nonneg hc0 n]
  calc ∑ k ∈ range n, x k ≤ ∑ k ∈ range n, x 0 * c ^ k := sum_le_sum (fun k _ => hpow k)
    _ = x 0 * ∑ k ∈ range n, c ^ k := by rw [mul_sum]
    _ ≤ x 0 * (1 / (1 - c)) := mul_le_mul_of_nonneg_left hsum (hx 0)
    _ = x 0 / (1 - c) := by ring

end LatticeGauge.AveragedBlockFlow

#print axioms LatticeGauge.AveragedBlockFlow.affine_iter
#print axioms LatticeGauge.AveragedBlockFlow.affine_dist
#print axioms LatticeGauge.AveragedBlockFlow.tail_sum
#print axioms LatticeGauge.AveragedBlockFlow.tail_bound
#print axioms LatticeGauge.AveragedBlockFlow.axis_flow_closed
#print axioms LatticeGauge.AveragedBlockFlow.axis_flow_values
#print axioms LatticeGauge.AveragedBlockFlow.cone_series
