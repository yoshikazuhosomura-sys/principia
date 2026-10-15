import Mathlib

/-!
# Ledger for the multi-step quartic cone and the block-covariance flow (finite, scalar facts)

* `cone_chain` (restated from `LatticeGaugeQuarticRowColumnBound.lean`, same statement and proof):
  if `|x (k+1)| ≤ M k * |x k|` then `|x n| ≤ c * ∏_{k<n} M k`.
* `cone_chain_uniform`: if moreover `M k ≤ m` for all `k`, then `|x n| ≤ c * m ^ n`.
* `growth_ledger` / `inverse_decay`: if a scalar `g` (a covariance eigenvalue) satisfies
  `r * g k ≤ g (k+1)`, then `r ^ n * g 0 ≤ g n`, and its inverse (the action eigenvalue) is at most
  `1 / (r ^ n * g 0)`.
* `face_sum_sq` : `(a+b+c+e)^2 ≤ 4 (a^2+b^2+c^2+e^2)` (the norm `‖S‖² = 4` of the 2×2 face sum).
* `four_split_quartic_floor` : if `a+b+c+e = t` then `t^4/64 ≤ a^4+b^4+c^4+e^4`,
  with equality for the even split `t/4` (`even_split_quartic`).
No lattice, Fourier transform or minimisation is formalised here.
-/

namespace LatticeGauge.BlockCovariance

open Finset

theorem cone_chain (n : ℕ) (c : ℝ) (M : ℕ → ℝ) (hc : 0 ≤ c) (hM : ∀ k, 0 ≤ M k)
    (x : ℕ → ℝ) (hx0 : |x 0| ≤ c) (hstep : ∀ k, |x (k + 1)| ≤ M k * |x k|) :
    |x n| ≤ c * ∏ k ∈ range n, M k := by
  induction n with
  | zero => simpa using hx0
  | succ n ih =>
    rw [prod_range_succ]
    calc |x (n + 1)| ≤ M n * |x n| := hstep n
      _ ≤ M n * (c * ∏ k ∈ range n, M k) := mul_le_mul_of_nonneg_left ih (hM n)
      _ = c * ((∏ k ∈ range n, M k) * M n) := by ring

theorem cone_chain_uniform (n : ℕ) (c m : ℝ) (M : ℕ → ℝ) (hc : 0 ≤ c) (hM : ∀ k, 0 ≤ M k)
    (hm : ∀ k, M k ≤ m) (x : ℕ → ℝ) (hx0 : |x 0| ≤ c)
    (hstep : ∀ k, |x (k + 1)| ≤ M k * |x k|) :
    |x n| ≤ c * m ^ n := by
  have h1 := cone_chain n c M hc hM x hx0 hstep
  have h2 : ∏ k ∈ range n, M k ≤ ∏ _k ∈ range n, m :=
    prod_le_prod (fun k _ => hM k) (fun k _ => hm k)
  rw [prod_const, card_range] at h2
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)

theorem growth_ledger (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (g : ℕ → ℝ)
    (hstep : ∀ k, r * g k ≤ g (k + 1)) : r ^ n * g 0 ≤ g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc r ^ (n + 1) * g 0 = r * (r ^ n * g 0) := by ring
      _ ≤ r * g n := mul_le_mul_of_nonneg_left ih hr
      _ ≤ g (n + 1) := hstep n

theorem inverse_decay (n : ℕ) (r : ℝ) (hr : 0 < r) (g : ℕ → ℝ) (hg0 : 0 < g 0)
    (hstep : ∀ k, r * g k ≤ g (k + 1)) : 1 / g n ≤ 1 / (r ^ n * g 0) := by
  have h := growth_ledger n r hr.le g hstep
  have hpos : 0 < r ^ n * g 0 := mul_pos (pow_pos hr n) hg0
  exact one_div_le_one_div_of_le hpos h

theorem face_sum_sq (a b c e : ℝ) : (a + b + c + e) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

theorem four_split_quartic_floor (a b c e t : ℝ) (h : a + b + c + e = t) :
    t ^ 4 / 64 ≤ a ^ 4 + b ^ 4 + c ^ 4 + e ^ 4 := by
  have h2 : t ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
    rw [← h]; exact face_sum_sq a b c e
  have h4 : (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) ^ 2 ≤ 4 * (a ^ 4 + b ^ 4 + c ^ 4 + e ^ 4) := by
    have := face_sum_sq (a ^ 2) (b ^ 2) (c ^ 2) (e ^ 2)
    nlinarith [this]
  have ht : 0 ≤ t ^ 2 := sq_nonneg t
  have hsq : (t ^ 2) ^ 2 ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2)) ^ 2 :=
    pow_le_pow_left₀ ht h2 2
  nlinarith [hsq, h4]

theorem even_split_quartic (t : ℝ) : 4 * (t / 4) ^ 4 = t ^ 4 / 64 := by ring

end LatticeGauge.BlockCovariance

#print axioms LatticeGauge.BlockCovariance.cone_chain
#print axioms LatticeGauge.BlockCovariance.cone_chain_uniform
#print axioms LatticeGauge.BlockCovariance.growth_ledger
#print axioms LatticeGauge.BlockCovariance.inverse_decay
#print axioms LatticeGauge.BlockCovariance.face_sum_sq
#print axioms LatticeGauge.BlockCovariance.four_split_quartic_floor
#print axioms LatticeGauge.BlockCovariance.even_split_quartic
