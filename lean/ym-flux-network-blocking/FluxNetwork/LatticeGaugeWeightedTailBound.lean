import Mathlib

/-!
# Distance-weighted sums of exponentially decaying inter-block weights

For an inter-block weight profile `q : ℕ → ℝ` (weight at block distance `r`), the bound needed
for an estimate uniform in the volume is a bound on the distance-weighted sum
`Σ_{r < R} r · |q r|` that does not depend on the cut-off `R`.

* `weighted_geom_identity`: closed form of `(1-ρ)^2 Σ_{r<R} r ρ^r`.
* `weighted_geom_le`: `Σ_{r<R} r ρ^r ≤ ρ/(1-ρ)^2` for `0 ≤ ρ < 1`, every `R`.
* `weighted_tail_le`: if `|q r| ≤ C ρ^r` then `Σ_{r<R} r |q r| ≤ C ρ/(1-ρ)^2`, every `R`.
* `linear_prefactor_le`: `(r+1) σ^r (1-σ) ≤ 1` for `0 ≤ σ < 1`.
* `weighted_sum_uniform_linear`: if `|q r| ≤ C (r+1) (σ^2)^r` (exponential decay with a linear
  prefactor), then `Σ_{r<R} r |q r| ≤ C/(1-σ) · σ/(1-σ)^2`, every `R`.
-/

namespace LatticeGaugeWeightedTailBound

open Finset

theorem weighted_geom_identity (ρ : ℝ) (R : ℕ) :
    (1 - ρ) ^ 2 * ∑ r ∈ range R, (r : ℝ) * ρ ^ r
      = ρ - (R : ℝ) * ρ ^ R + (R : ℝ) * ρ ^ (R + 1) - ρ ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem weighted_geom_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) (R : ℕ) :
    ∑ r ∈ range R, (r : ℝ) * ρ ^ r ≤ ρ / (1 - ρ) ^ 2 := by
  have hpos : 0 < (1 - ρ) ^ 2 := by
    have : 0 < 1 - ρ := by linarith
    positivity
  rw [le_div_iff₀ hpos, mul_comm]
  have hid := weighted_geom_identity ρ R
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have hp : 0 ≤ ρ ^ R := pow_nonneg h0 R
  have key : (R : ℝ) * ρ ^ (R + 1) ≤ (R : ℝ) * ρ ^ R := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hp h1.le) hR
  have hq : 0 ≤ ρ ^ (R + 1) := pow_nonneg h0 _
  linarith [hid, key, hq]

theorem weighted_tail_le (q : ℕ → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    (hq : ∀ r, |q r| ≤ C * ρ ^ r) (R : ℕ) :
    ∑ r ∈ range R, (r : ℝ) * |q r| ≤ C * ρ / (1 - ρ) ^ 2 := by
  calc ∑ r ∈ range R, (r : ℝ) * |q r| ≤ ∑ r ∈ range R, C * ((r : ℝ) * ρ ^ r) :=
        sum_le_sum fun r _ =>
          le_trans (mul_le_mul_of_nonneg_left (hq r) (Nat.cast_nonneg r)) (le_of_eq (by ring))
    _ = C * ∑ r ∈ range R, (r : ℝ) * ρ ^ r := by rw [mul_sum]
    _ ≤ C * (ρ / (1 - ρ) ^ 2) := mul_le_mul_of_nonneg_left (weighted_geom_le ρ h0 h1 R) hC
    _ = C * ρ / (1 - ρ) ^ 2 := by ring

theorem linear_prefactor_le (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ < 1) (r : ℕ) :
    ((r : ℝ) + 1) * σ ^ r * (1 - σ) ≤ 1 := by
  have hs : ∀ k ∈ range (r + 1), σ ^ r ≤ σ ^ k := fun k hk =>
    pow_le_pow_of_le_one h0 h1.le (by simp at hk; omega)
  have hsum : ((r : ℝ) + 1) * σ ^ r ≤ ∑ k ∈ range (r + 1), σ ^ k := by
    have := Finset.card_nsmul_le_sum (range (r + 1)) (fun k => σ ^ k) (σ ^ r) hs
    simpa [nsmul_eq_mul] using this
  have hgeom : (∑ k ∈ range (r + 1), σ ^ k) * (1 - σ) = 1 - σ ^ (r + 1) := by
    calc (∑ k ∈ range (r + 1), σ ^ k) * (1 - σ)
        = -((∑ k ∈ range (r + 1), σ ^ k) * (σ - 1)) := by ring
      _ = 1 - σ ^ (r + 1) := by rw [geom_sum_mul]; ring
  have h1σ : 0 ≤ 1 - σ := by linarith
  calc ((r : ℝ) + 1) * σ ^ r * (1 - σ) ≤ (∑ k ∈ range (r + 1), σ ^ k) * (1 - σ) :=
        mul_le_mul_of_nonneg_right hsum h1σ
    _ = 1 - σ ^ (r + 1) := hgeom
    _ ≤ 1 := by have := pow_nonneg h0 (r + 1); linarith

theorem weighted_sum_uniform_linear (q : ℕ → ℝ) (C σ : ℝ) (hC : 0 ≤ C) (h0 : 0 ≤ σ)
    (h1 : σ < 1) (hq : ∀ r, |q r| ≤ C * ((r : ℝ) + 1) * (σ ^ 2) ^ r) (R : ℕ) :
    ∑ r ∈ range R, (r : ℝ) * |q r| ≤ C / (1 - σ) * σ / (1 - σ) ^ 2 := by
  have hpos : 0 < 1 - σ := by linarith
  have hq' : ∀ r, |q r| ≤ C / (1 - σ) * σ ^ r := by
    intro r
    have hl := linear_prefactor_le σ h0 h1 r
    have hb : ((r : ℝ) + 1) * σ ^ r ≤ 1 / (1 - σ) := by
      rw [le_div_iff₀ hpos]; exact hl
    calc |q r| ≤ C * ((r : ℝ) + 1) * (σ ^ 2) ^ r := hq r
      _ = C * (((r : ℝ) + 1) * σ ^ r) * σ ^ r := by
          rw [← pow_mul, show 2 * r = r + r by ring, pow_add]; ring
      _ ≤ C * (1 / (1 - σ)) * σ ^ r := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 r)
          exact mul_le_mul_of_nonneg_left hb hC
      _ = C / (1 - σ) * σ ^ r := by ring
  have hC' : 0 ≤ C / (1 - σ) := div_nonneg hC hpos.le
  exact weighted_tail_le q (C / (1 - σ)) σ hC' h0 h1 hq' R

end LatticeGaugeWeightedTailBound

#print axioms LatticeGaugeWeightedTailBound.weighted_geom_identity
#print axioms LatticeGaugeWeightedTailBound.weighted_geom_le
#print axioms LatticeGaugeWeightedTailBound.weighted_tail_le
#print axioms LatticeGaugeWeightedTailBound.linear_prefactor_le
#print axioms LatticeGaugeWeightedTailBound.weighted_sum_uniform_linear
