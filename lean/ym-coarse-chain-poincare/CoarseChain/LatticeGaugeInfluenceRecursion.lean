import Mathlib

/-!
# Influence recursion for a one-dimensional chain: finite algebraic pieces

* `tp2_comp`: the composition of two TP2 kernels on a finite ordered index set is TP2
  (two-by-two Cauchy–Binet).  Used for the stochastic monotonicity in the boundary value.
* `cdf_upper`, `cdf_lower`: enclosure of a cumulative probability `A/(A+B)` from bounds on `A`, `B`.
* `k_upper`: the bound on `(1-F)·I + F·J` from bounds on `F`, `I`, `J`.
* `step_bound`: one step of the influence recursion with nonnegative weights.
* `gauss_product`: the product `∏ (15-i)/(16-i) = 1/2` (the Gaussian chain value).
-/

namespace LatticeGauge.InfluenceRecursion

open Finset

theorem tp2_comp {n : ℕ} (K K' g g' : Fin n → ℝ)
    (hK : ∀ w w' : Fin n, w ≤ w' → K w' * K' w ≤ K w * K' w')
    (hg : ∀ w w' : Fin n, w ≤ w' → g' w * g w' ≤ g w * g' w') :
    (∑ w, K w * g' w) * (∑ w, K' w * g w) ≤ (∑ w, K w * g w) * (∑ w, K' w * g' w) := by
  have key : ∀ w w' : Fin n,
      0 ≤ (K w * K' w' - K w' * K' w) * (g w * g' w' - g' w * g w') := by
    intro w w'
    rcases le_total w w' with h | h
    · exact mul_nonneg (by linarith [hK w w' h]) (by linarith [hg w w' h])
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hK w' w h]) (by linarith [hg w' w h])
  have hsum : 0 ≤ ∑ w, ∑ w', (K w * K' w' - K w' * K' w) * (g w * g' w' - g' w * g w') :=
    Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun w' _ => key w w'))
  have hsplit : ∑ w, ∑ w', (K w * K' w' - K w' * K' w) * (g w * g' w' - g' w * g w')
      = ∑ w, ∑ w', (K w * g w * (K' w' * g' w') - K w * g' w * (K' w' * g w'))
        + ∑ w, ∑ w', (K w' * g w' * (K' w * g' w) - K w' * g' w' * (K' w * g w)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    ring
  have hswap : ∑ w, ∑ w', (K w' * g w' * (K' w * g' w) - K w' * g' w' * (K' w * g w))
      = ∑ w, ∑ w', (K w * g w * (K' w' * g' w') - K w * g' w * (K' w' * g w')) := by
    rw [Finset.sum_comm]
  have hA : ∑ w, ∑ w', (K w * g w * (K' w' * g' w') - K w * g' w * (K' w' * g w'))
      = (∑ w, K w * g w) * (∑ w, K' w * g' w) - (∑ w, K w * g' w) * (∑ w, K' w * g w) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.sum_sub_distrib]
  rw [hsplit, hswap, hA] at hsum
  linarith

theorem cdf_upper (A B A' B' : ℝ) (hA : 0 ≤ A) (hB' : 0 < B') (hAA : A ≤ A') (hBB : B' ≤ B) :
    A / (A + B) ≤ A' / (A' + B') := by
  have h1 : 0 < A + B := by linarith
  have h2 : 0 < A' + B' := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_left hBB hA, mul_le_mul_of_nonneg_right hAA (le_of_lt hB')]

theorem cdf_lower (A B A' B' : ℝ) (hA' : 0 ≤ A') (hB : 0 < B) (hAA : A' ≤ A) (hBB : B ≤ B') :
    A' / (A' + B') ≤ A / (A + B) :=
  cdf_upper A' B' A B hA' hB hAA hBB

theorem k_upper (F Fl Fh I I' J J' : ℝ) (h0 : 0 ≤ F) (h1 : F ≤ 1) (hl : Fl ≤ F) (hh : F ≤ Fh)
    (hI : 0 ≤ I) (hII : I ≤ I') (hJ : 0 ≤ J) (hJJ : J ≤ J') :
    (1 - F) * I + F * J ≤ (1 - Fl) * I' + Fh * J' := by
  have a : (1 - F) * I ≤ (1 - Fl) * I' :=
    mul_le_mul (by linarith) hII hI (by linarith)
  have b : F * J ≤ Fh * J' := mul_le_mul hh hJJ hJ (by linarith)
  linarith

theorem step_bound {n : ℕ} (f F k kp w : Fin n → ℝ) (hf : ∀ j, 0 ≤ f j) (hfF : ∀ j, f j ≤ F j)
    (hk : ∀ j, 0 ≤ k j) (hkk : ∀ j, k j ≤ kp j) (hw : ∀ j, 0 ≤ w j) :
    ∑ j, f j * k j * w j ≤ ∑ j, F j * kp j * w j := by
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h1 : f j * k j ≤ F j * kp j :=
    mul_le_mul (hfF j) (hkk j) (hk j) (le_trans (hf j) (hfF j))
  exact mul_le_mul_of_nonneg_right h1 (hw j)

theorem gauss_product : ∏ i ∈ Finset.range 8, ((15 - i : ℚ) / (16 - i)) = 1 / 2 := by
  simp [Finset.prod_range_succ]
  norm_num

end LatticeGauge.InfluenceRecursion

#print axioms LatticeGauge.InfluenceRecursion.tp2_comp
#print axioms LatticeGauge.InfluenceRecursion.cdf_upper
#print axioms LatticeGauge.InfluenceRecursion.cdf_lower
#print axioms LatticeGauge.InfluenceRecursion.k_upper
#print axioms LatticeGauge.InfluenceRecursion.step_bound
#print axioms LatticeGauge.InfluenceRecursion.gauss_product
