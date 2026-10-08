/-
  A certificate that the trace-three secant test polynomial `p` is strictly "sub-additive in second differences"
  on the classes of norm at least one:  for `a, b ∈ ℝ³_{>0}` with `a₁a₂a₃ ≥ 1` and `b₁b₂b₃ ≥ 1`,
      `p(a+b) − p(a) − p(b) + p(0) < 0`,   while   `p(0) = 15176 > 0`.
  `p` is symmetric of multidegree ≤ (2,2,2) and lies in the span of `g(u_j)·u_k^α·u_l^β` with `g(x) = (x−3)² + 19`,
  i.e. it vanishes at the eight points `(3 ± i√19)³` (theorem `p_mem`).
  Proof: `−Δp` is a sum of mixed monomials; each negative monomial is absorbed by a weighted AM–GM inequality
  (integer weights `k_i`, `∑ k_i = L`) after multiplying by a power of `a₁a₂a₃ ≥ 1` or `b₁b₂b₃ ≥ 1`.
  Fourteen column lemmas, each used at the twelve images under permuting the slots and swapping `a ↔ b`.
-/
import Mathlib

set_option linter.unusedVariables false

namespace TraceThreeCertificate

open Finset in
/-- Integer-weighted AM–GM: `y^L ≤ ∏ x_i^{k_i}` and `∑ k_i = L` give `L*y ≤ ∑ k_i*x_i`. -/
theorem amgm_nat {n : ℕ} (x : Fin n → ℝ) (k : Fin n → ℕ) (L : ℕ) (hL : L ≠ 0)
    (hk : ∑ i, k i = L) (hx : ∀ i, 0 ≤ x i) (y : ℝ) (hy : 0 ≤ y)
    (h : y ^ L ≤ ∏ i, x i ^ k i) : (L : ℝ) * y ≤ ∑ i, (k i : ℝ) * x i := by
  have hLpos : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  have hw : ∀ i ∈ (univ : Finset (Fin n)), (0:ℝ) ≤ (k i : ℝ) / L := fun i _ => by positivity
  have hw' : ∑ i ∈ (univ : Finset (Fin n)), (k i : ℝ) / L = 1 := by
    rw [← Finset.sum_div, div_eq_one_iff_eq hLpos.ne']; exact_mod_cast hk
  have amgm := Real.geom_mean_le_arith_mean_weighted univ (fun i => (k i : ℝ) / L) x hw hw'
    (fun i _ => hx i)
  have h1 : y ≤ ∏ i, x i ^ ((k i : ℝ) / L) := by
    calc y = (y ^ L) ^ ((L:ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hy hL).symm
      _ ≤ (∏ i, x i ^ k i) ^ ((L:ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg hy _) h (by positivity)
      _ = ∏ i, (x i ^ k i) ^ ((L:ℝ)⁻¹) :=
          (Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hx i) _) _).symm
      _ = ∏ i, x i ^ ((k i : ℝ) / L) := by
          apply Finset.prod_congr rfl; intro i _
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i), div_eq_mul_inv]
  have h2 : ∑ i, (k i : ℝ) / L * x i = (∑ i, (k i : ℝ) * x i) / L := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
  have h3 := h1.trans amgm
  rw [h2, le_div_iff₀ hLpos] at h3
  linarith

theorem amgm2 (x1 x2 y : ℝ) (k1 k2 L : ℕ) (hL : L ≠ 0) (hk : k1 + k2 = L)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (hy : 0 ≤ y) (h : y ^ L ≤ x1 ^ k1 * x2 ^ k2) :
    (L : ℝ) * y ≤ k1 * x1 + k2 * x2 := by
  have := amgm_nat ![x1, x2] ![k1, k2] L hL
    (by simp [Fin.sum_univ_succ]; omega) (by intro i; fin_cases i <;> simp [h1, h2]) y hy
    (by simpa [Fin.prod_univ_succ, mul_assoc] using h)
  simpa [Fin.sum_univ_succ, add_assoc] using this

theorem amgm3 (x1 x2 x3 y : ℝ) (k1 k2 k3 L : ℕ) (hL : L ≠ 0) (hk : k1 + k2 + k3 = L)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (hy : 0 ≤ y)
    (h : y ^ L ≤ x1 ^ k1 * x2 ^ k2 * x3 ^ k3) :
    (L : ℝ) * y ≤ k1 * x1 + k2 * x2 + k3 * x3 := by
  have := amgm_nat ![x1, x2, x3] ![k1, k2, k3] L hL
    (by simp [Fin.sum_univ_succ]; omega) (by intro i; fin_cases i <;> simp [h1, h2, h3]) y hy
    (by simpa [Fin.prod_univ_succ, mul_assoc] using h)
  simpa [Fin.sum_univ_succ, add_assoc] using this

theorem amgm4 (x1 x2 x3 x4 y : ℝ) (k1 k2 k3 k4 L : ℕ) (hL : L ≠ 0) (hk : k1 + k2 + k3 + k4 = L)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4) (hy : 0 ≤ y)
    (h : y ^ L ≤ x1 ^ k1 * x2 ^ k2 * x3 ^ k3 * x4 ^ k4) :
    (L : ℝ) * y ≤ k1 * x1 + k2 * x2 + k3 * x3 + k4 * x4 := by
  have := amgm_nat ![x1, x2, x3, x4] ![k1, k2, k3, k4] L hL
    (by simp [Fin.sum_univ_succ]; omega) (by intro i; fin_cases i <;> simp [h1, h2, h3, h4]) y hy
    (by simpa [Fin.prod_univ_succ, mul_assoc] using h)
  simpa [Fin.sum_univ_succ, add_assoc] using this

theorem amgm5 (x1 x2 x3 x4 x5 y : ℝ) (k1 k2 k3 k4 k5 L : ℕ) (hL : L ≠ 0)
    (hk : k1 + k2 + k3 + k4 + k5 = L)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4) (h5 : 0 ≤ x5) (hy : 0 ≤ y)
    (h : y ^ L ≤ x1 ^ k1 * x2 ^ k2 * x3 ^ k3 * x4 ^ k4 * x5 ^ k5) :
    (L : ℝ) * y ≤ k1 * x1 + k2 * x2 + k3 * x3 + k4 * x4 + k5 * x5 := by
  have := amgm_nat ![x1, x2, x3, x4, x5] ![k1, k2, k3, k4, k5] L hL
    (by simp [Fin.sum_univ_succ]; omega) (by intro i; fin_cases i <;> simp [h1, h2, h3, h4, h5]) y hy
    (by simpa [Fin.prod_univ_succ, mul_assoc] using h)
  simpa [Fin.sum_univ_succ, add_assoc] using this

/-- The symmetric polynomial `p` (orbit coefficients 15176, -1420, -460, 342, -62, -92, 29, -18, -6, -1). -/
def p (u1 u2 u3 : ℝ) : ℝ :=
  (15176:ℝ) + (-1420:ℝ)*(u1+u2+u3) + (-460:ℝ)*(u1*u2+u1*u3+u2*u3) + (342:ℝ)*(u1*u2*u3) + (-62:ℝ)*(u1^2+u2^2+u3^2)
  + (-92:ℝ)*(u1^2*u2+u1^2*u3+u2^2*u1+u2^2*u3+u3^2*u1+u3^2*u2) + (29:ℝ)*(u1*u2*u3*(u1+u2+u3))
  + (-18:ℝ)*(u1^2*u2^2+u1^2*u3^2+u2^2*u3^2) + (-6:ℝ)*(u1*u2*u3*(u1*u2+u1*u3+u2*u3)) + (-1:ℝ)*(u1*u2*u3)^2

/-- `g(x) = (x − 3)² + 19`, whose roots are `3 ± i√19`. -/
def g (x : ℝ) : ℝ := (x - 3)^2 + 19

/-- The companion `R(v,w)` with `p = g(u₁)R(u₂,u₃) + g(u₂)R(u₁,u₃) + g(u₃)R(u₁,u₂)`. -/
noncomputable def R (v w : ℝ) : ℝ :=
  542/3 - 6*(v+w) - 13/3*(v^2+w^2) - 19*(v*w) - 4*(v^2*w + v*w^2) - 1/3*(v^2*w^2)

/-- `p` lies in the span of `g(u_j)·u_k^α·u_l^β` (`α, β ≤ 2`): it vanishes at the eight points `(3 ± i√19)³`. -/
theorem p_mem (u1 u2 u3 : ℝ) : p u1 u2 u3 = g u1 * R u2 u3 + g u2 * R u1 u3 + g u3 * R u1 u2 := by
  unfold p g R; ring

theorem p_zero : p 0 0 0 = 15176 := by unfold p; norm_num

/-- column 1: `a1*a2*b3^2` absorbed by `a2^2*b3^2`, `a1^2*b3^2` (weights [1, 1] / 2, shift (0, 0)). -/
theorem col1 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (827/100:ℝ) * (a1*a2*b3^2) ≤ (827/200:ℝ) * (a2^2*b3^2) + (827/200:ℝ) * (a1^2*b3^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm2 ((827/100:ℝ)*(1:ℝ)*(a2^2*b3^2)) ((827/100:ℝ)*(1:ℝ)*(a1^2*b3^2)) ((827/100:ℝ)*(a1*a2*b3^2)) 1 1 2 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by
      have e : ((827/100:ℝ)*(1:ℝ)*(a2^2*b3^2))^1 * ((827/100:ℝ)*(1:ℝ)*(a1^2*b3^2))^1
          = ((827/100:ℝ)*(a1*a2*b3^2))^2 * (((1:ℝ)^1*(1:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (1:ℝ)^1*(1:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((827/100:ℝ)*(a1*a2*b3^2))^2 := by positivity
      calc ((827/100:ℝ)*(a1*a2*b3^2))^2 = ((827/100:ℝ)*(a1*a2*b3^2))^2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 2: `a1*a2*a3*b3` absorbed by `a1*a3*b3`, `a1*a2^2*a3*b3` (weights [1, 1] / 2, shift (0, 0)). -/
theorem col2 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (73/50:ℝ) * (a1*a2*a3*b3) ≤ (657/500:ℝ) * (a1*a3*b3) + (511/1250:ℝ) * (a1*a2^2*a3*b3) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm2 ((73/50:ℝ)*(9/5:ℝ)*(a1*a3*b3)) ((73/50:ℝ)*(14/25:ℝ)*(a1*a2^2*a3*b3)) ((73/50:ℝ)*(a1*a2*a3*b3)) 1 1 2 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by
      have e : ((73/50:ℝ)*(9/5:ℝ)*(a1*a3*b3))^1 * ((73/50:ℝ)*(14/25:ℝ)*(a1*a2^2*a3*b3))^1
          = ((73/50:ℝ)*(a1*a2*a3*b3))^2 * (((9/5:ℝ)^1*(14/25:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (9/5:ℝ)^1*(14/25:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((73/50:ℝ)*(a1*a2*a3*b3))^2 := by positivity
      calc ((73/50:ℝ)*(a1*a2*a3*b3))^2 = ((73/50:ℝ)*(a1*a2*a3*b3))^2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 3: `a3*b1^2*b2` absorbed by `a3*b1^2`, `a3*b1^2*b2^2` (weights [1, 1] / 2, shift (0, 0)). -/
theorem col3 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (291/10:ℝ) * (a3*b1^2*b2) ≤ (7857/100:ℝ) * (a3*b1^2) + (5529/2000:ℝ) * (a3*b1^2*b2^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm2 ((291/10:ℝ)*(27/5:ℝ)*(a3*b1^2)) ((291/10:ℝ)*(19/100:ℝ)*(a3*b1^2*b2^2)) ((291/10:ℝ)*(a3*b1^2*b2)) 1 1 2 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by
      have e : ((291/10:ℝ)*(27/5:ℝ)*(a3*b1^2))^1 * ((291/10:ℝ)*(19/100:ℝ)*(a3*b1^2*b2^2))^1
          = ((291/10:ℝ)*(a3*b1^2*b2))^2 * (((27/5:ℝ)^1*(19/100:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (27/5:ℝ)^1*(19/100:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((291/10:ℝ)*(a3*b1^2*b2))^2 := by positivity
      calc ((291/10:ℝ)*(a3*b1^2*b2))^2 = ((291/10:ℝ)*(a3*b1^2*b2))^2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 4: `a3*b1*b2` absorbed by `a3*b1`, `a3^2*b1*b2^2`, `a1*a2*b1*b2` (weights [2, 2, 1] / 5, shift (1/5, 0)). -/
theorem col4 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (209/25:ℝ) * (a3*b1*b2) ≤ (6688/625:ℝ) * (a3*b1) + (209/625:ℝ) * (a3^2*b1*b2^2) + (20691/1250:ℝ) * (a1*a2*b1*b2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^1 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm3 ((209/25:ℝ)*(16/5:ℝ)*(a3*b1)) ((209/25:ℝ)*(1/10:ℝ)*(a3^2*b1*b2^2)) ((209/25:ℝ)*(99/10:ℝ)*(a1*a2*b1*b2)) ((209/25:ℝ)*(a3*b1*b2)) 2 2 1 5 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((209/25:ℝ)*(16/5:ℝ)*(a3*b1))^2 * ((209/25:ℝ)*(1/10:ℝ)*(a3^2*b1*b2^2))^2 * ((209/25:ℝ)*(99/10:ℝ)*(a1*a2*b1*b2))^1
          = ((209/25:ℝ)*(a3*b1*b2))^5 * (((16/5:ℝ)^2*(1/10:ℝ)^2*(99/10:ℝ)^1) * ((a1*a2*a3)^1 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^2*(1/10:ℝ)^2*(99/10:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((209/25:ℝ)*(a3*b1*b2))^5 := by positivity
      calc ((209/25:ℝ)*(a3*b1*b2))^5 = ((209/25:ℝ)*(a3*b1*b2))^5 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 5: `a2*a3*b1*b3` absorbed by `a3*b1*b3`, `a2^2*a3*b1*b3` (weights [1, 1] / 2, shift (0, 0)). -/
theorem col5 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (178/25:ℝ) * (a2*a3*b1*b3) ≤ (1424/125:ℝ) * (a3*b1*b3) + (712/625:ℝ) * (a2^2*a3*b1*b3) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm2 ((178/25:ℝ)*(16/5:ℝ)*(a3*b1*b3)) ((178/25:ℝ)*(8/25:ℝ)*(a2^2*a3*b1*b3)) ((178/25:ℝ)*(a2*a3*b1*b3)) 1 1 2 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by
      have e : ((178/25:ℝ)*(16/5:ℝ)*(a3*b1*b3))^1 * ((178/25:ℝ)*(8/25:ℝ)*(a2^2*a3*b1*b3))^1
          = ((178/25:ℝ)*(a2*a3*b1*b3))^2 * (((16/5:ℝ)^1*(8/25:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^1*(8/25:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((178/25:ℝ)*(a2*a3*b1*b3))^2 := by positivity
      calc ((178/25:ℝ)*(a2*a3*b1*b3))^2 = ((178/25:ℝ)*(a2*a3*b1*b3))^2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 6: `a1*a2*a3*b3` absorbed by `a3*b3`, `a1*a2^2*a3*b3`, `a1^2*a2*a3*b3` (weights [1, 1, 1] / 3, shift (0, 0)). -/
theorem col6 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (138/5:ℝ) * (a1*a2*a3*b3) ≤ (713/25:ℝ) * (a3*b3) + (1311/250:ℝ) * (a1*a2^2*a3*b3) + (1311/250:ℝ) * (a1^2*a2*a3*b3) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm3 ((138/5:ℝ)*(31/10:ℝ)*(a3*b3)) ((138/5:ℝ)*(57/100:ℝ)*(a1*a2^2*a3*b3)) ((138/5:ℝ)*(57/100:ℝ)*(a1^2*a2*a3*b3)) ((138/5:ℝ)*(a1*a2*a3*b3)) 1 1 1 3 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((138/5:ℝ)*(31/10:ℝ)*(a3*b3))^1 * ((138/5:ℝ)*(57/100:ℝ)*(a1*a2^2*a3*b3))^1 * ((138/5:ℝ)*(57/100:ℝ)*(a1^2*a2*a3*b3))^1
          = ((138/5:ℝ)*(a1*a2*a3*b3))^3 * (((31/10:ℝ)^1*(57/100:ℝ)^1*(57/100:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (31/10:ℝ)^1*(57/100:ℝ)^1*(57/100:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((138/5:ℝ)*(a1*a2*a3*b3))^3 := by positivity
      calc ((138/5:ℝ)*(a1*a2*a3*b3))^3 = ((138/5:ℝ)*(a1*a2*a3*b3))^3 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 7: `a1*a3*b2^2` absorbed by `a1*b2^2`, `a1*a3^2*b2^2` (weights [1, 1] / 2, shift (0, 0)). -/
theorem col7 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (156/25:ℝ) * (a1*a3*b2^2) ≤ (507/125:ℝ) * (a1*b2^2) + (3003/1250:ℝ) * (a1*a3^2*b2^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm2 ((156/25:ℝ)*(13/10:ℝ)*(a1*b2^2)) ((156/25:ℝ)*(77/100:ℝ)*(a1*a3^2*b2^2)) ((156/25:ℝ)*(a1*a3*b2^2)) 1 1 2 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by
      have e : ((156/25:ℝ)*(13/10:ℝ)*(a1*b2^2))^1 * ((156/25:ℝ)*(77/100:ℝ)*(a1*a3^2*b2^2))^1
          = ((156/25:ℝ)*(a1*a3*b2^2))^2 * (((13/10:ℝ)^1*(77/100:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (13/10:ℝ)^1*(77/100:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((156/25:ℝ)*(a1*a3*b2^2))^2 := by positivity
      calc ((156/25:ℝ)*(a1*a3*b2^2))^2 = ((156/25:ℝ)*(a1*a3*b2^2))^2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 8: `a1*a3*b2` absorbed by `a3*b2^2*b3`, `a1*a3*b1`, `a1^2*a3*b2^2` (weights [1, 1, 1] / 3, shift (0, 1/3)). -/
theorem col8 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (67/5:ℝ) * (a1*a3*b2) ≤ (201/25:ℝ) * (a3*b2^2*b3) + (1876/75:ℝ) * (a1*a3*b1) + (67/150:ℝ) * (a1^2*a3*b2^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^1 := one_le_pow₀ hB
  have h := amgm3 ((67/5:ℝ)*(9/5:ℝ)*(a3*b2^2*b3)) ((67/5:ℝ)*(28/5:ℝ)*(a1*a3*b1)) ((67/5:ℝ)*(1/10:ℝ)*(a1^2*a3*b2^2)) ((67/5:ℝ)*(a1*a3*b2)) 1 1 1 3 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((67/5:ℝ)*(9/5:ℝ)*(a3*b2^2*b3))^1 * ((67/5:ℝ)*(28/5:ℝ)*(a1*a3*b1))^1 * ((67/5:ℝ)*(1/10:ℝ)*(a1^2*a3*b2^2))^1
          = ((67/5:ℝ)*(a1*a3*b2))^3 * (((9/5:ℝ)^1*(28/5:ℝ)^1*(1/10:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^1)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (9/5:ℝ)^1*(28/5:ℝ)^1*(1/10:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((67/5:ℝ)*(a1*a3*b2))^3 := by positivity
      calc ((67/5:ℝ)*(a1*a3*b2))^3 = ((67/5:ℝ)*(a1*a3*b2))^3 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 9: `a1*a3*b2` absorbed by `a3*b2`, `a1*a3^2*b1`, `a1*b1*b2`, `a1^2*a3*b2^2`, `a1^2*a3*b2^2*b3` (weights [3, 1, 1, 1, 2] / 8, shift (0, 1/4)). -/
theorem col9 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (41/2:ℝ) * (a1*a3*b2) ≤ (123/5:ℝ) * (a3*b2) + (369/80:ℝ) * (a1*a3^2*b1) + (451/32:ℝ) * (a1*b1*b2) + (41/160:ℝ) * (a1^2*a3*b2^2) + (369/400:ℝ) * (a1^2*a3*b2^2*b3) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^2 := one_le_pow₀ hB
  have h := amgm5 ((41/2:ℝ)*(16/5:ℝ)*(a3*b2)) ((41/2:ℝ)*(9/5:ℝ)*(a1*a3^2*b1)) ((41/2:ℝ)*(11/2:ℝ)*(a1*b1*b2)) ((41/2:ℝ)*(1/10:ℝ)*(a1^2*a3*b2^2)) ((41/2:ℝ)*(9/50:ℝ)*(a1^2*a3*b2^2*b3)) ((41/2:ℝ)*(a1*a3*b2)) 3 1 1 1 2 8 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((41/2:ℝ)*(16/5:ℝ)*(a3*b2))^3 * ((41/2:ℝ)*(9/5:ℝ)*(a1*a3^2*b1))^1 * ((41/2:ℝ)*(11/2:ℝ)*(a1*b1*b2))^1 * ((41/2:ℝ)*(1/10:ℝ)*(a1^2*a3*b2^2))^1 * ((41/2:ℝ)*(9/50:ℝ)*(a1^2*a3*b2^2*b3))^2
          = ((41/2:ℝ)*(a1*a3*b2))^8 * (((16/5:ℝ)^3*(9/5:ℝ)^1*(11/2:ℝ)^1*(1/10:ℝ)^1*(9/50:ℝ)^2) * ((a1*a2*a3)^0 * (b1*b2*b3)^2)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^3*(9/5:ℝ)^1*(11/2:ℝ)^1*(1/10:ℝ)^1*(9/50:ℝ)^2 := by norm_num
      have h0 : 0 ≤ ((41/2:ℝ)*(a1*a3*b2))^8 := by positivity
      calc ((41/2:ℝ)*(a1*a3*b2))^8 = ((41/2:ℝ)*(a1*a3*b2))^8 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 10: `a1*a2*b3` absorbed by `a2*b3`, `a1*a2*b1`, `a1^2*a2*b3^2`, `a1^2*a2*b2` (weights [4, 1, 3, 1] / 9, shift (0, 1/9)). -/
theorem col10 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (312/5:ℝ) * (a1*a2*b3) ≤ (6656/75:ℝ) * (a2*b3) + (2912/75:ℝ) * (a1*a2*b1) + (52/25:ℝ) * (a1^2*a2*b3^2) + (312/25:ℝ) * (a1^2*a2*b2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^1 := one_le_pow₀ hB
  have h := amgm4 ((312/5:ℝ)*(16/5:ℝ)*(a2*b3)) ((312/5:ℝ)*(28/5:ℝ)*(a1*a2*b1)) ((312/5:ℝ)*(1/10:ℝ)*(a1^2*a2*b3^2)) ((312/5:ℝ)*(9/5:ℝ)*(a1^2*a2*b2)) ((312/5:ℝ)*(a1*a2*b3)) 4 1 3 1 9 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((312/5:ℝ)*(16/5:ℝ)*(a2*b3))^4 * ((312/5:ℝ)*(28/5:ℝ)*(a1*a2*b1))^1 * ((312/5:ℝ)*(1/10:ℝ)*(a1^2*a2*b3^2))^3 * ((312/5:ℝ)*(9/5:ℝ)*(a1^2*a2*b2))^1
          = ((312/5:ℝ)*(a1*a2*b3))^9 * (((16/5:ℝ)^4*(28/5:ℝ)^1*(1/10:ℝ)^3*(9/5:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^1)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^4*(28/5:ℝ)^1*(1/10:ℝ)^3*(9/5:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((312/5:ℝ)*(a1*a2*b3))^9 := by positivity
      calc ((312/5:ℝ)*(a1*a2*b3))^9 = ((312/5:ℝ)*(a1*a2*b3))^9 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 11: `a3*b1*b2` absorbed by `a3*b2`, `a3*b1`, `a2*b1*b2`, `a1*a3*b1`, `a3^2*b1^2*b2^2` (weights [2, 1, 1, 1, 2] / 7, shift (1/7, 0)). -/
theorem col11 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (351/10:ℝ) * (a3*b1*b2) ≤ (5616/175:ℝ) * (a3*b2) + (10881/700:ℝ) * (a3*b1) + (702/25:ℝ) * (a2*b1*b2) + (702/25:ℝ) * (a1*a3*b1) + (1404/4375:ℝ) * (a3^2*b1^2*b2^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^1 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm5 ((351/10:ℝ)*(16/5:ℝ)*(a3*b2)) ((351/10:ℝ)*(31/10:ℝ)*(a3*b1)) ((351/10:ℝ)*(28/5:ℝ)*(a2*b1*b2)) ((351/10:ℝ)*(28/5:ℝ)*(a1*a3*b1)) ((351/10:ℝ)*(4/125:ℝ)*(a3^2*b1^2*b2^2)) ((351/10:ℝ)*(a3*b1*b2)) 2 1 1 1 2 7 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((351/10:ℝ)*(16/5:ℝ)*(a3*b2))^2 * ((351/10:ℝ)*(31/10:ℝ)*(a3*b1))^1 * ((351/10:ℝ)*(28/5:ℝ)*(a2*b1*b2))^1 * ((351/10:ℝ)*(28/5:ℝ)*(a1*a3*b1))^1 * ((351/10:ℝ)*(4/125:ℝ)*(a3^2*b1^2*b2^2))^2
          = ((351/10:ℝ)*(a3*b1*b2))^7 * (((16/5:ℝ)^2*(31/10:ℝ)^1*(28/5:ℝ)^1*(28/5:ℝ)^1*(4/125:ℝ)^2) * ((a1*a2*a3)^1 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^2*(31/10:ℝ)^1*(28/5:ℝ)^1*(28/5:ℝ)^1*(4/125:ℝ)^2 := by norm_num
      have h0 : 0 ≤ ((351/10:ℝ)*(a3*b1*b2))^7 := by positivity
      calc ((351/10:ℝ)*(a3*b1*b2))^7 = ((351/10:ℝ)*(a3*b1*b2))^7 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 12: `a2*b1*b3` absorbed by `a2*b1`, `a2^2*a3*b1*b3`, `a1*a2*b1*b3^2` (weights [1, 1, 1] / 3, shift (1/3, 0)). -/
theorem col12 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (201/10:ℝ) * (a2*b1*b3) ≤ (536/25:ℝ) * (a2*b1) + (469/125:ℝ) * (a2^2*a3*b1*b3) + (3819/1000:ℝ) * (a1*a2*b1*b3^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^1 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm3 ((201/10:ℝ)*(16/5:ℝ)*(a2*b1)) ((201/10:ℝ)*(14/25:ℝ)*(a2^2*a3*b1*b3)) ((201/10:ℝ)*(57/100:ℝ)*(a1*a2*b1*b3^2)) ((201/10:ℝ)*(a2*b1*b3)) 1 1 1 3 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((201/10:ℝ)*(16/5:ℝ)*(a2*b1))^1 * ((201/10:ℝ)*(14/25:ℝ)*(a2^2*a3*b1*b3))^1 * ((201/10:ℝ)*(57/100:ℝ)*(a1*a2*b1*b3^2))^1
          = ((201/10:ℝ)*(a2*b1*b3))^3 * (((16/5:ℝ)^1*(14/25:ℝ)^1*(57/100:ℝ)^1) * ((a1*a2*a3)^1 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^1*(14/25:ℝ)^1*(57/100:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((201/10:ℝ)*(a2*b1*b3))^3 := by positivity
      calc ((201/10:ℝ)*(a2*b1*b3))^3 = ((201/10:ℝ)*(a2*b1*b3))^3 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 13: `a2*a3*b1*b2` absorbed by `a2*a3^2*b2`, `a2*b1*b2`, `a2*a3*b1^2*b2` (weights [1, 1, 1] / 3, shift (0, 0)). -/
theorem col13 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (22:ℝ) * (a2*a3*b1*b2) ≤ (121/15:ℝ) * (a2*a3^2*b2) + (341/15:ℝ) * (a2*b1*b2) + (176/75:ℝ) * (a2*a3*b1^2*b2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^0 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm3 ((22:ℝ)*(11/10:ℝ)*(a2*a3^2*b2)) ((22:ℝ)*(31/10:ℝ)*(a2*b1*b2)) ((22:ℝ)*(8/25:ℝ)*(a2*a3*b1^2*b2)) ((22:ℝ)*(a2*a3*b1*b2)) 1 1 1 3 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((22:ℝ)*(11/10:ℝ)*(a2*a3^2*b2))^1 * ((22:ℝ)*(31/10:ℝ)*(a2*b1*b2))^1 * ((22:ℝ)*(8/25:ℝ)*(a2*a3*b1^2*b2))^1
          = ((22:ℝ)*(a2*a3*b1*b2))^3 * (((11/10:ℝ)^1*(31/10:ℝ)^1*(8/25:ℝ)^1) * ((a1*a2*a3)^0 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (11/10:ℝ)^1*(31/10:ℝ)^1*(8/25:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((22:ℝ)*(a2*a3*b1*b2))^3 := by positivity
      calc ((22:ℝ)*(a2*a3*b1*b2))^3 = ((22:ℝ)*(a2*a3*b1*b2))^3 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- column 14: `a1*b2*b3` absorbed by `a1*b3`, `a1*b2`, `a1*a2*a3*b2*b3`, `a1^2*b2^2*b3^2` (weights [1, 1, 1, 1] / 4, shift (1/4, 0)). -/
theorem col14 (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    (58/5:ℝ) * (a1*b2*b3) ≤ (232/25:ℝ) * (a1*b3) + (232/25:ℝ) * (a1*b2) + (899/100:ℝ) * (a1*a2*a3*b2*b3) + (58/625:ℝ) * (a1^2*b2^2*b3^2) := by
  have hA' : (1:ℝ) ≤ (a1*a2*a3)^1 := one_le_pow₀ hA
  have hB' : (1:ℝ) ≤ (b1*b2*b3)^0 := one_le_pow₀ hB
  have h := amgm4 ((58/5:ℝ)*(16/5:ℝ)*(a1*b3)) ((58/5:ℝ)*(16/5:ℝ)*(a1*b2)) ((58/5:ℝ)*(31/10:ℝ)*(a1*a2*a3*b2*b3)) ((58/5:ℝ)*(4/125:ℝ)*(a1^2*b2^2*b3^2)) ((58/5:ℝ)*(a1*b2*b3)) 1 1 1 1 4 (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by
      have e : ((58/5:ℝ)*(16/5:ℝ)*(a1*b3))^1 * ((58/5:ℝ)*(16/5:ℝ)*(a1*b2))^1 * ((58/5:ℝ)*(31/10:ℝ)*(a1*a2*a3*b2*b3))^1 * ((58/5:ℝ)*(4/125:ℝ)*(a1^2*b2^2*b3^2))^1
          = ((58/5:ℝ)*(a1*b2*b3))^4 * (((16/5:ℝ)^1*(16/5:ℝ)^1*(31/10:ℝ)^1*(4/125:ℝ)^1) * ((a1*a2*a3)^1 * (b1*b2*b3)^0)) := by ring
      rw [e]
      have hG : (1:ℝ) ≤ (16/5:ℝ)^1*(16/5:ℝ)^1*(31/10:ℝ)^1*(4/125:ℝ)^1 := by norm_num
      have h0 : 0 ≤ ((58/5:ℝ)*(a1*b2*b3))^4 := by positivity
      calc ((58/5:ℝ)*(a1*b2*b3))^4 = ((58/5:ℝ)*(a1*b2*b3))^4 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
              (one_le_mul_of_one_le_of_one_le hG (one_le_mul_of_one_le_of_one_le hA' hB')) h0)
  push_cast at h
  linarith

/-- gap of column 1. -/
noncomputable def K1 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (827/200:ℝ) * (a2^2*b3^2) + (827/200:ℝ) * (a1^2*b3^2) - (827/100:ℝ) * (a1*a2*b3^2)
theorem K1_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K1 a1 a2 a3 b1 b2 b3 := by
  unfold K1; linarith [col1 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS1 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K1 a1 a2 a3 b1 b2 b3 + K1 b1 b2 b3 a1 a2 a3 + K1 a1 a3 a2 b1 b3 b2 + K1 b1 b3 b2 a1 a3 a2 + K1 a2 a1 a3 b2 b1 b3 + K1 b2 b1 b3 a2 a1 a3 + K1 a2 a3 a1 b2 b3 b1 + K1 b2 b3 b1 a2 a3 a1 + K1 a3 a1 a2 b3 b1 b2 + K1 b3 b1 b2 a3 a1 a2 + K1 a3 a2 a1 b3 b2 b1 + K1 b3 b2 b1 a3 a2 a1
theorem KS1_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS1 a1 a2 a3 b1 b2 b3 := by
  unfold KS1
  have h1 := K1_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K1_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K1_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K1_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K1_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K1_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K1_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K1_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K1_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K1_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K1_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K1_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 2. -/
noncomputable def K2 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (657/500:ℝ) * (a1*a3*b3) + (511/1250:ℝ) * (a1*a2^2*a3*b3) - (73/50:ℝ) * (a1*a2*a3*b3)
theorem K2_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K2 a1 a2 a3 b1 b2 b3 := by
  unfold K2; linarith [col2 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS2 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K2 a1 a2 a3 b1 b2 b3 + K2 b1 b2 b3 a1 a2 a3 + K2 a1 a3 a2 b1 b3 b2 + K2 b1 b3 b2 a1 a3 a2 + K2 a2 a1 a3 b2 b1 b3 + K2 b2 b1 b3 a2 a1 a3 + K2 a2 a3 a1 b2 b3 b1 + K2 b2 b3 b1 a2 a3 a1 + K2 a3 a1 a2 b3 b1 b2 + K2 b3 b1 b2 a3 a1 a2 + K2 a3 a2 a1 b3 b2 b1 + K2 b3 b2 b1 a3 a2 a1
theorem KS2_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS2 a1 a2 a3 b1 b2 b3 := by
  unfold KS2
  have h1 := K2_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K2_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K2_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K2_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K2_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K2_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K2_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K2_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K2_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K2_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K2_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K2_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 3. -/
noncomputable def K3 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (7857/100:ℝ) * (a3*b1^2) + (5529/2000:ℝ) * (a3*b1^2*b2^2) - (291/10:ℝ) * (a3*b1^2*b2)
theorem K3_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K3 a1 a2 a3 b1 b2 b3 := by
  unfold K3; linarith [col3 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS3 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K3 a1 a2 a3 b1 b2 b3 + K3 b1 b2 b3 a1 a2 a3 + K3 a1 a3 a2 b1 b3 b2 + K3 b1 b3 b2 a1 a3 a2 + K3 a2 a1 a3 b2 b1 b3 + K3 b2 b1 b3 a2 a1 a3 + K3 a2 a3 a1 b2 b3 b1 + K3 b2 b3 b1 a2 a3 a1 + K3 a3 a1 a2 b3 b1 b2 + K3 b3 b1 b2 a3 a1 a2 + K3 a3 a2 a1 b3 b2 b1 + K3 b3 b2 b1 a3 a2 a1
theorem KS3_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS3 a1 a2 a3 b1 b2 b3 := by
  unfold KS3
  have h1 := K3_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K3_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K3_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K3_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K3_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K3_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K3_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K3_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K3_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K3_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K3_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K3_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 4. -/
noncomputable def K4 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (6688/625:ℝ) * (a3*b1) + (209/625:ℝ) * (a3^2*b1*b2^2) + (20691/1250:ℝ) * (a1*a2*b1*b2) - (209/25:ℝ) * (a3*b1*b2)
theorem K4_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K4 a1 a2 a3 b1 b2 b3 := by
  unfold K4; linarith [col4 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS4 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K4 a1 a2 a3 b1 b2 b3 + K4 b1 b2 b3 a1 a2 a3 + K4 a1 a3 a2 b1 b3 b2 + K4 b1 b3 b2 a1 a3 a2 + K4 a2 a1 a3 b2 b1 b3 + K4 b2 b1 b3 a2 a1 a3 + K4 a2 a3 a1 b2 b3 b1 + K4 b2 b3 b1 a2 a3 a1 + K4 a3 a1 a2 b3 b1 b2 + K4 b3 b1 b2 a3 a1 a2 + K4 a3 a2 a1 b3 b2 b1 + K4 b3 b2 b1 a3 a2 a1
theorem KS4_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS4 a1 a2 a3 b1 b2 b3 := by
  unfold KS4
  have h1 := K4_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K4_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K4_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K4_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K4_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K4_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K4_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K4_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K4_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K4_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K4_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K4_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 5. -/
noncomputable def K5 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (1424/125:ℝ) * (a3*b1*b3) + (712/625:ℝ) * (a2^2*a3*b1*b3) - (178/25:ℝ) * (a2*a3*b1*b3)
theorem K5_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K5 a1 a2 a3 b1 b2 b3 := by
  unfold K5; linarith [col5 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS5 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K5 a1 a2 a3 b1 b2 b3 + K5 b1 b2 b3 a1 a2 a3 + K5 a1 a3 a2 b1 b3 b2 + K5 b1 b3 b2 a1 a3 a2 + K5 a2 a1 a3 b2 b1 b3 + K5 b2 b1 b3 a2 a1 a3 + K5 a2 a3 a1 b2 b3 b1 + K5 b2 b3 b1 a2 a3 a1 + K5 a3 a1 a2 b3 b1 b2 + K5 b3 b1 b2 a3 a1 a2 + K5 a3 a2 a1 b3 b2 b1 + K5 b3 b2 b1 a3 a2 a1
theorem KS5_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS5 a1 a2 a3 b1 b2 b3 := by
  unfold KS5
  have h1 := K5_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K5_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K5_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K5_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K5_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K5_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K5_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K5_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K5_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K5_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K5_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K5_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 6. -/
noncomputable def K6 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (713/25:ℝ) * (a3*b3) + (1311/250:ℝ) * (a1*a2^2*a3*b3) + (1311/250:ℝ) * (a1^2*a2*a3*b3) - (138/5:ℝ) * (a1*a2*a3*b3)
theorem K6_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K6 a1 a2 a3 b1 b2 b3 := by
  unfold K6; linarith [col6 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS6 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K6 a1 a2 a3 b1 b2 b3 + K6 b1 b2 b3 a1 a2 a3 + K6 a1 a3 a2 b1 b3 b2 + K6 b1 b3 b2 a1 a3 a2 + K6 a2 a1 a3 b2 b1 b3 + K6 b2 b1 b3 a2 a1 a3 + K6 a2 a3 a1 b2 b3 b1 + K6 b2 b3 b1 a2 a3 a1 + K6 a3 a1 a2 b3 b1 b2 + K6 b3 b1 b2 a3 a1 a2 + K6 a3 a2 a1 b3 b2 b1 + K6 b3 b2 b1 a3 a2 a1
theorem KS6_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS6 a1 a2 a3 b1 b2 b3 := by
  unfold KS6
  have h1 := K6_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K6_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K6_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K6_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K6_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K6_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K6_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K6_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K6_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K6_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K6_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K6_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 7. -/
noncomputable def K7 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (507/125:ℝ) * (a1*b2^2) + (3003/1250:ℝ) * (a1*a3^2*b2^2) - (156/25:ℝ) * (a1*a3*b2^2)
theorem K7_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K7 a1 a2 a3 b1 b2 b3 := by
  unfold K7; linarith [col7 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS7 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K7 a1 a2 a3 b1 b2 b3 + K7 b1 b2 b3 a1 a2 a3 + K7 a1 a3 a2 b1 b3 b2 + K7 b1 b3 b2 a1 a3 a2 + K7 a2 a1 a3 b2 b1 b3 + K7 b2 b1 b3 a2 a1 a3 + K7 a2 a3 a1 b2 b3 b1 + K7 b2 b3 b1 a2 a3 a1 + K7 a3 a1 a2 b3 b1 b2 + K7 b3 b1 b2 a3 a1 a2 + K7 a3 a2 a1 b3 b2 b1 + K7 b3 b2 b1 a3 a2 a1
theorem KS7_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS7 a1 a2 a3 b1 b2 b3 := by
  unfold KS7
  have h1 := K7_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K7_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K7_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K7_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K7_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K7_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K7_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K7_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K7_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K7_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K7_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K7_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 8. -/
noncomputable def K8 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (201/25:ℝ) * (a3*b2^2*b3) + (1876/75:ℝ) * (a1*a3*b1) + (67/150:ℝ) * (a1^2*a3*b2^2) - (67/5:ℝ) * (a1*a3*b2)
theorem K8_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K8 a1 a2 a3 b1 b2 b3 := by
  unfold K8; linarith [col8 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS8 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K8 a1 a2 a3 b1 b2 b3 + K8 b1 b2 b3 a1 a2 a3 + K8 a1 a3 a2 b1 b3 b2 + K8 b1 b3 b2 a1 a3 a2 + K8 a2 a1 a3 b2 b1 b3 + K8 b2 b1 b3 a2 a1 a3 + K8 a2 a3 a1 b2 b3 b1 + K8 b2 b3 b1 a2 a3 a1 + K8 a3 a1 a2 b3 b1 b2 + K8 b3 b1 b2 a3 a1 a2 + K8 a3 a2 a1 b3 b2 b1 + K8 b3 b2 b1 a3 a2 a1
theorem KS8_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS8 a1 a2 a3 b1 b2 b3 := by
  unfold KS8
  have h1 := K8_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K8_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K8_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K8_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K8_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K8_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K8_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K8_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K8_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K8_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K8_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K8_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 9. -/
noncomputable def K9 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (123/5:ℝ) * (a3*b2) + (369/80:ℝ) * (a1*a3^2*b1) + (451/32:ℝ) * (a1*b1*b2) + (41/160:ℝ) * (a1^2*a3*b2^2) + (369/400:ℝ) * (a1^2*a3*b2^2*b3) - (41/2:ℝ) * (a1*a3*b2)
theorem K9_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K9 a1 a2 a3 b1 b2 b3 := by
  unfold K9; linarith [col9 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS9 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K9 a1 a2 a3 b1 b2 b3 + K9 b1 b2 b3 a1 a2 a3 + K9 a1 a3 a2 b1 b3 b2 + K9 b1 b3 b2 a1 a3 a2 + K9 a2 a1 a3 b2 b1 b3 + K9 b2 b1 b3 a2 a1 a3 + K9 a2 a3 a1 b2 b3 b1 + K9 b2 b3 b1 a2 a3 a1 + K9 a3 a1 a2 b3 b1 b2 + K9 b3 b1 b2 a3 a1 a2 + K9 a3 a2 a1 b3 b2 b1 + K9 b3 b2 b1 a3 a2 a1
theorem KS9_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS9 a1 a2 a3 b1 b2 b3 := by
  unfold KS9
  have h1 := K9_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K9_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K9_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K9_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K9_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K9_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K9_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K9_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K9_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K9_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K9_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K9_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 10. -/
noncomputable def K10 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (6656/75:ℝ) * (a2*b3) + (2912/75:ℝ) * (a1*a2*b1) + (52/25:ℝ) * (a1^2*a2*b3^2) + (312/25:ℝ) * (a1^2*a2*b2) - (312/5:ℝ) * (a1*a2*b3)
theorem K10_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K10 a1 a2 a3 b1 b2 b3 := by
  unfold K10; linarith [col10 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS10 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K10 a1 a2 a3 b1 b2 b3 + K10 b1 b2 b3 a1 a2 a3 + K10 a1 a3 a2 b1 b3 b2 + K10 b1 b3 b2 a1 a3 a2 + K10 a2 a1 a3 b2 b1 b3 + K10 b2 b1 b3 a2 a1 a3 + K10 a2 a3 a1 b2 b3 b1 + K10 b2 b3 b1 a2 a3 a1 + K10 a3 a1 a2 b3 b1 b2 + K10 b3 b1 b2 a3 a1 a2 + K10 a3 a2 a1 b3 b2 b1 + K10 b3 b2 b1 a3 a2 a1
theorem KS10_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS10 a1 a2 a3 b1 b2 b3 := by
  unfold KS10
  have h1 := K10_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K10_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K10_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K10_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K10_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K10_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K10_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K10_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K10_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K10_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K10_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K10_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 11. -/
noncomputable def K11 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (5616/175:ℝ) * (a3*b2) + (10881/700:ℝ) * (a3*b1) + (702/25:ℝ) * (a2*b1*b2) + (702/25:ℝ) * (a1*a3*b1) + (1404/4375:ℝ) * (a3^2*b1^2*b2^2) - (351/10:ℝ) * (a3*b1*b2)
theorem K11_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K11 a1 a2 a3 b1 b2 b3 := by
  unfold K11; linarith [col11 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS11 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K11 a1 a2 a3 b1 b2 b3 + K11 b1 b2 b3 a1 a2 a3 + K11 a1 a3 a2 b1 b3 b2 + K11 b1 b3 b2 a1 a3 a2 + K11 a2 a1 a3 b2 b1 b3 + K11 b2 b1 b3 a2 a1 a3 + K11 a2 a3 a1 b2 b3 b1 + K11 b2 b3 b1 a2 a3 a1 + K11 a3 a1 a2 b3 b1 b2 + K11 b3 b1 b2 a3 a1 a2 + K11 a3 a2 a1 b3 b2 b1 + K11 b3 b2 b1 a3 a2 a1
theorem KS11_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS11 a1 a2 a3 b1 b2 b3 := by
  unfold KS11
  have h1 := K11_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K11_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K11_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K11_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K11_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K11_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K11_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K11_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K11_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K11_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K11_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K11_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 12. -/
noncomputable def K12 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (536/25:ℝ) * (a2*b1) + (469/125:ℝ) * (a2^2*a3*b1*b3) + (3819/1000:ℝ) * (a1*a2*b1*b3^2) - (201/10:ℝ) * (a2*b1*b3)
theorem K12_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K12 a1 a2 a3 b1 b2 b3 := by
  unfold K12; linarith [col12 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS12 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K12 a1 a2 a3 b1 b2 b3 + K12 b1 b2 b3 a1 a2 a3 + K12 a1 a3 a2 b1 b3 b2 + K12 b1 b3 b2 a1 a3 a2 + K12 a2 a1 a3 b2 b1 b3 + K12 b2 b1 b3 a2 a1 a3 + K12 a2 a3 a1 b2 b3 b1 + K12 b2 b3 b1 a2 a3 a1 + K12 a3 a1 a2 b3 b1 b2 + K12 b3 b1 b2 a3 a1 a2 + K12 a3 a2 a1 b3 b2 b1 + K12 b3 b2 b1 a3 a2 a1
theorem KS12_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS12 a1 a2 a3 b1 b2 b3 := by
  unfold KS12
  have h1 := K12_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K12_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K12_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K12_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K12_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K12_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K12_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K12_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K12_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K12_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K12_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K12_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 13. -/
noncomputable def K13 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (121/15:ℝ) * (a2*a3^2*b2) + (341/15:ℝ) * (a2*b1*b2) + (176/75:ℝ) * (a2*a3*b1^2*b2) - (22:ℝ) * (a2*a3*b1*b2)
theorem K13_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K13 a1 a2 a3 b1 b2 b3 := by
  unfold K13; linarith [col13 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS13 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K13 a1 a2 a3 b1 b2 b3 + K13 b1 b2 b3 a1 a2 a3 + K13 a1 a3 a2 b1 b3 b2 + K13 b1 b3 b2 a1 a3 a2 + K13 a2 a1 a3 b2 b1 b3 + K13 b2 b1 b3 a2 a1 a3 + K13 a2 a3 a1 b2 b3 b1 + K13 b2 b3 b1 a2 a3 a1 + K13 a3 a1 a2 b3 b1 b2 + K13 b3 b1 b2 a3 a1 a2 + K13 a3 a2 a1 b3 b2 b1 + K13 b3 b2 b1 a3 a2 a1
theorem KS13_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS13 a1 a2 a3 b1 b2 b3 := by
  unfold KS13
  have h1 := K13_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K13_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K13_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K13_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K13_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K13_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K13_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K13_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K13_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K13_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K13_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K13_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

/-- gap of column 14. -/
noncomputable def K14 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ := (232/25:ℝ) * (a1*b3) + (232/25:ℝ) * (a1*b2) + (899/100:ℝ) * (a1*a2*a3*b2*b3) + (58/625:ℝ) * (a1^2*b2^2*b3^2) - (58/5:ℝ) * (a1*b2*b3)
theorem K14_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ K14 a1 a2 a3 b1 b2 b3 := by
  unfold K14; linarith [col14 a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB]
noncomputable def KS14 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  K14 a1 a2 a3 b1 b2 b3 + K14 b1 b2 b3 a1 a2 a3 + K14 a1 a3 a2 b1 b3 b2 + K14 b1 b3 b2 a1 a3 a2 + K14 a2 a1 a3 b2 b1 b3 + K14 b2 b1 b3 a2 a1 a3 + K14 a2 a3 a1 b2 b3 b1 + K14 b2 b3 b1 a2 a3 a1 + K14 a3 a1 a2 b3 b1 b2 + K14 b3 b1 b2 a3 a1 a2 + K14 a3 a2 a1 b3 b2 b1 + K14 b3 b2 b1 a3 a2 a1
theorem KS14_nonneg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 ≤ KS14 a1 a2 a3 b1 b2 b3 := by
  unfold KS14
  have h1 := K14_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 (by linarith [hA]) (by linarith [hB])
  have h2 := K14_nonneg b1 b2 b3 a1 a2 a3 hb1 hb2 hb3 ha1 ha2 ha3 (by linarith [hB]) (by linarith [hA])
  have h3 := K14_nonneg a1 a3 a2 b1 b3 b2 ha1 ha3 ha2 hb1 hb3 hb2 (by linarith [hA]) (by linarith [hB])
  have h4 := K14_nonneg b1 b3 b2 a1 a3 a2 hb1 hb3 hb2 ha1 ha3 ha2 (by linarith [hB]) (by linarith [hA])
  have h5 := K14_nonneg a2 a1 a3 b2 b1 b3 ha2 ha1 ha3 hb2 hb1 hb3 (by linarith [hA]) (by linarith [hB])
  have h6 := K14_nonneg b2 b1 b3 a2 a1 a3 hb2 hb1 hb3 ha2 ha1 ha3 (by linarith [hB]) (by linarith [hA])
  have h7 := K14_nonneg a2 a3 a1 b2 b3 b1 ha2 ha3 ha1 hb2 hb3 hb1 (by linarith [hA]) (by linarith [hB])
  have h8 := K14_nonneg b2 b3 b1 a2 a3 a1 hb2 hb3 hb1 ha2 ha3 ha1 (by linarith [hB]) (by linarith [hA])
  have h9 := K14_nonneg a3 a1 a2 b3 b1 b2 ha3 ha1 ha2 hb3 hb1 hb2 (by linarith [hA]) (by linarith [hB])
  have h10 := K14_nonneg b3 b1 b2 a3 a1 a2 hb3 hb1 hb2 ha3 ha1 ha2 (by linarith [hB]) (by linarith [hA])
  have h11 := K14_nonneg a3 a2 a1 b3 b2 b1 ha3 ha2 ha1 hb3 hb2 hb1 (by linarith [hA]) (by linarith [hB])
  have h12 := K14_nonneg b3 b2 b1 a3 a2 a1 hb3 hb2 hb1 ha3 ha2 ha1 (by linarith [hB]) (by linarith [hA])
  linarith

noncomputable def T_1 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (124:ℝ)*(a3*b3) + (460:ℝ)*(a3*b2) + (184:ℝ)*(a3*b2*b3) + (92:ℝ)*(a3*b2^2) + (36:ℝ)*(a3*b2^2*b3) + (460:ℝ)*(a3*b1) + (184:ℝ)*(a3*b1*b3) + (-342:ℝ)*(a3*b1*b2) + (-58:ℝ)*(a3*b1*b2*b3) + (-29:ℝ)*(a3*b1*b2^2) + (12:ℝ)*(a3*b1*b2^2*b3) + (92:ℝ)*(a3*b1^2) + (36:ℝ)*(a3*b1^2*b3) + (-29:ℝ)*(a3*b1^2*b2) + (12:ℝ)*(a3*b1^2*b2*b3) + (6:ℝ)*(a3*b1^2*b2^2)
noncomputable def T_2 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (2:ℝ)*(a3*b1^2*b2^2*b3) + (92:ℝ)*(a3^2*b2) + (18:ℝ)*(a3^2*b2^2) + (92:ℝ)*(a3^2*b1) + (-29:ℝ)*(a3^2*b1*b2) + (6:ℝ)*(a3^2*b1*b2^2) + (18:ℝ)*(a3^2*b1^2) + (6:ℝ)*(a3^2*b1^2*b2) + (1:ℝ)*(a3^2*b1^2*b2^2) + (460:ℝ)*(a2*b3) + (92:ℝ)*(a2*b3^2) + (124:ℝ)*(a2*b2) + (184:ℝ)*(a2*b2*b3) + (36:ℝ)*(a2*b2*b3^2) + (460:ℝ)*(a2*b1) + (-342:ℝ)*(a2*b1*b3)
noncomputable def T_3 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (-29:ℝ)*(a2*b1*b3^2) + (184:ℝ)*(a2*b1*b2) + (-58:ℝ)*(a2*b1*b2*b3) + (12:ℝ)*(a2*b1*b2*b3^2) + (92:ℝ)*(a2*b1^2) + (-29:ℝ)*(a2*b1^2*b3) + (6:ℝ)*(a2*b1^2*b3^2) + (36:ℝ)*(a2*b1^2*b2) + (12:ℝ)*(a2*b1^2*b2*b3) + (2:ℝ)*(a2*b1^2*b2*b3^2) + (184:ℝ)*(a2*a3*b3) + (184:ℝ)*(a2*a3*b2) + (72:ℝ)*(a2*a3*b2*b3) + (-342:ℝ)*(a2*a3*b1) + (-58:ℝ)*(a2*a3*b1*b3) + (-58:ℝ)*(a2*a3*b1*b2)
noncomputable def T_4 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (24:ℝ)*(a2*a3*b1*b2*b3) + (-29:ℝ)*(a2*a3*b1^2) + (12:ℝ)*(a2*a3*b1^2*b3) + (12:ℝ)*(a2*a3*b1^2*b2) + (4:ℝ)*(a2*a3*b1^2*b2*b3) + (36:ℝ)*(a2*a3^2*b2) + (-29:ℝ)*(a2*a3^2*b1) + (12:ℝ)*(a2*a3^2*b1*b2) + (6:ℝ)*(a2*a3^2*b1^2) + (2:ℝ)*(a2*a3^2*b1^2*b2) + (92:ℝ)*(a2^2*b3) + (18:ℝ)*(a2^2*b3^2) + (92:ℝ)*(a2^2*b1) + (-29:ℝ)*(a2^2*b1*b3) + (6:ℝ)*(a2^2*b1*b3^2) + (18:ℝ)*(a2^2*b1^2)
noncomputable def T_5 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (6:ℝ)*(a2^2*b1^2*b3) + (1:ℝ)*(a2^2*b1^2*b3^2) + (36:ℝ)*(a2^2*a3*b3) + (-29:ℝ)*(a2^2*a3*b1) + (12:ℝ)*(a2^2*a3*b1*b3) + (6:ℝ)*(a2^2*a3*b1^2) + (2:ℝ)*(a2^2*a3*b1^2*b3) + (6:ℝ)*(a2^2*a3^2*b1) + (1:ℝ)*(a2^2*a3^2*b1^2) + (460:ℝ)*(a1*b3) + (92:ℝ)*(a1*b3^2) + (460:ℝ)*(a1*b2) + (-342:ℝ)*(a1*b2*b3) + (-29:ℝ)*(a1*b2*b3^2) + (92:ℝ)*(a1*b2^2) + (-29:ℝ)*(a1*b2^2*b3)
noncomputable def T_6 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (6:ℝ)*(a1*b2^2*b3^2) + (124:ℝ)*(a1*b1) + (184:ℝ)*(a1*b1*b3) + (36:ℝ)*(a1*b1*b3^2) + (184:ℝ)*(a1*b1*b2) + (-58:ℝ)*(a1*b1*b2*b3) + (12:ℝ)*(a1*b1*b2*b3^2) + (36:ℝ)*(a1*b1*b2^2) + (12:ℝ)*(a1*b1*b2^2*b3) + (2:ℝ)*(a1*b1*b2^2*b3^2) + (184:ℝ)*(a1*a3*b3) + (-342:ℝ)*(a1*a3*b2) + (-58:ℝ)*(a1*a3*b2*b3) + (-29:ℝ)*(a1*a3*b2^2) + (12:ℝ)*(a1*a3*b2^2*b3) + (184:ℝ)*(a1*a3*b1)
noncomputable def T_7 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (72:ℝ)*(a1*a3*b1*b3) + (-58:ℝ)*(a1*a3*b1*b2) + (24:ℝ)*(a1*a3*b1*b2*b3) + (12:ℝ)*(a1*a3*b1*b2^2) + (4:ℝ)*(a1*a3*b1*b2^2*b3) + (-29:ℝ)*(a1*a3^2*b2) + (6:ℝ)*(a1*a3^2*b2^2) + (36:ℝ)*(a1*a3^2*b1) + (12:ℝ)*(a1*a3^2*b1*b2) + (2:ℝ)*(a1*a3^2*b1*b2^2) + (-342:ℝ)*(a1*a2*b3) + (-29:ℝ)*(a1*a2*b3^2) + (184:ℝ)*(a1*a2*b2) + (-58:ℝ)*(a1*a2*b2*b3) + (12:ℝ)*(a1*a2*b2*b3^2) + (184:ℝ)*(a1*a2*b1)
noncomputable def T_8 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (-58:ℝ)*(a1*a2*b1*b3) + (12:ℝ)*(a1*a2*b1*b3^2) + (72:ℝ)*(a1*a2*b1*b2) + (24:ℝ)*(a1*a2*b1*b2*b3) + (4:ℝ)*(a1*a2*b1*b2*b3^2) + (-58:ℝ)*(a1*a2*a3*b3) + (-58:ℝ)*(a1*a2*a3*b2) + (24:ℝ)*(a1*a2*a3*b2*b3) + (-58:ℝ)*(a1*a2*a3*b1) + (24:ℝ)*(a1*a2*a3*b1*b3) + (24:ℝ)*(a1*a2*a3*b1*b2) + (8:ℝ)*(a1*a2*a3*b1*b2*b3) + (12:ℝ)*(a1*a2*a3^2*b2) + (12:ℝ)*(a1*a2*a3^2*b1) + (4:ℝ)*(a1*a2*a3^2*b1*b2) + (-29:ℝ)*(a1*a2^2*b3)
noncomputable def T_9 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (6:ℝ)*(a1*a2^2*b3^2) + (36:ℝ)*(a1*a2^2*b1) + (12:ℝ)*(a1*a2^2*b1*b3) + (2:ℝ)*(a1*a2^2*b1*b3^2) + (12:ℝ)*(a1*a2^2*a3*b3) + (12:ℝ)*(a1*a2^2*a3*b1) + (4:ℝ)*(a1*a2^2*a3*b1*b3) + (2:ℝ)*(a1*a2^2*a3^2*b1) + (92:ℝ)*(a1^2*b3) + (18:ℝ)*(a1^2*b3^2) + (92:ℝ)*(a1^2*b2) + (-29:ℝ)*(a1^2*b2*b3) + (6:ℝ)*(a1^2*b2*b3^2) + (18:ℝ)*(a1^2*b2^2) + (6:ℝ)*(a1^2*b2^2*b3) + (1:ℝ)*(a1^2*b2^2*b3^2)
noncomputable def T_10 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (36:ℝ)*(a1^2*a3*b3) + (-29:ℝ)*(a1^2*a3*b2) + (12:ℝ)*(a1^2*a3*b2*b3) + (6:ℝ)*(a1^2*a3*b2^2) + (2:ℝ)*(a1^2*a3*b2^2*b3) + (6:ℝ)*(a1^2*a3^2*b2) + (1:ℝ)*(a1^2*a3^2*b2^2) + (-29:ℝ)*(a1^2*a2*b3) + (6:ℝ)*(a1^2*a2*b3^2) + (36:ℝ)*(a1^2*a2*b2) + (12:ℝ)*(a1^2*a2*b2*b3) + (2:ℝ)*(a1^2*a2*b2*b3^2) + (12:ℝ)*(a1^2*a2*a3*b3) + (12:ℝ)*(a1^2*a2*a3*b2) + (4:ℝ)*(a1^2*a2*a3*b2*b3) + (2:ℝ)*(a1^2*a2*a3^2*b2)
noncomputable def T_11 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (6:ℝ)*(a1^2*a2^2*b3) + (1:ℝ)*(a1^2*a2^2*b3^2) + (2:ℝ)*(a1^2*a2^2*a3*b3)
/-- `−Δp` expanded in mixed monomials (in chunks). -/
noncomputable def T (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  T_1 a1 a2 a3 b1 b2 b3 + T_2 a1 a2 a3 b1 b2 b3 + T_3 a1 a2 a3 b1 b2 b3 + T_4 a1 a2 a3 b1 b2 b3 + T_5 a1 a2 a3 b1 b2 b3 + T_6 a1 a2 a3 b1 b2 b3 + T_7 a1 a2 a3 b1 b2 b3 + T_8 a1 a2 a3 b1 b2 b3 + T_9 a1 a2 a3 b1 b2 b3 + T_10 a1 a2 a3 b1 b2 b3 + T_11 a1 a2 a3 b1 b2 b3
noncomputable def Slack_1 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (248/25:ℝ)*(a3*b3) + (961633/26250:ℝ)*(a3*b2) + (173603/12000:ℝ)*(a3*b2*b3) + (4687/500:ℝ)*(a3*b2^2) + (3361/1200:ℝ)*(a3*b2^2*b3) + (961633/26250:ℝ)*(a3*b1) + (173603/12000:ℝ)*(a3*b1*b3) + (23/25:ℝ)*(a3*b1*b2) + (3/25:ℝ)*(a3*b1*b2*b3) + (1/10:ℝ)*(a3*b1*b2^2) + (1379/1250:ℝ)*(a3*b1*b2^2*b3) + (4687/500:ℝ)*(a3*b1^2) + (3361/1200:ℝ)*(a3*b1^2*b3) + (1/10:ℝ)*(a3*b1^2*b2) + (1379/1250:ℝ)*(a3*b1^2*b2*b3) + (471/1000:ℝ)*(a3*b1^2*b2^2)
noncomputable def Slack_2 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (2:ℝ)*(a3*b1^2*b2^2*b3) + (4687/500:ℝ)*(a3^2*b2) + (73/50:ℝ)*(a3^2*b2^2) + (4687/500:ℝ)*(a3^2*b1) + (1/50:ℝ)*(a3^2*b1*b2) + (28817/60000:ℝ)*(a3^2*b1*b2^2) + (73/50:ℝ)*(a3^2*b1^2) + (28817/60000:ℝ)*(a3^2*b1^2*b2) + (151/875:ℝ)*(a3^2*b1^2*b2^2) + (961633/26250:ℝ)*(a2*b3) + (4687/500:ℝ)*(a2*b3^2) + (248/25:ℝ)*(a2*b2) + (173603/12000:ℝ)*(a2*b2*b3) + (3361/1200:ℝ)*(a2*b2*b3^2) + (961633/26250:ℝ)*(a2*b1) + (23/25:ℝ)*(a2*b1*b3)
noncomputable def Slack_3 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (1/10:ℝ)*(a2*b1*b3^2) + (173603/12000:ℝ)*(a2*b1*b2) + (3/25:ℝ)*(a2*b1*b2*b3) + (1379/1250:ℝ)*(a2*b1*b2*b3^2) + (4687/500:ℝ)*(a2*b1^2) + (1/10:ℝ)*(a2*b1^2*b3) + (471/1000:ℝ)*(a2*b1^2*b3^2) + (3361/1200:ℝ)*(a2*b1^2*b2) + (1379/1250:ℝ)*(a2*b1^2*b2*b3) + (2:ℝ)*(a2*b1^2*b2*b3^2) + (173603/12000:ℝ)*(a2*a3*b3) + (173603/12000:ℝ)*(a2*a3*b2) + (3618/625:ℝ)*(a2*a3*b2*b3) + (23/25:ℝ)*(a2*a3*b1) + (6/25:ℝ)*(a2*a3*b1*b3) + (6/25:ℝ)*(a2*a3*b1*b2)
noncomputable def Slack_4 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (301/50:ℝ)*(a2*a3*b1*b2*b3) + (1/50:ℝ)*(a2*a3*b1^2) + (14147/15000:ℝ)*(a2*a3*b1^2*b3) + (14147/15000:ℝ)*(a2*a3*b1^2*b2) + (4:ℝ)*(a2*a3*b1^2*b2*b3) + (3361/1200:ℝ)*(a2*a3^2*b2) + (1/10:ℝ)*(a2*a3^2*b1) + (14147/15000:ℝ)*(a2*a3^2*b1*b2) + (28817/60000:ℝ)*(a2*a3^2*b1^2) + (31/200:ℝ)*(a2*a3^2*b1^2*b2) + (4687/500:ℝ)*(a2^2*b3) + (73/50:ℝ)*(a2^2*b3^2) + (4687/500:ℝ)*(a2^2*b1) + (1/50:ℝ)*(a2^2*b1*b3) + (28817/60000:ℝ)*(a2^2*b1*b3^2) + (73/50:ℝ)*(a2^2*b1^2)
noncomputable def Slack_5 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (28817/60000:ℝ)*(a2^2*b1^2*b3) + (151/875:ℝ)*(a2^2*b1^2*b3^2) + (3361/1200:ℝ)*(a2^2*a3*b3) + (1/10:ℝ)*(a2^2*a3*b1) + (14147/15000:ℝ)*(a2^2*a3*b1*b3) + (28817/60000:ℝ)*(a2^2*a3*b1^2) + (31/200:ℝ)*(a2^2*a3*b1^2*b3) + (471/1000:ℝ)*(a2^2*a3^2*b1) + (151/875:ℝ)*(a2^2*a3^2*b1^2) + (961633/26250:ℝ)*(a1*b3) + (4687/500:ℝ)*(a1*b3^2) + (961633/26250:ℝ)*(a1*b2) + (23/25:ℝ)*(a1*b2*b3) + (1/10:ℝ)*(a1*b2*b3^2) + (4687/500:ℝ)*(a1*b2^2) + (1/10:ℝ)*(a1*b2^2*b3)
noncomputable def Slack_6 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (471/1000:ℝ)*(a1*b2^2*b3^2) + (248/25:ℝ)*(a1*b1) + (173603/12000:ℝ)*(a1*b1*b3) + (3361/1200:ℝ)*(a1*b1*b3^2) + (173603/12000:ℝ)*(a1*b1*b2) + (3/25:ℝ)*(a1*b1*b2*b3) + (1379/1250:ℝ)*(a1*b1*b2*b3^2) + (3361/1200:ℝ)*(a1*b1*b2^2) + (1379/1250:ℝ)*(a1*b1*b2^2*b3) + (2:ℝ)*(a1*b1*b2^2*b3^2) + (173603/12000:ℝ)*(a1*a3*b3) + (23/25:ℝ)*(a1*a3*b2) + (6/25:ℝ)*(a1*a3*b2*b3) + (1/50:ℝ)*(a1*a3*b2^2) + (14147/15000:ℝ)*(a1*a3*b2^2*b3) + (173603/12000:ℝ)*(a1*a3*b1)
noncomputable def Slack_7 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (3618/625:ℝ)*(a1*a3*b1*b3) + (6/25:ℝ)*(a1*a3*b1*b2) + (301/50:ℝ)*(a1*a3*b1*b2*b3) + (14147/15000:ℝ)*(a1*a3*b1*b2^2) + (4:ℝ)*(a1*a3*b1*b2^2*b3) + (1/10:ℝ)*(a1*a3^2*b2) + (28817/60000:ℝ)*(a1*a3^2*b2^2) + (3361/1200:ℝ)*(a1*a3^2*b1) + (14147/15000:ℝ)*(a1*a3^2*b1*b2) + (31/200:ℝ)*(a1*a3^2*b1*b2^2) + (23/25:ℝ)*(a1*a2*b3) + (1/50:ℝ)*(a1*a2*b3^2) + (173603/12000:ℝ)*(a1*a2*b2) + (6/25:ℝ)*(a1*a2*b2*b3) + (14147/15000:ℝ)*(a1*a2*b2*b3^2) + (173603/12000:ℝ)*(a1*a2*b1)
noncomputable def Slack_8 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (6/25:ℝ)*(a1*a2*b1*b3) + (14147/15000:ℝ)*(a1*a2*b1*b3^2) + (3618/625:ℝ)*(a1*a2*b1*b2) + (301/50:ℝ)*(a1*a2*b1*b2*b3) + (4:ℝ)*(a1*a2*b1*b2*b3^2) + (3/25:ℝ)*(a1*a2*a3*b3) + (3/25:ℝ)*(a1*a2*a3*b2) + (301/50:ℝ)*(a1*a2*a3*b2*b3) + (3/25:ℝ)*(a1*a2*a3*b1) + (301/50:ℝ)*(a1*a2*a3*b1*b3) + (301/50:ℝ)*(a1*a2*a3*b1*b2) + (8:ℝ)*(a1*a2*a3*b1*b2*b3) + (1379/1250:ℝ)*(a1*a2*a3^2*b2) + (1379/1250:ℝ)*(a1*a2*a3^2*b1) + (4:ℝ)*(a1*a2*a3^2*b1*b2) + (1/10:ℝ)*(a1*a2^2*b3)
noncomputable def Slack_9 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (28817/60000:ℝ)*(a1*a2^2*b3^2) + (3361/1200:ℝ)*(a1*a2^2*b1) + (14147/15000:ℝ)*(a1*a2^2*b1*b3) + (31/200:ℝ)*(a1*a2^2*b1*b3^2) + (1379/1250:ℝ)*(a1*a2^2*a3*b3) + (1379/1250:ℝ)*(a1*a2^2*a3*b1) + (4:ℝ)*(a1*a2^2*a3*b1*b3) + (2:ℝ)*(a1*a2^2*a3^2*b1) + (4687/500:ℝ)*(a1^2*b3) + (73/50:ℝ)*(a1^2*b3^2) + (4687/500:ℝ)*(a1^2*b2) + (1/50:ℝ)*(a1^2*b2*b3) + (28817/60000:ℝ)*(a1^2*b2*b3^2) + (73/50:ℝ)*(a1^2*b2^2) + (28817/60000:ℝ)*(a1^2*b2^2*b3) + (151/875:ℝ)*(a1^2*b2^2*b3^2)
noncomputable def Slack_10 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (3361/1200:ℝ)*(a1^2*a3*b3) + (1/10:ℝ)*(a1^2*a3*b2) + (14147/15000:ℝ)*(a1^2*a3*b2*b3) + (28817/60000:ℝ)*(a1^2*a3*b2^2) + (31/200:ℝ)*(a1^2*a3*b2^2*b3) + (471/1000:ℝ)*(a1^2*a3^2*b2) + (151/875:ℝ)*(a1^2*a3^2*b2^2) + (1/10:ℝ)*(a1^2*a2*b3) + (28817/60000:ℝ)*(a1^2*a2*b3^2) + (3361/1200:ℝ)*(a1^2*a2*b2) + (14147/15000:ℝ)*(a1^2*a2*b2*b3) + (31/200:ℝ)*(a1^2*a2*b2*b3^2) + (1379/1250:ℝ)*(a1^2*a2*a3*b3) + (1379/1250:ℝ)*(a1^2*a2*a3*b2) + (4:ℝ)*(a1^2*a2*a3*b2*b3) + (2:ℝ)*(a1^2*a2*a3^2*b2)
noncomputable def Slack_11 (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  (471/1000:ℝ)*(a1^2*a2^2*b3) + (151/875:ℝ)*(a1^2*a2^2*b3^2) + (2:ℝ)*(a1^2*a2^2*a3*b3)
/-- the unused budget (all coefficients ≥ 0). -/
noncomputable def Slack (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  Slack_1 a1 a2 a3 b1 b2 b3 + Slack_2 a1 a2 a3 b1 b2 b3 + Slack_3 a1 a2 a3 b1 b2 b3 + Slack_4 a1 a2 a3 b1 b2 b3 + Slack_5 a1 a2 a3 b1 b2 b3 + Slack_6 a1 a2 a3 b1 b2 b3 + Slack_7 a1 a2 a3 b1 b2 b3 + Slack_8 a1 a2 a3 b1 b2 b3 + Slack_9 a1 a2 a3 b1 b2 b3 + Slack_10 a1 a2 a3 b1 b2 b3 + Slack_11 a1 a2 a3 b1 b2 b3
set_option maxHeartbeats 4000000 in
theorem delta_eq (a1 a2 a3 b1 b2 b3 : ℝ) :
    p (a1+b1) (a2+b2) (a3+b3) - p a1 a2 a3 - p b1 b2 b3 + p 0 0 0 = -T a1 a2 a3 b1 b2 b3 := by
  unfold p T T_1 T_2 T_3 T_4 T_5 T_6 T_7 T_8 T_9 T_10 T_11; ring
set_option maxHeartbeats 4000000 in
theorem T_eq (a1 a2 a3 b1 b2 b3 : ℝ) :
    T a1 a2 a3 b1 b2 b3 = KS1 a1 a2 a3 b1 b2 b3 + KS2 a1 a2 a3 b1 b2 b3 + KS3 a1 a2 a3 b1 b2 b3 + KS4 a1 a2 a3 b1 b2 b3 + KS5 a1 a2 a3 b1 b2 b3 + KS6 a1 a2 a3 b1 b2 b3 + KS7 a1 a2 a3 b1 b2 b3 + KS8 a1 a2 a3 b1 b2 b3 + KS9 a1 a2 a3 b1 b2 b3 + KS10 a1 a2 a3 b1 b2 b3 + KS11 a1 a2 a3 b1 b2 b3 + KS12 a1 a2 a3 b1 b2 b3 + KS13 a1 a2 a3 b1 b2 b3 + KS14 a1 a2 a3 b1 b2 b3 + Slack a1 a2 a3 b1 b2 b3 := by
  unfold T Slack T_1 T_2 T_3 T_4 T_5 T_6 T_7 T_8 T_9 T_10 T_11 Slack_1 Slack_2 Slack_3 Slack_4 Slack_5 Slack_6 Slack_7 Slack_8 Slack_9 Slack_10 Slack_11 KS1 KS2 KS3 KS4 KS5 KS6 KS7 KS8 KS9 KS10 KS11 KS12 KS13 KS14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14; ring
theorem Slack_pos (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) : 0 < Slack a1 a2 a3 b1 b2 b3 := by
  unfold Slack Slack_1 Slack_2 Slack_3 Slack_4 Slack_5 Slack_6 Slack_7 Slack_8 Slack_9 Slack_10 Slack_11; positivity

/-- Main theorem: on classes of norm at least one, every second difference of `p` is negative. -/
theorem delta_neg (a1 a2 a3 b1 b2 b3 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hA : 1 ≤ a1*a2*a3) (hB : 1 ≤ b1*b2*b3) :
    p (a1+b1) (a2+b2) (a3+b3) - p a1 a2 a3 - p b1 b2 b3 + p 0 0 0 < 0 := by
  rw [delta_eq, T_eq]
  have k1 := KS1_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k2 := KS2_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k3 := KS3_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k4 := KS4_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k5 := KS5_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k6 := KS6_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k7 := KS7_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k8 := KS8_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k9 := KS9_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k10 := KS10_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k11 := KS11_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k12 := KS12_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k13 := KS13_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have k14 := KS14_nonneg a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  have s := Slack_pos a1 a2 a3 b1 b2 b3 ha1 ha2 ha3 hb1 hb2 hb3 hA hB
  linarith

/-- Consequence (the Farkas side): for finitely many pieces of norm ≥ 1 and weights `n ≥ 0`,
    `∑ n·Δp ≤ 0 < p(0)`, so no nonnegative combination of pieces reproduces `p(0)`. -/
theorem no_design {ι : Type*} (s : Finset ι) (n : ι → ℝ) (hn : ∀ i ∈ s, 0 ≤ n i)
    (a b : ι → Fin 3 → ℝ) (ha : ∀ i ∈ s, ∀ j, 0 < a i j) (hb : ∀ i ∈ s, ∀ j, 0 < b i j)
    (hA : ∀ i ∈ s, 1 ≤ a i 0 * a i 1 * a i 2) (hB : ∀ i ∈ s, 1 ≤ b i 0 * b i 1 * b i 2) :
    ∑ i ∈ s, n i * (p (a i 0 + b i 0) (a i 1 + b i 1) (a i 2 + b i 2) - p (a i 0) (a i 1) (a i 2)
        - p (b i 0) (b i 1) (b i 2) + p 0 0 0) < p 0 0 0 := by
  have h : ∀ i ∈ s, n i * (p (a i 0 + b i 0) (a i 1 + b i 1) (a i 2 + b i 2) - p (a i 0) (a i 1) (a i 2)
        - p (b i 0) (b i 1) (b i 2) + p 0 0 0) ≤ 0 := by
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hn i hi) (le_of_lt (delta_neg _ _ _ _ _ _ (ha i hi 0) (ha i hi 1)
      (ha i hi 2) (hb i hi 0) (hb i hi 1) (hb i hi 2) (hA i hi) (hB i hi)))
  calc _ ≤ ∑ i ∈ s, (0:ℝ) := Finset.sum_le_sum h
    _ = 0 := by simp
    _ < p 0 0 0 := by rw [p_zero]; norm_num

end TraceThreeCertificate

#print axioms TraceThreeCertificate.amgm_nat
#print axioms TraceThreeCertificate.p_mem
#print axioms TraceThreeCertificate.p_zero
#print axioms TraceThreeCertificate.col1
#print axioms TraceThreeCertificate.col2
#print axioms TraceThreeCertificate.col3
#print axioms TraceThreeCertificate.col4
#print axioms TraceThreeCertificate.col5
#print axioms TraceThreeCertificate.col6
#print axioms TraceThreeCertificate.col7
#print axioms TraceThreeCertificate.col8
#print axioms TraceThreeCertificate.col9
#print axioms TraceThreeCertificate.col10
#print axioms TraceThreeCertificate.col11
#print axioms TraceThreeCertificate.col12
#print axioms TraceThreeCertificate.col13
#print axioms TraceThreeCertificate.col14
#print axioms TraceThreeCertificate.delta_eq
#print axioms TraceThreeCertificate.T_eq
#print axioms TraceThreeCertificate.delta_neg
#print axioms TraceThreeCertificate.no_design
