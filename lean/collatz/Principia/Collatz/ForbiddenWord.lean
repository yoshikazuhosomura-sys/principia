/-
  コラッツの奇ステップ写像における ±1 の符号の非対称と禁止語 DDD。

  設定：奇ステップ写像 x_{k+1} = (3 x_k + q)/2^{v_k}、V_k = Σ_{i<k} v_i、
        a = log₂ 3、e_k = V_k − ⌊k·a⌋。
  一歩の差分は e_{k+1} − e_k = v_{k+1} − g_k、g_k = ⌊(k+1)a⌋ − ⌊k·a⌋ ∈ {1,2}。

  ここで機械に確かめさせること：
    (1) 4 < 3a < 5（= 2⁴ < 3³ < 2⁵）、3 < 2a（= 2³ < 3²）、5a < 8（= 3⁵ < 2⁸）
    (2) 窓和の上限 ⌊(k+3)a⌋ − ⌊k a⌋ ≤ 5 と下限 3 ≤ ⌊(k+2)a⌋ − ⌊k a⌋
    (3) **e_k は 3 歩続けて下がれない**（禁止語 DDD）。証明に使う不等式は 3³ < 2⁵ だけ
    (4) 非対称 A = (3a − 5)/4 < 0（上昇優勢）。**同じ不等式 3³ < 2⁵ である**
  ⟹ 「非対称の符号」と「禁止語 DDD」は同一の不等式 27 < 32 から出る。

  sorry 0・native_decide 不使用。
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Collatz

open Real Finset

noncomputable def cA : ℝ := Real.logb 2 3

theorem log_two_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `cA = log 3 / log 2`。 -/
theorem cA_eq : cA = Real.log 3 / Real.log 2 := rfl

/-- `m * cA < n` は `3^m < 2^n` と同値（この向きだけ使う）。 -/
theorem mul_cA_lt (m n : ℕ) (h : (3:ℝ) ^ m < (2:ℝ) ^ n) : (m:ℝ) * cA < n := by
  have hl2 := log_two_pos
  have h3 : Real.log ((3:ℝ) ^ m) < Real.log ((2:ℝ) ^ n) :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h3
  rw [cA_eq, show (m:ℝ) * (Real.log 3 / Real.log 2) = ((m:ℝ) * Real.log 3) / Real.log 2 from by ring,
      div_lt_iff₀ hl2]
  linarith

/-- `n < m * cA` は `2^n < 3^m` と同値（この向きだけ使う）。 -/
theorem lt_mul_cA (m n : ℕ) (h : (2:ℝ) ^ n < (3:ℝ) ^ m) : (n:ℝ) < (m:ℝ) * cA := by
  have hl2 := log_two_pos
  have h3 : Real.log ((2:ℝ) ^ n) < Real.log ((3:ℝ) ^ m) :=
    Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h3
  rw [cA_eq, show (m:ℝ) * (Real.log 3 / Real.log 2) = ((m:ℝ) * Real.log 3) / Real.log 2 from by ring,
      lt_div_iff₀ hl2]
  linarith

/-- **3³ < 2⁵（27 < 32）** ⟹ `3a < 5`。非対称の符号と禁止語 DDD の両方の出所。 -/
theorem three_cA_lt_five : 3 * cA < 5 := by
  have := mul_cA_lt 3 5 (by norm_num)
  norm_num at this ⊢; linarith

/-- **2⁴ < 3³（16 < 27）** ⟹ `4 < 3a`。 -/
theorem four_lt_three_cA : 4 < 3 * cA := by
  have := lt_mul_cA 3 4 (by norm_num)
  norm_num at this ⊢; linarith

/-- **2³ < 3²（8 < 9）** ⟹ `3 < 2a`。これが「g に 11 が無い」の出所。 -/
theorem three_lt_two_cA : 3 < 2 * cA := by
  have := lt_mul_cA 2 3 (by norm_num)
  norm_num at this ⊢; linarith

/-- **3⁵ < 2⁸（243 < 256）** ⟹ `5a < 8`。これが禁止語 DDUDD の出所。 -/
theorem five_cA_lt_eight : 5 * cA < 8 := by
  have := mul_cA_lt 5 8 (by norm_num)
  norm_num at this ⊢; linarith

/-- 窓和の上限：`⌊(k+3)a⌋ − ⌊k a⌋ ≤ 5`。すなわち `g_k + g_{k+1} + g_{k+2} ≤ 5`。
    ⟹ 3 つの `g` がすべて 2 になることはない。 -/
theorem floor_window_three (k : ℕ) :
    ⌊((k:ℝ) + 3) * cA⌋ - ⌊(k:ℝ) * cA⌋ ≤ 5 := by
  have hexp : ((k:ℝ) + 3) * cA = (k:ℝ) * cA + 3 * cA := by ring
  have h2 : ((⌊((k:ℝ) + 3) * cA⌋ : ℤ) : ℝ) ≤ (k:ℝ) * cA + 3 * cA := by
    rw [← hexp]; exact Int.floor_le _
  have h3 : (k:ℝ) * cA - 1 < ((⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h5 := three_cA_lt_five
  have hz : ((⌊((k:ℝ) + 3) * cA⌋ - ⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) < 6 := by
    push_cast; linarith
  have : (⌊((k:ℝ) + 3) * cA⌋ - ⌊(k:ℝ) * cA⌋ : ℤ) < 6 := by exact_mod_cast hz
  omega

/-- 窓和の下限：`3 ≤ ⌊(k+2)a⌋ − ⌊k a⌋`。すなわち `g_k + g_{k+1} ≥ 3`。
    ⟹ 2 つの `g` がともに 1 になることはない（`g` に語 `11` が無い）。 -/
theorem floor_window_two (k : ℕ) :
    3 ≤ ⌊((k:ℝ) + 2) * cA⌋ - ⌊(k:ℝ) * cA⌋ := by
  have hexp : ((k:ℝ) + 2) * cA = (k:ℝ) * cA + 2 * cA := by ring
  have h2 : ((⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) ≤ (k:ℝ) * cA := Int.floor_le _
  have h3 : (k:ℝ) * cA + 2 * cA - 1 < ((⌊((k:ℝ) + 2) * cA⌋ : ℤ) : ℝ) := by
    rw [← hexp]; exact Int.sub_one_lt_floor _
  have h5 := three_lt_two_cA
  have hz : (2:ℝ) < ((⌊((k:ℝ) + 2) * cA⌋ - ⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  have : (2:ℤ) < ⌊((k:ℝ) + 2) * cA⌋ - ⌊(k:ℝ) * cA⌋ := by exact_mod_cast hz
  omega

/-- 窓和の上限（長さ 5）：`⌊(k+5)a⌋ − ⌊k a⌋ ≤ 8`。禁止語 DDUDD の出所。 -/
theorem floor_window_five (k : ℕ) :
    ⌊((k:ℝ) + 5) * cA⌋ - ⌊(k:ℝ) * cA⌋ ≤ 8 := by
  have hexp : ((k:ℝ) + 5) * cA = (k:ℝ) * cA + 5 * cA := by ring
  have h2 : ((⌊((k:ℝ) + 5) * cA⌋ : ℤ) : ℝ) ≤ (k:ℝ) * cA + 5 * cA := by
    rw [← hexp]; exact Int.floor_le _
  have h3 : (k:ℝ) * cA - 1 < ((⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h5 := five_cA_lt_eight
  have hz : ((⌊((k:ℝ) + 5) * cA⌋ - ⌊(k:ℝ) * cA⌋ : ℤ) : ℝ) < 9 := by
    push_cast; linarith
  have : (⌊((k:ℝ) + 5) * cA⌋ - ⌊(k:ℝ) * cA⌋ : ℤ) < 9 := by exact_mod_cast hz
  omega

/-! ### e_k と禁止語 -/

/-- `V_k = Σ_{i<k} v_i`。 -/
def Vsum (v : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, v i

/-- `e_k = V_k − ⌊k·a⌋`。 -/
noncomputable def eK (v : ℕ → ℕ) (k : ℕ) : ℤ := (Vsum v k : ℤ) - ⌊(k:ℝ) * cA⌋

theorem Vsum_step_three (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    (Vsum v k : ℤ) + 3 ≤ (Vsum v (k + 3) : ℤ) := by
  have h : Vsum v (k + 3) = Vsum v k + (v k + v (k + 1) + v (k + 2)) := by
    simp [Vsum, Finset.sum_range_succ]; ring
  have h0 := hv k; have h1 := hv (k + 1); have h2 := hv (k + 2)
  omega

/-- **主定理：`e_{k+3} − e_k ≥ −2`。** 使う不等式は `3³ < 2⁵` と `v_i ≥ 1` だけ。 -/
theorem eK_three_step_lower (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    -2 ≤ eK v (k + 3) - eK v k := by
  have hV := Vsum_step_three v hv k
  have hf := floor_window_three k
  have hc : ((k + 3 : ℕ) : ℝ) = (k:ℝ) + 3 := by push_cast; ring
  simp only [eK, hc]
  omega

/-- **系：禁止語 DDD。** `e` は 3 歩続けて下がれない。 -/
theorem no_three_consecutive_descents (v : ℕ → ℕ) (hv : ∀ i, 1 ≤ v i) (k : ℕ) :
    ¬ (eK v (k + 1) < eK v k ∧ eK v (k + 2) < eK v (k + 1) ∧
       eK v (k + 3) < eK v (k + 2)) := by
  intro ⟨h1, h2, h3⟩
  have := eK_three_step_lower v hv k
  omega

/-! ### 非対称の符号 -/

/-- 最小模型（v は iid `P(v=j)=2^{-j}`、g は Weyl 列、両者は独立）から紙で出た
    非対称 `A = P(下降) − P(上昇) = (3a − 5)/4`。その符号が負であること。
    **`no_three_consecutive_descents` と同じ不等式 `3³ < 2⁵` から出る。** -/
theorem asymmetry_negative : (3 * cA - 5) / 4 < 0 := by
  have := three_cA_lt_five
  linarith

/-- 非対称がゼロになる傾きは `5/3`、すなわち乗数 `2^(5/3) = 3.1748…`。
    `log₂ 3 < 5/3` が上昇優勢の理由である。 -/
theorem cA_lt_five_thirds : cA < 5 / 3 := by
  have := three_cA_lt_five
  linarith

end Collatz

#print axioms Collatz.log_two_pos
#print axioms Collatz.cA_eq
#print axioms Collatz.mul_cA_lt
#print axioms Collatz.lt_mul_cA
#print axioms Collatz.three_cA_lt_five
#print axioms Collatz.four_lt_three_cA
#print axioms Collatz.three_lt_two_cA
#print axioms Collatz.five_cA_lt_eight
#print axioms Collatz.floor_window_three
#print axioms Collatz.floor_window_two
#print axioms Collatz.floor_window_five
#print axioms Collatz.Vsum_step_three
#print axioms Collatz.eK_three_step_lower
#print axioms Collatz.no_three_consecutive_descents
#print axioms Collatz.asymmetry_negative
#print axioms Collatz.cA_lt_five_thirds
