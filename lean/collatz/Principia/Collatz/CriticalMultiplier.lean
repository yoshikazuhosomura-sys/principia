/-
  コラッツの「臨界の乗数」の唯一性。

  写像 n ↦ (q·n + r) / p^{v_p(qn+r)} の族で、比の期待値がちょうど 1 になる乗数は
      q_crit(p) = (p² − 1) / (p² − p − 1)
  である。**これが整数になるのは p = 2 のときだけで、そのとき q = 3。**
  つまり 3n+1 は、この形の写像のうち唯一の「ちょうど臨界」なものである。

  証明：
    d := p² − p − 1 が p² − 1 を割るとする。
    d は差 (p² − 1) − (p² − p − 1) = p も割る。
    p ≥ 3 では d = p² − p − 1 > p なので、正の p を割れない（d ≤ p に矛盾）。
    よって p = 2。逆に p = 2 では d = 1 で、何でも割る。
-/
import Mathlib.Tactic

namespace Collatz.CriticalMultiplier

/-- **臨界の乗数が整数になるのは p = 2 のときだけ。** -/
theorem qcrit_dvd_iff (p : ℤ) (hp : 2 ≤ p) :
    (p ^ 2 - p - 1) ∣ (p ^ 2 - 1) ↔ p = 2 := by
  constructor
  · intro hdvd
    -- d は差も割る：(p²−1) − (p²−p−1) = p
    have hp_dvd : (p ^ 2 - p - 1) ∣ p := by
      have h2 := dvd_sub hdvd (dvd_refl (p ^ 2 - p - 1))
      have hEq : (p ^ 2 - 1) - (p ^ 2 - p - 1) = p := by ring
      rwa [hEq] at h2
    by_contra hne
    have h3 : 3 ≤ p := by omega
    -- d は正で、しかも p より大きい
    have hdpos : 0 < p ^ 2 - p - 1 := by nlinarith
    have hgt : p < p ^ 2 - p - 1 := by nlinarith
    -- 正の p を割るなら d ≤ p。矛盾。
    have hle : p ^ 2 - p - 1 ≤ p := Int.le_of_dvd (by omega) hp_dvd
    omega
  · rintro rfl
    norm_num

/-- p = 2 のとき、臨界の乗数はちょうど 3。 -/
theorem qcrit_eq_three : ((2 : ℤ) ^ 2 - 1) = 3 * ((2 : ℤ) ^ 2 - 2 - 1) := by norm_num

/-- 言い換え：p ≥ 3 では、臨界の乗数は整数にならない。 -/
theorem qcrit_not_int_of_three_le (p : ℤ) (hp : 3 ≤ p) :
    ¬ (p ^ 2 - p - 1) ∣ (p ^ 2 - 1) := by
  intro h
  have := (qcrit_dvd_iff p (by omega)).mp h
  omega

end Collatz.CriticalMultiplier

-- 依存している公理を表示する（sorryAx が出なければ、証明は完結している）
#print axioms Collatz.CriticalMultiplier.qcrit_dvd_iff
#print axioms Collatz.CriticalMultiplier.qcrit_eq_three
#print axioms Collatz.CriticalMultiplier.qcrit_not_int_of_three_le
