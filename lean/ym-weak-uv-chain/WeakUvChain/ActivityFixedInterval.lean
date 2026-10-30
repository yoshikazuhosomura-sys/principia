/-
Arithmetic reducing the existence of an invariant interval for the activity recursion
(chain field `fix`: ρ Z + A Φ + B Z² ≤ Z) to an explicit smallness condition.
Single file; checks with `import Mathlib` only.

  With ρ < 1, A, Φ ≥ 0 (B of any sign) and Z = 2AΦ/(1−ρ): if 4·B·AΦ ≤ (1−ρ)²/2 then ρ Z + A Φ + B Z² ≤ Z.
  Taking ρ = L_d e^{−b} (one coarse-graining step), A Φ (upper bound on the freshly generated large-field supply)
  and B (merging coefficient, of type 2ε′), the invariant-interval condition becomes the single inequality
  "supply × merging coefficient ≤ (1 − ρ)²/8".
-/
import Mathlib

namespace ActivityFixedInterval

theorem fixed_interval (ρ A Φ B : ℝ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hΦ : 0 ≤ Φ)
    (hsmall : 4 * B * (A * Φ) ≤ (1 - ρ) ^ 2 / 2) :
    ρ * (2 * (A * Φ) / (1 - ρ)) + A * Φ + B * (2 * (A * Φ) / (1 - ρ)) ^ 2 ≤
      2 * (A * Φ) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  set w := A * Φ with hw
  have hw0 : 0 ≤ w := mul_nonneg hA hΦ
  -- compare after multiplying both sides by (1−ρ)²
  have key : (ρ * (2 * w / (1 - ρ)) + w + B * (2 * w / (1 - ρ)) ^ 2) * (1 - ρ) ^ 2 ≤
      (2 * w / (1 - ρ)) * (1 - ρ) ^ 2 := by
    have e1 : (ρ * (2 * w / (1 - ρ)) + w + B * (2 * w / (1 - ρ)) ^ 2) * (1 - ρ) ^ 2 =
        2 * ρ * w * (1 - ρ) + w * (1 - ρ) ^ 2 + 4 * B * w ^ 2 := by
      field_simp; ring
    have e2 : (2 * w / (1 - ρ)) * (1 - ρ) ^ 2 = 2 * w * (1 - ρ) := by
      field_simp
    rw [e1, e2]
    -- 2ρw(1−ρ) + w(1−ρ)² + 4Bw² ≤ 2w(1−ρ) ⇔ 4Bw² ≤ w(1−ρ)² ⇐ 4Bw ≤ (1−ρ)²
    have h4 : 4 * B * w ^ 2 ≤ w * ((1 - ρ) ^ 2 / 2) := by
      have := mul_le_mul_of_nonneg_left hsmall hw0
      nlinarith
    nlinarith [sq_nonneg (1 - ρ)]
  have hpos : 0 < (1 - ρ) ^ 2 := by positivity
  exact le_of_mul_le_mul_right key hpos

#print axioms fixed_interval

end ActivityFixedInterval
