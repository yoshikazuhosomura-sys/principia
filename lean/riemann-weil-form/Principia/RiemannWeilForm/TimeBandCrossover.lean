import Mathlib

/-!
# The crossover height of a window and the smooth zero count

Fix a window half-width `L > 0`.  Two counting functions compete at height `T`:

* the Shannon number of the even part of the window at band `T`, `shannon L T = L * T / π`,
  which grows linearly in `T`;
* the smooth part of the zero counting function,
  `smoothCount T = (T / 2π) * log (T / 2π e) + 7/8`,
  whose density `(1 / 2π) * log (T / 2π)` grows logarithmically.

The difference `shannon L T - smoothCount T` therefore has a maximum.  This file computes it:
the maximum is attained at the unique height `T = 2π * exp (2 * L)`, where the two densities
agree, and its value is exactly

  `exp (2 * L) - 7/8`.

So the constant `-7/8` of the smooth model is not a fitted quantity: it is the constant of
the zero counting function, carried unchanged through the maximisation, because the two
`L`-dependent parts cancel identically at the crossover height.

Everything reduces to one elementary inequality, `t * (1 - log t) ≤ 1` for `t > 0`, with
equality exactly at `t = 1`; that inequality is `log (1/t) ≤ 1/t - 1` multiplied by `t`.

Main statements:

* `TimeBand.mul_one_sub_log_le`, `TimeBand.mul_one_sub_log_lt` — the elementary inequality
  and its strict form.
* `TimeBand.crossover_le` — `shannon L T - smoothCount T ≤ exp (2 * L) - 7/8` for every
  `T > 0` and every real `L`.
* `TimeBand.crossover_eq` — equality at `T = 2π * exp (2 * L)`.
* `TimeBand.crossover_lt` — strict inequality at every other positive height.
* `TimeBand.smoothCount_eq_of_pos` — the two ways of writing the smooth count agree.
-/

namespace TimeBand

open Real

/-- The Shannon number of the even part of a window of half-width `L` at band `T`. -/
noncomputable def shannon (L T : ℝ) : ℝ := L * T / π

/-- The smooth part of the zero counting function, written with the `1/e` inside the log. -/
noncomputable def smoothCount (T : ℝ) : ℝ := (T / (2 * π)) * (Real.log (T / (2 * π)) - 1) + 7 / 8

/-- The elementary inequality `t * (1 - log t) ≤ 1` for `t > 0`. -/
theorem mul_one_sub_log_le {t : ℝ} (ht : 0 < t) : t * (1 - Real.log t) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h
  have h2 : t * (-Real.log t) ≤ t * (t⁻¹ - 1) := by
    exact mul_le_mul_of_nonneg_left h ht.le
  have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  nlinarith [h2, ht']

/-- The strict form of `mul_one_sub_log_le`. -/
theorem mul_one_sub_log_lt {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    t * (1 - Real.log t) < 1 := by
  have hinv : t⁻¹ ≠ 1 := by
    intro h
    exact ht1 (by field_simp at h; linarith [h])
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr ht) hinv
  rw [Real.log_inv] at h
  have h2 : t * (-Real.log t) < t * (t⁻¹ - 1) := by
    exact mul_lt_mul_of_pos_left h ht
  have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  nlinarith [h2, ht']

/-- The two ways of writing the smooth count agree for `T > 0`. -/
theorem smoothCount_eq_of_pos {T : ℝ} (hT : 0 < T) :
    (T / (2 * π)) * Real.log (T / (2 * π * Real.exp 1)) + 7 / 8 = smoothCount T := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hx : 0 < T / (2 * π) := by positivity
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hrw : T / (2 * π * Real.exp 1) = (T / (2 * π)) / Real.exp 1 := by
    field_simp
  rw [hrw, Real.log_div hx.ne' he.ne', Real.log_exp]
  rfl

/-- The key identity behind the crossover: writing `x = T / 2π` and `c = exp (2 L)`,
the difference of the two counts is `c * ((x/c) * (1 - log (x/c))) - 7/8`. -/
theorem crossover_rewrite {L T : ℝ} (hT : 0 < T) :
    shannon L T - smoothCount T
      = Real.exp (2 * L) * ((T / (2 * π) / Real.exp (2 * L)) *
          (1 - Real.log (T / (2 * π) / Real.exp (2 * L)))) - 7 / 8 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hx : 0 < T / (2 * π) := by positivity
  have hc : (0:ℝ) < Real.exp (2 * L) := Real.exp_pos _
  rw [Real.log_div hx.ne' hc.ne', Real.log_exp]
  simp only [shannon, smoothCount]
  field_simp
  ring

/-- The difference of the two counting functions never exceeds `exp (2 L) - 7/8`. -/
theorem crossover_le (L : ℝ) {T : ℝ} (hT : 0 < T) :
    shannon L T - smoothCount T ≤ Real.exp (2 * L) - 7 / 8 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hc : (0:ℝ) < Real.exp (2 * L) := Real.exp_pos _
  have ht : 0 < T / (2 * π) / Real.exp (2 * L) := by positivity
  have h := mul_one_sub_log_le ht
  have := mul_le_mul_of_nonneg_left h hc.le
  rw [crossover_rewrite hT]
  linarith [this]

/-- At the crossover height the difference equals `exp (2 L) - 7/8`. -/
theorem crossover_eq (L : ℝ) :
    shannon L (2 * π * Real.exp (2 * L)) - smoothCount (2 * π * Real.exp (2 * L))
      = Real.exp (2 * L) - 7 / 8 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hc : (0:ℝ) < Real.exp (2 * L) := Real.exp_pos _
  have hT : 0 < 2 * π * Real.exp (2 * L) := by positivity
  have hx : (2 * π * Real.exp (2 * L)) / (2 * π) / Real.exp (2 * L) = 1 := by
    field_simp
  rw [crossover_rewrite hT, hx]
  simp

/-- Away from the crossover height the inequality is strict: the maximiser is unique. -/
theorem crossover_lt (L : ℝ) {T : ℝ} (hT : 0 < T) (hne : T ≠ 2 * π * Real.exp (2 * L)) :
    shannon L T - smoothCount T < Real.exp (2 * L) - 7 / 8 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hc : (0:ℝ) < Real.exp (2 * L) := Real.exp_pos _
  have ht : 0 < T / (2 * π) / Real.exp (2 * L) := by positivity
  have ht1 : T / (2 * π) / Real.exp (2 * L) ≠ 1 := by
    intro h
    apply hne
    field_simp at h
    linarith [h]
  have h := mul_one_sub_log_lt ht ht1
  have := mul_lt_mul_of_pos_left h hc
  rw [crossover_rewrite hT]
  linarith [this]

end TimeBand

#print axioms TimeBand.mul_one_sub_log_le
#print axioms TimeBand.mul_one_sub_log_lt
#print axioms TimeBand.smoothCount_eq_of_pos
#print axioms TimeBand.crossover_rewrite
#print axioms TimeBand.crossover_le
#print axioms TimeBand.crossover_eq
#print axioms TimeBand.crossover_lt
