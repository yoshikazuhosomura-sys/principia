/-
  同変化の壁 — 平行移動の有限群による不変部分の跡の算術

  内容（幾何は一切入っていない。すべて有限群と整数の等式である）：

  (1) 跡の平均：非単位元の Lefschetz 数が 0 なら、不変部分のオイラー標数は `χ / |G|`。
      ゆえに `|G|` は `χ` を割る。
  (2) 冪指数の壁：群のすべての元が `g ^ 113 = 1` を満たし、位数が `495178790400` を割るなら、
      群は自明である（`113` は素数で `495178790400 = 2⁹·3⁷·5²·7²·19²` を割らない）。
  (3) 窓 `[104,125]` の中で `495178790400` と `30240` の両方を割る数の決定。
  (4) Serre 双対の算術：偶数次元 4 と 6 での `χ` と `ext^i` の関係。
      次元 4 では `ext²` が下から押される。次元 6 では押されるのは `ext³` であって
      `ext²` は `0` でも矛盾しない（証人つき）。
-/
import Mathlib

namespace EquivariantTrace

open Finset

/-! ## 1. 跡の平均（固定点が無い元の寄与は 0） -/

/-- 非単位元の Lefschetz 数がすべて 0 なら、群上の和は単位元の値に等しい。 -/
theorem sum_of_vanishing_offIdentity {G : Type*} [Fintype G] [DecidableEq G] [One G]
    (L : G → ℤ) (h : ∀ g : G, g ≠ 1 → L g = 0) :
    (∑ g : G, L g) = L 1 := by
  classical
  rw [Finset.sum_eq_single (1 : G)]
  · intro b _ hb; exact h b hb
  · intro hb; exact absurd (Finset.mem_univ (1 : G)) hb

/-- 不変部分のオイラー標数が `χ / |G|` であること（整数の形）：
    `|G| * χinv = χ` を仮定すれば `|G|` は `χ` を割る。 -/
theorem card_dvd_of_invariant (n χ χinv : ℤ) (h : (n : ℤ) * χinv = χ) : n ∣ χ :=
  Dvd.intro χinv (by linarith [h])

/-! ## 2. 冪指数の壁 -/

theorem not_dvd_113 : ¬ (113 ∣ (495178790400 : ℕ)) := by decide

theorem factor_M : (495178790400 : ℕ) = 2 ^ 9 * 3 ^ 7 * 5 ^ 2 * 7 ^ 2 * 19 ^ 2 := by norm_num

theorem gcd_113_M : Nat.gcd 113 495178790400 = 1 := by decide

/-- 位数 `113` の元は存在できない：`113` が位数を割らないから。 -/
theorem no_element_of_order_113 {G : Type*} [Group G] [Fintype G]
    (hcard : Fintype.card G ∣ 495178790400) :
    ¬ (113 ∣ Fintype.card G) := by
  intro h
  exact not_dvd_113 (h.trans hcard)

/-- **壁の芯**：すべての元が `g ^ 113 = 1` を満たし、位数が `495178790400` を割るなら群は自明。 -/
theorem trivial_of_exponent_113 {G : Type*} [Group G] [Fintype G]
    (hexp : ∀ g : G, g ^ 113 = 1)
    (hcard : Fintype.card G ∣ 495178790400) :
    Fintype.card G = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hpd
  have hdvd : orderOf g ∣ 113 := orderOf_dvd_of_pow_eq_one (hexp g)
  rw [hg] at hdvd
  have hp113 : p = 113 := by
    have h113 : Nat.Prime 113 := by norm_num
    rcases Nat.Prime.eq_one_or_self_of_dvd h113 p hdvd with h | h
    · exact absurd h hp.ne_one
    · exact h
  exact not_dvd_113 ((hp113 ▸ hpd).trans hcard)

/-! ## 3. 窓の中の候補 -/

/-- 窓 `[104,125]` の中で `495178790400` を割るのはちょうど `105,108,112,114,120`。 -/
theorem window_divisors_M :
    (Finset.Icc 104 125).filter (fun c => c ∣ (495178790400 : ℕ))
      = {105, 108, 112, 114, 120} := by decide

/-- 窓の中で `495178790400` と `30240` の両方を割るのはちょうど `105,108,112,120`。 -/
theorem window_divisors_both :
    (Finset.Icc 104 125).filter
        (fun c => c ∣ (495178790400 : ℕ) ∧ c ∣ (30240 : ℕ))
      = {105, 108, 112, 120} := by decide

theorem c113_excluded : ¬ ((113 : ℕ) ∣ 495178790400 ∨ (113 : ℕ) ∣ 30240) := by decide

/-! ## 4. Serre 双対の算術 -/

/-- 複素 4 次元・`K = O`・`ext⁰ = 1`：`χ = 2 − 2ext¹ + ext²` なので
    `ext²` は `χ + 2ext¹ − 2`、とくに `ext¹ ≥ 0` なら `ext² ≥ χ − 2`。 -/
theorem ext2_dim4 (e1 e2 chi : ℤ) (h : 2 * 1 - 2 * e1 + e2 = chi) :
    e2 = chi + 2 * e1 - 2 := by linarith

theorem ext2_dim4_lower (e1 e2 chi : ℤ) (h : 2 * 1 - 2 * e1 + e2 = chi) (he1 : 0 ≤ e1) :
    chi - 2 ≤ e2 := by linarith

/-- 複素 6 次元・`K = O`・`ext⁰ = 1`：`χ = 2 − 2ext¹ + 2ext² − ext³` なので
    押されるのは `ext³` であって `ext²` ではない。 -/
theorem ext3_dim6 (e1 e2 e3 chi : ℤ) (h : 2 * 1 - 2 * e1 + 2 * e2 - e3 = chi) :
    e3 = 2 - 2 * e1 + 2 * e2 - chi := by linarith

/-- `χ = −495178790400` のとき、`ext² = 0` でも非負の `ext¹, ext³` が取れる（証人）。 -/
theorem ext2_zero_consistent_dim6 :
    ∃ e1 e3 : ℤ, 0 ≤ e1 ∧ 0 ≤ e3 ∧
      2 * 1 - 2 * e1 + 2 * 0 - e3 = (-495178790400 : ℤ) := by
  refine ⟨247589395201, 0, by norm_num, by norm_num, by norm_num⟩

/-- `24 g² q²`（`g = 7560`, `q = 19`）の値。 -/
theorem chi_value : 24 * 7560 ^ 2 * 19 ^ 2 = (495178790400 : ℕ) := by norm_num

end EquivariantTrace

#print axioms EquivariantTrace.sum_of_vanishing_offIdentity
#print axioms EquivariantTrace.card_dvd_of_invariant
#print axioms EquivariantTrace.trivial_of_exponent_113
#print axioms EquivariantTrace.window_divisors_M
#print axioms EquivariantTrace.window_divisors_both
#print axioms EquivariantTrace.c113_excluded
#print axioms EquivariantTrace.ext2_dim4
#print axioms EquivariantTrace.ext2_dim4_lower
#print axioms EquivariantTrace.ext3_dim6
#print axioms EquivariantTrace.ext2_zero_consistent_dim6
#print axioms EquivariantTrace.chi_value
