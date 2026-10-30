import Mathlib

/-!
# Two-colour KP sum split by size

For a finite family `F` of connected polymers containing the root, with weights `w C ≥ 0` (the KP `|z C| e^{a|C|}`),
sum separately over size `|C| ≤ n₀` (thin colour) and `|C| > n₀` (thick colour).

* The thin colour is taken as a hypothesis `A` on the sum itself (supplied from outside, e.g. from actual Gaussian spectral values).
* The thick colour is bounded by a uniform per-plaquette bound `w C ≤ η^{|C|}` and counts per size `N n` (e.g. `e(eΔ)^{n-1}`).
* If the counts have the form `c K^{n-1}` and `q = K η < 1`, the thick-colour sum is ≤ `(c/K) q^{n₀+1}/(1-q)`.

Since the colour is determined by polymer size rather than by points, this can be used independently of the point-colour two-colour version (TwoColorPolymerSum).
-/

namespace SizeSplitKP

open Finset

variable {P : Type*}

/-- Splitting by size: the sum is the thin-colour sum plus the thick-colour sum. -/
theorem sum_split_by_card (F : Finset (Finset P)) (w : Finset P → ℝ) (n₀ : ℕ) :
    ∑ C ∈ F, w C = ∑ C ∈ F.filter (fun C => C.card ≤ n₀), w C
      + ∑ C ∈ F.filter (fun C => ¬ C.card ≤ n₀), w C :=
  (sum_filter_add_sum_filter_not F (fun C => C.card ≤ n₀) w).symm

/-- Thick-colour sum, summed over size fibres: if all polymers have size ≤ `M`,
the number of polymers of size `n` is ≤ `N n`, and thick polymers have `w C ≤ η^{|C|}` (`η ≥ 0`), then
`Σ_{thick} w ≤ Σ_{n ∈ [n₀+1, M]} N n η^n`. -/
theorem fat_sum_le (F : Finset (Finset P)) (w : Finset P → ℝ) (n₀ M : ℕ) (N : ℕ → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hM : ∀ C ∈ F, C.card ≤ M)
    (hN : ∀ n, ((F.filter (fun C => C.card = n)).card : ℝ) ≤ N n)
    (hfat : ∀ C ∈ F, n₀ < C.card → w C ≤ η ^ C.card) :
    ∑ C ∈ F.filter (fun C => ¬ C.card ≤ n₀), w C ≤ ∑ n ∈ Ico (n₀ + 1) (M + 1), N n * η ^ n := by
  have hmaps : ∀ C ∈ F.filter (fun C => ¬ C.card ≤ n₀), C.card ∈ Ico (n₀ + 1) (M + 1) := by
    intro C hC
    rw [mem_filter] at hC
    rw [mem_Ico]
    exact ⟨by omega, by have := hM C hC.1; omega⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum
  intro n hn
  calc ∑ C ∈ (F.filter (fun C => ¬ C.card ≤ n₀)).filter (fun C => C.card = n), w C
      ≤ ∑ C ∈ (F.filter (fun C => ¬ C.card ≤ n₀)).filter (fun C => C.card = n), η ^ n := by
        apply sum_le_sum
        intro C hC
        rw [mem_filter, mem_filter] at hC
        have h := hfat C hC.1.1 (by omega)
        rw [hC.2] at h
        exact h
    _ = (((F.filter (fun C => ¬ C.card ≤ n₀)).filter (fun C => C.card = n)).card : ℝ) * η ^ n := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((F.filter (fun C => C.card = n)).card : ℝ) * η ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hη n)
        exact_mod_cast card_le_card (by
          intro C hC
          rw [mem_filter, mem_filter] at hC
          rw [mem_filter]; exact ⟨hC.1.1, hC.2⟩)
    _ ≤ N n * η ^ n := mul_le_mul_of_nonneg_right (hN n) (pow_nonneg hη n)

/-- If the count is `c K^{n-1}` (`K > 0`), `q = K η`, `0 ≤ q < 1`, then
`Σ_{n ∈ [n₀+1, M]} c K^{n-1} η^n ≤ (c/K) q^{n₀+1}/(1-q)` (`c ≥ 0`). -/
theorem geometric_tail_le (c K η : ℝ) (n₀ M : ℕ) (hc : 0 ≤ c) (hK : 0 < K) (hη : 0 ≤ η)
    (hq : K * η < 1) :
    ∑ n ∈ Ico (n₀ + 1) (M + 1), c * K ^ (n - 1) * η ^ n
      ≤ c / K * ((K * η) ^ (n₀ + 1) / (1 - K * η)) := by
  have hterm : ∀ n ∈ Ico (n₀ + 1) (M + 1), c * K ^ (n - 1) * η ^ n = c / K * (K * η) ^ n := by
    intro n hn
    rw [mem_Ico] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, mul_pow, pow_succ]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hc hK.le)
  exact geom_sum_Ico_le_of_lt_one (mul_nonneg hK.le hη) hq

/-- Two-colour (by size) KP per-site sum: if the thin-colour sum is ≤ `A` and the thick colour has the two forms above, then
`Σ_F w ≤ A + (c/K) q^{n₀+1}/(1-q)`. -/
theorem size_split_site_sum (F : Finset (Finset P)) (w : Finset P → ℝ) (n₀ M : ℕ)
    (A c K η : ℝ) (hc : 0 ≤ c) (hK : 0 < K) (hη : 0 ≤ η) (hq : K * η < 1)
    (hthin : ∑ C ∈ F.filter (fun C => C.card ≤ n₀), w C ≤ A)
    (hM : ∀ C ∈ F, C.card ≤ M)
    (hN : ∀ n, ((F.filter (fun C => C.card = n)).card : ℝ) ≤ c * K ^ (n - 1))
    (hfat : ∀ C ∈ F, n₀ < C.card → w C ≤ η ^ C.card) :
    ∑ C ∈ F, w C ≤ A + c / K * ((K * η) ^ (n₀ + 1) / (1 - K * η)) := by
  rw [sum_split_by_card F w n₀]
  have h1 := fat_sum_le F w n₀ M (fun n => c * K ^ (n - 1)) η hη hM hN hfat
  have h2 := geometric_tail_le c K η n₀ M hc hK hη hq
  linarith

/-- The condition for the thick colour to beat the counting is `K η < 1`. With `K = eΔ`, `η = e² ε` it is equivalent to `ε < 1/(e³Δ)`. -/
theorem fat_condition_iff (Δ ε : ℝ) (hΔ : 0 < Δ) :
    (Real.exp 1 * Δ) * (Real.exp 1 ^ 2 * ε) < 1 ↔ ε < 1 / (Real.exp 1 ^ 3 * Δ) := by
  have he : 0 < Real.exp 1 ^ 3 * Δ := mul_pos (pow_pos (Real.exp_pos 1) 3) hΔ
  rw [lt_div_iff₀ he]
  constructor <;> intro h <;> nlinarith [h]

/-- Raising the adjacency degree from `Δ` to `Δ'` multiplies the allowed per-plaquette bound by `Δ/Δ'`. -/
theorem allowed_eps_scale (Δ Δ' : ℝ) (hΔ : 0 < Δ) (hΔ' : 0 < Δ') :
    1 / (Real.exp 1 ^ 3 * Δ') = (Δ / Δ') * (1 / (Real.exp 1 ^ 3 * Δ)) := by
  have : Real.exp 1 ^ 3 ≠ 0 := (pow_pos (Real.exp_pos 1) 3).ne'
  field_simp

end SizeSplitKP

#print axioms SizeSplitKP.sum_split_by_card
#print axioms SizeSplitKP.fat_sum_le
#print axioms SizeSplitKP.geometric_tail_le
#print axioms SizeSplitKP.size_split_site_sum
#print axioms SizeSplitKP.fat_condition_iff
#print axioms SizeSplitKP.allowed_eps_scale
