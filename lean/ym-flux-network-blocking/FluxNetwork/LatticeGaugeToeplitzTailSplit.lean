import Mathlib

/-!
# Toeplitz profile of an inter-block quadratic form: diagonal / nearest-neighbour / tail

A translation-invariant (Toeplitz or circulant) quadratic form `Σ_{i,j} q(|i-j|) x_i x_j` is
described by its distance profile `q : ℕ → ℝ`.  We split the profile into the diagonal part
(distance 0), the nearest-neighbour part (distance 1) and the tail (distance ≥ 2), show the
split is unique, and bound the tail sum uniformly in the cut-off `R` when the profile decays
geometrically.  We also record the flat profile `c_L = (4L+5)/(6(3L+2)^2)` of the one-row chain:
its row sum stays below `2/27` for every `L`, but no geometric bound `c_L ≤ C ρ^r` (`r < L`)
holds uniformly in `L`.
-/

namespace LatticeGaugeToeplitzTailSplit

open Finset Filter Topology

/-- distance-0 part of a profile -/
def diagPart (q : ℕ → ℝ) (r : ℕ) : ℝ := if r = 0 then q r else 0
/-- distance-1 part of a profile -/
def nnPart (q : ℕ → ℝ) (r : ℕ) : ℝ := if r = 1 then q r else 0
/-- distance-≥2 part (the tail) of a profile -/
def tailPart (q : ℕ → ℝ) (r : ℕ) : ℝ := if 2 ≤ r then q r else 0

theorem split (q : ℕ → ℝ) (r : ℕ) : q r = diagPart q r + nnPart q r + tailPart q r := by
  unfold diagPart nnPart tailPart
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r <;> simp
  · have h0 : r ≠ 0 := by omega
    have h1 : r ≠ 1 := by omega
    simp [h0, h1, h]

/-- uniqueness of the split: any decomposition with the right supports is the canonical one -/
theorem split_unique (q d m t : ℕ → ℝ)
    (hd : ∀ r, r ≠ 0 → d r = 0) (hm : ∀ r, r ≠ 1 → m r = 0) (ht : ∀ r, r < 2 → t r = 0)
    (h : ∀ r, q r = d r + m r + t r) :
    d = diagPart q ∧ m = nnPart q ∧ t = tailPart q := by
  refine ⟨funext fun r => ?_, funext fun r => ?_, funext fun r => ?_⟩
  · unfold diagPart
    by_cases h0 : r = 0
    · subst h0
      rw [if_pos rfl, h 0, hm 0 (by norm_num), ht 0 (by norm_num)]; ring
    · rw [if_neg h0, hd r h0]
  · unfold nnPart
    by_cases h1 : r = 1
    · subst h1
      rw [if_pos rfl, h 1, hd 1 (by norm_num), ht 1 (by norm_num)]; ring
    · rw [if_neg h1, hm r h1]
  · unfold tailPart
    by_cases h2 : 2 ≤ r
    · rw [if_pos h2, h r, hd r (by omega), hm r (by omega)]; ring
    · rw [if_neg h2, ht r (by omega)]

/-- the tail sum is bounded uniformly in the cut-off `R` under geometric decay -/
theorem tail_sum_le (q : ℕ → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hq : ∀ r, 2 ≤ r → |q r| ≤ C * ρ ^ r) (R : ℕ) :
    ∑ r ∈ Ico 2 R, |q r| ≤ C * ρ ^ 2 / (1 - ρ) := by
  calc ∑ r ∈ Ico 2 R, |q r| ≤ ∑ r ∈ Ico 2 R, C * ρ ^ r :=
        sum_le_sum fun r hr => hq r (mem_Ico.mp hr).1
    _ = C * ∑ r ∈ Ico 2 R, ρ ^ r := by rw [mul_sum]
    _ ≤ C * (ρ ^ 2 / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hρ0 hρ1) hC
    _ = C * ρ ^ 2 / (1 - ρ) := by ring

/-- the same bound for the tail part of the canonical split, summed over all distances `< R` -/
theorem tailPart_sum_le (q : ℕ → ℝ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hq : ∀ r, 2 ≤ r → |q r| ≤ C * ρ ^ r) (R : ℕ) :
    ∑ r ∈ range R, |tailPart q r| ≤ C * ρ ^ 2 / (1 - ρ) := by
  have hsub : ∑ r ∈ range R, |tailPart q r| = ∑ r ∈ Ico 2 R, |q r| := by
    rcases Nat.lt_or_ge R 2 with hR | hR
    · rw [Ico_eq_empty_of_le (by omega), sum_empty]
      apply sum_eq_zero
      intro r hr
      have : r < 2 := by have := mem_range.mp hr; omega
      simp [tailPart, show ¬ 2 ≤ r by omega]
    · rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 2) hR]
      have h01 : ∑ r ∈ Ico 0 2, |tailPart q r| = 0 := by
        rw [sum_Ico_eq_sum_range]; simp [sum_range_succ, tailPart]
      rw [h01, zero_add]
      apply sum_congr rfl
      intro r hr
      simp [tailPart, (mem_Ico.mp hr).1]
  rw [hsub]; exact tail_sum_le q C ρ hC hρ0 hρ1 hq R

/-- the Toeplitz quadratic form on an open chain of `n` sites with distance profile `q` -/
def qform (n : ℕ) (q : ℕ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, q (Nat.dist i j) * x i * x j

/-- periodic (circulant) distance on `n` sites -/
def cdist (n i j : ℕ) : ℕ := min (Nat.dist i j) (n - Nat.dist i j)

/-- the circulant quadratic form on a periodic chain of `n` sites -/
def cform (n : ℕ) (q : ℕ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, q (cdist n i j) * x i * x j

theorem qform_split (n : ℕ) (q : ℕ → ℝ) (x : Fin n → ℝ) :
    qform n q x = qform n (diagPart q) x + qform n (nnPart q) x + qform n (tailPart q) x := by
  unfold qform
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  rw [split q (Nat.dist i j)]; ring

theorem cform_split (n : ℕ) (q : ℕ → ℝ) (x : Fin n → ℝ) :
    cform n q x = cform n (diagPart q) x + cform n (nnPart q) x + cform n (tailPart q) x := by
  unfold cform
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  rw [split q (cdist n i j)]; ring

/-- one-loop flat inter-block weight of the open diagonal-definition chain with `L` blocks -/
noncomputable def flatQ (L : ℝ) : ℝ := (4 * L + 5) / (6 * (3 * L + 2) ^ 2)

theorem flatQ_two : flatQ 2 = 13 / 384 := by unfold flatQ; norm_num

theorem flat_row_sum_lt (L : ℝ) (hL : 1 ≤ L) : (L - 1) * flatQ L < 2 / 27 := by
  unfold flatQ
  have hp : 0 < 6 * (3 * L + 2) ^ 2 := by positivity
  rw [mul_div_assoc', div_lt_div_iff₀ hp (by norm_num)]
  nlinarith

theorem flatQ_ge (L : ℝ) (hL : 1 ≤ L) : 2 / (75 * L) ≤ flatQ L := by
  unfold flatQ
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith

/-- the flat profile admits no geometric bound `c_L ≤ C ρ^(L-1)` uniform in the length `L` -/
theorem flat_not_uniform_geometric :
    ¬ ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ, 2 ≤ n → flatQ n ≤ C * ρ ^ (n - 1) := by
  rintro ⟨C, ρ, hρ0, hρ1, h⟩
  rcases eq_or_lt_of_le hρ0 with h0 | hpos
  · have h2 := h 2 le_rfl
    rw [← h0] at h2
    norm_num [flatQ] at h2
  · have ht : Tendsto (fun n : ℕ => C * ((n : ℝ) * ρ ^ n)) atTop (𝓝 0) := by
      have := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).const_mul C
      simpa using this
    have hev := ht.eventually (gt_mem_nhds (show (0:ℝ) < 2 * ρ / 75 by positivity))
    obtain ⟨n, hn2, hn⟩ := ((eventually_ge_atTop 2).and hev).exists
    have hb := h n hn2
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hlow : 2 / (75 * (n:ℝ)) ≤ flatQ n := flatQ_ge n hn1
    have hpow : ρ ^ n = ρ * ρ ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hnpos : (0:ℝ) < n := by linarith
    have hn0 : (n:ℝ) ≠ 0 := hnpos.ne'
    have key : 2 * ρ / 75 ≤ C * ((n:ℝ) * ρ ^ n) := by
      rw [hpow]
      have h1 : 2 / (75 * (n:ℝ)) ≤ C * ρ ^ (n - 1) := le_trans hlow hb
      have h2 : (n:ℝ) * ρ * (2 / (75 * n)) ≤ (n:ℝ) * ρ * (C * ρ ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (n:ℝ) * ρ * (2 / (75 * n)) = 2 * ρ / 75 := by field_simp
      calc 2 * ρ / 75 = (n:ℝ) * ρ * (2 / (75 * n)) := h3.symm
        _ ≤ (n:ℝ) * ρ * (C * ρ ^ (n - 1)) := h2
        _ = C * ((n:ℝ) * (ρ * ρ ^ (n - 1))) := by ring
    linarith

end LatticeGaugeToeplitzTailSplit

#print axioms LatticeGaugeToeplitzTailSplit.split
#print axioms LatticeGaugeToeplitzTailSplit.split_unique
#print axioms LatticeGaugeToeplitzTailSplit.tail_sum_le
#print axioms LatticeGaugeToeplitzTailSplit.tailPart_sum_le
#print axioms LatticeGaugeToeplitzTailSplit.qform_split
#print axioms LatticeGaugeToeplitzTailSplit.cform_split
#print axioms LatticeGaugeToeplitzTailSplit.flatQ_two
#print axioms LatticeGaugeToeplitzTailSplit.flat_row_sum_lt
#print axioms LatticeGaugeToeplitzTailSplit.flatQ_ge
#print axioms LatticeGaugeToeplitzTailSplit.flat_not_uniform_geometric
