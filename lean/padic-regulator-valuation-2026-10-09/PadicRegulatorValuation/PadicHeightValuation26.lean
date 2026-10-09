/-
The leading term of the p-adic L-function, read through the valuation of the
p-adic regulator: the closed arithmetic behind the uniform bound

    v_p(L_p^{(r)}(E, chi^0)/r!) = 2*v_p(1 - alpha^{-1}) + v_p(Reg_p) >= r,

its sharp cases, the fact that it bounds the rank from above and not from below,
and the rank-two determinant criterion on the split side.

Every statement here is about integers, a prime element of a commutative ring, or
2x2 linear algebra over a field.  The inputs from the p-adic theory (the four
cases of the main theorem, the p-adic BSD formula) enter as hypotheses.
-/
import Mathlib

namespace PadicHeightLeading

/-! ### 1. The four cases, and the uniform bound `r ≤ 2*vE + vR` -/

/-- The admissible shapes of `(vE, vR)` in terms of the rank `r`:
`vE = v_p(1 - alpha^{-1})` is `0` at a non-anomalous prime and `1` at an anomalous
one (the Euler-factor lemma), and `vR = v_p(Reg_p)` obeys the main theorem:
`vR ≥ r` in the non-anomalous case, `vR ≥ max (r-2) 0` in the split case,
`vR = -1` in the non-split case of rank one, and `vR = (r-2) + vT` with `vT ≥ 0`
(the valuation of a Schur complement) in the non-split case of rank `≥ 2`. -/
def Admissible (r vE vR : ℤ) : Prop :=
  (vE = 0 ∧ r ≤ vR)
  ∨ (vE = 1 ∧ r - 2 ≤ vR ∧ 0 ≤ vR)
  ∨ (vE = 1 ∧ r = 1 ∧ vR = -1)
  ∨ (vE = 1 ∧ 2 ≤ r ∧ ∃ vT : ℤ, 0 ≤ vT ∧ vR = (r - 2) + vT)

/-- **The uniform bound.**  In all four cases the leading term of the p-adic
L-function has valuation at least the rank. -/
theorem leading_val_ge_rank {r vE vR : ℤ} (h : Admissible r vE vR) :
    r ≤ 2 * vE + vR := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, vT, h3, h4⟩
  · omega
  · omega
  · omega
  · omega

/-- The same read as a bound on the rank: the valuation of the leading term is an
**upper** bound for the rank. -/
theorem rank_le_leading_val {r vE vR vL : ℤ} (h : Admissible r vE vR)
    (hL : vL = 2 * vE + vR) : r ≤ vL := by
  rw [hL]; exact leading_val_ge_rank h

/-- On the non-split anomalous side of rank one the bound is an equality. -/
theorem leading_val_eq_rank_of_nonsplit_rank_one {vE vR : ℤ}
    (h1 : vE = 1) (h2 : vR = -1) : 2 * vE + vR = 1 := by omega

/-- On the split anomalous side of rank at most one the bound is never attained:
the leading term is divisible by `p^2` whatever the rank does. -/
theorem leading_val_gt_rank_of_split_le_one {r vE vR : ℤ}
    (h1 : vE = 1) (h2 : 0 ≤ vR) (hr : r ≤ 1) : r < 2 * vE + vR := by omega

/-- The bound is attained in the non-anomalous case exactly when `v_p(Reg_p) = r`. -/
theorem leading_val_eq_rank_iff_of_normal {r vE vR : ℤ} (h1 : vE = 0) :
    2 * vE + vR = r ↔ vR = r := by omega

/-! ### 2. No lower bound for the rank

The bound of §1 cannot be reversed: one and the same value of the leading
valuation is admissible with two different ranks.  A lower bound for `r` would
need an upper bound for `v_p(Reg_p)`, which is the non-degeneracy of the Schur
complement and is not decided by any of the data above. -/

/-- Two admissible triples with the same leading valuation `2` and ranks `1` and `2`:
a split anomalous prime of rank one with `v_p(Reg_p) = 0`, and a non-anomalous
prime of rank two with `v_p(Reg_p) = 2`. -/
theorem exists_two_ranks_same_leading_val :
    ∃ vE₁ vR₁ vE₂ vR₂ : ℤ,
      Admissible 1 vE₁ vR₁ ∧ Admissible 2 vE₂ vR₂ ∧
      2 * vE₁ + vR₁ = 2 * vE₂ + vR₂ := by
  refine ⟨1, 0, 0, 2, ?_, ?_, by norm_num⟩
  · exact Or.inr (Or.inl ⟨rfl, by norm_num, le_refl 0⟩)
  · exact Or.inl ⟨rfl, by norm_num⟩

/-- Sharper: the value `2` of the leading valuation is admissible with every rank
`r ≤ 2`, so nothing about `r` beyond `r ≤ 2` can be read off from it. -/
theorem admissible_leading_two_of_rank_le_two {r : ℤ} (h0 : 0 ≤ r) (h2 : r ≤ 2) :
    ∃ vE vR : ℤ, Admissible r vE vR ∧ 2 * vE + vR = 2 := by
  refine ⟨1, 0, Or.inr (Or.inl ⟨rfl, by omega, le_refl 0⟩), by norm_num⟩

/-! ### 3. The rank-two determinant criterion on the split side

In the split case the height matrix is integral and its reduction vanishes on the
hyperplane `ker χ`; in rank two that reduction is `[[a, b], [b, 0]]`, so the
determinant is `-b²` and the regulator is a unit exactly when the off-diagonal
entry is one.  The first statement is the divisibility step for a general prime
element, the second the rank-two case of `ρ₁ = 2 ⟺ v_p(Reg_p) = 0`. -/

/-- With `π` prime and `π ∣ c`, the determinant `a*c - b*b` of a symmetric `2×2`
matrix is divisible by `π` if and only if the off-diagonal entry is. -/
theorem prime_dvd_det_two_iff {R : Type*} [CommRing R] {π : R} (hπ : Prime π)
    {a b c : R} (hc : π ∣ c) : π ∣ a * c - b * b ↔ π ∣ b := by
  constructor
  · intro h
    have hb : π ∣ b * b := by
      have h2 : π ∣ a * c := hc.mul_left a
      have := dvd_sub h2 h
      simpa using this
    exact (hπ.dvd_mul.mp hb).elim id id
  · intro h
    exact dvd_sub (hc.mul_left a) (h.mul_right b)

/-- The reduced height matrix in rank two, `[[a, b], [b, 0]]`, is nonsingular
exactly when `b ≠ 0`: over the residue field `ρ₁ = 2 ⟺ v_p(Reg_p) = 0`. -/
theorem det_two_split_ne_zero_iff {K : Type*} [Field K] (a b : K) :
    a * 0 - b * b ≠ 0 ↔ b ≠ 0 := by
  simp

/-! ### 4. `(χ, γ)` onto is the same as a nonvanishing determinant

The local criterion for `ρ₁ = 2` in rank two: the pair of linear forms
`(χ, γ) : Λ → F_p²` is onto if and only if the `2×2` determinant of their values
on a basis is nonzero.  Both directions are proved by hand, so that the statement
is about the two forms and not about a matrix API. -/

/-- Auxiliary: over a field, a nonzero pair of coefficients hits `1`. -/
theorem exists_pair_eq_one {K : Type*} [Field K] {a b : K} (h : ¬(a = 0 ∧ b = 0)) :
    ∃ X Y : K, a * X - b * Y = 1 := by
  rcases eq_or_ne a 0 with ha | ha
  · have hb : b ≠ 0 := by tauto
    refine ⟨0, -b⁻¹, ?_⟩
    rw [ha, mul_zero, zero_sub, mul_neg, neg_neg, mul_inv_cancel₀ hb]
  · exact ⟨a⁻¹, 0, by rw [mul_inv_cancel₀ ha, mul_zero, sub_zero]⟩

/-- Surjectivity of `(s, t) ↦ (c₁ s + c₂ t, g₁ s + g₂ t)` is equivalent to
`c₁ g₂ - c₂ g₁ ≠ 0`. -/
theorem onto_iff_det_ne_zero {K : Type*} [Field K] (c₁ c₂ g₁ g₂ : K) :
    (∀ X Y : K, ∃ s t : K, c₁ * s + c₂ * t = X ∧ g₁ * s + g₂ * t = Y)
      ↔ c₁ * g₂ - c₂ * g₁ ≠ 0 := by
  constructor
  · intro hsurj hdet
    by_cases hcg : c₂ = 0 ∧ g₂ = 0
    · obtain ⟨hc2, hg2⟩ := hcg
      by_cases hcg1 : c₁ = 0 ∧ g₁ = 0
      · obtain ⟨hc1, hg1⟩ := hcg1
        obtain ⟨s, t, hs, _⟩ := hsurj 1 0
        rw [hc1, hc2] at hs; simp at hs
      · -- the form `(g₁, -c₁)` kills the image
        obtain ⟨X, Y, hXY⟩ := exists_pair_eq_one (a := g₁) (b := c₁) (by tauto)
        obtain ⟨s, t, hs, ht⟩ := hsurj X Y
        rw [← hs, ← ht, hc2, hg2] at hXY
        have : (0 : K) = 1 := by linear_combination hXY
        exact zero_ne_one this
    · -- the form `(g₂, -c₂)` kills the image, by the determinant relation
      obtain ⟨X, Y, hXY⟩ := exists_pair_eq_one (a := g₂) (b := c₂) (by tauto)
      obtain ⟨s, t, hs, ht⟩ := hsurj X Y
      rw [← hs, ← ht] at hXY
      have : (0 : K) = 1 := by linear_combination hXY - s * hdet
      exact zero_ne_one this
  · intro hdet X Y
    have hd : c₁ * g₂ - c₂ * g₁ ≠ 0 := hdet
    refine ⟨(X * g₂ - Y * c₂) / (c₁ * g₂ - c₂ * g₁),
            (Y * c₁ - X * g₁) / (c₁ * g₂ - c₂ * g₁), ?_, ?_⟩
    · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hd]; ring
    · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hd]; ring

/-- The two criteria agree: in rank two the reduced height matrix is nonsingular
exactly when the pair of local forms is onto (both sides being `≠ 0` of the same
determinant up to the unit factor supplied by the closed form of the height). -/
theorem onto_iff_reduced_det_ne_zero {K : Type*} [Field K] (c₁ c₂ g₁ g₂ b : K)
    (hb : b = c₁ * g₂ - c₂ * g₁) :
    (∀ X Y : K, ∃ s t : K, c₁ * s + c₂ * t = X ∧ g₁ * s + g₂ * t = Y)
      ↔ (0 : K) * 0 - b * b ≠ 0 := by
  rw [det_two_split_ne_zero_iff, hb]
  exact onto_iff_det_ne_zero c₁ c₂ g₁ g₂

end PadicHeightLeading

#print axioms PadicHeightLeading.leading_val_ge_rank
#print axioms PadicHeightLeading.rank_le_leading_val
#print axioms PadicHeightLeading.leading_val_eq_rank_of_nonsplit_rank_one
#print axioms PadicHeightLeading.leading_val_gt_rank_of_split_le_one
#print axioms PadicHeightLeading.leading_val_eq_rank_iff_of_normal
#print axioms PadicHeightLeading.exists_two_ranks_same_leading_val
#print axioms PadicHeightLeading.admissible_leading_two_of_rank_le_two
#print axioms PadicHeightLeading.prime_dvd_det_two_iff
#print axioms PadicHeightLeading.det_two_split_ne_zero_iff
#print axioms PadicHeightLeading.exists_pair_eq_one
#print axioms PadicHeightLeading.onto_iff_det_ne_zero
#print axioms PadicHeightLeading.onto_iff_reduced_det_ne_zero
