/-
  Companion to `Principia.PadicHeight.Valuation5`.

  Context (all geometry and p-adic analysis stays outside Lean; only the
  arithmetic/combinatorial core is formalised here).

  For a prime p ≥ 5 let, over `F_p[A,B]`,
      φ_p(x) = f(x^p),   ψ_p(x) = g(x^p)
  be the p-division polynomials mod p (`f` monic of degree p in X = x^p,
  `g` of degree (p-1)/2).  Weighted homogeneity (A : 4, B : 6, X : 2p) plus
  `2p ≡ 0` and `2p² ≡ 0` in characteristic p give Euler's identity
      4A·∂_A f + 6B·∂_B f = 0,
  hence `A ∣ ∂_B f`;  write `∂_B f = A·ũ`.  The invariant ρ of the deformation
  law satisfies  ρ(x̄) = -ũ(x̄)/(4 f(x̄)),  so ρ ≠ 0 ⟺ ũ(x̄) ≠ 0, i.e.
      Res_X(ũ, g) ≠ 0 at the curve.
  `Res_X(ũ, g)` is weighted homogeneous of weight (p-1)(p²+p-4) - 2(p-1)
  = (p-1)(p-2)(p+3) = 12·m p, and at the multiplicative degeneration the
  Newton polygon of `f` (root valuations 0,1,1,2,2,…,n,n with n = (p-1)/2)
  gives ord_Δ Res ≥ Σ_{j=1}^{n} (j(p-j) - 1) = m p.  Divisibility plus equal
  weight then forces `Res = c·Δ^(m p)`: the dichotomy "ρ never 0, or ρ ≡ 0".

  This file formalises:
    * the weight bookkeeping that produces `m p` (`weight_split`, `twelve_dvd_weight`),
    * the cusp sum  Σ_{j=1}^n (j(p-j) - 1) = m p  (`sum_pole_orders`, `cusp_sum_eq_m`),
    * the Newton polygon inequality  j(s-j) ≤ ⌊s/2⌋⌈s/2⌉  (`mul_compl_le_half_mul_half`),
    * the non-vanishing of the pole orders mod p (`not_dvd_half_mul_half`),
    * the "equal degree + divisibility ⇒ constant multiple" step, in its
      univariate polynomial shadow (`eq_C_mul_of_dvd_of_natDegree_eq`),
    * the values m 5 … m 23 = 8, 25, 105, 176, 400, 561, 1001.
-/
import Mathlib

namespace PadicHeight

open Finset

/-- The exponent of the discriminant predicted by the weight count:
`m p = (p-1)(p-2)(p+3)/12`, written as an integer-valued function of `p`. -/
def m (p : ℤ) : ℚ := (p - 1) * (p - 2) * (p + 3) / 12

/-- The weight identity: the weight `(p-1)(p²+p-4)` of `Res_X(∂_B f, g)` splits as
the weight `2(p-1)` of `A^((p-1)/2)` plus `12·m p`. -/
theorem weight_split (p : ℤ) :
    (p - 1) * (p ^ 2 + p - 4) = 2 * (p - 1) + (p - 1) * (p - 2) * (p + 3) := by
  ring

/-- `12 ∣ (p-1)(p-2)(p+3)` whenever `p` is odd and not divisible by `3`;
so `m p` is an integer for every prime `p ≥ 5`. -/
theorem twelve_dvd_weight (p a b : ℤ) (h2 : p = 2 * a + 1)
    (h3 : p = 3 * b + 1 ∨ p = 3 * b + 2) :
    (12 : ℤ) ∣ (p - 1) * (p - 2) * (p + 3) := by
  have h4 : (4 : ℤ) ∣ (p - 1) * (p - 2) * (p + 3) := by
    refine ⟨a * (a + 2) * (p - 2), ?_⟩
    subst h2; ring
  have h3' : (3 : ℤ) ∣ (p - 1) * (p - 2) * (p + 3) := by
    rcases h3 with h | h
    · exact ⟨b * (p - 2) * (p + 3), by subst h; ring⟩
    · exact ⟨(p - 1) * b * (p + 3), by subst h; ring⟩
  have hco : IsCoprime (4 : ℤ) 3 := by
    rw [Int.isCoprime_iff_gcd_eq_one]; norm_num
  have := hco.mul_dvd h4 h3'
  norm_num at this ⊢
  exact this

/-- `Σ_{i<n} i(i+1) = (n-1)n(n+1)/3`, in the cleared form. -/
theorem three_mul_sum_mul_succ (n : ℕ) :
    3 * ∑ i ∈ range n, ((i : ℤ) * (i + 1)) = ((n : ℤ) - 1) * n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- `2·Σ_{i<n}(i+1) = n(n+1)`. -/
theorem two_mul_sum_succ (n : ℕ) :
    2 * ∑ i ∈ range n, ((i : ℤ) + 1) = (n : ℤ) * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- The sum of the pole orders at the cusp:
`Σ_{j=1}^{n} j(p-j) = n(n+1)(2n+1)/3` for `p = 2n+1`
(the same number as `v_t(Res_X(f,g)) = p(p²-1)/12`). -/
theorem sum_pole_orders (n : ℕ) :
    3 * ∑ i ∈ range n, (((i : ℤ) + 1) * (2 * (n : ℤ) + 1 - (i + 1)))
      = (n : ℤ) * (n + 1) * (2 * n + 1) := by
  have key : ∑ i ∈ range n, (((i : ℤ) + 1) * (2 * (n : ℤ) + 1 - (i + 1)))
      = 2 * (n : ℤ) * (∑ i ∈ range n, ((i : ℤ) + 1)) - ∑ i ∈ range n, ((i : ℤ) * (i + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [key]
  linear_combination 3 * (n : ℤ) * two_mul_sum_succ n - three_mul_sum_mul_succ n

/-- The cusp estimate produces exactly `m p`:
`Σ_{j=1}^{n} (j(p-j) - 1) = m p` for `p = 2n+1`. -/
theorem cusp_sum_eq_m (n : ℤ) :
    (n * (n + 1) * (2 * n + 1) - 3 * n) = n * (2 * n - 1) * (n + 2) := by
  ring

/-- `12 * m (2n+1) = 3 * (n(2n-1)(n+2)) * 4 / 3`: the bridge between the cusp sum
and the weight count, in cleared form. -/
theorem twelve_m_eq (n : ℤ) :
    ((2 * n + 1) - 1) * ((2 * n + 1) - 2) * ((2 * n + 1) + 3)
      = 4 * (n * (2 * n - 1) * (n + 2)) := by
  ring

/-- Newton polygon inequality: `j(s-j) ≤ ⌊s/2⌋·⌈s/2⌉` for `0 ≤ j ≤ s`.
This is what makes `min_i (v(F_i) + i·j) = j(p-j)` the true pole order. -/
theorem mul_compl_le_half_mul_half (s j : ℕ) (h : j ≤ s) :
    j * (s - j) ≤ (s / 2) * ((s + 1) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k, s = j + k := ⟨s - j, by omega⟩
  have hsj : s - j = k := by omega
  rw [hsj]
  rcases Nat.even_or_odd s with ⟨a, ha⟩ | ⟨a, ha⟩
  · have h1 : s / 2 = a := by omega
    have h2 : (s + 1) / 2 = a := by omega
    rw [h1, h2]
    have hz : (j : ℤ) * (k : ℤ) ≤ (a : ℤ) * (a : ℤ) := by
      have e : (j : ℤ) + (k : ℤ) = 2 * (a : ℤ) := by
        exact_mod_cast (by omega : j + k = 2 * a)
      have hk' : (k : ℤ) = 2 * (a : ℤ) - (j : ℤ) := by linarith
      rw [hk']
      nlinarith [sq_nonneg ((a : ℤ) - (j : ℤ))]
    exact_mod_cast hz
  · have h1 : s / 2 = a := by omega
    have h2 : (s + 1) / 2 = a + 1 := by omega
    rw [h1, h2]
    have hz : (j : ℤ) * (k : ℤ) ≤ (a : ℤ) * ((a : ℤ) + 1) := by
      have e : (j : ℤ) + (k : ℤ) = 2 * (a : ℤ) + 1 := by
        exact_mod_cast (by omega : j + k = 2 * a + 1)
      have hk' : (k : ℤ) = 2 * (a : ℤ) + 1 - (j : ℤ) := by linarith
      have hnn : 0 ≤ ((a : ℤ) - (j : ℤ)) * ((a : ℤ) + 1 - (j : ℤ)) := by
        have hd : (j : ℤ) - (a : ℤ) ≤ 0 ∨ 1 ≤ (j : ℤ) - (a : ℤ) := by omega
        rcases hd with hd | hd
        · exact mul_nonneg (by linarith) (by linarith)
        · nlinarith
      rw [hk']
      nlinarith [hnn]
    exact_mod_cast hz

/-- The pole orders `⌊s/2⌋·⌈s/2⌉` of the coefficients of `f` at the cusp are never
divisible by `p` for `1 ≤ s ≤ p - 1`; this is what makes the `t`-derivative drop the
valuation by exactly one. -/
theorem not_dvd_half_mul_half (p s : ℕ) (hp : p.Prime) (h1 : 2 ≤ s) (h2 : s ≤ p - 1) :
    ¬ p ∣ (s / 2) * ((s + 1) / 2) := by
  intro hdvd
  have hp2 : 2 ≤ p := hp.two_le
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have hpos : 0 < s / 2 := by omega
    have hle := Nat.le_of_dvd hpos h
    omega
  · have hpos : 0 < (s + 1) / 2 := by omega
    have hle := Nat.le_of_dvd hpos h
    omega

/-- The final step of the dichotomy, in its univariate shadow: a nonzero polynomial
divisible by `d` and of the same degree as `d` is a nonzero constant times `d`. -/
theorem eq_C_mul_of_dvd_of_natDegree_eq {K : Type*} [Field K] {r d : Polynomial K}
    (hd : d ∣ r) (hr : r ≠ 0) (hdeg : r.natDegree = d.natDegree) :
    ∃ c : K, c ≠ 0 ∧ r = Polynomial.C c * d := by
  obtain ⟨s, hs⟩ := hd
  have hd0 : d ≠ 0 := by
    rintro rfl; simp at hs; exact hr hs
  have hs0 : s ≠ 0 := by
    rintro rfl; simp at hs; exact hr hs
  have hdegs : s.natDegree = 0 := by
    have := Polynomial.natDegree_mul hd0 hs0
    rw [hs] at hdeg
    omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegs
  refine ⟨c, ?_, ?_⟩
  · rintro rfl; simp at hc; exact hs0 hc.symm
  · rw [hs, ← hc]; ring

/-- The predicted exponents for the primes where the resultant identity has been
verified by computation. -/
theorem m_values :
    m 5 = 8 ∧ m 7 = 25 ∧ m 11 = 105 ∧ m 13 = 176 ∧ m 17 = 400 ∧ m 19 = 561
      ∧ m 23 = 1001 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · unfold m; norm_num

#print axioms weight_split
#print axioms twelve_dvd_weight
#print axioms three_mul_sum_mul_succ
#print axioms two_mul_sum_succ
#print axioms sum_pole_orders
#print axioms cusp_sum_eq_m
#print axioms twelve_m_eq
#print axioms mul_compl_le_half_mul_half
#print axioms not_dvd_half_mul_half
#print axioms eq_C_mul_of_dvd_of_natDegree_eq
#print axioms m_values

end PadicHeight
