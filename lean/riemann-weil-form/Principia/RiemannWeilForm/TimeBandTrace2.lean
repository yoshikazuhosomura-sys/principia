import Mathlib

/-!
# The cluster identity behind the `1/k` law for the trace of a time–band operator

Let `A = P B P` be a time–band operator and `a_k = tr (A^k - A^{k+1})`; write `c` for the
product of the window length and the bandwidth.  After the reduction of `tr A^k` to a
`(k-1)`-fold oscillatory integral, the law `a_k ~ (log c)/(π² k)` becomes a statement about
how `k` points on a line split into clusters: the coefficient of `1/c` in the part of the
integral where the `k` points have diameter larger than `c` is a sum over the ways of
cutting the cyclic word `1 2 … k` into `m` arcs, each cut weighted by an amplitude `w m`
that depends on `m` alone.

A cut into arcs of sizes `k₁, …, k_m` carries the weight `∏ⱼ 2 ^ (1 - kⱼ) = 2 ^ (m - k)`,
the same for every cut, so only the number of cuts survives:

  `clusterCoeff k m = (k.choose m) / 2 ^ (k - m)`.

The amplitude vanishes for odd `m`, and for `m = 2 n` it is `oddH n / 4 ^ (n - 1)` with
`oddH n = 1 + 1/3 + ⋯ + 1/(2 n - 1)`.  With those two ingredients the `1/k` law is the
identity

  `∑_{m} clusterCoeff k m * clusterAmp m = harm (k - 1)`,

equivalently `∑_{n ≥ 1} (k.choose (2 n)) * oddH n = 2 ^ (k - 2) * harm (k - 1)`.

Contents.

* `TimeBand.cluster_identity` — the identity itself, checked exactly over `ℚ` for
  `2 ≤ k ≤ 12`.
* `TimeBand.binom_oddH_identity` — its reduced binomial form, same range.
* `TimeBand.even_binom_sum` — the algebraic step behind the general proof: the even part of
  the binomial expansion, `(1+x)^k + (1-x)^k = 2 ∑_{j even} C(k,j) x^j`, for every `k`.
* `TimeBand.sum_odd_choose` — `∑_{j odd} C(N+1,j) = 2^N`, for every `N`; this is what makes
  the auxiliary sum `∑_n C(k,2n)/(2n+1)` collapse to `2^k/(k+1)` in the induction step of
  the general identity.
-/

namespace TimeBand

open Finset

/-- `oddH n = 1 + 1/3 + ⋯ + 1/(2 n - 1)`. -/
def oddH (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (1 : ℚ) / (2 * i + 1)

/-- `harm n = 1 + 1/2 + ⋯ + 1/n`. -/
def harm (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (1 : ℚ) / (i + 1)

/-- The weight of the cuts of the cyclic word `1 2 … k` into `m` arcs. -/
def clusterCoeff (k m : ℕ) : ℚ := (k.choose m : ℚ) / 2 ^ (k - m)

/-- The amplitude of a configuration of `m` clusters. -/
def clusterAmp (m : ℕ) : ℚ := if m % 2 = 0 then oddH (m / 2) / 4 ^ (m / 2 - 1) else 0

/-- `clusterAmp` vanishes at `0` and `1`, so summing over `range (k+1)` is the same as
summing over `2 ≤ m ≤ k`. -/
theorem clusterAmp_zero : clusterAmp 0 = 0 := by norm_num [clusterAmp, oddH]

theorem clusterAmp_one : clusterAmp 1 = 0 := by norm_num [clusterAmp]

/-- The cluster identity, checked exactly over `ℚ` for `2 ≤ k ≤ 12`. -/
theorem cluster_identity :
    (∑ m ∈ Finset.range 3, clusterCoeff 2 m * clusterAmp m = harm 1)
  ∧ (∑ m ∈ Finset.range 4, clusterCoeff 3 m * clusterAmp m = harm 2)
  ∧ (∑ m ∈ Finset.range 5, clusterCoeff 4 m * clusterAmp m = harm 3)
  ∧ (∑ m ∈ Finset.range 6, clusterCoeff 5 m * clusterAmp m = harm 4)
  ∧ (∑ m ∈ Finset.range 7, clusterCoeff 6 m * clusterAmp m = harm 5)
  ∧ (∑ m ∈ Finset.range 8, clusterCoeff 7 m * clusterAmp m = harm 6)
  ∧ (∑ m ∈ Finset.range 9, clusterCoeff 8 m * clusterAmp m = harm 7)
  ∧ (∑ m ∈ Finset.range 10, clusterCoeff 9 m * clusterAmp m = harm 8)
  ∧ (∑ m ∈ Finset.range 11, clusterCoeff 10 m * clusterAmp m = harm 9)
  ∧ (∑ m ∈ Finset.range 12, clusterCoeff 11 m * clusterAmp m = harm 10)
  ∧ (∑ m ∈ Finset.range 13, clusterCoeff 12 m * clusterAmp m = harm 11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [clusterCoeff, clusterAmp, oddH, harm, Finset.sum_range_succ, Nat.choose]

/-- The reduced binomial form of the same identity, for `1 ≤ k ≤ 12`. -/
theorem binom_oddH_identity :
    (4 * ∑ n ∈ Finset.range 2, ((1:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 1 * harm 0)
  ∧ (4 * ∑ n ∈ Finset.range 3, ((2:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 2 * harm 1)
  ∧ (4 * ∑ n ∈ Finset.range 4, ((3:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 3 * harm 2)
  ∧ (4 * ∑ n ∈ Finset.range 5, ((4:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 4 * harm 3)
  ∧ (4 * ∑ n ∈ Finset.range 6, ((5:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 5 * harm 4)
  ∧ (4 * ∑ n ∈ Finset.range 7, ((6:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 6 * harm 5)
  ∧ (4 * ∑ n ∈ Finset.range 8, ((7:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 7 * harm 6)
  ∧ (4 * ∑ n ∈ Finset.range 9, ((8:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 8 * harm 7)
  ∧ (4 * ∑ n ∈ Finset.range 10, ((9:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 9 * harm 8)
  ∧ (4 * ∑ n ∈ Finset.range 11, ((10:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 10 * harm 9)
  ∧ (4 * ∑ n ∈ Finset.range 12, ((11:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 11 * harm 10)
  ∧ (4 * ∑ n ∈ Finset.range 13, ((12:ℕ).choose (2*n) : ℚ) * oddH n = 2 ^ 12 * harm 11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [oddH, harm, Finset.sum_range_succ, Nat.choose]

/-- The even part of the binomial expansion. -/
theorem even_binom_sum (x : ℚ) (k : ℕ) :
    (1 + x) ^ k + (1 - x) ^ k
      = 2 * ∑ j ∈ Finset.range (k + 1),
          (if j % 2 = 0 then (k.choose j : ℚ) * x ^ j else 0) := by
  have h1 : (1 + x) ^ k = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * x ^ j := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [mul_comm]
  have h2 : (1 - x) ^ k = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℚ) * (-x) ^ j := by
    have hx : (1 : ℚ) - x = -x + 1 := by ring
    rw [hx, add_pow]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [mul_comm]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rcases Nat.even_or_odd j with hj | hj
  · rw [if_pos (Nat.even_iff.mp hj), hj.neg_pow]; ring
  · have hj' := Nat.odd_iff.mp hj
    rw [if_neg (by omega), hj.neg_pow]; ring

/-- `∑_{j odd} C(N+1, j) = 2 ^ N`. -/
theorem sum_odd_choose (N : ℕ) :
    ∑ j ∈ Finset.range (N + 2), (if j % 2 = 1 then ((N + 1).choose j : ℚ) else 0)
      = 2 ^ N := by
  have hall : ∑ j ∈ Finset.range (N + 2), ((N + 1).choose j : ℚ) = 2 ^ (N + 1) := by
    exact_mod_cast Nat.sum_range_choose (N + 1)
  have halt : ∑ j ∈ Finset.range (N + 2), ((-1 : ℚ) ^ j * ((N + 1).choose j : ℚ)) = 0 := by
    have h := Int.alternating_sum_range_choose (n := N + 1)
    rw [if_neg (Nat.succ_ne_zero N)] at h
    exact_mod_cast h
  have key : ∀ j ∈ Finset.range (N + 2),
      (if j % 2 = 1 then ((N + 1).choose j : ℚ) else 0)
        = (((N + 1).choose j : ℚ) - (-1 : ℚ) ^ j * ((N + 1).choose j : ℚ)) / 2 := by
    intro j _
    rcases Nat.even_or_odd j with hj | hj
    · have hj' := Nat.even_iff.mp hj
      rw [if_neg (by omega), hj.neg_one_pow]; ring
    · have hj' := Nat.odd_iff.mp hj
      rw [if_pos hj', hj.neg_one_pow]; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, Finset.sum_sub_distrib, hall, halt]
  ring

end TimeBand

#print axioms TimeBand.cluster_identity
#print axioms TimeBand.binom_oddH_identity
#print axioms TimeBand.even_binom_sum
#print axioms TimeBand.sum_odd_choose
