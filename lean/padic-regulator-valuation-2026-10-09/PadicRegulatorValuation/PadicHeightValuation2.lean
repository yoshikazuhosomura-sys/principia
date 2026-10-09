import Mathlib

/-!
# The split-anomalous criterion for the outside-`p` part of the cyclotomic `p`-adic height

Setting.  `E/ℚ` has good ordinary reduction at a prime `p ≥ 5` with `#E(𝔽_p) = p` (anomalous),
`P' ∈ E(ℚ)` reduces to a point of exact order `p`, and `P = pP'`.  Writing
`x(P) = α/d(P)²`, `y(P) = β/d(P)³` in lowest terms, the outside-`p` part of the `p`-adic height
is `A = ∑_{ℓ≠p} n_ℓ logₚ ℓ` with `∏ ℓ^{n_ℓ} = ±α/β`, and its valuation `c = v_p(A)` satisfies
`c ≥ 2 ↔ p² ∣ α^(p-1) - β^(p-1)`.

The arithmetic content of the step `e ≥ 2 ⟹ c ≥ 2` is isolated here.  Three inputs from the
geometry are used as hypotheses, not proved here:

* `α/β = φ_p(P')/ω_p(P')` up to a factor `d(P')^{p²}` (division polynomials);
* `ω_p² ≡ φ_p³ (mod p^e)`, which is the Weierstrass equation multiplied by `ψ_p^6` together with
  `p^e ∣ ψ_p(P')`;
* `φ_p mod p` is a polynomial in `x^p` (this is `[p] = V ∘ F` in characteristic `p`), so that the
  value `φ_p(P') mod p²` depends only on `x(P') mod p`.

Given these, the file proves:

* `fermatQuot_sub_iff_of_sq_eq_cube` : if `p² ∣ b² - a³` then
  `p² ∣ a^(p-1) - b^(p-1) ↔ p² ∣ a^(p-1) - 1`.  In words: modulo `p²` the Fermat quotient of
  `a/b` vanishes exactly when the Fermat quotient of `a` does.  This is the step that turns
  `c ≥ 2` into the single local quantity `λ = qₚ(φ_p)/2`.
* `eval_sub_eval_dvd_sq` : a polynomial whose derivative is `≡ 0 (mod p)` at `x` takes the same
  value mod `p²` at `x` and at `x + pk`.
* `dvd_sq_pow_totient` and `fermatQuot_mul_pow_sq` : the denominator factor `d^{p²}` does not
  change a Fermat quotient.

Everything is over `ℤ`; no `p`-adic analysis enters.
-/

namespace PadicHeight

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- Fermat's little theorem in quotient form: `a^(p-1) = 1 + p * A` for `p ∤ a`. -/
theorem exists_fermatQuot {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : ∃ A : ℤ, a ^ (p - 1) = 1 + p * A := by
  have h1 : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have h2 : ((a : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h1
  have h3 : (((a ^ (p - 1) - 1 : ℤ)) : ZMod p) = 0 := by push_cast [h2]; ring
  obtain ⟨A, hA⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h3
  exact ⟨A, by linarith [hA]⟩

/-- `p` does not divide `2` when `p ≠ 2`. -/
theorem not_dvd_two (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro hd
  have h1 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
  have h2 : 2 ≤ p := hp.out.two_le
  have : (p : ℤ) = 2 := by
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h2
    omega
  exact hp2 (by exact_mod_cast this)

/-- **The criterion.**  If `b² ≡ a³ (mod p²)` (the Weierstrass equation at a point where the
`p`-division polynomial is divisible by `p^e`, `e ≥ 2`), then the Fermat quotient of `a/b` and
the Fermat quotient of `a` vanish together.  Concretely `q(a) = 2λ`, `q(b) = 3λ` and
`q(a/b) = -λ`, so all three vanish at once. -/
theorem fermatQuot_sub_iff_of_sq_eq_cube (hp2 : p ≠ 2) {a b A B : ℤ}
    (hA : a ^ (p - 1) = 1 + p * A) (hB : b ^ (p - 1) = 1 + p * B)
    (h : (p : ℤ) ^ 2 ∣ b ^ 2 - a ^ 3) :
    ((p : ℤ) ^ 2 ∣ a ^ (p - 1) - b ^ (p - 1)) ↔ ((p : ℤ) ^ 2 ∣ a ^ (p - 1) - 1) := by
  have hp0 : (p : ℤ) ≠ 0 := by
    have : 0 < p := hp.out.pos
    exact_mod_cast this.ne'
  -- step 1 : `p ∣ 2B - 3A`
  have hmod : (a ^ 3) ≡ (b ^ 2) [ZMOD ((p : ℤ) ^ 2)] := Int.modEq_iff_dvd.2 h
  have hpow : (p : ℤ) ^ 2 ∣ (b ^ 2) ^ (p - 1) - (a ^ 3) ^ (p - 1) :=
    Int.modEq_iff_dvd.1 (hmod.pow (p - 1))
  have hrw1 : (b ^ 2) ^ (p - 1) = (1 + p * B) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, hB]
  have hrw2 : (a ^ 3) ^ (p - 1) = (1 + p * A) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul, hA]
  rw [hrw1, hrw2] at hpow
  have hexp : (1 + (p : ℤ) * B) ^ 2 - (1 + (p : ℤ) * A) ^ 3
      = p * (2 * B - 3 * A) + p ^ 2 * (B ^ 2 - 3 * A ^ 2 - p * A ^ 3) := by ring
  rw [hexp] at hpow
  have hstep : (p : ℤ) ^ 2 ∣ p * (2 * B - 3 * A) := by
    have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ 2 * (B ^ 2 - 3 * A ^ 2 - p * A ^ 3) := dvd_mul_right _ _
    simpa using dvd_sub hpow h2
  have key : (p : ℤ) ∣ 2 * B - 3 * A := by
    rw [sq] at hstep
    exact (mul_dvd_mul_iff_left hp0).1 hstep
  -- step 2 : rewrite both sides
  have e1 : a ^ (p - 1) - b ^ (p - 1) = p * (A - B) := by rw [hA, hB]; ring
  have e2 : a ^ (p - 1) - 1 = p * A := by rw [hA]; ring
  rw [e1, e2, sq, mul_dvd_mul_iff_left hp0, mul_dvd_mul_iff_left hp0]
  have h2 : (2 : ℤ) * (A - B) = -A - (2 * B - 3 * A) := by ring
  have hp2' : ¬ (p : ℤ) ∣ 2 := not_dvd_two hp2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  constructor
  · intro hAB
    have hneg : (p : ℤ) ∣ -A := by
      have h5 : (p : ℤ) ∣ 2 * (A - B) := hAB.mul_left 2
      rw [h2] at h5
      simpa using dvd_add h5 key
    exact (dvd_neg).1 hneg
  · intro hA0
    have h3 : (p : ℤ) ∣ 2 * (A - B) := by
      rw [h2]
      exact dvd_sub ((dvd_neg).2 hA0) key
    rcases hprime.dvd_mul.1 h3 with h4 | h4
    · exact absurd h4 hp2'
    · exact h4

/-- If the derivative of `f` is divisible by `p` at `x`, then `f` takes the same value modulo
`p²` at `x` and at `x + p k`.  Applied to `f = φ_p`, whose reduction mod `p` is a polynomial in
`x^p`, this says that `φ_p(P') mod p²` depends only on `x(P') mod p`. -/
theorem eval_sub_eval_dvd_sq (f : Polynomial ℤ) {x k : ℤ}
    (hd : (p : ℤ) ∣ f.derivative.eval x) :
    (p : ℤ) ^ 2 ∣ f.eval (x + p * k) - f.eval x := by
  obtain ⟨c, hc⟩ := f.binomExpansion x ((p : ℤ) * k)
  obtain ⟨d, hdd⟩ := hd
  refine ⟨d * k + c * k ^ 2, ?_⟩
  rw [hc, hdd]
  ring

/-- Euler: `d^{(p-1)p} ≡ 1 (mod p²)` for `p ∤ d`. -/
theorem dvd_sq_pow_totient {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) :
    (p : ℤ) ^ 2 ∣ d ^ ((p - 1) * p) - 1 := by
  obtain ⟨A, hA⟩ := exists_fermatQuot hd
  have h1 : d ^ ((p - 1) * p) = (1 + (p : ℤ) * A) ^ p := by rw [pow_mul, hA]
  have h2 : (1 + (p : ℤ) * A) ^ p - 1
      = (∑ i ∈ Finset.range p, (1 + (p : ℤ) * A) ^ i) * ((p : ℤ) * A) := by
    have := geom_sum_mul (1 + (p : ℤ) * A) p
    calc (1 + (p : ℤ) * A) ^ p - 1
        = (∑ i ∈ Finset.range p, (1 + (p : ℤ) * A) ^ i) * ((1 + (p : ℤ) * A) - 1) := this.symm
      _ = (∑ i ∈ Finset.range p, (1 + (p : ℤ) * A) ^ i) * ((p : ℤ) * A) := by ring_nf
  have h3 : (p : ℤ) ∣ ∑ i ∈ Finset.range p, (1 + (p : ℤ) * A) ^ i := by
    have : ((∑ i ∈ Finset.range p, (1 + (p : ℤ) * A) ^ i : ℤ) : ZMod p) = 0 := by
      push_cast
      simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  obtain ⟨S, hS⟩ := h3
  refine ⟨S * A, ?_⟩
  rw [h1, h2, hS]
  ring

/-- Multiplying by a `p²`-th power does not change a Fermat quotient: the denominator factor
`d(P')^{p²}` relating `α/β` to `φ_p(P')/ω_p(P')` is invisible mod `p²`. -/
theorem fermatQuot_mul_pow_sq {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) (a : ℤ) :
    (p : ℤ) ^ 2 ∣ (a * d ^ (p ^ 2)) ^ (p - 1) - a ^ (p - 1) := by
  have hbase : (p : ℤ) ^ 2 ∣ d ^ ((p - 1) * p) - 1 := dvd_sq_pow_totient hd
  obtain ⟨Y, hY⟩ := hbase
  have hX : d ^ ((p - 1) * p ^ 2) - 1
      = (d ^ ((p - 1) * p) - 1) * (∑ i ∈ Finset.range p, (d ^ ((p - 1) * p)) ^ i) := by
    have := geom_sum_mul (d ^ ((p - 1) * p)) p
    calc d ^ ((p - 1) * p ^ 2) - 1
        = (d ^ ((p - 1) * p)) ^ p - 1 := by rw [← pow_mul]; ring_nf
      _ = (∑ i ∈ Finset.range p, (d ^ ((p - 1) * p)) ^ i) * (d ^ ((p - 1) * p) - 1) := this.symm
      _ = (d ^ ((p - 1) * p) - 1) * (∑ i ∈ Finset.range p, (d ^ ((p - 1) * p)) ^ i) := by ring
  have hfac : (a * d ^ (p ^ 2)) ^ (p - 1) - a ^ (p - 1)
      = a ^ (p - 1) * (d ^ ((p - 1) * p ^ 2) - 1) := by
    rw [mul_pow, ← pow_mul]
    ring_nf
  rw [hfac, hX, hY]
  exact ⟨a ^ (p - 1) * Y * (∑ i ∈ Finset.range p, (d ^ ((p - 1) * p)) ^ i), by ring⟩

end PadicHeight

#print axioms PadicHeight.exists_fermatQuot
#print axioms PadicHeight.not_dvd_two
#print axioms PadicHeight.fermatQuot_sub_iff_of_sq_eq_cube
#print axioms PadicHeight.eval_sub_eval_dvd_sq
#print axioms PadicHeight.dvd_sq_pow_totient
#print axioms PadicHeight.fermatQuot_mul_pow_sq
