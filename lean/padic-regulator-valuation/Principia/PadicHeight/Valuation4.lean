import Mathlib

/-!
# The Fermat quotient of the `p`-division numerator scales by `m²`

Setting (continued from `Principia.PadicHeight.Valuation`, `2` and `3`).
`E/ℚ` has good ordinary reduction at a prime `p ≥ 5` with `#E(𝔽_p) = p` (anomalous),
so every non-zero point of `E(𝔽_p)` has exact order `p`.  For `Q ∈ E(ℤ_p)` whose reduction
is non-zero, `φ_p(x(Q)) = x(pQ)·ψ_p(x(Q))²` is a `p`-adic unit, and one sets
`λ(x̄) := q_p(φ_p(x(Q)))/2`, where `q_p(u) = (u^(p-1) - 1)/p mod p` is the Fermat quotient.

The geometric input formalised here is the pair of composition rules for division
polynomials, `ψ_{mn} = ψ_n^{m²}·ψ_m(n·)` and `φ_m(X) = X^{m²}(1 + O(1/X))`, which give the
purely multiplicative identity (all letters `p`-adic units, `p ∤ m`)

  `φ_p(x(mQ)) · ψ_m(x(Q))^{2p²} = φ_p(x(Q))^{m²} · (1 + p²k)`,

because `1/x(pQ)` has valuation `≥ 2`.  `fermatQuot_scale` turns this into
`q_p(φ_p(x(mQ))) = m²·q_p(φ_p(x(Q)))`, i.e. `λ(m x̄) = m²·λ(x̄)`; in particular `λ` vanishes
at one non-zero class of `E(𝔽_p)` iff it vanishes at all of them (`fermatQuot_scale_zero_iff`).

The second half is the linear algebra behind the regulator bound: if every entry of the
height matrix of a subgroup of index `p` is divisible by `p` and one column is divisible by
`p²`, the determinant gains one extra power of `p` (`pow_succ_dvd_det_of_col`), which is the
step `v_p(Reg_p) ≥ 2r - 2 - ρ` for `ρ` the `𝔽_p`-rank of the reduced height pairing.

No analysis and no geometry enter: everything below is an identity in `ℤ`.
-/

namespace PadicHeight

/-- First-order binomial ledger: `x² ∣ (1+x)^n - 1 - n·x`. -/
theorem sq_dvd_one_add_pow_sub (x : ℤ) (n : ℕ) :
    x ^ 2 ∣ (1 + x) ^ n - 1 - (n : ℤ) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(1 + x) * c + n, ?_⟩
      push_cast
      linear_combination (1 + x) * hc

/-- If `p ∣ n` then `(1 + p·x)^n ≡ 1 (mod p²)`: a `p`-th power has trivial Fermat quotient. -/
theorem sq_dvd_one_add_mul_pow_sub_one (p : ℤ) (x : ℤ) (n : ℕ) (h : p ∣ (n : ℤ)) :
    p ^ 2 ∣ (1 + p * x) ^ n - 1 := by
  have h1 : p ^ 2 ∣ (1 + p * x) ^ n - 1 - (n : ℤ) * (p * x) :=
    dvd_trans ⟨x ^ 2, by ring⟩ (sq_dvd_one_add_pow_sub (p * x) n)
  obtain ⟨c, hc⟩ := h
  have h2 : p ^ 2 ∣ (n : ℤ) * (p * x) := ⟨c * x, by rw [hc]; ring⟩
  have h3 : (1 + p * x) ^ n - 1
      = ((1 + p * x) ^ n - 1 - (n : ℤ) * (p * x)) + (n : ℤ) * (p * x) := by ring
  rw [h3]
  exact dvd_add h1 h2

/-- `(1 + p²k)^n ≡ 1 (mod p²)` for every exponent. -/
theorem sq_dvd_one_add_sq_mul_pow_sub_one (p k : ℤ) (n : ℕ) :
    p ^ 2 ∣ (1 + p ^ 2 * k) ^ n - 1 := by
  have hbase : (p ^ 2 * k) ^ 2 ∣ (1 + p ^ 2 * k) ^ n - 1 - (n : ℤ) * (p ^ 2 * k) :=
    sq_dvd_one_add_pow_sub (p ^ 2 * k) n
  have hdd : p ^ 2 ∣ (p ^ 2 * k) ^ 2 := ⟨k ^ 2 * p ^ 2, by ring⟩
  have h1 : p ^ 2 ∣ (1 + p ^ 2 * k) ^ n - 1 - (n : ℤ) * (p ^ 2 * k) := dvd_trans hdd hbase
  have h2 : p ^ 2 ∣ (n : ℤ) * (p ^ 2 * k) := ⟨(n : ℤ) * k, by ring⟩
  have h3 : (1 + p ^ 2 * k) ^ n - 1
      = ((1 + p ^ 2 * k) ^ n - 1 - (n : ℤ) * (p ^ 2 * k)) + (n : ℤ) * (p ^ 2 * k) := by ring
  rw [h3]
  exact dvd_add h1 h2

/-- **The `m²` scaling rule for Fermat quotients.**
`F`, `G`, `s` are `p`-adic units with Fermat quotients `qF`, `qG`, `qs`
(`F^(p-1) = 1 + p·qF`, …).  If `F·s^{2p²} = G^{m²}·(1 + p²k)` then `qF ≡ m²·qG (mod p)`.
With `F = φ_p(x(mQ))`, `G = φ_p(x(Q))`, `s = ψ_m(x(Q))` this is `λ(m x̄) = m²·λ(x̄)`. -/
theorem fermatQuot_scale (p : ℕ) (m : ℕ) (F G s k qF qG qs : ℤ) (hp : (p : ℤ) ≠ 0)
    (hF : F ^ (p - 1) = 1 + (p : ℤ) * qF)
    (hG : G ^ (p - 1) = 1 + (p : ℤ) * qG)
    (hs : s ^ (p - 1) = 1 + (p : ℤ) * qs)
    (hid : F * s ^ (2 * p ^ 2) = G ^ (m ^ 2) * (1 + (p : ℤ) ^ 2 * k)) :
    (p : ℤ) ∣ qF - (m : ℤ) ^ 2 * qG := by
  have hraise : (F * s ^ (2 * p ^ 2)) ^ (p - 1) = (G ^ (m ^ 2) * (1 + (p : ℤ) ^ 2 * k)) ^ (p - 1) := by
    rw [hid]
  have hL : (F * s ^ (2 * p ^ 2)) ^ (p - 1) = (1 + (p : ℤ) * qF) * (1 + (p : ℤ) * qs) ^ (2 * p ^ 2) := by
    rw [mul_pow, hF, ← pow_mul, mul_comm (2 * p ^ 2) (p - 1), pow_mul, hs]
  have hR : (G ^ (m ^ 2) * (1 + (p : ℤ) ^ 2 * k)) ^ (p - 1)
      = (1 + (p : ℤ) * qG) ^ (m ^ 2) * (1 + (p : ℤ) ^ 2 * k) ^ (p - 1) := by
    rw [mul_pow, ← pow_mul, mul_comm (m ^ 2) (p - 1), pow_mul, hG]
  obtain ⟨A, hA⟩ : (p : ℤ) ^ 2 ∣ (1 + (p : ℤ) * qs) ^ (2 * p ^ 2) - 1 := by
    refine sq_dvd_one_add_mul_pow_sub_one _ _ _ ⟨2 * (p : ℤ), ?_⟩
    push_cast; ring
  obtain ⟨B, hB⟩ : (p : ℤ) ^ 2 ∣ (1 + (p : ℤ) ^ 2 * k) ^ (p - 1) - 1 :=
    sq_dvd_one_add_sq_mul_pow_sub_one _ _ _
  obtain ⟨C, hC⟩ : (p : ℤ) ^ 2 ∣ (1 + (p : ℤ) * qG) ^ (m ^ 2) - 1 - ((m : ℤ) ^ 2) * ((p : ℤ) * qG) := by
    have hbase := sq_dvd_one_add_pow_sub ((p : ℤ) * qG) (m ^ 2)
    have hcast : ((m ^ 2 : ℕ) : ℤ) = (m : ℤ) ^ 2 := by push_cast; ring
    rw [hcast] at hbase
    exact dvd_trans ⟨qG ^ 2, by ring⟩ hbase
  have h' : (1 + (p : ℤ) * qF) * (1 + (p : ℤ) ^ 2 * A)
      = (1 + (m : ℤ) ^ 2 * ((p : ℤ) * qG) + (p : ℤ) ^ 2 * C) * (1 + (p : ℤ) ^ 2 * B) := by
    have e1 : (1 + (p : ℤ) * qs) ^ (2 * p ^ 2) = 1 + (p : ℤ) ^ 2 * A := by linarith [hA]
    have e2 : (1 + (p : ℤ) ^ 2 * k) ^ (p - 1) = 1 + (p : ℤ) ^ 2 * B := by linarith [hB]
    have e3 : (1 + (p : ℤ) * qG) ^ (m ^ 2)
        = 1 + (m : ℤ) ^ 2 * ((p : ℤ) * qG) + (p : ℤ) ^ 2 * C := by linarith [hC]
    rw [← e1, ← e2, ← e3, ← hL, ← hR, hraise]
  refine ⟨C + B + (p : ℤ) * (m : ℤ) ^ 2 * qG * B + (p : ℤ) ^ 2 * C * B - A - (p : ℤ) * qF * A, ?_⟩
  refine mul_left_cancel₀ hp ?_
  linear_combination h'

/-- `λ` vanishes at one non-zero class iff at all of them (`p ∤ m`). -/
theorem fermatQuot_scale_zero_iff (p : ℕ) (m : ℕ) (F G s k qF qG qs : ℤ) (hp : Prime (p : ℤ))
    (hm : ¬ (p : ℤ) ∣ (m : ℤ))
    (hF : F ^ (p - 1) = 1 + (p : ℤ) * qF)
    (hG : G ^ (p - 1) = 1 + (p : ℤ) * qG)
    (hs : s ^ (p - 1) = 1 + (p : ℤ) * qs)
    (hid : F * s ^ (2 * p ^ 2) = G ^ (m ^ 2) * (1 + (p : ℤ) ^ 2 * k)) :
    ((p : ℤ) ∣ qF ↔ (p : ℤ) ∣ qG) := by
  have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
  have key := fermatQuot_scale p m F G s k qF qG qs hp0 hF hG hs hid
  have hprime : Prime (p : ℤ) := hp
  constructor
  · intro h
    have h2 : (p : ℤ) ∣ (m : ℤ) ^ 2 * qG := by
      have hd := dvd_sub h key
      have e : qF - (qF - (m : ℤ) ^ 2 * qG) = (m : ℤ) ^ 2 * qG := by ring
      rwa [e] at hd
    rcases hprime.dvd_mul.mp h2 with h3 | h3
    · exact absurd (hprime.dvd_of_dvd_pow h3) hm
    · exact h3
  · intro h
    have h2 : (p : ℤ) ∣ (m : ℤ) ^ 2 * qG := Dvd.dvd.mul_left h _
    have hd := dvd_add key h2
    have e : qF - (m : ℤ) ^ 2 * qG + (m : ℤ) ^ 2 * qG = qF := by ring
    rwa [e] at hd

/-- If one column of an integer matrix is divisible by `q`, so is the determinant. -/
theorem dvd_det_of_col_dvd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (q : ℤ)
    (h : ∀ i, q ∣ M i j) : q ∣ M.det := by
  rw [Matrix.det_apply']
  refine Finset.dvd_sum ?_
  intro σ _
  exact Dvd.dvd.mul_left
    ((h (σ j)).trans (Finset.dvd_prod_of_mem (fun i => M (σ i) i) (Finset.mem_univ j))) _

/-- **The rank-drop step.**  If `M = p·N` (every entry divisible by `p`) and one column of
`N` is still divisible by `p`, then `p^{n+1} ∣ det M`.  Applied to the `p`-adic height matrix
of `Λ₀ = ker(E(ℚ) → E(𝔽_p))` this is the passage from `v_p(Reg_p) ≥ r - 2` to `≥ r - 1`. -/
theorem pow_succ_dvd_det_of_col {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ) (p : ℤ) (j : Fin n)
    (h : ∀ i, p ∣ N i j) : p ^ (n + 1) ∣ (p • N).det := by
  rw [Matrix.det_smul, Fintype.card_fin, pow_succ]
  exact mul_dvd_mul_left _ (dvd_det_of_col_dvd N j p h)

end PadicHeight

#print axioms PadicHeight.sq_dvd_one_add_pow_sub
#print axioms PadicHeight.sq_dvd_one_add_mul_pow_sub_one
#print axioms PadicHeight.sq_dvd_one_add_sq_mul_pow_sub_one
#print axioms PadicHeight.fermatQuot_scale
#print axioms PadicHeight.fermatQuot_scale_zero_iff
#print axioms PadicHeight.dvd_det_of_col_dvd
#print axioms PadicHeight.pow_succ_dvd_det_of_col
