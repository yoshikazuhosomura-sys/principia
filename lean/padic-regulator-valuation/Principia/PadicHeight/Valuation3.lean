import Mathlib

/-!
# `p`-th powers kill the Fermat quotient: the split case of the anomalous height bound

Setting (continued from `Principia.PadicHeight.Valuation` and `Principia.PadicHeight.Valuation2`).
`E/ℚ` has good ordinary reduction at a prime `p ≥ 5` with `#E(𝔽_p) = p` (anomalous),
`P' ∈ E(ℚ)` reduces to a point of exact order `p`, and `P = pP'`.  Writing
`x(P) = α/d(P)²`, `y(P) = β/d(P)³` in lowest terms, the outside-`p` part of the cyclotomic
`p`-adic height is `A = ∑_{ℓ≠p} n_ℓ logₚ ℓ`, and `c = v_p(A) ≥ 2 ↔ p² ∣ α^(p-1) - β^(p-1)`.

The geometric input now available is: if `E(ℚ_p)[p] ≠ 0`, with `τ` a `ℚ_p`-rational point of
order `p`, then the numerator of the `p`-division map satisfies

  `φ_p(x(τ)) = φ̄(x(τ))^p`,

where `φ̄` is the numerator of Vélu's isogeny `E → E/⟨τ⟩`.  So `φ_p(x(τ))` is an honest `p`-th
power of a `p`-adic unit.  This file isolates the arithmetic consequences over `ℤ`:

* `sq_dvd_one_add_pow_sub` : `x² ∣ (1+x)^n - 1 - n*x` (the first-order binomial ledger);
* `sq_dvd_pow_sub_one_of_isPow` : `p ∤ w → p² ∣ (w^p)^(p-1) - 1`, i.e. the Fermat quotient of a
  `p`-th power vanishes;
* `sq_dvd_pow_sub_one_iff_isPow` : conversely, `p² ∣ u^(p-1) - 1` holds **iff** `u` is a `p`-th
  power modulo `p²`.  This is the Kummer reformulation `λ = 0 ↔ φ_p(x̄) ∈ (ℤ_p^×)^p`;
* `sq_dvd_pow_sub_one_of_sq_eq_cube` : `ω² ≡ φ³ (mod p²)` and `p² ∣ φ^(p-1) - 1` force
  `p² ∣ ω^(p-1) - 1` (the Weierstrass equation at `P`, `p` odd);
* `sq_dvd_alpha_sub_beta_of_isPow` : the composite — if `φ` is a `p`-th power of a unit and
  `ω² ≡ φ³ (mod p²)`, then `p² ∣ α^(p-1) - β^(p-1)` for `α = φ·d^{p²}`, `β = ω·d^{p²}`,
  which is `c ≥ 2`.

Everything is over `ℤ`; no `p`-adic analysis and no geometry enter.
-/

namespace PadicHeight

variable {p : ℕ} [hp : Fact p.Prime]

/-- Fermat's little theorem in quotient form: `a^(p-1) = 1 + p * A` for `p ∤ a`. -/
theorem exists_fermatQuot' {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : ∃ A : ℤ, a ^ (p - 1) = 1 + p * A := by
  have h1 : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have h2 : ((a : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h1
  have h3 : (((a ^ (p - 1) - 1 : ℤ)) : ZMod p) = 0 := by push_cast [h2]; ring
  obtain ⟨A, hA⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h3
  exact ⟨A, by linarith [hA]⟩

/-- The binomial ledger to first order: `x² ∣ (1+x)^n - 1 - n*x`. -/
theorem sq_dvd_one_add_pow_sub (x : ℤ) (n : ℕ) : x ^ 2 ∣ (1 + x) ^ n - 1 - (n : ℤ) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      have h2 : (1 + x) ^ n = 1 + (n : ℤ) * x + x ^ 2 * k := by linarith
      refine ⟨(1 + x) * k + (n : ℤ), ?_⟩
      have h3 : (1 + x) ^ (n + 1) = (1 + x) * (1 + x) ^ n := by ring
      rw [h3, h2]
      push_cast
      ring

/-- **A `p`-th power has vanishing Fermat quotient.**  If `p ∤ w` then `p² ∣ (w^p)^(p-1) - 1`. -/
theorem sq_dvd_pow_sub_one_of_isPow {w : ℤ} (hw : ¬ (p : ℤ) ∣ w) :
    ((p : ℤ)) ^ 2 ∣ (w ^ p) ^ (p - 1) - 1 := by
  obtain ⟨A, hA⟩ := exists_fermatQuot' (p := p) hw
  obtain ⟨k, hk⟩ := sq_dvd_one_add_pow_sub ((p : ℤ) * A) p
  have hcomm : (w ^ p) ^ (p - 1) = (w ^ (p - 1)) ^ p := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  refine ⟨A ^ 2 * k + A, ?_⟩
  rw [hcomm, hA]
  linear_combination hk

/-- **Kummer reformulation.**  For a unit `u`, the Fermat quotient `q_p(u)` vanishes exactly when
`u` is a `p`-th power modulo `p²`. -/
theorem sq_dvd_pow_sub_one_iff_isPow {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ((p : ℤ)) ^ 2 ∣ u ^ (p - 1) - 1 ↔ ∃ v : ℤ, ¬ (p : ℤ) ∣ v ∧ ((p : ℤ)) ^ 2 ∣ u - v ^ p := by
  have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨u, hu, -(u * k), ?_⟩
    have hup : u ^ p = u ^ (p - 1) * u := by rw [← pow_succ, hp1]
    have hk' : u ^ (p - 1) = 1 + ((p : ℤ)) ^ 2 * k := by linarith
    rw [hup, hk']
    ring
  · rintro ⟨v, hv, hd⟩
    obtain ⟨k1, hk1⟩ := sq_dvd_pow_sub_one_of_isPow (p := p) hv
    obtain ⟨k0, hk0⟩ := hd
    have h2 : u ≡ v ^ p [ZMOD ((p : ℤ)) ^ 2] :=
      (Int.modEq_iff_dvd).2 ⟨-k0, by linarith⟩
    have h3 : u ^ (p - 1) ≡ (v ^ p) ^ (p - 1) [ZMOD ((p : ℤ)) ^ 2] := h2.pow (p - 1)
    obtain ⟨k2, hk2⟩ := (Int.modEq_iff_dvd).1 h3
    exact ⟨k1 - k2, by linear_combination hk1 - hk2⟩

/-- If `ω² ≡ φ³ (mod p²)` and the Fermat quotient of `φ` vanishes, then so does that of `ω`
(`p` odd). -/
theorem sq_dvd_pow_sub_one_of_sq_eq_cube (hp2 : p ≠ 2) {φ ω : ℤ} (hω : ¬ (p : ℤ) ∣ ω)
    (hcube : ((p : ℤ)) ^ 2 ∣ ω ^ 2 - φ ^ 3) (hφ : ((p : ℤ)) ^ 2 ∣ φ ^ (p - 1) - 1) :
    ((p : ℤ)) ^ 2 ∣ ω ^ (p - 1) - 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k1, hk1⟩ := hφ
  -- `X := ω^(p-1)` satisfies `X² ≡ 1 (mod p²)`
  have hsq : ((p : ℤ)) ^ 2 ∣ (ω ^ (p - 1)) ^ 2 - 1 := by
    have e1 : (ω ^ (p - 1)) ^ 2 = (ω ^ 2) ^ (p - 1) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have e2 : (φ ^ 3) ^ (p - 1) = (φ ^ (p - 1)) ^ 3 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    obtain ⟨k3, hk3⟩ := hcube
    have h2 : ω ^ 2 ≡ φ ^ 3 [ZMOD ((p : ℤ)) ^ 2] := (Int.modEq_iff_dvd).2 ⟨-k3, by linarith⟩
    have h3 : (ω ^ 2) ^ (p - 1) ≡ (φ ^ 3) ^ (p - 1) [ZMOD ((p : ℤ)) ^ 2] := h2.pow (p - 1)
    obtain ⟨k2, hk2⟩ := (Int.modEq_iff_dvd).1 h3
    rw [e2] at hk2
    have hcube' : (φ ^ (p - 1)) ^ 3 - 1 =
        ((p : ℤ)) ^ 2 * (k1 * ((φ ^ (p - 1)) ^ 2 + φ ^ (p - 1) + 1)) := by
      linear_combination ((φ ^ (p - 1)) ^ 2 + φ ^ (p - 1) + 1) * hk1
    refine ⟨k1 * ((φ ^ (p - 1)) ^ 2 + φ ^ (p - 1) + 1) - k2, ?_⟩
    rw [e1]
    linear_combination hcube' - hk2
  -- `p ∣ X - 1` by Fermat, and `p ∤ X + 1` since `p` is odd
  obtain ⟨A, hA⟩ := exists_fermatQuot' (p := p) hω
  have hXm : ω ^ (p - 1) - 1 = (p : ℤ) * A := by linarith
  have hnd : ¬ (p : ℤ) ∣ (ω ^ (p - 1) + 1) := by
    intro hd
    obtain ⟨m, hm⟩ := hd
    have h2 : (p : ℤ) ∣ 2 := ⟨m - A, by linarith⟩
    have h1 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
    have h3 : 2 ≤ p := hp.out.two_le
    have h4 : (p : ℤ) = 2 := by
      have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h3
      omega
    exact hp2 (by exact_mod_cast h4)
  obtain ⟨k, hk⟩ := hsq
  have hprod : (p : ℤ) * (A * (ω ^ (p - 1) + 1)) = (p : ℤ) * ((p : ℤ) * k) := by
    linear_combination hk - (ω ^ (p - 1) + 1) * hXm
  have hpA : (p : ℤ) ∣ A * (ω ^ (p - 1) + 1) := ⟨k, mul_left_cancel₀ hpne hprod⟩
  obtain ⟨B, hB⟩ := (hpZ.dvd_mul.1 hpA).resolve_right hnd
  exact ⟨B, by rw [hXm, hB]; ring⟩

/-- **The composite.**  If `φ = w^p` is a `p`-th power of a unit and `ω² ≡ φ³ (mod p²)`, then the
Fermat quotients of `α = φ·d^{p²}` and `β = ω·d^{p²}` agree, i.e. `c ≥ 2`. -/
theorem sq_dvd_alpha_sub_beta_of_isPow (hp2 : p ≠ 2) {w ω d : ℤ} (hw : ¬ (p : ℤ) ∣ w)
    (hω : ¬ (p : ℤ) ∣ ω) (hcube : ((p : ℤ)) ^ 2 ∣ ω ^ 2 - (w ^ p) ^ 3) :
    ((p : ℤ)) ^ 2 ∣ (w ^ p * d ^ (p ^ 2)) ^ (p - 1) - (ω * d ^ (p ^ 2)) ^ (p - 1) := by
  obtain ⟨k1, hk1⟩ := sq_dvd_pow_sub_one_of_isPow (p := p) hw
  obtain ⟨k2, hk2⟩ := sq_dvd_pow_sub_one_of_sq_eq_cube (p := p) hp2 hω hcube ⟨k1, hk1⟩
  refine ⟨(d ^ (p ^ 2)) ^ (p - 1) * (k1 - k2), ?_⟩
  have e1 : (w ^ p * d ^ (p ^ 2)) ^ (p - 1) = (w ^ p) ^ (p - 1) * (d ^ (p ^ 2)) ^ (p - 1) :=
    mul_pow _ _ _
  have e2 : (ω * d ^ (p ^ 2)) ^ (p - 1) = ω ^ (p - 1) * (d ^ (p ^ 2)) ^ (p - 1) := mul_pow _ _ _
  rw [e1, e2]
  linear_combination ((d : ℤ) ^ (p ^ 2)) ^ (p - 1) * hk1 - ((d : ℤ) ^ (p ^ 2)) ^ (p - 1) * hk2

end PadicHeight

#print axioms PadicHeight.exists_fermatQuot'
#print axioms PadicHeight.sq_dvd_one_add_pow_sub
#print axioms PadicHeight.sq_dvd_pow_sub_one_of_isPow
#print axioms PadicHeight.sq_dvd_pow_sub_one_iff_isPow
#print axioms PadicHeight.sq_dvd_pow_sub_one_of_sq_eq_cube
#print axioms PadicHeight.sq_dvd_alpha_sub_beta_of_isPow
