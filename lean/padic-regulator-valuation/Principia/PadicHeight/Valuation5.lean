import Mathlib

/-!
# Integrality of the `p`-adic regulator at split anomalous primes, and the deformation dichotomy

Setting (continued from `PadicHeightValuation`, `2`, `3`, `4`).  `E/ℚ` has good ordinary
reduction at a prime `p ≥ 5` with `#E(𝔽_p) = p` (anomalous), `Λ = E(ℚ)/tors` has rank `r`,
`Λ₀ = ker(Λ → E(𝔽_p))` has index `p` in `Λ`, and `h_p` is the cyclotomic `p`-adic height in
Harvey's normalisation.

Two blocks are formalised here; both are statements about integers and matrices, and all the
geometry is left outside as the shape of the hypotheses.

## 1. The regulator bound

*Integrality theorem for the `p`-adic regulator at split anomalous primes.*  If `E(ℚ_p)[p] ≠ 0`
then every entry of the height matrix `M_Λ` of a basis of `Λ` lies in `ℤ_p`, and
`v_p(Reg_p) ≥ max(r - 2, 0)`.

Two ledgers give the exponent `r - 2`:

* `regulator_valuation_of_split_anomalous`: the height matrix `M₀` of `Λ₀` has all entries in
  `p·ℤ_p`, so `det M₀ = p^r · det N`; dividing by the index square `p² = [Λ : Λ₀]²` leaves
  `p^(r-2) ∣ Reg_p`.  Since `Reg_p` is modelled by an *integer* (this is exactly the split
  hypothesis: `M_Λ` has entries in `ℤ_p`), the truncated subtraction `r - 2` in `ℕ` is literally
  `max (r - 2) 0`, which is the statement `v_p(Reg_p) ≥ max (r-2, 0)`.
* `pow_sub_two_dvd_det_of_offdiag`: the matrix version of "a symmetric matrix that is `≡ 0`
  outside one row and one column has rank `≤ 2`" — every term of the Leibniz expansion misses
  the distinguished index at most twice, hence is divisible by `p^(n-2)`.

## 2. The deformation dichotomy (the converse `λ = 0 ⟹ split`)

With `λ(x̄) = q_p(φ_p(x₀))/2` and `q_p(u) = (u^(p-1) - 1)/p mod p` the Fermat quotient, the
one-parameter family of lifts `a₆ ↦ a₆ + s·p` of a fixed reduction moves `φ_p(x₀)` by a unit
`1 + p·s·B`, so `λ` is an *affine* function of `s` (`fermatQuot_deform`).  An affine function on
`ZMod p` with non-zero slope has exactly one zero (`affine_zero_unique`), and the split lift is
one of its zeros; hence `λ s = 0 ↔ split s` as soon as the slope is non-zero
(`lambda_eq_zero_iff_split`).

No analysis and no geometry enter: everything below is an identity in `ℤ` or in `ZMod p`.
-/

namespace PadicHeight

/-! ## Determinant ledgers -/

/-- If every entry of an `n × n` matrix is divisible by `d`, then `d ^ n` divides the
determinant. -/
theorem pow_dvd_det_of_forall_dvd {n : ℕ} {R : Type*} [CommRing R] (d : R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, d ∣ M i j) :
    d ^ n ∣ M.det := by
  rw [Matrix.det_apply']
  refine Finset.dvd_sum ?_
  intro σ _
  refine Dvd.dvd.mul_left ?_ _
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin n)), (fun _ : Fin n => d) i ∣ M (σ i) i :=
    fun i _ => h _ _
  simpa [Finset.prod_const] using
    Finset.prod_dvd_prod_of_dvd (fun _ : Fin n => d) (fun i => M (σ i) i) h2

/-- Matrix form of `max (r - 2, 0)`: if all entries `M i j` with `i ≠ i₀` and `j ≠ i₀` are
divisible by `p`, then `p ^ (n - 2)` divides `det M`.  Every Leibniz term `∏ i, M (σ i) i` can
avoid the hypothesis only at `i = i₀` and at `i = σ⁻¹ i₀`. -/
theorem pow_sub_two_dvd_det_of_offdiag {n : ℕ} {R : Type*} [CommRing R] (p : R)
    (M : Matrix (Fin n) (Fin n) R) (i₀ : Fin n)
    (h : ∀ i j, i ≠ i₀ → j ≠ i₀ → p ∣ M i j) :
    p ^ (n - 2) ∣ M.det := by
  rw [Matrix.det_apply']
  refine Finset.dvd_sum ?_
  intro σ _
  refine Dvd.dvd.mul_left ?_ _
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun i => σ i ≠ i₀ ∧ i ≠ i₀) with hS
  have hcompl : Sᶜ ⊆ ({i₀, σ.symm i₀} : Finset (Fin n)) := by
    intro i hi
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_and_or, not_not] at hi
    rcases hi with hi | hi
    · have : i = σ.symm i₀ := by
        rw [← hi]; simp
      simp [this]
    · simp [hi]
  have hcard : n - 2 ≤ S.card := by
    have h1 : Sᶜ.card ≤ 2 := le_trans (Finset.card_le_card hcompl) (Finset.card_insert_le _ _)
    have h2 : S.card + Sᶜ.card = n := by
      simpa using Finset.card_add_card_compl S
    omega
  have hdvd : p ^ S.card ∣ ∏ i ∈ S, M (σ i) i := by
    have h2 : ∀ i ∈ S, (fun _ : Fin n => p) i ∣ M (σ i) i := by
      intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact h _ _ hi.1 hi.2
    simpa [Finset.prod_const] using
      Finset.prod_dvd_prod_of_dvd (fun _ : Fin n => p) (fun i => M (σ i) i) h2
  refine dvd_trans (pow_dvd_pow p hcard) (dvd_trans hdvd ?_)
  exact Finset.prod_dvd_prod_of_subset S Finset.univ (fun i => M (σ i) i) (Finset.subset_univ S)

/-- **Integrality theorem for the `p`-adic regulator at split anomalous primes** (Theorem M),
linear-algebra part.

`M₀` is the height matrix of a basis of `Λ₀` and `MΛ` that of a basis of `Λ`; the split
hypothesis `E(ℚ_p)[p] ≠ 0` is what makes the entries of `MΛ` lie in `ℤ_p`, which is modelled
here by `MΛ` having entries in `ℤ`, and `MΛ.det` is `Reg_p`.  The hypothesis `hM₀` is the
statement that every entry of `M₀` lies in `p·ℤ_p` (flight 344, Lemma 2), and `hidx` is
`det M₀ = [Λ : Λ₀]² · det M_Λ = p² · Reg_p`.

The conclusion `p ^ (n - 2) ∣ MΛ.det`, with truncated subtraction in `ℕ`, is exactly
`v_p(Reg_p) ≥ max (r - 2, 0)`. -/
theorem regulator_valuation_of_split_anomalous {n : ℕ} {p : ℤ} (hp : p ≠ 0)
    (M₀ N MΛ : Matrix (Fin n) (Fin n) ℤ)
    (hM₀ : M₀ = p • N) (hidx : M₀.det = p ^ 2 * MΛ.det) :
    p ^ (n - 2) ∣ MΛ.det := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hdet : p ^ n * N.det = p ^ 2 * MΛ.det := by
      rw [← hidx, hM₀, Matrix.det_smul, Fintype.card_fin]
    obtain ⟨k, hk⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    subst hk
    have hcancel : p ^ k * N.det = MΛ.det := by
      have h2 : (p ^ 2) * (p ^ k * N.det) = (p ^ 2) * MΛ.det := by
        rw [← hdet, pow_add]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hp) h2
    exact ⟨N.det, by simpa using hcancel.symm⟩

/-- The same bound from the block shape: the height pairing vanishes mod `p` on `Λ₀`, i.e. all
entries `M i j` with `i, j ≠ i₀` are divisible by `p`. -/
theorem regulator_valuation_of_split_anomalous_offdiag {n : ℕ} {p : ℤ}
    (MΛ : Matrix (Fin n) (Fin n) ℤ) (i₀ : Fin n)
    (h : ∀ i j, i ≠ i₀ → j ≠ i₀ → p ∣ MΛ i j) :
    p ^ (n - 2) ∣ MΛ.det :=
  pow_sub_two_dvd_det_of_offdiag p MΛ i₀ h

/-! ## The deformation dichotomy -/

/-- First-order binomial ledger: `x² ∣ (1+x)^n - 1 - n·x`. -/
theorem sq_dvd_one_add_pow_sub (x : ℤ) (n : ℕ) :
    x ^ 2 ∣ (1 + x) ^ n - 1 - (n : ℤ) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(1 + x) * c + n, ?_⟩
      have : (1 + x) ^ (n + 1) - 1 - ((n : ℤ) + 1) * x
          = (1 + x) * ((1 + x) ^ n - 1 - (n : ℤ) * x) + (n : ℤ) * x ^ 2 := by ring
      rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this
      rw [this, hc]; ring

/-- **The deformation law for the Fermat quotient.**  If the unit `F₀` is moved to
`F₁ = F₀ · (1 + p·a)` — which is what the lift `a₆ ↦ a₆ + s·p` does to `φ_p(x₀)`, with
`a = s·B` — then the Fermat quotient moves by `-a`:  `q_p(F₁) ≡ q_p(F₀) - a (mod p)`.
Hence `λ` is an affine function of the deformation parameter. -/
theorem fermatQuot_deform {p a F₀ F₁ q₀ q₁ : ℤ} {k : ℕ} (hp : p ≠ 0) (hk : (k : ℤ) = p - 1)
    (hF : F₁ = F₀ * (1 + p * a))
    (h₀ : F₀ ^ k - 1 = p * q₀) (h₁ : F₁ ^ k - 1 = p * q₁) :
    p ∣ q₁ - (q₀ - a) := by
  obtain ⟨c, hc⟩ := sq_dvd_one_add_pow_sub (p * a) k
  have hpow : (1 + p * a) ^ k = 1 + (k : ℤ) * (p * a) + (p * a) ^ 2 * c := by linarith [hc]
  have hF₀ : F₀ ^ k = 1 + p * q₀ := by linarith [h₀]
  have hF₁ : F₁ ^ k = (1 + p * q₀) * (1 + (p - 1) * (p * a) + (p * a) ^ 2 * c) := by
    rw [hF, mul_pow, hF₀, hpow, hk]
  refine ⟨a + a ^ 2 * c + (p - 1) * q₀ * a + p * q₀ * a ^ 2 * c, ?_⟩
  have e1 : p * q₁ = (1 + p * q₀) * (1 + (p - 1) * (p * a) + (p * a) ^ 2 * c) - 1 := by
    rw [← hF₁]; linarith [h₁]
  refine mul_left_cancel₀ hp ?_
  linear_combination e1

/-- An affine function on `ZMod p` with non-zero slope has exactly one zero. -/
theorem affine_zero_unique {p : ℕ} [Fact p.Prime] {c B s₀ : ZMod p} (hB : B ≠ 0)
    (h₀ : c - s₀ * B = 0) (s : ZMod p) :
    c - s * B = 0 ↔ s = s₀ := by
  constructor
  · intro h
    have h1 : (s₀ - s) * B = 0 := by linear_combination h - h₀
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact (sub_eq_zero.mp h').symm
    · exact absurd h' hB
  · intro h; rw [h]; exact h₀

/-- **`λ = 0 ⟺ split` inside a deformation family.**  `lam` is the invariant `λ` as a function
of the deformation parameter `s` of the family `a₆ ↦ a₆ + s·p`, which is affine with slope `B`
(`fermatQuot_deform`); `split s` holds for exactly one `s` (Serre–Tate: exactly one lift mod `p²`
of an ordinary reduction is the canonical one), and `λ` vanishes at that `s` (flight 354,
Corollary D).  If the slope is non-zero, the two vanishing loci coincide. -/
theorem lambda_eq_zero_iff_split {p : ℕ} [Fact p.Prime] {lam : ZMod p → ZMod p}
    {split : ZMod p → Prop} {l₀ B s₀ : ZMod p} (hB : B ≠ 0)
    (haff : ∀ s, lam s = l₀ - s * B)
    (hsplit : ∀ s, split s ↔ s = s₀)
    (hzero : lam s₀ = 0) (s : ZMod p) :
    lam s = 0 ↔ split s := by
  rw [haff s, hsplit s]
  exact affine_zero_unique hB (by rw [← haff s₀]; exact hzero) s


/-- **The dichotomy.**  `lam` is the invariant `λ` as a function of the deformation parameter
`s` of a family of lifts sweeping the Serre–Tate deformation space; it is affine (`haff`, which is
`fermatQuot_deform`), and it vanishes at the split lift `s₀` (flight 354, Corollary D).  Then
either `λ` vanishes identically on the family, or its zero locus is exactly `{s₀}`.  No third
possibility: this is the whole content of the converse `λ = 0 ⟹ split`, reduced to the
non-vanishing of one slope. -/
theorem lambda_dichotomy {p : ℕ} [Fact p.Prime] {lam : ZMod p → ZMod p} {l₀ B s₀ : ZMod p}
    (haff : ∀ s, lam s = l₀ - s * B) (hzero : lam s₀ = 0) :
    (∀ s, lam s = 0) ∨ (∀ s, lam s = 0 ↔ s = s₀) := by
  rcases eq_or_ne B 0 with hB | hB
  · left
    intro s
    have h₀ : l₀ = 0 := by
      have := hzero
      rw [haff s₀, hB, mul_zero, sub_zero] at this
      exact this
    rw [haff s, hB, mul_zero, sub_zero, h₀]
  · right
    intro s
    rw [haff s]
    exact affine_zero_unique hB (by rw [← haff s₀]; exact hzero) s

/-- With non-zero slope the family has exactly one zero — the counterpart of "exactly one lift in
the family is the canonical (split) one". -/
theorem exists_unique_lambda_zero {p : ℕ} [Fact p.Prime] {lam : ZMod p → ZMod p} {l₀ B : ZMod p}
    (hB : B ≠ 0) (haff : ∀ s, lam s = l₀ - s * B) :
    ∃! s, lam s = 0 := by
  refine ⟨l₀ / B, ?_, ?_⟩
  · show lam (l₀ / B) = 0
    rw [haff, div_mul_cancel₀ _ hB, sub_self]
  · intro y hy
    have hy' : l₀ - y * B = 0 := by rw [← haff y]; exact hy
    have h : l₀ = y * B := by linear_combination hy'
    rw [h, mul_div_assoc, div_self hB, mul_one]

/-- **One scalar governs the non-degeneracy.**  `B` and `B₄` are the two logarithmic derivatives
of `φ_p(x₀)` in the directions `a₆` and `a₄`.  Because `λ` is an isomorphism invariant, the pair
`(B₄, B)` annihilates the direction `(4a₄, 6a₆)` of the infinitesimal automorphism `u = 1 + p t`
(`hrel`), so it is a single scalar multiple of `(6a₆, -4a₄)`.  For an anomalous curve `a₆ ≠ 0`
always (`a₆ = 0` forces a rational point of order 2, so `#E(𝔽_p)` would be even), hence the
`a₄`-direction always has slope `B₄ = 6a₆ρ`, and `ρ ≠ 0` is the whole non-degeneracy. -/
theorem slope_of_rho {p : ℕ} [Fact p.Prime] {a4 a6 B B4 : ZMod p} (h6 : (6 : ZMod p) * a6 ≠ 0)
    (hrel : 4 * a4 * B4 + 6 * a6 * B = 0) :
    ∃ ρ : ZMod p, 6 * a6 * ρ = B4 ∧ 4 * a4 * ρ = -B ∧ (ρ = 0 ↔ B4 = 0) := by
  have hinv : (6 * a6) * (6 * a6)⁻¹ = 1 := mul_inv_cancel₀ h6
  refine ⟨(6 * a6)⁻¹ * B4, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hinv, one_mul]
  · refine mul_left_cancel₀ h6 ?_
    calc (6 * a6) * (4 * a4 * ((6 * a6)⁻¹ * B4))
        = ((6 * a6) * (6 * a6)⁻¹) * (4 * a4 * B4) := by ring
      _ = 4 * a4 * B4 := by rw [hinv, one_mul]
      _ = (6 * a6) * (-B) := by linear_combination hrel
  · constructor
    · intro h
      have h2 : (6 * a6) * ((6 * a6)⁻¹ * B4) = (6 * a6) * 0 := by rw [h]
      rw [← mul_assoc, hinv, one_mul, mul_zero] at h2
      exact h2
    · intro h
      rw [h, mul_zero]

/-- **Integrality theorem for the `p`-adic regulator at split anomalous primes, equivalence form**
(rank one).  `h1` is Theorem M at `r = 1` (split forces `Reg_p ∈ ℤ_p`); `h2` is the converse input
(if `E` is not split then `v_p(Reg_p) = -1` exactly, the baseline `r - 2`).  Together they turn the
inequality into an equivalence: `v_p(Reg_p) ≥ 0 ⟺ split`. -/
theorem regulator_valuation_of_split_anomalous_iff_split {p : ℤ} (hp : Prime p) {Reg : ℚ}
    {split : Prop}
    (h1 : split → ∃ z : ℤ, Reg = (z : ℚ))
    (h2 : ¬ split → ∃ z : ℤ, Reg = (z : ℚ) / (p : ℚ) ∧ ¬ ((p : ℤ) ∣ z)) :
    (∃ z : ℤ, Reg = (z : ℚ)) ↔ split := by
  constructor
  · rintro ⟨z, hz⟩
    by_contra hs
    obtain ⟨w, hw, hpw⟩ := h2 hs
    have hp0 : (p : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp.ne_zero
    have h3 : (z : ℚ) = (w : ℚ) / (p : ℚ) := hz.symm.trans hw
    have h4 : (w : ℚ) = (p : ℚ) * (z : ℚ) := by rw [h3]; field_simp
    exact hpw ⟨z, by exact_mod_cast h4⟩
  · exact h1

end PadicHeight

#print axioms PadicHeight.pow_dvd_det_of_forall_dvd
#print axioms PadicHeight.pow_sub_two_dvd_det_of_offdiag
#print axioms PadicHeight.regulator_valuation_of_split_anomalous
#print axioms PadicHeight.regulator_valuation_of_split_anomalous_offdiag
#print axioms PadicHeight.sq_dvd_one_add_pow_sub
#print axioms PadicHeight.fermatQuot_deform
#print axioms PadicHeight.affine_zero_unique
#print axioms PadicHeight.lambda_eq_zero_iff_split
#print axioms PadicHeight.lambda_dichotomy
#print axioms PadicHeight.exists_unique_lambda_zero
#print axioms PadicHeight.slope_of_rho
#print axioms PadicHeight.regulator_valuation_of_split_anomalous_iff_split
