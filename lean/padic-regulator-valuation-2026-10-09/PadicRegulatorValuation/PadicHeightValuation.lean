import Mathlib

/-!
# Valuation bounds for cyclotomic `p`-adic heights and regulators

Let `E/ℚ` have good ordinary reduction at a prime `p ≥ 5`, let `σ` be the Mazur–Tate `p`-adic
sigma function and, for a point `P` whose reduction is trivial at `p` and non-singular at every
bad prime, write `x(P) = α/d²`, `y(P) = β/d³` in lowest terms.  The cyclotomic `p`-adic height
is `h(P) = 2 logₚ(σ(P)/d(P))`, where `logₚ` is the Iwasawa logarithm.

Two elementary facts drive the valuation of the height and of the regulator.

* The outside-`p` part of the height is an integral combination `∑ nₗ logₚ ℓ` of Iwasawa
  logarithms of rational primes `ℓ ≠ p`, and `logₚ ℓ ∈ pℤ_p`.  Its finite content is Fermat's
  little theorem, `dvd_pow_sub_one` below; the second-order refinement (which governs how often
  the valuation jumps) is additivity of the Fermat quotient, `fermatQuot_additive`.
* `σ(P)/d(P)` is a `p`-adic unit, so `h(P) ∈ pℤ_p`; the regulator on a finite-index subgroup is
  then a determinant of a matrix with entries in `pℤ_p`, and passing to the full Mordell–Weil
  group divides by the square of the index.  This is `norm_det_le` and `norm_det_div_sq_le`.

Everything in this file is the valuation bookkeeping, stated over `ℤ` and `ℚ_[p]`; the analytic
input (that `σ(P)/d(P)` is a unit, and that the index of the subgroup is divisible by `p` at
most once) is left as the hypotheses.
-/

namespace PadicHeight

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The outside-`p` term -/

/-- Fermat's little theorem in the shape used here: for a rational integer `l` prime to `p`,
`p ∣ l^(p-1) - 1`.  Equivalently `v_p(logₚ l) ≥ 1`, which is why the outside-`p` part of the
`p`-adic height always has valuation at least `1`. -/
theorem dvd_pow_sub_one {l : ℤ} (h : ¬ (p : ℤ) ∣ l) : (p : ℤ) ∣ l ^ (p - 1) - 1 := by
  have hl : ((l : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  have h1 : ((l : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hl
  have h2 : (((l ^ (p - 1) - 1 : ℤ)) : ZMod p) = 0 := by push_cast [h1]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2

/-- Additivity of the Fermat quotient, in division-free form:
`(ab)^(p-1) ≡ a^(p-1) + b^(p-1) - 1  (mod p²)`.
Dividing by `p`, this says `q_p(ab) ≡ q_p(a) + q_p(b) (mod p)`, i.e. `q_p` is a homomorphism
`(ℤ/p²)ˣ → ℤ/p`.  Its kernel has index `p`, which is the source of the `1/p` law for the
jumps of the valuation of the outside-`p` term. -/
theorem fermatQuot_additive {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ((p : ℤ) ^ 2) ∣ (a * b) ^ (p - 1) - a ^ (p - 1) - b ^ (p - 1) + 1 := by
  have h : (a * b) ^ (p - 1) - a ^ (p - 1) - b ^ (p - 1) + 1
      = (a ^ (p - 1) - 1) * (b ^ (p - 1) - 1) := by
    rw [mul_pow]; ring
  rw [h, sq]
  exact mul_dvd_mul (dvd_pow_sub_one ha) (dvd_pow_sub_one hb)

/-! ### Ultrametric bookkeeping for the regulator -/

/-- If every entry of an `r × r` matrix over `ℚ_[p]` has norm at most `b`, its determinant has
norm at most `b ^ r`.  With `b = 1/p` this is: a height pairing matrix with entries in `pℤ_p`
has regulator in `p^r ℤ_p`. -/
theorem norm_det_le {r : ℕ} (M : Matrix (Fin r) (Fin r) ℚ_[p]) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, ‖M i j‖ ≤ b) : ‖M.det‖ ≤ b ^ r := by
  classical
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hb r) ?_
  intro σ _
  rw [norm_mul]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℚ_[p])‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hh | hh <;> rw [hh] <;> simp
  have hprod : ‖∏ i, M (σ i) i‖ ≤ b ^ r := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : Fin r, b :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
      _ = b ^ r := by simp
  calc ‖((Equiv.Perm.sign σ : ℤ) : ℚ_[p])‖ * ‖∏ i, M (σ i) i‖
      ≤ 1 * (b ^ r) := mul_le_mul hs hprod (norm_nonneg _) zero_le_one
    _ = b ^ r := one_mul _

/-- The baseline for the `p`-adic regulator.  If the height pairing matrix `M` of a
finite-index subgroup `G ⊆ E(ℚ)/tors` has all entries in `pℤ_p`, and the index `k` of `G` is
divisible by `p` at most once, then the regulator of `E(ℚ)`, namely `det M / k²`, has norm at
most `p^(2-r)`; that is, its valuation is at least `r - 2`. -/
theorem norm_det_div_sq_le {r : ℕ} (M : Matrix (Fin r) (Fin r) ℚ_[p]) (k : ℚ_[p])
    (hkn : ((p : ℝ))⁻¹ ≤ ‖k‖) (h : ∀ i j, ‖M i j‖ ≤ ((p : ℝ))⁻¹) :
    ‖M.det / k ^ 2‖ ≤ ((p : ℝ))⁻¹ ^ r * (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpi : (0 : ℝ) < ((p : ℝ))⁻¹ := by positivity
  have hk0 : (0 : ℝ) < ‖k‖ := lt_of_lt_of_le hpi hkn
  have hk2 : (0 : ℝ) < ‖k‖ ^ 2 := pow_pos hk0 2
  have h1 : ‖M.det‖ ≤ ((p : ℝ))⁻¹ ^ r := norm_det_le M (le_of_lt hpi) h
  have h2 : (((p : ℝ))⁻¹) ^ 2 ≤ ‖k‖ ^ 2 := pow_le_pow_left₀ (le_of_lt hpi) hkn 2
  have h3 : (0 : ℝ) < (((p : ℝ))⁻¹) ^ 2 := pow_pos hpi 2
  have h4 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ ^ r := pow_nonneg (le_of_lt hpi) r
  rw [norm_div, norm_pow]
  calc ‖M.det‖ / ‖k‖ ^ 2 ≤ ((p : ℝ))⁻¹ ^ r / ‖k‖ ^ 2 := by gcongr
    _ ≤ ((p : ℝ))⁻¹ ^ r / (((p : ℝ))⁻¹) ^ 2 := by gcongr
    _ = ((p : ℝ))⁻¹ ^ r * (p : ℝ) ^ 2 := by
        field_simp

/-- The rank one case, spelled out: if `a ∈ pℤ_p` is the height of a generator of the subgroup
and the index `k` is divisible by `p` at most once, the `p`-adic regulator `a / k²` has norm at
most `p`, i.e. valuation at least `-1`.  This is the floor that the anomalous rank one curves
sit on. -/
theorem norm_height_div_sq_le (a k : ℚ_[p]) (hkn : ((p : ℝ))⁻¹ ≤ ‖k‖)
    (ha : ‖a‖ ≤ ((p : ℝ))⁻¹) : ‖a / k ^ 2‖ ≤ (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpi : (0 : ℝ) < ((p : ℝ))⁻¹ := by positivity
  have hk0 : (0 : ℝ) < ‖k‖ := lt_of_lt_of_le hpi hkn
  have hk2 : (0 : ℝ) < ‖k‖ ^ 2 := pow_pos hk0 2
  have h2 : (((p : ℝ))⁻¹) ^ 2 ≤ ‖k‖ ^ 2 := pow_le_pow_left₀ (le_of_lt hpi) hkn 2
  have h3 : (0 : ℝ) < (((p : ℝ))⁻¹) ^ 2 := pow_pos hpi 2
  rw [norm_div, norm_pow]
  calc ‖a‖ / ‖k‖ ^ 2 ≤ ((p : ℝ))⁻¹ / ‖k‖ ^ 2 := by gcongr
    _ ≤ ((p : ℝ))⁻¹ / (((p : ℝ))⁻¹) ^ 2 := by gcongr
    _ = (p : ℝ) := by field_simp

end PadicHeight

#print axioms PadicHeight.dvd_pow_sub_one
#print axioms PadicHeight.fermatQuot_additive
#print axioms PadicHeight.norm_det_le
#print axioms PadicHeight.norm_det_div_sq_le
#print axioms PadicHeight.norm_height_div_sq_le
