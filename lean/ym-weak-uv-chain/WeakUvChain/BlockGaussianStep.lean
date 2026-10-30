/-
Finite-dimensional part of the one-step lemma. Single file; checks with `import Mathlib` only.

  §1 Arithmetic of the Kotecký–Preiss condition: if the number of connected polymers of size n is ≤ (eΔ)ⁿ, the activity is ≤ εⁿ,
     and ε ≤ 1/(2Δe²), then the KP sum Σ_n N(n) εⁿ eⁿ ≤ 1 (the condition with weight a(γ) = |γ|)
  §2 Gaussian quadratic form of a block: for the quadratic form [[A, B], [Bᴴ, D]] in the fluctuation x and the coarse variable y,
     (i) completing the square (after integrating out the fluctuation the coarse form is the Schur complement D − Bᴴ A⁻¹ B),
     (ii) the whole form is positive semidefinite ⇔ the Schur complement is (A positive definite),
     (iii) the Schur complement is ≤ D (integrating out fluctuations lowers the stiffness),
     (iv) positive definiteness of the pulled-back kernel M = Kᴴ Γ K (K injective) and an upper bound on its quadratic form
  §3 The one-step change of coupling as a ratio of quadratic-form coefficients: u' = u·q, and the ratio window ⇔ the (H-β) window
  §4 #print axioms

The Kotecký–Preiss theorem itself (convergence of the cluster expansion and the logarithm bound) and the count of connected sets
N(n) ≤ (eΔ)ⁿ enter as premises (from the literature).
-/
import Mathlib

namespace BlockGaussianStep

open Matrix Finset

set_option linter.unusedSectionVars false

/-! ## 1. Arithmetic of the Kotecký–Preiss condition -/

/-- If the number of connected polymers of size `n` (containing a given point) is ≤ `(eΔ)ⁿ`, the activity of a polymer of size `n`
is ≤ `εⁿ`, and `ε ≤ 1/(2Δe²)`, then the KP sum `Σ_{n=1}^{M} N(n) εⁿ eⁿ ≤ 1` (for every `M`). -/
theorem kp_sum_le_one (N : ℕ → ℝ) (Δ ε : ℝ) (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hN : ∀ n, 0 ≤ N n ∧ N n ≤ (Real.exp 1 * Δ) ^ n)
    (hsmall : ε ≤ 1 / (2 * Δ * Real.exp 1 ^ 2)) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, N n * ε ^ n * Real.exp 1 ^ n ≤ 1 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set q := Real.exp 1 * Δ * ε * Real.exp 1 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    have h2 : 0 < 2 * Δ * Real.exp 1 ^ 2 := by positivity
    have : ε * (2 * Δ * Real.exp 1 ^ 2) ≤ 1 := by
      rw [le_div_iff₀ h2] at hsmall; linarith
    rw [hq]; nlinarith
  have hterm : ∀ n, N n * ε ^ n * Real.exp 1 ^ n ≤ q ^ n := by
    intro n
    have h1 : N n * ε ^ n * Real.exp 1 ^ n ≤ (Real.exp 1 * Δ) ^ n * ε ^ n * Real.exp 1 ^ n := by
      have := (hN n).2
      have hpos : 0 ≤ ε ^ n * Real.exp 1 ^ n := by positivity
      nlinarith
    calc N n * ε ^ n * Real.exp 1 ^ n ≤ (Real.exp 1 * Δ) ^ n * ε ^ n * Real.exp 1 ^ n := h1
      _ = q ^ n := by rw [hq]; ring
  calc ∑ n ∈ Finset.Icc 1 M, N n * ε ^ n * Real.exp 1 ^ n
      ≤ ∑ n ∈ Finset.Icc 1 M, q ^ n := Finset.sum_le_sum fun n _ => hterm n
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ n :=
        Finset.sum_le_sum fun n _ => pow_le_pow_left₀ hq0 hq1 n
    _ ≤ 1 := by
        have key : ∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ n = 1 - (1 / 2) ^ M := by
          intro M
          induction M with
          | zero => simp
          | succ M ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            ring
        rw [key M]
        have : (0 : ℝ) ≤ (1 / 2) ^ M := by positivity
        linarith

/-! ## 2. Gaussian quadratic form of a block -/

section Gaussian

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- (i) Completing the square: shifting the fluctuation `x` to `x + A⁻¹ B y` splits the quadratic form in `(x, y)` into the `A` part
and the Schur complement `D − Bᴴ A⁻¹ B` part (Mathlib's `schur_complement_eq₁₁`). -/
theorem completing_square (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    [Invertible A] (hA : A.IsHermitian) (x : m → ℝ) (y : n → ℝ) :
    vecMul (Sum.elim x y) (fromBlocks A B Bᴴ D) ⬝ᵥ Sum.elim x y =
      vecMul (x + (A⁻¹ * B) *ᵥ y) A ⬝ᵥ (x + (A⁻¹ * B) *ᵥ y) +
        vecMul y (D - Bᴴ * A⁻¹ * B) ⬝ᵥ y :=
  schur_complement_eq₁₁ B D x y hA

/-- (ii) The whole form is positive semidefinite ⇔ the Schur complement is positive semidefinite (`A` positive definite). -/
theorem block_psd_iff_schur (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef :=
  PosDef.fromBlocks₁₁ B D hA

/-- (iii) Integrating out fluctuations lowers the stiffness: if `A` is positive definite, then for all `y`
`y·(D − Bᴴ A⁻¹ B) y ≤ y·D y`. -/
theorem schur_le_restricted (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.PosDef) (y : n → ℝ) :
    y ⬝ᵥ ((D - Bᴴ * A⁻¹ * B) *ᵥ y) ≤ y ⬝ᵥ (D *ᵥ y) := by
  have hpsd : (Bᴴ * A⁻¹ * B).PosSemidef := by
    have := hA.inv.posSemidef.conjTranspose_mul_mul_same B
    simpa [conjTranspose_conjTranspose] using this
  have h0 : 0 ≤ y ⬝ᵥ ((Bᴴ * A⁻¹ * B) *ᵥ y) := by
    have := (posSemidef_iff_dotProduct_mulVec.mp hpsd).2 y
    simpa using this
  rw [sub_mulVec, dotProduct_sub]
  linarith

/-- (iv-a) The pulled-back kernel `M = Kᴴ Γ K` is positive definite if `Γ` is positive definite and `K` injective (positivity of the kernel independent of gauge fixing). -/
theorem core_posDef {k : Type*} [Fintype k] [DecidableEq k] (Γ : Matrix m m ℝ) (K : Matrix m k ℝ)
    (hΓ : Γ.PosDef) (hK : Function.Injective K.mulVec) : (Kᴴ * Γ * K).PosDef :=
  hΓ.conjTranspose_mul_mul_same hK

/-- (iv-b) Upper bound on the kernel's quadratic form: if the quadratic form of `Γ` is ≤ `c‖·‖²` and `‖Kx‖² ≤ κ ‖x‖²`
(sums of squares), then `x·M x ≤ c κ ‖x‖²`. -/
theorem core_quadratic_le {k : Type*} [Fintype k] (Γ : Matrix m m ℝ) (K : Matrix m k ℝ)
    (c κ : ℝ) (hc : 0 ≤ c)
    (hΓ : ∀ v : m → ℝ, v ⬝ᵥ (Γ *ᵥ v) ≤ c * (v ⬝ᵥ v))
    (hK : ∀ x : k → ℝ, (K *ᵥ x) ⬝ᵥ (K *ᵥ x) ≤ κ * (x ⬝ᵥ x)) (x : k → ℝ) :
    x ⬝ᵥ ((Kᴴ * Γ * K) *ᵥ x) ≤ c * κ * (x ⬝ᵥ x) := by
  have e : x ⬝ᵥ ((Kᴴ * Γ * K) *ᵥ x) = (K *ᵥ x) ⬝ᵥ (Γ *ᵥ (K *ᵥ x)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, conjTranspose_eq_transpose_of_trivial,
      vecMul_transpose]
  rw [e]
  calc (K *ᵥ x) ⬝ᵥ (Γ *ᵥ (K *ᵥ x)) ≤ c * ((K *ᵥ x) ⬝ᵥ (K *ᵥ x)) := hΓ _
    _ ≤ c * (κ * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left (hK x) hc
    _ = c * κ * (x ⬝ᵥ x) := by ring

end Gaussian

/-! ## 3. The one-step change of coupling as a coefficient ratio -/

/-- Writing the one-step inverse coupling as `u' = u·q` with the quadratic-form coefficient ratio `q` (ratio of coarse to fine form
in the flux direction `v`), the ratio window `1 − 3b/(2u) ≤ q ≤ 1 − b/(2u)` is equivalent to the (H-β) window
`u − 3b/2 ≤ u' ≤ u − b/2` (`u > 0`). -/
theorem coupling_step_iff_ratio (u q b : ℝ) (hu : 0 < u) :
    (1 - 3 * b / (2 * u) ≤ q ∧ q ≤ 1 - b / (2 * u)) ↔
      (u - 3 * b / 2 ≤ u * q ∧ u * q ≤ u - b / 2) := by
  have h1 : u * (1 - 3 * b / (2 * u)) = u - 3 * b / 2 := by field_simp
  have h2 : u * (1 - b / (2 * u)) = u - b / 2 := by field_simp
  constructor
  · rintro ⟨a, c⟩
    exact ⟨by rw [← h1]; exact mul_le_mul_of_nonneg_left a hu.le,
      by rw [← h2]; exact mul_le_mul_of_nonneg_left c hu.le⟩
  · rintro ⟨a, c⟩
    rw [← h1] at a; rw [← h2] at c
    exact ⟨le_of_mul_le_mul_left a hu, le_of_mul_le_mul_left c hu⟩

/-- The ratio via quadratic forms: coefficient `q = (y·S y)/(y·D₀ y)` (`S` the Schur complement, `D₀` the tree-level form).
If `y·D₀ y > 0`, the ratio window is equivalent to `(1 − 3b/(2u)) y·D₀ y ≤ y·S y ≤ (1 − b/(2u)) y·D₀ y`. -/
theorem ratio_window_iff_quadratic (sS d₀ u b : ℝ) (hd : 0 < d₀) :
    (1 - 3 * b / (2 * u) ≤ sS / d₀ ∧ sS / d₀ ≤ 1 - b / (2 * u)) ↔
      ((1 - 3 * b / (2 * u)) * d₀ ≤ sS ∧ sS ≤ (1 - b / (2 * u)) * d₀) := by
  rw [le_div_iff₀ hd, div_le_iff₀ hd]

/-! ## 4. Axiom check -/

#print axioms kp_sum_le_one
#print axioms completing_square
#print axioms block_psd_iff_schur
#print axioms schur_le_restricted
#print axioms core_posDef
#print axioms core_quadratic_le
#print axioms coupling_step_iff_ratio
#print axioms ratio_window_iff_quadratic

end BlockGaussianStep
