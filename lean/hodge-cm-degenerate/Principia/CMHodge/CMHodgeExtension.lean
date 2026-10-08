/-
  Finite-dimensional linear algebra and arithmetic behind the 464th run
  (Hodge lane, the vanishing of the obstruction on the real-multiplication directions).
  No geometry, no sheaves, no cycles, no Hodge conjecture.

  Contents.
  1. The core of Lemma 2: if the two commutator vectors are linearly independent,
     the only surviving deformations are those in the first block
     (this is "9 - 3*2 = 3": three of the nine real-multiplication directions).
  2. The concrete commutator vectors for the rank-one divisor u u^T with u = e_1,
     against the real-multiplication matrix, are linearly independent.
  3. The divisibility arithmetic of the c | y_k condition.
  4. The dimension bookkeeping of Ext^2 (chi gives no upper bound; under surjectivity
     the weak condition is equivalent to dim Ext^2 = 54).
-/
import Mathlib

namespace HodgeExtension

open scoped BigOperators

/-! ## 1. the core of Lemma 2 -/

/-- If `c₁, c₂ : ι → ℚ` are linearly independent in the strong pointwise sense below, then
`c₁ ⊗ A₁ + c₂ ⊗ A₂ = 0` forces `A₁ = 0` and `A₂ = 0`. -/
theorem tensor_pair_vanish {ι κ : Type*} (c₁ c₂ : ι → ℚ)
    (hindep : ∀ a b : ℚ, (∀ i, a * c₁ i + b * c₂ i = 0) → a = 0 ∧ b = 0)
    (A₁ A₂ : κ → ℚ)
    (h : ∀ i j, c₁ i * A₁ j + c₂ i * A₂ j = 0) :
    A₁ = 0 ∧ A₂ = 0 := by
  constructor
  · funext j
    have := hindep (A₁ j) (A₂ j) (by
      intro i
      have := h i j
      linarith [this])
    simpa using this.1
  · funext j
    have := hindep (A₁ j) (A₂ j) (by
      intro i
      have := h i j
      linarith [this])
    simpa using this.2

/-- The solution set of `c₁ ⊗ A₁ + c₂ ⊗ A₂ = 0` inside the three blocks
`(A₀, A₁, A₂)`: the first block is free, the other two are forced to zero. -/
theorem sol_set_eq {ι κ : Type*} (c₁ c₂ : ι → ℚ)
    (hindep : ∀ a b : ℚ, (∀ i, a * c₁ i + b * c₂ i = 0) → a = 0 ∧ b = 0) :
    {p : (κ → ℚ) × (κ → ℚ) × (κ → ℚ) | ∀ i j, c₁ i * p.2.1 j + c₂ i * p.2.2 j = 0}
      = {p : (κ → ℚ) × (κ → ℚ) × (κ → ℚ) | p.2.1 = 0 ∧ p.2.2 = 0} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact tensor_pair_vanish c₁ c₂ hindep p.2.1 p.2.2 h
  · intro h i j
    rw [h.1, h.2]
    simp

/-- The free block has dimension three (the "product" directions);
the nine real-multiplication directions are three such blocks. -/
theorem finrank_block : Module.finrank ℚ (Fin 3 → ℚ) = 3 := by simp

theorem nine_blocks : 3 * 3 = 9 := by norm_num

theorem twelve_split : 9 + 3 = 12 := by norm_num

/-! ## 2. the concrete commutator vectors -/

/-- The real-multiplication matrix (the companion-like symmetric integral matrix whose
characteristic polynomial is `x³ + x² − 6x − 7`). -/
def M : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 1, 0; 1, 2, 1; 0, 1, -2]

/-- The rank-one divisor `e₁ e₁ᵀ`. -/
def S1 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

theorem M_symm : M.transpose = M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M, Matrix.transpose]

theorem M_S1_not_comm : M * S1 ≠ S1 * M := by
  intro h
  have h01 : (M * S1) 0 1 = (S1 * M) 0 1 := by rw [h]
  simp [M, S1, Matrix.mul_apply, Fin.sum_univ_succ] at h01

/-- The two commutator vectors of `S1` in `∧²ℚ³ ≅ ℚ³`, read off as
`(C i j) ↦ (C 0 1, C 0 2, C 1 2)`. -/
def c1 : Fin 3 → ℚ := fun i => if i = 0 then -1 else 0
def c2 : Fin 3 → ℚ := fun i => if i = 0 then -1 else if i = 1 then -1 else 0

theorem c1_c2_indep : ∀ a b : ℚ, (∀ i, a * c1 i + b * c2 i = 0) → a = 0 ∧ b = 0 := by
  intro a b h
  have h1 := h 1
  have h0 := h 0
  simp [c1, c2] at h0 h1
  constructor <;> linarith

/-- Hence for the rank-one divisor `e₁ e₁ᵀ` only the first of the three blocks survives:
the surviving space is three-dimensional inside the nine. -/
theorem surviving_e1 :
    {p : (Fin 3 → ℚ) × (Fin 3 → ℚ) × (Fin 3 → ℚ) |
        ∀ i j, c1 i * p.2.1 j + c2 i * p.2.2 j = 0}
      = {p : (Fin 3 → ℚ) × (Fin 3 → ℚ) × (Fin 3 → ℚ) | p.2.1 = 0 ∧ p.2.2 = 0} :=
  sol_set_eq c1 c2 c1_c2_indep

/-! ## 3. the arithmetic of the `c ∣ y_k` condition -/

/-- The gcd of the 28 target coordinates. -/
def gcdTarget : ℕ := 3780

theorem gcdTarget_factor : gcdTarget = 2 ^ 2 * 3 ^ 3 * 5 * 7 := by norm_num [gcdTarget]

theorem dvd_105 : 105 ∣ gcdTarget := by norm_num [gcdTarget]
theorem dvd_108 : 108 ∣ gcdTarget := by norm_num [gcdTarget]
theorem not_dvd_112 : ¬ (112 ∣ gcdTarget) := by norm_num [gcdTarget]
theorem not_dvd_120 : ¬ (120 ∣ gcdTarget) := by norm_num [gcdTarget]
theorem not_dvd_113 : ¬ (113 ∣ gcdTarget) := by norm_num [gcdTarget]

/-- Of the four candidates left by the 461st run, exactly two survive the finer
coordinatewise divisibility test. -/
theorem candidates_filter :
    ({105, 108, 112, 120} : Finset ℕ).filter (fun c => c ∣ gcdTarget) = {105, 108} := by
  decide

/-- Necessity: if every multiplicity is divisible by `c` then `c` divides every
coordinate of the target, because the columns are integral. -/
theorem dvd_of_all_dvd {n : ℕ} (c : ℕ) (A : Fin n → ℤ) (y : Fin n → ℕ) (b : ℤ)
    (hy : ∀ k, (c : ℤ) ∣ (y k : ℤ)) (hb : ∑ k, A k * (y k : ℤ) = b) :
    (c : ℤ) ∣ b := by
  rw [← hb]
  exact Finset.dvd_sum (fun k _ => Dvd.dvd.mul_left (hy k) (A k))

/-! ## 4. the dimension bookkeeping of `Ext²` -/

/-- Six-dimensional Serre duality gives no upper bound on `ext²`: for every value of
`ext²` there are non-negative `ext¹, ext³` compatible with the Euler characteristic. -/
theorem no_upper_bound_from_chi (e2 : ℕ) :
    ∃ e1 e3 : ℕ, (2 * 1 - 2 * (e1 : ℤ) + 2 * (e2 : ℤ) - (e3 : ℤ)) = -495178790400 := by
  refine ⟨1, 2 * e2 + 495178790400, ?_⟩
  push_cast
  ring

/-- Under surjectivity of `ev`, the weak criterion of Question 11.4 (the kernel of `ev`
being as large as the annihilator of `ch`, i.e. of dimension `12`) is equivalent to
`dim Ext² = 54`.  Here `66 = dim HH²`, and `kerdim + rk = 66`. -/
theorem weak_iff_ext2_eq_54 (kerdim rk ext2 : ℕ)
    (hsum : kerdim + rk = 66) (hle : kerdim ≤ 12) (hsurj : ext2 = rk) :
    kerdim = 12 ↔ ext2 = 54 := by
  omega

/-- Without surjectivity only the lower bound survives. -/
theorem ext2_lower (rk ext2 : ℕ) (hrk : 54 ≤ rk) (hle : rk ≤ ext2) : 54 ≤ ext2 := le_trans hrk hle

/-- Full semi-regularity (injectivity of `σ` on all of `Ext²`) forces `ext² ≤ 495`,
the dimension of the target. -/
theorem ext2_le_of_injective {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (σ : V →ₗ[ℚ] W) (hinj : Function.Injective σ) (hW : Module.finrank ℚ W = 495) :
    Module.finrank ℚ V ≤ 495 := by
  have := LinearMap.finrank_le_finrank_of_injective (f := σ) hinj
  omega

/-- The count of the three groups of directions: `12 = 3 + 6 + 3`. -/
theorem twelve_as_three_groups : 3 + 6 + 3 = 12 := by norm_num

#print axioms tensor_pair_vanish
#print axioms sol_set_eq
#print axioms finrank_block
#print axioms M_symm
#print axioms M_S1_not_comm
#print axioms c1_c2_indep
#print axioms surviving_e1
#print axioms gcdTarget_factor
#print axioms candidates_filter
#print axioms dvd_of_all_dvd
#print axioms no_upper_bound_from_chi
#print axioms weak_iff_ext2_eq_54
#print axioms ext2_le_of_injective

end HodgeExtension
