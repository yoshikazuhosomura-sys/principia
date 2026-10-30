/-
Assembly: connect, at the type level, the closed-ball trajectory of the class (window of the A-type Loc), the
small-field remainder and the large-field rarity to the fields of the chain structure.
The bodies of the four files LocProjectionAType, ClassStepRemainder, LargeFieldStep and UltravioletChain are placed in
one file unchanged (up to comments), with glue theorems at the end. Single file; checks with `import Mathlib` only.
-/
import Mathlib

/-!
# Projection onto the direction of the fixed-point action (A-type Loc) and contraction-mapping hypotheses

At a fixed point `a` of a degree-one homogeneous map `f` (the tree map = Schur complement), Euler's identity gives
`f' a = a`: the fixed-point action itself is the eigenvalue-1 (marginal) direction of the linearisation.
Taking Loc as `P x = φ x • a` (`φ a = 1`):

1. `P` is a projection, `x = P x + (x − P x)`, `φ (x − P x) = 0`.
2. If the linearisation `T` satisfies `T a = a` and `T (ker φ) ⊆ ker φ`, then `P T = T P` and
   `T^[n] x = φ x • a + T^[n] (x − P x)` (the β coordinate does not move; only the remainder is iterated).
3. If `‖T y‖ ≤ τ ‖y‖` on `ker φ` with `τ < 1`, the marginal direction is `a` alone
   (another direction `b` has `T^[n] b → a`; the difference `b − a` stays in the remainder).
4. The restriction of `T` to `ker φ` as a continuous linear map has `‖T_V‖ ≤ τ`, and `ker φ` is complete.
   Adding a Lipschitz remainder gives a map with a unique fixed point in `ker φ`
   (in the form of the contraction-mapping hypotheses `‖T‖ ≤ ρ`, `Lip R ≤ L`, `ρ + L < 1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LatticeGauge.LocProjection

open Function Filter Topology

/-! ## 1. Euler's identity -/

section Euler

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `f` is positively homogeneous of degree one (`f (t • x) = t • f x`, `t > 0`) and differentiable at `x`, then `f' x = f x`. -/
theorem euler_of_homogeneous {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) (hom : ∀ t : ℝ, 0 < t → f (t • x) = t • f x) :
    f' x = f x := by
  have h1 : HasDerivAt (fun t : ℝ => t • x) ((1 : ℝ) • x) 1 :=
    (hasDerivAt_id (1 : ℝ)).smul_const x
  rw [one_smul] at h1
  have hf1 : HasFDerivAt f f' ((1 : ℝ) • x) := by rwa [one_smul]
  have hg : HasDerivAt (fun t : ℝ => f (t • x)) (f' x) 1 := hf1.comp_hasDerivAt (1 : ℝ) h1
  have h2 : HasDerivAt (fun t : ℝ => t • f x) ((1 : ℝ) • f x) 1 :=
    (hasDerivAt_id (1 : ℝ)).smul_const (f x)
  rw [one_smul] at h2
  have hev : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] (fun t : ℝ => t • f x) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hom t ht
  exact hg.unique (h2.congr_of_eventuallyEq hev)

/-- A fixed point `f a = a` of a degree-one homogeneous map is an eigenvalue-1 (marginal) direction of the linearisation: `f' a = a`. -/
theorem marginal_of_fixed {f : E → E} {f' : E →L[ℝ] E} {a : E}
    (hf : HasFDerivAt f f' a) (hom : ∀ t : ℝ, 0 < t → f (t • a) = t • f a) (hfix : f a = a) :
    f' a = a := by
  rw [euler_of_homogeneous hf hom, hfix]

end Euler

/-! ## 2. The Schur complement (tree map) is homogeneous of degree one -/

section Schur

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- `A − B D⁻¹ C` is of degree one under `(A,B,C,D) ↦ (tA,tB,tC,tD)` (`t ≠ 0`, `D` invertible). -/
theorem schur_homogeneous (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ)
    (D : Matrix n n ℝ) (hD : IsUnit D.det) {t : ℝ} (ht : t ≠ 0) :
    t • A - (t • B) * (t • D)⁻¹ * (t • C) = t • (A - B * D⁻¹ * C) := by
  have hinv : (t • D)⁻¹ = t⁻¹ • D⁻¹ := by
    have := Matrix.inv_smul' D (Units.mk0 t ht) hD
    simpa [Units.smul_def] using this
  rw [hinv, smul_sub]
  congr 1
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [inv_mul_cancel₀ ht, mul_one]

end Schur

/-! ## 3. A-type projection `P x = φ x • a` and decomposition of the linearisation -/

section Proj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (φ : E →L[ℝ] ℝ) (a : E) (T : E →L[ℝ] E)

/-- Projection: `P (P x) = P x`. -/
theorem proj_idem (hφa : φ a = 1) (x : E) : φ (φ x • a) • a = φ x • a := by
  rw [map_smul, hφa, smul_eq_mul, mul_one]

/-- Decomposition: `x = P x + (1 − P) x` and `φ ((1 − P) x) = 0`. -/
theorem proj_decomp (hφa : φ a = 1) (x : E) :
    x = φ x • a + (x - φ x • a) ∧ φ (x - φ x • a) = 0 := by
  refine ⟨by abel, ?_⟩
  rw [map_sub, map_smul, hφa, smul_eq_mul, mul_one, sub_self]

/-- Step to step (not necessarily at a fixed point): if the input direction `a` (`φ a = 1`) maps to the output
direction `b` (`ψ b = 1`) (Euler: `T a_k = a_{k+1}`) and `T (ker φ) ⊆ ker ψ`, then the Loc coefficient is
carried unchanged: `ψ (T x) = φ x`. -/
theorem loc_comm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : F →L[ℝ] ℝ) (b : F) (S : E →L[ℝ] F) (hφa : φ a = 1) (hψb : ψ b = 1) (hSa : S a = b)
    (hker : ∀ y, φ y = 0 → ψ (S y) = 0) (x : E) : ψ (S x) = φ x := by
  obtain ⟨hx, hy⟩ := proj_decomp φ a hφa x
  have h := hker _ hy
  rw [map_sub, map_smul, hSa, map_sub, map_smul, hψb, smul_eq_mul, mul_one] at h
  linarith

/-- Step to step: `(1 − P_{k+1}) S = S (1 − P_k)`. -/
theorem comm_sub_proj {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : F →L[ℝ] ℝ) (b : F) (S : E →L[ℝ] F) (hφa : φ a = 1) (hψb : ψ b = 1) (hSa : S a = b)
    (hker : ∀ y, φ y = 0 → ψ (S y) = 0) (x : E) : S (x - φ x • a) = S x - ψ (S x) • b := by
  rw [map_sub, map_smul, hSa, loc_comm φ a ψ b S hφa hψb hSa hker]

/-- Under iteration the β coordinate (`φ`) does not move, and only the remainder is mapped by `T`:
`T^[n] x = φ x • a + T^[n] (x − φ x • a)`. -/
theorem iterate_split (hTa : T a = a) (n : ℕ) (x : E) :
    (⇑T)^[n] x = φ x • a + (⇑T)^[n] (x - φ x • a) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, map_add, map_smul, hTa]

/-- The contraction `‖T y‖ ≤ τ ‖y‖` on `ker φ` iterates to `τ^n`. -/
theorem iterate_contract_ker {τ : ℝ} (hτ : 0 ≤ τ) (hker : ∀ y, φ y = 0 → φ (T y) = 0)
    (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) (n : ℕ) (y : E) (hy : φ y = 0) :
    ‖(⇑T)^[n] y‖ ≤ τ ^ n * ‖y‖ ∧ φ ((⇑T)^[n] y) = 0 := by
  induction n with
  | zero => simp [hy]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [iterate_succ_apply']
    refine ⟨(hc _ h2).trans ?_, hker _ h2⟩
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hτ]

/-- Contraction of the linear part over `n` steps (the form of the `μ` hypothesis of `dist_iterate_le_mu`):
`‖T^[n] (x − P x)‖ ≤ τ^n ‖x − P x‖`. -/
theorem iterate_contract_remainder (hφa : φ a = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hker : ∀ y, φ y = 0 → φ (T y) = 0) (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) (n : ℕ) (x : E) :
    ‖(⇑T)^[n] (x - φ x • a)‖ ≤ τ ^ n * ‖x - φ x • a‖ :=
  (iterate_contract_ker φ T hτ hker hc n _ (proj_decomp φ a hφa x).2).1

/-- The marginal direction is unique: if `T v = v` and `φ v = 1`, then `v = a`. -/
theorem marginal_unique (hφa : φ a = 1) (hTa : T a = a) {τ : ℝ} (hτ1 : τ < 1)
    (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) {v : E} (hv : T v = v) (hφv : φ v = 1) : v = a := by
  have hy : φ (v - a) = 0 := by rw [map_sub, hφv, hφa, sub_self]
  have h := hc _ hy
  rw [map_sub, hv, hTa] at h
  have hn : ‖v - a‖ = 0 := by nlinarith [norm_nonneg (v - a)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

/-- Another direction `b` (`φ b = 1`, e.g. Pr type) approaches `a` under iteration:
`‖T^[n] b − a‖ ≤ τ^n ‖b − a‖`. The difference `b − a` stays on the remainder side. -/
theorem other_direction_drifts (hφa : φ a = 1) (hTa : T a = a) {τ : ℝ} (hτ : 0 ≤ τ)
    (hker : ∀ y, φ y = 0 → φ (T y) = 0) (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖)
    {b : E} (hφb : φ b = 1) (n : ℕ) : ‖(⇑T)^[n] b - a‖ ≤ τ ^ n * ‖b - a‖ := by
  have hs := iterate_split φ a T hTa n b
  rw [hφb, one_smul] at hs
  have e : (⇑T)^[n] b - a = (⇑T)^[n] (b - a) := by rw [hs]; abel_nf
  have hy : φ (b - a) = 0 := by rw [map_sub, hφb, hφa, sub_self]
  rw [e]
  exact (iterate_contract_ker φ T hτ hker hc n _ hy).1

/-- Another direction `b ≠ a` is not marginal (`τ < 1`). -/
theorem other_direction_not_fixed (hφa : φ a = 1) (hTa : T a = a) {τ : ℝ} (hτ1 : τ < 1)
    (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) {b : E} (hφb : φ b = 1) (hb : b ≠ a) : T b ≠ b :=
  fun h => hb (marginal_unique φ a T hφa hTa hτ1 hc h hφb)

end Proj

/-! ## 4. Linear part restricted to `ker φ`: contraction-mapping hypotheses -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (φ : E →L[ℝ] ℝ) (T : E →L[ℝ] E)

/-- Restriction of `T` to `ker φ` (when `T (ker φ) ⊆ ker φ`). -/
noncomputable def restrictKer (hker : ∀ y, φ y = 0 → φ (T y) = 0) :
    LinearMap.ker (φ : E →ₗ[ℝ] ℝ) →L[ℝ] LinearMap.ker (φ : E →ₗ[ℝ] ℝ) :=
  (T.comp (LinearMap.ker (φ : E →ₗ[ℝ] ℝ)).subtypeL).codRestrict (LinearMap.ker (φ : E →ₗ[ℝ] ℝ))
    (fun y => by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL,
        Submodule.coe_subtype, comp_apply, ContinuousLinearMap.coe_coe]
      exact hker _ (by simp))

/-- Form of hypothesis H1: the operator norm of the restricted linear part is at most `τ`. -/
theorem restrictKer_opNorm_le (hker : ∀ y, φ y = 0 → φ (T y) = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) : ‖restrictKer φ T hker‖ ≤ τ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hτ fun y => ?_
  rw [Submodule.coe_norm, Submodule.coe_norm]
  show ‖T y‖ ≤ τ * ‖(y : E)‖
  exact hc _ (by simp)

/-- On `ker φ`, the restricted linear part plus a Lipschitz remainder (`τ + L < 1`) has a unique fixed point
(`ker φ` is complete when `E` is). -/
theorem exists_unique_fixed_ker [CompleteSpace E] (hker : ∀ y, φ y = 0 → φ (T y) = 0)
    {τ L : ℝ} (hτ : 0 ≤ τ) (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖)
    (R : LinearMap.ker (φ : E →ₗ[ℝ] ℝ) → LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) (hR : ∀ x y, dist (R x) (R y) ≤ L * dist x y)
    (hlt : τ + L < 1) :
    ∃! w : LinearMap.ker (φ : E →ₗ[ℝ] ℝ), restrictKer φ T hker w + R w = w := by
  set TV := restrictKer φ T hker
  have hT := restrictKer_opNorm_le φ T hker hτ hc
  have hlip : LipschitzWith (Real.toNNReal (τ + L)) (fun x => TV x + R x) := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    calc dist (TV x + R x) (TV y + R y) ≤ dist (TV x) (TV y) + dist (R x) (R y) :=
          dist_add_add_le _ _ _ _
      _ ≤ τ * dist x y + L * dist x y := by
          refine add_le_add ?_ (hR x y)
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact (TV.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
      _ = (τ + L) * dist x y := by ring
  have hcw : ContractingWith (Real.toNNReal (τ + L)) (fun x => TV x + R x) :=
    ⟨by rw [Real.toNNReal_lt_one]; exact hlt, hlip⟩
  exact ⟨ContractingWith.fixedPoint _ hcw, ContractingWith.fixedPoint_isFixedPt hcw,
    fun y hy => ContractingWith.fixedPoint_unique hcw hy⟩

end Restrict


/-! ## 5. Degree-one homogeneity of the actual tree map (KKT plus gauge fixing) -/

section KKT

open Matrix

variable {n g c : Type*} [Fintype n] [Fintype g] [Fintype c] [DecidableEq g] [DecidableEq c]

/-- If the action kills the gauge directions (`Gᵀ H = 0`), the block constraint is invariant in the gauge directions
(`J G = 0`), and `Gᵀ G` is invertible, then the KKT solution is orthogonal to the gauge directions: `Gᵀ K = 0`. -/
theorem kkt_gauge_orthogonal (H : Matrix n n ℝ) (G : Matrix n g ℝ) (J : Matrix c n ℝ)
    (K : Matrix n c ℝ) (Λ : Matrix c c ℝ) (hGH : Gᵀ * H = 0) (hJG : J * G = 0)
    (hG : IsUnit (Gᵀ * G).det) (hkkt : (H + G * Gᵀ) * K + Jᵀ * Λ = 0) : Gᵀ * K = 0 := by
  have hGJ : Gᵀ * Jᵀ = 0 := by rw [← Matrix.transpose_mul, hJG, Matrix.transpose_zero]
  have h : (Gᵀ * G) * (Gᵀ * K) = 0 := by
    calc (Gᵀ * G) * (Gᵀ * K) = (Gᵀ * H) * K + (Gᵀ * G) * (Gᵀ * K) + (Gᵀ * Jᵀ) * Λ := by
          rw [hGH, hGJ, Matrix.zero_mul, Matrix.zero_mul, zero_add, add_zero]
      _ = Gᵀ * ((H + G * Gᵀ) * K + Jᵀ * Λ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hkkt, Matrix.mul_zero]
  have := congrArg (fun M => (Gᵀ * G)⁻¹ * M) h
  simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG] using this

/-- The same `K` also solves the KKT system for `t H` (with multiplier `t Λ`). -/
theorem kkt_scale (H : Matrix n n ℝ) (G : Matrix n g ℝ) (J : Matrix c n ℝ)
    (K : Matrix n c ℝ) (Λ : Matrix c c ℝ) (hGK : Gᵀ * K = 0)
    (hkkt : (H + G * Gᵀ) * K + Jᵀ * Λ = 0) (t : ℝ) :
    (t • H + G * Gᵀ) * K + Jᵀ * (t • Λ) = 0 := by
  have e : (H + G * Gᵀ) * K = H * K := by
    rw [Matrix.add_mul, Matrix.mul_assoc, hGK, Matrix.mul_zero, add_zero]
  have e2 : (t • H + G * Gᵀ) * K = t • (H * K) := by
    rw [Matrix.add_mul, Matrix.mul_assoc, hGK, Matrix.mul_zero, add_zero, Matrix.smul_mul]
  rw [e] at hkkt
  rw [e2, Matrix.mul_smul, ← smul_add, hkkt, smul_zero]

/-- The coarse tree action `Q₀(H) = Kᵀ H K` (`K` the unique KKT solution) is homogeneous of degree one in `H`:
`Q₀(t H) = t Q₀(H)`. This is the hypothesis `hom` of `euler_of_homogeneous` holding for the actual map. -/
theorem kkt_homogeneous (G : Matrix n g ℝ) (J : Matrix c n ℝ)
    (sol : Matrix n n ℝ → Matrix n c ℝ) (mult : Matrix n n ℝ → Matrix c c ℝ)
    (hsol : ∀ H : Matrix n n ℝ, (H + G * Gᵀ) * sol H + Jᵀ * mult H = 0 ∧ J * sol H = 1)
    (huniq : ∀ (H : Matrix n n ℝ) (K : Matrix n c ℝ) (Λ : Matrix c c ℝ), (H + G * Gᵀ) * K + Jᵀ * Λ = 0 → J * K = 1 → K = sol H)
    (H : Matrix n n ℝ) (hGH : Gᵀ * H = 0) (hJG : J * G = 0) (hG : IsUnit (Gᵀ * G).det) (t : ℝ) :
    (sol (t • H))ᵀ * (t • H) * sol (t • H) = t • ((sol H)ᵀ * H * sol H) := by
  obtain ⟨h1, h2⟩ := hsol H
  have hGK := kkt_gauge_orthogonal H G J (sol H) (mult H) hGH hJG hG h1
  have hs : sol H = sol (t • H) := huniq _ _ _ (kkt_scale H G J _ _ hGK h1 t) h2
  rw [← hs, Matrix.mul_smul, Matrix.smul_mul]

end KKT

/-! ## 6. Bridge: bi-infinite trajectory on `ker φ` of step-dependent maps (conclusion of the contraction-mapping framework)

The items from `pull` to `exists_unique_entire_orbit` below are copied from `ClassFixedPoint.lean` §5 (same proofs). -/

section Entire

variable {X : Type*} [MetricSpace X]

/-- The `m`-step composition ending at time `n`: `F (n−1) ∘ ⋯ ∘ F (n−m)`. -/
noncomputable def pull (F : ℤ → X → X) : ℤ → ℕ → X → X
  | _, 0, x => x
  | n, m + 1, x => F (n - 1) (pull F (n - 1) m x)

theorem pull_succ' (F : ℤ → X → X) (m : ℕ) : ∀ (n : ℤ) (x : X),
    pull F n (m + 1) x = pull F n m (F (n - m - 1) x) := by
  induction m with
  | zero => intro n x; simp [pull]
  | succ m ih =>
    intro n x
    show F (n - 1) (pull F (n - 1) (m + 1) x) = F (n - 1) (pull F (n - 1) m _)
    rw [ih]
    congr 3
    push_cast; ring

theorem pull_mem (F : ℤ → X → X) {S : Set X} (hS : ∀ k, Set.MapsTo (F k) S S) (m : ℕ) :
    ∀ (n : ℤ) (x : X), x ∈ S → pull F n m x ∈ S := by
  induction m with
  | zero => intro n x hx; exact hx
  | succ m ih => intro n x hx; exact hS _ (ih _ _ hx)

theorem dist_pull_le (F : ℤ → X → X) {S : Set X} (hS : ∀ k, Set.MapsTo (F k) S S) {K : ℝ}
    (hK0 : 0 ≤ K) (hF : ∀ k, ∀ a ∈ S, ∀ b ∈ S, dist (F k a) (F k b) ≤ K * dist a b) (m : ℕ) :
    ∀ (n : ℤ) (x y : X), x ∈ S → y ∈ S → dist (pull F n m x) (pull F n m y) ≤ K ^ m * dist x y := by
  induction m with
  | zero => intro n x y _ _; simp [pull]
  | succ m ih =>
    intro n x y hx hy
    refine (hF _ _ (pull_mem F hS m _ x hx) _ (pull_mem F hS m _ y hy)).trans ?_
    rw [pow_succ]
    nlinarith [ih (n - 1) x y hx hy]

theorem pull_orbit (F : ℤ → X → X) (u : ℤ → X) (hu : ∀ k, u (k + 1) = F k (u k)) (m : ℕ) :
    ∀ n : ℤ, u n = pull F n m (u (n - m)) := by
  induction m with
  | zero => intro n; simp [pull]
  | succ m ih =>
    intro n
    rw [pull_succ', ih n]
    congr 1
    have : n - (m : ℤ) = (n - m - 1) + 1 := by ring
    rw [this, hu]
    congr 2
    push_cast; ring

theorem exists_unique_entire_orbit [CompleteSpace X] (F : ℤ → X → X) {S : Set X}
    (hSc : IsClosed S) {x₀ : X} (hx₀ : x₀ ∈ S) {D : ℝ} (hD : ∀ a ∈ S, ∀ b ∈ S, dist a b ≤ D)
    (hS : ∀ k, Set.MapsTo (F k) S S) {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hF : ∀ k, ∀ a ∈ S, ∀ b ∈ S, dist (F k a) (F k b) ≤ K * dist a b) :
    ∃! u : ℤ → X, (∀ k, u k ∈ S) ∧ ∀ k, u (k + 1) = F k (u k) := by
  have hcauchy : ∀ n : ℤ, CauchySeq (fun m : ℕ => pull F n m x₀) := by
    intro n
    refine cauchySeq_of_le_geometric K D hK1 (fun m => ?_)
    rw [pull_succ']
    have := dist_pull_le F hS hK0 hF m n x₀ (F (n - m - 1) x₀) hx₀ (hS _ hx₀)
    have hd := hD x₀ hx₀ _ (hS (n - m - 1) hx₀)
    have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
    calc _ ≤ K ^ m * dist x₀ (F (n - m - 1) x₀) := this
      _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
      _ = D * K ^ m := by ring
  choose h hh using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hmemS : ∀ n, h n ∈ S := fun n =>
    hSc.mem_of_tendsto (hh n) (Eventually.of_forall fun m => pull_mem F hS m n x₀ hx₀)
  have huniq : ∀ u : ℤ → X, (∀ k, u k ∈ S) → (∀ k, u (k + 1) = F k (u k)) → ∀ n, u n = h n := by
    intro u huS hu n
    have hlim : Tendsto (fun m : ℕ => pull F n m x₀) atTop (𝓝 (u n)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K ^ m * D) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const D
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      rw [pull_orbit F u hu m n, dist_comm]
      have := dist_pull_le F hS hK0 hF m n _ _ (huS (n - m)) hx₀
      have hd := hD _ (huS (n - m)) x₀ hx₀
      have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
      calc _ ≤ K ^ m * dist (u (n - m)) x₀ := this
        _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
    exact tendsto_nhds_unique hlim (hh n)
  have hinv : ∀ n, h (n + 1) = F n (h n) := by
    intro n
    have h1 : Tendsto (fun m : ℕ => pull F (n + 1) (m + 1) x₀) atTop (𝓝 (h (n + 1))) :=
      (hh (n + 1)).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun m : ℕ => pull F (n + 1) (m + 1) x₀) atTop (𝓝 (F n (h n))) := by
      have e : ∀ m, pull F (n + 1) (m + 1) x₀ = F n (pull F n m x₀) := by
        intro m; simp [pull]
      simp only [e]
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K * dist (pull F n m x₀) (h n)) atTop (𝓝 0) := by
        simpa using ((tendsto_iff_dist_tendsto_zero.1 (hh n)).const_mul K)
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      exact hF n _ (pull_mem F hS m n x₀ hx₀) _ (hmemS n)
    exact tendsto_nhds_unique h1 h2
  refine ⟨h, ⟨hmemS, hinv⟩, fun u ⟨huS, hu⟩ => funext (huniq u huS hu)⟩

end Entire

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E →L[ℝ] ℝ)

/-- One-step bridge: the map `v ↦ T_V v + R v` on `ker φ` preserves the closed ball `‖v‖ ≤ r` and contracts on it with
`τ + L` (the hypotheses `hT`, `hR`, `hR0`, `hball` of the closed-ball version of ClassFixedPoint, from the A-type decomposition). -/
theorem ball_step_from_loc_A (T : E →L[ℝ] E) (hker : ∀ y, φ y = 0 → φ (T y) = 0)
    {τ L C r : ℝ} (hτ : 0 ≤ τ) (hc : ∀ y, φ y = 0 → ‖T y‖ ≤ τ * ‖y‖) (hL : 0 ≤ L)
    (R : LinearMap.ker (φ : E →ₗ[ℝ] ℝ) → LinearMap.ker (φ : E →ₗ[ℝ] ℝ))
    (hR : ∀ x ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      ∀ y ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r, dist (R x) (R y) ≤ L * dist x y)
    (hR0 : ‖R 0‖ ≤ C) (hr : 0 ≤ r) (hball : C + (τ + L) * r ≤ r) :
    Set.MapsTo (fun v => restrictKer φ T hker v + R v) (Metric.closedBall 0 r) (Metric.closedBall 0 r) ∧
    ∀ x ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      ∀ y ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      dist (restrictKer φ T hker x + R x) (restrictKer φ T hker y + R y) ≤ (τ + L) * dist x y := by
  set TV := restrictKer φ T hker
  have hT := restrictKer_opNorm_le φ T hker hτ hc
  have hlip : ∀ x ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      ∀ y ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      dist (TV x + R x) (TV y + R y) ≤ (τ + L) * dist x y := by
    intro x hx y hy
    calc dist (TV x + R x) (TV y + R y) ≤ dist (TV x) (TV y) + dist (R x) (R y) :=
          dist_add_add_le _ _ _ _
      _ ≤ τ * dist x y + L * dist x y := by
          refine add_le_add ?_ (hR x hx y hy)
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact (TV.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
      _ = (τ + L) * dist x y := by ring
  refine ⟨fun x hx => ?_, hlip⟩
  have h0 : (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) ∈ Metric.closedBall 0 r := Metric.mem_closedBall_self hr
  have h1 := hlip x hx 0 h0
  simp only [map_zero, zero_add, dist_zero_right] at h1
  have hx' : ‖x‖ ≤ r := by simpa using hx
  have h2 : ‖TV x + R x‖ ≤ dist (TV x + R x) (R 0) + ‖R 0‖ := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le (TV x + R x) (R 0)
    linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  have : (τ + L) * ‖x‖ ≤ (τ + L) * r := mul_le_mul_of_nonneg_left hx' (by linarith)
  linarith

/-- **Form of the window conclusion**: for step-dependent linear parts `T k` (each preserving `ker φ` and contracting
there by `τ`) and remainders `R k` (`L`-Lipschitz on the closed ball, source `‖R k 0‖ ≤ C`), if `τ + L < 1` and
`C + (τ+L) r ≤ r`, there is a unique bi-infinite trajectory `u (k+1) = T_V k (u k) + R k (u k)` staying in the
closed ball of `ker φ`. The β coordinate (`φ`) is carried separately by `iterate_split` and `loc_comm`. -/
theorem window_from_loc_A [CompleteSpace E] (T : ℤ → E →L[ℝ] E)
    (hker : ∀ k y, φ y = 0 → φ (T k y) = 0) {τ L C r : ℝ} (hτ : 0 ≤ τ)
    (hc : ∀ k y, φ y = 0 → ‖T k y‖ ≤ τ * ‖y‖) (hL : 0 ≤ L)
    (R : ℤ → LinearMap.ker (φ : E →ₗ[ℝ] ℝ) → LinearMap.ker (φ : E →ₗ[ℝ] ℝ))
    (hR : ∀ k, ∀ x ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      ∀ y ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      dist (R k x) (R k y) ≤ L * dist x y)
    (hR0 : ∀ k, ‖R k 0‖ ≤ C) (hr : 0 ≤ r) (hlt : τ + L < 1) (hball : C + (τ + L) * r ≤ r) :
    ∃! u : ℤ → LinearMap.ker (φ : E →ₗ[ℝ] ℝ), (∀ k, u k ∈ Metric.closedBall 0 r) ∧
      ∀ k, u (k + 1) = restrictKer φ (T k) (hker k) (u k) + R k (u k) := by
  have hst := fun k => ball_step_from_loc_A φ (T k) (hker k) hτ (hc k) hL (R k) (hR k) (hR0 k) hr hball
  refine exists_unique_entire_orbit (fun k v => restrictKer φ (T k) (hker k) v + R k v)
    Metric.isClosed_closedBall (Metric.mem_closedBall_self hr) (D := 2 * r) ?_
    (fun k => (hst k).1) (by linarith) hlt (fun k => (hst k).2)
  intro x hx y hy
  have hx' : ‖x‖ ≤ r := by simpa using hx
  have hy' : ‖y‖ ≤ r := by simpa using hy
  calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
    _ ≤ 2 * r := by linarith

/-- Window arithmetic (`ℓ = 0`, remainder Lipschitz constant `L = 2 a r`): with `r = (1−τ)/(4a)`,
`τ + L < 1`, and if `C ≤ (1−τ)²/(8a)` then `C + (τ+L) r ≤ r`. -/
theorem window_radius {τ a C : ℝ} (hτ1 : τ < 1) (ha : 0 < a)
    (hC : C ≤ (1 - τ) ^ 2 / (8 * a)) :
    τ + 2 * a * ((1 - τ) / (4 * a)) < 1 ∧
      C + (τ + 2 * a * ((1 - τ) / (4 * a))) * ((1 - τ) / (4 * a)) ≤ (1 - τ) / (4 * a) := by
  have ha' : a ≠ 0 := ha.ne'
  have e1 : 2 * a * ((1 - τ) / (4 * a)) = (1 - τ) / 2 := by field_simp; ring
  rw [e1]
  refine ⟨by linarith, ?_⟩
  have e2 : (1 - τ) / (4 * a) - (τ + (1 - τ) / 2) * ((1 - τ) / (4 * a)) = (1 - τ) ^ 2 / (8 * a) := by
    field_simp; ring
  linarith

/-- Measured values (S* normalisation): with `τ = 0.6953`, `a = 4.3348`, `c₀ = 0.022`, `g² = 4/β` (SU(2)),
`β ≥ 33` gives `C = c₀ g² ≤ (1−τ)²/(8a)`. -/
theorem window_numbers (β : ℝ) (hβ : 33 ≤ β) :
    (0.022 : ℝ) * (4 / β) ≤ (1 - 0.6953) ^ 2 / (8 * 4.3348) := by
  have hβ0 : 0 < β := by linarith
  have h1 : (0.022 : ℝ) * (4 / β) ≤ 0.022 * (4 / 33) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hβ
  refine h1.trans ?_
  norm_num

end Bridge


/-! ## 7. Version with step-dependent Loc: `ker φ_k → ker φ_{k+1}`

The step actions live in one space `E`, and the Loc functional `φ k` (and direction `a k`) changes with the step.
The remainder set at step `k` is `S k = ker φ_k ∩ closed ball`. The map sends `S k` to `S (k+1)`. -/

section EntireSets

variable {X : Type*} [MetricSpace X]

theorem pull_mem_sets (F : ℤ → X → X) (S : ℤ → Set X)
    (hS : ∀ k, Set.MapsTo (F k) (S k) (S (k + 1))) (m : ℕ) :
    ∀ (n : ℤ) (x : X), x ∈ S (n - m) → pull F n m x ∈ S n := by
  induction m with
  | zero => intro n x hx; simpa [pull] using hx
  | succ m ih =>
    intro n x hx
    show F (n - 1) (pull F (n - 1) m x) ∈ S n
    have e1 : n - ((m + 1 : ℕ) : ℤ) = n - 1 - m := by push_cast; ring
    rw [e1] at hx
    have h3 := hS (n - 1) (ih (n - 1) x hx)
    have e2 : n - 1 + 1 = n := by ring
    rwa [e2] at h3

theorem dist_pull_le_sets (F : ℤ → X → X) (S : ℤ → Set X)
    (hS : ∀ k, Set.MapsTo (F k) (S k) (S (k + 1))) {K : ℝ} (hK0 : 0 ≤ K)
    (hF : ∀ k, ∀ a ∈ S k, ∀ b ∈ S k, dist (F k a) (F k b) ≤ K * dist a b) (m : ℕ) :
    ∀ (n : ℤ) (x y : X), x ∈ S (n - m) → y ∈ S (n - m) →
      dist (pull F n m x) (pull F n m y) ≤ K ^ m * dist x y := by
  induction m with
  | zero => intro n x y _ _; simp [pull]
  | succ m ih =>
    intro n x y hx hy
    have e1 : n - ((m + 1 : ℕ) : ℤ) = n - 1 - m := by push_cast; ring
    rw [e1] at hx hy
    show dist (F (n - 1) (pull F (n - 1) m x)) (F (n - 1) (pull F (n - 1) m y)) ≤ _
    refine (hF _ _ (pull_mem_sets F S hS m _ x hx) _ (pull_mem_sets F S hS m _ y hy)).trans ?_
    rw [pow_succ]
    nlinarith [ih (n - 1) x y hx hy]

/-- For step-dependent sets `S k` (closed, diameter ≤ `D`) and maps `F k : S k → S (k+1)` (contracting with `K < 1`),
there is a unique bi-infinite trajectory staying in `S`. -/
theorem exists_unique_entire_orbit_sets [CompleteSpace X] (F : ℤ → X → X) (S : ℤ → Set X)
    (hSc : ∀ k, IsClosed (S k)) (x₀ : ℤ → X) (hx₀ : ∀ k, x₀ k ∈ S k) {D : ℝ}
    (hD : ∀ k, ∀ a ∈ S k, ∀ b ∈ S k, dist a b ≤ D)
    (hS : ∀ k, Set.MapsTo (F k) (S k) (S (k + 1))) {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hF : ∀ k, ∀ a ∈ S k, ∀ b ∈ S k, dist (F k a) (F k b) ≤ K * dist a b) :
    ∃! u : ℤ → X, (∀ k, u k ∈ S k) ∧ ∀ k, u (k + 1) = F k (u k) := by
  set s : ℤ → ℕ → X := fun n m => pull F n m (x₀ (n - m)) with hs
  have hstep : ∀ (n : ℤ) (m : ℕ), F (n - m - 1) (x₀ (n - ((m + 1 : ℕ) : ℤ))) ∈ S (n - m) := by
    intro n m
    have e1 : n - ((m + 1 : ℕ) : ℤ) = n - m - 1 := by push_cast; ring
    have h := hS (n - m - 1) (by rw [← e1]; exact hx₀ _)
    have e2 : n - (m : ℤ) - 1 + 1 = n - m := by ring
    rwa [e2] at h
  have hcauchy : ∀ n : ℤ, CauchySeq (s n) := by
    intro n
    refine cauchySeq_of_le_geometric K D hK1 (fun m => ?_)
    simp only [hs]
    rw [pull_succ']
    have := dist_pull_le_sets F S hS hK0 hF m n (x₀ (n - m)) _ (hx₀ _) (hstep n m)
    have hd := hD _ _ (hx₀ (n - m)) _ (hstep n m)
    have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
    calc _ ≤ K ^ m * dist (x₀ (n - m)) _ := this
      _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
      _ = D * K ^ m := by ring
  choose h hh using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hsmem : ∀ n m, s n m ∈ S n := fun n m => pull_mem_sets F S hS m n _ (hx₀ _)
  have hmemS : ∀ n, h n ∈ S n := fun n =>
    (hSc n).mem_of_tendsto (hh n) (Eventually.of_forall fun m => hsmem n m)
  have huniq : ∀ u : ℤ → X, (∀ k, u k ∈ S k) → (∀ k, u (k + 1) = F k (u k)) → ∀ n, u n = h n := by
    intro u huS hu n
    have hlim : Tendsto (s n) atTop (𝓝 (u n)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K ^ m * D) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const D
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      simp only [hs]
      rw [pull_orbit F u hu m n]
      have := dist_pull_le_sets F S hS hK0 hF m n _ _ (hx₀ (n - m)) (huS (n - m))
      have hd := hD _ _ (hx₀ (n - m)) _ (huS (n - m))
      have hp : 0 ≤ K ^ m := pow_nonneg hK0 m
      calc _ ≤ K ^ m * dist (x₀ (n - m)) (u (n - m)) := this
        _ ≤ K ^ m * D := mul_le_mul_of_nonneg_left hd hp
    exact tendsto_nhds_unique hlim (hh n)
  have hinv : ∀ n, h (n + 1) = F n (h n) := by
    intro n
    have h1 : Tendsto (fun m : ℕ => s (n + 1) (m + 1)) atTop (𝓝 (h (n + 1))) :=
      (hh (n + 1)).comp (tendsto_add_atTop_nat 1)
    have e : ∀ m : ℕ, s (n + 1) (m + 1) = F n (s n m) := by
      intro m
      simp only [hs]
      have e1 : n + 1 - ((m + 1 : ℕ) : ℤ) = n - m := by push_cast; ring
      rw [e1]
      show F (n + 1 - 1) (pull F (n + 1 - 1) m _) = _
      rw [add_sub_cancel_right]
    have h2 : Tendsto (fun m : ℕ => s (n + 1) (m + 1)) atTop (𝓝 (F n (h n))) := by
      simp only [e]
      rw [tendsto_iff_dist_tendsto_zero]
      have ht : Tendsto (fun m : ℕ => K * dist (s n m) (h n)) atTop (𝓝 0) := by
        simpa using ((tendsto_iff_dist_tendsto_zero.1 (hh n)).const_mul K)
      refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) ht
      exact hF n _ (hsmem n m) _ (hmemS n)
    exact tendsto_nhds_unique h1 h2
  exact ⟨h, ⟨hmemS, hinv⟩, fun u ⟨huS, hu⟩ => funext (huniq u huS hu)⟩

end EntireSets

section BridgeStages

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Remainder set at step `k`: `ker φ_k ∩ closed ball`. -/
def stageSet (φ : ℤ → E →L[ℝ] ℝ) (r : ℝ) (k : ℤ) : Set E := {v | φ k v = 0 ∧ ‖v‖ ≤ r}

theorem isClosed_stageSet (φ : ℤ → E →L[ℝ] ℝ) (r : ℝ) (k : ℤ) : IsClosed (stageSet φ r k) :=
  (isClosed_eq (φ k).continuous continuous_const).inter (isClosed_le continuous_norm continuous_const)

/-- **Form of the window conclusion with step-dependent Loc**: the linear part `T k` maps `ker φ_k` into `ker φ_{k+1}`
and contracts there by `τ`. The remainder `R k` maps `ker φ_k ∩ closed ball` into `ker φ_{k+1}`, is `L`-Lipschitz
there, and `‖R k 0‖ ≤ C`. If `τ + L < 1` and `C + (τ+L) r ≤ r`, there is a unique bi-infinite trajectory
`u (k+1) = T k (u k) + R k (u k)` staying in `ker φ_k ∩ closed ball` at each step. No identification of the
per-step spaces with a single `ker φ` is needed. -/
theorem window_from_loc_A_stages [CompleteSpace E] (φ : ℤ → E →L[ℝ] ℝ) (T : ℤ → E →L[ℝ] E)
    (hker : ∀ k y, φ k y = 0 → φ (k + 1) (T k y) = 0) {τ L C r : ℝ} (hτ : 0 ≤ τ)
    (hc : ∀ k y, φ k y = 0 → ‖T k y‖ ≤ τ * ‖y‖) (hL : 0 ≤ L) (R : ℤ → E → E)
    (hRker : ∀ k v, v ∈ stageSet φ r k → φ (k + 1) (R k v) = 0)
    (hR : ∀ k, ∀ x ∈ stageSet φ r k, ∀ y ∈ stageSet φ r k, dist (R k x) (R k y) ≤ L * dist x y)
    (hR0 : ∀ k, ‖R k 0‖ ≤ C) (hr : 0 ≤ r) (hlt : τ + L < 1) (hball : C + (τ + L) * r ≤ r) :
    ∃! u : ℤ → E, (∀ k, u k ∈ stageSet φ r k) ∧ ∀ k, u (k + 1) = T k (u k) + R k (u k) := by
  have h0 : ∀ k, (0 : E) ∈ stageSet φ r k := fun k => ⟨map_zero _, by simpa using hr⟩
  have hlip : ∀ k, ∀ x ∈ stageSet φ r k, ∀ y ∈ stageSet φ r k,
      dist (T k x + R k x) (T k y + R k y) ≤ (τ + L) * dist x y := by
    intro k x hx y hy
    have hxy : φ k (x - y) = 0 := by rw [map_sub, hx.1, hy.1, sub_self]
    calc dist (T k x + R k x) (T k y + R k y) ≤ dist (T k x) (T k y) + dist (R k x) (R k y) :=
          dist_add_add_le _ _ _ _
      _ ≤ τ * dist x y + L * dist x y := by
          refine add_le_add ?_ (hR k x hx y hy)
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          exact hc k _ hxy
      _ = (τ + L) * dist x y := by ring
  have hmaps : ∀ k, Set.MapsTo (fun v => T k v + R k v) (stageSet φ r k) (stageSet φ r (k + 1)) := by
    intro k x hx
    refine ⟨by rw [map_add, hker k x hx.1, hRker k x hx, add_zero], ?_⟩
    have h1 := hlip k x hx 0 (h0 k)
    simp only [map_zero, zero_add, dist_zero_right] at h1
    have h2 : ‖T k x + R k x‖ ≤ dist (T k x + R k x) (R k 0) + ‖R k 0‖ := by
      rw [dist_eq_norm]
      have := norm_sub_norm_le (T k x + R k x) (R k 0)
      linarith
    have : (τ + L) * ‖x‖ ≤ (τ + L) * r := mul_le_mul_of_nonneg_left hx.2 (by linarith)
    linarith [hR0 k]
  refine exists_unique_entire_orbit_sets (fun k v => T k v + R k v) (stageSet φ r)
    (isClosed_stageSet φ r) (fun _ => 0) h0 (D := 2 * r) ?_ hmaps (by linarith) hlt hlip
  intro k x hx y hy
  calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
    _ ≤ 2 * r := by linarith [hx.2, hy.2]

/-- The β coordinate is carried by the per-step directions `a k`: if `T k (a k) = a (k+1)`, `φ (k+1) (a (k+1)) = 1`
and `T k (ker φ_k) ⊆ ker φ_{k+1}`, then `x = λ a_k + v` (`v ∈ ker φ_k`) gives `T k x = λ a_{k+1} + T k v`
with `T k v ∈ ker φ_{k+1}`. -/
theorem stage_split (φ : ℤ → E →L[ℝ] ℝ) (a : ℤ → E) (T : ℤ → E →L[ℝ] E)
    (hTa : ∀ k, T k (a k) = a (k + 1)) (hker : ∀ k y, φ k y = 0 → φ (k + 1) (T k y) = 0)
    (k : ℤ) (lam : ℝ) (v : E) (hv : φ k v = 0) :
    T k (lam • a k + v) = lam • a (k + 1) + T k v ∧ φ (k + 1) (T k v) = 0 :=
  ⟨by rw [map_add, map_smul, hTa], hker k v hv⟩

end BridgeStages

end LatticeGauge.LocProjection



namespace ClassStepRemainder

open Filter Topology

/-! ## 1. A bounded two-sided infinite orbit lies in a small ball -/

/-- If a nonnegative sequence `n : ℤ → ℝ` satisfies `n (k+1) ≤ C + λ n k` (`0 ≤ λ < 1`, `C ≥ 0`) and `n k ≤ r` for all `k`,
then `n k ≤ C/(1−λ)` for all `k`. -/
theorem bounded_orbit_small (n : ℤ → ℝ) (C lam r : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (hrec : ∀ k, n (k + 1) ≤ C + lam * n k) (hbd : ∀ k, n k ≤ r) :
    ∀ k, n k ≤ C / (1 - lam) := by
  intro k
  have h1 : 0 < 1 - lam := by linarith
  -- estimate going back j steps: n k ≤ C (1 − λ^j)/(1 − λ) + λ^j r
  have key : ∀ j : ℕ, n k ≤ C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r := by
    intro j
    induction j generalizing k with
    | zero =>
      simp only [pow_zero, sub_self, mul_zero, zero_div, one_mul, zero_add]
      exact hbd k
    | succ j ih =>
      have hk := hrec (k - 1)
      simp only [sub_add_cancel] at hk
      have ih' := ih (k - 1)
      have hlj : 0 ≤ lam ^ j := pow_nonneg hl0 j
      have e : C * (1 - lam ^ (j + 1)) / (1 - lam) + lam ^ (j + 1) * r =
          C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
        field_simp; ring
      rw [e]
      calc n k ≤ C + lam * n (k - 1) := hk
        _ ≤ C + lam * (C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) := by
            have := mul_le_mul_of_nonneg_left ih' hl0; linarith
  have hlim : Tendsto (fun j : ℕ => C * (1 - lam ^ j) / (1 - lam) + lam ^ j * r) atTop
      (𝓝 (C * (1 - 0) / (1 - lam) + 0 * r)) := by
    have hp : Tendsto (fun j : ℕ => lam ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hl1
    exact ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hp)).div_const _).add
      (hp.mul tendsto_const_nhds)
  have := ge_of_tendsto hlim (Eventually.of_forall key)
  simpa using this

/-! ## 2. Norm recursion inside the ball from a quadratic-type remainder -/

section Step

variable {E : Type*} [NormedAddCommGroup E]

/-- If `‖T v‖ ≤ τ ‖v‖`, `‖R v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ r`, then `‖T v + R v‖ ≤ C + (τ + a r) ‖v‖`. -/
theorem norm_step_le (T R : E → E) (τ a C r : ℝ) (ha : 0 ≤ a)
    (hT : ∀ v, ‖T v‖ ≤ τ * ‖v‖) (hR : ∀ v, ‖R v‖ ≤ C + a * ‖v‖ ^ 2)
    (v : E) (hv : ‖v‖ ≤ r) : ‖T v + R v‖ ≤ C + (τ + a * r) * ‖v‖ := by
  have h1 := norm_add_le (T v) (R v)
  have h2 := hT v
  have h3 := hR v
  have h4 : a * ‖v‖ ^ 2 ≤ a * r * ‖v‖ := by
    have : ‖v‖ ^ 2 ≤ r * ‖v‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hv (norm_nonneg v)
    nlinarith
  nlinarith

/-- A two-sided infinite orbit `v (k+1) = T k (v k) + R k (v k)` staying in the class ball of radius `r` satisfies
`‖v k‖ ≤ C/(1−λ)` at every step, if `λ = τ + a r < 1`. -/
theorem orbit_in_small_ball (T R : ℤ → E → E) (v : ℤ → E) (τ a C r : ℝ)
    (hτ : 0 ≤ τ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hlt : τ + a * r < 1)
    (hT : ∀ k w, ‖T k w‖ ≤ τ * ‖w‖) (hR : ∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2)
    (horbit : ∀ k, v (k + 1) = T k (v k) + R k (v k)) (hball : ∀ k, ‖v k‖ ≤ r) :
    ∀ k, ‖v k‖ ≤ C / (1 - (τ + a * r)) := by
  apply bounded_orbit_small (fun k => ‖v k‖) C (τ + a * r) r (by positivity) hlt _ hball
  intro k
  show ‖v (k + 1)‖ ≤ C + (τ + a * r) * ‖v k‖
  rw [horbit k]
  exact norm_step_le (T k) (R k) τ a C r ha (hT k) (hR k) (v k) (hball k)

end Step

/-! ## 3. The coupling remainder read in the β coordinate -/

section Coupling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The component of the one-step remainder `Rf` (full-space valued) along the β coordinate `φ` (continuous linear) is the small-field
remainder of the coupling flow. If `‖Rf v‖ ≤ C + a ‖v‖²` and `‖v‖ ≤ ρ`, then `|φ (Rf v)| ≤ ‖φ‖ (C + a ρ²)`. -/
theorem coupling_remainder_le (φ : E →L[ℝ] ℝ) (Rf : E → E) (C a ρ : ℝ) (ha : 0 ≤ a)
    (hR : ∀ v, ‖Rf v‖ ≤ C + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ ρ) :
    |φ (Rf v)| ≤ ‖φ‖ * (C + a * ρ ^ 2) := by
  have h1 : |φ (Rf v)| ≤ ‖φ‖ * ‖Rf v‖ := by
    have := φ.le_opNorm (Rf v); rwa [Real.norm_eq_abs] at this
  have h2 : ‖v‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have h3 : ‖Rf v‖ ≤ C + a * ρ ^ 2 := le_trans (hR v) (by nlinarith)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (norm_nonneg φ))

/-- §1–§3 combined: with source `C = c₀ / u` (`c₀ g²`, `g² = 1/u`) and `u ≥ u⋆ > 0`, the coupling remainder read at the radius
`ρ = C/(1 − λ)` of the orbit's small ball satisfies
`|r^s| ≤ ‖φ‖ c₀ (1 + a c₀ / ((1−λ)² u⋆)) / u` (the chain's `small_rem` form `C_s / u`). -/
theorem small_rem_form (φ : E →L[ℝ] ℝ) (Rf : E → E) (c₀ a lam u ustar : ℝ)
    (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hl1 : lam < 1) (hus : 0 < ustar) (hu : ustar ≤ u)
    (hR : ∀ v, ‖Rf v‖ ≤ c₀ / u + a * ‖v‖ ^ 2) (v : E) (hv : ‖v‖ ≤ (c₀ / u) / (1 - lam)) :
    |φ (Rf v)| ≤ (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) / u := by
  have hu0 : 0 < u := lt_of_lt_of_le hus hu
  have hl : 0 < 1 - lam := by linarith
  have h := coupling_remainder_le φ Rf (c₀ / u) a ((c₀ / u) / (1 - lam)) ha hR v hv
  refine le_trans h ?_
  have e : ‖φ‖ * (c₀ / u + a * ((c₀ / u) / (1 - lam)) ^ 2) =
      (‖φ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * u))) / u := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hu0.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : a * c₀ / ((1 - lam) ^ 2 * u) ≤ a * c₀ / ((1 - lam) ^ 2 * ustar) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hu (by positivity))
  linarith

end Coupling

/-! ## 5. Axiom check -/


end ClassStepRemainder


namespace LargeFieldStep

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-! ## 1. Rarity (Chernoff type) -/

section Rarity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If the exponential moment is at most `M` then `P(Y ≥ y_h) ≤ M e^{−t y_h}` (`t ≥ 0`). -/
theorem rarity_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (t yh M : ℝ)
    (ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hM : mgf Y μ t ≤ M) :
    μ.real {ω | yh ≤ Y ω} ≤ M * Real.exp (-t * yh) := by
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Y) yh ht hint
  have he : 0 ≤ Real.exp (-t * yh) := (Real.exp_pos _).le
  calc μ.real {ω | yh ≤ Y ω} ≤ Real.exp (-t * yh) * mgf Y μ t := h
    _ ≤ Real.exp (-t * yh) * M := mul_le_mul_of_nonneg_left hM he
    _ = M * Real.exp (-t * yh) := mul_comm _ _

/-- In the form of the chain event `{θ_h < I}`: the `ℝ≥0∞` bound `ofReal (M e^{−t θ_h})`. -/
theorem rarity_ennreal (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Ω → ℝ) (t θh M : ℝ)
    (ht : 0 ≤ t) (hint : Integrable (fun ω => Real.exp (t * I ω)) μ)
    (hM : mgf I μ t ≤ M) :
    μ {ω | θh < I ω} ≤ ENNReal.ofReal (M * Real.exp (-t * θh)) := by
  have hsub : {ω | θh < I ω} ⊆ {ω | θh ≤ I ω} := by
    intro ω h; exact le_of_lt (show θh < I ω from h)
  have h1 : μ {ω | θh < I ω} ≤ μ {ω | θh ≤ I ω} := measure_mono hsub
  have h2 := rarity_chernoff μ I t θh M ht hint hM
  refine le_trans h1 ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | θh ≤ I ω})]
  exact ENNReal.ofReal_le_ofReal (by rwa [measureReal_def] at h2)

end Rarity

/-! ## 2. Healing (deterministic) -/

/-- If the coarse-block defect satisfies `d′ ≤ Σ wᵢ dᵢ` (wᵢ ≥ 0, Σ wᵢ = 1), good parts (`i ∉ bad`) have defect `≤ δ`
and bad parts `≤ 2` (the real-part defect of a quaternion, 1 − cos θ ≤ 2), then `d′ ≤ δ + 2 Σ_{i ∈ bad} wᵢ`. -/
theorem healing_deterministic {ι : Type*} [DecidableEq ι] (s bad : Finset ι) (w d : ι → ℝ) (d' δ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hδ : 0 ≤ δ)
    (hconv : d' ≤ ∑ i ∈ s, w i * d i)
    (hgood : ∀ i ∈ s, i ∉ bad → d i ≤ δ) (hbad : ∀ i ∈ s, i ∈ bad → d i ≤ 2) :
    d' ≤ δ + 2 * ∑ i ∈ s.filter (· ∈ bad), w i := by
  have hpt : ∀ i ∈ s, w i * d i ≤ w i * δ + 2 * (if i ∈ bad then w i else 0) := by
    intro i hi
    by_cases hb : i ∈ bad
    · simp only [hb, if_true]
      have := mul_le_mul_of_nonneg_left (hbad i hi hb) (hw i hi)
      have : 0 ≤ w i * δ := mul_nonneg (hw i hi) hδ
      linarith
    · simp only [hb, if_false, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood i hi hb) (hw i hi)
  have hsumle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, ← Finset.mul_sum,
    ← Finset.sum_filter] at hsumle
  linarith

/-! ## 3. Healing (probabilistic, Markov) -/

section HealingProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For the bad weight `W(ω) = Σ wᵢ 1_{badᵢ}(ω)`, `P(W ≥ s) ≤ (Σ wᵢ P(badᵢ))/s` (`s > 0`). -/
theorem healing_markov (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (Bad : ι → Set Ω) (hB : ∀ i, MeasurableSet (Bad i))
    (s : ℝ) (hs : 0 < s) :
    μ.real {ω | s ≤ ∑ i ∈ S, w i * (Bad i).indicator 1 ω} ≤
      (∑ i ∈ S, w i * μ.real (Bad i)) / s := by
  set W : Ω → ℝ := fun ω => ∑ i ∈ S, w i * (Bad i).indicator 1 ω with hW
  have hW0 : ∀ ω, 0 ≤ W ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i hi)
    by_cases h : ω ∈ Bad i <;> simp [h]
  have hint : Integrable W μ := by
    apply integrable_finsetSum
    intro i _
    exact ((integrable_const (1 : ℝ)).indicator (hB i)).const_mul (w i) |>.congr
      (Filter.Eventually.of_forall fun ω => by simp [Set.indicator])
  have hEW : ∫ ω, W ω ∂μ = ∑ i ∈ S, w i * μ.real (Bad i) := by
    rw [hW, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
      congr 1
      have : (fun ω => (Bad i).indicator (1 : Ω → ℝ) ω) = (Bad i).indicator (fun _ => (1 : ℝ)) := rfl
      rw [this, integral_indicator_const _ (hB i), smul_eq_mul, mul_one]
    · intro i _
      exact ((integrable_const (1 : ℝ)).indicator (hB i)).const_mul (w i) |>.congr
        (Filter.Eventually.of_forall fun ω => by simp [Set.indicator])
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hW0) hint s
  rw [hEW] at hm
  rw [le_div_iff₀ hs]
  linarith

end HealingProb

/-! ## 4. KP threshold -/

/-- `M e^{−t y_h} ≤ 1/(2Δe²)` (the ε of the KP condition) holds when `y_h ≥ log(2Δe² M)/t` (`t > 0`, `M, Δ > 0`). -/
theorem kp_threshold (M t Δ yh : ℝ) (hM : 0 < M) (ht : 0 < t) (hΔ : 0 < Δ)
    (hy : Real.log (2 * Δ * Real.exp 1 ^ 2 * M) / t ≤ yh) :
    M * Real.exp (-t * yh) ≤ 1 / (2 * Δ * Real.exp 1 ^ 2) := by
  have hK : 0 < 2 * Δ * Real.exp 1 ^ 2 := by positivity
  have h1 : Real.log (2 * Δ * Real.exp 1 ^ 2 * M) ≤ t * yh := by
    have := (div_le_iff₀ ht).mp hy
    linarith [mul_comm yh t]
  have h2 : 2 * Δ * Real.exp 1 ^ 2 * M ≤ Real.exp (t * yh) := by
    rw [← Real.exp_log (by positivity : (0:ℝ) < 2 * Δ * Real.exp 1 ^ 2 * M)]
    exact Real.exp_le_exp.mpr h1
  rw [le_div_iff₀ hK]
  have h3 : Real.exp (-t * yh) * Real.exp (t * yh) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-t * yh) := Real.exp_pos _
  nlinarith

/-! ## 5. Axiom check -/


end LargeFieldStep


namespace UltravioletChain

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

/-! ## 1. (H-β): from the small-field step and the large-field step -/

/-- Per-step premises (for each bare inverse coupling `x`). `u k x` is the inverse coupling after `k` steps, `z k x` the large-field
activity, `w k x` the large-field supply generated at that step, `rs`, `rl` the small-field and large-field remainders of the coupling flow.
All fields are imposed only inside the domain (`u⋆ ≤ u` at all previous steps). -/
structure CouplingSteps (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ)
    (b C D ρ A B Z ustar : ℝ) : Prop where
  ustar_pos : 0 < ustar
  hb : 0 < b
  hC : 0 ≤ C
  hD : 0 ≤ D
  hρ : 0 ≤ ρ
  hA : 0 ≤ A
  hB : 0 ≤ B
  /-- S_k: one coupling step (leading flow term `b` and two remainders) -/
  flow : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → u (k + 1) x = u k x - b + rs k x + rl k x
  /-- S_k: small-field remainder `|r^s| ≤ C g²` -/
  small_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rs k x| ≤ C / u k x
  /-- L_k: supply from the large-field gas to the coupling -/
  large_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rl k x| ≤ D * z k x
  /-- L_k: activity recursion -/
  act_rec : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
    z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2
  act_nonneg : ∀ k x, 0 ≤ z k x
  act_init : ∀ x, z 0 x ≤ Z
  /-- L_k: rarity (the supply is larger for stronger coupling; `Φ` is decreasing on the domain) -/
  supply : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → w k x ≤ Φ (u k x)
  supply_anti : ∀ s t, ustar ≤ s → s ≤ t → Φ t ≤ Φ s
  /-- Invariant interval: even with the supply at the worst coupling `u⋆`, the activity stays ≤ `Z` -/
  fix : ρ * Z + A * Φ ustar + B * Z ^ 2 ≤ Z
  /-- Margin: the sum of the remainders is at most half the flow -/
  margin : C / ustar + D * Z ≤ b / 2

/-- Inside the domain the activity stays ≤ `Z`. -/
theorem activity_le {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → z k x ≤ Z := by
  intro k
  induction k with
  | zero => intro x _; exact H.act_init x
  | succ k ih =>
    intro x hdom
    have hdom' : ∀ j ≤ k, ustar ≤ u j x := fun j hj => hdom j (by omega)
    have hz := ih x hdom'
    have hw : w k x ≤ Φ ustar :=
      le_trans (H.supply k x hdom') (H.supply_anti _ _ le_rfl (hdom' k le_rfl))
    have h1 : ρ * z k x ≤ ρ * Z := mul_le_mul_of_nonneg_left hz H.hρ
    have h2 : A * w k x ≤ A * Φ ustar := mul_le_mul_of_nonneg_left hw H.hA
    have h3 : z k x ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ (H.act_nonneg k x) hz 2
    have h4 : B * z k x ^ 2 ≤ B * Z ^ 2 := mul_le_mul_of_nonneg_left h3 H.hB
    linarith [H.act_rec k x hdom', H.fix]

/-- The (H-β) form: inside the domain `u_k − 3b/2 ≤ u_{k+1} ≤ u_k − b/2`. -/
theorem hbeta_of_steps {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    (H : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2 := by
  intro k x hdom
  have hu : ustar ≤ u k x := hdom k le_rfl
  have hz := activity_le H k x hdom
  have hdiv : C / u k x ≤ C / ustar := div_le_div_of_nonneg_left H.hC H.ustar_pos hu
  have hDz : D * z k x ≤ D * Z := mul_le_mul_of_nonneg_left hz H.hD
  have hs := abs_le.mp (le_trans (H.small_rem k x hdom) hdiv)
  have hl := abs_le.mp (le_trans (H.large_rem k x hdom) hDz)
  have hf := H.flow k x hdom
  have hm := H.margin
  constructor <;> nlinarith [hs.1, hs.2, hl.1, hl.2]

/-! ## 2. (H-sf): from the rarity of large-field events -/

section SmallField

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Union bound: if finitely many large-field events `Bad b` (`b ∈ R`) each have probability `≤ ε`,
the small-field event (none occurs) has probability `≥ 1 − |R| ε`. -/
theorem small_field_mass_of_rarity (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (R : Finset ι) (Bad : ι → Set Ω) (ε : ℝ≥0∞)
    (hbad : ∀ b ∈ R, μ (Bad b) ≤ ε) (Good : Set Ω) (hgood : (⋃ b ∈ R, Bad b)ᶜ ⊆ Good) :
    1 - R.card * ε ≤ μ Good := by
  have hU : μ (⋃ b ∈ R, Bad b) ≤ R.card * ε := by
    calc μ (⋃ b ∈ R, Bad b) ≤ ∑ b ∈ R, μ (Bad b) := measure_biUnion_finset_le R Bad
      _ ≤ ∑ _b ∈ R, ε := Finset.sum_le_sum hbad
      _ = R.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  set U := ⋃ b ∈ R, Bad b with hUdef
  have h1 : (1 : ℝ≥0∞) ≤ μ U + μ Uᶜ := by
    rw [← measure_univ (μ := μ)]
    calc μ univ = μ (U ∪ Uᶜ) := by rw [union_compl_self]
      _ ≤ μ U + μ Uᶜ := measure_union_le _ _
  have h2 : 1 - μ U ≤ μ Uᶜ := tsub_le_iff_left.mpr h1
  calc 1 - R.card * ε ≤ 1 - μ U := tsub_le_tsub_left hU 1
    _ ≤ μ Uᶜ := h2
    _ ≤ μ Good := measure_mono hgood

/-- Invariant form: the large-field event is defined by an invariant `I b` of the field strength on each block (e.g. f₁ − f₂)
exceeding the threshold `θ_h`. The small-field event is `I b ≤ θ_h` for all `b ∈ R`. -/
theorem small_field_mass_invariant (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} (R : Finset ι) (I : ι → Ω → ℝ) (θh : ℝ) (ε : ℝ≥0∞)
    (hbad : ∀ b ∈ R, μ {ω | θh < I b ω} ≤ ε) :
    1 - R.card * ε ≤ μ {ω | ∀ b ∈ R, I b ω ≤ θh} := by
  apply small_field_mass_of_rarity μ R (fun b => {ω | θh < I b ω}) ε hbad
  intro ω hω
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hω
  exact hω

end SmallField

/-! ## 3. (H-reg): measure-theoretic part of the one-step lemma, gauge fixing, equicontinuity -/

section Regularity

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]

/-- For a bounded (`|F| ≤ M`) `L`-Lipschitz observable, the difference of expectations of the images under two block maps is at most
the expectation of `min(2M, L·d)` of their distance. -/
theorem expectation_diff_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : E → ℝ) (M L : ℝ) (hM : ∀ e, |F e| ≤ M)
    (hLip : ∀ e e', |F e - F e'| ≤ L * dist e e')
    (V₁ V₂ : Ω → E)
    (hi₁ : Integrable (fun ω => F (V₁ ω)) μ) (hi₂ : Integrable (fun ω => F (V₂ ω)) μ)
    (him : Integrable (fun ω => min (2 * M) (L * dist (V₁ ω) (V₂ ω))) μ) :
    |∫ ω, F (V₁ ω) ∂μ - ∫ ω, F (V₂ ω) ∂μ| ≤
      ∫ ω, min (2 * M) (L * dist (V₁ ω) (V₂ ω)) ∂μ := by
  rw [← integral_sub hi₁ hi₂]
  refine le_trans (abs_integral_le_integral_abs) (integral_mono (hi₁.sub hi₂).abs him ?_)
  intro ω
  simp only
  refine le_min ?_ (hLip _ _)
  have h1 := hM (V₁ ω); have h2 := hM (V₂ ω)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Splitting by the small-field event `G`: `∫ min(2M, L·D) ≤ ∫_G L·D + 2M μ(Gᶜ)`. -/
theorem split_small_field (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (M L : ℝ)
    (G : Set Ω) (hG : MeasurableSet G)
    (him : Integrable (fun ω => min (2 * M) (L * D ω)) μ)
    (hiD : Integrable (G.indicator fun ω => L * D ω) μ) :
    ∫ ω, min (2 * M) (L * D ω) ∂μ ≤
      ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + 2 * M * (μ Gᶜ).toReal := by
  have hic : Integrable (Gᶜ.indicator fun _ => 2 * M) μ :=
    (integrable_const (2 * M)).indicator hG.compl
  have hpt : ∀ ω, min (2 * M) (L * D ω) ≤
      G.indicator (fun ω => L * D ω) ω + Gᶜ.indicator (fun _ => 2 * M) ω := by
    intro ω
    by_cases h : ω ∈ G
    · rw [indicator_of_mem h, indicator_of_notMem (by simpa using h)]
      simp only [add_zero]; exact min_le_right _ _
    · rw [indicator_of_notMem h, indicator_of_mem (by simpa using h)]
      simp only [zero_add]; exact min_le_left _ _
  calc ∫ ω, min (2 * M) (L * D ω) ∂μ
      ≤ ∫ ω, (G.indicator (fun ω => L * D ω) ω + Gᶜ.indicator (fun _ => 2 * M) ω) ∂μ :=
        integral_mono him (hiD.add hic) hpt
    _ = ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + ∫ ω, Gᶜ.indicator (fun _ => 2 * M) ω ∂μ :=
        integral_add hiD hic
    _ = ∫ ω, G.indicator (fun ω => L * D ω) ω ∂μ + 2 * M * (μ Gᶜ).toReal := by
        rw [integral_indicator_const _ hG.compl]
        simp [Measure.real, smul_eq_mul, mul_comm]

/-- Gauge fixing G_k: the difference of a gauge-invariant `L`-Lipschitz observable is bounded by the distance measured in any gauge `g`
(the background-field estimate may be used in the gauge where it holds). -/
theorem gauge_choice {G : Type*} (act : G → E → E) (F : E → ℝ) (L : ℝ)
    (hinv : ∀ g e, F (act g e) = F e) (hLip : ∀ e e', |F e - F e'| ≤ L * dist e e')
    (g : G) (e e' : E) : |F e - F e'| ≤ L * dist (act g e) (act g e') := by
  rw [← hinv g e, ← hinv g e']; exact hLip _ _

end Regularity

section Equicontinuity

variable {X : Type*} [PseudoMetricSpace X]

/-- If the estimate splits into a term τ_n going to 0 with the lattice and a term Ω(r) going to 0 with the shift,
the form of the `equicontinuous` field of Theorem W follows. -/
theorem equicontinuous_of_split (D : Set X) (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (Ωr : ℝ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 0))
    (hΩ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η)
    (hsplit : ∀ n, ∀ d ∈ D, ∀ d' ∈ D, |s n d - s n d'| ≤ τ n + Ωr (dist d d')) :
    ∀ η > 0, ∃ δ > 0, ∀ d ∈ D, ∀ d' ∈ D, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hΩδ⟩ := hΩ (η / 2) (by positivity)
  refine ⟨δ, hδ, fun d hd d' hd' hdd => ?_⟩
  have hev : ∀ᶠ n in atTop, τ n ≤ η / 2 :=
    (hτ.eventually (Iic_mem_nhds (by positivity : (0:ℝ) < η / 2))).mono fun n hn => hn
  refine hev.mono fun n hn => ?_
  have := hsplit n d hd d' hd'
  have := hΩδ (dist d d') dist_nonneg hdd
  linarith

/-- The sum of two estimates going to 0 also goes to 0 (assembling τ and Ω from parts). -/
theorem vanishing_add (Ω₁ Ω₂ : ℝ → ℝ)
    (h₁ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₁ r ≤ η)
    (h₂ : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₂ r ≤ η) :
    ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ω₁ r + Ω₂ r ≤ η := by
  intro η hη
  obtain ⟨δ₁, hδ₁, k₁⟩ := h₁ (η / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, k₂⟩ := h₂ (η / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr hrδ => ?_⟩
  have := k₁ r hr (lt_of_lt_of_le hrδ (min_le_left _ _))
  have := k₂ r hr (lt_of_lt_of_le hrδ (min_le_right _ _))
  linarith

/-- The linear term `c·r` (smoothness of the background) goes to 0. -/
theorem vanishing_linear (c : ℝ) (hc : 0 ≤ c) :
    ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → c * r ≤ η := by
  intro η hη
  refine ⟨η / (c + 1), by positivity, fun r hr hrδ => ?_⟩
  have hc1 : 0 < c + 1 := by linarith
  have : r * (c + 1) < η := by rwa [lt_div_iff₀ hc1] at hrδ
  nlinarith

end Equicontinuity

/-! ## 4. The chain: from per-step premises to the three fields of Theorem W -/

section Chain

variable {X : Type*} [PseudoMetricSpace X]
variable {E : ℕ → Type*} [∀ m, MeasurableSpace (E m)]

/-- The bundled chain premises.
* `steps`: the coupling part of S_k and L_k (§1).
* `rarity`: the rarity in L_k. For each block `b ∈ R m` at scale `m`, the probability of the large-field event (invariant form) is
  ≤ `ε m` on fine enough lattices.
* `split`: the one-step estimate through S_k, G_k, (H-reg-lf) splits into a term going to 0 with the lattice and one going to 0 with the shift. -/
structure ChainHypotheses (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (b C D ρ A B Z ustar : ℝ)
    (ν : ℕ → ∀ m, Measure (E m)) {ι : ℕ → Type*} (R : ∀ m, Finset (ι m))
    (I : ∀ m, ι m → E m → ℝ) (θh : ℕ → ℝ) (ε : ℕ → ℝ≥0∞)
    (Dset : Set X) (s : ℕ → X → ℝ) (τ : ℕ → ℝ) (Ωr : ℝ → ℝ) : Prop where
  steps : CouplingSteps u z w rs rl Φ b C D ρ A B Z ustar
  prob : ∀ n m, IsProbabilityMeasure (ν n m)
  rarity : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m, ν n m {ω | θh m < I m i ω} ≤ ε m
  lattice_vanishing : Tendsto τ atTop (𝓝 0)
  shift_vanishing : ∀ η > 0, ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → Ωr r ≤ η
  split : ∀ n, ∀ d ∈ Dset, ∀ d' ∈ Dset, |s n d - s n d'| ≤ τ n + Ωr (dist d d')

/-- Chain theorem: from the per-step premises follow (H-β) (the `hS` form of the bare-coupling lemma (W0)), (H-sf) (the `small_field_mass` form, with the event
defined by the invariant) and (H-reg) (the `equicontinuous` form) of Theorem W. -/
theorem chain_to_hypotheses {u z w rs rl : ℕ → ℝ → ℝ} {Φ : ℝ → ℝ} {b C D ρ A B Z ustar : ℝ}
    {ν : ℕ → ∀ m, Measure (E m)} {ι : ℕ → Type*} {R : ∀ m, Finset (ι m)}
    {I : ∀ m, ι m → E m → ℝ} {θh : ℕ → ℝ} {ε : ℕ → ℝ≥0∞}
    {Dset : Set X} {s : ℕ → X → ℝ} {τ : ℕ → ℝ} {Ωr : ℝ → ℝ}
    (H : ChainHypotheses u z w rs rl Φ b C D ρ A B Z ustar ν R I θh ε Dset s τ Ωr) :
    (∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      u k x - 3 * b / 2 ≤ u (k + 1) x ∧ u (k + 1) x ≤ u k x - b / 2) ∧
    (∀ m, ∀ᶠ n in atTop,
      1 - (R m).card * ε m ≤ ν n m {ω | ∀ i ∈ R m, I m i ω ≤ θh m}) ∧
    (∀ η > 0, ∃ δ > 0, ∀ d ∈ Dset, ∀ d' ∈ Dset, dist d d' < δ →
      ∀ᶠ n in atTop, |s n d - s n d'| ≤ η) := by
  refine ⟨hbeta_of_steps H.steps, ?_, ?_⟩
  · intro m
    refine (H.rarity m).mono fun n hn => ?_
    have := H.prob n m
    exact small_field_mass_invariant (ν n m) (R m) (I m) (θh m) (ε m) hn
  · exact equicontinuous_of_split Dset s τ Ωr H.lattice_vanishing H.shift_vanishing H.split

end Chain

/-! ## 5. Axiom check -/


end UltravioletChain

namespace UltravioletAssembly

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- Glue 1: the window trajectory of the A-type Loc (bi-infinite trajectory staying in the closed ball `r` of `ker φ`)
enters the small closed ball `C/(1 − (τ + a r))` at every step if the remainder is of quadratic type
`‖R k w‖ ≤ C + a‖w‖²` (`τ + a r < 1`). -/
theorem window_orbit_small {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (φ : E →L[ℝ] ℝ) (T : ℤ → E →L[ℝ] E) (hker : ∀ k y, φ y = 0 → φ (T k y) = 0)
    {τ L C r a : ℝ} (hτ : 0 ≤ τ) (hc : ∀ k y, φ y = 0 → ‖T k y‖ ≤ τ * ‖y‖) (hL : 0 ≤ L)
    (R : ℤ → LinearMap.ker (φ : E →ₗ[ℝ] ℝ) → LinearMap.ker (φ : E →ₗ[ℝ] ℝ))
    (hR : ∀ k, ∀ x ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      ∀ y ∈ Metric.closedBall (0 : LinearMap.ker (φ : E →ₗ[ℝ] ℝ)) r,
      dist (R k x) (R k y) ≤ L * dist x y)
    (hR0 : ∀ k, ‖R k 0‖ ≤ C) (hr : 0 ≤ r) (hlt : τ + L < 1) (hball : C + (τ + L) * r ≤ r)
    (ha : 0 ≤ a) (hquad : ∀ k w, ‖R k w‖ ≤ C + a * ‖w‖ ^ 2) (hlt' : τ + a * r < 1) :
    ∃ u : ℤ → LinearMap.ker (φ : E →ₗ[ℝ] ℝ),
      (∀ k, u k ∈ Metric.closedBall 0 r) ∧
      (∀ k, u (k + 1) = LatticeGauge.LocProjection.restrictKer φ (T k) (hker k) (u k) + R k (u k)) ∧
      ∀ k, ‖u k‖ ≤ C / (1 - (τ + a * r)) := by
  obtain ⟨u, ⟨hb, horb⟩, -⟩ :=
    LatticeGauge.LocProjection.window_from_loc_A φ T hker hτ hc hL R hR hR0 hr hlt hball
  refine ⟨u, hb, horb, ?_⟩
  have hT : ∀ k w, ‖LatticeGauge.LocProjection.restrictKer φ (T k) (hker k) w‖ ≤ τ * ‖w‖ := by
    intro k w
    exact ((LatticeGauge.LocProjection.restrictKer φ (T k) (hker k)).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right
        (LatticeGauge.LocProjection.restrictKer_opNorm_le φ (T k) (hker k) hτ (hc k)) (norm_nonneg _))
  have hbn : ∀ k, ‖u k‖ ≤ r := by
    intro k; have := hb k; rwa [Metric.mem_closedBall, dist_zero_right] at this
  exact ClassStepRemainder.orbit_in_small_ball
    (fun k => LatticeGauge.LocProjection.restrictKer φ (T k) (hker k)) R u τ a C r hτ ha hr hlt'
    hT hquad horb hbn

/-- Glue 2: the `small_rem` field of the chain. If the small-field remainder of the coupling is the β coordinate
`ψ (Rf k x (v k x))` of the remainder, the class trajectory lies in the small closed ball, and the remainder is of
quadratic type, then `|rs k x| ≤ C_s / u k x`. -/
theorem small_rem_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E →L[ℝ] ℝ) (Rf : ℕ → ℝ → E → E) (v : ℕ → ℝ → E) (u rs : ℕ → ℝ → ℝ)
    (c₀ a lam ustar : ℝ) (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hl1 : lam < 1) (hus : 0 < ustar)
    (hrep : ∀ k x, rs k x = ψ (Rf k x (v k x)))
    (hquad : ∀ k x w, ‖Rf k x w‖ ≤ c₀ / u k x + a * ‖w‖ ^ 2)
    (horb : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → ‖v k x‖ ≤ (c₀ / u k x) / (1 - lam)) :
    ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      |rs k x| ≤ (‖ψ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) / u k x := by
  intro k x hdom
  rw [hrep k x]
  exact ClassStepRemainder.small_rem_form ψ (Rf k x) c₀ a lam (u k x) ustar hc₀ ha hl1 hus
    (hdom k le_rfl) (hquad k x) (v k x) (horb k x hdom)

/-- Glue 3: the `rarity` field of the chain. If at each scale and each block the exponential moment is ≤ `M m` on
sufficiently fine lattices, then the large-field event (invariant `I` exceeding `θ_h`) has probability ≤ `ofReal (M m · e^{−t θ_h})`. -/
theorem rarity_field {Em : ℕ → Type*} [∀ m, MeasurableSpace (Em m)]
    (ν : ℕ → ∀ m, Measure (Em m)) (hprob : ∀ n m, IsProbabilityMeasure (ν n m))
    {ι : ℕ → Type*} (R : ∀ m, Finset (ι m)) (I : ∀ m, ι m → Em m → ℝ) (θh M : ℕ → ℝ) (t : ℝ)
    (ht : 0 ≤ t)
    (hmgf : ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m,
      Integrable (fun ω => Real.exp (t * I m i ω)) (ν n m) ∧ mgf (I m i) (ν n m) t ≤ M m) :
    ∀ m, ∀ᶠ n in atTop, ∀ i ∈ R m,
      ν n m {ω | θh m < I m i ω} ≤ ENNReal.ofReal (M m * Real.exp (-t * θh m)) := by
  intro m
  refine (hmgf m).mono fun n hn i hi => ?_
  have := hprob n m
  exact LargeFieldStep.rarity_ennreal (ν n m) (I m i) t (θh m) (M m) ht (hn i hi).1 (hn i hi).2

/-- Glue 4: assemble the chain's `CouplingSteps` from the parts. The small-field remainder field uses the constant `C_s`
of Glue 2; the other fields are taken as premises. -/
theorem coupling_steps_of_parts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u z w rs rl : ℕ → ℝ → ℝ) (Φ : ℝ → ℝ) (b D ρ A B Z ustar : ℝ)
    (ψ : E →L[ℝ] ℝ) (Rf : ℕ → ℝ → E → E) (v : ℕ → ℝ → E) (c₀ a lam : ℝ)
    (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hl1 : lam < 1) (hus : 0 < ustar)
    (hrep : ∀ k x, rs k x = ψ (Rf k x (v k x)))
    (hquad : ∀ k x w', ‖Rf k x w'‖ ≤ c₀ / u k x + a * ‖w'‖ ^ 2)
    (horb : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → ‖v k x‖ ≤ (c₀ / u k x) / (1 - lam))
    (hb : 0 < b) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (flow : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → u (k + 1) x = u k x - b + rs k x + rl k x)
    (large_rem : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → |rl k x| ≤ D * z k x)
    (act_rec : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) →
      z (k + 1) x ≤ ρ * z k x + A * w k x + B * z k x ^ 2)
    (act_nonneg : ∀ k x, 0 ≤ z k x) (act_init : ∀ x, z 0 x ≤ Z)
    (supply : ∀ k x, (∀ j ≤ k, ustar ≤ u j x) → w k x ≤ Φ (u k x))
    (supply_anti : ∀ s t, ustar ≤ s → s ≤ t → Φ t ≤ Φ s)
    (fix : ρ * Z + A * Φ ustar + B * Z ^ 2 ≤ Z)
    (margin : (‖ψ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) / ustar + D * Z ≤ b / 2) :
    UltravioletChain.CouplingSteps u z w rs rl Φ b
      (‖ψ‖ * c₀ * (1 + a * c₀ / ((1 - lam) ^ 2 * ustar))) D ρ A B Z ustar :=
  { ustar_pos := hus, hb := hb,
    hC := by
      have hl : 0 < 1 - lam := by linarith
      positivity,
    hD := hD, hρ := hρ, hA := hA, hB := hB, flow := flow,
    small_rem := small_rem_field ψ Rf v u rs c₀ a lam ustar hc₀ ha hl1 hus hrep hquad horb,
    large_rem := large_rem, act_rec := act_rec, act_nonneg := act_nonneg, act_init := act_init,
    supply := supply, supply_anti := supply_anti, fix := fix, margin := margin }

end UltravioletAssembly


#print axioms LatticeGauge.LocProjection.euler_of_homogeneous
#print axioms LatticeGauge.LocProjection.marginal_of_fixed
#print axioms LatticeGauge.LocProjection.schur_homogeneous
#print axioms LatticeGauge.LocProjection.proj_idem
#print axioms LatticeGauge.LocProjection.proj_decomp
#print axioms LatticeGauge.LocProjection.loc_comm
#print axioms LatticeGauge.LocProjection.comm_sub_proj
#print axioms LatticeGauge.LocProjection.iterate_split
#print axioms LatticeGauge.LocProjection.iterate_contract_ker
#print axioms LatticeGauge.LocProjection.iterate_contract_remainder
#print axioms LatticeGauge.LocProjection.marginal_unique
#print axioms LatticeGauge.LocProjection.other_direction_drifts
#print axioms LatticeGauge.LocProjection.other_direction_not_fixed
#print axioms LatticeGauge.LocProjection.restrictKer_opNorm_le
#print axioms LatticeGauge.LocProjection.exists_unique_fixed_ker
#print axioms LatticeGauge.LocProjection.kkt_gauge_orthogonal
#print axioms LatticeGauge.LocProjection.kkt_scale
#print axioms LatticeGauge.LocProjection.kkt_homogeneous
#print axioms LatticeGauge.LocProjection.pull_succ'
#print axioms LatticeGauge.LocProjection.pull_mem
#print axioms LatticeGauge.LocProjection.dist_pull_le
#print axioms LatticeGauge.LocProjection.pull_orbit
#print axioms LatticeGauge.LocProjection.exists_unique_entire_orbit
#print axioms LatticeGauge.LocProjection.ball_step_from_loc_A
#print axioms LatticeGauge.LocProjection.window_from_loc_A
#print axioms LatticeGauge.LocProjection.window_radius
#print axioms LatticeGauge.LocProjection.window_numbers
#print axioms LatticeGauge.LocProjection.pull_mem_sets
#print axioms LatticeGauge.LocProjection.dist_pull_le_sets
#print axioms LatticeGauge.LocProjection.exists_unique_entire_orbit_sets
#print axioms LatticeGauge.LocProjection.isClosed_stageSet
#print axioms LatticeGauge.LocProjection.window_from_loc_A_stages
#print axioms LatticeGauge.LocProjection.stage_split
#print axioms ClassStepRemainder.bounded_orbit_small
#print axioms ClassStepRemainder.norm_step_le
#print axioms ClassStepRemainder.orbit_in_small_ball
#print axioms ClassStepRemainder.coupling_remainder_le
#print axioms ClassStepRemainder.small_rem_form
#print axioms LargeFieldStep.rarity_chernoff
#print axioms LargeFieldStep.rarity_ennreal
#print axioms LargeFieldStep.healing_deterministic
#print axioms LargeFieldStep.healing_markov
#print axioms LargeFieldStep.kp_threshold
#print axioms UltravioletChain.activity_le
#print axioms UltravioletChain.hbeta_of_steps
#print axioms UltravioletChain.small_field_mass_of_rarity
#print axioms UltravioletChain.small_field_mass_invariant
#print axioms UltravioletChain.expectation_diff_le
#print axioms UltravioletChain.split_small_field
#print axioms UltravioletChain.gauge_choice
#print axioms UltravioletChain.equicontinuous_of_split
#print axioms UltravioletChain.vanishing_add
#print axioms UltravioletChain.vanishing_linear
#print axioms UltravioletChain.chain_to_hypotheses
#print axioms UltravioletAssembly.window_orbit_small
#print axioms UltravioletAssembly.small_rem_field
#print axioms UltravioletAssembly.rarity_field
#print axioms UltravioletAssembly.coupling_steps_of_parts
