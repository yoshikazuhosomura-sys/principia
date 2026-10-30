import Mathlib

/-!
# Summing the KP per-site sum directly with per-polymer activity bounds (sum split by class)

Put a per-polymer bound `|z γ| ≤ c · ε(cls γ)^{|supp γ|}` on the activity of polymer `γ`. `cls γ` is the class of the polymer
(e.g. a band of the largest eigenvalue μ_max of a principal submatrix of the projection), and `ε k` is the per-plaquette bound for that class
(e.g. the value of logMoment_le_per_face). If the number of polymers of class `k` and size `n` containing the point `x` is bounded by `N k n`, then

  `Σ_{γ ∋ x} |z γ| e^{2|supp γ|} ≤ c Σ_k Σ_{n ≤ M} N k n (ε k)^n e^{2n}`.

If the right-hand side is ≤ 1, the hypothesis `hsite` of KPToDobrushin.dobrushin_cond_of_kp holds as is.
`N k n` is a hypothesis supplied from outside (floating-point computation).
-/

namespace ClassSiteSum

open Finset

variable {P S κ : Type*} [DecidableEq S] [DecidableEq κ]

/-- Bound on the per-site sum, summed over fibres of class and size. -/
theorem site_sum_le_class_sum (supp : P → Finset S) (z : P → ℝ) (U : Finset P)
    (cls : P → κ) (K : Finset κ) (ε : κ → ℝ) (c : ℝ) (M : ℕ) (N : κ → ℕ → ℝ) (x : S)
    (hc : 0 ≤ c) (hε : ∀ k, 0 ≤ ε k)
    (hK : ∀ γ ∈ U, cls γ ∈ K) (hM : ∀ γ ∈ U, (supp γ).card ≤ M)
    (hz : ∀ γ ∈ U, |z γ| ≤ c * ε (cls γ) ^ (supp γ).card)
    (hN : ∀ k n, (((U.filter (fun s => x ∈ supp s)).filter
        (fun s => (cls s, (supp s).card) = (k, n))).card : ℝ) ≤ N k n) :
    ∑ γ ∈ U.filter (fun s => x ∈ supp s), |z γ| * Real.exp (2 * (supp γ).card)
      ≤ c * ∑ k ∈ K, ∑ n ∈ range (M + 1), N k n * (ε k ^ n * Real.exp (2 * n)) := by
  set V := U.filter (fun s => x ∈ supp s) with hV
  have hmaps : ∀ γ ∈ V, (cls γ, (supp γ).card) ∈ K ×ˢ range (M + 1) := by
    intro γ hγ
    rw [hV, mem_filter] at hγ
    rw [mem_product, mem_range]
    exact ⟨hK γ hγ.1, Nat.lt_succ_of_le (hM γ hγ.1)⟩
  have hstep1 : ∑ γ ∈ V, |z γ| * Real.exp (2 * (supp γ).card)
      ≤ ∑ γ ∈ V, c * (ε (cls γ) ^ (supp γ).card * Real.exp (2 * (supp γ).card)) := by
    apply sum_le_sum
    intro γ hγ
    rw [hV, mem_filter] at hγ
    have h := hz γ hγ.1
    have he : 0 ≤ Real.exp (2 * ((supp γ).card : ℝ)) := (Real.exp_pos _).le
    calc |z γ| * Real.exp (2 * (supp γ).card)
        ≤ c * ε (cls γ) ^ (supp γ).card * Real.exp (2 * (supp γ).card) :=
          mul_le_mul_of_nonneg_right h he
      _ = c * (ε (cls γ) ^ (supp γ).card * Real.exp (2 * (supp γ).card)) := by ring
  refine le_trans hstep1 ?_
  rw [← sum_fiberwise_of_maps_to hmaps, sum_product, mul_sum]
  apply sum_le_sum
  intro k _
  rw [mul_sum]
  apply sum_le_sum
  intro n _
  calc ∑ γ ∈ V.filter (fun s => (cls s, (supp s).card) = (k, n)),
        c * (ε (cls γ) ^ (supp γ).card * Real.exp (2 * (supp γ).card))
      = ∑ γ ∈ V.filter (fun s => (cls s, (supp s).card) = (k, n)),
          c * (ε k ^ n * Real.exp (2 * n)) := by
        apply sum_congr rfl
        intro γ hγ
        rw [mem_filter] at hγ
        have h1 : cls γ = k := (Prod.mk.inj hγ.2).1
        have h2 : (supp γ).card = n := (Prod.mk.inj hγ.2).2
        rw [h1, h2]
    _ = ((V.filter (fun s => (cls s, (supp s).card) = (k, n))).card : ℝ) *
          (c * (ε k ^ n * Real.exp (2 * n))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ N k n * (c * (ε k ^ n * Real.exp (2 * n))) := by
        apply mul_le_mul_of_nonneg_right (hN k n)
        exact mul_nonneg hc (mul_nonneg (pow_nonneg (hε k) n) (Real.exp_pos _).le)
    _ = c * (N k n * (ε k ^ n * Real.exp (2 * n))) := by ring

/-- If the right-hand side (independent of the point) is ≤ 1, the KP per-site condition `hsite` holds. -/
theorem hsite_of_class_sum (supp : P → Finset S) (z : P → ℝ) (U : Finset P)
    (cls : P → κ) (K : Finset κ) (ε : κ → ℝ) (c : ℝ) (M : ℕ) (N : κ → ℕ → ℝ)
    (hc : 0 ≤ c) (hε : ∀ k, 0 ≤ ε k)
    (hK : ∀ γ ∈ U, cls γ ∈ K) (hM : ∀ γ ∈ U, (supp γ).card ≤ M)
    (hz : ∀ γ ∈ U, |z γ| ≤ c * ε (cls γ) ^ (supp γ).card)
    (hN : ∀ x k n, (((U.filter (fun s => x ∈ supp s)).filter
        (fun s => (cls s, (supp s).card) = (k, n))).card : ℝ) ≤ N k n)
    (hone : c * ∑ k ∈ K, ∑ n ∈ range (M + 1), N k n * (ε k ^ n * Real.exp (2 * n)) ≤ 1) :
    ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1 := fun x =>
  le_trans (site_sum_le_class_sum supp z U cls K ε c M N x hc hε hK hM hz (hN x)) hone

/-- With a single class the sum reduces to the sum over sizes `Σ_n N n ε^n e^{2n}` (the form of the sum of S_n). -/
theorem single_class_sum (N : ℕ → ℝ) (ε c : ℝ) (M : ℕ) :
    c * ∑ k ∈ ({()} : Finset Unit), ∑ n ∈ range (M + 1), (fun _ => N) k n * (ε ^ n * Real.exp (2 * n))
      = c * ∑ n ∈ range (M + 1), N n * (ε ^ n * Real.exp (2 * n)) := by
  simp

/-- Geometric tail: if the terms of size `n > n₀` are ≤ `A r^{n-n₀}` (`0 ≤ r < 1`), their sum is ≤ `A r/(1-r)`.
(The extrapolation S_{n+1}/S_n ≤ r put into the sum.) -/
theorem tail_le_of_ratio (A r : ℝ) (n₀ M : ℕ) (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℕ → ℝ) (hs : ∀ n ∈ Ico (n₀ + 1) (M + 1), s n ≤ A * r ^ (n - n₀)) :
    ∑ n ∈ Ico (n₀ + 1) (M + 1), s n ≤ A * (r / (1 - r)) := by
  have hK : ∑ k ∈ range (M + 1 - (n₀ + 1)), r ^ k ≤ 1 / (1 - r) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := M + 1 - (n₀ + 1)) hr0 hr1
    rw [← range_eq_Ico, pow_zero] at h
    exact h
  calc ∑ n ∈ Ico (n₀ + 1) (M + 1), s n
      ≤ ∑ n ∈ Ico (n₀ + 1) (M + 1), A * r ^ (n - n₀) := sum_le_sum hs
    _ = ∑ k ∈ range (M + 1 - (n₀ + 1)), A * r ^ (n₀ + 1 + k - n₀) := sum_Ico_eq_sum_range _ _ _
    _ = ∑ k ∈ range (M + 1 - (n₀ + 1)), (A * r) * r ^ k := by
        apply sum_congr rfl
        intro k _
        rw [show n₀ + 1 + k - n₀ = k + 1 by omega, pow_succ]
        ring
    _ = (A * r) * ∑ k ∈ range (M + 1 - (n₀ + 1)), r ^ k := by rw [mul_sum]
    _ ≤ (A * r) * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hK (mul_nonneg hA hr0)
    _ = A * (r / (1 - r)) := by ring

end ClassSiteSum

#print axioms ClassSiteSum.site_sum_le_class_sum
#print axioms ClassSiteSum.hsite_of_class_sum
#print axioms ClassSiteSum.single_class_sum
#print axioms ClassSiteSum.tail_le_of_ratio
