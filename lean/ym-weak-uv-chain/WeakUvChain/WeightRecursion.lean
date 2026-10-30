/-
Per-step weight arithmetic for premise 3. Single file; checks with `import Mathlib` only.

  The step-k weight is a_k|A| + c_k|∂A| (∂ = inner boundary edges of the blocks, the ∂ of BoundaryRegulator).
  Under one coarse-graining step the image size satisfies |β(A)| ≤ |A|/L_d + |∂A| (BoundaryRegulator.image_card_boundary).
  The coarse boundary count is passed as a geometric hypothesis |∂β(A)| ≤ γ|A| + δ|∂A| (γ, δ arguments).
  §1 One step: a′ + δc′ ≤ c and a′/L_d + γc′ ≤ a − b′ ⇒ a′|β(A)| + c′|∂β(A)| ≤ (a − b′)|A| + c|∂A|
     (for γ = δ = 0 this is the original condition a′ ≤ c, a′/L_d ≤ a − b′).
  §2 Glue with the conclusion of BoundaryRegulator (finite-set form; two copies placed side by side).
  §3 All steps: if the coefficient sequence (a_k, c_k, b_k) satisfies the per-step inequalities and b_k > d ln L,
     then contraction L_d e^{−b_k} < 1 at every step.
  §4 Sufficient condition for stationarity: if 0 ≤ δ < 1, c(1 − δ) ≥ a and b′ = a(1 − 1/L_d) − γc > d ln L, then
     constant coefficients (a, c) are preserved at all steps (b′ = a − a′/L_d is the case γ = 0).
  §5 Obstruction: if δ ≥ 1, there is no infinite nonnegative sequence c_k keeping a_k ≥ α > 0
     (the boundary coefficient drops by α per step).
  §6 Boundary supply: if a fresh surface cost s_k|∂A| (of the type of the surface cost of large-field holes) is added at
     each step, the recursion is a_{k+1} + δc_{k+1} ≤ c_k + s_k and the stationarity condition is s ≥ a − (1 − δ)c
     (valid also for δ ≥ 1).
-/
import Mathlib

namespace WeightRecursion

open Finset

set_option linter.unusedSectionVars false

/-! ## 1. One-step inequality -/

/-- One step: the weight is transported, from the image bound, the boundary hand-over and the coefficient recursion. -/
theorem weight_step (nA nBd nB nBd' Ld γ δ a c a' c' b' : ℝ)
    (hL : 0 < Ld) (hnA : 0 ≤ nA) (hnBd : 0 ≤ nBd) (ha' : 0 ≤ a') (hc' : 0 ≤ c')
    (himg : nB ≤ nA / Ld + nBd) (hbd : nBd' ≤ γ * nA + δ * nBd)
    (hc : a' + δ * c' ≤ c) (ha : a' / Ld + γ * c' ≤ a - b') :
    a' * nB + c' * nBd' ≤ (a - b') * nA + c * nBd := by
  have h1 := mul_le_mul_of_nonneg_left himg ha'
  have h2 := mul_le_mul_of_nonneg_left hbd hc'
  have e : a' * (nA / Ld + nBd) = (a' / Ld) * nA + a' * nBd := by field_simp
  rw [e] at h1
  have h3 : (a' / Ld + γ * c') * nA ≤ (a - b') * nA := mul_le_mul_of_nonneg_right ha hnA
  have h4 : (a' + δ * c') * nBd ≤ c * nBd := mul_le_mul_of_nonneg_right hc hnBd
  nlinarith [h1, h2, h3, h4]

/-- Case γ = δ = 0: the original conditions `a′ ≤ c`, `a′/L_d ≤ a − b′` (no weight on the coarse boundary, c′ = 0). -/
theorem weight_step_plain (nA nBd nB Ld a c a' b' : ℝ)
    (hL : 0 < Ld) (hnA : 0 ≤ nA) (hnBd : 0 ≤ nBd) (ha' : 0 ≤ a')
    (himg : nB ≤ nA / Ld + nBd) (hc : a' ≤ c) (ha : a' / Ld ≤ a - b') :
    a' * nB ≤ (a - b') * nA + c * nBd := by
  have := weight_step nA nBd nB 0 Ld 0 0 a c a' 0 b' hL hnA hnBd ha' le_rfl himg
    (by simp) (by simpa using hc) (by simpa using ha)
  simpa using this

/-! ## 2. Junction with BoundaryRegulator -/

section Glue

variable {S S' : Type*} [DecidableEq S] [DecidableEq S']

/-- Copy of BoundaryRegulator.image_card_boundary. -/
theorem image_card_boundary (β : S → S') (Sfin A : Finset S)
    (Edges : Finset (S × S)) (Ld : ℕ)
    (hblk : ∀ x', Ld ≤ (Sfin.filter (fun x => β x = x')).card)
    (hconn : ∀ x' ∈ A.image β, ¬ (Sfin.filter (fun x => β x = x') ⊆ A) →
      ∃ p ∈ Edges, p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2 ∧ β p.1 = x') :
    (A.image β).card * Ld ≤
      A.card + Ld * (Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2)).card := by
  set Full := (A.image β).filter (fun x' => Sfin.filter (fun x => β x = x') ⊆ A) with hFull
  set Part := (A.image β).filter (fun x' => ¬ (Sfin.filter (fun x => β x = x') ⊆ A)) with hPart
  set Bd := Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2) with hBd
  have hsplit : (A.image β).card = Full.card + Part.card := by
    rw [hFull, hPart]; exact (card_filter_add_card_filter_not _).symm
  have hfull : Full.card * Ld ≤ A.card := by
    have hdisj : Set.PairwiseDisjoint (Full : Set S') (fun x' => Sfin.filter (fun x => β x = x')) := by
      intro x' _ y' _ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro x hx hy
      exact hne ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
    have hsub : Full.biUnion (fun x' => Sfin.filter (fun x => β x = x')) ⊆ A := by
      intro x hx
      obtain ⟨x', hx', hxx'⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hx').2 hxx'
    have hc := card_le_card hsub
    rw [card_biUnion hdisj] at hc
    calc Full.card * Ld = ∑ _x' ∈ Full, Ld := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x' ∈ Full, (Sfin.filter (fun x => β x = x')).card := sum_le_sum fun x' _ => hblk x'
      _ ≤ A.card := hc
  have hpart : Part.card ≤ Bd.card := by
    have hsub : Part ⊆ Bd.image (fun p => β p.1) := by
      intro x' hx'
      rw [hPart, mem_filter] at hx'
      obtain ⟨p, hp, h1, h2, h3, h4⟩ := hconn x' hx'.1 hx'.2
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, h1, h2, h3⟩, h4⟩
    exact le_trans (card_le_card hsub) card_image_le
  rw [hsplit]
  calc (Full.card + Part.card) * Ld = Full.card * Ld + Ld * Part.card := by ring
    _ ≤ A.card + Ld * Bd.card := Nat.add_le_add hfull (Nat.mul_le_mul_left Ld hpart)

/-- Copy of BoundaryRegulator.image_card_boundary_real. -/
theorem image_card_boundary_real (nB nA nBd : ℕ) (Ld : ℕ) (hLd : 1 ≤ Ld)
    (h : nB * Ld ≤ nA + Ld * nBd) : (nB : ℝ) ≤ nA / Ld + nBd := by
  have hL : (0 : ℝ) < Ld := by exact_mod_cast hLd
  have h' : (nB : ℝ) * Ld ≤ nA + Ld * nBd := by exact_mod_cast h
  rw [← mul_le_mul_iff_of_pos_right hL]
  have e : ((nA : ℝ) / Ld + nBd) * Ld = nA + Ld * nBd := by field_simp
  rw [e]; exact h'

/-- Junction: the one step in finite-set form. From the hypotheses of BoundaryRegulator (block size, boundary edges of
partial blocks) and a geometric hypothesis on the coarse boundary count `nBd'`, get the weight bound
`a′|β(A)| + c′|∂β(A)| ≤ (a − b′)|A| + c|∂A|`. -/
theorem weight_step_sets (β : S → S') (Sfin A : Finset S) (Edges : Finset (S × S)) (Ld : ℕ)
    (hLd : 1 ≤ Ld)
    (hblk : ∀ x', Ld ≤ (Sfin.filter (fun x => β x = x')).card)
    (hconn : ∀ x' ∈ A.image β, ¬ (Sfin.filter (fun x => β x = x') ⊆ A) →
      ∃ p ∈ Edges, p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2 ∧ β p.1 = x')
    (nBd' γ δ a c a' c' b' : ℝ) (ha' : 0 ≤ a') (hc' : 0 ≤ c')
    (hbd : nBd' ≤ γ * A.card +
      δ * (Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2)).card)
    (hc : a' + δ * c' ≤ c) (ha : a' / Ld + γ * c' ≤ a - b') :
    a' * (A.image β).card + c' * nBd' ≤
      (a - b') * A.card + c * (Edges.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ β p.1 = β p.2)).card := by
  have himg := image_card_boundary_real _ _ _ Ld hLd
    (image_card_boundary β Sfin A Edges Ld hblk hconn)
  have hL : (0 : ℝ) < Ld := by exact_mod_cast hLd
  exact weight_step _ _ _ nBd' Ld γ δ a c a' c' b' hL (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ha' hc' himg hbd hc ha

end Glue

/-! ## 3. Contraction at all steps -/

/-- Contraction: if `b > d ln L` (`L > 0`) then `L^d e^{−b} < 1`. -/
theorem contraction_of_gap (L b : ℝ) (d : ℕ) (hL : 0 < L) (hb : d * Real.log L < b) :
    L ^ d * Real.exp (-b) < 1 := by
  have e : L ^ d = Real.exp (d * Real.log L) := by
    rw [Real.exp_nat_mul, Real.exp_log hL]
  rw [e, ← Real.exp_add]
  calc Real.exp (d * Real.log L + -b) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- Sequence of weight coefficients per step. `a k`, `c k` are the volume and boundary coefficients at step k, `b k` the decay gained at that step. -/
structure WeightSchedule (a c b : ℕ → ℝ) (Ld γ δ : ℝ) : Prop where
  a_nonneg : ∀ k, 0 ≤ a k
  c_nonneg : ∀ k, 0 ≤ c k
  /-- Boundary coefficient recursion: a_{k+1} + δ c_{k+1} ≤ c_k (for γ = δ = 0 the original c ≥ a′) -/
  boundary_rec : ∀ k, a (k + 1) + δ * c (k + 1) ≤ c k
  /-- Volume coefficient recursion: a_{k+1}/L_d + γ c_{k+1} ≤ a_k − b_k -/
  volume_rec : ∀ k, a (k + 1) / Ld + γ * c (k + 1) ≤ a k - b k

/-- All steps: if the coefficient sequence satisfies the per-step inequalities and `b_k > d ln L` at every step, then
at each step the weight is transported (given the image bound and boundary hand-over) and the contraction `L^d e^{−b_k} < 1` holds. -/
theorem all_steps (a c b : ℕ → ℝ) (L γ δ : ℝ) (d : ℕ) (hL : 1 ≤ L)
    (H : WeightSchedule a c b (L ^ d) γ δ) (hgap : ∀ k, d * Real.log L < b k) :
    (∀ k (nA nBd nB nBd' : ℝ), 0 ≤ nA → 0 ≤ nBd → nB ≤ nA / L ^ d + nBd →
        nBd' ≤ γ * nA + δ * nBd →
        a (k + 1) * nB + c (k + 1) * nBd' ≤ (a k - b k) * nA + c k * nBd) ∧
    (∀ k, L ^ d * Real.exp (-b k) < 1) := by
  have hL0 : 0 < L := by linarith
  have hLd : 0 < L ^ d := pow_pos hL0 d
  refine ⟨fun k nA nBd nB nBd' hnA hnBd himg hbd => ?_, fun k => contraction_of_gap L (b k) d hL0 (hgap k)⟩
  exact weight_step nA nBd nB nBd' (L ^ d) γ δ (a k) (c k) (a (k + 1)) (c (k + 1)) (b k) hLd hnA hnBd
    (H.a_nonneg _) (H.c_nonneg _) himg hbd (H.boundary_rec k) (H.volume_rec k)

/-! ## 4. Sufficient condition for a stationary schedule -/

/-- Sufficient condition for constant coefficients `(a, c)` with `b′ = a − a/L_d − γc` to be preserved at all steps:
`0 ≤ a`, `0 ≤ c`, `a + δc ≤ c` (for `δ < 1`: `c ≥ a/(1 − δ)`), `b′ > d ln L`. -/
theorem stationary_schedule (a c L γ δ : ℝ) (d : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbd : a + δ * c ≤ c) :
    WeightSchedule (fun _ => a) (fun _ => c) (fun _ => a - a / L ^ d - γ * c) (L ^ d) γ δ where
  a_nonneg _ := ha
  c_nonneg _ := hc
  boundary_rec _ := hbd
  volume_rec _ := by
    show a / L ^ d + γ * c ≤ a - (a - a / L ^ d - γ * c)
    linarith

/-- Stationary form for `δ < 1`: `c = a/(1 − δ)` gives `a + δc ≤ c` (with equality). -/
theorem stationary_boundary_coeff (a δ : ℝ) (hδ : δ < 1) :
    a + δ * (a / (1 - δ)) ≤ a / (1 - δ) := by
  have h : 0 < 1 - δ := by linarith
  have e : a + δ * (a / (1 - δ)) = a / (1 - δ) := by field_simp; ring
  rw [e]

/-- Stationary chain: if `0 ≤ a`, `δ < 1`, `c = a/(1 − δ)`, `a(1 − 1/L^d) − γ a/(1 − δ) > d ln L`, then the weight is
transported and contraction holds at all steps (for γ = 0, b′ = a − a/L_d, i.e. a′ = a with b′ = a − a′/L_d). -/
theorem stationary_all_steps (a L γ δ : ℝ) (d : ℕ) (ha : 0 ≤ a) (hδ : δ < 1)
    (hL : 1 ≤ L)
    (hgap : d * Real.log L < a - a / L ^ d - γ * (a / (1 - δ))) :
    (∀ _k : ℕ, ∀ nA nBd nB nBd' : ℝ, 0 ≤ nA → 0 ≤ nBd → nB ≤ nA / L ^ d + nBd →
        nBd' ≤ γ * nA + δ * nBd →
        a * nB + a / (1 - δ) * nBd' ≤
          (a - (a - a / L ^ d - γ * (a / (1 - δ)))) * nA + a / (1 - δ) * nBd) ∧
    (∀ _k : ℕ, L ^ d * Real.exp (-(a - a / L ^ d - γ * (a / (1 - δ)))) < 1) := by
  have h1 : 0 < 1 - δ := by linarith
  have hc : 0 ≤ a / (1 - δ) := div_nonneg ha h1.le
  have H := stationary_schedule a (a / (1 - δ)) L γ δ d ha hc (stationary_boundary_coeff a δ hδ)
  have := all_steps (fun _ => a) (fun _ => a / (1 - δ)) (fun _ => a - a / L ^ d - γ * (a / (1 - δ)))
    L γ δ d hL H (fun _ => hgap)
  exact ⟨fun k => this.1 k, fun k => this.2 k⟩

/-! ## 5. Obstruction: for δ ≥ 1 the boundary coefficient cannot be maintained -/

/-- If `δ ≥ 1`, `c_k ≥ 0`, `a_{k+1} ≥ α`, then `c_k ≤ c_0 − kα`. -/
theorem boundary_coeff_decreases (a c : ℕ → ℝ) (δ α : ℝ) (hδ : 1 ≤ δ)
    (hc : ∀ k, 0 ≤ c k) (ha : ∀ k, α ≤ a (k + 1))
    (hrec : ∀ k, a (k + 1) + δ * c (k + 1) ≤ c k) : ∀ k : ℕ, c k ≤ c 0 - k * α := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hrec k
    have h2 : c (k + 1) ≤ δ * c (k + 1) := by nlinarith [hc (k + 1)]
    have h3 := ha k
    push_cast
    linarith

/-- Obstruction: for `δ ≥ 1` and `α > 0` there is no nonnegative sequence satisfying the per-step inequalities at all steps. -/
theorem no_schedule_of_delta_ge_one (a c : ℕ → ℝ) (δ α : ℝ) (hδ : 1 ≤ δ) (hα : 0 < α)
    (hc : ∀ k, 0 ≤ c k) (ha : ∀ k, α ≤ a (k + 1))
    (hrec : ∀ k, a (k + 1) + δ * c (k + 1) ≤ c k) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt (c 0 / α)
  have h := boundary_coeff_decreases a c δ α hδ hc ha hrec n
  have h' := hc n
  have : c 0 < n * α := by rwa [div_lt_iff₀ hα] at hn
  linarith

/-- Contraction needs `a_k > d ln L`: `b_k ≤ a_k − a_{k+1}/L_d − γ c_{k+1} ≤ a_k` (for nonnegative γ and coefficients). -/
theorem gap_le_volume_coeff (a c b : ℕ → ℝ) (Ld γ δ : ℝ) (hLd : 0 < Ld) (hγ : 0 ≤ γ)
    (H : WeightSchedule a c b Ld γ δ) (k : ℕ) : b k ≤ a k := by
  have h1 := H.volume_rec k
  have h2 : 0 ≤ a (k + 1) / Ld := div_nonneg (H.a_nonneg _) hLd.le
  have h3 : 0 ≤ γ * c (k + 1) := mul_nonneg hγ (H.c_nonneg _)
  linarith

/-! ## 6. Boundary supply -/

/-- Coefficient sequence with supply: at step k the cost `s k` (≥ 0) of freshly created surface is added to the boundary coefficient. -/
structure WeightScheduleSupply (a c b s : ℕ → ℝ) (Ld γ δ : ℝ) : Prop where
  a_nonneg : ∀ k, 0 ≤ a k
  c_nonneg : ∀ k, 0 ≤ c k
  boundary_rec : ∀ k, a (k + 1) + δ * c (k + 1) ≤ c k + s k
  volume_rec : ∀ k, a (k + 1) / Ld + γ * c (k + 1) ≤ a k - b k

/-- All steps with supply: if the fine weight can pay up to `(a_k − b_k)|A| + (c_k + s_k)|∂A|`, it is transported to the coarse weight,
and contraction holds when `b_k > d ln L`. -/
theorem all_steps_supply (a c b s : ℕ → ℝ) (L γ δ : ℝ) (d : ℕ) (hL : 1 ≤ L)
    (H : WeightScheduleSupply a c b s (L ^ d) γ δ) (hgap : ∀ k, d * Real.log L < b k) :
    (∀ k (nA nBd nB nBd' : ℝ), 0 ≤ nA → 0 ≤ nBd → nB ≤ nA / L ^ d + nBd →
        nBd' ≤ γ * nA + δ * nBd →
        a (k + 1) * nB + c (k + 1) * nBd' ≤ (a k - b k) * nA + (c k + s k) * nBd) ∧
    (∀ k, L ^ d * Real.exp (-b k) < 1) := by
  have hL0 : 0 < L := by linarith
  have hLd : 0 < L ^ d := pow_pos hL0 d
  refine ⟨fun k nA nBd nB nBd' hnA hnBd himg hbd => ?_, fun k => contraction_of_gap L (b k) d hL0 (hgap k)⟩
  exact weight_step nA nBd nB nBd' (L ^ d) γ δ (a k) (c k + s k) (a (k + 1)) (c (k + 1)) (b k) hLd
    hnA hnBd (H.a_nonneg _) (H.c_nonneg _) himg hbd (H.boundary_rec k) (H.volume_rec k)

/-- Sufficient condition for a stationary schedule with supply: constants `(a, c, s)` with `a + δc ≤ c + s` are preserved at all steps
with `b′ = a − a/L_d − γc` (this holds even for δ ≥ 1 provided `s ≥ a + (δ − 1)c`). -/
theorem stationary_schedule_supply (a c sv L γ δ : ℝ) (d : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbd : a + δ * c ≤ c + sv) :
    WeightScheduleSupply (fun _ => a) (fun _ => c) (fun _ => a - a / L ^ d - γ * c) (fun _ => sv)
      (L ^ d) γ δ where
  a_nonneg _ := ha
  c_nonneg _ := hc
  boundary_rec _ := hbd
  volume_rec _ := by
    show a / L ^ d + γ * c ≤ a - (a - a / L ^ d - γ * c)
    linarith

#print axioms weight_step
#print axioms weight_step_plain
#print axioms image_card_boundary
#print axioms image_card_boundary_real
#print axioms weight_step_sets
#print axioms contraction_of_gap
#print axioms all_steps
#print axioms stationary_schedule
#print axioms stationary_boundary_coeff
#print axioms stationary_all_steps
#print axioms boundary_coeff_decreases
#print axioms no_schedule_of_delta_ge_one
#print axioms gap_le_volume_coeff
#print axioms all_steps_supply
#print axioms stationary_schedule_supply

end WeightRecursion
