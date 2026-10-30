/-
Counting γ and δ of premise 3 for hypercubic blocks. Single file; checks with `import Mathlib` only.
Starts with a copy of WeightRecursion (unchanged up to comments); the junction is in BlockBoundaryCount at the end.

  Bound the coarse boundary ∂β(A) (edges inside coarse blocks leaving β(A)) by |∂β(A)| ≤ γ|A| + δ|∂A|.
  §1 Upper bound (general): if coarse points have degree ≤ deg then |∂β(A)| ≤ deg·|β(A)|. Valid pairs are
     (γ, δ) = (deg/L_d, deg) (from |β(A)| ≤ |A|/L_d + |∂A|), (deg, 0) (from |β(A)| ≤ |A|), and convex combinations.
  §2 Counts on ℤ⁴ (decide): block map x ↦ ⌊x/L⌋. Number of block-internal edges at a point x:
     nearest-neighbour: corner for L = 2: 4, corner for L = 4: 4, coarse interior point for L = 4: 8 (all 8)
     *-adjacency: corner for L = 2: 15, corner for L = 4: 15, coarse interior point for L = 4: 80 (all 80)
  §3 Lower constraint: validity on a one-point configuration (|A| = 1, |∂A| = p, |∂β(A)| = q) gives γ + pδ ≥ q.
     If p ≤ q and q ≥ 1, the sufficient condition for a stationary schedule (hgap of stationary_all_steps) fails even for δ < 1.
     In all four cases (scale factor 2 or 4, nearest-neighbour or *-adjacency) p ≤ q: no stationary weight without supply.
  §4 Lower bound on the supply: s ≥ a − (a(1 − 1/L_d) − b′)/q (for every valid pair and every c ≥ 0).
     With (γ, δ) = (deg, 0), c = (a(1 − 1/L_d) − b′)/deg, s = a − c one builds a stationary sequence with supply (to all_steps_supply).
  §5 Numbers: a is the large-field cost per plaquette −ln P₁(y_h) (P₁ = 4.7e^{−2y} (floating-point computation),
     y_h = 6.84 gives a ≈ 12.13 (arithmetic)).
     Lower bounds on s: ≥ 9.98 (factor 2, nearest), 11.31 (factor 4, nearest), 11.55 (factor 2, *), 12.04 (factor 4, *).
     Contraction needs a(1 − 1/L_d) > d ln L; the per-block reading a = −ln(96P₁)/16 ≈ 0.473 fails even for factor 2.
-/
import Mathlib

/-! Copy of WeightRecursion (unchanged up to comments) -/
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

namespace BlockBoundaryCount

open Finset

set_option linter.unusedSectionVars false

/-! ## 1. Upper bound (general) -/

section Upper

variable {S' S'' : Type*} [DecidableEq S'] [DecidableEq S'']

/-- If coarse points have degree ≤ deg, the number of coarse boundary edges is ≤ deg·|B|. -/
theorem coarse_boundary_le_deg (β' : S' → S'') (B : Finset S') (Edges' : Finset (S' × S'))
    (deg : ℕ) (hdeg : ∀ x', (Edges'.filter (fun p => p.1 = x')).card ≤ deg) :
    (Edges'.filter (fun p => p.1 ∈ B ∧ p.2 ∉ B ∧ β' p.1 = β' p.2)).card ≤ deg * B.card := by
  have hsub : Edges'.filter (fun p => p.1 ∈ B ∧ p.2 ∉ B ∧ β' p.1 = β' p.2) ⊆
      B.biUnion (fun x' => Edges'.filter (fun p => p.1 = x')) := by
    intro p hp
    rw [mem_filter] at hp
    exact mem_biUnion.mpr ⟨p.1, hp.2.1, mem_filter.mpr ⟨hp.1, rfl⟩⟩
  calc _ ≤ (B.biUnion (fun x' => Edges'.filter (fun p => p.1 = x'))).card := card_le_card hsub
    _ ≤ ∑ x' ∈ B, (Edges'.filter (fun p => p.1 = x')).card := card_biUnion_le
    _ ≤ ∑ _x' ∈ B, deg := sum_le_sum fun x' _ => hdeg x'
    _ = deg * B.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- Valid pair (deg/L_d, deg): from the image bound and the degree bound. -/
theorem pair_inner (nA nBd nB nBd' Ld deg : ℝ) (hdeg : 0 ≤ deg)
    (himg : nB ≤ nA / Ld + nBd) (hcoarse : nBd' ≤ deg * nB) :
    nBd' ≤ (deg / Ld) * nA + deg * nBd := by
  have := mul_le_mul_of_nonneg_left himg hdeg
  have e : deg * (nA / Ld + nBd) = (deg / Ld) * nA + deg * nBd := by ring
  linarith

/-- Valid pair (deg, 0): from |β(A)| ≤ |A| and the degree bound. -/
theorem pair_volume (nA nBd nB nBd' deg : ℝ) (hdeg : 0 ≤ deg)
    (himg : nB ≤ nA) (hcoarse : nBd' ≤ deg * nB) :
    nBd' ≤ deg * nA + 0 * nBd := by
  have := mul_le_mul_of_nonneg_left himg hdeg
  linarith

/-- Convex combination: for θ ∈ [0, 1], (deg(θ + (1−θ)/L_d), deg(1−θ)). -/
theorem pair_mix (nA nBd nB nBd' Ld deg θ : ℝ) (hdeg : 0 ≤ deg) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (himg : nB ≤ nA / Ld + nBd) (himg' : nB ≤ nA) (hcoarse : nBd' ≤ deg * nB) :
    nBd' ≤ deg * (θ + (1 - θ) / Ld) * nA + deg * (1 - θ) * nBd := by
  have h1 := mul_le_mul_of_nonneg_left himg' (mul_nonneg hdeg hθ0)
  have h2 := mul_le_mul_of_nonneg_left himg (mul_nonneg hdeg (by linarith : 0 ≤ 1 - θ))
  have e : deg * (θ + (1 - θ) / Ld) * nA + deg * (1 - θ) * nBd =
      deg * θ * nA + deg * (1 - θ) * (nA / Ld + nBd) := by ring
  rw [e]
  have e2 : deg * nB = deg * θ * nB + deg * (1 - θ) * nB := by ring
  linarith

end Upper

/-! ## 2. Counts on the four-dimensional lattice -/

/-- Block map x ↦ ⌊x/L⌋ (componentwise). -/
def blk (L : ℤ) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun j => x j / L

/-- Nearest neighbour: component `i` changed by ±1. -/
def nbr (x : Fin 4 → ℤ) (i : Fin 4) (s : Bool) : Fin 4 → ℤ :=
  Function.update x i (x i + if s then 1 else -1)

/-- Block-internal nearest-neighbour edges at the point `x` (counted by (component, direction)). -/
def innerNN (L : ℤ) (x : Fin 4 → ℤ) : Finset (Fin 4 × Bool) :=
  Finset.univ.filter (fun p => blk L (nbr x p.1 p.2) = blk L x)

/-- *-adjacency offsets {−1, 0, 1}⁴ ∖ {0}. -/
def starV : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)).erase 0

/-- Block-internal *-adjacency edges at the point `x`. -/
def innerStar (L : ℤ) (x : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  starV.filter (fun v => blk L (x + v) = blk L x)

theorem nn_total : (Finset.univ : Finset (Fin 4 × Bool)).card = 8 := by decide
theorem star_total : starV.card = 80 := by decide

/-- Scale factor 2: at the origin (corner of a 2-box) both the fine and coarse counts (β(0) = 0) are 4. -/
theorem nn_L2 : blk 2 0 = 0 ∧ (innerNN 2 0).card = 4 := by decide

/-- Scale factor 4: x = (4,4,4,4) is a box corner with count 4; the coarse point β(x) = (1,1,1,1) is interior to a coarse box with count 8. -/
theorem nn_L4 : blk 4 (fun _ => 4) = (fun _ => 1) ∧ (innerNN 4 (fun _ => 4)).card = 4 ∧
    (innerNN 4 (fun _ => 1)).card = 8 := by decide

theorem star_L2 : (innerStar 2 0).card = 15 := by decide

theorem star_L4 : (innerStar 4 (fun _ => 4)).card = 15 ∧ (innerStar 4 (fun _ => 1)).card = 80 := by
  decide

/-! ## 3. Lower constraint and the obstruction to stationary weights without supply -/

/-- Validity on one configuration: `|∂β(A)| ≤ γ|A| + δ|∂A|`. -/
def PairValidAt (γ δ nA nBd nBd' : ℝ) : Prop := nBd' ≤ γ * nA + δ * nBd

/-- If valid on a one-point configuration (|A| = 1, |∂A| = p, |∂β(A)| = q) and δ < 1, then γ/(1−δ) ≥ q. -/
theorem gamma_lower (γ δ p q : ℝ) (hpq : p ≤ q) (hδ0 : 0 ≤ δ)
    (hv : PairValidAt γ δ 1 p q) : q * (1 - δ) ≤ γ := by
  unfold PairValidAt at hv
  nlinarith

/-- Obstruction: if valid on a one-point configuration with p ≤ q and 1 ≤ q, then for every pair with 0 ≤ δ < 1 the hgap
`d ln L < a − a/L^d − γ·a/(1−δ)` of the stationary sufficient condition fails (L ≥ 1, a ≥ 0). For δ ≥ 1 see no_schedule_of_delta_ge_one. -/
theorem no_stationary (γ δ p q a L : ℝ) (d : ℕ) (hpq : p ≤ q) (hq : 1 ≤ q)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1) (ha : 0 ≤ a) (hL : 1 ≤ L) (hv : PairValidAt γ δ 1 p q) :
    ¬ (d * Real.log L < a - a / L ^ d - γ * (a / (1 - δ))) := by
  intro h
  have hγ := gamma_lower γ δ p q hpq hδ0 hv
  have h1 : 0 < 1 - δ := by linarith
  have hlog : 0 ≤ (d : ℝ) * Real.log L := mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hL)
  have hLd : 0 < L ^ d := pow_pos (by linarith) d
  have h2 : a ≤ γ * (a / (1 - δ)) := by
    have : q * (1 - δ) * (a / (1 - δ)) = q * a := by field_simp
    have h3 : q * (1 - δ) * (a / (1 - δ)) ≤ γ * (a / (1 - δ)) :=
      mul_le_mul_of_nonneg_right hγ (div_nonneg ha h1.le)
    nlinarith
  have h4 : 0 ≤ a / L ^ d := div_nonneg ha hLd.le
  linarith

/-- (p, q) for the one-point configuration in the four cases (factor 2 or 4, nearest or *-adjacency): (4, 4), (4, 8), (15, 15), (15, 80).
All have p ≤ q and 1 ≤ q, so no_stationary applies. -/
theorem four_cases_pq :
    ((innerNN 2 0).card ≤ (innerNN 2 (blk 2 0)).card ∧ 1 ≤ (innerNN 2 (blk 2 0)).card) ∧
    ((innerNN 4 (fun _ => 4)).card ≤ (innerNN 4 (blk 4 (fun _ => 4))).card ∧
      1 ≤ (innerNN 4 (blk 4 (fun _ => 4))).card) ∧
    ((innerStar 2 0).card ≤ (innerStar 2 (blk 2 0)).card ∧ 1 ≤ (innerStar 2 (blk 2 0)).card) ∧
    ((innerStar 4 (fun _ => 4)).card ≤ (innerStar 4 (blk 4 (fun _ => 4))).card ∧
      1 ≤ (innerStar 4 (blk 4 (fun _ => 4))).card) := by
  decide

/-! ## 4. Lower bound on the supply and a sequence attaining it -/

/-- Lower bound on the supply: if valid on a one-point configuration (γ + pδ ≥ q, p ≤ q, q > 0), δ ≥ 0, c ≥ 0,
boundary recursion `a + δc ≤ c + s`, volume recursion `a/L_d + γc ≤ a − b′`, and `X = a − a/L_d − b′ ≥ 0`, then `s ≥ a − X/q`. -/
theorem supply_lower (a c s γ δ Ld b' p q : ℝ) (hq : 0 < q) (hpq : p ≤ q)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hv : PairValidAt γ δ 1 p q)
    (hbd : a + δ * c ≤ c + s) (hvol : a / Ld + γ * c ≤ a - b') (hX : 0 ≤ a - a / Ld - b') :
    a - (a - a / Ld - b') / q ≤ s := by
  unfold PairValidAt at hv
  have hXq : 0 ≤ (a - a / Ld - b') / q := div_nonneg hX hq.le
  rcases le_or_gt δ 1 with h1 | h1
  · have hγ : q * (1 - δ) ≤ γ := by nlinarith
    have h2 : q * ((1 - δ) * c) ≤ a - a / Ld - b' := by nlinarith [mul_le_mul_of_nonneg_right hγ hc]
    have h3 : (1 - δ) * c ≤ (a - a / Ld - b') / q := by rw [le_div_iff₀ hq]; linarith
    nlinarith
  · nlinarith

/-- A sequence attaining the bound: (γ, δ) = (deg, 0), c = X/deg, s = a − c gives a stationary sequence with supply,
and contraction holds at all steps if b′ > d ln L (WeightRecursion.all_steps_supply). -/
theorem supply_achieved (a L deg b' : ℝ) (d : ℕ) (ha : 0 ≤ a) (hL : 1 ≤ L) (hdeg : 0 < deg)
    (hX : 0 ≤ a - a / L ^ d - b') (hgap : d * Real.log L < b') :
    WeightRecursion.WeightScheduleSupply (fun _ => a) (fun _ => (a - a / L ^ d - b') / deg)
      (fun _ => b') (fun _ => a - (a - a / L ^ d - b') / deg) (L ^ d) deg 0 ∧
    (∀ k : ℕ, L ^ d * Real.exp (-(fun _ => b') k) < 1) := by
  have hc : 0 ≤ (a - a / L ^ d - b') / deg := div_nonneg hX hdeg.le
  have H := WeightRecursion.stationary_schedule_supply a ((a - a / L ^ d - b') / deg)
    (a - (a - a / L ^ d - b') / deg) L deg 0 d ha hc (by linarith)
  have e : a - a / L ^ d - deg * ((a - a / L ^ d - b') / deg) = b' := by field_simp; ring
  have H' : WeightRecursion.WeightScheduleSupply (fun _ => a) (fun _ => (a - a / L ^ d - b') / deg)
      (fun _ => b') (fun _ => a - (a - a / L ^ d - b') / deg) (L ^ d) deg 0 := by
    simp only [e] at H; exact H
  exact ⟨H', (WeightRecursion.all_steps_supply _ _ _ _ L deg 0 d hL H' (fun _ => hgap)).2⟩

/-- Volume coefficient needed for contraction: `b′ ≤ a(1 − 1/L_d)` (γ, c ≥ 0). -/
theorem volume_needed (a c γ Ld b' : ℝ) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hvol : a / Ld + γ * c ≤ a - b') : b' ≤ a - a / Ld := by
  have := mul_nonneg hγ hc; linarith

/-! ## 5. Numbers (a = 12.13 is −ln P₁(6.84) (arithmetic); P₁ is (floating-point computation)) -/

/-- With the per-block reading a ≈ 0.473, b′ > 4 ln 2 is not reached even for scale factor 2. -/
theorem per_block_reading_fails : (0.473 : ℝ) - 0.473 / 2 ^ 4 < 4 * Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- Factor 2, nearest-neighbour (q = 4, L_d = 16, b′ ≥ 4 ln 2): s ≥ 9.98. -/
theorem supply_nn_L2 (c s γ δ b' : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hv : PairValidAt γ δ 1 4 4)
    (hbd : 12.13 + δ * c ≤ c + s) (hvol : 12.13 / 16 + γ * c ≤ 12.13 - b')
    (hb' : 4 * Real.log 2 ≤ b') (hX : 0 ≤ 12.13 - 12.13 / 16 - b') : 9.98 ≤ s := by
  have h := supply_lower 12.13 c s γ δ 16 b' 4 4 (by norm_num) le_rfl hδ hc hv hbd hvol hX
  have hl := Real.log_two_gt_d9
  linarith

/-- Factor 4, nearest-neighbour (q = 8, p = 4, L_d = 256, b′ ≥ 4 ln 4): s ≥ 11.31. -/
theorem supply_nn_L4 (c s γ δ b' : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hv : PairValidAt γ δ 1 4 8)
    (hbd : 12.13 + δ * c ≤ c + s) (hvol : 12.13 / 256 + γ * c ≤ 12.13 - b')
    (hb' : 4 * Real.log 4 ≤ b') (hX : 0 ≤ 12.13 - 12.13 / 256 - b') : 11.31 ≤ s := by
  have h := supply_lower 12.13 c s γ δ 256 b' 4 8 (by norm_num) (by norm_num) hδ hc hv
    hbd hvol hX
  have hl := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

/-- Factor 2, *-adjacency (q = p = 15): s ≥ 11.55. -/
theorem supply_star_L2 (c s γ δ b' : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hv : PairValidAt γ δ 1 15 15)
    (hbd : 12.13 + δ * c ≤ c + s) (hvol : 12.13 / 16 + γ * c ≤ 12.13 - b')
    (hb' : 4 * Real.log 2 ≤ b') (hX : 0 ≤ 12.13 - 12.13 / 16 - b') : 11.55 ≤ s := by
  have h := supply_lower 12.13 c s γ δ 16 b' 15 15 (by norm_num) le_rfl hδ hc hv
    hbd hvol hX
  have hl := Real.log_two_gt_d9
  linarith

/-- Factor 4, *-adjacency (q = 80, p = 15): s ≥ 12.04. -/
theorem supply_star_L4 (c s γ δ b' : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hv : PairValidAt γ δ 1 15 80)
    (hbd : 12.13 + δ * c ≤ c + s) (hvol : 12.13 / 256 + γ * c ≤ 12.13 - b')
    (hb' : 4 * Real.log 4 ≤ b') (hX : 0 ≤ 12.13 - 12.13 / 256 - b') : 12.04 ≤ s := by
  have h := supply_lower 12.13 c s γ δ 256 b' 15 80 (by norm_num) (by norm_num) hδ hc
    hv hbd hvol hX
  have hl := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith

#print axioms coarse_boundary_le_deg
#print axioms pair_inner
#print axioms pair_volume
#print axioms pair_mix
#print axioms nn_total
#print axioms star_total
#print axioms nn_L2
#print axioms nn_L4
#print axioms star_L2
#print axioms star_L4
#print axioms gamma_lower
#print axioms no_stationary
#print axioms four_cases_pq
#print axioms supply_lower
#print axioms supply_achieved
#print axioms volume_needed
#print axioms per_block_reading_fails
#print axioms supply_nn_L2
#print axioms supply_nn_L4
#print axioms supply_star_L2
#print axioms supply_star_L4

end BlockBoundaryCount
