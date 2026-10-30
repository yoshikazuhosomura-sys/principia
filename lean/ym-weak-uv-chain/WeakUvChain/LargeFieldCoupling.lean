/-
Contribution of the large-field gas to the coupling (large_rem of the chain: |r^ℓ| ≤ D z). The large-field part of the
coupling is extracted as the difference of gas free energies between background flux θ and 0,
r^ℓ = (log Z_θ − log Z_0)/(c·#A), and |r^ℓ| ≤ (2/c) ζ follows from the per-site activity sum ζ ≤ 1.
Copy of PolymerGasFreeEnergy (unchanged up to comments), with additions at the end.
Single file; checks with `import Mathlib` only.
-/
import Mathlib

namespace PolymerGasDobrushin

open Finset

set_option linter.unusedSectionVars false

variable {P : Type*} [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc] (z : P → ℝ)

/-- Compatibility: no two distinct elements are related by the incompatibility relation `inc`. -/
def Compat (t : Finset P) : Prop := ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ inc x y

open Classical in
/-- Partition function. -/
noncomputable def Z (Γ : Finset P) : ℝ :=
  ∑ t ∈ Γ.powerset, if Compat inc t then ∏ s ∈ t, z s else 0

theorem Z_empty : Z inc z ∅ = 1 := by
  classical
  simp [Z, Compat]

/-- Rewrite a sum over the powerset as a sum over the powerset of the part satisfying the condition. -/
theorem sum_powerset_ite_forall {β : Type*} [AddCommMonoid β] (s : Finset P) (q : P → Prop)
    [DecidablePred q] (g : Finset P → β) [∀ t : Finset P, Decidable (∀ x ∈ t, q x)] :
    ∑ t ∈ s.powerset, (if (∀ x ∈ t, q x) then g t else 0) = ∑ t ∈ (s.filter q).powerset, g t := by
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact mem_filter.mpr ⟨h1 hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (mem_filter.mp (h hx)).1, fun x hx => (mem_filter.mp (h hx)).2⟩

/-- Inserting into a compatible family: if `γ ∉ t`, then `insert γ t` is compatible iff `t` is compatible and
every element of `t` is compatible with `γ`. -/
theorem compat_insert (hsymm : ∀ x y, inc x y → inc y x) {γ : P} {t : Finset P} (hγ : γ ∉ t) :
    Compat inc (insert γ t) ↔ Compat inc t ∧ ∀ s ∈ t, ¬ inc γ s := by
  constructor
  · intro h
    refine ⟨fun x hx y hy hxy => h x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy,
      fun s hs => h γ (mem_insert_self γ t) s (mem_insert_of_mem hs) ?_⟩
    rintro rfl; exact hγ hs
  · rintro ⟨h1, h2⟩ x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx'
    · rcases mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · exact h2 y hy'
    · rcases mem_insert.mp hy with rfl | hy'
      · exact fun hinc => h2 x hx' (hsymm _ _ hinc)
      · exact h1 x hx' y hy' hxy

/-- The recursion of §1. -/
theorem Z_insert (hsymm : ∀ x y, inc x y → inc y x) {γ : P} {Γ' : Finset P} (hγ : γ ∉ Γ') :
    Z inc z (insert γ Γ') = Z inc z Γ' + z γ * Z inc z (Γ'.filter fun s => ¬ inc γ s) := by
  classical
  unfold Z
  rw [sum_powerset_insert hγ]
  congr 1
  rw [Finset.mul_sum]
  have key : ∀ t ∈ Γ'.powerset,
      (if Compat inc (insert γ t) then ∏ s ∈ insert γ t, z s else 0) =
        z γ * (if (∀ x ∈ t, ¬ inc γ x) then (if Compat inc t then ∏ s ∈ t, z s else 0) else 0) := by
    intro t ht
    have hγt : γ ∉ t := fun h => hγ (mem_powerset.mp ht h)
    rw [prod_insert hγt]
    by_cases hc : Compat inc t <;> by_cases hq : ∀ x ∈ t, ¬ inc γ x <;>
      simp [compat_insert inc hsymm hγt, hc, hq]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_powerset_ite_forall, Finset.mul_sum]

/-! ## 2. Induction -/

/-- Removal bound (the form used inside the induction): if the ratio lower bound `e^{−a(t)} Z(Δ∖t) ≤ Z(Δ)` and
positivity hold for subsets of `U` of size at most that of `Δ′`, then `Z(Δ′ ∖ T) ≤ exp(Σ_T a) Z(Δ′)` for `T ⊆ Δ′`. -/
theorem remove_le (U : Finset P) (a : P → ℝ) (Δ' : Finset P) (hΔ' : Δ' ⊆ U)
    (hratio : ∀ Δ ⊆ U, Δ.card ≤ Δ'.card → ∀ t ∈ Δ, Real.exp (-a t) * Z inc z (Δ.erase t) ≤ Z inc z Δ) :
    ∀ T : Finset P, T ⊆ Δ' → Z inc z (Δ' \ T) ≤ Real.exp (∑ t ∈ T, a t) * Z inc z Δ' := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert t T₀ ht ih =>
    intro hT
    have hT₀ : T₀ ⊆ Δ' := fun x hx => hT (mem_insert_of_mem hx)
    have htΔ : t ∈ Δ' \ T₀ := mem_sdiff.mpr ⟨hT (mem_insert_self t T₀), ht⟩
    have hsub : Δ' \ T₀ ⊆ U := fun x hx => hΔ' (mem_sdiff.mp hx).1
    have hcard : (Δ' \ T₀).card ≤ Δ'.card := card_le_card sdiff_subset
    have hr := hratio (Δ' \ T₀) hsub hcard t htΔ
    have e : Δ' \ insert t T₀ = (Δ' \ T₀).erase t := by
      ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    rw [e, sum_insert ht, Real.exp_add]
    have hea : 0 < Real.exp (a t) := Real.exp_pos _
    have h1 : Z inc z ((Δ' \ T₀).erase t) ≤ Real.exp (a t) * Z inc z (Δ' \ T₀) := by
      have : Real.exp (a t) * (Real.exp (-a t) * Z inc z ((Δ' \ T₀).erase t)) ≤
          Real.exp (a t) * Z inc z (Δ' \ T₀) := mul_le_mul_of_nonneg_left hr hea.le
      rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
    calc Z inc z ((Δ' \ T₀).erase t) ≤ Real.exp (a t) * Z inc z (Δ' \ T₀) := h1
      _ ≤ Real.exp (a t) * (Real.exp (∑ x ∈ T₀, a x) * Z inc z Δ') :=
          mul_le_mul_of_nonneg_left (ih hT₀) hea.le
      _ = Real.exp (a t) * Real.exp (∑ x ∈ T₀, a x) * Z inc z Δ' := by ring

/-- Main theorem of §2 (Dobrushin condition). -/
theorem dobrushin (hsymm : ∀ x y, inc x y → inc y x) (U : Finset P) (a : P → ℝ)
    (ha : ∀ γ, 0 ≤ a γ)
    (hcond : ∀ γ ∈ U, |z γ| ≤ (1 - Real.exp (-a γ)) *
      Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ')) :
    ∀ Γ ⊆ U, 0 < Z inc z Γ ∧ ∀ γ ∈ Γ, Real.exp (-a γ) * Z inc z (Γ.erase γ) ≤ Z inc z Γ := by
  intro Γ
  induction h : Γ.card using Nat.strong_induction_on generalizing Γ with
  | _ n ih =>
    intro hΓ
    -- Ratio lower bound and positivity on smaller sets
    have ihr : ∀ Δ ⊆ U, Δ.card < n →
        0 < Z inc z Δ ∧ ∀ t ∈ Δ, Real.exp (-a t) * Z inc z (Δ.erase t) ≤ Z inc z Δ :=
      fun Δ hΔ hc => ih Δ.card hc Δ rfl hΔ
    have hratio_step : ∀ γ ∈ Γ, Real.exp (-a γ) * Z inc z (Γ.erase γ) ≤ Z inc z Γ := by
      intro γ hγ
      set Δ' := Γ.erase γ with hΔ'
      have hγΔ : γ ∉ Δ' := notMem_erase γ Γ
      have hcardΔ : Δ'.card < n := by rw [← h]; exact card_erase_lt_of_mem hγ
      have hΔU : Δ' ⊆ U := fun x hx => hΓ (mem_of_mem_erase hx)
      have hins : insert γ Δ' = Γ := insert_erase hγ
      have hrec := Z_insert inc z hsymm hγΔ
      rw [hins] at hrec
      set T := Δ'.filter (fun s => inc γ s) with hT
      have hfilt : Δ'.filter (fun s => ¬ inc γ s) = Δ' \ T := by
        rw [hT, filter_not]
      rw [hfilt] at hrec
      have hTsub : T ⊆ Δ' := filter_subset _ _
      have hpos' : 0 < Z inc z Δ' := (ihr Δ' hΔU hcardΔ).1
      have hposT : 0 < Z inc z (Δ' \ T) :=
        (ihr (Δ' \ T) (fun x hx => hΔU (mem_sdiff.mp hx).1)
          (lt_of_le_of_lt (card_le_card sdiff_subset) hcardΔ)).1
      have hrem := remove_le inc z U a Δ' hΔU
        (fun Δ hΔ hc t ht => (ihr Δ hΔ (lt_of_le_of_lt hc hcardΔ)).2 t ht) T hTsub
      -- Comparison of sums: T ⊆ (U.erase γ).filter (inc γ)
      have hTU : T ⊆ (U.erase γ).filter (fun s => inc γ s) := by
        intro x hx
        rw [hT, mem_filter] at hx
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_, hΔU hx.1⟩, hx.2⟩
        rintro rfl; exact hγΔ hx.1
      have hsum : ∑ t ∈ T, a t ≤ ∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ' :=
        sum_le_sum_of_subset_of_nonneg hTU (fun x _ _ => ha x)
      have hz := hcond γ (hΓ hγ)
      have hexp : |z γ| * Real.exp (∑ t ∈ T, a t) ≤ 1 - Real.exp (-a γ) := by
        have h1 : Real.exp (∑ t ∈ T, a t) ≤
            Real.exp (∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ') := Real.exp_le_exp.mpr hsum
        have h2 : 0 ≤ 1 - Real.exp (-a γ) := by
          have : Real.exp (-a γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ha γ])
          linarith
        calc |z γ| * Real.exp (∑ t ∈ T, a t)
            ≤ ((1 - Real.exp (-a γ)) *
                Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ')) *
                Real.exp (∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ') :=
              mul_le_mul hz h1 (Real.exp_pos _).le (by positivity)
          _ = 1 - Real.exp (-a γ) := by
              rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      have hlow : -(|z γ| * Real.exp (∑ t ∈ T, a t) * Z inc z Δ') ≤ z γ * Z inc z (Δ' \ T) := by
        have h1 : -(|z γ| * Z inc z (Δ' \ T)) ≤ z γ * Z inc z (Δ' \ T) := by
          have := neg_abs_le (z γ)
          nlinarith
        have h2 : |z γ| * Z inc z (Δ' \ T) ≤ |z γ| * (Real.exp (∑ t ∈ T, a t) * Z inc z Δ') :=
          mul_le_mul_of_nonneg_left hrem (abs_nonneg _)
        nlinarith
      rw [hrec]
      nlinarith
    refine ⟨?_, hratio_step⟩
    rcases Γ.eq_empty_or_nonempty with he | ⟨γ, hγ⟩
    · subst he; rw [Z_empty]; exact one_pos
    · have hcardΔ : (Γ.erase γ).card < n := by rw [← h]; exact card_erase_lt_of_mem hγ
      have hpos' := (ihr (Γ.erase γ) (fun x hx => hΓ (mem_of_mem_erase hx)) hcardΔ).1
      have := hratio_step γ hγ
      have : 0 < Real.exp (-a γ) * Z inc z (Γ.erase γ) := mul_pos (Real.exp_pos _) hpos'
      linarith

/-! ## 3. Corollary: lower bound on the free energy -/

/-- Under the Dobrushin condition, `Z(Γ) ≥ exp(−Σ_{γ ∈ Γ} a(γ))`. -/
theorem Z_ge_exp (hsymm : ∀ x y, inc x y → inc y x) (U : Finset P) (a : P → ℝ)
    (ha : ∀ γ, 0 ≤ a γ)
    (hcond : ∀ γ ∈ U, |z γ| ≤ (1 - Real.exp (-a γ)) *
      Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ')) :
    ∀ Γ ⊆ U, Real.exp (-∑ γ ∈ Γ, a γ) ≤ Z inc z Γ := by
  intro Γ
  induction Γ using Finset.induction_on with
  | empty => intro _; simp [Z_empty]
  | insert γ Γ₀ hγ ih =>
    intro hsub
    have hΓ₀ : Γ₀ ⊆ U := fun x hx => hsub (mem_insert_of_mem hx)
    have hd := (dobrushin inc z hsymm U a ha hcond (insert γ Γ₀) hsub).2 γ (mem_insert_self γ Γ₀)
    rw [erase_insert hγ] at hd
    rw [sum_insert hγ, neg_add, Real.exp_add]
    calc Real.exp (-a γ) * Real.exp (-∑ x ∈ Γ₀, a x) ≤ Real.exp (-a γ) * Z inc z Γ₀ :=
          mul_le_mul_of_nonneg_left (ih hΓ₀) (Real.exp_pos _).le
      _ ≤ Z inc z (insert γ Γ₀) := hd

/-- Corollary: `log Z(Γ) ≥ −Σ_{γ ∈ Γ} a(γ)`. -/
theorem log_Z_ge (hsymm : ∀ x y, inc x y → inc y x) (U : Finset P) (a : P → ℝ)
    (ha : ∀ γ, 0 ≤ a γ)
    (hcond : ∀ γ ∈ U, |z γ| ≤ (1 - Real.exp (-a γ)) *
      Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => inc γ s), a γ')) :
    ∀ Γ ⊆ U, -∑ γ ∈ Γ, a γ ≤ Real.log (Z inc z Γ) := by
  intro Γ hΓ
  have h := Z_ge_exp inc z hsymm U a ha hcond Γ hΓ
  rw [← Real.log_exp (-∑ γ ∈ Γ, a γ)]
  exact Real.log_le_log (Real.exp_pos _) h


end PolymerGasDobrushin


namespace KPToDobrushin

open Finset

set_option linter.unusedSectionVars false

variable {P S : Type*} [DecidableEq P] [DecidableEq S]

/-- §1: for nonnegative `f`, the sum over polymers meeting support `A` ≤ the sum over sites of `A` of the sum over
polymers containing that site. -/
theorem intersect_sum_le (supp : P → Finset S) (V : Finset P) (A : Finset S) (f : P → ℝ)
    (hf : ∀ γ, 0 ≤ f γ) :
    ∑ γ' ∈ V.filter (fun s => (A ∩ supp s).Nonempty), f γ' ≤
      ∑ x ∈ A, ∑ γ' ∈ V.filter (fun s => x ∈ supp s), f γ' := by
  rw [sum_filter]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro γ' _
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    rw [mem_inter] at hx
    have hle : (if x ∈ supp γ' then f γ' else 0) ≤ ∑ y ∈ A, if y ∈ supp γ' then f γ' else 0 :=
      single_le_sum (f := fun y => if y ∈ supp γ' then f γ' else 0)
        (fun y _ => by split_ifs <;> simp [hf]) hx.1
    simpa [hx.2] using hle
  · exact sum_nonneg fun y _ => by split_ifs <;> simp [hf]

/-- §2: the Dobrushin condition from (KP). -/
theorem dobrushin_cond_of_kp (supp : P → Finset S) (z : P → ℝ) (U : Finset P)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1)
    (hsmall : ∀ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) :
    ∀ γ ∈ U, |z γ| ≤
      (1 - Real.exp (-Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)))) *
        Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
          Real.log (1 + |z γ'| * Real.exp (2 * (supp γ').card))) := by
  intro γ hγ
  set μ : P → ℝ := fun s => |z s| * Real.exp (2 * (supp s).card) with hμ
  have hμ0 : ∀ s, 0 ≤ μ s := fun s => by rw [hμ]; positivity
  set n : ℝ := ((supp γ).card : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hsize γ hγ
  -- Upper bound of the sum: Σ a ≤ Σ μ ≤ n
  have hlog : ∀ s, Real.log (1 + μ s) ≤ μ s := by
    intro s
    have := Real.log_le_sub_one_of_pos (by linarith [hμ0 s] : (0:ℝ) < 1 + μ s)
    linarith
  have hsum1 : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
      Real.log (1 + μ γ') ≤
      ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty), μ γ' :=
    sum_le_sum fun s _ => hlog s
  have hsum2 : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty), μ γ' ≤
      ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' :=
    intersect_sum_le supp (U.erase γ) (supp γ) μ hμ0
  have hsum3 : ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' ≤ n := by
    have : ∀ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' ≤ 1 := by
      intro x _
      refine le_trans ?_ (hsite x)
      exact sum_le_sum_of_subset_of_nonneg
        (filter_subset_filter _ (erase_subset γ U)) (fun s _ _ => hμ0 s)
    calc ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ'
        ≤ ∑ _x ∈ supp γ, (1 : ℝ) := sum_le_sum this
      _ = n := by simp [hn]
  have hSum : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
      Real.log (1 + μ γ') ≤ n := by linarith
  -- 1 − e^{−a} = μ/(1+μ)
  have hpos : 0 < 1 + μ γ := by linarith [hμ0 γ]
  have he1 : Real.exp (-Real.log (1 + μ γ)) = 1 / (1 + μ γ) := by
    rw [Real.exp_neg, Real.exp_log hpos, one_div]
  have hfac : 1 - Real.exp (-Real.log (1 + μ γ)) = μ γ / (1 + μ γ) := by
    rw [he1]; field_simp; ring
  -- exp(−Σ) ≥ e^{−n}
  have hexp : Real.exp (-n) ≤ Real.exp (-∑ γ' ∈ (U.erase γ).filter
      (fun s => (supp γ ∩ supp s).Nonempty), Real.log (1 + μ γ')) :=
    Real.exp_le_exp.mpr (by linarith)
  -- 1 + μ ≤ e ≤ e^n
  have hen : 1 + μ γ ≤ Real.exp n := by
    have h1 : 1 + μ γ ≤ Real.exp 1 := by linarith [hsmall γ hγ]
    exact le_trans h1 (Real.exp_le_exp.mpr hn1)
  show |z γ| ≤ (1 - Real.exp (-Real.log (1 + μ γ))) *
      Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
        Real.log (1 + μ γ'))
  rw [hfac]
  have hz0 : 0 ≤ |z γ| := abs_nonneg _
  have hμdef : μ γ = |z γ| * Real.exp (2 * n) := by rw [hμ, hn]
  have key : |z γ| ≤ μ γ / (1 + μ γ) * Real.exp (-n) := by
    rw [hμdef, div_mul_eq_mul_div, le_div_iff₀ (by rw [← hμdef]; exact hpos)]
    have h2 : Real.exp (2 * n) * Real.exp (-n) = Real.exp n := by
      rw [← Real.exp_add]; ring_nf
    have : |z γ| * (1 + |z γ| * Real.exp (2 * n)) ≤ |z γ| * Real.exp n := by
      rw [← hμdef]; exact mul_le_mul_of_nonneg_left hen hz0
    calc |z γ| * (1 + |z γ| * Real.exp (2 * n)) ≤ |z γ| * Real.exp n := this
      _ = |z γ| * Real.exp (2 * n) * Real.exp (-n) := by rw [mul_assoc, h2]
  calc |z γ| ≤ μ γ / (1 + μ γ) * Real.exp (-n) := key
    _ ≤ μ γ / (1 + μ γ) * Real.exp (-∑ γ' ∈ (U.erase γ).filter
        (fun s => (supp γ ∩ supp s).Nonempty), Real.log (1 + μ γ')) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg (hμ0 γ) hpos.le)


end KPToDobrushin

namespace PolymerGasKP

open Finset

/-- Junction: for the gas with incompatibility = intersecting supports, if (KP) Σ_{γ′∋x} |z| e^{2|γ′|} ≤ 1 at every
site, |z(γ)| e^{2|γ|} ≤ e − 1, and supports have size ≥ 1, then for all Γ ⊆ U, Z(Γ) > 0 and
log Z(Γ) ≥ −Σ_{γ∈Γ} log(1 + |z(γ)| e^{2|γ|}). -/
theorem kp_gas_bounds {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S)
    (z : P → ℝ) (U : Finset P)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1)
    (hsmall : ∀ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) :
    ∀ Γ ⊆ U, 0 < PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ ∧
      -∑ γ ∈ Γ, Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) ≤
        Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ) := by
  intro Γ hΓ
  have hsymm : ∀ x y : P, (supp x ∩ supp y).Nonempty → (supp y ∩ supp x).Nonempty := by
    intro x y h; rwa [inter_comm]
  have ha : ∀ γ, 0 ≤ Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) := by
    intro γ; apply Real.log_nonneg; have : 0 ≤ |z γ| * Real.exp (2 * (supp γ).card) := by positivity
    linarith
  have hcond := KPToDobrushin.dobrushin_cond_of_kp supp z U hsize hsite hsmall
  refine ⟨(PolymerGasDobrushin.dobrushin (fun γ s => (supp γ ∩ supp s).Nonempty) z hsymm U
      (fun γ => Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card))) ha hcond Γ hΓ).1, ?_⟩
  exact PolymerGasDobrushin.log_Z_ge (fun γ s => (supp γ ∩ supp s).Nonempty) z hsymm U
    (fun γ => Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card))) ha hcond Γ hΓ

end PolymerGasKP


namespace PolymerGasFreeEnergy

open Finset

/-- Upper bound for the gas: `Z(Γ) ≤ Π_{γ∈Γ} (1 + |z(γ)|)`. -/
theorem Z_le_prod {P : Type*} [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
    (z : P → ℝ) (Γ : Finset P) :
    PolymerGasDobrushin.Z inc z Γ ≤ ∏ γ ∈ Γ, (1 + |z γ|) := by
  classical
  rw [prod_one_add]
  unfold PolymerGasDobrushin.Z
  apply sum_le_sum
  intro t _
  split_ifs
  · calc ∏ s ∈ t, z s ≤ |∏ s ∈ t, z s| := le_abs_self _
      _ = ∏ s ∈ t, |z s| := abs_prod t z
  · exact prod_nonneg fun s _ => abs_nonneg _

/-- Two-sided free-energy bound under KP: `|log Z(Γ)| ≤ Σ_{γ∈Γ} log(1 + μ(γ))`. -/
theorem abs_log_Z_le {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S)
    (z : P → ℝ) (U : Finset P)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1)
    (hsmall : ∀ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) :
    ∀ Γ ⊆ U, |Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ)| ≤
      ∑ γ ∈ Γ, Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) := by
  intro Γ hΓ
  obtain ⟨hpos, hlow⟩ := PolymerGasKP.kp_gas_bounds supp z U hsize hsite hsmall Γ hΓ
  have hup : Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ) ≤
      ∑ γ ∈ Γ, Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) := by
    have h1 := Z_le_prod (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ
    have h2 : ∏ γ ∈ Γ, (1 + |z γ|) ≤ ∏ γ ∈ Γ, (1 + |z γ| * Real.exp (2 * (supp γ).card)) := by
      apply prod_le_prod (fun γ _ => by positivity)
      intro γ _
      have : |z γ| ≤ |z γ| * Real.exp (2 * (supp γ).card) := by
        have he : 1 ≤ Real.exp (2 * (supp γ).card) := Real.one_le_exp (by positivity)
        nlinarith [abs_nonneg (z γ)]
      linarith
    have h3 := le_trans h1 h2
    calc Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z Γ)
        ≤ Real.log (∏ γ ∈ Γ, (1 + |z γ| * Real.exp (2 * (supp γ).card))) :=
          Real.log_le_log hpos h3
      _ = ∑ γ ∈ Γ, Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) := by
          rw [Real.log_prod]
          intro γ _
          have : 0 ≤ |z γ| * Real.exp (2 * (supp γ).card) := by positivity
          linarith
  rw [abs_le]; exact ⟨hlow, hup⟩

/-- Free-energy density: if all polymer supports lie in `A`, then `Σ_{γ∈Γ} μ(γ) ≤ #A` (from the per-site sum ≤ 1).
Together with `log(1+μ) ≤ μ`, `|log Z(Γ)| ≤ #A`. -/
theorem sum_mu_le_card {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S)
    (z : P → ℝ) (U : Finset P) (A : Finset S)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card) (hA : ∀ γ ∈ U, supp γ ⊆ A)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1) :
    ∀ Γ ⊆ U, ∑ γ ∈ Γ, |z γ| * Real.exp (2 * (supp γ).card) ≤ A.card := by
  intro Γ hΓ
  set μ : P → ℝ := fun s => |z s| * Real.exp (2 * (supp s).card) with hμ
  have hμ0 : ∀ s, 0 ≤ μ s := fun s => by rw [hμ]; positivity
  -- Each γ has at least one support site, so recounting by sites counts each γ at least once
  have hcount : ∑ γ ∈ Γ, μ γ ≤ ∑ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro γ hγ
    obtain ⟨x, hx⟩ := card_pos.mp (lt_of_lt_of_le zero_lt_one (hsize γ (hΓ hγ)))
    have hle : (if x ∈ supp γ then μ γ else 0) ≤ ∑ y ∈ A, if y ∈ supp γ then μ γ else 0 :=
      single_le_sum (f := fun y => if y ∈ supp γ then μ γ else 0)
        (fun y _ => by split_ifs <;> simp [hμ0]) (hA γ (hΓ hγ) hx)
    simpa [hx] using hle
  have hsite' : ∀ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ ≤ 1 := by
    intro x _
    refine le_trans ?_ (hsite x)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hΓ) (fun s _ _ => hμ0 s)
  calc ∑ γ ∈ Γ, μ γ ≤ ∑ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ := hcount
    _ ≤ ∑ _x ∈ A, (1 : ℝ) := sum_le_sum hsite'
    _ = A.card := by simp

end PolymerGasFreeEnergy


namespace LargeFieldCoupling

open Finset

/-- If the per-site sum is at most `ζ`, the sum of μ over polymers with support in `A` is ≤ `#A · ζ`. -/
theorem sum_mu_le_card_mul {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S)
    (μ : P → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (U : Finset P) (A : Finset S) (ζ : ℝ)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card) (hA : ∀ γ ∈ U, supp γ ⊆ A)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s), μ γ' ≤ ζ) :
    ∀ Γ ⊆ U, ∑ γ ∈ Γ, μ γ ≤ A.card * ζ := by
  intro Γ hΓ
  have hcount : ∑ γ ∈ Γ, μ γ ≤ ∑ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro γ hγ
    obtain ⟨x, hx⟩ := card_pos.mp (lt_of_lt_of_le zero_lt_one (hsize γ (hΓ hγ)))
    have hle : (if x ∈ supp γ then μ γ else 0) ≤ ∑ y ∈ A, if y ∈ supp γ then μ γ else 0 :=
      single_le_sum (f := fun y => if y ∈ supp γ then μ γ else 0)
        (fun y _ => by split_ifs <;> simp [hμ0]) (hA γ (hΓ hγ) hx)
    simpa [hx] using hle
  have hsite' : ∀ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ ≤ ζ := by
    intro x _
    refine le_trans ?_ (hsite x)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hΓ) (fun s _ _ => hμ0 s)
  calc ∑ γ ∈ Γ, μ γ ≤ ∑ x ∈ A, ∑ γ ∈ Γ.filter (fun s => x ∈ supp s), μ γ := hcount
    _ ≤ ∑ _x ∈ A, ζ := sum_le_sum hsite'
    _ = A.card * ζ := by simp [mul_comm]

/-- Arithmetic of the difference: if `|F_θ|, |F_0| ≤ V ζ` (`V, c > 0`) then `|(F_θ − F_0)/(c V)| ≤ (2/c) ζ`. -/
theorem difference_le (Fθ F0 V c ζ : ℝ) (hV : 0 < V) (hc : 0 < c)
    (hθ : |Fθ| ≤ V * ζ) (h0 : |F0| ≤ V * ζ) : |(Fθ - F0) / (c * V)| ≤ 2 / c * ζ := by
  have hcV : 0 < c * V := mul_pos hc hV
  rw [abs_div, abs_of_pos hcV, div_le_iff₀ hcV]
  have := abs_sub Fθ F0
  have e : 2 / c * ζ * (c * V) = 2 * (V * ζ) := by field_simp
  rw [e]; linarith

/-- The large_rem form of the chain: if the gases at background θ and 0 (activities `zθ`, `z0`) both satisfy the KP
conditions (per-site sum ≤ ζ ≤ 1, μ ≤ e−1, support size ≥ 1, supports in A), then the coupling contribution extracted
by the difference satisfies `|r^ℓ| ≤ (2/c) ζ`. -/
theorem large_rem_from_gas {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S)
    (zθ z0 : P → ℝ) (U : Finset P) (A : Finset S) (ζ c : ℝ) (hζ1 : ζ ≤ 1) (hc : 0 < c)
    (hAne : 0 < A.card)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card) (hA : ∀ γ ∈ U, supp γ ⊆ A)
    (hsiteθ : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |zθ γ'| * Real.exp (2 * (supp γ').card) ≤ ζ)
    (hsite0 : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z0 γ'| * Real.exp (2 * (supp γ').card) ≤ ζ)
    (hsmallθ : ∀ γ ∈ U, |zθ γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1)
    (hsmall0 : ∀ γ ∈ U, |z0 γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) :
    |(Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) zθ U) -
        Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z0 U)) /
        (c * A.card)| ≤ 2 / c * ζ := by
  have bound : ∀ z : P → ℝ,
      (∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s), |z γ'| * Real.exp (2 * (supp γ').card) ≤ ζ) →
      (∀ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) →
      |Real.log (PolymerGasDobrushin.Z (fun γ s => (supp γ ∩ supp s).Nonempty) z U)| ≤
        A.card * ζ := by
    intro z hs hm
    have hs1 : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
        |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1 := fun x => le_trans (hs x) hζ1
    have h1 := PolymerGasFreeEnergy.abs_log_Z_le supp z U hsize hs1 hm U (subset_refl U)
    have h2 : ∑ γ ∈ U, Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)) ≤
        ∑ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) := by
      apply sum_le_sum; intro γ _
      have hp : 0 < 1 + |z γ| * Real.exp (2 * (supp γ).card) := by positivity
      have := Real.log_le_sub_one_of_pos hp
      linarith
    have h3 := sum_mu_le_card_mul supp (fun s => |z s| * Real.exp (2 * (supp s).card))
      (fun s => by positivity) U A ζ hsize hA hs U (subset_refl U)
    linarith
  exact difference_le _ _ _ c ζ (by exact_mod_cast hAne) hc
    (by have := bound zθ hsiteθ hsmallθ; linarith [this])
    (by have := bound z0 hsite0 hsmall0; linarith [this])

end LargeFieldCoupling

#print axioms PolymerGasDobrushin.Z_empty
#print axioms PolymerGasDobrushin.sum_powerset_ite_forall
#print axioms PolymerGasDobrushin.compat_insert
#print axioms PolymerGasDobrushin.Z_insert
#print axioms PolymerGasDobrushin.remove_le
#print axioms PolymerGasDobrushin.dobrushin
#print axioms PolymerGasDobrushin.Z_ge_exp
#print axioms PolymerGasDobrushin.log_Z_ge
#print axioms KPToDobrushin.intersect_sum_le
#print axioms KPToDobrushin.dobrushin_cond_of_kp
#print axioms PolymerGasKP.kp_gas_bounds
#print axioms PolymerGasFreeEnergy.Z_le_prod
#print axioms PolymerGasFreeEnergy.abs_log_Z_le
#print axioms PolymerGasFreeEnergy.sum_mu_le_card
#print axioms LargeFieldCoupling.sum_mu_le_card_mul
#print axioms LargeFieldCoupling.difference_le
#print axioms LargeFieldCoupling.large_rem_from_gas
