/-
Partition function of a finite polymer gas and an induction of Dobrushin–Kotecký–Preiss type.
Single file; checks with `import Mathlib` only.

  §1 Partition function Z(Γ) = Σ_{S ⊆ Γ, compatible} Π_{γ ∈ S} z(γ) (real activities, arbitrary sign) and the
     one-removal recursion Z(insert γ Γ′) = Z(Γ′) + z(γ) Z(elements of Γ′ compatible with γ) (compatibility symmetric)
  §2 Induction: if |z(γ)| ≤ (1 − e^{−a(γ)}) exp(−Σ_{γ′ ∈ U∖γ, γ′ ≁ γ} a(γ′)) for all γ ∈ U (a ≥ 0), then
     Z(Γ) > 0 and Z(Γ) ≥ e^{−a(γ)} Z(Γ∖γ) for all Γ ⊆ U
  §3 Corollaries: Z(Γ) ≥ exp(−Σ_{γ ∈ Γ} a(γ)) (free-energy lower bound log Z ≥ −Σ a) and the removal upper bound
  §4 #print axioms

That the large-field polymer gas (expansion of Bałaban's R operation) is a gas of this form, and the activity
estimates, are premises.
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

#print axioms Z_empty
#print axioms sum_powerset_ite_forall
#print axioms compat_insert
#print axioms Z_insert
#print axioms remove_le
#print axioms dobrushin
#print axioms Z_ge_exp
#print axioms log_Z_ge

end PolymerGasDobrushin
