/-
Step deriving the Dobrushin condition from a per-site Kotecký–Preiss sum.
Single file; checks with `import Mathlib` only.

  A polymer γ has a support supp γ (a finite set of lattice sites, size |γ| = #supp γ ≥ 1); two polymers are
  incompatible iff their supports intersect. Set μ(γ) = |z(γ)| e^{2|γ|}, a(γ) = log(1 + μ(γ)).
  (KP) If Σ_{γ′ ∋ x} μ(γ′) ≤ 1 at every site x and μ(γ) ≤ e − 1, then the Dobrushin condition
  |z(γ)| ≤ (1 − e^{−a(γ)}) exp(−Σ_{γ′ ≠ γ, supports intersect} a(γ′)) holds
  (the same formula as `hcond` of `dobrushin` in PolymerGasDobrushin).

  §1 Bound the sum over polymers meeting a support by the sum over its sites
  §2 The Dobrushin condition
  §3 #print axioms
-/
import Mathlib

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

#print axioms intersect_sum_le
#print axioms dobrushin_cond_of_kp

end KPToDobrushin
