/-
One coarse-graining step for polymer activities (the ρ z_k term of the activity recursion from step to step).
Single file; checks with `import Mathlib` only.

  A fine polymer γ (support supp γ ⊆ fine sites Sfin) is mapped to a coarse polymer π γ (support suppQ (π γ)),
  with coarse activity zc(q) = Σ_{π γ = q} z(γ). For a block map β (fine sites → coarse sites, each block ≤ L_d sites),
  if coarse support sites are images of fine support sites (covering) and the size condition a′ |π γ| ≤ a |γ| − b holds,
  then the coarse per-site KP sum ≤ L_d e^{−b} × the bound ε on the fine per-site sum.

  §1 Recounting by sites (general form)
  §2 One coarse-graining step
  §3 #print axioms
The size condition (large-set regulator type), covering and block size enter as premises on the coarse-graining geometry.
-/
import Mathlib

namespace PolymerBlocking

open Finset

set_option linter.unusedSectionVars false

variable {P Q S S' : Type*} [DecidableEq P] [DecidableEq Q] [DecidableEq S] [DecidableEq S']

/-- §1: if each γ ∈ V has at least one site `x` with `x ∈ supp γ ∧ x ∈ T`, then for nonnegative `f`,
`Σ_{γ∈V} f γ ≤ Σ_{x∈T} Σ_{γ∈V, x ∈ supp γ} f γ`. -/
theorem recount_le (supp : P → Finset S) (V : Finset P) (T : Finset S) (f : P → ℝ)
    (hf : ∀ γ, 0 ≤ f γ) (hcov : ∀ γ ∈ V, ∃ x ∈ T, x ∈ supp γ) :
    ∑ γ ∈ V, f γ ≤ ∑ x ∈ T, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro γ hγ
  obtain ⟨x, hxT, hx⟩ := hcov γ hγ
  have hle : (if x ∈ supp γ then f γ else 0) ≤ ∑ y ∈ T, if y ∈ supp γ then f γ else 0 :=
    single_le_sum (f := fun y => if y ∈ supp γ then f γ else 0)
      (fun y _ => by split_ifs <;> simp [hf]) hxT
  simpa [hx] using hle

/-- §2: one coarse-graining step. -/
theorem blocking_kp (supp : P → Finset S) (suppQ : Q → Finset S') (π : P → Q) (β : S → S')
    (z : P → ℝ) (U : Finset P) (Sfin : Finset S) (a a' b ε Ld : ℝ)
    (hsub : ∀ γ ∈ U, supp γ ⊆ Sfin)
    (hcover : ∀ γ ∈ U, ∀ x' ∈ suppQ (π γ), ∃ x ∈ supp γ, β x = x')
    (hsize : ∀ γ ∈ U, a' * (suppQ (π γ)).card ≤ a * (supp γ).card - b)
    (hfine : ∀ x, ∑ γ ∈ U.filter (fun s => x ∈ supp s), |z γ| * Real.exp (a * (supp γ).card) ≤ ε)
    (hfiber : ∀ x', ((Sfin.filter (fun x => β x = x')).card : ℝ) ≤ Ld) (hε : 0 ≤ ε) :
    ∀ x', ∑ q ∈ (U.image π).filter (fun q => x' ∈ suppQ q),
      |∑ γ ∈ U.filter (fun s => π s = q), z γ| * Real.exp (a' * (suppQ q).card) ≤
        Ld * Real.exp (-b) * ε := by
  intro x'
  set f : P → ℝ := fun γ => |z γ| * Real.exp (a * (supp γ).card) with hfdef
  have hf0 : ∀ γ, 0 ≤ f γ := fun γ => by rw [hfdef]; positivity
  set V := U.filter (fun s => x' ∈ suppQ (π s)) with hV
  -- (1) Bound the coarse activity by the sum of fine activities and merge the fibre sums into one sum
  have step1 : ∑ q ∈ (U.image π).filter (fun q => x' ∈ suppQ q),
      |∑ γ ∈ U.filter (fun s => π s = q), z γ| * Real.exp (a' * (suppQ q).card) ≤
      ∑ γ ∈ V, |z γ| * Real.exp (a' * (suppQ (π γ)).card) := by
    have hinner : ∀ q ∈ (U.image π).filter (fun q => x' ∈ suppQ q),
        |∑ γ ∈ U.filter (fun s => π s = q), z γ| * Real.exp (a' * (suppQ q).card) ≤
        ∑ γ ∈ V.filter (fun s => π s = q), |z γ| * Real.exp (a' * (suppQ (π γ)).card) := by
      intro q hq
      have hxq : x' ∈ suppQ q := (mem_filter.mp hq).2
      have hfil : V.filter (fun s => π s = q) = U.filter (fun s => π s = q) := by
        ext γ; simp only [hV, mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hxq⟩, h3⟩
      rw [hfil]
      calc |∑ γ ∈ U.filter (fun s => π s = q), z γ| * Real.exp (a' * (suppQ q).card)
          ≤ (∑ γ ∈ U.filter (fun s => π s = q), |z γ|) * Real.exp (a' * (suppQ q).card) :=
            mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
        _ = ∑ γ ∈ U.filter (fun s => π s = q), |z γ| * Real.exp (a' * (suppQ (π γ)).card) := by
            rw [sum_mul]
            refine sum_congr rfl fun γ hγ => ?_
            rw [(mem_filter.mp hγ).2]
    refine le_trans (sum_le_sum hinner) ?_
    rw [sum_fiberwise_of_maps_to]
    intro γ hγ
    rw [hV, mem_filter] at hγ
    exact mem_filter.mpr ⟨mem_image_of_mem π hγ.1, hγ.2⟩
  -- (2) Size condition
  have step2 : ∑ γ ∈ V, |z γ| * Real.exp (a' * (suppQ (π γ)).card) ≤
      Real.exp (-b) * ∑ γ ∈ V, f γ := by
    rw [mul_sum]
    apply sum_le_sum
    intro γ hγ
    have hγU : γ ∈ U := (mem_filter.mp hγ).1
    have h1 : Real.exp (a' * (suppQ (π γ)).card) ≤ Real.exp (-b) * Real.exp (a * (supp γ).card) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [hsize γ hγU]
    calc |z γ| * Real.exp (a' * (suppQ (π γ)).card)
        ≤ |z γ| * (Real.exp (-b) * Real.exp (a * (supp γ).card)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = Real.exp (-b) * f γ := by rw [hfdef]; ring
  -- (3) Recount by sites of the blocks
  set T := Sfin.filter (fun x => β x = x') with hT
  have step3 : ∑ γ ∈ V, f γ ≤ ∑ x ∈ T, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ := by
    apply recount_le supp V T f hf0
    intro γ hγ
    have hγU : γ ∈ U := (mem_filter.mp hγ).1
    obtain ⟨x, hx, hβ⟩ := hcover γ hγU x' (mem_filter.mp hγ).2
    exact ⟨x, mem_filter.mpr ⟨hsub γ hγU hx, hβ⟩, hx⟩
  have step4 : ∑ x ∈ T, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ ≤ Ld * ε := by
    have h1 : ∀ x ∈ T, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ ≤ ε := by
      intro x _
      refine le_trans ?_ (hfine x)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun s _ _ => hf0 s)
    calc ∑ x ∈ T, ∑ γ ∈ V.filter (fun s => x ∈ supp s), f γ ≤ ∑ _x ∈ T, ε := sum_le_sum h1
      _ = T.card * ε := by simp
      _ ≤ Ld * ε := mul_le_mul_of_nonneg_right (hfiber x') hε
  have hb : 0 < Real.exp (-b) := Real.exp_pos _
  calc _ ≤ ∑ γ ∈ V, |z γ| * Real.exp (a' * (suppQ (π γ)).card) := step1
    _ ≤ Real.exp (-b) * ∑ γ ∈ V, f γ := step2
    _ ≤ Real.exp (-b) * (Ld * ε) :=
        mul_le_mul_of_nonneg_left (le_trans step3 step4) hb.le
    _ = Ld * Real.exp (-b) * ε := by ring

#print axioms recount_le
#print axioms blocking_kp

end PolymerBlocking
