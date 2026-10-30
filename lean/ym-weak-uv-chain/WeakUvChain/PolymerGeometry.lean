/-
Two ingredients of premise 3. Single file; checks with `import Mathlib` only.

  §1 Merged activity: if the activity is a product of local factors on its support, z(A) = Π_{x∈A} φ(x) (locality),
     with |φ(x)| ≥ δ > 0 at every point and e^{a} δ ≥ 1, then with weights
     |z(A∪B)| e^{a|A∪B|} ≤ (|z(A)| e^{a|A|})·(|z(B)| e^{a|B|})
     (one gains a factor per point of the intersection: |A∪B| = |A| + |B| − |A∩B|).
  §2 Coarse-graining geometry: taking the coarse support to be the image β(supp γ) of the fine support, the covering
     holds by definition and |β(supp γ)| ≤ |supp γ|.
     If 0 ≤ a′ ≤ a and |γ| ≥ 1, then a′|πγ| ≤ a|γ| − b with b = a − a′.
  §3 Hypercubic lattice: with points Fin d → ℕ and block map β x = (x i / L)_i (L ≥ 1), each block has
     ≤ L^d points (L_d = L^d in PolymerBlocking). ρ = L^d e^{−b} < 1 ⇔ b > d ln L.
  §4 #print axioms
-/
import Mathlib

namespace PolymerGeometry

open Finset

/-! ## 1. Merged activity (locality) -/

theorem union_activity_le {S : Type*} [DecidableEq S] (φ : S → ℝ) (A B : Finset S) (a δ : ℝ)
    (hδ : 0 < δ) (hφ : ∀ x, δ ≤ |φ x|) (hea : 1 ≤ Real.exp a * δ) :
    |∏ x ∈ A ∪ B, φ x| * Real.exp (a * (A ∪ B).card) ≤
      (|∏ x ∈ A, φ x| * Real.exp (a * A.card)) * (|∏ x ∈ B, φ x| * Real.exp (a * B.card)) := by
  have hunion := prod_union_inter (s₁ := A) (s₂ := B) (f := φ)
  have hcard := card_union_add_card_inter A B
  rw [abs_prod, abs_prod, abs_prod]
  set PU := ∏ x ∈ A ∪ B, |φ x|
  set PI := ∏ x ∈ A ∩ B, |φ x|
  set PA := ∏ x ∈ A, |φ x|
  set PB := ∏ x ∈ B, |φ x|
  have habs : PU * PI = PA * PB := by
    have := congrArg abs hunion
    rw [abs_mul, abs_mul, abs_prod, abs_prod, abs_prod, abs_prod] at this
    exact this
  -- Lower bound on the product over the intersection: PI ≥ δ^{|A∩B|}
  have hPI : δ ^ (A ∩ B).card ≤ PI := by
    calc δ ^ (A ∩ B).card = ∏ _x ∈ A ∩ B, δ := by rw [prod_const]
      _ ≤ PI := prod_le_prod (fun _ _ => hδ.le) (fun x _ => hφ x)
  have hPIpos : 0 < PI := lt_of_lt_of_le (pow_pos hδ _) hPI
  have hPU0 : 0 ≤ PU := prod_nonneg fun _ _ => abs_nonneg _
  -- e^{a|A∩B|} δ^{|A∩B|} ≥ 1
  have hgain : 1 ≤ Real.exp (a * (A ∩ B).card) * δ ^ (A ∩ B).card := by
    have : Real.exp (a * (A ∩ B).card) * δ ^ (A ∩ B).card = (Real.exp a * δ) ^ (A ∩ B).card := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [this]; exact one_le_pow₀ hea
  have hexp : Real.exp (a * A.card) * Real.exp (a * B.card) =
      Real.exp (a * (A ∪ B).card) * Real.exp (a * (A ∩ B).card) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1
    have : ((A.card : ℝ) + B.card) = (A ∪ B).card + (A ∩ B).card := by exact_mod_cast hcard.symm
    linear_combination a * this
  have hE : 0 < Real.exp (a * (A ∪ B).card) := Real.exp_pos _
  calc PU * Real.exp (a * (A ∪ B).card)
      ≤ PU * Real.exp (a * (A ∪ B).card) * (Real.exp (a * (A ∩ B).card) * δ ^ (A ∩ B).card) := by
        have := mul_le_mul_of_nonneg_left hgain (mul_nonneg hPU0 hE.le)
        linarith
    _ ≤ PU * Real.exp (a * (A ∪ B).card) * (Real.exp (a * (A ∩ B).card) * PI) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hPU0 hE.le)
        exact mul_le_mul_of_nonneg_left hPI (Real.exp_pos _).le
    _ = (PU * PI) * (Real.exp (a * (A ∪ B).card) * Real.exp (a * (A ∩ B).card)) := by ring
    _ = (PA * PB) * (Real.exp (a * A.card) * Real.exp (a * B.card)) := by rw [habs, hexp]
    _ = (PA * Real.exp (a * A.card)) * (PB * Real.exp (a * B.card)) := by ring

/-! ## 2. Coarse-graining geometry: image support -/

/-- Covering: each point of the image support is the image of a point of the fine support. -/
theorem image_cover {S S' : Type*} [DecidableEq S'] (β : S → S') (A : Finset S) :
    ∀ x' ∈ A.image β, ∃ x ∈ A, β x = x' := by
  intro x' hx'; exact mem_image.mp hx'

/-- Size condition: if `0 ≤ a′ ≤ a` and `|A| ≥ 1`, then `a′ |β(A)| ≤ a |A| − (a − a′)`. -/
theorem image_size_condition {S S' : Type*} [DecidableEq S'] (β : S → S') (A : Finset S)
    (a a' : ℝ) (ha' : 0 ≤ a') (haa : a' ≤ a) (hA : 1 ≤ A.card) :
    a' * (A.image β).card ≤ a * A.card - (a - a') := by
  have h1 : ((A.image β).card : ℝ) ≤ A.card := by exact_mod_cast card_image_le
  have h2 : (1 : ℝ) ≤ A.card := by exact_mod_cast hA
  nlinarith

/-! ## 3. Blocks of the hypercubic lattice -/

/-- For the block map `β x = (x i / L)_i`, each block has `≤ L^d` points (independent of the point set `Sfin`). -/
theorem block_fiber_card {d : ℕ} (L : ℕ) (hL : 1 ≤ L) (Sfin : Finset (Fin d → ℕ))
    (x' : Fin d → ℕ) :
    ((Sfin.filter (fun x => (fun i => x i / L) = x')).card : ℝ) ≤ (L : ℝ) ^ d := by
  have hsub : Sfin.filter (fun x => (fun i => x i / L) = x') ⊆
      Fintype.piFinset (fun i => Finset.Ico (L * x' i) (L * x' i + L)) := by
    intro x hx
    rw [mem_filter] at hx
    rw [Fintype.mem_piFinset]
    intro i
    have hi : x i / L = x' i := congrFun hx.2 i
    rw [Finset.mem_Ico]
    have hLpos : 0 < L := by omega
    constructor
    · rw [← hi]; exact Nat.mul_div_le (x i) L
    · rw [← hi]
      have := Nat.lt_mul_div_succ (x i) hLpos
      linarith [Nat.mul_comm L (x i / L)]
  have hcard := card_le_card hsub
  rw [Fintype.card_piFinset] at hcard
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left, prod_const, card_univ, Fintype.card_fin] at hcard
  exact_mod_cast hcard

/-- Contraction condition: `ρ = L^d e^{−b} < 1` ⇔ `b > d ln L` (`L ≥ 1`). -/
theorem contraction_iff (L : ℝ) (d : ℕ) (hL : 1 ≤ L) (b : ℝ) :
    L ^ d * Real.exp (-b) < 1 ↔ (d : ℝ) * Real.log L < b := by
  have hLp : 0 < L := by linarith
  have hpow : 0 < L ^ d := pow_pos hLp d
  have e : L ^ d = Real.exp ((d : ℝ) * Real.log L) := by
    rw [← Real.log_pow, Real.exp_log hpow]
  rw [e, ← Real.exp_add, ← Real.exp_zero, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

#print axioms union_activity_le
#print axioms image_cover
#print axioms image_size_condition
#print axioms block_fiber_card
#print axioms contraction_iff

end PolymerGeometry
