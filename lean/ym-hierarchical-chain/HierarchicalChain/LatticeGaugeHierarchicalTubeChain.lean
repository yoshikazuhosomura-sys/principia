/-
  階層（Migdal–Kadanoff）模型の帯の継ぎ目：組み立ての有限の代数だけ。
  計算機援用の入力（管の不変性・一段の b の下がり幅・出口の包含・帯の定理）は仮定として受け取る。
  写像そのもの・測度・区間演算は形式化していない。
-/
import Mathlib

namespace LatticeGaugeHierarchicalTubeChain

open Function

/-- 管の中では一段ごとに `b` が `δ` 以上下がり、管を出るときは出口 `E` に入るなら、
`b x - blo < n δ` の点は `n` 段以内に `E` に入る。 -/
theorem tube_exit_of_lt {X : Type*} (f : X → X) (U E : X → Prop) (b : X → ℝ) (δ blo : ℝ)
    (hU : ∀ x, U x → blo ≤ b x)
    (hstep : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - δ) ∨ E (f x)) :
    ∀ n : ℕ, ∀ x, U x → b x - blo < n * δ → ∃ k, 1 ≤ k ∧ k ≤ n ∧ E (f^[k] x) := by
  intro n
  induction n with
  | zero =>
    intro x hx h
    have := hU x hx
    simp at h
    linarith
  | succ n ih =>
    intro x hx h
    rcases hstep x hx with ⟨hU', hb⟩ | hE
    · obtain ⟨k, hk1, hkn, hE⟩ := ih (f x) hU' (by push_cast at h; linarith)
      refine ⟨k + 1, by omega, by omega, ?_⟩
      rw [iterate_succ_apply]
      exact hE
    · exact ⟨1, le_refl _, by omega, by simpa using hE⟩

/-- 段数の一様な上界：`δ > 0` なら `⌈(b x - blo)/δ⌉ + 1` 段以内。 -/
theorem tube_exit {X : Type*} (f : X → X) (U E : X → Prop) (b : X → ℝ) (δ blo : ℝ) (hδ : 0 < δ)
    (hU : ∀ x, U x → blo ≤ b x)
    (hstep : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - δ) ∨ E (f x)) :
    ∀ x, U x → ∃ k, 1 ≤ k ∧ k ≤ ⌈(b x - blo) / δ⌉₊ + 1 ∧ E (f^[k] x) := by
  intro x hx
  apply tube_exit_of_lt f U E b δ blo hU hstep _ x hx
  have h1 : (b x - blo) / δ ≤ (⌈(b x - blo) / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : b x - blo ≤ (⌈(b x - blo) / δ⌉₊ : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at h1
  push_cast
  nlinarith

/-- 二つの段の合成：`P` から `n₁` 段以内に `Q`、`Q` から `n₂` 段以内に `R` なら、`P` から `n₁ + n₂` 段以内に `R`。 -/
theorem chain_compose {X : Type*} (f : X → X) (P Q R : X → Prop) (n₁ n₂ : ℕ)
    (h₁ : ∀ x, P x → ∃ k, k ≤ n₁ ∧ Q (f^[k] x))
    (h₂ : ∀ y, Q y → ∃ k, k ≤ n₂ ∧ R (f^[k] y)) :
    ∀ x, P x → ∃ k, k ≤ n₁ + n₂ ∧ R (f^[k] x) := by
  intro x hx
  obtain ⟨k₁, hk₁, hq⟩ := h₁ x hx
  obtain ⟨k₂, hk₂, hr⟩ := h₂ _ hq
  exact ⟨k₂ + k₁, by omega, by rw [iterate_add_apply]; exact hr⟩

/-- 管の重みの単調性：`0 ≤ s`、`0 ≤ R ≤ R'`、`0 ≤ A ≤ A'`、`0 ≤ q` なら
`R (q² s⁴ + A q s³) ≤ R' (q² s⁴ + A' q s³)`（区分ごとの管の包含の一行）。 -/
theorem tube_weight_mono (q s R R' A A' : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s) (hR : 0 ≤ R) (hRR : R ≤ R')
    (hA : 0 ≤ A) (hAA : A ≤ A') :
    R * (q ^ 2 * s ^ 4 + A * q * s ^ 3) ≤ R' * (q ^ 2 * s ^ 4 + A' * q * s ^ 3) := by
  have h0 : 0 ≤ q ^ 2 * s ^ 4 + A * q * s ^ 3 := by positivity
  have h1 : q ^ 2 * s ^ 4 + A * q * s ^ 3 ≤ q ^ 2 * s ^ 4 + A' * q * s ^ 3 := by
    have : A * (q * s ^ 3) ≤ A' * (q * s ^ 3) := mul_le_mul_of_nonneg_right hAA (by positivity)
    nlinarith
  calc R * (q ^ 2 * s ^ 4 + A * q * s ^ 3) ≤ R' * (q ^ 2 * s ^ 4 + A * q * s ^ 3) :=
        mul_le_mul_of_nonneg_right hRR h0
    _ ≤ R' * (q ^ 2 * s ^ 4 + A' * q * s ^ 3) := mul_le_mul_of_nonneg_left h1 (le_trans hR hRR)

/-- 帯の側（セルの番号 `r` が一段ごとに狭義に下がるか、判定領域 `K` に入る）：`r y + 1` 段以内に `K`。 -/
theorem cell_descent {X : Type*} (f : X → X) (D K : X → Prop) (r : X → ℕ)
    (hstep : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y)) :
    ∀ y, D y → ∃ k, 1 ≤ k ∧ k ≤ r y + 1 ∧ K (f^[k] y) := by
  intro y hy
  have hU : ∀ z, D z → (0 : ℝ) ≤ (r z : ℝ) := fun z _ => Nat.cast_nonneg _
  have hs : ∀ z, D z → (D (f z) ∧ (r (f z) : ℝ) ≤ (r z : ℝ) - 1) ∨ K (f z) := by
    intro z hz
    rcases hstep z hz with ⟨h1, h2⟩ | h
    · left
      refine ⟨h1, ?_⟩
      have : r (f z) + 1 ≤ r z := h2
      have : ((r (f z) + 1 : ℕ) : ℝ) ≤ (r z : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    · exact Or.inr h
  apply tube_exit_of_lt f D K (fun z => (r z : ℝ)) 1 0 hU hs (r y + 1) y hy
  push_cast
  linarith

/-- 継いだ言明の組み立て：管 `U`（一段 `δ` 以上下がる）→ 出口 `D` → 帯の定理（`r` 段＋1 以内に `K`）。
段数は `⌈(b x - blo)/δ⌉ + 1 + (R_D + 1)` 以内（`R_D` は `D` の中のセルの番号の上界）。 -/
theorem mk_full_chain {X : Type*} (f : X → X) (U D K : X → Prop) (b : X → ℝ) (r : X → ℕ)
    (δ blo : ℝ) (hδ : 0 < δ) (RD : ℕ)
    (hU : ∀ x, U x → blo ≤ b x)
    (hstepU : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - δ) ∨ D (f x))
    (hstepD : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y))
    (hr : ∀ y, D y → r y ≤ RD) :
    ∀ x, U x → ∃ k, k ≤ ⌈(b x - blo) / δ⌉₊ + 1 + (RD + 1) ∧ K (f^[k] x) := by
  intro x hx
  obtain ⟨k₁, -, hk₁, hD⟩ := tube_exit f U D b δ blo hδ hU hstepU x hx
  obtain ⟨k₂, -, hk₂, hK⟩ := cell_descent f D K r hstepD _ hD
  have := hr _ hD
  exact ⟨k₂ + k₁, by omega, by rw [iterate_add_apply]; exact hK⟩


/-- 数の一行：`⌈(64 - 19/20)/(2196/10000)⌉ = 288`（一段の下がり幅の下界 0.2196・出口 0.95・上端 64）。 -/
theorem steps_numeric : ⌈((64 : ℝ) - 19 / 20) / (2196 / 10000)⌉₊ = 288 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- 上端 `b x ≤ 64`、下がり幅 `δ = 0.2196`、出口 `blo = 0.95`、帯の側のセルの番号 `≤ 556` のとき、
`288 + 1 + 557 = 846` 段以内に判定領域 `K` に入る（仮定は計算機援用の入力をそのまま受け取ったもの）。 -/
theorem mk_full_chain_64 {X : Type*} (f : X → X) (U D K : X → Prop) (b : X → ℝ) (r : X → ℕ)
    (hU : ∀ x, U x → (19 / 20 : ℝ) ≤ b x) (hb64 : ∀ x, U x → b x ≤ 64)
    (hstepU : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - 2196 / 10000) ∨ D (f x))
    (hstepD : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y))
    (hr : ∀ y, D y → r y ≤ 556) :
    ∀ x, U x → ∃ k, k ≤ 846 ∧ K (f^[k] x) := by
  intro x hx
  obtain ⟨k, hk, hK⟩ := mk_full_chain f U D K b r (2196 / 10000) (19 / 20) (by norm_num) 556 hU hstepU hstepD hr x hx
  have hc : ⌈(b x - 19 / 20) / (2196 / 10000 : ℝ)⌉₊ ≤ 288 := by
    rw [← steps_numeric]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [hb64 x hx]
  exact ⟨k, by omega, hK⟩

end LatticeGaugeHierarchicalTubeChain

#print axioms LatticeGaugeHierarchicalTubeChain.tube_exit_of_lt
#print axioms LatticeGaugeHierarchicalTubeChain.tube_exit
#print axioms LatticeGaugeHierarchicalTubeChain.chain_compose
#print axioms LatticeGaugeHierarchicalTubeChain.tube_weight_mono
#print axioms LatticeGaugeHierarchicalTubeChain.cell_descent
#print axioms LatticeGaugeHierarchicalTubeChain.mk_full_chain
#print axioms LatticeGaugeHierarchicalTubeChain.steps_numeric
#print axioms LatticeGaugeHierarchicalTubeChain.mk_full_chain_64
