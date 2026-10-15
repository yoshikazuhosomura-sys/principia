/-
  階層（Migdal–Kadanoff）模型の鎖の段数の帳簿：管の上端を 64 から 128 へ延ばしたときの数え方。
  組み立ての有限の代数だけ。計算機援用の入力（管の不変性・一段の b の下がり幅・出口の包含・帯の定理）は
  仮定として受け取る。写像そのもの・測度・区間演算は形式化していない。
  （同じ帳簿の 64 版の補題を、このファイルだけで読めるように書き直して含める。）
-/
import Mathlib

namespace LatticeGaugeHierarchicalUpperTube

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

/-- 上端 `B` の管：`b x ≤ B`、`δ > 0` なら `⌈(B - blo)/δ⌉ + 1` 段以内に出口。 -/
theorem tube_exit_top {X : Type*} (f : X → X) (U E : X → Prop) (b : X → ℝ) (δ blo B : ℝ) (hδ : 0 < δ)
    (hU : ∀ x, U x → blo ≤ b x) (hB : ∀ x, U x → b x ≤ B)
    (hstep : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - δ) ∨ E (f x)) :
    ∀ x, U x → ∃ k, 1 ≤ k ∧ k ≤ ⌈(B - blo) / δ⌉₊ + 1 ∧ E (f^[k] x) := by
  intro x hx
  apply tube_exit_of_lt f U E b δ blo hU hstep _ x hx
  have h1 : (B - blo) / δ ≤ (⌈(B - blo) / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : B - blo ≤ (⌈(B - blo) / δ⌉₊ : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at h1
  have := hB x hx
  push_cast
  nlinarith

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

/-- 上端 `B` の鎖：管（一段 `δ` 以上下がる・`b ≤ B`）→ 出口 `D` → 帯（`RD + 1` 段以内に `K`）。 -/
theorem chain_top {X : Type*} (f : X → X) (U D K : X → Prop) (b : X → ℝ) (r : X → ℕ)
    (δ blo B : ℝ) (hδ : 0 < δ) (RD : ℕ)
    (hU : ∀ x, U x → blo ≤ b x) (hB : ∀ x, U x → b x ≤ B)
    (hstepU : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - δ) ∨ D (f x))
    (hstepD : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y))
    (hr : ∀ y, D y → r y ≤ RD) :
    ∀ x, U x → ∃ k, k ≤ ⌈(B - blo) / δ⌉₊ + 1 + (RD + 1) ∧ K (f^[k] x) := by
  intro x hx
  obtain ⟨k₁, -, hk₁, hD⟩ := tube_exit_top f U D b δ blo B hδ hU hB hstepU x hx
  obtain ⟨k₂, -, hk₂, hK⟩ := cell_descent f D K r hstepD _ hD
  have := hr _ hD
  exact ⟨k₂ + k₁, by omega, by rw [iterate_add_apply]; exact hK⟩

/-- 数の一行：`⌈(128 - 19/20)/(2196/10000)⌉ = 579`。 -/
theorem steps_numeric_128 : ⌈((128 : ℝ) - 19 / 20) / (2196 / 10000)⌉₊ = 579 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- 数の一行（64 版との照合）：`⌈(64 - 19/20)/(2196/10000)⌉ = 288`。 -/
theorem steps_numeric_64 : ⌈((64 : ℝ) - 19 / 20) / (2196 / 10000)⌉₊ = 288 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- 上端 `b x ≤ 128`、下がり幅 `δ = 0.2196`、出口 `blo = 0.95`、帯の側のセルの番号 `≤ 556` のとき、
`579 + 1 + 557 = 1137` 段以内に判定領域 `K` に入る（仮定は計算機援用の入力をそのまま受け取ったもの）。 -/
theorem mk_full_chain_128 {X : Type*} (f : X → X) (U D K : X → Prop) (b : X → ℝ) (r : X → ℕ)
    (hU : ∀ x, U x → (19 / 20 : ℝ) ≤ b x) (hb : ∀ x, U x → b x ≤ 128)
    (hstepU : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - 2196 / 10000) ∨ D (f x))
    (hstepD : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y))
    (hr : ∀ y, D y → r y ≤ 556) :
    ∀ x, U x → ∃ k, k ≤ 1137 ∧ K (f^[k] x) := by
  intro x hx
  obtain ⟨k, hk, hK⟩ := chain_top f U D K b r (2196 / 10000) (19 / 20) 128 (by norm_num) 556 hU hb hstepU hstepD hr x hx
  rw [steps_numeric_128] at hk
  exact ⟨k, by omega, hK⟩

/-- 管が二つの区間の和（下の管 `U₁`：`b ≤ 64`、上の管 `U₂`：`64 ≤ b ≤ 128`）で、各段は
「和の管に留まり δ 以上下がる」か出口に入るなら、和の管は上の補題の `U` に当たる（言い換えの一行）。 -/
theorem union_tube_step {X : Type*} (f : X → X) (U₁ U₂ D : X → Prop) (b : X → ℝ) (δ : ℝ)
    (h₁ : ∀ x, U₁ x → ((U₁ (f x) ∨ U₂ (f x)) ∧ b (f x) ≤ b x - δ) ∨ D (f x))
    (h₂ : ∀ x, U₂ x → ((U₁ (f x) ∨ U₂ (f x)) ∧ b (f x) ≤ b x - δ) ∨ D (f x)) :
    ∀ x, (U₁ x ∨ U₂ x) → ((U₁ (f x) ∨ U₂ (f x)) ∧ b (f x) ≤ b x - δ) ∨ D (f x) := by
  intro x hx
  rcases hx with h | h
  · exact h₁ x h
  · exact h₂ x h

end LatticeGaugeHierarchicalUpperTube

#print axioms LatticeGaugeHierarchicalUpperTube.tube_exit_of_lt
#print axioms LatticeGaugeHierarchicalUpperTube.tube_exit_top
#print axioms LatticeGaugeHierarchicalUpperTube.cell_descent
#print axioms LatticeGaugeHierarchicalUpperTube.chain_top
#print axioms LatticeGaugeHierarchicalUpperTube.steps_numeric_128
#print axioms LatticeGaugeHierarchicalUpperTube.steps_numeric_64
#print axioms LatticeGaugeHierarchicalUpperTube.mk_full_chain_128
#print axioms LatticeGaugeHierarchicalUpperTube.union_tube_step
