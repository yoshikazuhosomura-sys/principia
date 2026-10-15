/-
  階層（Migdal–Kadanoff）模型の鎖の段数の帳簿：上端を母数 β₀ にした一般形と、
  一つのセルの判定「各行の上界 ≤ 要求」を列ごとの係数の和から出す有限の不等式。
  組み立ての有限の代数だけ。計算機援用の入力（管の不変性・一段の b の下がり幅・出口の包含・帯の定理・
  列ごとの係数の上界）は仮定として受け取る。写像そのもの・測度・区間演算は形式化していない。
  （段数の補題は同じ帳簿の先行の版を、このファイルだけで読めるように書き直して含める。）
-/
import Mathlib

namespace LatticeGaugeHierarchicalChainGeneral

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

/-- **鎖の段数の β₀ 一般版**：出発の点が `b x ≤ β₀` を満たし、管の中で一段ごとに `b` が `0.2196` 以上下がるか
出口 `D` に入り（出口の下端 `0.95`）、帯の側のセルの番号が `≤ 556` なら、
`⌈(β₀ − 0.95)/0.2196⌉ + 558` 段以内に判定領域 `K` に入る。仮定は計算機援用の入力をそのまま受け取ったもの。 -/
theorem mk_full_chain_general {X : Type*} (f : X → X) (U D K : X → Prop) (b : X → ℝ) (r : X → ℕ)
    (β₀ : ℝ)
    (hU : ∀ x, U x → (19 / 20 : ℝ) ≤ b x) (hb : ∀ x, U x → b x ≤ β₀)
    (hstepU : ∀ x, U x → (U (f x) ∧ b (f x) ≤ b x - 2196 / 10000) ∨ D (f x))
    (hstepD : ∀ y, D y → (D (f y) ∧ r (f y) < r y) ∨ K (f y))
    (hr : ∀ y, D y → r y ≤ 556) :
    ∀ x, U x → ∃ k, k ≤ ⌈(β₀ - 19 / 20) / (2196 / 10000)⌉₊ + 558 ∧ K (f^[k] x) := by
  intro x hx
  obtain ⟨k, hk, hK⟩ :=
    chain_top f U D K b r (2196 / 10000) (19 / 20) β₀ (by norm_num) 556 hU hb hstepU hstepD hr x hx
  exact ⟨k, by omega, hK⟩

/-- 照合：`β₀ = 128` で一般版の段数は `579 + 558 = 1137`（先行の版の `mk_full_chain_128` と同じ数）。 -/
theorem steps_general_at_128 : ⌈((128 : ℝ) - 19 / 20) / (2196 / 10000)⌉₊ + 558 = 1137 := by
  have h : ⌈((128 : ℝ) - 19 / 20) / (2196 / 10000)⌉₊ = 579 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  rw [h]

/-- 段数の式は β₀ について単調（上端を上げても段数の上界は減らない）。 -/
theorem steps_general_mono {β₁ β₂ : ℝ} (h : β₁ ≤ β₂) :
    ⌈(β₁ - 19 / 20) / (2196 / 10000)⌉₊ + 558 ≤ ⌈(β₂ - 19 / 20) / (2196 / 10000)⌉₊ + 558 := by
  have : (β₁ - 19 / 20) / (2196 / 10000) ≤ (β₂ - 19 / 20) / (2196 / 10000) := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  have := Nat.ceil_mono this
  omega

/-- 段数の式の線形の上界：`⌈(β₀ − 0.95)/0.2196⌉ + 558 ≤ (β₀ − 0.95)/0.2196 + 559`（`β₀ ≥ 0.95`）。 -/
theorem steps_general_le_linear {β₀ : ℝ} (h : 19 / 20 ≤ β₀) :
    ((⌈(β₀ - 19 / 20) / (2196 / 10000)⌉₊ + 558 : ℕ) : ℝ) ≤ (β₀ - 19 / 20) / (2196 / 10000) + 559 := by
  have h0 : 0 ≤ (β₀ - 19 / 20) / (2196 / 10000) := by
    apply div_nonneg <;> linarith
  have := Nat.ceil_lt_add_one h0
  push_cast
  linarith

/-- **一行の判定の帳簿**：行の上界が四つの項（欠損・線形・二次・剰余）の和で、各項が重み `W > 0` の
`e, l, qd, r` 倍以下、要求が `W` 以上（像の s′ がセルの中心より大きいので W(s′) ≥ W(s_c)）、
`e + l + qd + r < 1` なら、行の上界は要求より小さい。 -/
theorem row_lt_req_of_columns (base lin quad rem W req e l qd r : ℝ) (hW : 0 < W) (hreq : W ≤ req)
    (hb : base ≤ e * W) (hl : lin ≤ l * W) (hq : quad ≤ qd * W) (hr : rem ≤ r * W)
    (hsum : e + l + qd + r < 1) : base + lin + quad + rem < req := by
  calc base + lin + quad + rem ≤ e * W + l * W + qd * W + r * W := by linarith
    _ = (e + l + qd + r) * W := by ring
    _ < 1 * W := mul_lt_mul_of_pos_right hsum hW
    _ = W := one_mul W
    _ ≤ req := hreq

/-- **u に一様な形**：二次の列だけが `q1·u` で他の列が定数 `e0, l0, r0` で押さえられ、
`u ∈ [0, u*]` の端で和が 1 未満なら、区間の全ての `u` で和が 1 未満（単調性の帳簿）。 -/
theorem uniform_columns (e0 l0 q1 r0 ustar : ℝ) (hq1 : 0 ≤ q1) (hsum : e0 + l0 + q1 * ustar + r0 < 1) :
    ∀ u : ℝ, 0 ≤ u → u ≤ ustar → e0 + l0 + q1 * u + r0 < 1 := by
  intro u _ hu
  have : q1 * u ≤ q1 * ustar := mul_le_mul_of_nonneg_left hu hq1
  linarith

/-- 数の一行：列の係数 `e0 = 0.2604`（紙の主項 σ₁/R の上界）、`l0 = 0.2570`、`q1 = 2`、`r0 = 0.0835`
（β = 128, 256 のセルの測った値を少し上に丸めたもの）と `u* = 1/128` で和は 1 未満（0.6165…）。**列の係数が [128, ∞) で
この値以下であることは仮定であり、示していない。** -/
theorem uniform_columns_numeric :
    (2604 / 10000 : ℝ) + 2570 / 10000 + 2 * (1 / 128) + 835 / 10000 < 1 := by
  norm_num

/-- 上の二つを合わせた形：列の係数の仮定の下で、全ての `u ∈ [0, 1/128]` で和は 1 未満。 -/
theorem uniform_columns_128 : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 128 →
    (2604 / 10000 : ℝ) + 2570 / 10000 + 2 * u + 835 / 10000 < 1 :=
  uniform_columns _ _ _ _ _ (by norm_num) uniform_columns_numeric

end LatticeGaugeHierarchicalChainGeneral

#print axioms LatticeGaugeHierarchicalChainGeneral.tube_exit_of_lt
#print axioms LatticeGaugeHierarchicalChainGeneral.tube_exit_top
#print axioms LatticeGaugeHierarchicalChainGeneral.cell_descent
#print axioms LatticeGaugeHierarchicalChainGeneral.chain_top
#print axioms LatticeGaugeHierarchicalChainGeneral.mk_full_chain_general
#print axioms LatticeGaugeHierarchicalChainGeneral.steps_general_at_128
#print axioms LatticeGaugeHierarchicalChainGeneral.steps_general_mono
#print axioms LatticeGaugeHierarchicalChainGeneral.steps_general_le_linear
#print axioms LatticeGaugeHierarchicalChainGeneral.row_lt_req_of_columns
#print axioms LatticeGaugeHierarchicalChainGeneral.uniform_columns
#print axioms LatticeGaugeHierarchicalChainGeneral.uniform_columns_numeric
#print axioms LatticeGaugeHierarchicalChainGeneral.uniform_columns_128
