/-
  曲線の場合の Weil 正値性を支える線形代数の核を閉じる。

  曲線 C/F_q の場合、Weil の正値性は曲面 S = C×C の交点形式に対する Hodge 指数定理
  （署名 (1, ρ−1)）から一行で出る。その「一行」を抽象的な対称双線形形式の言明として取り出す：

  * reverse_cauchy_schwarz : 豊富な類 h（Q h > 0）があり h の直交補空間で形式が ≤ 0 なら
      Q x * Q h ≤ (B x h)^2（逆 Cauchy–Schwarz）。
  * castelnuovo_severi : 双曲平面 f₁,f₂（Q f₁ = Q f₂ = 0, B f₁ f₂ = 1）の直交補空間で
      形式が ≤ 0 なら Q D ≤ 2 (B D f₁)(B D f₂)。
  * no_ample_of_two_negatives : 互いに直交する二つの負の方向があると、
      どの超平面（線形汎関数の核）に制限しても形式は半正定値にならない。

  三番目が本稿の要点である。Weil の二次形式の「極＋アルキメデス」部分 S_L は
  負の慣性指数が ⌈2L−1⌉ で L とともに増える（数値計算による）。したがって
  L > 1 ではどの超平面に落としても半正定値にならず、
  「一つの豊富な類だけで正値性が出る」という曲線の場合の構造は写らない。

  RH の本体についての主張は一切していない。
-/
import Mathlib

namespace HodgeIndex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- 実ベクトル空間上の対称双線形形式（必要な性質だけを持つ構造）。 -/
structure SymBil (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  symm : ∀ x y, B x y = B y x
  add_left : ∀ x y z, B (x + y) z = B x z + B y z
  smul_left : ∀ (c : ℝ) (x y : V), B (c • x) y = c * B x y

namespace SymBil

variable (S : SymBil V)

lemma add_right (x y z : V) : S.B x (y + z) = S.B x y + S.B x z := by
  rw [S.symm x (y + z), S.add_left, S.symm y x, S.symm z x]

lemma smul_right (c : ℝ) (x y : V) : S.B x (c • y) = c * S.B x y := by
  rw [S.symm x (c • y), S.smul_left, S.symm y x]

lemma neg_left (x y : V) : S.B (-x) y = - S.B x y := by
  have h : (-x : V) = (-1 : ℝ) • x := by
    simp
  rw [h, S.smul_left]; ring

lemma sub_left (x y z : V) : S.B (x - y) z = S.B x z - S.B y z := by
  have h : x - y = x + (-y) := sub_eq_add_neg x y
  rw [h, S.add_left, S.neg_left]; ring

/-- 二次形式。 -/
def Q (x : V) : ℝ := S.B x x

lemma Q_add (x y : V) : S.Q (x + y) = S.Q x + 2 * S.B x y + S.Q y := by
  unfold Q
  rw [S.add_left, S.add_right, S.add_right, S.symm y x]
  ring

lemma Q_smul (c : ℝ) (x : V) : S.Q (c • x) = c ^ 2 * S.Q x := by
  unfold Q
  rw [S.smul_left, S.smul_right]
  ring

lemma B_smul_left_right (a b : ℝ) (x y : V) :
    S.B (a • x) (b • y) = a * b * S.B x y := by
  rw [S.smul_left, S.smul_right]; ring

lemma Q_sub (x y : V) : S.Q (x - y) = S.Q x - 2 * S.B x y + S.Q y := by
  have h : x - y = x + (-1 : ℝ) • y := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, S.Q_add, S.smul_right, S.Q_smul]
  ring

end SymBil

open SymBil

/-- **逆 Cauchy–Schwarz（Hodge 指数定理の線形代数の核）**。
`h` は「豊富な類」（`Q h > 0`）、その直交補空間で形式が `≤ 0` なら、
すべての `x` について `Q x * Q h ≤ (B x h)^2`。 -/
theorem reverse_cauchy_schwarz (S : SymBil V) (h : V) (hh : 0 < S.Q h)
    (hneg : ∀ y : V, S.B y h = 0 → S.Q y ≤ 0) (x : V) :
    S.Q x * S.Q h ≤ (S.B x h) ^ 2 := by
  set t : ℝ := S.B x h / S.Q h with ht
  have hQh : S.Q h ≠ 0 := ne_of_gt hh
  have hy : S.B (x - t • h) h = 0 := by
    rw [S.sub_left, S.smul_left, ht]
    have : S.B h h = S.Q h := rfl
    rw [this]
    field_simp
    ring
  have h1 : S.Q (x - t • h) ≤ 0 := hneg _ hy
  have h2 : S.Q x = S.Q (x - t • h) + t ^ 2 * S.Q h := by
    have key : S.Q ((x - t • h) + t • h)
        = S.Q (x - t • h) + 2 * S.B (x - t • h) (t • h) + S.Q (t • h) := S.Q_add _ _
    have hx : (x - t • h) + t • h = x := by abel
    rw [hx] at key
    rw [key, S.smul_right, hy, S.Q_smul]
    ring
  have h3 : S.Q x ≤ t ^ 2 * S.Q h := by linarith
  have h4 : t ^ 2 * S.Q h * S.Q h = (S.B x h) ^ 2 := by
    rw [ht]; field_simp
  nlinarith [hh, h3]

/-- **Castelnuovo–Severi の不等式の線形代数の核**。
双曲平面 `f₁, f₂`（`Q f₁ = Q f₂ = 0`, `B f₁ f₂ = 1`）の直交補空間で形式が `≤ 0` なら
`Q D ≤ 2 (B D f₁)(B D f₂)`。 -/
theorem castelnuovo_severi (S : SymBil V) (f₁ f₂ : V)
    (h1 : S.Q f₁ = 0) (h2 : S.Q f₂ = 0) (h12 : S.B f₁ f₂ = 1)
    (hneg : ∀ y : V, S.B y f₁ = 0 → S.B y f₂ = 0 → S.Q y ≤ 0) (D : V) :
    S.Q D ≤ 2 * S.B D f₁ * S.B D f₂ := by
  set d₁ : ℝ := S.B D f₁ with hd1
  set d₂ : ℝ := S.B D f₂ with hd2
  set E : V := d₂ • f₁ + d₁ • f₂ with hE
  set D0 : V := D - E with hD0
  have hBf11 : S.B f₁ f₁ = 0 := h1
  have hBf22 : S.B f₂ f₂ = 0 := h2
  have hBf21 : S.B f₂ f₁ = 1 := by rw [S.symm]; exact h12
  have e1 : S.B D0 f₁ = 0 := by
    rw [hD0, S.sub_left, hE, S.add_left, S.smul_left, S.smul_left, hBf11, hBf21]
    rw [← hd1]; ring
  have e2 : S.B D0 f₂ = 0 := by
    rw [hD0, S.sub_left, hE, S.add_left, S.smul_left, S.smul_left, hBf22, h12]
    rw [← hd2]; ring
  have hQE : S.Q E = 2 * d₁ * d₂ := by
    rw [hE, S.Q_add, S.Q_smul, S.Q_smul, h1, h2, S.B_smul_left_right, h12]
    ring
  have hBD0E : S.B D0 E = 0 := by
    rw [hE, S.add_right, S.smul_right, S.smul_right, e1, e2]
    ring
  have hsplit : S.Q D = S.Q D0 + 2 * S.B D0 E + S.Q E := by
    have : D = D0 + E := by rw [hD0]; abel
    rw [this, S.Q_add]
  have hle : S.Q D0 ≤ 0 := hneg _ e1 e2
  rw [hsplit, hBD0E, hQE]
  linarith

/-- **負の方向が二つあれば、どの超平面でも半正定値にならない**。
`u, v` が互いに直交し `Q u < 0`, `Q v < 0` なら、任意の線形汎関数 `φ` の核の中に
`Q w < 0` となる `w` がある。したがって「一つの類を落として正値にする」ことはできない。 -/
theorem no_ample_of_two_negatives (S : SymBil V) (u v : V)
    (huv : S.B u v = 0) (hu : S.Q u < 0) (hv : S.Q v < 0)
    (φ : V →ₗ[ℝ] ℝ) : ∃ w : V, φ w = 0 ∧ S.Q w < 0 := by
  by_cases hu0 : φ u = 0
  · exact ⟨u, hu0, hu⟩
  · refine ⟨(φ v) • u - (φ u) • v, ?_, ?_⟩
    · simp [map_sub, map_smul]
      ring
    · have hQ : S.Q ((φ v) • u - (φ u) • v)
          = (φ v) ^ 2 * S.Q u + (φ u) ^ 2 * S.Q v := by
        rw [S.Q_sub, S.Q_smul, S.Q_smul, S.B_smul_left_right, huv]
        ring
      rw [hQ]
      have h1 : (φ v) ^ 2 * S.Q u ≤ 0 := by
        have : (0:ℝ) ≤ (φ v) ^ 2 := sq_nonneg _
        nlinarith
      have h2 : (φ u) ^ 2 * S.Q v < 0 := by
        have : (0:ℝ) < (φ u) ^ 2 := by positivity
        nlinarith
      linarith

/-- 空虚でないことの確認：双曲平面（`f₁ = (1,0)`, `f₂ = (0,1)`）。 -/
def hyp : SymBil (ℝ × ℝ) where
  B x y := x.1 * y.2 + x.2 * y.1
  symm := by intro x y; ring
  add_left := by intro x y z; simp; ring
  smul_left := by intro c x y; simp; ring

example : hyp.Q ((1 : ℝ), (0 : ℝ)) = 0 := by
  simp [SymBil.Q, hyp]

example : hyp.B ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = 1 := by
  simp [hyp]

example (D : ℝ × ℝ) : hyp.Q D ≤ 2 * hyp.B D ((1:ℝ),(0:ℝ)) * hyp.B D ((0:ℝ),(1:ℝ)) := by
  simp [SymBil.Q, hyp]
  linarith

#print axioms reverse_cauchy_schwarz
#print axioms castelnuovo_severi
#print axioms no_ample_of_two_negatives
