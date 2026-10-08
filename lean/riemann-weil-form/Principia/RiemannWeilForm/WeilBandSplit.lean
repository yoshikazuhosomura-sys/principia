/-
  切り落とした Weil 形式を「帯」で二つに割る議論に、何が要るかを閉じる。

  実測：W_L を低帯（r < r₀ = 6.2898…、次元 k ≈ 2.002 L）に圧縮すると
  最小固有値は正だが e^{4.9 − 17.4 L} しかない（L = 3.5 で 6.4×10⁻²⁶）。
  一方、低帯と高帯を結ぶ交差ブロックのノルムは 0.1〜0.8 で、L とともに増える。
  この二つの数字が両立するために何が要るかを、抽象的な対称双線形形式の言明として取り出す：

  * schur_rank_one : Q u ≠ 0 のとき Q (w − (B u w / Q u) • u) = Q w − (B u w)² / Q u
      （階数 1 の Schur 補元。恒等式）
  * cross_bound_of_nonneg : 形式が半正定値なら (B u w)² ≤ Q u · Q w
  * complement_lower_bound : ゆえに Q w ≥ (B u w)² / Q u
      ——低帯の値 Q u が小さいほど、高帯に要求される値が大きくなる
  * two_block_nonneg : 逆に (B u w)² ≤ Q u · Q w が成り立てば span{u} ⊕ w 上で Q ≥ 0
      （帯で割る議論の「必要かつ十分な形」）
  * band_split_counterexample : Q u = ε > 0 と Q w = 0 ≥ 0 だけでは足りない。
      どの ε > 0 でも、値が −1/ε になるベクトルを持つ形式が在る

  含意（数学の側）：低帯で Q u ≈ 1.7×10⁻²⁰（L = 3）・交差 B u w ≈ 0.38 なら
  complement_lower_bound は Q w ≥ 8.6×10¹⁸ を要求する。
  「低帯の有限次元の不等式 ＋ 高帯の半正定値性」という分割では W_L ⪰ 0 は出ない。

  RH の本体の証明にも反証にも使えない。本ファイルは有限次元の線形代数だけである。
-/
import Mathlib

namespace BandSplit

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
  have h : (-x : V) = (-1 : ℝ) • x := by simp
  rw [h, S.smul_left]; ring

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

lemma Q_sub (x y : V) : S.Q (x - y) = S.Q x - 2 * S.B x y + S.Q y := by
  have h : x - y = x + (-1 : ℝ) • y := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, S.Q_add, S.smul_right, S.Q_smul]
  ring

end SymBil

open SymBil

/-- **階数 1 の Schur 補元（恒等式）**。低帯の一方向 `u` を掃き出したあとに残る値。 -/
theorem schur_rank_one (S : SymBil V) (u w : V) (hu : S.Q u ≠ 0) :
    S.Q (w - (S.B u w / S.Q u) • u) = S.Q w - (S.B u w) ^ 2 / S.Q u := by
  rw [S.Q_sub, S.smul_right, S.Q_smul, S.symm w u]
  field_simp
  ring

/-- **半正定値なら交差ブロックは二つの対角ブロックで抑えられる**（psd の Cauchy–Schwarz）。 -/
theorem cross_bound_of_nonneg (S : SymBil V) (hpos : ∀ x, 0 ≤ S.Q x) (u w : V)
    (hu : 0 < S.Q u) : (S.B u w) ^ 2 ≤ S.Q u * S.Q w := by
  have h := hpos (w - (S.B u w / S.Q u) • u)
  rw [schur_rank_one S u w (ne_of_gt hu)] at h
  rw [sub_nonneg, div_le_iff₀ hu] at h
  calc (S.B u w) ^ 2 ≤ S.Q w * S.Q u := h
    _ = S.Q u * S.Q w := mul_comm _ _

/-- **低帯の余裕が小さいほど高帯に要求される値が大きい**。
`Q u` が低帯の圧縮の最小固有値、`B u w` が交差ブロックにあたる。 -/
theorem complement_lower_bound (S : SymBil V) (hpos : ∀ x, 0 ≤ S.Q x) (u w : V)
    (hu : 0 < S.Q u) : (S.B u w) ^ 2 / S.Q u ≤ S.Q w := by
  rw [div_le_iff₀ hu]
  calc (S.B u w) ^ 2 ≤ S.Q u * S.Q w := cross_bound_of_nonneg S hpos u w hu
    _ = S.Q w * S.Q u := mul_comm _ _

/-- **逆向き（帯で割る議論の十分条件）**：交差ブロックが対角ブロックの積で抑えられていれば、
`u` と `w` の張る面の上で形式は半正定値である。 -/
theorem two_block_nonneg (S : SymBil V) (u w : V) (hu : 0 < S.Q u)
    (h : (S.B u w) ^ 2 ≤ S.Q u * S.Q w) (t : ℝ) : 0 ≤ S.Q (t • u + w) := by
  have e : S.Q (t • u + w) = t ^ 2 * S.Q u + 2 * t * S.B u w + S.Q w := by
    rw [S.Q_add, S.Q_smul, S.smul_left]; ring
  rw [e]
  nlinarith [sq_nonneg (t * S.Q u + S.B u w), hu, h,
    mul_pos hu (mul_pos hu hu)]

/-- 反例に使う形式：`B x y = ε x₁y₁ + (x₁y₂ + x₂y₁)`。 -/
def ex (ε : ℝ) : SymBil (ℝ × ℝ) where
  B := fun x y => ε * (x.1 * y.1) + (x.1 * y.2 + x.2 * y.1)
  symm := by intro x y; ring
  add_left := by intro x y z; simp only [Prod.fst_add, Prod.snd_add]; ring
  smul_left := by
    intro c x y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- **対角ブロックだけでは足りない**：`Q u = ε > 0` と `Q w = 0 ≥ 0` が成り立っていても、
`u, w` の張る面の上に値 `−1/ε` のベクトルが在る。
低帯の余裕 `ε` が小さいほど、破れの深さ `1/ε` は大きくなる。 -/
theorem band_split_counterexample (ε : ℝ) (hε : 0 < ε) :
    (ex ε).Q ((1 : ℝ), (0 : ℝ)) = ε ∧ (ex ε).Q ((0 : ℝ), (1 : ℝ)) = 0 ∧
      (ex ε).Q ((-(1 / ε) : ℝ), (1 : ℝ)) = -(1 / ε) := by
  refine ⟨by simp [SymBil.Q, ex], by simp [SymBil.Q, ex], ?_⟩
  simp only [SymBil.Q, ex]
  field_simp
  ring

end BandSplit

#print axioms BandSplit.schur_rank_one
#print axioms BandSplit.cross_bound_of_nonneg
#print axioms BandSplit.complement_lower_bound
#print axioms BandSplit.two_block_nonneg
#print axioms BandSplit.band_split_counterexample
