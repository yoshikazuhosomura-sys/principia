/-
  紙の上で閉じた「m₄ ≥ m₇」の証明を機械検査する。
  これで **「Syracuse 測度の最小は mod 9 では類 7 でしか取られない」** が完全な定理になる。
  類 7 = 2 × 類 8 であり、類 8 は最大点 −1 の類だから、
  **「最小は最大の類の倍の類にある」**（−2 ≡ 7 (mod 9) が最小の類）。

  記号（すべて実数の抽象化。測度そのものの形式化はしていない）:
    u_j : Z/3^j の単位上の非負関数、d_j := min、m_r := min_{z ≡ r (mod 9)} u_j(z)
    (L-A) u_j(2y) = 2u_j(y) − 3·1{y ≡ 2 (mod 3)}·u_{j−1}((2y−1)/3)
    (L-B) min_{z ≡ 2 (mod 3)} u_{j−1} = 2·d_{j−1}

  証明の骨:
    z ≡ 4 (mod 9) に L-A を二回当てる。1 段目（z ≡ 1 mod 3）は引き算なし、
    2 段目（2z ≡ 8 mod 9 ⟹ ≡ 2 mod 3）は引き算あり:
      u_j(4z) = 4u_j(z) − 3u_{j−1}(s),  s := (4z−1)/3.
    s ≡ 2 (mod 3) なので s は単位で、L-B から u_{j−1}(s) ≥ 2d_{j−1}。
    u_j(4z) ≥ 0 と合わせて **点ごとに u_j(z) ≥ (3/2)d_{j−1}**。
    d_{j−1} ≥ d_j と d_j = min(m₄, m₇) から d_j = m₇、すなわち m₇ ≤ m₄。
-/
import Mathlib.Tactic

namespace Collatz.SubtractionSteps

/-! ### 1. 算術核（mod 9 の帳尻） -/

/-- 類 4 の点を 4 倍すると類 7 に入る（連鎖 4 → 8 → 7 の二段）。 -/
theorem four_times_class_four (z : ℤ) (h : z % 9 = 4) : (4 * z) % 9 = 7 := by omega

/-- 1 段目は引き算が起きない（z ≡ 4 (mod 9) ⟹ z ≡ 1 (mod 3)）。 -/
theorem first_step_no_subtraction (z : ℤ) (h : z % 9 = 4) : z % 3 = 1 := by omega

/-- 2 段目は引き算が起きる（2z ≡ 8 (mod 9) ⟹ 2z ≡ 2 (mod 3)）。 -/
theorem second_step_subtraction (z : ℤ) (h : z % 9 = 4) : (2 * z) % 3 = 2 := by omega

/-- **本命の算術核**：引き算に現れる子 s = (4z−1)/3 は 3 の倍数ではなく、
    しかも必ず類 2 (mod 3) に入る。⟹ s は単位であり、L-B の下界 2d が使える。 -/
theorem subtracted_child_is_unit (z : ℤ) (h : z % 9 = 4) :
    ∃ s : ℤ, 4 * z - 1 = 3 * s ∧ s % 3 = 2 := by
  refine ⟨(4 * z - 1) / 3, ?_, ?_⟩ <;> omega

/-- 引き算が生きるのは類 2 と類 8 (mod 9) の二箇所だけである。
    （y ≡ 5 (mod 9) では子 (2y−1)/3 が 3 の倍数になり、引き算は自動的に消える。） -/
theorem subtraction_only_at_two_and_eight (y : ℤ) (h : y % 3 = 2)
    (h9 : y % 9 ≠ 2 ∧ y % 9 ≠ 8) : (3 : ℤ) ∣ (2 * y - 1) / 3 := by
  obtain ⟨h2, h8⟩ := h9
  refine ⟨(2 * y - 1) / 9, ?_⟩
  omega

/-! ### 2. 点ごとの下界（紙の側の (N1)〜(N4)） -/

/-- **(N4) 点ごとの下界**：`u4z = 4·uz − 3·us`（二段の倍化恒等式）、`u4z ≥ 0`、
    `us ≥ 2·dprev`（L-B）から、`uz ≥ (3/2)·dprev`。 -/
theorem pointwise_class_four_lower (uz u4z us dprev : ℝ)
    (hid : u4z = 4 * uz - 3 * us) (hnn : 0 ≤ u4z) (hus : 2 * dprev ≤ us) :
    (3 / 2) * dprev ≤ uz := by linarith

/-- 系：類 4 の最小 `m4` も同じ下界を満たす。 -/
theorem min_class_four_lower (m4 u4 us dprev : ℝ)
    (hid : u4 = 4 * m4 - 3 * us) (hnn : 0 ≤ u4) (hus : 2 * dprev ≤ us) :
    (3 / 2) * dprev ≤ m4 :=
  pointwise_class_four_lower m4 u4 us dprev hid hnn hus

/-- **精密版**：`m7 ≤ 4·m4 − 3·us ≤ 4·m4 − 6·dprev` から `m4 ≥ (6·dprev + m7)/4`。 -/
theorem min_class_four_precise (m4 m7 u4 us dprev : ℝ)
    (hid : u4 = 4 * m4 - 3 * us) (hm7 : m7 ≤ u4) (hus : 2 * dprev ≤ us) :
    (6 * dprev + m7) / 4 ≤ m4 := by linarith

/-! ### 3. 最小の類は 7 である（紙の側の (N5)(N6)） -/

/-- **本命**：`d = min(m4, m7)`、`d ≤ dprev`（d の単調性・紙の側）、`d > 0`、
    そして類 4 の下界 `(3/2)·dprev ≤ m4` から、**`d = m7` かつ `m7 ≤ m4`**。 -/
theorem argmin_is_class_seven (m4 m7 d dprev : ℝ)
    (hd4 : d ≤ m4) (hd7 : d ≤ m7) (hdd : d = m4 ∨ d = m7)
    (hanti : d ≤ dprev) (hpos : 0 < d) (hlb : (3 / 2) * dprev ≤ m4) :
    d = m7 ∧ m7 ≤ m4 := by
  have hlt : d < m4 := by linarith
  have h7 : d = m7 := by
    rcases hdd with h | h
    · exact absurd h (by linarith)
    · exact h
  exact ⟨h7, by linarith⟩

/-- **m₄ ≥ (3/2)·m₇**（実測は 2.37〜5.50。下界は 1.5）。 -/
theorem m4_ge_three_halves_m7 (m4 m7 d dprev : ℝ)
    (hd7 : d = m7) (hanti : d ≤ dprev) (hlb : (3 / 2) * dprev ≤ m4) :
    (3 / 2) * m7 ≤ m4 := by
  rw [← hd7]; linarith

/-! ### 4. 六類の連鎖と合わせた完全形 -/

/-- **mod 9 の完全な位置定理**：連鎖 `7→5→1→2`（引き算なし）と `4→8`（引き算なし）で
    `m5 = 2m7`, `m1 = 4m7`, `m2 = 8m7`, `m8 = 2m4` が成り立ち、さらに `m7 ≤ m4` なら、
    **六類の最小はすべて `m7` 以上**、すなわち最小は類 7 で取られる。 -/
theorem min_over_six_classes (m1 m2 m4 m5 m7 m8 : ℝ)
    (h5 : m5 = 2 * m7) (h1 : m1 = 4 * m7) (h2 : m2 = 8 * m7) (h8 : m8 = 2 * m4)
    (hpos : 0 < m7) (hle : m7 ≤ m4) :
    m7 ≤ m1 ∧ m7 ≤ m2 ∧ m7 ≤ m4 ∧ m7 ≤ m5 ∧ m7 ≤ m8 :=
  ⟨by linarith, by linarith, hle, by linarith, by linarith⟩

/-- 最小の類 7 は最大点の類 8（`−1 ≡ 8 (mod 9)`）のちょうど倍である：`2·8 ≡ 7 (mod 9)`。
    かつ `−2 ≡ 7 (mod 9)`——凍結アドレス `z_j ≡ −2 (mod 3⁴)` はこの類の中にいる。 -/
theorem seven_is_double_of_max_class : (2 * 8) % 9 = 7 ∧ ((-2 : ℤ) % 9) = 7 := by
  constructor
  · decide
  · decide

/-- 走行の全体像（mod 9 の 2 倍写像の 6-巡）。 -/
theorem doubling_cycle_mod_nine :
    (2 * 7) % 9 = 5 ∧ (2 * 5) % 9 = 1 ∧ (2 * 1) % 9 = 2 ∧
    (2 * 2) % 9 = 4 ∧ (2 * 4) % 9 = 8 ∧ (2 * 8) % 9 = 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### 5. Finset 版（最小そのものを扱う形） -/

/-- 写像 `σ` が重みを 4 倍から引き算した形にするとき、像の最小は
    `4·(もとの最小) − 3·(引かれる項の下界)` 以下である。
    ⟹ `m7 ≤ 4·m4 − 6·dprev`（紙の側の不等式の Finset 版）。 -/
theorem inf_image_of_sub {β : Type*} [DecidableEq β] (s : Finset β) (hs : s.Nonempty)
    (σ : β → β) (wt : β → ℝ) (sub : β → ℝ) (dprev : ℝ)
    (hσ : ∀ b ∈ s, wt (σ b) = 4 * wt b - 3 * sub b)
    (hsub : ∀ b ∈ s, 2 * dprev ≤ sub b) :
    (s.image σ).inf' (hs.image σ) wt ≤ 4 * s.inf' hs wt - 6 * dprev := by
  obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' hs wt
  have hmem : σ b ∈ s.image σ := Finset.mem_image_of_mem σ hb
  have h1 : (s.image σ).inf' (hs.image σ) wt ≤ wt (σ b) := Finset.inf'_le _ hmem
  rw [hσ b hb] at h1
  have h2 : 2 * dprev ≤ sub b := hsub b hb
  rw [hbeq]
  linarith

/-- 系（Finset 版）：像の最小が非負なら、もとの最小は `(3/2)·dprev` 以上。 -/
theorem inf_ge_of_image_nonneg {β : Type*} [DecidableEq β] (s : Finset β) (hs : s.Nonempty)
    (σ : β → β) (wt : β → ℝ) (sub : β → ℝ) (dprev : ℝ)
    (hσ : ∀ b ∈ s, wt (σ b) = 4 * wt b - 3 * sub b)
    (hsub : ∀ b ∈ s, 2 * dprev ≤ sub b)
    (hnn : 0 ≤ (s.image σ).inf' (hs.image σ) wt) :
    (3 / 2) * dprev ≤ s.inf' hs wt := by
  have := inf_image_of_sub s hs σ wt sub dprev hσ hsub
  linarith

end Collatz.SubtractionSteps

#print axioms Collatz.SubtractionSteps.four_times_class_four
#print axioms Collatz.SubtractionSteps.subtracted_child_is_unit
#print axioms Collatz.SubtractionSteps.subtraction_only_at_two_and_eight
#print axioms Collatz.SubtractionSteps.pointwise_class_four_lower
#print axioms Collatz.SubtractionSteps.min_class_four_lower
#print axioms Collatz.SubtractionSteps.min_class_four_precise
#print axioms Collatz.SubtractionSteps.argmin_is_class_seven
#print axioms Collatz.SubtractionSteps.m4_ge_three_halves_m7
#print axioms Collatz.SubtractionSteps.min_over_six_classes
#print axioms Collatz.SubtractionSteps.seven_is_double_of_max_class
#print axioms Collatz.SubtractionSteps.doubling_cycle_mod_nine
#print axioms Collatz.SubtractionSteps.inf_image_of_sub
#print axioms Collatz.SubtractionSteps.inf_ge_of_image_nonneg
