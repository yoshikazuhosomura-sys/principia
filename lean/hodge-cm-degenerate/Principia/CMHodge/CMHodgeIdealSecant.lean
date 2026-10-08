/-
  CM 型の退化した例外類 — イデアル層の族に対する障害の論理の芯（有限の代数だけ）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ = pr₁^*θ₀+pr₂^*θ₀+pr₃^*θ₀`（積の主偏極）。
  対称行列 `S` に有理因子類 `D_S` が対応し（`D_{vvᵀ} = φ_v^*θ₀`）、交点数は
  `∫ D_{v₁}⋯D_{v₆} = 2 Σ_{T} det[v_T]² det[v_{T'}]²`（`{T,T'}` は `{1..6}` の補的な三つ組の非順序対・10 個）。
  `W := Θ ∧_{F₀} Θ`、`β := Θ·exp(-(q/2)W)`、`q = 19`。
  `D ∈ |gΘ|`・`A = D_S`・`Z ⊂ D` として `Ψ := (1-e^{-gΘ}) - g·β·e^{-A}` と置くと、
  `Z` が平行移動したアーベル部分多様体の和（Todd 補正が消える場合）なら
  「`ch(e_*I_{Z,D}(A))` が次数 8 まで `g·β` と一致する」は「`Ψ₄, Ψ₆, Ψ₈` が有効類」と同値で、
  `∫Ψ_{2c}Θ^{6-c} ≥ 0` が必要になる。その三つは `S` の固有値 `s₁,s₂,s₃` と `g` で閉じた形になる：
     J4 = g(240e₁ - 360g),  J6 = g(120g² - 24(e₁²+2e₂) + 1368),  J8 = g(-30g³ + 12(e₁e₂+e₃) - 456e₁)
  （`∫Θ⁵D_S = 240e₁`・`∫Θ⁴D_S² = 48(e₁²+2e₂)`・`∫Θ³D_S³ = 72(e₁e₂+e₃)`・`∫Θ³W D_S = 48e₁`・`∫Θ⁴W = 144`）。

  この頁で Lean にするのは次の五つで、いずれも**有限の代数の等式・不等式・尽くし**である。
  幾何・層・変形理論・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 対称式の恒等式：`Σ_{i≠j} sᵢ²sⱼ = e₁e₂ - 3e₃`、および `8(36e₃+9(e₁e₂-3e₃)) = 72(e₁e₂+e₃)`。
  (2) マクローリン型の不等式：任意の実数で `3e₂ ≤ e₁²`、`sᵢ ≥ 0` なら `27e₃ ≤ e₁³`。
  (3) 直交枠での尽くし：`(2,2,2)` を作る指数の組はちょうど一つ（`Ψ₄` の固有値判定の芯）。
  (4) 補的三つ組の非順序対はちょうど 10 個、そのうち三つのブロックを各一回ずつ拾うものは 4 個
      （`∫Θ₁²Θ₂²Θ₃² = 2·4 = 8` の芯）。
  (5) **主結果**：`sᵢ ≥ 0`（= `S` 半正定値）・`g > 0`・`J4 ≥ 0`・`J6 ≥ 0` ならば `J8 < 0`。
      ゆえに半正定値な `S` は三条件を同時に満たせない。
-/
import Mathlib

namespace CMHodgeIdealSecant

/-! ### (1) 対称式の恒等式 -/

theorem sym3_mixed (s₁ s₂ s₃ : ℚ) :
    s₁^2*s₂ + s₁^2*s₃ + s₂^2*s₁ + s₂^2*s₃ + s₃^2*s₁ + s₃^2*s₂
      = (s₁+s₂+s₃)*(s₁*s₂+s₁*s₃+s₂*s₃) - 3*(s₁*s₂*s₃) := by ring

theorem cubic_moment_form (s₁ s₂ s₃ : ℚ) :
    8*(36*(s₁*s₂*s₃) + 9*((s₁+s₂+s₃)*(s₁*s₂+s₁*s₃+s₂*s₃) - 3*(s₁*s₂*s₃)))
      = 72*((s₁+s₂+s₃)*(s₁*s₂+s₁*s₃+s₂*s₃) + s₁*s₂*s₃) := by ring

/-! ### (2) マクローリン型の不等式 -/

theorem e2_le (s₁ s₂ s₃ : ℚ) : 3*(s₁*s₂+s₁*s₃+s₂*s₃) ≤ (s₁+s₂+s₃)^2 := by
  nlinarith [sq_nonneg (s₁-s₂), sq_nonneg (s₁-s₃), sq_nonneg (s₂-s₃)]

theorem e3_le (s₁ s₂ s₃ : ℚ) (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃) :
    27*(s₁*s₂*s₃) ≤ (s₁+s₂+s₃)^3 := by
  nlinarith [mul_nonneg h₁ (sq_nonneg (s₂-s₃)), mul_nonneg h₂ (sq_nonneg (s₃-s₁)),
    mul_nonneg h₃ (sq_nonneg (s₁-s₂)),
    mul_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) (sq_nonneg (s₁-s₂)),
    mul_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) (sq_nonneg (s₂-s₃)),
    mul_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) (sq_nonneg (s₃-s₁))]

/-! ### (3) 直交枠での尽くし -/

/-- `e k i` は第 `k` 標準基底ベクトルの第 `i` 成分。`Θ` の項 `i` と `D_T` の項 `j` を取って
`y²z²` と掛けたとき、最高次 `(2,2,2)` になるのは `i = j = 0` だけ。 -/
def e (k i : Fin 3) : ℕ := if i = k then 1 else 0

theorem frame_exhaust :
    ∀ i j : Fin 3, (∀ k : Fin 3, e i k + e j k + (if k = 0 then 0 else 2) = 2) ↔ (i = 0 ∧ j = 0) := by
  decide

/-! ### (4) 補的三つ組の数え上げ -/

/-- `idx` は `Fin 6` を三つのブロック `{0,1}, {2,3}, {4,5}` に送る。 -/
def idx : Fin 6 → Fin 3
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2

theorem ten_pairs :
    (Finset.univ.filter (fun T : Finset (Fin 6) => T.card = 3 ∧ (0 : Fin 6) ∈ T)).card = 10 := by
  decide

theorem four_transversals :
    (Finset.univ.filter
      (fun T : Finset (Fin 6) => T.card = 3 ∧ (0 : Fin 6) ∈ T ∧ T.image idx = Finset.univ)).card
      = 4 := by
  decide

/-! ### (5) 主結果：半正定値な `S` は三条件を同時に満たせない -/

/-- `p² ≤ 5g²+57` のもとで `(40/3)pg² + 152p < 30g³ + 456p`。 -/
theorem key_bound (p g : ℚ) (hp : 0 < p) (hg : 0 < g) (h : p^2 ≤ 5*g^2 + 57) :
    (40/3)*p*g^2 + 152*p < 30*g^3 + 456*p := by
  rcases le_or_gt (g^2) (114/5) with hu | hu
  · nlinarith [mul_pos hg (mul_pos hg hg), mul_pos hp hg]
  · have hc : 0 < (40/3)*g^2 - 304 := by nlinarith
    have hsq : (p*((40/3)*g^2 - 304))^2 < (30*g^3)^2 := by
      have h1 : (114/5 : ℚ)^2 < (g^2)^2 := by nlinarith
      have h2 : p^2 * ((40/3)*g^2 - 304)^2 ≤ (5*g^2+57) * ((40/3)*g^2 - 304)^2 := by
        exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
      nlinarith [h2, h1, hu, mul_pos hg hg]
    have hpos : 0 < p*((40/3)*g^2 - 304) := mul_pos hp hc
    have h30 : 0 < 30*g^3 := by positivity
    nlinarith [hsq, hpos, h30]

/-- `12(pe₂+e₃) ≤ (40/3)pg² + 152p`。 -/
theorem moment_bound (p e₂ e₃ g : ℚ) (hp : 0 < p) (hg : 0 < g)
    (h2 : 3*e₂ ≤ p^2) (h2n : 0 ≤ e₂) (h3 : 27*e₃ ≤ p^3) (hM : p^2 + 2*e₂ ≤ 5*g^2 + 57) :
    12*(p*e₂ + e₃) ≤ (40/3)*p*g^2 + 152*p := by
  rcases le_or_gt (5*p^2) (3*(5*g^2+57)) with hcase | hcase
  · nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt hp), hp, hcase,
      mul_le_mul_of_nonneg_left hcase (le_of_lt hp)]
  · nlinarith [mul_le_mul_of_nonneg_left hM (le_of_lt hp), hp, hcase,
      mul_le_mul_of_nonneg_left (le_of_lt hcase) (le_of_lt hp)]

/-- **主結果**：`S` が半正定値（固有値 `sᵢ ≥ 0`）なら `J4 ≥ 0` と `J6 ≥ 0` から `J8 < 0` が従う。 -/
theorem psd_obstruction (s₁ s₂ s₃ g : ℚ)
    (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) (h₃ : 0 ≤ s₃) (hg : 0 < g)
    (hJ4 : 0 ≤ 240*(s₁+s₂+s₃) - 360*g)
    (hJ6 : 0 ≤ 120*g^2 - 24*((s₁+s₂+s₃)^2 + 2*(s₁*s₂+s₁*s₃+s₂*s₃)) + 1368) :
    -30*g^3 + 12*((s₁+s₂+s₃)*(s₁*s₂+s₁*s₃+s₂*s₃) + s₁*s₂*s₃) - 456*(s₁+s₂+s₃) < 0 := by
  set p := s₁+s₂+s₃ with hpdef
  set e₂ := s₁*s₂+s₁*s₃+s₂*s₃ with he2def
  set e₃ := s₁*s₂*s₃ with he3def
  have hp : 0 < p := by nlinarith
  have h2n : 0 ≤ e₂ := by
    have := mul_nonneg h₁ h₂; have := mul_nonneg h₁ h₃; have := mul_nonneg h₂ h₃
    simp only [he2def]; linarith
  have h2 : 3*e₂ ≤ p^2 := by simpa [hpdef, he2def] using e2_le s₁ s₂ s₃
  have h3 : 27*e₃ ≤ p^3 := by simpa [hpdef, he3def] using e3_le s₁ s₂ s₃ h₁ h₂ h₃
  have hM : p^2 + 2*e₂ ≤ 5*g^2 + 57 := by linarith
  have hb := moment_bound p e₂ e₃ g hp hg h2 h2n h3 hM
  have hk := key_bound p g hp hg (by linarith)
  linarith

/-- 等方な場合（`S = cI`、すなわち `A = cΘ`）の系。 -/
theorem isotropic_obstruction (c g : ℚ) (hc : 0 ≤ c) (hg : 0 < g)
    (hJ4 : 0 ≤ 720*c - 360*g) (hJ6 : 0 ≤ 120*g^2 - 360*c^2 + 1368) :
    -30*g^3 + 120*c^3 - 1368*c < 0 := by
  have := psd_obstruction c c c g hc hc hc hg (by linarith) (by nlinarith)
  nlinarith [this]

end CMHodgeIdealSecant

#print axioms CMHodgeIdealSecant.sym3_mixed
#print axioms CMHodgeIdealSecant.cubic_moment_form
#print axioms CMHodgeIdealSecant.e2_le
#print axioms CMHodgeIdealSecant.e3_le
#print axioms CMHodgeIdealSecant.frame_exhaust
#print axioms CMHodgeIdealSecant.ten_pairs
#print axioms CMHodgeIdealSecant.four_transversals
#print axioms CMHodgeIdealSecant.key_bound
#print axioms CMHodgeIdealSecant.moment_bound
#print axioms CMHodgeIdealSecant.psd_obstruction
#print axioms CMHodgeIdealSecant.isotropic_obstruction
