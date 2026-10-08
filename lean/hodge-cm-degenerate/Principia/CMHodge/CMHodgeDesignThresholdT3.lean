import Mathlib

/-!
# The edge `t₃` of the real-positivity certificates (`O`-analogue, `q = 19`, §12-type full splitting)

Coefficients of an `S₃`-symmetric `q` of multidegree `≤ (2,2,2)` over the ten orbit sums
`m₀₀₀, m₁₀₀, m₁₁₀, m₁₁₁, m₂₀₀, m₂₁₀, m₂₁₁, m₂₂₀, m₂₂₁, m₂₂₂` are `c000, …, c222`.
`q ∈ T_t` means the four rational conditions `row1 … row4` (values at `(z,z,z)`, `(z,z,z̄)`,
`z = t + √−19`, real part and `√19`-part).  `dP2` is `Δ_{P₂} q` for the piece
`P₂ = (−2−θ+θ², 23+3θ−3θ²)` (orbit-sum second differences `0,0,182,1163,68,4774,41558,28752,464356,1563071`).

Main theorem `dP2_nonneg_of_necessary` (hypotheses next to the name):
for real `t` with `44/5 ≤ t ≤ 14` and `f t ≤ 0` (i.e. `t ≥ t₃ = 8.88860881172…`, the real root of the quartic `f`
in that range), every `q ∈ T_t` with
* `c000 ≥ 0` (the value `q(0)`),
* `c200 ≤ 0`, `c220 ≤ 0`,
* `c210 + c211 z + c221 z² ≤ 0` for all `z > 0`
has `Δ_{P₂} q ≥ 0`.
The four sign conditions are necessary for `−Δ q ≥ 0` on the real region "some coordinate `≥ R`" and for the
Farkas use of `q` (argument on paper, not in this file); so no certificate of that type exists for `t ∈ [t₃, 14]`.
The proof is an explicit dual identity with rational-function multipliers in `t` (`dual_identity`).
-/

namespace DesignThresholdT3

/-- the quartic: its real root in `(8.8885, 8.889)` is `t₃` -/
def f (t : ℝ) : ℝ := 140777*t^4 - 4043858*t^3 + 35443487*t^2 - 89056524*t - 47598822

def row1 (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) : ℝ :=
  c000 + 3*t*c100 + 3*(t^2-19)*c110 + t*(t^2-57)*c111 + 3*(t^2-19)*c200 + 6*t*(t^2-57)*c210
  + 3*(t^4-114*t^2+361)*c211 + 3*(t^4-114*t^2+361)*c220 + 3*t*(t^4-190*t^2+1805)*c221
  + (t^2-19)*(t^4-266*t^2+361)*c222
def row2 (t c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) : ℝ :=
  3*c100 + 6*t*c110 + (3*t^2-19)*c111 + 6*t*c200 + 6*(3*t^2-19)*c210 + 12*t*(t^2-19)*c211
  + 12*t*(t^2-19)*c220 + 3*(5*t^4-190*t^2+361)*c221 + 2*t*(t^2-57)*(3*t^2-19)*c222
def row3 (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) : ℝ :=
  c000 + 3*t*c100 + (3*t^2+19)*c110 + t*(t^2+19)*c111 + 3*(t^2-19)*c200 + 2*t*(3*t^2-19)*c210
  + (t^2+19)*(3*t^2-19)*c211 + (3*t^4-38*t^2+1083)*c220 + t*(t^2+19)*(3*t^2-19)*c221
  + (t^2-19)*(t^2+19)^2*c222
def row4 (t c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) : ℝ :=
  c100 + 2*t*c110 + (t^2+19)*c111 + 2*t*c200 + 2*(3*t^2-19)*c210 + 4*t*(t^2+19)*c211
  + 4*t*(t^2-19)*c220 + (t^2+19)*(5*t^2+19)*c221 + 2*t*(t^2+19)^2*c222

/-- `Δ_{P₂} q` -/
def dP2 (c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) : ℝ :=
  182*c110 + 1163*c111 + 68*c200 + 4774*c210 + 41558*c211 + 28752*c220 + 464356*c221 + 1563071*c222

def P0 (t : ℝ) : ℝ := 728*t^4 - 9304*t^3 + 13832*t^2 + 1563071
def P1 (t : ℝ) : ℝ := 2116*t^4 - 27912*t^3 + 38912*t^2 + 4664665
def P2 (t : ℝ) : ℝ := 1456*t^4 - 27912*t^3 + 56416*t^2 + 5235501
def M0 (t : ℝ) : ℝ := 728*t - 4774
def M1 (t : ℝ) : ℝ := -182*t^2 + 6978*t - 45016
def M2 (t : ℝ) : ℝ := -728*t^3 + 13956*t^2 - 13832*t - 464356
def N1 (t : ℝ) : ℝ := 2002*t^6 - 27912*t^5 + 17290*t^4 + 176776*t^3 + 4229299*t^2 - 30946687
def N2 (t : ℝ) : ℝ := -546*t^7 + 8141*t^6 + 38038*t^5 - 596619*t^4 - 577541*t^3 - 1259529*t^2
  + 90343385*t - 7977017
def N3 (t : ℝ) : ℝ := -2002*t^4 + 27912*t^3 - 34580*t^2 - 4623511
def N4 (t : ℝ) : ℝ := 1638*t^5 - 24423*t^4 + 20748*t^3 + 132582*t^2 + 4492107*t + 1259529

/-- the dual identity (all `t`, all coefficients) -/
theorem dual_identity (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ) :
    76*(t^2+19)^3 * dP2 c110 c111 c200 c210 c211 c220 c221 c222
      = 76*P0 t*c000 - 76*(t^2+19)*P1 t*c200 + 76*(t^2+19)^2*P2 t*c220
        - 76*(t^2+19)^3*(M0 t*c210 + M1 t*c211 + M2 t*c221)
        + N1 t * row1 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222
        + N2 t * row2 t c100 c110 c111 c200 c210 c211 c220 c221 c222
        + (t^2+19)*N3 t * row3 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222
        + (t^2+19)*N4 t * row4 t c100 c110 c111 c200 c210 c211 c220 c221 c222 := by
  unfold dP2 P0 P1 P2 M0 M1 M2 N1 N2 N3 N4 row1 row2 row3 row4; ring

theorem moment_det (t : ℝ) : M0 t * M2 t - M1 t ^ 2 = -4 * f t := by
  unfold M0 M1 M2 f; ring

theorem P0_pos (t : ℝ) (h1 : 44/5 ≤ t) (h2 : t ≤ 14) : 0 < P0 t := by
  unfold P0; nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (t^2 - 7*t), sq_nonneg (t - 9),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (t - 9))]
theorem P1_pos (t : ℝ) (h1 : 44/5 ≤ t) (h2 : t ≤ 14) : 0 < P1 t := by
  unfold P1; nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (t^2 - 7*t), sq_nonneg (t - 9),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (t - 9))]
theorem P2_neg (t : ℝ) (h1 : 44/5 ≤ t) (h2 : t ≤ 14) : P2 t < 0 := by
  unfold P2; nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2), sq_nonneg (t^2 - 7*t), sq_nonneg (t - 9),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sq_nonneg (t - 9)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)) (sub_nonneg.2 h1)]
theorem M0_pos (t : ℝ) (h1 : 44/5 ≤ t) : 0 < M0 t := by unfold M0; linarith
theorem M1_pos (t : ℝ) (h1 : 44/5 ≤ t) (h2 : t ≤ 14) : 0 < M1 t := by
  unfold M1; nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

/-- a quadratic `a + b z + c z²` that is `≤ 0` for all `z > 0` has `c ≤ 0` -/
theorem coef_nonpos_of_quad (a b c : ℝ) (h : ∀ z : ℝ, 0 < z → a + b*z + c*z^2 ≤ 0) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  set z : ℝ := (|a| + |b| + 1) / c + 1 with hz
  have hz1 : 1 ≤ z := by
    have : 0 ≤ (|a| + |b| + 1) / c := by positivity
    linarith
  have hcz : c * z ≥ |a| + |b| + 1 := by
    have : c * ((|a| + |b| + 1) / c) = |a| + |b| + 1 := by field_simp
    nlinarith
  have := h z (by linarith)
  have ha : -|a| ≤ a := neg_abs_le a
  have hb : -|b| * z ≤ b * z := by nlinarith [neg_abs_le b]
  have h2 : c * z ^ 2 ≥ z * (|a| + |b| + 1) := by
    have : c * z ^ 2 = z * (c * z) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hcz (by linarith)
  nlinarith [mul_nonneg (abs_nonneg a) (sub_nonneg.2 hz1)]

/-- the moment step: `h ≤ 0` on `z > 0` and `M0 M2 − M1² ≥ 0`, `M0, M1 > 0` give `M0 c210 + M1 c211 + M2 c221 ≤ 0` -/
theorem moment_step (t c210 c211 c221 : ℝ) (h1 : 44/5 ≤ t) (h2 : t ≤ 14) (hf : f t ≤ 0)
    (hh : ∀ z : ℝ, 0 < z → c210 + c211*z + c221*z^2 ≤ 0) :
    M0 t * c210 + M1 t * c211 + M2 t * c221 ≤ 0 := by
  have hm0 := M0_pos t h1
  have hm1 := M1_pos t h1 h2
  have hc221 : c221 ≤ 0 := coef_nonpos_of_quad c210 c211 c221 hh
  have hz : 0 < M1 t / M0 t := div_pos hm1 hm0
  have hv := hh (M1 t / M0 t) hz
  have key : M0 t ^ 2 * (c210 + c211 * (M1 t / M0 t) + c221 * (M1 t / M0 t) ^ 2)
      = M0 t ^ 2 * c210 + M0 t * M1 t * c211 + M1 t ^ 2 * c221 := by
    field_simp
  have hG := moment_det t
  have hA : M0 t ^ 2 * c210 + M0 t * M1 t * c211 + M1 t ^ 2 * c221 ≤ 0 := by
    rw [← key]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hv
  have hB : (M0 t * M2 t - M1 t ^ 2) * c221 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by rw [hG]; linarith) hc221
  have hprod : M0 t * (M0 t * c210 + M1 t * c211 + M2 t * c221) ≤ 0 := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hm0 hcon
  linarith

/-- **Main theorem** (hypotheses: `44/5 ≤ t ≤ 14`, `f t ≤ 0` i.e. `t ≥ t₃`; `q ∈ T_t` (four rows);
`c000 ≥ 0`; `c200 ≤ 0`; `c220 ≤ 0`; `c210 + c211 z + c221 z² ≤ 0` for `z > 0`): `Δ_{P₂} q ≥ 0`. -/
theorem dP2_nonneg_of_necessary (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ)
    (h1 : 44/5 ≤ t) (h2 : t ≤ 14) (hf : f t ≤ 0)
    (hr1 : row1 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr2 : row2 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr3 : row3 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr4 : row4 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hc0 : 0 ≤ c000) (hc200 : c200 ≤ 0) (hc220 : c220 ≤ 0)
    (hh : ∀ z : ℝ, 0 < z → c210 + c211*z + c221*z^2 ≤ 0) :
    0 ≤ dP2 c110 c111 c200 c210 c211 c220 c221 c222 := by
  have hid := dual_identity t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222
  rw [hr1, hr2, hr3, hr4] at hid
  have hs : 0 < t^2 + 19 := by positivity
  have hp0 := P0_pos t h1 h2
  have hp1 := P1_pos t h1 h2
  have hp2 := P2_neg t h1 h2
  have hm := moment_step t c210 c211 c221 h1 h2 hf hh
  have e1 : 0 ≤ 76*P0 t*c000 := by positivity
  have e2 : 0 ≤ -(76*(t^2+19)*P1 t*c200) := by
    have : 0 ≤ 76*(t^2+19)*P1 t := by positivity
    nlinarith
  have e3 : 0 ≤ 76*(t^2+19)^2*P2 t*c220 := by
    have : 76*(t^2+19)^2*P2 t*c220 = (76*(t^2+19)^2) * (P2 t * c220) := by ring
    rw [this]; exact mul_nonneg (by positivity) (mul_nonneg_of_nonpos_of_nonpos hp2.le hc220)
  have e4 : 0 ≤ -(76*(t^2+19)^3*(M0 t*c210 + M1 t*c211 + M2 t*c221)) := by
    have : 0 ≤ 76*(t^2+19)^3 := by positivity
    nlinarith
  have hpos : 0 < 76*(t^2+19)^3 := by positivity
  by_contra hcon
  push Not at hcon
  have := mul_neg_of_pos_of_neg hpos hcon
  linarith

/-- corollary: for `t ∈ [t₃, 14]` (`44/5 ≤ t`, `f t ≤ 0`) no `q ∈ T_t` satisfies the four necessary sign conditions
together with `Δ_{P₂} q < 0` -/
theorem no_certificate_of_t3_le (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ)
    (h1 : 44/5 ≤ t) (h2 : t ≤ 14) (hf : f t ≤ 0)
    (hr1 : row1 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr2 : row2 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr3 : row3 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr4 : row4 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hc0 : 0 ≤ c000) (hc200 : c200 ≤ 0) (hc220 : c220 ≤ 0)
    (hh : ∀ z : ℝ, 0 < z → c210 + c211*z + c221*z^2 ≤ 0)
    (hP2 : dP2 c110 c111 c200 c210 c211 c220 c221 c222 < 0) : False := by
  have := dP2_nonneg_of_necessary t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 h1 h2 hf hr1 hr2 hr3 hr4
    hc0 hc200 hc220 hh
  linarith

/-! ## with the antisymmetric component `V = (u₁−u₂)(u₂−u₃)(u₃−u₁)` (in `T_t` for every `t`)
`Δ_{P₂} V = −342` (embeddings in descending order of `θ`).  On the real region `V` shifts the coefficient `c210`
of the two chiral faces by `∓ c_V`, so both `h_±(z) = (c210 ± c_V) + c211 z + c221 z²` must be `≤ 0`. -/

/-- **Main theorem with `V`** (hypotheses: as `dP2_nonneg_of_necessary`, with the two chiral face conditions
`h_±(z) ≤ 0` for `z > 0` in place of one): `Δ_{P₂} q − 342 c_V ≥ 0`. -/
theorem dP2V_nonneg_of_necessary (t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 cV : ℝ)
    (h1 : 44/5 ≤ t) (h2 : t ≤ 14) (hf : f t ≤ 0)
    (hr1 : row1 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr2 : row2 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr3 : row3 t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr4 : row4 t c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hc0 : 0 ≤ c000) (hc200 : c200 ≤ 0) (hc220 : c220 ≤ 0)
    (hhp : ∀ z : ℝ, 0 < z → (c210 + cV) + c211*z + c221*z^2 ≤ 0)
    (hhm : ∀ z : ℝ, 0 < z → (c210 - cV) + c211*z + c221*z^2 ≤ 0) :
    0 ≤ dP2 c110 c111 c200 c210 c211 c220 c221 c222 - 342 * cV := by
  have hid := dual_identity t c000 c100 c110 c111 c200 c210 c211 c220 c221 c222
  rw [hr1, hr2, hr3, hr4] at hid
  have hp0 := P0_pos t h1 h2
  have hp1 := P1_pos t h1 h2
  have hp2 := P2_neg t h1 h2
  have Hp := moment_step t (c210 + cV) c211 c221 h1 h2 hf hhp
  have Hm := moment_step t (c210 - cV) c211 c221 h1 h2 hf hhm
  have hm0 : 342 ≤ M0 t := by unfold M0; linarith
  have hS2 : 2 * M0 t * (M0 t * c210 + M1 t * c211 + M2 t * c221 + 342 * cV)
      = (M0 t + 342) * (M0 t * (c210 + cV) + M1 t * c211 + M2 t * c221)
        + (M0 t - 342) * (M0 t * (c210 - cV) + M1 t * c211 + M2 t * c221) := by ring
  have hS : M0 t * c210 + M1 t * c211 + M2 t * c221 + 342 * cV ≤ 0 := by
    have hA : (M0 t + 342) * (M0 t * (c210 + cV) + M1 t * c211 + M2 t * c221) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) Hp
    have hB : (M0 t - 342) * (M0 t * (c210 - cV) + M1 t * c211 + M2 t * c221) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) Hm
    by_contra hcon
    push Not at hcon
    have : 0 < 2 * M0 t * (M0 t * c210 + M1 t * c211 + M2 t * c221 + 342 * cV) :=
      mul_pos (by linarith) hcon
    linarith
  have e1 : 0 ≤ 76*P0 t*c000 := by positivity
  have e2 : 0 ≤ -(76*(t^2+19)*P1 t*c200) := by
    have : 0 ≤ 76*(t^2+19)*P1 t := by positivity
    nlinarith
  have e3 : 0 ≤ 76*(t^2+19)^2*P2 t*c220 := by
    have : 76*(t^2+19)^2*P2 t*c220 = (76*(t^2+19)^2) * (P2 t * c220) := by ring
    rw [this]; exact mul_nonneg (by positivity) (mul_nonneg_of_nonpos_of_nonpos hp2.le hc220)
  have hpos : 0 < 76*(t^2+19)^3 := by positivity
  have e4 : 0 ≤ -(76*(t^2+19)^3*(M0 t*c210 + M1 t*c211 + M2 t*c221 + 342 * cV)) := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_neg_of_pos_of_neg hpos hcon
  nlinarith

/-! ## location of `t₃` (exact rational evaluations of `f`) -/
theorem f_pos_17777_2000 : 0 < f (17777/2000) := by norm_num [f]
theorem f_pos_88886088 : 0 < f (88886088/10000000) := by norm_num [f]
theorem f_neg_88886089 : f (88886089/10000000) < 0 := by norm_num [f]
theorem f_neg_88887 : f (88887/10000) < 0 := by norm_num [f]
theorem f_neg_8889 : f (8889/1000) < 0 := by norm_num [f]
theorem f_neg_14 : f 14 < 0 := by norm_num [f]

/-- instance: at the rational point `t = 88887/10000` (just above `t₃`) the necessary conditions exclude `Δ_{P₂} q < 0` -/
theorem no_certificate_at_88887 (c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 : ℝ)
    (hr1 : row1 (88887/10000) c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr2 : row2 (88887/10000) c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr3 : row3 (88887/10000) c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hr4 : row4 (88887/10000) c100 c110 c111 c200 c210 c211 c220 c221 c222 = 0)
    (hc0 : 0 ≤ c000) (hc200 : c200 ≤ 0) (hc220 : c220 ≤ 0)
    (hh : ∀ z : ℝ, 0 < z → c210 + c211*z + c221*z^2 ≤ 0)
    (hP2 : dP2 c110 c111 c200 c210 c211 c220 c221 c222 < 0) : False :=
  no_certificate_of_t3_le (88887/10000) c000 c100 c110 c111 c200 c210 c211 c220 c221 c222 (by norm_num) (by norm_num)
    f_neg_88887.le hr1 hr2 hr3 hr4 hc0 hc200 hc220 hh hP2

end DesignThresholdT3

#print axioms DesignThresholdT3.dual_identity
#print axioms DesignThresholdT3.moment_det
#print axioms DesignThresholdT3.coef_nonpos_of_quad
#print axioms DesignThresholdT3.moment_step
#print axioms DesignThresholdT3.dP2_nonneg_of_necessary
#print axioms DesignThresholdT3.no_certificate_of_t3_le
#print axioms DesignThresholdT3.dP2V_nonneg_of_necessary
#print axioms DesignThresholdT3.f_pos_17777_2000
#print axioms DesignThresholdT3.f_pos_88886088
#print axioms DesignThresholdT3.f_neg_88886089
#print axioms DesignThresholdT3.f_neg_88887
#print axioms DesignThresholdT3.f_neg_8889
#print axioms DesignThresholdT3.f_neg_14
#print axioms DesignThresholdT3.no_certificate_at_88887
