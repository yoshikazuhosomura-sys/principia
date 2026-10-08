import Principia.DistinctCircumradii.SevenPoints

/-!
# 非実現（向きの議論）：名前空間 `QU2` の k11・k33

土台の宣言は `import` で引く。ここに残した宣言が本ファイルの内容である。
-/

namespace DistinctCircumradii

set_option linter.unusedVariables false

namespace QU2

/-- 格子の証明書が作る形。`L = R`（証人条件の積）と `N * R = D * L`（単項式の恒等式）
から `N = D` が出る。`N`, `D` は目標の形式に対応する単項式で、`L`, `R` は
証人条件を掛け合わせた単項式である。 -/
theorem eq_of_cert {N D L R : ℂ} (hLR : L = R) (hmono : N * R = D * L) (hL : L ≠ 0) :
    N = D := by
  rw [← hLR] at hmono
  exact mul_right_cancel₀ hL hmono

/-- 2 乗距離は負にならない。 -/
theorem sqdist_nonneg (p q : Pt) : 0 ≤ sqdist p q := by
  simp only [sqdist]
  positivity

/-- `qq` は最初の 2 つの引数について対称。 -/
theorem qq_comm (a b p : Pt) : qq a b p = qq b a p := by
  simp only [qq]; ring

/-- 直角を多項式の等式として書く。`(b - a) * conj (c - a)` の実部が `qq b c a` なので、
その数とその共役の和が `2 * qq b c a` である。 -/
theorem perp_poly {a b c : Pt} (h : qq b c a = 0) :
    (toC b - toC a) * (barC c - barC a) + (barC b - barC a) * (toC c - toC a) = 0 := by
  simp only [qq] at h
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
      toC_re, toC_im, barC_re, barC_im]
  · linear_combination (2 : ℝ) * h
  · ring

/-! ### 閉じた 5 角形の各頂点が直角にはなれない

5 点 `V₀ … V₄` を巡る辺のベクトルを `u₀ … u₄` とし、`v` をその共役とする。
頂点 `V_t` での直角は `u_{t-1} v_t + v_{t-1} u_t = 0`（実部が 0）である。
2 本続けると `u_{t-1} v_{t+1} = v_{t-1} u_{t+1}`（＝ 1 本飛ばしの辺が平行）になり、
これを 2 回使うと `u₀ v₄ = v₀ u₄`、すなわち `u₀ ∥ u₄` が出る。
ところが残る 1 本は `u₄ v₀ + v₄ u₀ = 0`（＝ `u₀ ⊥ u₄`）なので、
平行かつ直交となり `u₀ = 0` か `v₄ = 0` になる。 -/

theorem pentagon_absurd {u1 u2 u3 u4 u5 v1 v2 v3 v4 v5 : ℂ}
    (e1 : u1 * v2 + v1 * u2 = 0) (e2 : u2 * v3 + v2 * u3 = 0)
    (e3 : u3 * v4 + v3 * u4 = 0) (e4 : u4 * v5 + v4 * u5 = 0)
    (e5 : u5 * v1 + v5 * u1 = 0)
    (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) (hu3 : u3 ≠ 0) (hu4 : u4 ≠ 0)
    (hv2 : v2 ≠ 0) (hv3 : v3 ≠ 0) (hv4 : v4 ≠ 0) (hv5 : v5 ≠ 0) :
    False := by
  have p13 : u1 * v3 = v1 * u3 := by
    have h : (u2 * v2) * (u1 * v3 - v1 * u3) = 0 := by
      linear_combination (u2 * v3) * e1 - (v1 * u2) * e2
    have h2 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu2 hv2)
    linear_combination h2
  have p35 : u3 * v5 = v3 * u5 := by
    have h : (u4 * v4) * (u3 * v5 - v3 * u5) = 0 := by
      linear_combination (u4 * v5) * e3 - (v3 * u4) * e4
    have h2 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu4 hv4)
    linear_combination h2
  have p15 : u1 * v5 = v1 * u5 := by
    have h : (u3 * v3) * (u1 * v5 - v1 * u5) = 0 := by
      linear_combination (u3 * v5) * p13 + (v1 * u3) * p35
    have h2 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu3 hv3)
    linear_combination h2
  have hfin : u1 * v5 = 0 := by
    linear_combination (1 / 2 : ℂ) * p15 + (1 / 2 : ℂ) * e5
  exact (mul_ne_zero hu1 hv5) hfin

/-! ### 1 つ目の類（直角 5 本の和が 2 乗距離の和になる） -/

/-- 格子の所属の証明書（枡 7 個・係数 [-1, 1, 1, 1, 1, -1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{01} - e_{04}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p0 - p1) / (p0 - p4)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem rightAngleCert1 {z01 z02 z03 z04 z05 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z04 * z24 * c05 * c25 = z05 * z25 * c04 * c24)
    (E2 : z01 * z13 * c02 * c23 = z02 * z23 * c01 * c13)
    (E3 : z02 * z24 * c03 * c34 = z03 * z34 * c02 * c24)
    (E4 : z01 * z03 * c15 * c35 = z15 * z35 * c01 * c03)
    (E5 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E6 : z13 * z14 * c35 * c45 = z35 * z45 * c13 * c14)
    (E7 : z04 * z05 * c14 * c15 = z14 * z15 * c04 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z01 * z01 * c04 * c04 = z04 * z04 * c01 * c01 := by
  have hL : z01 * z01 * z02 * z03 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz01)) (nz02)) (nz03)) (nz05)) (nz13)) (nz14)) (nz15)) (nz23)) (nz24)) (nz25)) (nz34)) (nz35)) (nz45)) (nc02)) (nc03)) (nc04)) (nc04)) (nc05)) (nc13)) (nc14)) (nc15)) (nc23)) (nc24)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z01 * z02 * z03 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 = z02 * z03 * z04 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c05 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 := by
    linear_combination - (z01 * z01 * z02 * z03 * z13 * z14 * z15 * z23 * z24 * z34 * z35 * z45 * c02 * c03 * c04 * c05 * c13 * c14 * c15 * c23 * c25 * c34 * c35 * c45) * E1 + (z01 * z02 * z03 * z04 * z14 * z15 * z23 * z24 * z24 * z34 * z35 * z45 * c03 * c04 * c05 * c05 * c13 * c14 * c15 * c25 * c25 * c34 * c35 * c45) * E2 + (z01 * z02 * z03 * z04 * z14 * z15 * z23 * z23 * z24 * z34 * z35 * z45 * c01 * c04 * c05 * c05 * c13 * c13 * c14 * c15 * c25 * c25 * c35 * c45) * E3 + (z02 * z03 * z04 * z14 * z15 * z23 * z23 * z24 * z34 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c05 * c13 * c13 * c14 * c24 * c25 * c25 * c45) * E4 + (z02 * z03 * z04 * z14 * z15 * z15 * z23 * z24 * z34 * z35 * z35 * z45 * c01 * c01 * c02 * c03 * c04 * c05 * c05 * c13 * c13 * c14 * c24 * c25) * E5 - (z02 * z03 * z04 * z14 * z15 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c04 * c05 * c05 * c13 * c23 * c24 * c25 * c34) * E6 - (z02 * z03 * z04 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c05 * c13 * c23 * c24 * c25 * c34 * c35 * c45) * E7
  have hmono : z01 * z01 * c04 * c04 * (z02 * z03 * z04 * z04 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c01 * c02 * c03 * c05 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45) = z04 * z04 * c01 * c01 * (z01 * z01 * z02 * z03 * z05 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c02 * c03 * c04 * c04 * c05 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [1, 1, -1, -1, -1, 1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{02} - e_{23}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p2 - p0) / (p2 - p3)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem rightAngleCert2 {z01 z02 z03 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z12 * c05 * c15 = z05 * z15 * c02 * c12)
    (E2 : z01 * z02 * c14 * c24 = z14 * z24 * c01 * c02)
    (E3 : z01 * z03 * c15 * c35 = z15 * z35 * c01 * c03)
    (E4 : z12 * z13 * c24 * c34 = z24 * z34 * c12 * c13)
    (E5 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E6 : z13 * z14 * c35 * c45 = z35 * z45 * c13 * c14)
    (E7 : z03 * z05 * c23 * c25 = z23 * z25 * c03 * c05)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z02 * z02 * c23 * c23 = z23 * z23 * c02 * c02 := by
  have hL : z01 * z02 * z02 * z03 * z05 * z12 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c03 * c05 * c12 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz02)) (nz03)) (nz05)) (nz12)) (nz13)) (nz14)) (nz15)) (nz24)) (nz25)) (nz34)) (nz35)) (nz45)) (nc01)) (nc03)) (nc05)) (nc12)) (nc13)) (nc14)) (nc15)) (nc23)) (nc23)) (nc24)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z02 * z02 * z03 * z05 * z12 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c03 * c05 * c12 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35 * c45 = z01 * z03 * z05 * z12 * z13 * z14 * z15 * z23 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c02 * c03 * c05 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35 * c45 := by
    linear_combination (z01 * z02 * z03 * z05 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c03 * c12 * c13 * c14 * c23 * c23 * c24 * c25 * c34 * c35 * c45) * E1 + (z03 * z05 * z05 * z13 * z14 * z15 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c12 * c12 * c13 * c23 * c23 * c25 * c34 * c35 * c45) * E2 - (z03 * z05 * z05 * z13 * z14 * z14 * z15 * z24 * z24 * z25 * z34 * z45 * c01 * c02 * c02 * c12 * c12 * c13 * c23 * c23 * c25 * c34 * c35 * c45) * E3 - (z01 * z03 * z03 * z05 * z05 * z13 * z14 * z14 * z15 * z24 * z25 * z45 * c01 * c02 * c02 * c12 * c15 * c23 * c23 * c25 * c34 * c35 * c35 * c45) * E4 - (z01 * z03 * z03 * z05 * z05 * z12 * z13 * z13 * z14 * z14 * z15 * z24 * c01 * c02 * c02 * c12 * c15 * c23 * c24 * c25 * c34 * c35 * c35 * c45) * E5 + (z01 * z03 * z03 * z05 * z05 * z12 * z13 * z14 * z15 * z23 * z24 * z34 * c01 * c02 * c02 * c12 * c15 * c23 * c24 * c25 * c25 * c34 * c35 * c45) * E6 + (z01 * z03 * z05 * z12 * z13 * z14 * z15 * z23 * z24 * z34 * z35 * z45 * c01 * c02 * c02 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35 * c45) * E7
  have hmono : z02 * z02 * c23 * c23 * (z01 * z03 * z05 * z12 * z13 * z14 * z15 * z23 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c02 * c03 * c05 * c12 * c13 * c14 * c15 * c24 * c25 * c34 * c35 * c45) = z23 * z23 * c02 * c02 * (z01 * z02 * z02 * z03 * z05 * z12 * z13 * z14 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c03 * c05 * c12 * c13 * c14 * c15 * c23 * c23 * c24 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [-1, 1, -1, 1, 1, 1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{03} - e_{34}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p3 - p0) / (p3 - p4)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem rightAngleCert3 {z01 z02 z03 z04 z05 z12 z13 z15 z23 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z12 * c05 * c15 = z05 * z15 * c02 * c12)
    (E2 : z04 * z24 * c05 * c25 = z05 * z25 * c04 * c24)
    (E3 : z01 * z13 * c02 * c23 = z02 * z23 * c01 * c13)
    (E4 : z03 * z35 * c04 * c45 = z04 * z45 * c03 * c35)
    (E5 : z01 * z03 * c15 * c35 = z15 * z35 * c01 * c03)
    (E6 : z12 * z13 * c24 * c34 = z24 * z34 * c12 * c13)
    (E7 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z03 * z03 * c34 * c34 = z34 * z34 * c03 * c03 := by
  have hL : z01 * z02 * z03 * z03 * z04 * z05 * z12 * z13 * z15 * z23 * z24 * z25 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c25 * c34 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz03)) (nz03)) (nz04)) (nz05)) (nz12)) (nz13)) (nz15)) (nz23)) (nz24)) (nz25)) (nz35)) (nz45)) (nc01)) (nc02)) (nc04)) (nc05)) (nc12)) (nc13)) (nc15)) (nc23)) (nc24)) (nc25)) (nc34)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z02 * z03 * z03 * z04 * z05 * z12 * z13 * z15 * z23 * z24 * z25 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c25 * c34 * c34 * c35 * c45 = z01 * z02 * z04 * z05 * z12 * z13 * z15 * z23 * z24 * z25 * z34 * z34 * z35 * z45 * c01 * c02 * c03 * c03 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c25 * c35 * c45 := by
    linear_combination - (z01 * z02 * z03 * z03 * z04 * z12 * z13 * z23 * z24 * z25 * z35 * z45 * c01 * c04 * c05 * c13 * c15 * c23 * c24 * c25 * c34 * c34 * c35 * c45) * E1 + (z01 * z02 * z02 * z03 * z03 * z12 * z12 * z13 * z23 * z25 * z35 * z45 * c01 * c04 * c05 * c13 * c15 * c15 * c23 * c24 * c34 * c34 * c35 * c45) * E2 - (z01 * z02 * z03 * z03 * z05 * z12 * z12 * z13 * z25 * z25 * z35 * z45 * c04 * c04 * c05 * c15 * c15 * c23 * c24 * c24 * c34 * c34 * c35 * c45) * E3 + (z01 * z01 * z02 * z03 * z05 * z12 * z12 * z13 * z13 * z25 * z25 * z45 * c02 * c04 * c05 * c15 * c15 * c23 * c23 * c24 * c24 * c34 * c34 * c35) * E4 + (z01 * z02 * z04 * z05 * z12 * z12 * z13 * z13 * z25 * z25 * z45 * z45 * c02 * c03 * c04 * c05 * c15 * c23 * c23 * c24 * c24 * c34 * c34 * c35) * E5 + (z01 * z02 * z04 * z05 * z12 * z13 * z15 * z25 * z25 * z35 * z45 * z45 * c01 * c02 * c03 * c03 * c04 * c05 * c15 * c23 * c23 * c24 * c34 * c35) * E6 - (z01 * z02 * z04 * z05 * z12 * z13 * z15 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c03 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c35) * E7
  have hmono : z03 * z03 * c34 * c34 * (z01 * z02 * z04 * z05 * z12 * z13 * z15 * z23 * z24 * z25 * z34 * z34 * z35 * z45 * c01 * c02 * c03 * c03 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c25 * c35 * c45) = z34 * z34 * c03 * c03 * (z01 * z02 * z03 * z03 * z04 * z05 * z12 * z13 * z15 * z23 * z24 * z25 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c13 * c15 * c23 * c24 * c25 * c34 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [1, -1, -1, 1, 1, 1, -1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{12} - e_{13}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p1 - p2) / (p1 - p3)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem rightAngleCert4 {z01 z02 z04 z05 z12 z13 z14 z15 z23 z24 z25 z34 z35 z45 c01 c02 c04 c05 c12 c13 c14 c15 c23 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z12 * c05 * c15 = z05 * z15 * c02 * c12)
    (E2 : z04 * z24 * c05 * c25 = z05 * z25 * c04 * c24)
    (E3 : z01 * z02 * c14 * c24 = z14 * z24 * c01 * c02)
    (E4 : z01 * z04 * c13 * c34 = z13 * z34 * c01 * c04)
    (E5 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E6 : z12 * z15 * c23 * c35 = z23 * z35 * c12 * c15)
    (E7 : z13 * z14 * c35 * c45 = z35 * z45 * c13 * c14)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc14 : c14 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z12 * z12 * c13 * c13 = z13 * z13 * c12 * c12 := by
  have hL : z01 * z02 * z04 * z05 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c13 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz04)) (nz05)) (nz12)) (nz12)) (nz14)) (nz15)) (nz23)) (nz24)) (nz25)) (nz34)) (nz35)) (nz45)) (nc01)) (nc02)) (nc04)) (nc05)) (nc13)) (nc13)) (nc14)) (nc15)) (nc23)) (nc24)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z02 * z04 * z05 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c13 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 = z01 * z02 * z04 * z05 * z13 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45 := by
    linear_combination (z01 * z04 * z05 * z12 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c13 * c13 * c14 * c23 * c24 * c25 * c34 * c35 * c45) * E1 - (z01 * z04 * z05 * z12 * z14 * z15 * z15 * z23 * z24 * z34 * z35 * z45 * c01 * c02 * c02 * c12 * c13 * c13 * c14 * c23 * c25 * c34 * c35 * c45) * E2 - (z01 * z04 * z04 * z05 * z12 * z15 * z15 * z23 * z24 * z34 * z35 * z45 * c02 * c05 * c12 * c13 * c13 * c14 * c23 * c25 * c25 * c34 * c35 * c45) * E3 + (z01 * z02 * z04 * z05 * z12 * z15 * z15 * z23 * z24 * z34 * z35 * z45 * c02 * c05 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c25 * c35 * c45) * E4 + (z01 * z02 * z04 * z05 * z12 * z13 * z15 * z15 * z24 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c35) * E5 + (z01 * z02 * z04 * z05 * z13 * z15 * z24 * z25 * z34 * z35 * z45 * z45 * c01 * c02 * c04 * c05 * c12 * c13 * c14 * c14 * c23 * c24 * c25 * c34) * E6 - (z01 * z02 * z04 * z05 * z13 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c34) * E7
  have hmono : z12 * z12 * c13 * c13 * (z01 * z02 * z04 * z05 * z13 * z13 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c12 * c12 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45) = z13 * z13 * c12 * c12 * (z01 * z02 * z04 * z05 * z12 * z12 * z14 * z15 * z23 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c04 * c05 * c13 * c13 * c14 * c15 * c23 * c24 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 7 個・係数 [1, -1, -1, -1, 1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{14} - e_{24}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p4 - p1) / (p4 - p2)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem rightAngleCert5 {z01 z02 z03 z04 z05 z12 z13 z14 z15 z24 z25 z34 z35 z45 c01 c02 c03 c04 c05 c12 c13 c14 c15 c24 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z12 * c05 * c15 = z05 * z15 * c02 * c12)
    (E2 : z04 * z24 * c05 * c25 = z05 * z25 * c04 * c24)
    (E3 : z02 * z24 * c03 * c34 = z03 * z34 * c02 * c24)
    (E4 : z01 * z03 * c15 * c35 = z15 * z35 * c01 * c03)
    (E5 : z01 * z04 * c13 * c34 = z13 * z34 * c01 * c04)
    (E6 : z12 * z25 * c14 * c45 = z14 * z45 * c12 * c25)
    (E7 : z13 * z14 * c35 * c45 = z35 * z45 * c13 * c14)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz15 : z15 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz34 : z34 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc03 : c03 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z14 * z14 * c24 * c24 = z24 * z24 * c14 * c14 := by
  have hL : z01 * z02 * z03 * z04 * z05 * z12 * z13 * z14 * z14 * z15 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c15 * c24 * c24 * c25 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz03)) (nz04)) (nz05)) (nz12)) (nz13)) (nz14)) (nz14)) (nz15)) (nz25)) (nz34)) (nz35)) (nz45)) (nc01)) (nc02)) (nc03)) (nc04)) (nc05)) (nc12)) (nc13)) (nc15)) (nc24)) (nc24)) (nc25)) (nc34)) (nc35)) (nc45)
  have hLR : z01 * z02 * z03 * z04 * z05 * z12 * z13 * z14 * z14 * z15 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c15 * c24 * c24 * c25 * c34 * c35 * c45 = z01 * z02 * z03 * z04 * z05 * z12 * z13 * z15 * z24 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c14 * c14 * c15 * c25 * c34 * c35 * c45 := by
    linear_combination (z01 * z03 * z04 * z05 * z13 * z14 * z14 * z15 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c12 * c13 * c24 * c24 * c25 * c34 * c35 * c45) * E1 - (z01 * z03 * z04 * z05 * z13 * z14 * z14 * z15 * z15 * z34 * z35 * z45 * c01 * c02 * c02 * c03 * c12 * c12 * c13 * c24 * c25 * c34 * c35 * c45) * E2 - (z01 * z04 * z04 * z05 * z13 * z14 * z14 * z15 * z15 * z24 * z35 * z45 * c01 * c02 * c03 * c05 * c12 * c12 * c13 * c25 * c25 * c34 * c35 * c45) * E3 - (z01 * z02 * z04 * z04 * z05 * z13 * z14 * z14 * z15 * z24 * z24 * z45 * c02 * c03 * c05 * c12 * c12 * c13 * c25 * c25 * c34 * c34 * c35 * c45) * E4 + (z01 * z02 * z03 * z04 * z05 * z13 * z14 * z14 * z15 * z24 * z24 * z45 * c02 * c03 * c05 * c12 * c12 * c15 * c25 * c25 * c34 * c35 * c35 * c45) * E5 - (z01 * z02 * z03 * z04 * z05 * z13 * z13 * z14 * z15 * z24 * z24 * z34 * c01 * c02 * c03 * c04 * c05 * c12 * c15 * c25 * c34 * c35 * c35 * c45) * E6 + (z01 * z02 * z03 * z04 * z05 * z12 * z13 * z15 * z24 * z24 * z25 * z34 * c01 * c02 * c03 * c04 * c05 * c12 * c14 * c15 * c25 * c34 * c35 * c45) * E7
  have hmono : z14 * z14 * c24 * c24 * (z01 * z02 * z03 * z04 * z05 * z12 * z13 * z15 * z24 * z24 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c14 * c14 * c15 * c25 * c34 * c35 * c45) = z24 * z24 * c14 * c14 * (z01 * z02 * z03 * z04 * z05 * z12 * z13 * z14 * z14 * z15 * z25 * z34 * z35 * z45 * c01 * c02 * c03 * c04 * c05 * c12 * c13 * c15 * c24 * c24 * c25 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- **この 5 枡の証人を持つ 6 点は一般の位置にない。**単因子が `1⁹, 2⁶` の類の証人集合（15 枡）のうち、証明書に使う枡だけを仮定にしている。位数 2 の共線形式は `(0;1,4), (2;0,3), (3;0,4), (1;2,3), (4;1,2)` の 5 本で、直角を 2 乗距離で読んだ 5 本の和が `sqdist p₀p₁ + sqdist p₀p₂ + sqdist p₁p₃ + sqdist p₂p₄ + sqdist p₃p₄ = 0` になる。 -/

theorem no_general_position_of_right_angle_sum (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 4) (p 5) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 2) (p 0) (p 3) = 0)
    (hw4 : Psi (p 2) (p 3) (p 0) (p 4) = 0)
    (hw5 : Psi (p 3) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 4) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 5) (p 1) (p 3) = 0)
    (hw8 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 4) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 5) = 0)
    (hw13 : Psi (p 1) (p 5) (p 3) (p 4) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hsq1 : ((toC (p 0) - toC (p 1)) * (barC (p 0) - barC (p 4))) ^ 2
      = ((barC (p 0) - barC (p 1)) * (toC (p 0) - toC (p 4))) ^ 2 := by
    linear_combination rightAngleCert1
      (show (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 4)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 1) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr1 : qq (p 1) (p 4) (p 0) * cross (p 0) (p 1) (p 4) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq1
  have hc1 : cross (p 0) (p 1) (p 4) ≠ 0 := by
    simpa [Collinear3] using hcol 0 1 4 (by decide) (by decide)
  have ha1 : qq (p 1) (p 4) (p 0) = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hc1
  have hsq2 : ((toC (p 2) - toC (p 0)) * (barC (p 2) - barC (p 3))) ^ 2
      = ((barC (p 2) - barC (p 0)) * (toC (p 2) - toC (p 3))) ^ 2 := by
    linear_combination rightAngleCert2
      (show (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 1) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 1) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 3)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw13)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr2 : qq (p 0) (p 3) (p 2) * cross (p 2) (p 0) (p 3) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq2
  have hc2 : cross (p 2) (p 0) (p 3) ≠ 0 := by
    have h0 : cross (p 0) (p 2) (p 3) ≠ 0 := by
      simpa [Collinear3] using hcol 0 2 3 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination -hx
  have ha2 : qq (p 0) (p 3) (p 2) = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hc2
  have hsq3 : ((toC (p 3) - toC (p 0)) * (barC (p 3) - barC (p 4))) ^ 2
      = ((barC (p 3) - barC (p 0)) * (toC (p 3) - toC (p 4))) ^ 2 := by
    linear_combination rightAngleCert3
      (show (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) = (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 3)) * (barC (p 2) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 2) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr3 : qq (p 0) (p 4) (p 3) * cross (p 3) (p 0) (p 4) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq3
  have hc3 : cross (p 3) (p 0) (p 4) ≠ 0 := by
    have h0 : cross (p 0) (p 3) (p 4) ≠ 0 := by
      simpa [Collinear3] using hcol 0 3 4 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination -hx
  have ha3 : qq (p 0) (p 4) (p 3) = 0 := by
    rcases mul_eq_zero.mp hr3 with h | h
    · exact h
    · exact absurd h hc3
  have hsq4 : ((toC (p 1) - toC (p 2)) * (barC (p 1) - barC (p 3))) ^ 2
      = ((barC (p 1) - barC (p 2)) * (toC (p 1) - toC (p 3))) ^ 2 := by
    linear_combination rightAngleCert4
      (show (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 1) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 1) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw8)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw11)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw13)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 4 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr4 : qq (p 2) (p 3) (p 1) * cross (p 1) (p 2) (p 3) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq4
  have hc4 : cross (p 1) (p 2) (p 3) ≠ 0 := by
    simpa [Collinear3] using hcol 1 2 3 (by decide) (by decide)
  have ha4 : qq (p 2) (p 3) (p 1) = 0 := by
    rcases mul_eq_zero.mp hr4 with h | h
    · exact h
    · exact absurd h hc4
  have hsq5 : ((toC (p 4) - toC (p 1)) * (barC (p 4) - barC (p 2))) ^ 2
      = ((barC (p 4) - barC (p 1)) * (toC (p 4) - toC (p 2))) ^ 2 := by
    linear_combination rightAngleCert5
      (show (toC (p 0) - toC (p 2)) * (toC (p 1) - toC (p 2)) * (barC (p 0) - barC (p 5)) * (barC (p 1) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 1) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw7)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw8)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw9)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw13)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 1 5 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 3 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr5 : qq (p 1) (p 2) (p 4) * cross (p 4) (p 1) (p 2) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq5
  have hc5 : cross (p 4) (p 1) (p 2) ≠ 0 := by
    have h0 : cross (p 1) (p 2) (p 4) ≠ 0 := by
      simpa [Collinear3] using hcol 1 2 4 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination hx
  have ha5 : qq (p 1) (p 2) (p 4) = 0 := by
    rcases mul_eq_zero.mp hr5 with h | h
    · exact h
    · exact absurd h hc5
  have hsum : sqdist (p 0) (p 1) + sqdist (p 0) (p 2) + sqdist (p 1) (p 3) + sqdist (p 2) (p 4) + sqdist (p 3) (p 4) = 0 := by
    simp only [qq] at ha1 ha2 ha3 ha4 ha5
    simp only [sqdist]
    linear_combination 2 * ha1 + 2 * ha2 + 2 * ha3 + 2 * ha4 + 2 * ha5
  have hz : sqdist (p 0) (p 1) = 0 := by
    linarith [sqdist_nonneg (p 0) (p 1), sqdist_nonneg (p 0) (p 2), sqdist_nonneg (p 1) (p 3), sqdist_nonneg (p 2) (p 4), sqdist_nonneg (p 3) (p 4)]
  exact (hne 0 1 (by decide)) (eq_of_sqdist_eq_zero hz)

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。使うのは上の枡だけである。 -/
theorem no_general_position_of_right_angle_sum_all (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 2) (p 5) (p 0) (p 1) = 0)
    (hw2 : Psi (p 4) (p 5) (p 0) (p 2) = 0)
    (hw3 : Psi (p 1) (p 2) (p 0) (p 3) = 0)
    (hw4 : Psi (p 2) (p 3) (p 0) (p 4) = 0)
    (hw5 : Psi (p 3) (p 4) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 4) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 5) (p 1) (p 3) = 0)
    (hw8 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (hw9 : Psi (p 2) (p 4) (p 1) (p 5) = 0)
    (hw10 : Psi (p 1) (p 4) (p 2) (p 3) = 0)
    (hw11 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw12 : Psi (p 1) (p 3) (p 2) (p 5) = 0)
    (hw13 : Psi (p 1) (p 5) (p 3) (p 4) = 0)
    (hw14 : Psi (p 0) (p 2) (p 3) (p 5) = 0)
    (hw15 : Psi (p 0) (p 1) (p 4) (p 5) = 0)
    : False :=
  no_general_position_of_right_angle_sum p hgp hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15

/-! ### 2 つ目の類（直角 5 本が閉じた 5 角形の各頂点にある） -/

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{03} - e_{34}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p3 - p0) / (p3 - p4)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem pentagonCert1 {z02 z03 z04 z23 z25 z34 z35 z45 c02 c03 c04 c23 c25 c34 c35 c45 : ℂ}
    (E1 : z02 * z23 * c04 * c34 = z04 * z34 * c02 * c23)
    (E2 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E3 : z23 * z34 * c25 * c45 = z25 * z45 * c23 * c34)
    (E4 : z03 * z04 * c35 * c45 = z35 * z45 * c03 * c04)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc34 : c34 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z03 * z03 * c34 * c34 = z34 * z34 * c03 * c03 := by
  have hL : z02 * z03 * z03 * z04 * z23 * z25 * z35 * z45 * c02 * c04 * c23 * c25 * c34 * c34 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz02) (nz03)) (nz03)) (nz04)) (nz23)) (nz25)) (nz35)) (nz45)) (nc02)) (nc04)) (nc23)) (nc25)) (nc34)) (nc34)) (nc35)) (nc45)
  have hLR : z02 * z03 * z03 * z04 * z23 * z25 * z35 * z45 * c02 * c04 * c23 * c25 * c34 * c34 * c35 * c45 = z02 * z04 * z23 * z25 * z34 * z34 * z35 * z45 * c02 * c03 * c03 * c04 * c23 * c25 * c35 * c45 := by
    linear_combination (z03 * z03 * z04 * z25 * z35 * z45 * c02 * c23 * c25 * c34 * c35 * c45) * E1 - (z03 * z04 * z04 * z25 * z34 * z45 * c02 * c23 * c23 * c34 * c35 * c45) * E2 - (z02 * z03 * z04 * z04 * z25 * z34 * c02 * c03 * c23 * c35 * c35 * c45) * E3 + (z02 * z04 * z23 * z25 * z34 * z34 * c02 * c03 * c23 * c25 * c35 * c45) * E4
  have hmono : z03 * z03 * c34 * c34 * (z02 * z04 * z23 * z25 * z34 * z34 * z35 * z45 * c02 * c03 * c03 * c04 * c23 * c25 * c35 * c45) = z34 * z34 * c03 * c03 * (z02 * z03 * z03 * z04 * z23 * z25 * z35 * z45 * c02 * c04 * c23 * c25 * c34 * c34 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, 1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{14} - e_{34}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p4 - p1) / (p4 - p3)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem pentagonCert2 {z01 z02 z04 z13 z14 z23 z24 z34 c01 c02 c04 c13 c14 c23 c24 c34 : ℂ}
    (E1 : z02 * z23 * c04 * c34 = z04 * z34 * c02 * c23)
    (E2 : z01 * z02 * c14 * c24 = z14 * z24 * c01 * c02)
    (E3 : z01 * z04 * c13 * c34 = z13 * z34 * c01 * c04)
    (E4 : z13 * z14 * c23 * c24 = z23 * z24 * c13 * c14)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc34 : c34 ≠ 0)
    : z14 * z14 * c34 * c34 = z34 * z34 * c14 * c14 := by
  have hL : z01 * z02 * z04 * z13 * z14 * z14 * z23 * z24 * c01 * c02 * c04 * c13 * c23 * c24 * c34 * c34 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz04)) (nz13)) (nz14)) (nz14)) (nz23)) (nz24)) (nc01)) (nc02)) (nc04)) (nc13)) (nc23)) (nc24)) (nc34)) (nc34)
  have hLR : z01 * z02 * z04 * z13 * z14 * z14 * z23 * z24 * c01 * c02 * c04 * c13 * c23 * c24 * c34 * c34 = z01 * z02 * z04 * z13 * z23 * z24 * z34 * z34 * c01 * c02 * c04 * c13 * c14 * c14 * c23 * c24 := by
    linear_combination (z01 * z04 * z13 * z14 * z14 * z24 * c01 * c02 * c13 * c23 * c24 * c34) * E1 - (z01 * z04 * z04 * z13 * z14 * z34 * c02 * c13 * c23 * c23 * c24 * c34) * E2 + (z01 * z02 * z04 * z13 * z14 * z34 * c02 * c14 * c23 * c23 * c24 * c24) * E3 + (z01 * z02 * z04 * z13 * z34 * z34 * c01 * c02 * c04 * c14 * c23 * c24) * E4
  have hmono : z14 * z14 * c34 * c34 * (z01 * z02 * z04 * z13 * z23 * z24 * z34 * z34 * c01 * c02 * c04 * c13 * c14 * c14 * c23 * c24) = z34 * z34 * c14 * c14 * (z01 * z02 * z04 * z13 * z14 * z14 * z23 * z24 * c01 * c02 * c04 * c13 * c23 * c24 * c34 * c34) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{14} - e_{15}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p1 - p4) / (p1 - p5)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem pentagonCert3 {z12 z13 z14 z15 z23 z24 z35 z45 c12 c13 c14 c15 c23 c24 c35 c45 : ℂ}
    (E1 : z12 * z24 * c15 * c45 = z15 * z45 * c12 * c24)
    (E2 : z13 * z35 * c14 * c45 = z14 * z45 * c13 * c35)
    (E3 : z12 * z15 * c23 * c35 = z23 * z35 * c12 * c15)
    (E4 : z13 * z14 * c23 * c24 = z23 * z24 * c13 * c14)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz14 : z14 ≠ 0)
    (nz23 : z23 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc23 : c23 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc35 : c35 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z14 * z14 * c15 * c15 = z15 * z15 * c14 * c14 := by
  have hL : z12 * z13 * z14 * z14 * z23 * z24 * z35 * z45 * c12 * c13 * c15 * c15 * c23 * c24 * c35 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz12) (nz13)) (nz14)) (nz14)) (nz23)) (nz24)) (nz35)) (nz45)) (nc12)) (nc13)) (nc15)) (nc15)) (nc23)) (nc24)) (nc35)) (nc45)
  have hLR : z12 * z13 * z14 * z14 * z23 * z24 * z35 * z45 * c12 * c13 * c15 * c15 * c23 * c24 * c35 * c45 = z12 * z13 * z15 * z15 * z23 * z24 * z35 * z45 * c12 * c13 * c14 * c14 * c23 * c24 * c35 * c45 := by
    linear_combination (z13 * z14 * z14 * z23 * z35 * z45 * c12 * c13 * c15 * c23 * c24 * c35) * E1 - (z13 * z14 * z15 * z23 * z35 * z45 * c12 * c12 * c15 * c23 * c24 * c24) * E2 - (z13 * z13 * z14 * z15 * z35 * z45 * c12 * c14 * c23 * c24 * c24 * c45) * E3 + (z12 * z13 * z15 * z15 * z35 * z45 * c12 * c14 * c23 * c24 * c35 * c45) * E4
  have hmono : z14 * z14 * c15 * c15 * (z12 * z13 * z15 * z15 * z23 * z24 * z35 * z45 * c12 * c13 * c14 * c14 * c23 * c24 * c35 * c45) = z15 * z15 * c14 * c14 * (z12 * z13 * z14 * z14 * z23 * z24 * z35 * z45 * c12 * c13 * c15 * c15 * c23 * c24 * c35 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 4 個・係数 [-1, -1, 1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{05} - e_{15}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p5 - p0) / (p5 - p1)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem pentagonCert4 {z01 z04 z05 z12 z15 z24 z25 z45 c01 c04 c05 c12 c15 c24 c25 c45 : ℂ}
    (E1 : z04 * z24 * c05 * c25 = z05 * z25 * c04 * c24)
    (E2 : z01 * z15 * c04 * c45 = z04 * z45 * c01 * c15)
    (E3 : z12 * z24 * c15 * c45 = z15 * z45 * c12 * c24)
    (E4 : z01 * z05 * c12 * c25 = z12 * z25 * c01 * c05)
    (nz01 : z01 ≠ 0)
    (nz04 : z04 ≠ 0)
    (nz05 : z05 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz24 : z24 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz45 : z45 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc04 : c04 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc15 : c15 ≠ 0)
    (nc24 : c24 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc45 : c45 ≠ 0)
    : z05 * z05 * c15 * c15 = z15 * z15 * c05 * c05 := by
  have hL : z01 * z04 * z05 * z05 * z12 * z24 * z25 * z45 * c01 * c04 * c12 * c15 * c15 * c24 * c25 * c45 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz04)) (nz05)) (nz05)) (nz12)) (nz24)) (nz25)) (nz45)) (nc01)) (nc04)) (nc12)) (nc15)) (nc15)) (nc24)) (nc25)) (nc45)
  have hLR : z01 * z04 * z05 * z05 * z12 * z24 * z25 * z45 * c01 * c04 * c12 * c15 * c15 * c24 * c25 * c45 = z01 * z04 * z12 * z15 * z15 * z24 * z25 * z45 * c01 * c04 * c05 * c05 * c12 * c24 * c25 * c45 := by
    linear_combination - (z01 * z04 * z05 * z12 * z24 * z45 * c01 * c12 * c15 * c15 * c25 * c45) * E1 - (z01 * z04 * z05 * z12 * z24 * z24 * c05 * c12 * c15 * c25 * c25 * c45) * E2 + (z01 * z01 * z04 * z05 * z15 * z24 * c04 * c05 * c12 * c25 * c25 * c45) * E3 + (z01 * z04 * z15 * z15 * z24 * z45 * c04 * c05 * c12 * c24 * c25 * c45) * E4
  have hmono : z05 * z05 * c15 * c15 * (z01 * z04 * z12 * z15 * z15 * z24 * z25 * z45 * c01 * c04 * c05 * c05 * c12 * c24 * c25 * c45) = z15 * z15 * c05 * c05 * (z01 * z04 * z05 * z05 * z12 * z24 * z25 * z45 * c01 * c04 * c12 * c15 * c15 * c24 * c25 * c45) := by ring
  exact eq_of_cert hLR hmono hL

/-- 格子の所属の証明書（枡 4 個・係数 [1, -1, -1, 1]）を、15 本の差とその共役を**抽象の複素変数**に置き換えて書いたもの。`E1 …` は各枡の証人条件で、結論は共線形式 `e_{03} - e_{05}` の 2 倍が格子に入ることの幾何的な読み、すなわち `Im(W ^ 2) = 0`（`W = (p0 - p3) / (p0 - p5)`）にあたる等式である。`ring` は単項式しか見ない。 -/
theorem pentagonCert5 {z01 z02 z03 z05 z12 z13 z25 z35 c01 c02 c03 c05 c12 c13 c25 c35 : ℂ}
    (E1 : z01 * z13 * c05 * c35 = z05 * z35 * c01 * c13)
    (E2 : z02 * z25 * c03 * c35 = z03 * z35 * c02 * c25)
    (E3 : z01 * z05 * c12 * c25 = z12 * z25 * c01 * c05)
    (E4 : z02 * z03 * c12 * c13 = z12 * z13 * c02 * c03)
    (nz01 : z01 ≠ 0)
    (nz02 : z02 ≠ 0)
    (nz03 : z03 ≠ 0)
    (nz12 : z12 ≠ 0)
    (nz13 : z13 ≠ 0)
    (nz25 : z25 ≠ 0)
    (nz35 : z35 ≠ 0)
    (nc01 : c01 ≠ 0)
    (nc02 : c02 ≠ 0)
    (nc05 : c05 ≠ 0)
    (nc12 : c12 ≠ 0)
    (nc13 : c13 ≠ 0)
    (nc25 : c25 ≠ 0)
    (nc35 : c35 ≠ 0)
    : z03 * z03 * c05 * c05 = z05 * z05 * c03 * c03 := by
  have hL : z01 * z02 * z03 * z03 * z12 * z13 * z25 * z35 * c01 * c02 * c05 * c05 * c12 * c13 * c25 * c35 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (nz01) (nz02)) (nz03)) (nz03)) (nz12)) (nz13)) (nz25)) (nz35)) (nc01)) (nc02)) (nc05)) (nc05)) (nc12)) (nc13)) (nc25)) (nc35)
  have hLR : z01 * z02 * z03 * z03 * z12 * z13 * z25 * z35 * c01 * c02 * c05 * c05 * c12 * c13 * c25 * c35 = z01 * z02 * z05 * z05 * z12 * z13 * z25 * z35 * c01 * c02 * c03 * c03 * c12 * c13 * c25 * c35 := by
    linear_combination (z02 * z03 * z03 * z12 * z25 * z35 * c01 * c02 * c05 * c12 * c13 * c25) * E1 - (z02 * z03 * z05 * z12 * z25 * z35 * c01 * c01 * c05 * c12 * c13 * c13) * E2 - (z02 * z02 * z03 * z05 * z25 * z35 * c01 * c03 * c12 * c13 * c13 * c35) * E3 + (z01 * z02 * z05 * z05 * z25 * z35 * c01 * c03 * c12 * c13 * c25 * c35) * E4
  have hmono : z03 * z03 * c05 * c05 * (z01 * z02 * z05 * z05 * z12 * z13 * z25 * z35 * c01 * c02 * c03 * c03 * c12 * c13 * c25 * c35) = z05 * z05 * c03 * c03 * (z01 * z02 * z03 * z03 * z12 * z13 * z25 * z35 * c01 * c02 * c05 * c05 * c12 * c13 * c25 * c35) := by ring
  exact eq_of_cert hLR hmono hL

set_option maxHeartbeats 1000000 in
/-- **この枡の証人を持つ 6 点は一般の位置にない。**単因子が `1⁹, 2⁶` の別の類（15 枡）。位数 2 の共線形式は `(3;0,4), (4;1,3), (1;4,5), (5;0,1), (0;3,5)` の 5 本で、これは 5 点 `p₀, p₃, p₄, p₁, p₅` を巡る閉じた 5 角形の各頂点での直角である。 -/

theorem no_general_position_of_right_angled_pentagon (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 4) (p 5) (p 0) (p 2) = 0)
    (hw2 : Psi (p 1) (p 5) (p 0) (p 3) = 0)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw5 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 4) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (hw8 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (hw9 : Psi (p 0) (p 2) (p 1) (p 5) = 0)
    (hw10 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 0) (p 1) (p 2) (p 3) = 0)
    (hw12 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw13 : Psi (p 1) (p 3) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 1) (p 2) (p 3) (p 4) = 0)
    : False := by
  have hne := hgp.1
  have hcol := hgp.2.1
  have hsq1 : ((toC (p 3) - toC (p 0)) * (barC (p 3) - barC (p 4))) ^ 2
      = ((barC (p 3) - barC (p 0)) * (toC (p 3) - toC (p 4))) ^ 2 := by
    linear_combination pentagonCert1
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 2) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 2) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw12)
      (show (toC (p 0) - toC (p 3)) * (toC (p 0) - toC (p 4)) * (barC (p 3) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 3) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 0) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw14)
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr1 : qq (p 0) (p 4) (p 3) * cross (p 3) (p 0) (p 4) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq1
  have hc1 : cross (p 3) (p 0) (p 4) ≠ 0 := by
    have h0 : cross (p 0) (p 3) (p 4) ≠ 0 := by
      simpa [Collinear3] using hcol 0 3 4 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination -hx
  have ha1 : qq (p 0) (p 4) (p 3) = 0 := by
    rcases mul_eq_zero.mp hr1 with h | h
    · exact h
    · exact absurd h hc1
  have hsq2 : ((toC (p 4) - toC (p 1)) * (barC (p 4) - barC (p 3))) ^ 2
      = ((barC (p 4) - barC (p 1)) * (toC (p 4) - toC (p 3))) ^ 2 := by
    linear_combination pentagonCert2
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 3)) * (barC (p 0) - barC (p 4)) * (barC (p 3) - barC (p 4)) = (toC (p 0) - toC (p 4)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw3)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 2)) * (barC (p 1) - barC (p 4)) * (barC (p 2) - barC (p 4)) = (toC (p 1) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 2)) by linear_combination (1 : ℂ) * witnessEq hw6)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 4)) = (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 4)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw7)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 4)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 3 4 (by decide)))
  have hr2 : qq (p 1) (p 3) (p 4) * cross (p 4) (p 1) (p 3) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq2
  have hc2 : cross (p 4) (p 1) (p 3) ≠ 0 := by
    have h0 : cross (p 1) (p 3) (p 4) ≠ 0 := by
      simpa [Collinear3] using hcol 1 3 4 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination hx
  have ha2 : qq (p 1) (p 3) (p 4) = 0 := by
    rcases mul_eq_zero.mp hr2 with h | h
    · exact h
    · exact absurd h hc2
  have hsq3 : ((toC (p 1) - toC (p 4)) * (barC (p 1) - barC (p 5))) ^ 2
      = ((barC (p 1) - barC (p 4)) * (toC (p 1) - toC (p 5))) ^ 2 := by
    linear_combination pentagonCert3
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw8)
      (show (toC (p 1) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 3)) * (barC (p 3) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw10)
      (show (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 5)) * (barC (p 2) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 2) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw13)
      (show (toC (p 1) - toC (p 3)) * (toC (p 1) - toC (p 4)) * (barC (p 2) - barC (p 3)) * (barC (p 2) - barC (p 4)) = (toC (p 2) - toC (p 3)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 3)) * (barC (p 1) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw15)
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 1 4 (by decide)))
      (toC_sub_ne_zero (hne 2 3 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 3 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr3 : qq (p 4) (p 5) (p 1) * cross (p 1) (p 4) (p 5) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq3
  have hc3 : cross (p 1) (p 4) (p 5) ≠ 0 := by
    simpa [Collinear3] using hcol 1 4 5 (by decide) (by decide)
  have ha3 : qq (p 4) (p 5) (p 1) = 0 := by
    rcases mul_eq_zero.mp hr3 with h | h
    · exact h
    · exact absurd h hc3
  have hsq4 : ((toC (p 5) - toC (p 0)) * (barC (p 5) - barC (p 1))) ^ 2
      = ((barC (p 5) - barC (p 0)) * (toC (p 5) - toC (p 1))) ^ 2 := by
    linear_combination pentagonCert4
      (show (toC (p 0) - toC (p 4)) * (toC (p 2) - toC (p 4)) * (barC (p 0) - barC (p 5)) * (barC (p 2) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 2) - barC (p 4)) by linear_combination (1 : ℂ) * witnessEq hw1)
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 5)) * (barC (p 0) - barC (p 4)) * (barC (p 4) - barC (p 5)) = (toC (p 0) - toC (p 4)) * (toC (p 4) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw4)
      (show (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 4)) * (barC (p 1) - barC (p 5)) * (barC (p 4) - barC (p 5)) = (toC (p 1) - toC (p 5)) * (toC (p 4) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 4)) by linear_combination (-1 : ℂ) * witnessEq hw8)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) = (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 4 (by decide)))
      (toC_sub_ne_zero (hne 0 5 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 2 4 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 4 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 4 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 5 (by decide)))
      (barC_sub_ne_zero (hne 2 4 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 4 5 (by decide)))
  have hr4 : qq (p 0) (p 1) (p 5) * cross (p 5) (p 0) (p 1) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq4
  have hc4 : cross (p 5) (p 0) (p 1) ≠ 0 := by
    have h0 : cross (p 0) (p 1) (p 5) ≠ 0 := by
      simpa [Collinear3] using hcol 0 1 5 (by decide) (by decide)
    intro hx
    refine h0 ?_
    simp only [cross] at hx ⊢
    linear_combination hx
  have ha4 : qq (p 0) (p 1) (p 5) = 0 := by
    rcases mul_eq_zero.mp hr4 with h | h
    · exact h
    · exact absurd h hc4
  have hsq5 : ((toC (p 0) - toC (p 3)) * (barC (p 0) - barC (p 5))) ^ 2
      = ((barC (p 0) - barC (p 3)) * (toC (p 0) - toC (p 5))) ^ 2 := by
    linear_combination pentagonCert5
      (show (toC (p 0) - toC (p 1)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 5)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 5)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 1) - barC (p 3)) by linear_combination (-1 : ℂ) * witnessEq hw2)
      (show (toC (p 0) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 3)) * (barC (p 3) - barC (p 5)) = (toC (p 0) - toC (p 3)) * (toC (p 3) - toC (p 5)) * (barC (p 0) - barC (p 2)) * (barC (p 2) - barC (p 5)) by linear_combination (1 : ℂ) * witnessEq hw5)
      (show (toC (p 0) - toC (p 1)) * (toC (p 0) - toC (p 5)) * (barC (p 1) - barC (p 2)) * (barC (p 2) - barC (p 5)) = (toC (p 1) - toC (p 2)) * (toC (p 2) - toC (p 5)) * (barC (p 0) - barC (p 1)) * (barC (p 0) - barC (p 5)) by linear_combination (-1 : ℂ) * witnessEq hw9)
      (show (toC (p 0) - toC (p 2)) * (toC (p 0) - toC (p 3)) * (barC (p 1) - barC (p 2)) * (barC (p 1) - barC (p 3)) = (toC (p 1) - toC (p 2)) * (toC (p 1) - toC (p 3)) * (barC (p 0) - barC (p 2)) * (barC (p 0) - barC (p 3)) by linear_combination (1 : ℂ) * witnessEq hw11)
      (toC_sub_ne_zero (hne 0 1 (by decide)))
      (toC_sub_ne_zero (hne 0 2 (by decide)))
      (toC_sub_ne_zero (hne 0 3 (by decide)))
      (toC_sub_ne_zero (hne 1 2 (by decide)))
      (toC_sub_ne_zero (hne 1 3 (by decide)))
      (toC_sub_ne_zero (hne 2 5 (by decide)))
      (toC_sub_ne_zero (hne 3 5 (by decide)))
      (barC_sub_ne_zero (hne 0 1 (by decide)))
      (barC_sub_ne_zero (hne 0 2 (by decide)))
      (barC_sub_ne_zero (hne 0 5 (by decide)))
      (barC_sub_ne_zero (hne 1 2 (by decide)))
      (barC_sub_ne_zero (hne 1 3 (by decide)))
      (barC_sub_ne_zero (hne 2 5 (by decide)))
      (barC_sub_ne_zero (hne 3 5 (by decide)))
  have hr5 : qq (p 3) (p 5) (p 0) * cross (p 0) (p 3) (p 5) = 0 :=
    qq_mul_cross_eq_zero_of_sq_eq hsq5
  have hc5 : cross (p 0) (p 3) (p 5) ≠ 0 := by
    simpa [Collinear3] using hcol 0 3 5 (by decide) (by decide)
  have ha5 : qq (p 3) (p 5) (p 0) = 0 := by
    rcases mul_eq_zero.mp hr5 with h | h
    · exact h
    · exact absurd h hc5
  have e1 : (toC (p 3) - toC (p 0)) * (barC (p 4) - barC (p 3)) + (barC (p 3) - barC (p 0)) * (toC (p 4) - toC (p 3)) = 0 := by
    linear_combination -perp_poly ha1
  have e2 : (toC (p 4) - toC (p 3)) * (barC (p 1) - barC (p 4)) + (barC (p 4) - barC (p 3)) * (toC (p 1) - toC (p 4)) = 0 := by
    have h : qq (p 3) (p 1) (p 4) = 0 := by
      simp only [qq] at ha2 ⊢
      linear_combination ha2
    linear_combination -perp_poly h
  have e3 : (toC (p 1) - toC (p 4)) * (barC (p 5) - barC (p 1)) + (barC (p 1) - barC (p 4)) * (toC (p 5) - toC (p 1)) = 0 := by
    linear_combination -perp_poly ha3
  have e4 : (toC (p 5) - toC (p 1)) * (barC (p 0) - barC (p 5)) + (barC (p 5) - barC (p 1)) * (toC (p 0) - toC (p 5)) = 0 := by
    have h : qq (p 1) (p 0) (p 5) = 0 := by
      simp only [qq] at ha4 ⊢
      linear_combination ha4
    linear_combination -perp_poly h
  have e5 : (toC (p 0) - toC (p 5)) * (barC (p 3) - barC (p 0)) + (barC (p 0) - barC (p 5)) * (toC (p 3) - toC (p 0)) = 0 := by
    have h : qq (p 5) (p 3) (p 0) = 0 := by
      simp only [qq] at ha5 ⊢
      linear_combination ha5
    linear_combination -perp_poly h
  exact pentagon_absurd e1 e2 e3 e4 e5 (toC_sub_ne_zero (hne 0 3 (by decide)).symm) (toC_sub_ne_zero (hne 3 4 (by decide)).symm) (toC_sub_ne_zero (hne 1 4 (by decide))) (toC_sub_ne_zero (hne 1 5 (by decide)).symm) (barC_sub_ne_zero (hne 3 4 (by decide)).symm) (barC_sub_ne_zero (hne 1 4 (by decide))) (barC_sub_ne_zero (hne 1 5 (by decide)).symm) (barC_sub_ne_zero (hne 0 5 (by decide)))

/-- 同じことを、その類の 15 枡すべてを仮定にした形で書いたもの。 -/
theorem no_general_position_of_right_angled_pentagon_all (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hw1 : Psi (p 4) (p 5) (p 0) (p 2) = 0)
    (hw2 : Psi (p 1) (p 5) (p 0) (p 3) = 0)
    (hw3 : Psi (p 2) (p 4) (p 0) (p 3) = 0)
    (hw4 : Psi (p 1) (p 4) (p 0) (p 5) = 0)
    (hw5 : Psi (p 2) (p 3) (p 0) (p 5) = 0)
    (hw6 : Psi (p 0) (p 4) (p 1) (p 2) = 0)
    (hw7 : Psi (p 0) (p 3) (p 1) (p 4) = 0)
    (hw8 : Psi (p 2) (p 5) (p 1) (p 4) = 0)
    (hw9 : Psi (p 0) (p 2) (p 1) (p 5) = 0)
    (hw10 : Psi (p 3) (p 4) (p 1) (p 5) = 0)
    (hw11 : Psi (p 0) (p 1) (p 2) (p 3) = 0)
    (hw12 : Psi (p 3) (p 5) (p 2) (p 4) = 0)
    (hw13 : Psi (p 1) (p 3) (p 2) (p 5) = 0)
    (hw14 : Psi (p 0) (p 5) (p 3) (p 4) = 0)
    (hw15 : Psi (p 1) (p 2) (p 3) (p 4) = 0)
    : False :=
  no_general_position_of_right_angled_pentagon p hgp hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12 hw13 hw14 hw15

/-- The value of `cellPsi` at a cell whose index is known. -/
theorem cellPsi_eq {p : Fin 6 → Pt} {i : ℕ} {a b c d : Fin 6}
    (h : cellOf i = ((a, b), (c, d))) :
    cellPsi p i = Psi (p c) (p d) (p a) (p b) := by
  simp only [cellPsi, h]

/-! ## The direction classes, in the shape of the census -/

/-! ### Class 33 -/

/-- The mask of class 33 (entry 32 of `censusRest`). -/
def maskK33 : Mask := 20023461225293663191439364

/-- Class 33 is one of the thirty-four census representatives. -/
theorem maskK33_mem : maskK33 ∈ censusRest := by decide

/-- **Class 33, sharp form.**  No six points in general position support
the mask of class 33.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k33 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK33) : False := by
  have c2 : Psi (p 2) (p 5) (p 0) (p 1) = 0 := by
    have h := hs 2 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 2 = ((0, 1), (2, 5)) from by decide)] at h
  have c11 : Psi (p 4) (p 5) (p 0) (p 2) = 0 := by
    have h := hs 11 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 11 = ((0, 2), (4, 5)) from by decide)] at h
  have c12 : Psi (p 1) (p 2) (p 0) (p 3) = 0 := by
    have h := hs 12 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 12 = ((0, 3), (1, 2)) from by decide)] at h
  have c21 : Psi (p 2) (p 3) (p 0) (p 4) = 0 := by
    have h := hs 21 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 21 = ((0, 4), (2, 3)) from by decide)] at h
  have c29 : Psi (p 3) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 29 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 29 = ((0, 5), (3, 4)) from by decide)] at h
  have c31 : Psi (p 0) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 31 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 31 = ((1, 2), (0, 4)) from by decide)] at h
  have c38 : Psi (p 0) (p 5) (p 1) (p 3) = 0 := by
    have h := hs 38 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 38 = ((1, 3), (0, 5)) from by decide)] at h
  have c43 : Psi (p 0) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 43 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 43 = ((1, 4), (0, 3)) from by decide)] at h
  have c52 : Psi (p 2) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 52 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 52 = ((1, 5), (2, 4)) from by decide)] at h
  have c57 : Psi (p 1) (p 4) (p 2) (p 3) = 0 := by
    have h := hs 57 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 57 = ((2, 3), (1, 4)) from by decide)] at h
  have c65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have c69 : Psi (p 1) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 69 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 69 = ((2, 5), (1, 3)) from by decide)] at h
  have c76 : Psi (p 1) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 76 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 76 = ((3, 4), (1, 5)) from by decide)] at h
  have c79 : Psi (p 0) (p 2) (p 3) (p 5) = 0 := by
    have h := hs 79 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 79 = ((3, 5), (0, 2)) from by decide)] at h
  have c84 : Psi (p 0) (p 1) (p 4) (p 5) = 0 := by
    have h := hs 84 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 84 = ((4, 5), (0, 1)) from by decide)] at h
  exact no_general_position_of_right_angle_sum_all p hgp c2 c11 c12 c21 c29 c31 c38 c43 c52 c57 c65 c69 c76 c79 c84

/-- **Class 33.**  No six points in general position carry the mask of
class 33. -/
theorem not_carries_k33 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK33) : False :=
  not_supports_k33 p hgp (supports_of_carries hc)

/-! ### Class 11 -/

/-- The mask of class 11 (entry 10 of `censusRest`). -/
def maskK11 : Mask := 57295614475181794314240

/-- Class 11 is one of the thirty-four census representatives. -/
theorem maskK11_mem : maskK11 ∈ censusRest := by decide

/-- **Class 11, sharp form.**  No six points in general position support
the mask of class 11.  All fifteen cells of the mask are used and no cell
outside it is needed. -/
theorem not_supports_k11 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hs : Supports p maskK11) : False := by
  have c11 : Psi (p 4) (p 5) (p 0) (p 2) = 0 := by
    have h := hs 11 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 11 = ((0, 2), (4, 5)) from by decide)] at h
  have c14 : Psi (p 1) (p 5) (p 0) (p 3) = 0 := by
    have h := hs 14 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 14 = ((0, 3), (1, 5)) from by decide)] at h
  have c15 : Psi (p 2) (p 4) (p 0) (p 3) = 0 := by
    have h := hs 15 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 15 = ((0, 3), (2, 4)) from by decide)] at h
  have c26 : Psi (p 1) (p 4) (p 0) (p 5) = 0 := by
    have h := hs 26 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 26 = ((0, 5), (1, 4)) from by decide)] at h
  have c27 : Psi (p 2) (p 3) (p 0) (p 5) = 0 := by
    have h := hs 27 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 27 = ((0, 5), (2, 3)) from by decide)] at h
  have c31 : Psi (p 0) (p 4) (p 1) (p 2) = 0 := by
    have h := hs 31 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 31 = ((1, 2), (0, 4)) from by decide)] at h
  have c43 : Psi (p 0) (p 3) (p 1) (p 4) = 0 := by
    have h := hs 43 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 43 = ((1, 4), (0, 3)) from by decide)] at h
  have c46 : Psi (p 2) (p 5) (p 1) (p 4) = 0 := by
    have h := hs 46 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 46 = ((1, 4), (2, 5)) from by decide)] at h
  have c48 : Psi (p 0) (p 2) (p 1) (p 5) = 0 := by
    have h := hs 48 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 48 = ((1, 5), (0, 2)) from by decide)] at h
  have c53 : Psi (p 3) (p 4) (p 1) (p 5) = 0 := by
    have h := hs 53 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 53 = ((1, 5), (3, 4)) from by decide)] at h
  have c54 : Psi (p 0) (p 1) (p 2) (p 3) = 0 := by
    have h := hs 54 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 54 = ((2, 3), (0, 1)) from by decide)] at h
  have c65 : Psi (p 3) (p 5) (p 2) (p 4) = 0 := by
    have h := hs 65 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 65 = ((2, 4), (3, 5)) from by decide)] at h
  have c69 : Psi (p 1) (p 3) (p 2) (p 5) = 0 := by
    have h := hs 69 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 69 = ((2, 5), (1, 3)) from by decide)] at h
  have c74 : Psi (p 0) (p 5) (p 3) (p 4) = 0 := by
    have h := hs 74 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 74 = ((3, 4), (0, 5)) from by decide)] at h
  have c75 : Psi (p 1) (p 2) (p 3) (p 4) = 0 := by
    have h := hs 75 (by norm_num) (by decide)
    rwa [cellPsi_eq (show cellOf 75 = ((3, 4), (1, 2)) from by decide)] at h
  exact no_general_position_of_right_angled_pentagon_all p hgp c11 c14 c15 c26 c27 c31 c43 c46 c48 c53 c54 c65 c69 c74 c75

/-- **Class 11.**  No six points in general position carry the mask of
class 11. -/
theorem not_carries_k11 (p : Fin 6 → Pt) (hgp : GeneralPosition p)
    (hc : Carries p maskK11) : False :=
  not_supports_k11 p hgp (supports_of_carries hc)



end QU2

end DistinctCircumradii

#print axioms DistinctCircumradii.QU2.eq_of_cert
#print axioms DistinctCircumradii.QU2.sqdist_nonneg
#print axioms DistinctCircumradii.QU2.qq_comm
#print axioms DistinctCircumradii.QU2.perp_poly
#print axioms DistinctCircumradii.QU2.pentagon_absurd
#print axioms DistinctCircumradii.QU2.rightAngleCert1
#print axioms DistinctCircumradii.QU2.rightAngleCert2
#print axioms DistinctCircumradii.QU2.rightAngleCert3
#print axioms DistinctCircumradii.QU2.rightAngleCert4
#print axioms DistinctCircumradii.QU2.rightAngleCert5
#print axioms DistinctCircumradii.QU2.no_general_position_of_right_angle_sum
#print axioms DistinctCircumradii.QU2.no_general_position_of_right_angle_sum_all
#print axioms DistinctCircumradii.QU2.pentagonCert1
#print axioms DistinctCircumradii.QU2.pentagonCert2
#print axioms DistinctCircumradii.QU2.pentagonCert3
#print axioms DistinctCircumradii.QU2.pentagonCert4
#print axioms DistinctCircumradii.QU2.pentagonCert5
#print axioms DistinctCircumradii.QU2.no_general_position_of_right_angled_pentagon
#print axioms DistinctCircumradii.QU2.no_general_position_of_right_angled_pentagon_all
#print axioms DistinctCircumradii.QU2.cellPsi_eq
#print axioms DistinctCircumradii.QU2.maskK33_mem
#print axioms DistinctCircumradii.QU2.not_supports_k33
#print axioms DistinctCircumradii.QU2.not_carries_k33
#print axioms DistinctCircumradii.QU2.maskK11_mem
#print axioms DistinctCircumradii.QU2.not_supports_k11
#print axioms DistinctCircumradii.QU2.not_carries_k11
