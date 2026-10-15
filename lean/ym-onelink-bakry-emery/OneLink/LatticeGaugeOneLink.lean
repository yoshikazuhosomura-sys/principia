/-
格子ゲージ理論の一リンク積分：star の純代数の不等式から、四元数の staple 曲線・Bessel 型の級数・
周期格子の完全な族・staple の摂動を経て、Wilson 作用の star 分解と一リンク積分までを一本にまとめた版。
Mathlib だけを読み込んで検査できる。
-/
import Mathlib

-- ===== 純代数から staple の摂動まで =====
section PerturbationPart


-- ===== 純代数から周期格子の完全な族まで =====
section LatticePart

-- ===== star の純代数と四元数の staple 曲線 =====
section AlgebraPart
/-
star の純代数の不等式（`StarInequality`）と、四元数 `ℍ[ℝ]` の上の staple 曲線の二階微分（`StapleCurve`）。
-/


-- ===== 平方和の恒等式 =====
/-
staple ごとの平方和の恒等式（実数 13 変数）。
  18n − c|Y|² − 2⟨v,W⟩ = |3P − (Z×v)/6|² + ⟨Z,v⟩²/36 + (27−μ)|b − kY|² + R|Y|²
  Y = a+b+c', P = a−c', Z = Y+b, W = a×b + a×c' + b×c',
  μ = |v|²/36, k = (9+μ)/(27−μ), R = 9 − c − μ − (9+μ)²/(27−μ).
E1・E2 の二つの恒等式に分ける（係数は計算機代数で恒等式であることを確かめた形）。
-/

namespace StarInequality

/-- E1：`W = ½ P × Z`（成分ごと）。 -/
theorem W_eq_half_P_cross_Z (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2)
        = ((a2-c2)*((a3+b3+c3)+b3) - (a3-c3)*((a2+b2+c2)+b2)) / 2) ∧
    ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3)
        = ((a3-c3)*((a1+b1+c1)+b1) - (a1-c1)*((a3+b3+c3)+b3)) / 2) ∧
    ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)
        = ((a1-c1)*((a2+b2+c2)+b2) - (a2-c2)*((a1+b1+c1)+b1)) / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- E2 の多項式部分（割り算は数 36・6 だけ）：`(27−μ)|b−kY|² + R|Y|²` を展開した形。 -/
theorem staple_sos_poly (a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ : ℝ)
    (hμ : μ = (v1^2 + v2^2 + v3^2) / 36) :
    18 * ((a1^2+a2^2+a3^2) + (b1^2+b2^2+b3^2) + (c1^2+c2^2+c3^2))
      - c * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2)
      - 2 * (v1 * ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2))
           + v2 * ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3))
           + v3 * ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)))
    = ( (3*(a1-c1) - (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2)/6)^2
      + (3*(a2-c2) - (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3)/6)^2
      + (3*(a3-c3) - (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1)/6)^2 )
      + (((a1+b1+c1)+b1)*v1 + ((a2+b2+c2)+b2)*v2 + ((a3+b3+c3)+b3)*v3)^2 / 36
      + (27 - μ) * (b1^2 + b2^2 + b3^2)
      - 2 * (9 + μ) * (b1*(a1+b1+c1) + b2*(a2+b2+c2) + b3*(a3+b3+c3))
      + (9 - c - μ) * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2) := by
  subst hμ
  ring

/-- E2：staple ごとの平方和の恒等式。`μ = |v|²/36`・`m = 27 − μ ≠ 0`。 -/
theorem staple_sos (a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ : ℝ)
    (hμ : μ = (v1^2 + v2^2 + v3^2) / 36) (hm : 27 - μ ≠ 0) :
    18 * ((a1^2+a2^2+a3^2) + (b1^2+b2^2+b3^2) + (c1^2+c2^2+c3^2))
      - c * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2)
      - 2 * (v1 * ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2))
           + v2 * ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3))
           + v3 * ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)))
    = ( (3*(a1-c1) - (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2)/6)^2
      + (3*(a2-c2) - (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3)/6)^2
      + (3*(a3-c3) - (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1)/6)^2 )
      + (((a1+b1+c1)+b1)*v1 + ((a2+b2+c2)+b2)*v2 + ((a3+b3+c3)+b3)*v3)^2 / 36
      + (27 - μ) * ( (b1 - (9+μ)/(27-μ) * (a1+b1+c1))^2
                   + (b2 - (9+μ)/(27-μ) * (a2+b2+c2))^2
                   + (b3 - (9+μ)/(27-μ) * (a3+b3+c3))^2 )
      + (9 - c - μ - (9+μ)^2/(27-μ))
          * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2) := by
  have hk : ∀ b y : ℝ, (27 - μ) * (b - (9+μ)/(27-μ) * y)^2
      = (27 - μ) * b^2 - 2 * (9+μ) * (b * y) + (9+μ)^2/(27-μ) * y^2 := by
    intro b y
    field_simp
    ring
  rw [staple_sos_poly a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ hμ]
  linear_combination (-1 : ℝ) * (hk b1 (a1+b1+c1)) - hk b2 (a2+b2+c2) - hk b3 (a3+b3+c3)

end StarInequality

#print axioms StarInequality.W_eq_half_P_cross_Z
#print axioms StarInequality.staple_sos_poly
#print axioms StarInequality.staple_sos


-- ===== `R ≥ 0` と staple ごとの不等式 =====
/-
`R ≥ 0` の符号と、staple ごとの不等式（実数成分）。
  c₀ := 6 − 36μ/(6−p) のとき (27−μ)R = 12μ(57 − 3μ + 4p)/(6−p)（計算機代数で確かめた恒等式）。
  範囲：−6 ≤ p < 6・0 ≤ μ ≤ 1。`R` は `c` について減少なので `c ≤ c₀` で足りる。
-/

namespace StarInequality

/-- `(27−μ)R` の閉じた形（`c = 6 − 36μ/(6−p)`）。 -/
theorem R_closed (p μ : ℝ) (hp : 6 - p ≠ 0) (hm : 27 - μ ≠ 0) :
    (27 - μ) * (9 - (6 - 36*μ/(6-p)) - μ - (9+μ)^2/(27-μ))
      = 12 * μ * (57 - 3*μ + 4*p) / (6 - p) := by
  field_simp
  ring

/-- L3：`R ≥ 0`。 -/
theorem R_nonneg (p μ c : ℝ) (hp1 : -6 ≤ p) (hp2 : p < 6) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hc : c ≤ 6 - 36*μ/(6-p)) :
    0 ≤ 9 - c - μ - (9+μ)^2/(27-μ) := by
  have h6 : 0 < 6 - p := by linarith
  have h27 : 0 < 27 - μ := by linarith
  have hcl := R_closed p μ h6.ne' h27.ne'
  have hnum : 0 ≤ 12 * μ * (57 - 3*μ + 4*p) / (6 - p) := by
    apply div_nonneg _ h6.le
    have : 0 ≤ 57 - 3*μ + 4*p := by linarith
    positivity
  have h0 : 0 ≤ 9 - (6 - 36*μ/(6-p)) - μ - (9+μ)^2/(27-μ) := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_pos_of_neg h27 hneg
    linarith
  linarith

/-- staple ごとの不等式（成分）：`c|Y|² + 2⟨v,W⟩ ≤ 18 n`。 -/
theorem staple_ineq (a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c p : ℝ)
    (hp1 : -6 ≤ p) (hp2 : p < 6) (hv : v1^2 + v2^2 + v3^2 ≤ 36)
    (hc : c ≤ 6 - (v1^2 + v2^2 + v3^2)/(6-p)) :
    c * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2)
      + 2 * (v1 * ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2))
           + v2 * ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3))
           + v3 * ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)))
    ≤ 18 * ((a1^2+a2^2+a3^2) + (b1^2+b2^2+b3^2) + (c1^2+c2^2+c3^2)) := by
  set μ : ℝ := (v1^2 + v2^2 + v3^2) / 36 with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμ1 : μ ≤ 1 := by rw [hμ]; linarith
  have h27 : 0 < 27 - μ := by linarith
  have hc' : c ≤ 6 - 36*μ/(6-p) := by
    have : 36 * μ = v1^2 + v2^2 + v3^2 := by rw [hμ]; ring
    rw [this]; exact hc
  have hR := R_nonneg p μ c hp1 hp2 hμ0 hμ1 hc'
  have hsos := staple_sos a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ hμ h27.ne'
  have hY : 0 ≤ (a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2 := by positivity
  have h3 : 0 ≤ (27 - μ) * ( (b1 - (9+μ)/(27-μ) * (a1+b1+c1))^2
                   + (b2 - (9+μ)/(27-μ) * (a2+b2+c2))^2
                   + (b3 - (9+μ)/(27-μ) * (a3+b3+c3))^2 ) :=
    mul_nonneg h27.le (by positivity)
  have h4 := mul_nonneg hR hY
  have h1 : 0 ≤ ( (3*(a1-c1) - (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2)/6)^2
      + (3*(a2-c2) - (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3)/6)^2
      + (3*(a3-c3) - (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1)/6)^2 ) := by positivity
  have h2 : 0 ≤ (((a1+b1+c1)+b1)*v1 + ((a2+b2+c2)+b2)*v2 + ((a3+b3+c3)+b3)*v3)^2 / 36 := by
    positivity
  linarith

end StarInequality

#print axioms StarInequality.R_closed
#print axioms StarInequality.R_nonneg
#print axioms StarInequality.staple_ineq


-- ===== 重みつき Cauchy–Schwarz =====
/-
重みつき Cauchy–Schwarz `‖Σu_i‖² ≤ Σ‖u_i‖²/λ_i`（`λ_i > 0`・`Σλ_i = 1`）
と、staple ごとの不等式のベクトル形（`Fin 3 → ℝ`・`⬝ᵥ`・`⨯₃`）。
-/

open Matrix

namespace StarInequality

/-- L1：重みつき Cauchy–Schwarz（Sedrakyan の形）。 -/
theorem weighted_cs {ι E : Type*} [SeminormedAddCommGroup E] (S : Finset ι)
    (u : ι → E) (lam : ι → ℝ) (hpos : ∀ i ∈ S, 0 < lam i) (hsum : ∑ i ∈ S, lam i = 1) :
    ‖∑ i ∈ S, u i‖ ^ 2 ≤ ∑ i ∈ S, ‖u i‖ ^ 2 / lam i := by
  have h1 : ‖∑ i ∈ S, u i‖ ^ 2 ≤ (∑ i ∈ S, ‖u i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S u) 2
  have h2 := Finset.sq_sum_div_le_sum_sq_div S (fun i => ‖u i‖) hpos
  rw [hsum, div_one] at h2
  exact h1.trans h2

theorem dot3 (x y : Fin 3 → ℝ) : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [dotProduct, Fin.sum_univ_three]

theorem dot3_self_nonneg (x : Fin 3 → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [dot3]; nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]

/-- staple ごとの不等式（ベクトル形）。 -/
theorem staple_ineq_vec (a b c v : Fin 3 → ℝ) (cc p : ℝ)
    (hp1 : -6 ≤ p) (hp2 : p < 6) (hv : v ⬝ᵥ v ≤ 36)
    (hc : cc ≤ 6 - (v ⬝ᵥ v) / (6 - p)) :
    cc * ((a + b + c) ⬝ᵥ (a + b + c)) + 2 * (v ⬝ᵥ (a ⨯₃ b + a ⨯₃ c + b ⨯₃ c))
      ≤ 18 * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c) := by
  have hvv : v ⬝ᵥ v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by rw [dot3]; ring
  rw [hvv] at hv hc
  have key := staple_ineq (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) (c 0) (c 1) (c 2)
    (v 0) (v 1) (v 2) cc p hp1 hp2 hv hc
  simp only [dot3, cross_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linarith [key]

end StarInequality

#print axioms StarInequality.weighted_cs
#print axioms StarInequality.staple_ineq_vec


-- ===== 定理 S（純代数） =====
/-
組み立て——定理 S（純代数・`n = 6`）。
`s_i` は実内積空間 `E` の単位ベクトル（`E = ℝ⁴` に限らない）・`u_i ∈ E`・
`a_i, b_i, c_i, v_i : Fin 3 → ℝ`。
-/

open Matrix

namespace StarInequality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 定理 S。 -/
theorem star_S (s u : Fin 6 → E) (a b c v : Fin 6 → Fin 3 → ℝ)
    (hs : ∀ i, ‖s i‖ = 1)
    (hu : ∀ i, ‖u i‖ ^ 2 ≤ (a i + b i + c i) ⬝ᵥ (a i + b i + c i))
    (hv : ∀ i, v i ⬝ᵥ v i ≤ ‖∑ j, s j‖ ^ 2 - inner ℝ (s i) (∑ j, s j) ^ 2) :
    ‖∑ i, u i‖ ^ 2
      - ∑ i, inner ℝ (s i) (∑ j, s j) * ((a i + b i + c i) ⬝ᵥ (a i + b i + c i))
      + 2 * ∑ i, v i ⬝ᵥ (a i ⨯₃ b i + a i ⨯₃ c i + b i ⨯₃ c i)
    ≤ 18 * ∑ i, (a i ⬝ᵥ a i + b i ⬝ᵥ b i + c i ⬝ᵥ c i) := by
  set M : E := ∑ j, s j with hM
  set p : Fin 6 → ℝ := fun i => inner ℝ (s i) M with hp
  set yy : Fin 6 → ℝ := fun i => (a i + b i + c i) ⬝ᵥ (a i + b i + c i) with hyy
  set w : Fin 6 → ℝ := fun i => v i ⬝ᵥ (a i ⨯₃ b i + a i ⨯₃ c i + b i ⨯₃ c i) with hw
  set n : Fin 6 → ℝ := fun i => a i ⬝ᵥ a i + b i ⬝ᵥ b i + c i ⬝ᵥ c i with hn
  change ‖∑ i, u i‖ ^ 2 - ∑ i, p i * yy i + 2 * ∑ i, w i ≤ 18 * ∑ i, n i
  have hyy0 : ∀ i, 0 ≤ yy i := fun i => dot3_self_nonneg _
  have hn0 : ∀ i, 0 ≤ n i := fun i =>
    add_nonneg (add_nonneg (dot3_self_nonneg _) (dot3_self_nonneg _)) (dot3_self_nonneg _)
  -- Σ p_i = t
  have hsum_p : ∑ i, p i = ‖M‖ ^ 2 := by
    simp only [hp]
    rw [← sum_inner, ← hM, real_inner_self_eq_norm_sq]
  -- ‖M‖ ≤ 6
  have hM6 : ‖M‖ ≤ 6 := by
    have h := norm_sum_le Finset.univ s
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [hM]; norm_num at h; exact h
  have hM0 : 0 ≤ ‖M‖ := norm_nonneg _
  -- |p_i| ≤ ‖M‖
  have hp_abs : ∀ i, |p i| ≤ ‖M‖ := by
    intro i
    have h := abs_real_inner_le_norm (s i) M
    rw [hs i, one_mul] at h
    exact h
  have hp_le : ∀ i, p i ≤ ‖M‖ := fun i => (le_abs_self _).trans (hp_abs i)
  have hp_ge : ∀ i, -6 ≤ p i := fun i => by
    have := neg_abs_le (p i); have := hp_abs i; linarith
  have ht36 : ‖M‖ ^ 2 ≤ 36 := by nlinarith
  have hvle : ∀ i, v i ⬝ᵥ v i ≤ ‖M‖ ^ 2 - p i ^ 2 := hv
  rcases lt_or_eq_of_le hM6 with hlt | heq
  · -- t < 36
    have ht : 0 < 36 - ‖M‖ ^ 2 := by nlinarith
    have hp6 : ∀ i, 0 < 6 - p i := fun i => by have := hp_le i; linarith
    set lam : Fin 6 → ℝ := fun i => (6 - p i) / (36 - ‖M‖ ^ 2) with hlam
    have hlam_pos : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 0 < lam i :=
      fun i _ => div_pos (hp6 i) ht
    have hlam_sum : ∑ i, lam i = 1 := by
      simp only [hlam]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum_p]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_eq_one_iff_eq ht.ne']
      norm_num
    have hcs := weighted_cs Finset.univ u lam hlam_pos hlam_sum
    have hterm : ∀ i, ‖u i‖ ^ 2 / lam i - p i * yy i + 2 * w i ≤ 18 * n i := by
      intro i
      have hl : 0 < lam i := hlam_pos i (Finset.mem_univ i)
      have h1 : ‖u i‖ ^ 2 / lam i ≤ yy i / lam i := div_le_div_of_nonneg_right (hu i) hl.le
      have hinv : yy i / lam i = ((36 - ‖M‖ ^ 2) / (6 - p i)) * yy i := by
        simp only [hlam]
        have := (hp6 i).ne'
        field_simp
      have hvi : v i ⬝ᵥ v i ≤ 36 := by
        have := hvle i; nlinarith [sq_nonneg (p i)]
      have hcc : (36 - ‖M‖ ^ 2) / (6 - p i) - p i ≤ 6 - (v i ⬝ᵥ v i) / (6 - p i) := by
        have hne := (hp6 i).ne'
        have e : (36 - ‖M‖ ^ 2) / (6 - p i) - p i
            = 6 - (‖M‖ ^ 2 - p i ^ 2) / (6 - p i) := by
          field_simp
          ring
        rw [e]
        have := div_le_div_of_nonneg_right (hvle i) (hp6 i).le
        linarith
      have hst := staple_ineq_vec (a i) (b i) (c i) (v i)
        ((36 - ‖M‖ ^ 2) / (6 - p i) - p i) (p i) (hp_ge i) (by have := hp6 i; linarith) hvi hcc
      change ((36 - ‖M‖ ^ 2) / (6 - p i) - p i) * yy i + 2 * w i ≤ 18 * n i at hst
      rw [hinv] at h1
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    linarith
  · -- t = 36：全 p_i = 6・v_i = 0
    have hp6 : ∀ i, p i = 6 := by
      intro i
      by_contra hne
      have hlt : p i < 6 := lt_of_le_of_ne (by have := hp_le i; linarith) hne
      have hslt : ∑ j, p j < ∑ _j : Fin 6, (6 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => by have := hp_le j; linarith) ⟨i, Finset.mem_univ i, hlt⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hslt
      rw [hsum_p, heq] at hslt
      norm_num at hslt
    have hv0 : ∀ i, v i = 0 := by
      intro i
      have h1 := hvle i
      rw [hp6 i, heq] at h1
      have h2 : v i ⬝ᵥ v i = 0 := le_antisymm (by linarith) (dot3_self_nonneg _)
      exact dotProduct_self_eq_zero.mp h2
    have hw0 : ∀ i, w i = 0 := fun i => by simp only [hw, hv0 i, zero_dotProduct]
    have hcs := weighted_cs Finset.univ u (fun _ : Fin 6 => (1 / 6 : ℝ))
      (fun _ _ => by norm_num)
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
    have hterm : ∀ i, ‖u i‖ ^ 2 / (1 / 6 : ℝ) ≤ 6 * yy i := by
      intro i
      have := hu i
      rw [div_div_eq_mul_div, div_one]
      change ‖u i‖ ^ 2 ≤ yy i at this
      linarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hterm i)
    rw [← Finset.mul_sum] at hsum
    have hpy : ∑ i, p i * yy i = 6 * ∑ i, yy i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [hp6 i])
    have hwz : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => hw0 i)
    have hnn : 0 ≤ ∑ i, n i := Finset.sum_nonneg (fun i _ => hn0 i)
    rw [hpy, hwz]
    linarith

end StarInequality

#print axioms StarInequality.star_S


-- ===== staple が `n` 本の版の部品 =====
/-
staple が `n` 本の版の部品（`n > 0` は実数）。
  3n·nn − c|Y|² − 2⟨v,W⟩ = (r/6)|3nP − Z×v|² + (r/6)⟨Z,v⟩² + (9n/2−μ)|b − kY|² + R|Y|²
  r = 1/n・μ = r|v|²/6・k = (3n/2+μ)/(9n/2−μ)・R = 3n/2 − c − μ − (3n/2+μ)²/(9n/2−μ)
一般の `n` の版の恒等式（計算機代数で確かめた形）。`√` を避けるため第一項を (1/(6n))|3nP − Z×v|² と書いた。
-/

open Matrix

namespace StarInequality

theorem staple_sos_poly_gen (a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ n r : ℝ)
    (hr : n * r = 1) (hμ : μ = r * (v1^2 + v2^2 + v3^2) / 6) :
    3 * n * ((a1^2+a2^2+a3^2) + (b1^2+b2^2+b3^2) + (c1^2+c2^2+c3^2))
      - c * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2)
      - 2 * (v1 * ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2))
           + v2 * ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3))
           + v3 * ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)))
    = r / 6 * ( (3*n*(a1-c1) - (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2))^2
      + (3*n*(a2-c2) - (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3))^2
      + (3*n*(a3-c3) - (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1))^2 )
      + r / 6 * (((a1+b1+c1)+b1)*v1 + ((a2+b2+c2)+b2)*v2 + ((a3+b3+c3)+b3)*v3)^2
      + (9*n/2 - μ) * (b1^2 + b2^2 + b3^2)
      - 2 * (3*n/2 + μ) * (b1*(a1+b1+c1) + b2*(a2+b2+c2) + b3*(a3+b3+c3))
      + (3*n/2 - c - μ) * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2) := by
  subst hμ
  linear_combination
    ( (a1-c1) * (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2)
    + (a2-c2) * (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3)
    + (a3-c3) * (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1)
    - 3 * n / 2 * ((a1-c1)^2 + (a2-c2)^2 + (a3-c3)^2) ) * hr

theorem sq_complete (m q b y : ℝ) (hm : m ≠ 0) :
    m * (b - q / m * y)^2 = m * b^2 - 2 * q * (b * y) + q^2 / m * y^2 := by
  field_simp
  ring

theorem R_closed_gen (p μ n : ℝ) (hp : n - p ≠ 0) (hm : 9*n/2 - μ ≠ 0) :
    (9*n/2 - μ) * (3*n/2 - (n - 6*n*μ/(n-p)) - μ - (3*n/2+μ)^2/(9*n/2-μ))
      = 2 * n * μ * (19*n/2 + 4*p - 3*μ) / (n - p) := by
  have hm2 : n * 9 - μ * 2 ≠ 0 := fun h => hm (by linarith)
  have e : (9*n/2 - μ) = (n * 9 - μ * 2) / 2 := by ring
  rw [e]
  field_simp
  ring

theorem R_nonneg_gen (p μ c n : ℝ) (hn : 0 < n) (hp1 : -n ≤ p) (hp2 : p < n)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ n / 6) (hc : c ≤ n - 6*n*μ/(n-p)) :
    0 ≤ 3*n/2 - c - μ - (3*n/2+μ)^2/(9*n/2-μ) := by
  have h6 : 0 < n - p := by linarith
  have h27 : 0 < 9*n/2 - μ := by linarith
  have hcl := R_closed_gen p μ n h6.ne' h27.ne'
  have hnum : 0 ≤ 2 * n * μ * (19*n/2 + 4*p - 3*μ) / (n - p) := by
    apply div_nonneg _ h6.le
    have : 0 ≤ 19*n/2 + 4*p - 3*μ := by linarith
    positivity
  have h0 : 0 ≤ 3*n/2 - (n - 6*n*μ/(n-p)) - μ - (3*n/2+μ)^2/(9*n/2-μ) := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_pos_of_neg h27 hneg
    linarith
  linarith

/-- staple ごとの不等式（`n` 本版・成分）：`c|Y|² + 2⟨v,W⟩ ≤ 3n·nn`。 -/
theorem staple_ineq_gen (a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c p n : ℝ) (hn : 0 < n)
    (hp1 : -n ≤ p) (hp2 : p < n) (hv : v1^2 + v2^2 + v3^2 ≤ n^2)
    (hc : c ≤ n - (v1^2 + v2^2 + v3^2)/(n-p)) :
    c * ((a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2)
      + 2 * (v1 * ((a2*b3 - a3*b2) + (a2*c3 - a3*c2) + (b2*c3 - b3*c2))
           + v2 * ((a3*b1 - a1*b3) + (a3*c1 - a1*c3) + (b3*c1 - b1*c3))
           + v3 * ((a1*b2 - a2*b1) + (a1*c2 - a2*c1) + (b1*c2 - b2*c1)))
    ≤ 3 * n * ((a1^2+a2^2+a3^2) + (b1^2+b2^2+b3^2) + (c1^2+c2^2+c3^2)) := by
  have hr : n * n⁻¹ = 1 := mul_inv_cancel₀ hn.ne'
  have hr0 : 0 < n⁻¹ := inv_pos.mpr hn
  set r : ℝ := n⁻¹ with hrdef
  set μ : ℝ := r * (v1^2 + v2^2 + v3^2) / 6 with hμ
  have hvv : 0 ≤ v1^2 + v2^2 + v3^2 := by positivity
  have hμ0 : 0 ≤ μ := by positivity
  have h6nμ : 6 * n * μ = v1^2 + v2^2 + v3^2 := by
    rw [hμ]; linear_combination (v1^2 + v2^2 + v3^2) * hr
  have hμ1 : μ ≤ n / 6 := by nlinarith
  have h27 : 0 < 9*n/2 - μ := by linarith
  have hc' : c ≤ n - 6*n*μ/(n-p) := by rw [h6nμ]; exact hc
  have hR := R_nonneg_gen p μ c n hn hp1 hp2 hμ0 hμ1 hc'
  have hpoly := staple_sos_poly_gen a1 a2 a3 b1 b2 b3 c1 c2 c3 v1 v2 v3 c μ n r hr hμ
  have hk : ∀ b y : ℝ, (9*n/2 - μ) * (b - (3*n/2+μ)/(9*n/2-μ) * y)^2
      = (9*n/2 - μ) * b^2 - 2 * (3*n/2+μ) * (b * y) + (3*n/2+μ)^2/(9*n/2-μ) * y^2 :=
    fun b y => sq_complete (9*n/2 - μ) (3*n/2+μ) b y h27.ne'
  have hY : 0 ≤ (a1+b1+c1)^2 + (a2+b2+c2)^2 + (a3+b3+c3)^2 := by positivity
  have h4 := mul_nonneg hR hY
  have k1 := mul_nonneg h27.le (sq_nonneg (b1 - (3*n/2+μ)/(9*n/2-μ) * (a1+b1+c1)))
  have k2 := mul_nonneg h27.le (sq_nonneg (b2 - (3*n/2+μ)/(9*n/2-μ) * (a2+b2+c2)))
  have k3 := mul_nonneg h27.le (sq_nonneg (b3 - (3*n/2+μ)/(9*n/2-μ) * (a3+b3+c3)))
  rw [hk] at k1 k2 k3
  have h1 : 0 ≤ r / 6 * ( (3*n*(a1-c1) - (((a2+b2+c2)+b2)*v3 - ((a3+b3+c3)+b3)*v2))^2
      + (3*n*(a2-c2) - (((a3+b3+c3)+b3)*v1 - ((a1+b1+c1)+b1)*v3))^2
      + (3*n*(a3-c3) - (((a1+b1+c1)+b1)*v2 - ((a2+b2+c2)+b2)*v1))^2 ) := by positivity
  have h2 : 0 ≤ r / 6 * (((a1+b1+c1)+b1)*v1 + ((a2+b2+c2)+b2)*v2 + ((a3+b3+c3)+b3)*v3)^2 := by
    positivity
  linarith

/-- staple ごとの不等式（`n` 本版・ベクトル形）。 -/
theorem staple_ineq_vec_gen (a b c v : Fin 3 → ℝ) (cc p n : ℝ) (hn : 0 < n)
    (hp1 : -n ≤ p) (hp2 : p < n) (hv : v ⬝ᵥ v ≤ n ^ 2)
    (hc : cc ≤ n - (v ⬝ᵥ v) / (n - p)) :
    cc * ((a + b + c) ⬝ᵥ (a + b + c)) + 2 * (v ⬝ᵥ (a ⨯₃ b + a ⨯₃ c + b ⨯₃ c))
      ≤ 3 * n * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c) := by
  have hvv : v ⬝ᵥ v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by rw [dot3]; ring
  rw [hvv] at hv hc
  have key := staple_ineq_gen (a 0) (a 1) (a 2) (b 0) (b 1) (b 2) (c 0) (c 1) (c 2)
    (v 0) (v 1) (v 2) cc p n hn hp1 hp2 hv hc
  simp only [dot3, cross_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linarith [key]

end StarInequality

#print axioms StarInequality.staple_sos_poly_gen
#print axioms StarInequality.R_nonneg_gen
#print axioms StarInequality.staple_ineq_vec_gen


-- ===== 定理 S の staple `N` 本版 =====
/-
定理 S の staple `N` 本版——定数 `3N`（`N = 6` で 18）。
`t'' ≤ 6N|X|²` の純代数の部分。証明は `star_S` と同じ骨組み。
-/

open Matrix

namespace StarInequality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 定理 S（staple `N` 本）。 -/
theorem star_S_gen {N : ℕ} (s u : Fin N → E) (a b c v : Fin N → Fin 3 → ℝ)
    (hs : ∀ i, ‖s i‖ = 1)
    (hu : ∀ i, ‖u i‖ ^ 2 ≤ (a i + b i + c i) ⬝ᵥ (a i + b i + c i))
    (hv : ∀ i, v i ⬝ᵥ v i ≤ ‖∑ j, s j‖ ^ 2 - inner ℝ (s i) (∑ j, s j) ^ 2) :
    ‖∑ i, u i‖ ^ 2
      - ∑ i, inner ℝ (s i) (∑ j, s j) * ((a i + b i + c i) ⬝ᵥ (a i + b i + c i))
      + 2 * ∑ i, v i ⬝ᵥ (a i ⨯₃ b i + a i ⨯₃ c i + b i ⨯₃ c i)
    ≤ 3 * (N : ℝ) * ∑ i, (a i ⬝ᵥ a i + b i ⬝ᵥ b i + c i ⬝ᵥ c i) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  set M : E := ∑ j, s j with hM
  set p : Fin N → ℝ := fun i => inner ℝ (s i) M with hp
  set yy : Fin N → ℝ := fun i => (a i + b i + c i) ⬝ᵥ (a i + b i + c i) with hyy
  set w : Fin N → ℝ := fun i => v i ⬝ᵥ (a i ⨯₃ b i + a i ⨯₃ c i + b i ⨯₃ c i) with hw
  set n : Fin N → ℝ := fun i => a i ⬝ᵥ a i + b i ⬝ᵥ b i + c i ⬝ᵥ c i with hn
  change ‖∑ i, u i‖ ^ 2 - ∑ i, p i * yy i + 2 * ∑ i, w i ≤ 3 * (N : ℝ) * ∑ i, n i
  have hyy0 : ∀ i, 0 ≤ yy i := fun i => dot3_self_nonneg _
  have hn0 : ∀ i, 0 ≤ n i := fun i =>
    add_nonneg (add_nonneg (dot3_self_nonneg _) (dot3_self_nonneg _)) (dot3_self_nonneg _)
  -- Σ p_i = t
  have hsum_p : ∑ i, p i = ‖M‖ ^ 2 := by
    simp only [hp]
    rw [← sum_inner, ← hM, real_inner_self_eq_norm_sq]
  -- ‖M‖ ≤ N
  have hM6 : ‖M‖ ≤ (N : ℝ) := by
    have h := norm_sum_le Finset.univ s
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [hM]; simpa using h
  have hM0 : 0 ≤ ‖M‖ := norm_nonneg _
  -- |p_i| ≤ ‖M‖
  have hp_abs : ∀ i, |p i| ≤ ‖M‖ := by
    intro i
    have h := abs_real_inner_le_norm (s i) M
    rw [hs i, one_mul] at h
    exact h
  have hp_le : ∀ i, p i ≤ ‖M‖ := fun i => (le_abs_self _).trans (hp_abs i)
  have hp_ge : ∀ i, -(N : ℝ) ≤ p i := fun i => by
    have := neg_abs_le (p i); have := hp_abs i; linarith
  have ht36 : ‖M‖ ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hvle : ∀ i, v i ⬝ᵥ v i ≤ ‖M‖ ^ 2 - p i ^ 2 := hv
  rcases lt_or_eq_of_le hM6 with hlt | heq
  · -- t < N²
    have ht : 0 < (N : ℝ) ^ 2 - ‖M‖ ^ 2 := by nlinarith
    have hp6 : ∀ i, 0 < (N : ℝ) - p i := fun i => by have := hp_le i; linarith
    set lam : Fin N → ℝ := fun i => ((N : ℝ) - p i) / ((N : ℝ) ^ 2 - ‖M‖ ^ 2) with hlam
    have hlam_pos : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 < lam i :=
      fun i _ => div_pos (hp6 i) ht
    have hlam_sum : ∑ i, lam i = 1 := by
      simp only [hlam]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum_p]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_eq_one_iff_eq ht.ne']
      ring
    have hcs := weighted_cs Finset.univ u lam hlam_pos hlam_sum
    have hterm : ∀ i, ‖u i‖ ^ 2 / lam i - p i * yy i + 2 * w i ≤ 3 * (N : ℝ) * n i := by
      intro i
      have hl : 0 < lam i := hlam_pos i (Finset.mem_univ i)
      have h1 : ‖u i‖ ^ 2 / lam i ≤ yy i / lam i := div_le_div_of_nonneg_right (hu i) hl.le
      have hinv : yy i / lam i = (((N : ℝ) ^ 2 - ‖M‖ ^ 2) / ((N : ℝ) - p i)) * yy i := by
        simp only [hlam]
        have := (hp6 i).ne'
        field_simp
      have hvi : v i ⬝ᵥ v i ≤ (N : ℝ) ^ 2 := by
        have := hvle i; nlinarith [sq_nonneg (p i)]
      have hcc : ((N : ℝ) ^ 2 - ‖M‖ ^ 2) / ((N : ℝ) - p i) - p i ≤ (N : ℝ) - (v i ⬝ᵥ v i) / ((N : ℝ) - p i) := by
        have hne := (hp6 i).ne'
        have e : ((N : ℝ) ^ 2 - ‖M‖ ^ 2) / ((N : ℝ) - p i) - p i
            = (N : ℝ) - (‖M‖ ^ 2 - p i ^ 2) / ((N : ℝ) - p i) := by
          field_simp
          ring
        rw [e]
        have := div_le_div_of_nonneg_right (hvle i) (hp6 i).le
        linarith
      have hst := staple_ineq_vec_gen (a i) (b i) (c i) (v i)
        (((N : ℝ) ^ 2 - ‖M‖ ^ 2) / ((N : ℝ) - p i) - p i) (p i) (N : ℝ) hNR (hp_ge i) (by have := hp6 i; linarith) hvi hcc
      change (((N : ℝ) ^ 2 - ‖M‖ ^ 2) / ((N : ℝ) - p i) - p i) * yy i + 2 * w i ≤ 3 * (N : ℝ) * n i at hst
      rw [hinv] at h1
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hterm i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    linarith
  · -- t = N²：全 p_i = N・v_i = 0
    have hp6 : ∀ i, p i = (N : ℝ) := by
      intro i
      by_contra hne
      have hlt : p i < (N : ℝ) := lt_of_le_of_ne (by have := hp_le i; linarith) hne
      have hslt : ∑ j, p j < ∑ _j : Fin N, (N : ℝ) :=
        Finset.sum_lt_sum (fun j _ => by have := hp_le j; linarith) ⟨i, Finset.mem_univ i, hlt⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hslt
      rw [hsum_p, heq] at hslt
      nlinarith
    have hv0 : ∀ i, v i = 0 := by
      intro i
      have h1 := hvle i
      rw [hp6 i, heq] at h1
      have h2 : v i ⬝ᵥ v i = 0 := le_antisymm (by linarith) (dot3_self_nonneg _)
      exact dotProduct_self_eq_zero.mp h2
    have hw0 : ∀ i, w i = 0 := fun i => by simp only [hw, hv0 i, zero_dotProduct]
    have hcs := weighted_cs Finset.univ u (fun _ : Fin N => (1 / (N : ℝ)))
      (fun _ _ => by positivity)
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp)
    have hterm : ∀ i, ‖u i‖ ^ 2 / (1 / (N : ℝ)) ≤ (N : ℝ) * yy i := by
      intro i
      have := hu i
      rw [div_div_eq_mul_div, div_one]
      change ‖u i‖ ^ 2 ≤ yy i at this
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hterm i)
    rw [← Finset.mul_sum] at hsum
    have hpy : ∑ i, p i * yy i = (N : ℝ) * ∑ i, yy i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [hp6 i])
    have hwz : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => hw0 i)
    have hnn : 0 ≤ ∑ i, n i := Finset.sum_nonneg (fun i _ => hn0 i)
    rw [hpy, hwz]
    have : 0 ≤ 3 * (N : ℝ) * ∑ i, n i := by positivity
    linarith

/-- `N = 6` で `star_S` と同じ言明が出る（一般版の検算）。 -/
theorem star_S_from_gen (s u : Fin 6 → E) (a b c v : Fin 6 → Fin 3 → ℝ)
    (hs : ∀ i, ‖s i‖ = 1)
    (hu : ∀ i, ‖u i‖ ^ 2 ≤ (a i + b i + c i) ⬝ᵥ (a i + b i + c i))
    (hv : ∀ i, v i ⬝ᵥ v i ≤ ‖∑ j, s j‖ ^ 2 - inner ℝ (s i) (∑ j, s j) ^ 2) :
    ‖∑ i, u i‖ ^ 2
      - ∑ i, inner ℝ (s i) (∑ j, s j) * ((a i + b i + c i) ⬝ᵥ (a i + b i + c i))
      + 2 * ∑ i, v i ⬝ᵥ (a i ⨯₃ b i + a i ⨯₃ c i + b i ⨯₃ c i)
    ≤ 18 * ∑ i, (a i ⬝ᵥ a i + b i ⬝ᵥ b i + c i ⬝ᵥ c i) := by
  have h := star_S_gen s u a b c v hs hu hv
  have e : (3 : ℝ) * ((6 : ℕ) : ℝ) = 18 := by norm_num
  rw [e] at h
  exact h

end StarInequality

#print axioms StarInequality.star_S_gen
#print axioms StarInequality.star_S_from_gen


-- ===== 四元数の橋（代数の部分） =====
/-
四元数の橋（代数の部分）。
Mathlib の `ℍ[ℝ]` の上で、staple `s(τ) = s e^{τA} e^{τB} e^{τC}` の二階のテイラー係数
`s * D2 A B C`（`D2 = A² + B² + C² + 2AB + 2AC + 2BC`）を `StarInequality.star_S` に流し込み、
Hesse 形式 `hessForm := 2‖Σ s_i Y_i‖² + 2⟨M, Σ s_i D2_i⟩ ≤ 36 Σ(‖A_i‖²+‖B_i‖²+‖C_i‖²)`。
微分との同一視は次の節。
-/

open Matrix Quaternion

namespace StapleCurve

/-- 四元数の虚部を `Fin 3 → ℝ` と見る。 -/
def vec (q : ℍ[ℝ]) : Fin 3 → ℝ := ![q.imI, q.imJ, q.imK]

@[simp] theorem vec_zero' (q : ℍ[ℝ]) : vec q 0 = q.imI := rfl
@[simp] theorem vec_one' (q : ℍ[ℝ]) : vec q 1 = q.imJ := rfl
@[simp] theorem vec_two' (q : ℍ[ℝ]) : vec q 2 = q.imK := rfl

theorem vec_add (p q : ℍ[ℝ]) : vec (p + q) = vec p + vec q := by
  ext i; fin_cases i <;> simp [vec]

theorem cross3_0 (a b : Fin 3 → ℝ) : (a ⨯₃ b) 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross_apply]
theorem cross3_1 (a b : Fin 3 → ℝ) : (a ⨯₃ b) 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross_apply]
theorem cross3_2 (a b : Fin 3 → ℝ) : (a ⨯₃ b) 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross_apply]

/-- `e^{τA} e^{τB} e^{τC}` の `τ = 0` での二階微分。 -/
noncomputable def D2 (A B C : ℍ[ℝ]) : ℍ[ℝ] :=
  A * A + B * B + C * C + (2 : ℝ) • (A * B) + (2 : ℝ) • (A * C) + (2 : ℝ) • (B * C)

/-- (Q1) 実部：`−|Y|²`。 -/
theorem D2_re (A B C : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) :
    (D2 A B C).re = -(vec (A + B + C) ⬝ᵥ vec (A + B + C)) := by
  simp only [D2, StarInequality.dot3, vec_zero', vec_one', vec_two', re_add, re_mul, re_smul,
    imI_add, imJ_add, imK_add, smul_eq_mul, hA, hB, hC]
  ring

/-- (Q1) 虚部：`2W`・`W = A×B + A×C + B×C`。 -/
theorem D2_vec (A B C : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) :
    vec (D2 A B C) = (2 : ℝ) • (vec A ⨯₃ vec B + vec A ⨯₃ vec C + vec B ⨯₃ vec C) := by
  ext i
  fin_cases i
  · change vec (D2 A B C) 0 = ((2 : ℝ) • (vec A ⨯₃ vec B + vec A ⨯₃ vec C + vec B ⨯₃ vec C)) 0
    simp only [D2, Pi.smul_apply, Pi.add_apply, cross3_0, vec_zero', vec_one', vec_two',
      imI_add, imI_mul, imI_smul, smul_eq_mul, hA, hB, hC]
    ring
  · change vec (D2 A B C) 1 = ((2 : ℝ) • (vec A ⨯₃ vec B + vec A ⨯₃ vec C + vec B ⨯₃ vec C)) 1
    simp only [D2, Pi.smul_apply, Pi.add_apply, cross3_1, vec_zero', vec_one', vec_two',
      imJ_add, imJ_mul, imJ_smul, smul_eq_mul, hA, hB, hC]
    ring
  · change vec (D2 A B C) 2 = ((2 : ℝ) • (vec A ⨯₃ vec B + vec A ⨯₃ vec C + vec B ⨯₃ vec C)) 2
    simp only [D2, Pi.smul_apply, Pi.add_apply, cross3_2, vec_zero', vec_one', vec_two',
      imK_add, imK_mul, imK_smul, smul_eq_mul, hA, hB, hC]
    ring

/-- `ℍ` の内積は実部の積＋虚部の内積。 -/
theorem inner_eq_re_vec (x y : ℍ[ℝ]) : inner ℝ x y = x.re * y.re + vec x ⬝ᵥ vec y := by
  rw [Quaternion.inner_def]
  simp only [StarInequality.dot3, vec_zero', vec_one', vec_two', re_mul, re_star, imI_star,
    imJ_star, imK_star]
  ring

/-- `‖q‖² = re² + |im|²`。 -/
theorem norm_sq_eq (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + vec q ⬝ᵥ vec q := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_re_vec]; ring

theorem norm_sq_eq_of_re (q : ℍ[ℝ]) (hq : q.re = 0) : ‖q‖ ^ 2 = vec q ⬝ᵥ vec q := by
  rw [norm_sq_eq, hq]; ring

/-- (Q3) 左からの積の随伴：`⟨M, s q⟩ = ⟨s̄ M, q⟩`。 -/
theorem inner_mul_left_adj (M s q : ℍ[ℝ]) : inner ℝ M (s * q) = inner ℝ (star s * M) q := by
  rw [inner_eq_re_vec, inner_eq_re_vec]
  simp only [StarInequality.dot3, vec_zero', vec_one', vec_two', re_mul, imI_mul, imJ_mul, imK_mul,
    re_star, imI_star, imJ_star, imK_star]
  ring

/-- `re(s̄ M) = ⟨s, M⟩`。 -/
theorem re_star_mul (s M : ℍ[ℝ]) : (star s * M).re = inner ℝ s M := by
  rw [inner_eq_re_vec]
  simp only [StarInequality.dot3, vec_zero', vec_one', vec_two', re_mul, re_star, imI_star,
    imJ_star, imK_star]
  ring

/-- (Q2a) `‖s Y‖² = |Y|²`（`‖s‖ = 1`・`Y` 虚）。 -/
theorem norm_sq_unit_mul (s Y : ℍ[ℝ]) (hs : ‖s‖ = 1) (hY : Y.re = 0) :
    ‖s * Y‖ ^ 2 = vec Y ⬝ᵥ vec Y := by
  rw [norm_mul, hs, one_mul, norm_sq_eq_of_re Y hY]

/-- (Q2b) `|Im(s̄ M)|² = ‖M‖² − ⟨s, M⟩²`（`‖s‖ = 1`）。 -/
theorem vec_star_mul_sq (s M : ℍ[ℝ]) (hs : ‖s‖ = 1) :
    vec (star s * M) ⬝ᵥ vec (star s * M) = ‖M‖ ^ 2 - inner ℝ s M ^ 2 := by
  have h := norm_sq_eq (star s * M)
  rw [norm_mul, norm_star, hs, one_mul, re_star_mul] at h
  linarith

/-- staple 一本：`⟨M, s D2⟩ = −⟨s,M⟩|Y|² + 2⟨Im(s̄M), W⟩`。 -/
theorem inner_staple (M s A B C : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) :
    inner ℝ M (s * D2 A B C)
      = -(inner ℝ s M * (vec (A + B + C) ⬝ᵥ vec (A + B + C)))
        + 2 * (vec (star s * M) ⬝ᵥ (vec A ⨯₃ vec B + vec A ⨯₃ vec C + vec B ⨯₃ vec C)) := by
  rw [inner_mul_left_adj, inner_eq_re_vec, D2_re A B C hA hB hC, D2_vec A B C hA hB hC,
    re_star_mul, dotProduct_smul, smul_eq_mul]
  ring

/-- (Q5) Hesse 形式：`t(τ) = ‖Σ_i s_i e^{τA_i} e^{τB_i} e^{τC_i}‖²` の `τ = 0` での
二階微分の式 `2‖M'‖² + 2⟨M, M''⟩`（微分との同一視は次の節）。 -/
noncomputable def hessForm (s A B C : Fin 6 → ℍ[ℝ]) : ℝ :=
  2 * ‖∑ i, s i * (A i + B i + C i)‖ ^ 2
    + 2 * inner ℝ (∑ j, s j) (∑ i, s i * D2 (A i) (B i) (C i))

/-- (Q5) `hessForm ≤ 36 Σ_i (‖A_i‖² + ‖B_i‖² + ‖C_i‖²)`。 -/
theorem hessForm_le (s A B C : Fin 6 → ℍ[ℝ]) (hs : ∀ i, ‖s i‖ = 1)
    (hA : ∀ i, (A i).re = 0) (hB : ∀ i, (B i).re = 0) (hC : ∀ i, (C i).re = 0) :
    hessForm s A B C ≤ 36 * ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) := by
  have hY : ∀ i, (A i + B i + C i).re = 0 := fun i => by
    simp [hA i, hB i, hC i]
  have key := StarInequality.star_S s (fun i => s i * (A i + B i + C i))
    (fun i => vec (A i)) (fun i => vec (B i)) (fun i => vec (C i))
    (fun i => vec (star (s i) * ∑ j, s j)) hs
    (fun i => by
      show ‖s i * (A i + B i + C i)‖ ^ 2 ≤ _
      rw [norm_sq_unit_mul _ _ (hs i) (hY i), vec_add, vec_add])
    (fun i => by
      show vec (star (s i) * ∑ j, s j) ⬝ᵥ vec (star (s i) * ∑ j, s j) ≤ _
      rw [vec_star_mul_sq _ _ (hs i)])
  have hin : inner ℝ (∑ j, s j) (∑ i, s i * D2 (A i) (B i) (C i))
      = -∑ i, inner ℝ (s i) (∑ j, s j)
            * ((vec (A i) + vec (B i) + vec (C i)) ⬝ᵥ (vec (A i) + vec (B i) + vec (C i)))
        + 2 * ∑ i, vec (star (s i) * ∑ j, s j)
            ⬝ᵥ (vec (A i) ⨯₃ vec (B i) + vec (A i) ⨯₃ vec (C i) + vec (B i) ⨯₃ vec (C i)) := by
    rw [inner_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_staple _ _ _ _ _ (hA i) (hB i) (hC i), vec_add, vec_add]
  have hn : ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2)
      = ∑ i, (vec (A i) ⬝ᵥ vec (A i) + vec (B i) ⬝ᵥ vec (B i) + vec (C i) ⬝ᵥ vec (C i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sq_eq_of_re _ (hA i), norm_sq_eq_of_re _ (hB i), norm_sq_eq_of_re _ (hC i)]
  unfold hessForm
  rw [hin, hn]
  linarith [key]

end StapleCurve

#print axioms StapleCurve.D2_re
#print axioms StapleCurve.D2_vec
#print axioms StapleCurve.inner_mul_left_adj
#print axioms StapleCurve.norm_sq_unit_mul
#print axioms StapleCurve.vec_star_mul_sq
#print axioms StapleCurve.inner_staple
#print axioms StapleCurve.hessForm_le


-- ===== 四元数の橋（微分との同一視） =====
/-
四元数の橋（微分との同一視）。
`curve s A B C τ = s e^{τA} e^{τB} e^{τC}`（`NormedSpace.exp`）について
`t(τ) = ‖Σ_i curve_i τ‖²` の `τ = 0` での二階微分が `hessForm` に等しいこと、
したがって `≤ 36 Σ(‖A_i‖²+‖B_i‖²+‖C_i‖²)`。
-/

open Quaternion NormedSpace

namespace StapleCurve

/-- 内積空間の曲線 `M` の `‖M‖²` の二階微分：`2‖M'‖² + 2⟨M, M''⟩`。 -/
theorem second_deriv_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M M' : ℝ → E) (M'' : E) (h1 : ∀ τ, HasDerivAt M (M' τ) τ) (h2 : HasDerivAt M' M'' 0) :
    deriv (deriv (fun τ => ‖M τ‖ ^ 2)) 0 = 2 * ‖M' 0‖ ^ 2 + 2 * inner ℝ (M 0) M'' := by
  have hd : deriv (fun τ => ‖M τ‖ ^ 2) = fun τ => 2 * inner ℝ (M τ) (M' τ) := by
    funext τ
    have e : (fun τ => ‖M τ‖ ^ 2) = fun τ => inner ℝ (M τ) (M τ) := by
      funext σ; rw [real_inner_self_eq_norm_sq]
    rw [e, (HasDerivAt.inner ℝ (h1 τ) (h1 τ)).deriv, real_inner_comm (M τ) (M' τ)]
    ring
  rw [hd, ((HasDerivAt.inner ℝ (h1 0) h2).const_mul (2 : ℝ)).deriv, real_inner_self_eq_norm_sq]
  ring

/-- staple の曲線。 -/
noncomputable def curve (s A B C : ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] :=
  s * exp (τ • A) * exp (τ • B) * exp (τ • C)

/-- その一階微分。 -/
noncomputable def curve' (s A B C : ℍ[ℝ]) (τ : ℝ) : ℍ[ℝ] :=
  s * (exp (τ • A) * A) * exp (τ • B) * exp (τ • C)
    + s * exp (τ • A) * (exp (τ • B) * B) * exp (τ • C)
    + s * exp (τ • A) * exp (τ • B) * (exp (τ • C) * C)

theorem curve_zero (s A B C : ℍ[ℝ]) : curve s A B C 0 = s := by
  simp [curve]

theorem curve'_zero (s A B C : ℍ[ℝ]) : curve' s A B C 0 = s * (A + B + C) := by
  simp [curve', mul_add]

theorem hasDerivAt_curve (s A B C : ℍ[ℝ]) (τ : ℝ) :
    HasDerivAt (curve s A B C) (curve' s A B C τ) τ := by
  have hA : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (τ • A) * A) τ :=
    hasDerivAt_exp_smul_const A τ
  have hB : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (τ • B) * B) τ :=
    hasDerivAt_exp_smul_const B τ
  have hC : HasDerivAt (fun u : ℝ => exp (u • C)) (exp (τ • C) * C) τ :=
    hasDerivAt_exp_smul_const C τ
  have h := ((hA.const_mul s).fun_mul hB).fun_mul hC
  refine h.congr_deriv ?_
  simp only [curve', mul_assoc, add_mul]

theorem hasDerivAt_curve'_zero (s A B C : ℍ[ℝ]) :
    HasDerivAt (curve' s A B C) (s * D2 A B C) 0 := by
  have hA : HasDerivAt (fun u : ℝ => exp (u • A)) (exp ((0 : ℝ) • A) * A) 0 :=
    hasDerivAt_exp_smul_const A 0
  have hB : HasDerivAt (fun u : ℝ => exp (u • B)) (exp ((0 : ℝ) • B) * B) 0 :=
    hasDerivAt_exp_smul_const B 0
  have hC : HasDerivAt (fun u : ℝ => exp (u • C)) (exp ((0 : ℝ) • C) * C) 0 :=
    hasDerivAt_exp_smul_const C 0
  have t1 := ((((hA.mul_const A).const_mul s).fun_mul hB).fun_mul hC)
  have t2 := (((hA.const_mul s).fun_mul (hB.mul_const B)).fun_mul hC)
  have t3 := (((hA.const_mul s).fun_mul hB).fun_mul (hC.mul_const C))
  have h := (t1.fun_add t2).fun_add t3
  refine h.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, D2, two_smul, mul_add, add_mul,
    mul_assoc]
  abel

/-- `t(τ) = ‖Σ_i s_i e^{τA_i} e^{τB_i} e^{τC_i}‖²` の `τ = 0` での二階微分は `hessForm`。 -/
theorem second_deriv_eq_hessForm (s A B C : Fin 6 → ℍ[ℝ]) :
    deriv (deriv (fun τ => ‖∑ i, curve (s i) (A i) (B i) (C i) τ‖ ^ 2)) 0
      = hessForm s A B C := by
  have h1 : ∀ τ, HasDerivAt (fun τ => ∑ i, curve (s i) (A i) (B i) (C i) τ)
      (∑ i, curve' (s i) (A i) (B i) (C i) τ) τ := fun τ =>
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve (s i) (A i) (B i) (C i) τ
  have h2 : HasDerivAt (fun τ => ∑ i, curve' (s i) (A i) (B i) (C i) τ)
      (∑ i, s i * D2 (A i) (B i) (C i)) 0 :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve'_zero (s i) (A i) (B i) (C i)
  rw [second_deriv_norm_sq _ _ _ h1 h2]
  simp only [curve_zero, curve'_zero, hessForm]

/-- 橋の結論：`t''(0) ≤ 36 Σ_i (‖A_i‖² + ‖B_i‖² + ‖C_i‖²)`
（`‖s_i‖ = 1`・`A_i, B_i, C_i` は虚四元数）。 -/
theorem second_deriv_le (s A B C : Fin 6 → ℍ[ℝ]) (hs : ∀ i, ‖s i‖ = 1)
    (hA : ∀ i, (A i).re = 0) (hB : ∀ i, (B i).re = 0) (hC : ∀ i, (C i).re = 0) :
    deriv (deriv (fun τ => ‖∑ i, curve (s i) (A i) (B i) (C i) τ‖ ^ 2)) 0
      ≤ 36 * ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) := by
  rw [second_deriv_eq_hessForm]
  exact hessForm_le s A B C hs hA hB hC

end StapleCurve

#print axioms StapleCurve.second_deriv_norm_sq
#print axioms StapleCurve.hasDerivAt_curve
#print axioms StapleCurve.hasDerivAt_curve'_zero
#print axioms StapleCurve.second_deriv_eq_hessForm
#print axioms StapleCurve.second_deriv_le


-- ===== staple `N` 本の版と定数の鋭さ =====
/-
staple `N` 本の版（定数 `6N`）と、定数 `36` の鋭さ（四元数の配位で等号）。
-/

open Matrix Quaternion NormedSpace

namespace StapleCurve

/-- Hesse 形式（staple `N` 本）。 -/
noncomputable def hessFormN {N : ℕ} (s A B C : Fin N → ℍ[ℝ]) : ℝ :=
  2 * ‖∑ i, s i * (A i + B i + C i)‖ ^ 2
    + 2 * inner ℝ (∑ j, s j) (∑ i, s i * D2 (A i) (B i) (C i))

theorem hessFormN_le {N : ℕ} (s A B C : Fin N → ℍ[ℝ]) (hs : ∀ i, ‖s i‖ = 1)
    (hA : ∀ i, (A i).re = 0) (hB : ∀ i, (B i).re = 0) (hC : ∀ i, (C i).re = 0) :
    hessFormN s A B C ≤ 6 * (N : ℝ) * ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) := by
  have hY : ∀ i, (A i + B i + C i).re = 0 := fun i => by
    simp [hA i, hB i, hC i]
  have key := StarInequality.star_S_gen s (fun i => s i * (A i + B i + C i))
    (fun i => vec (A i)) (fun i => vec (B i)) (fun i => vec (C i))
    (fun i => vec (star (s i) * ∑ j, s j)) hs
    (fun i => by
      show ‖s i * (A i + B i + C i)‖ ^ 2 ≤ _
      rw [norm_sq_unit_mul _ _ (hs i) (hY i), vec_add, vec_add])
    (fun i => by
      show vec (star (s i) * ∑ j, s j) ⬝ᵥ vec (star (s i) * ∑ j, s j) ≤ _
      rw [vec_star_mul_sq _ _ (hs i)])
  have hin : inner ℝ (∑ j, s j) (∑ i, s i * D2 (A i) (B i) (C i))
      = -∑ i, inner ℝ (s i) (∑ j, s j)
            * ((vec (A i) + vec (B i) + vec (C i)) ⬝ᵥ (vec (A i) + vec (B i) + vec (C i)))
        + 2 * ∑ i, vec (star (s i) * ∑ j, s j)
            ⬝ᵥ (vec (A i) ⨯₃ vec (B i) + vec (A i) ⨯₃ vec (C i) + vec (B i) ⨯₃ vec (C i)) := by
    rw [inner_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_staple _ _ _ _ _ (hA i) (hB i) (hC i), vec_add, vec_add]
  have hn : ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2)
      = ∑ i, (vec (A i) ⬝ᵥ vec (A i) + vec (B i) ⬝ᵥ vec (B i) + vec (C i) ⬝ᵥ vec (C i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sq_eq_of_re _ (hA i), norm_sq_eq_of_re _ (hB i), norm_sq_eq_of_re _ (hC i)]
  unfold hessFormN
  rw [hin, hn]
  linarith [key]

theorem second_deriv_eq_hessFormN {N : ℕ} (s A B C : Fin N → ℍ[ℝ]) :
    deriv (deriv (fun τ => ‖∑ i, curve (s i) (A i) (B i) (C i) τ‖ ^ 2)) 0
      = hessFormN s A B C := by
  have h1 : ∀ τ, HasDerivAt (fun τ => ∑ i, curve (s i) (A i) (B i) (C i) τ)
      (∑ i, curve' (s i) (A i) (B i) (C i) τ) τ := fun τ =>
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve (s i) (A i) (B i) (C i) τ
  have h2 : HasDerivAt (fun τ => ∑ i, curve' (s i) (A i) (B i) (C i) τ)
      (∑ i, s i * D2 (A i) (B i) (C i)) 0 :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve'_zero (s i) (A i) (B i) (C i)
  rw [second_deriv_norm_sq _ _ _ h1 h2]
  simp only [curve_zero, curve'_zero, hessFormN]

/-- staple `N` 本：`t''(0) ≤ 6N Σ_i (‖A_i‖² + ‖B_i‖² + ‖C_i‖²)`。 -/
theorem second_deriv_le_gen {N : ℕ} (s A B C : Fin N → ℍ[ℝ]) (hs : ∀ i, ‖s i‖ = 1)
    (hA : ∀ i, (A i).re = 0) (hB : ∀ i, (B i).re = 0) (hC : ∀ i, (C i).re = 0) :
    deriv (deriv (fun τ => ‖∑ i, curve (s i) (A i) (B i) (C i) τ‖ ^ 2)) 0
      ≤ 6 * (N : ℝ) * ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) := by
  rw [second_deriv_eq_hessFormN]
  exact hessFormN_le s A B C hs hA hB hC

/-- 符号 `(+,+,+,−,−,−)`。 -/
def sg : Fin 6 → ℝ := ![1, 1, 1, -1, -1, -1]

theorem sg_sq (i : Fin 6) : sg i * sg i = 1 := by
  fin_cases i <;> simp [sg]

/-- `x i`（虚四元数）。 -/
def qI (x : ℝ) : ℍ[ℝ] := ⟨0, x, 0, 0⟩

@[simp] theorem qI_re (x : ℝ) : (qI x).re = 0 := rfl
@[simp] theorem qI_imI (x : ℝ) : (qI x).imI = x := rfl
@[simp] theorem qI_imJ (x : ℝ) : (qI x).imJ = 0 := rfl
@[simp] theorem qI_imK (x : ℝ) : (qI x).imK = 0 := rfl

theorem norm_qI_sq (x : ℝ) : ‖qI x‖ ^ 2 = x ^ 2 := by
  rw [norm_sq_eq_of_re _ rfl, StarInequality.dot3]
  show x * x + 0 * 0 + 0 * 0 = x ^ 2
  ring

theorem coe_mul_qI3 (r x : ℝ) : (r : ℍ[ℝ]) * (qI x + qI x + qI x) = qI (3 * (r * x)) := by
  ext <;> simp
  ring

theorem sum_sg : ∑ j, ((sg j : ℝ) : ℍ[ℝ]) = 0 := by
  ext <;> simp [Fin.sum_univ_six, sg]

theorem six_qI : (6 : ℕ) • qI 3 = qI 18 := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  ext <;> simp only [re_smul, imI_smul, imJ_smul, imK_smul, qI_re, qI_imI, qI_imJ, qI_imK,
    smul_eq_mul] <;> norm_num

/-- 定数 `36` は下げられない：`s_i = ±1`・`A_i = B_i = C_i = ± i` で等号。 -/
theorem second_deriv_sharp :
    ∃ (s A B C : Fin 6 → ℍ[ℝ]), (∀ i, ‖s i‖ = 1) ∧
      (∀ i, (A i).re = 0) ∧ (∀ i, (B i).re = 0) ∧ (∀ i, (C i).re = 0) ∧
      deriv (deriv (fun τ => ‖∑ i, curve (s i) (A i) (B i) (C i) τ‖ ^ 2)) 0
        = 36 * ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) ∧
      0 < ∑ i, (‖A i‖ ^ 2 + ‖B i‖ ^ 2 + ‖C i‖ ^ 2) := by
  have hnA : ∀ i, ‖qI (sg i)‖ ^ 2 = 1 := fun i => by
    rw [norm_qI_sq, sq, sg_sq]
  have hsY : ∀ i, ((sg i : ℝ) : ℍ[ℝ]) * (qI (sg i) + qI (sg i) + qI (sg i)) = qI 3 := fun i => by
    rw [coe_mul_qI3, sg_sq, mul_one]
  refine ⟨fun i => ((sg i : ℝ) : ℍ[ℝ]), fun i => qI (sg i), fun i => qI (sg i),
    fun i => qI (sg i), fun i => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · have h := sg_sq i
    have h2 : |sg i| * |sg i| = 1 := by rw [abs_mul_abs_self]; exact h
    rw [Quaternion.norm_coe, Real.norm_eq_abs]
    nlinarith [abs_nonneg (sg i)]
  · rw [second_deriv_eq_hessForm]
    unfold hessForm
    simp only [hsY, sum_sg, inner_zero_left, hnA, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, six_qI, norm_qI_sq]
    norm_num
  · simp only [hnA]; norm_num

end StapleCurve

#print axioms StapleCurve.hessFormN_le
#print axioms StapleCurve.second_deriv_le_gen
#print axioms StapleCurve.second_deriv_sharp


-- ===== staple の曲線は単位球面の上 =====
/-
staple の曲線は単位球面 `S³ ⊂ ℍ` の上にある
（`‖s‖ = 1`・`A, B, C` は虚四元数のとき `‖s e^{τA} e^{τB} e^{τC}‖ = 1`）。
-/

open Quaternion NormedSpace

namespace StapleCurve

theorem norm_exp_smul_of_re (A : ℍ[ℝ]) (hA : A.re = 0) (τ : ℝ) : ‖exp (τ • A)‖ = 1 := by
  rw [Quaternion.norm_exp]
  simp [hA]

theorem norm_curve (s A B C : ℍ[ℝ]) (hs : ‖s‖ = 1)
    (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) (τ : ℝ) : ‖curve s A B C τ‖ = 1 := by
  simp only [curve, norm_mul, hs, norm_exp_smul_of_re _ hA, norm_exp_smul_of_re _ hB,
    norm_exp_smul_of_re _ hC, mul_one]

end StapleCurve

#print axioms StapleCurve.norm_curve
end AlgebraPart

-- ===== 二項係数の補題 =====
section BinomialLemmas
/-
純粋に自然数・整数の補題。
  vdm      : ∑_{k ≤ n} C(n,k)·C(m,k+r) = C(n+m, n+r)      （Vandermonde・帰納法）
  B1       : ∑_{j ≤ n} C(n,j)·(C(n+4,j+2) − C(n+4,j+1)) = C(2n+4,n+2) − C(2n+4,n+1)   （ℤ）
  B1_pos   : 右辺 > 0
-/

open Finset

namespace OneLinkSeries

/-- Vandermonde の畳み込み（ずらし `r` つき）。 -/
theorem vdm (n m r : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k * m.choose (k + r) = (n + m).choose (n + r) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ k ∈ range (n + 1),
        (n + 1).choose (k + 1) * m.choose (k + 1 + r)
          = n.choose k * m.choose (k + (r + 1)) + n.choose (k + 1) * m.choose (k + 1 + r) := by
      intro k _
      rw [Nat.choose_succ_succ', add_mul, show k + (r + 1) = k + 1 + r by ring]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih (r + 1)]
    have h2 : ∑ k ∈ range (n + 1), n.choose (k + 1) * m.choose (k + 1 + r)
        + (n + 1).choose 0 * m.choose (0 + r) = (n + m).choose (n + r) := by
      have key : ∑ k ∈ range (n + 2), n.choose k * m.choose (k + r) = (n + m).choose (n + r) := by
        rw [Finset.sum_range_succ, ih r]
        simp
      rw [Finset.sum_range_succ'] at key
      simpa using key
    have h3 : (n + 1 + m).choose (n + 1 + r)
        = (n + m).choose (n + r) + (n + m).choose (n + (r + 1)) := by
      have : n + 1 + m = (n + m) + 1 := by ring
      rw [this, show n + 1 + r = (n + r) + 1 by ring, Nat.choose_succ_succ']
      rfl
    rw [h3]
    omega

/-- B1（整数で）。 -/
theorem B1 (n : ℕ) :
    ∑ j ∈ range (n + 1),
        (n.choose j : ℤ) * (((n + 4).choose (j + 2) : ℤ) - ((n + 4).choose (j + 1) : ℤ))
      = ((2 * n + 4).choose (n + 2) : ℤ) - ((2 * n + 4).choose (n + 1) : ℤ) := by
  have e2 := vdm n (n + 4) 2
  have e1 := vdm n (n + 4) 1
  have t : n + (n + 4) = 2 * n + 4 := by ring
  rw [t] at e2 e1
  rw [← e2, ← e1]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- 中央の隣：`C(2n+4,n+1) < C(2n+4,n+2)`。 -/
theorem choose_lt_mid (n : ℕ) : (2 * n + 4).choose (n + 1) < (2 * n + 4).choose (n + 2) := by
  have h := Nat.choose_succ_right_eq (2 * n + 4) (n + 1)
  have h' : 2 * n + 4 - (n + 1) = n + 3 := by omega
  rw [h'] at h
  have hpos : 0 < (2 * n + 4).choose (n + 1) := Nat.choose_pos (by omega)
  nlinarith

theorem B1_pos (n : ℕ) :
    (0 : ℤ) < ((2 * n + 4).choose (n + 2) : ℤ) - ((2 * n + 4).choose (n + 1) : ℤ) := by
  have := choose_lt_mid n
  have : ((2 * n + 4).choose (n + 1) : ℤ) < ((2 * n + 4).choose (n + 2) : ℤ) := by exact_mod_cast this
  linarith

/-- `C(2n+4,n+2) − C(2n+4,n+1)` は Catalan 数 `Cat(n+2)`。 -/
theorem B1_catalan (n : ℕ) :
    ((2 * n + 4).choose (n + 2) : ℤ) - ((2 * n + 4).choose (n + 1) : ℤ) = (catalan (n + 2) : ℤ) := by
  have h := succ_mul_catalan_eq_centralBinom (n + 2)
  have hc : Nat.centralBinom (n + 2) = (2 * n + 4).choose (n + 2) := by
    rw [Nat.centralBinom]; congr 1
  have h2 := Nat.choose_succ_right_eq (2 * n + 4) (n + 1)
  have h' : 2 * n + 4 - (n + 1) = n + 3 := by omega
  rw [h'] at h2
  rw [hc] at h
  have hz : ((n : ℤ) + 3) * (((2 * n + 4).choose (n + 2) : ℤ) - ((2 * n + 4).choose (n + 1) : ℤ))
      = ((n : ℤ) + 3) * (catalan (n + 2) : ℤ) := by
    have h2z : ((2 * n + 4).choose (n + 2) : ℤ) * ((n : ℤ) + 2) = ((2 * n + 4).choose (n + 1) : ℤ) * ((n : ℤ) + 3) := by
      exact_mod_cast h2
    have hz' : ((n : ℤ) + 3) * (catalan (n + 2) : ℤ) = ((2 * n + 4).choose (n + 2) : ℤ) := by
      exact_mod_cast h
    rw [hz']
    linarith
  have hn : ((n : ℤ) + 3) ≠ 0 := by positivity
  exact mul_left_cancel₀ hn hz

end OneLinkSeries

#print axioms OneLinkSeries.vdm
#print axioms OneLinkSeries.B1
#print axioms OneLinkSeries.B1_pos
#print axioms OneLinkSeries.B1_catalan
end BinomialLemmas

-- ===== 係数の補題 =====
section SeriesCoefficients
/-
係数の補題（標数 0 の体 `K` の上で）。
  a k = 1/(k!(k+1)!)・b k = 1/(k!(k+2)!)・d k = 1/(k!(k+3)!)
  b = a の形式微分・d = b の形式微分
  cauchy_coeff : ∑_{i+j=n} (b_i b_j − a_i d_j) = (C(2n+4,n+2) − C(2n+4,n+1)) / (n!(n+4)!)
  形式的冪級数 `Fps = mk a` について `(F')² − F·F''` の係数が `Cat(n+2)/(n!(n+4)!)`
-/

open Finset

namespace OneLinkSeries

section coeffs
variable (K : Type*) [Field K] [CharZero K]

/-- `F` の係数。 -/
noncomputable def a (k : ℕ) : K := 1 / ((k.factorial : K) * ((k + 1).factorial : K))
/-- `F'` の係数。 -/
noncomputable def b (k : ℕ) : K := 1 / ((k.factorial : K) * ((k + 2).factorial : K))
/-- `F''` の係数。 -/
noncomputable def d (k : ℕ) : K := 1 / ((k.factorial : K) * ((k + 3).factorial : K))

variable {K}

theorem fac_ne (k : ℕ) : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

/-- `b_k = (k+1)·a_{k+1}`。 -/
theorem b_eq (k : ℕ) : b K k = ((k : K) + 1) * a K (k + 1) := by
  unfold a b
  have h1 := fac_ne (K := K) k
  have h2 := fac_ne (K := K) (k + 2)
  have h3 : ((k + 1).factorial : K) = ((k : K) + 1) * (k.factorial : K) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h4 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [show k + 1 + 1 = k + 2 by ring, h3]
  field_simp

/-- `d_k = (k+1)·b_{k+1}`。 -/
theorem d_eq (k : ℕ) : d K k = ((k : K) + 1) * b K (k + 1) := by
  unfold b d
  have h1 := fac_ne (K := K) k
  have h2 := fac_ne (K := K) (k + 3)
  have h3 : ((k + 1).factorial : K) = ((k : K) + 1) * (k.factorial : K) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h4 : ((k : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [show k + 1 + 2 = k + 3 by ring, h3]
  field_simp

/-- `a_k − 2 b_k = a_k · k/(k+2)`。 -/
theorem a_sub_two_b (k : ℕ) : a K k - 2 * b K k = a K k * ((k : K) / ((k : K) + 2)) := by
  unfold a b
  have h1 := fac_ne (K := K) k
  have h2 := fac_ne (K := K) (k + 1)
  have h3 : ((k + 2).factorial : K) = ((k : K) + 2) * ((k + 1).factorial : K) := by
    rw [show k + 2 = (k + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have h4 : ((k : K) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  rw [h3]
  field_simp
  ring

omit [CharZero K] in
private theorem aux (P Q fi fj fi2 fj2 N M : K) (hfi : fi ≠ 0) (hfj : fj ≠ 0) (hfi2 : fi2 ≠ 0)
    (hfj2 : fj2 ≠ 0) (h0 : P * fi * fj = N) (h2 : Q * fi2 * fj2 = M) :
    N * M * (1 / (fi * fi2) * (1 / (fj * fj2))) = P * Q := by
  subst h0; subst h2
  field_simp

/-- 項ごとの恒等式：`(i+j)!(i+j+4)!·(b_i b_j − a_i d_j) = C(i+j,i)·(C(i+j+4,i+2) − C(i+j+4,i+1))`。 -/
theorem term_eq (i j : ℕ) :
    ((i + j).factorial : K) * ((i + j + 4).factorial : K) * (b K i * b K j - a K i * d K j)
      = ((i + j).choose i : K) * (((i + j + 4).choose (i + 2) : K) - ((i + j + 4).choose (i + 1) : K)) := by
  have h0 : ((i + j).choose i : K) * (i.factorial : K) * (j.factorial : K) = ((i + j).factorial : K) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at this
    exact_mod_cast this
  have h2 : ((i + j + 4).choose (i + 2) : K) * ((i + 2).factorial : K) * ((j + 2).factorial : K)
      = ((i + j + 4).factorial : K) := by
    have := Nat.add_choose_mul_factorial_mul_factorial (i + 2) (j + 2)
    rw [← Nat.choose_symm_add, show i + 2 + (j + 2) = i + j + 4 by ring] at this
    exact_mod_cast this
  have h1 : ((i + j + 4).choose (i + 1) : K) * ((i + 1).factorial : K) * ((j + 3).factorial : K)
      = ((i + j + 4).factorial : K) := by
    have := Nat.add_choose_mul_factorial_mul_factorial (i + 1) (j + 3)
    rw [← Nat.choose_symm_add, show i + 1 + (j + 3) = i + j + 4 by ring] at this
    exact_mod_cast this
  have t2 := aux _ _ _ _ _ _ _ _ (fac_ne i) (fac_ne j) (fac_ne (i + 2)) (fac_ne (j + 2)) h0 h2
  have t1 := aux _ _ _ _ _ _ _ _ (fac_ne i) (fac_ne j) (fac_ne (i + 1)) (fac_ne (j + 3)) h0 h1
  unfold a b d
  rw [mul_sub, t2, t1, mul_sub]

/-- B2：Cauchy 積の係数。 -/
theorem cauchy_coeff (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (b K ij.1 * b K ij.2 - a K ij.1 * d K ij.2)
      = (((2 * n + 4).choose (n + 2) : K) - ((2 * n + 4).choose (n + 1) : K))
          / ((n.factorial : K) * ((n + 4).factorial : K)) := by
  have hne : (n.factorial : K) * ((n + 4).factorial : K) ≠ 0 := mul_ne_zero (fac_ne n) (fac_ne (n + 4))
  rw [eq_div_iff hne, Finset.sum_mul]
  have hB := congrArg (Int.cast : ℤ → K) (B1 n)
  push_cast at hB
  rw [← hB, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij : ℕ × ℕ => (n.choose ij.1 : K) * (((n + 4).choose (ij.1 + 2) : K) - ((n + 4).choose (ij.1 + 1) : K))) n]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hn : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have := term_eq (K := K) ij.1 ij.2
  rw [hn] at this
  rw [← this]
  ring

theorem cauchy_coeff_catalan (n : ℕ) :
    ∑ ij ∈ antidiagonal n, (b K ij.1 * b K ij.2 - a K ij.1 * d K ij.2)
      = (catalan (n + 2) : K) / ((n.factorial : K) * ((n + 4).factorial : K)) := by
  rw [cauchy_coeff]
  have h := congrArg (Int.cast : ℤ → K) (B1_catalan n)
  push_cast at h
  rw [h]

end coeffs

section fps
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

/-- 形式的冪級数 `F = ∑ x^k/(k!(k+1)!)`。 -/
noncomputable def Fps : K⟦X⟧ := PowerSeries.mk (a K)

theorem derivative_Fps : d⁄dX K (Fps K) = PowerSeries.mk (b K) := by
  ext n
  rw [coeff_derivative, Fps, coeff_mk, coeff_mk, b_eq]
  ring

theorem derivative_derivative_Fps : d⁄dX K (d⁄dX K (Fps K)) = PowerSeries.mk (d K) := by
  ext n
  rw [derivative_Fps, coeff_derivative, coeff_mk, coeff_mk, d_eq]
  ring

/-- `(F')² − F·F''` の `x^n` の係数は `Cat(n+2)/(n!(n+4)!)`。 -/
theorem coeff_turan (n : ℕ) :
    coeff n ((d⁄dX K (Fps K)) ^ 2 - Fps K * d⁄dX K (d⁄dX K (Fps K)))
      = (catalan (n + 2) : K) / ((n.factorial : K) * ((n + 4).factorial : K)) := by
  rw [derivative_derivative_Fps, derivative_Fps, ← cauchy_coeff_catalan, pow_two, map_sub,
    coeff_mul, coeff_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_mk, coeff_mk, Fps, coeff_mk, coeff_mk]

/-- `F − 2F'` の係数は `a_n·n/(n+2)`。 -/
theorem coeff_F_sub_two_F' (n : ℕ) :
    coeff n (Fps K - (2 : K) • d⁄dX K (Fps K)) = a K n * ((n : K) / ((n : K) + 2)) := by
  rw [derivative_Fps, map_sub, coeff_smul, Fps, coeff_mk, coeff_mk, smul_eq_mul, a_sub_two_b]

end fps

/-- 有理数の上で：`(F')² − F F''` の係数は全部正。 -/
theorem coeff_turan_pos (n : ℕ) :
    0 < PowerSeries.coeff n ((PowerSeries.derivative ℚ (Fps ℚ)) ^ 2
      - Fps ℚ * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ (Fps ℚ))) := by
  rw [coeff_turan]
  have : 0 < catalan (n + 2) := by
    have h := succ_mul_catalan_eq_centralBinom (n + 2)
    have := Nat.centralBinom_pos (n + 2)
    rcases Nat.eq_zero_or_pos (catalan (n + 2)) with h0 | h0
    · rw [h0] at h; omega
    · exact h0
  positivity

end OneLinkSeries

#print axioms OneLinkSeries.b_eq
#print axioms OneLinkSeries.d_eq
#print axioms OneLinkSeries.a_sub_two_b
#print axioms OneLinkSeries.term_eq
#print axioms OneLinkSeries.cauchy_coeff
#print axioms OneLinkSeries.cauchy_coeff_catalan
#print axioms OneLinkSeries.coeff_turan
#print axioms OneLinkSeries.coeff_F_sub_two_F'
#print axioms OneLinkSeries.coeff_turan_pos
end SeriesCoefficients

-- ===== 実解析との接続 =====
section SeriesAnalysis
/-
実解析との接続。
  一般補題：`|c k| ≤ 1/k!` なら `f(x) = ∑' c_k x^k` は全域で収束し、
            `f' (x) = ∑' (k+1) c_{k+1} x^k`（項別微分・`hasDerivAt_tsum_of_isPreconnected`）
  F0 = ∑' a_k x^k・F1 = ∑' b_k x^k・F2 = ∑' d_k x^k（ℝ）
  HasDerivAt F0 (F1 x) x・HasDerivAt F1 (F2 x) x
  x ≥ 0 で  1 ≤ F0 x・0 ≤ F1 x・2·F1 x ≤ F0 x・0 ≤ F1 x ^ 2 − F0 x · F2 x
-/

open Finset

namespace OneLinkSeries

section generic

variable {c : ℕ → ℝ}

theorem norm_term_le (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (x : ℝ) (k : ℕ) :
    ‖c k * x ^ k‖ ≤ |x| ^ k / (k.factorial : ℝ) := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |c k| * |x| ^ k ≤ 1 / (k.factorial : ℝ) * |x| ^ k :=
        mul_le_mul_of_nonneg_right (hc k) (by positivity)
    _ = |x| ^ k / (k.factorial : ℝ) := by ring

theorem summable_norm_term (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (x : ℝ) :
    Summable fun k => ‖c k * x ^ k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hc x)
    (Real.summable_pow_div_factorial |x|)

theorem summable_term (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (x : ℝ) :
    Summable fun k => c k * x ^ k :=
  (summable_norm_term hc x).of_norm

/-- 優級数 `u k = k · R^(k-1) / k!` の可総和性。 -/
theorem summable_major (R : ℝ) :
    Summable fun k : ℕ => (k : ℝ) * R ^ (k - 1) / (k.factorial : ℝ) := by
  rw [← summable_nat_add_iff 1]
  have h : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * R ^ (k + 1 - 1) / ((k + 1).factorial : ℝ))
      = fun k : ℕ => R ^ k / (k.factorial : ℝ) := by
    funext k
    have h1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have h2 : (k.factorial : ℝ) ≠ 0 := fac_ne k
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    push_cast at h1
    field_simp
  rw [h]
  exact Real.summable_pow_div_factorial R

/-- 項別微分。 -/
theorem hasDerivAt_series (hc : ∀ k, |c k| ≤ 1 / (k.factorial : ℝ)) (x : ℝ) :
    HasDerivAt (fun y => ∑' k, c k * y ^ k) (∑' k : ℕ, ((k : ℝ) + 1) * c (k + 1) * x ^ k) x := by
  set R : ℝ := |x| + 1 with hR
  have hRpos : 0 < R := by positivity
  have hu := summable_major R
  have hg : ∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      HasDerivAt (fun y => c k * y ^ k) (c k * ((k : ℝ) * y ^ (k - 1))) y :=
    fun k y _ => (hasDerivAt_pow k y).const_mul (c k)
  have hg' : ∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖c k * ((k : ℝ) * y ^ (k - 1))‖ ≤ (k : ℝ) * R ^ (k - 1) / (k.factorial : ℝ) := by
    intro k y hy
    have hy' : |y| ≤ R := by
      have := Metric.mem_ball.mp hy
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      Nat.abs_cast]
    have h1 : |y| ^ (k - 1) ≤ R ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
    calc |c k| * ((k : ℝ) * |y| ^ (k - 1))
        ≤ 1 / (k.factorial : ℝ) * ((k : ℝ) * R ^ (k - 1)) := by
          apply mul_le_mul (hc k) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (k : ℝ) * R ^ (k - 1) / (k.factorial : ℝ) := by ring
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self hRpos
  have key := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected hg hg' h0 (summable_term hc 0) hx
  have hsum : Summable fun k : ℕ => c k * ((k : ℝ) * x ^ (k - 1)) :=
    Summable.of_norm_bounded hu (fun k => hg' k x hx)
  have e : ∑' k : ℕ, c k * ((k : ℝ) * x ^ (k - 1))
      = ∑' k : ℕ, ((k : ℝ) + 1) * c (k + 1) * x ^ k := by
    rw [hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one]
    refine tsum_congr fun k => ?_
    ring
  rw [← e]
  exact key

end generic

section bessel

theorem a_pos (k : ℕ) : 0 < a ℝ k := by unfold a; positivity
theorem b_pos (k : ℕ) : 0 < b ℝ k := by unfold b; positivity
theorem d_pos (k : ℕ) : 0 < d ℝ k := by unfold d; positivity

theorem coef_bound (k m : ℕ) :
    |1 / ((k.factorial : ℝ) * ((k + m).factorial : ℝ))| ≤ 1 / (k.factorial : ℝ) := by
  have h1 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h2 : (1 : ℝ) ≤ ((k + m).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [abs_of_pos (by positivity)]
  apply one_div_le_one_div_of_le h1
  exact le_mul_of_one_le_right h1.le h2

theorem a_bound (k : ℕ) : |a ℝ k| ≤ 1 / (k.factorial : ℝ) := coef_bound k 1
theorem b_bound (k : ℕ) : |b ℝ k| ≤ 1 / (k.factorial : ℝ) := coef_bound k 2
theorem d_bound (k : ℕ) : |d ℝ k| ≤ 1 / (k.factorial : ℝ) := coef_bound k 3

/-- `F(x) = ∑ x^k/(k!(k+1)!)`。 -/
noncomputable def F0 (x : ℝ) : ℝ := ∑' k, a ℝ k * x ^ k
/-- `F'`。 -/
noncomputable def F1 (x : ℝ) : ℝ := ∑' k, b ℝ k * x ^ k
/-- `F''`。 -/
noncomputable def F2 (x : ℝ) : ℝ := ∑' k, d ℝ k * x ^ k

theorem hasDerivAt_F0 (x : ℝ) : HasDerivAt F0 (F1 x) x := by
  have h := hasDerivAt_series a_bound x
  have e : F1 x = ∑' k : ℕ, ((k : ℝ) + 1) * a ℝ (k + 1) * x ^ k := by
    unfold F1
    refine tsum_congr fun k => ?_
    rw [b_eq]
  rw [e]
  exact h

theorem hasDerivAt_F1 (x : ℝ) : HasDerivAt F1 (F2 x) x := by
  have h := hasDerivAt_series b_bound x
  have e : F2 x = ∑' k : ℕ, ((k : ℝ) + 1) * b ℝ (k + 1) * x ^ k := by
    unfold F2
    refine tsum_congr fun k => ?_
    rw [d_eq]
  rw [e]
  exact h

theorem F0_zero : F0 0 = 1 := by
  unfold F0
  rw [tsum_eq_single 0]
  · simp [a]
  · intro k hk
    simp [hk]

theorem one_le_F0 {x : ℝ} (hx : 0 ≤ x) : 1 ≤ F0 x := by
  have h := (summable_term a_bound x).le_tsum 0
    (fun j _ => mul_nonneg (a_pos j).le (pow_nonneg hx j))
  have e : a ℝ 0 * x ^ 0 = 1 := by simp [a]
  rw [e] at h
  exact h

theorem F0_pos {x : ℝ} (hx : 0 ≤ x) : 0 < F0 x := lt_of_lt_of_le one_pos (one_le_F0 hx)

theorem F1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F1 x :=
  tsum_nonneg fun k => mul_nonneg (b_pos k).le (pow_nonneg hx k)

/-- (B-i) `2F' ≤ F`（`x ≥ 0`）。 -/
theorem two_F1_le_F0 {x : ℝ} (hx : 0 ≤ x) : 2 * F1 x ≤ F0 x := by
  unfold F0 F1
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ((summable_term b_bound x).mul_left 2)
    (summable_term a_bound x)
  have h := a_sub_two_b (K := ℝ) k
  have h2 : 0 ≤ a ℝ k * ((k : ℝ) / ((k : ℝ) + 2)) :=
    mul_nonneg (a_pos k).le (by positivity)
  have h3 : 2 * b ℝ k ≤ a ℝ k := by linarith
  calc 2 * (b ℝ k * x ^ k) = (2 * b ℝ k) * x ^ k := by ring
    _ ≤ a ℝ k * x ^ k := mul_le_mul_of_nonneg_right h3 (pow_nonneg hx k)

/-- Cauchy 積：`F1² − F0·F2 = ∑' n, (Cat(n+2)/(n!(n+4)!)) x^n`。 -/
theorem turan_series (x : ℝ) :
    F1 x ^ 2 - F0 x * F2 x
      = ∑' n : ℕ, (catalan (n + 2) : ℝ) / ((n.factorial : ℝ) * ((n + 4).factorial : ℝ)) * x ^ n := by
  have hA := summable_norm_term a_bound x
  have hB := summable_norm_term b_bound x
  have hD := summable_norm_term d_bound x
  have e1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hB hB
  have e2 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hD
  have s1 := (summable_norm_sum_mul_antidiagonal_of_summable_norm hB hB).of_norm
  have s2 := (summable_norm_sum_mul_antidiagonal_of_summable_norm hA hD).of_norm
  unfold F0 F1 F2
  rw [pow_two, e1, e2, ← s1.tsum_sub s2]
  refine tsum_congr fun n => ?_
  rw [← cauchy_coeff_catalan (K := ℝ) n, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hn : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hn, pow_add]
  ring

/-- (B-ii) Turán 型：`F'² − F F'' ≥ 0`（`x ≥ 0`）。 -/
theorem turan_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F1 x ^ 2 - F0 x * F2 x := by
  rw [turan_series]
  exact tsum_nonneg fun n => mul_nonneg (by positivity) (pow_nonneg hx n)

end bessel

end OneLinkSeries

#print axioms OneLinkSeries.hasDerivAt_series
#print axioms OneLinkSeries.hasDerivAt_F0
#print axioms OneLinkSeries.hasDerivAt_F1
#print axioms OneLinkSeries.F0_zero
#print axioms OneLinkSeries.one_le_F0
#print axioms OneLinkSeries.F1_nonneg
#print axioms OneLinkSeries.two_F1_le_F0
#print axioms OneLinkSeries.turan_series
#print axioms OneLinkSeries.turan_nonneg
end SeriesAnalysis

-- ===== `G` への翻訳と数え上げ =====
section LogSeriesG
/-
`G` への翻訳と数え上げ。
  Z κ = F0 (κ²/4)（＝紙の上では `2 I₁(κ)/κ`）・G β t = log (F0 (β² t / 4)) = log Z(β√t)（t ≥ 0）
  G1・G2：`G` の一階・二階導関数の陽な式。t ≥ 0 で
     HasDerivAt (G β) (G1 β t) t・HasDerivAt (G1 β) (G2 β t) t
     0 ≤ G1 β t ≤ β²/8・G2 β t ≤ 0・G1 β 0 = β²/8
  hess_lower：曲線 t(s) ≥ 0 に沿って (−G∘t)'' ≥ −(β²/8)·B（t'' ≤ B・B ≥ 0）
  count27：各辺がちょうど 6 個の star に入るなら Σ_star D ≥ −27β² Σ_e x_e
  hess_total：上二つの合成
-/

open Finset

namespace OneLinkSeries

/-- 一リンク積分の級数（紙の上で `2 I₁(κ)/κ`）。 -/
noncomputable def Z (κ : ℝ) : ℝ := F0 (κ ^ 2 / 4)

noncomputable def G (β t : ℝ) : ℝ := Real.log (F0 (β ^ 2 * t / 4))

noncomputable def G1 (β t : ℝ) : ℝ := β ^ 2 / 4 * F1 (β ^ 2 * t / 4) / F0 (β ^ 2 * t / 4)

noncomputable def G2 (β t : ℝ) : ℝ :=
  (β ^ 2 / 4) ^ 2 * (F2 (β ^ 2 * t / 4) * F0 (β ^ 2 * t / 4) - F1 (β ^ 2 * t / 4) ^ 2)
    / F0 (β ^ 2 * t / 4) ^ 2

theorem G_eq_log_Z (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : G β t = Real.log (Z (β * Real.sqrt t)) := by
  unfold G Z
  rw [mul_pow, Real.sq_sqrt ht]

theorem arg_nonneg (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ β ^ 2 * t / 4 := by positivity

theorem hasDerivAt_arg (β t : ℝ) : HasDerivAt (fun t : ℝ => β ^ 2 * t / 4) (β ^ 2 / 4) t := by
  have h := ((hasDerivAt_id t).const_mul (β ^ 2)).div_const 4
  simpa using h

theorem hasDerivAt_G (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : HasDerivAt (G β) (G1 β t) t := by
  have h0 : HasDerivAt (fun t : ℝ => F0 (β ^ 2 * t / 4)) (F1 (β ^ 2 * t / 4) * (β ^ 2 / 4)) t := by
    have := (hasDerivAt_F0 (β ^ 2 * t / 4)).comp t (hasDerivAt_arg β t)
    exact this
  have h := h0.log (F0_pos (arg_nonneg β ht)).ne'
  have e : G1 β t = F1 (β ^ 2 * t / 4) * (β ^ 2 / 4) / F0 (β ^ 2 * t / 4) := by
    unfold G1; ring
  rw [e]
  exact h

theorem hasDerivAt_G1 (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : HasDerivAt (G1 β) (G2 β t) t := by
  have hF0 : HasDerivAt (fun t : ℝ => F0 (β ^ 2 * t / 4)) (F1 (β ^ 2 * t / 4) * (β ^ 2 / 4)) t := by
    have := (hasDerivAt_F0 (β ^ 2 * t / 4)).comp t (hasDerivAt_arg β t)
    exact this
  have hF1 : HasDerivAt (fun t : ℝ => F1 (β ^ 2 * t / 4)) (F2 (β ^ 2 * t / 4) * (β ^ 2 / 4)) t := by
    have := (hasDerivAt_F1 (β ^ 2 * t / 4)).comp t (hasDerivAt_arg β t)
    exact this
  have hne : F0 (β ^ 2 * t / 4) ≠ 0 := (F0_pos (arg_nonneg β ht)).ne'
  have h := (hF1.const_mul (β ^ 2 / 4)).fun_div hF0 hne
  have e : G2 β t = (β ^ 2 / 4 * (F2 (β ^ 2 * t / 4) * (β ^ 2 / 4)) * F0 (β ^ 2 * t / 4)
      - β ^ 2 / 4 * F1 (β ^ 2 * t / 4) * (F1 (β ^ 2 * t / 4) * (β ^ 2 / 4))) / F0 (β ^ 2 * t / 4) ^ 2 := by
    unfold G2; ring
  rw [e]
  exact h

theorem G1_nonneg (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ G1 β t := by
  unfold G1
  have h1 := F1_nonneg (arg_nonneg β ht)
  have h0 := F0_pos (arg_nonneg β ht)
  positivity

/-- `G' ≤ β²/8`。 -/
theorem G1_le (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : G1 β t ≤ β ^ 2 / 8 := by
  unfold G1
  have h0 := F0_pos (arg_nonneg β ht)
  have h2 := two_F1_le_F0 (arg_nonneg β ht)
  rw [div_le_iff₀ h0]
  nlinarith [sq_nonneg β]

/-- `G'' ≤ 0`。 -/
theorem G2_nonpos (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : G2 β t ≤ 0 := by
  unfold G2
  have h0 := F0_pos (arg_nonneg β ht)
  have h2 := turan_nonneg (arg_nonneg β ht)
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  linarith

theorem F1_zero : F1 0 = 1 / 2 := by
  unfold F1
  rw [tsum_eq_single 0]
  · simp [b]
  · intro k hk
    simp [hk]

/-- `t = 0` で等号：`G'(0) = β²/8`。 -/
theorem G1_zero (β : ℝ) : G1 β 0 = β ^ 2 / 8 := by
  unfold G1
  rw [mul_zero, zero_div, F0_zero, F1_zero]
  ring

/-- 曲線に沿った二階微分の下界：`(−G∘t)'' ≥ −(β²/8)·B`。 -/
theorem hess_lower (β B : ℝ) (t t1 : ℝ → ℝ) (t2 τ : ℝ) (hpos : ∀ s, 0 ≤ t s)
    (ht : ∀ s, HasDerivAt t (t1 s) s) (ht1 : HasDerivAt t1 t2 τ) (hB : t2 ≤ B) (hB0 : 0 ≤ B) :
    (∀ s, HasDerivAt (fun s => -G β (t s)) (-(G1 β (t s) * t1 s)) s) ∧
    ∃ D, HasDerivAt (fun s => -(G1 β (t s) * t1 s)) D τ ∧ -(β ^ 2 / 8) * B ≤ D := by
  refine ⟨fun s => ?_, ?_⟩
  · exact ((hasDerivAt_G β (hpos s)).comp s (ht s)).neg
  · refine ⟨-(G2 β (t τ) * t1 τ * t1 τ + G1 β (t τ) * t2), ?_, ?_⟩
    · have h1 : HasDerivAt (fun s => G1 β (t s)) (G2 β (t τ) * t1 τ) τ :=
        (hasDerivAt_G1 β (hpos τ)).comp τ (ht τ)
      exact (h1.mul ht1).neg
    · have g2 := G2_nonpos β (hpos τ)
      have g1 := G1_nonneg β (hpos τ)
      have g1' := G1_le β (hpos τ)
      have e1 : G2 β (t τ) * t1 τ * t1 τ ≤ 0 := by
        have : G2 β (t τ) * t1 τ * t1 τ = G2 β (t τ) * (t1 τ * t1 τ) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg g2 (mul_self_nonneg _)
      have e2 : G1 β (t τ) * t2 ≤ β ^ 2 / 8 * B :=
        (mul_le_mul_of_nonneg_left hB g1).trans (mul_le_mul_of_nonneg_right g1' hB0)
      linarith

/-- 数え上げ：各辺がちょうど 6 個の star に入る。 -/
theorem count27 {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E] (Es : S → Finset E)
    (h6 : ∀ e, (univ.filter (fun s => e ∈ Es s)).card = 6) (x : E → ℝ) (β : ℝ) (D : S → ℝ)
    (hD : ∀ s, -(β ^ 2 / 8) * (36 * ∑ e ∈ Es s, x e) ≤ D s) :
    -(27 * β ^ 2) * ∑ e, x e ≤ ∑ s, D s := by
  have hc : ∑ s, ∑ e ∈ Es s, x e = 6 * ∑ e, x e := by
    rw [Finset.sum_comm' (s' := fun e => univ.filter (fun s => e ∈ Es s)) (t' := univ)
      (by intro s e; simp)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_const, h6 e]
    simp
  calc -(27 * β ^ 2) * ∑ e, x e = ∑ s, -(β ^ 2 / 8) * (36 * ∑ e ∈ Es s, x e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, hc]; ring
    _ ≤ ∑ s, D s := Finset.sum_le_sum fun s _ => hD s

/-- 合成：`Φ(τ) = Σ_star −G(t_s(τ))` の二階微分 `≥ −27β² Σ_e x_e`。
仮定：star ごとに `t_s ≥ 0`・`t_s'' ≤ 36 Σ_{e ∈ star} x_e`（`StapleCurve.second_deriv_le` の形）・
`x_e ≥ 0`・各辺はちょうど 6 個の star に入る。 -/
theorem hess_total {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E] (Es : S → Finset E)
    (h6 : ∀ e, (univ.filter (fun s => e ∈ Es s)).card = 6) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e)
    (β τ : ℝ) (t t1 : S → ℝ → ℝ) (t2 : S → ℝ) (hpos : ∀ s u, 0 ≤ t s u)
    (ht : ∀ s u, HasDerivAt (t s) (t1 s u) u) (ht1 : ∀ s, HasDerivAt (t1 s) (t2 s) τ)
    (h36 : ∀ s, t2 s ≤ 36 * ∑ e ∈ Es s, x e) :
    (∀ u, HasDerivAt (fun u => ∑ s, -G β (t s u)) (∑ s, -(G1 β (t s u) * t1 s u)) u) ∧
    ∃ D, HasDerivAt (fun u => ∑ s, -(G1 β (t s u) * t1 s u)) D τ ∧
      -(27 * β ^ 2) * ∑ e, x e ≤ D := by
  have hl := fun s => hess_lower β (36 * ∑ e ∈ Es s, x e) (t s) (t1 s) (t2 s) τ (hpos s) (ht s)
    (ht1 s) (h36 s) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => hx e))
  refine ⟨fun u => HasDerivAt.fun_sum fun s _ => (hl s).1 u, ?_⟩
  choose D hD hDle using fun s => (hl s).2
  exact ⟨∑ s, D s, HasDerivAt.fun_sum fun s _ => hD s, count27 Es h6 x β D hDle⟩

end OneLinkSeries

#print axioms OneLinkSeries.G_eq_log_Z
#print axioms OneLinkSeries.hasDerivAt_G
#print axioms OneLinkSeries.hasDerivAt_G1
#print axioms OneLinkSeries.G1_nonneg
#print axioms OneLinkSeries.G1_le
#print axioms OneLinkSeries.G2_nonpos
#print axioms OneLinkSeries.G1_zero
#print axioms OneLinkSeries.hess_lower
#print axioms OneLinkSeries.count27
#print axioms OneLinkSeries.hess_total
end LogSeriesG

-- ===== 級数と角度表示の一致 =====
section SeriesAngleForm
/-
級数 `Z κ = F0 (κ²/4)` は一リンク積分の角度表示に等しい：
   Z κ = (2/π) ∫_0^π exp(κ cos θ) sin²θ dθ
（`S³` の一様測度の下で `u₀ = cos θ` の分布が `(2/π) sin²θ dθ` であること自体は紙。）
-/

open Finset Real MeasureTheory intervalIntegral

namespace OneLinkSeries

/-- `I n = ∫_0^π cos^n`。 -/
noncomputable def Icos (n : ℕ) : ℝ := ∫ θ in (0 : ℝ)..π, cos θ ^ n

theorem Icos_succ_succ (n : ℕ) : Icos (n + 2) = ((n : ℝ) + 1) / ((n : ℝ) + 2) * Icos n := by
  unfold Icos
  rw [integral_cos_pow]
  simp

theorem Icos_zero : Icos 0 = π := by
  unfold Icos
  simp

theorem Icos_one : Icos 1 = 0 := by
  unfold Icos
  simp

theorem Icos_odd (k : ℕ) : Icos (2 * k + 1) = 0 := by
  induction k with
  | zero => simpa using Icos_one
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Icos_succ_succ, ih, mul_zero]

theorem Icos_even (k : ℕ) :
    Icos (2 * k) = π * ((2 * k).factorial : ℝ) / ((4 : ℝ) ^ k * (k.factorial : ℝ) ^ 2) := by
  induction k with
  | zero => simpa using Icos_zero
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, Icos_succ_succ, ih]
    have h1 : ((2 * k + 2).factorial : ℝ)
        = ((2 * k : ℕ) + 2 : ℝ) * (((2 * k : ℕ) : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have h2 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h3 : (k.factorial : ℝ) ≠ 0 := fac_ne k
    rw [h1, h2]
    push_cast
    have h4 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    have h5 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- モーメント `m n = ∫_0^π cos^n sin²`。 -/
noncomputable def mom (n : ℕ) : ℝ := ∫ θ in (0 : ℝ)..π, cos θ ^ n * sin θ ^ 2

theorem mom_eq (n : ℕ) : mom n = Icos n / ((n : ℝ) + 2) := by
  have h : mom n = Icos n - Icos (n + 2) := by
    unfold mom Icos
    rw [← intervalIntegral.integral_sub]
    · refine integral_congr fun θ _ => ?_
      have := sin_sq_add_cos_sq θ
      have e : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith
      simp only [e]
      ring
    · exact (by fun_prop : Continuous fun θ : ℝ => cos θ ^ n).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ : ℝ => cos θ ^ (n + 2)).intervalIntegrable _ _
  rw [h, Icos_succ_succ]
  have h4 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem mom_odd (k : ℕ) : mom (2 * k + 1) = 0 := by
  rw [mom_eq, Icos_odd, zero_div]

theorem mom_even (k : ℕ) (κ : ℝ) :
    κ ^ (2 * k) / ((2 * k).factorial : ℝ) * mom (2 * k) = π / 2 * (a ℝ k * (κ ^ 2 / 4) ^ k) := by
  rw [mom_eq, Icos_even]
  unfold a
  have h2 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h3 : (k.factorial : ℝ) ≠ 0 := fac_ne k
  have h3' : ((2 * k).factorial : ℝ) ≠ 0 := fac_ne (2 * k)
  have h5 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [h2, div_pow, pow_mul]
  push_cast
  have h6 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  field_simp

/-- 和と積分の交換。 -/
theorem hasSum_integral (κ : ℝ) :
    HasSum (fun n : ℕ => κ ^ n / (n.factorial : ℝ) * mom n)
      (∫ θ in (0 : ℝ)..π, exp (κ * cos θ) * sin θ ^ 2) := by
  have key := hasSum_integral_of_dominated_convergence (μ := volume) (a := (0 : ℝ)) (b := π)
    (F := fun (n : ℕ) (θ : ℝ) => (κ * cos θ) ^ n / (n.factorial : ℝ) * sin θ ^ 2)
    (f := fun θ => exp (κ * cos θ) * sin θ ^ 2)
    (fun (n : ℕ) (_ : ℝ) => |κ| ^ n / (n.factorial : ℝ))
    (fun n => (by fun_prop : Continuous fun θ : ℝ =>
      (κ * cos θ) ^ n / (n.factorial : ℝ) * sin θ ^ 2).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun θ _ => by
      simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs, Nat.abs_cast]
      have hc : |cos θ| ≤ 1 := abs_cos_le_one θ
      have hs : |sin θ| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_sin_le_one θ)
      have h1 : (|κ| * |cos θ|) ^ n ≤ |κ| ^ n :=
        pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (abs_nonneg κ) hc) n
      have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
      calc (|κ| * |cos θ|) ^ n / (n.factorial : ℝ) * |sin θ| ^ 2
          ≤ |κ| ^ n / (n.factorial : ℝ) * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right h1 hf.le) hs (by positivity) (by positivity)
        _ = |κ| ^ n / (n.factorial : ℝ) := mul_one _)
    (Filter.Eventually.of_forall fun θ _ => Real.summable_pow_div_factorial |κ|)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => by
      have h := (NormedSpace.expSeries_div_hasSum_exp (κ * cos θ)).mul_right (sin θ ^ 2)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h)
  have e : (fun n : ℕ => κ ^ n / (n.factorial : ℝ) * mom n)
      = fun n : ℕ => ∫ θ in (0 : ℝ)..π, (κ * cos θ) ^ n / (n.factorial : ℝ) * sin θ ^ 2 := by
    funext n
    unfold mom
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun θ _ => ?_
    simp only [mul_pow]
    ring
  rw [e]
  exact key

/-- `Z κ = (2/π) ∫_0^π e^{κ cos θ} sin²θ dθ`。 -/
theorem Z_eq_integral (κ : ℝ) :
    Z κ = 2 / π * ∫ θ in (0 : ℝ)..π, exp (κ * cos θ) * sin θ ^ 2 := by
  have he : HasSum (fun k : ℕ => κ ^ (2 * k) / ((2 * k).factorial : ℝ) * mom (2 * k))
      (π / 2 * F0 (κ ^ 2 / 4)) := by
    have h := ((summable_term a_bound (κ ^ 2 / 4)).hasSum).mul_left (π / 2)
    have e : (fun k : ℕ => κ ^ (2 * k) / ((2 * k).factorial : ℝ) * mom (2 * k))
        = fun k : ℕ => π / 2 * (a ℝ k * (κ ^ 2 / 4) ^ k) := funext fun k => mom_even k κ
    rw [e]
    exact h
  have ho : HasSum (fun k : ℕ => κ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * mom (2 * k + 1))
      0 := by
    have e : (fun k : ℕ => κ ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * mom (2 * k + 1))
        = fun _ : ℕ => (0 : ℝ) := funext fun k => by rw [mom_odd, mul_zero]
    rw [e]
    exact hasSum_zero
  have hs : HasSum (fun n : ℕ => κ ^ n / (n.factorial : ℝ) * mom n) (π / 2 * F0 (κ ^ 2 / 4) + 0) :=
    HasSum.even_add_odd (f := fun n : ℕ => κ ^ n / (n.factorial : ℝ) * mom n) he ho
  have h := hs.unique (hasSum_integral κ)
  unfold Z
  rw [← h]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end OneLinkSeries

#print axioms OneLinkSeries.Icos_even
#print axioms OneLinkSeries.mom_even
#print axioms OneLinkSeries.hasSum_integral
#print axioms OneLinkSeries.Z_eq_integral
end SeriesAngleForm

-- ===== 合成：star の族の Hesse 下界 =====
section StarFamilyHessian
/-
四元数の staple 曲線の橋（`t'' ≤ 36Σ‖·‖²`）と Bessel の二不等式・数え上げの合成。
  star の族 `S`・辺の集合 `E`・各 star の辺集合 `Es s`・各辺はちょうど 6 個の star に入る。
  star `s` の 6 本の staple 曲線 `curve (q s i) (A s i) (B s i) (C s i)`（`‖q s i‖ = 1`・`A,B,C` は虚）。
  `Σ_i (‖A s i‖²+‖B s i‖²+‖C s i‖²) ≤ Σ_{e ∈ Es s} x e`（格子の上では等号——18 辺が相異なり `Ad` が等長）。
  結論：`Φ(τ) = Σ_s −G β ‖Σ_i curve_i τ‖²` について `Φ''(0) ≥ −27β² Σ_e x_e`。
-/

open Finset Quaternion NormedSpace

namespace OneLinkSeries

open StapleCurve

theorem hasDerivAt_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (M M' : ℝ → V) (h1 : ∀ τ, HasDerivAt M (M' τ) τ) (τ : ℝ) :
    HasDerivAt (fun τ => ‖M τ‖ ^ 2) (2 * inner ℝ (M τ) (M' τ)) τ := by
  have e : (fun τ => ‖M τ‖ ^ 2) = fun τ => inner ℝ (M τ) (M τ) := by
    funext σ; rw [real_inner_self_eq_norm_sq]
  rw [e]
  have h := HasDerivAt.inner ℝ (h1 τ) (h1 τ)
  rw [real_inner_comm (M τ) (M' τ)] at h
  exact h.congr_deriv (two_mul _).symm

theorem hasDerivAt_norm_sq' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (M M' : ℝ → V) (M'' : V) (h1 : ∀ τ, HasDerivAt M (M' τ) τ) (h2 : HasDerivAt M' M'' 0) :
    HasDerivAt (fun τ => 2 * inner ℝ (M τ) (M' τ))
      (2 * ‖M' 0‖ ^ 2 + 2 * inner ℝ (M 0) M'') 0 := by
  have h := (HasDerivAt.inner ℝ (h1 0) h2).const_mul (2 : ℝ)
  rw [real_inner_self_eq_norm_sq] at h
  exact h.congr_deriv (by ring)

/-- star の族の Hesse 下界——解析の部分（格子の幾何は仮定に置いた形）。 -/
theorem hess_star_family {S E : Type*} [Fintype S] [Fintype E] [DecidableEq E]
    (Es : S → Finset E) (h6 : ∀ e, (univ.filter (fun s => e ∈ Es s)).card = 6)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e) (β : ℝ)
    (q A B C : S → Fin 6 → ℍ[ℝ]) (hq : ∀ s i, ‖q s i‖ = 1)
    (hA : ∀ s i, (A s i).re = 0) (hB : ∀ s i, (B s i).re = 0) (hC : ∀ s i, (C s i).re = 0)
    (hslot : ∀ s, ∑ i, (‖A s i‖ ^ 2 + ‖B s i‖ ^ 2 + ‖C s i‖ ^ 2) ≤ ∑ e ∈ Es s, x e) :
    -(27 * β ^ 2) * ∑ e, x e ≤
      deriv (deriv (fun τ => ∑ s, -G β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2))) 0 := by
  have h1 : ∀ s τ, HasDerivAt (fun τ => ∑ i, curve (q s i) (A s i) (B s i) (C s i) τ)
      (∑ i, curve' (q s i) (A s i) (B s i) (C s i) τ) τ := fun s τ =>
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve (q s i) (A s i) (B s i) (C s i) τ
  have h2 : ∀ s, HasDerivAt (fun τ => ∑ i, curve' (q s i) (A s i) (B s i) (C s i) τ)
      (∑ i, q s i * D2 (A s i) (B s i) (C s i)) 0 := fun s =>
    HasDerivAt.fun_sum fun i _ => hasDerivAt_curve'_zero (q s i) (A s i) (B s i) (C s i)
  have ht := fun s u => hasDerivAt_norm_sq _ _ (h1 s) u
  have ht1 := fun s => hasDerivAt_norm_sq' _ _ _ (h1 s) (h2 s)
  have h36 : ∀ s, 2 * ‖∑ i, curve' (q s i) (A s i) (B s i) (C s i) 0‖ ^ 2
      + 2 * inner ℝ (∑ i, curve (q s i) (A s i) (B s i) (C s i) 0)
          (∑ i, q s i * D2 (A s i) (B s i) (C s i)) ≤ 36 * ∑ e ∈ Es s, x e := by
    intro s
    have e : 2 * ‖∑ i, curve' (q s i) (A s i) (B s i) (C s i) 0‖ ^ 2
      + 2 * inner ℝ (∑ i, curve (q s i) (A s i) (B s i) (C s i) 0)
          (∑ i, q s i * D2 (A s i) (B s i) (C s i)) = hessForm (q s) (A s) (B s) (C s) := by
      simp only [curve_zero, curve'_zero, hessForm]
    rw [e]
    exact (hessForm_le (q s) (A s) (B s) (C s) (hq s) (hA s) (hB s) (hC s)).trans
      (mul_le_mul_of_nonneg_left (hslot s) (by norm_num))
  obtain ⟨hΦ, D, hD, hle⟩ := hess_total Es h6 x hx β 0
    (fun s τ => ‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2)
    (fun s τ => 2 * inner ℝ (∑ i, curve (q s i) (A s i) (B s i) (C s i) τ)
      (∑ i, curve' (q s i) (A s i) (B s i) (C s i) τ))
    _ (fun s u => by positivity) ht ht1 h36
  have hd : deriv (fun τ => ∑ s, -G β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2))
      = fun u => ∑ s, -(G1 β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) u‖ ^ 2)
          * (2 * inner ℝ (∑ i, curve (q s i) (A s i) (B s i) (C s i) u)
              (∑ i, curve' (q s i) (A s i) (B s i) (C s i) u))) := by
    funext u
    exact (hΦ u).deriv
  rw [hd, hD.deriv]
  exact hle

end OneLinkSeries

#print axioms OneLinkSeries.hess_star_family
end StarFamilyHessian

section LatticeFamily
/-
`d = 4` の周期格子 `(ZMod L)⁴`（`L` 偶数）の辺の族 `I*`（mod 2 の条件で書いた一例）。
  C0：型（頂点 `V L`・辺 `Edge L = V L × Fin 4`・プラケット `(x, μ, ν)` の 4 辺 `InP`）
  C1：全プラケットはちょうど一本の `I*` の辺を含む（`plaq_unique`）。
      有限部分は `(ZMod 2)⁴ × Fin 4 × Fin 4` の上の `decide`（`one_mod2`）。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

namespace CompleteFamilyLattice

/-- mod 2 の座標 `(a,b,c,d) = (x₁,x₂,x₃,x₄)` で書いた `I*`：
`I_1 : x₂ = x₃ ≠ x₄`・`I_2 : x₃ = x₄ ≠ x₁`・`I_3 : x₁ = x₂ = x₄`・`I_4 : x₁ = x₃ ≠ x₂`。 -/
def I2 (a b c d : ZMod 2) (μ : Fin 4) : Bool :=
  match μ with
  | 0 => decide (b = c ∧ c ≠ d)
  | 1 => decide (c = d ∧ d ≠ a)
  | 2 => decide (a = b ∧ b = d)
  | 3 => decide (a = c ∧ c ≠ b)

/-- `e_μ` の第 `i` 成分（mod 2）。 -/
def sh (μ i : Fin 4) : ZMod 2 := if i = μ then 1 else 0

/-- 点 `z + e_μ` から出る方向 `ρ` の辺が `I*` か。 -/
def I2s (a b c d : ZMod 2) (μ ρ : Fin 4) : Bool :=
  I2 (a + sh μ 0) (b + sh μ 1) (c + sh μ 2) (d + sh μ 3) ρ

/-- C1 の有限部分：`(ZMod 2)⁴` の各点・各 `μ ≠ ν` で、4 辺のうち `I*` はちょうど一本。 -/
theorem one_mod2 : ∀ a b c d : ZMod 2, ∀ μ ν : Fin 4, μ ≠ ν →
    (I2 a b c d μ).toNat + (I2s a b c d μ ν).toNat + (I2s a b c d ν μ).toNat
      + (I2 a b c d ν).toNat = 1 := by
  decide

theorem one_of_four : ∀ p q r s : Bool, p.toNat + q.toNat + r.toNat + s.toNat = 1 →
    (p = true ∧ q = false ∧ r = false ∧ s = false) ∨
    (p = false ∧ q = true ∧ r = false ∧ s = false) ∨
    (p = false ∧ q = false ∧ r = true ∧ s = false) ∨
    (p = false ∧ q = false ∧ r = false ∧ s = true) := by
  decide

section lattice

variable {L : ℕ}

/-- 頂点。 -/
abbrev V (L : ℕ) := Fin 4 → ZMod L

/-- 辺 `(x, μ)`：`x` から `x + e_μ` へ。 -/
abbrev Edge (L : ℕ) := V L × Fin 4

/-- 単位ベクトル `e_μ`。 -/
def ev (μ : Fin 4) : V L := Pi.single μ 1

/-- mod 2 への還元（`L` は偶数）。 -/
def red (h2 : 2 ∣ L) (t : ZMod L) : ZMod 2 := ZMod.castHom h2 (ZMod 2) t

/-- 辺の族 `I*`。 -/
def Istar (h2 : 2 ∣ L) (e : Edge L) : Prop :=
  I2 (red h2 (e.1 0)) (red h2 (e.1 1)) (red h2 (e.1 2)) (red h2 (e.1 3)) e.2 = true

theorem red_shift (h2 : 2 ∣ L) (x : V L) (μ i : Fin 4) :
    red h2 ((x + (ev μ : V L)) i) = red h2 (x i) + sh μ i := by
  unfold red ev sh
  rw [Pi.add_apply, map_add, Pi.single_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem Istar_shift (h2 : 2 ∣ L) (x : V L) (μ ρ : Fin 4) :
    Istar h2 (x + ev μ, ρ) ↔
      I2s (red h2 (x 0)) (red h2 (x 1)) (red h2 (x 2)) (red h2 (x 3)) μ ρ = true := by
  unfold Istar I2s
  simp only [red_shift]

/-- 辺 `e` がプラケット `(x, μ, ν)` の 4 辺のどれかであること。 -/
def InP (e : Edge L) (x : V L) (μ ν : Fin 4) : Prop :=
  e = (x, μ) ∨ e = (x + ev μ, ν) ∨ e = (x + ev ν, μ) ∨ e = (x, ν)

theorem InP_symm (e : Edge L) (x : V L) (μ ν : Fin 4) : InP e x μ ν ↔ InP e x ν μ := by
  unfold InP; tauto

/-- **C1**：全プラケットは `I*` の辺をちょうど一本含む。 -/
theorem plaq_unique (h2 : 2 ∣ L) (x : V L) (μ ν : Fin 4) (h : μ ≠ ν) :
    ∃! e : Edge L, InP e x μ ν ∧ Istar h2 e := by
  have h1 := one_of_four _ _ _ _
    (one_mod2 (red h2 (x 0)) (red h2 (x 1)) (red h2 (x 2)) (red h2 (x 3)) μ ν h)
  have e1 : Istar h2 (x, μ) ↔
      I2 (red h2 (x 0)) (red h2 (x 1)) (red h2 (x 2)) (red h2 (x 3)) μ = true := Iff.rfl
  have e4 : Istar h2 (x, ν) ↔
      I2 (red h2 (x 0)) (red h2 (x 1)) (red h2 (x 2)) (red h2 (x 3)) ν = true := Iff.rfl
  have e2 := Istar_shift h2 x μ ν
  have e3 := Istar_shift h2 x ν μ
  rcases h1 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
  · refine ⟨(x, μ), ⟨Or.inl rfl, e1.2 a1⟩, ?_⟩
    rintro e ⟨hin, hI⟩
    rcases hin with rfl | rfl | rfl | rfl
    · rfl
    · rw [e2, a2] at hI; exact absurd hI (by decide)
    · rw [e3, a3] at hI; exact absurd hI (by decide)
    · rw [e4, a4] at hI; exact absurd hI (by decide)
  · refine ⟨(x + ev μ, ν), ⟨Or.inr (Or.inl rfl), e2.2 a2⟩, ?_⟩
    rintro e ⟨hin, hI⟩
    rcases hin with rfl | rfl | rfl | rfl
    · rw [e1, a1] at hI; exact absurd hI (by decide)
    · rfl
    · rw [e3, a3] at hI; exact absurd hI (by decide)
    · rw [e4, a4] at hI; exact absurd hI (by decide)
  · refine ⟨(x + ev ν, μ), ⟨Or.inr (Or.inr (Or.inl rfl)), e3.2 a3⟩, ?_⟩
    rintro e ⟨hin, hI⟩
    rcases hin with rfl | rfl | rfl | rfl
    · rw [e1, a1] at hI; exact absurd hI (by decide)
    · rw [e2, a2] at hI; exact absurd hI (by decide)
    · rfl
    · rw [e4, a4] at hI; exact absurd hI (by decide)
  · refine ⟨(x, ν), ⟨Or.inr (Or.inr (Or.inr rfl)), e4.2 a4⟩, ?_⟩
    rintro e ⟨hin, hI⟩
    rcases hin with rfl | rfl | rfl | rfl
    · rw [e1, a1] at hI; exact absurd hI (by decide)
    · rw [e2, a2] at hI; exact absurd hI (by decide)
    · rw [e3, a3] at hI; exact absurd hI (by decide)
    · rfl

/-- プラケットを `μ < ν` で数える形。 -/
theorem plaq_unique_lt (h2 : 2 ∣ L) (x : V L) (μ ν : Fin 4) (h : μ < ν) :
    ∃! e : Edge L, InP e x μ ν ∧ Istar h2 e :=
  plaq_unique h2 x μ ν (ne_of_lt h)

end lattice

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.one_mod2
#print axioms CompleteFamilyLattice.one_of_four
#print axioms CompleteFamilyLattice.red_shift
#print axioms CompleteFamilyLattice.Istar_shift
#print axioms CompleteFamilyLattice.plaq_unique
#print axioms CompleteFamilyLattice.plaq_unique_lt

end LatticeFamily

section LatticeStarCount
/-
C2。`L ≥ 3`（`(2 : ZMod L) ≠ 0`）・`L` 偶数のとき、`I*` でない各辺は
ちょうど 6 個の star（＝`I*` の辺）に入る（`star_count`）。
  star `s`（`I*` の辺）の辺集合 `Es s`＝`s` と同じプラケットに入る非 `I*` 辺の全体。
  辺 `(x, μ)` を含むプラケットは `(base x ν σ, μ, ν)`（`ν ≠ μ`・`σ : Bool`）の 6 枚（`InP_cases`）。
  相異なる 2 枚は `(x, μ)` 以外の辺を共有しない（`star_inj`・ここで `2 ≠ 0` を使う）。
-/

open Finset

namespace CompleteFamilyLattice

variable {L : ℕ}

theorem ev_same (ν : Fin 4) : (ev ν : V L) ν = 1 := by
  unfold ev; rw [Pi.single_eq_same]

theorem ev_ne {i ν : Fin 4} (h : i ≠ ν) : (ev ν : V L) i = 0 := by
  unfold ev; rw [Pi.single_eq_of_ne h]

theorem two_ne_zero_of_le (hL : 3 ≤ L) : (2 : ZMod L) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod L) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

/-- 辺 `(x, μ)` を含む 6 枚のプラケット `(base x ν σ, μ, ν)` の基点。`σ = true` が前向き。 -/
def base (x : V L) (ν : Fin 4) (σ : Bool) : V L := if σ then x else x - ev ν

theorem InP_base (x : V L) (μ ν : Fin 4) (σ : Bool) : InP (x, μ) (base x ν σ) μ ν := by
  cases σ
  · right; right; left
    simp [base]
  · left
    simp [base]

/-- `(x, μ)` を含むプラケットは 6 枚のどれか（辺集合として）。 -/
theorem InP_cases (x : V L) (μ : Fin 4) (y : V L) (α β : Fin 4) (hαβ : α ≠ β)
    (h : InP (x, μ) y α β) :
    ∃ ν σ, ν ≠ μ ∧ ∀ e : Edge L, InP e y α β ↔ InP e (base x ν σ) μ ν := by
  rcases h with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  · exact ⟨β, true, hαβ.symm, fun e => by simp [base]⟩
  · refine ⟨α, false, hαβ, fun e => ?_⟩
    have : base (y + ev α) α false = y := by simp [base]
    rw [this]
    exact InP_symm e y α μ
  · refine ⟨β, false, hαβ.symm, fun _ => ?_⟩
    have : base (y + ev β) β false = y := by simp [base]
    rw [this]
  · exact ⟨α, true, hαβ, fun e => by simpa [base] using InP_symm e x α μ⟩

/-- プラケット `(base x ν σ, μ, ν)` の `(x, μ)` 以外の辺 `(y, d)` から `ν`・`σ` が読める。 -/
theorem key (hL : (2 : ZMod L) ≠ 0) (x : V L) (μ ν : Fin 4) (hν : ν ≠ μ) (σ : Bool)
    (y : V L) (d : Fin 4) (hs : InP (y, d) (base x ν σ) μ ν) (hne : (y, d) ≠ (x, μ)) :
    (d = ν ∨ (d = μ ∧ y ν ≠ x ν)) ∧ (∀ ν', ν' ≠ ν → ν' ≠ μ → y ν' = x ν') ∧
      (y ν = x ν - 1 ↔ σ = false) := by
  have h10 : (1 : ZMod L) ≠ 0 := by
    intro h; apply hL; rw [← one_add_one_eq_two, h, add_zero]
  have f1 : ∀ a : ZMod L, a - 1 ≠ a := fun a h => h10 (by linear_combination -h)
  have f2 : ∀ a : ZMod L, a + 1 ≠ a - 1 := fun a h => hL (by linear_combination h)
  have f3 : ∀ a : ZMod L, a ≠ a - 1 := fun a h => h10 (by linear_combination h)
  have f4 : ∀ a : ZMod L, a + 1 ≠ a := fun a h => h10 (by linear_combination h)
  cases σ
  · have hb : base x ν false = x - ev ν := by simp [base]
    rw [hb] at hs
    rcases hs with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · refine ⟨Or.inr ⟨rfl, ?_⟩, fun ν' h1 _ => ?_, ?_⟩
      · rw [Pi.sub_apply, ev_same]; exact f1 _
      · rw [Pi.sub_apply, ev_ne h1, sub_zero]
      · rw [Pi.sub_apply, ev_same]; simp
    · refine ⟨Or.inl rfl, fun ν' h1 h2 => ?_, ?_⟩
      · rw [Pi.add_apply, Pi.sub_apply, ev_ne h1, ev_ne h2, sub_zero, add_zero]
      · rw [Pi.add_apply, Pi.sub_apply, ev_same, ev_ne hν, add_zero]; simp
    · exact absurd (by rw [sub_add_cancel]) hne
    · refine ⟨Or.inl rfl, fun ν' h1 _ => ?_, ?_⟩
      · rw [Pi.sub_apply, ev_ne h1, sub_zero]
      · rw [Pi.sub_apply, ev_same]; simp
  · have hb : base x ν true = x := by simp [base]
    rw [hb] at hs
    rcases hs with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    · exact absurd rfl hne
    · refine ⟨Or.inl rfl, fun ν' _ h2 => ?_, ?_⟩
      · rw [Pi.add_apply, ev_ne h2, add_zero]
      · rw [Pi.add_apply, ev_ne hν, add_zero]; simpa using f3 _
    · refine ⟨Or.inr ⟨rfl, ?_⟩, fun ν' h1 _ => ?_, ?_⟩
      · rw [Pi.add_apply, ev_same]; exact f4 _
      · rw [Pi.add_apply, ev_ne h1, add_zero]
      · rw [Pi.add_apply, ev_same]; simpa using f2 _
    · refine ⟨Or.inl rfl, fun ν' _ _ => rfl, ?_⟩
      simpa using f3 _

/-- `(x, μ)` を含む相異なる 2 枚のプラケットは、`(x, μ)` 以外の辺を共有しない。 -/
theorem star_inj (hL : (2 : ZMod L) ≠ 0) (x : V L) (μ ν ν' : Fin 4) (hν : ν ≠ μ) (hν' : ν' ≠ μ)
    (σ σ' : Bool) (s : Edge L) (hne : s ≠ (x, μ)) (h1 : InP s (base x ν σ) μ ν)
    (h2 : InP s (base x ν' σ') μ ν') : ν = ν' ∧ σ = σ' := by
  obtain ⟨y, d⟩ := s
  obtain ⟨a1, b1, c1⟩ := key hL x μ ν hν σ y d h1 hne
  obtain ⟨a2, b2, c2⟩ := key hL x μ ν' hν' σ' y d h2 hne
  by_cases hνν : ν = ν'
  · subst hνν
    refine ⟨rfl, ?_⟩
    have : σ = false ↔ σ' = false := c1.symm.trans c2
    cases σ <;> cases σ' <;> simp_all
  · exfalso
    have e1 : y ν = x ν := b2 ν hνν hν
    rcases a1 with rfl | ⟨rfl, h⟩
    · rcases a2 with h' | ⟨h', _⟩
      · exact hνν h'
      · exact hν h'
    · exact h e1

section family

variable [NeZero L] (h2 : 2 ∣ L)

instance : DecidablePred (Istar (L := L) h2) := fun _ =>
  inferInstanceAs (Decidable (I2 _ _ _ _ _ = true))

/-- star の族＝`I*` の辺。 -/
abbrev Star := {e : Edge L // Istar h2 e}

/-- 残る辺＝`I*` でない辺。 -/
abbrev Rest := {e : Edge L // ¬ Istar h2 e}

/-- star `s` の辺集合：`s` と同じプラケットに入る非 `I*` 辺。 -/
noncomputable def Es (s : Star h2) : Finset (Rest h2) := by
  classical
  exact univ.filter (fun e => ∃ y α β, α ≠ β ∧ InP s.1 y α β ∧ InP e.1 y α β)

theorem mem_Es (s : Star h2) (e : Rest h2) :
    e ∈ Es h2 s ↔ ∃ y α β, α ≠ β ∧ InP s.1 y α β ∧ InP e.1 y α β := by
  unfold Es
  simp

/-- 辺 `(x, μ)` を含む 6 枚のプラケットの `I*` 辺。 -/
noncomputable def st (x : V L) (μ : Fin 4) (k : {ν : Fin 4 // ν ≠ μ} × Bool) : Star h2 :=
  ⟨(plaq_unique h2 (base x k.1.1 k.2) μ k.1.1 k.1.2.symm).exists.choose,
    (plaq_unique h2 (base x k.1.1 k.2) μ k.1.1 k.1.2.symm).exists.choose_spec.2⟩

omit [NeZero L] in
theorem st_in (x : V L) (μ : Fin 4) (k : {ν : Fin 4 // ν ≠ μ} × Bool) :
    InP (st h2 x μ k).1 (base x k.1.1 k.2) μ k.1.1 :=
  (plaq_unique h2 (base x k.1.1 k.2) μ k.1.1 k.1.2.symm).exists.choose_spec.1

omit [NeZero L] in
theorem st_injective (hL : (2 : ZMod L) ≠ 0) (x : V L) (μ : Fin 4) (he : ¬ Istar h2 (x, μ)) :
    Function.Injective (st h2 x μ) := by
  intro k k' hk
  have hne : (st h2 x μ k).1 ≠ (x, μ) := fun h => he (h ▸ (st h2 x μ k).2)
  have h1 := st_in h2 x μ k
  have h1' := st_in h2 x μ k'
  rw [← hk] at h1'
  obtain ⟨hν, hσ⟩ := star_inj hL x μ k.1.1 k'.1.1 k.1.2 k'.1.2 k.2 k'.2 _ hne h1 h1'
  exact Prod.ext (Subtype.ext hν) hσ

theorem card_K : ∀ μ : Fin 4, Fintype.card ({ν : Fin 4 // ν ≠ μ} × Bool) = 6 := by
  decide

/-- **C2**：`I*` でない各辺は、ちょうど 6 個の star に入る（`hess_star_family` の `h6` の形）。 -/
theorem star_count (hL : (2 : ZMod L) ≠ 0) (e : Rest h2) :
    (univ.filter (fun s => e ∈ Es h2 s)).card = 6 := by
  obtain ⟨⟨x, μ⟩, he⟩ := e
  have himg : univ.filter (fun s => (⟨(x, μ), he⟩ : Rest h2) ∈ Es h2 s)
      = univ.image (st h2 x μ) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_Es]
    constructor
    · rintro ⟨y, α, β, hαβ, hs, hin⟩
      obtain ⟨ν, σ, hν, hiff⟩ := InP_cases x μ y α β hαβ hin
      refine ⟨(⟨ν, hν⟩, σ), ?_⟩
      apply Subtype.ext
      exact (plaq_unique h2 (base x ν σ) μ ν hν.symm).unique
        ⟨st_in h2 x μ (⟨ν, hν⟩, σ), (st h2 x μ (⟨ν, hν⟩, σ)).2⟩ ⟨(hiff _).1 hs, s.2⟩
    · rintro ⟨k, rfl⟩
      exact ⟨base x k.1.1 k.2, μ, k.1.1, k.1.2.symm, st_in h2 x μ k, InP_base x μ k.1.1 k.2⟩
  rw [himg, card_image_of_injective _ (st_injective h2 hL x μ he), card_univ, card_K]

end family

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.two_ne_zero_of_le
#print axioms CompleteFamilyLattice.InP_base
#print axioms CompleteFamilyLattice.InP_cases
#print axioms CompleteFamilyLattice.key
#print axioms CompleteFamilyLattice.star_inj
#print axioms CompleteFamilyLattice.mem_Es
#print axioms CompleteFamilyLattice.st_injective
#print axioms CompleteFamilyLattice.card_K
#print axioms CompleteFamilyLattice.star_count

end LatticeStarCount

section LatticeHessian
/-
C3。`OneLinkSeries.hess_star_family` の仮定 `h6` を、周期格子 `(ZMod L)⁴`（`L` 偶数・`L ≥ 3`、
つまり `L ≥ 4`）の `I*` の族で満たした形。`S = Star h2`（`I*` の辺）・`E = Rest h2`（非 `I*` 辺）・
`Es s`＝`s` と同じプラケットに入る非 `I*` 辺。仮定 `hslot`（star の 6 本の staple の 18 個の
Lie 環成分の二乗和 ≤ `Σ_{e ∈ Es s} x e`）は格子の上で等号になるはずのもの——ここでは仮定のまま。
-/

open Finset Quaternion

namespace CompleteFamilyLattice

open OneLinkSeries StapleCurve

theorem hess_lattice {L : ℕ} [NeZero L] (h2 : 2 ∣ L) (hL : 3 ≤ L)
    (x : Rest h2 → ℝ) (hx : ∀ e, 0 ≤ x e) (β : ℝ)
    (q A B C : Star h2 → Fin 6 → ℍ[ℝ]) (hq : ∀ s i, ‖q s i‖ = 1)
    (hA : ∀ s i, (A s i).re = 0) (hB : ∀ s i, (B s i).re = 0) (hC : ∀ s i, (C s i).re = 0)
    (hslot : ∀ s, ∑ i, (‖A s i‖ ^ 2 + ‖B s i‖ ^ 2 + ‖C s i‖ ^ 2) ≤ ∑ e ∈ Es h2 s, x e) :
    -(27 * β ^ 2) * ∑ e, x e ≤
      deriv (deriv (fun τ => ∑ s, -G β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2))) 0 :=
  hess_star_family (Es h2) (star_count h2 (two_ne_zero_of_le hL)) x hx β q A B C hq hA hB hC hslot

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.hess_lattice

end LatticeHessian

section LatticeStarEdges
/-
star の辺集合はちょうど 18 本（`L` 偶数・`(2 : ZMod L) ≠ 0`）。
  `I*` の辺 `(x, μ)` を含む 6 枚のプラケットの、`(x, μ)` 以外の 3 辺ずつ `oth x μ ν σ j` が
  全部相異なり（`oth_injective`）、`Es s` はその像（`Es_card`）。
-/

open Finset

namespace CompleteFamilyLattice

variable {L : ℕ}

inductive J | a | b | c
  deriving DecidableEq

instance : Fintype J := ⟨{J.a, J.b, J.c}, fun j => by cases j <;> simp⟩

/-- プラケット `(base x ν σ, μ, ν)` の、`(x, μ)` 以外の 3 辺。 -/
def oth (x : V L) (μ ν : Fin 4) (σ : Bool) (j : J) : Edge L :=
  match σ, j with
  | true, J.a => (x + ev μ, ν)
  | true, J.b => (x + ev ν, μ)
  | true, J.c => (x, ν)
  | false, J.a => (x - ev ν, μ)
  | false, J.b => (x - ev ν + ev μ, ν)
  | false, J.c => (x - ev ν, ν)

theorem oth_in (x : V L) (μ ν : Fin 4) (σ : Bool) (j : J) :
    InP (oth x μ ν σ j) (base x ν σ) μ ν := by
  cases σ <;> cases j <;> simp [oth, base, InP]

theorem oth_ne (h10 : (1 : ZMod L) ≠ 0) (x : V L) (μ ν : Fin 4) (hν : ν ≠ μ) (σ : Bool) (j : J) :
    oth x μ ν σ j ≠ (x, μ) := by
  intro h
  cases σ <;> cases j <;> obtain ⟨h1, h2⟩ := Prod.mk.inj h <;>
    first
    | exact hν h2
    | (have := congrFun h1 ν
       simp [ev_same, h10] at this)

theorem oth_surj (x : V L) (μ ν : Fin 4) (σ : Bool) (t : Edge L)
    (ht : InP t (base x ν σ) μ ν) (hne : t ≠ (x, μ)) : ∃ j, oth x μ ν σ j = t := by
  cases σ
  · have hb : base x ν false = x - ev ν := by simp [base]
    rw [hb] at ht
    rcases ht with h | h | h | h
    · exact ⟨J.a, h.symm⟩
    · exact ⟨J.b, h.symm⟩
    · exact absurd (by rw [h, sub_add_cancel]) hne
    · exact ⟨J.c, h.symm⟩
  · have hb : base x ν true = x := by simp [base]
    rw [hb] at ht
    rcases ht with h | h | h | h
    · exact absurd h hne
    · exact ⟨J.a, h.symm⟩
    · exact ⟨J.b, h.symm⟩
    · exact ⟨J.c, h.symm⟩

theorem oth_inj_j (h10 : (1 : ZMod L) ≠ 0) (x : V L) (μ ν : Fin 4) (hν : ν ≠ μ) (σ : Bool)
    (j j' : J) (h : oth x μ ν σ j = oth x μ ν σ j') : j = j' := by
  cases σ <;> cases j <;> cases j' <;>
    first
    | rfl
    | (exfalso
       obtain ⟨h1, h2⟩ := Prod.mk.inj h
       first
       | exact hν h2
       | exact hν h2.symm
       | (have := congrFun h1 μ
          simp [ev_same, ev_ne hν.symm, h10] at this))

theorem oth_injective (hL : (2 : ZMod L) ≠ 0) (x : V L) (μ : Fin 4) :
    Function.Injective
      (fun p : ({ν : Fin 4 // ν ≠ μ} × Bool) × J => oth x μ p.1.1.1 p.1.2 p.2) := by
  have h10 : (1 : ZMod L) ≠ 0 := by
    intro h; apply hL; rw [← one_add_one_eq_two, h, add_zero]
  rintro ⟨⟨⟨ν, hν⟩, σ⟩, j⟩ ⟨⟨⟨ν', hν'⟩, σ'⟩, j'⟩ h
  simp only at h
  obtain ⟨rfl, rfl⟩ := star_inj hL x μ ν ν' hν hν' σ σ' (oth x μ ν σ j)
    (oth_ne h10 x μ ν hν σ j) (oth_in x μ ν σ j) (h ▸ oth_in x μ ν' σ' j')
  obtain rfl := oth_inj_j h10 x μ ν hν σ j j' h
  rfl

theorem card_J : Fintype.card J = 3 := rfl

/-- star の辺集合はちょうど 18 本（6 枚のプラケット × 3 辺が全部相異なる）。 -/
theorem Es_card [NeZero L] (h2 : 2 ∣ L) (hL : (2 : ZMod L) ≠ 0) (s : Star h2) :
    (Es h2 s).card = 18 := by
  have h10 : (1 : ZMod L) ≠ 0 := by
    intro h; apply hL; rw [← one_add_one_eq_two, h, add_zero]
  obtain ⟨⟨x, μ⟩, hs⟩ := s
  have himg : (Es h2 ⟨(x, μ), hs⟩).image Subtype.val
      = univ.image (fun p : ({ν : Fin 4 // ν ≠ μ} × Bool) × J => oth x μ p.1.1.1 p.1.2 p.2) := by
    ext t
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [mem_Es] at he
      obtain ⟨y, α, β, hαβ, hin_s, hin_e⟩ := he
      obtain ⟨ν, σ, hν, hiff⟩ := InP_cases x μ y α β hαβ hin_s
      have hne : e.1 ≠ (x, μ) := fun h => e.2 (h ▸ hs)
      obtain ⟨j, hj⟩ := oth_surj x μ ν σ e.1 ((hiff _).1 hin_e) hne
      exact ⟨((⟨ν, hν⟩, σ), j), hj⟩
    · rintro ⟨⟨⟨⟨ν, hν⟩, σ⟩, j⟩, rfl⟩
      have hnI : ¬ Istar h2 (oth x μ ν σ j) := fun hI =>
        oth_ne h10 x μ ν hν σ j ((plaq_unique h2 (base x ν σ) μ ν hν.symm).unique
          ⟨oth_in x μ ν σ j, hI⟩ ⟨InP_base x μ ν σ, hs⟩)
      refine ⟨⟨oth x μ ν σ j, hnI⟩, ?_, rfl⟩
      rw [mem_Es]
      exact ⟨base x ν σ, μ, ν, hν.symm, InP_base x μ ν σ, oth_in x μ ν σ j⟩
  rw [← card_image_of_injective _ Subtype.val_injective, himg,
    card_image_of_injective _ (oth_injective hL x μ), card_univ, Fintype.card_prod, card_K, card_J]

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.oth_in
#print axioms CompleteFamilyLattice.oth_ne
#print axioms CompleteFamilyLattice.oth_surj
#print axioms CompleteFamilyLattice.oth_inj_j
#print axioms CompleteFamilyLattice.oth_injective
#print axioms CompleteFamilyLattice.Es_card

end LatticeStarEdges

section LatticeSlots
/-
`hslot` も格子の言葉で。star `s = (x, μ)` の 6 本の staple の 18 個の枠
`slot s i j`（`i : Fin 6`・`j : J`）は相異なる非 `I*` 辺で、全部 `Es s` に入る。
辺の変数 `X : Rest → ℍ` に対して `‖A s i‖ = ‖X (slot s i a)‖`・`‖B s i‖ = ‖X (slot s i b)‖`・
`‖C s i‖ = ‖X (slot s i c)‖`（`Ad` の等長性——ここでは仮定）なら
`Φ''(0) ≥ −27β² Σ_e ‖X e‖²`。
-/

open Finset Quaternion

namespace CompleteFamilyLattice

open OneLinkSeries StapleCurve

variable {L : ℕ}

theorem sum_J {M : Type*} [AddCommMonoid M] (f : J → M) : ∑ j, f j = f J.a + f J.b + f J.c := by
  show Finset.sum {J.a, J.b, J.c} f = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem oth_not_Istar (h2 : 2 ∣ L) (hL : (2 : ZMod L) ≠ 0) (x : V L) (μ ν : Fin 4) (hν : ν ≠ μ)
    (σ : Bool) (j : J) (hs : Istar h2 (x, μ)) : ¬ Istar h2 (oth x μ ν σ j) := by
  have h10 : (1 : ZMod L) ≠ 0 := by
    intro h; apply hL; rw [← one_add_one_eq_two, h, add_zero]
  exact fun hI => oth_ne h10 x μ ν hν σ j ((plaq_unique h2 (base x ν σ) μ ν hν.symm).unique
    ⟨oth_in x μ ν σ j, hI⟩ ⟨InP_base x μ ν σ, hs⟩)

/-- 6 本の staple の番号づけ。 -/
noncomputable def kap (μ : Fin 4) : Fin 6 ≃ ({ν : Fin 4 // ν ≠ μ} × Bool) :=
  (Fintype.equivFinOfCardEq (card_K μ)).symm

/-- star `s` の第 `i` staple の第 `j` 辺。 -/
noncomputable def slot (h2 : 2 ∣ L) (hL : (2 : ZMod L) ≠ 0) (s : Star h2) (i : Fin 6) (j : J) :
    Rest h2 :=
  ⟨oth s.1.1 s.1.2 (kap s.1.2 i).1.1 (kap s.1.2 i).2 j,
    oth_not_Istar h2 hL s.1.1 s.1.2 _ (kap s.1.2 i).1.2 _ j s.2⟩

theorem slot_mem [NeZero L] (h2 : 2 ∣ L) (hL : (2 : ZMod L) ≠ 0) (s : Star h2) (i : Fin 6)
    (j : J) : slot h2 hL s i j ∈ Es h2 s := by
  rw [mem_Es]
  exact ⟨base s.1.1 (kap s.1.2 i).1.1 (kap s.1.2 i).2, s.1.2, (kap s.1.2 i).1.1,
    (kap s.1.2 i).1.2.symm, InP_base _ _ _ _, oth_in _ _ _ _ _⟩

theorem slot_injective (h2 : 2 ∣ L) (hL : (2 : ZMod L) ≠ 0) (s : Star h2) :
    Function.Injective (fun p : Fin 6 × J => slot h2 hL s p.1 p.2) := by
  intro p p' h
  have h' := congrArg Subtype.val h
  have := oth_injective hL s.1.1 s.1.2 (a₁ := (kap s.1.2 p.1, p.2)) (a₂ := (kap s.1.2 p'.1, p'.2)) h'
  obtain ⟨h1, h2'⟩ := Prod.mk.inj this
  exact Prod.ext ((kap s.1.2).injective h1) h2'

/-- 格子版の系（`h6`・`hslot` とも格子の組合せから。`Ad` の等長性は仮定 `nA`・`nB`・`nC`）。 -/
theorem hess_lattice_slots [NeZero L] (h2 : 2 ∣ L) (hL : 3 ≤ L)
    (X : Rest h2 → ℍ[ℝ]) (β : ℝ)
    (q A B C : Star h2 → Fin 6 → ℍ[ℝ]) (hq : ∀ s i, ‖q s i‖ = 1)
    (hA : ∀ s i, (A s i).re = 0) (hB : ∀ s i, (B s i).re = 0) (hC : ∀ s i, (C s i).re = 0)
    (nA : ∀ s i, ‖A s i‖ = ‖X (slot h2 (two_ne_zero_of_le hL) s i J.a)‖)
    (nB : ∀ s i, ‖B s i‖ = ‖X (slot h2 (two_ne_zero_of_le hL) s i J.b)‖)
    (nC : ∀ s i, ‖C s i‖ = ‖X (slot h2 (two_ne_zero_of_le hL) s i J.c)‖) :
    -(27 * β ^ 2) * ∑ e, ‖X e‖ ^ 2 ≤
      deriv (deriv (fun τ => ∑ s, -G β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2))) 0 := by
  refine hess_lattice h2 hL (fun e => ‖X e‖ ^ 2) (fun e => sq_nonneg _) β q A B C hq hA hB hC
    fun s => ?_
  have hL2 := two_ne_zero_of_le hL
  have e1 : ∑ i, (‖A s i‖ ^ 2 + ‖B s i‖ ^ 2 + ‖C s i‖ ^ 2)
      = ∑ p : Fin 6 × J, ‖X (slot h2 hL2 s p.1 p.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_J, nA, nB, nC]
  have e2 : ∑ p : Fin 6 × J, ‖X (slot h2 hL2 s p.1 p.2)‖ ^ 2
      = ∑ e ∈ univ.image (fun p : Fin 6 × J => slot h2 hL2 s p.1 p.2), ‖X e‖ ^ 2 := by
    exact (Finset.sum_image (f := fun e => ‖X e‖ ^ 2)
      (g := fun p : Fin 6 × J => slot h2 hL2 s p.1 p.2)
      ((slot_injective h2 hL2 s).injOn)).symm
  rw [e1, e2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => sq_nonneg _
  intro e he
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
  exact slot_mem h2 hL2 s p.1 p.2

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.slot_mem
#print axioms CompleteFamilyLattice.slot_injective
#print axioms CompleteFamilyLattice.hess_lattice_slots

end LatticeSlots

section LatticeExample
/-
空でないことの確認（`L = 4`）と公理の一覧。
-/

namespace CompleteFamilyLattice

/-- `L = 4` で仮定が満たされること（定理が空でない）。 -/
example (x : V 4) (μ ν : Fin 4) (h : μ ≠ ν) :
    ∃! e : Edge 4, InP e x μ ν ∧ Istar (L := 4) ⟨2, rfl⟩ e :=
  plaq_unique _ x μ ν h

example (e : Rest (L := 4) ⟨2, rfl⟩) :
    (Finset.univ.filter (fun s => e ∈ Es (L := 4) ⟨2, rfl⟩ s)).card = 6 :=
  star_count _ (two_ne_zero_of_le (by norm_num)) e

example (s : Star (L := 4) ⟨2, rfl⟩) : (Es (L := 4) ⟨2, rfl⟩ s).card = 18 :=
  Es_card _ (two_ne_zero_of_le (by norm_num)) s

/-- 原点から方向 3 の辺は `I*`（`x₁ = x₂ = x₄`）：star の族は空でない。 -/
example : Istar (L := 4) ⟨2, rfl⟩ ((0 : V 4), (2 : Fin 4)) := by
  unfold Istar red
  simp only [Pi.zero_apply, map_zero]
  decide

end CompleteFamilyLattice

#print axioms CompleteFamilyLattice.one_mod2
#print axioms CompleteFamilyLattice.plaq_unique
#print axioms CompleteFamilyLattice.plaq_unique_lt
#print axioms CompleteFamilyLattice.InP_cases
#print axioms CompleteFamilyLattice.key
#print axioms CompleteFamilyLattice.star_inj
#print axioms CompleteFamilyLattice.star_count
#print axioms CompleteFamilyLattice.oth_injective
#print axioms CompleteFamilyLattice.Es_card
#print axioms CompleteFamilyLattice.hess_lattice
#print axioms CompleteFamilyLattice.slot_mem
#print axioms CompleteFamilyLattice.slot_injective
#print axioms CompleteFamilyLattice.hess_lattice_slots

end LatticeExample

end LatticePart

-- ===== staple の摂動（代数の部分） =====
section PerturbationAlgebra
/-
staple の摂動の形（四元数 `ℍ[ℝ]` の上の等式・格子は出てこない）。
  辺の変数を右から `U ↦ U e^{τX}` と動かすと、
    前向き staple `U_a U_b⁻¹ U_c⁻¹`・後ろ向き staple `U_b⁻¹ U_a⁻¹ U_c`
  はどちらも `StapleCurve.curve q A B C τ = q e^{τA} e^{τB} e^{τC}` の形になる。
    前向き：`q = U_a U_b⁻¹ U_c⁻¹`・`w = U_b⁻¹ U_c⁻¹`・
            `A = w⁻¹ X_a w`・`B = −w⁻¹ X_b w`・`C = −U_c X_c U_c⁻¹`
    後ろ向き：`q = U_b⁻¹ U_a⁻¹ U_c`・`v = U_a⁻¹ U_c`・
            `A = −v⁻¹ (U_b X_b U_b⁻¹) v`・`B = −v⁻¹ X_a v`・`C = X_c`
  `‖q‖ = 1`・`A, B, C` は虚・`‖A‖²+‖B‖²+‖C‖² = ‖X_a‖²+‖X_b‖²+‖X_c‖²`。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

open Quaternion NormedSpace

namespace StaplePerturbation

open StapleCurve

/-! ### S1：共役と指数 -/

theorem re_mul_comm' (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [re_mul]
  ring

theorem re_conj (w X : ℍ[ℝ]) (hw : w ≠ 0) (hX : X.re = 0) : (w⁻¹ * X * w).re = 0 := by
  rw [re_mul_comm', ← mul_assoc, mul_inv_cancel₀ hw, one_mul, hX]

theorem re_conj' (w X : ℍ[ℝ]) (hw : w ≠ 0) (hX : X.re = 0) : (w * X * w⁻¹).re = 0 := by
  have := re_conj w⁻¹ X (inv_ne_zero hw) hX
  rwa [inv_inv] at this

theorem norm_conj (w X : ℍ[ℝ]) (hw : w ≠ 0) : ‖w⁻¹ * X * w‖ = ‖X‖ := by
  rw [norm_mul, norm_mul, norm_inv, mul_right_comm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw),
    one_mul]

theorem norm_conj' (w X : ℍ[ℝ]) (hw : w ≠ 0) : ‖w * X * w⁻¹‖ = ‖X‖ := by
  have := norm_conj w⁻¹ X (inv_ne_zero hw)
  rwa [inv_inv] at this

/-- 単位四元数の逆は共役。 -/
theorem inv_eq_star_of_norm_one (u : ℍ[ℝ]) (hu : ‖u‖ = 1) : u⁻¹ = star u := by
  have h0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  have h1 : star u * u = 1 := by
    rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hu]
    simp
  exact inv_eq_of_mul_eq_one_left h1

theorem exp_conj_H (w Y : ℍ[ℝ]) (hw : w ≠ 0) : exp (w⁻¹ * Y * w) = w⁻¹ * exp Y * w := by
  let _ : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  exact exp_conj' w Y hw

theorem exp_neg_H (Y : ℍ[ℝ]) : exp (-Y) = (exp Y)⁻¹ := by
  let _ : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  exact exp_neg Y

/-- 指数を右へ運ぶ：`e^{τY} w = w e^{τ w⁻¹Yw}`。 -/
theorem mv (w Y : ℍ[ℝ]) (hw : w ≠ 0) (τ : ℝ) :
    exp (τ • Y) * w = w * exp (τ • (w⁻¹ * Y * w)) := by
  have e : τ • (w⁻¹ * Y * w) = w⁻¹ * (τ • Y) * w := by
    rw [mul_smul_comm, smul_mul_assoc]
  rw [e, exp_conj_H w (τ • Y) hw, mul_assoc, mul_inv_cancel_left₀ hw]

theorem mvneg (w X : ℍ[ℝ]) (hw : w ≠ 0) (τ : ℝ) :
    exp (τ • -X) * w = w * exp (τ • -(w⁻¹ * X * w)) := by
  rw [mv w (-X) hw τ, mul_neg, neg_mul]

theorem mvinv (U X : ℍ[ℝ]) (hU : U ≠ 0) (τ : ℝ) :
    exp (τ • -X) * U⁻¹ = U⁻¹ * exp (τ • -(U * X * U⁻¹)) := by
  have := mvneg U⁻¹ X (inv_ne_zero hU) τ
  rwa [inv_inv] at this

/-- `(U e^{τX})⁻¹ = e^{−τX} U⁻¹`。 -/
theorem pert_inv (U X : ℍ[ℝ]) (τ : ℝ) : (U * exp (τ • X))⁻¹ = exp (τ • -X) * U⁻¹ := by
  rw [mul_inv_rev, smul_neg, exp_neg_H]

/-! ### S2：staple の摂動 -/

theorem fwd_alg (Ua Ubi Uci EA EB EC EA' EB' EC' : ℍ[ℝ])
    (h1 : EA * (Ubi * Uci) = (Ubi * Uci) * EA') (h2 : EB * (Ubi * Uci) = (Ubi * Uci) * EB')
    (h3 : EC * Uci = Uci * EC') :
    Ua * EA * (EB * Ubi) * (EC * Uci) = Ua * Ubi * Uci * EA' * EB' * EC' := by
  calc Ua * EA * (EB * Ubi) * (EC * Uci)
      = Ua * EA * (EB * Ubi) * (Uci * EC') := by rw [h3]
    _ = Ua * EA * (EB * (Ubi * Uci)) * EC' := by simp only [mul_assoc]
    _ = Ua * EA * ((Ubi * Uci) * EB') * EC' := by rw [h2]
    _ = Ua * (EA * (Ubi * Uci)) * EB' * EC' := by simp only [mul_assoc]
    _ = Ua * ((Ubi * Uci) * EA') * EB' * EC' := by rw [h1]
    _ = Ua * Ubi * Uci * EA' * EB' * EC' := by simp only [mul_assoc]

theorem bwd_alg (Ubi Uai Uc EB0 EA0 EC EY EA' EB' : ℍ[ℝ])
    (g1 : EB0 * Ubi = Ubi * EY) (g2 : EY * (Uai * Uc) = (Uai * Uc) * EA')
    (g3 : EA0 * (Uai * Uc) = (Uai * Uc) * EB') :
    (EB0 * Ubi) * (EA0 * Uai) * (Uc * EC) = Ubi * Uai * Uc * EA' * EB' * EC := by
  calc (EB0 * Ubi) * (EA0 * Uai) * (Uc * EC)
      = (Ubi * EY) * (EA0 * Uai) * (Uc * EC) := by rw [g1]
    _ = Ubi * EY * (EA0 * (Uai * Uc)) * EC := by simp only [mul_assoc]
    _ = Ubi * EY * ((Uai * Uc) * EB') * EC := by rw [g3]
    _ = Ubi * (EY * (Uai * Uc)) * EB' * EC := by simp only [mul_assoc]
    _ = Ubi * ((Uai * Uc) * EA') * EB' * EC := by rw [g2]
    _ = Ubi * Uai * Uc * EA' * EB' * EC := by simp only [mul_assoc]

/-- 前向き staple `U_a U_b⁻¹ U_c⁻¹` の摂動。 -/
theorem staple_fwd (Ua Ub Uc Xa Xb Xc : ℍ[ℝ]) (hb : Ub ≠ 0) (hc : Uc ≠ 0) (τ : ℝ) :
    (Ua * exp (τ • Xa)) * (Ub * exp (τ • Xb))⁻¹ * (Uc * exp (τ • Xc))⁻¹
      = curve (Ua * Ub⁻¹ * Uc⁻¹) ((Ub⁻¹ * Uc⁻¹)⁻¹ * Xa * (Ub⁻¹ * Uc⁻¹))
          (-((Ub⁻¹ * Uc⁻¹)⁻¹ * Xb * (Ub⁻¹ * Uc⁻¹))) (-(Uc * Xc * Uc⁻¹)) τ := by
  have hw : Ub⁻¹ * Uc⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hc)
  rw [pert_inv, pert_inv, curve]
  exact fwd_alg _ _ _ _ _ _ _ _ _ (mv _ Xa hw τ) (mvneg _ Xb hw τ) (mvinv Uc Xc hc τ)

/-- 後ろ向き staple `U_b⁻¹ U_a⁻¹ U_c` の摂動。指数の順は `b, a, c`。 -/
theorem staple_bwd (Ua Ub Uc Xa Xb Xc : ℍ[ℝ]) (ha : Ua ≠ 0) (hb : Ub ≠ 0) (hc : Uc ≠ 0)
    (τ : ℝ) :
    (Ub * exp (τ • Xb))⁻¹ * (Ua * exp (τ • Xa))⁻¹ * (Uc * exp (τ • Xc))
      = curve (Ub⁻¹ * Ua⁻¹ * Uc) (-((Ua⁻¹ * Uc)⁻¹ * (Ub * Xb * Ub⁻¹) * (Ua⁻¹ * Uc)))
          (-((Ua⁻¹ * Uc)⁻¹ * Xa * (Ua⁻¹ * Uc))) Xc τ := by
  have hv : Ua⁻¹ * Uc ≠ 0 := mul_ne_zero (inv_ne_zero ha) hc
  rw [pert_inv, pert_inv, curve]
  exact bwd_alg _ _ _ _ _ _ _ _ _ (mvinv Ub Xb hb τ) (mvneg _ (Ub * Xb * Ub⁻¹) hv τ)
    (mvneg _ Xa hv τ)

/-! ### S3 の四元数の部分：向き `σ` つきの staple と `q, A, B, C` -/

/-- 向きつきの staple。`σ = true`：`U_a U_b⁻¹ U_c⁻¹`・`σ = false`：`U_b⁻¹ U_a⁻¹ U_c`。 -/
noncomputable def qS (σ : Bool) (Ua Ub Uc : ℍ[ℝ]) : ℍ[ℝ] :=
  match σ with
  | true => Ua * Ub⁻¹ * Uc⁻¹
  | false => Ub⁻¹ * Ua⁻¹ * Uc

noncomputable def AS (σ : Bool) (Ua Ub Uc Xa Xb : ℍ[ℝ]) : ℍ[ℝ] :=
  match σ with
  | true => (Ub⁻¹ * Uc⁻¹)⁻¹ * Xa * (Ub⁻¹ * Uc⁻¹)
  | false => -((Ua⁻¹ * Uc)⁻¹ * (Ub * Xb * Ub⁻¹) * (Ua⁻¹ * Uc))

noncomputable def BS (σ : Bool) (Ua Ub Uc Xa Xb : ℍ[ℝ]) : ℍ[ℝ] :=
  match σ with
  | true => -((Ub⁻¹ * Uc⁻¹)⁻¹ * Xb * (Ub⁻¹ * Uc⁻¹))
  | false => -((Ua⁻¹ * Uc)⁻¹ * Xa * (Ua⁻¹ * Uc))

noncomputable def CS (σ : Bool) (Uc Xc : ℍ[ℝ]) : ℍ[ℝ] :=
  match σ with
  | true => -(Uc * Xc * Uc⁻¹)
  | false => Xc

theorem qS_pert (σ : Bool) (Ua Ub Uc Xa Xb Xc : ℍ[ℝ]) (ha : Ua ≠ 0) (hb : Ub ≠ 0) (hc : Uc ≠ 0)
    (τ : ℝ) :
    qS σ (Ua * exp (τ • Xa)) (Ub * exp (τ • Xb)) (Uc * exp (τ • Xc))
      = curve (qS σ Ua Ub Uc) (AS σ Ua Ub Uc Xa Xb) (BS σ Ua Ub Uc Xa Xb) (CS σ Uc Xc) τ := by
  cases σ
  · exact staple_bwd Ua Ub Uc Xa Xb Xc ha hb hc τ
  · exact staple_fwd Ua Ub Uc Xa Xb Xc hb hc τ

theorem ne_zero_of_norm_one {u : ℍ[ℝ]} (hu : ‖u‖ = 1) : u ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)

theorem norm_qS (σ : Bool) (Ua Ub Uc : ℍ[ℝ]) (ha : ‖Ua‖ = 1) (hb : ‖Ub‖ = 1) (hc : ‖Uc‖ = 1) :
    ‖qS σ Ua Ub Uc‖ = 1 := by
  cases σ <;> simp [qS, norm_mul, norm_inv, ha, hb, hc]

theorem AS_re (σ : Bool) (Ua Ub Uc Xa Xb : ℍ[ℝ]) (ha : Ua ≠ 0) (hb : Ub ≠ 0) (hc : Uc ≠ 0)
    (hXa : Xa.re = 0) (hXb : Xb.re = 0) : (AS σ Ua Ub Uc Xa Xb).re = 0 := by
  cases σ
  · show (-((Ua⁻¹ * Uc)⁻¹ * (Ub * Xb * Ub⁻¹) * (Ua⁻¹ * Uc))).re = 0
    rw [re_neg, re_conj _ _ (mul_ne_zero (inv_ne_zero ha) hc) (re_conj' Ub Xb hb hXb), neg_zero]
  · exact re_conj _ _ (mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hc)) hXa

theorem BS_re (σ : Bool) (Ua Ub Uc Xa Xb : ℍ[ℝ]) (ha : Ua ≠ 0) (hb : Ub ≠ 0) (hc : Uc ≠ 0)
    (hXa : Xa.re = 0) (hXb : Xb.re = 0) : (BS σ Ua Ub Uc Xa Xb).re = 0 := by
  cases σ
  · show (-((Ua⁻¹ * Uc)⁻¹ * Xa * (Ua⁻¹ * Uc))).re = 0
    rw [re_neg, re_conj _ _ (mul_ne_zero (inv_ne_zero ha) hc) hXa, neg_zero]
  · show (-((Ub⁻¹ * Uc⁻¹)⁻¹ * Xb * (Ub⁻¹ * Uc⁻¹))).re = 0
    rw [re_neg, re_conj _ _ (mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hc)) hXb, neg_zero]

theorem CS_re (σ : Bool) (Uc Xc : ℍ[ℝ]) (hc : Uc ≠ 0) (hXc : Xc.re = 0) :
    (CS σ Uc Xc).re = 0 := by
  cases σ
  · exact hXc
  · show (-(Uc * Xc * Uc⁻¹)).re = 0
    rw [re_neg, re_conj' Uc Xc hc hXc, neg_zero]

/-- `Ad` の等長性：三つの生成子のノルムの二乗和は辺の変数のノルムの二乗和。 -/
theorem normsq_S (σ : Bool) (Ua Ub Uc Xa Xb Xc : ℍ[ℝ]) (ha : Ua ≠ 0) (hb : Ub ≠ 0)
    (hc : Uc ≠ 0) :
    ‖AS σ Ua Ub Uc Xa Xb‖ ^ 2 + ‖BS σ Ua Ub Uc Xa Xb‖ ^ 2 + ‖CS σ Uc Xc‖ ^ 2
      = ‖Xa‖ ^ 2 + ‖Xb‖ ^ 2 + ‖Xc‖ ^ 2 := by
  cases σ
  · show ‖-((Ua⁻¹ * Uc)⁻¹ * (Ub * Xb * Ub⁻¹) * (Ua⁻¹ * Uc))‖ ^ 2
        + ‖-((Ua⁻¹ * Uc)⁻¹ * Xa * (Ua⁻¹ * Uc))‖ ^ 2 + ‖Xc‖ ^ 2 = _
    rw [norm_neg, norm_neg, norm_conj _ _ (mul_ne_zero (inv_ne_zero ha) hc),
      norm_conj _ _ (mul_ne_zero (inv_ne_zero ha) hc), norm_conj' Ub Xb hb]
    ring
  · show ‖(Ub⁻¹ * Uc⁻¹)⁻¹ * Xa * (Ub⁻¹ * Uc⁻¹)‖ ^ 2
        + ‖-((Ub⁻¹ * Uc⁻¹)⁻¹ * Xb * (Ub⁻¹ * Uc⁻¹))‖ ^ 2 + ‖-(Uc * Xc * Uc⁻¹)‖ ^ 2 = _
    rw [norm_neg, norm_neg, norm_conj _ _ (mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hc)),
      norm_conj _ _ (mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hc)), norm_conj' Uc Xc hc]

end StaplePerturbation

#print axioms StaplePerturbation.re_conj
#print axioms StaplePerturbation.norm_conj
#print axioms StaplePerturbation.inv_eq_star_of_norm_one
#print axioms StaplePerturbation.exp_conj_H
#print axioms StaplePerturbation.exp_neg_H
#print axioms StaplePerturbation.mv
#print axioms StaplePerturbation.pert_inv
#print axioms StaplePerturbation.staple_fwd
#print axioms StaplePerturbation.staple_bwd
#print axioms StaplePerturbation.qS_pert
#print axioms StaplePerturbation.norm_qS
#print axioms StaplePerturbation.AS_re
#print axioms StaplePerturbation.BS_re
#print axioms StaplePerturbation.CS_re
#print axioms StaplePerturbation.normsq_S

end PerturbationAlgebra

-- ===== staple の摂動（格子の上での組み立て） =====
section PerturbationLattice
/-
組み立て。周期格子 `(ZMod L)⁴`（`L` 偶数・`L ≥ 3`）の非 `I*` 辺の上のゲージ場
`U : Rest h2 → ℍ[ℝ]`（`‖U e‖ = 1`）と接ベクトル `X : Rest h2 → ℍ[ℝ]`（`re = 0`）に対し、
  `pert U X τ e = U e * exp (τ • X e)`・
  `staple V s i`＝star `s` の第 `i` staple（向き `σ = (kap s.1.2 i).2`。
     `σ = true`：`V a * (V b)⁻¹ * (V c)⁻¹`・`σ = false`：`(V b)⁻¹ * (V a)⁻¹ * V c`。
     `a, b, c = slot s i J.a/J.b/J.c`——`CompleteFamilyLattice.oth` の並び）・
  `Phi β V = Σ_s −G β ‖Σ_i staple V s i‖²`（一リンク積分後の有効作用 `S'` の形——
     `S'` がこの形になること自体は紙）
について `deriv (deriv (fun τ => Phi β (pert U X τ))) 0 ≥ −27β² Σ_e ‖X e‖²`。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

open Finset Quaternion NormedSpace

namespace StaplePerturbation

open OneLinkSeries StapleCurve CompleteFamilyLattice

variable {L : ℕ}

/-- `hess_lattice_slots` の、枠の並びに依らない形（`A, B, C` と `a, b, c` の対応は置換つきでよい）。 -/
theorem hess_lattice_slots_sum [NeZero L] (h2 : 2 ∣ L) (hL : 3 ≤ L)
    (X : Rest h2 → ℍ[ℝ]) (β : ℝ)
    (q A B C : Star h2 → Fin 6 → ℍ[ℝ]) (hq : ∀ s i, ‖q s i‖ = 1)
    (hA : ∀ s i, (A s i).re = 0) (hB : ∀ s i, (B s i).re = 0) (hC : ∀ s i, (C s i).re = 0)
    (hn : ∀ s i, ‖A s i‖ ^ 2 + ‖B s i‖ ^ 2 + ‖C s i‖ ^ 2
      = ∑ j, ‖X (slot h2 (two_ne_zero_of_le hL) s i j)‖ ^ 2) :
    -(27 * β ^ 2) * ∑ e, ‖X e‖ ^ 2 ≤
      deriv (deriv (fun τ => ∑ s, -G β (‖∑ i, curve (q s i) (A s i) (B s i) (C s i) τ‖ ^ 2))) 0 := by
  refine hess_lattice h2 hL (fun e => ‖X e‖ ^ 2) (fun e => sq_nonneg _) β q A B C hq hA hB hC
    fun s => ?_
  have hL2 := two_ne_zero_of_le hL
  have e1 : ∑ i, (‖A s i‖ ^ 2 + ‖B s i‖ ^ 2 + ‖C s i‖ ^ 2)
      = ∑ p : Fin 6 × J, ‖X (slot h2 hL2 s p.1 p.2)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hn s i
  have e2 : ∑ p : Fin 6 × J, ‖X (slot h2 hL2 s p.1 p.2)‖ ^ 2
      = ∑ e ∈ univ.image (fun p : Fin 6 × J => slot h2 hL2 s p.1 p.2), ‖X e‖ ^ 2 := by
    exact (Finset.sum_image (f := fun e => ‖X e‖ ^ 2)
      (g := fun p : Fin 6 × J => slot h2 hL2 s p.1 p.2)
      ((slot_injective h2 hL2 s).injOn)).symm
  rw [e1, e2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => sq_nonneg _
  intro e he
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 he
  exact slot_mem h2 hL2 s p.1 p.2

/-- 辺の摂動 `U_e ↦ U_e e^{τX_e}`。 -/
noncomputable def pert (h2 : 2 ∣ L) (U X : Rest h2 → ℍ[ℝ]) (τ : ℝ) (e : Rest h2) : ℍ[ℝ] :=
  U e * exp (τ • X e)

/-- star `s` の第 `i` staple（star の辺そのものは含まない 3 辺の積）。 -/
noncomputable def staple (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (V : Rest h2 → ℍ[ℝ])
    (s : Star h2) (i : Fin 6) : ℍ[ℝ] :=
  qS (kap s.1.2 i).2 (V (slot h2 hL2 s i J.a)) (V (slot h2 hL2 s i J.b)) (V (slot h2 hL2 s i J.c))

/-- 有効作用の形：`Σ_s −G β ‖M_s‖²`・`M_s = Σ_i staple`。 -/
noncomputable def Phi [NeZero L] (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (β : ℝ)
    (V : Rest h2 → ℍ[ℝ]) : ℝ :=
  ∑ s, -G β (‖∑ i, staple h2 hL2 V s i‖ ^ 2)

/-- staple の向きの確認：前向きは `V a * (V b)⁻¹ * (V c)⁻¹`。 -/
theorem staple_true (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (V : Rest h2 → ℍ[ℝ])
    (s : Star h2) (i : Fin 6) (hσ : (kap s.1.2 i).2 = true) :
    staple h2 hL2 V s i
      = V (slot h2 hL2 s i J.a) * (V (slot h2 hL2 s i J.b))⁻¹ * (V (slot h2 hL2 s i J.c))⁻¹ := by
  rw [staple, hσ]; rfl

/-- 後ろ向きは `(V b)⁻¹ * (V a)⁻¹ * V c`。 -/
theorem staple_false (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (V : Rest h2 → ℍ[ℝ])
    (s : Star h2) (i : Fin 6) (hσ : (kap s.1.2 i).2 = false) :
    staple h2 hL2 V s i
      = (V (slot h2 hL2 s i J.b))⁻¹ * (V (slot h2 hL2 s i J.a))⁻¹ * V (slot h2 hL2 s i J.c) := by
  rw [staple, hσ]; rfl

/-- 摂動した staple は `curve` の形。 -/
theorem staple_pert (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (U X : Rest h2 → ℍ[ℝ])
    (hU : ∀ e, ‖U e‖ = 1) (s : Star h2) (i : Fin 6) (τ : ℝ) :
    staple h2 hL2 (pert h2 U X τ) s i
      = curve (staple h2 hL2 U s i)
          (AS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.a)) (U (slot h2 hL2 s i J.b))
            (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.a)) (X (slot h2 hL2 s i J.b)))
          (BS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.a)) (U (slot h2 hL2 s i J.b))
            (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.a)) (X (slot h2 hL2 s i J.b)))
          (CS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.c))) τ :=
  qS_pert _ _ _ _ _ _ _ (ne_zero_of_norm_one (hU _)) (ne_zero_of_norm_one (hU _))
    (ne_zero_of_norm_one (hU _)) τ

/-- **有効作用の Hesse 形式の下界（格子のゲージ場の言葉）。** -/
theorem hess_gauge [NeZero L] (h2 : 2 ∣ L) (hL : 3 ≤ L) (U X : Rest h2 → ℍ[ℝ])
    (hU : ∀ e, ‖U e‖ = 1) (hX : ∀ e, (X e).re = 0) (β : ℝ) :
    -(27 * β ^ 2) * ∑ e, ‖X e‖ ^ 2 ≤
      deriv (deriv (fun τ => Phi h2 (two_ne_zero_of_le hL) β (pert h2 U X τ))) 0 := by
  have hL2 := two_ne_zero_of_le hL
  have hfun : (fun τ => Phi h2 hL2 β (pert h2 U X τ))
      = fun τ => ∑ s, -G β (‖∑ i, curve (staple h2 hL2 U s i)
          (AS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.a)) (U (slot h2 hL2 s i J.b))
            (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.a)) (X (slot h2 hL2 s i J.b)))
          (BS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.a)) (U (slot h2 hL2 s i J.b))
            (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.a)) (X (slot h2 hL2 s i J.b)))
          (CS (kap s.1.2 i).2 (U (slot h2 hL2 s i J.c)) (X (slot h2 hL2 s i J.c))) τ‖ ^ 2) := by
    funext τ
    simp only [Phi, staple_pert h2 hL2 U X hU]
  rw [hfun]
  refine hess_lattice_slots_sum h2 hL X β _ _ _ _ (fun s i => ?_) (fun s i => ?_) (fun s i => ?_)
    (fun s i => ?_) (fun s i => ?_)
  · exact norm_qS _ _ _ _ (hU _) (hU _) (hU _)
  · exact AS_re _ _ _ _ _ _ (ne_zero_of_norm_one (hU _)) (ne_zero_of_norm_one (hU _))
      (ne_zero_of_norm_one (hU _)) (hX _) (hX _)
  · exact BS_re _ _ _ _ _ _ (ne_zero_of_norm_one (hU _)) (ne_zero_of_norm_one (hU _))
      (ne_zero_of_norm_one (hU _)) (hX _) (hX _)
  · exact CS_re _ _ _ (ne_zero_of_norm_one (hU _)) (hX _)
  · rw [sum_J]
    exact normsq_S _ _ _ _ _ _ _ (ne_zero_of_norm_one (hU _)) (ne_zero_of_norm_one (hU _))
      (ne_zero_of_norm_one (hU _))

/-- 摂動した場も単位四元数の場（`S³` の上に留まる）。 -/
theorem norm_pert (h2 : 2 ∣ L) (U X : Rest h2 → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1)
    (hX : ∀ e, (X e).re = 0) (τ : ℝ) (e : Rest h2) : ‖pert h2 U X τ e‖ = 1 := by
  rw [pert, norm_mul, hU, one_mul, Quaternion.norm_exp, re_smul, hX, smul_zero, exp_zero,
    norm_one]

/-- `τ = 0` では元の場。 -/
theorem pert_zero (h2 : 2 ∣ L) (U X : Rest h2 → ℍ[ℝ]) : pert h2 U X 0 = U := by
  funext e
  simp [pert]

end StaplePerturbation

#print axioms StaplePerturbation.hess_lattice_slots_sum
#print axioms StaplePerturbation.staple_true
#print axioms StaplePerturbation.staple_false
#print axioms StaplePerturbation.staple_pert
#print axioms StaplePerturbation.hess_gauge
#print axioms StaplePerturbation.norm_pert
#print axioms StaplePerturbation.pert_zero

end PerturbationLattice

-- ===== 規約の確認 =====
section PerturbationConventions
/-
規約の確認。`slot` の中身は `CompleteFamilyLattice.oth` で、
  前向き（`σ = true`）の staple `V a * (V b)⁻¹ * (V c)⁻¹` は
    `a = (x+e_μ, ν)`・`b = (x+e_ν, μ)`・`c = (x, ν)`——道 `x+e_μ → x+e_μ+e_ν → x+e_ν → x`、
  後ろ向き（`σ = false`）の staple `(V b)⁻¹ * (V a)⁻¹ * V c` は
    `b = (x−e_ν+e_μ, ν)`・`a = (x−e_ν, μ)`・`c = (x−e_ν, ν)`——道 `x+e_μ → x+e_μ−e_ν → x−e_ν → x`。
  どちらも star の辺 `(x, μ)`（`x → x+e_μ`）と合わせてプラケットを一周する。
-/

namespace StaplePerturbation

open CompleteFamilyLattice

variable {L : ℕ}

theorem slot_val (h2 : 2 ∣ L) (hL2 : (2 : ZMod L) ≠ 0) (s : Star h2) (i : Fin 6) (j : J) :
    (slot h2 hL2 s i j).1 = oth s.1.1 s.1.2 (kap s.1.2 i).1.1 (kap s.1.2 i).2 j := rfl

theorem oth_true (x : V L) (μ ν : Fin 4) :
    oth x μ ν true J.a = (x + ev μ, ν) ∧ oth x μ ν true J.b = (x + ev ν, μ)
      ∧ oth x μ ν true J.c = (x, ν) := ⟨rfl, rfl, rfl⟩

theorem oth_false (x : V L) (μ ν : Fin 4) :
    oth x μ ν false J.a = (x - ev ν, μ) ∧ oth x μ ν false J.b = (x - ev ν + ev μ, ν)
      ∧ oth x μ ν false J.c = (x - ev ν, ν) := ⟨rfl, rfl, rfl⟩

/-- `L = 4` で仮定が満たされる：`hess_gauge` は空な言明ではない。 -/
example (U X : Rest (show 2 ∣ 4 by norm_num) → Quaternion ℝ) (hU : ∀ e, ‖U e‖ = 1)
    (hX : ∀ e, (X e).re = 0) (β : ℝ) :
    -(27 * β ^ 2) * ∑ e, ‖X e‖ ^ 2 ≤
      deriv (deriv (fun τ => Phi (show 2 ∣ 4 by norm_num) (two_ne_zero_of_le (by norm_num)) β
        (pert _ U X τ))) 0 :=
  hess_gauge _ (by norm_num) U X hU hX β

end StaplePerturbation

#print axioms StaplePerturbation.slot_val
#print axioms StaplePerturbation.oth_true
#print axioms StaplePerturbation.oth_false

end PerturbationConventions

end PerturbationPart

-- ===== ホロノミーとその実部 =====
section WilsonHolonomy
/-
W1。全辺の場 `U : Edge L → ℍ[ℝ]`・プラケット `(x, μ, ν)` のホロノミー
  `hol U x μ ν = U(x,μ) · U(x+e_μ,ν) · U(x+e_ν,μ)⁻¹ · U(x,ν)⁻¹`
と、その実部が向き（`μ ↔ ν`）・基点（巡回）に依らないこと。star の辺 `(x, μ)` を含む
プラケット `(base x ν σ, μ, ν)` では `re(hol) = re(U(x,μ) · qS σ …)`（`qS` は `StaplePerturbation` の staple）。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

open Finset Quaternion

namespace WilsonOneLink

open StapleCurve CompleteFamilyLattice StaplePerturbation

variable {L : ℕ}

/-- プラケット `(x, μ, ν)` のホロノミー（staple と同じ向きの規約）。 -/
noncomputable def hol (U : Edge L → ℍ[ℝ]) (x : V L) (μ ν : Fin 4) : ℍ[ℝ] :=
  U (x, μ) * U (x + ev μ, ν) * (U (x + ev ν, μ))⁻¹ * (U (x, ν))⁻¹

theorem re_inv_of_norm_one (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : (q⁻¹).re = q.re := by
  rw [inv_eq_star_of_norm_one q hq, re_star]

/-- 巡回：`re(abcd) = re(bcda)`。 -/
theorem re_cyc4 (a b c d : ℍ[ℝ]) : (a * b * c * d).re = (b * c * d * a).re := by
  have e : a * b * c * d = a * (b * c * d) := by simp only [mul_assoc]
  rw [e, re_mul_comm']

/-- 向きを逆にしたホロノミーは逆元。 -/
theorem hol_swap (U : Edge L → ℍ[ℝ]) (x : V L) (μ ν : Fin 4) :
    hol U x ν μ = (hol U x μ ν)⁻¹ := by
  simp only [hol, mul_inv_rev, inv_inv, mul_assoc]

theorem norm_hol (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1) (x : V L) (μ ν : Fin 4) :
    ‖hol U x μ ν‖ = 1 := by
  simp [hol, norm_mul, norm_inv, hU]

/-- 実部はプラケットの向きに依らない。 -/
theorem re_hol_swap (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1) (x : V L) (μ ν : Fin 4) :
    (hol U x ν μ).re = (hol U x μ ν).re := by
  rw [hol_swap, re_inv_of_norm_one _ (norm_hol U hU x μ ν)]

/-- 実部は基点に依らない（一つ先の角 `x + e_μ` から回っても同じ）。 -/
theorem re_hol_base (U : Edge L → ℍ[ℝ]) (x : V L) (μ ν : Fin 4) :
    (hol U x μ ν).re
      = (U (x + ev μ, ν) * (U (x + ev ν, μ))⁻¹ * (U (x, ν))⁻¹ * U (x, μ)).re :=
  re_cyc4 _ _ _ _

/-- 後ろ向きの枠の代数：`re(A B u⁻¹ C⁻¹) = re(u · B⁻¹ A⁻¹ C)`（単位四元数）。 -/
theorem re_bwd (A B u C : ℍ[ℝ]) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hu : ‖u‖ = 1) (hC : ‖C‖ = 1) :
    (A * B * u⁻¹ * C⁻¹).re = (u * (B⁻¹ * A⁻¹ * C)).re := by
  have e : A * B * u⁻¹ * C⁻¹ = (C * (u * (B⁻¹ * A⁻¹)))⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hn : ‖C * (u * (B⁻¹ * A⁻¹))‖ = 1 := by
    simp [norm_mul, norm_inv, hA, hB, hu, hC]
  rw [e, re_inv_of_norm_one _ hn, re_mul_comm']
  simp only [mul_assoc]

/-- star の辺 `(x, μ)` を含むプラケット `(base x ν σ, μ, ν)`：`re(hol) = re(u · staple)`。
`staple` の中身は `StaplePerturbation.qS σ (U a) (U b) (U c)`・`a, b, c = oth x μ ν σ J.a/b/c`。 -/
theorem re_hol_slot (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1) (x : V L) (μ ν : Fin 4)
    (σ : Bool) :
    (hol U (base x ν σ) μ ν).re
      = (U (x, μ) * qS σ (U (oth x μ ν σ J.a)) (U (oth x μ ν σ J.b)) (U (oth x μ ν σ J.c))).re := by
  cases σ
  · have hb : base x ν false = x - ev ν := by simp [base]
    rw [hb]
    show (U (x - ev ν, μ) * U (x - ev ν + ev μ, ν) * (U (x - ev ν + ev ν, μ))⁻¹
        * (U (x - ev ν, ν))⁻¹).re
      = (U (x, μ) * ((U (x - ev ν + ev μ, ν))⁻¹ * (U (x - ev ν, μ))⁻¹ * U (x - ev ν, ν))).re
    rw [sub_add_cancel]
    exact re_bwd _ _ _ _ (hU _) (hU _) (hU _) (hU _)
  · have hb : base x ν true = x := by simp [base]
    rw [hb]
    show (U (x, μ) * U (x + ev μ, ν) * (U (x + ev ν, μ))⁻¹ * (U (x, ν))⁻¹).re
      = (U (x, μ) * (U (x + ev μ, ν) * (U (x + ev ν, μ))⁻¹ * (U (x, ν))⁻¹)).re
    simp only [mul_assoc]

/-- `re(u · s) = ⟨star u, s⟩`。 -/
theorem re_mul_eq_inner (u s : ℍ[ℝ]) : (u * s).re = inner ℝ (star u) s := by
  rw [← re_star_mul, star_star]

end WilsonOneLink

#print axioms WilsonOneLink.re_cyc4
#print axioms WilsonOneLink.hol_swap
#print axioms WilsonOneLink.norm_hol
#print axioms WilsonOneLink.re_hol_swap
#print axioms WilsonOneLink.re_hol_base
#print axioms WilsonOneLink.re_bwd
#print axioms WilsonOneLink.re_hol_slot
#print axioms WilsonOneLink.re_mul_eq_inner

end WilsonHolonomy

-- ===== Wilson 作用の star 分解 =====
section WilsonStarSum
/-
W2。Wilson 作用 `SW β U = −β Σ_{(x, μ<ν)} re(hol U x μ ν)` を `plaq_unique` で
star ごとに組み替える：プラケットの全体と `Star × Fin 6` の間の全単射 `T`
（`T (s, i)`＝star の辺 `s = (x, μ)` の第 `i` 枠 `(ν, σ) = kap μ i` のプラケット
 `(base x ν σ, {μ, ν})`）を作り、
  `SW β U = −β Σ_s ⟨star (U s), M_s⟩`・`M_s = Σ_i staple (U|Rest) s i`（`StaplePerturbation.staple` そのまま）。
-/

open Finset Quaternion

namespace WilsonOneLink

open StapleCurve CompleteFamilyLattice StaplePerturbation

variable {L : ℕ}

/-- 向きをつけないプラケット `(x, μ, ν)`・`μ < ν`。 -/
abbrev Plaq (L : ℕ) := {p : V L × Fin 4 × Fin 4 // p.2.1 < p.2.2}

/-- Wilson 作用（`SU(2)`＝単位四元数・`(1/2) tr = re`）。 -/
noncomputable def SW [NeZero L] (β : ℝ) (U : Edge L → ℍ[ℝ]) : ℝ :=
  -β * ∑ p : Plaq L, (hol U p.1.1 p.1.2.1 p.1.2.2).re

/-- 辺 `(x, μ)` の枠 `k = (ν, σ)` のプラケット。 -/
def Tk (x : V L) (μ : Fin 4) (k : {ν : Fin 4 // ν ≠ μ} × Bool) : Plaq L :=
  if h : μ < k.1.1 then ⟨(base x k.1.1 k.2, μ, k.1.1), h⟩
  else ⟨(base x k.1.1 k.2, k.1.1, μ), lt_of_le_of_ne (not_lt.1 h) k.1.2⟩

theorem Tk_InP (x : V L) (μ : Fin 4) (k : {ν : Fin 4 // ν ≠ μ} × Bool) :
    InP (x, μ) (Tk x μ k).1.1 (Tk x μ k).1.2.1 (Tk x μ k).1.2.2 := by
  unfold Tk
  split_ifs
  · exact InP_base x μ k.1.1 k.2
  · exact (InP_symm _ _ _ _).1 (InP_base x μ k.1.1 k.2)

theorem Tk_re (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1) (x : V L) (μ : Fin 4)
    (k : {ν : Fin 4 // ν ≠ μ} × Bool) :
    (hol U (Tk x μ k).1.1 (Tk x μ k).1.2.1 (Tk x μ k).1.2.2).re
      = (hol U (base x k.1.1 k.2) μ k.1.1).re := by
  unfold Tk
  split_ifs
  · rfl
  · exact re_hol_swap U hU _ _ _

theorem base_inj (h10 : (1 : ZMod L) ≠ 0) (x : V L) (ν : Fin 4) (σ σ' : Bool)
    (h : base x ν σ = base x ν σ') : σ = σ' := by
  cases σ <;> cases σ' <;>
    first
    | rfl
    | (exfalso
       have := congrFun h ν
       simp only [base, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply, ev_same] at this
       first
       | exact h10 (by linear_combination this)
       | exact h10 (by linear_combination -this))

theorem Tk_injective (h10 : (1 : ZMod L) ≠ 0) (x : V L) (μ : Fin 4) :
    Function.Injective (Tk x μ) := by
  rintro ⟨⟨ν, hν⟩, σ⟩ ⟨⟨ν', hν'⟩, σ'⟩ h
  unfold Tk at h
  simp only at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨hb, -, rfl⟩ := Prod.mk.inj (Subtype.mk.inj h) |>.imp id Prod.mk.inj
    rw [base_inj h10 x ν σ σ' hb]
  · exact absurd (Prod.mk.inj (Prod.mk.inj (Subtype.mk.inj h)).2).1.symm hν'
  · exact absurd (Prod.mk.inj (Prod.mk.inj (Subtype.mk.inj h)).2).1 hν
  · obtain ⟨hb, rfl, -⟩ := Prod.mk.inj (Subtype.mk.inj h) |>.imp id Prod.mk.inj
    rw [base_inj h10 x ν σ σ' hb]

section family

variable [NeZero L] (h2 : 2 ∣ L)

/-- 全単射の本体：`(s, i) ↦` star `s` の第 `i` 枠のプラケット。 -/
noncomputable def T (p : Star h2 × Fin 6) : Plaq L :=
  Tk p.1.1.1 p.1.1.2 (kap p.1.1.2 p.2)

omit [NeZero L] in
theorem T_injective (h10 : (1 : ZMod L) ≠ 0) : Function.Injective (T h2) := by
  rintro ⟨s, i⟩ ⟨s', i'⟩ h
  have h1 : InP s.1 (T h2 (s, i)).1.1 (T h2 (s, i)).1.2.1 (T h2 (s, i)).1.2.2 :=
    Tk_InP s.1.1 s.1.2 _
  have h1' : InP s'.1 (T h2 (s', i')).1.1 (T h2 (s', i')).1.2.1 (T h2 (s', i')).1.2.2 :=
    Tk_InP s'.1.1 s'.1.2 _
  rw [← h] at h1'
  have hs : s = s' := Subtype.ext
    ((plaq_unique h2 _ _ _ (ne_of_lt (T h2 (s, i)).2)).unique ⟨h1, s.2⟩ ⟨h1', s'.2⟩)
  subst hs
  have := Tk_injective h10 s.1.1 s.1.2 h
  exact congrArg (Prod.mk s) ((kap s.1.2).injective this)

omit [NeZero L] in
theorem T_surjective : Function.Surjective (T h2) := by
  rintro ⟨⟨y, α, β⟩, hlt⟩
  have hlt' : α < β := hlt
  have hne : α ≠ β := ne_of_lt hlt'
  obtain ⟨e, ⟨hin, hI⟩, -⟩ := plaq_unique h2 y α β hne
  rcases hin with rfl | rfl | rfl | rfl
  · refine ⟨(⟨(y, α), hI⟩, (kap α).symm (⟨β, hne.symm⟩, true)), ?_⟩
    apply Subtype.ext
    simp [T, Tk, base, hlt']
  · refine ⟨(⟨(y + ev α, β), hI⟩, (kap β).symm (⟨α, hne⟩, false)), ?_⟩
    apply Subtype.ext
    simp [T, Tk, base, not_lt_of_gt hlt']
  · refine ⟨(⟨(y + ev β, α), hI⟩, (kap α).symm (⟨β, hne.symm⟩, false)), ?_⟩
    apply Subtype.ext
    simp [T, Tk, base, hlt']
  · refine ⟨(⟨(y, β), hI⟩, (kap β).symm (⟨α, hne⟩, true)), ?_⟩
    apply Subtype.ext
    simp [T, Tk, base, not_lt_of_gt hlt']

omit [NeZero L] in
theorem T_bijective (h10 : (1 : ZMod L) ≠ 0) : Function.Bijective (T h2) :=
  ⟨T_injective h2 h10, T_surjective h2⟩

/-- 全辺の場の、非 `I*` 辺への制限。 -/
def restr (U : Edge L → ℍ[ℝ]) : Rest h2 → ℍ[ℝ] := fun e => U e.1

/-- star `s` の staple の和 `M_s`（`StaplePerturbation.staple` の和）。 -/
noncomputable def Mst (hL2 : (2 : ZMod L) ≠ 0) (W : Rest h2 → ℍ[ℝ]) (s : Star h2) : ℍ[ℝ] :=
  ∑ i, staple h2 hL2 W s i

omit [NeZero L] in
/-- 枠ごと：`re(hol (T (s, i))) = ⟨star (U s), staple (U|Rest) s i⟩`。 -/
theorem re_hol_T (hL2 : (2 : ZMod L) ≠ 0) (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1)
    (s : Star h2) (i : Fin 6) :
    (hol U (T h2 (s, i)).1.1 (T h2 (s, i)).1.2.1 (T h2 (s, i)).1.2.2).re
      = inner ℝ (star (U s.1)) (staple h2 hL2 (restr h2 U) s i) := by
  rw [← re_mul_eq_inner]
  exact (Tk_re U hU s.1.1 s.1.2 _).trans (re_hol_slot U hU s.1.1 s.1.2 _ _)

/-- **W2：Wilson 作用は star ごとに `−β ⟨star u_s, M_s⟩` の和。** -/
theorem SW_eq (hL2 : (2 : ZMod L) ≠ 0) (β : ℝ) (U : Edge L → ℍ[ℝ]) (hU : ∀ e, ‖U e‖ = 1) :
    SW β U = -β * ∑ s : Star h2, inner ℝ (star (U s.1)) (Mst h2 hL2 (restr h2 U) s) := by
  have h10 : (1 : ZMod L) ≠ 0 := by
    intro h; apply hL2; rw [← one_add_one_eq_two, h, add_zero]
  unfold SW Mst
  congr 1
  rw [← Fintype.sum_bijective (T h2) (T_bijective h2 h10)
    (fun p => inner ℝ (star (U p.1.1)) (staple h2 hL2 (restr h2 U) p.1 p.2))
    (fun p => (hol U p.1.1 p.1.2.1 p.1.2.2).re)
    (fun p => (re_hol_T h2 hL2 U hU p.1 p.2).symm), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_sum]

end family

end WilsonOneLink

#print axioms WilsonOneLink.Tk_InP
#print axioms WilsonOneLink.Tk_re
#print axioms WilsonOneLink.Tk_injective
#print axioms WilsonOneLink.T_injective
#print axioms WilsonOneLink.T_surjective
#print axioms WilsonOneLink.T_bijective
#print axioms WilsonOneLink.re_hol_T
#print axioms WilsonOneLink.SW_eq

end WilsonStarSum

-- ===== `S³` の Haar 確率測度 =====
section HaarMeasure
/-
H1。`S³`＝単位四元数の群の上の Haar 確率測度を、`ℍ[ℝ]` の上の測度 `μ` で
  (prob) 確率測度・(unit) `μ`-a.e. に `‖u‖ = 1`・(inv) 単位四元数の左からの積で不変
を満たすものとして扱う（`IsHaarS3 μ`。具体例は `haarS3`）。
  `integral_inner`：`∫ f(⟨u, M⟩) dμ = ∫ f(‖M‖ · re u) dμ`（`f` 連続）——左不変性だけから。
  `mixed`：`(2k+1) ∫ (re u)^{2k} ℓ(u)² dμ = ∫ (re u)^{2k+2} dμ`（`ℓ = imI, imJ, imK`）
    ——`∫ (re u − b ℓ(u))^{2k+2} dμ = (1+b²)^{k+1} ∫ (re u)^{2k+2} dμ` の `b²` の係数。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

open MeasureTheory Quaternion Finset

namespace WilsonOneLink

open StapleCurve

/-- `ℍ[ℝ]` の Borel 構造（Mathlib には未登録）。 -/
noncomputable instance instMeasurableSpaceH : MeasurableSpace ℍ[ℝ] := borel _

instance instBorelSpaceH : BorelSpace ℍ[ℝ] := ⟨rfl⟩

/-- `S³` の Haar 確率測度（`ℍ[ℝ]` の上の測度として）。 -/
structure IsHaarS3 (μ : Measure ℍ[ℝ]) : Prop where
  prob : IsProbabilityMeasure μ
  unit : ∀ᵐ u ∂μ, ‖u‖ = 1
  inv : ∀ q : ℍ[ℝ], ‖q‖ = 1 → μ.map (fun u => q * u) = μ

theorem sq_sum_of_norm_one (u : ℍ[ℝ]) (hu : ‖u‖ = 1) :
    u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
  have := Quaternion.normSq_eq_norm_mul_self u
  rw [hu, Quaternion.normSq_def'] at this
  linarith

theorem abs_re_le (u : ℍ[ℝ]) (hu : ‖u‖ = 1) : |u.re| ≤ 1 := by
  have := sq_sum_of_norm_one u hu
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK])

theorem abs_imI_le (u : ℍ[ℝ]) (hu : ‖u‖ = 1) : |u.imI| ≤ 1 := by
  have := sq_sum_of_norm_one u hu
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg u.re, sq_nonneg u.imJ, sq_nonneg u.imK])

theorem abs_imJ_le (u : ℍ[ℝ]) (hu : ‖u‖ = 1) : |u.imJ| ≤ 1 := by
  have := sq_sum_of_norm_one u hu
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg u.re, sq_nonneg u.imI, sq_nonneg u.imK])

theorem abs_imK_le (u : ℍ[ℝ]) (hu : ‖u‖ = 1) : |u.imK| ≤ 1 := by
  have := sq_sum_of_norm_one u hu
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg u.re, sq_nonneg u.imI, sq_nonneg u.imJ])

variable {μ : Measure ℍ[ℝ]}

/-- 左不変性の積分形。 -/
theorem IsHaarS3.integral_mul_left (h : IsHaarS3 μ) (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (f : ℍ[ℝ] → ℝ)
    (hf : Continuous f) : ∫ u, f (q * u) ∂μ = ∫ u, f u ∂μ := by
  have hm : Measurable (fun u : ℍ[ℝ] => q * u) := (continuous_const.mul continuous_id).measurable
  conv_rhs => rw [← h.inv q hq]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]

theorem inner_unit_mul (M u : ℍ[ℝ]) (hM : M ≠ 0) :
    inner ℝ (((‖M‖⁻¹ : ℝ) • M) * u) M = ‖M‖ * u.re := by
  have hn : ‖M‖ ≠ 0 := norm_ne_zero_iff.2 hM
  have e : star ((‖M‖⁻¹ : ℝ) • M) * M = ((‖M‖ : ℝ) : ℍ[ℝ]) := by
    rw [Quaternion.star_smul, smul_mul_assoc, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self,
      Quaternion.smul_coe]
    congr 1
    field_simp
  rw [real_inner_comm, inner_mul_left_adj, e, ← re_star_mul, Quaternion.star_coe,
    Quaternion.coe_mul_eq_smul, Quaternion.re_smul, smul_eq_mul]

/-- **H1**：`∫ f(⟨u, M⟩) dμ` は `‖M‖` だけで決まる。 -/
theorem IsHaarS3.integral_inner (h : IsHaarS3 μ) (f : ℝ → ℝ) (hf : Continuous f) (M : ℍ[ℝ]) :
    ∫ u, f (inner ℝ u M) ∂μ = ∫ u, f (‖M‖ * u.re) ∂μ := by
  by_cases hM : M = 0
  · subst hM
    simp
  · have hq : ‖((‖M‖⁻¹ : ℝ) • M)‖ = 1 := norm_smul_inv_norm hM
    have hc : Continuous fun u : ℍ[ℝ] => f (inner ℝ u M) :=
      hf.comp (continuous_id.inner continuous_const)
    rw [← h.integral_mul_left _ hq _ hc]
    simp only [inner_unit_mul M _ hM]

end WilsonOneLink

#print axioms WilsonOneLink.IsHaarS3.integral_mul_left
#print axioms WilsonOneLink.IsHaarS3.integral_inner

end HaarMeasure

-- ===== モーメントの漸化式 =====
section HaarMoments
/-
H2（モーメントの形）。`IsHaarS3 μ` の下で `c n := ∫ (re u)^n dμ` は
  `c (2k+1) = 0`・`(2k+4) c (2k+2) = (2k+1) c (2k)`・`c 0 = 1`
を満たし、`OneLinkSeries.mom n = ∫_0^π cos^n θ sin²θ dθ` と `c n = (2/π) mom n` で一致する
（`re u` の分布のモーメントが密度 `(2/π) sin²θ dθ` のモーメントに等しい）。
漸化式は左不変性（`(1, i)`・`(1, j)`・`(1, k)` 平面の回転）と `‖u‖ = 1` だけから出る。
-/

open MeasureTheory Quaternion Finset

namespace WilsonOneLink

open OneLinkSeries

variable {μ : Measure ℍ[ℝ]}

theorem choose_two (k : ℕ) : (((2 * k + 2).choose 2 : ℕ) : ℝ) = ((k : ℝ) + 1) * (2 * k + 1) := by
  have h : (2 * k + 2).choose 2 = (k + 1) * (2 * k + 1) := by
    rw [Nat.choose_two_right]
    have h1 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have h2 : (2 * k + 2) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) := by ring
    rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [h]; push_cast; ring

theorem IsHaarS3.integrable_mono (h : IsHaarS3 μ) (ℓ : ℍ[ℝ] → ℝ) (hℓc : Continuous ℓ)
    (hℓb : ∀ u, ‖u‖ = 1 → |ℓ u| ≤ 1) (i j : ℕ) :
    Integrable (fun u => ℓ u ^ i * u.re ^ j) μ := by
  have := h.prob
  refine Integrable.of_bound ((hℓc.pow i).mul (continuous_re.pow j)).aestronglyMeasurable 1 ?_
  filter_upwards [h.unit] with u hu
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (hℓb u hu)) (by positivity)
    (pow_le_one₀ (abs_nonneg _) (abs_re_le u hu))

/-- 回転：`∫ (re u − b ℓ(u))^{2k+2} dμ = (1+b²)^{k+1} ∫ (re u)^{2k+2} dμ`。 -/
theorem IsHaarS3.rot (h : IsHaarS3 μ) (ℓ : ℍ[ℝ] → ℝ)
    (hq : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ u : ℍ[ℝ], (q * u).re = a * u.re - b * ℓ u)
    (k : ℕ) (b : ℝ) :
    ∫ u, (u.re - b * ℓ u) ^ (2 * k + 2) ∂μ
      = (1 + b ^ 2) ^ (k + 1) * ∫ u, u.re ^ (2 * k + 2) ∂μ := by
  have hpos : 0 < 1 + b ^ 2 := by positivity
  set r := Real.sqrt (1 + b ^ 2) with hr
  have hr2 : r ^ 2 = 1 + b ^ 2 := Real.sq_sqrt hpos.le
  have hr0 : r ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  obtain ⟨q, hq1, hq2⟩ := hq (1 / r) (b / r) (by
    rw [div_pow, div_pow, ← add_div, one_pow, hr2, div_self hpos.ne'])
  have key := h.integral_mul_left q hq1 (fun u => u.re ^ (2 * k + 2)) (continuous_re.pow _)
  simp only [hq2] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : u.re - b * ℓ u = r * (1 / r * u.re - b / r * ℓ u) := by
    field_simp
  have e2 : r ^ (2 * k + 2) = (1 + b ^ 2) ^ (k + 1) := by
    rw [← hr2]; ring
  show (u.re - b * ℓ u) ^ (2 * k + 2) = _
  rw [e, mul_pow, e2]

/-- `b²` の係数の比較：`(2k+1) ∫ (re u)^{2k} ℓ(u)² dμ = ∫ (re u)^{2k+2} dμ`。 -/
theorem IsHaarS3.mixed (h : IsHaarS3 μ) (ℓ : ℍ[ℝ] → ℝ) (hℓc : Continuous ℓ)
    (hℓb : ∀ u, ‖u‖ = 1 → |ℓ u| ≤ 1)
    (hq : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 →
      ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ u : ℍ[ℝ], (q * u).re = a * u.re - b * ℓ u)
    (k : ℕ) :
    (2 * (k : ℝ) + 1) * ∫ u, ℓ u ^ 2 * u.re ^ (2 * k) ∂μ = ∫ u, u.re ^ (2 * k + 2) ∂μ := by
  set n := 2 * k + 2 with hn
  set I : ℕ → ℝ := fun m => ∫ u, ℓ u ^ m * u.re ^ (n - m) ∂μ with hI
  set c : ℝ := ∫ u, u.re ^ n ∂μ with hc
  -- 二項展開
  have hexp : ∀ b : ℝ, ∫ u, (u.re - b * ℓ u) ^ n ∂μ
      = ∑ m ∈ range (n + 1), ((-1) ^ m * (n.choose m : ℝ) * I m) * b ^ m := by
    intro b
    have e1 : ∀ u : ℍ[ℝ], (u.re - b * ℓ u) ^ n
        = ∑ m ∈ range (n + 1), ((-b) ^ m * (n.choose m : ℝ)) * (ℓ u ^ m * u.re ^ (n - m)) := by
      intro u
      have : u.re - b * ℓ u = -b * ℓ u + u.re := by ring
      rw [this, add_pow]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp only [e1]
    rw [integral_finsetSum _ fun m _ => (h.integrable_mono ℓ hℓc hℓb m (n - m)).const_mul _]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, neg_pow]
    ring
  -- 多項式の等式
  have hpoly : (∑ m ∈ range (n + 1),
        Polynomial.C ((-1) ^ m * (n.choose m : ℝ) * I m) * Polynomial.X ^ m : Polynomial ℝ)
      = Polynomial.C c * (Polynomial.X ^ 2 + 1) ^ (k + 1) := by
    refine Polynomial.funext fun b => ?_
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_one]
    rw [← hexp b, h.rot ℓ hq k b]
    ring
  have hcoef := congrArg (fun p : Polynomial ℝ => p.coeff 2) hpoly
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq] at hcoef
  have hex : ((Polynomial.X : Polynomial ℝ) ^ 2 + 1) ^ (k + 1)
      = Polynomial.expand ℝ 2 ((Polynomial.X + 1) ^ (k + 1)) := by
    simp
  have hc2 : (((Polynomial.X : Polynomial ℝ) ^ 2 + 1) ^ (k + 1)).coeff 2 = (k : ℝ) + 1 := by
    rw [hex]
    have := Polynomial.coeff_expand_mul (R := ℝ) (p := 2) (by norm_num)
      ((Polynomial.X + 1) ^ (k + 1)) 1
    rw [one_mul] at this
    rw [this, Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]
    push_cast; ring
  rw [hc2, if_pos (by rw [mem_range, hn]; omega)] at hcoef
  have h2 : n - 2 = 2 * k := by omega
  have hI2 : I 2 = ∫ u, ℓ u ^ 2 * u.re ^ (2 * k) ∂μ := by rw [hI]; simp only [h2]
  rw [hn, choose_two, hI2] at hcoef
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) * ((2 * (k : ℝ) + 1) * ∫ u, ℓ u ^ 2 * u.re ^ (2 * k) ∂μ)
      = ((k : ℝ) + 1) * c := by
    linear_combination hcoef
  exact mul_left_cancel₀ hk this

end WilsonOneLink

#print axioms WilsonOneLink.IsHaarS3.rot
#print axioms WilsonOneLink.IsHaarS3.mixed

end HaarMoments

-- ===== 一リンク積分 =====
section OneLinkIntegral
/-
H2・H3 の一本。`IsHaarS3 μ` の下で
  `cm μ n := ∫ (re u)^n dμ = (2/π) · mom n`（`mom n = ∫_0^π cos^n θ sin²θ dθ`）、
  `∫ e^{κ re u} dμ = Z κ = F0(κ²/4)`、
  **`∫ e^{β⟨u, M⟩} dμ(u) = F0(β²‖M‖²/4)`**（一リンク積分）。
-/

open MeasureTheory Quaternion Finset

namespace WilsonOneLink

open OneLinkSeries

variable {μ : Measure ℍ[ℝ]}

theorem norm_eq_one_of (q : ℍ[ℝ]) (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    ‖q‖ = 1 := by
  have h1 := Quaternion.normSq_eq_norm_mul_self q
  rw [Quaternion.normSq_def'] at h1
  have h2 : (‖q‖ - 1) * (‖q‖ + 1) = 0 := by
    have : ‖q‖ * ‖q‖ = 1 := by rw [← h1]; exact h
    linear_combination this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · linarith [norm_nonneg q]

/-- `a + b i`・`a + b j`・`a + b k`。 -/
def qI (a b : ℝ) : ℍ[ℝ] := ⟨a, b, 0, 0⟩
def qJ (a b : ℝ) : ℍ[ℝ] := ⟨a, 0, b, 0⟩
def qK (a b : ℝ) : ℍ[ℝ] := ⟨a, 0, 0, b⟩

theorem rotI (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ u : ℍ[ℝ], (q * u).re = a * u.re - b * u.imI := by
  refine ⟨qI a b, norm_eq_one_of _ ?_, fun u => ?_⟩
  · show a ^ 2 + b ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
    linarith
  · rw [re_mul]
    show a * u.re - b * u.imI - 0 * u.imJ - 0 * u.imK = _
    ring

theorem rotJ (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ u : ℍ[ℝ], (q * u).re = a * u.re - b * u.imJ := by
  refine ⟨qJ a b, norm_eq_one_of _ ?_, fun u => ?_⟩
  · show a ^ 2 + 0 ^ 2 + b ^ 2 + 0 ^ 2 = 1
    linarith
  · rw [re_mul]
    show a * u.re - 0 * u.imI - b * u.imJ - 0 * u.imK = _
    ring

theorem rotK (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ u : ℍ[ℝ], (q * u).re = a * u.re - b * u.imK := by
  refine ⟨qK a b, norm_eq_one_of _ ?_, fun u => ?_⟩
  · show a ^ 2 + 0 ^ 2 + 0 ^ 2 + b ^ 2 = 1
    linarith
  · rw [re_mul]
    show a * u.re - 0 * u.imI - 0 * u.imJ - b * u.imK = _
    ring

/-- `re u` のモーメント。 -/
noncomputable def cm (μ : Measure ℍ[ℝ]) (n : ℕ) : ℝ := ∫ u, u.re ^ n ∂μ

theorem IsHaarS3.integrable_re_pow (h : IsHaarS3 μ) (j : ℕ) :
    Integrable (fun u : ℍ[ℝ] => u.re ^ j) μ := by
  simpa using h.integrable_mono (fun u => u.imI) continuous_imI abs_imI_le 0 j

theorem IsHaarS3.cm_zero (h : IsHaarS3 μ) : cm μ 0 = 1 := by
  have := h.prob
  simp [cm]

/-- 漸化式 `(2k+4) c_{2k+2} = (2k+1) c_{2k}`。 -/
theorem IsHaarS3.cm_rec (h : IsHaarS3 μ) (k : ℕ) :
    (2 * (k : ℝ) + 4) * cm μ (2 * k + 2) = (2 * (k : ℝ) + 1) * cm μ (2 * k) := by
  have hI := h.mixed (fun u => u.imI) continuous_imI abs_imI_le rotI k
  have hJ := h.mixed (fun u => u.imJ) continuous_imJ abs_imJ_le rotJ k
  have hK := h.mixed (fun u => u.imK) continuous_imK abs_imK_le rotK k
  have iI := h.integrable_mono (fun u => u.imI) continuous_imI abs_imI_le 2 (2 * k)
  have iJ := h.integrable_mono (fun u => u.imJ) continuous_imJ abs_imJ_le 2 (2 * k)
  have iK := h.integrable_mono (fun u => u.imK) continuous_imK abs_imK_le 2 (2 * k)
  have i0 := h.integrable_re_pow (2 * k + 2)
  have e : cm μ (2 * k) = ∫ u, (u.re ^ (2 * k + 2) + (u.imI ^ 2 * u.re ^ (2 * k)
      + (u.imJ ^ 2 * u.re ^ (2 * k) + u.imK ^ 2 * u.re ^ (2 * k)))) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h.unit] with u hu
    have := sq_sum_of_norm_one u hu
    linear_combination (-(u.re ^ (2 * k))) * this
  have iJK : Integrable (fun u : ℍ[ℝ] => u.imJ ^ 2 * u.re ^ (2 * k) + u.imK ^ 2 * u.re ^ (2 * k)) μ :=
    iJ.add iK
  have iIJK : Integrable (fun u : ℍ[ℝ] => u.imI ^ 2 * u.re ^ (2 * k)
      + (u.imJ ^ 2 * u.re ^ (2 * k) + u.imK ^ 2 * u.re ^ (2 * k))) μ := iI.add iJK
  rw [integral_add i0 iIJK, integral_add iI iJK, integral_add iJ iK] at e
  unfold cm at e ⊢
  linear_combination (-(2 * (k : ℝ) + 1)) * e - hI - hJ - hK

theorem IsHaarS3.cm_odd (h : IsHaarS3 μ) (k : ℕ) : cm μ (2 * k + 1) = 0 := by
  have hq : ‖(-1 : ℍ[ℝ])‖ = 1 := by simp
  have key := h.integral_mul_left (-1) hq (fun u => u.re ^ (2 * k + 1)) (continuous_re.pow _)
  have e : ∀ u : ℍ[ℝ], ((-1 : ℍ[ℝ]) * u).re ^ (2 * k + 1) = -(u.re ^ (2 * k + 1)) := by
    intro u
    rw [neg_one_mul, re_neg, Odd.neg_pow ⟨k, rfl⟩]
  simp only [e] at key
  rw [integral_neg] at key
  unfold cm
  linarith

theorem mom_rec (k : ℕ) :
    (2 * (k : ℝ) + 4) * mom (2 * k + 2) = (2 * (k : ℝ) + 1) * mom (2 * k) := by
  rw [mom_eq, mom_eq, Icos_succ_succ]
  push_cast
  have h1 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h2 : (2 * (k : ℝ) + 2 + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem mom_zero : mom 0 = Real.pi / 2 := by
  rw [mom_eq, Icos_zero]
  norm_num

/-- **H2（モーメントの形）**：`re u` の分布のモーメントは密度 `(2/π) sin²θ dθ` のモーメント。 -/
theorem IsHaarS3.cm_eq_mom (h : IsHaarS3 μ) (n : ℕ) : cm μ n = 2 / Real.pi * mom n := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heven : ∀ k : ℕ, cm μ (2 * k) = 2 / Real.pi * mom (2 * k) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.mul_zero, h.cm_zero, mom_zero]
      field_simp
    | succ k ih =>
      have h1 := h.cm_rec k
      have h2 := mom_rec k
      have h3 : (2 * (k : ℝ) + 4) ≠ 0 := by positivity
      have e : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e]
      apply mul_left_cancel₀ h3
      rw [h1, ih]
      linear_combination (-(2 / Real.pi)) * h2
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact heven k
  · rw [h.cm_odd, mom_odd, mul_zero]

/-- `∫ e^{κ re u} dμ = Z κ`。 -/
theorem IsHaarS3.integral_exp_re (h : IsHaarS3 μ) (κ : ℝ) :
    ∫ u, Real.exp (κ * u.re) ∂μ = Z κ := by
  have := h.prob
  have key := hasSum_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) (u : ℍ[ℝ]) => (κ * u.re) ^ n / (n.factorial : ℝ))
    (f := fun u => Real.exp (κ * u.re))
    (fun (n : ℕ) (_ : ℍ[ℝ]) => |κ| ^ n / (n.factorial : ℝ))
    (fun n => (((continuous_const.mul continuous_re).pow n).div_const _).aestronglyMeasurable)
    (fun n => by
      filter_upwards [h.unit] with u hu
      simp only [norm_div, norm_pow, norm_mul, Real.norm_eq_abs, Nat.abs_cast]
      have h1 : (|κ| * |u.re|) ^ n ≤ |κ| ^ n :=
        pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (abs_nonneg κ) (abs_re_le u hu)) n
      exact div_le_div_of_nonneg_right h1 (by positivity))
    (Filter.Eventually.of_forall fun _ => Real.summable_pow_div_factorial |κ|)
    (integrable_const _)
    (Filter.Eventually.of_forall fun u => by
      have h' := NormedSpace.expSeries_div_hasSum_exp (κ * u.re)
      rw [← Real.exp_eq_exp_ℝ] at h'
      exact h')
  have e : (fun n : ℕ => ∫ u, (κ * u.re) ^ n / (n.factorial : ℝ) ∂μ)
      = fun n : ℕ => 2 / Real.pi * (κ ^ n / (n.factorial : ℝ) * mom n) := by
    funext n
    calc ∫ u, (κ * u.re) ^ n / (n.factorial : ℝ) ∂μ
        = ∫ u, κ ^ n / (n.factorial : ℝ) * u.re ^ n ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show (κ * u.re) ^ n / (n.factorial : ℝ) = κ ^ n / (n.factorial : ℝ) * u.re ^ n
          rw [mul_pow]; ring
      _ = κ ^ n / (n.factorial : ℝ) * cm μ n := integral_const_mul _ _
      _ = 2 / Real.pi * (κ ^ n / (n.factorial : ℝ) * mom n) := by
          rw [h.cm_eq_mom]; ring
  rw [e] at key
  have h2 := (hasSum_integral κ).mul_left (2 / Real.pi)
  rw [Z_eq_integral]
  exact key.unique h2

/-- **H3：一リンク積分** `∫ e^{β⟨u, M⟩} dμ(u) = F0(β²‖M‖²/4)`。 -/
theorem IsHaarS3.one_link (h : IsHaarS3 μ) (β : ℝ) (M : ℍ[ℝ]) :
    ∫ u, Real.exp (β * inner ℝ u M) ∂μ = F0 (β ^ 2 * ‖M‖ ^ 2 / 4) := by
  have h1 := h.integral_inner (fun t => Real.exp (β * t)) (by fun_prop) M
  have h2 := h.integral_exp_re (β * ‖M‖)
  simp only [← mul_assoc] at h1
  rw [h1, h2, Z, mul_pow]

end WilsonOneLink

#print axioms WilsonOneLink.IsHaarS3.cm_rec
#print axioms WilsonOneLink.IsHaarS3.cm_odd
#print axioms WilsonOneLink.IsHaarS3.cm_eq_mom
#print axioms WilsonOneLink.IsHaarS3.integral_exp_re
#print axioms WilsonOneLink.IsHaarS3.one_link

end OneLinkIntegral

-- ===== Haar 確率測度の具体例 =====
section HaarExample
/-
`IsHaarS3` を満たす測度の具体例。`ℍ[ℝ] ≅ ℝ⁴` の Lebesgue 測度を単位球に制限し、
`x ↦ x/‖x‖` で押し出して正規化したもの（＝`S³` の一様確率測度・Mathlib の `Measure.toSphere` と
同じ作り方で `ℍ[ℝ]` の上に置いた形）。左不変性は「単位四元数の左からの積は線型等長」から。
-/

open MeasureTheory Quaternion Metric

namespace WilsonOneLink

/-- 正規化 `x ↦ ‖x‖⁻¹ • x`。 -/
noncomputable def nrm (x : ℍ[ℝ]) : ℍ[ℝ] := (‖x‖⁻¹ : ℝ) • x

theorem measurable_nrm : Measurable nrm := (measurable_norm.inv).smul measurable_id

/-- `S³` の一様確率測度（`ℍ[ℝ]` の上の測度として）。 -/
noncomputable def haarS3 : Measure ℍ[ℝ] :=
  (volume (ball (0 : ℍ[ℝ]) 1))⁻¹ • (volume.restrict (ball (0 : ℍ[ℝ]) 1)).map nrm

/-- 零でない四元数の左からの積（線型同型）。 -/
noncomputable def mulLe (q : ℍ[ℝ]) (hq0 : q ≠ 0) : ℍ[ℝ] ≃ₗ[ℝ] ℍ[ℝ] where
  toFun u := q * u
  map_add' := mul_add q
  map_smul' c u := by simp
  invFun u := q⁻¹ * u
  left_inv u := inv_mul_cancel_left₀ hq0 u
  right_inv u := mul_inv_cancel_left₀ hq0 u

/-- 単位四元数の左からの積（線型等長同型）。 -/
noncomputable def mulL (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toLinearEquiv := mulLe q (norm_ne_zero_iff.1 (by rw [hq]; exact one_ne_zero))
  norm_map' x := by
    show ‖q * x‖ = ‖x‖
    rw [norm_mul, hq, one_mul]

theorem mulL_apply (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (u : ℍ[ℝ]) : mulL q hq u = q * u := rfl

theorem map_mulL_volume (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    (volume : Measure ℍ[ℝ]).map (fun u => q * u) = volume :=
  (mulL q hq).measurePreserving.map_eq

theorem isHaarS3_haarS3 : IsHaarS3 haarS3 := by
  have hB0 : volume (ball (0 : ℍ[ℝ]) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  have hBt : volume (ball (0 : ℍ[ℝ]) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [haarS3, Measure.smul_apply, Measure.map_apply measurable_nrm MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel hB0 hBt]
  · rw [haarS3]
    refine Measure.ae_smul_measure ?_ _
    have hm : MeasurableSet {u : ℍ[ℝ] | ‖u‖ = 1} :=
      measurableSet_eq_fun measurable_norm measurable_const
    rw [ae_map_iff measurable_nrm.aemeasurable hm]
    refine ae_restrict_of_ae ?_
    have h0 : ∀ᵐ x : ℍ[ℝ] ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with x hx
    exact norm_smul_inv_norm hx
  · intro q hq
    have hmq : Measurable (fun u : ℍ[ℝ] => q * u) :=
      (continuous_const.mul continuous_id).measurable
    have hcomm : (fun u : ℍ[ℝ] => q * u) ∘ nrm = nrm ∘ (fun u : ℍ[ℝ] => q * u) := by
      funext x
      simp only [Function.comp, nrm, norm_mul, hq, one_mul, mul_smul_comm]
    have hpre : (fun u : ℍ[ℝ] => q * u) ⁻¹' ball (0 : ℍ[ℝ]) 1 = ball 0 1 := by
      ext x
      simp [norm_mul, hq]
    have hres : (volume.restrict (ball (0 : ℍ[ℝ]) 1)).map (fun u => q * u)
        = volume.restrict (ball (0 : ℍ[ℝ]) 1) := by
      conv_rhs => rw [← map_mulL_volume q hq]
      rw [Measure.restrict_map hmq measurableSet_ball, hpre]
    rw [haarS3, Measure.map_smul, Measure.map_map hmq measurable_nrm, hcomm,
      ← Measure.map_map measurable_nrm hmq, hres]

/-- 具体的な測度での一リンク積分。 -/
theorem one_link_haarS3 (β : ℝ) (M : ℍ[ℝ]) :
    ∫ u, Real.exp (β * inner ℝ u M) ∂haarS3 = OneLinkSeries.F0 (β ^ 2 * ‖M‖ ^ 2 / 4) :=
  isHaarS3_haarS3.one_link β M

end WilsonOneLink

#print axioms WilsonOneLink.map_mulL_volume
#print axioms WilsonOneLink.isHaarS3_haarS3
#print axioms WilsonOneLink.one_link_haarS3

end HaarExample

-- ===== star の辺についての積分 =====
section StarLinkIntegral
/-
H3 の組み立て。`I*` の辺の場 `u : Star h2 → ℍ[ℝ]` と残りの辺の場 `W : Rest h2 → ℍ[ℝ]` を
`glue u W : Edge L → ℍ[ℝ]` に貼り合わせると、
  `exp(−SW β (glue u W)) = ∏_s exp(β ⟨star (u s), M_s(W)⟩)`（`SW_eq`）、
`I*` の辺を積測度 `⨂_s μ`（`IsHaarS3 μ`）で積分すると star ごとに分かれて
  **`∫ exp(−SW β (glue u W)) d(⨂_s μ)(u) = ∏_s F0(β²‖M_s‖²/4) = exp(−Phi β W)`**
（`Phi` は `StaplePerturbation` の有効作用）。
強結合域の定数の話の部品であり、連続極限・Clay の問題への主張は無い。
-/

open MeasureTheory Quaternion Finset

namespace WilsonOneLink

open StapleCurve OneLinkSeries CompleteFamilyLattice StaplePerturbation

theorem inner_star_left (u M : ℍ[ℝ]) : inner ℝ (star u) M = inner ℝ u (star M) := by
  rw [← re_mul_eq_inner, ← re_star_mul, ← star_mul, re_star, re_mul_comm']

variable {L : ℕ} [NeZero L] (h2 : 2 ∣ L)

/-- `I*` の辺の場と残りの辺の場の貼り合わせ。 -/
noncomputable def glue (u : Star h2 → ℍ[ℝ]) (W : Rest h2 → ℍ[ℝ]) : Edge L → ℍ[ℝ] :=
  fun e => if h : Istar h2 e then u ⟨e, h⟩ else W ⟨e, h⟩

omit [NeZero L] in
theorem glue_star (u : Star h2 → ℍ[ℝ]) (W : Rest h2 → ℍ[ℝ]) (s : Star h2) :
    glue h2 u W s.1 = u s := by
  unfold glue
  rw [dif_pos s.2]

omit [NeZero L] in
theorem restr_glue (u : Star h2 → ℍ[ℝ]) (W : Rest h2 → ℍ[ℝ]) :
    restr h2 (glue h2 u W) = W := by
  funext e
  unfold restr glue
  rw [dif_neg e.2]

omit [NeZero L] in
theorem norm_glue (u : Star h2 → ℍ[ℝ]) (W : Rest h2 → ℍ[ℝ]) (hu : ∀ s, ‖u s‖ = 1)
    (hW : ∀ e, ‖W e‖ = 1) (e : Edge L) : ‖glue h2 u W e‖ = 1 := by
  unfold glue
  split_ifs
  · exact hu _
  · exact hW _

/-- Boltzmann 因子は star ごとの積。 -/
theorem exp_neg_SW (hL2 : (2 : ZMod L) ≠ 0) (β : ℝ) (u : Star h2 → ℍ[ℝ]) (W : Rest h2 → ℍ[ℝ])
    (hu : ∀ s, ‖u s‖ = 1) (hW : ∀ e, ‖W e‖ = 1) :
    Real.exp (-SW β (glue h2 u W))
      = ∏ s : Star h2, Real.exp (β * inner ℝ (u s) (star (Mst h2 hL2 W s))) := by
  rw [SW_eq h2 hL2 β _ (norm_glue h2 u W hu hW), restr_glue, ← Real.exp_sum, neg_mul, neg_neg,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [glue_star, inner_star_left]

/-- **H3：`I*` の辺の積分で Wilson 作用は `StaplePerturbation.Phi` になる。** -/
theorem integral_star_links (hL2 : (2 : ZMod L) ≠ 0) (β : ℝ) (W : Rest h2 → ℍ[ℝ])
    (hW : ∀ e, ‖W e‖ = 1) {μ : Measure ℍ[ℝ]} (hμ : IsHaarS3 μ) :
    ∫ u, Real.exp (-SW β (glue h2 u W)) ∂(Measure.pi fun _ : Star h2 => μ)
      = Real.exp (-Phi h2 hL2 β W) := by
  have := hμ.prob
  have hae : ∀ᵐ u ∂(Measure.pi fun _ : Star h2 => μ), ∀ s, ‖u s‖ = 1 :=
    ae_all_iff.2 fun s => (Measure.tendsto_eval_ae_ae (μ := fun _ : Star h2 => μ)).eventually hμ.unit
  have e1 : ∫ u, Real.exp (-SW β (glue h2 u W)) ∂(Measure.pi fun _ : Star h2 => μ)
      = ∫ u, ∏ s : Star h2, Real.exp (β * inner ℝ (u s) (star (Mst h2 hL2 W s)))
          ∂(Measure.pi fun _ : Star h2 => μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    exact exp_neg_SW h2 hL2 β u W hu hW
  rw [e1, integral_fintype_prod_eq_prod
    (fun (s : Star h2) (v : ℍ[ℝ]) => Real.exp (β * inner ℝ v (star (Mst h2 hL2 W s))))]
  simp only [hμ.one_link, norm_star]
  unfold Phi Mst
  rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold G
  rw [Real.exp_log (F0_pos (by positivity))]

/-- 具体的な一様測度 `haarS3` での形。 -/
theorem integral_star_links_haarS3 (hL2 : (2 : ZMod L) ≠ 0) (β : ℝ) (W : Rest h2 → ℍ[ℝ])
    (hW : ∀ e, ‖W e‖ = 1) :
    ∫ u, Real.exp (-SW β (glue h2 u W)) ∂(Measure.pi fun _ : Star h2 => haarS3)
      = Real.exp (-Phi h2 hL2 β W) :=
  integral_star_links h2 hL2 β W hW isHaarS3_haarS3

/-- `L = 4` で仮定が満たされる。 -/
example (β : ℝ) (W : Rest (show 2 ∣ 4 by norm_num) → ℍ[ℝ]) (hW : ∀ e, ‖W e‖ = 1) :
    ∫ u, Real.exp (-SW β (glue _ u W)) ∂(Measure.pi fun _ : Star (show 2 ∣ 4 by norm_num) => haarS3)
      = Real.exp (-Phi _ (two_ne_zero_of_le (by norm_num)) β W) :=
  integral_star_links_haarS3 _ _ β W hW

end WilsonOneLink

#print axioms WilsonOneLink.inner_star_left
#print axioms WilsonOneLink.exp_neg_SW
#print axioms WilsonOneLink.integral_star_links
#print axioms WilsonOneLink.integral_star_links_haarS3

end StarLinkIntegral

-- ===== 球面測度との一致 =====
section HaarSphere
/-
`haarS3` は Mathlib の球面測度 `volume.toSphere`（`Metric.sphere 0 1` の上）を
正規化して `ℍ[ℝ]` に押し出したものに等しい。
-/

open MeasureTheory Quaternion Metric Set
open scoped Pointwise ENNReal

namespace WilsonOneLink

theorem cone_eq (A : Set ℍ[ℝ]) :
    Ioo (0 : ℝ) 1 • (sphere (0 : ℍ[ℝ]) 1 ∩ A) = (nrm ⁻¹' A ∩ ball 0 1) \ {0} := by
  ext x
  simp only [Set.mem_smul, mem_Ioo, mem_inter_iff, mem_sphere_iff_norm, sub_zero, mem_sdiff,
    mem_preimage, mem_ball_zero_iff, mem_singleton_iff]
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, v, ⟨hv, hvA⟩, rfl⟩
    have hn : ‖r • v‖ = r := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hr0.le]
    refine ⟨⟨?_, by rw [hn]; exact hr1⟩, ?_⟩
    · have : nrm (r • v) = v := by
        unfold nrm
        rw [hn, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
      rw [this]; exact hvA
    · intro h0
      rw [h0, norm_zero] at hn
      exact hr0.ne hn
  · rintro ⟨⟨hA, hx1⟩, hx0⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine ⟨‖x‖, ⟨hn, hx1⟩, nrm x, ⟨norm_smul_inv_norm hx0, hA⟩, ?_⟩
    unfold nrm
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem haarS3_eq_toSphere :
    haarS3 = ((volume : Measure ℍ[ℝ]).toSphere univ)⁻¹ •
      ((volume : Measure ℍ[ℝ]).toSphere).map Subtype.val := by
  ext A hA
  have hd0 : ((Module.finrank ℝ ℍ[ℝ] : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hdt : ((Module.finrank ℝ ℍ[ℝ] : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : volume (ball (0 : ℍ[ℝ]) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
  rw [haarS3, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_nrm hA, Measure.map_apply measurable_subtype_coe hA,
    Measure.restrict_apply (measurable_nrm hA), Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ (measurable_subtype_coe hA), Subtype.image_preimage_coe, cone_eq,
    measure_sdiff_null (measure_singleton 0), smul_eq_mul, smul_eq_mul,
    ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt)]
  calc (volume (ball (0 : ℍ[ℝ]) 1))⁻¹ * volume (nrm ⁻¹' A ∩ ball 0 1)
      = (((Module.finrank ℝ ℍ[ℝ] : ℕ) : ℝ≥0∞)⁻¹ * ((Module.finrank ℝ ℍ[ℝ] : ℕ) : ℝ≥0∞))
          * ((volume (ball (0 : ℍ[ℝ]) 1))⁻¹ * volume (nrm ⁻¹' A ∩ ball 0 1)) := by
        rw [ENNReal.inv_mul_cancel hd0 hdt, one_mul]
    _ = _ := by ring

end WilsonOneLink

#print axioms WilsonOneLink.cone_eq
#print axioms WilsonOneLink.haarS3_eq_toSphere

end HaarSphere

-- ===== 分布の形 =====
section HaarDistribution
/-
H2（分布の形）。`IsHaarS3 μ` の下で、連続な `f : ℝ → ℝ` について
  `∫ f(re u) dμ(u) = (2/π) ∫_0^π f(cos θ) sin²θ dθ`
——`re u` の分布は密度 `(2/π) sin²θ dθ`（`x = cos θ` で `(2/π)√(1−x²) dx`）の分布。
モーメントの一致（`cm_eq_mom`）と Weierstrass の多項式近似から。
-/

open MeasureTheory Quaternion Finset Real

namespace WilsonOneLink

open OneLinkSeries

variable {μ : Measure ℍ[ℝ]}

theorem IsHaarS3.re_mem_Icc (h : IsHaarS3 μ) : ∀ᵐ u ∂μ, u.re ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [h.unit] with u hu
  exact abs_le.1 (abs_re_le u hu)

theorem IsHaarS3.integrable_comp_re (h : IsHaarS3 μ) (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun u : ℍ[ℝ] => g u.re) μ := by
  have := h.prob
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Set.Icc (-1) 1))
  refine Integrable.of_bound (hg.comp continuous_re).aestronglyMeasurable C ?_
  filter_upwards [h.re_mem_Icc] with u hu
  exact hC _ hu

/-- 多項式では両辺が一致（モーメントの一致）。 -/
theorem IsHaarS3.integral_poly (h : IsHaarS3 μ) (p : Polynomial ℝ) :
    ∫ u, p.eval u.re ∂μ = 2 / π * ∫ θ in (0 : ℝ)..π, p.eval (cos θ) * sin θ ^ 2 := by
  simp only [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => (h.integrable_re_pow i).const_mul _),
    intervalIntegral.integral_finsetSum
      (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∫ θ in (0 : ℝ)..π, p.coeff i * cos θ ^ i * sin θ ^ 2 = p.coeff i * mom i := by
    unfold mom
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring
  rw [integral_const_mul, e, show ∫ u, u.re ^ i ∂μ = cm μ i from rfl, h.cm_eq_mom]
  ring

/-- **H2**：`re u` の分布は `(2/π) sin²θ dθ` を `cos` で押し出したもの。 -/
theorem IsHaarS3.integral_comp_re (h : IsHaarS3 μ) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ u, f u.re ∂μ = 2 / π * ∫ θ in (0 : ℝ)..π, f (cos θ) * sin θ ^ 2 := by
  have := h.prob
  have hpi : 0 < π := Real.pi_pos
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf.continuousOn (ε / 3)
    (by positivity)
  -- 測度の側
  have hA : ‖∫ u, (f u.re - p.eval u.re) ∂μ‖ ≤ ε / 3 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u : ℍ[ℝ] => f u.re - p.eval u.re)
      (C := ε / 3) (by
        filter_upwards [h.re_mem_Icc] with u hu
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hp _ hu).le)
    rwa [probReal_univ, mul_one] at this
  rw [integral_sub (h.integrable_comp_re f hf) (h.integrable_comp_re _ p.continuous),
    h.integral_poly p] at hA
  -- 区間の側
  have hB : ‖∫ θ in (0 : ℝ)..π, (f (cos θ) * sin θ ^ 2 - p.eval (cos θ) * sin θ ^ 2)‖
      ≤ ε / 3 * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    have h1 : |f (cos θ) - p.eval (cos θ)| ≤ ε / 3 := by
      rw [abs_sub_comm]
      exact (hp _ ⟨neg_one_le_cos θ, cos_le_one θ⟩).le
    have h2 : |sin θ| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_sin_le_one θ)
    rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_pow]
    calc |f (cos θ) - p.eval (cos θ)| * |sin θ| ^ 2 ≤ ε / 3 * 1 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ε / 3 := mul_one _
  rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), sub_zero, abs_of_pos hpi] at hB
  rw [Real.norm_eq_abs] at hA hB
  rw [Real.dist_eq]
  set a := ∫ u, f u.re ∂μ
  set b := ∫ θ in (0 : ℝ)..π, f (cos θ) * sin θ ^ 2
  set c := ∫ θ in (0 : ℝ)..π, p.eval (cos θ) * sin θ ^ 2
  have hB' : |2 / π * c - 2 / π * b| ≤ 2 / 3 * ε := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / π), abs_sub_comm]
    calc 2 / π * |b - c| ≤ 2 / π * (ε / 3 * π) := by gcongr
      _ = 2 / 3 * ε := by field_simp
  calc |a - 2 / π * b| = |(a - 2 / π * c) + (2 / π * c - 2 / π * b)| := by ring_nf
    _ ≤ |a - 2 / π * c| + |2 / π * c - 2 / π * b| := abs_add_le _ _
    _ ≤ ε / 3 + 2 / 3 * ε := add_le_add hA hB'
    _ = ε := by ring

end WilsonOneLink

#print axioms WilsonOneLink.IsHaarS3.integral_poly
#print axioms WilsonOneLink.IsHaarS3.integral_comp_re

end HaarDistribution
