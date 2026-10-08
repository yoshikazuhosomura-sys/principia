/-
  CM 型の退化したホッジ類の候補：曲線類の整数性と層の側の一歩目（有限の代数だけ）

  ここに入っているのは、外部の計算が出した**数**についての有限の算術と、
  それらから形式的に従う含意だけである。層・コホモロジー・指数定理・Koszul 分解・
  Kleiman の横断性・Mayer–Vietoris は Lean に入っていない（幾何の側は紙の等級）。
-/
import Mathlib

namespace CMHodge

/-! ## 1. 円分配（round robin）の対の数 -/

/-- `y` 個を `c` スロットに順に配ると、余り `r` 個のスロットが `q+1` 個・残りが `q` 個を持つ。 -/
theorem round_robin_split (y c q r : ℕ) (hq : y = c * q + r) (hr : r ≤ c) :
    y = r * (q + 1) + (c - r) * q := by
  obtain ⟨k, hk⟩ := Nat.le.dest hr
  subst hk; subst hq
  rw [Nat.add_sub_cancel_left]
  ring

/-- 実データ：`y = 1182`・`c = 113` なら商 10・余り 52。 -/
theorem min_multiplicity_split : (1182 : ℕ) = 113 * 10 + 52 ∧ (52 : ℕ) < 113 := by
  constructor <;> norm_num

/-- 同じスロットに落ちる対の数（対角）は `r·C(q+1,2) + (c−r)·C(q,2)`。
    `y = 1182`・`c = 113` での値と、余次元 6 に移る対の数。 -/
theorem diagonal_pairs_1182 :
    52 * (11 * 10 / 2) + 61 * (10 * 9 / 2) = 5605 ∧
    1182 * 1181 / 2 = 697971 ∧
    1182 * 1181 / 2 - (52 * (11 * 10 / 2) + 61 * (10 * 9 / 2)) = 692366 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- 円分配の重みは「近似 `y_k y_l / c`」と一致しない：ずれは `Σ_s a b − y_k y_l / c` で、
    整列型なら `min(r_k,r_l) − r_k r_l / c`。`r_k = 52`・`r_l = 52`・`c = 113` の例。 -/
theorem exact_vs_approx_pair_weight :
    (52 : ℚ) - 52 * 52 / 113 = 3172 / 113 ∧ (0 : ℚ) < 3172 / 113 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## 2. `glue_exact` と `[C′]` -/

/-- 円分配の厳密な数は、第一近似（`glue/c`）より**小さい**。 -/
theorem glue_exact_lt_approx :
    23891801266886140992 * 113 < (2707982373794854464480 : ℕ) := by norm_num

/-- それでも次数 10 の下限（`glue ≥ |deficit|`）は保たれる。 -/
theorem glue_exact_ge_deficit :
    (21588496448972677456 : ℕ) < 23891801266886140992 := by norm_num

/-- `[C′]` の 6 座標（`deficit + glue_exact`）。 -/
def CC : List ℤ :=
  [764943211908060616, 770628938189068160, 767732667816334760,
   -29656975399003664, -14594220427009064, 4156233642976456]

/-- 5 重完全交叉の類が生む格子は `4Z⁶`（Hermite 標準形の対角が `(4,4,4,4,4,4)`）なので、
    整数性の判定は「6 座標が 4 で割れるか」だけになる。`[C′]` は通る。 -/
theorem CC_in_four_Z : ∀ v ∈ CC, (4 : ℤ) ∣ v := by decide

/-- 実際には 8 で割れる（`gcd = 8`）。 -/
theorem CC_gcd_eight : ∀ v ∈ CC, (8 : ℤ) ∣ v := by decide

/-- `[C′]·Θ`（座標 0,1,2 の和）。 -/
theorem CC_theta_degree :
    764943211908060616 + 770628938189068160 + 767732667816334760
      = (2303304817913463536 : ℤ) := by norm_num

/-- LP の基底（6 本の原子）が張る格子は `4Z⁶` の真の部分格子であり、指数は 1 でない
    ⇒ 6 本の台では係数の分母が消えない。実測の一例 `|det| = 2^42`。 -/
theorem six_atom_basis_index_not_one :
    (4398046511104 : ℕ) = 4096 * 1073741824 ∧ (1073741824 : ℕ) ≠ 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- 丸めの余裕：Babai の補正 `‖k‖_∞ = 9` は内点の最小成分よりずっと小さいので
    非負性が壊れない。 -/
theorem rounding_margin_safe : (9 : ℕ) < 155200520199 ∧ 155200520199 - 9 > 0 := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## 3. 次数 12 -/

/-- `C′` を入れる前の `n` と、`ch(O_{C′})_{12} = −2265856817939027152` を入れた後の `n_final`。 -/
theorem degree12_after_curve :
    (17657751979690799860060 : ℤ) + 2265856817939027152 = 17660017836508738887212 ∧
    (0 : ℤ) < 17660017836508738887212 := by
  refine ⟨by norm_num, by norm_num⟩

/-- 孤立点は `ch` の次数 12 に `+n[pt]` しか足せないので、`n > 0` が必要条件である。
    円分配の厳密な数でも、近似の値（`1.71085×10²²`）より大きい。 -/
theorem degree12_exact_beats_approx :
    (1933262236425183396439556 : ℤ) < 113 * 17657751979690799860060 := by norm_num

/-! ## 4. 層の側：`χ(F,F)` -/

/-- `χ(F,F) = −2∫ch₂ch₁₀ + 2∫ch₄ch₈ − ∫ch₆²` で `ch₄(F) = 0`。
    `∫ch₂ch₁₀ = 123794697600`・`∫ch₆² = 247589395200` から。 -/
theorem chi_FF_from_pairings :
    -2 * 123794697600 + 2 * 0 - 247589395200 = (-495178790400 : ℤ) := by norm_num

/-- 閉じた形 `χ(F,F) = −24 g² q²`（`g = 7560`・`q = 19`）。 -/
theorem chi_FF_closed : -24 * 7560 ^ 2 * 19 ^ 2 = (-495178790400 : ℤ) := by norm_num

/-- `∫ch₂ch₁₀ = g·(g q²/8)·∫Θ²W²` と `∫ch₆² = (g q/2)²·∫Θ²W²`（`∫Θ²W² = 48`）。
    ゆえに `χ(F,F) = −(g²q²/2)·48`。 -/
theorem chi_FF_from_theta_W_squared :
    (7560 : ℚ) * (7560 * 19 ^ 2 / 8) * 48 = 123794697600 ∧
    ((7560 : ℚ) * 19 / 2) ^ 2 * 48 = 247589395200 ∧
    -((7560 : ℚ) ^ 2 * 19 ^ 2 / 2) * 48 = -495178790400 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- `ext^i = ext^{6−i}`（Serre 双対・`K_X = O`）と `ext⁰ = 1` を入れると、
    `χ(F,F)` は `ext¹`・`ext²`・`ext³` の一つの線型関係になる。 -/
theorem ext_relation (e0 e1 e2 e3 : ℤ) (h0 : e0 = 1)
    (hchi : 2 * e0 - 2 * e1 + 2 * e2 - e3 = -495178790400) :
    2 * e1 + e3 = 2 + 2 * e2 + 495178790400 := by
  subst h0; linarith

/-- `Ext¹` は（`ext² = ext³ = 0` の最も小さい場合でも）`10¹¹` の桁になる。 -/
theorem ext1_large (e1 : ℤ) (h : 2 * e1 + 0 = 2 + 2 * 0 + 495178790400) :
    247589395201 = e1 := by linarith

/-! ## 5. `h⁰(O_D) = 1`（`D` の既約性に依らない） -/

/-- `−gΘ ↔ −gI` の 3×3 の固有値は `−g` の三重。`X = B₂³` では各固有値の重複度が 2 なので
    Mumford 指数は `2·3 = 6`。`i ≠ 1` なので `H¹(X,O(−gΘ)) = 0`。 -/
theorem index_minus_g_theta : 2 * 3 = 6 ∧ (6 : ℕ) ≠ 1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- `χ(O(−gΘ)) = det(−gI)² = g⁶`。 -/
theorem chi_minus_g_theta :
    (432081216000 : ℕ) ^ 2 = 7560 ^ 6 ∧ (432081216000 : ℕ) ^ 2 = 186694177220038656000000 := by
  refine ⟨by norm_num, by norm_num⟩

/-- 含有条件の残り `gI − 113·Σ_j S₁^{(j)}` は `1119 I + 339 (J − I)` で、
    固有値は `1119 − 339 = 780`（二重）と `1119 + 2·339 = 1797`。狭義正定値・`det > 0`。 -/
theorem residual_divisor_pos_def :
    (7560 : ℤ) - 113 * 57 = 1119 ∧ (0 : ℤ) - 113 * (-3) = 339 ∧
    (780 : ℤ) ^ 2 * 1797 = 1093294800 ∧ (0 : ℤ) < 1093294800 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 6. `Ext¹` の一歩目と半正則性の舞台 -/

/-- `Σ_k y_k χ(N_{Z_k/D}) = Σ y χ(O(S₂)) + Σ y χ(O(S₃))` は**負**なので、
    `h⁰(N)` の下からの評価は `χ` からは出ない。 -/
theorem chiN_negative :
    (-233151571931207586036896 : ℤ) + 232996619586328405647136 = -154952344879180389760 ∧
    (-154952344879180389760 : ℤ) < 0 := by
  refine ⟨by norm_num, by norm_num⟩

/-- Koszul の 16 項（`M = S₂,S₃` × 8 部分集合）のうち、`det = 0`（退化）は 6214 項である。
    退化した項には Mumford の指数定理が使えない。 -/
theorem koszul_degenerate_count :
    835 * 16 = 13360 ∧ 3345 + 83 + 3718 = 7146 ∧ 13360 - 7146 = 6214 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- 半正則写像の的 `⊕_q H^{q+2}(X,Ω^q)` の次元（`h^{p,q} = C(6,p)C(6,q)`）。 -/
theorem semiregularity_target_dim :
    15 + 120 + 225 + 120 + 15 = 495 ∧
    Nat.choose 6 2 * Nat.choose 6 0 = 15 ∧ Nat.choose 6 3 * Nat.choose 6 1 = 120 ∧
    Nat.choose 6 4 * Nat.choose 6 2 = 225 ∧ Nat.choose 6 5 * Nat.choose 6 3 = 120 ∧
    Nat.choose 6 6 * Nat.choose 6 4 = 15 := by
  refine ⟨by norm_num, by decide, by decide, by decide, by decide, by decide⟩

/-- 同スロットの対の総数と、余次元 6 に移った対の総数（円分配・`c = 113`）。 -/
theorem pair_census :
    (309206455 : ℕ) + 5150089757 + 29558581714 = 35017877926 := by norm_num

end CMHodge

#print axioms CMHodge.round_robin_split
#print axioms CMHodge.diagonal_pairs_1182
#print axioms CMHodge.exact_vs_approx_pair_weight
#print axioms CMHodge.glue_exact_lt_approx
#print axioms CMHodge.glue_exact_ge_deficit
#print axioms CMHodge.CC_in_four_Z
#print axioms CMHodge.CC_gcd_eight
#print axioms CMHodge.CC_theta_degree
#print axioms CMHodge.six_atom_basis_index_not_one
#print axioms CMHodge.rounding_margin_safe
#print axioms CMHodge.degree12_after_curve
#print axioms CMHodge.degree12_exact_beats_approx
#print axioms CMHodge.chi_FF_from_pairings
#print axioms CMHodge.chi_FF_closed
#print axioms CMHodge.chi_FF_from_theta_W_squared
#print axioms CMHodge.ext_relation
#print axioms CMHodge.ext1_large
#print axioms CMHodge.index_minus_g_theta
#print axioms CMHodge.chi_minus_g_theta
#print axioms CMHodge.residual_divisor_pos_def
#print axioms CMHodge.chiN_negative
#print axioms CMHodge.koszul_degenerate_count
#print axioms CMHodge.semiregularity_target_dim
#print axioms CMHodge.pair_census
