/-
  CM 型の退化した例外類 — 純スピノルの族 `B` の階別と、その上の交点形式（有限の代数だけ）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `F_0` は総実 3 次体（我々の枡では `Q[θ]/(θ³+θ²−6θ−7)`、導手 19 の巡回 3 次体）、
  `q ∈ Q_{>0}`、`K = F_0(√−q)`（6 次 CM 体）。`X` は `F_0` による実乗法つきアーベル 6 次元多様体、
  `Θ ∈ H^{1,1}(X,Q) ∩ ∧²_{F_0}H¹(X,Q)` は非退化で、実素点ごとの分解 `Θ = Θ₁+Θ₂+Θ₃` は
  `Θ_j³ = 0` を満たす（各 `H¹_{σ̂_j}(X)` が 4 次元だから）。
  純スピノルの族は `ℓ_ε = ∏_j exp(√−q·ε_jΘ_j)`（`ε ∈ {±1}³`、8 個）で、その張る有理 8 次元空間が `B`。

  この頁で Lean にするのは次の四つで、いずれも**有限の組合せと有限の代数の等式**である。
  幾何・層・変形理論・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 符号の型（CM 型）の階別 `|T ∩ T₁| = i` の数え上げ（`1,3,3,1`）と、
      `KB₁` の線形方程式（素点 `σ` ごとに一本）に現れる項が**ちょうど一個**であること。
      これが「`c₁ ∉ KB₁ ⟺ β₁ ≠ 0`」の芯で、3 素点（`[F_0:Q] = 3`）の場合を尽くしで確かめる。
  (2) `⟨H^{1,1}(X,Q)⟩` の単項式（指数 `≤ 2` の三つ組、27 個）の次数別の個数 `1,3,6,7,6,3,1`、
      および奇次数の単項式が 13 個・偶次数が 14 個であること。
  (3) 4 個の奇指標（`ε_j` の 3 個と `ε₁ε₂ε₃`）の Hadamard 変換。`(a₁,a₂,a₃,p)` から
      `P_{K_0}` 成分の係数が `(a₁+a₂+a₃+p)/4` で出ること、および
      「残りの 3 成分が全て 0 ⟺ `a₁ = a₂ = a₃ = p`」。
  (4) 交点形式：奇部分の 27 単項式の畳み込みの最高次係数が `q²(Σ_j a_j a'_j + P P')` であること。
      これは `∫_X x_{f,P}·x_{f',P'} = q²(Tr_{F_0/Q}(f f') + P P')·∫_X ω` の係数の芯である。
  (5) 2 素点のときだけ成り立つ偶然（`N(f) = 1 ⟹ f_i^{-2}f_j^{-1} = f_j`）と、
      3 素点でそれが壊れること。
-/
import Mathlib

namespace CMHodgeSecantGrading

/-! ### 1. 符号の型の階別と `KB₁` の方程式 -/

/-- 3 実素点の上の符号の型。`true` が `+`（`T₁` の側）。 -/
abbrev Pat := Fin 3 → Bool

/-- 全て `+` の型（`T₁`）。 -/
def topPat : Pat := fun _ => true
/-- 全て `−` の型（`T̄₁`）。 -/
def botPat : Pat := fun _ => false

/-- `|T ∩ T₁|`：`+` の個数。 -/
def plusCount (e : Pat) : ℕ := (Finset.univ.filter (fun j => e j = true)).card

/-- `T ∩ T'`：値が一致する実素点の集合。 -/
def agree (e d : Pat) : Finset (Fin 3) := Finset.univ.filter (fun j => e j = d j)

/-- 階別 `B_i` の次元（`K̃` 上）：`1, 3, 3, 1`。和は `2³ = 8 = dim B`。 -/
theorem grade_cards :
    (Finset.univ.filter (fun e : Pat => plusCount e = 0)).card = 1 ∧
    (Finset.univ.filter (fun e : Pat => plusCount e = 1)).card = 3 ∧
    (Finset.univ.filter (fun e : Pat => plusCount e = 2)).card = 3 ∧
    (Finset.univ.filter (fun e : Pat => plusCount e = 3)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `dim B = 8`。 -/
theorem pat_card : Fintype.card Pat = 8 := by decide

/-- `α₀ ∈ P = B₀ ⊕ B_{e/2}` の台は `{T₁, T̄₁}` のみ。`β` の側で `BB₁` に効くのは
    `|T ∩ T'| = 1` の対で、素点 `σ = (j, s)` ごとにそれは**ちょうど一つ**である。
    （`Σ` は `K` の 6 個の埋め込み＝（実素点 `j`, 符号 `s`）の組。） -/
theorem kb1_exactly_one_term (j : Fin 3) (s : Bool) :
    (Finset.univ.filter (fun p : Pat × Pat =>
      (p.1 = topPat ∨ p.1 = botPat) ∧ agree p.1 p.2 = {j} ∧ p.1 j = s)).card = 1 := by
  revert j s
  decide

/-- 6 個の素点の方程式に現れる対を合わせると 6 個で、`BB₁ ∩ [P ⊗ (B₁+B_{e/2−1})]` の次元 `e = 6`
    と一致する。 -/
theorem kb1_total_pairs :
    (Finset.univ.filter (fun p : Pat × Pat =>
      (p.1 = topPat ∨ p.1 = botPat) ∧ (agree p.1 p.2).card = 1)).card = 6 := by decide

/-- `dim BB₁ = e·2^{e/2−1} = 24` は `dim KB₁ = 18` と上の `6` に分かれる。 -/
theorem bb1_split : (24 : ℕ) = 18 + 6 := by norm_num

/-! ### 2. `⟨H^{1,1}(X,Q)⟩` の単項式の数え上げ -/

/-- 指数の三つ組（各 `0,1,2`）。`Θ_j³ = 0` だから指数は `2` まで。 -/
abbrev Expv := Fin 3 → Fin 3

/-- 単項式の総次数（`Θ` の冪の次数）。 -/
def deg (k : Expv) : ℕ := (k 0).val + (k 1).val + (k 2).val

/-- 単項式は全部で 27 個。 -/
theorem expv_card : Fintype.card Expv = 27 := by decide

/-- 次数別の個数は `(1+x+x²)³` の係数 `1,3,6,7,6,3,1`。 -/
theorem deg_cards :
    (Finset.univ.filter (fun k : Expv => deg k = 0)).card = 1 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 1)).card = 3 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 2)).card = 6 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 3)).card = 7 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 4)).card = 6 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 5)).card = 3 ∧
    (Finset.univ.filter (fun k : Expv => deg k = 6)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- 奇次数の単項式は 13 個、偶次数は 14 個（`13 + 14 = 27`）。
    奇次数の側が `B` の奇部分（`Q` 上 4 次元）の入る場所である。 -/
theorem odd_even_cards :
    (Finset.univ.filter (fun k : Expv => deg k % 2 = 1)).card = 13 ∧
    (Finset.univ.filter (fun k : Expv => deg k % 2 = 0)).card = 14 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### 3. 奇指標の Hadamard 変換（`β₀`・`β₁` の判定） -/

variable {R : Type*} [Field R] [CharZero R]

/-- 4 個の奇指標の値 `(a₁,a₂,a₃,p)` を、4 個の純スピノルの類 `c₀,…,c₃` から作る。 -/
def aOf (c₀ c₁ c₂ c₃ : R) : R × R × R × R :=
  (c₀ + c₁ + c₂ - c₃, c₀ + c₁ - c₂ + c₃, c₀ - c₁ + c₂ + c₃, c₀ - c₁ - c₂ - c₃)

/-- `P_{K_0}` 成分の係数は `(a₁+a₂+a₃+p)/4`。 -/
theorem c0_from_a (c₀ c₁ c₂ c₃ : R) :
    (aOf c₀ c₁ c₂ c₃).1 + (aOf c₀ c₁ c₂ c₃).2.1 + (aOf c₀ c₁ c₂ c₃).2.2.1
      + (aOf c₀ c₁ c₂ c₃).2.2.2 = 4 * c₀ := by
  simp only [aOf]; ring

/-- 逆変換（`(a,p)` から純スピノルの係数へ）。 -/
theorem a_to_c (a₁ a₂ a₃ p : R) :
    aOf ((a₁+a₂+a₃+p)/4) ((a₁+a₂-a₃-p)/4) ((a₁-a₂+a₃-p)/4) ((-a₁+a₂+a₃-p)/4)
      = (a₁, a₂, a₃, p) := by
  simp only [aOf, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `β₁ = 0`（`B₁ ⊕ B_{e/2−1}` の成分が消える）⟺ `a₁ = a₂ = a₃ = p`。
    すなわち `f ∈ Q` かつ `P = f`。 -/
theorem beta1_vanishes_iff (a₁ a₂ a₃ p : R) :
    (a₁+a₂-a₃-p = 0 ∧ a₁-a₂+a₃-p = 0 ∧ -a₁+a₂+a₃-p = 0) ↔ (a₁ = p ∧ a₂ = p ∧ a₃ = p) := by
  have h2 : (2:R) ≠ 0 := by norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · have h5 : (2:R) * (a₁ - p) = 0 := by linear_combination h₁ + h₂
      have h6 : a₁ - p = 0 := (mul_eq_zero.mp h5).resolve_left h2
      linear_combination h6
    · have h5 : (2:R) * (a₂ - p) = 0 := by linear_combination h₁ + h₃
      have h6 : a₂ - p = 0 := (mul_eq_zero.mp h5).resolve_left h2
      linear_combination h6
    · have h5 : (2:R) * (a₃ - p) = 0 := by linear_combination h₂ + h₃
      have h6 : a₃ - p = 0 := (mul_eq_zero.mp h5).resolve_left h2
      linear_combination h6
  · rintro ⟨h₁, h₂, h₃⟩
    subst h₁; subst h₂; subst h₃
    refine ⟨by ring, by ring, by ring⟩

/-! ### 4. 交点形式：27 単項式の畳み込みの最高次係数 -/

/-- `x_{f,P} = (f·Θ)exp(−(q/2)Θ∧_{F_0}Θ) − qPπ` の単項式係数（`a j = σ̂_j(f)`）。
    非零なのは 13 個（`§2` の奇単項式の個数）。 -/
def co (a : Fin 3 → R) (P q : R) : ℕ → ℕ → ℕ → R
  | 1, 0, 0 => a 0
  | 1, 2, 0 => -q/2 * a 0
  | 1, 0, 2 => -q/2 * a 0
  | 1, 2, 2 => q^2/4 * a 0
  | 0, 1, 0 => a 1
  | 2, 1, 0 => -q/2 * a 1
  | 0, 1, 2 => -q/2 * a 1
  | 2, 1, 2 => q^2/4 * a 1
  | 0, 0, 1 => a 2
  | 2, 0, 1 => -q/2 * a 2
  | 0, 2, 1 => -q/2 * a 2
  | 2, 2, 1 => q^2/4 * a 2
  | 1, 1, 1 => -q * P
  | _, _, _ => 0

/-- **交点形式**：`∫_X x_{f,P}·x_{f',P'} / ∫_X ω = q²(Σ_j σ̂_j(f)σ̂_j(f') + P P')`
    `= q²(Tr_{F_0/Q}(f f') + P P')`。相棒の指数は `2 − k`（最高次 `ω = Θ₁²Θ₂²Θ₃²` を作る）。 -/
theorem top_pairing (a a' : Fin 3 → R) (P P' q : R) :
    (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
        co a P q i j k * co a' P' q (2-i) (2-j) (2-k))
      = q^2 * (a 0 * a' 0 + a 1 * a' 1 + a 2 * a' 2 + P * P') := by
  simp [Finset.sum_range_succ, co]
  ring

/-- `α₀ = x_{1,1}`（`a' = (1,1,1)`・`P' = 1`）との対：`q²(a₁+a₂+a₃+P)`。
    `§3` の `P_{K_0}` 成分の係数と同じ線形形式なので、
    **`ϕ̌(α₀⊗β₀)₀ ≠ 0` と `β₀ ≠ 0` は同値**である。 -/
theorem pairing_with_alpha0 (a : Fin 3 → R) (P q : R) :
    (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
        co a P q i j k * co (fun _ => 1) 1 q (2-i) (2-j) (2-k))
      = q^2 * (a 0 + a 1 + a 2 + P) := by
  rw [top_pairing]; ring

/-! ### 5. 2 素点だけの偶然 -/

/-- `[F:Q] = 2` で `N(f) = f₁f₂ = 1` なら `f₁²f₂² = 1`。これが
    `(g^{-1})^*Θ³` の係数 `f_i^{-2}f_j^{-1}` と `B` の要求する `f_j` を一致させる。 -/
theorem two_place_coincidence (f₁ f₂ : R) (h : f₁ * f₂ = 1) : f₁^2 * f₂^2 = 1 := by
  have : (f₁ * f₂)^2 = 1 := by rw [h]; ring
  linear_combination this

/-- `[F:Q] = 3` では `N(f) = f₁f₂f₃ = 1` から `f_i²f_j² = 1` は出ない。
    ゆえに `g^*Θ − (q/6)(g^{-1})^*Θ³ ∈ B_{√−qΘ}` は 3 素点では成り立たない。 -/
theorem three_place_no_coincidence :
    ∃ f₁ f₂ f₃ : ℚ, f₁ * f₂ * f₃ = 1 ∧ f₁^2 * f₂^2 ≠ 1 := by
  refine ⟨2, 3, 1/6, by norm_num, by norm_num⟩

/-! ### 6. `HT²(X)` の核の次元の分け方（厳密計算で観測した形） -/

/-- `dim HT²(X) = 2n² − n` は `(n² − n) + n²` に分かれる。
    厳密有理数計算で、純スピノルの偶部分・奇部分いずれを縮約しても
    `rank = n² − n`・`dim ker = n²`（`n = 3,4,5,6`）であった。
    （`n = 3` の `9` は文献 [M2] Prop 8.3.9 の値と一致する。
    ただしこの値は `Θ` の実乗法の構造に依らないので、構造の情報は持たない。） -/
theorem ht2_split (n : ℤ) : 2*n^2 - n = (n^2 - n) + n^2 := by ring

theorem ht2_values : (2*6^2 - 6 : ℤ) = 66 ∧ (6^2 - 6 : ℤ) = 30 ∧ (6^2 : ℤ) = 36 ∧
    (2*3^2 - 3 : ℤ) = 15 ∧ (3^2 - 3 : ℤ) = 6 ∧ (3^2 : ℤ) = 9 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end CMHodgeSecantGrading

#print axioms CMHodgeSecantGrading.grade_cards
#print axioms CMHodgeSecantGrading.pat_card
#print axioms CMHodgeSecantGrading.kb1_exactly_one_term
#print axioms CMHodgeSecantGrading.kb1_total_pairs
#print axioms CMHodgeSecantGrading.bb1_split
#print axioms CMHodgeSecantGrading.expv_card
#print axioms CMHodgeSecantGrading.deg_cards
#print axioms CMHodgeSecantGrading.odd_even_cards
#print axioms CMHodgeSecantGrading.c0_from_a
#print axioms CMHodgeSecantGrading.a_to_c
#print axioms CMHodgeSecantGrading.beta1_vanishes_iff
#print axioms CMHodgeSecantGrading.top_pairing
#print axioms CMHodgeSecantGrading.pairing_with_alpha0
#print axioms CMHodgeSecantGrading.two_place_coincidence
#print axioms CMHodgeSecantGrading.three_place_no_coincidence
#print axioms CMHodgeSecantGrading.ht2_split
#print axioms CMHodgeSecantGrading.ht2_values
