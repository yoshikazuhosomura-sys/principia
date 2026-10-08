/-
  退化 CM 型の例外類 — `X × X̂` の側の閉じた核

  先行の計算で、`ξ`（`A × E` の余次元 2 の例外ホッジ類）は 12 次元 `B = A × E³` の
  Weil 類の引き戻しであり、`B` は分裂 Weil 型（署名 `(2,2)` が 3 実素点・`disc = 1`）と分かった。
  `F = F_0(√−19)`（6 次 CM・巡回）・`F_0 = Q[θ]/(θ³+θ²−6θ−7)`（導手 19 の巡回 3 次体）。

  ここで扱うのは Markman 2509.23079 の側、すなわち
  `X` を `F_0` による実乗法つきアーベル 6 次元多様体、`Θ ∈ H^{1,1}(X,Q) ∩ ∧²_{F_0}H¹(X,Q)`、
  `q = 19` として作る `(X × X̂, η, Ξ_t)` である。その `F`-エルミート形式は（同論文 Lemma 11.1.2 の
  証明の行列表示で）`H_t = −t²√−q · Θ`（`Θ` は `H¹(X̂,Q)` 上の `F`-反対称形式・階数 `d`）。

  ここで Lean にするのは**有限の代数の等式と有限の組合せの数え上げだけ**である。
  幾何・代数的サイクル・層・変形理論・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 階数 4 の反対称行列の行列式は Pfaffian の平方（`det4_eq_pf_sq`）。
      ゆえに `det H_t = (−t²√−q)⁴ det Θ` は `F_0` の平方で、判別式の類は `1 = (−1)^{d/2}`。
  (2) `d = 2` では同じ計算が `disc = [−q] = [−1] = (−1)^{d/2}` を与える（`detH_d2_class`）。
  (3) `e = [K:Q] = 6` の CM 型の組合せ：`dim B = 8`・`dim BB_i = (8,24,24,8)`・`dim HW = 6`。
      `Π : BB_1 → HW` は `e = 2` のときだけ単射で、`e = 6` では核が 18 次元（`pi_not_injective`）。
  (4) `HT²(X)` の中で `α = 1 − (q/2)Θ∧_FΘ` を消す部分空間の次元の組合せ的な核
      （block 対角の数え上げ。数値は厳密有理数計算と一致）。
-/
import Mathlib

namespace CMHodgeSecant

/-! ### 1. 階数 4 の反対称形式：`det = Pf²`（判別式が平方であることの核） -/

/-- `d = 4` の反対称行列（`a = Θ₁₂`, `b = Θ₁₃`, `c = Θ₁₄`, `d' = Θ₂₃`, `e = Θ₂₄`, `f = Θ₃₄`）。 -/
def A4 (a b c d' e f : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, a, b, c; -a, 0, d', e; -b, -d', 0, f; -c, -e, -f, 0]

/-- Pfaffian。 -/
def pf4 (a b c d' e f : ℤ) : ℤ := a * f - b * e + c * d'

/-- 反対称 `4×4` の行列式は Pfaffian の平方。 -/
theorem det4_eq_pf_sq (a b c d' e f : ℤ) :
    (A4 a b c d' e f).det = (pf4 a b c d' e f) ^ 2 := by
  simp [A4, pf4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix_apply]
  ring

/-- `d = 4`：`det H_t = (−t²·√−q)⁴ · det Θ` は `F_0` の平方。
    （`u = −t²`・`v = √−q`・`v² = −q`・`det Θ = Pf²`。）
    ゆえに判別式の類は `1 = (−1)^{d/2}` で、（署名が `(2,2)` なら）分裂型である。 -/
theorem detH_d4_is_square (u v q p : ℤ) (hv : v ^ 2 = -q) :
    (u * v) ^ 4 * p ^ 2 = (u ^ 2 * q * p) ^ 2 := by
  have h4 : v ^ 4 = q ^ 2 := by
    have h : v ^ 4 = (v ^ 2) ^ 2 := by ring
    rw [h, hv]; ring
  calc (u * v) ^ 4 * p ^ 2 = u ^ 4 * v ^ 4 * p ^ 2 := by ring
    _ = u ^ 4 * q ^ 2 * p ^ 2 := by rw [h4]
    _ = (u ^ 2 * q * p) ^ 2 := by ring

/-- `d = 2`：同じ計算が `disc = [−q]` を与える（`−q` は `F_0^*/N` で `[−1]`、`q = N(√−q)` だから）。
    `(−1)^{d/2} = −1` と整合する。 -/
theorem detH_d2_class (u v q a : ℤ) (hv : v ^ 2 = -q) :
    (u * v) ^ 2 * a ^ 2 = -q * (u * a) ^ 2 := by
  calc (u * v) ^ 2 * a ^ 2 = u ^ 2 * v ^ 2 * a ^ 2 := by ring
    _ = u ^ 2 * -q * a ^ 2 := by rw [hv]
    _ = -q * (u * a) ^ 2 := by ring

/-- `d = 4` のときの Deligne–Milne Cor 4.2 の目標値。 -/
theorem split_target4 : (-1 : ℤ) ^ (4 / 2) = 1 := by decide

/-- `d = 2` のときの目標値。 -/
theorem split_target2 : (-1 : ℤ) ^ (2 / 2) = -1 := by decide

/-! ### 2. `e = [K:Q] = 6` の CM 型の組合せ（`B ⊗ B` の階層と `Π` の核） -/

/-- CM 型 = 3 つの実素点それぞれでの持ち上げの選択。 -/
abbrev CMT := Fin 3 → Bool

/-- `|T ∩ T'|`＝一致する実素点の個数。 -/
def agree (T T' : CMT) : ℕ := (Finset.univ.filter fun i => T i = T' i).card

/-- `dim B = 2^{e/2} = 8`。 -/
theorem num_types : Fintype.card CMT = 8 := by decide

/-- `dim BB_k`＝`|T ∩ T'| = k` となる対の個数。 -/
def bbDim (k : ℕ) : ℕ := (Finset.univ.filter fun p : CMT × CMT => agree p.1 p.2 = k).card

/-- `(dim BB_0, …, dim BB_3) = (8, 24, 24, 8)`。 -/
theorem bb_dims : (List.range 4).map bbDim = [8, 24, 24, 8] := by decide

/-- `dim BB_1 = e·2^{e/2−1} = 6·4 = 24`（Markman §10.1 の式）。 -/
theorem bb1_formula : bbDim 1 = 6 * 2 ^ (3 - 1) := by decide

/-- `Σ_k dim BB_k = dim(B ⊗ B) = 2^e = 64`。 -/
theorem bb_total : bbDim 0 + bbDim 1 + bbDim 2 + bbDim 3 = 64 := by decide

/-- `dim HW = e = 6 < 24 = dim BB_1`：`Π : BB_1 → HW` は `e = 6` では単射でない
    （`e = 2` のときだけ同型。Markman §10.1）。 -/
theorem pi_not_injective : 6 < bbDim 1 := by decide

/-- `Π` の核 `KB_1` の次元。 -/
theorem ker_pi_dim : bbDim 1 - 6 = 18 := by decide

/-! ### 3. `HT²(X)` の中で `α` を消す部分空間（block 対角の数え上げ） -/

/-- `H¹(X,R) = ⊕_{σ̂} H¹_{σ̂}(X)`：`Fin 6` を 3 つの block `{0,1},{2,3},{4,5}` に分ける。 -/
def blk (i : Fin 6) : ℕ := i.val / 2

/-- `μ ∈ V ⊗ V̄^*` のうち `F_0` 同変なもの（block 対角）の個数 `= 12`。
    本稿の厳密計算では `ker(⌋α) ∩ H¹(T_X)` がちょうどこれに一致した。 -/
theorem eqpairs_card :
    (Finset.univ.filter fun p : Fin 6 × Fin 6 => blk p.1 = blk p.2).card = 12 := by decide

/-- `i < j` で同じ block に入る対は 3 個。ゆえに `a ∈ ∧²V` 側の核は `C(6,2) − 3 = 12`。 -/
theorem diag2_card :
    (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ blk p.1 = blk p.2).card = 3 := by
  decide

theorem a_ker_dim : Nat.choose 6 2 - 3 = 12 := by decide

/-- 2 元集合は 3 つの block すべてと交わることができない。
    これが `b ∧ (Θ∧_FΘ) = 0 ⟹ b = 0`（`H²(O_X)` 側の核が 0）の組合せ的な核である。 -/
theorem no_pair_meets_all :
    ∀ p : Fin 6 × Fin 6, p.1 < p.2 →
      ¬ (∀ s : Fin 3, blk p.1 = s.val ∨ blk p.2 = s.val) := by decide

/-- `dim HT²(X) = C(n,2) + n² + C(n,2) = 2n² − n`：`n = 6` で 66、`n = 3` で 15
    （後者は Markman [M2] の `HT²(X)` の次元と一致）。 -/
theorem ht2_dim6 : Nat.choose 6 2 + 6 * 6 + Nat.choose 6 2 = 66 := by decide

theorem ht2_dim3 : Nat.choose 3 2 + 3 * 3 + Nat.choose 3 2 = 15 := by decide

/-- 本稿の厳密有理数計算の内訳：`12 (∧²V) + 12 (V⊗V̄^*) + 0 (∧²V̄^*) = 24`。 -/
theorem ker_alpha_total : 12 + 12 + 0 = 24 := by decide

/-- Weil 型の周期領域 `Ω_{B,t} ≅ (開集合 ⊂ ∏_{σ̂} Gr(d/2, V_{T(σ̂)}))` の次元
    `= [F:Q]·(d/2)² = 3·4 = 12`（Markman §9.2 末尾）。`ker(⌋α) ∩ H¹(T_X)` の 12 と一致する。 -/
theorem period_dim : 3 * (4 / 2) ^ 2 = 12 := by decide

/-- `[F:Q] = 1`・`d = 6` の既知の枡（Markman [M2]）では同じ式が 9 を与える。 -/
theorem period_dim_M2 : 1 * (6 / 2) ^ 2 = 9 := by decide

/-! ### 4. `B` 自身は `X × X̂` の形になれない（数値の核） -/

/-- `X × X̂ ~ X × X` で `dim X = m`、`2m = 12` なら `m = 6 < 9 = dim A`。
    `A` は単純だから `A` は `X × X` の同種因子になれない。 -/
theorem no_selfdual_realisation (m : ℕ) (h : 2 * m = 12) : m < 9 := by omega

/-- `d = 4·dim X/[K:Q]`：`dim X = 6`・`[K:Q] = 6` で `d = 4`。 -/
theorem d_value : 4 * 6 / 6 = 4 := by decide

end CMHodgeSecant

#print axioms CMHodgeSecant.det4_eq_pf_sq
#print axioms CMHodgeSecant.detH_d4_is_square
#print axioms CMHodgeSecant.detH_d2_class
#print axioms CMHodgeSecant.split_target4
#print axioms CMHodgeSecant.split_target2
#print axioms CMHodgeSecant.num_types
#print axioms CMHodgeSecant.bb_dims
#print axioms CMHodgeSecant.bb1_formula
#print axioms CMHodgeSecant.bb_total
#print axioms CMHodgeSecant.pi_not_injective
#print axioms CMHodgeSecant.ker_pi_dim
#print axioms CMHodgeSecant.eqpairs_card
#print axioms CMHodgeSecant.diag2_card
#print axioms CMHodgeSecant.a_ker_dim
#print axioms CMHodgeSecant.no_pair_meets_all
#print axioms CMHodgeSecant.ht2_dim6
#print axioms CMHodgeSecant.ht2_dim3
#print axioms CMHodgeSecant.ker_alpha_total
#print axioms CMHodgeSecant.period_dim
#print axioms CMHodgeSecant.period_dim_M2
#print axioms CMHodgeSecant.no_selfdual_realisation
#print axioms CMHodgeSecant.d_value
