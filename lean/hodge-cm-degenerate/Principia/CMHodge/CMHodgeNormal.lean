/-
  ホッジ予想：非正規な因子（`Sing Y` が 7 次元）の符号の勘定

  幾何は一切入れていない。入れたのは次の三種の**算術**だけである。

  (1) `NS(A) ≅ O_{K_0}`（`K_0` は 9 次総実体）の実符号座標 `e_j` の勘定。
      * 非零な整数ノルムを持つ nef 類は豊富（境界の格子点が存在しない）。
      * 「箱」`0 < 2 e_j(c) < e_j(y)`（`j = 0,…,8`）が整数点を持つには
        `N(y) > 2⁹ = 512` が必要。これが小平消滅による閉鎖条件の**空でない条件**である。
      * Nakai–Moishezon を「豊富 ＋ nef」の分解で通すときの二項展開の正値性。
      * 交点数がパーマネント（非負行列で非負・正行列で正）。
  (2) `W_F = ∧³_F H_1(A,Q)` の CM 型の勘定：重み `(2,1,2,1,2,1)`・level 1・
      `{n = 2}` が `Z/6` の位数 3 の部分群に一致（＝ `Q(√−19)` から誘導）。陰性対照つき。
  (3) 位数 19 の群から `±1` への準同型は自明（`E` 上の `μ_19` 作用は平行移動しかない）。

  `sorry` 0・`native_decide` 不使用。末尾に `#print axioms`。
-/
import Mathlib

namespace CMHodge

open Finset

/-! ## 1. 符号の勘定（`NS(A) ≅ O_{K_0}`、9 個の実符号座標） -/

/-- nef（全成分 ≥ 0）で積が非零なら、全成分が正（＝豊富）。
    `O_{K_0}` では `∏_j e_j(y) = N_{K_0/Q}(y)` が非零整数なので、
    **非零な nef 類はつねに豊富である**（nef 錐の境界に格子点がない）。 -/
theorem nef_pos_of_prod_ne_zero {n : ℕ} (e : Fin n → ℝ)
    (h0 : ∀ j, 0 ≤ e j) (hp : ∏ j, e j ≠ 0) : ∀ j, 0 < e j := by
  intro j
  rcases lt_or_eq_of_le (h0 j) with h | h
  · exact h
  · exact absurd (Finset.prod_eq_zero (Finset.mem_univ j) h.symm) hp

/-- 整数ノルム版：`∏_j e_j = (N : ℝ)` で `N ≠ 0` なら、nef ⟹ 豊富。 -/
theorem nef_pos_of_int_norm {n : ℕ} (e : Fin n → ℝ) (N : ℤ) (hN : N ≠ 0)
    (hprod : ∏ j, e j = (N : ℝ)) (h0 : ∀ j, 0 ≤ e j) : ∀ j, 0 < e j := by
  refine nef_pos_of_prod_ne_zero e h0 ?_
  rw [hprod]
  exact Int.cast_ne_zero.mpr hN

/-- 「箱」の壁：`0 < 2 e_j(c) < e_j(y)`（`j = 0,…,8`）かつ `∏_j e_j(c) ≥ 1`（`|N(c)| ≥ 1`）なら
    `∏_j e_j(y) > 512 = 2⁹`。
    つまり **`N(y) ≤ 512` の偏極では、`I_W ⊗ L_c` の生成閾値による閉鎖条件は空**である。 -/
theorem box_forces_norm_gt (ey ec : Fin 9 → ℝ)
    (hc : ∀ j, 0 < ec j) (hlt : ∀ j, 2 * ec j < ey j)
    (hn : 1 ≤ ∏ j, ec j) : 512 < ∏ j, ey j := by
  have h2 : ∏ j, (2 * ec j) < ∏ j, ey j := by
    refine Finset.prod_lt_prod_of_nonempty ?_ (fun j _ => hlt j) ⟨0, Finset.mem_univ 0⟩
    intro j _
    have := hc j
    linarith
  have hfac : ∏ j : Fin 9, (2 * ec j) = 512 * ∏ j, ec j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    norm_num
  have : (512 : ℝ) * 1 ≤ 512 * ∏ j, ec j := by
    exact mul_le_mul_of_nonneg_left hn (by norm_num)
  linarith [hfac ▸ h2]

/-- 対偶：`∏_j e_j(y) ≤ 512` なら、箱の中に `|N(c)| ≥ 1` の点はない。 -/
theorem no_box_of_norm_le (ey : Fin 9 → ℝ) (h : ∏ j, ey j ≤ 512) :
    ¬ ∃ ec : Fin 9 → ℝ, (∀ j, 0 < ec j) ∧ (∀ j, 2 * ec j < ey j) ∧ 1 ≤ ∏ j, ec j := by
  rintro ⟨ec, hc, hlt, hn⟩
  linarith [box_forces_norm_gt ey ec hc hlt hn]

/-! ## 2. Nakai–Moishezon を「豊富 ＋ nef」で通す二項展開 -/

/-- `D = P + M`（`P` 豊富・`M` nef）のとき、`D^k·V` の二項展開
    `Σ_i C(k,i) (P^{k−i} M^i · V)` は、`i ≥ 1` の項が非負で `i = 0` の項が正なら正。
    これが「`y − 2c` が豊富なら `L_y|_W − K_W` は `W` 上豊富」（Nakai の全部の `V` で成立）の
    数値の芯である。 -/
theorem binom_sum_pos (k : ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h0 : 0 < x 0) :
    0 < ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * x i := by
  have hsplit : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * x i
      = (k.choose 0 : ℝ) * x 0
        + ∑ i ∈ Finset.Ico 1 (k + 1), (k.choose i : ℝ) * x i := by
    rw [Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : (0 : ℕ) < k + 1)
        (fun i => (k.choose i : ℝ) * x i)]
  have hrest : 0 ≤ ∑ i ∈ Finset.Ico 1 (k + 1), (k.choose i : ℝ) * x i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hx i)
  rw [hsplit]
  have : (k.choose 0 : ℝ) = 1 := by simp
  rw [this]
  linarith

/-- つまみ因子の等式 `2(L_y|_W − K_W) = Δ` と `Δ` の有効性（`Δ·h⁶ ≥ 0`）から
    `K_W·h⁶ ≤ L_y·h⁶`。さらに `K_W·h⁶ > 0`（`ω_W` が豊富）なら `Δ·h⁶ < 2 L_y·h⁶`。 -/
theorem pinch_bounds (ly kw d : ℝ) (hd : 0 ≤ d) (heq : 2 * (ly - kw) = d)
    (hk : 0 < kw) : kw ≤ ly ∧ d < 2 * ly := by
  constructor <;> linarith

/-! ## 3. 交点数はパーマネント -/

/-- 9 個の類の交点数 `(L_{y_1}···L_{y_9}) = perm[e_j(y_i)]`。 -/
def perm {n : ℕ} (M : Fin n → Fin n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i)

theorem perm_nonneg {n : ℕ} (M : Fin n → Fin n → ℝ) (h : ∀ i j, 0 ≤ M i j) :
    0 ≤ perm M :=
  Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun i _ => h i (σ i)

theorem perm_pos {n : ℕ} (M : Fin n → Fin n → ℝ) (h : ∀ i j, 0 < M i j) :
    0 < perm M := by
  refine Finset.sum_pos (fun σ _ => Finset.prod_pos fun i _ => h i (σ i)) ?_
  exact ⟨1, Finset.mem_univ 1⟩

/-! ## 4. `W_F = ∧³_F H_1(A,Q)` の CM 型 -/

/-- 退化かつ原始的な CM 型 `S ⊂ Z/18`（埋め込みは `ζ ↦ ζ^{2^k}` で添字づける）。 -/
def Sl : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 16]

def inS (k : ℕ) : Bool := Sl.contains k

/-- `S` は CM 型：各対 `{k, k+9}` からちょうど一つ。 -/
theorem Sl_cm : ∀ k < 18, (inS k = true) ↔ ¬ (inS ((k + 9) % 18) = true) := by decide

/-- 6 次 CM 部分体 `F = K^{⟨γ⁶⟩}` の埋め込みは `k mod 6` で添字づく。
    `wt c = #(C_c ∩ S)` は `∧³_F H_1(A,Q)` の `c` 成分のホッジ重み。 -/
def wt (c : ℕ) : ℕ := ((List.range 18).filter (fun k => decide (k % 6 = c) && inS k)).length

theorem wt_values : wt 0 = 2 ∧ wt 1 = 1 ∧ wt 2 = 2 ∧ wt 3 = 1 ∧ wt 4 = 2 ∧ wt 5 = 1 := by
  decide

/-- **level 1**：すべての重みが `{1,2}`（＝ 3 でも 0 でもない）。
    ゆえに `W_F` はひねりの後で 3 次元アーベル多様体の `H¹` になる。 -/
theorem wt_level_one : ∀ c < 6, wt c = 1 ∨ wt c = 2 := by decide

/-- 共役対 `(c, c+3)` の重みの和は 3。 -/
theorem wt_conj : ∀ c < 6, wt c + wt ((c + 3) % 6) = 3 := by decide

/-- `W_F` の CM 型 `Φ_W = {c : wt c = 2}`。 -/
def PhiW : List ℕ := (List.range 6).filter (fun c => decide (wt c = 2))

theorem PhiW_eq : PhiW = [0, 2, 4] := by decide

theorem PhiW_length : PhiW.length = 3 := by decide

/-- **誘導性**：`Φ_W` は `Z/6` の位数 3 の部分群 `⟨2⟩ = Gal(F/Q(√−19))` のコセットの和である
    （`+2` で閉じている）。ゆえに `W_F ≅ H¹(E)³`（`E` は `Q(√−19)` による CM 楕円曲線）。 -/
theorem PhiW_shift_closed : ∀ c ∈ PhiW, ((c + 2) % 6) ∈ PhiW := by decide

/-- 陰性対照：非退化な CM 型 `S' = {0,…,8}` でも level 1 になるが、
    その `Φ'` は `+2` で閉じない（＝ 二次部分体から誘導されない）。
    **level 1 であることと誘導であることは別**であり、`E` が現れる理由は誘導性の側にある。 -/
def Sl' : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8]

def inS' (k : ℕ) : Bool := Sl'.contains k

theorem Sl'_cm : ∀ k < 18, (inS' k = true) ↔ ¬ (inS' ((k + 9) % 18) = true) := by decide

def wt' (c : ℕ) : ℕ := ((List.range 18).filter (fun k => decide (k % 6 = c) && inS' k)).length

def PhiW' : List ℕ := (List.range 6).filter (fun c => decide (wt' c = 2))

theorem control_level_one' : ∀ c < 6, wt' c = 1 ∨ wt' c = 2 := by decide

theorem control_not_induced : ¬ (∀ c ∈ PhiW', ((c + 2) % 6) ∈ PhiW') := by decide

/-! ## 5. `E` 上の `μ_19` 作用は平行移動しかない -/

/-- 位数 19 の巡回群から位数 2 の群への（加法的な）準同型は自明。
    `End⁰(E) = Q(√−19)` の単数は `±1` なので、`μ_19 → Aut(E) = {±1}` は自明であり、
    `μ_19` は `E` に**平行移動**でしか作用しない。 -/
theorem hom_mu19_to_pm_trivial (f : ZMod 19 →+ ZMod 2) : ∀ x, f x = 0 := by
  intro x
  have hx : x = 10 * x + 10 * x := by
    have : (20 : ZMod 19) = 1 := by decide
    calc x = (20 : ZMod 19) * x := by rw [this]; ring
    _ = 10 * x + 10 * x := by ring
  calc f x = f (10 * x) + f (10 * x) := by rw [← map_add]; rw [← hx]
  _ = 0 := by
      have : ∀ a : ZMod 2, a + a = 0 := by decide
      exact this _

end CMHodge

#print axioms CMHodge.nef_pos_of_prod_ne_zero
#print axioms CMHodge.nef_pos_of_int_norm
#print axioms CMHodge.box_forces_norm_gt
#print axioms CMHodge.no_box_of_norm_le
#print axioms CMHodge.binom_sum_pos
#print axioms CMHodge.pinch_bounds
#print axioms CMHodge.perm_nonneg
#print axioms CMHodge.perm_pos
#print axioms CMHodge.Sl_cm
#print axioms CMHodge.Sl'_cm
#print axioms CMHodge.wt_values
#print axioms CMHodge.wt_level_one
#print axioms CMHodge.wt_conj
#print axioms CMHodge.PhiW_eq
#print axioms CMHodge.PhiW_length
#print axioms CMHodge.PhiW_shift_closed
#print axioms CMHodge.control_level_one'
#print axioms CMHodge.control_not_induced
#print axioms CMHodge.hom_mu19_to_pm_trivial
