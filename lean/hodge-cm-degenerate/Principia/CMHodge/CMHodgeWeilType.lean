/-
  退化 CM 型の例外類を「Weil 型」に持ち上げる — 組合せの核

  `K = Q(ζ_19)`、`G = (Z/19)^* ≅ Z/18`（`γ = 2` の指数座標）、複素共役 `= +9`。
  `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18` は退化かつ原始的な CM 型、`A = A_S` は 9 次元単純。
  `F ⊂ K` は 6 次 CM 部分体（`Gal(K/F) = {0,6,12}`）。`F` の埋め込みは `Z/6`（`s mod 6`）、
  複素共役は `+3`、`F` の虚二次部分体の埋め込みはパリティで見る。

  ここで確かめるのは次の有限の事実だけである（幾何・代数的サイクル・ホッジ予想は含まない）：
  (1) `A` の `F` に関する署名は `(2,1,2,1,2,1)`。
  (2) `C` が `F` を CM 体とする 3 次元 CM アーベル多様体（CM 型 `Ψ ⊂ Z/6`）のとき、
      `A × C` が `F` について **Weil 型**（`H^{1,0}` が `F ⊗ C` 上自由 ⟺ 署名が全部 `d/2 = 2`）
      になるのは `Ψ = {1,3,5}` のときに限る（8 個の CM 型のうちただ 1 つ）。
  (3) その `Ψ` は位数 3 の部分群 `{0,2,4}` の剰余類（＝虚二次部分体から誘導された型）。
  (4) Pohlmann の判定で `H^3(A) ⊗ H^1(C)` の部分のホッジ類はちょうど 18 個、
      そのうち `F` 多重線形な 6 個（`∧^4_F`、`T = C_k ⊔ {k}`）はすべて許容で、
      共役の `F` 構造（`C_k ⊔ {k+3}`）はどれも許容でない。
  (5) 次元の下限：`d = 4` の Weil 型で `A` を因子に持つには `dim ≥ 12`。

  Pohlmann の判定（Milne, arXiv:2010.08857 の 1.2(c) が Pohlmann 1968 Thm 1 として引く形）：
  `ω_T` が有理ホッジ類の空間を張る ⟺ 全ての Galois 共役で `|T ∩ (Φ − u)| = p`。
-/
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 400

namespace CMHodge

/-- 代表 CM 型 `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18`（ビットマスク）。 -/
def SM : ℕ := 65919

/-- ビットの取り出し（添字は `mod 18`）。 -/
def bit (m i : ℕ) : ℕ := (m >>> (i % 18)) &&& 1

/-- 6 ビット版（`Z/6` の部分集合）。 -/
def bit6 (m i : ℕ) : ℕ := (m >>> (i % 6)) &&& 1

/-- `S` は CM 型。 -/
theorem SM_is_cm_type : ∀ i < 18, bit SM i + bit SM (i + 9) = 1 := by decide

/-! ### (1) `F` に関する署名 -/

/-- `n_k(A) = #{s ∈ S : s ≡ k (mod 6)}`。 -/
def nA (k : ℕ) : ℕ := ((List.range 18).map (fun i => if i % 6 = k % 6 then bit SM i else 0)).sum

theorem nA_values : (List.range 6).map nA = [2, 1, 2, 1, 2, 1] := by decide

/-- `A` 自身は `F` について Weil 型でない（署名が一定でない）。 -/
theorem nA_not_constant : ∃ k < 6, ∃ l < 6, nA k ≠ nA l := by decide

/-! ### (2) 第二因子の CM 型 -/

/-- `Ψ ⊂ Z/6` が `F` の CM 型：`Ψ ⊔ (Ψ + 3) = Z/6`。 -/
def isCMType6 (m : ℕ) : Bool := (List.range 6).all (fun i => bit6 m i + bit6 m (i + 3) == 1)

/-- `F` の CM 型はちょうど 8 個。 -/
theorem cm_types_six_card :
    ((List.range 64).filter (fun m => isCMType6 m)).length = 8 := by decide

/-- `A × C_Ψ`（`dim = 12`）の署名：`n_k = n_k(A) + [k ∈ Ψ]`。 -/
def nB (m k : ℕ) : ℕ := nA k + bit6 m k

/-- Weil 型条件：`H^{1,0}` が `F ⊗ C` 上自由 ⟺ 全ての `k` で `n_k = d/2 = 2`。 -/
def isWeilType (m : ℕ) : Bool := (List.range 6).all (fun k => nB m k == 2)

/-- **`A × C_Ψ` が `F` について Weil 型になる CM 型 `Ψ` はただ一つ、`Ψ = {1,3,5}`（マスク 42）**。 -/
theorem weil_type_unique :
    (List.range 64).filter (fun m => isCMType6 m && isWeilType m) = [42] := by decide

/-- 反対側の CM 型 `Ψ' = {0,2,4}`（マスク 21）では署名が `(3,1,3,1,3,1)`。 -/
theorem nB_21_values : (List.range 6).map (nB 21) = [3, 1, 3, 1, 3, 1] := by decide

/-- ただし Moonen–Zarhin の弱い条件 `n_k + n_{k+3} = d = 4` はどちらでも成り立つ。 -/
theorem nB_sum_four : ∀ m < 64, isCMType6 m = true → ∀ k < 6, nB m k + nB m (k + 3) = 4 := by
  decide

/-! ### (3) `Ψ = {1,3,5}` は虚二次部分体から誘導された型 -/

/-- `Ψ = {1,3,5}` は `+2` で閉じる（＝位数 3 の部分群 `{0,2,4}` の剰余類）。 -/
theorem psi_shift_closed : ∀ i < 6, bit6 42 i = bit6 42 (i + 2) := by decide

/-- 陰性対照：`+2` で閉じない CM 型も在る（たとえばマスク 7 = `{0,1,2}`）。 -/
theorem psi_control_not_closed : isCMType6 7 = true ∧ ∃ i < 6, bit6 7 i ≠ bit6 7 (i + 2) := by
  decide

/-! ### (4) Pohlmann の許容性（`H^3(A) ⊗ H^1(C)` の枡） -/

/-- `T = {a,b,c} ⊂ Z/18` と `j ∈ Z/6`。許容 ⟺ 全ての `u` で
`|T ∩ (S − u)| + [j + u ∈ Ψ] = 2`。 -/
def adm31F (m a b c j : ℕ) : Bool :=
  (List.range 18).all (fun u =>
    bit SM (a + u) + bit SM (b + u) + bit SM (c + u) + bit6 m (j + u) == 2)

def sumR (n : ℕ) (f : ℕ → ℕ) : ℕ := ((List.range n).map f).sum

def count31F (m : ℕ) : ℕ :=
  sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c => sumR 6 (fun j =>
    if a < b ∧ b < c ∧ adm31F m a b c j = true then 1 else 0))))

/-- `H^3(A) ⊗ H^1(C)` のホッジ類はちょうど **18** 個（`= 6 コセット × 3`）。 -/
theorem count31F_eq : count31F 42 = 18 := by decide

/-- 許容な枡の形：`T_A` は位数 3 の部分群の剰余類 `C_k`、`j` は `k` と同じパリティ。 -/
theorem adm31F_iff :
    ∀ a < 18, ∀ b < 18, ∀ c < 18, ∀ j < 6,
      (decide (a < b) && decide (b < c) && adm31F 42 a b c j)
        = (decide (a < 6) && decide (b = a + 6) && decide (c = a + 12)
            && decide (j % 2 = a % 2)) := by
  decide

/-- **`∧^4_F` の 6 個（`σ_k` 固有空間 `C_k ⊕ M_k`）はすべて許容**。 -/
theorem weil_monomials_adm : ∀ k < 6, adm31F 42 k (k + 6) (k + 12) k = true := by decide

/-- **共役の `F` 構造（`C_k ⊕ M_{k+3}`）はどれも許容でない**。 -/
theorem conj_weil_monomials_not_adm :
    ∀ k < 6, adm31F 42 k (k + 6) (k + 12) (k + 3) = false := by decide

/-- 陰性対照：Weil 型でない CM 型 `Ψ' = {0,2,4}` では `∧^4_F` の 6 個はどれも許容でない。 -/
theorem weil_monomials_not_adm_21 :
    ∀ k < 6, adm31F 21 k (k + 6) (k + 12) k = false := by decide

/-- 陰性対照（枡の総数は `F` 構造の取り方に依らない＝同じ多様体である）。 -/
theorem count31F_eq_21 : count31F 21 = 18 := by decide

/-! ### (5) 次元の下限 -/

/-- `d = 4` の Weil 型 `(Z, E')` に `A`（9 次元）が同種因子として入るなら
`dim Z = 2[E':Q]` で `[E':Q]` は偶数、ゆえに `dim Z ≥ 12`。 -/
theorem min_dim_twelve : ∀ m : ℕ, m % 2 = 0 → 9 ≤ 2 * m → 12 ≤ 2 * m := by
  intro m hm h; omega

#print axioms nA_values
#print axioms weil_type_unique
#print axioms nB_sum_four
#print axioms psi_shift_closed
#print axioms count31F_eq
#print axioms adm31F_iff
#print axioms weil_monomials_adm
#print axioms conj_weil_monomials_not_adm
#print axioms weil_monomials_not_adm_21
#print axioms min_dim_twelve

end CMHodge
