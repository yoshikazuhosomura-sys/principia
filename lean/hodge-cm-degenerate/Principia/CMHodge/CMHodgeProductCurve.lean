/-
  余次元 2 のホッジ類：`A × E` の組合せ部分（Pohlmann の判定）

  `A` は `Q(ζ_19)` の退化かつ単純な CM 型による 9 次元 CM アーベル多様体、
  `E` は `Q(√−19)` による CM 楕円曲線（`Q(√−19) ⊂ Q(ζ_19)`）。
  `A × E` は CM 代数 `K = Q(ζ_19) × Q(√−19)`（次数 20）による CM アーベル多様体で、
  `Hom(K, C) = G ⊔ {e_0, e_1}`、`G = (Z/19)^* ≅ Z/18`（`γ = 2` の指数で座標を取る）。
  CM 型は `Φ = S ⊔ {e_0}`。Galois（＝`G` の平行移動）は `G` には平行移動で、
  `{e_0, e_1}` には `G/Q ≅ Z/2`（`Q` ＝ 平方剰余 ＝ 偶指数）を通して作用する。

  Pohlmann の判定（Milne, arXiv:2010.08857, 1.2(c) が Pohlmann 1968 Thm 1 として引く形）：
  `ω_Δ` がホッジ類 ⟺ `|(t∘Δ) ∩ Φ| = p` が全ての `t ∈ Gal` について成り立つ。

  このファイルは **組合せの言明だけ**を扱う。幾何・代数的サイクル・ホッジ予想は含まない。

  座標：`S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18` をビットマスク `SM` で表す。
  `bit SM (a + u) = 1 ⟺ a ∈ S − u` なので、`u` を全て走らせる条件は
  「全ての Galois 共役 `t∘Φ` について」と同値。`u = 0` の値がホッジ型を与える。
-/
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 2000000

namespace CMHodge

/-- `Z/18` の全体（18 ビットのマスク）。 -/
def mask : ℕ := 262143

/-- 代表 CM 型 `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18`。 -/
def SM : ℕ := 65919

/-- 平方剰余（偶指数）`Q = {0,2,4,…,16}`。 -/
def QRM : ℕ := 87381

/-- ビットの取り出し（添字は `mod 18`）。 -/
def bit (m i : ℕ) : ℕ := (m >>> (i % 18)) &&& 1

/-- `S` は CM 型：`S ⊔ (S + 9) = Z/18`。 -/
theorem SM_is_cm_type : ∀ i < 18, bit SM i + bit SM (i + 9) = 1 := by decide

/-- `S` の位数は 9。 -/
theorem SM_card : (((List.range 18).map (fun i => bit SM i)).sum) = 9 := by decide

/-- `S` の平行移動の安定化群は自明（＝`S` は原始的）。 -/
theorem SM_stab_trivial : ∀ u < 18, 0 < u → ∃ i < 18, bit SM i ≠ bit SM (i + u) := by decide

/-- `S` は平方剰余の剰余類ではない（`Q(√−19)` から誘導された型ではない）。 -/
theorem SM_ne_quadratic : ∀ u < 18, ∃ i < 18, bit SM (i + u) ≠ bit QRM i := by decide

/-! ### Pohlmann の許容性 -/

def c1 (a u : ℕ) : ℕ := bit SM (a + u)
def c2 (a b u : ℕ) : ℕ := bit SM (a + u) + bit SM (b + u)
def c3 (a b c u : ℕ) : ℕ := bit SM (a + u) + bit SM (b + u) + bit SM (c + u)
def c4 (a b c d u : ℕ) : ℕ := bit SM (a+u) + bit SM (b+u) + bit SM (c+u) + bit SM (d+u)

/-- `E` 側：`σ_u . e_i = e_{(i+u) mod 2}`、`Φ_E = {e_0}`。よって `e_i ∈ σ_u Φ_E ⟺ i = u mod 2`。 -/
def cE (e u : ℕ) : ℕ := if u % 2 = e then 1 else 0

/-- `H^4(A) ⊗ H^0(E)`：`|T_A| = 4`。 -/
def adm40 (a b c d : ℕ) : Bool := (List.range 18).all (fun u => c4 a b c d u == 2)
/-- `H^3(A) ⊗ H^1(E)`：`|T_A| = 3`、`E` 側は `e_i` 一つ。 -/
def adm31 (a b c e : ℕ) : Bool := (List.range 18).all (fun u => c3 a b c u + cE e u == 2)
/-- `H^2(A) ⊗ H^2(E)`：`|T_A| = 2`、`E` 側は `e_0 ∧ e_1`。 -/
def adm22 (a b : ℕ) : Bool := (List.range 18).all (fun u => c2 a b u + 1 == 2)
/-- `H^2(A) ⊗ H^0(E)`（`A` の因子）。 -/
def adm20 (a b : ℕ) : Bool := (List.range 18).all (fun u => c2 a b u == 1)
/-- `H^1(A) ⊗ H^1(E)`（混合の因子類）。 -/
def adm11 (a e : ℕ) : Bool := (List.range 18).all (fun u => c1 a u + cE e u == 1)

/-! ### 余次元 1（因子）-/

/-- `A` の因子類は `ρ` 対 `{a, a+9}` に限る（9 個）。 -/
theorem adm20_iff : ∀ a < 18, ∀ b < 18, a < b → (adm20 a b = true ↔ (a < 9 ∧ b = a + 9)) := by
  decide

/-- `H^1(A) ⊗ H^1(E)` にホッジ類は無い（`S` が平方剰余の剰余類でないことの帰結）。 -/
theorem adm11_none : ∀ a < 18, ∀ e < 2, adm11 a e = false := by decide

/-! ### 余次元 2 -/

/-- `H^4(A)` のホッジ類は `ρ` 対 2 個の合併に限る（＝因子の積、36 個）。 -/
def check40 : Bool :=
  (List.range 18).all (fun a => (List.range 18).all (fun b => (List.range 18).all (fun c =>
    (List.range 18).all (fun d =>
      (decide (a < b) && decide (b < c) && decide (c < d) && adm40 a b c d)
        == (decide (a < b) && decide (b < 9) && decide (c = a + 9) && decide (d = b + 9))))))

theorem adm40_iff : check40 = true := by decide

/-- `H^2(A) ⊗ H^2(E)` のホッジ類は `A` の因子 9 個に限る。 -/
theorem adm22_iff : ∀ a < 18, ∀ b < 18, a < b → (adm22 a b = true ↔ (a < 9 ∧ b = a + 9)) := by
  decide

/-- **主定理（組合せ部分）**：`H^3(A) ⊗ H^1(E)` のホッジ類はちょうど 6 個で、
`T_A` は位数 3 の部分群 `H = {0,6,12}` の剰余類 `C_k = {k, k+6, k+12}` に限り、
`E` 側の埋め込みは `k` のパリティで決まる（`k` 偶 ⟹ `e_1`、`k` 奇 ⟹ `e_0`）。 -/
theorem adm31_iff :
    ∀ a < 18, ∀ b < 18, ∀ c < 18, ∀ e < 2,
      (decide (a < b) && decide (b < c) && adm31 a b c e)
        = (decide (a < 6) && decide (b = a + 6) && decide (c = a + 12)
            && decide (e = (a + 1) % 2)) := by
  decide

/-- 6 個は因子の積では書けない（`T_A = C_k` は `ρ` 対の合併でない）。 -/
theorem coset_not_divisorial :
    ∀ a < 6, ¬ (a + 6 = a + 9 ∨ a + 12 = a + 9 ∨ a + 12 = (a + 6) + 9) := by decide

/-! ### 個数 -/

def sumR (n : ℕ) (f : ℕ → ℕ) : ℕ := ((List.range n).map f).sum

def count40 : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c => sumR 18 (fun d =>
  if a < b ∧ b < c ∧ c < d ∧ adm40 a b c d = true then 1 else 0))))
def count31 : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c => sumR 2 (fun e =>
  if a < b ∧ b < c ∧ adm31 a b c e = true then 1 else 0))))
def count22 : ℕ := sumR 18 (fun a => sumR 18 (fun b =>
  if a < b ∧ adm22 a b = true then 1 else 0))

theorem count31_eq : count31 = 6 := by decide
theorem count22_eq : count22 = 9 := by decide
theorem count40_eq : count40 = 36 := by decide

/-! ### `H^3(A)` の level ≤ 1 の部分 -/

/-- `ω_T`（`|T| = 3`）の型が全ての Galois 共役で `(2,1)` か `(1,2)` になる（level ≤ 1）。 -/
def lvl (a b c : ℕ) : Bool :=
  (List.range 18).all (fun u => 1 ≤ c3 a b c u && c3 a b c u ≤ 2)
/-- `T` が `ρ` 対を含む（＝ `ω_T` は因子と `H^1` の積）。 -/
def hasPair (a b c : ℕ) : Bool := (b == a + 9) || (c == a + 9) || (c == b + 9)
/-- `T` が `H = {0,6,12}` の剰余類（＝`W_F` の単項式）。 -/
def isCoset (a b c : ℕ) : Bool := (b == a + 6) && (c == a + 12) && (a < 6)

def countLvl : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c =>
  if a < b ∧ b < c ∧ lvl a b c = true then 1 else 0)))
def countLvlPair : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c =>
  if a < b ∧ b < c ∧ lvl a b c = true ∧ hasPair a b c = true then 1 else 0)))
def countLvlCoset : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c =>
  if a < b ∧ b < c ∧ lvl a b c = true ∧ isCoset a b c = true then 1 else 0)))
def countLvlRest : ℕ := sumR 18 (fun a => sumR 18 (fun b => sumR 18 (fun c =>
  if a < b ∧ b < c ∧ lvl a b c = true ∧ hasPair a b c = false ∧ isCoset a b c = false
  then 1 else 0)))

/-- `H^3(A)` の level ≤ 1 の最大有理部分ホッジ構造の次元は 204 で、
その内訳は 144（因子 ∪ `H^1`）＋ 6（`W_F`）＋ 54（残り 3 軌道）である。 -/
theorem level1_breakdown :
    countLvl = 204 ∧ countLvlPair = 144 ∧ countLvlCoset = 6 ∧ countLvlRest = 54 := by decide

/-! ### André–Deligne の分裂 Weil 類としての `ξ` -/

/-- `Δ_k = C_k ⊔ {e_{(k+1) mod 2}}` の 4 つの CM 型のうち `G` 側のもの：
`φ_u(t) = [t + u ∈ S]`（`A_u` は `A` の Galois 共役の CM 型）。 -/
def phiA (u t : ℕ) : ℕ := bit SM (t + u)
/-- `E` 側の CM 型（`Q(√−19)` から `Q(ζ_19)` へ誘導された非原始的な型）。 -/
def phiE (i t : ℕ) : ℕ := if t % 2 = i then 1 else 0

/-- Deligne（1982, §5）の分裂 Weil 型の条件：`Δ_k` の 4 つの CM 型の和は
全ての `t` で `p = 2` に等しい。すなわち `A_{Δ_k} = A_{k} × A_{k+6} × A_{k+12} × A_{e}`
（次元 36）は `F = Q(ζ_19)` に関して分裂 Weil 型である。 -/
theorem split_weil_condition :
    ∀ k < 6, ∀ t < 18,
      phiA k t + phiA (k + 6) t + phiA (k + 12) t + phiE ((k + 1) % 2) t = 2 := by decide

/-- **障害**：`Δ_k` の 4 つの CM 型は、どの 2 個を取っても互いに補型でない。
ゆえに `A_{Δ_k}` を `F` 安定な 2 つの Weil 型の因子に割って
分裂 Weil 類を「2 つの因子類の積」として書くことはできない。 -/
theorem no_complementary_pairing :
    ∀ k < 6, ∀ i < 3, ∀ j < 3,
      (¬ ∀ t < 18, phiA (k + 6 * i) t + phiA (k + 6 * j) t = 1) ∧
      (¬ ∀ t < 18, phiA (k + 6 * i) t + phiE ((k + 1) % 2) t = 1) := by decide

end CMHodge

#print axioms CMHodge.SM_is_cm_type
#print axioms CMHodge.SM_card
#print axioms CMHodge.SM_stab_trivial
#print axioms CMHodge.SM_ne_quadratic
#print axioms CMHodge.adm20_iff
#print axioms CMHodge.adm11_none
#print axioms CMHodge.adm40_iff
#print axioms CMHodge.adm22_iff
#print axioms CMHodge.adm31_iff
#print axioms CMHodge.coset_not_divisorial
#print axioms CMHodge.count31_eq
#print axioms CMHodge.count22_eq
#print axioms CMHodge.count40_eq
#print axioms CMHodge.level1_breakdown
#print axioms CMHodge.split_weil_condition
#print axioms CMHodge.no_complementary_pairing
