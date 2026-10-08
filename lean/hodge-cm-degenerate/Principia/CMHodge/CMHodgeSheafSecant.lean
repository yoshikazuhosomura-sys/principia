/-
  CM 型の退化した例外類 — 積偏極モデルの整数対称行列、`π` の消去、`W` の有理分解、
  そして「因子の上の直線束の直和」では作れないことの論理の芯（有限の代数だけ）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `F₀ = Q[θ]/(θ³+θ²−6θ−7)`（導手 19 の巡回 3 次体・`h = 1`・狭義類数 1）、`q ∈ Q_{>0}`。
  `B₂` は主偏極アーベル曲面、`X = B₂ ⊗_Z O_{F₀}`（6 次元）。逆異なり `𝔡^{-1}` の総正な生成元 `λ` を取ると
  跡形式 `Tr(λ x y)` は単模正定値になり、`O_{F₀}` の Z 基底を `Tr(λ v_a v_b) = δ_{ab}` に取れる。
  この基底で `X ≅ B₂³`・`Θ = pr₁^*θ₀ + pr₂^*θ₀ + pr₃^*θ₀`（積の主偏極）であり、
  `f ∈ O_{F₀}` の作用は整数**対称**行列 `M_f` で、`f·Θ` はその行列に対応する有理因子類である。
  実素点ごとの分解 `Θ = Θ₁+Θ₂+Θ₃` は `Θ_j³ = 0` を満たし、`W := Θ ∧_{F₀} Θ = Σ_j Θ_j²`、
  `π := Θ₁Θ₂Θ₃`。

  この頁で Lean にするのは次の六つで、いずれも**有限の代数の等式・不等式**である。
  幾何・層・変形理論・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 積偏極モデルの行列：`M = !![-1,1,0; 1,2,1; 0,1,-2]` は対称で、固有多項式が `θ³+θ²−6θ−7`。
      跡は `-1`（`= Tr_{F₀/Q}(θ)`）、行列式は `7`（`= N_{F₀/Q}(θ)`）。
  (2) 跡形式の格子：`T = !![1,-1,-2; -1,2,2; -2,2,5]` は行列式 1 で、`U = !![1,1,2; 0,1,0; 0,0,1]` により
      `Uᵀ T U = 1`（単模正定値 3 次格子は `Z³` に同型、の具体形）。
  (3) ニュートンの公式（3 変数）：`6xyz = p₁³ − 3p₁p₂ + 2p₃`。三乗が消えるときの系として
      `6π = Θ³ − 3ΘW`。すなわち `π` は `Θ` と `W` の多項式で書ける。
  (4) `W` の有理分解：跡形式に関して双対な二つの基底（行列 `A`・`B` が `A Bᵀ = 1`）に対して
      `Σ_a (Σ_j A_{ja}T_j)(Σ_k B_{ka}T_k) = Σ_j T_j²`。
  (5) 次数の尽くし：`i+j+k = 6`・`i,j,k ≤ 2` を満たす三つ組はちょうど `(2,2,2)` の一つで、
      その多項係数は `6!/(2!)³ = 90`（`χ(O_X(h·Θ)) = N_{F₀/Q}(h)²` の芯）。
  (6) モーメントの非負性：`ν ≥ 0` なら `Σ_l ν_l (Σ_a v_{la}w_a)² ≥ 0`、とくに `Σ_l ν_l N_l² ≥ 0`。
      ゆえに負の値（本稿の計算で出た `-200293/30`）には決してならない。
-/
import Mathlib

namespace CMHodgeSheafSecant

open Matrix Finset

/-! ### 1. 積偏極モデルの整数対称行列 -/

/-- `θ` の乗法行列（自己双対基底 `v = [1, θ+1, θ²−θ−3]` で）。 -/
def Mth : Matrix (Fin 3) (Fin 3) ℚ := !![(-1 : ℚ), 1, 0; 1, 2, 1; 0, 1, -2]

theorem mth_symm : Mthᵀ = Mth := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem mth_charpoly :
    Mth * Mth * Mth + Mth * Mth
      = (6 : ℚ) • Mth + (7 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mth, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> norm_num

theorem mth_trace : Mth.trace = -1 := by
  simp [Mth, Matrix.trace_fin_three]

theorem mth_det : Mth.det = 7 := by
  rw [Matrix.det_fin_three]; simp [Mth]; norm_num

/-! ### 2. 跡形式の格子は単模（`Z³` に同型） -/

/-- `Tr(λ z_a z_b)`（`z` は `O_{F₀}` の標準の整基底、`λ` は `𝔡^{-1}` の総正な生成元）。 -/
def Tg : Matrix (Fin 3) (Fin 3) ℚ := !![(1 : ℚ), -1, -2; -1, 2, 2; -2, 2, 5]
/-- 基底変換。 -/
def Ug : Matrix (Fin 3) (Fin 3) ℚ := !![(1 : ℚ), 1, 2; 0, 1, 0; 0, 0, 1]

theorem tg_det : Tg.det = 1 := by
  rw [Matrix.det_fin_three]; simp [Tg]; norm_num

theorem ug_det : Ug.det = 1 := by
  rw [Matrix.det_fin_three]; simp [Ug]

theorem gram_unimodular : Ugᵀ * Tg * Ug = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tg, Ug, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.transpose_apply] <;> norm_num

/-! ### 3. `π = (Θ³ − 3ΘW)/6` -/

variable {R : Type*} [CommRing R]

/-- 3 変数のニュートンの公式：`6e₃ = p₁³ − 3p₁p₂ + 2p₃`。 -/
theorem newton_e3 (x y z : R) :
    6 * (x * y * z)
      = (x + y + z) ^ 3 - 3 * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2)
        + 2 * (x ^ 3 + y ^ 3 + z ^ 3) := by
  ring

/-- 三乗が消えるとき（`Θ_j³ = 0`）：`6π = Θ³ − 3ΘW`。 -/
theorem pi_from_theta_W (x y z : R) (hx : x ^ 3 = 0) (hy : y ^ 3 = 0) (hz : z ^ 3 = 0) :
    6 * (x * y * z)
      = (x + y + z) ^ 3 - 3 * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [newton_e3, hx, hy, hz]; ring

/-! ### 4. `W` の有理分解（跡形式の双対基底） -/

/-- `A Bᵀ = 1` なら `Σ_a (A の第 a 列)·Θ × (B の第 a 列)·Θ = Σ_j Θ_j²`。 -/
theorem W_trace_dual (A B : Matrix (Fin 3) (Fin 3) R) (h : A * Bᵀ = 1) (T : Fin 3 → R) :
    (∑ a : Fin 3, (∑ j : Fin 3, A j a * T j) * (∑ k : Fin 3, B k a * T k))
      = ∑ j : Fin 3, T j ^ 2 := by
  have key : ∀ i j : Fin 3,
      A i 0 * B j 0 + A i 1 * B j 1 + A i 2 * B j 2 = if i = j then (1 : R) else 0 := by
    intro i j
    have hh := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, Fin.sum_univ_three]
      using hh
  have h00 : A 0 0 * B 0 0 + A 0 1 * B 0 1 + A 0 2 * B 0 2 = (1 : R) := by
    have hk := key 0 0; rw [if_pos rfl] at hk; exact hk
  have h11 : A 1 0 * B 1 0 + A 1 1 * B 1 1 + A 1 2 * B 1 2 = (1 : R) := by
    have hk := key 1 1; rw [if_pos rfl] at hk; exact hk
  have h22 : A 2 0 * B 2 0 + A 2 1 * B 2 1 + A 2 2 * B 2 2 = (1 : R) := by
    have hk := key 2 2; rw [if_pos rfl] at hk; exact hk
  have h01 : A 0 0 * B 1 0 + A 0 1 * B 1 1 + A 0 2 * B 1 2 = (0 : R) := by
    have hk := key 0 1; rw [if_neg (by decide)] at hk; exact hk
  have h02 : A 0 0 * B 2 0 + A 0 1 * B 2 1 + A 0 2 * B 2 2 = (0 : R) := by
    have hk := key 0 2; rw [if_neg (by decide)] at hk; exact hk
  have h10 : A 1 0 * B 0 0 + A 1 1 * B 0 1 + A 1 2 * B 0 2 = (0 : R) := by
    have hk := key 1 0; rw [if_neg (by decide)] at hk; exact hk
  have h12 : A 1 0 * B 2 0 + A 1 1 * B 2 1 + A 1 2 * B 2 2 = (0 : R) := by
    have hk := key 1 2; rw [if_neg (by decide)] at hk; exact hk
  have h20 : A 2 0 * B 0 0 + A 2 1 * B 0 1 + A 2 2 * B 0 2 = (0 : R) := by
    have hk := key 2 0; rw [if_neg (by decide)] at hk; exact hk
  have h21 : A 2 0 * B 1 0 + A 2 1 * B 1 1 + A 2 2 * B 1 2 = (0 : R) := by
    have hk := key 2 1; rw [if_neg (by decide)] at hk; exact hk
  simp only [Fin.sum_univ_three]
  linear_combination (T 0 * T 0) * h00 + (T 0 * T 1) * h01 + (T 0 * T 2) * h02
    + (T 1 * T 0) * h10 + (T 1 * T 1) * h11 + (T 1 * T 2) * h12
    + (T 2 * T 0) * h20 + (T 2 * T 1) * h21 + (T 2 * T 2) * h22

/-! ### 5. 最高次の単項式はただ一つ・多項係数は 90 -/

theorem only_deg_222 :
    (Finset.univ.filter
      (fun p : Fin 3 × Fin 3 × Fin 3 => (p.1 : ℕ) + (p.2.1 : ℕ) + (p.2.2 : ℕ) = 6))
      = {((2 : Fin 3), (2 : Fin 3), (2 : Fin 3))} := by decide

theorem multinomial_222 :
    Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 := by
  norm_num [Nat.factorial]

/-! ### 6. モーメントの非負性（「直和では作れない」の論理の芯） -/

theorem moment_nonneg {n : ℕ} (ν : Fin n → ℚ) (hν : ∀ l, 0 ≤ ν l)
    (v : Fin n → Fin 8 → ℚ) (w : Fin 8 → ℚ) :
    0 ≤ ∑ l : Fin n, ν l * (∑ a : Fin 8, v l a * w a) ^ 2 :=
  Finset.sum_nonneg fun l _ => mul_nonneg (hν l) (sq_nonneg _)

/-- `χ(O_X(h·Θ)) = N(h)²` と非負係数から `Σ_l ν_l N_l² ≥ 0`。
    本稿の計算値 `-200293/30`（`= ∫_X [Θ exp(−(q/2)W)/(e^Θ−1)]`）には決してならない。 -/
theorem split_sheaf_obstruction {n : ℕ} (ν : Fin n → ℚ) (hν : ∀ l, 0 ≤ ν l) (N : Fin n → ℚ) :
    (∑ l : Fin n, ν l * (N l) ^ 2) ≠ (-200293 : ℚ) / 30 := by
  intro hcon
  have h0 : (0 : ℚ) ≤ ∑ l : Fin n, ν l * (N l) ^ 2 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hν l) (sq_nonneg _)
  rw [hcon] at h0
  norm_num at h0

end CMHodgeSheafSecant

#print axioms CMHodgeSheafSecant.mth_symm
#print axioms CMHodgeSheafSecant.mth_charpoly
#print axioms CMHodgeSheafSecant.mth_trace
#print axioms CMHodgeSheafSecant.mth_det
#print axioms CMHodgeSheafSecant.tg_det
#print axioms CMHodgeSheafSecant.ug_det
#print axioms CMHodgeSheafSecant.gram_unimodular
#print axioms CMHodgeSheafSecant.newton_e3
#print axioms CMHodgeSheafSecant.pi_from_theta_W
#print axioms CMHodgeSheafSecant.W_trace_dual
#print axioms CMHodgeSheafSecant.only_deg_222
#print axioms CMHodgeSheafSecant.multinomial_222
#print axioms CMHodgeSheafSecant.moment_nonneg
#print axioms CMHodgeSheafSecant.split_sheaf_obstruction
