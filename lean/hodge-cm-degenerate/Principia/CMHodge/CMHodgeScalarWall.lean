/-
  CM 型の退化した例外類 — 共有因子がスカラーのときの壁（階数 1 の Farkas 証明書）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、`W = Θ ∧_{F₀} Θ`
  （`F₀` は三次の総実体・`q = 19`）。`NS(X)⊗Q` は 3 次対称行列の 6 次元空間 `V` で、`D_S` が因子類。
  成分は `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）、要求は `Σ y_k [Z_k] = G₆`、
  `G₆ = (g³/24)Θ³ + (gq/2)ΘW`、`y_k ≥ 0`。

  共有因子がスカラー（`S₁ = aI`・`a ≥ 0`）のとき `D_{S₁} = aΘ` なので
  `[Z_k] = a(g-a)² · Θ·D_T·D_{I-T}`（`T := S₂/(g-a)`）である。

  この頁で Lean にするのは次の五つで、いずれも**有限の代数の等式・不等式**である。
  幾何・層・コホモロジー・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (1) 線型汎関数 `φ(A) = -A₀₀ + 2A₁₁ - A₂₂` は `φ(I) = 0` を満たす。
  (2) `ψ(Θ D_A D_B) := -φ(A)φ(B)` と置くと `ψ(Θ D_T D_{I-T}) = φ(T)²`（すべての対称 `T` で非負）。
  (3) `ψ(Θ³) = -φ(I)² = 0`。
  (4) `ψ(ΘW) = -Σ_{a=1}^{3} φ(P_a)φ(R_a) = -78/19 < 0`（`P_a`・`R_a` は `W` の三つの因子の対）。
  (5) ゆえに `ψ(G₆) = -39g < 0` である一方、右辺 `Σ y_k ψ([Z_k])` は非負の和。矛盾する。
      ⇒ 共有因子がスカラーなら、`g > 0` と `ε = 12q/g² > 0` の取り方に依らず表示は存在しない。
-/
import Mathlib

namespace CMHodgeScalarWall

/-! ### (1) 証明書 `φ` と `φ(I) = 0` -/

/-- 3 次対称行列を 6 座標 `(A₀₀, A₁₁, A₂₂, A₀₁, A₀₂, A₁₂)` で表したときの証明書の汎関数。 -/
def phi (a b c d e f : ℚ) : ℚ := -a + 2 * b - c

theorem phi_I : phi 1 1 1 0 0 0 = 0 := by norm_num [phi]

theorem phi_add (a b c d e f a' b' c' d' e' f' : ℚ) :
    phi (a + a') (b + b') (c + c') (d + d') (e + e') (f + f')
      = phi a b c d e f + phi a' b' c' d' e' f' := by
  simp [phi]; ring

/-! ### (2) 原子の上での値は平方である -/

/-- `I - T` の 6 座標は `(1-t₁, 1-t₂, 1-t₃, -t₄, -t₅, -t₆)`。
    `ψ(Θ D_T D_{I-T}) = -φ(T)·φ(I-T) = φ(T)²`。 -/
theorem psi_atom_is_square (t₁ t₂ t₃ t₄ t₅ t₆ : ℚ) :
    -(phi t₁ t₂ t₃ t₄ t₅ t₆) * (phi (1 - t₁) (1 - t₂) (1 - t₃) (-t₄) (-t₅) (-t₆))
      = (phi t₁ t₂ t₃ t₄ t₅ t₆) ^ 2 := by
  simp [phi]; ring

/-- 成分の値：`ψ([Z_k]) = a(g-a)²·φ(T)² ≥ 0`（`a ≥ 0`）。 -/
theorem psi_component_nonneg (a g t₁ t₂ t₃ t₄ t₅ t₆ : ℚ) (ha : 0 ≤ a) :
    0 ≤ a * (g - a) ^ 2 * (phi t₁ t₂ t₃ t₄ t₅ t₆) ^ 2 := by
  have h1 : (0:ℚ) ≤ (g - a) ^ 2 := sq_nonneg _
  have h2 : (0:ℚ) ≤ (phi t₁ t₂ t₃ t₄ t₅ t₆) ^ 2 := sq_nonneg _
  have := mul_nonneg ha h1
  exact mul_nonneg this h2

/-! ### (3)(4) 目標の上での値 -/

theorem psi_theta_cubed : -(phi 1 1 1 0 0 0) * (phi 1 1 1 0 0 0) = 0 := by norm_num [phi]

/-- `W` の三つの対 `(P_a, R_a)`（`P_a` は整数、`R_a` は分母 19）。 -/
def P1 : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ := (1, 1, 1, 0, 0, 0)
def P2 : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ := (0, 3, -1, 1, 0, 1)
def P3 : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ := (0, 1, 4, 0, 1, -1)

theorem phi_P_values :
    phi 1 1 1 0 0 0 = 0 ∧ phi 0 3 (-1) 1 0 1 = 7 ∧ phi 0 1 4 0 1 (-1) = -2 := by
  refine ⟨by norm_num [phi], by norm_num [phi], by norm_num [phi]⟩

theorem phi_R_values :
    phi (15/19) (2/19) (2/19) (-3/19) (-4/19) (1/19) = -13/19 ∧
    phi (-3/19) (4/19) (-1/19) (2/19) (1/19) (1/19) = 12/19 ∧
    phi (-4/19) (1/19) (3/19) (1/19) (2/19) (-1/19) = 3/19 := by
  refine ⟨by norm_num [phi], by norm_num [phi], by norm_num [phi]⟩

/-- `ψ(ΘW) = -Σ_a φ(P_a)φ(R_a) = -78/19 < 0`。 -/
theorem psi_thetaW : -((0:ℚ) * (-13/19) + 7 * (12/19) + (-2) * (3/19)) = -78/19 := by norm_num

theorem psi_thetaW_neg : (-78/19 : ℚ) < 0 := by norm_num

/-- `ψ(G₆) = (g³/24)·ψ(Θ³) + (g·19/2)·ψ(ΘW) = -39g`。 -/
theorem psi_G6 (g : ℚ) : (g ^ 3 / 24) * 0 + (g * 19 / 2) * (-78/19) = -39 * g := by ring

/-! ### (5) 壁 -/

/-- 共有因子がスカラーの成分だけからなる非負の和は、`ψ` の値が `-39g`（`g > 0`）になれない。
    `y k` は重複度、`a k` は共有因子のスカラー、`t k` は `φ(T_k)`。 -/
theorem scalar_shared_wall (g : ℚ) (hg : 0 < g) (n : ℕ) (y a t : Fin n → ℚ)
    (hy : ∀ k, 0 ≤ y k) (ha : ∀ k, 0 ≤ a k) :
    (∑ k : Fin n, y k * (a k * (g - a k) ^ 2 * (t k) ^ 2)) ≠ -39 * g := by
  have hsum : 0 ≤ ∑ k : Fin n, y k * (a k * (g - a k) ^ 2 * (t k) ^ 2) := by
    refine Finset.sum_nonneg ?_
    intro k _
    exact mul_nonneg (hy k)
      (mul_nonneg (mul_nonneg (ha k) (sq_nonneg _)) (sq_nonneg _))
  have hneg : -39 * g < 0 := by nlinarith
  intro h
  rw [h] at hsum
  exact absurd hsum (not_le.mpr hneg)

/-- Farkas の形（この頁で使った論法そのもの）：生成元で非負・目標で負なら、目標は錐に入らない。 -/
theorem not_in_cone_of_functional (n : ℕ) (y v : Fin n → ℚ) (target : ℚ)
    (hy : ∀ k, 0 ≤ y k) (hv : ∀ k, 0 ≤ v k) (ht : target < 0) :
    (∑ k : Fin n, y k * v k) ≠ target := by
  have hsum : 0 ≤ ∑ k : Fin n, y k * v k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hy k) (hv k))
  intro h
  rw [h] at hsum
  exact absurd hsum (not_le.mpr ht)

#print axioms CMHodgeScalarWall.phi_I
#print axioms CMHodgeScalarWall.phi_add
#print axioms CMHodgeScalarWall.psi_atom_is_square
#print axioms CMHodgeScalarWall.psi_component_nonneg
#print axioms CMHodgeScalarWall.psi_theta_cubed
#print axioms CMHodgeScalarWall.phi_P_values
#print axioms CMHodgeScalarWall.phi_R_values
#print axioms CMHodgeScalarWall.psi_thetaW
#print axioms CMHodgeScalarWall.psi_thetaW_neg
#print axioms CMHodgeScalarWall.psi_G6
#print axioms CMHodgeScalarWall.scalar_shared_wall
#print axioms CMHodgeScalarWall.not_in_cone_of_functional

end CMHodgeScalarWall
