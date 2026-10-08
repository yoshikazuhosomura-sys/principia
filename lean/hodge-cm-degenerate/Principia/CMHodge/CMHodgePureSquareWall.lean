/-
  CM 型の退化した例外類 — 三重線型の還元と「純粋な平方だけ」の壁（2 進）

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、`W = Θ ∧_{F₀} Θ`
  （`F₀` は三次の総実体・`q = 19`）。`NS(X)⊗Q` は 3 次対称行列の 6 次元空間 `V` で、`D_S` が因子類。
  成分は `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）、要求は `Σ y_k [Z_k] = G₆`、
  `G₆ = (g³/24)Θ³ + (gq/2)ΘW`、`y_k ≥ 0` かつ `y_k ∈ ℤ`。

  この頁で Lean にするのは次の二つの束で、いずれも**有限の代数の等式・不等式**である。
  幾何・層・コホモロジー・Chern 指標・代数的サイクル・ホッジ予想は一切含まない。代数性は何も主張しない。

  (A) 三重線型の還元。交点数 `μ(S₁,S₂,S₃) = [D_{S₁}D_{S₂}D_{S₃}]` は各引数について線型で
      第 2・第 3 引数について対称だから、`S₃ = gI - S₁ - S₂` を入れると
        `μ(S₁,S₂,gI-S₁-S₂) = g·μ(S₁,S₂,I) - μ(S₁,S₁,S₂) - μ(S₁,S₂,S₂)`
      であり、`S₁ = a·u`・`S₂ = b·v`（`u = uu^T`・`v = vv^T` は階数 1 の類）なら
        `μ = (abg)·μ(u,v,I) - (a²b)·μ(u,u,v) - (ab²)·μ(u,v,v)`
      になる。さらに `μ(u,u,u) = 0` のとき（`u` が階数 1 なら `Θ_u = f_u^*θ₀`・`θ₀³ ∈ H⁶(B₂) = 0`
      だからこれが成り立つ）、`v = u` の場合は補正項が消えて
        `μ(a·u, b·u, gI - a·u - b·u) = (abg)·μ(u,u,I)`
      になる。

  (B) 「純粋な平方だけ」の壁（2 進）。`W` の四次形式 `w` は `19·w` が整係数で、
      その `x⁴` の係数は 15（奇数）である。`u = v` の原子だけを使うと、要求は
        `Σ_u m_u · (u·x)⁴ = (19/2)·w(x)`（`m_u ≥ 0` は整数）
      に帰着する。`x⁴` の係数を見ると `Σ_u m_u · u₁⁴ = 15/2` が必要になるが、
      左辺は整数だからこれは不可能である。同じことを整数に直すと
      `Σ_u n_u u₁⁴ = 15`（奇数）なので `n_u` をすべて偶数に取ることもできない。
-/
import Mathlib

namespace CMHodgePureSquareWall

/-! ### (A) 三重線型の還元 -/

section Trilinear

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- 第 3 引数の線型性だけを使った展開。 -/
theorem expand_third (mu : V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] W) (g : ℚ) (Id S₁ S₂ : V) :
    mu S₁ S₂ (g • Id - S₁ - S₂) = g • mu S₁ S₂ Id - mu S₁ S₂ S₁ - mu S₁ S₂ S₂ := by
  simp [map_sub, map_smul]

/-- 第 2・第 3 引数の対称性を使った還元。`S₃ = gI - S₁ - S₂` のとき
`μ(S₁,S₂,S₃) = g·μ(S₁,S₂,I) - μ(S₁,S₁,S₂) - μ(S₁,S₂,S₂)`。 -/
theorem trilinear_reduction (mu : V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] W)
    (hsym : ∀ x y z : V, mu x y z = mu x z y) (g : ℚ) (Id S₁ S₂ : V) :
    mu S₁ S₂ (g • Id - S₁ - S₂) = g • mu S₁ S₂ Id - mu S₁ S₁ S₂ - mu S₁ S₂ S₂ := by
  rw [expand_third mu g Id S₁ S₂, hsym S₁ S₂ S₁]

/-- 階数 1 の二つを使った原子の閉じた式。 -/
theorem rank_one_atom (mu : V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] W)
    (hsym : ∀ x y z : V, mu x y z = mu x z y) (g a b : ℚ) (Id u v : V) :
    mu (a • u) (b • v) (g • Id - a • u - b • v)
      = (a * b * g) • mu u v Id - (a * a * b) • mu u u v - (a * b * b) • mu u v v := by
  rw [trilinear_reduction mu hsym g Id (a • u) (b • v)]
  simp [map_smul, smul_smul]
  ring_nf

/-- `μ(u,u,u) = 0` なら、`v = u` の原子は補正項を持たない。 -/
theorem diagonal_atom (mu : V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] W)
    (hsym : ∀ x y z : V, mu x y z = mu x z y) (g a b : ℚ) (Id u : V)
    (hu : mu u u u = 0) :
    mu (a • u) (b • u) (g • Id - a • u - b • u) = (a * b * g) • mu u u Id := by
  rw [rank_one_atom mu hsym g a b Id u u, hu]
  simp

end Trilinear

/-! ### (B) 「純粋な平方だけ」の壁（2 進） -/

/-- 整数の 4 乗の非負整数結合を 2 倍しても 15 にはならない（左辺は偶数・右辺は奇数）。 -/
theorem two_mul_sum_ne_fifteen (n : ℕ) (m : Fin n → ℕ) (w : Fin n → ℤ) :
    2 * ∑ i, (m i : ℤ) * (w i) ^ 4 ≠ 15 := by
  intro h
  have h2 : (2 : ℤ) ∣ 15 := ⟨∑ i, (m i : ℤ) * (w i) ^ 4, h.symm⟩
  norm_num at h2

/-- 重複度をすべて偶数に取ることはできない（`Σ n_u u₁⁴ = 15` は奇数）。 -/
theorem no_all_even_multiplicities (n : ℕ) (k : Fin n → ℕ) (w : Fin n → ℤ) :
    ∑ i, ((2 * k i : ℕ) : ℤ) * (w i) ^ 4 ≠ 15 := by
  intro h
  refine two_mul_sum_ne_fifteen n k w ?_
  rw [Finset.mul_sum]
  simpa [mul_assoc, Nat.cast_mul] using h

/-- `x⁴` の係数の要求 `Σ m_u u₁⁴ = 15/2` は、整数の重複度では満たせない。
これが「`u = v` の原子（補正項なし）だけでは表示が取れない」ことの 2 進の理由である。 -/
theorem pure_square_wall (n : ℕ) (m : Fin n → ℕ) (w : Fin n → ℤ) :
    ∑ i, (m i : ℚ) * ((w i : ℚ)) ^ 4 ≠ 15 / 2 := by
  intro h
  have h2 : (2 : ℚ) * ∑ i, (m i : ℚ) * ((w i : ℚ)) ^ 4 = 15 := by
    rw [h]; ring
  have hcast : ((2 * ∑ i, (m i : ℤ) * (w i) ^ 4 : ℤ) : ℚ) = 15 := by
    push_cast
    simpa using h2
  have := two_mul_sum_ne_fifteen n m w
  exact this (by exact_mod_cast hcast)

/-- 同じ壁を「`19w` の `x⁴` の係数は 15」という形で書いたもの：
整数の非負重複度で `Σ n_u u₁⁴ = 15` を満たしても、その半分 `m_u = n_u/2` が整数にはならない。 -/
theorem half_not_integral (n : ℕ) (m : Fin n → ℕ) (w : Fin n → ℤ)
    (h : ∑ i, ((2 * m i : ℕ) : ℤ) * (w i) ^ 4 = 15) : False :=
  no_all_even_multiplicities n m w h

#print axioms CMHodgePureSquareWall.expand_third
#print axioms CMHodgePureSquareWall.trilinear_reduction
#print axioms CMHodgePureSquareWall.rank_one_atom
#print axioms CMHodgePureSquareWall.diagonal_atom
#print axioms CMHodgePureSquareWall.two_mul_sum_ne_fifteen
#print axioms CMHodgePureSquareWall.no_all_even_multiplicities
#print axioms CMHodgePureSquareWall.pure_square_wall
#print axioms CMHodgePureSquareWall.half_not_integral

end CMHodgePureSquareWall
