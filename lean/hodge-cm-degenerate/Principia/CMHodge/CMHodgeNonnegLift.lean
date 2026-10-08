/-
  CM 型の退化した例外類 — 非負整数解の持ち上げ補題と、奇単項の「4 対 2」

  設定（幾何は Lean に入れない。以下は記号の由来の説明である）：
  `B₂` は一般な主偏極アーベル曲面、`X = B₂³`（6 次元）、`Θ` は積の主偏極、
  `W = Θ ∧_{F₀} Θ`（`F₀` は三次の総実体・`q = 19`）。成分は
  `Z_k = D_{S₁}∩D_{S₂}∩D_{S₃}`（`ΣSᵢ = gI`・`Sᵢ ⪰ 0`）で、要求は
  `Σ y_k [Z_k] = G₆ = (g³/24)Θ³ + (gq/2)ΘW`、`y_k ≥ 0` かつ `y_k ∈ ℤ` である。

  この頁で Lean にするのは次の二つだけである。

  (A) 持ち上げ補題。整数係数の線型系 `A y = b` に整数解 `y` があり、かつ
      `A w = 0` かつ `w ≥ 1`（すべての座標で）を満たす整数ベクトル `w` があれば、
      `z := y + t·w`（`t := Σ_j max 0 (-y_j)`）は **非負整数解**である。
      ⇒ 「非負整数解が在るか」は「格子に入るか」と「核の中に狭義正のベクトルが在るか」に分かれる。
      後者は線型計画一本で決まる（整数計画を解く必要がない）。

  (B) 奇単項の「4 対 2」。`μ(I,·) : Sym²V → H⁶` の像の元は三変数の四次形式で表され、
      因子の対 `(u,v)` の作る `M21` の元は `(u·x)²(v·x)²` に対応する。その `x³y` の係数は
      `pairCoeff u₁ u₂ v₁ v₂ = 2·u₁v₁(u₁v₂ + u₂v₁)` である。
      これは常に 2 の倍数で、`u = v` のときだけ `4u₁³u₂` となって 4 の倍数になる。
      目標の側の対応する量は `-6`（`-6g` の `g` の一次の係数）で、
      `2 ∣ -6` だが `4 ∤ -6` である。ゆえに
      「`u = v` の因子（あるいは符号変換で不変な組み合わせ）だけでは届かないが、
        `u ≠ v` の因子の対は一つで届く」。
      届く最小の例は `u = (1,0,0)`・`v = (1,1,0)` で、そこでは係数が `2` である。
-/
import Mathlib

namespace CMHodgeNonnegLift

open Finset

/-! ### (A) 持ち上げ補題 -/

/-- **持ち上げ補題**。整数解 `y` と、核の中の狭義正のベクトル `w`（`w_j ≥ 1`）があれば、
非負整数解が在る。`t := Σ_j max 0 (-y_j)` と置けばよい。 -/
theorem nonneg_lift {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (y w : Fin n → ℤ)
    (hy : ∀ i, ∑ j, A i j * y j = b i)
    (hw : ∀ i, ∑ j, A i j * w j = 0)
    (hw1 : ∀ j, 1 ≤ w j) :
    ∃ z : Fin n → ℤ, (∀ i, ∑ j, A i j * z j = b i) ∧ ∀ j, 0 ≤ z j := by
  classical
  set t : ℤ := ∑ j, max 0 (-y j) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg (fun j _ => le_max_left _ _)
  have htj : ∀ j, -y j ≤ t := by
    intro j
    have h1 : max 0 (-y j) ≤ t := by
      rw [ht]
      exact Finset.single_le_sum (f := fun k => max 0 (-y k))
        (fun k _ => le_max_left _ _) (Finset.mem_univ j)
    exact le_trans (le_max_right _ _) h1
  refine ⟨fun j => y j + t * w j, ?_, ?_⟩
  · intro i
    have e1 : ∀ j : Fin n, A i j * (y j + t * w j) = A i j * y j + t * (A i j * w j) := by
      intro j; ring
    calc ∑ j, A i j * (y j + t * w j)
        = ∑ j, (A i j * y j + t * (A i j * w j)) := Finset.sum_congr rfl (fun j _ => e1 j)
      _ = (∑ j, A i j * y j) + ∑ j, t * (A i j * w j) := Finset.sum_add_distrib
      _ = (∑ j, A i j * y j) + t * ∑ j, A i j * w j := by rw [Finset.mul_sum]
      _ = b i := by rw [hy i, hw i]; ring
  · intro j
    have h1 : t * 1 ≤ t * w j := mul_le_mul_of_nonneg_left (hw1 j) ht0
    have h2 : -y j ≤ t := htj j
    have : t ≤ t * w j := by linarith [h1]
    linarith

/-- 持ち上げに使う `t` は具体的に取れる（上の証明の中身を外に出した形）。 -/
theorem nonneg_lift_explicit {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (y w : Fin n → ℤ)
    (hy : ∀ i, ∑ j, A i j * y j = b i)
    (hw : ∀ i, ∑ j, A i j * w j = 0)
    (hw1 : ∀ j, 1 ≤ w j) :
    ∃ t : ℤ, 0 ≤ t ∧ (∀ i, ∑ j, A i j * (y j + t * w j) = b i) ∧ ∀ j, 0 ≤ y j + t * w j := by
  classical
  refine ⟨∑ j, max 0 (-y j), Finset.sum_nonneg (fun j _ => le_max_left _ _), ?_, ?_⟩
  · intro i
    have e1 : ∀ j : Fin n, A i j * (y j + (∑ k, max 0 (-y k)) * w j)
        = A i j * y j + (∑ k, max 0 (-y k)) * (A i j * w j) := by intro j; ring
    calc ∑ j, A i j * (y j + (∑ k, max 0 (-y k)) * w j)
        = ∑ j, (A i j * y j + (∑ k, max 0 (-y k)) * (A i j * w j)) :=
          Finset.sum_congr rfl (fun j _ => e1 j)
      _ = (∑ j, A i j * y j) + ∑ j, (∑ k, max 0 (-y k)) * (A i j * w j) := Finset.sum_add_distrib
      _ = (∑ j, A i j * y j) + (∑ k, max 0 (-y k)) * ∑ j, A i j * w j := by rw [Finset.mul_sum]
      _ = b i := by rw [hy i, hw i]; ring
  · intro j
    have ht0 : 0 ≤ ∑ k, max 0 (-y k) := Finset.sum_nonneg (fun k _ => le_max_left _ _)
    have h1 : max 0 (-y j) ≤ ∑ k, max 0 (-y k) :=
      Finset.single_le_sum (f := fun k => max 0 (-y k)) (fun k _ => le_max_left _ _)
        (Finset.mem_univ j)
    have h2 : -y j ≤ ∑ k, max 0 (-y k) := le_trans (le_max_right _ _) h1
    have h3 : (∑ k, max 0 (-y k)) * 1 ≤ (∑ k, max 0 (-y k)) * w j :=
      mul_le_mul_of_nonneg_left (hw1 j) ht0
    linarith

/-! ### (B) 奇単項の「4 対 2」 -/

/-- `(u·x)²(v·x)²` の `x³y` の係数。 -/
def pairCoeff (u₁ u₂ v₁ v₂ : ℤ) : ℤ := 2 * (u₁ * v₁ * (u₁ * v₂ + u₂ * v₁))

theorem two_dvd_pairCoeff (u₁ u₂ v₁ v₂ : ℤ) : (2:ℤ) ∣ pairCoeff u₁ u₂ v₁ v₂ :=
  ⟨u₁ * v₁ * (u₁ * v₂ + u₂ * v₁), rfl⟩

theorem pairCoeff_diag (u₁ u₂ : ℤ) : pairCoeff u₁ u₂ u₁ u₂ = 4 * u₁ ^ 3 * u₂ := by
  unfold pairCoeff; ring

theorem four_dvd_pairCoeff_diag (u₁ u₂ : ℤ) : (4:ℤ) ∣ pairCoeff u₁ u₂ u₁ u₂ := by
  rw [pairCoeff_diag]; exact ⟨u₁ ^ 3 * u₂, by ring⟩

theorem pairCoeff_example : pairCoeff 1 0 1 1 = 2 := by unfold pairCoeff; norm_num

theorem not_four_dvd_two : ¬ (4:ℤ) ∣ 2 := by decide

/-- `u ≠ v` の対は一つで mod 4 の壁を破る。 -/
theorem distinct_pair_breaks_mod_four :
    ∃ u₁ u₂ v₁ v₂ : ℤ, ¬ (4:ℤ) ∣ pairCoeff u₁ u₂ v₁ v₂ := by
  refine ⟨1, 0, 1, 1, ?_⟩
  rw [pairCoeff_example]; exact not_four_dvd_two

/-- 対の係数の全体が生む `ℤ` の部分群はちょうど `2ℤ` である（割り切れること＋到達すること）。 -/
theorem pairCoeff_generates_two :
    (∀ u₁ u₂ v₁ v₂ : ℤ, (2:ℤ) ∣ pairCoeff u₁ u₂ v₁ v₂) ∧
    (∃ u₁ u₂ v₁ v₂ : ℤ, pairCoeff u₁ u₂ v₁ v₂ = 2) :=
  ⟨two_dvd_pairCoeff, ⟨1, 0, 1, 1, pairCoeff_example⟩⟩

/-- 目標の側の量 `-6` は `2ℤ` に入るが `4ℤ` には入らない。 -/
theorem target_two_not_four : (2:ℤ) ∣ (-6) ∧ ¬ (4:ℤ) ∣ (-6) := by
  refine ⟨⟨-3, by norm_num⟩, ?_⟩; decide

/-- 「4 対 2」のまとめ：`u = v` の因子（と符号変換で不変な組み合わせ）だけでは目標の
`x³y` 成分に届かないが、`u ≠ v` の対を許せば届く。 -/
theorem four_versus_two :
    (¬ ∃ k : ℤ, 4 * k = -6) ∧ (∃ k : ℤ, 2 * k = -6) := by
  refine ⟨?_, ⟨-3, by norm_num⟩⟩
  intro h
  obtain ⟨k, hk⟩ := h
  omega

end CMHodgeNonnegLift

#print axioms CMHodgeNonnegLift.nonneg_lift
#print axioms CMHodgeNonnegLift.nonneg_lift_explicit
#print axioms CMHodgeNonnegLift.two_dvd_pairCoeff
#print axioms CMHodgeNonnegLift.pairCoeff_diag
#print axioms CMHodgeNonnegLift.four_dvd_pairCoeff_diag
#print axioms CMHodgeNonnegLift.pairCoeff_example
#print axioms CMHodgeNonnegLift.distinct_pair_breaks_mod_four
#print axioms CMHodgeNonnegLift.pairCoeff_generates_two
#print axioms CMHodgeNonnegLift.target_two_not_four
#print axioms CMHodgeNonnegLift.four_versus_two
