/-
  CM アーベル多様体 `A = C^9 / Φ_S(O_K)`（`K = Q(ζ_19)`、`S` は退化かつ原始的な CM 型）の
  上で「非有理特異点を持つ因子」を作る試みの、**有限の部分**だけをここに置く。

  幾何については何も主張していない。交点数・有効性・Grothendieck–Lefschetz は
  ここには入っていない。入っているのは、それらを使った議論が最後に落ちる
  次の 5 つの有限の事実である。

  (1) 正値の核：`p k > 0`、`c k ≥ 0`、`Σ c k p k ≤ 0` なら `c k = 0`。
  (2) 重複度の核：`P - 3 p k ≥ 0`（k = 0,1,2）かつ `Σ p k - P ≥ 0` なら
      `P = 3 p 0 = 3 p 1 = 3 p 2` かつ `Σ p k = P`。
      （`p k` は `y_k · a^5 · y_0y_1y_2`、`P` は `y · a^5 · y_0y_1y_2` に当たる。）
  (3) 三つ組と四つ組：`x : Fin 9 → ℝ` が「どの 3 個の和も ≥ 0」「どの 4 個の和も ≤ 0」
      を満たせば `x = 0`。（三つの因子が同じ類のときの、退化した形の同じ結論。）
  (4) 符号ベクトル：指数 `s(v) = #{j : v j < 0}` は成分ごとの増加で減らない。
      そこから来る錐の議論（`y - 3 y_k` が全成分非負なら `Σ y_k - y` は 0）。
  (5) `ZMod 19` / `ℕ` の勘定：CM 型 `S~ = {1,2,4,5,7,8,9,13,16}` は
      三点分岐の巡回 19 次被覆 `w^19 = x^a (1-x)^b` の Jacobian の CM 型のどれとも異なる。
-/
import Mathlib

namespace CMHodge

/-! ## 1. 正値の核 -/

/-- `p k > 0`、`c k ≥ 0`、`Σ_k c k * p k ≤ 0` なら、すべての `c k` が `0`。 -/
theorem coeff_zero_of_sum_nonpos (c p : Fin 3 → ℝ)
    (hp : ∀ k, 0 < p k) (hc : ∀ k, 0 ≤ c k)
    (h : c 0 * p 0 + c 1 * p 1 + c 2 * p 2 ≤ 0) : ∀ k, c k = 0 := by
  have n0 : 0 ≤ c 0 * p 0 := mul_nonneg (hc 0) (hp 0).le
  have n1 : 0 ≤ c 1 * p 1 := mul_nonneg (hc 1) (hp 1).le
  have n2 : 0 ≤ c 2 * p 2 := mul_nonneg (hc 2) (hp 2).le
  have e0 : c 0 * p 0 = 0 := by linarith
  have e1 : c 1 * p 1 = 0 := by linarith
  have e2 : c 2 * p 2 = 0 := by linarith
  intro k
  fin_cases k
  · exact (mul_eq_zero.1 e0).resolve_right (ne_of_gt (hp 0))
  · exact (mul_eq_zero.1 e1).resolve_right (ne_of_gt (hp 1))
  · exact (mul_eq_zero.1 e2).resolve_right (ne_of_gt (hp 2))

/-- 重複度 3 の核。
`P - 3 * p k ≥ 0`（`k = 0,1,2`）と `p 0 + p 1 + p 2 - P ≥ 0` が同時に立てば、
四つの不等式はすべて等号である。 -/
theorem defect_core (p : Fin 3 → ℝ) (P : ℝ)
    (hmult : ∀ k, 0 ≤ P - 3 * p k)
    (hdef : 0 ≤ p 0 + p 1 + p 2 - P) :
    P = 3 * p 0 ∧ P = 3 * p 1 ∧ P = 3 * p 2 ∧ p 0 + p 1 + p 2 = P := by
  have h0 := hmult 0
  have h1 := hmult 1
  have h2 := hmult 2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **重複度 `m₀ ≥ 3` の核（本稿の主定理が落ちる有限の不等式）。**
`m` は重複度、`p k` は `(L_{y_k}·L_a⁵·L_{y_1}L_{y_2}L_{y_3})`、`P` は `(L_y·L_a⁵·…)`、
`c k = 1 + a k ≥ 1` は随伴イデアルの段から来る係数（`Σ c k ≤ m`）。
`m·p k ≤ P`（重複度）と `P ≤ Σ c k · p k`（欠損）が同時に立てば、
**`m·p k = P` がすべての `k` で成り立ち、`Σ c k = m`**。 -/
theorem defect_core_general (m : ℝ) (hm : 0 < m) (c p : Fin 3 → ℝ) (P : ℝ)
    (hc : ∀ k, 1 ≤ c k) (hcs : c 0 + c 1 + c 2 ≤ m)
    (hp : ∀ k, 0 < p k)
    (hmult : ∀ k, m * p k ≤ P)
    (hdef : P ≤ c 0 * p 0 + c 1 * p 1 + c 2 * p 2) :
    (∀ k, m * p k = P) ∧ c 0 + c 1 + c 2 = m := by
  have hP : 0 < P := lt_of_lt_of_le (mul_pos hm (hp 0)) (hmult 0)
  have s1 : (c 0 + c 1 + c 2) * P ≤ m * P := mul_le_mul_of_nonneg_right hcs hP.le
  have s2 : m * P ≤ m * (c 0 * p 0 + c 1 * p 1 + c 2 * p 2) :=
    mul_le_mul_of_nonneg_left hdef hm.le
  have n0 : 0 ≤ c 0 * (P - m * p 0) := mul_nonneg (by linarith [hc 0]) (by linarith [hmult 0])
  have n1 : 0 ≤ c 1 * (P - m * p 1) := mul_nonneg (by linarith [hc 1]) (by linarith [hmult 1])
  have n2 : 0 ≤ c 2 * (P - m * p 2) := mul_nonneg (by linarith [hc 2]) (by linarith [hmult 2])
  have idd : c 0 * (P - m * p 0) + c 1 * (P - m * p 1) + c 2 * (P - m * p 2)
      = (c 0 + c 1 + c 2) * P - m * (c 0 * p 0 + c 1 * p 1 + c 2 * p 2) := by ring
  have hle : c 0 * (P - m * p 0) + c 1 * (P - m * p 1) + c 2 * (P - m * p 2) ≤ 0 := by
    rw [idd]; linarith
  have z0 : c 0 * (P - m * p 0) = 0 := by linarith
  have z1 : c 1 * (P - m * p 1) = 0 := by linarith
  have z2 : c 2 * (P - m * p 2) = 0 := by linarith
  have e0 : m * p 0 = P := by
    rcases mul_eq_zero.1 z0 with h | h
    · exact absurd h (by linarith [hc 0] : c 0 ≠ 0)
    · linarith
  have e1 : m * p 1 = P := by
    rcases mul_eq_zero.1 z1 with h | h
    · exact absurd h (by linarith [hc 1] : c 1 ≠ 0)
    · linarith
  have e2 : m * p 2 = P := by
    rcases mul_eq_zero.1 z2 with h | h
    · exact absurd h (by linarith [hc 2] : c 2 ≠ 0)
    · linarith
  refine ⟨?_, ?_⟩
  · intro k; fin_cases k <;> assumption
  · have hsum0 : (c 0 + c 1 + c 2) * P - m * (c 0 * p 0 + c 1 * p 1 + c 2 * p 2) = 0 := by
      rw [← idd]; linarith
    have hge : m * P ≤ (c 0 + c 1 + c 2) * P := by linarith
    have := le_of_mul_le_mul_right hge hP
    linarith

/-- 随伴イデアルの段の勘定：係数の和が `m₀` に等しいなら `Σ a k = m₀ - 3`
（`Σ a k ≤ m₀ - 3` の側は先行の Koszul の段数から来る）。 -/
theorem mult_sum_eq (m0 : ℕ) (a : Fin 3 → ℕ)
    (h : a 0 + a 1 + a 2 + 3 ≤ m0)
    (he : (1 + a 0) + (1 + a 1) + (1 + a 2) = m0) :
    a 0 + a 1 + a 2 + 3 = m0 := by omega

/-! ## 2. 三つ組と四つ組（三因子が同じ類のとき） -/

/-- `x : Fin 9 → ℝ` について、どの 3 元部分集合の和も `≥ 0` で、
どの 4 元部分集合の和も `≤ 0` なら、`x = 0`。 -/
theorem three_four_zero (x : Fin 9 → ℝ)
    (h3 : ∀ S : Finset (Fin 9), S.card = 3 → 0 ≤ ∑ i ∈ S, x i)
    (h4 : ∀ S : Finset (Fin 9), S.card = 4 → ∑ i ∈ S, x i ≤ 0) :
    ∀ i, x i = 0 := by
  have hcompl : ∀ i : Fin 9, ({i}ᶜ : Finset (Fin 9)).card = 8 := by
    intro i
    rw [Finset.card_compl, Finset.card_singleton]
    simp
  have hneg : ∀ i, x i ≤ 0 := by
    intro i
    obtain ⟨T, hTsub, hTcard⟩ :=
      Finset.exists_subset_card_eq (n := 3) (s := ({i}ᶜ : Finset (Fin 9)))
        (by rw [hcompl]; norm_num)
    have hiT : i ∉ T := fun hmem => by simpa using hTsub hmem
    have hins : (insert i T).card = 4 := by
      rw [Finset.card_insert_of_notMem hiT, hTcard]
    have hsum : ∑ j ∈ insert i T, x j = x i + ∑ j ∈ T, x j := Finset.sum_insert hiT
    have a1 := h4 (insert i T) hins
    have a2 := h3 T hTcard
    rw [hsum] at a1
    linarith
  intro i
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (n := 2) (s := ({i}ᶜ : Finset (Fin 9)))
      (by rw [hcompl]; norm_num)
  have hiT : i ∉ T := fun hmem => by simpa using hTsub hmem
  have hins : (insert i T).card = 3 := by
    rw [Finset.card_insert_of_notMem hiT, hTcard]
  have hsum : ∑ j ∈ insert i T, x j = x i + ∑ j ∈ T, x j := Finset.sum_insert hiT
  have hTle : ∑ j ∈ T, x j ≤ 0 := Finset.sum_nonpos (fun j _ => hneg j)
  have a1 := h3 (insert i T) hins
  rw [hsum] at a1
  have hi := hneg i
  linarith

/-! ## 3. 符号ベクトルと錐 -/

/-- 指数 `s(v) = #{j : v j < 0}`。 -/
noncomputable def sIdx (v : Fin 9 → ℝ) : ℕ := (Finset.univ.filter (fun j => v j < 0)).card

/-- 成分ごとに増やすと指数は減らない（豊富な類を足すと指数は上がらない）。 -/
theorem sIdx_mono {u v : Fin 9 → ℝ} (h : ∀ j, v j ≤ u j) : sIdx u ≤ sIdx v := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact lt_of_le_of_lt (h j) hj

/-- 錐の議論（成分ごとの版）。`y - 3 Y k` がすべて非負で `Σ Y k - y` も非負なら、
`Σ Y k - y = 0`。 -/
theorem cone_forces_zero (Y : Fin 3 → Fin 9 → ℝ) (y : Fin 9 → ℝ)
    (hmult : ∀ k j, 0 ≤ y j - 3 * Y k j)
    (hz : ∀ j, 0 ≤ Y 0 j + Y 1 j + Y 2 j - y j) :
    ∀ j, Y 0 j + Y 1 j + Y 2 j - y j = 0 := by
  intro j
  have h0 := hmult 0 j
  have h1 := hmult 1 j
  have h2 := hmult 2 j
  have h3 := hz j
  linarith

/-- 錐の議論の帰結：指数 0 の道では三つの偏極が一致する。 -/
theorem cone_forces_equal (Y : Fin 3 → Fin 9 → ℝ) (y : Fin 9 → ℝ)
    (hmult : ∀ k j, 0 ≤ y j - 3 * Y k j)
    (hz : ∀ j, 0 ≤ Y 0 j + Y 1 j + Y 2 j - y j) :
    ∀ j, y j = 3 * Y 0 j ∧ y j = 3 * Y 1 j ∧ y j = 3 * Y 2 j := by
  intro j
  have h0 := hmult 0 j
  have h1 := hmult 1 j
  have h2 := hmult 2 j
  have h3 := cone_forces_zero Y y hmult hz j
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## 4. CM 型の勘定（`ℕ` の有限計算） -/

/-- 指数座標の CM 型 `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18` を `γ = 2` で
`(Z/19)^*` に移したもの。 -/
def Stil : Finset ℕ := {1, 2, 4, 5, 7, 8, 9, 13, 16}

/-- 指数座標から直接作った像と一致する。 -/
theorem Stil_eq_image :
    Stil = Finset.image (fun u => 2 ^ u % 19) ({0, 1, 2, 3, 4, 5, 6, 8, 16} : Finset ℕ) := by
  decide

/-- `S~` は CM 型である（`#S~ = 9`、`x ∈ S~` なら `19 - x ∉ S~`）。 -/
theorem Stil_card : Stil.card = 9 := by decide

theorem Stil_cm : ∀ x ∈ Stil, (19 - x) ∉ Stil := by decide

/-- 接空間の重み（先行の計算の `(1,2,4,8,16,13,7,9,5)`）の集合は `S~` に一致する。 -/
theorem weights_eq_Stil : ({1, 2, 4, 8, 16, 13, 7, 9, 5} : Finset ℕ) = Stil := by decide

/-- `Gal(K/F) = {1,7,11}`。`S~` はその剰余類の和ではない（CM 型は原始的）。 -/
theorem Stil_not_coset_union : ¬ (∀ x ∈ Stil, 7 * x % 19 ∈ Stil) := by decide

/-- 平方剰余（`Q(√-19)` に対応する指数 2 の部分群）との交わりは 6 元。 -/
theorem Stil_inter_qr :
    (Stil ∩ ({1, 4, 5, 6, 7, 9, 11, 16, 17} : Finset ℕ)).card = 6 := by decide

/-- `(-x) mod 19`。 -/
def neg19 (x : ℕ) : ℕ := (19 - x % 19) % 19

/-- `1` から `18` まで。 -/
def KS : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}

/-- 三点分岐の巡回 19 次被覆 `w^19 = x^a (1-x)^b`（`c ≡ -a-b`）の Jacobian の
`H^{1,0}` が指標 `k` で 1 次元になる `k` の集合。
`⟨-ka/19⟩ + ⟨-kb/19⟩ + ⟨-kc/19⟩ = 1` を分子で書いたもの。 -/
def cyclicType (a b : ℕ) : Finset ℕ :=
  KS.filter (fun k => neg19 (k * a) + neg19 (k * b) + neg19 (k * neg19 (a + b)) = 19)

/-- 陽性対照：`(a,b) = (1,1)`（`c = 17`）は実際に CM 型を出す。 -/
theorem cyclicType_1_1_card : (cyclicType 1 1).card = 9 := by decide

/-- `S~` は三点分岐の巡回 19 次被覆から出る CM 型のどれとも一致しない。 -/
theorem Stil_not_cyclic : ∀ a ∈ KS, ∀ b ∈ KS, cyclicType a b ≠ Stil := by decide

end CMHodge

#print axioms CMHodge.coeff_zero_of_sum_nonpos
#print axioms CMHodge.defect_core
#print axioms CMHodge.defect_core_general
#print axioms CMHodge.mult_sum_eq
#print axioms CMHodge.three_four_zero
#print axioms CMHodge.sIdx_mono
#print axioms CMHodge.cone_forces_zero
#print axioms CMHodge.cone_forces_equal
#print axioms CMHodge.Stil_eq_image
#print axioms CMHodge.Stil_card
#print axioms CMHodge.Stil_cm
#print axioms CMHodge.weights_eq_Stil
#print axioms CMHodge.Stil_not_coset_union
#print axioms CMHodge.Stil_inter_qr
#print axioms CMHodge.cyclicType_1_1_card
#print axioms CMHodge.Stil_not_cyclic
