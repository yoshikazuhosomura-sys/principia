/-
  ハドヴィガー・ネルソン（Erdős #132 系）：`f(α)` の**下界**の証人と、その族。

  `f(α)` は「独立数 `≤ α` の有限単位距離グラフの最大点数」。ここで Lean に載せたのは
  「独立数 `≤ α` の `n` 点平面単位距離グラフが**存在する**」という下界の言明（`FGe n α`）で
  あって、`f(α)` そのものの定義と最大性の主張は Lean の外に置いてある。

  * 証人の段：`Moser ⊔ K₃`（10 点・14 辺・`α = 3`）⟹ `f(3) ≥ 10`、
    `Moser ⊔ Moser`（14 点・22 辺・`α = 4`）⟹ `f(4) ≥ 14`
  * 族の段：非交和の加法定理 `FGe n₁ α₁ → FGe n₂ α₂ → FGe (n₁+n₂) (α₁+α₂)` から
    `f(2k) ≥ 7k`・`f(2k+1) ≥ 7k+3`

  sorry 0・native_decide 不使用。
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.unusedTactic false

/-!
## ハドヴィガー・ネルソン（#132 系）：`f(α)` の**下界**の証人を Lean 4 で。
  **一般部**（この段）。

  `f(α)` は「独立数 `≤ α` の有限単位距離グラフの最大点数」。`f(3) ≤ 10` の
  証明書部分（`n = 11`・`α ≤ 3` の候補 117 類はいずれも実現しない）は別に閉じてある。ここはその**下界**側、
  すなわち **証人の提示** である：

  * (A) `Moser ⊔ K₃`：10 点・14 辺・`α = 3` ⟹ `f(3) ≥ 10`
  * (B) `Moser ⊔ Moser`：14 点・22 辺・`α = 4` ⟹ `f(4) ≥ 14`

  下界の証人には二つの負担がある。

  1. **実現の存在**。辺集合を明示し、**その辺だけ**距離 1 を要求する（非辺には何も課さない）。
     Moser spindle の座標は `Q(√3,√11,√33)` に入る。平方根を式から消さず、
     `s3² = 3`・`s11² = 11`・`s3·s11 = s33` の三つの等式だけで各辺を閉じる
     （`linear_combination` の係数は多項式除算で先に計算しておく：`erdos1183gen.py`）。
  2. **独立数の上界**。`indepNum ≤ k` は「`k+1` 点の**増加**組はどれも辺を含む」から出す。
     `Finset` の独立集合から増加組を取り出すのに `Finset.orderEmbOfFin` を使う。
     増加組に絞ると `decide` の当たりは `C(n, k+1)` 個で済む（(A) 210 個・(B) 2002 個）。

  頂点が互いに異なること（`Function.Injective p`）は、`L(x, y) = x + 3y` が
  **頂点番号の順に狭義単調**になるように番号を付け替えて出す。45 組・91 組の
  場合分けを、10 個・14 個の隣接不等式に減らすための細工である。

  sorry 0・native_decide 不使用。
-/

set_option linter.style.longLine false

namespace HadwigerNelson.Witness

/-! ## 1. 三つの平方根 -/

noncomputable def s3 : ℝ := Real.sqrt 3
noncomputable def s11 : ℝ := Real.sqrt 11
noncomputable def s33 : ℝ := Real.sqrt 33

lemma s3_sq : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma s11_sq : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
lemma s33_sq : s33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)

/-- `√3 · √11 = √33`。座標の積から出る `s33` を消すための唯一の関係式。 -/
lemma s3_mul_s11 : s3 * s11 = s33 := by
  unfold s3 s11 s33
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

/-! ### 有理数による箱（単調性の検査に使う） -/

private lemma sqrt_lb {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 < x) : c < Real.sqrt x := by
  have h' : Real.sqrt (c ^ 2) < Real.sqrt x := Real.sqrt_lt_sqrt (by positivity) h
  rwa [Real.sqrt_sq hc] at h'

private lemma sqrt_ub {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (h : x < c ^ 2) :
    Real.sqrt x < c := by
  have h' : Real.sqrt x < Real.sqrt (c ^ 2) := Real.sqrt_lt_sqrt hx h
  rwa [Real.sqrt_sq hc] at h'

lemma s3_lb : (1.7320 : ℝ) < s3 := sqrt_lb (by norm_num) (by norm_num)
lemma s3_ub : s3 < 1.7321 := sqrt_ub (by norm_num) (by norm_num) (by norm_num)
lemma s11_lb : (3.3166 : ℝ) < s11 := sqrt_lb (by norm_num) (by norm_num)
lemma s11_ub : s11 < 3.3167 := sqrt_ub (by norm_num) (by norm_num) (by norm_num)
lemma s33_lb : (5.7445 : ℝ) < s33 := sqrt_lb (by norm_num) (by norm_num)
lemma s33_ub : s33 < 5.7446 := sqrt_ub (by norm_num) (by norm_num) (by norm_num)

/-! ## 2. 平面単位距離実現 -/

/-- 平面の 2 点の距離の 2 乗。 -/
noncomputable def sq2 (a b : ℝ × ℝ) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

lemma sq2_comm (a b : ℝ × ℝ) : sq2 a b = sq2 b a := by unfold sq2; ring

/-- グラフ `G` の平面単位距離実現：**辺**の端点は距離 1（非辺には何も課さない）・
  異なる頂点は異なる点。 -/
def Realiz {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n → ℝ × ℝ) : Prop :=
  (∀ i j : Fin n, G.Adj i j → sq2 (p i) (p j) = 1) ∧ Function.Injective p

/-- `f(α) ≥ n`：独立数 `≤ α` の `n` 点平面単位距離グラフが存在する。
  `f(α)` は「独立数 `≤ α` の有限単位距離グラフの最大点数」なので、これが下界の言明になる。 -/
def FGe (n α : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), (∃ p : Fin n → ℝ × ℝ, Realiz G p) ∧ G.indepNum ≤ α

/-! ## 3. 辺リストからのグラフ -/

/-- 辺リスト `E`（頂点は `ℕ` の名）から作る隣接関係。 -/
def adjOf {n : ℕ} (E : List (ℕ × ℕ)) (i j : Fin n) : Prop :=
  ((i : ℕ), (j : ℕ)) ∈ E ∨ ((j : ℕ), (i : ℕ)) ∈ E

instance {n : ℕ} (E : List (ℕ × ℕ)) (i j : Fin n) : Decidable (adjOf E i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `E` を辺リストとするグラフ（自己ループがないことは `hl` で与える）。 -/
def graphOf {n : ℕ} (E : List (ℕ × ℕ)) (hl : ∀ i : Fin n, ¬ adjOf E i i) :
    SimpleGraph (Fin n) where
  Adj := adjOf E
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨hl⟩

@[simp] lemma graphOf_adj {n : ℕ} {E : List (ℕ × ℕ)} {hl : ∀ i : Fin n, ¬ adjOf E i i}
    {i j : Fin n} : (graphOf E hl).Adj i j ↔ adjOf E i j := Iff.rfl

/-- 辺リストの各辺で距離が 1 で、頂点が互いに異なれば、実現が得られる。 -/
lemma realiz_of_edges {n : ℕ} {E : List (ℕ × ℕ)} {hl : ∀ i : Fin n, ¬ adjOf E i i}
    {q : ℕ → ℝ × ℝ} (hE : ∀ e ∈ E, sq2 (q e.1) (q e.2) = 1)
    (hi : Function.Injective (fun i : Fin n => q (i : ℕ))) :
    Realiz (graphOf E hl) (fun i : Fin n => q (i : ℕ)) := by
  refine ⟨?_, hi⟩
  intro i j h
  simp only [graphOf_adj, adjOf] at h
  rcases h with h | h
  · exact hE ((i : ℕ), (j : ℕ)) h
  · rw [sq2_comm]; exact hE ((j : ℕ), (i : ℕ)) h

/-- 座標が `L(x,y) = x + 3y` で（番号の順に）狭義単調なら、頂点は互いに異なる。 -/
lemma injective_of_strictMono {n : ℕ} (q : ℕ → ℝ × ℝ)
    (hm : StrictMono (fun k : ℕ => (q k).1 + 3 * (q k).2)) :
    Function.Injective (fun i : Fin n => q (i : ℕ)) := by
  intro i j hij
  have h : (q (i : ℕ)).1 + 3 * (q (i : ℕ)).2 = (q (j : ℕ)).1 + 3 * (q (j : ℕ)).2 := by
    rw [show q (i : ℕ) = q (j : ℕ) from hij]
  exact Fin.ext (hm.injective h)

/-! ## 4. 独立数の上界 -/

/-- どの独立集合も濃度 `≤ k` なら `indepNum ≤ k`。 -/
lemma indepNum_le {n k : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → s.card ≤ k) :
    G.indepNum ≤ k := by
  obtain ⟨s, hs, hcard⟩ := G.exists_isNIndepSet_indepNum
  rw [← hcard]
  exact h s hs

/-- 増加 4 点組がどれも辺を含むなら独立数は `≤ 3`。
  `Finset.orderEmbOfFin` で独立集合から増加 4 点組を取り出す。 -/
lemma indepNum_le_three {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ a b c d : Fin n, a < b → b < c → c < d →
      G.Adj a b ∨ G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d ∨ G.Adj c d) :
    G.indepNum ≤ 3 := by
  refine indepNum_le ?_
  intro s hs
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
  have hmem : ∀ i : Fin 4, (t.orderEmbOfFin htc) i ∈ (s : Set (Fin n)) := fun i =>
    Finset.mem_coe.mpr (hts (t.orderEmbOfFin_mem htc i))
  have key : ∀ i j : Fin 4, i < j →
      ¬ G.Adj ((t.orderEmbOfFin htc) i) ((t.orderEmbOfFin htc) j) := fun i j hij =>
    hs (hmem i) (hmem j) (ne_of_lt ((t.orderEmbOfFin htc).strictMono hij))
  rcases h _ _ _ _ ((t.orderEmbOfFin htc).strictMono (show (0 : Fin 4) < 1 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (1 : Fin 4) < 2 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (2 : Fin 4) < 3 by decide)) with
    H | H | H | H | H | H
  exacts [key 0 1 (by decide) H, key 0 2 (by decide) H, key 0 3 (by decide) H,
          key 1 2 (by decide) H, key 1 3 (by decide) H, key 2 3 (by decide) H]

/-- 増加 5 点組がどれも辺を含むなら独立数は `≤ 4`。 -/
lemma indepNum_le_four {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ a b c d e : Fin n, a < b → b < c → c < d → d < e →
      G.Adj a b ∨ G.Adj a c ∨ G.Adj a d ∨ G.Adj a e ∨ G.Adj b c ∨ G.Adj b d ∨
      G.Adj b e ∨ G.Adj c d ∨ G.Adj c e ∨ G.Adj d e) :
    G.indepNum ≤ 4 := by
  refine indepNum_le ?_
  intro s hs
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 5 ≤ s.card by omega)
  have hmem : ∀ i : Fin 5, (t.orderEmbOfFin htc) i ∈ (s : Set (Fin n)) := fun i =>
    Finset.mem_coe.mpr (hts (t.orderEmbOfFin_mem htc i))
  have key : ∀ i j : Fin 5, i < j →
      ¬ G.Adj ((t.orderEmbOfFin htc) i) ((t.orderEmbOfFin htc) j) := fun i j hij =>
    hs (hmem i) (hmem j) (ne_of_lt ((t.orderEmbOfFin htc).strictMono hij))
  rcases h _ _ _ _ _ ((t.orderEmbOfFin htc).strictMono (show (0 : Fin 5) < 1 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (1 : Fin 5) < 2 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (2 : Fin 5) < 3 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (3 : Fin 5) < 4 by decide)) with
    H | H | H | H | H | H | H | H | H | H
  exacts [key 0 1 (by decide) H, key 0 2 (by decide) H, key 0 3 (by decide) H,
          key 0 4 (by decide) H, key 1 2 (by decide) H, key 1 3 (by decide) H,
          key 1 4 (by decide) H, key 2 3 (by decide) H, key 2 4 (by decide) H,
          key 3 4 (by decide) H]

end HadwigerNelson.Witness

/-!
## HN の下界の証人 **(A)**：`f(3) ≥ 10`（`Moser ⊔ K₃`・10 点・`α = 3`）

  **(A) `Moser ⊔ K₃`**：Moser spindle（7 点・11 辺・`α = 2`）と単位正三角形（3 点・`α = 1`）を
  互いに離して置いた 10 点のグラフ。辺集合を明示し、**その辺だけ**距離 1 を要求する
  （非辺には何も課さない）。異なる頂点が異なる点であることは、
  `L(x,y) = x + 3y` が頂点番号の順に狭義単調であることから出す。

  座標は `Q(√3,√11,√33)`。Moser spindle は原点と `(√3,0)` を結ぶ菱形と、
  それを `cos θ = 5/6`・`sin θ = √11/6` で回した菱形の合併で、
  遠い二頂点の距離が `6(1 − cos θ) = 1` になる。
-/

set_option linter.style.longLine false
set_option linter.unusedTactic false

namespace HadwigerNelson.Witness

/-! ## (A) `f(3) ≥ 10`（`Moser ⊔ K₃`・10 点・`α = 3`） -/

/-- (A) の辺集合（14 辺）。頂点は `L(x,y) = x + 3y` の昇順に並べてある。 -/
def EA : List (ℕ × ℕ) :=
  [(0,1), (0,3), (0,4), (1,2), (1,4), (1,5), (2,5), (2,6), (3,4), (3,6), (5,6), (7,8), (7,9), 
   (8,9)]

lemma EA_loopless : ∀ i : Fin 10, ¬ adjOf EA i i := by decide

/-- (A) のグラフ。 -/
def GA : SimpleGraph (Fin 10) := graphOf EA EA_loopless

/-- (A) の座標。`√3`・`√11`・`√33` の有理結合。`10` 以上の番号は使わない
  （単調性を `ℕ` 全体で言うための埋め草）。 -/
noncomputable def qA : ℕ → ℝ × ℝ
  | 0 => (1/2 * s3, (-1/2))
  | 1 => (0, 0)
  | 2 => (1/12 * s11 + 5/12 * s3, (-5/12) + 1/12 * s33)
  | 3 => (s3, 0)
  | 4 => (1/2 * s3, 1/2)
  | 5 => ((-1/12) * s11 + 5/12 * s3, 5/12 + 1/12 * s33)
  | 6 => (5/6 * s3, 1/6 * s33)
  | 7 => (10, 0)
  | 8 => (11, 0)
  | 9 => (21/2, 1/2 * s3)
  | k => (100 * (k : ℝ), 0)

/-- (A) の頂点の位置。 -/
noncomputable def pA : Fin 10 → ℝ × ℝ := fun i => qA (i : ℕ)

/-! ### 各辺の距離が 1 -/

lemma eA_0_1 : sq2 (qA 0) (qA 1) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_0_3 : sq2 (qA 0) (qA 3) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_0_4 : sq2 (qA 0) (qA 4) = 1 := by
  simp only [sq2, qA]
  linear_combination (0) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_1_2 : sq2 (qA 1) (qA 2) = 1 := by
  simp only [sq2, qA]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eA_1_4 : sq2 (qA 1) (qA 4) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_1_5 : sq2 (qA 1) (qA 5) = 1 := by
  simp only [sq2, qA]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eA_2_5 : sq2 (qA 2) (qA 5) = 1 := by
  simp only [sq2, qA]
  linear_combination (0) * s3_sq + (1/36) * s11_sq + (0) * s3_mul_s11

lemma eA_2_6 : sq2 (qA 2) (qA 6) = 1 := by
  simp only [sq2, qA]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eA_3_4 : sq2 (qA 3) (qA 4) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_3_6 : sq2 (qA 3) (qA 6) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/36 + 1/36 * s11 ^ 2) * s3_sq + (1/12) * s11_sq + ((-1/36) * s33 + (-1/36) * s3 * s11) * s3_mul_s11

lemma eA_5_6 : sq2 (qA 5) (qA 6) = 1 := by
  simp only [sq2, qA]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eA_7_8 : sq2 (qA 7) (qA 8) = 1 := by
  simp only [sq2, qA]
  linear_combination (0) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_7_9 : sq2 (qA 7) (qA 9) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eA_8_9 : sq2 (qA 8) (qA 9) = 1 := by
  simp only [sq2, qA]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma EA_edges : ∀ e ∈ EA, sq2 (qA e.1) (qA e.2) = 1 := by
  intro e he
  simp only [EA] at he
  fin_cases he
  exacts [eA_0_1, eA_0_3, eA_0_4, eA_1_2, eA_1_4, eA_1_5, eA_2_5, eA_2_6, eA_3_4, eA_3_6, eA_5_6, 
   eA_7_8, eA_7_9, eA_8_9]

/-! ### 頂点は互いに異なる（`L = x + 3y` が狭義単調） -/

lemma monoA : StrictMono (fun k : ℕ => (qA k).1 + 3 * (qA k).2) := by
  apply strictMono_nat_of_lt_succ
  intro k
  match k with
  | 0 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 1 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 2 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 3 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 4 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 5 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 6 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 7 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 8 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 9 =>
      simp only [qA]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | (m+10) =>
      simp only [qA]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]

lemma pA_inj : Function.Injective pA :=
  injective_of_strictMono qA monoA

/-- (A) は平面単位距離グラフとして実現される。 -/
theorem realizA : Realiz GA pA :=
  realiz_of_edges EA_edges pA_inj

/-! ### 独立数 `≤ 3` -/

/-- 増加 4 点組はどれも辺を含む（`decide +kernel`：`Fin 10` の増加 4 点組 210 個）。 -/
theorem tupA : ∀ a b c d : Fin 10,
    a < b → b < c → c < d →
    adjOf EA a b ∨ adjOf EA a c ∨ adjOf EA a d ∨ adjOf EA b c ∨ adjOf EA b d ∨ adjOf EA c d := by
  decide +kernel

theorem indepA : GA.indepNum ≤ 3 :=
  indepNum_le_three (fun a b c d => tupA a b c d)

/-- **(A)** `f(3) ≥ 10`：独立数 `≤ 3` の 10 点平面単位距離グラフがある。 -/
theorem fGe_10_3 : FGe 10 3 := ⟨GA, ⟨pA, realizA⟩, indepA⟩

end HadwigerNelson.Witness

/-!
## HN の下界の証人 **(B)**：`f(4) ≥ 14`（`Moser ⊔ Moser`・14 点・`α = 4`）

  **(B) `Moser ⊔ Moser`**：Moser spindle 二つ（14 点・22 辺）。
  二つ目は一つ目を `(10, 0)` だけ平行移動したもの。`α = 2 + 2 = 4`。
-/

set_option linter.style.longLine false
set_option linter.unusedTactic false

namespace HadwigerNelson.Witness

/-! ## (B) `f(4) ≥ 14`（`Moser ⊔ Moser`・14 点・`α = 4`） -/

/-- (B) の辺集合（22 辺）。頂点は `L(x,y) = x + 3y` の昇順に並べてある。 -/
def EB : List (ℕ × ℕ) :=
  [(0,1), (0,3), (0,4), (1,2), (1,4), (1,5), (2,5), (2,6), (3,4), (3,6), (5,6), (7,8), (7,10), 
   (7,11), (8,9), (8,11), (8,12), (9,12), (9,13), (10,11), (10,13), (12,13)]

lemma EB_loopless : ∀ i : Fin 14, ¬ adjOf EB i i := by decide

/-- (B) のグラフ。 -/
def GB : SimpleGraph (Fin 14) := graphOf EB EB_loopless

/-- (B) の座標。`√3`・`√11`・`√33` の有理結合。`14` 以上の番号は使わない
  （単調性を `ℕ` 全体で言うための埋め草）。 -/
noncomputable def qB : ℕ → ℝ × ℝ
  | 0 => (1/2 * s3, (-1/2))
  | 1 => (0, 0)
  | 2 => (1/12 * s11 + 5/12 * s3, (-5/12) + 1/12 * s33)
  | 3 => (s3, 0)
  | 4 => (1/2 * s3, 1/2)
  | 5 => ((-1/12) * s11 + 5/12 * s3, 5/12 + 1/12 * s33)
  | 6 => (5/6 * s3, 1/6 * s33)
  | 7 => (10 + 1/2 * s3, (-1/2))
  | 8 => (10, 0)
  | 9 => (10 + 1/12 * s11 + 5/12 * s3, (-5/12) + 1/12 * s33)
  | 10 => (10 + s3, 0)
  | 11 => (10 + 1/2 * s3, 1/2)
  | 12 => (10 + (-1/12) * s11 + 5/12 * s3, 5/12 + 1/12 * s33)
  | 13 => (10 + 5/6 * s3, 1/6 * s33)
  | k => (100 * (k : ℝ), 0)

/-- (B) の頂点の位置。 -/
noncomputable def pB : Fin 14 → ℝ × ℝ := fun i => qB (i : ℕ)

/-! ### 各辺の距離が 1 -/

lemma eB_0_1 : sq2 (qB 0) (qB 1) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_0_3 : sq2 (qB 0) (qB 3) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_0_4 : sq2 (qB 0) (qB 4) = 1 := by
  simp only [sq2, qB]
  linear_combination (0) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_1_2 : sq2 (qB 1) (qB 2) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_1_4 : sq2 (qB 1) (qB 4) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_1_5 : sq2 (qB 1) (qB 5) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_2_5 : sq2 (qB 2) (qB 5) = 1 := by
  simp only [sq2, qB]
  linear_combination (0) * s3_sq + (1/36) * s11_sq + (0) * s3_mul_s11

lemma eB_2_6 : sq2 (qB 2) (qB 6) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_3_4 : sq2 (qB 3) (qB 4) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_3_6 : sq2 (qB 3) (qB 6) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/36 + 1/36 * s11 ^ 2) * s3_sq + (1/12) * s11_sq + ((-1/36) * s33 + (-1/36) * s3 * s11) * s3_mul_s11

lemma eB_5_6 : sq2 (qB 5) (qB 6) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_7_8 : sq2 (qB 7) (qB 8) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_7_10 : sq2 (qB 7) (qB 10) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_7_11 : sq2 (qB 7) (qB 11) = 1 := by
  simp only [sq2, qB]
  linear_combination (0) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_8_9 : sq2 (qB 8) (qB 9) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_8_11 : sq2 (qB 8) (qB 11) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_8_12 : sq2 (qB 8) (qB 12) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_9_12 : sq2 (qB 9) (qB 12) = 1 := by
  simp only [sq2, qB]
  linear_combination (0) * s3_sq + (1/36) * s11_sq + (0) * s3_mul_s11

lemma eB_9_13 : sq2 (qB 9) (qB 13) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + ((-5/72) + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma eB_10_11 : sq2 (qB 10) (qB 11) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/4) * s3_sq + (0) * s11_sq + (0) * s3_mul_s11

lemma eB_10_13 : sq2 (qB 10) (qB 13) = 1 := by
  simp only [sq2, qB]
  linear_combination (1/36 + 1/36 * s11 ^ 2) * s3_sq + (1/12) * s11_sq + ((-1/36) * s33 + (-1/36) * s3 * s11) * s3_mul_s11

lemma eB_12_13 : sq2 (qB 12) (qB 13) = 1 := by
  simp only [sq2, qB]
  linear_combination (25/144 + 1/144 * s11 ^ 2) * s3_sq + (1/36) * s11_sq + (5/72 + (-1/144) * s33 + (-1/144) * s3 * s11) * s3_mul_s11

lemma EB_edges : ∀ e ∈ EB, sq2 (qB e.1) (qB e.2) = 1 := by
  intro e he
  simp only [EB] at he
  fin_cases he
  exacts [eB_0_1, eB_0_3, eB_0_4, eB_1_2, eB_1_4, eB_1_5, eB_2_5, eB_2_6, eB_3_4, eB_3_6, eB_5_6, 
   eB_7_8, eB_7_10, eB_7_11, eB_8_9, eB_8_11, eB_8_12, eB_9_12, eB_9_13, eB_10_11, eB_10_13, 
   eB_12_13]

/-! ### 頂点は互いに異なる（`L = x + 3y` が狭義単調） -/

lemma monoB : StrictMono (fun k : ℕ => (qB k).1 + 3 * (qB k).2) := by
  apply strictMono_nat_of_lt_succ
  intro k
  match k with
  | 0 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 1 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 2 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 3 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 4 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 5 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 6 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 7 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 8 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 9 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 10 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 11 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 12 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | 13 =>
      simp only [qB]
      first
        | (norm_num; linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub])
        | norm_num
        | linarith [s3_lb, s3_ub, s11_lb, s11_ub, s33_lb, s33_ub]
  | (m+14) =>
      simp only [qB]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]

lemma pB_inj : Function.Injective pB :=
  injective_of_strictMono qB monoB

/-- (B) は平面単位距離グラフとして実現される。 -/
theorem realizB : Realiz GB pB :=
  realiz_of_edges EB_edges pB_inj

/-! ### 独立数 `≤ 4` -/

/-- 増加 5 点組はどれも辺を含む（`decide +kernel`：`Fin 14` の増加 5 点組 2002 個）。 -/
/- 峰のメモリを下げるため、先頭の頂点ごとに 14 本に分ける。 -/
theorem tupB_0 : ∀ b c d e : Fin 14,
    (0 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (0 : Fin 14) b ∨ adjOf EB (0 : Fin 14) c ∨ adjOf EB (0 : Fin 14) d ∨ 
    adjOf EB (0 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_1 : ∀ b c d e : Fin 14,
    (1 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (1 : Fin 14) b ∨ adjOf EB (1 : Fin 14) c ∨ adjOf EB (1 : Fin 14) d ∨ 
    adjOf EB (1 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_2 : ∀ b c d e : Fin 14,
    (2 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (2 : Fin 14) b ∨ adjOf EB (2 : Fin 14) c ∨ adjOf EB (2 : Fin 14) d ∨ 
    adjOf EB (2 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_3 : ∀ b c d e : Fin 14,
    (3 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (3 : Fin 14) b ∨ adjOf EB (3 : Fin 14) c ∨ adjOf EB (3 : Fin 14) d ∨ 
    adjOf EB (3 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_4 : ∀ b c d e : Fin 14,
    (4 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (4 : Fin 14) b ∨ adjOf EB (4 : Fin 14) c ∨ adjOf EB (4 : Fin 14) d ∨ 
    adjOf EB (4 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_5 : ∀ b c d e : Fin 14,
    (5 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (5 : Fin 14) b ∨ adjOf EB (5 : Fin 14) c ∨ adjOf EB (5 : Fin 14) d ∨ 
    adjOf EB (5 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_6 : ∀ b c d e : Fin 14,
    (6 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (6 : Fin 14) b ∨ adjOf EB (6 : Fin 14) c ∨ adjOf EB (6 : Fin 14) d ∨ 
    adjOf EB (6 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_7 : ∀ b c d e : Fin 14,
    (7 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (7 : Fin 14) b ∨ adjOf EB (7 : Fin 14) c ∨ adjOf EB (7 : Fin 14) d ∨ 
    adjOf EB (7 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_8 : ∀ b c d e : Fin 14,
    (8 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (8 : Fin 14) b ∨ adjOf EB (8 : Fin 14) c ∨ adjOf EB (8 : Fin 14) d ∨ 
    adjOf EB (8 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_9 : ∀ b c d e : Fin 14,
    (9 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (9 : Fin 14) b ∨ adjOf EB (9 : Fin 14) c ∨ adjOf EB (9 : Fin 14) d ∨ 
    adjOf EB (9 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_10 : ∀ b c d e : Fin 14,
    (10 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (10 : Fin 14) b ∨ adjOf EB (10 : Fin 14) c ∨ adjOf EB (10 : Fin 14) d ∨ 
    adjOf EB (10 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_11 : ∀ b c d e : Fin 14,
    (11 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (11 : Fin 14) b ∨ adjOf EB (11 : Fin 14) c ∨ adjOf EB (11 : Fin 14) d ∨ 
    adjOf EB (11 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_12 : ∀ b c d e : Fin 14,
    (12 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (12 : Fin 14) b ∨ adjOf EB (12 : Fin 14) c ∨ adjOf EB (12 : Fin 14) d ∨ 
    adjOf EB (12 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB_13 : ∀ b c d e : Fin 14,
    (13 : Fin 14) < b → b < c → c < d → d < e →
    adjOf EB (13 : Fin 14) b ∨ adjOf EB (13 : Fin 14) c ∨ adjOf EB (13 : Fin 14) d ∨ 
    adjOf EB (13 : Fin 14) e ∨ adjOf EB b c ∨ adjOf EB b d ∨ adjOf EB b e ∨ adjOf EB c d ∨ 
    adjOf EB c e ∨ adjOf EB d e := by
  decide +kernel

theorem tupB : ∀ a b c d e : Fin 14,
    a < b → b < c → c < d → d < e →
    adjOf EB a b ∨ adjOf EB a c ∨ adjOf EB a d ∨ adjOf EB a e ∨ adjOf EB b c ∨ adjOf EB b d ∨ 
    adjOf EB b e ∨ adjOf EB c d ∨ adjOf EB c e ∨ adjOf EB d e := by
  intro a
  fin_cases a
  exacts [tupB_0, tupB_1, tupB_2, tupB_3, tupB_4, tupB_5, tupB_6, tupB_7, tupB_8, tupB_9, 
   tupB_10, tupB_11, tupB_12, tupB_13]

theorem indepB : GB.indepNum ≤ 4 :=
  indepNum_le_four (fun a b c d e => tupB a b c d e)

/-- **(B)** `f(4) ≥ 14`：独立数 `≤ 4` の 14 点平面単位距離グラフがある。 -/
theorem fGe_14_4 : FGe 14 4 := ⟨GB, ⟨pB, realizB⟩, indepB⟩

end HadwigerNelson.Witness

/-!
## 総括：ハドヴィガー・ネルソンの `f(α)` の**下界**の証人二つ。

  * (A) `Moser ⊔ K₃`：10 点・14 辺・独立数 3 ⟹ **`f(3) ≥ 10`**
  * (B) `Moser ⊔ Moser`：14 点・22 辺・独立数 4 ⟹ **`f(4) ≥ 14`**

  `f(3) ≤ 10` の証明書部分（`n = 11`・`α ≤ 3` の候補 117 類はいずれも実現しない）が
  別に閉じているので、二つを併せると **`f(3) = 10`** が Lean の中で
  （列挙の完全性を Lean の外に置いたまま）言えることになる。

  **Lean の外に残すもの**：`f(α)` そのものの定義。ここで Lean に載せたのは
  「独立数 `≤ α` の `n` 点平面単位距離グラフが**存在する**」という下界の言明
  （`FGe n α`）であって、最大性の主張ではない。

  陽性対照として、独立数がちょうど `α` であること（`≥` の側）も付けてある。
  これは「増加組がどれも辺を含む」という `decide` が空虚に真ではないことの検問である。
-/

set_option linter.style.longLine false

namespace HadwigerNelson.Witness

/-! ## 陽性対照：独立数はちょうど 3・4 -/

instance : DecidableRel GA.Adj := fun i j => inferInstanceAs (Decidable (adjOf EA i j))
instance : DecidableRel GB.Adj := fun i j => inferInstanceAs (Decidable (adjOf EB i j))

/-- (A) には大きさ 3 の独立集合がある（spindle の 2 点 ＋ 三角形の 1 点）。 -/
theorem indepA_ge : 3 ≤ GA.indepNum := by
  have h : GA.IsIndepSet ((({0, 2, 7} : Finset (Fin 10))) : Set (Fin 10)) := by decide
  have h2 := h.card_le_indepNum
  rw [show (({0, 2, 7} : Finset (Fin 10))).card = 3 from by decide] at h2
  exact h2

theorem indepA_eq : GA.indepNum = 3 := le_antisymm indepA indepA_ge

/-- (B) には大きさ 4 の独立集合がある（各 spindle から 2 点）。 -/
theorem indepB_ge : 4 ≤ GB.indepNum := by
  have h : GB.IsIndepSet ((({0, 2, 7, 9} : Finset (Fin 14))) : Set (Fin 14)) := by decide
  have h2 := h.card_le_indepNum
  rw [show (({0, 2, 7, 9} : Finset (Fin 14))).card = 4 from by decide] at h2
  exact h2

theorem indepB_eq : GB.indepNum = 4 := le_antisymm indepB indepB_ge

/-! ## 主定理 -/

/-- **この段の主定理**：`f(3) ≥ 10` かつ `f(4) ≥ 14`。 -/
theorem hn_lower : FGe 10 3 ∧ FGe 14 4 := ⟨fGe_10_3, fGe_14_4⟩

end HadwigerNelson.Witness

/-!
## ハドヴィガー・ネルソン（#132 系）：**非交和の一般補題**（この段）。

  証人の段は `f(3) ≥ 10`・`f(4) ≥ 14` を「Moser spindle と三角形を離して置いた
  10 点・14 点のグラフ」として一つずつ Lean に載せた。そこで残った宿題が

      `α(G₁ ⊔ G₂) = α(G₁) + α(G₂)`

  の一般補題である。これを入れると、下界の証人は「部品を並べる」ことに還り、
  `f(2k) ≥ 7k` が `k` について一本で出る（増加組の `decide` は 7 点の spindle 一つで済む）。

  この段の構成：

  * §1 頂点型を `Fin n` から外した `RealizV`・`FGeV`（`Fin n` では証人の段の定義に
    定義的に一致する）
  * §2 独立数の上界（一般の有限型版 `indepNum_le'`）
  * §3 **補題 A**：`(G ⊕g H).indepNum = G.indepNum + H.indepNum`。
    `≤` は `Finset.toLeft`・`Finset.toRight` で独立集合を割り、
    `≥` は `Finset.disjSum` で独立集合を貼る
  * §4 **補題 B**：実現の非交和。右側を `shift` だけ右へ平行移動する。
    辺だけに距離 1 を課すので平行移動は「像が重ならない」だけでよく、
    量は `max` を使わず**絶対値の和**で取る（頂点集合が空でも通るように）
  * §5 `comap` による頂点型の移送と加法定理 `FGe (n₁+n₂) (α₁+α₂)`
  * §6 独立数 `≤ 1`・`≤ 2` の増加組版（証人の段の `≤ 3`・`≤ 4` と同じ型）

  sorry 0・native_decide 不使用。
-/

set_option linter.style.longLine false

namespace HadwigerNelson.Family

open HadwigerNelson.Witness

/-! ## 1. 頂点型を外した実現 -/

/-- 任意の頂点型での平面単位距離実現。`HadwigerNelson.Witness.Realiz` の `Fin n` を外しただけ。 -/
def RealizV {V : Type*} (G : SimpleGraph V) (p : V → ℝ × ℝ) : Prop :=
  (∀ i j : V, G.Adj i j → sq2 (p i) (p j) = 1) ∧ Function.Injective p

/-- 任意の頂点型での下界の言明。 -/
def FGeV (V : Type*) (α : ℕ) : Prop :=
  ∃ G : SimpleGraph V, (∃ p : V → ℝ × ℝ, RealizV G p) ∧ G.indepNum ≤ α

lemma realizV_iff_realiz {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n → ℝ × ℝ) :
    RealizV G p ↔ Realiz G p := Iff.rfl

lemma fGeV_fin (n α : ℕ) : FGeV (Fin n) α ↔ FGe n α := Iff.rfl

/-! ## 2. 独立数の上界（一般の有限型） -/

/-- どの独立集合も濃度 `≤ k` なら `indepNum ≤ k`（証人の段の `indepNum_le` の頂点型一般版）。 -/
lemma indepNum_le' {V : Type*} [Finite V] {k : ℕ} {G : SimpleGraph V}
    (h : ∀ s : Finset V, G.IsIndepSet (s : Set V) → s.card ≤ k) : G.indepNum ≤ k := by
  obtain ⟨s, hs, hcard⟩ := G.exists_isNIndepSet_indepNum
  rw [← hcard]
  exact h s hs

/-! ## 3. 補題 A：非交和の独立数 -/

/-- 非交和の独立集合を左に落とすと独立集合。 -/
lemma isIndepSet_toLeft {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : Finset (V ⊕ W)} (hs : (G ⊕g H).IsIndepSet (s : Set (V ⊕ W))) :
    G.IsIndepSet (s.toLeft : Set V) := by
  intro a ha b hb hab hadj
  have ha' : (Sum.inl a : V ⊕ W) ∈ (s : Set (V ⊕ W)) :=
    Finset.mem_coe.mpr (Finset.mem_toLeft.mp (Finset.mem_coe.mp ha))
  have hb' : (Sum.inl b : V ⊕ W) ∈ (s : Set (V ⊕ W)) :=
    Finset.mem_coe.mpr (Finset.mem_toLeft.mp (Finset.mem_coe.mp hb))
  exact hs ha' hb' (Sum.inl_injective.ne hab) (SimpleGraph.sum_adj_inl.mpr hadj)

/-- 非交和の独立集合を右に落とすと独立集合。 -/
lemma isIndepSet_toRight {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : Finset (V ⊕ W)} (hs : (G ⊕g H).IsIndepSet (s : Set (V ⊕ W))) :
    H.IsIndepSet (s.toRight : Set W) := by
  intro a ha b hb hab hadj
  have ha' : (Sum.inr a : V ⊕ W) ∈ (s : Set (V ⊕ W)) :=
    Finset.mem_coe.mpr (Finset.mem_toRight.mp (Finset.mem_coe.mp ha))
  have hb' : (Sum.inr b : V ⊕ W) ∈ (s : Set (V ⊕ W)) :=
    Finset.mem_coe.mpr (Finset.mem_toRight.mp (Finset.mem_coe.mp hb))
  exact hs ha' hb' (Sum.inr_injective.ne hab) (SimpleGraph.sum_adj_inr.mpr hadj)

/-- **補題 A（`≤`）**：非交和の独立数は和以下。 -/
theorem indepNum_sum_le {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).indepNum ≤ G.indepNum + H.indepNum := by
  refine indepNum_le' ?_
  intro s hs
  have h1 := (isIndepSet_toLeft hs).card_le_indepNum
  have h2 := (isIndepSet_toRight hs).card_le_indepNum
  have h3 := Finset.card_toLeft_add_card_toRight (u := s)
  omega

/-- 左右の独立集合を `disjSum` で貼ると非交和の独立集合。 -/
lemma isIndepSet_disjSum {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : Finset V} {t : Finset W} (hs : G.IsIndepSet (s : Set V))
    (ht : H.IsIndepSet (t : Set W)) :
    (G ⊕g H).IsIndepSet ((s.disjSum t : Finset (V ⊕ W)) : Set (V ⊕ W)) := by
  rintro (a | a) ha (b | b) hb hab hadj
  · exact hs (Finset.mem_coe.mpr (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hb)))
      (fun h => hab (by rw [h])) (SimpleGraph.sum_adj_inl.mp hadj)
  · exact SimpleGraph.not_adj_sum_inl_inr a b hadj
  · exact SimpleGraph.not_adj_sum_inl_inr b a hadj.symm
  · exact ht (Finset.mem_coe.mpr (Finset.inr_mem_disjSum.mp (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (Finset.inr_mem_disjSum.mp (Finset.mem_coe.mp hb)))
      (fun h => hab (by rw [h])) (SimpleGraph.sum_adj_inr.mp hadj)

/-- **補題 A（`≥`）**：非交和の独立数は和以上。 -/
theorem le_indepNum_sum {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    G.indepNum + H.indepNum ≤ (G ⊕g H).indepNum := by
  obtain ⟨s, hs, hsc⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨t, ht, htc⟩ := H.exists_isNIndepSet_indepNum
  have h := (isIndepSet_disjSum hs ht).card_le_indepNum
  rw [Finset.card_disjSum, hsc, htc] at h
  exact h

/-- **補題 A**：非交和の独立数は独立数の和。 -/
theorem indepNum_sum {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).indepNum = G.indepNum + H.indepNum :=
  le_antisymm (indepNum_sum_le G H) (le_indepNum_sum G H)

/-! ## 4. 補題 B：実現の非交和 -/

/-- 第 1 座標を `c` ずらす平行移動。 -/
def transl (c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 + c, x.2)

lemma transl_injective (c : ℝ) : Function.Injective (transl c) := by
  intro x y h
  have h1 : x.1 = y.1 := by
    have := congrArg Prod.fst h
    simp only [transl] at this
    linarith
  have h2 : x.2 = y.2 := by
    have := congrArg Prod.snd h
    simpa only [transl] using this
  exact Prod.ext h1 h2

@[simp] lemma sq2_transl (c : ℝ) (x y : ℝ × ℝ) : sq2 (transl c x) (transl c y) = sq2 x y := by
  simp only [sq2, transl]
  ring

/-- 右側をどれだけ右へずらすか。`max` を使わず絶対値の和で取るので、
  頂点集合が空でも（`Fintype` があれば）そのまま通る。 -/
noncomputable def shift {V W : Type*} [Fintype V] [Fintype W]
    (p : V → ℝ × ℝ) (q : W → ℝ × ℝ) : ℝ :=
  (∑ i : V, |(p i).1|) + (∑ j : W, |(q j).1|) + 1

/-- ずらした後の右側の点は、左側のどの点よりも右にある。 -/
lemma lt_shift {V W : Type*} [Fintype V] [Fintype W] (p : V → ℝ × ℝ) (q : W → ℝ × ℝ)
    (i : V) (j : W) : (p i).1 < ((q j).1 + shift p q) := by
  have hA : (p i).1 ≤ ∑ i : V, |(p i).1| :=
    le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun i : V => |(p i).1|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i))
  have hB : |(q j).1| ≤ ∑ j : W, |(q j).1| :=
    Finset.single_le_sum (f := fun j : W => |(q j).1|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  have hC : -|(q j).1| ≤ (q j).1 := neg_abs_le _
  simp only [shift]
  linarith

/-- **補題 B**：実現の非交和。右側を `shift` だけ平行移動して像の重なりを断つ。 -/
theorem realizV_sum {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {p : V → ℝ × ℝ} {q : W → ℝ × ℝ}
    (hp : RealizV G p) (hq : RealizV H q) :
    RealizV (G ⊕g H) (Sum.elim p (transl (shift p q) ∘ q)) := by
  obtain ⟨hpE, hpI⟩ := hp
  obtain ⟨hqE, hqI⟩ := hq
  constructor
  · rintro (a | a) (b | b) hab
    · exact hpE a b (SimpleGraph.sum_adj_inl.mp hab)
    · exact absurd hab (SimpleGraph.not_adj_sum_inl_inr a b)
    · exact absurd hab.symm (SimpleGraph.not_adj_sum_inl_inr b a)
    · show sq2 (transl (shift p q) (q a)) (transl (shift p q) (q b)) = 1
      rw [sq2_transl]
      exact hqE a b (SimpleGraph.sum_adj_inr.mp hab)
  · rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (hpI hab)
    · exfalso
      have h1 : (p a).1 = ((q b).1 + shift p q) := congrArg Prod.fst hab
      exact absurd h1 (ne_of_lt (lt_shift p q a b))
    · exfalso
      have h1 : (p b).1 = ((q a).1 + shift p q) := congrArg Prod.fst hab.symm
      exact absurd h1 (ne_of_lt (lt_shift p q b a))
    · exact congrArg Sum.inr (hqI (transl_injective (shift p q) hab))

/-- `FGeV` の非交和。 -/
theorem fGeV_sum {V W : Type*} [Fintype V] [Fintype W] {α β : ℕ}
    (hV : FGeV V α) (hW : FGeV W β) : FGeV (V ⊕ W) (α + β) := by
  obtain ⟨G, ⟨p, hp⟩, hα⟩ := hV
  obtain ⟨H, ⟨q, hq⟩, hβ⟩ := hW
  exact ⟨G ⊕g H, ⟨_, realizV_sum hp hq⟩,
    le_trans (indepNum_sum_le G H) (Nat.add_le_add hα hβ)⟩

/-! ## 5. 頂点型の移送と加法定理 -/

/-- `comap` は独立数を増やさない（単射に沿って引き戻すとき）。 -/
theorem indepNum_comap_le {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph W}
    {f : V → W} (hf : Function.Injective f) : (G.comap f).indepNum ≤ G.indepNum := by
  refine indepNum_le' ?_
  intro s hs
  have hind : G.IsIndepSet ((s.map ⟨f, hf⟩ : Finset W) : Set W) := by
    intro a ha b hb hab hadj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    exact hs (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) (fun h => hab (by rw [h]))
      (SimpleGraph.comap_adj.mpr hadj)
  have := hind.card_le_indepNum
  rwa [Finset.card_map] at this

/-- 頂点型 `V` の証人から `Fin n` の証人へ（`Fin n → V` の単射に沿って引き戻す）。 -/
theorem fGe_of_fGeV {n α : ℕ} {V : Type*} [Finite V] {f : Fin n → V}
    (hf : Function.Injective f) (h : FGeV V α) : FGe n α := by
  obtain ⟨G, ⟨p, hpE, hpI⟩, hα⟩ := h
  exact ⟨G.comap f, ⟨p ∘ f, fun i j hij => hpE (f i) (f j) (SimpleGraph.comap_adj.mp hij),
    hpI.comp hf⟩, le_trans (indepNum_comap_le hf) hα⟩

/-- **加法定理**：証人は並べられる。 -/
theorem fGe_add {n₁ n₂ α₁ α₂ : ℕ} (h₁ : FGe n₁ α₁) (h₂ : FGe n₂ α₂) :
    FGe (n₁ + n₂) (α₁ + α₂) :=
  fGe_of_fGeV (f := finSumFinEquiv.symm) finSumFinEquiv.symm.injective
    (fGeV_sum ((fGeV_fin n₁ α₁).mpr h₁) ((fGeV_fin n₂ α₂).mpr h₂))

/-! ## 6. 独立数 `≤ 1`・`≤ 2`（増加組版） -/

/-- 増加 2 点組がどれも辺なら独立数は `≤ 1`。 -/
lemma indepNum_le_one {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ a b : Fin n, a < b → G.Adj a b) : G.indepNum ≤ 1 := by
  refine indepNum_le ?_
  intro s hs
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 2 ≤ s.card by omega)
  have hmem : ∀ i : Fin 2, (t.orderEmbOfFin htc) i ∈ (s : Set (Fin n)) := fun i =>
    Finset.mem_coe.mpr (hts (t.orderEmbOfFin_mem htc i))
  exact hs (hmem 0) (hmem 1)
    (ne_of_lt ((t.orderEmbOfFin htc).strictMono (show (0 : Fin 2) < 1 by decide)))
    (h _ _ ((t.orderEmbOfFin htc).strictMono (show (0 : Fin 2) < 1 by decide)))

/-- 増加 3 点組がどれも辺を含むなら独立数は `≤ 2`。 -/
lemma indepNum_le_two {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ∀ a b c : Fin n, a < b → b < c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c) :
    G.indepNum ≤ 2 := by
  refine indepNum_le ?_
  intro s hs
  by_contra hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 3 ≤ s.card by omega)
  have hmem : ∀ i : Fin 3, (t.orderEmbOfFin htc) i ∈ (s : Set (Fin n)) := fun i =>
    Finset.mem_coe.mpr (hts (t.orderEmbOfFin_mem htc i))
  have key : ∀ i j : Fin 3, i < j →
      ¬ G.Adj ((t.orderEmbOfFin htc) i) ((t.orderEmbOfFin htc) j) := fun i j hij =>
    hs (hmem i) (hmem j) (ne_of_lt ((t.orderEmbOfFin htc).strictMono hij))
  rcases h _ _ _ ((t.orderEmbOfFin htc).strictMono (show (0 : Fin 3) < 1 by decide))
      ((t.orderEmbOfFin htc).strictMono (show (1 : Fin 3) < 2 by decide)) with H | H | H
  exacts [key 0 1 (by decide) H, key 0 2 (by decide) H, key 1 2 (by decide) H]

end HadwigerNelson.Family

/-!
## **部品**：`FGe 7 2`（Moser spindle 単体）と `FGe 3 1`（単位正三角形）。

  証人の段は spindle を「三角形と並べた 10 点」「二つ並べた 14 点」の中でしか扱わなかった。
  族の段の加法定理は部品を並べるので、部品そのものを単体で出しておく必要がある。

  * **spindle**：証人の段の座標 `qA`（の 0–6 番）と辺の検査 `eA_*` をそのまま使う。
    `monoA`（`L = x + 3y` が `ℕ` 上で狭義単調）も再利用できるので、
    単射性は `Fin 7` に制限しただけで出る。独立数 `≤ 2` は増加 3 点組 `C(7,3) = 35` 個の `decide`
  * **三角形**：`(0,0)`・`(1,0)`・`(1/2, √3/2)`。独立数 `≤ 1` は増加 2 点組 3 個の `decide`

  sorry 0・native_decide 不使用。
-/

set_option linter.style.longLine false
set_option linter.unusedTactic false

namespace HadwigerNelson.Family

open HadwigerNelson.Witness

/-! ## 1. Moser spindle 単体（7 点・11 辺・独立数 2） -/

/-- spindle の辺集合（11 辺）。証人の段の `EA` から三角形の 3 辺を落としたもの。 -/
def ES : List (ℕ × ℕ) :=
  [(0,1), (0,3), (0,4), (1,2), (1,4), (1,5), (2,5), (2,6), (3,4), (3,6), (5,6)]

lemma ES_loopless : ∀ i : Fin 7, ¬ adjOf ES i i := by decide

/-- spindle のグラフ。 -/
def GS : SimpleGraph (Fin 7) := graphOf ES ES_loopless

/-- spindle の頂点の位置（証人の段の座標 `qA` の 0–6 番）。 -/
noncomputable def pS : Fin 7 → ℝ × ℝ := fun i => qA (i : ℕ)

lemma ES_edges : ∀ e ∈ ES, sq2 (qA e.1) (qA e.2) = 1 := by
  intro e he
  simp only [ES] at he
  fin_cases he
  exacts [eA_0_1, eA_0_3, eA_0_4, eA_1_2, eA_1_4, eA_1_5, eA_2_5, eA_2_6, eA_3_4, eA_3_6, eA_5_6]

lemma pS_inj : Function.Injective pS :=
  injective_of_strictMono qA monoA

/-- spindle は平面単位距離グラフとして実現される。 -/
theorem realizS : Realiz GS pS :=
  realiz_of_edges ES_edges pS_inj

/-- 増加 3 点組はどれも辺を含む（`Fin 7` の増加 3 点組 35 個）。 -/
theorem tupS : ∀ a b c : Fin 7, a < b → b < c →
    adjOf ES a b ∨ adjOf ES a c ∨ adjOf ES b c := by
  decide

theorem indepS : GS.indepNum ≤ 2 :=
  indepNum_le_two (fun a b c => tupS a b c)

/-- **`f(2) ≥ 7`**：独立数 `≤ 2` の 7 点平面単位距離グラフがある（Moser spindle）。 -/
theorem fGe_7_2 : FGe 7 2 := ⟨GS, ⟨pS, realizS⟩, indepS⟩

/-! ## 2. 単位正三角形（3 点・3 辺・独立数 1） -/

/-- 三角形の辺集合。 -/
def ET : List (ℕ × ℕ) := [(0,1), (0,2), (1,2)]

lemma ET_loopless : ∀ i : Fin 3, ¬ adjOf ET i i := by decide

/-- 三角形のグラフ（`K₃`）。 -/
def GT : SimpleGraph (Fin 3) := graphOf ET ET_loopless

/-- 三角形の座標。`3` 以上の番号は埋め草（単調性を `ℕ` 全体で言うため）。 -/
noncomputable def qT : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (1/2, 1/2 * s3)
  | k => (100 * (k : ℝ), 0)

noncomputable def pT : Fin 3 → ℝ × ℝ := fun i => qT (i : ℕ)

lemma eT_0_1 : sq2 (qT 0) (qT 1) = 1 := by
  simp only [sq2, qT]
  norm_num

lemma eT_0_2 : sq2 (qT 0) (qT 2) = 1 := by
  simp only [sq2, qT]
  linear_combination (1/4) * s3_sq

lemma eT_1_2 : sq2 (qT 1) (qT 2) = 1 := by
  simp only [sq2, qT]
  linear_combination (1/4) * s3_sq

lemma ET_edges : ∀ e ∈ ET, sq2 (qT e.1) (qT e.2) = 1 := by
  intro e he
  simp only [ET] at he
  fin_cases he
  exacts [eT_0_1, eT_0_2, eT_1_2]

lemma monoT : StrictMono (fun k : ℕ => (qT k).1 + 3 * (qT k).2) := by
  apply strictMono_nat_of_lt_succ
  intro k
  match k with
  | 0 =>
      simp only [qT]
      norm_num
  | 1 =>
      simp only [qT]
      norm_num
      linarith [s3_lb]
  | 2 =>
      simp only [qT]
      norm_num
      linarith [s3_ub]
  | (m+3) =>
      simp only [qT]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) m]

lemma pT_inj : Function.Injective pT :=
  injective_of_strictMono qT monoT

theorem realizT : Realiz GT pT :=
  realiz_of_edges ET_edges pT_inj

/-- 増加 2 点組はどれも辺（`Fin 3` の増加 2 点組 3 個）。 -/
theorem tupT : ∀ a b : Fin 3, a < b → adjOf ET a b := by
  decide

theorem indepT : GT.indepNum ≤ 1 :=
  indepNum_le_one (fun a b => tupT a b)

/-- **`f(1) ≥ 3`**：独立数 `≤ 1` の 3 点平面単位距離グラフがある（単位正三角形）。 -/
theorem fGe_3_1 : FGe 3 1 := ⟨GT, ⟨pT, realizT⟩, indepT⟩

/-! ## 3. 陽性対照：独立数はちょうど 2・1 -/

instance : DecidableRel GS.Adj := fun i j => inferInstanceAs (Decidable (adjOf ES i j))
instance : DecidableRel GT.Adj := fun i j => inferInstanceAs (Decidable (adjOf ET i j))

theorem indepS_ge : 2 ≤ GS.indepNum := by
  have h : GS.IsIndepSet ((({0, 2} : Finset (Fin 7))) : Set (Fin 7)) := by decide
  have h2 := h.card_le_indepNum
  rw [show (({0, 2} : Finset (Fin 7))).card = 2 from by decide] at h2
  exact h2

theorem indepS_eq : GS.indepNum = 2 := le_antisymm indepS indepS_ge

theorem indepT_ge : 1 ≤ GT.indepNum := by
  have h : GT.IsIndepSet ((({0} : Finset (Fin 3))) : Set (Fin 3)) := by decide
  have h2 := h.card_le_indepNum
  rw [show (({0} : Finset (Fin 3))).card = 1 from by decide] at h2
  exact h2

theorem indepT_eq : GT.indepNum = 1 := le_antisymm indepT indepT_ge

end HadwigerNelson.Family

/-!
## 総括：`f(2k) ≥ 7k`・`f(2k+1) ≥ 7k+3` を `k` について一本で。

  部品（`FGe 7 2` = Moser spindle・`FGe 3 1` = 単位正三角形）と加法定理
  `FGe n₁ α₁ → FGe n₂ α₂ → FGe (n₁+n₂) (α₁+α₂)` を組むと、下界の族が帰納で出る。

  * `fGe_even k : FGe (7k) (2k)`  ——  **`f(2k) ≥ 7k`**（spindle を `k` 個並べる）
  * `fGe_odd  k : FGe (7k+3) (2k+1)`  ——  **`f(2k+1) ≥ 7k+3`**（さらに三角形を一つ）

  証人の段の `fGe_10_3`・`fGe_14_4` はこの族の `k = 1`（奇）・`k = 2`（偶）にあたる。
  §3 の `example` で、同じ命題を両方の道で埋めて突き合わせてある。

  **Lean の外に残すもの**：`f(α)` そのものの定義。ここで言っているのは
  「独立数 `≤ α` の `n` 点平面単位距離グラフが**存在する**」までで、最大性ではない。
-/

set_option linter.style.longLine false

namespace HadwigerNelson.Family

open HadwigerNelson.Witness

/-! ## 1. 帰納の出発点 -/

/-- `FGe 0 0`：頂点のないグラフ。帰納を `k = 0` から始めるために置く。 -/
theorem fGe_zero : FGe 0 0 := by
  refine ⟨⊥, ⟨fun _ => (0, 0), ?_, ?_⟩, ?_⟩
  · intro i _ hij
    exact absurd hij (by simp)
  · intro i _ _
    exact Fin.elim0 i
  · refine indepNum_le' ?_
    intro s _
    simpa using s.card_le_univ

/-! ## 2. 下界の族 -/

/-- **`f(2k) ≥ 7k`**：Moser spindle を `k` 個、互いに離して並べる。 -/
theorem fGe_even : ∀ k : ℕ, FGe (7 * k) (2 * k)
  | 0 => fGe_zero
  | (k + 1) => by
      have h := fGe_add (fGe_even k) fGe_7_2
      have e1 : 7 * (k + 1) = 7 * k + 7 := by ring
      have e2 : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e1, e2]
      exact h

/-- **`f(2k+1) ≥ 7k+3`**：spindle を `k` 個と単位正三角形を一つ並べる。 -/
theorem fGe_odd (k : ℕ) : FGe (7 * k + 3) (2 * k + 1) :=
  fGe_add (fGe_even k) fGe_3_1

/-- **この段の主定理**：下界の二つの族。 -/
theorem hn_lower_family :
    (∀ k : ℕ, FGe (7 * k) (2 * k)) ∧ (∀ k : ℕ, FGe (7 * k + 3) (2 * k + 1)) :=
  ⟨fGe_even, fGe_odd⟩

/-! ## 3. 証人の段との突き合わせ -/

/-- `f(3) ≥ 10`：証人の段は 10 点のグラフを直に置いた。 -/
example : FGe 10 3 := HadwigerNelson.Witness.fGe_10_3

/-- 同じ命題がこの段の族の `k = 1`（奇）から出る（`7·1+3 = 10`・`2·1+1 = 3`）。 -/
example : FGe 10 3 := fGe_odd 1

/-- `f(4) ≥ 14`：証人の段は 14 点のグラフを直に置いた。 -/
example : FGe 14 4 := HadwigerNelson.Witness.fGe_14_4

/-- 同じ命題がこの段の族の `k = 2`（偶）から出る（`7·2 = 14`・`2·2 = 4`）。 -/
example : FGe 14 4 := fGe_even 2

/-- 族は証人の段の二例より先へ延びる：`f(6) ≥ 21`・`f(5) ≥ 17`・`f(8) ≥ 28`。 -/
example : FGe 21 6 := fGe_even 3
example : FGe 17 5 := fGe_odd 2
example : FGe 28 8 := fGe_even 4

end HadwigerNelson.Family

#print axioms HadwigerNelson.Witness.hn_lower
#print axioms HadwigerNelson.Witness.fGe_10_3
#print axioms HadwigerNelson.Witness.fGe_14_4
#print axioms HadwigerNelson.Witness.realizA
#print axioms HadwigerNelson.Witness.indepA
#print axioms HadwigerNelson.Witness.tupA
#print axioms HadwigerNelson.Witness.pA_inj
#print axioms HadwigerNelson.Witness.EA_edges
#print axioms HadwigerNelson.Witness.monoA
#print axioms HadwigerNelson.Witness.realizB
#print axioms HadwigerNelson.Witness.indepB
#print axioms HadwigerNelson.Witness.tupB
#print axioms HadwigerNelson.Witness.pB_inj
#print axioms HadwigerNelson.Witness.EB_edges
#print axioms HadwigerNelson.Witness.monoB
#print axioms HadwigerNelson.Witness.indepNum_le
#print axioms HadwigerNelson.Witness.indepNum_le_three
#print axioms HadwigerNelson.Witness.indepNum_le_four
#print axioms HadwigerNelson.Witness.realiz_of_edges
#print axioms HadwigerNelson.Witness.injective_of_strictMono
#print axioms HadwigerNelson.Witness.s3_mul_s11
#print axioms HadwigerNelson.Witness.indepA_eq
#print axioms HadwigerNelson.Witness.indepB_eq
#print axioms HadwigerNelson.Family.hn_lower_family
#print axioms HadwigerNelson.Family.fGe_even
#print axioms HadwigerNelson.Family.fGe_odd
#print axioms HadwigerNelson.Family.indepNum_sum
#print axioms HadwigerNelson.Family.indepNum_sum_le
#print axioms HadwigerNelson.Family.le_indepNum_sum
#print axioms HadwigerNelson.Family.isIndepSet_toLeft
#print axioms HadwigerNelson.Family.isIndepSet_toRight
#print axioms HadwigerNelson.Family.isIndepSet_disjSum
#print axioms HadwigerNelson.Family.realizV_sum
#print axioms HadwigerNelson.Family.lt_shift
#print axioms HadwigerNelson.Family.transl_injective
#print axioms HadwigerNelson.Family.sq2_transl
#print axioms HadwigerNelson.Family.fGe_add
#print axioms HadwigerNelson.Family.fGe_of_fGeV
#print axioms HadwigerNelson.Family.fGeV_sum
#print axioms HadwigerNelson.Family.indepNum_comap_le
#print axioms HadwigerNelson.Family.indepNum_le'
#print axioms HadwigerNelson.Family.fGe_7_2
#print axioms HadwigerNelson.Family.fGe_3_1
#print axioms HadwigerNelson.Family.fGe_zero
#print axioms HadwigerNelson.Family.realizS
#print axioms HadwigerNelson.Family.realizT
#print axioms HadwigerNelson.Family.tupS
#print axioms HadwigerNelson.Family.tupT
#print axioms HadwigerNelson.Family.indepS
#print axioms HadwigerNelson.Family.indepT
#print axioms HadwigerNelson.Family.indepS_eq
#print axioms HadwigerNelson.Family.indepT_eq
#print axioms HadwigerNelson.Family.indepNum_le_one
#print axioms HadwigerNelson.Family.indepNum_le_two
