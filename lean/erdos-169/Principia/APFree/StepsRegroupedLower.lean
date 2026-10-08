/-
  結び — **110 段（率基準・主値）の集合 A と、その上の Σ 1/a の下界。**

  100 段（`APFreeWindowsDisjoint`）にあって 110 段に無かった三層を、ここで埋める：
    (1) 集合 A の定義 `setA110 = unionW winsAll110`（頭 Z₀ ＋ 窓 128 個）
    (2) Σ 1/a の下界 `setA110_lower`（3.0085326654815）
    (3) 記録超え `setA110_beats_record`（3.00849 < Σ 1/a）

  これまで 110 段にあったのは (W)（`APFreeStepsSeparated`）と maxelt（`APFreeStepsMaxElement`）だけで、
  **集合として組んで逆数和の下界を出す層が無かった**。八訂 §1.1′ の表が 110 段の行に
  `APFreeWindowsDisjoint` / `APFreeChainRecord` を挙げていたのは誤りで、それらは 100 段ロールアウトの窓
  （`wins50 ++ wins100b`）についてのものである。本ファイルはその欄を埋めるために作った。

  混合深さの葉は 149404（予算 150000）。Python の挟み込み 3.0085326723249 との差は 6.84e-09。
  sorry 0・native_decide 不使用。
-/
import Principia.APFree.BlockBoundsStagesLead
import Principia.APFree.BlockBoundsStagesMid
import Principia.APFree.BlockBoundsStagesRest
import Principia.APFree.StepsRegroupedWindows
import Principia.APFree.BlockBoundsHeadLower
import Principia.APFree.StepsSeparated
import Principia.APFree.StepsMaxElement

namespace APFree.StepsRegrouped

open APFree.BlockBounds APFree.WindowsDisjoint

set_option maxRecDepth 4000000

/-! ## 1. チャンクを連結すると窓の一覧に戻る -/

theorem winsG_map : winsG0.map Prod.fst ++ winsG1.map Prod.fst ++ winsG2.map Prod.fst = wins110 := by rfl

theorem wins110_lower : (43227101765848370641157902854437260459760256556625249544408748581909372694390105515782221143472804 : ℚ) / 10 ^ 100 ≤ sumWin wins110 := by
  have h : sumWin wins110 = sumWin (winsG0.map Prod.fst) + sumWin (winsG1.map Prod.fst) + sumWin (winsG2.map Prod.fst) := by
    rw [← winsG_map, sumWin_append, sumWin_append]
  rw [h]
  have he : (43227101765848370641157902854437260459760256556625249544408748581909372694390105515782221143472804 : ℚ) / 10 ^ 100 = (37924688550629421041273070823940415524943515010446650481463083774329463469512659327712784563404660 : ℚ) / 10 ^ 100 + (5199981032954784321553881424152533573103688763700539159266128322754619532313630296084153465664304 : ℚ) / 10 ^ 100 + (102432182264165278330950606344311361713052782478059903679536484825289692563815891985283114403840 : ℚ) / 10 ^ 100 := by norm_num
  rw [he]
  have h0 := winsG0_lower
  have h1 := winsG1_lower
  have h2 := winsG2_lower
  exact add_le_add (add_le_add h0 h1) h2

/-! ## 2. 集合として組む -/

/-- **構成そのもの**：頭 Z₀ と 110 段 128 個の窓を、一本の一覧にする。
    頭 Z₀ = 1 + B(2,16,0) は `winF (2,16,0,1)` そのものである。 -/
def winsAll110 : List (ℕ × ℕ × ℕ × ℕ) := (2, 16, 0, 1) :: wins110

/-- 110 段の構成が覆う集合 A。 -/
def setA110 : Finset ℕ := unionW winsAll110

theorem winsAll110_p : ∀ w ∈ winsAll110, 1 ≤ w.1 := by decide

set_option maxHeartbeats 4000000 in
/-- **窓は互いに素である**（128 対 ＋ 頭。kernel 評価。最小の隙間は 20171202）。 -/
theorem winsAll110_ord : ordWB winsAll110 = true := by decide

/-- 集合 A の上の逆数和は、頭と窓の逆数和の総和に等しい。 -/
theorem sum_setA110 :
    ∑ x ∈ setA110, (1 : ℚ) / x = (∑ n ∈ Z0F, (1 : ℚ) / n) + sumWin wins110 := by
  have h := sum_set_eq winsAll110 winsAll110_p winsAll110_ord
  rw [setA110, h, winsAll110, sumWin, Z0F_eq_winF, sum_winF]

/-! ## 3. 下界 -/

/-- **本ファイルの結論（110 段の構成そのものについて）**：
    率基準 110 段の Wróblewski 型 3-AP-free 集合 A の逆数和は **3.0085326654815 を超える**。
    これは「窓ごとの逆数和の総和」ではなく、**集合 A の上の Σ 1/n** についての言明である。 -/
theorem setA110_lower : (30085326654815 : ℚ) / 10 ^ 13 < ∑ x ∈ setA110, (1 : ℚ) / x := by
  rw [sum_setA110]
  have h1 : (3004209955304941 : ℚ) / 10 ^ 15 ≤ ∑ n ∈ Z0F, (1 : ℚ) / n := Z0F_lower
  have h2 := wins110_lower
  have h3 : (30085326654815 : ℚ) / 10 ^ 13
      < (3004209955304941 : ℚ) / 10 ^ 15 + (43227101765848370641157902854437260459760256556625249544408748581909372694390105515782221143472804 : ℚ) / 10 ^ 100 := by
    norm_num
  linarith

/-- 記録 3.00849 との比較（集合そのものについて）。 -/
theorem setA110_beats_record : (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ setA110, (1 : ℚ) / x := by
  have h := setA110_lower
  have : (300849 : ℚ) / 10 ^ 5 < (30085326654815 : ℚ) / 10 ^ 13 := by norm_num
  linarith

/-! ## 4. 窓の一覧が、110 段そのものから出ていること

  `wins110` は Python が組み立てたリテラルである。それが本当に 110 段
  （`APFree.StepsSeparated.steps` の鎖と `APFree.StepsMaxElement.steps` のブロック）から出ていることを、
  ここで Lean の中で閉じる。これが無いと「(W) は APFreeStepsSeparated で、窓は別のリテラルで」
  という二つが同じ 110 段を指している保証が、Lean の外（Python）にしか無い。
-/

/-- 段 `(z, t, M)` とブロック `(p, q, r)` から、その段が置く窓を作る。
    offset は置き方の規則そのもの（この構成で使う三つの場合の全部）：

      `M = 1` : `max (2z) (z+t) + 1`（倍加税）
      `M = 2` : `2z+1` と `2z+2t+2`（内側案。`3t < z` のとき）
      `M = 3` : `m + z + 1`・`3m + 2t + z + 3`・`3m + 4t + z + 4`（`m = max z t`。
                Wróblewski の閉じた式＝`APFree.WindowSeparationM3.W3` の左端） -/
def winsOfStep : (ℤ × ℤ × ℕ) → (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ × ℕ)
  | (z, t, M), (p, q, r) =>
      if M = 1 then [(p, q, r, (max (2 * z) (z + t) + 1).toNat)]
      else if M = 2 then [(p, q, r, (2 * z + 1).toNat), (p, q, r, (2 * z + 2 * t + 2).toNat)]
      else if M = 3 then
        [(p, q, r, (max z t + z + 1).toNat),
         (p, q, r, (3 * max z t + 2 * t + z + 3).toNat),
         (p, q, r, (3 * max z t + 4 * t + z + 4).toNat)]
      else []
/-- 鎖の段（`APFree.StepsSeparated.steps`）と、その段のブロック（`APFree.StepsMaxElement.steps` の `(p,q,r)`）の対。 -/
def stepsPaired : List ((ℤ × ℤ × ℕ) × (ℕ × ℕ × ℕ)) :=
  List.zip APFree.StepsSeparated.steps (APFree.StepsMaxElement.steps.map fun s => (s.1, s.2.1, s.2.2.1))

theorem stepsPaired_length : stepsPaired.length = 110 := by decide

/-- **`APFree.StepsSeparated` の t と `APFree.StepsMaxElement` の t は 110 段すべてで一致する**
    （前者は鎖と (W) の出所、後者は maxelt の出所。独立な二つのデータである）。 -/
theorem t_agree :
    (List.zip APFree.StepsSeparated.steps APFree.StepsMaxElement.steps).all
      (fun x => decide (x.1.2.1 = (x.2.2.2.2.1 : ℤ))) = true := by decide

/-- **M = 3 の段は無い**（率基準は M=3 を一度も使わない。ゆえに `winsOfStep` の
    残りの枝に落ちる段が無く、窓の総数は 92 + 2·18 = 128 である）。 -/
theorem no_M3 : APFree.StepsSeparated.steps.all (fun s => decide (s.2.2 = 1 ∨ s.2.2 = 2)) = true := by decide

/-- **本節の結論**：`wins110` は 110 段の鎖とブロックから、置き方の規則どおりに出てくる。 -/
theorem wins110_from_steps :
    (stepsPaired.flatMap fun x => winsOfStep x.1 x.2) = wins110 := by decide

end APFree.StepsRegrouped

/-! ### 公理の確認 -/

#print axioms APFree.StepsRegrouped.setA110_lower
#print axioms APFree.StepsRegrouped.setA110_beats_record
#print axioms APFree.StepsRegrouped.sum_setA110
#print axioms APFree.StepsRegrouped.winsAll110_ord
#print axioms APFree.StepsRegrouped.wins110_from_steps
#print axioms APFree.StepsRegrouped.t_agree
#print axioms APFree.StepsRegrouped.no_M3
