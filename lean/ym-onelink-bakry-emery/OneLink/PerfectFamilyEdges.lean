/-
周期 `L` の格子 `(ZMod L)^d` の上の**辺の族**（`k = 1`・格子ゲージ理論の本来の枡）について、
完全な族が在るか無いかを**周期 `L` と次元 `d` の両方について決めた**一枚。

主定理（`perfectK_one_iff`）：`2 ≤ d` のとき

  周期 `L` の格子に `k=1` の完全な族が在る  ⟺  `d ≤ 4` かつ `2 ∣ L`

`2 ≤ d` は仮定に出してある。`d ≤ 1` では `2`-cell が無いので完全性は空虚に真になり、
⟺ は壊れる（`iff_fails_without_hd`：`d=1`・`L=3` で左辺が真・右辺が偽）。

`import Mathlib` だけで素の `lake env lean` を通る一枚版。`sorry` 0・`native_decide` 不使用。

単独検査の一枚は互いに `import` できないので、必要な定義と定理を原本から**行範囲でそのまま
写した**（下の表。`diff` が空であることを確かめてある）。

| 原本 | 原本の行 | 中身 |
|---|---|---|
| `PerfectFamilyPeriodic.lean` | 71〜100 | `Wp`・`shiftp`・`card_Wp`・`shiftp_bijective`・`sum_shiftp` |
| `PerfectFamilyPeriodic.lean` | 102〜261 | `faceCount`・`PackK` とパッキング上界の一式 |
| `PerfectFamilyPeriodic.lean` | 265〜310 | `V`・`flipAt` 系・`Perfect`・`support`・`powersetCard_univ_eq` |
| `PerfectFamilyPeriodic.lean` | 314〜331 | `PerfectK`・`packK_of_perfectK` |
| `PerfectFamilyPeriodic.lean` | 449〜550 | `supportK`・`total_incidencesK`・`card_supportK_of_perfectK` |
| `PerfectFamilyPeriodic.lean` | 574〜616 | `two_mul_sum_card_slice`・`two_dvd_of_perfectK`・`no_perfectK_of_odd` |
| `PerfectFamilyPeriodic.lean` | 743〜796 | `perfectK_d_le_succ`・`perfectK_d_le`・`no_perfectK_of_lt` ほか |
| `PerfectFamilyPeriodic.lean` | 800〜842 | `par2`・`vOfPar`・`perfectK_of_perfect`・`perfectK_two_iff` |
| `PerfectFamilyBound.lean` | 173〜207 | `sum_pair_faces`・`perfect_one_iff`（`k=1` の言い換え） |
| `PlaquetteCounting.lean` | 170〜178 | `PerfectP`（方向で添字した辺の族の完全性） |
| `PlaquetteCounting.lean` | 183〜191 | `A4`（`d=4`・周期 2 の完全な辺の族） |
| `PlaquetteCounting.lean` | 200 | `A4_perfect` |

写した部分は名前空間だけを `PerfectFamily` に揃えてある。

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/
import Mathlib

/-!
# `k = 1`（辺の族）の完全な族は、周期と次元について完全に決まる

周期 `L` のトーラス `(ℤ/L)^d` の辺を `({μ}, x)`（`μ` は向き・`x` は基点）で表す。
2 次元の面（プラケット）`(T, x)`（`T = {μ,ν}`）の辺は `({ν},x)`・`({ν},x+e_μ)`・
`({μ},x)`・`({μ},x+e_ν)` の 4 本で、辺の族 `I` が**完全**（`PerfectK 1 I`）とは、
どのプラケットもちょうど一本を `I` に持つことをいう。

## 主な結果

* `perfectK_one_iff`：**`2 ≤ d` のとき、完全な族が在る ⟺ `d ≤ 4` かつ `2 ∣ L`**
* `perfectK_one_d4_iff`・`perfectK_one_d3_iff`・`perfectK_one_d2_iff`：
  `d = 4, 3, 2` のそれぞれで「在る ⟺ `2 ∣ L`」
* `no_perfectK_one_of_five_le`：`5 ≤ d` なら**どの周期にも**無い
* `bound_sharp_k1`：**`k = 1` では上界 `d ≤ 3k+1` は鋭い**（`d = 4` で達成される）
* `exists_perfectK_one_infinite`：在る側は `NeZero L` を使っていないので、`L = 0`
  （`ZMod 0 = ℤ`、無限格子 `ℤ^d`）でも `d = 2, 3, 4` の族が在る
* `perfect_edge4`：`PlaquetteCounting.A4` を対の型へ移した族（二通りの道で閉じてある）
* `perfect_edge3`：`d = k+2 = 3` の三角ガジェット、`perfect_edge2`：`d = k+1 = 2` の端

## 言っていないこと

* **`2 ≤ d` は落とせない**（`iff_fails_without_hd`）。`d ≤ 1` では `2`-cell が無く空虚に真
* **分類でない。**完全な族の個数や型については何も言っていない
* `k ≥ 2` については何も新しく言っていない（`k=2, d=4` は原本の `perfectK_k2_d4_iff`）
* **ヤン–ミルズの本体への主張は無い。**組合せの補題である
-/

namespace PerfectFamily

variable {d L : ℕ}

/-! ## §0 写した定義（周期格子の側） -/

/-- 周期格子の頂点。 -/
abbrev Wp (d L : ℕ) : Type := Fin d → ZMod L

/-- 第 `i` 座標を 1 だけ進める（`x ↦ x + e_i`）。 -/
def shiftp (x : Wp d L) (i : Fin d) : Wp d L := Function.update x i (x i + 1)

/-- 周期格子の頂点の数は `L^d`。 -/
theorem card_Wp [NeZero L] : Fintype.card (Wp d L) = L ^ d := by
  simp [Wp, ZMod.card]

/-- `x ↦ x + e_ν` は `(ZMod L)^d` の上の全単射（逆は `x ↦ x − e_ν`）。 -/
theorem shiftp_bijective [NeZero L] (ν : Fin d) :
    Function.Bijective (fun x : Wp d L => shiftp x ν) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => Function.update y ν (y ν - 1), ?_, ?_⟩
  · intro x
    funext i
    rcases eq_or_ne i ν with h | h
    · subst h; simp [shiftp]
    · simp [shiftp, h]
  · intro y
    funext i
    rcases eq_or_ne i ν with h | h
    · subst h; simp [shiftp]
    · simp [shiftp, h]

/-- 平行移動での添字の付け替え：`∑_x f(x + e_ν) = ∑_x f(x)`。 -/
theorem sum_shiftp [NeZero L] (f : Wp d L → ℕ) (ν : Fin d) :
    ∑ x : Wp d L, f (shiftp x ν) = ∑ x : Wp d L, f x :=
  Fintype.sum_bijective _ (shiftp_bijective ν) _ _ (fun _ => rfl)

/-- `(k+1)`-cell `(T, x)` の面 `ν` に載っている `I` の個数（`(T\{ν}, x)` と `(T\{ν}, x+e_ν)`）。 -/
def faceCount (I : Finset (Fin d) → Wp d L → Bool) (T : Finset (Fin d)) (x : Wp d L)
    (ν : Fin d) : ℕ :=
  (I (T.erase ν) x).toNat + (I (T.erase ν) (shiftp x ν)).toNat

/--
`PackK m I`：`(m+1)`-cell の族 `I` が、どの `(m+2)`-cell も高々一つの面しか含まない。
`m = 0` が `PlaquettePacking.AtMostOne`（プラケットと辺）に当たる。
-/
def PackK (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) : Prop :=
  ∀ T : Finset (Fin d), T.card = m + 2 → ∀ x : Wp d L,
    ∑ ν ∈ T, faceCount I T x ν ≤ 1

instance instDecidablePackK [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Decidable (PackK m I) := by
  unfold PackK; infer_instance

/--
**芯 (i)**：同じ基点 `x` で選ばれた二つの `(m+1)`-cell は、`m` 個の方向を共有できない。
`T = S ∪ S'` は `(m+2)`-cell で、`S = T \ {a}`・`S' = T \ {b}`（`a ≠ b`）はその面だから。
（`S ≠ S'` は仮定に要らない——`|S ∩ S'| = m < m+1 = |S|` から従う。）
-/
theorem not_share_m [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool} (h : PackK m I)
    {S S' : Finset (Fin d)} {x : Wp d L} (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (hint : (S ∩ S').card = m) (h1 : I S x = true) (h2 : I S' x = true) :
    False := by
  classical
  have hUI := Finset.card_union_add_card_inter S S'
  have hUcard : (S ∪ S').card = m + 2 := by omega
  obtain ⟨a, ha, hins⟩ : ∃ a ∉ S, insert a S = S ∪ S' :=
    Finset.exists_eq_insert_iff.2 ⟨Finset.subset_union_left, by omega⟩
  obtain ⟨b, hb, hins'⟩ : ∃ b ∉ S', insert b S' = S ∪ S' :=
    Finset.exists_eq_insert_iff.2 ⟨Finset.subset_union_right, by omega⟩
  have haT : a ∈ S ∪ S' := hins ▸ Finset.mem_insert_self a S
  have hbT : b ∈ S ∪ S' := hins' ▸ Finset.mem_insert_self b S'
  have hea : (S ∪ S').erase a = S := by rw [← hins, Finset.erase_insert ha]
  have heb : (S ∪ S').erase b = S' := by rw [← hins', Finset.erase_insert hb]
  have hab : a ≠ b := by
    intro hh
    subst hh
    rcases Finset.mem_union.1 haT with h' | h'
    · exact ha h'
    · exact hb h'
  have hsum := h (S ∪ S') hUcard x
  have hfa : 1 ≤ faceCount I (S ∪ S') x a := by simp [faceCount, hea, h1]
  have hfb : 1 ≤ faceCount I (S ∪ S') x b := by simp [faceCount, heb, h2]
  have hsplit : faceCount I (S ∪ S') x a + ∑ ν ∈ (S ∪ S').erase a, faceCount I (S ∪ S') x ν
      = ∑ ν ∈ S ∪ S', faceCount I (S ∪ S') x ν :=
    Finset.add_sum_erase _ _ haT
  have hbmem : b ∈ (S ∪ S').erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hbT⟩
  have hfble : faceCount I (S ∪ S') x b ≤ ∑ ν ∈ (S ∪ S').erase a, faceCount I (S ∪ S') x ν :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hbmem
  omega

/-- 選ばれた二つの `(m+1)`-cell の `m`-部分集合の族は互いに素（芯 (i) の言い換え）。 -/
theorem disjoint_powersetCard_of_pack [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (h : PackK m I) {x : Wp d L} {S S' : Finset (Fin d)}
    (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (h1 : I S x = true) (h2 : I S' x = true) (hne : S ≠ S') :
    Disjoint (S.powersetCard m) (S'.powersetCard m) := by
  classical
  rw [Finset.disjoint_left]
  intro R hR hR'
  rw [Finset.mem_powersetCard] at hR hR'
  have hsub : R ⊆ S ∩ S' := Finset.subset_inter hR.1 hR'.1
  have hge : m ≤ (S ∩ S').card := by
    rw [← hR.2]; exact Finset.card_le_card hsub
  have hlecard : (S ∩ S').card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hle : (S ∩ S').card ≤ m := by
    by_contra hc
    have h5 : S ∩ S' = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h6 : S ⊆ S' := by rw [← h5]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le h6 (by omega))
  exact not_share_m h hS hS' (by omega) h1 h2

/-- 基点 `x` で選ばれた `(m+1)`-cell の方向集合の族 `F(x)`。 -/
def cellsAt [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) (x : Wp d L) :
    Finset (Finset (Fin d)) :=
  Finset.univ.filter (fun S => S.card = m + 1 ∧ I S x = true)

/-- **基点ごとの上界**：`k·|F(x)| ≤ C(d, k−1)`（`k = m+1`）。
`F(x)` の成員の `m`-部分集合は各 `m+1` 個あって互いに素で、全部 `Fin d` の `m`-部分集合。 -/
theorem card_cellsAt_le [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (h : PackK m I) (x : Wp d L) :
    (m + 1) * (cellsAt m I x).card ≤ d.choose m := by
  classical
  have hmem : ∀ S ∈ cellsAt m I x, S.card = m + 1 ∧ I S x = true := by
    intro S hS
    simpa [cellsAt] using hS
  have hdisj : ((cellsAt m I x : Finset (Finset (Fin d))) : Set (Finset (Fin d))).PairwiseDisjoint
      (fun S => S.powersetCard m) := by
    intro S hS S' hS' hne
    simp only [Function.onFun]
    have hSm := hmem S (Finset.mem_coe.1 hS)
    have hS'm := hmem S' (Finset.mem_coe.1 hS')
    exact disjoint_powersetCard_of_pack h hSm.1 hS'm.1 hSm.2 hS'm.2 hne
  have hcard : ((cellsAt m I x).biUnion (fun S => S.powersetCard m)).card
      = ∑ S ∈ cellsAt m I x, (S.powersetCard m).card := Finset.card_biUnion hdisj
  have hterm : ∀ S ∈ cellsAt m I x, (S.powersetCard m).card = m + 1 := by
    intro S hS
    rw [Finset.card_powersetCard, (hmem S hS).1, Nat.choose_succ_self_right]
  have hsum : ∑ S ∈ cellsAt m I x, (S.powersetCard m).card
      = ∑ _S ∈ cellsAt m I x, (m + 1) := Finset.sum_congr rfl hterm
  have hsub : (cellsAt m I x).biUnion (fun S => S.powersetCard m)
      ⊆ (Finset.univ : Finset (Fin d)).powersetCard m := by
    intro R hR
    obtain ⟨S, _, hRS⟩ := Finset.mem_biUnion.1 hR
    rw [Finset.mem_powersetCard] at hRS ⊢
    exact ⟨Finset.subset_univ R, hRS.2⟩
  calc (m + 1) * (cellsAt m I x).card
      = ((cellsAt m I x).biUnion (fun S => S.powersetCard m)).card := by
        rw [hcard, hsum, Finset.sum_const, smul_eq_mul]; ring
    _ ≤ ((Finset.univ : Finset (Fin d)).powersetCard m).card := Finset.card_le_card hsub
    _ = d.choose m := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- 選ばれた `(m+1)`-cell の全体（方向集合と基点の組）。 -/
def cellSet [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Finset (Finset (Fin d) × Wp d L) :=
  Finset.univ.filter (fun p => p.1.card = m + 1 ∧ I p.1 p.2 = true)

theorem card_cellSet_eq_sum [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    (cellSet m I).card = ∑ x : Wp d L, (cellsAt m I x).card := by
  classical
  rw [cellSet, Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun x _ => by rw [cellsAt, Finset.card_filter]

/--
**`k`-cell 版の上界**（`k = m+1`）：`k·|I| ≤ L^d·C(d, k−1)`。
`k`-cell の総数は `L^d·C(d,k)` なので、密度は `C(d,k−1)/(k·C(d,k)) = 1/(d−k+1)` 以下。
-/
theorem card_cellSet_le [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool} (h : PackK m I) :
    (m + 1) * (cellSet m I).card ≤ L ^ d * d.choose m := by
  rw [card_cellSet_eq_sum, Finset.mul_sum]
  calc ∑ x : Wp d L, (m + 1) * (cellsAt m I x).card
      ≤ ∑ _x : Wp d L, d.choose m := Finset.sum_le_sum fun x _ => card_cellsAt_le h x
    _ = L ^ d * d.choose m := by
        rw [Finset.sum_const, Finset.card_univ, card_Wp, smul_eq_mul]

/-- 陽性対照（`k = 1` への特殊化）：`m = 0` では `|I| ≤ L^d`。
パッキングの頂点の上界（`card_edgeSet_le`）と同じ値で、そちらとは別の道（`m`-部分集合の
互いに素性）で出ている。 -/
theorem card_cellSet_le_zero [NeZero L] {I : Finset (Fin d) → Wp d L → Bool} (h : PackK 0 I) :
    (cellSet 0 I).card ≤ L ^ d := by
  have h1 := card_cellSet_le h
  simpa using h1

/-- 陽性対照（自明な側）：空の族はどんな `m` でもパッキング。 -/
theorem packK_empty [NeZero L] (m : ℕ) :
    PackK (d := d) (L := L) m (fun _ _ => false) := by
  intro T _ x
  simp [faceCount]

/-- 陰性対照：`d = 2`・`L = 2`・`m = 0` で全部の 1-cell を採る族はパッキングでない
（`PackK 0` は空虚な条件ではない——`|T| = 2` の `T` が実在する）。 -/
theorem not_packK_full : ¬ PackK (d := 2) (L := 2) 0 (fun _ _ => true) := by
  decide

/-- 陰性対照：`d = 3`・`L = 2`・`m = 1`（`k = 2`）でも全部採る族はパッキングでない。 -/
theorem not_packK_full_k2 : ¬ PackK (d := 3) (L := 2) 1 (fun _ _ => true) := by
  decide

/-! ## §0b 写した定義（周期 2 の側・`Perfect` と `k=1` の言い換えに使う） -/

/-- 周期格子 `(ℤ/2)^d` の頂点。 -/
abbrev V (d : ℕ) : Type := Fin d → Bool

/-- 第 `i` 座標を反転する（`x ↦ x + e_i`）。 -/
def flipAt (x : V d) (i : Fin d) : V d := Function.update x i (!x i)

@[simp] lemma flipAt_self (x : V d) (i : Fin d) : flipAt x i i = !x i := by
  simp [flipAt]

@[simp] lemma flipAt_of_ne (x : V d) {i j : Fin d} (h : j ≠ i) : flipAt x i j = x j :=
  Function.update_of_ne h _ _

lemma flipAt_flipAt (x : V d) (i : Fin d) : flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipAt_of_ne _ h]

lemma flipAt_ne (x : V d) (i : Fin d) : flipAt x i ≠ x := by
  intro h
  have h1 : flipAt x i i = x i := by rw [h]
  simp at h1

/--
`k`-cell は `(S, y)`（`S ⊆ [d]`・`|S| = k`・`y ∈ F_2^d`）。
`(k+1)`-cell `(T, y)` の面は `ν ∈ T` ごとに `(T∖ν, y)` と `(T∖ν, y⊕e_ν)` の `2(k+1)` 枚。

`Perfect k A`：どの `(k+1)`-cell もちょうど一枚の面を `A` に持つ。
-/
def Perfect (k : ℕ) (A : Finset (Fin d) × V d → Bool) : Prop :=
  ∀ T : Finset (Fin d), T.card = k + 1 → ∀ y : V d,
    ∑ ν ∈ T, ((A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat) = 1

instance instDecidablePerfect (k : ℕ) (A : Finset (Fin d) × V d → Bool) :
    Decidable (Perfect k A) := by
  unfold Perfect; infer_instance

/-- `A` に入る `k`-cell の集合。 -/
def support (A : Finset (Fin d) × V d → Bool) (k : ℕ) : Finset (Finset (Fin d) × V d) :=
  Finset.univ.filter (fun c => c.1.card = k ∧ A c = true)

lemma powersetCard_univ_eq (k : ℕ) :
    Finset.powersetCard k (Finset.univ : Finset (Fin d))
      = Finset.univ.filter (fun S : Finset (Fin d) => S.card = k) := by
  ext S
  simp

/-! ## §0c 写した定義（`PerfectK`） -/

/--
`PerfectK k I`：周期 `L` の格子で、どの `(k+1)`-cell `(T, x)` も、その面
（`ν ∈ T` ごとの `(T∖ν, x)` と `(T∖ν, x+e_ν)`）のうち**ちょうど一枚**を `I` に持つ。
`PackK m` の `≤ 1` を `= 1` にしたもの。添字は胞体の大きさで直に付けるので、
`PackK m` に当たるのは `PerfectK (m+1)` である。
-/
def PerfectK (k : ℕ) (I : Finset (Fin d) → Wp d L → Bool) : Prop :=
  ∀ T : Finset (Fin d), T.card = k + 1 → ∀ x : Wp d L,
    ∑ ν ∈ T, faceCount I T x ν = 1

instance instDecidablePerfectK [NeZero L] (k : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Decidable (PerfectK k I) := by
  unfold PerfectK; infer_instance

/-- 完全な族はパッキングである（`= 1` を `≤ 1` に緩めるだけ）。 -/
theorem packK_of_perfectK {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (h : PerfectK (m + 1) I) : PackK m I :=
  fun T hT x => le_of_eq (h T (by omega) x)

/-! ## §0d 写した定理（数え上げ `2(k+1)·|I| = C(d,k)·L^d`） -/

/-- `I` に入る `k`-cell の集合（`cellSet` を胞体の大きさ `k` で直に添字したもの）。 -/
def supportK [NeZero L] (k : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Finset (Finset (Fin d) × Wp d L) :=
  Finset.univ.filter (fun p => p.1.card = k ∧ I p.1 p.2 = true)

theorem supportK_eq_cellSet [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    supportK (m + 1) I = cellSet m I := rfl

theorem supportK_card_eq [NeZero L] (I : Finset (Fin d) → Wp d L → Bool) (k : ℕ) :
    (supportK k I).card
      = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)),
          ∑ x : Wp d L, (I S x).toNat := by
  classical
  rw [supportK, Finset.card_filter, Fintype.sum_prod_type, powersetCard_univ_eq,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : S.card = k
  · simp only [h, if_true, true_and]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases hI : I S x with _ | _ <;> simp
  · simp [h]

/-- 入射の数え上げ：`(k+1)`-cell の側から数えた面の総数は、`I` の `k`-cell の側から
数えた `2(d−k)` 倍に等しい。**`I` に仮定は要らない。**使うのは平行移動
`x ↦ x + e_ν` が頂点の上の全単射であることだけで、`L` に条件は要らない。 -/
theorem total_incidencesK [NeZero L] (I : Finset (Fin d) → Wp d L → Bool) (k : ℕ) :
    ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)), ∑ x : Wp d L,
        ∑ ν ∈ T, faceCount I T x ν
      = 2 * (d - k) * (supportK k I).card := by
  classical
  simp only [faceCount]
  rw [Finset.sum_comm]
  have key : ∀ x : Wp d L,
      ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)),
          ∑ ν ∈ T, ((I (T.erase ν) x).toNat + (I (T.erase ν) (shiftp x ν)).toNat)
        = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)),
            ∑ ν ∈ Sᶜ, ((I S x).toNat + (I S (shiftp x ν)).toNat) := by
    intro x
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p => ⟨p.1.erase p.2, p.2⟩) (fun p => ⟨insert p.2 p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨T, ν⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard_univ] at hp ⊢
      refine ⟨?_, ?_⟩
      · rw [Finset.card_erase_of_mem hp.2, hp.1]; rfl
      · simp [Finset.mem_compl]
    · rintro ⟨S, ν⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_powersetCard_univ, Finset.mem_compl] at hp ⊢
      exact ⟨by rw [Finset.card_insert_of_notMem hp.2, hp.1], Finset.mem_insert_self _ _⟩
    · rintro ⟨T, ν⟩ hp
      simp only [Finset.mem_sigma] at hp
      simp [Finset.insert_erase hp.2]
    · rintro ⟨S, ν⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_compl] at hp
      simp [Finset.erase_insert hp.2]
    · rintro ⟨T, ν⟩ _
      rfl
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  rw [Finset.sum_comm]
  rw [supportK_card_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.sum_comm]
  have hcard : (Sᶜ : Finset (Fin d)).card = d - k := by
    rw [Finset.card_compl, Finset.mem_powersetCard_univ.1 hS]
    simp
  have step : ∀ ν ∈ (Sᶜ : Finset (Fin d)),
      ∑ x : Wp d L, ((I S x).toNat + (I S (shiftp x ν)).toNat)
        = 2 * ∑ x : Wp d L, (I S x).toNat := by
    intro ν _
    rw [Finset.sum_add_distrib, sum_shiftp (fun y => (I S y).toNat) ν]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_const, hcard]
  ring

/--
**(1) 完全な族の大きさ**：`k+1 ≤ d` のとき `2(k+1)·|I| = C(d,k)·L^d`。
密度はちょうど `1/(2(k+1))` で、`d` にも `L` にも依らない。
-/
theorem card_supportK_of_perfectK [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK k I) :
    2 * (k + 1) * (supportK k I).card = Nat.choose d k * L ^ d := by
  classical
  have h1 : ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)), ∑ x : Wp d L,
      ∑ ν ∈ T, faceCount I T x ν = Nat.choose d (k + 1) * L ^ d := by
    have hinner : ∀ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)),
        (∑ x : Wp d L, ∑ ν ∈ T, faceCount I T x ν) = L ^ d := by
      intro T hT
      rw [Finset.sum_congr rfl (fun x _ => hI T (Finset.mem_powersetCard_univ.1 hT) x),
        Finset.sum_const, Finset.card_univ, card_Wp, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [total_incidencesK] at h1
  have h2 : (d - k) * (2 * (k + 1) * (supportK k I).card)
      = (d - k) * (Nat.choose d k * L ^ d) := by
    calc (d - k) * (2 * (k + 1) * (supportK k I).card)
        = (k + 1) * (2 * (d - k) * (supportK k I).card) := by ring
      _ = (k + 1) * (Nat.choose d (k + 1) * L ^ d) := by rw [h1]
      _ = (Nat.choose d (k + 1) * (k + 1)) * L ^ d := by ring
      _ = (Nat.choose d k * (d - k)) * L ^ d := by rw [Nat.choose_succ_right_eq]
      _ = (d - k) * (Nat.choose d k * L ^ d) := by ring
  have hpos : 0 < d - k := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos h2

/-! ## §0e 写した定理（層ごとの等式と「周期が奇数なら無い」） -/

/--
**(I) 層ごとの等式**：`(k+1)`-集合 `T` を固定して完全性の等式を `x` 全体で足すと、
`x ↦ x + e_ν` が全単射だから面の第二枚は第一枚と同じ個数を数え、
`2·Σ_{ν∈T} |I_{T∖ν}| = L^d`。**`T` ごとに成り立つ**（`k`・`d` に依らない）。
-/
theorem two_mul_sum_card_slice [NeZero L] {k : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (hI : PerfectK k I) {T : Finset (Fin d)} (hT : T.card = k + 1) :
    2 * ∑ ν ∈ T, (∑ x : Wp d L, (I (T.erase ν) x).toNat) = L ^ d := by
  classical
  have htot : (∑ x : Wp d L, ∑ ν ∈ T, faceCount I T x ν) = L ^ d := by
    rw [Finset.sum_congr rfl (fun x _ => hI T hT x), Finset.sum_const, Finset.card_univ,
      card_Wp, smul_eq_mul, mul_one]
  have hswap : (∑ x : Wp d L, ∑ ν ∈ T, faceCount I T x ν)
      = ∑ ν ∈ T, ∑ x : Wp d L, faceCount I T x ν := Finset.sum_comm
  have hslice : ∀ ν ∈ T, (∑ x : Wp d L, faceCount I T x ν)
      = 2 * ∑ x : Wp d L, (I (T.erase ν) x).toNat := by
    intro ν _
    simp only [faceCount]
    rw [Finset.sum_add_distrib, sum_shiftp (fun y => (I (T.erase ν) y).toNat) ν]
    ring
  calc 2 * ∑ ν ∈ T, (∑ x : Wp d L, (I (T.erase ν) x).toNat)
      = ∑ ν ∈ T, 2 * ∑ x : Wp d L, (I (T.erase ν) x).toNat := by rw [Finset.mul_sum]
    _ = ∑ ν ∈ T, ∑ x : Wp d L, faceCount I T x ν :=
        Finset.sum_congr rfl fun ν hν => (hslice ν hν).symm
    _ = ∑ x : Wp d L, ∑ ν ∈ T, faceCount I T x ν := hswap.symm
    _ = L ^ d := htot

/-- 系：完全な族が在れば `2 ∣ L^d`、ゆえに `2 ∣ L`。 -/
theorem two_dvd_of_perfectK [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK k I) : 2 ∣ L := by
  classical
  obtain ⟨T, -, hT⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d))) (n := k + 1)
      (by simpa using hk)
  have h := two_mul_sum_card_slice hI hT
  exact Nat.prime_two.dvd_of_dvd_pow ⟨_, h.symm⟩

/-- **周期が奇数なら完全な族は無い**（`k`・`d` に依らない。`k+1 ≤ d` は要る
——`(k+1)`-cell が一つも無ければ完全性は空虚に真）。 -/
theorem no_perfectK_of_odd [NeZero L] {k : ℕ} (hk : k + 1 ≤ d) (hL : ¬ (2 ∣ L)) :
    ¬ ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK k I := by
  rintro ⟨I, hI⟩
  exact hL (two_dvd_of_perfectK hk I hI)

/-! ## §0f 写した定理（上界 `d ≤ 3k+1`） -/

/-- **主定理（`k = m+1` の形）**：周期 `L` の格子で `(m+1)`-cell の完全な族が在れば
`d ≤ 3(m+1)+1`。 -/
theorem perfectK_d_le_succ [NeZero L] {m : ℕ} (hk : m + 2 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK (m + 1) I) :
    d ≤ 3 * (m + 1) + 1 := by
  have hE : 2 * (m + 1 + 1) * (supportK (m + 1) I).card = Nat.choose d (m + 1) * L ^ d :=
    card_supportK_of_perfectK (by omega) I hI
  have hP : (m + 1) * (cellSet m I).card ≤ L ^ d * d.choose m :=
    card_cellSet_le (packK_of_perfectK hI)
  rw [← supportK_eq_cellSet] at hP
  have hkey : (Nat.choose d m * L ^ d) * (d - m)
      ≤ (Nat.choose d m * L ^ d) * (2 * (m + 2)) := by
    calc (Nat.choose d m * L ^ d) * (d - m)
        = (Nat.choose d m * (d - m)) * L ^ d := by ring
      _ = (Nat.choose d (m + 1) * (m + 1)) * L ^ d := by rw [Nat.choose_succ_right_eq]
      _ = (m + 1) * (Nat.choose d (m + 1) * L ^ d) := by ring
      _ = (m + 1) * (2 * (m + 1 + 1) * (supportK (m + 1) I).card) := by rw [hE]
      _ = (2 * (m + 2)) * ((m + 1) * (supportK (m + 1) I).card) := by ring
      _ ≤ (2 * (m + 2)) * (L ^ d * d.choose m) := Nat.mul_le_mul_left _ hP
      _ = (Nat.choose d m * L ^ d) * (2 * (m + 2)) := by ring
  have hc : 0 < Nat.choose d m := Nat.choose_pos (by omega)
  have hL : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  have hpos : 0 < Nat.choose d m * L ^ d := Nat.mul_pos hc hL
  have hfin := Nat.le_of_mul_le_mul_left hkey hpos
  omega

/--
**主定理**：周期 `L` の格子で `1 ≤ k` かつ `k+1 ≤ d` のとき、`k`-cell の完全な族が
在れば `d ≤ 3k+1`。**周期 `L` には条件が要らない**（`NeZero L` は頂点の有限性のため）。
-/
theorem perfectK_d_le [NeZero L] {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK k I) : d ≤ 3 * k + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact perfectK_d_le_succ (by omega) I hI

/-- **非存在**：`3k+1 < d` なら、**どの周期の格子にも**完全な族は無い。 -/
theorem no_perfectK_of_lt [NeZero L] {k : ℕ} (hk1 : 1 ≤ k) (hd : 3 * k + 1 < d) :
    ¬ ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK k I := by
  rintro ⟨I, hI⟩
  have := perfectK_d_le hk1 (by omega) I hI
  omega

/-- `k = 1` への特殊化：辺の族（プラケットごとにちょうど一本）は `d ≤ 4` でしか在らない。
`PlaquetteCounting.perfect_torus_d_le_four` と同じ値。 -/
theorem perfectK_one_d_le_four [NeZero L] (hd : 2 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK 1 I) : d ≤ 4 := by
  have := perfectK_d_le (k := 1) le_rfl (by omega) I hI
  omega

/-- 比べた不等式そのもの（等号になるのは `d = 3k+1` のときだけ、という形）。 -/
theorem perfectK_sub_le [NeZero L] {m : ℕ} (hk : m + 2 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK (m + 1) I) : d - m ≤ 2 * (m + 2) := by
  have := perfectK_d_le_succ hk I hI
  omega

/-! ## §0g 写した定理（偶奇による持ち上げ `perfectK_of_perfect`） -/

/-- `2 ∣ L` のときの偶奇（環準同型 `ZMod L → ZMod 2` を通す）。 -/
def par2 (h : 2 ∣ L) (a : ZMod L) : Bool := decide (ZMod.castHom h (ZMod 2) a = 1)

theorem par2_add_one (h : 2 ∣ L) (a : ZMod L) : par2 h (a + 1) = !par2 h a := by
  have hb : ∀ b : ZMod 2, decide (b + 1 = 1) = !decide (b = 1) := by decide
  simp only [par2, map_add, map_one]
  exact hb _

/-- 偶奇で周期 `L` の頂点を周期 2 の頂点へ潰す写像。 -/
def vOfPar (h : 2 ∣ L) (x : Wp d L) : V d := fun i => par2 h (x i)

theorem vOfPar_shiftp (h : 2 ∣ L) (x : Wp d L) (ν : Fin d) :
    vOfPar h (shiftp x ν) = flipAt (vOfPar h x) ν := by
  funext i
  rcases eq_or_ne i ν with rfl | hne
  · simp [vOfPar, shiftp, par2_add_one]
  · simp [vOfPar, shiftp, Function.update_of_ne hne, flipAt_of_ne _ hne]

/-- **存在の側**：`2 ∣ L` なら、周期 2 の完全な族から周期 `L` の完全な族が作れる
（偶奇で引き戻すだけ）。ゆえに `PerfectK` は `2 ∣ L` のどの周期でも空虚でない。 -/
theorem perfectK_of_perfect (h : 2 ∣ L) {k : ℕ} (A : Finset (Fin d) × V d → Bool)
    (hA : Perfect k A) : PerfectK k (fun S x => A (S, vOfPar h x)) := by
  intro T hT x
  simp only [faceCount, vOfPar_shiftp]
  exact hA T hT (vOfPar h x)

theorem vOfPar_two_surjective : Function.Surjective (vOfPar (d := d) (dvd_refl 2)) := by
  intro y
  refine ⟨fun i => if y i then 1 else 0, ?_⟩
  have h : ∀ b : Bool, par2 (dvd_refl 2) (if b then (1 : ZMod 2) else 0) = b := by decide
  funext i
  simpa [vOfPar] using h (y i)

/-- **`L = 2` では `PerfectFamilyBound.lean` の `Perfect` と同じ内容**（両向き）。 -/
theorem perfectK_two_iff (k : ℕ) (A : Finset (Fin d) × V d → Bool) :
    PerfectK k (fun S x => A (S, vOfPar (dvd_refl 2) x)) ↔ Perfect k A := by
  constructor
  · intro h T hT y
    obtain ⟨x, hx⟩ := vOfPar_two_surjective (d := d) y
    have hsum := h T hT x
    simp only [faceCount, vOfPar_shiftp, hx] at hsum
    exact hsum
  · exact fun hA => perfectK_of_perfect (dvd_refl 2) A hA

/-! ## §0h 写した定理（`k = 1` の言い換え `perfect_one_iff`） -/

/-- `2`-cell `{μ, ν}` の 4 枚の面の並べ替え。 -/
lemma sum_pair_faces (A : Finset (Fin d) × V d → Bool) {μ ν : Fin d} (h : μ ≠ ν) (z : V d) :
    ∑ i ∈ ({μ, ν} : Finset (Fin d)),
        ((A ((({μ, ν} : Finset (Fin d))).erase i, z)).toNat
          + (A ((({μ, ν} : Finset (Fin d))).erase i, flipAt z i)).toNat)
      = (A ({ν}, z)).toNat + (A ({ν}, flipAt z μ)).toNat
        + (A ({μ}, z)).toNat + (A ({μ}, flipAt z ν)).toNat := by
  rw [Finset.sum_pair h]
  have e1 : ({μ, ν} : Finset (Fin d)).erase μ = {ν} := by
    rw [Finset.erase_insert (by simp [h])]
  have e2 : ({μ, ν} : Finset (Fin d)).erase ν = {μ} := by
    rw [Finset.erase_insert_of_ne h, Finset.erase_singleton]
    simp
  rw [e1, e2]
  omega

/-- **`k = 1` のときの言い換え**：`Perfect 1 A` は、方向 `μ` と位置 `z` で辺を表したときの
「2 次元の面 `(μ, ν, z)` の 4 本 `(μ,z)`・`(μ,z+e_ν)`・`(ν,z)`・`(ν,z+e_μ)` のうち
ちょうど一本」に等しい。 -/
theorem perfect_one_iff (A : Finset (Fin d) × V d → Bool) :
    Perfect 1 A ↔ ∀ μ ν : Fin d, μ ≠ ν → ∀ z : V d,
      (A ({μ}, z)).toNat + (A ({μ}, flipAt z ν)).toNat
        + (A ({ν}, z)).toNat + (A ({ν}, flipAt z μ)).toNat = 1 := by
  constructor
  · intro hA μ ν h z
    have hcard : ({μ, ν} : Finset (Fin d)).card = 1 + 1 := Finset.card_pair h
    have hsum := hA {μ, ν} hcard z
    rw [sum_pair_faces A h z] at hsum
    omega
  · intro hA T hT y
    have hT2 : T.card = 2 := by omega
    obtain ⟨μ, ν, h, rfl⟩ := Finset.card_eq_two.1 hT2
    rw [sum_pair_faces A h y]
    have := hA μ ν h y
    omega

/-! ## §0i 写した定義と定理（方向で添字した辺の族 `PerfectP` と `A4`） -/

/-- 周期格子の**完全な族**：どのプラケットもちょうど一本を含む。 -/
def PerfectP (I : Fin d → Wp d L → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wp d L,
    (I μ x).toNat + (I μ (shiftp x ν)).toNat
      + (I ν x).toNat + (I ν (shiftp x μ)).toNat = 1

instance instDecidablePerfectP [NeZero L] (I : Fin d → Wp d L → Bool) :
    Decidable (PerfectP I) := by
  unfold PerfectP; infer_instance

/--
`d = 4`・周期 2 の完全な族 `A4`。方向ごとに「残り 3 座標の長さ 3 の反復符号」で書ける
（全数探索が出した 8 通りのうちの一つ）。
-/
def A4 (μ : Fin 4) (x : Wp 4 2) : Bool :=
  if μ = 0 then (x 1 == x 2) && (x 2 == x 3)
  else if μ = 1 then (x 0 == x 3) && !(x 2 == x 0)
  else if μ = 2 then (x 0 == x 1) && !(x 3 == x 0)
  else (x 0 == x 2) && !(x 1 == x 0)

theorem A4_perfect : PerfectP A4 := by decide

/-! ## §1 `d = 4`：`A4` を対の型へ移す

`A4` は方向 `μ` で添字した辺の族（`PerfectP`）である。`PerfectK 1` は胞体の対 `(S, x)` で
書かれているので、`S` が一点 `{μ}` のところで `A4 μ` に一致する族 `edge4` を対の型に置き、
`perfect_one_iff`（`k=1` の言い換え）と偶奇の写像 `vOfPar` を通して `Perfect 1 edge4` を出す。
-/

/-- `A4` を胞体の対 `(S, y)` の型に書き直した族。`S` が一点 `{μ}` のところで `A4 μ` の値に
一致する（`edge4_eq_A4`）。`S` の大きさが 1 でないところの値は完全性には効かない
（`Perfect 1` が見るのは `T.erase ν`（`|T| = 2`）だけで、これは常に一点である）。 -/
def edge4 : Finset (Fin 4) × V 4 → Bool := fun p =>
  if 0 ∈ p.1 then (p.2 1 == p.2 2) && (p.2 2 == p.2 3)
  else if 1 ∈ p.1 then (p.2 0 == p.2 3) && !(p.2 2 == p.2 0)
  else if 2 ∈ p.1 then (p.2 0 == p.2 1) && !(p.2 3 == p.2 0)
  else (p.2 0 == p.2 2) && !(p.2 1 == p.2 0)

/-- **移し替えが正しいこと**：偶奇の写像 `vOfPar` で頂点を読み替えると、`edge4` の一点での値は
`A4` の値に一致する（64 通りを `decide`）。 -/
theorem edge4_eq_A4 :
    ∀ (μ : Fin 4) (x : Wp 4 2), edge4 ({μ}, vOfPar (dvd_refl 2) x) = A4 μ x := by decide

/-- **`d = 4` の完全な族**：`A4_perfect`（方向で添字した形）から対の型へ移したもの。 -/
theorem perfect_edge4 : Perfect 1 edge4 := by
  rw [perfect_one_iff]
  intro μ ν hμν z
  obtain ⟨x, rfl⟩ := vOfPar_two_surjective (d := 4) z
  rw [← vOfPar_shiftp (dvd_refl 2) x ν, ← vOfPar_shiftp (dvd_refl 2) x μ]
  rw [edge4_eq_A4 μ x, edge4_eq_A4 μ (shiftp x ν), edge4_eq_A4 ν x, edge4_eq_A4 ν (shiftp x μ)]
  exact A4_perfect μ ν hμν x

/-- 同じ言明を**核の計算で直に**出したもの（二通りの道の突き合わせ）。 -/
theorem perfect_edge4_decide : Perfect 1 edge4 := by decide +kernel

/-! ## §2 `d = 3`：`d = k+2` の三角ガジェット

`d = 3` は `k = 1` では `d = k+2` に当たるので、`PerfectFamilyConstruction.lean` の構成
（`Layout.perfect_fam`）が使える枡である。そこでは族は `Sᶜ` が対 `{u,v}` であることで
添字され、大きさ 3 の部分 `{a,b,c}` には
`g_{ab} = y_a y_b`・`g_{ac} = (1⊕y_a) y_c`・`g_{bc} = (1⊕y_b)(1⊕y_c)` が置かれる。
`d = 3` ではその一つの部分だけがあり、`S = {0}` なら `Sᶜ = {1,2}` で `g_{12}`、
`S = {1}` なら `g_{02}`、`S = {2}` なら `g_{01}` になる。
この一枚は `Layout` の一式を写す代わりに、その値を書き下したものを核の計算で閉じた。
-/

/-- **`d = 3` の族**（`a,b,c = 0,1,2` の三角ガジェットを書き下したもの）。 -/
def edge3 : Finset (Fin 3) × V 3 → Bool := fun p =>
  if 0 ∈ p.1 then (!p.2 1 && !p.2 2)
  else if 1 ∈ p.1 then (!p.2 0 && p.2 2)
  else (p.2 0 && p.2 1)

theorem perfect_edge3 : Perfect 1 edge3 := by decide +kernel

/-- 陰性対照：ガジェットの一つを崩すと完全でなくなる（`g_{01} = y_0 y_1` を
`y_0 (1⊕y_1)` に替えた族）。族の大きさは同じ 6 なので、大きさだけでは決まらない。 -/
def edge3bad : Finset (Fin 3) × V 3 → Bool := fun p =>
  if 0 ∈ p.1 then (!p.2 1 && !p.2 2)
  else if 1 ∈ p.1 then (!p.2 0 && p.2 2)
  else (p.2 0 && !p.2 1)

theorem not_perfect_edge3bad : ¬ Perfect 1 edge3bad := by decide +kernel

theorem card_support_edge3bad : (support edge3bad 1).card = 6 := by decide +kernel

/-! ## §3 `d = 2`：`k+1 ≤ d` の端

`d = 2` は `k = 1` では `d = k+1` で、プラケットは向きの組が一通りしかない。
`d = k+2` の構成は使えないが、片方の向きだけを使う族で足りる：
向き 0 の辺を `y_1 = 0` の行だけで採ると、どのプラケットもちょうど一本を持つ。
-/

/-- **`d = 2` の族**：向き 0 の辺のうち `y_1 = 0` のもの（`|I| = 2`）。 -/
def edge2 : Finset (Fin 2) × V 2 → Bool := fun p =>
  if 0 ∈ p.1 then !p.2 1 else false

theorem perfect_edge2 : Perfect 1 edge2 := by decide +kernel

/-! ## §4 偶数の周期への持ち上げと、次元ごとの判定 -/

theorem perfectK_one_d4 (h : 2 ∣ L) :
    PerfectK (d := 4) (L := L) 1 (fun S x => edge4 (S, vOfPar h x)) :=
  perfectK_of_perfect h edge4 perfect_edge4

theorem perfectK_one_d3 (h : 2 ∣ L) :
    PerfectK (d := 3) (L := L) 1 (fun S x => edge3 (S, vOfPar h x)) :=
  perfectK_of_perfect h edge3 perfect_edge3

theorem perfectK_one_d2 (h : 2 ∣ L) :
    PerfectK (d := 2) (L := L) 1 (fun S x => edge2 (S, vOfPar h x)) :=
  perfectK_of_perfect h edge2 perfect_edge2

/-- **`d = 4`**：完全な辺の族が在るのは `2 ∣ L` のとき、かつそのときに限る。 -/
theorem perfectK_one_d4_iff [NeZero L] :
    (∃ I : Finset (Fin 4) → Wp 4 L → Bool, PerfectK 1 I) ↔ 2 ∣ L := by
  constructor
  · rintro ⟨I, hI⟩
    exact two_dvd_of_perfectK (by norm_num) I hI
  · intro h
    exact ⟨_, perfectK_one_d4 h⟩

/-- **`d = 3`**：同じく「在る ⟺ `2 ∣ L`」。 -/
theorem perfectK_one_d3_iff [NeZero L] :
    (∃ I : Finset (Fin 3) → Wp 3 L → Bool, PerfectK 1 I) ↔ 2 ∣ L := by
  constructor
  · rintro ⟨I, hI⟩
    exact two_dvd_of_perfectK (by norm_num) I hI
  · intro h
    exact ⟨_, perfectK_one_d3 h⟩

/-- **`d = 2`**：同じく「在る ⟺ `2 ∣ L`」。 -/
theorem perfectK_one_d2_iff [NeZero L] :
    (∃ I : Finset (Fin 2) → Wp 2 L → Bool, PerfectK 1 I) ↔ 2 ∣ L := by
  constructor
  · rintro ⟨I, hI⟩
    exact two_dvd_of_perfectK (by norm_num) I hI
  · intro h
    exact ⟨_, perfectK_one_d2 h⟩

/-- `5 ≤ d` なら**どの周期の格子にも**完全な辺の族は無い（`perfectK_d_le` の対偶）。 -/
theorem no_perfectK_one_of_five_le [NeZero L] (hd : 5 ≤ d) :
    ¬ ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK 1 I :=
  no_perfectK_of_lt (k := 1) le_rfl (by omega)

/-- `2 ≤ d ≤ 4` かつ `2 ∣ L` なら在る（三つの族を次元で場合分けして持ち上げる）。 -/
theorem exists_perfectK_one [NeZero L] (hd2 : 2 ≤ d) (hd4 : d ≤ 4) (hL : 2 ∣ L) :
    ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK 1 I := by
  interval_cases d
  · exact ⟨_, perfectK_one_d2 hL⟩
  · exact ⟨_, perfectK_one_d3 hL⟩
  · exact ⟨_, perfectK_one_d4 hL⟩

/-! ## §5 まとめの定理 -/

/--
**主定理**：`2 ≤ d` のとき、周期 `L` の格子 `(ℤ/L)^d` に `k = 1` の完全な族
（どのプラケットもちょうど一本の辺を持つ辺の族）が在るのは、
**`d ≤ 4` かつ `2 ∣ L` のとき、かつそのときに限る。**

⟹ は二本立てで、`d ≤ 4` は `perfectK_d_le`（パッキング上界と数え上げの比較）、
`2 ∣ L` は `two_mul_sum_card_slice`（層ごとの等式）から来る。
⟸ は `d = 2, 3, 4` の明示の族を偶奇で持ち上げたもの。
-/
theorem perfectK_one_iff [NeZero L] (hd : 2 ≤ d) :
    (∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK 1 I) ↔ (d ≤ 4 ∧ 2 ∣ L) := by
  constructor
  · rintro ⟨I, hI⟩
    have hb := perfectK_d_le (k := 1) le_rfl (by omega) I hI
    exact ⟨by omega, two_dvd_of_perfectK (by omega) I hI⟩
  · rintro ⟨h4, hL⟩
    exact exists_perfectK_one hd h4 hL

/-- 同じことを「`2 ≤ d ≤ 4` かつ `2 ∣ L`」の形で（`2 ≤ d` は仮定に置いてあるので
右辺にも出しただけ）。 -/
theorem perfectK_one_iff_range [NeZero L] (hd : 2 ≤ d) :
    (∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK 1 I) ↔ (2 ≤ d ∧ d ≤ 4 ∧ 2 ∣ L) := by
  rw [perfectK_one_iff hd]
  exact ⟨fun h => ⟨hd, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-- **`k = 1` では上界 `d ≤ 3k+1` は鋭い**：`3·1+1 = 4` で、`2 ∣ L` のどの周期でも
完全な族が実在する（`perfectK_d_le` が `k=1` で最良であることの確認）。 -/
theorem bound_sharp_k1 (hL : 2 ∣ L) :
    (3 * 1 + 1 = 4) ∧ ∃ I : Finset (Fin 4) → Wp 4 L → Bool, PerfectK 1 I :=
  ⟨by norm_num, ⟨_, perfectK_one_d4 hL⟩⟩

/--
**在る側は頂点の有限性を使っていない**：持ち上げ `perfectK_of_perfect` に `NeZero L` が
要らないので、`L = 0`（`ZMod 0 = ℤ`、つまり**無限格子 `ℤ^d`**）でも `d = 2, 3, 4` の
完全な族が在る（偶奇の構成そのもの）。
無い側（`d ≤ 4` と `2 ∣ L`）は数え上げで頂点の数 `L^d` を使うので、こちらは持ち上がらない
——`L = 0` について何も言っていない。
-/
theorem exists_perfectK_one_infinite (hd2 : 2 ≤ d) (hd4 : d ≤ 4) :
    ∃ I : Finset (Fin d) → Wp d 0 → Bool, PerfectK 1 I := by
  interval_cases d
  · exact ⟨_, perfectK_one_d2 (dvd_zero 2)⟩
  · exact ⟨_, perfectK_one_d3 (dvd_zero 2)⟩
  · exact ⟨_, perfectK_one_d4 (dvd_zero 2)⟩

/-! ## §6 `2 ≤ d` は落とせない -/

/-- `d ≤ 1` では `2`-cell が無いので、**どの族も**完全である（空虚に真）。 -/
theorem perfectK_one_of_d_le_one [NeZero L] (hd : d ≤ 1)
    (I : Finset (Fin d) → Wp d L → Bool) : PerfectK 1 I := by
  intro T hT x
  have h1 : T.card ≤ d := by
    have h := Finset.card_le_univ T
    simpa using h
  exact absurd hT (by omega)

/-- `d = 1`・`L = 3`（奇数）でも族は在る。 -/
theorem perfectK_one_d1_L3 : ∃ I : Finset (Fin 1) → Wp 1 3 → Bool, PerfectK 1 I :=
  ⟨fun _ _ => false, perfectK_one_of_d_le_one (by norm_num) _⟩

/-- **陰性対照（主定理の仮定 `2 ≤ d` が落とせないこと）**：`d = 1`・`L = 3` では
左辺（族が在る）は真で、右辺（`d ≤ 4` かつ `2 ∣ L`）は偽。 -/
theorem iff_fails_without_hd :
    (∃ I : Finset (Fin 1) → Wp 1 3 → Bool, PerfectK 1 I)
      ∧ ¬ ((1 : ℕ) ≤ 4 ∧ (2 : ℕ) ∣ 3) :=
  ⟨perfectK_one_d1_L3, by decide⟩

/-! ## §7 陽性対照（実在する族に定理を当てる）と陰性対照 -/

theorem two_dvd_six : (2 : ℕ) ∣ 6 := by decide

/-- 陽性対照：`d = 4` の族を**周期 6**（周期 2 でも 4 でもない偶数）に持ち上げたもの。 -/
theorem perfectK_edge4_L6 :
    PerfectK (d := 4) (L := 6) 1 (fun S x => edge4 (S, vOfPar two_dvd_six x)) :=
  perfectK_one_d4 two_dvd_six

theorem perfectK_edge3_L6 :
    PerfectK (d := 3) (L := 6) 1 (fun S x => edge3 (S, vOfPar two_dvd_six x)) :=
  perfectK_one_d3 two_dvd_six

theorem perfectK_edge2_L6 :
    PerfectK (d := 2) (L := 6) 1 (fun S x => edge2 (S, vOfPar two_dvd_six x)) :=
  perfectK_one_d2 two_dvd_six

/-- 陽性対照：`L = 2` では `perfectK_two_iff` で往復できる。 -/
theorem perfectK_edge4_L2 :
    PerfectK (d := 4) (L := 2) 1 (fun S x => edge4 (S, vOfPar (dvd_refl 2) x)) :=
  (perfectK_two_iff 1 edge4).2 perfect_edge4

/-- 陽性対照：数え上げ (1) を実在する族に当てる（`d = 4`・周期 6）：
`4·|I| = C(4,1)·6^4 = 5184`。 -/
theorem counting_edge4_L6 :
    2 * (1 + 1) * (supportK 1 (fun S x => edge4 (S, vOfPar two_dvd_six x))).card
        = Nat.choose 4 1 * 6 ^ 4
      ∧ Nat.choose 4 1 * 6 ^ 4 = 5184 :=
  ⟨card_supportK_of_perfectK (by norm_num) _ perfectK_edge4_L6, by decide⟩

/-- 陽性対照：同じく `d = 3`・周期 6：`4·|I| = C(3,1)·6^3 = 648`。 -/
theorem counting_edge3_L6 :
    2 * (1 + 1) * (supportK 1 (fun S x => edge3 (S, vOfPar two_dvd_six x))).card
        = Nat.choose 3 1 * 6 ^ 3
      ∧ Nat.choose 3 1 * 6 ^ 3 = 648 :=
  ⟨card_supportK_of_perfectK (by norm_num) _ perfectK_edge3_L6, by decide⟩

/-- 陽性対照：層ごとの等式 (I) を当てる（`d = 4`・周期 6）：どの 2-集合 `T` でも
`2·Σ_{ν∈T}|I_{T∖ν}| = 6^4`。 -/
theorem slice_edge4_L6 (T : Finset (Fin 4)) (hT : T.card = 2) :
    2 * ∑ ν ∈ T, (∑ x : Wp 4 6, (edge4 (T.erase ν, vOfPar two_dvd_six x)).toNat) = 6 ^ 4 :=
  two_mul_sum_card_slice perfectK_edge4_L6 hT

/-- 陽性対照：パッキング上界も同じ族で成り立つ（`|I| ≤ 6^4`）。 -/
theorem packing_edge4_L6 :
    (cellSet 0 (fun S x => edge4 (S, vOfPar two_dvd_six x))).card ≤ 6 ^ 4 :=
  card_cellSet_le_zero (packK_of_perfectK perfectK_edge4_L6)

/-- 陽性対照：周期 2 での族の大きさ（`|I| = C(d,1)·2^d/4`）。 -/
theorem card_support_edges :
    (support edge4 1).card = 16 ∧ (support edge3 1).card = 6
      ∧ (support edge2 1).card = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- 陽性対照：上の大きさが数え上げ (1) の値と合っている（`4·|I| = C(d,1)·2^d`）。 -/
theorem card_support_edges_consistent :
    4 * 16 = Nat.choose 4 1 * 2 ^ 4 ∧ 4 * 6 = Nat.choose 3 1 * 2 ^ 3
      ∧ 4 * 2 = Nat.choose 2 1 * 2 ^ 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- 陰性対照：`Perfect 1` は空虚でも自明でもない（`d = 3`・全部採る／何も採らない）。 -/
theorem not_perfect_full3 : ¬ Perfect 1 (fun _ : Finset (Fin 3) × V 3 => true) := by
  decide +kernel

theorem not_perfect_empty3 : ¬ Perfect 1 (fun _ : Finset (Fin 3) × V 3 => false) := by
  decide +kernel

/-- 陰性対照：`d = 4` でも同じ（`A4` の形が効いていることの裏）。 -/
theorem not_perfect_full4 : ¬ Perfect 1 (fun _ : Finset (Fin 4) × V 4 => true) := by
  decide +kernel

/-- 陰性対照：奇数の周期は落ちる（`d = 3`・`L = 3`）。 -/
theorem no_perfectK_one_d3_L3 : ¬ ∃ I : Finset (Fin 3) → Wp 3 3 → Bool, PerfectK 1 I :=
  no_perfectK_of_odd (by norm_num) (by decide)

/-- 陰性対照：`d = 5` は偶数の周期でも落ちる（上界の側）。 -/
theorem no_perfectK_one_d5_L10 : ¬ ∃ I : Finset (Fin 5) → Wp 5 10 → Bool, PerfectK 1 I :=
  no_perfectK_one_of_five_le (by norm_num)

/-- 陰性対照：`d = 6`・周期 12 でも落ちる。 -/
theorem no_perfectK_one_d6_L12 : ¬ ∃ I : Finset (Fin 6) → Wp 6 12 → Bool, PerfectK 1 I :=
  no_perfectK_one_of_five_le (by norm_num)

end PerfectFamily

/-! ## §8 使った公理 -/

namespace PerfectFamily
#print axioms PerfectFamily.Wp
#print axioms PerfectFamily.shiftp
#print axioms PerfectFamily.card_Wp
#print axioms PerfectFamily.shiftp_bijective
#print axioms PerfectFamily.sum_shiftp
#print axioms PerfectFamily.faceCount
#print axioms PerfectFamily.PackK
#print axioms PerfectFamily.instDecidablePackK
#print axioms PerfectFamily.not_share_m
#print axioms PerfectFamily.disjoint_powersetCard_of_pack
#print axioms PerfectFamily.cellsAt
#print axioms PerfectFamily.card_cellsAt_le
#print axioms PerfectFamily.cellSet
#print axioms PerfectFamily.card_cellSet_eq_sum
#print axioms PerfectFamily.card_cellSet_le
#print axioms PerfectFamily.card_cellSet_le_zero
#print axioms PerfectFamily.packK_empty
#print axioms PerfectFamily.not_packK_full
#print axioms PerfectFamily.not_packK_full_k2
#print axioms PerfectFamily.V
#print axioms PerfectFamily.flipAt
#print axioms PerfectFamily.flipAt_flipAt
#print axioms PerfectFamily.flipAt_ne
#print axioms PerfectFamily.Perfect
#print axioms PerfectFamily.instDecidablePerfect
#print axioms PerfectFamily.support
#print axioms PerfectFamily.powersetCard_univ_eq
#print axioms PerfectFamily.PerfectK
#print axioms PerfectFamily.instDecidablePerfectK
#print axioms PerfectFamily.packK_of_perfectK
#print axioms PerfectFamily.supportK
#print axioms PerfectFamily.supportK_eq_cellSet
#print axioms PerfectFamily.supportK_card_eq
#print axioms PerfectFamily.total_incidencesK
#print axioms PerfectFamily.card_supportK_of_perfectK
#print axioms PerfectFamily.two_mul_sum_card_slice
#print axioms PerfectFamily.two_dvd_of_perfectK
#print axioms PerfectFamily.no_perfectK_of_odd
#print axioms PerfectFamily.perfectK_d_le_succ
#print axioms PerfectFamily.perfectK_d_le
#print axioms PerfectFamily.no_perfectK_of_lt
#print axioms PerfectFamily.perfectK_one_d_le_four
#print axioms PerfectFamily.perfectK_sub_le
#print axioms PerfectFamily.par2
#print axioms PerfectFamily.par2_add_one
#print axioms PerfectFamily.vOfPar
#print axioms PerfectFamily.vOfPar_shiftp
#print axioms PerfectFamily.perfectK_of_perfect
#print axioms PerfectFamily.vOfPar_two_surjective
#print axioms PerfectFamily.perfectK_two_iff
#print axioms PerfectFamily.sum_pair_faces
#print axioms PerfectFamily.perfect_one_iff
#print axioms PerfectFamily.PerfectP
#print axioms PerfectFamily.instDecidablePerfectP
#print axioms PerfectFamily.A4
#print axioms PerfectFamily.A4_perfect
#print axioms PerfectFamily.edge4
#print axioms PerfectFamily.edge4_eq_A4
#print axioms PerfectFamily.perfect_edge4
#print axioms PerfectFamily.perfect_edge4_decide
#print axioms PerfectFamily.edge3
#print axioms PerfectFamily.perfect_edge3
#print axioms PerfectFamily.edge3bad
#print axioms PerfectFamily.not_perfect_edge3bad
#print axioms PerfectFamily.card_support_edge3bad
#print axioms PerfectFamily.edge2
#print axioms PerfectFamily.perfect_edge2
#print axioms PerfectFamily.perfectK_one_d4
#print axioms PerfectFamily.perfectK_one_d3
#print axioms PerfectFamily.perfectK_one_d2
#print axioms PerfectFamily.perfectK_one_d4_iff
#print axioms PerfectFamily.perfectK_one_d3_iff
#print axioms PerfectFamily.perfectK_one_d2_iff
#print axioms PerfectFamily.no_perfectK_one_of_five_le
#print axioms PerfectFamily.exists_perfectK_one
#print axioms PerfectFamily.perfectK_one_iff
#print axioms PerfectFamily.perfectK_one_iff_range
#print axioms PerfectFamily.bound_sharp_k1
#print axioms PerfectFamily.exists_perfectK_one_infinite
#print axioms PerfectFamily.perfectK_one_of_d_le_one
#print axioms PerfectFamily.perfectK_one_d1_L3
#print axioms PerfectFamily.iff_fails_without_hd
#print axioms PerfectFamily.two_dvd_six
#print axioms PerfectFamily.perfectK_edge4_L6
#print axioms PerfectFamily.perfectK_edge3_L6
#print axioms PerfectFamily.perfectK_edge2_L6
#print axioms PerfectFamily.perfectK_edge4_L2
#print axioms PerfectFamily.counting_edge4_L6
#print axioms PerfectFamily.counting_edge3_L6
#print axioms PerfectFamily.slice_edge4_L6
#print axioms PerfectFamily.packing_edge4_L6
#print axioms PerfectFamily.card_support_edges
#print axioms PerfectFamily.card_support_edges_consistent
#print axioms PerfectFamily.not_perfect_full3
#print axioms PerfectFamily.not_perfect_empty3
#print axioms PerfectFamily.not_perfect_full4
#print axioms PerfectFamily.no_perfectK_one_d3_L3
#print axioms PerfectFamily.no_perfectK_one_d5_L10
#print axioms PerfectFamily.no_perfectK_one_d6_L12

end PerfectFamily
