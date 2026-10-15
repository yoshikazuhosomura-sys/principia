/-
周期 `L` の格子 `(ZMod L)^d` の上の `k`-cell の**完全な族** `PerfectK`
（どの `(k+1)`-cell もその `2(k+1)` 枚の面のうちちょうど一枚を持つ）と、そこから出る三つ：

1. 入射の二通りの数え上げ `2(k+1)·|I| = C(d,k)·L^d`（`card_supportK_of_perfectK`）
2. 系として `2(k+1) ∣ C(d,k)·L^d`、および層ごとの等式から **周期が奇数なら完全な族は無い**
3. パッキング上界と合わせて `d ≤ 3k+1`（`perfectK_d_le`）——**周期に依らない**

`import Mathlib` だけで素の `lake env lean` を通る一枚版。`sorry` 0・`native_decide` 不使用。

単独検査の一枚は互いに `import` できないので、必要な定義と定理を原本から**行範囲でそのまま
写した**（下の表。`diff` が空であることを確かめてある）。

| 原本 | 原本の行 | 中身 |
|---|---|---|
| `PlaquetteCounting.lean` | 72〜76 | `Wp`・`shiftp` |
| `PlaquetteCounting.lean` | 97〜99 | `card_Wp` |
| `PlaquetteCounting.lean` | 344〜363 | `shiftp_bijective`・`sum_shiftp` |
| `PlaquetteCounting.lean` | 659〜818 | `faceCount`・`PackK`・`not_share_m`・`disjoint_powersetCard_of_pack`・`cellsAt`・`card_cellsAt_le`・`cellSet`・`card_cellSet_eq_sum`・`card_cellSet_le`・`card_cellSet_le_zero`・`packK_empty`・`not_packK_full`・`not_packK_full_k2` |
| `PerfectFamilyBound.lean` | 59〜60 | `V` |
| `PerfectFamilyBound.lean` | 64〜96 | `flipAt` 系・`Perfect`・`instDecidablePerfect` |
| `PerfectFamilyBound.lean` | 211〜219 | `support`・`powersetCard_univ_eq` |
| `PerfectFamilyBound.lean` | 605〜613 | `fam4`・`perfect_fam4`・`card_fam4`（陽性対照） |
| `PerfectFamilyBound.lean` | 630〜635 | `par5`・`perfect_par5`（`1 ≤ k` が要ることの反例） |

写した部分は名前空間だけを `PerfectFamily` に揃えてある（原本では `PlaquettePacking`・
`PlaquetteCounting`・`PerfectFamily` に分かれている）。

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/
import Mathlib

/-!
# 周期 `L` の格子の `k`-cell の完全な族

胞体を `(S, x)`（`S ⊆ [d]`・`x ∈ (ZMod L)^d`）で表し、`|S| = k` のものを `k`-cell と呼ぶ。
`(k+1)`-cell `(T, x)` の面は `ν ∈ T` ごとの `(T∖ν, x)` と `(T∖ν, x+e_ν)` の `2(k+1)` 枚で、
族 `I` が**完全**（`PerfectK k I`）とは、どの `(k+1)`-cell もちょうど一枚の面を持つことをいう。

## 主な結果

* `card_supportK_of_perfectK`：`2(k+1)·|I| = C(d,k)·L^d`（`k+1 ≤ d`）
* `two_mul_sum_card_slice`：`T` ごとに `2·Σ_{ν∈T}|I_{T∖ν}| = L^d`
* `no_perfectK_of_odd`：**周期が奇数なら完全な族は無い**（`k`・`d` に依らない）
* `no_perfectK_of_not_dvd`：`2(k+1) ∤ C(d,k)·L^d` からの非存在。
  `k=4,d=9` は `5 ∤ L` なら無く（`no_perfectK_k4_d9`）、奇数も落ちるので必要条件は `10 ∣ L`
  （`no_perfectK_k4_d9_ten`）。`k=5,d=8` は `3 ∤ L` なら無く、必要条件は `6 ∣ L`
* `perfectK_d_le`：`1 ≤ k`・`k+1 ≤ d` のとき `d ≤ 3k+1`。**周期 `L` に条件は要らない**
  （`NeZero L` は頂点の有限性のため）
* `perfectK_two_iff`：`L = 2` では `PerfectFamilyBound.lean` の `Perfect` と同じ内容
* `perfectK_of_perfect`：`2 ∣ L` なら周期 2 の族を周期 `L` に持ち上げられる（存在の側）
* `perfectK_k2_d4_iff`：`k=2, d=4` では完全な族が在るのは `2 ∣ L` のとき、かつそのときに限る

## 言っていないこと

* `d ≤ 3k+1` は**鋭くない**。逆向き（`d ≤ 3k+1` なら在る）は言っていない
* 完全な族の**分類**をしていない。`1 ≤ k` は落とせない（`k=0` の反例あり）
* 面が相異なる（`2(k+1)` 枚である）ことには `2 ≤ L` が要る。`L = 1` では潰れる
  （`card_faceSetK_fails_L1`）。数え上げ・上界そのものには `2 ≤ L` は要らない
* 各層の大きさが等しいこと（`d ≥ 2k+1` で `|I_S| = L^d/(2(k+1))`、ゆえに `2(k+1) ∣ L^d`）は
  **入っていない**。包含行列の階数（Gottlieb）が要るが、探した範囲では Mathlib に無い
* **ヤン–ミルズの本体への主張は無い。**
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

/-! ## §0b 写した定義（周期 2 の側・`L = 2` との突き合わせに使う） -/

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

/-! ## §1 周期 `L` の完全な族 -/

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

/-! ## §2 「ちょうど一枚」の意味——面が相異なるには `2 ≤ L` が要る -/

/-- `x ↦ x + e_ν` が動くのは `2 ≤ L` のとき。 -/
theorem shiftp_ne (hL : 2 ≤ L) (x : Wp d L) (ν : Fin d) : shiftp x ν ≠ x := by
  have hne : NeZero L := ⟨by omega⟩
  have hfact : Fact (1 < L) := ⟨by omega⟩
  intro h
  have h1 : shiftp x ν ν = x ν := by rw [h]
  have h2 : x ν + 1 = x ν := by
    have hs : shiftp x ν ν = x ν + 1 := by simp [shiftp]
    rw [← hs]; exact h1
  have h3 : (1 : ZMod L) = 0 := add_left_cancel (a := x ν) (by rw [h2, add_zero])
  have h4 : (1 : ZMod L).val = 0 := by rw [h3]; simp
  rw [ZMod.val_one] at h4
  omega

/-- `L = 1` では面が潰れる（`x + e_ν = x`）。 -/
theorem shiftp_eq_self_one (x : Wp d 1) (ν : Fin d) : shiftp x ν = x := by
  have h : ∀ a b : ZMod 1, a = b := by decide
  funext i
  exact h _ _

/-- `(k+1)`-cell `(T, x)` の面の枠。`p = (ν, b)`：`b = false` なら `(T∖ν, x)`、
`b = true` なら `(T∖ν, x+e_ν)`。 -/
def faceAtK (T : Finset (Fin d)) (x : Wp d L) (p : Fin d × Bool) :
    Finset (Fin d) × Wp d L :=
  (T.erase p.1, if p.2 then shiftp x p.1 else x)

/-- `(T, x)` の面の集合。 -/
def faceSetK [NeZero L] (T : Finset (Fin d)) (x : Wp d L) :
    Finset (Finset (Fin d) × Wp d L) :=
  (T ×ˢ (Finset.univ : Finset Bool)).image (faceAtK T x)

theorem faceAtK_injOn (hL : 2 ≤ L) (T : Finset (Fin d)) (x : Wp d L) :
    Set.InjOn (faceAtK T x) ↑(T ×ˢ (Finset.univ : Finset Bool)) := by
  rintro ⟨ν, b⟩ hp ⟨μ, c⟩ hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true] at hp hq
  have hνμ : ν = μ := by
    by_contra hne
    have h1 : T.erase ν = T.erase μ := congrArg Prod.fst h
    have h2 : ν ∈ T.erase μ := Finset.mem_erase.2 ⟨hne, hp⟩
    rw [← h1] at h2
    exact (Finset.notMem_erase ν T) h2
  subst hνμ
  have h3 : (if b then shiftp x ν else x) = (if c then shiftp x ν else x) := congrArg Prod.snd h
  have hbc : b = c := by
    rcases b with _ | _ <;> rcases c with _ | _
    · rfl
    · exact absurd h3.symm (shiftp_ne hL x ν)
    · exact absurd h3 (shiftp_ne hL x ν)
    · rfl
  subst hbc; rfl

/-- **`2 ≤ L` のとき面はちょうど `2(k+1)` 枚**。 -/
theorem card_faceSetK [NeZero L] (hL : 2 ≤ L) (T : Finset (Fin d)) (x : Wp d L) :
    (faceSetK T x).card = 2 * T.card := by
  rw [faceSetK, Finset.card_image_of_injOn (faceAtK_injOn hL T x), Finset.card_product]
  simp [Nat.mul_comm]

/-- 陰性対照（`2 ≤ L` が落とせないこと）：`L = 1` では面が潰れて枚数が `2(k+1)` にならない。 -/
theorem card_faceSetK_fails_L1 :
    (faceSetK (d := 2) (L := 1) {0, 1} (fun _ => 0)).card
      ≠ 2 * ({0, 1} : Finset (Fin 2)).card := by
  decide

/-- 完全性の「`toNat` の和が 1」は「面のうちちょうど一枚が `I` に入る」である（`2 ≤ L`）。 -/
theorem sum_eq_card_filterK [NeZero L] (hL : 2 ≤ L) (I : Finset (Fin d) → Wp d L → Bool)
    (T : Finset (Fin d)) (x : Wp d L) :
    ∑ ν ∈ T, faceCount I T x ν
      = ((faceSetK T x).filter (fun c => I c.1 c.2 = true)).card := by
  classical
  have hsub : ((T ×ˢ (Finset.univ : Finset Bool)).filter
      (fun p => I (faceAtK T x p).1 (faceAtK T x p).2 = true))
        ⊆ T ×ˢ (Finset.univ : Finset Bool) := Finset.filter_subset _ _
  have himg : (faceSetK T x).filter (fun c => I c.1 c.2 = true)
      = ((T ×ˢ (Finset.univ : Finset Bool)).filter
          (fun p => I (faceAtK T x p).1 (faceAtK T x p).2 = true)).image (faceAtK T x) := by
    rw [faceSetK, Finset.filter_image]
  rw [himg, Finset.card_image_of_injOn
    ((faceAtK_injOn hL T x).mono (by exact_mod_cast hsub)), Finset.card_filter,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Fintype.sum_bool, faceCount]
  rcases hy : I (T.erase ν) x with _ | _ <;>
    rcases hf : I (T.erase ν) (shiftp x ν) with _ | _ <;>
      simp [faceAtK, hy, hf]

/-- 完全性の言い換え（`2 ≤ L`）：どの `(k+1)`-cell についても、相異なる `2(k+1)` 枚の面のうち
`I` に入るものがちょうど一枚。 -/
theorem perfectK_iff [NeZero L] (hL : 2 ≤ L) (k : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    PerfectK k I ↔ ∀ T : Finset (Fin d), T.card = k + 1 → ∀ x : Wp d L,
      ((faceSetK T x).filter (fun c => I c.1 c.2 = true)).card = 1 := by
  unfold PerfectK
  constructor
  · intro h T hT x; rw [← sum_eq_card_filterK hL]; exact h T hT x
  · intro h T hT x; rw [sum_eq_card_filterK hL]; exact h T hT x

/-- `L = 1` には完全な族が無い（面が潰れて枚数が偶数になるから）。
§4 の `no_perfectK_of_odd` の特別な場合だが、別の道（面の潰れ）で出している。 -/
theorem no_perfectK_L1 {k : ℕ} (hk : k + 1 ≤ d) :
    ¬ ∃ I : Finset (Fin d) → Wp d 1 → Bool, PerfectK k I := by
  rintro ⟨I, hI⟩
  obtain ⟨T, -, hT⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d))) (n := k + 1)
      (by simpa using hk)
  have hsum := hI T hT (fun _ => 0)
  have heven : ∑ ν ∈ T, faceCount I T (fun _ => 0) ν
      = 2 * ∑ ν ∈ T, (I (T.erase ν) (fun _ => 0)).toNat := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [faceCount, shiftp_eq_self_one]
    ring
  omega

/-! ## §3 入射の二通りの数え上げ：`2(k+1)·|I| = C(d,k)·L^d` -/

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

/-- **密度は必ず `1/(2(k+1))`**（`d` にも `L` にも依らない・有理数の形）。 -/
theorem density_of_perfectK [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK k I) :
    ((supportK k I).card : ℚ) / ((Nat.choose d k : ℚ) * (L : ℚ) ^ d)
      = 1 / (2 * ((k : ℚ) + 1)) := by
  have h := card_supportK_of_perfectK hk I hI
  have hLpos : (0 : ℚ) < (L : ℚ) ^ d :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) d
  have hq : ((supportK k I).card : ℚ) * (2 * ((k : ℚ) + 1))
      = (Nat.choose d k : ℚ) * (L : ℚ) ^ d := by
    have h' := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h'
    linarith
  have hck : (0 : ℚ) < (Nat.choose d k : ℚ) := by
    exact_mod_cast Nat.choose_pos (show k ≤ d by omega)
  have hc : (0 : ℚ) < (Nat.choose d k : ℚ) * (L : ℚ) ^ d := by positivity
  have hd2 : (0 : ℚ) < 2 * ((k : ℚ) + 1) := by positivity
  rw [div_eq_div_iff (ne_of_gt hc) (ne_of_gt hd2)]
  linarith

/-! ## §4 層ごとの等式：周期が奇数なら完全な族は無い -/

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

/-! ## §5 割り算の検問（周期つきの形） -/

/-- **(2) 系**：完全な族が在れば `2(k+1) ∣ C(d,k)·L^d`。 -/
theorem two_mul_succ_dvd_of_perfectK [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (I : Finset (Fin d) → Wp d L → Bool) (hI : PerfectK k I) :
    2 * (k + 1) ∣ Nat.choose d k * L ^ d :=
  ⟨(supportK k I).card, (card_supportK_of_perfectK hk I hI).symm⟩

/-- 割り算の検問からの非存在。 -/
theorem no_perfectK_of_not_dvd [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (h : ¬ (2 * (k + 1) ∣ Nat.choose d k * L ^ d)) :
    ¬ ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK k I := by
  rintro ⟨I, hI⟩
  exact h (two_mul_succ_dvd_of_perfectK hk I hI)

/-- `2(k+1)` と `L` が互いに素なら、検問は `L` に依らず `2(k+1) ∣ C(d,k)` になる。 -/
theorem dvd_iff_of_coprime [NeZero L] {k : ℕ} (hcop : Nat.Coprime (2 * (k + 1)) L) :
    2 * (k + 1) ∣ Nat.choose d k * L ^ d ↔ 2 * (k + 1) ∣ Nat.choose d k := by
  constructor
  · exact fun h => (Nat.Coprime.pow_right d hcop).dvd_of_dvd_mul_right h
  · exact fun h => h.mul_right _

theorem no_perfectK_of_coprime [NeZero L] {k : ℕ} (hk : k + 1 ≤ d)
    (hcop : Nat.Coprime (2 * (k + 1)) L) (h : ¬ (2 * (k + 1) ∣ Nat.choose d k)) :
    ¬ ∃ I : Finset (Fin d) → Wp d L → Bool, PerfectK k I :=
  no_perfectK_of_not_dvd hk (fun hd => h ((dvd_iff_of_coprime hcop).1 hd))

/-- `k=4, d=9`：**`5 ∤ L` なら**完全な族は無い（`10 ∤ 126·L^9`）。
限定は言明に出ている。`5 ∣ L` のときは検問を通る（`dvd_pass_k4_d9_of_five_dvd`）。 -/
theorem no_perfectK_k4_d9 [NeZero L] (hL : ¬ (5 ∣ L)) :
    ¬ ∃ I : Finset (Fin 9) → Wp 9 L → Bool, PerfectK 4 I := by
  refine no_perfectK_of_not_dvd (by norm_num) ?_
  intro h
  have hc : Nat.choose 9 4 = 126 := by decide
  rw [hc] at h
  have h5 : (5 : ℕ) ∣ 126 * L ^ 9 := dvd_trans (by norm_num) h
  have hp : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).1 h5 with h' | h'
  · norm_num at h'
  · exact hL (hp.dvd_of_dvd_pow h')

/-- `k=5, d=8`：**`3 ∤ L` なら**完全な族は無い（`12 ∤ 56·L^8`）。 -/
theorem no_perfectK_k5_d8 [NeZero L] (hL : ¬ (3 ∣ L)) :
    ¬ ∃ I : Finset (Fin 8) → Wp 8 L → Bool, PerfectK 5 I := by
  refine no_perfectK_of_not_dvd (by norm_num) ?_
  intro h
  have hc : Nat.choose 8 5 = 56 := by decide
  rw [hc] at h
  have h3 : (3 : ℕ) ∣ 56 * L ^ 8 := dvd_trans (by norm_num) h
  have hp : Nat.Prime 3 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).1 h3 with h' | h'
  · norm_num at h'
  · exact hL (hp.dvd_of_dvd_pow h')

/-- `k=3, d=9`：**周期が奇数なら**完全な族は無い（`8 ∤ 84·L^9`）。
周期 2 では検問を通る枡で、`§4` の `no_perfectK_of_odd` とは別の道で同じ結論に達する。 -/
theorem no_perfectK_k3_d9 [NeZero L] (hL : ¬ (2 ∣ L)) :
    ¬ ∃ I : Finset (Fin 9) → Wp 9 L → Bool, PerfectK 3 I := by
  refine no_perfectK_of_not_dvd (by norm_num) ?_
  intro h
  obtain ⟨c, hc⟩ := h
  have hch : Nat.choose 9 3 = 84 := by decide
  rw [hch] at hc
  have h2 : 21 * L ^ 9 = 2 * c := by omega
  have hp : Nat.Prime 2 := Nat.prime_two
  rcases (Nat.Prime.dvd_mul hp).1 (⟨c, h2⟩ : (2 : ℕ) ∣ 21 * L ^ 9) with h' | h'
  · norm_num at h'
  · exact hL (hp.dvd_of_dvd_pow h')

/-- **`k=4, d=9` の必要条件は `10 ∣ L`**（奇数を落とす §4 と `5 ∣ L` を要求する検問の合わせ技。
周期 2 だけを見ていたときより強い）。 -/
theorem no_perfectK_k4_d9_ten [NeZero L] (hL : ¬ (10 ∣ L)) :
    ¬ ∃ I : Finset (Fin 9) → Wp 9 L → Bool, PerfectK 4 I := by
  rintro ⟨I, hI⟩
  have h2 : 2 ∣ L := two_dvd_of_perfectK (by norm_num) I hI
  have h5 : 5 ∣ L := by
    by_contra h
    exact no_perfectK_k4_d9 h ⟨I, hI⟩
  have h10 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 5 by decide) h2 h5
  exact hL (by simpa using h10)

/-- **`k=5, d=8` の必要条件は `6 ∣ L`**。 -/
theorem no_perfectK_k5_d8_six [NeZero L] (hL : ¬ (6 ∣ L)) :
    ¬ ∃ I : Finset (Fin 8) → Wp 8 L → Bool, PerfectK 5 I := by
  rintro ⟨I, hI⟩
  have h2 : 2 ∣ L := two_dvd_of_perfectK (by norm_num) I hI
  have h3 : 3 ∣ L := by
    by_contra h
    exact no_perfectK_k5_d8 h ⟨I, hI⟩
  have h6 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by decide) h2 h3
  exact hL (by simpa using h6)

/-- 周期 2 での再現（`PerfectFamilyBound.lean` の `no_perfect_k4_d9`・`no_perfect_k5_d8`
と同じ枡）。 -/
theorem no_perfectK_k4_d9_L2 : ¬ ∃ I : Finset (Fin 9) → Wp 9 2 → Bool, PerfectK 4 I :=
  no_perfectK_k4_d9 (by decide)

theorem no_perfectK_k5_d8_L2 : ¬ ∃ I : Finset (Fin 8) → Wp 8 2 → Bool, PerfectK 5 I :=
  no_perfectK_k5_d8 (by decide)

/-- 限定が効いていること（検問は `5 ∣ L` の周期を落とせない）：`5 ∣ L` なら `10 ∣ 126·L^9`。 -/
theorem dvd_pass_k4_d9_of_five_dvd (hL : 5 ∣ L) : 2 * (4 + 1) ∣ Nat.choose 9 4 * L ^ 9 := by
  obtain ⟨t, rfl⟩ := hL
  have hc : Nat.choose 9 4 = 126 := by decide
  rw [hc]
  exact ⟨63 * 5 ^ 8 * t ^ 9, by ring⟩

/-- 同じく `3 ∣ L` なら `12 ∣ 56·L^8`。 -/
theorem dvd_pass_k5_d8_of_three_dvd (hL : 3 ∣ L) : 2 * (5 + 1) ∣ Nat.choose 8 5 * L ^ 8 := by
  obtain ⟨t, rfl⟩ := hL
  have hc : Nat.choose 8 5 = 56 := by decide
  rw [hc]
  exact ⟨14 * 3 ^ 7 * t ^ 8, by ring⟩

/-- `no_perfectK_k4_d9_ten`・`no_perfectK_k5_d8_six` から、この一枚の検問を通りうる周期は
`k=4,d=9` では `10 ∣ L`、`k=5,d=8` では `6 ∣ L` に限る。その最小の周期で検問が実際に
通ること（＝この一枚では落とせないこと）と、上界の側もこの二枡を落とさないこと。 -/
theorem open_moduli_pass :
    (2 * (4 + 1) ∣ Nat.choose 9 4 * 10 ^ 9) ∧ (2 * (5 + 1) ∣ Nat.choose 8 5 * 6 ^ 8)
      ∧ (9 : ℕ) ≤ 3 * 4 + 1 ∧ (8 : ℕ) ≤ 3 * 5 + 1 := by
  refine ⟨dvd_pass_k4_d9_of_five_dvd (by decide), dvd_pass_k5_d8_of_three_dvd (by decide),
    by norm_num, by norm_num⟩

/-! ## §6 二つを比べる：`d ≤ 3k+1`（周期に依らない） -/

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

/-! ## §7 `L = 2` は `Perfect` と同じ内容・`2 ∣ L` には持ち上げられる -/

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

/-- 周期 2 の主定理（`PerfectFamilyBound.perfect_d_le`）は、この一枚の主定理の
特別な場合として出る。 -/
theorem perfect_d_le_of_perfectK {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ d)
    (A : Finset (Fin d) × V d → Bool) (hA : Perfect k A) : d ≤ 3 * k + 1 :=
  perfectK_d_le (L := 2) hk1 hk _ ((perfectK_two_iff k A).2 hA)

/-! ## §8 陽性対照（実在する族に定理を当てる）と陰性対照 -/

/-- `k = 2, d = 4`：分割 `{0,1} ⊔ {2,3}`、対ガジェットが二つ。 -/
def fam4 : Finset (Fin 4) × V 4 → Bool := fun p =>
  if p.1ᶜ = {0, 1} then (p.2 0 != p.2 1)
  else if p.1ᶜ = {2, 3} then (p.2 2 != p.2 3)
  else false

theorem perfect_fam4 : Perfect 2 fam4 := by decide +kernel

theorem card_fam4 : (support fam4 2).card = 16 := by decide +kernel

theorem two_dvd_six : (2 : ℕ) ∣ 6 := by decide

/-- 陽性対照：`k=2, d=4` の実在する族を周期 2 に読み替えたもの。 -/
theorem perfectK_fam4_L2 :
    PerfectK (d := 4) (L := 2) 2 (fun S x => fam4 (S, vOfPar (dvd_refl 2) x)) :=
  (perfectK_two_iff 2 fam4).2 perfect_fam4

/-- 陽性対照：同じ族を**周期 6** に持ち上げたもの（周期 2 以外でも `PerfectK` は空虚でない）。 -/
theorem perfectK_fam4_L6 :
    PerfectK (d := 4) (L := 6) 2 (fun S x => fam4 (S, vOfPar two_dvd_six x)) :=
  perfectK_of_perfect two_dvd_six fam4 perfect_fam4

/--
**一つの枡は周期について完全に決まる**：`k=2, d=4` では、周期 `L`（`NeZero L`）の
完全な族が在るのは **`2 ∣ L` のとき、かつそのときに限る**。
（⟸ は `fam4` の偶奇による持ち上げ、⟹ は層ごとの等式。）
-/
theorem perfectK_k2_d4_iff [NeZero L] :
    (∃ I : Finset (Fin 4) → Wp 4 L → Bool, PerfectK 2 I) ↔ 2 ∣ L := by
  constructor
  · rintro ⟨I, hI⟩
    exact two_dvd_of_perfectK (by norm_num) I hI
  · intro h
    exact ⟨_, perfectK_of_perfect h fam4 perfect_fam4⟩

/-- 陽性対照：主定理を実在する族に当てる（`4 ≤ 3·2+1 = 7`・周期 6）。 -/
theorem bound_fam4_L6 : (4 : ℕ) ≤ 3 * 2 + 1 :=
  perfectK_d_le (L := 6) (by norm_num) (by norm_num) _ perfectK_fam4_L6

/-- 陽性対照：同じ族で数え上げの等式（周期 6）：`6·|I| = C(4,2)·6^4 = 7776`。 -/
theorem counting_fam4_L6 :
    2 * (2 + 1) * (supportK 2 (fun S x => fam4 (S, vOfPar two_dvd_six x))).card
        = Nat.choose 4 2 * 6 ^ 4
      ∧ Nat.choose 4 2 * 6 ^ 4 = 7776 :=
  ⟨card_supportK_of_perfectK (by norm_num) _ perfectK_fam4_L6, by decide⟩

/-- 陽性対照：層ごとの等式（周期 6）：どの 3-集合 `T` でも `2·Σ_{ν∈T}|I_{T∖ν}| = 6^4 = 1296`。 -/
theorem slice_fam4_L6 (T : Finset (Fin 4)) (hT : T.card = 3) :
    2 * ∑ ν ∈ T, (∑ x : Wp 4 6, (fam4 (T.erase ν, vOfPar two_dvd_six x)).toNat) = 6 ^ 4 :=
  two_mul_sum_card_slice perfectK_fam4_L6 hT

/-- 陽性対照：パッキング上界も同じ族で成り立つ（`2·|I| ≤ 6^4·C(4,1)`）。 -/
theorem packing_fam4_L6 :
    (1 + 1) * (cellSet 1 (fun S x => fam4 (S, vOfPar two_dvd_six x))).card
      ≤ 6 ^ 4 * Nat.choose 4 1 :=
  card_cellSet_le (packK_of_perfectK perfectK_fam4_L6)

/-- `d = 5`・`k = 0` の族：`y` のパリティ。`Perfect 0` を満たす。 -/
def par5 : Finset (Fin 5) × V 5 → Bool := fun p =>
  (Finset.univ.filter (fun i : Fin 5 => p.2 i = true)).card % 2 == 1

/-- **`1 ≤ k` は落とせない**：`k = 0` では `d = 5` でも完全な族が在る（`5 > 3·0+1 = 1`）。 -/
theorem perfect_par5 : Perfect 0 par5 := by decide +kernel

/-- **`1 ≤ k` は落とせない**：`k = 0` では `d = 5` でも（周期 2 でも周期 6 でも）
完全な族が在る（`5 > 3·0+1 = 1`）。 -/
theorem perfectK_par5_L2 :
    PerfectK (d := 5) (L := 2) 0 (fun S x => par5 (S, vOfPar (dvd_refl 2) x)) :=
  (perfectK_two_iff 0 par5).2 perfect_par5

theorem perfectK_par5_L6 :
    PerfectK (d := 5) (L := 6) 0 (fun S x => par5 (S, vOfPar two_dvd_six x)) :=
  perfectK_of_perfect two_dvd_six par5 perfect_par5

theorem par5_breaks_bound : ¬ ((5 : ℕ) ≤ 3 * 0 + 1) := by norm_num

/-- 陰性対照：`PerfectK` は空虚な条件でない——全部採る族は満たさない。 -/
theorem not_perfectK_full : ¬ PerfectK (d := 2) (L := 3) 1 (fun _ _ => true) := by decide

/-- 陰性対照：空の族も満たさない（`= 1` の側が働いている）。 -/
theorem not_perfectK_empty : ¬ PerfectK (d := 2) (L := 3) 1 (fun _ _ => false) := by decide

/-- 陰性対照：周期 3（奇数）には `k=1, d=2` の完全な族が無い（§4 から）。 -/
theorem no_perfectK_d2_L3 : ¬ ∃ I : Finset (Fin 2) → Wp 2 3 → Bool, PerfectK 1 I :=
  no_perfectK_of_odd (by norm_num) (by decide)

/-- 陰性対照（上界の側）：`3k+1 < d` は周期に依らず落ちる（`k=1, d=6, L=10`）。 -/
theorem no_perfectK_d6_k1_L10 : ¬ ∃ I : Finset (Fin 6) → Wp 6 10 → Bool, PerfectK 1 I :=
  no_perfectK_of_lt (by norm_num) (by norm_num)

end PerfectFamily

/-! ## §9 使った公理 -/

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
#print axioms PerfectFamily.flipAt_self
#print axioms PerfectFamily.flipAt_of_ne
#print axioms PerfectFamily.flipAt_flipAt
#print axioms PerfectFamily.flipAt_ne
#print axioms PerfectFamily.Perfect
#print axioms PerfectFamily.instDecidablePerfect
#print axioms PerfectFamily.support
#print axioms PerfectFamily.powersetCard_univ_eq
#print axioms PerfectFamily.PerfectK
#print axioms PerfectFamily.instDecidablePerfectK
#print axioms PerfectFamily.packK_of_perfectK
#print axioms PerfectFamily.shiftp_ne
#print axioms PerfectFamily.shiftp_eq_self_one
#print axioms PerfectFamily.faceAtK
#print axioms PerfectFamily.faceSetK
#print axioms PerfectFamily.faceAtK_injOn
#print axioms PerfectFamily.card_faceSetK
#print axioms PerfectFamily.card_faceSetK_fails_L1
#print axioms PerfectFamily.sum_eq_card_filterK
#print axioms PerfectFamily.perfectK_iff
#print axioms PerfectFamily.no_perfectK_L1
#print axioms PerfectFamily.supportK
#print axioms PerfectFamily.supportK_eq_cellSet
#print axioms PerfectFamily.supportK_card_eq
#print axioms PerfectFamily.total_incidencesK
#print axioms PerfectFamily.card_supportK_of_perfectK
#print axioms PerfectFamily.density_of_perfectK
#print axioms PerfectFamily.two_mul_sum_card_slice
#print axioms PerfectFamily.two_dvd_of_perfectK
#print axioms PerfectFamily.no_perfectK_of_odd
#print axioms PerfectFamily.two_mul_succ_dvd_of_perfectK
#print axioms PerfectFamily.no_perfectK_of_not_dvd
#print axioms PerfectFamily.dvd_iff_of_coprime
#print axioms PerfectFamily.no_perfectK_of_coprime
#print axioms PerfectFamily.no_perfectK_k4_d9
#print axioms PerfectFamily.no_perfectK_k5_d8
#print axioms PerfectFamily.no_perfectK_k3_d9
#print axioms PerfectFamily.no_perfectK_k4_d9_ten
#print axioms PerfectFamily.no_perfectK_k5_d8_six
#print axioms PerfectFamily.no_perfectK_k4_d9_L2
#print axioms PerfectFamily.no_perfectK_k5_d8_L2
#print axioms PerfectFamily.dvd_pass_k4_d9_of_five_dvd
#print axioms PerfectFamily.dvd_pass_k5_d8_of_three_dvd
#print axioms PerfectFamily.open_moduli_pass
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
#print axioms PerfectFamily.perfect_d_le_of_perfectK
#print axioms PerfectFamily.fam4
#print axioms PerfectFamily.perfect_fam4
#print axioms PerfectFamily.card_fam4
#print axioms PerfectFamily.two_dvd_six
#print axioms PerfectFamily.perfectK_fam4_L2
#print axioms PerfectFamily.perfectK_fam4_L6
#print axioms PerfectFamily.perfectK_k2_d4_iff
#print axioms PerfectFamily.bound_fam4_L6
#print axioms PerfectFamily.counting_fam4_L6
#print axioms PerfectFamily.slice_fam4_L6
#print axioms PerfectFamily.packing_fam4_L6
#print axioms PerfectFamily.par5
#print axioms PerfectFamily.perfect_par5
#print axioms PerfectFamily.perfectK_par5_L2
#print axioms PerfectFamily.perfectK_par5_L6
#print axioms PerfectFamily.par5_breaks_bound
#print axioms PerfectFamily.not_perfectK_full
#print axioms PerfectFamily.not_perfectK_empty
#print axioms PerfectFamily.no_perfectK_d2_L3
#print axioms PerfectFamily.no_perfectK_d6_k1_L10

end PerfectFamily
