/-
超立方体の「`k`-cell の完全な族」の**存在する次元の上界** `d ≤ 3k+1` の単独検査用の一枚版
（`import Mathlib` だけ）。`sorry` 0・`native_decide` 不使用（核の計算は `decide` と `decide +kernel` のみ）。

この一枚は既存の二枚の内容を **そのまま写した部分** と **新しい部分** からできている。
- 写した部分（文字まで同じ）：`PerfectFamilyConstruction.lean` の 49〜326 行
  （`namespace PerfectFamily` から `density_of_perfect` まで）。
  ここに `V`・`flipAt`・`Perfect`・`support`・`total_incidences`・`card_support_of_perfect`・
  `density_of_perfect` が入っている。単独検査のファイルは互いに `import` できないので写した。
- 新しい部分：`§A` 以降。`PlaquetteCounting.lean` の `k`-cell パッキング上界
  （`PackK`・`not_share_m`・`disjoint_powersetCard_of_pack`・`cellsAt`・`card_cellsAt_le`・
  `cellSet`・`card_cellSet_le`）を**この型に移した**もの（`Wp d L`・`shiftp` を
  `V d`・`flipAt` に、カリー化を対に替えた。証明の筋は同じで、文字は同じでない）と、
  二つを比べて `d ≤ 3k+1` を出す部分。
-/
import Mathlib

/-!
# `k`-cell の完全な族は `d ≤ 3k+1` の範囲にしかない（周期 2 の格子）

周期格子 `(ℤ/2)^d` の胞体を `(S, y)`（`S ⊆ [d]`・`y ∈ F_2^d`）で表し、`|S| = k` のものを
`k`-cell と呼ぶ。`(k+1)`-cell `(T, y)` の面は `ν ∈ T` ごとの `(T∖ν, y)` と `(T∖ν, y⊕e_ν)` の
`2(k+1)` 枚で、族 `A` が**完全**（`Perfect k A`）とは、どの `(k+1)`-cell も
ちょうど一枚の面を `A` に持つことをいう。

## 主な結果

* `PerfectFamily.perfect_d_le`：`1 ≤ k` かつ `k+1 ≤ d` のとき、完全な族が在れば `d ≤ 3k+1`
* `PerfectFamily.no_perfect_of_lt`：したがって `3k+1 < d` では完全な族は無い
* `PerfectFamily.card_support_le_of_packCell`：パッキング上界 `k·|A| ≤ 2^d·C(d,k−1)`
  （密度 `≤ 1/(d−k+1)`）
* `PerfectFamily.no_perfect_of_not_dvd`：割り算の検問
  `2(k+1) ∤ C(d,k)·2^d` からの非存在。`k=4,d=9`（`no_perfect_k4_d9`）と
  `k=5,d=8`（`no_perfect_k5_d8`）はこれで落ちる

## 筋

二つの数え上げを比べる。
* 完全性から（入射の数え上げ）`2(k+1)·|A| = C(d,k)·2^d`——密度はちょうど `1/(2(k+1))`
* パッキング性（`= 1` を `≤ 1` に緩めただけ）から、基点ごとに選ばれた `k`-cell の
  `(k−1)`-部分集合の族が互いに素なので `k·|A| ≤ 2^d·C(d,k−1)`——密度 `≤ 1/(d−k+1)`

`C(d,k)·k = C(d,k−1)·(d−k+1)` で割ると `d−k+1 ≤ 2(k+1)`、すなわち `d ≤ 3k+1`。

## 言っていないこと

* **周期 2 の格子に限る。**頂点は `V d = Fin d → Bool` であって、一般の周期 `L` の
  トーラスは扱っていない。割り算の検問は特に `L^d = 2^d` に依っており、
  `2(k+1) ∤ C(d,k)·2^d` は「周期 2 では無い」までしか言わない
* `1 ≤ k` は落とせない（`k = 0` の反例が `perfect_par5` にある）
* `d ≤ 3k+1` は**鋭くない**。`k=3` は `d=9 ≤ 10` だが完全な族は無いことが別に
  分かっている（この一枚には入っていない）。逆向き（どの `d ≤ 3k+1` にも在る）も
  この一枚は言っていない
* 完全な族の**分類**をしていない
-/

namespace PerfectFamily

/-- 周期格子 `(ℤ/2)^d` の頂点。 -/
abbrev V (d : ℕ) : Type := Fin d → Bool

variable {d : ℕ}

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

/-! ## 「ちょうど一枚」の意味（面は相異なる `2(k+1)` 枚） -/

/-- `(k+1)`-cell `(T, y)` の面の枠。`p = (ν, b)`：`b = false` なら `(T∖ν, y)`、
`b = true` なら `(T∖ν, y⊕e_ν)`。 -/
def faceAt (T : Finset (Fin d)) (y : V d) (p : Fin d × Bool) : Finset (Fin d) × V d :=
  (T.erase p.1, if p.2 then flipAt y p.1 else y)

/-- `(T, y)` の面の集合。 -/
def faceSet (T : Finset (Fin d)) (y : V d) : Finset (Finset (Fin d) × V d) :=
  (T ×ˢ (Finset.univ : Finset Bool)).image (faceAt T y)

lemma faceAt_injOn (T : Finset (Fin d)) (y : V d) :
    Set.InjOn (faceAt T y) ↑(T ×ˢ (Finset.univ : Finset Bool)) := by
  rintro ⟨ν, b⟩ hp ⟨μ, c⟩ hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, and_true] at hp hq
  have hνμ : ν = μ := by
    by_contra hne
    have h1 : T.erase ν = T.erase μ := congrArg Prod.fst h
    have h2 : ν ∈ T.erase μ := Finset.mem_erase.2 ⟨hne, hp⟩
    rw [← h1] at h2
    exact (Finset.notMem_erase ν T) h2
  subst hνμ
  have h3 : (if b then flipAt y ν else y) = (if c then flipAt y ν else y) := congrArg Prod.snd h
  have hbc : b = c := by
    rcases b with _ | _ <;> rcases c with _ | _
    · rfl
    · exact absurd h3.symm (flipAt_ne y ν)
    · exact absurd h3 (flipAt_ne y ν)
    · rfl
  subst hbc; rfl

/-- `(k+1)`-cell の面はちょうど `2(k+1)` 枚ある。 -/
lemma card_faceSet (T : Finset (Fin d)) (y : V d) :
    (faceSet T y).card = 2 * T.card := by
  rw [faceSet, Finset.card_image_of_injOn (faceAt_injOn T y), Finset.card_product]
  simp [Nat.mul_comm]

/-- `Perfect` の「`toNat` の和が 1」は「面のうちちょうど一枚が `A` に入る」である。 -/
lemma sum_eq_card_filter (A : Finset (Fin d) × V d → Bool) (T : Finset (Fin d)) (y : V d) :
    ∑ ν ∈ T, ((A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat)
      = ((faceSet T y).filter (fun c => A c = true)).card := by
  classical
  have hsub : ((T ×ˢ (Finset.univ : Finset Bool)).filter (fun p => A (faceAt T y p) = true))
      ⊆ T ×ˢ (Finset.univ : Finset Bool) := Finset.filter_subset _ _
  have himg : (faceSet T y).filter (fun c => A c = true)
      = ((T ×ˢ (Finset.univ : Finset Bool)).filter (fun p => A (faceAt T y p) = true)).image
          (faceAt T y) := by
    rw [faceSet, Finset.filter_image]
  rw [himg, Finset.card_image_of_injOn
    ((faceAt_injOn T y).mono (by exact_mod_cast hsub)), Finset.card_filter,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Fintype.sum_bool]
  simp [faceAt, Bool.toNat]
  rcases hy : A (T.erase ν, y) with _ | _ <;> rcases hf : A (T.erase ν, flipAt y ν) with _ | _ <;>
    simp

/-- 完全性の言い換え：どの `(k+1)`-cell についても、その `2(k+1)` 枚の面のうち
`A` に入るものがちょうど一枚。 -/
theorem perfect_iff (k : ℕ) (A : Finset (Fin d) × V d → Bool) :
    Perfect k A ↔ ∀ T : Finset (Fin d), T.card = k + 1 → ∀ y : V d,
      ((faceSet T y).filter (fun c => A c = true)).card = 1 := by
  unfold Perfect
  constructor
  · intro h T hT y; rw [← sum_eq_card_filter]; exact h T hT y
  · intro h T hT y; rw [sum_eq_card_filter]; exact h T hT y

/-! ## `k = 1` のとき（辺の族の版との突き合わせ）

`k = 1` の胞体は辺 `({μ}, z)` で、`2`-cell は 2 次元の面である。このとき上の定義は
「どの面も 4 本の辺のうちちょうど一本を族に持つ」に書き下される——辺の族の版の定義
（方向 `μ` と位置 `z` で辺を表し、面 `(μ, ν, z)` の 4 本 `(μ,z)`・`(μ,z+e_ν)`・`(ν,z)`・`(ν,z+e_μ)`
のうちちょうど一本）と同じ形である。位置の正規化（`z μ = z ν = false`）は要らない。
-/

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

/-! ## 密度 -/

/-- `A` に入る `k`-cell の集合。 -/
def support (A : Finset (Fin d) × V d → Bool) (k : ℕ) : Finset (Finset (Fin d) × V d) :=
  Finset.univ.filter (fun c => c.1.card = k ∧ A c = true)

lemma powersetCard_univ_eq (k : ℕ) :
    Finset.powersetCard k (Finset.univ : Finset (Fin d))
      = Finset.univ.filter (fun S : Finset (Fin d) => S.card = k) := by
  ext S
  simp

lemma card_V (d : ℕ) : Fintype.card (V d) = 2 ^ d := by
  simp [V]

lemma support_card_eq (A : Finset (Fin d) × V d → Bool) (k : ℕ) :
    (support A k).card
      = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)), ∑ y : V d, (A (S, y)).toNat := by
  classical
  rw [support, Finset.card_filter, Fintype.sum_prod_type, powersetCard_univ_eq,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : S.card = k
  · simp only [h, if_true, true_and]
    refine Finset.sum_congr rfl fun y _ => ?_
    rcases hA : A (S, y) with _ | _ <;> simp
  · simp [h]

/-- `y ↦ y⊕e_ν` は `V d` の全単射だから、`A (S, ·)` の個数は変わらない。 -/
lemma sum_flip (A : Finset (Fin d) × V d → Bool) (S : Finset (Fin d)) (ν : Fin d) :
    ∑ y : V d, (A (S, flipAt y ν)).toNat = ∑ y : V d, (A (S, y)).toNat := by
  refine Fintype.sum_bijective (fun y : V d => flipAt y ν) ?_ _ _ (fun y => rfl)
  exact Function.Involutive.bijective (fun x => flipAt_flipAt x ν)

/-- 入射の数え上げ：`(k+1)`-cell の側から数えた面の総数は、`A` の `k`-cell の側から
数えた `2(d−k)` 倍に等しい。 -/
lemma total_incidences (A : Finset (Fin d) × V d → Bool) (k : ℕ) :
    ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)), ∑ y : V d,
        ∑ ν ∈ T, ((A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat)
      = 2 * (d - k) * (support A k).card := by
  classical
  -- まず ∑_T ∑_y を ∑_y ∑_T に入れ替える
  rw [Finset.sum_comm]
  have key : ∀ y : V d,
      ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)),
          ∑ ν ∈ T, ((A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat)
        = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)),
            ∑ ν ∈ Sᶜ, ((A (S, y)).toNat + (A (S, flipAt y ν)).toNat) := by
    intro y
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
  rw [Finset.sum_congr rfl (fun y _ => key y)]
  -- ∑_y ∑_S ∑_{ν∈Sᶜ} → ∑_S ∑_{ν∈Sᶜ} ∑_y
  rw [Finset.sum_comm]
  rw [support_card_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.sum_comm]
  have hcard : (Sᶜ : Finset (Fin d)).card = d - k := by
    rw [Finset.card_compl, Finset.mem_powersetCard_univ.1 hS]
    simp
  have step : ∀ ν ∈ (Sᶜ : Finset (Fin d)),
      ∑ y : V d, ((A (S, y)).toNat + (A (S, flipAt y ν)).toNat)
        = 2 * ∑ y : V d, (A (S, y)).toNat := by
    intro ν _
    rw [Finset.sum_add_distrib, sum_flip]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_const, hcard]
  ring

/-- **完全な族の大きさ**：`k+1 ≤ d` のとき、完全な族の `k`-cell の個数 `|A|` は
`2(k+1)|A| = C(d,k)·2^d` を満たす。 -/
theorem card_support_of_perfect {k : ℕ} (hk : k + 1 ≤ d)
    (A : Finset (Fin d) × V d → Bool) (hA : Perfect k A) :
    2 * (k + 1) * (support A k).card = Nat.choose d k * 2 ^ d := by
  classical
  have h1 : ∑ T ∈ Finset.powersetCard (k + 1) (Finset.univ : Finset (Fin d)), ∑ y : V d,
      ∑ ν ∈ T, ((A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat)
      = Nat.choose d (k + 1) * 2 ^ d := by
    rw [Finset.sum_congr rfl (fun T hT => by
      refine Finset.sum_congr rfl fun y _ => hA T (Finset.mem_powersetCard_univ.1 hT) y)]
    simp [Finset.card_powersetCard, Finset.card_univ, Finset.sum_const]
  rw [total_incidences] at h1
  -- 2(d−k)|A| = C(d,k+1)·2^d と C(d,k+1)(k+1) = C(d,k)(d−k) から
  have h2 : (d - k) * (2 * (k + 1) * (support A k).card)
      = (d - k) * (Nat.choose d k * 2 ^ d) := by
    calc (d - k) * (2 * (k + 1) * (support A k).card)
        = (k + 1) * (2 * (d - k) * (support A k).card) := by ring
      _ = (k + 1) * (Nat.choose d (k + 1) * 2 ^ d) := by rw [h1]
      _ = (Nat.choose d (k + 1) * (k + 1)) * 2 ^ d := by ring
      _ = (Nat.choose d k * (d - k)) * 2 ^ d := by rw [Nat.choose_succ_right_eq]
      _ = (d - k) * (Nat.choose d k * 2 ^ d) := by ring
  have hpos : 0 < d - k := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos h2

/-- **密度は必ず `1/(2(k+1))`**（`d` に依らない）。 -/
theorem density_of_perfect {k : ℕ} (hk : k + 1 ≤ d)
    (A : Finset (Fin d) × V d → Bool) (hA : Perfect k A) :
    ((support A k).card : ℚ) / ((Nat.choose d k : ℚ) * 2 ^ d) = 1 / (2 * (k + 1)) := by
  have h := card_support_of_perfect hk A hA
  have hq : ((support A k).card : ℚ) * (2 * ((k : ℚ) + 1)) = (Nat.choose d k : ℚ) * 2 ^ d := by
    have h' := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at h'
    linarith
  have hck : (0:ℚ) < (Nat.choose d k : ℚ) := by
    exact_mod_cast Nat.choose_pos (show k ≤ d by omega)
  have hc : (0:ℚ) < (Nat.choose d k : ℚ) * 2 ^ d := by positivity
  have hd2 : (0:ℚ) < 2 * ((k:ℚ) + 1) := by positivity
  rw [div_eq_div_iff (ne_of_gt hc) (ne_of_gt hd2)]
  linarith

/-! ## §A パッキング上界（`PlaquetteCounting.lean` の `k`-cell 版をこの型に移したもの）

添字の対応：`PlaquetteCounting.PackK m` は大きさ `m+1` の胞体の族についての条件だから、
ここでの `PackCell k` は `PackK (k−1)` に当たる（`k` で直に添字を付ける）。
-/

/-- `(k+1)`-cell `(T, y)` の面 `ν` に載っている `A` の個数（`(T∖ν, y)` と `(T∖ν, y⊕e_ν)`）。 -/
def faceCount (A : Finset (Fin d) × V d → Bool) (T : Finset (Fin d)) (y : V d)
    (ν : Fin d) : ℕ :=
  (A (T.erase ν, y)).toNat + (A (T.erase ν, flipAt y ν)).toNat

/-- `PackCell k A`：`k`-cell の族 `A` が、どの `(k+1)`-cell についても高々一枚の面しか
持たない。`Perfect k A` の `= 1` を `≤ 1` に緩めたもの。 -/
def PackCell (k : ℕ) (A : Finset (Fin d) × V d → Bool) : Prop :=
  ∀ T : Finset (Fin d), T.card = k + 1 → ∀ y : V d,
    ∑ ν ∈ T, faceCount A T y ν ≤ 1

instance instDecidablePackCell (k : ℕ) (A : Finset (Fin d) × V d → Bool) :
    Decidable (PackCell k A) := by
  unfold PackCell; infer_instance

/-- 完全な族はパッキングである（`= 1` から `≤ 1`）。 -/
theorem packCell_of_perfect {k : ℕ} {A : Finset (Fin d) × V d → Bool} (hA : Perfect k A) :
    PackCell k A := fun T hT y => le_of_eq (hA T hT y)

/--
**芯 (i)**：同じ基点 `y` で選ばれた二つの `(m+1)`-cell は、`m` 個の方向を共有できない。
`T = S ∪ S'` は `(m+2)`-cell で、`S = T∖{a}`・`S' = T∖{b}`（`a ≠ b`）はその面だから。
（`S ≠ S'` は仮定に要らない——`|S ∩ S'| = m < m+1 = |S|` から従う。）
-/
theorem not_share {m : ℕ} {A : Finset (Fin d) × V d → Bool} (h : PackCell (m + 1) A)
    {S S' : Finset (Fin d)} {y : V d} (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (hint : (S ∩ S').card = m) (h1 : A (S, y) = true) (h2 : A (S', y) = true) :
    False := by
  classical
  have hUI := Finset.card_union_add_card_inter S S'
  have hUcard : (S ∪ S').card = m + 1 + 1 := by omega
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
  have hsum := h (S ∪ S') hUcard y
  have hfa : 1 ≤ faceCount A (S ∪ S') y a := by simp [faceCount, hea, h1]
  have hfb : 1 ≤ faceCount A (S ∪ S') y b := by simp [faceCount, heb, h2]
  have hsplit : faceCount A (S ∪ S') y a + ∑ ν ∈ (S ∪ S').erase a, faceCount A (S ∪ S') y ν
      = ∑ ν ∈ S ∪ S', faceCount A (S ∪ S') y ν :=
    Finset.add_sum_erase _ _ haT
  have hbmem : b ∈ (S ∪ S').erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hbT⟩
  have hfble : faceCount A (S ∪ S') y b ≤ ∑ ν ∈ (S ∪ S').erase a, faceCount A (S ∪ S') y ν :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hbmem
  omega

/-- 選ばれた二つの `(m+1)`-cell の `m`-部分集合の族は互いに素（芯 (i) の言い換え）。 -/
theorem disjoint_powersetCard_of_packCell {m : ℕ} {A : Finset (Fin d) × V d → Bool}
    (h : PackCell (m + 1) A) {y : V d} {S S' : Finset (Fin d)}
    (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (h1 : A (S, y) = true) (h2 : A (S', y) = true) (hne : S ≠ S') :
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
  exact not_share h hS hS' (by omega) h1 h2

/-- 基点 `y` で選ばれた `k`-cell の方向集合の族 `F(y)`。 -/
def cellsAt (k : ℕ) (A : Finset (Fin d) × V d → Bool) (y : V d) :
    Finset (Finset (Fin d)) :=
  Finset.univ.filter (fun S => S.card = k ∧ A (S, y) = true)

/-- **基点ごとの上界**：`k·|F(y)| ≤ C(d, k−1)`（`k = m+1`）。
`F(y)` の成員の `m`-部分集合は各 `m+1` 個あって互いに素で、全部 `Fin d` の `m`-部分集合。 -/
theorem card_cellsAt_le {m : ℕ} {A : Finset (Fin d) × V d → Bool}
    (h : PackCell (m + 1) A) (y : V d) :
    (m + 1) * (cellsAt (m + 1) A y).card ≤ d.choose m := by
  classical
  have hmem : ∀ S ∈ cellsAt (m + 1) A y, S.card = m + 1 ∧ A (S, y) = true := by
    intro S hS
    simpa [cellsAt] using hS
  have hdisj : ((cellsAt (m + 1) A y : Finset (Finset (Fin d))) :
      Set (Finset (Fin d))).PairwiseDisjoint (fun S => S.powersetCard m) := by
    intro S hS S' hS' hne
    simp only [Function.onFun]
    have hSm := hmem S (Finset.mem_coe.1 hS)
    have hS'm := hmem S' (Finset.mem_coe.1 hS')
    exact disjoint_powersetCard_of_packCell h hSm.1 hS'm.1 hSm.2 hS'm.2 hne
  have hcard : ((cellsAt (m + 1) A y).biUnion (fun S => S.powersetCard m)).card
      = ∑ S ∈ cellsAt (m + 1) A y, (S.powersetCard m).card := Finset.card_biUnion hdisj
  have hterm : ∀ S ∈ cellsAt (m + 1) A y, (S.powersetCard m).card = m + 1 := by
    intro S hS
    rw [Finset.card_powersetCard, (hmem S hS).1, Nat.choose_succ_self_right]
  have hsum : ∑ S ∈ cellsAt (m + 1) A y, (S.powersetCard m).card
      = ∑ _S ∈ cellsAt (m + 1) A y, (m + 1) := Finset.sum_congr rfl hterm
  have hsub : (cellsAt (m + 1) A y).biUnion (fun S => S.powersetCard m)
      ⊆ (Finset.univ : Finset (Fin d)).powersetCard m := by
    intro R hR
    obtain ⟨S, _, hRS⟩ := Finset.mem_biUnion.1 hR
    rw [Finset.mem_powersetCard] at hRS ⊢
    exact ⟨Finset.subset_univ R, hRS.2⟩
  calc (m + 1) * (cellsAt (m + 1) A y).card
      = ((cellsAt (m + 1) A y).biUnion (fun S => S.powersetCard m)).card := by
        rw [hcard, hsum, Finset.sum_const, smul_eq_mul]; ring
    _ ≤ ((Finset.univ : Finset (Fin d)).powersetCard m).card := Finset.card_le_card hsub
    _ = d.choose m := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- `support` を基点ごとに分ける。 -/
lemma card_support_eq_sum_cellsAt (A : Finset (Fin d) × V d → Bool) (k : ℕ) :
    (support A k).card = ∑ y : V d, (cellsAt k A y).card := by
  classical
  rw [support, Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun y _ => by rw [cellsAt, Finset.card_filter]

/--
**パッキング上界**（`k = m+1`）：`k·|A| ≤ 2^d·C(d, k−1)`。
`k`-cell の総数は `2^d·C(d,k)` なので、密度は `C(d,k−1)/(k·C(d,k)) = 1/(d−k+1)` 以下。
-/
theorem card_support_le_of_packCell {m : ℕ} {A : Finset (Fin d) × V d → Bool}
    (h : PackCell (m + 1) A) :
    (m + 1) * (support A (m + 1)).card ≤ 2 ^ d * d.choose m := by
  rw [card_support_eq_sum_cellsAt, Finset.mul_sum]
  calc ∑ y : V d, (m + 1) * (cellsAt (m + 1) A y).card
      ≤ ∑ _y : V d, d.choose m := Finset.sum_le_sum fun y _ => card_cellsAt_le h y
    _ = 2 ^ d * d.choose m := by
        rw [Finset.sum_const, Finset.card_univ, card_V, smul_eq_mul]

/-- 密度の形のパッキング上界：`|A| / (C(d,k)·2^d) ≤ 1/(d−k+1)`（`k = m+1`・`d−k+1 = d−m`）。 -/
theorem density_le_of_packCell {m : ℕ} (hk : m + 1 ≤ d) {A : Finset (Fin d) × V d → Bool}
    (h : PackCell (m + 1) A) :
    ((support A (m + 1)).card : ℚ) / ((Nat.choose d (m + 1) : ℚ) * 2 ^ d)
      ≤ 1 / ((d - m : ℕ) : ℚ) := by
  have hN := card_support_le_of_packCell h
  have hchoose : Nat.choose d (m + 1) * (m + 1) = Nat.choose d m * (d - m) :=
    Nat.choose_succ_right_eq d m
  have hdmn : 0 < d - m := by omega
  have hpos : (0:ℚ) < ((d - m : ℕ) : ℚ) := by exact_mod_cast hdmn
  have hcq : (0:ℚ) < (Nat.choose d (m + 1) : ℚ) := by exact_mod_cast Nat.choose_pos hk
  have hden : (0:ℚ) < (Nat.choose d (m + 1) : ℚ) * 2 ^ d := by positivity
  have hq : ((m : ℚ) + 1) * ((support A (m + 1)).card : ℚ)
      ≤ 2 ^ d * (Nat.choose d m : ℚ) := by exact_mod_cast hN
  have hchq : (Nat.choose d (m + 1) : ℚ) * ((m : ℚ) + 1)
      = (Nat.choose d m : ℚ) * ((d - m : ℕ) : ℚ) := by exact_mod_cast hchoose
  have hm1 : (0:ℚ) < (m : ℚ) + 1 := by positivity
  rw [div_le_div_iff₀ hden hpos]
  refine le_of_mul_le_mul_right ?_ hm1
  calc ((support A (m + 1)).card : ℚ) * ((d - m : ℕ) : ℚ) * ((m : ℚ) + 1)
      = (((m : ℚ) + 1) * ((support A (m + 1)).card : ℚ)) * ((d - m : ℕ) : ℚ) := by ring
    _ ≤ (2 ^ d * (Nat.choose d m : ℚ)) * ((d - m : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_right hq (le_of_lt hpos)
    _ = 2 ^ d * ((Nat.choose d m : ℚ) * ((d - m : ℕ) : ℚ)) := by ring
    _ = 2 ^ d * ((Nat.choose d (m + 1) : ℚ) * ((m : ℚ) + 1)) := by rw [hchq]
    _ = (1 : ℚ) * ((Nat.choose d (m + 1) : ℚ) * 2 ^ d) * ((m : ℚ) + 1) := by ring

/-! ## §B 二つを比べる：`d ≤ 3k+1` -/

/-- **主定理（`k = m+1` の形）**：周期 2 の格子で `(m+1)`-cell の完全な族が在れば
`d ≤ 3(m+1)+1`。 -/
theorem perfect_d_le_succ {m : ℕ} (hk : m + 2 ≤ d) (A : Finset (Fin d) × V d → Bool)
    (hA : Perfect (m + 1) A) : d ≤ 3 * (m + 1) + 1 := by
  have hE : 2 * (m + 1 + 1) * (support A (m + 1)).card = Nat.choose d (m + 1) * 2 ^ d :=
    card_support_of_perfect (by omega) A hA
  have hP : (m + 1) * (support A (m + 1)).card ≤ 2 ^ d * d.choose m :=
    card_support_le_of_packCell (packCell_of_perfect hA)
  have hkey : (Nat.choose d m * 2 ^ d) * (d - m)
      ≤ (Nat.choose d m * 2 ^ d) * (2 * (m + 2)) := by
    calc (Nat.choose d m * 2 ^ d) * (d - m)
        = (Nat.choose d m * (d - m)) * 2 ^ d := by ring
      _ = (Nat.choose d (m + 1) * (m + 1)) * 2 ^ d := by rw [Nat.choose_succ_right_eq]
      _ = (m + 1) * (Nat.choose d (m + 1) * 2 ^ d) := by ring
      _ = (m + 1) * (2 * (m + 1 + 1) * (support A (m + 1)).card) := by rw [hE]
      _ = (2 * (m + 2)) * ((m + 1) * (support A (m + 1)).card) := by ring
      _ ≤ (2 * (m + 2)) * (2 ^ d * d.choose m) := Nat.mul_le_mul_left _ hP
      _ = (Nat.choose d m * 2 ^ d) * (2 * (m + 2)) := by ring
  have hc : 0 < Nat.choose d m := Nat.choose_pos (by omega)
  have h2 : 0 < 2 ^ d := Nat.two_pow_pos d
  have hpos : 0 < Nat.choose d m * 2 ^ d := Nat.mul_pos hc h2
  have hfin := Nat.le_of_mul_le_mul_left hkey hpos
  omega

/-- **主定理**：周期 2 の格子で `1 ≤ k` かつ `k+1 ≤ d` のとき、`k`-cell の完全な族が
在れば `d ≤ 3k+1`。 -/
theorem perfect_d_le {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ d)
    (A : Finset (Fin d) × V d → Bool) (hA : Perfect k A) : d ≤ 3 * k + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact perfect_d_le_succ (by omega) A hA

/-- **非存在**：`3k+1 < d` なら（周期 2 の格子に）完全な族は無い。 -/
theorem no_perfect_of_lt {k : ℕ} (hk1 : 1 ≤ k) (hd : 3 * k + 1 < d) :
    ¬ ∃ A : Finset (Fin d) × V d → Bool, Perfect k A := by
  rintro ⟨A, hA⟩
  have := perfect_d_le hk1 (by omega) A hA
  omega

/-- `k = 1` への特殊化：辺の族（プラケットごとにちょうど一本）は `d ≤ 4` でしか在らない。 -/
theorem perfect_one_d_le_four (hd : 2 ≤ d) (A : Finset (Fin d) × V d → Bool)
    (hA : Perfect 1 A) : d ≤ 4 := by
  have := perfect_d_le (k := 1) le_rfl (by omega) A hA
  omega

/-- 構成（`d = k+2`）は上界に矛盾しない：`1 ≤ k` のとき `k+2 ≤ 3k+1`。 -/
theorem construction_within_bound {k : ℕ} (hk : 1 ≤ k) : k + 2 ≤ 3 * k + 1 := by omega

/-- 上界が等号になるのは `d = 3k+1` のときだけ、という形（比べた不等式そのもの）。 -/
theorem perfect_sub_le {m : ℕ} (hk : m + 2 ≤ d) (A : Finset (Fin d) × V d → Bool)
    (hA : Perfect (m + 1) A) : d - m ≤ 2 * (m + 2) := by
  have := perfect_d_le_succ hk A hA
  omega

/-! ## §C 割り算の検問（周期 2 に限る） -/

/-- 完全な族が在れば `2(k+1) ∣ C(d,k)·2^d`。 -/
theorem two_mul_succ_dvd_of_perfect {k : ℕ} (hk : k + 1 ≤ d)
    (A : Finset (Fin d) × V d → Bool) (hA : Perfect k A) :
    2 * (k + 1) ∣ Nat.choose d k * 2 ^ d :=
  ⟨(support A k).card, (card_support_of_perfect hk A hA).symm⟩

/-- **割り算の検問からの非存在**（周期 2 に限る）。 -/
theorem no_perfect_of_not_dvd {k : ℕ} (hk : k + 1 ≤ d)
    (h : ¬ (2 * (k + 1) ∣ Nat.choose d k * 2 ^ d)) :
    ¬ ∃ A : Finset (Fin d) × V d → Bool, Perfect k A := by
  rintro ⟨A, hA⟩
  exact h (two_mul_succ_dvd_of_perfect hk A hA)

/-- `k = 4`・`d = 9`：`10 ∤ C(9,4)·2^9 = 64512` なので完全な族は無い（**周期 2 に限る**）。 -/
theorem no_perfect_k4_d9 : ¬ ∃ A : Finset (Fin 9) × V 9 → Bool, Perfect 4 A :=
  no_perfect_of_not_dvd (by norm_num) (by decide)

/-- `k = 5`・`d = 8`：`12 ∤ C(8,5)·2^8 = 14336` なので完全な族は無い（**周期 2 に限る**）。 -/
theorem no_perfect_k5_d8 : ¬ ∃ A : Finset (Fin 8) × V 8 → Bool, Perfect 5 A :=
  no_perfect_of_not_dvd (by norm_num) (by decide)

/-- 検問に使った二つの数（`d` に依らない読み替えを避けるため明示）。 -/
theorem dvd_values : Nat.choose 9 4 * 2 ^ 9 = 64512 ∧ Nat.choose 8 5 * 2 ^ 8 = 14336 := by
  constructor <;> decide

/-- 陽性対照：`k=2, d=4`（完全な族が在ることが別に分かっている枡）は検問を**通る**
——検問がすべてを落としているのではない。 -/
theorem dvd_pass_k2_d4 : 2 * (2 + 1) ∣ Nat.choose 4 2 * 2 ^ 4 := by decide

/-- 陽性対照：`k=3, d=9` も検問を通る（`8 ∣ 43008`）。この枡に完全な族が無いことは
別の道（この一枚には無い）でしか出ない——検問は `k=4,d=9` に効いて `k=3,d=9` に効かない。 -/
theorem dvd_pass_k3_d9 : 2 * (3 + 1) ∣ Nat.choose 9 3 * 2 ^ 9 := by decide

/-- 上界も `k=3, d=9` を落とさない（`9 ≤ 3·3+1 = 10`）。 -/
theorem bound_pass_k3_d9 : (9:ℕ) ≤ 3 * 3 + 1 := by norm_num

/-! ## §D 陽性対照：実在する完全な族に主定理を当てる

`k = 2, d = 4` の族（`PerfectFamilyConstruction.lean` の 890〜898 行をそのまま写した。
文字まで同じ）。`Perfect k A` に実例が在るので、主定理は空虚でない。
-/

/-- `k = 2, d = 4`：分割 `{0,1} ⊔ {2,3}`、対ガジェットが二つ。 -/
def fam4 : Finset (Fin 4) × V 4 → Bool := fun p =>
  if p.1ᶜ = {0, 1} then (p.2 0 != p.2 1)
  else if p.1ᶜ = {2, 3} then (p.2 2 != p.2 3)
  else false

theorem perfect_fam4 : Perfect 2 fam4 := by decide +kernel

theorem card_fam4 : (support fam4 2).card = 16 := by decide +kernel

/-- 主定理をこの族に当てる（`4 ≤ 3·2+1 = 7`）。 -/
theorem bound_fam4 : (4:ℕ) ≤ 3 * 2 + 1 :=
  perfect_d_le (by norm_num) (by norm_num) fam4 perfect_fam4

/-- 同じ族で二つの数え上げの両方が成り立つ：
密度の等式 `2·3·16 = 96 = C(4,2)·2^4` と、パッキング上界 `2·16 = 32 ≤ 64 = 2^4·C(4,1)`。
`d = 4 < 7 = 3k+1` なので上界には余裕がある（等号は `d = 3k+1` のときだけ）。 -/
theorem fam4_numbers :
    2 * (2 + 1) * (support fam4 2).card = Nat.choose 4 2 * 2 ^ 4
      ∧ (1 + 1) * (support fam4 (1 + 1)).card ≤ 2 ^ 4 * Nat.choose 4 1 :=
  ⟨card_support_of_perfect (by norm_num) fam4 perfect_fam4,
   card_support_le_of_packCell (packCell_of_perfect perfect_fam4)⟩

/-! ## §E 対照（仮定が働いていることの確認） -/

/-- `d = 5`・`k = 0` の族：`y` のパリティ。`Perfect 0` を満たす。 -/
def par5 : Finset (Fin 5) × V 5 → Bool := fun p =>
  (Finset.univ.filter (fun i : Fin 5 => p.2 i = true)).card % 2 == 1

/-- **`1 ≤ k` は落とせない**：`k = 0` では `d = 5` でも完全な族が在る（`5 > 3·0+1 = 1`）。 -/
theorem perfect_par5 : Perfect 0 par5 := by decide +kernel

theorem par5_breaks_bound : ¬ ((5:ℕ) ≤ 3 * 0 + 1) := by norm_num

/-- 陰性対照：全部の `1`-cell を採る族はパッキングでない（`PackCell` は空虚な条件でない）。 -/
theorem not_packCell_full : ¬ PackCell (d := 2) 1 (fun _ : Finset (Fin 2) × V 2 => true) := by decide

/-- 陽性対照（自明な側）：空の族はどんな `k` でもパッキング。 -/
theorem packCell_empty (k : ℕ) : PackCell (d := d) k (fun _ : Finset (Fin d) × V d => false) := by
  intro T _ y
  simp [faceCount]

end PerfectFamily

/-! ## 使った公理 -/

namespace PerfectFamily

#print axioms PerfectFamily.V
#print axioms PerfectFamily.flipAt
#print axioms PerfectFamily.Perfect
#print axioms PerfectFamily.perfect_iff
#print axioms PerfectFamily.perfect_one_iff
#print axioms PerfectFamily.support
#print axioms PerfectFamily.card_V
#print axioms PerfectFamily.support_card_eq
#print axioms PerfectFamily.sum_flip
#print axioms PerfectFamily.total_incidences
#print axioms PerfectFamily.card_support_of_perfect
#print axioms PerfectFamily.density_of_perfect
#print axioms PerfectFamily.faceCount
#print axioms PerfectFamily.PackCell
#print axioms PerfectFamily.instDecidablePackCell
#print axioms PerfectFamily.packCell_of_perfect
#print axioms PerfectFamily.not_share
#print axioms PerfectFamily.disjoint_powersetCard_of_packCell
#print axioms PerfectFamily.cellsAt
#print axioms PerfectFamily.card_cellsAt_le
#print axioms PerfectFamily.card_support_eq_sum_cellsAt
#print axioms PerfectFamily.card_support_le_of_packCell
#print axioms PerfectFamily.density_le_of_packCell
#print axioms PerfectFamily.perfect_d_le_succ
#print axioms PerfectFamily.perfect_d_le
#print axioms PerfectFamily.no_perfect_of_lt
#print axioms PerfectFamily.perfect_one_d_le_four
#print axioms PerfectFamily.construction_within_bound
#print axioms PerfectFamily.perfect_sub_le
#print axioms PerfectFamily.two_mul_succ_dvd_of_perfect
#print axioms PerfectFamily.no_perfect_of_not_dvd
#print axioms PerfectFamily.no_perfect_k4_d9
#print axioms PerfectFamily.no_perfect_k5_d8
#print axioms PerfectFamily.dvd_values
#print axioms PerfectFamily.dvd_pass_k2_d4
#print axioms PerfectFamily.dvd_pass_k3_d9
#print axioms PerfectFamily.bound_pass_k3_d9
#print axioms PerfectFamily.fam4
#print axioms PerfectFamily.perfect_fam4
#print axioms PerfectFamily.card_fam4
#print axioms PerfectFamily.bound_fam4
#print axioms PerfectFamily.fam4_numbers
#print axioms PerfectFamily.par5
#print axioms PerfectFamily.perfect_par5
#print axioms PerfectFamily.par5_breaks_bound
#print axioms PerfectFamily.not_packCell_full
#print axioms PerfectFamily.packCell_empty

end PerfectFamily
