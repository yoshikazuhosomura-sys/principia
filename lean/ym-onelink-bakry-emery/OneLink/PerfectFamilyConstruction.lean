/-
超立方体の「`k`-cell の完全な族」についての単独検査用の一枚版（`import Mathlib` だけ）。
`sorry` 0・`native_decide` 不使用（`decide +kernel` のみ）。
-/
import Mathlib

/-!
# `k`-cell の完全な族：密度 `1/(2(k+1))` と `d = k+2` の明示構成

周期格子 `(ℤ/2)^d` の胞体を `(S, y)`（`S ⊆ [d]`・`y ∈ F_2^d`）で表す。
`|S| = k` のものを `k`-cell と呼ぶ。`(k+1)`-cell `(T, y)` の**面**は、
`ν ∈ T` ごとの `(T∖ν, y)` と `(T∖ν, y⊕e_ν)` の `2(k+1)` 枚である
（相異なることは `PerfectFamily.card_faceSet`）。

`k`-cell の族 `A` が **完全**（`PerfectFamily.Perfect k A`）とは、
**どの `(k+1)`-cell もちょうど一枚の面を `A` に持つ**ことをいう
（`PerfectFamily.perfect_iff` がこの言い換えを与える）。

## 主な結果

* `PerfectFamily.card_support_of_perfect`：`k+1 ≤ d` のとき、完全な族の大きさ `|A|` は
  `2(k+1)·|A| = C(d,k)·2^d` を満たす
* `PerfectFamily.density_of_perfect`：したがって密度 `|A| / (C(d,k)·2^d)` は必ず
  `1/(2(k+1))` である（**`d` に依らない**）
* `PerfectFamily.Layout.perfect_fam`：`d = k+2` のとき、`[d]` を大きさ 2 と 3 の部分に
  分ける分割の上に**対ガジェット**と**三角ガジェット**を置いた族は完全である
* `PerfectFamily.exists_perfect`：`d = k+2` の完全な族は、`k` の偶奇によらず必ず在る
* `PerfectFamily.card_support_fam`：その族の大きさは `(k+2)·2^k`（＝ `d·2^{d−2}`）
* `PerfectFamily.perfect_one_iff`：`k = 1` のときこの定義は「2 次元の面の 4 本のうち
  ちょうど一本」という辺の族の版の定義と同値である
* `PerfectFamily.Layout.fam_invariant`：構成した族は `S` の内側の座標の反転で変わらない
* `PerfectFamily.perfect_fam4`・`PerfectFamily.perfect_fam5`：`k=2, d=4`（対ガジェットだけ）と
  `k=3, d=5`（三角ガジェットが要る最小の場合）を核の計算（`decide +kernel`）で閉じたもの

## ガジェット

大きさ 2 の部分 `{a,b}` には `g_{ab}(y) = y_a ⊕ y_b`、
大きさ 3 の部分 `{a,b,c}` には `g_{ab} = y_a y_b`・`g_{ac} = (1⊕y_a) y_c`・
`g_{bc} = (1⊕y_b)(1⊕y_c)` を置く。どの点 `c` でも、`c` を含む対にわたる
`Σ_{ν ≠ c} ( g_{cν}(y) + g_{cν}(y⊕e_ν) )` が `y_c + (1⊕y_c) = 1` になり
（`PerfectFamily.Layout.local_sum`）、各部分の中だけで閉じる。

## 言っていないこと

この一枚は「完全な族が在る `d` の範囲」の分類をしていない。
`d = k+2` の構成は存在の構成であって、完全な族すべての分類ではない。
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


/-! ## `d = k+2` の明示構成 -/

/-- `[d]` の分割の一つの部分。`pr a b` は大きさ 2、`tr a b c` は大きさ 3。 -/
inductive Blk (d : ℕ) where
  | pr (a b : Fin d) : Blk d
  | tr (a b c : Fin d) : Blk d
  deriving DecidableEq

namespace Blk

/-- 部分の元。 -/
def elems : Blk d → Finset (Fin d)
  | .pr a b => {a, b}
  | .tr a b c => {a, b, c}

/-- 部分の元は相異なる。 -/
def Good : Blk d → Prop
  | .pr a b => a ≠ b
  | .tr a b c => a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- 順序のない対の一致。 -/
def PairEq (u v a b : Fin d) : Prop := (u = a ∧ v = b) ∨ (u = b ∧ v = a)

instance instDecidablePairEq (u v a b : Fin d) : Decidable (PairEq u v a b) := by
  unfold PairEq; infer_instance

lemma PairEq.comm {u v a b : Fin d} (h : PairEq u v a b) : PairEq v u a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

lemma PairEq.left_mem {u v a b : Fin d} (h : PairEq u v a b) : u = a ∨ u = b := by
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr h1

lemma PairEq.right_mem {u v a b : Fin d} (h : PairEq u v a b) : v = a ∨ v = b := by
  rcases h with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact Or.inr h2
  · exact Or.inl h2

lemma PairEq.ne {u v a b : Fin d} (hab : a ≠ b) (h : PairEq u v a b) : u ≠ v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hab
  · rw [h1, h2]; exact hab.symm

/--
**ガジェット**。部分 `{a,b}`（対ガジェット）には `g_{ab} = y_a ⊕ y_b`、
部分 `{a,b,c}`（三角ガジェット）には `g_{ab} = y_a y_b`・`g_{ac} = (1⊕y_a) y_c`・
`g_{bc} = (1⊕y_b)(1⊕y_c)` を置く。それ以外の対では 0。
-/
def g : Blk d → Fin d → Fin d → V d → Bool
  | .pr a b, u, v, y => if PairEq u v a b then (y a != y b) else false
  | .tr a b c, u, v, y =>
      if PairEq u v a b then (y a && y b)
      else if PairEq u v a c then (!y a && y c)
      else if PairEq u v b c then (!y b && !y c)
      else false

lemma g_pr {a b u v : Fin d} (h : PairEq u v a b) (y : V d) :
    (Blk.pr a b).g u v y = (y a != y b) := by
  simp [g, h]

lemma g_tr_ab {a b c u v : Fin d} (h : PairEq u v a b) (y : V d) :
    (Blk.tr a b c).g u v y = (y a && y b) := by
  simp [g, h]

lemma g_tr_ac {a b c u v : Fin d} (h1 : ¬ PairEq u v a b) (h2 : PairEq u v a c) (y : V d) :
    (Blk.tr a b c).g u v y = (!y a && y c) := by
  simp [g, h1, h2]

lemma g_tr_bc {a b c u v : Fin d} (h1 : ¬ PairEq u v a b) (h2 : ¬ PairEq u v a c)
    (h3 : PairEq u v b c) (y : V d) :
    (Blk.tr a b c).g u v y = (!y b && !y c) := by
  simp [g, h1, h2, h3]

lemma g_comm (B : Blk d) (u v : Fin d) (y : V d) : B.g u v y = B.g v u y := by
  cases B with
  | pr a b =>
    simp only [g]
    by_cases h : PairEq u v a b
    · rw [if_pos h, if_pos h.comm]
    · rw [if_neg h, if_neg (fun hc : PairEq v u a b => h hc.comm)]
  | tr a b c =>
    simp only [g]
    by_cases h1 : PairEq u v a b
    · rw [if_pos h1, if_pos h1.comm]
    · rw [if_neg h1, if_neg (fun hc : PairEq v u a b => h1 hc.comm)]
      by_cases h2 : PairEq u v a c
      · rw [if_pos h2, if_pos h2.comm]
      · rw [if_neg h2, if_neg (fun hc : PairEq v u a c => h2 hc.comm)]
        by_cases h3 : PairEq u v b c
        · rw [if_pos h3, if_pos h3.comm]
        · rw [if_neg h3, if_neg (fun hc : PairEq v u b c => h3 hc.comm)]

/-- 対の片方が部分の外なら 0。 -/
lemma g_eq_false_of_right {B : Blk d} {u v : Fin d} (y : V d) (h : v ∉ B.elems) :
    B.g u v y = false := by
  cases B with
  | pr a b =>
    simp only [elems, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    simp only [g]
    rw [if_neg]
    intro hc
    rcases hc.right_mem with h1 | h1
    · exact h.1 h1
    · exact h.2 h1
  | tr a b c =>
    simp only [elems, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨ha, hb, hc⟩ := h
    simp only [g]
    rw [if_neg, if_neg, if_neg]
    · intro hcon
      rcases hcon.right_mem with h1 | h1
      · exact hb h1
      · exact hc h1
    · intro hcon
      rcases hcon.right_mem with h1 | h1
      · exact ha h1
      · exact hc h1
    · intro hcon
      rcases hcon.right_mem with h1 | h1
      · exact ha h1
      · exact hb h1

lemma g_eq_false_of_left {B : Blk d} {u v : Fin d} (y : V d) (h : u ∉ B.elems) :
    B.g u v y = false := by
  rw [g_comm]; exact g_eq_false_of_right y h

/-- 対の片方を固定すると、相手は部分の中の（自分と異なる）元でなければ 0。 -/
lemma g_eq_false_of_notMem_erase {B : Blk d} (hB : B.Good) {u v : Fin d} (y : V d)
    (h : v ∉ B.elems.erase u) : B.g u v y = false := by
  by_cases hv : v ∈ B.elems
  · have hvu : v = u := by
      by_contra hne
      exact h (Finset.mem_erase.2 ⟨hne, hv⟩)
    subst hvu
    cases B with
    | pr a b =>
      simp only [g]
      rw [if_neg]
      intro hc
      exact (hc.ne hB) rfl
    | tr a b c =>
      obtain ⟨hab, hac, hbc⟩ := hB
      simp only [g]
      rw [if_neg, if_neg, if_neg]
      · intro hc; exact (hc.ne hbc) rfl
      · intro hc; exact (hc.ne hac) rfl
      · intro hc; exact (hc.ne hab) rfl
  · exact g_eq_false_of_right y hv

/-- `g u v` は `y` の座標 `u, v` だけで決まる。 -/
lemma g_congr (B : Blk d) (u v : Fin d) {y y' : V d} (hu : y u = y' u) (hv : y v = y' v) :
    B.g u v y = B.g u v y' := by
  cases B with
  | pr a b =>
    simp only [g]
    by_cases h : PairEq u v a b
    · rw [if_pos h, if_pos h]
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hu, hv]
    · rw [if_neg h, if_neg h]
  | tr a b c =>
    simp only [g]
    by_cases h1 : PairEq u v a b
    · rw [if_pos h1, if_pos h1]
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hu, hv]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : PairEq u v a c
      · rw [if_pos h2, if_pos h2]
        rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hu, hv]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : PairEq u v b c
        · rw [if_pos h3, if_pos h3]
          rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hu, hv]
        · rw [if_neg h3, if_neg h3]

end Blk

/--
`[d]` を大きさ 2 と 3 の部分に分ける分割。`blk i` は `i` の属する部分。
-/
structure Layout (d : ℕ) where
  blk : Fin d → Blk d
  self : ∀ i, i ∈ (blk i).elems
  closed : ∀ i j, j ∈ (blk i).elems → blk j = blk i
  good : ∀ i, (blk i).Good

namespace Layout

variable (L : Layout d)

/-- 分割から決まる、対ごとの指示関数。 -/
def G (u v : Fin d) (y : V d) : Bool := (L.blk u).g u v y

lemma G_comm (u v : Fin d) (y : V d) : L.G u v y = L.G v u y := by
  by_cases h : v ∈ (L.blk u).elems
  · rw [G, G, L.closed u v h, Blk.g_comm]
  · have h2 : u ∉ (L.blk v).elems := by
      intro h2
      have hcl := L.closed v u h2
      rw [hcl] at h
      exact h (L.self v)
    rw [G, G, Blk.g_eq_false_of_right y h, Blk.g_eq_false_of_right y h2]

/-- **局所の数え上げ**：どの点 `c` でも、`c` を含む対にわたる和はちょうど 1。
対ガジェットでは `c` の相手が一つ、三角ガジェットでは二つあり、
どちらの形でも和は `y_c + (1⊕y_c) = 1` になる。 -/
theorem local_sum (c : Fin d) (y : V d) :
    ∑ ν ∈ Finset.univ.erase c, ((L.G c ν y).toNat + (L.G c ν (flipAt y ν)).toNat) = 1 := by
  classical
  have hsub : (L.blk c).elems.erase c ⊆ Finset.univ.erase c := by
    intro x hx
    rw [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, Finset.mem_univ x⟩
  have hzero : ∀ x ∈ Finset.univ.erase c, x ∉ (L.blk c).elems.erase c →
      ((L.G c x y).toNat + (L.G c x (flipAt y x)).toNat) = 0 := by
    intro x _ hx
    simp only [G]
    rw [Blk.g_eq_false_of_notMem_erase (L.good c) y hx,
      Blk.g_eq_false_of_notMem_erase (L.good c) (flipAt y x) hx]
    rfl
  rw [← Finset.sum_subset hsub hzero]
  simp only [G]
  have hc := L.self c
  have hgood := L.good c
  obtain ⟨B, hB⟩ : ∃ B, L.blk c = B := ⟨_, rfl⟩
  rw [hB] at hc hgood ⊢
  cases B with
  | pr a b =>
    simp only [Blk.elems, Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Blk.Good] at hgood
    rcases hc with rfl | rfl
    · -- `c` は対の第一成分
      have he : ({c, b} : Finset (Fin d)).erase c = {b} := by
        rw [Finset.erase_insert (by simp [hgood])]
      have e1 : flipAt y b c = y c := flipAt_of_ne y hgood
      have e2 : flipAt y b b = !y b := flipAt_self y b
      simp only [Blk.elems]
      rw [he, Finset.sum_singleton]
      simp only [Blk.g_pr (Or.inl ⟨rfl, rfl⟩ : Blk.PairEq c b c b), e1, e2]
      rcases h1 : y c with _ | _ <;> rcases h2 : y b with _ | _ <;> simp
    · -- `c` は対の第二成分
      have he : ({a, c} : Finset (Fin d)).erase c = {a} := by
        rw [Finset.erase_insert_of_ne (by simp [hgood]), Finset.erase_singleton]
        simp
      have e1 : flipAt y a c = y c := flipAt_of_ne y (Ne.symm hgood)
      have e2 : flipAt y a a = !y a := flipAt_self y a
      simp only [Blk.elems]
      rw [he, Finset.sum_singleton]
      simp only [Blk.g_pr (Or.inr ⟨rfl, rfl⟩ : Blk.PairEq c a a c), e1, e2]
      rcases h1 : y c with _ | _ <;> rcases h2 : y a with _ | _ <;> simp
  | tr a b e =>
    simp only [Blk.elems, Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Blk.Good] at hgood
    obtain ⟨hab, hae, hbe⟩ := hgood
    rcases hc with rfl | rfl | rfl
    · -- `c` は三つ組の第一成分：相手は `b`（`g = y_c y_b`）と `e`（`g = (1⊕y_c) y_e`）
      have he : ({c, b, e} : Finset (Fin d)).erase c = {b, e} := by
        rw [Finset.erase_insert (by simp [hab, hae])]
      have p1 : Blk.PairEq c b c b := Or.inl ⟨rfl, rfl⟩
      have p2 : ¬ Blk.PairEq c e c b := by
        rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact hbe h.symm
        · exact hab h
      have p3 : Blk.PairEq c e c e := Or.inl ⟨rfl, rfl⟩
      have e1 : flipAt y b c = y c := flipAt_of_ne y hab
      have e2 : flipAt y b b = !y b := flipAt_self y b
      have e3 : flipAt y e c = y c := flipAt_of_ne y hae
      have e4 : flipAt y e e = !y e := flipAt_self y e
      simp only [Blk.elems]
      rw [he, Finset.sum_pair hbe]
      simp only [Blk.g_tr_ab p1, Blk.g_tr_ac p2 p3, e1, e2, e3, e4]
      rcases h1 : y c with _ | _ <;> rcases h2 : y b with _ | _ <;>
        rcases h3 : y e with _ | _ <;> simp
    · -- `c` は三つ組の第二成分：相手は `a`（`g = y_a y_c`）と `e`（`g = (1⊕y_c)(1⊕y_e)`）
      have he : ({a, c, e} : Finset (Fin d)).erase c = {a, e} := by
        rw [Finset.erase_insert_of_ne (by simp [hab]), Finset.erase_insert (by simp [hbe])]
      have p1 : Blk.PairEq c a a c := Or.inr ⟨rfl, rfl⟩
      have p2 : ¬ Blk.PairEq c e a c := by
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hab h.symm
        · exact hae h.symm
      have p3 : ¬ Blk.PairEq c e a e := by
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hab h.symm
        · exact hbe h
      have p4 : Blk.PairEq c e c e := Or.inl ⟨rfl, rfl⟩
      have e1 : flipAt y a c = y c := flipAt_of_ne y (Ne.symm hab)
      have e2 : flipAt y a a = !y a := flipAt_self y a
      have e3 : flipAt y e c = y c := flipAt_of_ne y hbe
      have e4 : flipAt y e e = !y e := flipAt_self y e
      simp only [Blk.elems]
      rw [he, Finset.sum_pair hae]
      simp only [Blk.g_tr_ab p1, Blk.g_tr_bc p2 p3 p4, e1, e2, e3, e4]
      rcases h1 : y c with _ | _ <;> rcases h2 : y a with _ | _ <;>
        rcases h3 : y e with _ | _ <;> simp
    · -- `c` は三つ組の第三成分：相手は `a`（`g = (1⊕y_a) y_c`）と `b`（`g = (1⊕y_b)(1⊕y_c)`）
      have he : ({a, b, c} : Finset (Fin d)).erase c = {a, b} := by
        rw [Finset.erase_insert_of_ne (by simp [hae]),
          Finset.erase_insert_of_ne (by simp [hbe]), Finset.erase_singleton]
        simp
      have p1 : ¬ Blk.PairEq c a a b := by
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hae h.symm
        · exact hbe h.symm
      have p2 : Blk.PairEq c a a c := Or.inr ⟨rfl, rfl⟩
      have p3 : ¬ Blk.PairEq c b a b := by
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact hae h.symm
        · exact hbe h.symm
      have p4 : ¬ Blk.PairEq c b a c := by
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hae h.symm
        · exact hab h.symm
      have p5 : Blk.PairEq c b b c := Or.inr ⟨rfl, rfl⟩
      have e1 : flipAt y a c = y c := flipAt_of_ne y (Ne.symm hae)
      have e2 : flipAt y a a = !y a := flipAt_self y a
      have e3 : flipAt y b c = y c := flipAt_of_ne y (Ne.symm hbe)
      have e4 : flipAt y b b = !y b := flipAt_self y b
      simp only [Blk.elems]
      rw [he, Finset.sum_pair hab]
      simp only [Blk.g_tr_ac p1 p2, Blk.g_tr_bc p3 p4 p5, e1, e2, e3, e4]
      rcases h1 : y c with _ | _ <;> rcases h2 : y a with _ | _ <;>
        rcases h3 : y b with _ | _ <;> simp

/-- 分割から作る族。`S` の補集合が対 `{u,v}` のとき `G u v y`。 -/
def fam : Finset (Fin d) × V d → Bool := fun p =>
  decide (∃ u ∈ p.1ᶜ, ∃ v ∈ p.1ᶜ, u ≠ v ∧ L.G u v p.2 = true)

lemma fam_pair {S : Finset (Fin d)} {u v : Fin d} (hne : u ≠ v) (hS : Sᶜ = {u, v})
    (y : V d) : L.fam (S, y) = L.G u v y := by
  classical
  simp only [fam, hS]
  rcases hg : L.G u v y with _ | _
  · simp only [decide_eq_false_iff_not]
    rintro ⟨p, hp, q, hq, hpq, hG⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact hpq rfl
    · rw [hg] at hG; exact Bool.false_ne_true hG
    · rw [L.G_comm, hg] at hG; exact Bool.false_ne_true hG
    · exact hpq rfl
  · simp only [decide_eq_true_eq]
    exact ⟨u, by simp, v, by simp, hne, hg⟩

/-- **`d = k+2` の完全な族**：`[d]` を大きさ 2 と 3 の部分に分ける分割の上に
対ガジェットと三角ガジェットを置いた族は完全である。 -/
theorem perfect_fam {k : ℕ} (L : Layout (k + 2)) : Perfect k L.fam := by
  classical
  intro T hT y
  have hTc : (Tᶜ : Finset (Fin (k + 2))).card = 1 := by
    rw [Finset.card_compl, hT]
    simp
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hTc
  have hTeq : T = Finset.univ.erase c := by
    rw [← Finset.compl_singleton, ← hc, compl_compl]
  rw [hTeq, ← L.local_sum c y]
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hνc : ν ≠ c := (Finset.mem_erase.1 hν).1
  have hcompl : ((Finset.univ.erase c).erase ν)ᶜ = {ν, c} := by
    rw [Finset.compl_erase, Finset.compl_erase, Finset.compl_univ]
    simp
  rw [L.fam_pair hνc hcompl, L.fam_pair hνc hcompl, L.G_comm ν c y,
    L.G_comm ν c (flipAt y ν)]

lemma G_congr (u v : Fin d) {y y' : V d} (hu : y u = y' u) (hv : y v = y' v) :
    L.G u v y = L.G u v y' := Blk.g_congr _ u v hu hv

/-- 構成した族は `S` の内側の座標を反転しても変わらない。つまり
`(S, y)` と `(S, y⊕e_i)`（`i ∈ S`）が同じ胞体を指すという読みと両立する。 -/
theorem fam_invariant (S : Finset (Fin d)) (y : V d) {i : Fin d} (hi : i ∈ S) :
    L.fam (S, flipAt y i) = L.fam (S, y) := by
  have key : ∀ u ∈ Sᶜ, ∀ v ∈ Sᶜ, L.G u v (flipAt y i) = L.G u v y := by
    intro u hu v hv
    refine L.G_congr u v ?_ ?_
    · exact flipAt_of_ne y (fun hx => (Finset.mem_compl.1 hu) (by rw [hx]; exact hi))
    · exact flipAt_of_ne y (fun hx => (Finset.mem_compl.1 hv) (by rw [hx]; exact hi))
  simp only [fam]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨u, hu, v, hv, hne, hG⟩
    exact ⟨u, hu, v, hv, hne, by rw [← key u hu v hv]; exact hG⟩
  · rintro ⟨u, hu, v, hv, hne, hG⟩
    exact ⟨u, hu, v, hv, hne, by rw [key u hu v hv]; exact hG⟩

end Layout



/-! ## どの `d ≥ 2` にも大きさ 2 と 3 の分割が在る -/

/-- `d` が偶数なら `d`、奇数なら `d − 3`。`[0, evenPart d)` を対で埋め、
`d` が奇数のときだけ残る `{d−3, d−2, d−1}` に三角ガジェットを置く。 -/
def evenPart (d : ℕ) : ℕ := if d % 2 = 0 then d else d - 3

lemma evenPart_le (d : ℕ) : evenPart d ≤ d := by
  unfold evenPart; split <;> omega

lemma evenPart_even (d : ℕ) : evenPart d % 2 = 0 := by
  unfold evenPart; split <;> omega

lemma evenPart_of_even {d : ℕ} (h : d % 2 = 0) : evenPart d = d := by
  unfold evenPart; rw [if_pos h]

lemma evenPart_of_odd {d : ℕ} (h : ¬ d % 2 = 0) : evenPart d = d - 3 := by
  unfold evenPart; rw [if_neg h]

/-- **標準の分割**：`0,1` / `2,3` / … と対を作り、`d` が奇数のときは最後の三点
`{d−3, d−2, d−1}` を三つ組にする。 -/
def stdBlk (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : Blk d :=
  if h : i.val < evenPart d then
    Blk.pr ⟨2 * (i.val / 2), by
        have h1 := evenPart_le d; have h2 := evenPart_even d; have h3 := i.isLt; omega⟩
      ⟨2 * (i.val / 2) + 1, by
        have h1 := evenPart_le d; have h2 := evenPart_even d; have h3 := i.isLt; omega⟩
  else
    Blk.tr ⟨d - 3, by omega⟩ ⟨d - 2, by omega⟩ ⟨d - 1, by omega⟩

lemma stdBlk_pos {d : ℕ} (hd : 2 ≤ d) {i : Fin d} (h : i.val < evenPart d)
    {a b : Fin d} (ha : a.val = 2 * (i.val / 2)) (hb : b.val = 2 * (i.val / 2) + 1) :
    stdBlk d hd i = Blk.pr a b := by
  unfold stdBlk
  rw [dif_pos h]
  simp only [Blk.pr.injEq]
  exact ⟨Fin.ext ha.symm, Fin.ext hb.symm⟩

lemma stdBlk_neg {d : ℕ} (hd : 2 ≤ d) {i : Fin d} (h : ¬ i.val < evenPart d)
    {a b c : Fin d} (ha : a.val = d - 3) (hb : b.val = d - 2) (hc : c.val = d - 1) :
    stdBlk d hd i = Blk.tr a b c := by
  unfold stdBlk
  rw [dif_neg h]
  simp only [Blk.tr.injEq]
  exact ⟨Fin.ext ha.symm, Fin.ext hb.symm, Fin.ext hc.symm⟩

lemma stdBlk_self (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : i ∈ (stdBlk d hd i).elems := by
  have h1 := evenPart_le d
  have h2 := evenPart_even d
  have h3 := i.isLt
  by_cases h : i.val < evenPart d
  · by_cases hpar : i.val % 2 = 0
    · rw [stdBlk_pos hd h (a := i) (b := ⟨2 * (i.val / 2) + 1, by omega⟩)
        (show i.val = 2 * (i.val / 2) by omega) rfl]
      simp [Blk.elems]
    · rw [stdBlk_pos hd h (a := ⟨2 * (i.val / 2), by omega⟩) (b := i)
        rfl (show i.val = 2 * (i.val / 2) + 1 by omega)]
      simp [Blk.elems]
  · have hodd : ¬ d % 2 = 0 := by
      intro he
      rw [evenPart_of_even he] at h
      exact h h3
    have hep : evenPart d = d - 3 := evenPart_of_odd hodd
    have h' : ¬ i.val < d - 3 := by rw [← hep]; exact h
    rw [stdBlk_neg hd h (a := ⟨d - 3, by omega⟩) (b := ⟨d - 2, by omega⟩)
      (c := ⟨d - 1, by omega⟩) rfl rfl rfl]
    simp only [Blk.elems, Finset.mem_insert, Finset.mem_singleton]
    have hv : i.val = d - 3 ∨ i.val = d - 2 ∨ i.val = d - 1 := by omega
    rcases hv with h4 | h4 | h4
    · exact Or.inl (Fin.ext h4)
    · exact Or.inr (Or.inl (Fin.ext h4))
    · exact Or.inr (Or.inr (Fin.ext h4))

lemma stdBlk_good (d : ℕ) (hd : 2 ≤ d) (i : Fin d) : (stdBlk d hd i).Good := by
  have h1 := evenPart_le d
  have h2 := evenPart_even d
  have h3 := i.isLt
  by_cases h : i.val < evenPart d
  · rw [stdBlk_pos hd h (a := ⟨2 * (i.val / 2), by omega⟩)
      (b := ⟨2 * (i.val / 2) + 1, by omega⟩) rfl rfl]
    simp only [Blk.Good, ne_eq, Fin.mk.injEq]
    omega
  · have hodd : ¬ d % 2 = 0 := by
      intro he
      rw [evenPart_of_even he] at h
      exact h h3
    have hep : evenPart d = d - 3 := evenPart_of_odd hodd
    rw [stdBlk_neg hd h (a := ⟨d - 3, by omega⟩) (b := ⟨d - 2, by omega⟩)
      (c := ⟨d - 1, by omega⟩) rfl rfl rfl]
    simp only [Blk.Good, ne_eq, Fin.mk.injEq]
    omega

lemma stdBlk_closed (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) (hj : j ∈ (stdBlk d hd i).elems) :
    stdBlk d hd j = stdBlk d hd i := by
  have h1 := evenPart_le d
  have h2 := evenPart_even d
  have h3 := i.isLt
  have h4 := j.isLt
  by_cases h : i.val < evenPart d
  · rw [stdBlk_pos hd h (a := ⟨2 * (i.val / 2), by omega⟩)
      (b := ⟨2 * (i.val / 2) + 1, by omega⟩) rfl rfl] at hj ⊢
    simp only [Blk.elems, Finset.mem_insert, Finset.mem_singleton] at hj
    have hjv : j.val = 2 * (i.val / 2) ∨ j.val = 2 * (i.val / 2) + 1 := by
      rcases hj with hj | hj
      · exact Or.inl (by rw [hj])
      · exact Or.inr (by rw [hj])
    have hjlt : j.val < evenPart d := by omega
    exact stdBlk_pos hd hjlt (show (2 * (i.val / 2) : ℕ) = 2 * (j.val / 2) by omega)
      (show (2 * (i.val / 2) + 1 : ℕ) = 2 * (j.val / 2) + 1 by omega)
  · have hodd : ¬ d % 2 = 0 := by
      intro he
      rw [evenPart_of_even he] at h
      exact h h3
    have hep : evenPart d = d - 3 := evenPart_of_odd hodd
    have h' : ¬ i.val < d - 3 := by rw [← hep]; exact h
    rw [stdBlk_neg hd h (a := ⟨d - 3, by omega⟩) (b := ⟨d - 2, by omega⟩)
      (c := ⟨d - 1, by omega⟩) rfl rfl rfl] at hj ⊢
    simp only [Blk.elems, Finset.mem_insert, Finset.mem_singleton] at hj
    have hjv : j.val = d - 3 ∨ j.val = d - 2 ∨ j.val = d - 1 := by
      rcases hj with hj | hj | hj
      · exact Or.inl (by rw [hj])
      · exact Or.inr (Or.inl (by rw [hj]))
      · exact Or.inr (Or.inr (by rw [hj]))
    have hjn : ¬ j.val < evenPart d := by rw [hep]; omega
    exact stdBlk_neg hd hjn rfl rfl rfl

/-- 標準の分割（どの `d ≥ 2` にも在る）。 -/
def stdLayout (d : ℕ) (hd : 2 ≤ d) : Layout d where
  blk := stdBlk d hd
  self := stdBlk_self d hd
  closed := stdBlk_closed d hd
  good := stdBlk_good d hd

/-- **主定理**：`d = k+2` のとき `k`-cell の完全な族は必ず在る（`k` の偶奇によらない）。 -/
theorem exists_perfect (k : ℕ) :
    ∃ A : Finset (Fin (k + 2)) × V (k + 2) → Bool, Perfect k A :=
  ⟨(stdLayout (k + 2) (by omega)).fam, Layout.perfect_fam _⟩

/-! ## 構成した族の大きさ -/

lemma two_mul_choose_two (k : ℕ) : 2 * Nat.choose (k + 2) 2 = (k + 2) * (k + 1) := by
  have h1 : Nat.choose (k + 2) 2 = (k + 2) * (k + 1) / 2 := by
    simp [Nat.choose_two_right]
  obtain ⟨m, hm⟩ : Even ((k + 2) * (k + 1)) := by
    have h2 : (k + 2) * (k + 1) = (k + 1) * (k + 1 + 1) := by ring
    rw [h2]
    exact Nat.even_mul_succ_self (k + 1)
  rw [h1, hm]
  omega

/-- 構成した族の `k`-cell の個数は `(k+2)·2^k`（＝ `d·2^{d−2}`）。 -/
theorem card_support_fam (k : ℕ) (L : Layout (k + 2)) :
    (support L.fam k).card = (k + 2) * 2 ^ k := by
  have h := card_support_of_perfect (d := k + 2) (by omega) L.fam (Layout.perfect_fam L)
  have hch : Nat.choose (k + 2) k = Nat.choose (k + 2) 2 := by
    have hs := Nat.choose_symm (n := k + 2) (k := 2) (by omega)
    simpa using hs
  have key : (4 * (k + 1)) * (support L.fam k).card
      = (4 * (k + 1)) * ((k + 2) * 2 ^ k) := by
    calc (4 * (k + 1)) * (support L.fam k).card
        = 2 * (2 * (k + 1) * (support L.fam k).card) := by ring
      _ = 2 * (Nat.choose (k + 2) k * 2 ^ (k + 2)) := by rw [h]
      _ = (2 * Nat.choose (k + 2) 2) * 2 ^ (k + 2) := by rw [hch]; ring
      _ = ((k + 2) * (k + 1)) * 2 ^ (k + 2) := by rw [two_mul_choose_two]
      _ = (4 * (k + 1)) * ((k + 2) * 2 ^ k) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-! ## 小さい二例（核の計算で閉じる）

`k = 2, d = 4`（対ガジェットだけ）と `k = 3, d = 5`（三角ガジェットが要る最小の場合）。
-/

/-- `k = 2, d = 4`：分割 `{0,1} ⊔ {2,3}`、対ガジェットが二つ。 -/
def fam4 : Finset (Fin 4) × V 4 → Bool := fun p =>
  if p.1ᶜ = {0, 1} then (p.2 0 != p.2 1)
  else if p.1ᶜ = {2, 3} then (p.2 2 != p.2 3)
  else false

theorem perfect_fam4 : Perfect 2 fam4 := by decide +kernel

theorem card_fam4 : (support fam4 2).card = 16 := by decide +kernel

/-- `k = 3, d = 5`：分割 `{0,1} ⊔ {2,3,4}`、対ガジェット一つと三角ガジェット一つ。 -/
def fam5 : Finset (Fin 5) × V 5 → Bool := fun p =>
  if p.1ᶜ = {0, 1} then (p.2 0 != p.2 1)
  else if p.1ᶜ = {2, 3} then (p.2 2 && p.2 3)
  else if p.1ᶜ = {2, 4} then (!p.2 2 && p.2 4)
  else if p.1ᶜ = {3, 4} then (!p.2 3 && !p.2 4)
  else false

theorem perfect_fam5 : Perfect 3 fam5 := by decide +kernel

theorem card_fam5 : (support fam5 3).card = 40 := by decide +kernel

/-! ## 陰性対照（`decide` が機械的に真を返しているのではないことの確認） -/

/-- 空の族は完全でない。 -/
theorem not_perfect_empty4 : ¬ Perfect 2 (fun _ : Finset (Fin 4) × V 4 => false) := by
  decide +kernel

/-- 全部の `2`-cell をとった族は完全でない。 -/
theorem not_perfect_full4 : ¬ Perfect 2 (fun _ : Finset (Fin 4) × V 4 => true) := by
  decide +kernel

/-- `d = 5` で三角ガジェットを対ガジェットに替えると完全でなくなる
（`d` が奇数のとき完全マッチングでは作れないこと）。 -/
theorem not_perfect_pairs5 :
    ¬ Perfect 3 (fun p : Finset (Fin 5) × V 5 =>
      if p.1ᶜ = {0, 1} then (p.2 0 != p.2 1)
      else if p.1ᶜ = {2, 3} then (p.2 2 != p.2 3)
      else false) := by
  decide +kernel

/-! ## 一般の構成と小さい二例が同じものであることの確認

`Layout.fam` は `S` の補集合が二元のときに意味を持つので、
突き合わせは `k`-cell（`|S| = k = d−2`）の上で行う。 -/

instance instDecidableGood : ∀ B : Blk d, Decidable B.Good
  | .pr a b => by simp only [Blk.Good]; infer_instance
  | .tr a b c => by simp only [Blk.Good]; infer_instance

/-- `d = 4` の標準の分割 `{0,1} ⊔ {2,3}`。 -/
def blk4 : Fin 4 → Blk 4 := fun i => if i.val < 2 then Blk.pr 0 1 else Blk.pr 2 3

def layout4 : Layout 4 where
  blk := blk4
  self := by decide
  closed := by decide
  good := by decide

theorem fam_layout4 : ∀ p : Finset (Fin 4) × V 4, p.1.card = 2 → layout4.fam p = fam4 p := by
  decide +kernel

/-- `d = 5` の標準の分割 `{0,1} ⊔ {2,3,4}`。 -/
def blk5 : Fin 5 → Blk 5 := fun i => if i.val < 2 then Blk.pr 0 1 else Blk.tr 2 3 4

def layout5 : Layout 5 where
  blk := blk5
  self := by decide
  closed := by decide
  good := by decide

theorem fam_layout5 : ∀ p : Finset (Fin 5) × V 5, p.1.card = 3 → layout5.fam p = fam5 p := by
  decide +kernel

/-! ## 公理の確認 -/

#print axioms PerfectFamily.V
#print axioms PerfectFamily.flipAt
#print axioms PerfectFamily.flipAt_self
#print axioms PerfectFamily.flipAt_of_ne
#print axioms PerfectFamily.flipAt_flipAt
#print axioms PerfectFamily.flipAt_ne
#print axioms PerfectFamily.Perfect
#print axioms PerfectFamily.instDecidablePerfect
#print axioms PerfectFamily.faceAt
#print axioms PerfectFamily.faceSet
#print axioms PerfectFamily.faceAt_injOn
#print axioms PerfectFamily.card_faceSet
#print axioms PerfectFamily.sum_eq_card_filter
#print axioms PerfectFamily.perfect_iff
#print axioms PerfectFamily.sum_pair_faces
#print axioms PerfectFamily.perfect_one_iff
#print axioms PerfectFamily.support
#print axioms PerfectFamily.powersetCard_univ_eq
#print axioms PerfectFamily.card_V
#print axioms PerfectFamily.support_card_eq
#print axioms PerfectFamily.sum_flip
#print axioms PerfectFamily.total_incidences
#print axioms PerfectFamily.card_support_of_perfect
#print axioms PerfectFamily.density_of_perfect
#print axioms PerfectFamily.Blk
#print axioms PerfectFamily.Blk.elems
#print axioms PerfectFamily.Blk.Good
#print axioms PerfectFamily.Blk.PairEq
#print axioms PerfectFamily.Blk.instDecidablePairEq
#print axioms PerfectFamily.Blk.PairEq.comm
#print axioms PerfectFamily.Blk.PairEq.left_mem
#print axioms PerfectFamily.Blk.PairEq.right_mem
#print axioms PerfectFamily.Blk.PairEq.ne
#print axioms PerfectFamily.Blk.g
#print axioms PerfectFamily.Blk.g_pr
#print axioms PerfectFamily.Blk.g_tr_ab
#print axioms PerfectFamily.Blk.g_tr_ac
#print axioms PerfectFamily.Blk.g_tr_bc
#print axioms PerfectFamily.Blk.g_comm
#print axioms PerfectFamily.Blk.g_eq_false_of_right
#print axioms PerfectFamily.Blk.g_eq_false_of_left
#print axioms PerfectFamily.Blk.g_eq_false_of_notMem_erase
#print axioms PerfectFamily.Blk.g_congr
#print axioms PerfectFamily.Layout
#print axioms PerfectFamily.Layout.G
#print axioms PerfectFamily.Layout.G_comm
#print axioms PerfectFamily.Layout.local_sum
#print axioms PerfectFamily.Layout.fam
#print axioms PerfectFamily.Layout.fam_pair
#print axioms PerfectFamily.Layout.perfect_fam
#print axioms PerfectFamily.Layout.G_congr
#print axioms PerfectFamily.Layout.fam_invariant
#print axioms PerfectFamily.evenPart
#print axioms PerfectFamily.evenPart_le
#print axioms PerfectFamily.evenPart_even
#print axioms PerfectFamily.evenPart_of_even
#print axioms PerfectFamily.evenPart_of_odd
#print axioms PerfectFamily.stdBlk
#print axioms PerfectFamily.stdBlk_pos
#print axioms PerfectFamily.stdBlk_neg
#print axioms PerfectFamily.stdBlk_self
#print axioms PerfectFamily.stdBlk_good
#print axioms PerfectFamily.stdBlk_closed
#print axioms PerfectFamily.stdLayout
#print axioms PerfectFamily.exists_perfect
#print axioms PerfectFamily.two_mul_choose_two
#print axioms PerfectFamily.card_support_fam
#print axioms PerfectFamily.fam4
#print axioms PerfectFamily.perfect_fam4
#print axioms PerfectFamily.card_fam4
#print axioms PerfectFamily.fam5
#print axioms PerfectFamily.perfect_fam5
#print axioms PerfectFamily.card_fam5
#print axioms PerfectFamily.not_perfect_empty4
#print axioms PerfectFamily.not_perfect_full4
#print axioms PerfectFamily.not_perfect_pairs5
#print axioms PerfectFamily.instDecidableGood
#print axioms PerfectFamily.blk4
#print axioms PerfectFamily.layout4
#print axioms PerfectFamily.fam_layout4
#print axioms PerfectFamily.blk5
#print axioms PerfectFamily.layout5
#print axioms PerfectFamily.fam_layout5

end PerfectFamily
