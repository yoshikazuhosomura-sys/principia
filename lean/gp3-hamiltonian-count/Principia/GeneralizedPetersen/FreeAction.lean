import Mathlib
import Principia.GeneralizedPetersen.Small

/-!
# Principia.GeneralizedPetersen.FreeAction

  自由な反復写像からの可除性 `dvd_card_of_iterate_free`（`Finset` の言葉）と、
  `n = 7, …, 15` の明示的な閉路リストの上での回転の自由性。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### 1. 有限集合上の自由な反復作用（一般部） -/

section General

variable {α : Type*}

/-- `Finset` を保つ写像から作った置換の `i` 乗の値は、写像の `i` 回反復である。 -/
theorem val_pow (S : Finset α) (g : α → α) (f : Equiv.Perm ↥S)
    (hf : ∀ x : ↥S, ((f x : ↥S) : α) = g (x : α)) :
    ∀ (i : ℕ) (x : ↥S), (((f ^ i) x : ↥S) : α) = g^[i] (x : α) := by
  intro i
  induction i with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      have h1 : (((f ^ (k + 1)) x : ↥S) : α) = (((f ^ k) (f x) : ↥S) : α) := by
        rw [pow_succ, Equiv.Perm.mul_apply]
      rw [h1, ih (f x), hf x, Function.iterate_succ_apply]

/-- **接続の要**：有限集合 `S` を保つ写像 `g` が `g^[n] = id`（`S` 上）で、
  `0 < i < n` のとき `g^[i]` が `S` の点を動かさないことが無いなら、`n ∣ S.card`。
  `Small` の `card_dvd_of_perm_free`（段階 2）を `Finset` と写像の言葉に直したもの。 -/
theorem dvd_card_of_iterate_free (S : Finset α) (g : α → α) (n : ℕ) (hn : 0 < n)
    (hmap : ∀ a ∈ S, g a ∈ S)
    (hidn : ∀ a ∈ S, g^[n] a = a)
    (hfree : ∀ i, 0 < i → i < n → ∀ a ∈ S, g^[i] a ≠ a) :
    n ∣ S.card := by
  classical
  have hback : ∀ x : ↥S, g^[n - 1] (g (x : α)) = (x : α) := by
    intro x
    have h : g^[n - 1 + 1] (x : α) = (x : α) := by
      rw [Nat.sub_add_cancel hn]; exact hidn _ x.2
    rwa [Function.iterate_succ_apply] at h
  set F : ↥S → ↥S := fun x => ⟨g (x : α), hmap _ x.2⟩ with hFdef
  have hinj : Function.Injective F := by
    intro x y hxy
    have hg : g (x : α) = g (y : α) := congrArg Subtype.val hxy
    exact Subtype.ext (by rw [← hback x, ← hback y, hg])
  have hbij : Function.Bijective F := (Finite.injective_iff_bijective).mp hinj
  set f : Equiv.Perm ↥S := Equiv.ofBijective F hbij with hfdef
  have hf : ∀ x : ↥S, ((f x : ↥S) : α) = g (x : α) := fun _ => rfl
  have hfn : f ^ n = 1 := by
    refine Equiv.ext fun x => ?_
    have h := val_pow S g f hf n x
    rw [hidn _ x.2] at h
    change (f ^ n) x = x
    exact Subtype.ext h
  have hfree' : ∀ i, 0 < i → i < n → ∀ x : ↥S, (f ^ i) x ≠ x := by
    intro i hi hin x hx
    have h := val_pow S g f hf i x
    rw [hx] at h
    exact hfree i hi hin _ x.2 h.symm
  have hd := GeneralizedPetersen.Small.card_dvd_of_perm_free f n hn hfn hfree'
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at hd

/-- 族で述べた版（`G i` が「`i` 回作用させた結果」）。各 `n` の `decide` を
  「反復」ではなく「一回の作用」で済ませるためにこの形を使う。 -/
theorem dvd_card_of_family_free (S : Finset α) (G : ℕ → α → α) (n : ℕ) (hn : 0 < n)
    (hmap : ∀ a ∈ S, G 1 a ∈ S)
    (hid0 : ∀ a ∈ S, G 0 a = a)
    (hcomp : ∀ i < n, ∀ a ∈ S, G 1 (G i a) = G (i + 1) a)
    (hidn : ∀ a ∈ S, G n a = a)
    (hfree : ∀ i, 0 < i → i < n → ∀ a ∈ S, G i a ≠ a) :
    n ∣ S.card := by
  have key : ∀ i ≤ n, ∀ a ∈ S, (G 1)^[i] a = G i a := by
    intro i
    induction i with
    | zero =>
        intro _ a ha
        simp only [Function.iterate_zero_apply]
        exact (hid0 a ha).symm
    | succ k ih =>
        intro hk a ha
        rw [Function.iterate_succ_apply', ih (by omega) a ha, hcomp k (by omega) a ha]
  refine dvd_card_of_iterate_free S (G 1) n hn hmap ?_ ?_
  · intro a ha; rw [key n le_rfl a ha]; exact hidn a ha
  · intro i hi hin a ha; rw [key i (le_of_lt hin) a ha]; exact hfree i hi hin a ha

end General

/-! ### 2. 正準化と回転の作用 -/

/-- 頂点 0 の位置（無ければ長さ）。 -/
def idx0 : List ℕ → ℕ
  | [] => 0
  | (v :: t) => if v = 0 then 0 else idx0 t + 1

/-- 閉路の頂点列（0 を含む長さ `N` の列）を正準形に直す：
  0 を先頭に回して 0 を落とし、第 2 頂点 < 最終頂点になる向きを選ぶ。
  結果は `HamRep` の表現（`0 :: ·` を付けると閉路になる列）と同じ形。 -/
def canon (l : List ℕ) : List ℕ :=
  match l.drop (idx0 l) ++ l.take (idx0 l) with
  | [] => []
  | (_ :: m) => if m.headD 0 < m.reverse.headD 0 then m else m.reverse

/-- 回転 `ρ^d`（外輪 `i ↦ i+d`・内輪 `i' ↦ (i+d)'`）が正準形の頂点列に誘導する作用。 -/
def ract (n d : ℕ) (l : List ℕ) : List ℕ := canon (List.map (rho n d) (0 :: l))

/-- `HamRep` は決定可能（`decide` で回すため）。 -/
instance decHamRep (N AMD : ℕ) (l : List ℕ) : Decidable (HamRep N AMD l) :=
  decidable_of_iff (l.length = N - 1 ∧ l.Nodup ∧ 0 ∉ l ∧ cycB N AMD l = true) Iff.rfl

end GeneralizedPetersen.FreeAction

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### GP(7,3) の正準向きハミルトン閉路（7 本） -/

/-- `HamRep 14 AMD7` を満たす頂点列の全体（Python が列挙。全部であることは `L7_eq`）。 -/
def L7 : List (List ℕ) :=
  [[1, 2, 9, 13, 6, 5, 12, 8, 11, 4, 3, 10, 7],
  [1, 8, 11, 4, 3, 2, 9, 12, 5, 6, 13, 10, 7],
  [1, 8, 12, 5, 4, 11, 7, 10, 3, 2, 9, 13, 6],
  [1, 8, 12, 9, 2, 3, 10, 13, 6, 5, 4, 11, 7],
  [6, 5, 12, 8, 1, 2, 9, 13, 10, 3, 4, 11, 7],
  [6, 13, 9, 12, 5, 4, 11, 8, 1, 2, 3, 10, 7],
  [6, 13, 10, 3, 4, 5, 12, 9, 2, 1, 8, 11, 7]]

theorem hamL7 : ∀ l ∈ L7, HamRep 14 AMD7 l := by decide

theorem ndL7 : L7.Nodup := by decide

theorem lenL7 : L7.length = 7 := by decide

/-- **段階 1 との接続**：`L7` は `HamRep` を満たす頂点列のちょうど全体である。
  （⊆ は `hamL7`（decide）、= は核計算が出した個数 7 との濃度の一致。） -/
theorem L7_eq : ∀ l : List ℕ, l ∈ L7 ↔ HamRep 14 AMD7 l := by
  obtain ⟨S, hmem, hcard, -⟩ := GP7_hc_card
  have hsub : L7.toFinset ⊆ S := fun l hl =>
    (hmem l).mpr (hamL7 l (List.mem_toFinset.mp hl))
  have hc : L7.toFinset.card = 7 := by
    rw [List.toFinset_card_of_nodup ndL7, lenL7]
  have hle : S.card ≤ L7.toFinset.card := by rw [hcard, hc]
  have heq : L7.toFinset = S := Finset.eq_of_subset_of_card_le hsub hle
  intro l
  rw [← List.mem_toFinset, heq, hmem]

/-! ### 回転の作用 `ract 7` の性質（すべて明示的なリスト上の decide） -/

/-- (i) `ract 7 1` は `L7` を `L7` に写す（`ρ` が自己同型だから隣接は保たれ、
  `Nodup`・`0 ∉ ·` も保たれ、正準化が `HamRep` の形に合う——を実例で確かめたもの）。 -/
theorem ractMem7 : ∀ a ∈ L7, ract 7 1 a ∈ L7 := by decide +kernel

/-- `ract 7 0` は恒等（`ρ^0 = id`）。 -/
theorem ractZero7 : ∀ a ∈ L7, ract 7 0 a = a := by decide +kernel

/-- (ii) 合成則：`ract 1 ∘ ract i = ract (i+1)`（`L7` 上）。これで
  `(ract 1)^[i] = ract i` が帰納法で出る（`dvd_card_of_family_free`）。 -/
theorem ractComp7 : ∀ i < 7, ∀ a ∈ L7, ract 7 1 (ract 7 i a) = ract 7 (i + 1) a := by
  decide +kernel

/-- (iii) 位数 `7`：`ract 7 7` は恒等。 -/
theorem ractOrd7 : ∀ a ∈ L7, ract 7 7 a = a := by decide +kernel

/-! ### `ract` が本当に ρ の作用であること、そして不動点なし -/

/-- **意味の橋**：`ract 7 i l` は「閉路 `0 :: l` を `ρ^i` で写した閉路」の
  正準表現である——両者の **辺集合** が一致する。
  （これがあるので (iv) の「`ract` の不動点なし」は「`ρ^i` 不変な閉路なし」と同じ内容になる。） -/
theorem ractEmask7 : ∀ i < 8, ∀ l ∈ L7,
    emask 14 (0 :: ract 7 i l) = emask 14 (List.map (rho 7 i) (0 :: l)) := by decide +kernel

/-- 段階 3：非自明な回転 `ρ^d` で不変な閉路は無い。
  核で列挙を回していた（`n = 13, 15` はメモリが足りなかった）。
  ここでは明示的なリスト上の decide なので `n = 13, 15` も通る。 -/
theorem no_rho_fixed7L : ∀ l ∈ L7, ∀ d < 7, 0 < d →
    emask 14 (List.map (rho 7 d) (0 :: l)) ≠ emask 14 (0 :: l) := by decide +kernel

/-- 同じことを `HamRep` の言葉で（`Small` の `no_rho_fixed7'` と同形。`n = 13, 15` も）。 -/
theorem no_rho_fixed7' : ∀ l : List ℕ, HamRep 14 AMD7 l → ∀ d < 7, 0 < d →
    emask 14 (List.map (rho 7 d) (0 :: l)) ≠ emask 14 (0 :: l) :=
  fun l hl => no_rho_fixed7L l ((L7_eq l).mpr hl)

/-- (iv) **不動点なし**：`0 < i < 7` なら `ract 7 i` はどの閉路も固定しない。
  段階 3（`no_rho_fixed7L`）と意味の橋（`ractEmask7`）から出る——
  「`ract` が固定する ⟹ 辺集合が `ρ^i` 不変」だから。 -/
theorem ractFree7 : ∀ i < 7, 0 < i → ∀ a ∈ L7, ract 7 i a ≠ a := by
  intro i hi hi0 a ha h
  have e := ractEmask7 i (by omega) a ha
  rw [h] at e
  exact no_rho_fixed7L a ha i hi hi0 e.symm

/-! ### 主定理 -/

/-- **回転の自由作用から**：`7 ∣ (閉路の個数)`。
  段階 1 の核計算の **値**（7）は使わない——`dvd_card_of_family_free` に
  (i)〜(iv) を渡すだけで割り切れが出る。 -/
theorem gp7_dvd_by_rotation : 7 ∣ L7.toFinset.card :=
  dvd_card_of_family_free L7.toFinset (ract 7) 7 (by norm_num)
    (fun a ha => List.mem_toFinset.mpr (ractMem7 a (List.mem_toFinset.mp ha)))
    (fun a ha => ractZero7 a (List.mem_toFinset.mp ha))
    (fun i hi a ha => ractComp7 i hi a (List.mem_toFinset.mp ha))
    (fun a ha => ractOrd7 a (List.mem_toFinset.mp ha))
    (fun i hi hin a ha => ractFree7 i hin hi a (List.mem_toFinset.mp ha))

/-- **主定理**：`GP(7,3)` の正準向きハミルトン閉路の集合 `S` について
  `7 ∣ S.card` が **回転 ρ の自由作用から** 出る（段階 2 ＋ 段階 3。
  段階 1 の個数を数える核計算は、`S` が `L7` で汲み尽くされていること
  〈`L7_eq`〉を言うためだけに使う）。併せて `S.card = 7` も述べる。 -/
theorem GP7_dvd_rot : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 14 AMD7 l) ∧ 7 ∣ S.card ∧ S.card = 7 := by
  refine ⟨L7.toFinset, ?_, gp7_dvd_by_rotation, ?_⟩
  · intro l; rw [List.mem_toFinset]; exact L7_eq l
  · rw [List.toFinset_card_of_nodup ndL7, lenL7]

/-- 表現の取り方によらない形：`HamRep 14 AMD7` を満たす頂点列全体の `Finset` は
  （どう取っても `L7.toFinset` に等しいので）濃度が `7` で割れる。 -/
theorem GP7_dvd_any (S : Finset (List ℕ))
    (hS : ∀ l : List ℕ, l ∈ S ↔ HamRep 14 AMD7 l) : 7 ∣ S.card := by
  have hSL : S = L7.toFinset := by
    ext l; rw [List.mem_toFinset, L7_eq l, hS l]
  rw [hSL]
  exact gp7_dvd_by_rotation

end GeneralizedPetersen.FreeAction

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### GP(9,3) の正準向きハミルトン閉路（9 本） -/

/-- `HamRep 18 AMD9` を満たす頂点列の全体（Python が列挙。全部であることは `L9_eq`）。 -/
def L9 : List (List ℕ) :=
  [[1, 2, 3, 4, 13, 10, 16, 7, 8, 17, 11, 14, 5, 6, 15, 12, 9],
  [1, 2, 3, 12, 9, 15, 6, 7, 16, 10, 13, 4, 5, 14, 11, 17, 8],
  [1, 2, 11, 17, 14, 5, 6, 15, 9, 12, 3, 4, 13, 10, 16, 7, 8],
  [1, 10, 13, 16, 7, 8, 17, 14, 11, 2, 3, 4, 5, 6, 15, 12, 9],
  [1, 10, 16, 13, 4, 5, 6, 7, 8, 17, 14, 11, 2, 3, 12, 15, 9],
  [1, 10, 16, 13, 4, 5, 14, 17, 11, 2, 3, 12, 9, 15, 6, 7, 8],
  [8, 7, 6, 5, 14, 17, 11, 2, 1, 10, 16, 13, 4, 3, 12, 15, 9],
  [8, 17, 11, 14, 5, 4, 3, 2, 1, 10, 13, 16, 7, 6, 15, 12, 9],
  [8, 17, 14, 11, 2, 1, 10, 13, 16, 7, 6, 5, 4, 3, 12, 15, 9]]

theorem hamL9 : ∀ l ∈ L9, HamRep 18 AMD9 l := by decide

theorem ndL9 : L9.Nodup := by decide

theorem lenL9 : L9.length = 9 := by decide

/-- **段階 1 との接続**：`L9` は `HamRep` を満たす頂点列のちょうど全体である。
  （⊆ は `hamL9`（decide）、= は核計算が出した個数 9 との濃度の一致。） -/
theorem L9_eq : ∀ l : List ℕ, l ∈ L9 ↔ HamRep 18 AMD9 l := by
  obtain ⟨S, hmem, hcard, -⟩ := GP9_hc_card
  have hsub : L9.toFinset ⊆ S := fun l hl =>
    (hmem l).mpr (hamL9 l (List.mem_toFinset.mp hl))
  have hc : L9.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup ndL9, lenL9]
  have hle : S.card ≤ L9.toFinset.card := by rw [hcard, hc]
  have heq : L9.toFinset = S := Finset.eq_of_subset_of_card_le hsub hle
  intro l
  rw [← List.mem_toFinset, heq, hmem]

/-! ### 回転の作用 `ract 9` の性質（すべて明示的なリスト上の decide） -/

/-- (i) `ract 9 1` は `L9` を `L9` に写す（`ρ` が自己同型だから隣接は保たれ、
  `Nodup`・`0 ∉ ·` も保たれ、正準化が `HamRep` の形に合う——を実例で確かめたもの）。 -/
theorem ractMem9 : ∀ a ∈ L9, ract 9 1 a ∈ L9 := by decide +kernel

/-- `ract 9 0` は恒等（`ρ^0 = id`）。 -/
theorem ractZero9 : ∀ a ∈ L9, ract 9 0 a = a := by decide +kernel

/-- (ii) 合成則：`ract 1 ∘ ract i = ract (i+1)`（`L9` 上）。これで
  `(ract 1)^[i] = ract i` が帰納法で出る（`dvd_card_of_family_free`）。 -/
theorem ractComp9 : ∀ i < 9, ∀ a ∈ L9, ract 9 1 (ract 9 i a) = ract 9 (i + 1) a := by
  decide +kernel

/-- (iii) 位数 `9`：`ract 9 9` は恒等。 -/
theorem ractOrd9 : ∀ a ∈ L9, ract 9 9 a = a := by decide +kernel

/-! ### `ract` が本当に ρ の作用であること、そして不動点なし -/

/-- **意味の橋**：`ract 9 i l` は「閉路 `0 :: l` を `ρ^i` で写した閉路」の
  正準表現である——両者の **辺集合** が一致する。
  （これがあるので (iv) の「`ract` の不動点なし」は「`ρ^i` 不変な閉路なし」と同じ内容になる。） -/
theorem ractEmask9 : ∀ i < 10, ∀ l ∈ L9,
    emask 18 (0 :: ract 9 i l) = emask 18 (List.map (rho 9 i) (0 :: l)) := by decide +kernel

/-- 段階 3：非自明な回転 `ρ^d` で不変な閉路は無い。
  核で列挙を回していた（`n = 13, 15` はメモリが足りなかった）。
  ここでは明示的なリスト上の decide なので `n = 13, 15` も通る。 -/
theorem no_rho_fixed9L : ∀ l ∈ L9, ∀ d < 9, 0 < d →
    emask 18 (List.map (rho 9 d) (0 :: l)) ≠ emask 18 (0 :: l) := by decide +kernel

/-- 同じことを `HamRep` の言葉で（`Small` の `no_rho_fixed7'` と同形。`n = 13, 15` も）。 -/
theorem no_rho_fixed9' : ∀ l : List ℕ, HamRep 18 AMD9 l → ∀ d < 9, 0 < d →
    emask 18 (List.map (rho 9 d) (0 :: l)) ≠ emask 18 (0 :: l) :=
  fun l hl => no_rho_fixed9L l ((L9_eq l).mpr hl)

/-- (iv) **不動点なし**：`0 < i < 9` なら `ract 9 i` はどの閉路も固定しない。
  段階 3（`no_rho_fixed9L`）と意味の橋（`ractEmask9`）から出る——
  「`ract` が固定する ⟹ 辺集合が `ρ^i` 不変」だから。 -/
theorem ractFree9 : ∀ i < 9, 0 < i → ∀ a ∈ L9, ract 9 i a ≠ a := by
  intro i hi hi0 a ha h
  have e := ractEmask9 i (by omega) a ha
  rw [h] at e
  exact no_rho_fixed9L a ha i hi hi0 e.symm

/-! ### 主定理 -/

/-- **回転の自由作用から**：`9 ∣ (閉路の個数)`。
  段階 1 の核計算の **値**（9）は使わない——`dvd_card_of_family_free` に
  (i)〜(iv) を渡すだけで割り切れが出る。 -/
theorem gp9_dvd_by_rotation : 9 ∣ L9.toFinset.card :=
  dvd_card_of_family_free L9.toFinset (ract 9) 9 (by norm_num)
    (fun a ha => List.mem_toFinset.mpr (ractMem9 a (List.mem_toFinset.mp ha)))
    (fun a ha => ractZero9 a (List.mem_toFinset.mp ha))
    (fun i hi a ha => ractComp9 i hi a (List.mem_toFinset.mp ha))
    (fun a ha => ractOrd9 a (List.mem_toFinset.mp ha))
    (fun i hi hin a ha => ractFree9 i hin hi a (List.mem_toFinset.mp ha))

/-- **主定理**：`GP(9,3)` の正準向きハミルトン閉路の集合 `S` について
  `9 ∣ S.card` が **回転 ρ の自由作用から** 出る（段階 2 ＋ 段階 3。
  段階 1 の個数を数える核計算は、`S` が `L9` で汲み尽くされていること
  〈`L9_eq`〉を言うためだけに使う）。併せて `S.card = 9` も述べる。 -/
theorem GP9_dvd_rot : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 18 AMD9 l) ∧ 9 ∣ S.card ∧ S.card = 9 := by
  refine ⟨L9.toFinset, ?_, gp9_dvd_by_rotation, ?_⟩
  · intro l; rw [List.mem_toFinset]; exact L9_eq l
  · rw [List.toFinset_card_of_nodup ndL9, lenL9]

/-- 表現の取り方によらない形：`HamRep 18 AMD9` を満たす頂点列全体の `Finset` は
  （どう取っても `L9.toFinset` に等しいので）濃度が `9` で割れる。 -/
theorem GP9_dvd_any (S : Finset (List ℕ))
    (hS : ∀ l : List ℕ, l ∈ S ↔ HamRep 18 AMD9 l) : 9 ∣ S.card := by
  have hSL : S = L9.toFinset := by
    ext l; rw [List.mem_toFinset, L9_eq l, hS l]
  rw [hSL]
  exact gp9_dvd_by_rotation

end GeneralizedPetersen.FreeAction

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### GP(11,3) の正準向きハミルトン閉路（11 本） -/

/-- `HamRep 22 AMD11` を満たす頂点列の全体（Python が列挙。全部であることは `L11_eq`）。 -/
def L11 : List (List ℕ) :=
  [[1, 2, 13, 16, 5, 6, 17, 14, 3, 4, 15, 12, 20, 9, 10, 21, 18, 7, 8, 19, 11],
  [1, 12, 15, 4, 5, 6, 17, 20, 9, 10, 21, 18, 7, 8, 19, 16, 13, 2, 3, 14, 11],
  [1, 12, 15, 4, 5, 16, 13, 2, 3, 14, 11, 19, 8, 9, 20, 17, 6, 7, 18, 21, 10],
  [1, 12, 20, 9, 10, 21, 13, 2, 3, 4, 15, 18, 7, 8, 19, 16, 5, 6, 17, 14, 11],
  [1, 12, 20, 9, 10, 21, 18, 15, 4, 5, 16, 13, 2, 3, 14, 17, 6, 7, 8, 19, 11],
  [1, 12, 20, 17, 6, 7, 18, 15, 4, 5, 16, 19, 8, 9, 10, 21, 13, 2, 3, 14, 11],
  [10, 9, 20, 17, 6, 5, 16, 19, 8, 7, 18, 21, 13, 2, 1, 12, 15, 4, 3, 14, 11],
  [10, 21, 13, 2, 1, 12, 15, 18, 7, 6, 17, 20, 9, 8, 19, 16, 5, 4, 3, 14, 11],
  [10, 21, 13, 2, 1, 12, 20, 9, 8, 7, 18, 15, 4, 3, 14, 17, 6, 5, 16, 19, 11],
  [10, 21, 13, 16, 5, 4, 15, 18, 7, 6, 17, 14, 3, 2, 1, 12, 20, 9, 8, 19, 11],
  [10, 21, 18, 7, 6, 5, 16, 13, 2, 1, 12, 15, 4, 3, 14, 17, 20, 9, 8, 19, 11]]

theorem hamL11 : ∀ l ∈ L11, HamRep 22 AMD11 l := by decide

theorem ndL11 : L11.Nodup := by decide

theorem lenL11 : L11.length = 11 := by decide

/-- **段階 1 との接続**：`L11` は `HamRep` を満たす頂点列のちょうど全体である。
  （⊆ は `hamL11`（decide）、= は核計算が出した個数 11 との濃度の一致。） -/
theorem L11_eq : ∀ l : List ℕ, l ∈ L11 ↔ HamRep 22 AMD11 l := by
  obtain ⟨S, hmem, hcard, -⟩ := GP11_hc_card
  have hsub : L11.toFinset ⊆ S := fun l hl =>
    (hmem l).mpr (hamL11 l (List.mem_toFinset.mp hl))
  have hc : L11.toFinset.card = 11 := by
    rw [List.toFinset_card_of_nodup ndL11, lenL11]
  have hle : S.card ≤ L11.toFinset.card := by rw [hcard, hc]
  have heq : L11.toFinset = S := Finset.eq_of_subset_of_card_le hsub hle
  intro l
  rw [← List.mem_toFinset, heq, hmem]

/-! ### 回転の作用 `ract 11` の性質（すべて明示的なリスト上の decide） -/

/-- (i) `ract 11 1` は `L11` を `L11` に写す（`ρ` が自己同型だから隣接は保たれ、
  `Nodup`・`0 ∉ ·` も保たれ、正準化が `HamRep` の形に合う——を実例で確かめたもの）。 -/
theorem ractMem11 : ∀ a ∈ L11, ract 11 1 a ∈ L11 := by decide +kernel

/-- `ract 11 0` は恒等（`ρ^0 = id`）。 -/
theorem ractZero11 : ∀ a ∈ L11, ract 11 0 a = a := by decide +kernel

/-- (ii) 合成則：`ract 1 ∘ ract i = ract (i+1)`（`L11` 上）。これで
  `(ract 1)^[i] = ract i` が帰納法で出る（`dvd_card_of_family_free`）。 -/
theorem ractComp11 : ∀ i < 11, ∀ a ∈ L11, ract 11 1 (ract 11 i a) = ract 11 (i + 1) a := by
  decide +kernel

/-- (iii) 位数 `11`：`ract 11 11` は恒等。 -/
theorem ractOrd11 : ∀ a ∈ L11, ract 11 11 a = a := by decide +kernel

/-! ### `ract` が本当に ρ の作用であること、そして不動点なし -/

/-- **意味の橋**：`ract 11 i l` は「閉路 `0 :: l` を `ρ^i` で写した閉路」の
  正準表現である——両者の **辺集合** が一致する。
  （これがあるので (iv) の「`ract` の不動点なし」は「`ρ^i` 不変な閉路なし」と同じ内容になる。） -/
theorem ractEmask11 : ∀ i < 12, ∀ l ∈ L11,
    emask 22 (0 :: ract 11 i l) = emask 22 (List.map (rho 11 i) (0 :: l)) := by decide +kernel

/-- 段階 3：非自明な回転 `ρ^d` で不変な閉路は無い。
  核で列挙を回していた（`n = 13, 15` はメモリが足りなかった）。
  ここでは明示的なリスト上の decide なので `n = 13, 15` も通る。 -/
theorem no_rho_fixed11L : ∀ l ∈ L11, ∀ d < 11, 0 < d →
    emask 22 (List.map (rho 11 d) (0 :: l)) ≠ emask 22 (0 :: l) := by decide +kernel

/-- 同じことを `HamRep` の言葉で（`Small` の `no_rho_fixed7'` と同形。`n = 13, 15` も）。 -/
theorem no_rho_fixed11' : ∀ l : List ℕ, HamRep 22 AMD11 l → ∀ d < 11, 0 < d →
    emask 22 (List.map (rho 11 d) (0 :: l)) ≠ emask 22 (0 :: l) :=
  fun l hl => no_rho_fixed11L l ((L11_eq l).mpr hl)

/-- (iv) **不動点なし**：`0 < i < 11` なら `ract 11 i` はどの閉路も固定しない。
  段階 3（`no_rho_fixed11L`）と意味の橋（`ractEmask11`）から出る——
  「`ract` が固定する ⟹ 辺集合が `ρ^i` 不変」だから。 -/
theorem ractFree11 : ∀ i < 11, 0 < i → ∀ a ∈ L11, ract 11 i a ≠ a := by
  intro i hi hi0 a ha h
  have e := ractEmask11 i (by omega) a ha
  rw [h] at e
  exact no_rho_fixed11L a ha i hi hi0 e.symm

/-! ### 主定理 -/

/-- **回転の自由作用から**：`11 ∣ (閉路の個数)`。
  段階 1 の核計算の **値**（11）は使わない——`dvd_card_of_family_free` に
  (i)〜(iv) を渡すだけで割り切れが出る。 -/
theorem gp11_dvd_by_rotation : 11 ∣ L11.toFinset.card :=
  dvd_card_of_family_free L11.toFinset (ract 11) 11 (by norm_num)
    (fun a ha => List.mem_toFinset.mpr (ractMem11 a (List.mem_toFinset.mp ha)))
    (fun a ha => ractZero11 a (List.mem_toFinset.mp ha))
    (fun i hi a ha => ractComp11 i hi a (List.mem_toFinset.mp ha))
    (fun a ha => ractOrd11 a (List.mem_toFinset.mp ha))
    (fun i hi hin a ha => ractFree11 i hin hi a (List.mem_toFinset.mp ha))

/-- **主定理**：`GP(11,3)` の正準向きハミルトン閉路の集合 `S` について
  `11 ∣ S.card` が **回転 ρ の自由作用から** 出る（段階 2 ＋ 段階 3。
  段階 1 の個数を数える核計算は、`S` が `L11` で汲み尽くされていること
  〈`L11_eq`〉を言うためだけに使う）。併せて `S.card = 11` も述べる。 -/
theorem GP11_dvd_rot : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 22 AMD11 l) ∧ 11 ∣ S.card ∧ S.card = 11 := by
  refine ⟨L11.toFinset, ?_, gp11_dvd_by_rotation, ?_⟩
  · intro l; rw [List.mem_toFinset]; exact L11_eq l
  · rw [List.toFinset_card_of_nodup ndL11, lenL11]

/-- 表現の取り方によらない形：`HamRep 22 AMD11` を満たす頂点列全体の `Finset` は
  （どう取っても `L11.toFinset` に等しいので）濃度が `11` で割れる。 -/
theorem GP11_dvd_any (S : Finset (List ℕ))
    (hS : ∀ l : List ℕ, l ∈ S ↔ HamRep 22 AMD11 l) : 11 ∣ S.card := by
  have hSL : S = L11.toFinset := by
    ext l; rw [List.mem_toFinset, L11_eq l, hS l]
  rw [hSL]
  exact gp11_dvd_by_rotation

end GeneralizedPetersen.FreeAction

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### GP(13,3) の正準向きハミルトン閉路（26 本） -/

/-- `HamRep 26 AMD13` を満たす頂点列の全体（Python が列挙。全部であることは `L13_eq`）。 -/
def L13 : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 6, 7, 8, 21, 18, 15, 25, 12, 11, 24, 14, 17, 20, 23, 10, 9, 22, 19, 16, 13],
  [1, 2, 3, 4, 5, 6, 7, 20, 17, 14, 24, 11, 10, 23, 13, 16, 19, 22, 9, 8, 21, 18, 15, 25, 12],
  [1, 2, 3, 4, 5, 6, 19, 16, 13, 23, 10, 9, 22, 25, 15, 18, 21, 8, 7, 20, 17, 14, 24, 11, 12],
  [1, 2, 3, 4, 5, 18, 15, 25, 22, 9, 8, 21, 24, 14, 17, 20, 7, 6, 19, 16, 13, 23, 10, 11, 12],
  [1, 2, 3, 4, 17, 14, 24, 21, 8, 7, 20, 23, 13, 16, 19, 6, 5, 18, 15, 25, 22, 9, 10, 11, 12],
  [1, 2, 3, 16, 13, 23, 20, 7, 6, 19, 22, 25, 15, 18, 5, 4, 17, 14, 24, 21, 8, 9, 10, 11, 12],
  [1, 2, 15, 18, 5, 4, 3, 16, 19, 6, 7, 20, 17, 14, 24, 21, 8, 9, 22, 25, 12, 11, 10, 23, 13],
  [1, 2, 15, 25, 12, 11, 10, 23, 20, 7, 8, 9, 22, 19, 6, 5, 18, 21, 24, 14, 17, 4, 3, 16, 13],
  [1, 2, 15, 25, 12, 11, 24, 14, 17, 20, 23, 10, 9, 22, 19, 6, 7, 8, 21, 18, 5, 4, 3, 16, 13],
  [1, 2, 15, 25, 22, 19, 6, 5, 18, 21, 24, 14, 17, 4, 3, 16, 13, 23, 20, 7, 8, 9, 10, 11, 12],
  [1, 14, 17, 4, 3, 2, 15, 18, 5, 6, 7, 20, 23, 10, 9, 8, 21, 24, 11, 12, 25, 22, 19, 16, 13],
  [1, 14, 17, 4, 3, 2, 15, 18, 5, 6, 19, 16, 13, 23, 20, 7, 8, 21, 24, 11, 10, 9, 22, 25, 12],
  [1, 14, 17, 20, 23, 10, 9, 8, 7, 6, 5, 4, 3, 2, 15, 18, 21, 24, 11, 12, 25, 22, 19, 16, 13],
  [1, 14, 24, 11, 10, 9, 22, 19, 6, 7, 8, 21, 18, 5, 4, 17, 20, 23, 13, 16, 3, 2, 15, 25, 12],
  [1, 14, 24, 11, 10, 23, 13, 16, 19, 22, 9, 8, 21, 18, 5, 6, 7, 20, 17, 4, 3, 2, 15, 25, 12],
  [1, 14, 24, 21, 18, 5, 4, 17, 20, 23, 13, 16, 3, 2, 15, 25, 22, 19, 6, 7, 8, 9, 10, 11, 12],
  [1, 14, 24, 21, 18, 15, 2, 3, 16, 19, 6, 5, 4, 17, 20, 7, 8, 9, 22, 25, 12, 11, 10, 23, 13],
  [1, 14, 24, 21, 18, 15, 2, 3, 16, 19, 22, 25, 12, 11, 10, 9, 8, 7, 6, 5, 4, 17, 20, 23, 13],
  [12, 11, 10, 9, 8, 7, 6, 5, 18, 21, 24, 14, 1, 2, 15, 25, 22, 19, 16, 3, 4, 17, 20, 23, 13],
  [12, 11, 24, 14, 1, 2, 3, 16, 19, 6, 5, 4, 17, 20, 7, 8, 21, 18, 15, 25, 22, 9, 10, 23, 13],
  [12, 11, 24, 14, 1, 2, 15, 25, 22, 19, 16, 3, 4, 17, 20, 7, 6, 5, 18, 21, 8, 9, 10, 23, 13],
  [12, 11, 24, 21, 8, 9, 10, 23, 20, 7, 6, 19, 22, 25, 15, 18, 5, 4, 17, 14, 1, 2, 3, 16, 13],
  [12, 25, 15, 18, 21, 24, 11, 10, 23, 20, 7, 8, 9, 22, 19, 6, 5, 4, 17, 14, 1, 2, 3, 16, 13],
  [12, 25, 15, 18, 21, 24, 11, 10, 23, 20, 17, 14, 1, 2, 3, 4, 5, 6, 7, 8, 9, 22, 19, 16, 13],
  [12, 25, 22, 9, 10, 11, 24, 21, 8, 7, 6, 19, 16, 3, 4, 5, 18, 15, 2, 1, 14, 17, 20, 23, 13],
  [12, 25, 22, 19, 16, 3, 4, 5, 6, 7, 8, 9, 10, 11, 24, 21, 18, 15, 2, 1, 14, 17, 20, 23, 13]]

theorem hamL13 : ∀ l ∈ L13, HamRep 26 AMD13 l := by decide

theorem ndL13 : L13.Nodup := by decide

theorem lenL13 : L13.length = 26 := by decide

/-- **段階 1 との接続**：`L13` は `HamRep` を満たす頂点列のちょうど全体である。
  （⊆ は `hamL13`（decide）、= は核計算が出した個数 26 との濃度の一致。） -/
theorem L13_eq : ∀ l : List ℕ, l ∈ L13 ↔ HamRep 26 AMD13 l := by
  obtain ⟨S, hmem, hcard, -⟩ := GP13_hc_card
  have hsub : L13.toFinset ⊆ S := fun l hl =>
    (hmem l).mpr (hamL13 l (List.mem_toFinset.mp hl))
  have hc : L13.toFinset.card = 26 := by
    rw [List.toFinset_card_of_nodup ndL13, lenL13]
  have hle : S.card ≤ L13.toFinset.card := by rw [hcard, hc]
  have heq : L13.toFinset = S := Finset.eq_of_subset_of_card_le hsub hle
  intro l
  rw [← List.mem_toFinset, heq, hmem]

/-! ### 回転の作用 `ract 13` の性質（すべて明示的なリスト上の decide） -/

/-- (i) `ract 13 1` は `L13` を `L13` に写す（`ρ` が自己同型だから隣接は保たれ、
  `Nodup`・`0 ∉ ·` も保たれ、正準化が `HamRep` の形に合う——を実例で確かめたもの）。 -/
theorem ractMem13 : ∀ a ∈ L13, ract 13 1 a ∈ L13 := by decide +kernel

/-- `ract 13 0` は恒等（`ρ^0 = id`）。 -/
theorem ractZero13 : ∀ a ∈ L13, ract 13 0 a = a := by decide +kernel

/-- (ii) 合成則：`ract 1 ∘ ract i = ract (i+1)`（`L13` 上）。これで
  `(ract 1)^[i] = ract i` が帰納法で出る（`dvd_card_of_family_free`）。 -/
theorem ractComp13 : ∀ i < 13, ∀ a ∈ L13, ract 13 1 (ract 13 i a) = ract 13 (i + 1) a := by
  decide +kernel

/-- (iii) 位数 `13`：`ract 13 13` は恒等。 -/
theorem ractOrd13 : ∀ a ∈ L13, ract 13 13 a = a := by decide +kernel

/-! ### `ract` が本当に ρ の作用であること、そして不動点なし -/

/-- **意味の橋**：`ract 13 i l` は「閉路 `0 :: l` を `ρ^i` で写した閉路」の
  正準表現である——両者の **辺集合** が一致する。
  （これがあるので (iv) の「`ract` の不動点なし」は「`ρ^i` 不変な閉路なし」と同じ内容になる。） -/
theorem ractEmask13 : ∀ i < 14, ∀ l ∈ L13,
    emask 26 (0 :: ract 13 i l) = emask 26 (List.map (rho 13 i) (0 :: l)) := by decide +kernel

/-- 段階 3：非自明な回転 `ρ^d` で不変な閉路は無い。
  核で列挙を回していた（`n = 13, 15` はメモリが足りなかった）。
  ここでは明示的なリスト上の decide なので `n = 13, 15` も通る。 -/
theorem no_rho_fixed13L : ∀ l ∈ L13, ∀ d < 13, 0 < d →
    emask 26 (List.map (rho 13 d) (0 :: l)) ≠ emask 26 (0 :: l) := by decide +kernel

/-- 同じことを `HamRep` の言葉で（`Small` の `no_rho_fixed7'` と同形。`n = 13, 15` も）。 -/
theorem no_rho_fixed13' : ∀ l : List ℕ, HamRep 26 AMD13 l → ∀ d < 13, 0 < d →
    emask 26 (List.map (rho 13 d) (0 :: l)) ≠ emask 26 (0 :: l) :=
  fun l hl => no_rho_fixed13L l ((L13_eq l).mpr hl)

/-- (iv) **不動点なし**：`0 < i < 13` なら `ract 13 i` はどの閉路も固定しない。
  段階 3（`no_rho_fixed13L`）と意味の橋（`ractEmask13`）から出る——
  「`ract` が固定する ⟹ 辺集合が `ρ^i` 不変」だから。 -/
theorem ractFree13 : ∀ i < 13, 0 < i → ∀ a ∈ L13, ract 13 i a ≠ a := by
  intro i hi hi0 a ha h
  have e := ractEmask13 i (by omega) a ha
  rw [h] at e
  exact no_rho_fixed13L a ha i hi hi0 e.symm

/-! ### 主定理 -/

/-- **回転の自由作用から**：`13 ∣ (閉路の個数)`。
  段階 1 の核計算の **値**（26）は使わない——`dvd_card_of_family_free` に
  (i)〜(iv) を渡すだけで割り切れが出る。 -/
theorem gp13_dvd_by_rotation : 13 ∣ L13.toFinset.card :=
  dvd_card_of_family_free L13.toFinset (ract 13) 13 (by norm_num)
    (fun a ha => List.mem_toFinset.mpr (ractMem13 a (List.mem_toFinset.mp ha)))
    (fun a ha => ractZero13 a (List.mem_toFinset.mp ha))
    (fun i hi a ha => ractComp13 i hi a (List.mem_toFinset.mp ha))
    (fun a ha => ractOrd13 a (List.mem_toFinset.mp ha))
    (fun i hi hin a ha => ractFree13 i hin hi a (List.mem_toFinset.mp ha))

/-- **主定理**：`GP(13,3)` の正準向きハミルトン閉路の集合 `S` について
  `13 ∣ S.card` が **回転 ρ の自由作用から** 出る（段階 2 ＋ 段階 3。
  段階 1 の個数を数える核計算は、`S` が `L13` で汲み尽くされていること
  〈`L13_eq`〉を言うためだけに使う）。併せて `S.card = 26` も述べる。 -/
theorem GP13_dvd_rot : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 26 AMD13 l) ∧ 13 ∣ S.card ∧ S.card = 26 := by
  refine ⟨L13.toFinset, ?_, gp13_dvd_by_rotation, ?_⟩
  · intro l; rw [List.mem_toFinset]; exact L13_eq l
  · rw [List.toFinset_card_of_nodup ndL13, lenL13]

/-- 表現の取り方によらない形：`HamRep 26 AMD13` を満たす頂点列全体の `Finset` は
  （どう取っても `L13.toFinset` に等しいので）濃度が `13` で割れる。 -/
theorem GP13_dvd_any (S : Finset (List ℕ))
    (hS : ∀ l : List ℕ, l ∈ S ↔ HamRep 26 AMD13 l) : 13 ∣ S.card := by
  have hSL : S = L13.toFinset := by
    ext l; rw [List.mem_toFinset, L13_eq l, hS l]
  rw [hSL]
  exact gp13_dvd_by_rotation

end GeneralizedPetersen.FreeAction

namespace GeneralizedPetersen.FreeAction

open GeneralizedPetersen.Small

set_option maxRecDepth 40000

/-! ### GP(15,3) の正準向きハミルトン閉路（75 本） -/

/-- `HamRep 30 AMD15` を満たす頂点列の全体（Python が列挙。全部であることは `L15_eq`）。 -/
def L15 : List (List ℕ) :=
  [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 25, 22, 19, 16, 28, 13, 14, 29, 17, 20, 23, 26, 11, 12, 27,
     24, 21, 18, 15],
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 24, 21, 18, 15, 27, 12, 13, 28, 16, 19, 22, 25, 10, 11, 26, 23,
     20, 17, 29, 14],
  [1, 2, 3, 4, 5, 6, 7, 8, 23, 20, 17, 29, 26, 11, 12, 27, 15, 18, 21, 24, 9, 10, 25, 22, 19,
     16, 28, 13, 14],
  [1, 2, 3, 4, 5, 6, 7, 22, 19, 16, 28, 25, 10, 11, 26, 29, 17, 20, 23, 8, 9, 24, 21, 18, 15,
     27, 12, 13, 14],
  [1, 2, 3, 4, 5, 6, 21, 18, 15, 27, 24, 9, 10, 25, 28, 16, 19, 22, 7, 8, 23, 20, 17, 29, 26,
     11, 12, 13, 14],
  [1, 2, 3, 4, 5, 20, 17, 29, 14, 13, 12, 27, 24, 9, 8, 23, 26, 11, 10, 25, 28, 16, 19, 22, 7,
     6, 21, 18, 15],
  [1, 2, 3, 4, 5, 20, 17, 29, 14, 13, 28, 16, 19, 22, 25, 10, 9, 24, 27, 12, 11, 26, 23, 8, 7,
     6, 21, 18, 15],
  [1, 2, 3, 4, 5, 20, 17, 29, 26, 23, 8, 9, 24, 27, 15, 18, 21, 6, 7, 22, 19, 16, 28, 25, 10,
     11, 12, 13, 14],
  [1, 2, 3, 4, 19, 16, 28, 13, 12, 11, 26, 23, 8, 7, 22, 25, 10, 9, 24, 27, 15, 18, 21, 6, 5,
     20, 17, 29, 14],
  [1, 2, 3, 4, 19, 16, 28, 13, 12, 27, 15, 18, 21, 24, 9, 8, 23, 26, 11, 10, 25, 22, 7, 6, 5,
     20, 17, 29, 14],
  [1, 2, 3, 4, 19, 16, 28, 13, 14, 29, 17, 20, 5, 6, 7, 22, 25, 10, 9, 8, 23, 26, 11, 12, 27,
     24, 21, 18, 15],
  [1, 2, 3, 4, 19, 16, 28, 25, 22, 7, 8, 23, 26, 11, 10, 9, 24, 27, 12, 13, 14, 29, 17, 20, 5,
     6, 21, 18, 15],
  [1, 2, 3, 4, 19, 16, 28, 25, 22, 7, 8, 23, 26, 29, 17, 20, 5, 6, 21, 18, 15, 27, 24, 9, 10,
     11, 12, 13, 14],
  [1, 2, 3, 18, 15, 27, 12, 11, 10, 25, 22, 7, 6, 21, 24, 9, 8, 23, 26, 29, 17, 20, 5, 4, 19,
     16, 28, 13, 14],
  [1, 2, 3, 18, 15, 27, 12, 11, 26, 29, 17, 20, 23, 8, 7, 22, 25, 10, 9, 24, 21, 6, 5, 4, 19,
     16, 28, 13, 14],
  [1, 2, 3, 18, 15, 27, 12, 13, 28, 16, 19, 4, 5, 6, 21, 24, 9, 8, 7, 22, 25, 10, 11, 26, 23,
     20, 17, 29, 14],
  [1, 2, 3, 18, 15, 27, 24, 21, 6, 7, 22, 25, 10, 9, 8, 23, 26, 11, 12, 13, 28, 16, 19, 4, 5,
     20, 17, 29, 14],
  [1, 2, 3, 18, 15, 27, 24, 21, 6, 7, 22, 25, 28, 16, 19, 4, 5, 20, 17, 29, 26, 23, 8, 9, 10,
     11, 12, 13, 14],
  [1, 2, 17, 20, 5, 4, 3, 18, 21, 6, 7, 22, 19, 16, 28, 25, 10, 11, 12, 13, 14, 29, 26, 23, 8,
     9, 24, 27, 15],
  [1, 2, 17, 20, 5, 6, 21, 18, 3, 4, 19, 16, 28, 25, 22, 7, 8, 23, 26, 29, 14, 13, 12, 11, 10,
     9, 24, 27, 15],
  [1, 2, 17, 20, 23, 8, 7, 6, 5, 4, 3, 18, 21, 24, 9, 10, 25, 22, 19, 16, 28, 13, 14, 29, 26,
     11, 12, 27, 15],
  [1, 2, 17, 20, 23, 8, 9, 24, 21, 18, 3, 4, 5, 6, 7, 22, 19, 16, 28, 25, 10, 11, 26, 29, 14,
     13, 12, 27, 15],
  [1, 2, 17, 29, 14, 13, 12, 27, 24, 21, 6, 5, 20, 23, 26, 11, 10, 9, 8, 7, 22, 25, 28, 16,
     19, 4, 3, 18, 15],
  [1, 2, 17, 29, 14, 13, 28, 16, 19, 22, 25, 10, 9, 8, 7, 6, 21, 24, 27, 12, 11, 26, 23, 20,
     5, 4, 3, 18, 15],
  [1, 2, 17, 29, 26, 11, 10, 9, 24, 21, 6, 5, 20, 23, 8, 7, 22, 25, 28, 16, 19, 4, 3, 18, 15,
     27, 12, 13, 14],
  [1, 2, 17, 29, 26, 11, 10, 25, 28, 16, 19, 22, 7, 6, 21, 24, 9, 8, 23, 20, 5, 4, 3, 18, 15,
     27, 12, 13, 14],
  [1, 2, 17, 29, 26, 11, 12, 27, 15, 18, 3, 4, 5, 20, 23, 8, 7, 6, 21, 24, 9, 10, 25, 22, 19,
     16, 28, 13, 14],
  [1, 2, 17, 29, 26, 23, 20, 5, 6, 21, 24, 9, 8, 7, 22, 25, 10, 11, 12, 27, 15, 18, 3, 4, 19,
     16, 28, 13, 14],
  [1, 2, 17, 29, 26, 23, 20, 5, 6, 21, 24, 27, 15, 18, 3, 4, 19, 16, 28, 25, 22, 7, 8, 9, 10,
     11, 12, 13, 14],
  [1, 16, 19, 4, 3, 2, 17, 20, 5, 6, 7, 22, 25, 28, 13, 14, 29, 26, 23, 8, 9, 10, 11, 12, 27,
     24, 21, 18, 15],
  [1, 16, 19, 4, 3, 2, 17, 20, 5, 6, 21, 18, 15, 27, 24, 9, 10, 11, 12, 13, 28, 25, 22, 7, 8,
     23, 26, 29, 14],
  [1, 16, 19, 4, 5, 6, 21, 24, 27, 12, 11, 10, 9, 8, 7, 22, 25, 28, 13, 14, 29, 26, 23, 20,
     17, 2, 3, 18, 15],
  [1, 16, 19, 4, 5, 20, 17, 2, 3, 18, 15, 27, 24, 21, 6, 7, 22, 25, 28, 13, 12, 11, 10, 9, 8,
     23, 26, 29, 14],
  [1, 16, 19, 22, 7, 6, 5, 4, 3, 2, 17, 20, 23, 8, 9, 10, 25, 28, 13, 14, 29, 26, 11, 12, 27,
     24, 21, 18, 15],
  [1, 16, 19, 22, 7, 6, 5, 4, 3, 2, 17, 20, 23, 8, 9, 24, 21, 18, 15, 27, 12, 13, 28, 25, 10,
     11, 26, 29, 14],
  [1, 16, 19, 22, 7, 8, 9, 24, 27, 12, 11, 10, 25, 28, 13, 14, 29, 26, 23, 20, 17, 2, 3, 4, 5,
     6, 21, 18, 15],
  [1, 16, 19, 22, 7, 8, 23, 20, 17, 2, 3, 4, 5, 6, 21, 18, 15, 27, 24, 9, 10, 25, 28, 13, 12,
     11, 26, 29, 14],
  [1, 16, 19, 22, 25, 28, 13, 14, 29, 26, 23, 20, 17, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 27,
     24, 21, 18, 15],
  [1, 16, 28, 13, 12, 11, 26, 23, 20, 5, 4, 19, 22, 25, 10, 9, 8, 7, 6, 21, 24, 27, 15, 18, 3,
     2, 17, 29, 14],
  [1, 16, 28, 13, 12, 27, 15, 18, 21, 24, 9, 8, 7, 6, 5, 20, 23, 26, 11, 10, 25, 22, 19, 4, 3,
     2, 17, 29, 14],
  [1, 16, 28, 13, 14, 29, 17, 2, 3, 4, 19, 22, 25, 10, 9, 8, 7, 6, 5, 20, 23, 26, 11, 12, 27,
     24, 21, 18, 15],
  [1, 16, 28, 13, 14, 29, 26, 23, 20, 17, 2, 3, 18, 21, 24, 9, 8, 7, 6, 5, 4, 19, 22, 25, 10,
     11, 12, 27, 15],
  [1, 16, 28, 25, 10, 9, 8, 23, 20, 5, 4, 19, 22, 7, 6, 21, 24, 27, 15, 18, 3, 2, 17, 29, 26,
     11, 12, 13, 14],
  [1, 16, 28, 25, 10, 9, 24, 27, 15, 18, 21, 6, 5, 20, 23, 8, 7, 22, 19, 4, 3, 2, 17, 29, 26,
     11, 12, 13, 14],
  [1, 16, 28, 25, 10, 11, 12, 13, 14, 29, 26, 23, 20, 17, 2, 3, 18, 21, 6, 5, 4, 19, 22, 7, 8,
     9, 24, 27, 15],
  [1, 16, 28, 25, 10, 11, 26, 29, 17, 2, 3, 4, 19, 22, 7, 6, 5, 20, 23, 8, 9, 24, 21, 18, 15,
     27, 12, 13, 14],
  [1, 16, 28, 25, 22, 19, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 29, 26, 23, 20, 17, 2, 3, 18,
     21, 24, 27, 15],
  [1, 16, 28, 25, 22, 19, 4, 5, 6, 7, 8, 23, 20, 17, 2, 3, 18, 21, 24, 9, 10, 11, 26, 29, 14,
     13, 12, 27, 15],
  [1, 16, 28, 25, 22, 19, 4, 5, 20, 17, 2, 3, 18, 21, 6, 7, 8, 23, 26, 29, 14, 13, 12, 11, 10,
     9, 24, 27, 15],
  [1, 16, 28, 25, 22, 19, 4, 5, 20, 23, 8, 7, 6, 21, 24, 9, 10, 11, 26, 29, 17, 2, 3, 18, 15,
     27, 12, 13, 14],
  [1, 16, 28, 25, 22, 19, 4, 5, 20, 23, 26, 11, 10, 9, 8, 7, 6, 21, 24, 27, 12, 13, 14, 29,
     17, 2, 3, 18, 15],
  [1, 16, 28, 25, 22, 19, 4, 5, 20, 23, 26, 29, 17, 2, 3, 18, 15, 27, 24, 21, 6, 7, 8, 9, 10,
     11, 12, 13, 14],
  [14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 20, 23, 26, 29, 17, 2, 1, 16, 28, 25, 22, 19, 4, 3, 18,
     21, 24, 27, 15],
  [14, 13, 12, 11, 10, 25, 28, 16, 1, 2, 3, 18, 21, 6, 7, 22, 19, 4, 5, 20, 17, 29, 26, 23, 8,
     9, 24, 27, 15],
  [14, 13, 12, 11, 10, 25, 28, 16, 1, 2, 17, 29, 26, 23, 20, 5, 6, 21, 18, 3, 4, 19, 22, 7, 8,
     9, 24, 27, 15],
  [14, 13, 12, 11, 26, 29, 17, 2, 1, 16, 28, 25, 10, 9, 8, 23, 20, 5, 6, 7, 22, 19, 4, 3, 18,
     21, 24, 27, 15],
  [14, 13, 12, 11, 26, 29, 17, 20, 23, 8, 7, 22, 19, 4, 5, 6, 21, 18, 3, 2, 1, 16, 28, 25, 10,
     9, 24, 27, 15],
  [14, 13, 28, 16, 1, 2, 3, 18, 21, 24, 9, 10, 25, 22, 19, 4, 5, 6, 7, 8, 23, 20, 17, 29, 26,
     11, 12, 27, 15],
  [14, 13, 28, 16, 1, 2, 17, 29, 26, 23, 20, 5, 6, 7, 8, 9, 24, 21, 18, 3, 4, 19, 22, 25, 10,
     11, 12, 27, 15],
  [14, 13, 28, 25, 10, 9, 24, 27, 12, 11, 26, 29, 17, 20, 23, 8, 7, 22, 19, 16, 1, 2, 3, 4, 5,
     6, 21, 18, 15],
  [14, 13, 28, 25, 10, 11, 12, 27, 24, 9, 8, 23, 26, 29, 17, 20, 5, 4, 3, 2, 1, 16, 19, 22, 7,
     6, 21, 18, 15],
  [14, 13, 28, 25, 22, 7, 6, 21, 24, 27, 12, 11, 10, 9, 8, 23, 26, 29, 17, 20, 5, 4, 19, 16,
     1, 2, 3, 18, 15],
  [14, 13, 28, 25, 22, 7, 8, 9, 10, 11, 12, 27, 24, 21, 6, 5, 20, 23, 26, 29, 17, 2, 1, 16,
     19, 4, 3, 18, 15],
  [14, 29, 17, 2, 1, 16, 19, 22, 25, 28, 13, 12, 27, 24, 21, 6, 7, 8, 9, 10, 11, 26, 23, 20,
     5, 4, 3, 18, 15],
  [14, 29, 17, 2, 1, 16, 28, 13, 12, 11, 26, 23, 20, 5, 6, 7, 8, 9, 10, 25, 22, 19, 4, 3, 18,
     21, 24, 27, 15],
  [14, 29, 17, 20, 5, 4, 3, 2, 1, 16, 19, 22, 25, 28, 13, 12, 27, 24, 9, 10, 11, 26, 23, 8, 7,
     6, 21, 18, 15],
  [14, 29, 17, 20, 23, 26, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 16, 19, 22, 25, 28, 13, 12, 27,
     24, 21, 18, 15],
  [14, 29, 17, 20, 23, 26, 11, 10, 9, 8, 7, 22, 25, 28, 13, 12, 27, 24, 21, 6, 5, 4, 19, 16,
     1, 2, 3, 18, 15],
  [14, 29, 17, 20, 23, 26, 11, 10, 25, 22, 19, 4, 5, 6, 7, 8, 9, 24, 21, 18, 3, 2, 1, 16, 28,
     13, 12, 27, 15],
  [14, 29, 17, 20, 23, 26, 11, 10, 25, 28, 13, 12, 27, 24, 9, 8, 7, 22, 19, 16, 1, 2, 3, 4, 5,
     6, 21, 18, 15],
  [14, 29, 26, 11, 10, 9, 24, 21, 18, 3, 4, 5, 6, 7, 8, 23, 20, 17, 2, 1, 16, 19, 22, 25, 28,
     13, 12, 27, 15],
  [14, 29, 26, 11, 12, 13, 28, 25, 10, 9, 8, 23, 20, 17, 2, 1, 16, 19, 22, 7, 6, 5, 4, 3, 18,
     21, 24, 27, 15],
  [14, 29, 26, 23, 8, 7, 6, 21, 18, 3, 4, 5, 20, 17, 2, 1, 16, 19, 22, 25, 28, 13, 12, 11, 10,
     9, 24, 27, 15],
  [14, 29, 26, 23, 8, 9, 10, 11, 12, 13, 28, 25, 22, 7, 6, 5, 20, 17, 2, 1, 16, 19, 4, 3, 18,
     21, 24, 27, 15],
  [14, 29, 26, 23, 20, 17, 2, 1, 16, 19, 22, 25, 28, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 18,
     21, 24, 27, 15]]

theorem hamL15 : ∀ l ∈ L15, HamRep 30 AMD15 l := by decide

theorem ndL15 : L15.Nodup := by decide

theorem lenL15 : L15.length = 75 := by decide

/-- **段階 1 との接続**：`L15` は `HamRep` を満たす頂点列のちょうど全体である。
  （⊆ は `hamL15`（decide）、= は核計算が出した個数 75 との濃度の一致。） -/
theorem L15_eq : ∀ l : List ℕ, l ∈ L15 ↔ HamRep 30 AMD15 l := by
  obtain ⟨S, hmem, hcard, -⟩ := GP15_hc_card
  have hsub : L15.toFinset ⊆ S := fun l hl =>
    (hmem l).mpr (hamL15 l (List.mem_toFinset.mp hl))
  have hc : L15.toFinset.card = 75 := by
    rw [List.toFinset_card_of_nodup ndL15, lenL15]
  have hle : S.card ≤ L15.toFinset.card := by rw [hcard, hc]
  have heq : L15.toFinset = S := Finset.eq_of_subset_of_card_le hsub hle
  intro l
  rw [← List.mem_toFinset, heq, hmem]

/-! ### 回転の作用 `ract 15` の性質（すべて明示的なリスト上の decide） -/

/-- (i) `ract 15 1` は `L15` を `L15` に写す（`ρ` が自己同型だから隣接は保たれ、
  `Nodup`・`0 ∉ ·` も保たれ、正準化が `HamRep` の形に合う——を実例で確かめたもの）。 -/
theorem ractMem15 : ∀ a ∈ L15, ract 15 1 a ∈ L15 := by decide +kernel

/-- `ract 15 0` は恒等（`ρ^0 = id`）。 -/
theorem ractZero15 : ∀ a ∈ L15, ract 15 0 a = a := by decide +kernel

/-- (ii) 合成則：`ract 1 ∘ ract i = ract (i+1)`（`L15` 上）。これで
  `(ract 1)^[i] = ract i` が帰納法で出る（`dvd_card_of_family_free`）。 -/
theorem ractComp15 : ∀ i < 15, ∀ a ∈ L15, ract 15 1 (ract 15 i a) = ract 15 (i + 1) a := by
  decide +kernel

/-- (iii) 位数 `15`：`ract 15 15` は恒等。 -/
theorem ractOrd15 : ∀ a ∈ L15, ract 15 15 a = a := by decide +kernel

/-! ### `ract` が本当に ρ の作用であること、そして不動点なし -/

/-- **意味の橋**：`ract 15 i l` は「閉路 `0 :: l` を `ρ^i` で写した閉路」の
  正準表現である——両者の **辺集合** が一致する。
  （これがあるので (iv) の「`ract` の不動点なし」は「`ρ^i` 不変な閉路なし」と同じ内容になる。） -/
theorem ractEmask15 : ∀ i < 16, ∀ l ∈ L15,
    emask 30 (0 :: ract 15 i l) = emask 30 (List.map (rho 15 i) (0 :: l)) := by decide +kernel

/-- 段階 3：非自明な回転 `ρ^d` で不変な閉路は無い。
  核で列挙を回していた（`n = 13, 15` はメモリが足りなかった）。
  ここでは明示的なリスト上の decide なので `n = 13, 15` も通る。 -/
theorem no_rho_fixed15L : ∀ l ∈ L15, ∀ d < 15, 0 < d →
    emask 30 (List.map (rho 15 d) (0 :: l)) ≠ emask 30 (0 :: l) := by decide +kernel

/-- 同じことを `HamRep` の言葉で（`Small` の `no_rho_fixed7'` と同形。`n = 13, 15` も）。 -/
theorem no_rho_fixed15' : ∀ l : List ℕ, HamRep 30 AMD15 l → ∀ d < 15, 0 < d →
    emask 30 (List.map (rho 15 d) (0 :: l)) ≠ emask 30 (0 :: l) :=
  fun l hl => no_rho_fixed15L l ((L15_eq l).mpr hl)

/-- (iv) **不動点なし**：`0 < i < 15` なら `ract 15 i` はどの閉路も固定しない。
  段階 3（`no_rho_fixed15L`）と意味の橋（`ractEmask15`）から出る——
  「`ract` が固定する ⟹ 辺集合が `ρ^i` 不変」だから。 -/
theorem ractFree15 : ∀ i < 15, 0 < i → ∀ a ∈ L15, ract 15 i a ≠ a := by
  intro i hi hi0 a ha h
  have e := ractEmask15 i (by omega) a ha
  rw [h] at e
  exact no_rho_fixed15L a ha i hi hi0 e.symm

/-! ### 主定理 -/

/-- **回転の自由作用から**：`15 ∣ (閉路の個数)`。
  段階 1 の核計算の **値**（75）は使わない——`dvd_card_of_family_free` に
  (i)〜(iv) を渡すだけで割り切れが出る。 -/
theorem gp15_dvd_by_rotation : 15 ∣ L15.toFinset.card :=
  dvd_card_of_family_free L15.toFinset (ract 15) 15 (by norm_num)
    (fun a ha => List.mem_toFinset.mpr (ractMem15 a (List.mem_toFinset.mp ha)))
    (fun a ha => ractZero15 a (List.mem_toFinset.mp ha))
    (fun i hi a ha => ractComp15 i hi a (List.mem_toFinset.mp ha))
    (fun a ha => ractOrd15 a (List.mem_toFinset.mp ha))
    (fun i hi hin a ha => ractFree15 i hin hi a (List.mem_toFinset.mp ha))

/-- **主定理**：`GP(15,3)` の正準向きハミルトン閉路の集合 `S` について
  `15 ∣ S.card` が **回転 ρ の自由作用から** 出る（段階 2 ＋ 段階 3。
  段階 1 の個数を数える核計算は、`S` が `L15` で汲み尽くされていること
  〈`L15_eq`〉を言うためだけに使う）。併せて `S.card = 75` も述べる。 -/
theorem GP15_dvd_rot : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 30 AMD15 l) ∧ 15 ∣ S.card ∧ S.card = 75 := by
  refine ⟨L15.toFinset, ?_, gp15_dvd_by_rotation, ?_⟩
  · intro l; rw [List.mem_toFinset]; exact L15_eq l
  · rw [List.toFinset_card_of_nodup ndL15, lenL15]

/-- 表現の取り方によらない形：`HamRep 30 AMD15` を満たす頂点列全体の `Finset` は
  （どう取っても `L15.toFinset` に等しいので）濃度が `15` で割れる。 -/
theorem GP15_dvd_any (S : Finset (List ℕ))
    (hS : ∀ l : List ℕ, l ∈ S ↔ HamRep 30 AMD15 l) : 15 ∣ S.card := by
  have hSL : S = L15.toFinset := by
    ext l; rw [List.mem_toFinset, L15_eq l, hS l]
  rw [hSL]
  exact gp15_dvd_by_rotation

end GeneralizedPetersen.FreeAction
