import Mathlib
import Principia.GeneralizedPetersen.Base

/-!
# Principia.GeneralizedPetersen.Blocks

  `d` が奇のときの欠け辺のブロック構造、内輪の糸、初回帰置換 `next₃`、
  被覆 `GP(n,k) → GP(d,k)`。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.Blocks

open Finset GeneralizedPetersen.Base

variable {d : ℕ} [NeZero d]

/-! ### 1. 四つの集合 -/

/-- `G_i`：内辺の欠けの集合。 -/
def Gi (F : Win d) : Finset (ZMod d) := Finset.univ.filter (fun r => F.i r = 0)

/-- ドミノの左端：`r` と `r+1` がともに欠け。 -/
def Doms (F : Win d) : Finset (ZMod d) :=
  Finset.univ.filter (fun r => F.i r = 0 ∧ F.i (r + 1) = 0)

/-- 右端：`r` は欠けだが `r+1`・`r+2` は欠けでない。 -/
def Ends (F : Win d) : Finset (ZMod d) :=
  Finset.univ.filter (fun r => F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) ≠ 0)

theorem mem_Gi (F : Win d) (r : ZMod d) : r ∈ Gi F ↔ F.i r = 0 := by
  simp [Gi]

theorem card_Gi (F : Win d) : (Gi F).card = F.q := rfl

theorem card_Doms (F : Win d) : (Doms F).card = F.n1 := by
  have h : F.n1 = ∑ r : ZMod d, (if F.i r = 0 ∧ F.i (r + 1) = 0 then (1 : ℕ) else 0) := rfl
  rw [h, Finset.sum_boole]
  simp [Doms]

theorem card_Ends (F : Win d) :
    (Ends F).card = ∑ r : ZMod d, (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) ≠ 0
      then (1 : ℕ) else 0) := by
  rw [Finset.sum_boole]
  simp [Ends]

/-! ### 2. 勘定：`q = n₁ + n₂ + e`、ゆえに `n₁ = e` -/

/-- `G` の各点はちょうど一つの型に入る（ドミノの左端／間の空いた対の左／右端）。 -/
theorem q_split (F : Win d) : F.q = F.n1 + F.n2 + (Ends F).card := by
  have hq : F.q = ∑ r : ZMod d, (if F.i r = 0 then (1 : ℕ) else 0) := by
    rw [Finset.sum_boole]; simp [Win.q]
  have hpt : ∀ r : ZMod d, (if F.i r = 0 then (1 : ℕ) else 0)
      = (if F.i r = 0 ∧ F.i (r + 1) = 0 then (1 : ℕ) else 0)
      + (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) = 0 then (1 : ℕ) else 0)
      + (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) ≠ 0 then (1 : ℕ) else 0) := by
    intro r
    by_cases h0 : F.i r = 0 <;> by_cases h1 : F.i (r + 1) = 0 <;>
      by_cases h2 : F.i (r + 2) = 0 <;> simp [h0, h1, h2]
  have hn1 : F.n1 = ∑ r : ZMod d, (if F.i r = 0 ∧ F.i (r + 1) = 0 then (1 : ℕ) else 0) := rfl
  have hn2 : F.n2 = ∑ r : ZMod d,
      (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) = 0 then (1 : ℕ) else 0) := rfl
  rw [hq, hn1, hn2, card_Ends, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => hpt r)

/-- **ドミノの数＝右端の数。**（`Base` の `2n₁ + n₂ = q` と `q = n₁ + n₂ + e` から。） -/
theorem n1_eq_ends (F : Win d) : F.n1 = (Ends F).card := by
  have h1 := F.pairs_eq_q
  have h2 := q_split F
  omega

/-! ### 3. 単射 `r ↦ r+1` と、その全射性 -/

/-- ドミノの左端 `r` に対し `r+1` は右端である（3 連続の禁止と距離 3 の禁止）。 -/
theorem succ_mem_Ends (F : Win d) {r : ZMod d} (hr : r ∈ Doms F) : r + 1 ∈ Ends F := by
  simp only [Doms, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  obtain ⟨h0, h1⟩ := hr
  have h2 : F.i (r + 2) ≠ 0 := fun h => F.no_three_consecutive r ⟨h0, h1, h⟩
  have h3 : F.i (r + 3) ≠ 0 := fun h => F.no_gap_dist_three r ⟨h0, h⟩
  simp only [Ends, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨h1, ?_, ?_⟩
  · rw [show r + 1 + 1 = r + 2 from by ring]; exact h2
  · rw [show r + 1 + 2 = r + 3 from by ring]; exact h3

/-- **全単射**：右端の集合はドミノの左端を `+1` したものに他ならない。 -/
theorem image_Doms (F : Win d) : (Doms F).image (fun r => r + 1) = Ends F := by
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    exact succ_mem_Ends F hr
  · rw [Finset.card_image_of_injective _ (add_left_injective (1 : ZMod d)), card_Doms,
      n1_eq_ends]

/-- **要**：どの右端 `s` も、左隣 `s−1` が `G` に入っている。 -/
theorem ends_has_pred (F : Win d) {s : ZMod d} (hs : s ∈ Ends F) : F.i (s - 1) = 0 := by
  rw [← image_Doms F] at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  rw [show r + 1 - 1 = r from by ring]
  exact ((Finset.mem_filter.mp hr).2).1

/-! ### 4. `+2` の鎖と `d` の奇偶 -/

/-- 両隣が `G` の外にある点 `r` からは、`+2` の鎖が果てしなく続く。
  （`r + 2t` はいつも `G` の中にあり、その両隣は `G` の外。） -/
theorem chain_two (F : Win d) {r : ZMod d}
    (h0 : F.i r = 0) (h1 : F.i (r + 1) ≠ 0) (hm : F.i (r - 1) ≠ 0) :
    ∀ t : ℕ, F.i (r + 2 * (t : ZMod d)) = 0 ∧ F.i (r + 2 * (t : ZMod d) + 1) ≠ 0
      ∧ F.i (r + 2 * (t : ZMod d) - 1) ≠ 0 := by
  intro t
  induction t with
  | zero => simpa using ⟨h0, h1, hm⟩
  | succ u ih =>
      obtain ⟨a0, a1, am⟩ := ih
      have he : r + 2 * ((u + 1 : ℕ) : ZMod d) = (r + 2 * (u : ZMod d)) + 2 := by
        push_cast; ring
      set s := r + 2 * (u : ZMod d) with hs
      -- `s` は右端になれない（右端なら `s−1 ∈ G` だが `am` に反する）
      have h2 : F.i (s + 2) = 0 := by
        by_contra hne
        have : s ∈ Ends F := by
          simp only [Ends, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨a0, a1, hne⟩
        exact am (ends_has_pred F this)
      have h3 : F.i (s + 3) ≠ 0 := fun h => F.no_gap_dist_three s ⟨a0, h⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [he]; exact h2
      · rw [he, show s + 2 + 1 = s + 3 from by ring]; exact h3
      · rw [he, show s + 2 - 1 = s + 1 from by ring]; exact a1

/-- **`d` 奇なら、欠けの点は必ず隣にもう一つ欠けを持つ**（ドミノになる）。
  ここが紙の証明の「クラスタの余剰 ≤ 0、等号はドミノ」に対応する段で、
  **`d` の奇偶が効くのはこの証明の最後の一行だけ**である。 -/
theorem odd_pair (F : Win d) (hodd : Odd d) {r : ZMod d} (hr : F.i r = 0) :
    F.i (r + 1) = 0 ∨ F.i (r - 1) = 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, hm⟩ := hc
  obtain ⟨m, hmd⟩ := hodd
  have hkey : (2 : ZMod d) * ((m + 1 : ℕ) : ZMod d) = 1 := by
    have hd : ((2 * m + 1 : ℕ) : ZMod d) = 0 := by
      rw [← hmd]; exact ZMod.natCast_self d
    push_cast at hd ⊢
    linear_combination hd
  have h := (chain_two F hr h1 hm (m + 1)).1
  rw [hkey] at h
  exact h1 h

/-! ### 5. ブロック構造（紙の証明の定理 1） -/

/-- `d` 奇なら `G_i` はドミノの直和である。 -/
theorem block (F : Win d) (hodd : Odd d) {r : ZMod d} (hr : F.i r = 0) :
    ∃ b : ZMod d, F.i b = 0 ∧ F.i (b + 1) = 0 ∧ (r = b ∨ r = b + 1) := by
  rcases odd_pair F hodd hr with h | h
  · exact ⟨r, hr, h, Or.inl rfl⟩
  · refine ⟨r - 1, h, ?_, Or.inr ?_⟩
    · rw [show r - 1 + 1 = r from by ring]; exact hr
    · ring

/-- ドミノは互いに 5 以上離れている（紙の証明の `r_{k+1} ≥ r_k + 5`）。 -/
theorem block_sep (F : Win d) {b : ZMod d} (h0 : F.i b = 0) (h1 : F.i (b + 1) = 0) :
    F.i (b + 2) ≠ 0 ∧ F.i (b + 3) ≠ 0 ∧ F.i (b + 4) ≠ 0
      ∧ F.i (b - 1) ≠ 0 ∧ F.i (b - 2) ≠ 0 ∧ F.i (b - 3) ≠ 0 := by
  refine ⟨fun h => F.no_three_consecutive b ⟨h0, h1, h⟩,
    fun h => F.no_gap_dist_three b ⟨h0, h⟩, fun h => F.no_gap_dist_three (b + 1) ⟨h1, ?_⟩,
    fun h => F.no_three_consecutive (b - 1) ⟨h, ?_, ?_⟩,
    fun h => F.no_gap_dist_three (b - 2) ⟨h, ?_⟩, fun h => F.no_gap_dist_three (b - 3) ⟨h, ?_⟩⟩
  · rw [show b + 1 + 3 = b + 4 from by ring]; exact h
  · rw [show b - 1 + 1 = b from by ring]; exact h0
  · rw [show b - 1 + 2 = b + 1 from by ring]; exact h1
  · rw [show b - 2 + 3 = b + 1 from by ring]; exact h1
  · rw [show b - 3 + 3 = b from by ring]; exact h0

/-- 窓 `{j−2, j−1, j}` の零がちょうど一つであることの展開。 -/
theorem Z_eq_one_iff (F : Win d) (j : ZMod d) :
    F.Z j = 1 ↔ (F.i (j - 2) = 0 ∧ F.i (j - 1) ≠ 0 ∧ F.i j ≠ 0)
      ∨ (F.i (j - 2) ≠ 0 ∧ F.i (j - 1) = 0 ∧ F.i j ≠ 0)
      ∨ (F.i (j - 2) ≠ 0 ∧ F.i (j - 1) ≠ 0 ∧ F.i j = 0) := by
  unfold Win.Z
  by_cases h2 : F.i (j - 2) = 0 <;> by_cases h1 : F.i (j - 1) = 0 <;>
    by_cases h0 : F.i j = 0 <;> simp [h2, h1, h0]

/-- 欠けた**外**辺の位置（紙の証明の定理 1 の `G_o = ⊔ {r_k, r_k+3}`）。
  `d` 奇なら、外辺が欠けているのはドミノの左端 `b` と `b+3` のちょうど二か所である。 -/
theorem outer_zero_iff (F : Win d) (hodd : Odd d) (j : ZMod d) :
    F.o j = 0 ↔ (F.i j = 0 ∧ F.i (j + 1) = 0) ∨ (F.i (j - 3) = 0 ∧ F.i (j - 2) = 0) := by
  have hZ := F.Z_spec j
  constructor
  · intro ho
    rcases (Z_eq_one_iff F j).mp (hZ.2.mpr ho) with ⟨h2, h1, h0⟩ | ⟨h2, h1, h0⟩ | ⟨h2, h1, h0⟩
    · right
      refine ⟨?_, h2⟩
      rcases odd_pair F hodd h2 with h | h
      · exact absurd (by rw [show j - 1 = j - 2 + 1 from by ring]; exact h) h1
      · rw [show j - 3 = j - 2 - 1 from by ring]; exact h
    · exfalso
      rcases odd_pair F hodd h1 with h | h
      · exact h0 (by rw [show j = j - 1 + 1 from by ring]; exact h)
      · exact h2 (by rw [show j - 2 = j - 1 - 1 from by ring]; exact h)
    · left
      refine ⟨h0, ?_⟩
      rcases odd_pair F hodd h0 with h | h
      · exact h
      · exact absurd h h1
  · intro h
    refine hZ.2.mp ((Z_eq_one_iff F j).mpr ?_)
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · obtain ⟨_, _, _, hm1, hm2, _⟩ := block_sep F h0 h1
      exact Or.inr (Or.inr ⟨hm2, hm1, h0⟩)
    · have h1' : F.i (j - 3 + 1) = 0 := by rw [show j - 3 + 1 = j - 2 from by ring]; exact h1
      obtain ⟨e1, e2, _, _, _, _⟩ := block_sep F h0 h1'
      refine Or.inl ⟨h1, ?_, ?_⟩
      · rw [show j - 1 = j - 3 + 2 from by ring]; exact e1
      · rw [show j = j - 3 + 3 from by ring]; exact e2

end GeneralizedPetersen.Blocks

namespace GeneralizedPetersen.Blocks

open Finset GeneralizedPetersen.Base

variable {d : ℕ} [NeZero d]

/-! ### 1. 糸（`+3` の軌道）と、その番号付け -/

/-- 糸の番号付け：`ZMod d → ZMod (gcd 3 d)`。 -/
def thrHom (d : ℕ) : ZMod d →+* ZMod (Nat.gcd 3 d) :=
  ZMod.castHom (Nat.gcd_dvd_right 3 d) _

/-- `r` と `s` が同じ糸に載っている（`+3` の軌道が同じ）。 -/
def sameThread (d : ℕ) (r s : ZMod d) : Prop := ∃ t : ℕ, s = r + 3 * (t : ZMod d)

/-- **番号付けは忠実**：`thrHom` の値が等しいことと、同じ糸に載っていることは同値。
  （←は `3` が核に入ること、→は Bezout（`gcd 3 d = 3a + d b`）。） -/
theorem thrHom_eq_iff (r s : ZMod d) : thrHom d r = thrHom d s ↔ sameThread d r s := by
  have h3 : thrHom d (3 : ZMod d) = 0 := by
    rw [show (3 : ZMod d) = ((3 : ℕ) : ZMod d) by norm_num, thrHom, map_natCast]
    exact (CharP.cast_eq_zero_iff (ZMod (Nat.gcd 3 d)) (Nat.gcd 3 d) 3).mpr (Nat.gcd_dvd_left 3 d)
  constructor
  · intro h
    have hri : ∀ z : ZMod d, ((z.val : ℕ) : ZMod d) = z := ZMod.natCast_rightInverse
    have hz : (((s - r).val : ℕ) : ZMod (Nat.gcd 3 d)) = 0 := by
      have h1 : thrHom d (s - r) = 0 := by rw [map_sub, h, sub_self]
      rw [← hri (s - r)] at h1
      rwa [thrHom, map_natCast] at h1
    obtain ⟨m, hm⟩ := (CharP.cast_eq_zero_iff (ZMod (Nat.gcd 3 d)) (Nat.gcd 3 d) _).mp hz
    have hb : ((Nat.gcd 3 d : ℕ) : ℤ) = 3 * Nat.gcdA 3 d + (d : ℤ) * Nat.gcdB 3 d :=
      Nat.gcd_eq_gcd_ab 3 d
    have hd0 : ((d : ℕ) : ZMod d) = 0 := ZMod.natCast_self d
    have hgz : ((Nat.gcd 3 d : ℕ) : ZMod d) = 3 * ((Nat.gcdA 3 d : ℤ) : ZMod d) := by
      have h0 : (((Nat.gcd 3 d : ℕ) : ℤ) : ZMod d)
          = ((3 * Nat.gcdA 3 d + (d : ℤ) * Nat.gcdB 3 d : ℤ) : ZMod d) := by rw [← hb]
      push_cast at h0
      first
        | linear_combination h0 + ((Nat.gcdB 3 d : ℤ) : ZMod d) * hd0
        | linear_combination h0
    have hsr : s - r = 3 * (((Nat.gcdA 3 d : ℤ) : ZMod d) * ((m : ℕ) : ZMod d)) := by
      have hv : (((s - r).val : ℕ) : ZMod d) = ((Nat.gcd 3 d * m : ℕ) : ZMod d) := by rw [hm]
      rw [hri] at hv
      rw [hv]
      push_cast
      rw [hgz]
      ring
    refine ⟨((((Nat.gcdA 3 d : ℤ) : ZMod d) * ((m : ℕ) : ZMod d))).val, ?_⟩
    rw [hri]
    linear_combination hsr
  · rintro ⟨t, rfl⟩
    rw [map_add, map_mul, h3, zero_mul, add_zero]

/-! ### 2. `G_i` と交わる糸の数 `c` -/

/-- `c`：`G_i` と交わる糸の数。 -/
def Thr (F : Win d) : Finset (ZMod (Nat.gcd 3 d)) := (Gi F).image (thrHom d)

/-- **`c` は奇数**（紙の証明）。`3 ∤ d` なら `c = 1`、`3 ∣ d` なら仮定から `c = 3`。 -/
theorem thr_card_odd (F : Win d) (hne : (Gi F).Nonempty)
    (hall : 3 ∣ d → ∀ c : ZMod (Nat.gcd 3 d), c ∈ Thr F) : Odd (Thr F).card := by
  haveI : NeZero (Nat.gcd 3 d) := ⟨fun h => (NeZero.ne d) (Nat.gcd_eq_zero_iff.mp h).2⟩
  by_cases h3 : 3 ∣ d
  · have hg : Nat.gcd 3 d = 3 := Nat.gcd_eq_left h3
    have huniv : Thr F = Finset.univ := Finset.eq_univ_iff_forall.mpr (hall h3)
    rw [huniv, Finset.card_univ, ZMod.card, hg]
    exact ⟨1, rfl⟩
  · have hg : Nat.gcd 3 d = 1 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
    have hle : (Thr F).card ≤ 1 := by
      have h := Finset.card_le_univ (Thr F)
      rw [ZMod.card] at h
      omega
    have hpos : 0 < (Thr F).card := Finset.card_pos.mpr (hne.image _)
    have he : (Thr F).card = 1 := by omega
    rw [he]
    exact ⟨0, rfl⟩

/-! ### 3. `d` 奇なら `|G_i| = 2 n₁`（ドミノの数が紙の証明の `q`） -/

/-- `d` 奇なら「間の空いた距離 2 の対」は無い。 -/
theorem n2_eq_zero (F : Win d) (hodd : Odd d) : F.n2 = 0 := by
  have h : F.n2 = ∑ r : ZMod d,
      (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) = 0 then (1 : ℕ) else 0) := rfl
  rw [h]
  refine Finset.sum_eq_zero (fun r _ => ?_)
  by_cases hc : F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) = 0
  · exfalso
    obtain ⟨h0, h1, h2⟩ := hc
    rcases odd_pair F hodd h0 with h | h
    · exact h1 h
    · refine F.no_gap_dist_three (r - 1) ⟨h, ?_⟩
      rw [show r - 1 + 3 = r + 2 from by ring]; exact h2
  · simp [hc]

/-- **紙の証明の定理 1 の勘定**：`d` 奇なら `|G_i| = 2 q`（`q` ＝ドミノの数 `n₁`）。 -/
theorem q_eq_two_n1 (F : Win d) (hodd : Odd d) : F.q = 2 * F.n1 := by
  have h1 := F.pairs_eq_q
  have h2 := n2_eq_zero F hodd
  omega

/-! ### 4. 符号の矛盾（紙の証明の定理 2 の商側） -/

/-- **到達点（商側）**：`d` 奇の `Win d`（＝巻き数 2 の向き付き 2 因子）に対し、
  `G_i` の上の置換 `θ`（円周上の前者）と `ν`（`next₃`）は、合成が全体を回る巡回にならない。

  仮定として残っているのは
  * `α ≃ G_i`（`Fintype.card α = F.q`）と `θ`・`ν` の構成、
  * `hbridge`：`ν`（`next₃`）の軌道の本数が `G_i` と交わる糸の数に等しいこと、
  * `hall`：`3 ∣ d` のとき三本の糸がすべて `G_i` と交わること（ハミルトン性から）。

  `d` の奇偶は `q = 2 n₁`（ブロック構造）を通してのみ効く。 -/
theorem quot_two_factor_not_cycle (F : Win d) (hodd : Odd d)
    (hall : 3 ∣ d → ∀ c : ZMod (Nat.gcd 3 d), c ∈ Thr F)
    {α : Type*} [Fintype α] [DecidableEq α] (hcard : Fintype.card α = F.q)
    (θ ν : Equiv.Perm α) (hθ : θ.IsCycle) (hθs : θ.support = Finset.univ)
    (hbridge : GeneralizedPetersen.Base.orbCount ν = (Thr F).card) :
    ¬ ((ν * θ).IsCycle ∧ (ν * θ).support = Finset.univ) := by
  obtain ⟨a, -, -⟩ := id hθ
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hne : (Gi F).Nonempty := by
    rw [← Finset.card_pos, card_Gi]
    omega
  refine GeneralizedPetersen.Base.next_theta_not_full_cycle F.n1 ?_ θ ν hθ hθs ?_
  · rw [hcard, q_eq_two_n1 F hodd]
  · rw [hbridge]
    exact thr_card_odd F hne hall

end GeneralizedPetersen.Blocks

namespace GeneralizedPetersen.Blocks

open SimpleGraph GeneralizedPetersen.Base

/-! ### 1. 被覆と歩道の持ち上げ（一般のグラフ） -/

variable {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}

/-- **被覆**：商側の各隣接点にちょうど一つの持ち上げがある。 -/
def IsCovering (f : G →g H) : Prop :=
  ∀ (x : A) (b : B), H.Adj (f x) b → ∃! y : A, G.Adj x y ∧ f y = b

/-- 局所の一意性：同じ点の隣で、同じ点に写るものは一つ。 -/
theorem IsCovering.eq_of_adj {f : G →g H} (hf : IsCovering f) {x y y' : A}
    (hy : G.Adj x y) (hy' : G.Adj x y') (he : f y = f y') : y = y' := by
  obtain ⟨z, -, hz⟩ := hf x (f y) (f.map_adj hy)
  rw [hz y ⟨hy, rfl⟩, hz y' ⟨hy', he.symm⟩]

/-- **歩道の持ち上げ（存在）**：商 `H` の歩道 `p` は、始点の持ち上げ `x` を決めれば持ち上がる。
  長さは変わらず、台（頂点列）は `f` で `p` の台に写る。 -/
theorem exists_lift {f : G →g H} (hf : IsCovering f) :
    ∀ {a b : B} (p : H.Walk a b) (x : A), f x = a →
      ∃ (y : A) (w : G.Walk x y), f y = b ∧ w.length = p.length
        ∧ w.support.map f = p.support := by
  intro a b p
  induction p with
  | nil =>
      intro x hx
      exact ⟨x, Walk.nil, hx, rfl, by simp [hx]⟩
  | @cons u v w hadj p ih =>
      intro x hx
      subst hx
      obtain ⟨y, hxy, hy⟩ := (hf x v hadj).exists
      obtain ⟨z, wz, hz, hlen, hsup⟩ := ih y hy
      exact ⟨z, Walk.cons hxy wz, hz, by simp [hlen], by simp [hsup]⟩

/-- **歩道の持ち上げ（一意性）**：始点が同じで、`f` での像の頂点列が同じ持ち上げは、
  頂点列が一致する。 -/
theorem lift_unique {f : G →g H} (hf : IsCovering f) :
    ∀ {x y : A} (w : G.Walk x y) {y' : A} (w' : G.Walk x y'),
      w.support.map f = w'.support.map f → w.support = w'.support := by
  intro x y w
  induction w with
  | nil =>
      intro y' w' hmap
      simp only [Walk.support_nil, List.map_cons, List.map_nil] at hmap
      have hlen : w'.support.length = 1 := by
        have h2 := congrArg List.length hmap
        simp only [List.length_cons, List.length_nil, List.length_map] at h2
        omega
      have hcons := Walk.cons_tail_support w'
      have htail : w'.support.tail = [] := by
        have h3 := congrArg List.length hcons
        simp only [List.length_cons] at h3
        exact List.eq_nil_of_length_eq_zero (by omega)
      rw [Walk.support_nil, ← hcons, htail]
  | @cons u v y hadj w1 ih =>
      intro y' w' hmap
      cases w' with
      | nil =>
          exfalso
          simp only [Walk.support_cons, Walk.support_nil, List.map_cons, List.map_nil] at hmap
          have h2 := congrArg List.length hmap
          simp only [List.length_cons, List.length_nil, List.length_map] at h2
          rw [Walk.length_support] at h2
          omega
      | @cons _ v' _ hadj' w1' =>
          have hmap' : (f u :: w1.support.map f) = (f u :: w1'.support.map f) := by
            simpa only [Walk.support_cons, List.map_cons] using hmap
          rw [List.cons.injEq] at hmap'
          have htail := hmap'.2
          have hv : v = v' := by
            refine hf.eq_of_adj hadj hadj' ?_
            have e1 : w1.support = v :: w1.support.tail := (Walk.cons_tail_support w1).symm
            have e2 : w1'.support = v' :: w1'.support.tail := (Walk.cons_tail_support w1').symm
            have h4 := htail
            rw [e1, e2, List.map_cons, List.map_cons, List.cons.injEq] at h4
            exact h4.1
          subst hv
          rw [Walk.support_cons, Walk.support_cons, ih w1' htail]

/-! ### 2. `GP(n,k) →g GP(d,k)` は被覆である -/

/-- `GP n k` の頂点 `(a,s)` の隣は三つだけ。 -/
theorem GP_neighbor (n k : ℕ) (a : ZMod n) (s : Bool) (y : V n) (hy : (GP n k).Adj (a, s) y) :
    (s = false ∧ (y = (a + 1, false) ∨ y = (a - 1, false) ∨ y = (a, true)))
      ∨ (s = true ∧ (y = (a + (k : ZMod n), true) ∨ y = (a - (k : ZMod n), true)
          ∨ y = (a, false))) := by
  obtain ⟨c, t⟩ := y
  rw [GP_adj] at hy
  obtain ⟨-, hr⟩ := hy
  rcases hr with (⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩) |
    (⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩)
  · refine Or.inl ⟨p1, Or.inl ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨by simpa using p3, by simpa using p2⟩
  · refine Or.inr ⟨p1, Or.inl ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨by simpa using p3, by simpa using p2⟩
  · refine Or.inl ⟨p1, Or.inr (Or.inr ?_)⟩
    simp only [Prod.mk.injEq]
    exact ⟨by simpa using p3, by simpa using p2⟩
  · refine Or.inl ⟨p2, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, by simpa using p1⟩
    have : a = c + 1 := by simpa using p3
    linear_combination -this
  · refine Or.inr ⟨p2, Or.inr (Or.inl ?_)⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, by simpa using p1⟩
    have : a = c + (k : ZMod n) := by simpa using p3
    linear_combination -this
  · refine Or.inr ⟨p2, Or.inr (Or.inr ?_)⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, by simpa using p1⟩
    have : a = c := by simpa using p3
    linear_combination -this

/-- `d ∣ n` なら `1 ≠ 0` は `ZMod d` から `ZMod n` に降りる。 -/
theorem one_ne_zero_of_quot (n d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0) : (1 : ZMod n) ≠ 0 := by
  intro hc
  apply h1
  have hq := congrArg (ZMod.castHom h (ZMod d)) hc
  rwa [map_one, map_zero] at hq

/-- `d ∣ n` なら `k ≠ 0` は `ZMod d` から `ZMod n` に降りる。 -/
theorem natCast_ne_zero_of_quot (n k d : ℕ) (h : d ∣ n) (hk : ((k : ℕ) : ZMod d) ≠ 0) :
    ((k : ℕ) : ZMod n) ≠ 0 := by
  intro hc
  apply hk
  have hq := congrArg (ZMod.castHom h (ZMod d)) hc
  rwa [map_natCast, map_zero] at hq

/-- **持ち上げの存在（局所）**：商側の隣接点は必ず持ち上がる。 -/
theorem exists_nbr_lift (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0) (hk : ((k : ℕ) : ZMod d) ≠ 0)
    (x : V n) (b : V d) (hb : (GP d k).Adj (quotMap n d h x) b) :
    ∃ y, (GP n k).Adj x y ∧ quotMap n d h y = b := by
  have hn1 : (1 : ZMod n) ≠ 0 := one_ne_zero_of_quot n d h h1
  have hnk : ((k : ℕ) : ZMod n) ≠ 0 := natCast_ne_zero_of_quot n k d h hk
  obtain ⟨a, s⟩ := x
  have hb' : (GP d k).Adj (ZMod.castHom h (ZMod d) a, s) b := hb
  rcases GP_neighbor d k (ZMod.castHom h (ZMod d) a) s b hb' with ⟨hs, hb3⟩ | ⟨hs, hb3⟩ <;>
    subst hs
  · rcases hb3 with rfl | rfl | rfl
    · exact ⟨(a + 1, false), GP_adj_outer n k a hn1, by
        simp only [quotMap_apply, map_add, map_one]⟩
    · refine ⟨(a - 1, false), ?_, by simp only [quotMap_apply, map_sub, map_one]⟩
      have := GP_adj_outer n k (a - 1) hn1
      rw [show a - 1 + 1 = a from by ring] at this
      exact this.symm
    · exact ⟨(a, true), GP_adj_spoke n k a, by simp only [quotMap_apply]⟩
  · rcases hb3 with rfl | rfl | rfl
    · exact ⟨(a + (k : ZMod n), true), GP_adj_inner n k a hnk, by
        simp only [quotMap_apply, map_add, map_natCast]⟩
    · refine ⟨(a - (k : ZMod n), true), ?_, by simp only [quotMap_apply, map_sub, map_natCast]⟩
      have := GP_adj_inner n k (a - (k : ZMod n)) hnk
      rw [show a - (k : ZMod n) + (k : ZMod n) = a from by ring] at this
      exact this.symm
    · exact ⟨(a, false), (GP_adj_spoke n k a).symm, by simp only [quotMap_apply]⟩

/-- **持ち上げの一意性（局所）**：`π` は各頂点の隣の三点の上で単射。
  要るのは `2 ≠ 0`（外輪の二つの隣が分かれる）と `2k ≠ 0`（内輪の二つの隣が分かれる）。 -/
theorem quot_inj_on_nbrs (n k d : ℕ) (h : d ∣ n) (h2 : (2 : ZMod d) ≠ 0)
    (h2k : (2 * (k : ℕ) : ZMod d) ≠ 0) {x y y' : V n}
    (hy : (GP n k).Adj x y) (hy' : (GP n k).Adj x y')
    (he : quotMap n d h y = quotMap n d h y') : y = y' := by
  obtain ⟨a, s⟩ := x
  have hfst : ZMod.castHom h (ZMod d) y.1 = ZMod.castHom h (ZMod d) y'.1 := congrArg Prod.fst he
  have hsnd : y.2 = y'.2 := congrArg (fun z : V d => z.2) he
  rcases GP_neighbor n k a s y hy with ⟨hs, hy3⟩ | ⟨hs, hy3⟩ <;>
    rcases GP_neighbor n k a s y' hy' with ⟨hs', hy3'⟩ | ⟨hs', hy3'⟩
  · rcases hy3 with rfl | rfl | rfl <;> rcases hy3' with rfl | rfl | rfl <;>
      simp only [map_add, map_sub, map_one, map_natCast] at hfst hsnd <;>
      first
        | rfl
        | exact absurd hsnd (by decide)
        | (exfalso; exact h2 (by push_cast; linear_combination hfst))
        | (exfalso; exact h2 (by push_cast; linear_combination -hfst))
  · exact absurd (hs'.symm.trans hs) (by decide)
  · exact absurd (hs.symm.trans hs') (by decide)
  · rcases hy3 with rfl | rfl | rfl <;> rcases hy3' with rfl | rfl | rfl <;>
      simp only [map_add, map_sub, map_one, map_natCast] at hfst hsnd <;>
      first
        | rfl
        | exact absurd hsnd (by decide)
        | (exfalso; exact h2k (by push_cast; linear_combination hfst))
        | (exfalso; exact h2k (by push_cast; linear_combination -hfst))

/-- **`π : GP(n,k) →g GP(d,k)` は被覆である。**
  条件はすべて「商グラフが 3 正則な単純グラフである」ことの言い換えで、
  `k = 3`・`d` 奇・`d ≥ 7` なら満たされる。 -/
theorem GP_isCovering (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0) (hk : ((k : ℕ) : ZMod d) ≠ 0)
    (h2 : (2 : ZMod d) ≠ 0) (h2k : (2 * (k : ℕ) : ZMod d) ≠ 0) :
    IsCovering (quotHom n k d h h1 hk) := by
  intro x b hb
  have hb' : (GP d k).Adj (quotMap n d h x) b := hb
  obtain ⟨y, hxy, hy⟩ := exists_nbr_lift n k d h h1 hk x b hb'
  refine ⟨y, ⟨hxy, hy⟩, fun z hz => ?_⟩
  have hz2 : quotMap n d h z = b := hz.2
  exact quot_inj_on_nbrs n k d h h2 h2k hz.1 hxy (by rw [hz2, hy])

/-- `k = 3` の場合の条件（`d` 奇・`d ≥ 7` で自動）。 -/
theorem GP3_covering_conditions (d : ℕ) (hodd : Odd d) (hd : 7 ≤ d) :
    (1 : ZMod d) ≠ 0 ∧ ((3 : ℕ) : ZMod d) ≠ 0 ∧ (2 : ZMod d) ≠ 0 ∧ (2 * (3 : ℕ) : ZMod d) ≠ 0 := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    rw [show (1 : ZMod d) = ((1 : ℕ) : ZMod d) by norm_num, ZMod.natCast_eq_zero_iff] at hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  · intro hc
    rw [ZMod.natCast_eq_zero_iff] at hc
    obtain ⟨m, hm⟩ := hodd
    have := Nat.le_of_dvd (by norm_num) hc
    interval_cases d <;> omega
  · intro hc
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_num, ZMod.natCast_eq_zero_iff] at hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega
  · intro hc
    rw [show (2 * (3 : ℕ) : ZMod d) = ((6 : ℕ) : ZMod d) by norm_num,
      ZMod.natCast_eq_zero_iff] at hc
    have := Nat.le_of_dvd (by norm_num) hc
    omega

end GeneralizedPetersen.Blocks

namespace GeneralizedPetersen.Blocks

open SimpleGraph GeneralizedPetersen.Base

/-- 射影は歩道を歩道に写し、台は像の台になる（Mathlib の `Walk.map`）。 -/
theorem quot_map_support (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0)
    (hk : ((k : ℕ) : ZMod d) ≠ 0) {x y : V n} (p : (GP n k).Walk x y) :
    (p.map (quotHom n k d h h1 hk)).support = p.support.map (quotHom n k d h h1 hk) :=
  SimpleGraph.Walk.support_map _ p

/-- 商写像は全射。 -/
theorem quotMap_surjective (n d : ℕ) [NeZero n] (h : d ∣ n) (z : V d) :
    ∃ x : V n, quotMap n d h x = z := by
  haveI : NeZero d := ⟨by rintro rfl; exact NeZero.ne n (Nat.eq_zero_of_zero_dvd h)⟩
  obtain ⟨c, t⟩ := z
  refine ⟨((((c.val : ℕ) : ZMod n)), t), ?_⟩
  simp only [quotMap_apply, Prod.mk.injEq, and_true, map_natCast]
  exact ZMod.natCast_rightInverse c

/-- **巻き数が定義できる**：商 `GP(d,k)` の閉路（始点は `x` の像）を持ち上げると、
  終点は `ρ^{d j} x` の形になる。この `j`（mod `n/d`）が紙の証明の巻き数 `w` である。 -/
theorem exists_lift_winding (n k d : ℕ) [NeZero n] (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0)
    (hk : ((k : ℕ) : ZMod d) ≠ 0) (h2 : (2 : ZMod d) ≠ 0) (h2k : (2 * (k : ℕ) : ZMod d) ≠ 0)
    (x : V n) (p : (GP d k).Walk (quotMap n d h x) (quotMap n d h x)) :
    ∃ (j : ℕ) (w : (GP n k).Walk x (((rot n) ^ (d * j)) x)),
      w.length = p.length ∧ w.support.map (quotHom n k d h h1 hk) = p.support := by
  obtain ⟨y, w, hy, hlen, hsup⟩ :=
    exists_lift (GP_isCovering n k d h h1 hk h2 h2k) p x rfl
  have hy' : quotMap n d h x = quotMap n d h y := hy.symm
  obtain ⟨j, hj⟩ := (quotMap_eq_iff n d h x y).mp hy'
  subst hj
  exact ⟨j, w, hlen, hsup⟩

/-- **持ち上げは始点で決まる**（`GP` 版）。 -/
theorem lift_unique_GP (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0)
    (hk : ((k : ℕ) : ZMod d) ≠ 0) (h2 : (2 : ZMod d) ≠ 0) (h2k : (2 * (k : ℕ) : ZMod d) ≠ 0)
    {x y y' : V n} (w : (GP n k).Walk x y) (w' : (GP n k).Walk x y')
    (hmap : w.support.map (quotHom n k d h h1 hk) = w'.support.map (quotHom n k d h h1 hk)) :
    w.support = w'.support :=
  lift_unique (GP_isCovering n k d h h1 hk h2 h2k) w w' hmap

end GeneralizedPetersen.Blocks

namespace GeneralizedPetersen.Blocks

open Finset GeneralizedPetersen.Base

variable {d : ℕ} [NeZero d]

/-! ### 1. 戻り時間 -/

/-- `t` 歩（歩幅 3）で `G_i` に戻る。`d` 歩目は無条件に許す（`3d = 0` で必ず戻るため）。
  こうしておくと `Nat.find` の存在条件が `r` に依らず成り立ち、定義が全域になる。 -/
def retP (F : Win d) (r : ZMod d) (t : ℕ) : Prop :=
  0 < t ∧ (d ≤ t ∨ F.i (r + 3 * (t : ZMod d)) = 0)

instance decRetP (F : Win d) (r : ZMod d) : DecidablePred (retP F r) := fun t => by
  unfold retP; infer_instance

theorem retP_ex (F : Win d) (r : ZMod d) : ∃ t, retP F r t :=
  ⟨d, Nat.pos_of_ne_zero (NeZero.ne d), Or.inl le_rfl⟩

/-- 戻り時間。 -/
def retT (F : Win d) (r : ZMod d) : ℕ := Nat.find (retP_ex F r)

/-- `next₃` の値。 -/
def ret (F : Win d) (r : ZMod d) : ZMod d := r + 3 * ((retT F r : ℕ) : ZMod d)

theorem retT_pos (F : Win d) (r : ZMod d) : 0 < retT F r := (Nat.find_spec (retP_ex F r)).1

theorem retT_le (F : Win d) (r : ZMod d) : retT F r ≤ d :=
  Nat.find_le ⟨Nat.pos_of_ne_zero (NeZero.ne d), Or.inl le_rfl⟩

theorem retT_min (F : Win d) {r : ZMod d} {t : ℕ} (ht : t < retT F r) : ¬ retP F r t :=
  Nat.find_min _ ht

/-- `G_i` の元から出発すれば、`next₃` の値も `G_i` の元。 -/
theorem ret_mem (F : Win d) {r : ZMod d} (hr : F.i r = 0) : F.i (ret F r) = 0 := by
  rcases (Nat.find_spec (retP_ex F r)).2 with hge | h
  · have he : retT F r = d := le_antisymm (retT_le F r) hge
    rw [ret, he, ZMod.natCast_self, mul_zero, add_zero]
    exact hr
  · exact h

/-- `next₃` は糸を変えない。 -/
theorem ret_sameThread (F : Win d) (r : ZMod d) : sameThread d r (ret F r) := ⟨retT F r, rfl⟩

/-! ### 2. 単射性 -/

theorem ret_inj_aux (F : Win d) {r r' : ZMod d} (hr : F.i r = 0) (hr' : F.i r' = 0)
    (he : ret F r = ret F r') (hle : retT F r ≤ retT F r') : r = r' := by
  have hp := retT_pos F r
  have hp' := retT_pos F r'
  rcases eq_or_lt_of_le hle with heq | hlt
  · simp only [ret, heq] at he
    exact add_right_cancel he
  · exfalso
    refine retT_min F (r := r') (t := retT F r' - retT F r) (by omega) ⟨by omega, Or.inr ?_⟩
    have hcast : ((retT F r' - retT F r : ℕ) : ZMod d)
        = ((retT F r' : ℕ) : ZMod d) - ((retT F r : ℕ) : ZMod d) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have hrw : r' + 3 * (((retT F r' : ℕ) : ZMod d) - ((retT F r : ℕ) : ZMod d)) = r := by
      simp only [ret] at he
      linear_combination -he
    rw [hrw]
    exact hr

/-- **単射性**：`next₃` は `G_i` の上で単射。 -/
theorem ret_inj (F : Win d) {r r' : ZMod d} (hr : F.i r = 0) (hr' : F.i r' = 0)
    (he : ret F r = ret F r') : r = r' := by
  rcases le_total (retT F r) (retT F r') with hle | hle
  · exact ret_inj_aux F hr hr' he hle
  · exact (ret_inj_aux F hr' hr he.symm hle).symm

/-! ### 3. 置換としての `next₃` -/

/-- **`next₃` は `G_i` の置換**（紙の証明の `ν`）。 -/
noncomputable def next3 (F : Win d) : Equiv.Perm ↥(Gi F) :=
  Equiv.ofBijective (fun x => ⟨ret F (x : ZMod d), by
      rw [mem_Gi]
      exact ret_mem F ((mem_Gi F _).mp x.2)⟩)
    (Finite.injective_iff_bijective.mp (fun x y hxy => by
      apply Subtype.ext
      exact ret_inj F ((mem_Gi F _).mp x.2) ((mem_Gi F _).mp y.2) (congrArg Subtype.val hxy)))

@[simp] theorem next3_val (F : Win d) (x : ↥(Gi F)) :
    ((next3 F x : ↥(Gi F)) : ZMod d) = ret F (x : ZMod d) := rfl

/-- `G_i` の要素の数は `q`。 -/
theorem card_Gi_type (F : Win d) : Fintype.card ↥(Gi F) = F.q := by
  rw [Fintype.card_coe, card_Gi]

/-- **紙の証明の定理 2 の形**：`α` を `G_i` そのもの、`ν` を `next₃` に固定した版。
  残る仮定は `θ`（円周上の前者置換）の構成と、`hbridge`（`next₃` の軌道の本数＝糸の数）だけ。 -/
theorem next3_theta_not_full_cycle (F : Win d) (hodd : Odd d)
    (hall : 3 ∣ d → ∀ c : ZMod (Nat.gcd 3 d), c ∈ Thr F)
    (θ : Equiv.Perm ↥(Gi F)) (hθ : θ.IsCycle) (hθs : θ.support = Finset.univ)
    (hbridge : GeneralizedPetersen.Base.orbCount (next3 F) = (Thr F).card) :
    ¬ ((next3 F * θ).IsCycle ∧ (next3 F * θ).support = Finset.univ) :=
  quot_two_factor_not_cycle F hodd hall (card_Gi_type F) θ (next3 F) hθ hθs hbridge

end GeneralizedPetersen.Blocks

namespace GeneralizedPetersen.Blocks

open Finset GeneralizedPetersen.Base

variable {d : ℕ} [NeZero d]

/-! ### 1. 反復と `ret` -/

theorem next3_pow_val (F : Win d) : ∀ (k : ℕ) (x : ↥(Gi F)),
    (((next3 F ^ k) x : ↥(Gi F)) : ZMod d) = (ret F)^[k] (x : ZMod d) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (next3 F x), Function.iterate_succ_apply, next3_val]

/-! ### 2. 到達可能性 -/

/-- `x` から `x + 3u`（どちらも `G_i` の元）へは `next₃` の反復で届く。 -/
theorem reach (F : Win d) : ∀ (u : ℕ) (x : ZMod d), F.i x = 0 →
    F.i (x + 3 * (u : ZMod d)) = 0 → ∃ k : ℕ, (ret F)^[k] x = x + 3 * (u : ZMod d) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro x hx hxu
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · exact ⟨0, by simp⟩
    · have hretP : retP F x u := ⟨hu, Or.inr hxu⟩
      have hle : retT F x ≤ u := Nat.find_le hretP
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact ⟨1, by rw [Function.iterate_one]; simp only [ret, heq]⟩
      · have hp := retT_pos F x
        have hx' : F.i (ret F x) = 0 := ret_mem F hx
        have hcast : ret F x + 3 * ((u - retT F x : ℕ) : ZMod d) = x + 3 * (u : ZMod d) := by
          rw [Nat.cast_sub hle]
          simp only [ret]
          ring
        obtain ⟨k, hk⟩ := ih (u - retT F x) (by omega) (ret F x) hx' (by rw [hcast]; exact hxu)
        exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk, hcast]⟩

/-! ### 3. `3 ∤ d` なら糸は一本 -/

theorem sameThread_of_not_dvd (h3 : ¬ (3 ∣ d)) (r s : ZMod d) : sameThread d r s := by
  rw [← thrHom_eq_iff]
  haveI : NeZero (Nat.gcd 3 d) := ⟨fun h => (NeZero.ne d) (Nat.gcd_eq_zero_iff.mp h).2⟩
  have hg : Nat.gcd 3 d = 1 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
  have hcard : Fintype.card (ZMod (Nat.gcd 3 d)) = 1 := by rw [ZMod.card, hg]
  haveI : Subsingleton (ZMod (Nat.gcd 3 d)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hcard)
  exact Subsingleton.elim _ _

/-- **不動点なし**：`d` 奇・`3 ∤ d` なら `next₃` は `G_i` の元を固定しない。 -/
theorem next3_ne_self (F : Win d) (hodd : Odd d) (h3 : ¬ (3 ∣ d)) (x : ↥(Gi F)) :
    next3 F x ≠ x := by
  intro hfix
  have hxG : F.i (x : ZMod d) = 0 := (mem_Gi F _).mp x.2
  have hret : ret F (x : ZMod d) = (x : ZMod d) := by
    have := congrArg Subtype.val hfix
    rwa [next3_val] at this
  -- `3 * retT x = 0` から `d ∣ retT x`、ゆえに `retT x = d`
  have h0 : ((3 * retT F (x : ZMod d) : ℕ) : ZMod d) = 0 := by
    push_cast
    simp only [ret] at hret
    linear_combination hret
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hcop : Nat.Coprime d 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3)
  have h0' : d ∣ retT F (x : ZMod d) * 3 := by rw [Nat.mul_comm]; exact h0
  have hdvd : d ∣ retT F (x : ZMod d) := by
    first
      | exact hcop.dvd_of_dvd_mul_left h0'
      | exact hcop.dvd_of_dvd_mul_right h0'
      | exact hcop.dvd_of_dvd_mul_left h0
      | exact hcop.dvd_of_dvd_mul_right h0
  have hpos := retT_pos F (x : ZMod d)
  have hle := retT_le F (x : ZMod d)
  have heqd : retT F (x : ZMod d) = d := Nat.le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  -- ところが `|G_i| ≥ 2` なので、`x` とは別の元がある
  have hq2 : 2 ≤ F.q := by
    have h1 : F.q = 2 * F.n1 := q_eq_two_n1 F hodd
    have h2 : 0 < F.q := by
      rw [← card_Gi]
      exact Finset.card_pos.mpr ⟨(x : ZMod d), x.2⟩
    omega
  have hcard2 : 1 < (Gi F).card := by rw [card_Gi]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
  obtain ⟨y, hyG, hyx⟩ : ∃ y ∈ Gi F, y ≠ (x : ZMod d) := by
    by_cases hax : a = (x : ZMod d)
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨t, ht⟩ := sameThread_of_not_dvd h3 (x : ZMod d) y
  have hmod : ((t % d : ℕ) : ZMod d) = ((t : ℕ) : ZMod d) := by
    conv_rhs => rw [← Nat.div_add_mod t d]
    push_cast
    simp [ZMod.natCast_self]
  have hs0 : t % d ≠ 0 := by
    intro hz
    apply hyx
    rw [ht, ← hmod, hz]
    simp
  have hsP : retP F (x : ZMod d) (t % d) := by
    refine ⟨Nat.pos_of_ne_zero hs0, Or.inr ?_⟩
    rw [hmod, ← ht]
    exact (mem_Gi F y).mp hyG
  have hfin : retT F (x : ZMod d) ≤ t % d := Nat.find_le hsP
  have hlt : t % d < d := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))
  omega

/-! ### 4. `next₃` は全体を回す巡回、ゆえに符号は `−1` -/

theorem card_Gi_even (F : Win d) (hodd : Odd d) : Even (Fintype.card ↥(Gi F)) := by
  refine ⟨F.n1, ?_⟩
  rw [card_Gi_type, q_eq_two_n1 F hodd]
  ring

/-- **`3 ∤ d` なら `next₃` は `G_i` 全体を回す一本の巡回**。 -/
theorem next3_isCycle (F : Win d) (hodd : Odd d) (h3 : ¬ (3 ∣ d)) (hne : (Gi F).Nonempty) :
    (next3 F).IsCycle ∧ (next3 F).support = Finset.univ := by
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨⟨⟨x0, hx0⟩, next3_ne_self F hodd h3 _, fun y _ => ?_⟩, ?_⟩
  · -- 推移性
    obtain ⟨t, ht⟩ := sameThread_of_not_dvd h3 x0 (y : ZMod d)
    obtain ⟨k, hk⟩ := reach F t x0 ((mem_Gi F _).mp hx0) (by rw [← ht]; exact (mem_Gi F _).mp y.2)
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    rw [next3_pow_val]
    rw [hk, ← ht]
  · refine Finset.eq_univ_iff_forall.mpr (fun y => ?_)
    rw [Equiv.Perm.mem_support]
    exact next3_ne_self F hodd h3 y

/-- **符号が仮定なしで出る**：`d` 奇・`3 ∤ d` なら `sign (next₃) = −1`。 -/
theorem sign_next3 (F : Win d) (hodd : Odd d) (h3 : ¬ (3 ∣ d)) (hne : (Gi F).Nonempty) :
    Equiv.Perm.sign (next3 F) = -1 := by
  obtain ⟨hc, hs⟩ := next3_isCycle F hodd h3 hne
  exact GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle _ hc hs (card_Gi_even F hodd)

/-- **紙の証明の定理 2（`3 ∤ d` の場合）が、橋の仮定なしで閉じる。**
  `d` 奇・`3 ∤ d` の `Win d` に対し、`next₃ ∘ θ` は `G_i` 全体を回る巡回になれない。 -/
theorem next3_theta_not_full_cycle_of_not_dvd (F : Win d) (hodd : Odd d) (h3 : ¬ (3 ∣ d))
    (hne : (Gi F).Nonempty) (θ : Equiv.Perm ↥(Gi F)) (hθ : θ.IsCycle)
    (hθs : θ.support = Finset.univ) :
    ¬ ((next3 F * θ).IsCycle ∧ (next3 F * θ).support = Finset.univ) := by
  rintro ⟨h1, h2⟩
  have hev := card_Gi_even F hodd
  have e1 : Equiv.Perm.sign (next3 F * θ) = -1 :=
    GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle _ h1 h2 hev
  have e2 : Equiv.Perm.sign (next3 F * θ) = 1 := by
    rw [map_mul, sign_next3 F hodd h3 hne,
      GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle θ hθ hθs hev]
    simp
  rw [e1] at e2
  have e3 := congrArg (Units.val : ℤˣ → ℤ) e2
  norm_num at e3

end GeneralizedPetersen.Blocks
