/-
  その2・本体 —
  エルデシュ問題 #169。**setA と 3-AP-free の鎖を一本の定理にする。**

  【何を結ぶか（J2-4 の「新しい未」）】
    ・逆数和：`APFreeWindowsDisjoint.setA_lower` — 集合 `setA = ⋃ winsAll` の上の Σ 1/n
    ・3-AP-free：`APFreePolicyRollout` の鎖（`steps793` の (z,t,M) と `blocks793` の (p,q,r,t,桁)）
    この二つは**別の対象**について立っていた。本ファイルは両者を `regroup` で照合し、
    **「setA は 3-AP-free であり、かつ Σ 1/x > 3.00849」を一つの定理**にする。

  【照合の骨（Python `外の生成器` で先に確かめた）】
    ・Σ M_i = 56·1 + 17·2 + 27·3 = 171 = wins50.length + wins100b.length。
      ⟹ steps793 の M で窓の一覧を順に切れば、第 i 段の窓がちょうど取れる。
    ・各窓の (p,n,r) は blocks793[i] の (p,q,r) と 171/171 一致する。
    ・段の t は blocks793[i] の最大元と 100/100 一致する。
    ・窓の右端を **t（真の最大元）**に取れば段ごとの (W) は 100/100 通る。
      **`mxv`（緩い上界）に取ると 55/100 で破れる**——ここは緩めてはいけない。
      （壁8''：道具のパラメータを、適用範囲を確かめずに緩めない。）

  【機械検査の中身】`chainChk groups844 21523361 = true` の一つの `decide` が
    ・鎖の整合（cur = z、z ≤ nextZ793）
    ・blocks793 の各段の `APFree.StepsMaxElement.stepOK`（⟹ t がブロックの最大元）
    ・窓と段の (p,n,r,t) の照合
    ・窓が次の段の箱に収まること
    ・段ごとの窓分離 (W)（`sepL`。(M+1)³ ≤ 64 三つ組 × 100 段）
    を一度に見る。

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.ChainRecordCore

namespace APFree.ChainRecord

open APFree.WindowSeparation APFree.StepsMaxElement APFree.BlockBounds

set_option maxRecDepth 4000000

/-! ## 1. 段と窓の対応（regroup） -/

/-- 鎖の段 `(z,t,M)` と、その段のブロック `(p,q,r,t,桁)` と、その段の窓 M 個。 -/
abbrev Group := ((ℤ × ℤ × ℕ) × (ℕ × ℕ × ℕ × ℕ × List ℕ)) × List (ℕ × ℕ × ℕ × ℕ)

/-- 窓の一覧を、段ごとの M で順に切り分ける。 -/
def regroup : List ((ℤ × ℤ × ℕ) × (ℕ × ℕ × ℕ × ℕ × List ℕ)) →
    List (ℕ × ℕ × ℕ × ℕ) → List Group
  | [], _ => []
  | s :: ss, ws => (s, ws.take s.1.2.2) :: regroup ss (ws.drop s.1.2.2)

/-- 切り分けは窓の一覧をちょうど使い切る（Σ M = 窓の数のとき）。 -/
theorem regroup_flat : ∀ (ss : List ((ℤ × ℤ × ℕ) × (ℕ × ℕ × ℕ × ℕ × List ℕ)))
    (ws : List (ℕ × ℕ × ℕ × ℕ)),
    (ss.map (fun s => s.1.2.2)).sum = ws.length →
    (regroup ss ws).flatMap (fun g => g.2) = ws := by
  intro ss
  induction ss with
  | nil =>
      intro ws h
      cases ws with
      | nil => rfl
      | cons a l => simp at h
  | cons s ss ih =>
      intro ws h
      simp only [List.map_cons, List.sum_cons] at h
      have hrest : (ss.map (fun s => s.1.2.2)).sum = (ws.drop s.1.2.2).length := by
        rw [List.length_drop]; omega
      simp only [regroup, List.flatMap_cons, ih _ hrest]
      exact List.take_append_drop _ _

/-! ## 2. 一段ぶんの機械検査 -/

/-- 一段ぶんの検査。**照合（窓の (p,n,r) と段のブロックの一致）はここに入っている。** -/
def stepChk : Group → Bool
  | (((z, t, M), (p, q, r, tb, ds)), ws) =>
      decide (ws.length = M) &&
      decide ((0 : ℤ) ≤ z) &&
      decide ((0 : ℤ) ≤ t) &&
      decide (1 ≤ p) &&
      decide ((tb : ℤ) = t) &&
      APFree.StepsMaxElement.stepOK (p, q, r, tb, ds) &&
      decide (z ≤ APFree.PolicyRollout.nextZ793 z t M) &&
      (ws.all fun w =>
        decide (w.1 = p) && decide (w.2.1 = q) && decide (w.2.2.1 = r) &&
        decide (((w.2.2.2 : ℕ) : ℤ) + t ≤ APFree.PolicyRollout.nextZ793 z t M)) &&
      sepL (stepIvs z t ws)

/-- 鎖ぜんぶの検査（頭の最大元から始めて、段ごとに箱を継ぐ）。 -/
def chainChk : List Group → ℤ → Bool
  | [], _ => true
  | g :: gs, cur =>
      decide (cur = g.1.1.1) && stepChk g &&
        chainChk gs (APFree.PolicyRollout.nextZ793 g.1.1.1 g.1.1.2.1 g.1.1.2.2)

/-! ## 3. 鎖を継ぐ -/

/-- 段を継いで得られる集合。 -/
def growZ (S : Set ℤ) : List Group → Set ℤ
  | [] => S
  | g :: gs => growZ (S ∪ unionWZ g.2) gs

theorem growZ_eq : ∀ (gs : List Group) (S : Set ℤ),
    growZ S gs = S ∪ unionWZ (gs.flatMap (fun g => g.2)) := by
  intro gs
  induction gs with
  | nil => intro S; simp [growZ, unionWZ]
  | cons g gs ih =>
      intro S
      simp [growZ, ih, List.flatMap_cons, unionWZ_append, Set.union_assoc]

/-- **鎖の定理**：検査を通る鎖を継いで得られる集合は 3-AP-free。 -/
theorem grow_apfree : ∀ (gs : List Group) (S : Set ℤ) (cur : ℤ),
    IsThreeAPFree S → (∀ x ∈ S, (0 : ℤ) ≤ x ∧ x ≤ cur) → chainChk gs cur = true →
    IsThreeAPFree (growZ S gs) := by
  intro gs
  induction gs with
  | nil => intro S cur hS _ _; exact hS
  | cons g gs ih =>
      intro S cur hS hbox hchk
      obtain ⟨⟨⟨z, t, M⟩, p, q, r, tb, ds⟩, ws⟩ := g
      rw [chainChk] at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      obtain ⟨⟨hcur, hstep⟩, hrest⟩ := hchk
      rw [hcur] at hbox
      rw [stepChk] at hstep
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
      obtain ⟨hA, hsep⟩ := hstep
      obtain ⟨hB, hwallB⟩ := hA
      obtain ⟨hC, hznext⟩ := hB
      obtain ⟨hD, hsok⟩ := hC
      obtain ⟨hE, htb⟩ := hD
      obtain ⟨hF, hp1⟩ := hE
      obtain ⟨hG, _ht⟩ := hF
      obtain ⟨_hlen, _hz⟩ := hG
      have hwall := List.all_eq_true.mp hwallB
      -- ブロックの最大元
      have hgreat : IsGreatest (Blk p q r) tb :=
        APFree.StepsMaxElement.maxelt_of_stepOK (p, q, r, tb, ds) hsok
      -- 各窓の性質
      have hwin : ∀ i, i < ws.length →
          (nthW ws i).1 = p ∧ (nthW ws i).2.1 = q ∧ (nthW ws i).2.2.1 = r ∧
          (((nthW ws i).2.2.2 : ℕ) : ℤ) + t ≤ APFree.PolicyRollout.nextZ793 z t M := by
        intro i hi
        have h := hwall (nthW ws i) (nthW_mem ws i hi)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      have hgreat' : ∀ i, i < ws.length →
          IsGreatest (Blk (nthW ws i).1 (nthW ws i).2.1 (nthW ws i).2.2.1) tb := by
        intro i hi
        obtain ⟨h1, h2, h3, _⟩ := hwin i hi
        rw [h1, h2, h3]; exact hgreat
      have hwbox : ∀ i, i < ws.length → ∀ x ∈ winZ (nthW ws i),
          (((nthW ws i).2.2.2 : ℕ) : ℤ) ≤ x ∧ x ≤ (((nthW ws i).2.2.2 : ℕ) : ℤ) + t := by
        intro i hi x hx
        have h := winZ_box (nthW ws i) tb (hgreat' i hi) x hx
        rw [← htb]; exact h
      have hwfree : ∀ i, i < ws.length → IsThreeAPFree (winZ (nthW ws i)) := by
        intro i hi
        refine winZ_apfree (nthW ws i) ?_
        rw [(hwin i hi).1]; exact hp1
      -- 一段ぶん
      have hnew : IsThreeAPFree (S ∪ unionWZ ws) :=
        step_apfree S z t ws hS hbox hwbox hwfree hsep
      have hnewbox : ∀ x ∈ S ∪ unionWZ ws,
          (0 : ℤ) ≤ x ∧ x ≤ APFree.PolicyRollout.nextZ793 z t M := by
        rintro x (hx | hx)
        · have := hbox x hx; omega
        · obtain ⟨i, hi, hx'⟩ := (mem_unionWZ ws x).mp hx
          have hb := hwbox i hi x hx'
          have hn := (hwin i hi).2.2.2
          have h0 : (0 : ℤ) ≤ (((nthW ws i).2.2.2 : ℕ) : ℤ) := Int.natCast_nonneg _
          omega
      exact ih (S ∪ unionWZ ws) (APFree.PolicyRollout.nextZ793 z t M) hnew hnewbox hrest

/-! ## 4. 実データを流し込む -/

/-- 100 段ぶんの (段 × ブロック × 窓)。**窓の一覧は `APFreeBlockBoundsWindows50/c` のもの、
    段とブロックは `APFreePolicyRollout` のもの**——二つの表がここで初めて一つになる。 -/
def groups844 : List Group :=
  regroup (List.zip APFree.PolicyRollout.steps793 APFree.PolicyRollout.blocks793) (wins50 ++ wins100b)

set_option maxHeartbeats 4000000 in
/-- **本ファイルの機械検査**（鎖の整合・最大元・照合・箱・窓分離をまとめて一つの `decide`）。 -/
theorem chain844 : chainChk groups844 21523361 = true := by decide

/-! ## 5. 頭 Z₀ -/

/-- 頭 Z₀ = 1 + B(2,16,0) のブロック記述。p = 2 では T ≡ 0 なので r = 0、
    最大元は桁がすべて 1 の 21523360 = (3¹⁶−1)/2 である。 -/
def headBlk : ℕ × ℕ × ℕ × ℕ × List ℕ :=
  (2, 16, 0, 21523360, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])

theorem headBlk_ok : APFree.StepsMaxElement.stepOK headBlk = true := by decide

theorem head_great : IsGreatest (Blk 2 16 0) 21523360 :=
  APFree.StepsMaxElement.maxelt_of_stepOK headBlk headBlk_ok

theorem head_apfree : IsThreeAPFree (winZ (2, 16, 0, 1)) := winZ_apfree (2, 16, 0, 1) (by norm_num)

theorem head_box : ∀ x ∈ winZ (2, 16, 0, 1), (0 : ℤ) ≤ x ∧ x ≤ 21523361 := by
  intro x hx
  have h := winZ_box (2, 16, 0, 1) 21523360 head_great x hx
  simp only at h
  omega

/-! ## 6. 得られた集合が `APFreeWindowsDisjoint.setA` であること -/

theorem winZ_eq_coe (w : ℕ × ℕ × ℕ × ℕ) (hp : 1 ≤ w.1) :
    winZ w = {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.winF w, x = (n : ℤ)} := by
  obtain ⟨p, n, r, a⟩ := w
  ext x
  simp only [winZ, APFree.WindowsDisjoint.winF, Set.mem_setOf_eq, Finset.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ BlkF p n r := by
      have hc := coe_BlkF p hp n r
      rw [← hc] at hs; exact hs
    exact ⟨a + s, ⟨s, hs', rfl⟩, by push_cast; ring⟩
  · rintro ⟨m, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s, ?_, by push_cast; ring⟩
    have hc := coe_BlkF p hp n r
    rw [← hc]; exact hs

theorem unionWZ_eq_coe : ∀ (ws : List (ℕ × ℕ × ℕ × ℕ)), (∀ w ∈ ws, 1 ≤ w.1) →
    unionWZ ws = {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.unionW ws, x = (n : ℤ)} := by
  intro ws
  induction ws with
  | nil => intro _; ext x; simp [unionWZ, APFree.WindowsDisjoint.unionW]
  | cons w ws ih =>
      intro h
      ext x
      rw [unionWZ, APFree.WindowsDisjoint.unionW, Set.mem_union, winZ_eq_coe w (h w (by simp)),
        ih (fun v hv => h v (by simp [hv]))]
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_union]
      constructor
      · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
        · exact ⟨n, Or.inl hn, rfl⟩
        · exact ⟨n, Or.inr hn, rfl⟩
      · rintro ⟨n, (hn | hn), rfl⟩
        · exact Or.inl ⟨n, hn, rfl⟩
        · exact Or.inr ⟨n, hn, rfl⟩

theorem groups_flat : groups844.flatMap (fun g => g.2) = wins50 ++ wins100b := by
  refine regroup_flat _ _ ?_
  decide

theorem grow_eq_setA :
    growZ (winZ (2, 16, 0, 1)) groups844 = {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.setA, x = (n : ℤ)} := by
  rw [growZ_eq, groups_flat]
  have hw : winZ (2, 16, 0, 1) ∪ unionWZ (wins50 ++ wins100b)
      = unionWZ APFree.WindowsDisjoint.winsAll := rfl
  rw [hw, APFree.WindowsDisjoint.setA]
  exact unionWZ_eq_coe APFree.WindowsDisjoint.winsAll APFree.WindowsDisjoint.winsAll_p

/-! ## 7. 主定理 -/

/-- **構成 A は 3-AP を含まない**（Wróblewski 1984 Lemma 1 ＋ 定理W ＋ 100 段の鎖）。 -/
theorem setA_apfree : IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.setA, x = (n : ℤ)} := by
  rw [← grow_eq_setA]
  exact grow_apfree groups844 (winZ (2, 16, 0, 1)) 21523361 head_apfree head_box chain844

/-- **本ファイルの主定理（★91 の機械検証を単一の型に）**：
    構成 A は 3-AP-free であり、かつその逆数和は **3.0085383814002 を超える**。
    ⟹ 42 年動いていない記録 3.00849 を、**同じ一つの集合について**上回る。
    （sorry 0・native_decide 不使用。**査読ではない——検証待ちの候補である。**） -/
theorem setA_apfree_and_lower :
    IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.setA, x = (n : ℤ)} ∧
      (30085383814002 : ℚ) / 10 ^ 13 < ∑ x ∈ APFree.WindowsDisjoint.setA, (1 : ℚ) / x :=
  ⟨setA_apfree, APFree.WindowsDisjoint.setA_lower⟩

/-- 記録との比較まで含めた形。 -/
theorem setA_apfree_and_beats_record :
    IsThreeAPFree {x : ℤ | ∃ n ∈ APFree.WindowsDisjoint.setA, x = (n : ℤ)} ∧
      (300849 : ℚ) / 10 ^ 5 < ∑ x ∈ APFree.WindowsDisjoint.setA, (1 : ℚ) / x :=
  ⟨setA_apfree, APFree.WindowsDisjoint.setA_beats_record⟩

end APFree.ChainRecord

/-! ### 公理の確認 -/

#print axioms APFree.ChainRecord.chain844
#print axioms APFree.ChainRecord.grow_apfree
#print axioms APFree.ChainRecord.grow_eq_setA
#print axioms APFree.ChainRecord.setA_apfree
#print axioms APFree.ChainRecord.setA_apfree_and_lower
#print axioms APFree.ChainRecord.setA_apfree_and_beats_record
#print axioms APFree.ChainRecord.groups_flat
