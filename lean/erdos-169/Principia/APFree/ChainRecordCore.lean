/-
  その1 —
  エルデシュ問題 #169。**setA（逆数和の対象）と鎖（3-AP-free 性の対象）を結ぶための一般機構。**

  【なぜ要るか（J2-4）】
    `APFreeWindowsDisjoint.setA_lower` は「集合 A の上の Σ 1/n」を言う。
    `APFreePolicyRollout.all_steps_separated` は「鎖の各段が窓分離 (W) を満たす」を言う。
    **両者は Lean の中で結ばれていない。**本ファイルはその橋を一般形で架け、
    `Principia.APFree.ChainRecord` が 100 段の実データを流し込む。

  【設計】
    (0) リストの取り出し `nthI` / `nthW` を自前で持つ（Mathlib の補題名に依存しない）
    (1) `sepL` — 窓分離 (W) を**区間のリストの Bool 検査**にしたもの。
        APFreeWindowSeparation の `Separated` と同じ内容を、`decide` に載る形で書き直す。
        **適用範囲：この定式化が使えるのは「各集合が閉区間 [l, r] に収まる」ときだけである。**
        （壁8'' ——注意書きは、書いた場所ではなく使う場所に置く。）
    (2) `apfree_unionL` — 区間で分離されたリストの合併は 3-AP-free。
        APFreeWindowSeparation `apfree_iUnion_of_separated` の**リスト版**（同じ論法を添字 ℕ で書き直したもの）
    (3) `Blk_apfree` — **APFreeNonAveraging の Lemma 1 を `APFreeWindowSeparation.IsThreeAPFree` の形に載せる**。
        ここがまで空いていた穴である。Sphere の weight は `W = 2·T` の総和なので
        **r ではなく 2r** を渡す。桁の向きは `valL`（下位から）＝ APFreeNonAveraging の `val`。
    (4) `winZ` / `unionWZ` — 窓 `(p,n,r,a)` の覆う集合を ℤ 側で見たもの
    (5) `step_apfree` — 一段ぶん（前段までの集合を「頭の窓 [0,z]」に潰す）
    (6) `regroup` / `growZ` / `grow_apfree` — 鎖を継ぐ帰納

  sorry 0・native_decide 不使用。
-/
import Principia.APFree.WindowsDisjoint
import Principia.APFree.PolicyRollout
import Principia.APFree.NonAveraging

namespace APFree.ChainRecord

open APFree.WindowSeparation APFree.StepsMaxElement APFree.BlockBounds

/-! ## 0. 自前の取り出し（既存の補題名に依存しない） -/

/-- 区間のリストの i 番目（範囲外は `(0,0)`）。 -/
def nthI : List (ℤ × ℤ) → ℕ → ℤ × ℤ
  | [], _ => (0, 0)
  | a :: _, 0 => a
  | _ :: l, n + 1 => nthI l n

/-- 窓のリストの i 番目（範囲外は `(1,0,0,0)`）。 -/
def nthW : List (ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ × ℕ × ℕ × ℕ
  | [], _ => (1, 0, 0, 0)
  | a :: _, 0 => a
  | _ :: l, n + 1 => nthW l n

theorem nthW_mem : ∀ (ws : List (ℕ × ℕ × ℕ × ℕ)) (i : ℕ), i < ws.length → nthW ws i ∈ ws := by
  intro ws
  induction ws with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
      intro i hi
      cases i with
      | zero => simp [nthW]
      | succ n =>
          have hn : n < ws.length := by simpa using hi
          exact List.mem_cons_of_mem _ (ih n hn)

theorem nthI_map (f : (ℕ × ℕ × ℕ × ℕ) → ℤ × ℤ) :
    ∀ (ws : List (ℕ × ℕ × ℕ × ℕ)) (i : ℕ), i < ws.length →
      nthI (ws.map f) i = f (nthW ws i) := by
  intro ws
  induction ws with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ n =>
          have hn : n < ws.length := by simpa using hi
          simpa [List.map_cons, nthI, nthW] using ih n hn

/-! ## 1. 窓分離 (W) の Bool 版

  **適用範囲**：`sepL` は区間のリストだけを見る。使う側は
  「各集合が対応する閉区間に収まる」ことを別に示さねばならない（`apfree_unionL` の `hbox`）。 -/

/-- 三つ組 (i, j, k) についての (W)。 -/
def sepPair (I J K : ℤ × ℤ) : Bool :=
  decide (2 * J.2 < I.1 + K.1) || decide (I.2 + K.2 < 2 * J.1)

/-- 区間のリストが (W) を満たすか（i = j = k は除く）。 -/
def sepL (ivs : List (ℤ × ℤ)) : Bool :=
  (List.range ivs.length).all fun i =>
    (List.range ivs.length).all fun j =>
      (List.range ivs.length).all fun k =>
        (i == j && j == k) || sepPair (nthI ivs i) (nthI ivs j) (nthI ivs k)

theorem sepL_spec (ivs : List (ℤ × ℤ)) (h : sepL ivs = true)
    (i j k : ℕ) (hi : i < ivs.length) (hj : j < ivs.length) (hk : k < ivs.length)
    (hne : ¬(i = j ∧ j = k)) :
    2 * (nthI ivs j).2 < (nthI ivs i).1 + (nthI ivs k).1 ∨
      (nthI ivs i).2 + (nthI ivs k).2 < 2 * (nthI ivs j).1 := by
  have h1 := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  have h2 := (List.all_eq_true.mp h1) j (List.mem_range.mpr hj)
  have h3 := (List.all_eq_true.mp h2) k (List.mem_range.mpr hk)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · exact absurd (by simpa [Bool.and_eq_true] using h3) hne
  · rw [sepPair, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h3
    exact h3

/-! ## 2. 分離されたリストの合併は 3-AP-free（APFreeWindowSeparation のリスト版） -/

/-- 添字つきの合併。 -/
def unionIdx (A : ℕ → Set ℤ) (n : ℕ) : Set ℤ := {x | ∃ i, i < n ∧ x ∈ A i}

/-- **定理W のリスト版**。論法は `APFreeWindowSeparation.apfree_iUnion_of_separated` と同じ。 -/
theorem apfree_unionL (ivs : List (ℤ × ℤ)) (A : ℕ → Set ℤ)
    (hbox : ∀ i, i < ivs.length → ∀ x ∈ A i, (nthI ivs i).1 ≤ x ∧ x ≤ (nthI ivs i).2)
    (hfree : ∀ i, i < ivs.length → IsThreeAPFree (A i))
    (hsep : sepL ivs = true) :
    IsThreeAPFree (unionIdx A ivs.length) := by
  rintro x ⟨i, hi, hxi⟩ y ⟨j, hj, hyj⟩ z ⟨k, hk, hzk⟩ hxyz
  by_cases hh : i = j ∧ j = k
  · obtain ⟨rfl, rfl⟩ := hh
    exact hfree i hi x hxi y hyj z hzk hxyz
  · exfalso
    obtain ⟨hx1, hx2⟩ := hbox i hi x hxi
    obtain ⟨hy1, hy2⟩ := hbox j hj y hyj
    obtain ⟨hz1, hz2⟩ := hbox k hk z hzk
    rcases sepL_spec ivs hsep i j k hi hj hk hh with hs | hs <;> omega

/-! ## 3. ブロック B(p,q,r) は 3-AP-free（APFreeNonAveraging の Lemma 1 を IsThreeAPFree の形に載せる） -/

/-- APFreeNonAveraging の `val`（下位から）は `APFreeStepsMaxElement.valL` と同じ。 -/
theorem val_eq_valL (b : ℕ) : ∀ ks : List ℕ, APFree.NonAveraging.val b ks = valL b ks := by
  intro ks
  induction ks with
  | nil => rfl
  | cons a as ih => simp [APFree.NonAveraging.val, valL, ih]

/-- 重み。`W (aa p) (bb p) ks = 2 · Σ T_p(k)`（`two_mul_T` の総和版）。 -/
theorem W_eq_two_mul (p : ℕ) (hp : 1 ≤ p) : ∀ ks : List ℕ,
    APFree.NonAveraging.W ((aa p : ℕ) : ℤ) ((bb p : ℕ) : ℤ) ks = 2 * (((ks.map (T p)).sum : ℕ) : ℤ) := by
  intro ks
  induction ks with
  | nil => simp [APFree.NonAveraging.W]
  | cons a as ih =>
      have hT := two_mul_T p a hp
      simp only [APFree.NonAveraging.W_cons, ih, List.map_cons, List.sum_cons, Nat.cast_add,
        APFree.NonAveraging.F]
      linarith

/-- ブロック B(p,q,r) を ℤ の部分集合として見たもの。 -/
def BlkZ (p q r : ℕ) : Set ℤ := {x : ℤ | ∃ s ∈ Blk p q r, x = (s : ℤ)}

/-- **B(p,q,r) は 3-AP-free**（Wróblewski 1984 Lemma 1、`APFreeWindowSeparation.IsThreeAPFree` の形）。 -/
theorem Blk_apfree (p q r : ℕ) (hp : 1 ≤ p) : IsThreeAPFree (BlkZ p q r) := by
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩ z ⟨sz, hsz, rfl⟩ hxyz
  have hnat : sx + sz = 2 * sy := by exact_mod_cast hxyz
  obtain ⟨kx, hkxl, hkxb, hkxs, hkxv⟩ := (mem_Blk_iff p q r sx).mp hsx
  obtain ⟨ky, hkyl, hkyb, hkys, hkyv⟩ := (mem_Blk_iff p q r sy).mp hsy
  obtain ⟨kz, hkzl, hkzb, hkzs, hkzv⟩ := (mem_Blk_iff p q r sz).mp hsz
  have hval : APFree.NonAveraging.val (2 * p - 1) kx + APFree.NonAveraging.val (2 * p - 1) kz
      = 2 * APFree.NonAveraging.val (2 * p - 1) ky := by
    rw [val_eq_valL, val_eq_valL, val_eq_valL, ← hkxv, ← hkyv, ← hkzv]
    exact hnat
  -- Sphere の weight は `W = 2·T` の総和なので、渡す r は **2r** である。
  have hd : kx = kz :=
    APFree.NonAveraging.lemma1_nonaveraging (p := p) (q := q) (r := 2 * (r : ℤ))
      (A := ((aa p : ℕ) : ℤ)) (B := ((bb p : ℕ) : ℤ)) (by omega)
      ⟨kx, hkxl, hkxb, by rw [W_eq_two_mul p hp kx, hkxs]⟩
      ⟨kz, hkzl, hkzb, by rw [W_eq_two_mul p hp kz, hkzs]⟩
      ⟨ky, hkyl, hkyb, by rw [W_eq_two_mul p hp ky, hkys]⟩
      hval
  have hxz : sx = sz := by rw [hkxv, hkzv, hd]
  omega

/-! ## 4. 窓 `(p, n, r, a)` の覆う集合（ℤ 側） -/

/-- 窓 `(p,n,r,a)` が覆う集合 `a + B(p,n,r)`（ℤ の部分集合として）。 -/
def winZ (w : ℕ × ℕ × ℕ × ℕ) : Set ℤ :=
  {x : ℤ | ∃ s ∈ Blk w.1 w.2.1 w.2.2.1, x = (w.2.2.2 : ℤ) + (s : ℤ)}

theorem winZ_apfree (w : ℕ × ℕ × ℕ × ℕ) (hp : 1 ≤ w.1) : IsThreeAPFree (winZ w) := by
  rintro x ⟨sx, hsx, rfl⟩ y ⟨sy, hsy, rfl⟩ z ⟨sz, hsz, rfl⟩ hxyz
  have h2 : (sx : ℤ) + (sz : ℤ) = 2 * (sy : ℤ) := by linarith
  have := Blk_apfree w.1 w.2.1 w.2.2.1 hp (sx : ℤ) ⟨sx, hsx, rfl⟩ (sy : ℤ) ⟨sy, hsy, rfl⟩
    (sz : ℤ) ⟨sz, hsz, rfl⟩ h2
  omega

/-- 窓の元は区間 `[a, a + t]` に収まる（`t` はブロックの**真の最大元**）。 -/
theorem winZ_box (w : ℕ × ℕ × ℕ × ℕ) (t : ℕ)
    (ht : IsGreatest (Blk w.1 w.2.1 w.2.2.1) t) :
    ∀ x ∈ winZ w, ((w.2.2.2 : ℕ) : ℤ) ≤ x ∧ x ≤ ((w.2.2.2 : ℕ) : ℤ) + (t : ℤ) := by
  rintro x ⟨s, hs, rfl⟩
  have hle : s ≤ t := ht.2 hs
  omega

/-- 窓の一覧が覆う集合（ℤ 側）。 -/
def unionWZ : List (ℕ × ℕ × ℕ × ℕ) → Set ℤ
  | [] => ∅
  | w :: ws => winZ w ∪ unionWZ ws

theorem mem_unionWZ : ∀ (ws : List (ℕ × ℕ × ℕ × ℕ)) (x : ℤ),
    x ∈ unionWZ ws ↔ ∃ i, i < ws.length ∧ x ∈ winZ (nthW ws i) := by
  intro ws
  induction ws with
  | nil => intro x; simp [unionWZ]
  | cons w ws ih =>
      intro x
      simp only [unionWZ, Set.mem_union, ih, List.length_cons]
      constructor
      · rintro (h | ⟨i, hi, hx⟩)
        · exact ⟨0, by omega, h⟩
        · exact ⟨i + 1, by omega, hx⟩
      · rintro ⟨i, hi, hx⟩
        cases i with
        | zero => exact Or.inl hx
        | succ n => exact Or.inr ⟨n, by omega, hx⟩

theorem unionWZ_append : ∀ (a b : List (ℕ × ℕ × ℕ × ℕ)),
    unionWZ (a ++ b) = unionWZ a ∪ unionWZ b := by
  intro a
  induction a with
  | nil => intro b; simp [unionWZ]
  | cons w a ih => intro b; simp [unionWZ, ih, Set.union_assoc]

/-! ## 5. 一段ぶん（前段までの集合を「頭の窓 [0, z]」に潰す） -/

/-- 窓の区間（右端はブロックの最大元 `t`）。 -/
def winIv (t : ℤ) (w : ℕ × ℕ × ℕ × ℕ) : ℤ × ℤ := ((w.2.2.2 : ℤ), (w.2.2.2 : ℤ) + t)

/-- 一段ぶんの区間の一覧：頭 `[0, z]` と、M 個のブロック窓。 -/
def stepIvs (z t : ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) : List (ℤ × ℤ) :=
  (0, z) :: ws.map (winIv t)

theorem stepIvs_length (z t : ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) :
    (stepIvs z t ws).length = ws.length + 1 := by simp [stepIvs]

theorem nthI_stepIvs_zero (z t : ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) :
    nthI (stepIvs z t ws) 0 = (0, z) := rfl

theorem nthI_stepIvs_succ (z t : ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) (n : ℕ) (hn : n < ws.length) :
    nthI (stepIvs z t ws) (n + 1) = winIv t (nthW ws n) := nthI_map (winIv t) ws n hn

/-- 段の族：0 番が前段までの集合、i+1 番が i 番目の窓。 -/
def stepFam (S : Set ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) : ℕ → Set ℤ
  | 0 => S
  | i + 1 => winZ (nthW ws i)

theorem union_eq_unionIdx (S : Set ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ)) :
    S ∪ unionWZ ws = unionIdx (stepFam S ws) (ws.length + 1) := by
  ext x
  simp only [Set.mem_union, unionIdx, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact ⟨0, by omega, h⟩
    · obtain ⟨i, hi, hx⟩ := (mem_unionWZ ws x).mp h
      exact ⟨i + 1, by omega, hx⟩
  · rintro ⟨i, hi, hx⟩
    cases i with
    | zero => exact Or.inl hx
    | succ n => exact Or.inr ((mem_unionWZ ws x).mpr ⟨n, by omega, hx⟩)

/-- **一段の定理**：前段までの集合 S（3-AP-free・`[0,z]` に収まる）に、
    区間 `[a_j, a_j + t]` に収まる 3-AP-free な窓を M 個足しても 3-AP-free。 -/
theorem step_apfree (S : Set ℤ) (z t : ℤ) (ws : List (ℕ × ℕ × ℕ × ℕ))
    (hS : IsThreeAPFree S) (hSbox : ∀ x ∈ S, (0 : ℤ) ≤ x ∧ x ≤ z)
    (hwbox : ∀ i, i < ws.length → ∀ x ∈ winZ (nthW ws i),
        (((nthW ws i).2.2.2 : ℕ) : ℤ) ≤ x ∧ x ≤ (((nthW ws i).2.2.2 : ℕ) : ℤ) + t)
    (hwfree : ∀ i, i < ws.length → IsThreeAPFree (winZ (nthW ws i)))
    (hsep : sepL (stepIvs z t ws) = true) :
    IsThreeAPFree (S ∪ unionWZ ws) := by
  rw [union_eq_unionIdx, ← stepIvs_length z t ws]
  refine apfree_unionL (stepIvs z t ws) (stepFam S ws) ?_ ?_ hsep
  · intro i hi x hx
    rw [stepIvs_length] at hi
    cases i with
    | zero => exact hSbox x hx
    | succ n =>
        have hn : n < ws.length := by omega
        rw [nthI_stepIvs_succ z t ws n hn]
        exact hwbox n hn x hx
  · intro i hi
    rw [stepIvs_length] at hi
    cases i with
    | zero => exact hS
    | succ n => exact hwfree n (by omega)

end APFree.ChainRecord

/-! ### 公理の確認 -/

#print axioms APFree.ChainRecord.Blk_apfree
#print axioms APFree.ChainRecord.winZ_apfree
#print axioms APFree.ChainRecord.apfree_unionL
#print axioms APFree.ChainRecord.sepL_spec
