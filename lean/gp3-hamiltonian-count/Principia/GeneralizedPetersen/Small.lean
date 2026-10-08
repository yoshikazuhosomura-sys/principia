import Mathlib

/-!
# Principia.GeneralizedPetersen.Small

  `n = 7, 9, 11, 13, 15` での `#HC(GP(n,3))` の核内全列挙（7, 9, 11, 26, 75）と、
  自由作用から従う可除性 `card_dvd_of_perm_free`。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.Small

set_option maxRecDepth 8000

/-! ### 1. 符号化 -/

/-- 隣接判定：N×N ビットの隣接行列 `AMD` の `N*a+b` 番目のビット。
  両端が `N` 未満であることも条件に含める（範囲外で隣の行のビットを拾わないため）。 -/
def adjB (N AMD a b : ℕ) : Bool :=
  decide (a < N) && decide (b < N) && Nat.testBit AMD (N * a + b)

/-- 頂点 `v` の第 `i` 近傍（`NBD` に 5 ビットずつ・昇順に詰めてある）。 -/
def nb (NBD v i : ℕ) : ℕ := (NBD >>> (15 * v + 5 * i)) &&& 31

theorem adjB_lt {N AMD a b : ℕ} (h : adjB N AMD a b = true) : a < N ∧ b < N := by
  rw [adjB, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2⟩

/-! ### 2. 閉路の条件（tailB・cycB） -/

/-- 終端の条件：`v` が 0 に隣接し、かつ `a < v`（向きの正準化）。 -/
def baseB (N AMD a v : ℕ) : Bool := adjB N AMD v 0 && decide (a < v)

/-- しっぽの判定。`tailB N AMD a v l = true` は
  「`v` から `l` の頂点を順に隣接でたどれて、最後の頂点が 0 に隣接し、
  かつ `a <` 最後の頂点」。`a` は閉路の第 2 頂点（向きの正準化に使う）。 -/
def tailB (N AMD a : ℕ) : ℕ → List ℕ → Bool
  | v, [] => baseB N AMD a v
  | v, (u :: l) => adjB N AMD v u && tailB N AMD a u l

/-- 閉路の判定：`0 :: l` を閉路として見たときの、隣接・0 への閉じ・向きの条件。
  （`l` の先頭 `u` を正準化の基準にして `tailB N AMD u 0 l`。） -/
def cycB (N AMD : ℕ) : List ℕ → Bool
  | [] => false
  | (u :: l) => tailB N AMD u 0 (u :: l)

/-- 正準向きハミルトン閉路の表現：`0 :: l` が長さ `N` の閉路で、頂点は全て異なり
  0 を含まない `l` の長さは `N − 1`、そして向きは正準（`cycB`）。 -/
def HamRep (N AMD : ℕ) (l : List ℕ) : Prop :=
  l.length = N - 1 ∧ l.Nodup ∧ 0 ∉ l ∧ cycB N AMD l = true

/-! ### 3. 列挙（ext）と個数（cnt） -/

/-- 枝：頂点 `u` が未訪問なら部分列挙 `L` の各要素の先頭に `u` を付ける。訪問済みなら空。 -/
def brf (u vis : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  if Nat.testBit vis u then [] else L.map (List.cons u)

/-- `brf` の長さに対応するもの。 -/
def cntf (u vis m : ℕ) : ℕ := if Nat.testBit vis u then 0 else m

/-- `ext N AMD NBD a k v vis`：`v` から未訪問（`vis` のビットが 0）の頂点を `k` 個
  たどって最後が 0 に隣接し `a <` 最後の頂点、という道の「残り `k` 頂点」の全リスト。 -/
def ext (N AMD NBD a : ℕ) : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, v, _ => if baseB N AMD a v then [[]] else []
  | (k + 1), v, vis =>
      brf (nb NBD v 0) vis (ext N AMD NBD a k (nb NBD v 0) (vis ||| 2 ^ nb NBD v 0)) ++
      brf (nb NBD v 1) vis (ext N AMD NBD a k (nb NBD v 1) (vis ||| 2 ^ nb NBD v 1)) ++
      brf (nb NBD v 2) vis (ext N AMD NBD a k (nb NBD v 2) (vis ||| 2 ^ nb NBD v 2))

/-- `ext` の要素数。核で評価するのはこちら（List を作らないので速い）。 -/
def cnt (N AMD NBD a : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, v, _ => if baseB N AMD a v then 1 else 0
  | (k + 1), v, vis =>
      cntf (nb NBD v 0) vis (cnt N AMD NBD a k (nb NBD v 0) (vis ||| 2 ^ nb NBD v 0)) +
      cntf (nb NBD v 1) vis (cnt N AMD NBD a k (nb NBD v 1) (vis ||| 2 ^ nb NBD v 1)) +
      cntf (nb NBD v 2) vis (cnt N AMD NBD a k (nb NBD v 2) (vis ||| 2 ^ nb NBD v 2))

/-- 第 2 頂点を `a` に固定した枝の列挙（頂点 0 と `a` を訪問済みにして始める）。 -/
def top (N AMD NBD a k : ℕ) : List (List ℕ) :=
  (ext N AMD NBD a k a (1 ||| 2 ^ a)).map (List.cons a)

/-- `top` の要素数。 -/
def topc (N AMD NBD a k : ℕ) : ℕ := cnt N AMD NBD a k a (1 ||| 2 ^ a)

/-- 頂点 0 の 3 本の辺で分けた全列挙。 -/
def enumAll (N AMD NBD k : ℕ) : List (List ℕ) :=
  top N AMD NBD (nb NBD 0 0) k ++ top N AMD NBD (nb NBD 0 1) k ++ top N AMD NBD (nb NBD 0 2) k

/-- 全個数。 -/
def numAll (N AMD NBD k : ℕ) : ℕ :=
  topc N AMD NBD (nb NBD 0 0) k + topc N AMD NBD (nb NBD 0 1) k + topc N AMD NBD (nb NBD 0 2) k

/-! ### 4. brf の基本性質 -/

theorem brf_true {u vis : ℕ} {L : List (List ℕ)} (hb : Nat.testBit vis u = true) :
    brf u vis L = [] := by simp [brf, hb]

theorem brf_false {u vis : ℕ} {L : List (List ℕ)} (hb : Nat.testBit vis u = false) :
    brf u vis L = L.map (List.cons u) := by simp [brf, hb]

theorem length_brf (u vis : ℕ) (L : List (List ℕ)) :
    (brf u vis L).length = cntf u vis L.length := by
  by_cases hb : Nat.testBit vis u = true
  · rw [brf_true hb]; simp [cntf, hb]
  · rw [Bool.not_eq_true] at hb
    rw [brf_false hb]; simp [cntf, hb]

theorem mem_brf {u vis : ℕ} {L : List (List ℕ)} {l : List ℕ} :
    l ∈ brf u vis L ↔ (Nat.testBit vis u = false ∧ ∃ l', l' ∈ L ∧ l = u :: l') := by
  by_cases hb : Nat.testBit vis u = true
  · rw [brf_true hb]; simp [hb]
  · rw [Bool.not_eq_true] at hb
    rw [brf_false hb]
    constructor
    · intro h
      obtain ⟨l', hl', he⟩ := List.mem_map.mp h
      exact ⟨hb, l', hl', he.symm⟩
    · rintro ⟨-, l', hl', rfl⟩
      exact List.mem_map_of_mem hl'

theorem head_of_mem_brf {u vis : ℕ} {L : List (List ℕ)} {l : List ℕ}
    (h : l ∈ brf u vis L) : l.head? = some u := by
  obtain ⟨-, l', -, rfl⟩ := mem_brf.mp h
  rfl

theorem nodup_brf {u vis : ℕ} {L : List (List ℕ)} (h : L.Nodup) : (brf u vis L).Nodup := by
  by_cases hb : Nat.testBit vis u = true
  · rw [brf_true hb]; exact List.nodup_nil
  · rw [Bool.not_eq_true] at hb
    rw [brf_false hb]
    exact h.map (fun x y hxy => by simpa using hxy)

/-! ### 5. cnt = (ext …).length -/

theorem cnt_eq_length (N AMD NBD a : ℕ) : ∀ (k v vis : ℕ),
    cnt N AMD NBD a k v vis = (ext N AMD NBD a k v vis).length := by
  intro k
  induction k with
  | zero =>
      intro v vis
      rw [cnt, ext]
      by_cases hb : baseB N AMD a v = true
      · rw [if_pos hb, if_pos hb]; rfl
      · rw [if_neg hb, if_neg hb]; rfl
  | succ k ih =>
      intro v vis
      rw [cnt, ext, List.length_append, List.length_append, length_brf, length_brf, length_brf,
        ih, ih, ih]

/-! ### 6. ext の membership（健全性と完全性を同時に） -/

theorem mem_ext (N AMD NBD a : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hS : ∀ v < N, ∀ u, adjB N AMD v u = true →
      u = nb NBD v 0 ∨ u = nb NBD v 1 ∨ u = nb NBD v 2) :
    ∀ (k v vis : ℕ), v < N → ∀ l : List ℕ,
      (l ∈ ext N AMD NBD a k v vis ↔
        (l.length = k ∧ tailB N AMD a v l = true ∧ l.Nodup ∧
          ∀ x ∈ l, Nat.testBit vis x = false)) := by
  intro k
  induction k with
  | zero =>
      intro v vis hv l
      rw [ext]
      cases l with
      | nil =>
          by_cases hb : baseB N AMD a v = true
          · rw [if_pos hb]; simp [tailB, hb]
          · rw [if_neg hb]
            rw [Bool.not_eq_true] at hb
            simp [tailB, hb]
      | cons u l' =>
          by_cases hb : baseB N AMD a v = true
          · rw [if_pos hb]; simp
          · rw [if_neg hb]; simp
  | succ k ih =>
      intro v vis hv l
      have hn := hA v hv
      -- 一つの枝についての言い換え
      have key : ∀ u : ℕ, adjB N AMD v u = true →
          (l ∈ brf u vis (ext N AMD NBD a k u (vis ||| 2 ^ u)) ↔
            (l.length = k + 1 ∧ tailB N AMD a v l = true ∧ l.Nodup ∧
              (∀ x ∈ l, Nat.testBit vis x = false) ∧ l.head? = some u)) := by
        intro u hu
        have huN : u < N := (adjB_lt hu).2
        constructor
        · intro h
          obtain ⟨hbit, l', hl', rfl⟩ := mem_brf.mp h
          obtain ⟨hlen, htl, hnd, hvis⟩ := (ih u (vis ||| 2 ^ u) huN l').mp hl'
          have hunotin : u ∉ l' := by
            intro hmem
            have := hvis u hmem
            rw [Nat.testBit_or, Nat.testBit_two_pow_self] at this
            simp at this
          refine ⟨by simp [hlen], ?_, ?_, ?_, rfl⟩
          · rw [tailB, hu, htl]; rfl
          · exact List.nodup_cons.mpr ⟨hunotin, hnd⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hbit
            · have := hvis x hx'
              rw [Nat.testBit_or] at this
              simpa using (Bool.or_eq_false_iff.mp this).1
        · rintro ⟨hlen, htl, hnd, hvis, hhd⟩
          cases l with
          | nil => simp at hhd
          | cons w l' =>
              have hwu : w = u := by simpa using hhd
              subst hwu
              rw [tailB, Bool.and_eq_true] at htl
              obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
              refine mem_brf.mpr ⟨hvis w List.mem_cons_self, l', ?_, rfl⟩
              refine (ih w (vis ||| 2 ^ w) huN l').mpr ⟨by simpa using hlen, htl.2, hnd', ?_⟩
              intro x hx
              have h1 : Nat.testBit vis x = false := hvis x (List.mem_cons_of_mem _ hx)
              have h2 : Nat.testBit (2 ^ w) x = false :=
                Nat.testBit_two_pow_of_ne (fun h => hnotin (h ▸ hx))
              rw [Nat.testBit_or, h1, h2]
              rfl
      rw [ext]
      constructor
      · intro h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨h1, h2, h3, h4, -⟩ := (key _ hn.1).mp h
            exact ⟨h1, h2, h3, h4⟩
          · obtain ⟨h1, h2, h3, h4, -⟩ := (key _ hn.2.1).mp h
            exact ⟨h1, h2, h3, h4⟩
        · obtain ⟨h1, h2, h3, h4, -⟩ := (key _ hn.2.2).mp h
          exact ⟨h1, h2, h3, h4⟩
      · rintro ⟨hlen, htl, hnd, hvis⟩
        cases l with
        | nil => simp at hlen
        | cons u l' =>
            have hu : adjB N AMD v u = true := by
              rw [tailB, Bool.and_eq_true] at htl; exact htl.1
            have hhd : (u :: l').head? = some u := rfl
            rcases hS v hv u hu with he | he | he
            · subst he
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                ((key _ hn.1).mpr ⟨hlen, htl, hnd, hvis, hhd⟩))))
            · subst he
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
                ((key _ hn.2.1).mpr ⟨hlen, htl, hnd, hvis, hhd⟩))))
            · subst he
              exact List.mem_append.mpr (Or.inr
                ((key _ hn.2.2).mpr ⟨hlen, htl, hnd, hvis, hhd⟩))

/-! ### 7. ext は重複なし -/

theorem nodup_ext (N AMD NBD a : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hD : ∀ v < N, nb NBD v 0 ≠ nb NBD v 1 ∧ nb NBD v 0 ≠ nb NBD v 2 ∧
      nb NBD v 1 ≠ nb NBD v 2) :
    ∀ (k v vis : ℕ), v < N → (ext N AMD NBD a k v vis).Nodup := by
  intro k
  induction k with
  | zero =>
      intro v vis _
      rw [ext]
      by_cases hb : baseB N AMD a v = true
      · rw [if_pos hb]; simp
      · rw [if_neg hb]; simp
  | succ k ih =>
      intro v vis hv
      have hn := hA v hv
      have hd := hD v hv
      have h0 : nb NBD v 0 < N := (adjB_lt hn.1).2
      have h1 : nb NBD v 1 < N := (adjB_lt hn.2.1).2
      have h2 : nb NBD v 2 < N := (adjB_lt hn.2.2).2
      rw [ext]
      have dis : ∀ i j : ℕ, nb NBD v i ≠ nb NBD v j →
          ∀ (L M : List (List ℕ)),
            List.Disjoint (brf (nb NBD v i) vis L) (brf (nb NBD v j) vis M) := by
        intro i j hij L M x hx1 hx2
        have e1 := head_of_mem_brf hx1
        have e2 := head_of_mem_brf hx2
        rw [e1] at e2
        exact hij (by simpa using e2)
      refine List.Nodup.append (List.Nodup.append (nodup_brf (ih _ _ h0))
        (nodup_brf (ih _ _ h1)) (dis 0 1 hd.1 _ _)) (nodup_brf (ih _ _ h2)) ?_
      intro x hx1 hx2
      rcases List.mem_append.mp hx1 with hx | hx
      · exact dis 0 2 hd.2.1 _ _ hx hx2
      · exact dis 1 2 hd.2.2 _ _ hx hx2

/-! ### 8. 閉路条件の読み替え（List.IsChain による言い換え） -/

theorem tailB_lt {N AMD a : ℕ} : ∀ (l : List ℕ) (v : ℕ),
    tailB N AMD a v l = true → ∀ x ∈ l, x < N := by
  intro l
  induction l with
  | nil => intro v _ x hx; simp at hx
  | cons u l ih =>
      intro v h x hx
      rw [tailB, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact (adjB_lt h.1).2
      · exact ih u h.2 x hx'

/-- `tailB` は「`v` から `l` を通って 0 に戻る道（隣接の鎖）」＋「向きの正準性」に等しい。 -/
theorem tailB_iff (N AMD a : ℕ) : ∀ (l : List ℕ) (v : ℕ),
    (tailB N AMD a v l = true ↔
      (List.IsChain (fun x y => adjB N AMD x y = true) (v :: (l ++ [0])) ∧
        ∃ z, (v :: l).getLast? = some z ∧ a < z)) := by
  intro l
  induction l with
  | nil =>
      intro v
      rw [tailB, baseB, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, v, rfl, h2⟩
        simp only [List.nil_append]
        exact List.isChain_cons_cons.mpr ⟨h1, List.IsChain.singleton 0⟩
      · rintro ⟨hc, z, hz, hlt⟩
        simp only [List.nil_append] at hc
        refine ⟨(List.isChain_cons_cons.mp hc).1, ?_⟩
        have hzv : v = z := by simpa using hz
        omega
  | cons u l ih =>
      intro v
      rw [tailB, Bool.and_eq_true, ih u]
      simp only [List.cons_append]
      constructor
      · rintro ⟨h1, hc, z, hz, hlt⟩
        refine ⟨List.isChain_cons_cons.mpr ⟨h1, hc⟩, z, ?_, hlt⟩
        rw [List.getLast?_cons_cons]; exact hz
      · rintro ⟨hc, z, hz, hlt⟩
        rw [List.getLast?_cons_cons] at hz
        obtain ⟨h1, hc'⟩ := List.isChain_cons_cons.mp hc
        exact ⟨h1, hc', z, hz, hlt⟩

/-- `cycB N AMD l = true` は「`0 :: l ++ [0]` が隣接の鎖（＝閉じた歩道）で、
  `l` の先頭が `l` の末尾より小さい（向きの正準化）」に等しい。 -/
theorem cycB_iff (N AMD : ℕ) (l : List ℕ) (hl : l ≠ []) :
    cycB N AMD l = true ↔
      (List.IsChain (fun x y => adjB N AMD x y = true) (0 :: (l ++ [0])) ∧
        ∃ b c, l.head? = some b ∧ l.getLast? = some c ∧ b < c) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons u l =>
      rw [cycB, tailB_iff]
      constructor
      · rintro ⟨hc, z, hz, hlt⟩
        exact ⟨hc, u, z, rfl, by simpa using hz, hlt⟩
      · rintro ⟨hc, b, c, hb, hz, hlt⟩
        have hbu : u = b := by simpa using hb
        subst u
        exact ⟨hc, c, by simpa using hz, hlt⟩

/-- `HamRep` の読みやすい形：`0 :: l` は長さ `N` の閉路（頂点は全て異なる・
  連続する頂点は隣接・最後の頂点は 0 に隣接）で、向きは正準。 -/
theorem hamRep_iff (N AMD : ℕ) (hN : 2 ≤ N) (l : List ℕ) :
    HamRep N AMD l ↔
      (l.length = N - 1 ∧ (0 :: l).Nodup ∧
        List.IsChain (fun x y => adjB N AMD x y = true) (0 :: (l ++ [0])) ∧
        ∃ b c, l.head? = some b ∧ l.getLast? = some c ∧ b < c) := by
  simp only [HamRep]
  constructor
  · rintro ⟨hlen, hnd, h0, hcyc⟩
    have hl : l ≠ [] := by
      intro h; subst h; rw [List.length_nil] at hlen; omega
    obtain ⟨hc, hbc⟩ := (cycB_iff N AMD l hl).mp hcyc
    exact ⟨hlen, List.nodup_cons.mpr ⟨h0, hnd⟩, hc, hbc⟩
  · rintro ⟨hlen, hnd0, hc, hbc⟩
    obtain ⟨h0, hnd⟩ := List.nodup_cons.mp hnd0
    have hl : l ≠ [] := by
      intro h; subst h; rw [List.length_nil] at hlen; omega
    exact ⟨hlen, hnd, h0, (cycB_iff N AMD l hl).mpr ⟨hc, hbc⟩⟩

/-- `HamRep` なら `0 :: l` は `N` 未満の全頂点を通る（ハミルトンであること）。 -/
theorem hamRep_covers {N AMD : ℕ} (hN : 0 < N) {l : List ℕ} (h : HamRep N AMD l) :
    ∀ v < N, v ∈ (0 :: l) := by
  obtain ⟨hlen, hnd, h0, hcyc⟩ := h
  have hlt : ∀ x ∈ l, x < N := by
    cases l with
    | nil => intro x hx; simp at hx
    | cons u t =>
        rw [cycB] at hcyc
        exact tailB_lt (u :: t) 0 hcyc
  have hnd0 : (0 :: l).Nodup := List.nodup_cons.mpr ⟨h0, hnd⟩
  have hsub : (0 :: l).toFinset ⊆ Finset.range N := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · simpa using hN
    · simpa using hlt x hx'
  have hcard : (0 :: l).toFinset.card = N := by
    rw [List.toFinset_card_of_nodup hnd0, List.length_cons, hlen]
    omega
  have heq : (0 :: l).toFinset = Finset.range N :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, hcard])
  intro v hv
  rw [← List.mem_toFinset, heq, Finset.mem_range]
  exact hv

/-! ### 9. 頂点 0 を固定した枝（top）と全列挙（enumAll） -/

theorem testBit_one_or_two_pow (a x : ℕ) :
    Nat.testBit (1 ||| 2 ^ a) x = false ↔ (x ≠ 0 ∧ x ≠ a) := by
  rw [Nat.testBit_or, Bool.or_eq_false_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro hx; subst x; exact absurd h1 (by decide)
    · intro hx; subst x; rw [Nat.testBit_two_pow_self] at h2; exact absurd h2 (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, Nat.testBit_two_pow_of_ne (Ne.symm h2)⟩
    have e : (1 : ℕ) = 2 ^ 0 := by norm_num
    rw [e]
    exact Nat.testBit_two_pow_of_ne (Ne.symm h1)

theorem head_of_mem_top {N AMD NBD a k : ℕ} {l : List ℕ} (h : l ∈ top N AMD NBD a k) :
    l.head? = some a := by
  obtain ⟨l', -, rfl⟩ := List.mem_map.mp h
  rfl

theorem mem_top (N AMD NBD : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hS : ∀ v < N, ∀ u, adjB N AMD v u = true →
      u = nb NBD v 0 ∨ u = nb NBD v 1 ∨ u = nb NBD v 2)
    (hI : ∀ v < N, adjB N AMD v v = false)
    {a k : ℕ} (ha : adjB N AMD 0 a = true) {l : List ℕ} :
    l ∈ top N AMD NBD a k ↔
      (l.length = k + 1 ∧ l.Nodup ∧ 0 ∉ l ∧ cycB N AMD l = true ∧ l.head? = some a) := by
  have haN : a < N := (adjB_lt ha).2
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, hI 0 (by omega)] at ha
    exact absurd ha (by decide)
  rw [top]
  constructor
  · intro h
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
    obtain ⟨hlen, htl, hnd, hvis⟩ :=
      (mem_ext N AMD NBD a hA hS k a (1 ||| 2 ^ a) haN l').mp hl'
    have hnot : ∀ x ∈ l', x ≠ 0 ∧ x ≠ a := fun x hx => (testBit_one_or_two_pow a x).mp (hvis x hx)
    refine ⟨by simp [hlen], ?_, ?_, ?_, rfl⟩
    · exact List.nodup_cons.mpr ⟨fun hm => (hnot a hm).2 rfl, hnd⟩
    · intro hm
      rcases List.mem_cons.mp hm with hz | hz
      · exact ha0 hz.symm
      · exact (hnot 0 hz).1 rfl
    · simp [cycB, tailB, ha, htl]
  · rintro ⟨hlen, hnd, h0, hcyc, hhd⟩
    cases l with
    | nil => simp at hhd
    | cons u l' =>
        have hu : u = a := by simpa using hhd
        subst u
        simp only [cycB, tailB, Bool.and_eq_true] at hcyc
        obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
        refine List.mem_map_of_mem ?_
        refine (mem_ext N AMD NBD a hA hS k a (1 ||| 2 ^ a) haN l').mpr
          ⟨by simpa using hlen, hcyc.2, hnd', ?_⟩
        intro x hx
        refine (testBit_one_or_two_pow a x).mpr ⟨?_, ?_⟩
        · intro hx0; subst x; exact h0 (List.mem_cons_of_mem _ hx)
        · intro hxa; subst x; exact hnotin hx

theorem nodup_top (N AMD NBD : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hD : ∀ v < N, nb NBD v 0 ≠ nb NBD v 1 ∧ nb NBD v 0 ≠ nb NBD v 2 ∧
      nb NBD v 1 ≠ nb NBD v 2)
    (a k : ℕ) (haN : a < N) : (top N AMD NBD a k).Nodup :=
  (nodup_ext N AMD NBD a hA hD k a (1 ||| 2 ^ a) haN).map (fun x y hxy => by simpa using hxy)

theorem mem_enumAll (N AMD NBD : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hS : ∀ v < N, ∀ u, adjB N AMD v u = true →
      u = nb NBD v 0 ∨ u = nb NBD v 1 ∨ u = nb NBD v 2)
    (hI : ∀ v < N, adjB N AMD v v = false)
    (hN : 0 < N) (k : ℕ) {l : List ℕ} :
    l ∈ enumAll N AMD NBD k ↔
      (l.length = k + 1 ∧ l.Nodup ∧ 0 ∉ l ∧ cycB N AMD l = true) := by
  have h0 := hA 0 hN
  rw [enumAll]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨h1, h2, h3, h4, -⟩ := (mem_top N AMD NBD hA hS hI h0.1).mp h
        exact ⟨h1, h2, h3, h4⟩
      · obtain ⟨h1, h2, h3, h4, -⟩ := (mem_top N AMD NBD hA hS hI h0.2.1).mp h
        exact ⟨h1, h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := (mem_top N AMD NBD hA hS hI h0.2.2).mp h
      exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨hlen, hnd, hz, hcyc⟩
    cases l with
    | nil => simp at hlen
    | cons u l' =>
        have hu : adjB N AMD 0 u = true := by
          simp only [cycB, tailB, Bool.and_eq_true] at hcyc
          exact hcyc.1
        have hhd : (u :: l').head? = some u := rfl
        rcases hS 0 hN u hu with he | he | he
        · subst u
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
            ((mem_top N AMD NBD hA hS hI h0.1).mpr ⟨hlen, hnd, hz, hcyc, hhd⟩))))
        · subst u
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
            ((mem_top N AMD NBD hA hS hI h0.2.1).mpr ⟨hlen, hnd, hz, hcyc, hhd⟩))))
        · subst u
          exact List.mem_append.mpr (Or.inr
            ((mem_top N AMD NBD hA hS hI h0.2.2).mpr ⟨hlen, hnd, hz, hcyc, hhd⟩))

theorem nodup_enumAll (N AMD NBD : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hD : ∀ v < N, nb NBD v 0 ≠ nb NBD v 1 ∧ nb NBD v 0 ≠ nb NBD v 2 ∧
      nb NBD v 1 ≠ nb NBD v 2)
    (hN : 0 < N) (k : ℕ) : (enumAll N AMD NBD k).Nodup := by
  have h0 := hA 0 hN
  have hd := hD 0 hN
  have b0 : nb NBD 0 0 < N := (adjB_lt h0.1).2
  have b1 : nb NBD 0 1 < N := (adjB_lt h0.2.1).2
  have b2 : nb NBD 0 2 < N := (adjB_lt h0.2.2).2
  have dis : ∀ i j : ℕ, nb NBD 0 i ≠ nb NBD 0 j →
      List.Disjoint (top N AMD NBD (nb NBD 0 i) k) (top N AMD NBD (nb NBD 0 j) k) := by
    intro i j hij x hx1 hx2
    have e1 := head_of_mem_top hx1
    have e2 := head_of_mem_top hx2
    rw [e1] at e2
    exact hij (by simpa using e2)
  rw [enumAll]
  refine List.Nodup.append (List.Nodup.append (nodup_top N AMD NBD hA hD _ k b0)
    (nodup_top N AMD NBD hA hD _ k b1) (dis 0 1 hd.1)) (nodup_top N AMD NBD hA hD _ k b2) ?_
  intro x hx1 hx2
  rcases List.mem_append.mp hx1 with hx | hx
  · exact dis 0 2 hd.2.1 hx hx2
  · exact dis 1 2 hd.2.2 hx hx2

theorem length_enumAll (N AMD NBD k : ℕ) :
    (enumAll N AMD NBD k).length = numAll N AMD NBD k := by
  simp only [enumAll, numAll, top, topc, List.length_append, List.length_map, cnt_eq_length]

/-! ### 10. 一般部の主結果 -/

/-- 核で得た `numAll` の値は、正準向きハミルトン閉路の表現（`HamRep`）の **個数** である。
  （重複なしの列挙 `enumAll` の要素がちょうど `HamRep` を満たすもの全部であることと、
  その長さが `numAll` であることから。） -/
theorem card_hamRep (N AMD NBD : ℕ)
    (hA : ∀ v < N, adjB N AMD v (nb NBD v 0) = true ∧ adjB N AMD v (nb NBD v 1) = true ∧
      adjB N AMD v (nb NBD v 2) = true)
    (hS : ∀ v < N, ∀ u, adjB N AMD v u = true →
      u = nb NBD v 0 ∨ u = nb NBD v 1 ∨ u = nb NBD v 2)
    (hD : ∀ v < N, nb NBD v 0 ≠ nb NBD v 1 ∧ nb NBD v 0 ≠ nb NBD v 2 ∧
      nb NBD v 1 ≠ nb NBD v 2)
    (hI : ∀ v < N, adjB N AMD v v = false)
    (hN : 0 < N) (k : ℕ) (hk : k + 1 = N - 1) :
    ∃ S : Finset (List ℕ), (∀ l : List ℕ, l ∈ S ↔ HamRep N AMD l) ∧
      S.card = numAll N AMD NBD k := by
  refine ⟨(enumAll N AMD NBD k).toFinset, ?_, ?_⟩
  · intro l
    rw [List.mem_toFinset, mem_enumAll N AMD NBD hA hS hI hN k]
    simp only [HamRep, hk]
  · rw [List.toFinset_card_of_nodup (nodup_enumAll N AMD NBD hA hD hN k), length_enumAll]


end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### GP(7,3) の符号化（14 頂点・21 辺・三価） -/

/-- 隣接行列（14×14 ビット）。 -/
def AMD7 : ℕ := 9808270786223007879324673895102045082814747193431449223362

/-- 近傍表（5 ビット × 3 × 14、昇順）。 -/
def NBD7 : ℕ := 528998441298553472624279186186603447260259504256310854245424321

theorem hA7 : ∀ v < 14, adjB 14 AMD7 v (nb NBD7 v 0) = true ∧
    adjB 14 AMD7 v (nb NBD7 v 1) = true ∧ adjB 14 AMD7 v (nb NBD7 v 2) = true := by
  decide

theorem hSb7 : ∀ v < 14, ∀ u < 14, adjB 14 AMD7 v u = true →
    u = nb NBD7 v 0 ∨ u = nb NBD7 v 1 ∨ u = nb NBD7 v 2 := by
  decide

theorem hS7 : ∀ v < 14, ∀ u, adjB 14 AMD7 v u = true →
    u = nb NBD7 v 0 ∨ u = nb NBD7 v 1 ∨ u = nb NBD7 v 2 :=
  fun v hv u hu => hSb7 v hv u (adjB_lt hu).2 hu

theorem hD7 : ∀ v < 14, nb NBD7 v 0 ≠ nb NBD7 v 1 ∧ nb NBD7 v 0 ≠ nb NBD7 v 2 ∧
    nb NBD7 v 1 ≠ nb NBD7 v 2 := by
  decide

theorem hI7 : ∀ v < 14, adjB 14 AMD7 v v = false := by decide

/-- **監査**：ビット符号化されたグラフは GP(7,3) そのものである。
  外輪 O_j–O_(j+1)（頂点 j, j < 7）・スポーク O_j–I_j（I_j = 7+j）・
  内輪 I_x–I_(x+3)（歩幅 3）。 -/
theorem adjB7_iff_GP : ∀ a < 14, ∀ b < 14,
    (adjB 14 AMD7 a b = true ↔
      ((a < 7 ∧ b < 7 ∧ (b = (a + 1) % 7 ∨ a = (b + 1) % 7)) ∨
       (a < 7 ∧ b = a + 7) ∨ (b < 7 ∧ a = b + 7) ∨
       (7 ≤ a ∧ 7 ≤ b ∧ (b - 7 = (a - 7 + 3) % 7 ∨ a - 7 = (b - 7 + 3) % 7)))) := by
  decide

/-! ### Mathlib の SimpleGraph として -/

theorem adjB7_symm : ∀ a b : Fin 14, adjB 14 AMD7 a.val b.val = true →
    adjB 14 AMD7 b.val a.val = true := by decide

theorem adjB7_irrefl : ∀ a : Fin 14, ¬ (adjB 14 AMD7 a.val a.val = true) := by decide

/-- GP(7,3)。 -/
def GP7 : SimpleGraph (Fin 14) where
  Adj a b := adjB 14 AMD7 a.val b.val = true
  symm := ⟨fun a b h => adjB7_symm a b h⟩
  loopless := ⟨fun a h => adjB7_irrefl a h⟩

instance : DecidableRel GP7.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB 14 AMD7 a.val b.val = true))

theorem GP7_degree : ∀ v : Fin 14, GP7.degree v = 3 := by decide

theorem GP7_adj_iff (a b : Fin 14) : GP7.Adj a b ↔ adjB 14 AMD7 a.val b.val = true :=
  Iff.rfl

/-- 頂点 0 の第 0 近傍（頂点 1）から始まる枝。探索木 460 節点。 -/
theorem t70 : topc 14 AMD7 NBD7 (nb NBD7 0 0) 12 = 4 := by
  decide +kernel

/-- 頂点 0 の第 1 近傍（頂点 6）から始まる枝。探索木 460 節点。 -/
theorem t71 : topc 14 AMD7 NBD7 (nb NBD7 0 1) 12 = 3 := by
  decide +kernel

/-- 頂点 0 の第 2 近傍（頂点 7）から始まる枝。探索木 455 節点。 -/
theorem t72 : topc 14 AMD7 NBD7 (nb NBD7 0 2) 12 = 0 := by
  decide +kernel

/-! ### 個数（核で評価） -/

theorem num7 : numAll 14 AMD7 NBD7 12 = 7 := by
  rw [numAll, t70, t71, t72]

/-- **主定理**：GP(7,3) の正準向きハミルトン閉路の表現はちょうど 7 個あり、
  7 はその個数を割る。`HamRep 14 AMD7 l` は「`0 :: l` が長さ 14 の閉路で
  頂点が全て異なり、向きが正準（`l` の先頭 < `l` の末尾）」という条件
  （`hamRep_iff` / `hamRep_covers` を見よ）。向きの正準化により、これは
  **無向のハミルトン閉路の個数 #HC(GP(7,3)) そのもの** である。 -/
theorem GP7_hc_card : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 14 AMD7 l) ∧ S.card = 7 ∧ 7 ∣ S.card := by
  obtain ⟨S, hmem, hc⟩ :=
    card_hamRep 14 AMD7 NBD7 hA7 hS7 hD7 hI7 (by norm_num) 12 (by norm_num)
  have hcard : S.card = 7 := by rw [hc, num7]
  exact ⟨S, hmem, hcard, by omega⟩

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### GP(9,3) の符号化（18 頂点・27 辺・三価） -/

/-- 隣接行列（18×18 ビット）。 -/
def AMD9 : ℕ := 2436364859844473466222590421487650943766032667233605545221466155426149141256403735451369433465602

/-- 近傍表（5 ビット × 3 × 18、昇順）。 -/
def NBD9 : ℕ := 850864370421365247515956807738434279429449423267140125598552281844898756030375169

theorem hA9 : ∀ v < 18, adjB 18 AMD9 v (nb NBD9 v 0) = true ∧
    adjB 18 AMD9 v (nb NBD9 v 1) = true ∧ adjB 18 AMD9 v (nb NBD9 v 2) = true := by
  decide

theorem hSb9 : ∀ v < 18, ∀ u < 18, adjB 18 AMD9 v u = true →
    u = nb NBD9 v 0 ∨ u = nb NBD9 v 1 ∨ u = nb NBD9 v 2 := by
  decide

theorem hS9 : ∀ v < 18, ∀ u, adjB 18 AMD9 v u = true →
    u = nb NBD9 v 0 ∨ u = nb NBD9 v 1 ∨ u = nb NBD9 v 2 :=
  fun v hv u hu => hSb9 v hv u (adjB_lt hu).2 hu

theorem hD9 : ∀ v < 18, nb NBD9 v 0 ≠ nb NBD9 v 1 ∧ nb NBD9 v 0 ≠ nb NBD9 v 2 ∧
    nb NBD9 v 1 ≠ nb NBD9 v 2 := by
  decide

theorem hI9 : ∀ v < 18, adjB 18 AMD9 v v = false := by decide

/-- **監査**：ビット符号化されたグラフは GP(9,3) そのものである。
  外輪 O_j–O_(j+1)（頂点 j, j < 9）・スポーク O_j–I_j（I_j = 9+j）・
  内輪 I_x–I_(x+3)（歩幅 3）。 -/
theorem adjB9_iff_GP : ∀ a < 18, ∀ b < 18,
    (adjB 18 AMD9 a b = true ↔
      ((a < 9 ∧ b < 9 ∧ (b = (a + 1) % 9 ∨ a = (b + 1) % 9)) ∨
       (a < 9 ∧ b = a + 9) ∨ (b < 9 ∧ a = b + 9) ∨
       (9 ≤ a ∧ 9 ≤ b ∧ (b - 9 = (a - 9 + 3) % 9 ∨ a - 9 = (b - 9 + 3) % 9)))) := by
  decide

/-! ### Mathlib の SimpleGraph として -/

theorem adjB9_symm : ∀ a b : Fin 18, adjB 18 AMD9 a.val b.val = true →
    adjB 18 AMD9 b.val a.val = true := by decide

theorem adjB9_irrefl : ∀ a : Fin 18, ¬ (adjB 18 AMD9 a.val a.val = true) := by decide

/-- GP(9,3)。 -/
def GP9 : SimpleGraph (Fin 18) where
  Adj a b := adjB 18 AMD9 a.val b.val = true
  symm := ⟨fun a b h => adjB9_symm a b h⟩
  loopless := ⟨fun a h => adjB9_irrefl a h⟩

instance : DecidableRel GP9.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB 18 AMD9 a.val b.val = true))

theorem GP9_degree : ∀ v : Fin 18, GP9.degree v = 3 := by decide

theorem GP9_adj_iff (a b : Fin 18) : GP9.Adj a b ↔ adjB 18 AMD9 a.val b.val = true :=
  Iff.rfl

/-- 頂点 0 の第 0 近傍（頂点 1）から始まる枝。探索木 1546 節点。 -/
theorem t90 : topc 18 AMD9 NBD9 (nb NBD9 0 0) 16 = 6 := by
  decide +kernel

/-- 頂点 0 の第 1 近傍（頂点 8）から始まる枝。探索木 1546 節点。 -/
theorem t91 : topc 18 AMD9 NBD9 (nb NBD9 0 1) 16 = 3 := by
  decide +kernel

/-- 頂点 0 の第 2 近傍（頂点 9）から始まる枝。探索木 1863 節点。 -/
theorem t92 : topc 18 AMD9 NBD9 (nb NBD9 0 2) 16 = 0 := by
  decide +kernel

/-! ### 個数（核で評価） -/

theorem num9 : numAll 18 AMD9 NBD9 16 = 9 := by
  rw [numAll, t90, t91, t92]

/-- **主定理**：GP(9,3) の正準向きハミルトン閉路の表現はちょうど 9 個あり、
  9 はその個数を割る。`HamRep 18 AMD9 l` は「`0 :: l` が長さ 18 の閉路で
  頂点が全て異なり、向きが正準（`l` の先頭 < `l` の末尾）」という条件
  （`hamRep_iff` / `hamRep_covers` を見よ）。向きの正準化により、これは
  **無向のハミルトン閉路の個数 #HC(GP(9,3)) そのもの** である。 -/
theorem GP9_hc_card : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 18 AMD9 l) ∧ S.card = 9 ∧ 9 ∣ S.card := by
  obtain ⟨S, hmem, hc⟩ :=
    card_hamRep 18 AMD9 NBD9 hA9 hS9 hD9 hI9 (by norm_num) 16 (by norm_num)
  have hcard : S.card = 9 := by rw [hc, num9]
  exact ⟨S, hmem, hcard, by omega⟩

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### GP(11,3) の符号化（22 頂点・33 辺・三価） -/

/-- 隣接行列（22×22 ビット）。 -/
def AMD11 : ℕ := 3231497908012608632623337177291320178436368977741426990745713949138960213930250070036541917915243426476167599491274602087466683057310615038069762

/-- 近傍表（5 ビット × 3 × 22、昇順）。 -/
def NBD11 : ℕ := 1258800122424495308088695356101166564383612787840798911283051503978904715963597113304624114635386177

theorem hA11 : ∀ v < 22, adjB 22 AMD11 v (nb NBD11 v 0) = true ∧
    adjB 22 AMD11 v (nb NBD11 v 1) = true ∧ adjB 22 AMD11 v (nb NBD11 v 2) = true := by
  decide

theorem hSb11 : ∀ v < 22, ∀ u < 22, adjB 22 AMD11 v u = true →
    u = nb NBD11 v 0 ∨ u = nb NBD11 v 1 ∨ u = nb NBD11 v 2 := by
  decide

theorem hS11 : ∀ v < 22, ∀ u, adjB 22 AMD11 v u = true →
    u = nb NBD11 v 0 ∨ u = nb NBD11 v 1 ∨ u = nb NBD11 v 2 :=
  fun v hv u hu => hSb11 v hv u (adjB_lt hu).2 hu

theorem hD11 : ∀ v < 22, nb NBD11 v 0 ≠ nb NBD11 v 1 ∧ nb NBD11 v 0 ≠ nb NBD11 v 2 ∧
    nb NBD11 v 1 ≠ nb NBD11 v 2 := by
  decide

theorem hI11 : ∀ v < 22, adjB 22 AMD11 v v = false := by decide

/-- **監査**：ビット符号化されたグラフは GP(11,3) そのものである。
  外輪 O_j–O_(j+1)（頂点 j, j < 11）・スポーク O_j–I_j（I_j = 11+j）・
  内輪 I_x–I_(x+3)（歩幅 3）。 -/
theorem adjB11_iff_GP : ∀ a < 22, ∀ b < 22,
    (adjB 22 AMD11 a b = true ↔
      ((a < 11 ∧ b < 11 ∧ (b = (a + 1) % 11 ∨ a = (b + 1) % 11)) ∨
       (a < 11 ∧ b = a + 11) ∨ (b < 11 ∧ a = b + 11) ∨
       (11 ≤ a ∧ 11 ≤ b ∧ (b - 11 = (a - 11 + 3) % 11 ∨ a - 11 = (b - 11 + 3) % 11)))) := by
  decide

/-! ### Mathlib の SimpleGraph として -/

theorem adjB11_symm : ∀ a b : Fin 22, adjB 22 AMD11 a.val b.val = true →
    adjB 22 AMD11 b.val a.val = true := by decide

theorem adjB11_irrefl : ∀ a : Fin 22, ¬ (adjB 22 AMD11 a.val a.val = true) := by decide

/-- GP(11,3)。 -/
def GP11 : SimpleGraph (Fin 22) where
  Adj a b := adjB 22 AMD11 a.val b.val = true
  symm := ⟨fun a b h => adjB11_symm a b h⟩
  loopless := ⟨fun a h => adjB11_irrefl a h⟩

instance : DecidableRel GP11.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB 22 AMD11 a.val b.val = true))

theorem GP11_degree : ∀ v : Fin 22, GP11.degree v = 3 := by decide

theorem GP11_adj_iff (a b : Fin 22) : GP11.Adj a b ↔ adjB 22 AMD11 a.val b.val = true :=
  Iff.rfl

/-- 頂点 0 の第 0 近傍（頂点 1）から始まる枝。探索木 10226 節点。 -/
theorem t110 : topc 22 AMD11 NBD11 (nb NBD11 0 0) 20 = 6 := by
  decide +kernel

/-- 頂点 0 の第 1 近傍（頂点 10）から始まる枝。探索木 10226 節点。 -/
theorem t111 : topc 22 AMD11 NBD11 (nb NBD11 0 1) 20 = 5 := by
  decide +kernel

/-- 頂点 0 の第 2 近傍（頂点 11）から始まる枝。探索木 10185 節点。 -/
theorem t112 : topc 22 AMD11 NBD11 (nb NBD11 0 2) 20 = 0 := by
  decide +kernel

/-! ### 個数（核で評価） -/

theorem num11 : numAll 22 AMD11 NBD11 20 = 11 := by
  rw [numAll, t110, t111, t112]

/-- **主定理**：GP(11,3) の正準向きハミルトン閉路の表現はちょうど 11 個あり、
  11 はその個数を割る。`HamRep 22 AMD11 l` は「`0 :: l` が長さ 22 の閉路で
  頂点が全て異なり、向きが正準（`l` の先頭 < `l` の末尾）」という条件
  （`hamRep_iff` / `hamRep_covers` を見よ）。向きの正準化により、これは
  **無向のハミルトン閉路の個数 #HC(GP(11,3)) そのもの** である。 -/
theorem GP11_hc_card : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 22 AMD11 l) ∧ S.card = 11 ∧ 11 ∣ S.card := by
  obtain ⟨S, hmem, hc⟩ :=
    card_hamRep 22 AMD11 NBD11 hA11 hS11 hD11 hI11 (by norm_num) 20 (by norm_num)
  have hcard : S.card = 11 := by rw [hc, num11]
  exact ⟨S, hmem, hcard, by omega⟩

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### GP(13,3) の符号化（26 頂点・39 辺・三価） -/

/-- 隣接行列（26×26 ビット）。 -/
def AMD13 : ℕ := 19767759756300954227788458834369185021504927816243007496523257791720885538422334751154709471951822533969066082066402447053833923936774322342281436610025754726068418839629829108868475043995851543566888962

/-- 近傍表（5 ビット × 3 × 26、昇順）。 -/
def NBD13 : ℕ := 1771602720509879026298245428921422518635491668268015146824817746932257157323300962038818748483330819793153456213079425

theorem hA13 : ∀ v < 26, adjB 26 AMD13 v (nb NBD13 v 0) = true ∧
    adjB 26 AMD13 v (nb NBD13 v 1) = true ∧ adjB 26 AMD13 v (nb NBD13 v 2) = true := by
  decide

theorem hSb13 : ∀ v < 26, ∀ u < 26, adjB 26 AMD13 v u = true →
    u = nb NBD13 v 0 ∨ u = nb NBD13 v 1 ∨ u = nb NBD13 v 2 := by
  decide

theorem hS13 : ∀ v < 26, ∀ u, adjB 26 AMD13 v u = true →
    u = nb NBD13 v 0 ∨ u = nb NBD13 v 1 ∨ u = nb NBD13 v 2 :=
  fun v hv u hu => hSb13 v hv u (adjB_lt hu).2 hu

theorem hD13 : ∀ v < 26, nb NBD13 v 0 ≠ nb NBD13 v 1 ∧ nb NBD13 v 0 ≠ nb NBD13 v 2 ∧
    nb NBD13 v 1 ≠ nb NBD13 v 2 := by
  decide

theorem hI13 : ∀ v < 26, adjB 26 AMD13 v v = false := by decide

/-- **監査**：ビット符号化されたグラフは GP(13,3) そのものである。
  外輪 O_j–O_(j+1)（頂点 j, j < 13）・スポーク O_j–I_j（I_j = 13+j）・
  内輪 I_x–I_(x+3)（歩幅 3）。 -/
theorem adjB13_iff_GP : ∀ a < 26, ∀ b < 26,
    (adjB 26 AMD13 a b = true ↔
      ((a < 13 ∧ b < 13 ∧ (b = (a + 1) % 13 ∨ a = (b + 1) % 13)) ∨
       (a < 13 ∧ b = a + 13) ∨ (b < 13 ∧ a = b + 13) ∨
       (13 ≤ a ∧ 13 ≤ b ∧ (b - 13 = (a - 13 + 3) % 13 ∨ a - 13 = (b - 13 + 3) % 13)))) := by
  decide

/-! ### Mathlib の SimpleGraph として -/

theorem adjB13_symm : ∀ a b : Fin 26, adjB 26 AMD13 a.val b.val = true →
    adjB 26 AMD13 b.val a.val = true := by decide

theorem adjB13_irrefl : ∀ a : Fin 26, ¬ (adjB 26 AMD13 a.val a.val = true) := by decide

/-- GP(13,3)。 -/
def GP13 : SimpleGraph (Fin 26) where
  Adj a b := adjB 26 AMD13 a.val b.val = true
  symm := ⟨fun a b h => adjB13_symm a b h⟩
  loopless := ⟨fun a h => adjB13_irrefl a h⟩

instance : DecidableRel GP13.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB 26 AMD13 a.val b.val = true))

theorem GP13_degree : ∀ v : Fin 26, GP13.degree v = 3 := by decide

theorem GP13_adj_iff (a b : Fin 26) : GP13.Adj a b ↔ adjB 26 AMD13 a.val b.val = true :=
  Iff.rfl

/-- 頂点 0 の第 0 近傍（頂点 1）から始まる枝。探索木 45152 節点。 -/
theorem t130 : topc 26 AMD13 NBD13 (nb NBD13 0 0) 24 = 18 := by
  decide +kernel

/-- 頂点 0 の第 1 近傍（頂点 12）から始まる枝。探索木 45152 節点。 -/
theorem t131 : topc 26 AMD13 NBD13 (nb NBD13 0 1) 24 = 8 := by
  decide +kernel

/-- 頂点 0 の第 2 近傍（頂点 13）から始まる枝。探索木 44623 節点。 -/
theorem t132 : topc 26 AMD13 NBD13 (nb NBD13 0 2) 24 = 0 := by
  decide +kernel

/-! ### 個数（核で評価） -/

theorem num13 : numAll 26 AMD13 NBD13 24 = 26 := by
  rw [numAll, t130, t131, t132]

/-- **主定理**：GP(13,3) の正準向きハミルトン閉路の表現はちょうど 26 個あり、
  13 はその個数を割る。`HamRep 26 AMD13 l` は「`0 :: l` が長さ 26 の閉路で
  頂点が全て異なり、向きが正準（`l` の先頭 < `l` の末尾）」という条件
  （`hamRep_iff` / `hamRep_covers` を見よ）。向きの正準化により、これは
  **無向のハミルトン閉路の個数 #HC(GP(13,3)) そのもの** である。 -/
theorem GP13_hc_card : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 26 AMD13 l) ∧ S.card = 26 ∧ 13 ∣ S.card := by
  obtain ⟨S, hmem, hc⟩ :=
    card_hamRep 26 AMD13 NBD13 hA13 hS13 hD13 hI13 (by norm_num) 24 (by norm_num)
  have hcard : S.card = 26 := by rw [hc, num13]
  exact ⟨S, hmem, hcard, by omega⟩

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### GP(15,3) の符号化（30 頂点・45 辺・三価） -/

/-- 隣接行列（30×30 ビット）。 -/
def AMD15 : ℕ := 529455334795351988582410621574237727007841005463894098797430061896183676652942369967509654001058881321400239779427876103365554449247710928124847380911958267967260423265776512741178198059363609454148465817852080869166041644536757077375668302461248776273325320612754800642

/-- 近傍表（5 ビット × 3 × 30、昇順）。 -/
def NBD15 : ℕ := 2411805384367547620783358138022719940367112317003718527045045632381169406000588117351327990447675300589886904111028522271023058464554433

theorem hA15 : ∀ v < 30, adjB 30 AMD15 v (nb NBD15 v 0) = true ∧
    adjB 30 AMD15 v (nb NBD15 v 1) = true ∧ adjB 30 AMD15 v (nb NBD15 v 2) = true := by
  decide

theorem hSb15 : ∀ v < 30, ∀ u < 30, adjB 30 AMD15 v u = true →
    u = nb NBD15 v 0 ∨ u = nb NBD15 v 1 ∨ u = nb NBD15 v 2 := by
  decide

theorem hS15 : ∀ v < 30, ∀ u, adjB 30 AMD15 v u = true →
    u = nb NBD15 v 0 ∨ u = nb NBD15 v 1 ∨ u = nb NBD15 v 2 :=
  fun v hv u hu => hSb15 v hv u (adjB_lt hu).2 hu

theorem hD15 : ∀ v < 30, nb NBD15 v 0 ≠ nb NBD15 v 1 ∧ nb NBD15 v 0 ≠ nb NBD15 v 2 ∧
    nb NBD15 v 1 ≠ nb NBD15 v 2 := by
  decide

theorem hI15 : ∀ v < 30, adjB 30 AMD15 v v = false := by decide

/-- **監査**：ビット符号化されたグラフは GP(15,3) そのものである。
  外輪 O_j–O_(j+1)（頂点 j, j < 15）・スポーク O_j–I_j（I_j = 15+j）・
  内輪 I_x–I_(x+3)（歩幅 3）。 -/
theorem adjB15_iff_GP : ∀ a < 30, ∀ b < 30,
    (adjB 30 AMD15 a b = true ↔
      ((a < 15 ∧ b < 15 ∧ (b = (a + 1) % 15 ∨ a = (b + 1) % 15)) ∨
       (a < 15 ∧ b = a + 15) ∨ (b < 15 ∧ a = b + 15) ∨
       (15 ≤ a ∧ 15 ≤ b ∧ (b - 15 = (a - 15 + 3) % 15 ∨ a - 15 = (b - 15 + 3) % 15)))) := by
  decide

/-! ### Mathlib の SimpleGraph として -/

theorem adjB15_symm : ∀ a b : Fin 30, adjB 30 AMD15 a.val b.val = true →
    adjB 30 AMD15 b.val a.val = true := by decide

theorem adjB15_irrefl : ∀ a : Fin 30, ¬ (adjB 30 AMD15 a.val a.val = true) := by decide

/-- GP(15,3)。 -/
def GP15 : SimpleGraph (Fin 30) where
  Adj a b := adjB 30 AMD15 a.val b.val = true
  symm := ⟨fun a b h => adjB15_symm a b h⟩
  loopless := ⟨fun a h => adjB15_irrefl a h⟩

instance : DecidableRel GP15.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB 30 AMD15 a.val b.val = true))

theorem GP15_degree : ∀ v : Fin 30, GP15.degree v = 3 := by decide

theorem GP15_adj_iff (a b : Fin 30) : GP15.Adj a b ↔ adjB 30 AMD15 a.val b.val = true :=
  Iff.rfl

/-! ### 分割の道具（核計算を 6 本に割るため） -/

theorem cntf_true {u vis m : ℕ} (h : Nat.testBit vis u = true) : cntf u vis m = 0 := by
  simp [cntf, h]

theorem cntf_false {u vis m : ℕ} (h : Nat.testBit vis u = false) : cntf u vis m = m := by
  simp [cntf, h]

/-- 探索を一歩ほどく（`nb` の値を与えて `cnt` の定義式を使うだけ。核計算はしない）。 -/
theorem cnt_step3 (N AMD NBD a k v vis u0 u1 u2 : ℕ)
    (h0 : nb NBD v 0 = u0) (h1 : nb NBD v 1 = u1) (h2 : nb NBD v 2 = u2) :
    cnt N AMD NBD a (k + 1) v vis =
      cntf u0 vis (cnt N AMD NBD a k u0 (vis ||| 2 ^ u0)) +
      cntf u1 vis (cnt N AMD NBD a k u1 (vis ||| 2 ^ u1)) +
      cntf u2 vis (cnt N AMD NBD a k u2 (vis ||| 2 ^ u2)) := by
  rw [cnt, h0, h1, h2]

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 1 - 2」の核計算（探索木 89939 節点）。 -/
theorem s15_1_2 : cnt 30 AMD15 NBD15 1 27 2 (3 ||| 2 ^ 2) = 29 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 1 - 16」の核計算（探索木 92426 節点）。 -/
theorem s15_1_16 : cnt 30 AMD15 NBD15 1 27 16 (3 ||| 2 ^ 16) = 23 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 14 - 13」の核計算（探索木 89939 節点）。 -/
theorem s15_14_13 : cnt 30 AMD15 NBD15 14 27 13 (16385 ||| 2 ^ 13) = 11 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 14 - 29」の核計算（探索木 92426 節点）。 -/
theorem s15_14_29 : cnt 30 AMD15 NBD15 14 27 29 (16385 ||| 2 ^ 29) = 12 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 15 - 18」の核計算（探索木 92207 節点）。 -/
theorem s15_15_18 : cnt 30 AMD15 NBD15 15 27 18 (32769 ||| 2 ^ 18) = 0 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 枝「0 - 15 - 27」の核計算（探索木 92207 節点）。 -/
theorem s15_15_27 : cnt 30 AMD15 NBD15 15 27 27 (32769 ||| 2 ^ 27) = 0 := by
  decide +kernel

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-- 頂点 0 の第 0 近傍（頂点 1）から始まる枝。二つの部分木を合わせる。 -/
theorem t150 : topc 30 AMD15 NBD15 (nb NBD15 0 0) 28 = 52 := by
  rw [show nb NBD15 0 0 = 1 from by decide, topc,
    show (1 ||| 2 ^ 1 : ℕ) = 3 from by decide,
    show (28 : ℕ) = 27 + 1 from by decide,
    cnt_step3 30 AMD15 NBD15 1 27 1 3 0 2 16
      (by decide) (by decide) (by decide),
    cntf_true (show Nat.testBit 3 0 = true from by decide),
    cntf_false (show Nat.testBit 3 2 = false from by decide),
    cntf_false (show Nat.testBit 3 16 = false from by decide),
    s15_1_2, s15_1_16]

/-- 頂点 0 の第 1 近傍（頂点 14）から始まる枝。二つの部分木を合わせる。 -/
theorem t151 : topc 30 AMD15 NBD15 (nb NBD15 0 1) 28 = 23 := by
  rw [show nb NBD15 0 1 = 14 from by decide, topc,
    show (1 ||| 2 ^ 14 : ℕ) = 16385 from by decide,
    show (28 : ℕ) = 27 + 1 from by decide,
    cnt_step3 30 AMD15 NBD15 14 27 14 16385 0 13 29
      (by decide) (by decide) (by decide),
    cntf_true (show Nat.testBit 16385 0 = true from by decide),
    cntf_false (show Nat.testBit 16385 13 = false from by decide),
    cntf_false (show Nat.testBit 16385 29 = false from by decide),
    s15_14_13, s15_14_29]

/-- 頂点 0 の第 2 近傍（頂点 15）から始まる枝。二つの部分木を合わせる。 -/
theorem t152 : topc 30 AMD15 NBD15 (nb NBD15 0 2) 28 = 0 := by
  rw [show nb NBD15 0 2 = 15 from by decide, topc,
    show (1 ||| 2 ^ 15 : ℕ) = 32769 from by decide,
    show (28 : ℕ) = 27 + 1 from by decide,
    cnt_step3 30 AMD15 NBD15 15 27 15 32769 0 18 27
      (by decide) (by decide) (by decide),
    cntf_true (show Nat.testBit 32769 0 = true from by decide),
    cntf_false (show Nat.testBit 32769 18 = false from by decide),
    cntf_false (show Nat.testBit 32769 27 = false from by decide),
    s15_15_18, s15_15_27]

/-! ### 個数（核で評価） -/

theorem num15 : numAll 30 AMD15 NBD15 28 = 75 := by
  rw [numAll, t150, t151, t152]

/-- **主定理**：GP(15,3) の正準向きハミルトン閉路の表現はちょうど 75 個あり、
  15 はその個数を割る。`HamRep 30 AMD15 l` は「`0 :: l` が長さ 30 の閉路で
  頂点が全て異なり、向きが正準（`l` の先頭 < `l` の末尾）」という条件
  （`hamRep_iff` / `hamRep_covers` を見よ）。向きの正準化により、これは
  **無向のハミルトン閉路の個数 #HC(GP(15,3)) そのもの** である。 -/
theorem GP15_hc_card : ∃ S : Finset (List ℕ),
    (∀ l : List ℕ, l ∈ S ↔ HamRep 30 AMD15 l) ∧ S.card = 75 ∧ 15 ∣ S.card := by
  obtain ⟨S, hmem, hc⟩ :=
    card_hamRep 30 AMD15 NBD15 hA15 hS15 hD15 hI15 (by norm_num) 28 (by norm_num)
  have hcard : S.card = 75 := by rw [hc, num15]
  exact ⟨S, hmem, hcard, by omega⟩

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

set_option maxRecDepth 1000000

/-! ### 回転 ρ^d と閉路の辺集合 -/

/-- 回転 ρ^d：外輪 `O_j = j ↦ O_(j+d)`、内輪 `I_j = n+j ↦ I_(j+d)`（頂点数 N = 2n）。 -/
def rho (n d v : ℕ) : ℕ := if v < n then (v + d) % n else n + ((v - n + d) % n)

/-- 辺 `{a,b}` に対応するビットの位置（`N * min + max`）。 -/
def ebit (N a b : ℕ) : ℕ := if a < b then N * a + b else N * b + a

/-- 頂点列の辺集合（`first` で閉じる）。 -/
def emaskAux (N first : ℕ) : ℕ → List ℕ → ℕ
  | v, [] => 2 ^ ebit N v first
  | v, (u :: t) => 2 ^ ebit N v u ||| emaskAux N first u t

/-- 閉路（長さ N の頂点列、最後の頂点は先頭に戻る）の辺集合のビットマスク。 -/
def emask (N : ℕ) : List ℕ → ℕ
  | [] => 0
  | (v :: t) => emaskAux N v v t

/-! ### ρ^d は GP(n,3) の自己同型 -/

theorem rho_aut7 : ∀ d < 7, ∀ a < 14, ∀ b < 14,
    (adjB 14 AMD7 a b = true ↔ adjB 14 AMD7 (rho 7 d a) (rho 7 d b) = true) := by decide

theorem rho_aut9 : ∀ d < 9, ∀ a < 18, ∀ b < 18,
    (adjB 18 AMD9 a b = true ↔ adjB 18 AMD9 (rho 9 d a) (rho 9 d b) = true) := by decide

theorem rho_aut11 : ∀ d < 11, ∀ a < 22, ∀ b < 22,
    (adjB 22 AMD11 a b = true ↔ adjB 22 AMD11 (rho 11 d a) (rho 11 d b) = true) := by decide

/-! ### 不動点なし（核で全列挙して確かめる） -/

/-- GP(7,3)：どのハミルトン閉路も、非自明な回転で写すと別の閉路になる。 -/
theorem no_rho_fixed7 : ∀ l ∈ enumAll 14 AMD7 NBD7 12, ∀ d < 7, 0 < d →
    emask 14 (List.map (rho 7 d) (0 :: l)) ≠ emask 14 (0 :: l) := by
  decide +kernel

/-- GP(9,3)（`3 | n` の場合）。 -/
theorem no_rho_fixed9 : ∀ l ∈ enumAll 18 AMD9 NBD9 16, ∀ d < 9, 0 < d →
    emask 18 (List.map (rho 9 d) (0 :: l)) ≠ emask 18 (0 :: l) := by
  decide +kernel

/-- GP(11,3)。 -/
theorem no_rho_fixed11 : ∀ l ∈ enumAll 22 AMD11 NBD11 20, ∀ d < 11, 0 < d →
    emask 22 (List.map (rho 11 d) (0 :: l)) ≠ emask 22 (0 :: l) := by
  decide +kernel

/-- 段階 1 の `HamRep` の言葉に直したもの（`mem_enumAll` 経由）。 -/
theorem no_rho_fixed7' : ∀ l : List ℕ, HamRep 14 AMD7 l → ∀ d < 7, 0 < d →
    emask 14 (List.map (rho 7 d) (0 :: l)) ≠ emask 14 (0 :: l) := by
  intro l hl d hd hd0
  obtain ⟨h1, h2, h3, h4⟩ := hl
  exact no_rho_fixed7 l
    ((mem_enumAll 14 AMD7 NBD7 hA7 hS7 hI7 (by norm_num) 12).mpr ⟨by omega, h2, h3, h4⟩) d hd hd0

end GeneralizedPetersen.Small

namespace GeneralizedPetersen.Small

open MulAction

/-- 自由作用の数え上げ（一般の群）：群 `G` が `X` に作用し、どの点の固定化群も
  自明（`⊥`）なら `Nat.card G ∣ Nat.card X`。
  Mathlib の `MulAction.selfEquivOrbitsQuotientProd`（`X ≃ X/G × G`）から一行。 -/
theorem card_dvd_of_stabilizer_bot (G : Type*) [Group G] (X : Type*) [MulAction G X]
    (h : ∀ b : X, MulAction.stabilizer G b = ⊥) : Nat.card G ∣ Nat.card X := by
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd h), Nat.card_prod]
  exact dvd_mul_left _ _

/-- 同じことを点ごとの自由性で述べたもの。 -/
theorem card_dvd_of_free (G : Type*) [Group G] (X : Type*) [MulAction G X]
    (h : ∀ (b : X) (g : G), g • b = b → g = 1) : Nat.card G ∣ Nat.card X :=
  card_dvd_of_stabilizer_bot G X fun b =>
    (Subgroup.eq_bot_iff_forall _).mpr fun g hg => h b g (MulAction.mem_stabilizer_iff.mp hg)

/-- 巡回群の場合（主定理が使う形。`n` は素数でなくてよい）。 -/
theorem card_dvd_of_free_cyclic (G : Type*) [Group G] [IsCyclic G] (n : ℕ) (hG : Nat.card G = n)
    (X : Type*) [MulAction G X] (h : ∀ (b : X) (g : G), g • b = b → g = 1) :
    n ∣ Nat.card X := by
  rw [← hG]; exact card_dvd_of_free G X h

/-- **段階 2 の主結果**：位数 `n` の置換 `f` が集合 `X` に「不動点なし」で作用すれば
  `n ∣ Nat.card X`。
  主定理では `f` が一般化ペテルセングラフ `GP(n,3)` の回転 `ρ`、`X` がハミルトン閉路の
  集合であり、`hfree`（`0 < i < n` なる `ρ^i` は閉路を固定しない）が
  紙の証明の内容。 -/
theorem card_dvd_of_perm_free {X : Type*} (f : Equiv.Perm X) (n : ℕ) (hn : 0 < n)
    (hfn : f ^ n = 1) (hfree : ∀ i, 0 < i → i < n → ∀ x : X, (f ^ i) x ≠ x) :
    n ∣ Nat.card X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Nat.card_eq_zero.mpr (Or.inl hX)]
    exact dvd_zero n
  · obtain ⟨x0⟩ := hX
    have hord : orderOf f = n := by
      rw [orderOf_eq_iff hn]
      refine ⟨hfn, fun m hm hm0 hpow => hfree m hm0 hm x0 ?_⟩
      rw [hpow]; rfl
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hst : ∀ b : X, MulAction.stabilizer (Subgroup.zpowers f) b = ⊥ := by
      intro b
      refine (Subgroup.eq_bot_iff_forall _).mpr ?_
      intro g hg
      have hgb : (g : Equiv.Perm X) b = b := MulAction.mem_stabilizer_iff.mp hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hle : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k hnz
      have hlt : k % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos k (by exact_mod_cast hn)
      set m : ℕ := (k % (n : ℤ)).toNat with hmdef
      have hmn : m < n := by omega
      have hfm : f ^ m = (g : Equiv.Perm X) := by
        rw [hmdef, ← zpow_natCast, Int.toNat_of_nonneg hle, ← hord]
        rw [show ((orderOf f : ℕ) : ℤ) = (n : ℤ) by rw [hord]]
        rw [show (k % (n : ℤ)) = k % ((orderOf f : ℕ) : ℤ) by rw [hord]]
        rw [zpow_mod_orderOf]
        exact hk
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0, pow_zero] at hfm
        exact Subtype.ext hfm.symm
      · exact absurd (hfm ▸ hgb) (hfree m hm0 hmn b)
    have hd := card_dvd_of_stabilizer_bot (Subgroup.zpowers f) X hst
    rwa [Nat.card_zpowers, hord] at hd

end GeneralizedPetersen.Small
