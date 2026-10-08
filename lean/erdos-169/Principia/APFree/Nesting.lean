/-

  エルデシュ問題 #169。が紙で証明した「k-AP の入れ子補題」を機械検査する。

  【定義】APFreeK k S：公差 d > 0 の k 項等差数列 x, x+d, …, x+(k−1)d が S に
    すべて入ることはない。k = 3 で APFreeWindowSeparation の IsThreeAPFree と同値（apFreeK_three_iff）。

  【核（二集合版）】頭 H ⊆ [1, z]、ブロック B ⊆ [l, r]。
    補題 1（core_loc） ：k ≥ 3、H・B が k-AP-free、(i) l > 2z、(ii) r − l < (k−2)(l − z)
                          ⟹ H ∪ B は k-AP-free。
    補題 2（core_strong）：k ≥ 4、H が k-AP-free、B が (k−1)-AP-free、(i) l > 2z
                          ⟹ H ∪ B は k-AP-free。**r（窓の長さ）への条件なし。**

  【場合分け】x_0 < … < x_{k−1} を公差 d の k-AP とする。
    x_{k−1} ∈ H → 全項 ≤ z < l なので全項 ∈ H（m = k の下側）。
    x_{k−1} ∈ B, x_0 ∈ B → 全項 ≥ l > z なので全項 ∈ B（m = k）。
    x_0 ∈ H, x_1 ∈ B → x_1..x_{k−1} ∈ B（m = k−1）。補題 2 は (k−1)-AP-free で終わり。
                         補題 1 は (k−2)d = x_{k−1} − x_1 ≤ r − l < (k−2)(l − z) ≤ (k−2)d。
    x_0 ∈ H, x_1 ∈ H → どこかで H から B へ渡る隣接対があるので d ≥ l − z、
                         ゆえに x_1 = x_0 + d ≥ 1 + l − z > z、x_1 ∈ H に反する
                         （紙の m = 1 と 2 ≤ m ≤ k−2 の二行がここで一つになる）。

  【ℕ 添字の合併】A_j ⊆ [l_j, r_j]、0 < l_0、l_j ≤ r_j、l_{j+1} > 2 r_j。
    有限接頭辞 U n = ⋃_{j<n} A_j で帰納し、k-AP は有限個の項しか持たないので
    ⋃_j A_j にも及ぶ（lemma1_iUnion / lemma2_iUnion）。

  【k = 3 への帰着】(i)(ii) は a > 2z ∧ a > z + t（Wróblewski の倍加税、
    APFreeStepsSeparated.sep_M1 の前提）と一致する（three_conditions_iff）。
-/
import Mathlib.Tactic
import Principia.APFree.WindowSeparation
import Principia.APFree.StepsSeparated

namespace APFree.Nesting
open APFree.WindowSeparation

/-! ## 1. k-AP-free の述語 -/

/-- 集合 S が公差 d > 0 の k 項等差数列を含まない。 -/
def APFreeK (k : ℕ) (S : Set ℤ) : Prop :=
  ∀ x d : ℤ, 0 < d → ¬ (∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ S)

/-- 短い AP を含まなければ長い AP も含まない。 -/
theorem apFreeK_of_le {m k : ℕ} (hmk : m ≤ k) {S : Set ℤ} (h : APFreeK m S) :
    APFreeK k S := fun x d hd hall =>
  h x d hd (fun i hi => hall i (lt_of_lt_of_le hi hmk))

/-- 部分集合に遺伝する。 -/
theorem apFreeK_mono {k : ℕ} {S T : Set ℤ} (hST : S ⊆ T) (h : APFreeK k T) :
    APFreeK k S := fun x d hd hall => h x d hd (fun i hi => hST (hall i hi))

/-- **k = 3 で APFreeWindowSeparation の `IsThreeAPFree` と同値。** -/
theorem apFreeK_three_iff (S : Set ℤ) : APFreeK 3 S ↔ IsThreeAPFree S := by
  constructor
  · intro h x hx y hy z hz hxyz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- x < y < z, 公差 y − x
      apply h x (y - x) (by omega)
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · simpa using hx
      · simpa using hy
      · have : x + ((2 : ℕ) : ℤ) * (y - x) = z := by push_cast; omega
        rw [this]; exact hz
    · -- z < y < x, 公差 x − y、始点 z
      apply h z (x - y) (by omega)
      intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · simpa using hz
      · have : z + ((1 : ℕ) : ℤ) * (x - y) = y := by push_cast; omega
        rw [this]; exact hy
      · have : z + ((2 : ℕ) : ℤ) * (x - y) = x := by push_cast; omega
        rw [this]; exact hx
  · intro h x d hd hall
    have h0 := hall 0 (by norm_num)
    have h1 := hall 1 (by norm_num)
    have h2 := hall 2 (by norm_num)
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] at h0 h1
    push_cast at h2
    have := h x h0 (x + d) h1 (x + 2 * d) h2 (by ring)
    omega

/-! ## 2. 核：二集合版 -/

section core

variable {k : ℕ} {H B : Set ℤ} {z l r : ℤ}

/-- 補助：`i ≤ n` なら `(i:ℤ) * d ≤ (n:ℤ) * d`（d > 0）。 -/
private theorem cast_mul_le {i n : ℕ} (h : i ≤ n) {d : ℤ} (hd : 0 < d) :
    (i : ℤ) * d ≤ (n : ℤ) * d :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) hd.le

/-- **場合 x_{k−1} ∈ H**：全項が H に入る。 -/
private theorem all_in_head (_hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x)
    (hlt : ∀ x ∈ H, x < l) {x d : ℤ} (hd : 0 < d) (hk : 1 ≤ k)
    (hall : ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ H ∪ B)
    (hlast : x + ((k - 1 : ℕ) : ℤ) * d ∈ H) :
    ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ H := by
  intro i hi
  rcases hall i hi with h | h
  · exact h
  · exfalso
    have h1 := hlt _ hlast
    have h2 := hB _ h
    have h3 := cast_mul_le (show i ≤ k - 1 by omega) hd
    omega

/-- **場合 x_0 ∈ B**：全項が B に入る。 -/
private theorem all_in_block (_hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x)
    (hlt : ∀ x ∈ H, x < l) {x d : ℤ} (hd : 0 < d)
    (hall : ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ H ∪ B)
    (hfirst : x ∈ B) :
    ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ B := by
  intro i hi
  rcases hall i hi with h | h
  · exfalso
    have h1 := hlt _ h
    have h2 := hB _ hfirst
    have h3 : (0 : ℤ) ≤ (i : ℤ) * d := mul_nonneg (by positivity) hd.le
    omega
  · exact h

/-- **場合 x_0 ∈ H, x_1 ∈ B**：x_1 以降は全部 B。 -/
private theorem tail_in_block (_hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x)
    (hlt : ∀ x ∈ H, x < l) {x d : ℤ} (hd : 0 < d)
    (hall : ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ H ∪ B)
    (hsecond : x + d ∈ B) :
    ∀ i : ℕ, i < k - 1 → (x + d) + (i : ℤ) * d ∈ B := by
  intro i hi
  have hmem := hall (i + 1) (by omega)
  have heq : x + ((i + 1 : ℕ) : ℤ) * d = (x + d) + (i : ℤ) * d := by push_cast; ring
  rw [heq] at hmem
  rcases hmem with h | h
  · exfalso
    have h1 := hlt _ h
    have h2 := hB _ hsecond
    have h3 : (0 : ℤ) ≤ (i : ℤ) * d := mul_nonneg (by positivity) hd.le
    omega
  · exact h

/-- **渡り**：x_0 ≤ z かつ x_{k−1} ≥ l なら、H から B に渡る隣接対があり d ≥ l − z。
    帰納で「i までは全部 ≤ z」か「既に d ≥ l − z」のどちらかを保つ。 -/
private theorem crossing_gap (hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x) (hzl : z < l)
    {x d : ℤ} (_hd : 0 < d) (hk : 1 ≤ k)
    (hall : ∀ i : ℕ, i < k → x + (i : ℤ) * d ∈ H ∪ B)
    (hfirst : x ∈ H) (hlast : x + ((k - 1 : ℕ) : ℤ) * d ∈ B) :
    l - z ≤ d := by
  have key : ∀ n : ℕ, n < k → (x + (n : ℤ) * d ≤ z ∨ l - z ≤ d) := by
    intro n
    induction n with
    | zero =>
      intro _
      left; simpa using (hH x hfirst).2
    | succ n ih =>
      intro hn
      rcases ih (by omega) with hle | hgap
      · rcases hall (n + 1) hn with h | h
        · left; exact (hH _ h).2
        · right
          have h2 := hB _ h
          push_cast at h2
          nlinarith
      · right; exact hgap
  rcases key (k - 1) (by omega) with hle | hgap
  · exfalso
    have := hB _ hlast
    omega
  · exact hgap

/-- **補題 1 の核（二集合版）**。頭 H ⊆ [1, z] とブロック B ⊆ [l, r] が k-AP-free、
    (i) l > 2z、(ii) r − l < (k−2)(l − z) ⟹ H ∪ B は k-AP-free。 -/
theorem core_loc (hk : 3 ≤ k)
    (hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x ∧ x ≤ r)
    (hHf : APFreeK k H) (hBf : APFreeK k B)
    (hi : 2 * z < l) (hii : r - l < ((k : ℤ) - 2) * (l - z)) :
    APFreeK k (H ∪ B) := by
  intro x d hd hall
  have hB' : ∀ x ∈ B, l ≤ x := fun x hx => (hB x hx).1
  -- H の元は正なので、(i) から H の元はすべて l 未満（z ≤ 0 で H が空でもよい）
  have hlt : ∀ x ∈ H, x < l := fun x hx => by have := hH x hx; omega
  rcases hall (k - 1) (by omega) with hlast | hlast
  · -- m = k, 下側
    exact hHf x d hd (all_in_head hH hB' hlt hd (by omega) hall hlast)
  rcases hall 0 (by omega) with hfirst | hfirst
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    rcases hall 1 (by omega) with hsecond | hsecond
    · -- x_0, x_1 ∈ H：渡りの隙間から矛盾
      simp only [Nat.cast_one, one_mul] at hsecond
      have hzl : z < l := by have := hH _ hfirst; omega
      have hgap := crossing_gap hH hB' hzl hd (by omega) hall hfirst hlast
      have h0 := (hH _ hfirst).1
      have h1 := (hH _ hsecond).2
      omega
    · -- m = k − 1：(k−2) d = x_{k−1} − x_1 ≤ r − l < (k−2)(l − z) ≤ (k−2) d
      simp only [Nat.cast_one, one_mul] at hsecond
      have hx1 := hB _ hsecond
      have hxk := hB _ hlast
      have h0 := (hH _ hfirst).2
      have hgap : l - z ≤ d := by omega
      have hk2 : (0 : ℤ) ≤ (k : ℤ) - 2 := by
        have : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
        omega
      have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast] at hxk
      have hmul : ((k : ℤ) - 2) * (l - z) ≤ ((k : ℤ) - 2) * d :=
        mul_le_mul_of_nonneg_left hgap hk2
      nlinarith
  · -- m = k, 上側
    simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    exact hBf x d hd (all_in_block hH hB' hlt hd hall hfirst)

/-- **補題 2 の核（二集合版）**。k ≥ 4。頭 H ⊆ [1, z] は k-AP-free、
    ブロック B ⊆ [l, ∞) は (k−1)-AP-free、(i) l > 2z ⟹ H ∪ B は k-AP-free。
    **窓の上端 r への条件はない。** -/
theorem core_strong (hk : 4 ≤ k)
    (hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, l ≤ x)
    (hHf : APFreeK k H) (hBf : APFreeK (k - 1) B)
    (hi : 2 * z < l) :
    APFreeK k (H ∪ B) := by
  intro x d hd hall
  -- H の元は正なので、(i) から H の元はすべて l 未満（z ≤ 0 で H が空でもよい）
  have hlt : ∀ x ∈ H, x < l := fun x hx => by have := hH x hx; omega
  rcases hall (k - 1) (by omega) with hlast | hlast
  · exact hHf x d hd (all_in_head hH hB hlt hd (by omega) hall hlast)
  rcases hall 0 (by omega) with hfirst | hfirst
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    rcases hall 1 (by omega) with hsecond | hsecond
    · simp only [Nat.cast_one, one_mul] at hsecond
      have hzl : z < l := by have := hH _ hfirst; omega
      have hgap := crossing_gap hH hB hzl hd (by omega) hall hfirst hlast
      have h0 := (hH _ hfirst).1
      have h1 := (hH _ hsecond).2
      omega
    · -- m = k − 1：x_1..x_{k−1} は B の (k−1)-AP
      simp only [Nat.cast_one, one_mul] at hsecond
      exact hBf (x + d) d hd (tail_in_block hH hB hlt hd hall hsecond)
  · simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    exact (apFreeK_of_le (Nat.sub_le k 1) hBf) x d hd
      (all_in_block hH hB hlt hd hall hfirst)

end core

/-! ## 3. ℕ 添字の合併（紙の言明そのもの） -/

section iUnion

variable {k : ℕ} (W : Windows ℕ) (A : ℕ → Set ℤ)

/-- 有限接頭辞 ⋃_{j<n} A_j。 -/
def prefixUnion (n : ℕ) : Set ℤ := ⋃ j, ⋃ (_ : j < n), A j

theorem prefixUnion_succ (n : ℕ) :
    prefixUnion A (n + 1) = prefixUnion A n ∪ A n := by
  ext x
  simp only [prefixUnion, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨j, hj, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · exact Or.inl ⟨j, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨j, hj, hx⟩ | hx)
    · exact ⟨j, by omega, hx⟩
    · exact ⟨n, by omega, hx⟩

theorem prefixUnion_zero : prefixUnion A 0 = ∅ := by
  ext x; simp [prefixUnion]

/-- 窓の基本仮定：0 < l_0、l_j ≤ r_j、l_{j+1} > 2 r_j（倍加税）。 -/
structure Doubling (W : Windows ℕ) : Prop where
  l0 : 0 < W.l 0
  le : ∀ j, W.l j ≤ W.r j
  tax : ∀ j, 2 * W.r j < W.l (j + 1)

variable {W}

theorem Doubling.r_pos (hW : Doubling W) : ∀ j, 0 < W.r j := by
  intro j
  induction j with
  | zero => exact lt_of_lt_of_le hW.l0 (hW.le 0)
  | succ n ih => have := hW.tax n; have := hW.le (n + 1); omega

theorem Doubling.r_mono (hW : Doubling W) : ∀ j, W.r j ≤ W.r (j + 1) := by
  intro j; have := hW.tax j; have := hW.le (j + 1); have := hW.r_pos j; omega

/-- 有限接頭辞は [1, r_{n}] に収まる（n+1 個）。 -/
theorem Doubling.prefix_box (hW : Doubling W)
    (hbox : ∀ j, ∀ x ∈ A j, W.l j ≤ x ∧ x ≤ W.r j) :
    ∀ n, ∀ x ∈ prefixUnion A (n + 1), 0 < x ∧ x ≤ W.r n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [prefixUnion_succ, prefixUnion_zero, Set.empty_union] at hx
    have := hbox 0 x hx; have := hW.l0; omega
  | succ n ih =>
    intro x hx
    rw [prefixUnion_succ] at hx
    rcases hx with hx | hx
    · have := ih x hx; have := hW.r_mono n; omega
    · have := hbox (n + 1) x hx; have := hW.tax n; have := hW.r_pos n; omega

/-- k-AP が ⋃_j A_j に入るなら、ある有限接頭辞に入る。 -/
theorem apFreeK_iUnion_of_prefix (hpre : ∀ n, APFreeK k (prefixUnion A n)) :
    APFreeK k (⋃ j, A j) := by
  intro x d hd hall
  have hex : ∀ i : ℕ, ∃ j : ℕ, i < k → x + (i : ℤ) * d ∈ A j := by
    intro i
    by_cases hi : i < k
    · have := hall i hi
      simp only [Set.mem_iUnion] at this
      obtain ⟨j, hj⟩ := this
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose f hf using hex
  apply hpre ((Finset.range k).sup f + 1) x d hd
  intro i hi
  simp only [prefixUnion, Set.mem_iUnion]
  refine ⟨f i, ?_, hf i hi⟩
  have : f i ≤ (Finset.range k).sup f := Finset.le_sup (Finset.mem_range.mpr hi)
  omega

/-- **補題 1（区間だけの形）**。k ≥ 3、各 A_j ⊆ [l_j, r_j] が k-AP-free、
    (i) l_{j+1} > 2 r_j、(ii) r_{j+1} − l_{j+1} < (k−2)(l_{j+1} − r_j) ⟹ ⋃_j A_j は k-AP-free。 -/
theorem lemma1_iUnion (hk : 3 ≤ k) (hW : Doubling W)
    (hbox : ∀ j, ∀ x ∈ A j, W.l j ≤ x ∧ x ≤ W.r j)
    (hfree : ∀ j, APFreeK k (A j))
    (hii : ∀ j, W.r (j + 1) - W.l (j + 1) < ((k : ℤ) - 2) * (W.l (j + 1) - W.r j)) :
    APFreeK k (⋃ j, A j) := by
  apply apFreeK_iUnion_of_prefix
  intro n
  induction n with
  | zero =>
    rw [prefixUnion_zero]
    intro x d hd hall; exact hall 0 (by omega)
  | succ n ih =>
    rw [prefixUnion_succ]
    cases n with
    | zero =>
      rw [prefixUnion_zero, Set.empty_union]; exact hfree 0
    | succ n =>
      exact core_loc hk (hW.prefix_box A hbox n) (hbox (n + 1)) ih (hfree (n + 1))
        (hW.tax n) (hii n)

/-- **補題 2（ブロックを強くして窓を自由にする形）**。k ≥ 4、A_0 は k-AP-free、
    j ≥ 1 の A_j は (k−1)-AP-free、l_{j+1} > 2 r_j ⟹ ⋃_j A_j は k-AP-free。
    **窓の長さに制約はない。** -/
theorem lemma2_iUnion (hk : 4 ≤ k) (hW : Doubling W)
    (hbox : ∀ j, ∀ x ∈ A j, W.l j ≤ x ∧ x ≤ W.r j)
    (hhead : APFreeK k (A 0))
    (hblock : ∀ j, APFreeK (k - 1) (A (j + 1))) :
    APFreeK k (⋃ j, A j) := by
  apply apFreeK_iUnion_of_prefix
  intro n
  induction n with
  | zero =>
    rw [prefixUnion_zero]
    intro x d hd hall; exact hall 0 (by omega)
  | succ n ih =>
    rw [prefixUnion_succ]
    cases n with
    | zero =>
      rw [prefixUnion_zero, Set.empty_union]; exact hhead
    | succ n =>
      exact core_strong hk (hW.prefix_box A hbox n) (fun x hx => (hbox (n + 1) x hx).1) ih
        (hblock n) (hW.tax n)

/-- 補題 2 の k = 4 の形：頭は 4-AP-free、ブロックは 3-AP-free（APFreeWindowSeparation の `IsThreeAPFree`）、
    倍加税だけ。これが f(4) の機械の本体。 -/
theorem lemma2_four (hW : Doubling W)
    (hbox : ∀ j, ∀ x ∈ A j, W.l j ≤ x ∧ x ≤ W.r j)
    (hhead : APFreeK 4 (A 0))
    (hblock : ∀ j, IsThreeAPFree (A (j + 1))) :
    APFreeK 4 (⋃ j, A j) :=
  lemma2_iUnion A (le_refl 4) hW hbox hhead
    (fun j => (apFreeK_three_iff _).mpr (hblock j))

end iUnion

/-! ## 4. k = 3 への帰着（Wróblewski の倍加税） -/

/-- 頭 [0, z]（実際は [1, z]）、ブロック [a, a+t] のとき、補題 1 の (i)(ii) は
    a > 2z ∧ a > z + t（`APFreeStepsSeparated.sep_M1` の前提）と同値。 -/
theorem three_conditions_iff (z t a : ℤ) :
    (2 * z < a ∧ (a + t) - a < ((3 : ℕ) - 2 : ℤ) * (a - z)) ↔ (2 * z < a ∧ z + t < a) := by
  push_cast
  constructor <;> intro h <;> constructor <;> omega

/-- 補題 1 の k = 3 の二集合版は、そのまま APFreeWindowSeparation の `IsThreeAPFree` の言明になる。 -/
theorem core_loc_three (H B : Set ℤ) (z t a : ℤ)
    (hH : ∀ x ∈ H, 0 < x ∧ x ≤ z) (hB : ∀ x ∈ B, a ≤ x ∧ x ≤ a + t)
    (hHf : IsThreeAPFree H) (hBf : IsThreeAPFree B)
    (h1 : 2 * z < a) (h2 : z + t < a) : IsThreeAPFree (H ∪ B) :=
  (apFreeK_three_iff _).mp
    (core_loc (le_refl 3) hH hB ((apFreeK_three_iff _).mpr hHf) ((apFreeK_three_iff _).mpr hBf)
      h1 (by push_cast; omega))

/-- 同じ前提から APFreeStepsSeparated の窓 `W1 z t a` の分離 (W) も出る（頭が [0,z] の形）。
    すなわち補題 1 (k=3) の前提 ＝ `sep_M1` の前提。 -/
theorem three_reduces_to_sep_M1 (z t a : ℤ) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (h : 2 * z < a ∧ (a + t) - a < ((3 : ℕ) - 2 : ℤ) * (a - z)) :
    Separated (APFree.StepsSeparated.W1 z t a) := by
  have h' := (three_conditions_iff z t a).mp h
  exact APFree.StepsSeparated.sep_M1 z t a hz ht h'.1 h'.2

/-! ## 5. (ii) は tight：k = 4、A_0 = {1}、A_1 = {3,5,7} -/

/-- (ii) が等号で破れる例：{1,3,5,7} は 4-AP。 -/
theorem tight_example : ¬ APFreeK 4 ({1, 3, 5, 7} : Set ℤ) := by
  intro h
  apply h 1 2 (by norm_num)
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi' with rfl | rfl | rfl | rfl <;> simp

/-- そのとき (ii) はちょうど等号：r − l = 4 = (4−2)(l − r_0)。 -/
theorem tight_equality : (7 : ℤ) - 3 = ((4 : ℕ) - 2 : ℤ) * (3 - 1) := by norm_num

end APFree.Nesting

/-! ### 公理の確認 -/

#print axioms APFree.Nesting.apFreeK_three_iff
#print axioms APFree.Nesting.apFreeK_of_le
#print axioms APFree.Nesting.apFreeK_mono
#print axioms APFree.Nesting.core_loc
#print axioms APFree.Nesting.core_strong
#print axioms APFree.Nesting.lemma1_iUnion
#print axioms APFree.Nesting.lemma2_iUnion
#print axioms APFree.Nesting.lemma2_four
#print axioms APFree.Nesting.three_conditions_iff
#print axioms APFree.Nesting.core_loc_three
#print axioms APFree.Nesting.three_reduces_to_sep_M1
#print axioms APFree.Nesting.tight_example
#print axioms APFree.Nesting.tight_equality
#print axioms APFree.Nesting.Doubling.prefix_box
#print axioms APFree.Nesting.apFreeK_iUnion_of_prefix
