/-

  エルデシュ問題 #169。**逆数和の挟み込みの Lean 化（骨組み＋頭 Z₀）**。

  これまで全政策に共通して残っていた唯一の「未」が、逆数和 Σ 1/n の挟み込みだった
  （Python の厳密整数演算と二系統の独立実装はあるが、Lean は 10 段まで `#eval` にとどまっていた）。
  本ファイルはその挟み込みを **Lean の定義と定理**にする。

  【設計】Python の `bracket_int` と一対一に対応させる。
    ・`BlkF p n r : Finset ℕ` — ブロック B(p,n,r) を桁の再帰で **Finset** として作る
      （`APFree.StepsMaxElement.Blk`（Set 版・論文の定義）と一致することを `coe_BlkF` で示す）
    ・`mxv p n` — n 桁（各桁 < p、底 2p−1）の最大値
    ・`loI` — 上位 d 桁を全部展開し、残りの尾は「個数 × 端の値」で押さえた
                    **整数スケール SC 倍の切り捨て下界**（Python の `rlo` と同じ。有理数の通分を避ける）
    ・`hiI` — 同じ形の切り上げ上界（Python の `rhi`）
    葉の個数は外から `cf` として与え、`cf n r ≤ (BlkF p n r).card` だけを要求する
    （下界には個数の**下からの評価**があればよい）。

  【本ファイルは骨組みだけ】数値（kernel 評価）は `APFreeBlockBoundsHeadLower`（下界）・`APFreeBlockBoundsHeadUpper`（上界）に分けた。
  一つの `lake build` を 3 分以内に収めるためである。

  【この三つ組で閉じたもの】
    **頭 Z₀ は p = 2 の Wróblewski ブロックそのものである**（`Z0_eq_block`）：
      Z₀ = 1 + B(2, 16, 0)、底 2·2−1 = 3、桁 {0,1}、T₂ ≡ 0、r = 0。
    その逆数和が
      **3.004209955304941 ≤ Σ_{n ∈ Z₀} 1/n ≤ 3.004209955304942**
    であることを機械検査した（`head_lower` / `head_upper`。葉 2¹⁶ = 65536）。

  sorry 0・native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.StepsMaxElement

namespace APFree.BlockBounds

open APFree.StepsMaxElement

set_option maxRecDepth 4000000

/-! ## 1. ブロックを Finset として作る -/

/-- `n` 桁（各桁 < p、底 2p−1）の最大値。 -/
def mxv (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (p - 1) * (2 * p - 1) ^ n + mxv p n

/-- **B(p,n,r) の Finset 版**。桁を上位から一つずつ剥がす再帰。 -/
def BlkF (p : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, r => if r = 0 then {0} else ∅
  | n + 1, r => (Finset.range p).biUnion fun k =>
      if T p k ≤ r then (BlkF p n (r - T p k)).image (fun v => k * (2 * p - 1) ^ n + v) else ∅

@[simp] theorem BlkF_zero (p r : ℕ) : BlkF p 0 r = if r = 0 then {0} else ∅ := rfl

theorem mem_BlkF_succ (p n r s : ℕ) :
    s ∈ BlkF p (n + 1) r ↔
      ∃ k < p, T p k ≤ r ∧ ∃ v ∈ BlkF p n (r - T p k), s = k * (2 * p - 1) ^ n + v := by
  constructor
  · intro h
    rw [BlkF, Finset.mem_biUnion] at h
    obtain ⟨k, hk, hmem⟩ := h
    rw [Finset.mem_range] at hk
    by_cases hT : T p k ≤ r
    · rw [if_pos hT, Finset.mem_image] at hmem
      obtain ⟨v, hv, hveq⟩ := hmem
      exact ⟨k, hk, hT, v, hv, hveq.symm⟩
    · rw [if_neg hT] at hmem; simp at hmem
  · rintro ⟨k, hk, hT, v, hv, rfl⟩
    rw [BlkF, Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [if_pos hT]
    exact Finset.mem_image_of_mem _ hv

/-! ## 2. 大きさの評価と、桁の分離 -/

theorem mxv_lt (p : ℕ) (hp : 1 ≤ p) : ∀ n, mxv p n < (2 * p - 1) ^ n := by
  intro n
  induction n with
  | zero => simp [mxv]
  | succ n ih =>
      have hb : p ≤ 2 * p - 1 := by omega
      calc mxv p (n + 1) = (p - 1) * (2 * p - 1) ^ n + mxv p n := rfl
        _ < (p - 1) * (2 * p - 1) ^ n + (2 * p - 1) ^ n := by omega
        _ = ((p - 1) + 1) * (2 * p - 1) ^ n := by ring
        _ = p * (2 * p - 1) ^ n := by congr 1; omega
        _ ≤ (2 * p - 1) * (2 * p - 1) ^ n := Nat.mul_le_mul_right _ hb
        _ = (2 * p - 1) ^ (n + 1) := by ring

/-- ブロックの元は `mxv p n` 以下。 -/
theorem BlkF_le (p : ℕ) (hp : 1 ≤ p) : ∀ (n r s : ℕ), s ∈ BlkF p n r → s ≤ mxv p n := by
  intro n
  induction n with
  | zero =>
      intro r s hs
      by_cases h : r = 0
      · rw [BlkF_zero, if_pos h, Finset.mem_singleton] at hs; simp [hs, mxv]
      · rw [BlkF_zero, if_neg h] at hs; exact absurd hs (Finset.notMem_empty s)
  | succ n ih =>
      intro r s hs
      obtain ⟨k, hk, _, v, hv, rfl⟩ := (mem_BlkF_succ p n r s).mp hs
      have h1 : v ≤ mxv p n := ih _ _ hv
      have h2 : k ≤ p - 1 := by omega
      calc k * (2 * p - 1) ^ n + v
          ≤ (p - 1) * (2 * p - 1) ^ n + mxv p n :=
            Nat.add_le_add (Nat.mul_le_mul_right _ h2) h1
        _ = mxv p (n + 1) := rfl

/-- ブロックの元は `(2p−1)^n` 未満（桁の分離に使う）。 -/
theorem BlkF_lt (p : ℕ) (hp : 1 ≤ p) (n r s : ℕ) (hs : s ∈ BlkF p n r) :
    s < (2 * p - 1) ^ n :=
  lt_of_le_of_lt (BlkF_le p hp n r s hs) (mxv_lt p hp n)

/-- 上位の桁が違えば、像は交わらない。 -/
theorem BlkF_disj (p : ℕ) (hp : 1 ≤ p) (n r : ℕ) :
    ∀ k ∈ Finset.range p, ∀ l ∈ Finset.range p, k ≠ l →
      Disjoint
        (if T p k ≤ r then (BlkF p n (r - T p k)).image (fun v => k * (2 * p - 1) ^ n + v) else ∅)
        (if T p l ≤ r then (BlkF p n (r - T p l)).image (fun v => l * (2 * p - 1) ^ n + v) else ∅) := by
  intro k _ l _ hkl
  by_cases hk : T p k ≤ r
  · by_cases hl : T p l ≤ r
    · rw [if_pos hk, if_pos hl, Finset.disjoint_left]
      rintro s hs ht
      rw [Finset.mem_image] at hs ht
      obtain ⟨v, hv, hveq⟩ := hs
      obtain ⟨w, hw, hweq⟩ := ht
      have h1 : v < (2 * p - 1) ^ n := BlkF_lt p hp _ _ _ hv
      have h2 : w < (2 * p - 1) ^ n := BlkF_lt p hp _ _ _ hw
      -- k * B + v = l * B + w、v, w < B から k = l
      have hB : 0 < (2 * p - 1) ^ n := pow_pos (by omega) n
      have key : k * (2 * p - 1) ^ n + v = l * (2 * p - 1) ^ n + w := by
        rw [hveq, hweq]
      have : k = l := by
        rcases Nat.lt_trichotomy k l with h | h | h
        · exfalso
          have : (k + 1) * (2 * p - 1) ^ n ≤ l * (2 * p - 1) ^ n :=
            Nat.mul_le_mul_right _ h
          nlinarith [key]
        · exact h
        · exfalso
          have : (l + 1) * (2 * p - 1) ^ n ≤ k * (2 * p - 1) ^ n :=
            Nat.mul_le_mul_right _ h
          nlinarith [key]
      exact hkl this
    · rw [if_neg hl]; exact disjoint_bot_right
  · rw [if_neg hk]; exact disjoint_bot_left

/-! ## 3. 個数と、和の分解 -/

theorem card_BlkF_succ (p : ℕ) (hp : 1 ≤ p) (n r : ℕ) :
    (BlkF p (n + 1) r).card
      = ∑ k ∈ Finset.range p, (if T p k ≤ r then (BlkF p n (r - T p k)).card else 0) := by
  rw [BlkF, Finset.card_biUnion (BlkF_disj p hp n r)]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hT : T p k ≤ r
  · rw [if_pos hT, if_pos hT,
      Finset.card_image_of_injective _ (fun a b hab => Nat.add_left_cancel hab)]
  · rw [if_neg hT, if_neg hT]; simp

theorem sum_BlkF_succ {M : Type*} [AddCommMonoid M] (p : ℕ) (hp : 1 ≤ p) (n r : ℕ) (f : ℕ → M) :
    ∑ s ∈ BlkF p (n + 1) r, f s
      = ∑ k ∈ Finset.range p,
          (if T p k ≤ r then ∑ v ∈ BlkF p n (r - T p k), f (k * (2 * p - 1) ^ n + v) else 0) := by
  rw [BlkF, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro k _
    by_cases hT : T p k ≤ r
    · rw [if_pos hT, if_pos hT, Finset.sum_image]
      intro a _ b _ hab; exact Nat.add_left_cancel hab
    · rw [if_neg hT, if_neg hT]; simp
  · intro k hk l hl hkl
    exact BlkF_disj p hp n r k hk l hl hkl

/-! ## 4. 挟み込みの整数版（Python の rlo / rhi と同じ形） -/

/-- 切り上げ除算。 -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

/-- **下界**（SC 倍・整数）。上位 `d` 桁を展開し、葉では「個数 × SC/(a + 尾の最大)」。 -/
def loI (p SC : ℕ) (cf : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, a, n, r => cf n r * (SC / (a + mxv p n))
  | _ + 1, a, 0, r => cf 0 r * (SC / (a + mxv p 0))
  | d + 1, a, n + 1, r =>
      ((List.range p).map fun k =>
        if T p k ≤ r then loI p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k) else 0).sum

/-- **上界**（SC 倍・整数）。葉では「個数 × ⌈SC/a⌉」。 -/
def hiI (p SC : ℕ) (cf : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, a, _n, r => cf 0 r * cdiv SC a
  | _ + 1, a, 0, r => cf 0 r * cdiv SC a
  | d + 1, a, n + 1, r =>
      ((List.range p).map fun k =>
        if T p k ≤ r then hiI p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k) else 0).sum

theorem sum_range_list (p : ℕ) (f : ℕ → ℕ) :
    ((List.range p).map f).sum = ∑ k ∈ Finset.range p, f k := by
  induction p with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

/-! ## 5. 下界の定理 -/

/-- 葉の評価：個数の下からの評価と「元は `mxv` 以下」から。 -/
theorem leaf_lower (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (c a n r : ℕ) (ha : 0 < a)
    (hc : c ≤ (BlkF p n r).card) :
    ((c * (SC / (a + mxv p n)) : ℕ) : ℚ) / SC ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) := by
  set D : ℕ := a + mxv p n with hD
  have hDpos : (0 : ℚ) < D := by positivity
  -- 各項の下からの評価
  have hterm : ∀ s ∈ BlkF p n r, (1 : ℚ) / D ≤ (1 : ℚ) / (a + s) := by
    intro s hs
    have h1 : s ≤ mxv p n := BlkF_le p hp n r s hs
    have h2 : ((a : ℚ) + s) ≤ (D : ℚ) := by
      rw [hD]; push_cast; linarith [(Nat.cast_le (α := ℚ)).mpr h1]
    have h3 : (0 : ℚ) < (a : ℚ) + s := by positivity
    exact one_div_le_one_div_of_le h3 h2
  have hsum : ((BlkF p n r).card : ℚ) * (1 / D) ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) := by
    calc ((BlkF p n r).card : ℚ) * (1 / D)
        = ∑ _s ∈ BlkF p n r, (1 : ℚ) / D := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) := Finset.sum_le_sum hterm
  -- 左辺の評価
  have hdiv : ((SC / D : ℕ) : ℚ) ≤ (SC : ℚ) / D := Nat.cast_div_le
  have hSCq : (0 : ℚ) < SC := by exact_mod_cast hSC
  have hleft : ((c * (SC / D) : ℕ) : ℚ) / SC ≤ (c : ℚ) * (1 / D) := by
    push_cast
    rw [div_le_iff₀ hSCq]
    have hcnn : (0 : ℚ) ≤ (c : ℚ) := by positivity
    calc (c : ℚ) * ((SC / D : ℕ) : ℚ) ≤ (c : ℚ) * ((SC : ℚ) / D) := by
          exact mul_le_mul_of_nonneg_left hdiv hcnn
      _ = (c : ℚ) * (1 / D) * SC := by field_simp
  have hcc : (c : ℚ) * (1 / D) ≤ ((BlkF p n r).card : ℚ) * (1 / D) := by
    have : (c : ℚ) ≤ ((BlkF p n r).card : ℚ) := by exact_mod_cast hc
    have hpos : (0 : ℚ) ≤ 1 / D := by positivity
    exact mul_le_mul_of_nonneg_right this hpos
  linarith

/-- **本定理（下界）**：`loI` を SC で割ったものは、ブロックの逆数和の下界である。 -/
theorem loI_le (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (cf : ℕ → ℕ → ℕ)
    (hcf : ∀ n r, cf n r ≤ (BlkF p n r).card) :
    ∀ (d a n r : ℕ), 0 < a →
      ((loI p SC cf d a n r : ℕ) : ℚ) / SC ≤ ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) := by
  intro d
  induction d with
  | zero =>
      intro a n r ha
      exact leaf_lower p SC hSC hp _ a n r ha (hcf n r)
  | succ d ih =>
      intro a n r ha
      match n with
      | 0 => exact leaf_lower p SC hSC hp _ a 0 r ha (hcf 0 r)
      | n + 1 =>
          rw [loI, sum_range_list, sum_BlkF_succ p hp n r]
          have hcast : ∀ x y v : ℕ,
              (1 : ℚ) / (((x + y : ℕ) : ℚ) + (v : ℚ))
                = (1 : ℚ) / ((x : ℚ) + ((y + v : ℕ) : ℚ)) := by
            intro x y v; simp only [Nat.cast_add]; ring_nf
          have key : ∀ k ∈ Finset.range p,
              ((if T p k ≤ r then loI p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k)
                else 0 : ℕ) : ℚ) / SC
                ≤ (if T p k ≤ r then
                    ∑ v ∈ BlkF p n (r - T p k),
                      (1 : ℚ) / ((a : ℚ) + ((k * (2 * p - 1) ^ n + v : ℕ) : ℚ))
                   else 0) := by
            intro k _
            by_cases hT : T p k ≤ r
            · rw [if_pos hT, if_pos hT]
              have hpos : 0 < a + k * (2 * p - 1) ^ n := by omega
              have hih := ih (a + k * (2 * p - 1) ^ n) n (r - T p k) hpos
              refine hih.trans (le_of_eq ?_)
              exact Finset.sum_congr rfl fun v _ => hcast a (k * (2 * p - 1) ^ n) v
            · rw [if_neg hT, if_neg hT]; simp
          refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
          rw [Nat.cast_sum, Finset.sum_div]

/-! ## 6. 上界の定理 -/

theorem cdiv_ge (SC a : ℕ) (ha : 0 < a) : SC ≤ cdiv SC a * a := by
  have hd := Nat.div_add_mod (SC + a - 1) a
  have hm : (SC + a - 1) % a < a := Nat.mod_lt _ ha
  have he : cdiv SC a * a = a * ((SC + a - 1) / a) := by
    unfold cdiv; exact Nat.mul_comm _ _
  rw [he]
  set Q := a * ((SC + a - 1) / a) with hQ
  set R := (SC + a - 1) % a with hR
  omega

theorem leaf_upper (p SC : ℕ) (hSC : 0 < SC) (c a r : ℕ) (ha : 0 < a)
    (hc : (BlkF p 0 r).card ≤ c) :
    ∑ s ∈ BlkF p 0 r, (1 : ℚ) / (a + s) ≤ ((c * cdiv SC a : ℕ) : ℚ) / SC := by
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hSCq : (0 : ℚ) < SC := by exact_mod_cast hSC
  by_cases hr : r = 0
  · subst hr
    rw [BlkF_zero, if_pos rfl] at hc ⊢
    rw [Finset.sum_singleton]
    simp only [Nat.cast_zero, add_zero]
    have h1 : 1 ≤ c := by simpa using hc
    have hSCa : (SC : ℚ) ≤ ((cdiv SC a : ℕ) : ℚ) * (a : ℚ) := by
      exact_mod_cast cdiv_ge SC a ha
    have step1 : (1 : ℚ) / (a : ℚ) ≤ ((cdiv SC a : ℕ) : ℚ) / (SC : ℚ) := by
      rw [div_le_div_iff₀ haq hSCq]; linarith
    have step2 : ((cdiv SC a : ℕ) : ℚ) / (SC : ℚ) ≤ ((c * cdiv SC a : ℕ) : ℚ) / (SC : ℚ) := by
      gcongr
      exact Nat.le_mul_of_pos_left _ h1
    linarith
  · rw [BlkF_zero, if_neg hr]
    simp only [Finset.sum_empty]
    positivity

/-- **本定理（上界）**：`hiI` を SC で割ったものは、ブロックの逆数和の上界である。 -/
theorem le_hiI (p SC : ℕ) (hSC : 0 < SC) (hp : 1 ≤ p) (cf : ℕ → ℕ → ℕ)
    (hcf : ∀ r, (BlkF p 0 r).card ≤ cf 0 r) :
    ∀ (d a n r : ℕ), 0 < a → n ≤ d →
      ∑ s ∈ BlkF p n r, (1 : ℚ) / (a + s) ≤ ((hiI p SC cf d a n r : ℕ) : ℚ) / SC := by
  intro d
  induction d with
  | zero =>
      intro a n r ha hnd
      have hn : n = 0 := Nat.le_zero.mp hnd
      subst hn
      exact leaf_upper p SC hSC _ a r ha (hcf r)
  | succ d ih =>
      intro a n r ha hnd
      match n with
      | 0 => exact leaf_upper p SC hSC _ a r ha (hcf r)
      | n + 1 =>
          rw [hiI, sum_range_list, sum_BlkF_succ p hp n r]
          have hcast : ∀ x y v : ℕ,
              (1 : ℚ) / ((x : ℚ) + ((y + v : ℕ) : ℚ))
                = (1 : ℚ) / (((x + y : ℕ) : ℚ) + (v : ℚ)) := by
            intro x y v; simp only [Nat.cast_add]; ring_nf
          have key : ∀ k ∈ Finset.range p,
              (if T p k ≤ r then
                  ∑ v ∈ BlkF p n (r - T p k),
                    (1 : ℚ) / ((a : ℚ) + ((k * (2 * p - 1) ^ n + v : ℕ) : ℚ))
               else 0)
                ≤ ((if T p k ≤ r then hiI p SC cf d (a + k * (2 * p - 1) ^ n) n (r - T p k)
                    else 0 : ℕ) : ℚ) / SC := by
            intro k _
            by_cases hT : T p k ≤ r
            · rw [if_pos hT, if_pos hT]
              have hpos : 0 < a + k * (2 * p - 1) ^ n := by omega
              have hle : n ≤ d := by omega
              have hih := ih (a + k * (2 * p - 1) ^ n) n (r - T p k) hpos hle
              refine le_trans (le_of_eq ?_) hih
              exact Finset.sum_congr rfl fun v _ => hcast a (k * (2 * p - 1) ^ n) v
            · rw [if_neg hT, if_neg hT]; simp
          refine le_trans (Finset.sum_le_sum key) (le_of_eq ?_)
          rw [Nat.cast_sum, Finset.sum_div]

/-! ## 7. 論文の定義との一致 -/

/-- `BlkF` は `APFree.StepsMaxElement.Blk`（論文 B(p,q,r) の Set 版）と同じものを指す。 -/
theorem coe_BlkF (p : ℕ) (hp : 1 ≤ p) : ∀ (n r : ℕ), (↑(BlkF p n r) : Set ℕ) = Blk p n r := by
  intro n
  induction n with
  | zero =>
      intro r
      ext s
      simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Finset.mem_coe, BlkF_zero, Blk]
      constructor
      · intro h
        by_cases hr : r = 0
        · subst hr
          rw [if_pos rfl, Finset.mem_singleton] at h
          exact ⟨[], rfl, by simp, by simp, by simp [valM, h]⟩
        · rw [if_neg hr] at h; exact absurd h (Finset.notMem_empty s)
      · rintro ⟨ks, hlen, _, hsum, hval⟩
        have : ks = [] := List.eq_nil_of_length_eq_zero hlen
        subst this
        simp only [List.map_nil, List.sum_nil] at hsum
        rw [if_pos hsum.symm, Finset.mem_singleton]
        simpa [valM] using hval
  | succ n ih =>
      intro r
      ext s
      simp only [Finset.mem_coe]
      rw [mem_BlkF_succ]
      constructor
      · rintro ⟨k, hk, hT, v, hv, rfl⟩
        have : v ∈ Blk p n (r - T p k) := by
          rw [← ih (r - T p k)]; exact hv
        obtain ⟨ks, hlen, hdig, hsum, hval⟩ := this
        refine ⟨k :: ks, by simp [hlen], ?_, ?_, ?_⟩
        · intro d hd; rcases List.mem_cons.mp hd with h | h
          · omega
          · exact hdig d h
        · simp only [List.map_cons, List.sum_cons, hsum]; omega
        · simp only [valM, hlen, hval]
      · rintro ⟨ks, hlen, hdig, hsum, hval⟩
        match ks, hlen with
        | k :: ks, hlen =>
          have hlen' : ks.length = n := by simpa using hlen
          have hk : k < p := hdig k (by simp)
          have hsum' : (ks.map (T p)).sum = r - T p k := by
            simp only [List.map_cons, List.sum_cons] at hsum; omega
          have hT : T p k ≤ r := by
            simp only [List.map_cons, List.sum_cons] at hsum; omega
          have hv : valM (2 * p - 1) ks ∈ BlkF p n (r - T p k) := by
            have : valM (2 * p - 1) ks ∈ Blk p n (r - T p k) :=
              ⟨ks, hlen', fun d hd => hdig d (by simp [hd]), hsum', rfl⟩
            rw [← ih (r - T p k)] at this; exact this
          exact ⟨k, hk, hT, _, hv, by simp only [valM, hlen'] at hval ⊢; exact hval⟩

/-! ## 8. 頭 Z₀ — p = 2 の Wróblewski ブロック -/

theorem T2 (k : ℕ) (hk : k < 2) : T 2 k = 0 := by
  interval_cases k <;> decide

/-- p = 2 のブロックの個数は `2^n`。 -/
theorem card_BlkF_two : ∀ n : ℕ, (BlkF 2 n 0).card = 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [card_BlkF_succ 2 (by norm_num) n 0]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      rw [T2 0 (by norm_num), T2 1 (by norm_num)]
      simp only [Nat.le_refl, if_true, Nat.sub_zero, ih]
      ring

/-- 頭の葉の個数（`cf`）。p = 2 では重みが恒等的に 0 なので `2^n`。 -/
def cfH (n r : ℕ) : ℕ := if r = 0 then 2 ^ n else 0

theorem cfH_le : ∀ n r, cfH n r ≤ (BlkF 2 n r).card := by
  intro n r
  by_cases hr : r = 0
  · subst hr; rw [cfH, if_pos rfl, card_BlkF_two]
  · rw [cfH, if_neg hr]; exact Nat.zero_le _

theorem card_BlkF_zero_le : ∀ r, (BlkF 2 0 r).card ≤ cfH 0 r := by
  intro r
  by_cases hr : r = 0
  · subst hr; simp [cfH]
  · rw [BlkF_zero, if_neg hr, cfH, if_neg hr]; simp

/-- スケール。Python の `SCALE = 10^100` と同じ。 -/
def SC : ℕ := 10 ^ 100

/-! ### 8-3. 頭 Z₀ そのものの逆数和 -/

/-- 頭 Z₀ = 1 + B(2,16,0)。 -/
def Z0F : Finset ℕ := (BlkF 2 16 0).image (fun s => 1 + s)

/-- **頭 Z₀ は p = 2 の Wróblewski ブロックである**：`Z0F = 1 + B(2,16,0)`（Set 版）。 -/
theorem Z0F_eq : (↑Z0F : Set ℕ) = (fun s => 1 + s) '' Blk 2 16 0 := by
  rw [Z0F, Finset.coe_image, coe_BlkF 2 (by norm_num) 16 0]

theorem sum_Z0F : ∑ n ∈ Z0F, (1 : ℚ) / n = ∑ s ∈ BlkF 2 16 0, (1 : ℚ) / (1 + s) := by
  rw [Z0F, Finset.sum_image]
  · exact Finset.sum_congr rfl fun s _ => by push_cast; ring_nf
  · intro a _ b _ hab; exact Nat.add_left_cancel hab

theorem Z0F_inj : Function.Injective (fun s : ℕ => 1 + s) :=
  fun a b hab => Nat.add_left_cancel hab

theorem Z0F_card : Z0F.card = 65536 := by
  rw [Z0F, Finset.card_image_of_injective _ Z0F_inj, card_BlkF_two 16]
  norm_num

end APFree.BlockBounds

/-! ### 公理の確認 -/

#print axioms APFree.BlockBounds.Z0F_eq
#print axioms APFree.BlockBounds.Z0F_card
#print axioms APFree.BlockBounds.coe_BlkF
#print axioms APFree.BlockBounds.loI_le
#print axioms APFree.BlockBounds.le_hiI
