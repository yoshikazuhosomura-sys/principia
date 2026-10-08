/-
  頭の補題 —
  エルデシュ問題 #169、`k = 4`。**Walker 2025 の Theorem 1.2 を Lean に入れる。**

  【主張】底 `b ≥ 2`、桁集合 `S ⊆ [0, b−1]`。`S` が **mod b で k-free**
    （公差 `Δ ≢ 0 (mod b)` の `k` 項等差数列の剰余がすべて `S` に入ることはない）ならば、
    Kempner 集合 `K(S, b)`（底 `b` の全桁が `S` に入る非負整数の全体）は `k`-AP-free。

  【証明の骨（Walker の infinite descent を公差 `d` の強い帰納にしたもの）】
    `x, x+d, …, x+(k−1)d ∈ K(S,b)`、`d > 0` とする。
    ・`b ∤ d` なら最下位桁 `(x + jd) mod b = (x + jΔ) mod b`（`Δ = d mod b ≠ 0`）が
      `S` の中の mod b の `k`-AP になる——仮定に反する。
    ・`b ∣ d` なら `d = b d'`、`(x + jd)/b = x/b + j d'` で桁を一つ落とせる。
      `K(S,b)` は「最下位桁 ∈ S かつ `n/b ∈ K`」で閉じているので、`d' < d` に帰着する。
    `APFreeSzekeresHead.Z0_apfree`（`b = 3, S = {0,1}`、3-AP）の議論を一般の `S, b, k` に上げたもの。

  【Walker の前提について】Theorem 1.2 の前提は「`S ⊊ [0,b−1]`、mod b で k-free、`0 ∈ S`」。
    ここでは `0 ∈ S` は `K` の定義（上位の空桁が 0）にだけ使い、`S ≠ [0,b−1]` は要らない
    （`S` が全部なら mod b の AP を含むので前提が空になるだけ）。整数としての AP 条件 (ii) は
    (i) から従う（`|d| < b` の整数 AP は mod b の非自明 AP）。

  sorry 0・native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.Nesting

namespace APFree.FourTermRecord

open APFree.Nesting

/-! ## 1. 「全桁が S」という述語 -/

/-- `DigIn b S n`：`n` の底 `b` の全桁が `S` に入る（Kempner 集合 `K(S,b)` の特徴づけ）。 -/
def DigIn (b : ℕ) (S : Finset ℕ) (n : ℕ) : Prop := ∀ i : ℕ, n / b ^ i % b ∈ S

/-- 分解補題：最下位桁とそれ以外に分かれる（`APFreeSzekeresHead.tri01_iff` の一般形）。 -/
theorem digIn_iff (b : ℕ) (S : Finset ℕ) (n : ℕ) :
    DigIn b S n ↔ (n % b ∈ S ∧ DigIn b S (n / b)) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    have h' := h (i + 1)
    have e : b * b ^ i = b ^ (i + 1) := by ring
    rw [Nat.div_div_eq_div_mul, e]
    exact h'
  · rintro ⟨h0, h1⟩ i
    cases i with
    | zero => simpa using h0
    | succ i =>
        have h' := h1 i
        have e : b * b ^ i = b ^ (i + 1) := by ring
        rw [Nat.div_div_eq_div_mul, e] at h'
        exact h'

theorem digIn_zero (b : ℕ) (S : Finset ℕ) (h0 : 0 ∈ S) : DigIn b S 0 := by
  intro i; simpa using h0

/-- 燃料つきの Bool 版（kernel で評価できる）。 -/
def digB (b : ℕ) (S : Finset ℕ) : ℕ → ℕ → Bool
  | 0, n => decide (n = 0)
  | f + 1, n => decide (n % b ∈ S) && digB b S f (n / b)

theorem digIn_of_digB (b : ℕ) (S : Finset ℕ) (h0 : 0 ∈ S) :
    ∀ (f n : ℕ), digB b S f n = true → DigIn b S n := by
  intro f
  induction f with
  | zero =>
      intro n h
      simp only [digB, decide_eq_true_eq] at h
      subst h; exact digIn_zero b S h0
  | succ f ih =>
      intro n h
      simp only [digB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact (digIn_iff b S n).2 ⟨h.1, ih _ h.2⟩

/-! ## 2. 「mod b で k-free」 -/

/-- `S` は mod b で非自明な `k`-AP を含まない（Walker の "k-free mod b"）。 -/
def KFreeMod (b k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ c Δ : ℕ, 0 < Δ → Δ < b → ¬ (∀ j : ℕ, j < k → (c + j * Δ) % b ∈ S)

/-- Bool 版（`c < b` に制限。`decide` が当たる先）。 -/
def kFreeModB (b k : ℕ) (S : Finset ℕ) : Bool :=
  (List.range b).all fun c => (List.range b).all fun Δ =>
    decide (Δ = 0) || !((List.range k).all fun j => decide ((c + j * Δ) % b ∈ S))

theorem kFreeMod_of_B (b k : ℕ) (S : Finset ℕ) (hb : 0 < b) (h : kFreeModB b k S = true) :
    KFreeMod b k S := by
  intro c Δ hΔ hΔb hall
  have h1 := (List.all_eq_true.mp h) (c % b) (List.mem_range.mpr (Nat.mod_lt c hb))
  have h2 := (List.all_eq_true.mp h1) Δ (List.mem_range.mpr hΔb)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_false,
    List.mem_range] at h2
  rcases h2 with h2 | ⟨j, hj, hmem⟩
  · omega
  · have := hall j hj
    apply hmem
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    exact this

/-! ## 3. 本体：`K(S,b)` は k-AP-free（ℕ の言葉で） -/

/-- **Walker の Theorem 1.2（ℕ 版）**。公差 `d` についての強い帰納。 -/
theorem no_ap_of_kFreeMod (b k : ℕ) (S : Finset ℕ) (hb : 1 < b) (hfree : KFreeMod b k S) :
    ∀ d : ℕ, 0 < d → ∀ x : ℕ, ¬ (∀ j : ℕ, j < k → DigIn b S (x + j * d)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd x hall
    by_cases hdiv : d % b = 0
    · -- b ∣ d：桁を一つ落として d/b に帰着
      have hb0 : 0 < b := by omega
      have hd' : d = b * (d / b) := by
        have := Nat.div_add_mod d b; omega
      have hdpos : 0 < d / b := by
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0, mul_zero] at hd'
        omega
      have hlt : d / b < d := Nat.div_lt_self hd hb
      apply ih (d / b) hlt hdpos (x / b)
      intro j hj
      have hj' := (digIn_iff b S _).1 (hall j hj)
      have e : (x + j * d) / b = x / b + j * (d / b) := by
        conv_lhs => rw [hd']
        have : x + j * (b * (d / b)) = x + b * (j * (d / b)) := by ring
        rw [this, Nat.add_mul_div_left _ _ hb0]
      rw [e] at hj'
      exact hj'.2
    · -- b ∤ d：最下位桁が S の中の mod b の k-AP
      have hΔ : 0 < d % b := Nat.pos_of_ne_zero hdiv
      have hΔb : d % b < b := Nat.mod_lt d (by omega)
      apply hfree x (d % b) hΔ hΔb
      intro j hj
      have hj' := ((digIn_iff b S _).1 (hall j hj)).1
      have e : (x + j * d) % b = (x + j * (d % b)) % b := by
        conv_lhs => rw [← Nat.div_add_mod d b]
        have : x + j * (b * (d / b) + d % b) = x + j * (d % b) + (j * (d / b)) * b := by ring
        rw [this, Nat.add_mul_mod_self_right]
      rw [e] at hj'
      exact hj'

/-! ## 4. ℤ の集合として：`K(S,b) + 1` は `APFreeK k` -/

/-- Kempner 集合を 1 ずらしたもの `K(S,b) + 1`（ℤ の部分集合として）。 -/
def KSet (b : ℕ) (S : Finset ℕ) : Set ℤ := {x : ℤ | ∃ n : ℕ, DigIn b S n ∧ x = (n : ℤ) + 1}

/-- **本ファイルの結論**：`S` が mod b で k-free なら `K(S,b) + 1` は k-AP-free（`k ≥ 1`）。 -/
theorem KSet_apfree (b k : ℕ) (S : Finset ℕ) (hb : 1 < b) (hk : 0 < k)
    (hfree : KFreeMod b k S) : APFreeK k (KSet b S) := by
  intro x d hd hall
  obtain ⟨n0, hn0, hx⟩ := hall 0 hk
  simp only [Nat.cast_zero, zero_mul, add_zero] at hx
  apply no_ap_of_kFreeMod b k S hb hfree d.toNat (by omega) n0
  intro j hj
  obtain ⟨nj, hnj, hxj⟩ := hall j hj
  have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have : (nj : ℤ) = ((n0 + j * d.toNat : ℕ) : ℤ) := by push_cast; rw [hdn]; omega
  have hnn : nj = n0 + j * d.toNat := by exact_mod_cast this
  rw [← hnn]; exact hnj

/-! ## 5. Walker の桁集合 `S`（`b = 55`、`|S| = 21`） -/

/-- Walker 2025, Table 1 の `k = 4` 最良の桁集合（`H(K(S,55)+1) ≈ 4.43975`）。 -/
def S55 : Finset ℕ := {0, 1, 2, 4, 5, 9, 10, 11, 14, 16, 17, 18, 21, 24, 30, 37, 39, 41, 42, 45, 47}

theorem S55_card : S55.card = 21 := by decide

theorem S55_zero : 0 ∈ S55 := by decide

theorem S55_lt : ∀ e ∈ S55, e < 55 := by decide

theorem S55_le : ∀ e ∈ S55, e ≤ 47 := by decide

/-- **(i) `S` は mod 55 で 4-free**（55 × 54 × 4 通りの kernel 評価）。 -/
theorem S55_kfree_B : kFreeModB 55 4 S55 = true := by decide +kernel

theorem S55_kfree : KFreeMod 55 4 S55 := kFreeMod_of_B 55 4 S55 (by norm_num) S55_kfree_B

/-- **`K(S,55) + 1` は 4-AP-free**。 -/
theorem KSet55_apfree : APFreeK 4 (KSet 55 S55) :=
  KSet_apfree 55 4 S55 (by norm_num) (by norm_num) S55_kfree

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.KSet55_apfree
