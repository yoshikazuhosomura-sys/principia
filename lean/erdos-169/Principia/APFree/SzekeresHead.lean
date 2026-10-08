/-
  エルデシュ問題 #169。**頭 Z₀（Szekeres 集合）の 3-AP-free 性を Lean に入れる。**

  【なぜ要るか】
    ★91 の構成は「頭 Z₀ ∪ 平行移動したブロックたち」を段ごとに重ねたものである。
    3-AP-free 性の部品のうち
      ・各ブロック（Behrend 球面） … `APFreeNonAveraging`（p について一般）
      ・窓分離定理 (W) の一般形 … `APFreeWindowSeparation`
      ・一段の窓 M = 1, 2, 3 … `APFreeStepsSeparated`, `APFreeWindowSeparationM3`
      ・各段の t が maxelt であること … `APFreeStepsMaxElement`
    は機械検査済みだが、**頭 Z₀ だけが「未」**だった（Python の 65536² 対の全対検定のみ）。
    ここを閉じると、構成の 3-AP-free 性は全部が Lean の中に入る。

  【頭 Z₀（Szekeres 1936 / Behrend 以前の下界）】
    Python 側（`外の生成器` / `外の生成器` / `外の生成器`）の生成は
        zs = [1]; for i in 0..15: zs = zs ++ [x + 3^i for x in zs]
    すなわち Z₀ = { 1 + Σ_{i ∈ S} 3^i : S ⊆ {0,…,15} }。
    |Z₀| = 2^16 = 65536、max Z₀ = 1 + (3^16 − 1)/2 = **21523361**
    （`APFreePolicyLookahead2.steps790` / `APFreePolicyRollout.steps793` の第一段の z がこの値である）。

  【証明の骨格 —— 全列挙 decide を使わない】
    65536² 対の全列挙は Lean では重すぎる（`decide` で 4×10^9 通り）。
    そこで **3 進の桁**で議論する。n − 1 の 3 進表示の桁がすべて {0,1} であることを
        tri01 n := ∀ i, n / 3^i % 3 ≤ 1
    と書く。x + y = 2w を最下位の桁で見ると
        3·(x/3) + a + 3·(y/3) + b = 6·(w/3) + 2c, a, b, c ≤ 1
    で、a + b ≤ 2 < 3 かつ 2c ≤ 2 < 3 だから桁の繰り上がりが起きない。よって
        a + b = 2c かつ x/3 + y/3 = 2·(w/3)
    に分かれ、a, b, c ∈ {0,1} と a + b = 2c から a = b = c。あとは w について帰納する。
    ——**この議論は 16 桁に限らないので、Z₀ の大きさに依存しない。**

  sorry 0、native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.WindowSeparation

namespace APFree.SzekeresHead

/-! ## 1. 3 進表示の桁がすべて {0,1} という述語 -/

/-- `tri01 n` : n の 3 進表示に桁 2 が現れない（Szekeres 集合の特徴づけ）。 -/
def tri01 (n : ℕ) : Prop := ∀ i : ℕ, n / 3 ^ i % 3 ≤ 1

theorem tri01_zero : tri01 0 := by
  intro i; simp

/-- **分解補題**：最下位の桁とそれ以外に分かれる。 -/
theorem tri01_iff (n : ℕ) : tri01 n ↔ (n % 3 ≤ 1 ∧ tri01 (n / 3)) := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, ?_⟩
    intro i
    have h' := h (i + 1)
    have e : (3 : ℕ) * 3 ^ i = 3 ^ (i + 1) := by ring
    rw [Nat.div_div_eq_div_mul, e]
    exact h'
  · rintro ⟨h0, h1⟩ i
    cases i with
    | zero => simpa using h0
    | succ i =>
        have h' := h1 i
        have e : (3 : ℕ) * 3 ^ i = 3 ^ (i + 1) := by ring
        rw [Nat.div_div_eq_div_mul, e] at h'
        exact h'

theorem tri01_one : tri01 1 :=
  (tri01_iff 1).2 ⟨by norm_num, by norm_num; exact tri01_zero⟩

/-! ## 2. 本体：桁が {0,1} の集合は 3-AP を含まない -/

/-- 補助：`w ≤ k` についての帰納で書く（強帰納の代わり。停止が明らかになる）。 -/
theorem ap_aux : ∀ k w x y : ℕ, w ≤ k →
    tri01 x → tri01 y → tri01 w → x + y = 2 * w → x = y ∧ x = w := by
  intro k
  induction k with
  | zero =>
      intro w x y hk _ _ _ hxy
      have hw : w = 0 := Nat.le_zero.1 hk
      subst hw
      omega
  | succ k ih =>
      intro w x y hk hx hy hw hxy
      rcases Nat.eq_zero_or_pos w with h0 | hpos
      · subst h0; omega
      · obtain ⟨hx0, hx3⟩ := (tri01_iff x).1 hx
        obtain ⟨hy0, hy3⟩ := (tri01_iff y).1 hy
        obtain ⟨hw0, hw3⟩ := (tri01_iff w).1 hw
        have key : x / 3 + y / 3 = 2 * (w / 3) := by omega
        have hlt : w / 3 < w := Nat.div_lt_self hpos (by norm_num)
        have hle : w / 3 ≤ k := by omega
        obtain ⟨h1, h2⟩ := ih (w / 3) (x / 3) (y / 3) hle hx3 hy3 hw3 key
        constructor <;> omega

/-- **主定理（ℕ 版）**：3 進の桁が {0,1} だけの数の集合は 3-AP を含まない。 -/
theorem ap_of_tri01 (x y w : ℕ) (hx : tri01 x) (hy : tri01 y) (hw : tri01 w)
    (h : x + y = 2 * w) : x = y ∧ x = w :=
  ap_aux w w x y le_rfl hx hy hw h

/-! ## 3. 3^k を足す操作（倍加構成の一段） -/

/-- `x < 3^k` のとき、`x + 3^k` が桁 {0,1} であることと `x` が桁 {0,1} であることは同値。 -/
theorem tri01_add_pow : ∀ k x : ℕ, x < 3 ^ k → (tri01 (x + 3 ^ k) ↔ tri01 x) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have : x = 0 := by simpa using hx
      subst this
      have e : (0 : ℕ) + 3 ^ 0 = 1 := by norm_num
      rw [e]
      exact iff_of_true tri01_one tri01_zero
  | succ k ih =>
      intro x hx
      have hA : 0 < (3 : ℕ) ^ k := pow_pos (by norm_num) k
      have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
      have hx' : x < 3 * 3 ^ k := by rw [h3] at hx; exact hx
      have hmod : (x + 3 ^ (k + 1)) % 3 = x % 3 := by rw [h3]; omega
      have hdiv : (x + 3 ^ (k + 1)) / 3 = x / 3 + 3 ^ k := by rw [h3]; omega
      have hlt : x / 3 < 3 ^ k := by omega
      constructor
      · intro h
        obtain ⟨h0, h1⟩ := (tri01_iff _).1 h
        rw [hmod] at h0
        rw [hdiv] at h1
        exact (tri01_iff x).2 ⟨h0, (ih (x / 3) hlt).1 h1⟩
      · intro h
        obtain ⟨h0, h1⟩ := (tri01_iff x).1 h
        refine (tri01_iff _).2 ⟨?_, ?_⟩
        · rw [hmod]; exact h0
        · rw [hdiv]; exact (ih (x / 3) hlt).2 h1

/-! ## 4. Python の倍加構成そのもの -/

/-- Python の `zs = zs ++ [x + 3^i for x in zs]`（頭の 1 を引いた形）。 -/
def build : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => build k ++ (build k).map (· + 3 ^ k)

/-- **倍加構成は「3^k 未満で桁が {0,1}」の全体とちょうど一致する。** -/
theorem build_mem_iff : ∀ k n : ℕ, n ∈ build k ↔ (n < 3 ^ k ∧ tri01 n) := by
  intro k
  induction k with
  | zero =>
      intro n
      constructor
      · intro h
        have : n = 0 := by simpa [build] using h
        subst this
        exact ⟨by norm_num, tri01_zero⟩
      · rintro ⟨h, -⟩
        have : n = 0 := by simpa using h
        subst this
        simp [build]
  | succ k ih =>
      intro n
      have hA : 0 < (3 : ℕ) ^ k := pow_pos (by norm_num) k
      have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
      constructor
      · intro h
        rcases List.mem_append.1 h with h1 | h1
        · obtain ⟨hlt, htr⟩ := (ih n).1 h1
          exact ⟨by omega, htr⟩
        · obtain ⟨y, hy, hyn⟩ := List.mem_map.1 h1
          obtain ⟨hlt, htr⟩ := (ih y).1 hy
          have hn : n = y + 3 ^ k := by simpa using hyn.symm
          subst hn
          exact ⟨by omega, (tri01_add_pow k y hlt).2 htr⟩
      · rintro ⟨hlt, htr⟩
        by_cases hc : n < 3 ^ k
        · exact List.mem_append.2 (Or.inl ((ih n).2 ⟨hc, htr⟩))
        · have hc : 3 ^ k ≤ n := Nat.not_lt.1 hc
          -- 位置 k の桁は 1（2 なら tri01 に反する）
          have hq1 : 1 ≤ n / 3 ^ k := (Nat.le_div_iff_mul_le hA).2 (by omega)
          have hq3 : n / 3 ^ k < 3 := (Nat.div_lt_iff_lt_mul hA).2 (by omega)
          have hqm : n / 3 ^ k % 3 = n / 3 ^ k := Nat.mod_eq_of_lt hq3
          have hq : n / 3 ^ k = 1 := by
            have := htr k
            omega
          have hn2 : n < 2 * 3 ^ k := (Nat.div_lt_iff_lt_mul hA).1 (by omega)
          set y := n - 3 ^ k with hy
          have hyn : n = y + 3 ^ k := by omega
          have hylt : y < 3 ^ k := by omega
          have hytr : tri01 y := by
            rw [hyn] at htr
            exact (tri01_add_pow k y hylt).1 htr
          refine List.mem_append.2 (Or.inr (List.mem_map.2 ⟨y, (ih y).2 ⟨hylt, hytr⟩, ?_⟩))
          simpa using hyn.symm

theorem build_length : ∀ k : ℕ, (build k).length = 2 ^ k := by
  intro k
  induction k with
  | zero => simp [build]
  | succ k ih => simp [build, ih]; ring

/-- 倍加構成の最大元 Σ_{i<k} 3^i。 -/
def mx : ℕ → ℕ
  | 0 => 0
  | k + 1 => mx k + 3 ^ k

theorem two_mx : ∀ k : ℕ, 2 * mx k + 1 = 3 ^ k := by
  intro k
  induction k with
  | zero => simp [mx]
  | succ k ih =>
      have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
      simp only [mx, h3]
      omega

theorem mx_mem : ∀ k : ℕ, mx k ∈ build k := by
  intro k
  induction k with
  | zero => simp [build, mx]
  | succ k ih =>
      refine List.mem_append.2 (Or.inr (List.mem_map.2 ⟨mx k, ih, ?_⟩))
      simp [mx]

theorem build_le : ∀ k n : ℕ, n ∈ build k → n ≤ mx k := by
  intro k
  induction k with
  | zero => intro n h; simp [build] at h; simp [mx, h]
  | succ k ih =>
      intro n h
      have hmx : mx (k + 1) = mx k + 3 ^ k := rfl
      rcases List.mem_append.1 h with h1 | h1
      · have h2 := ih n h1
        rw [hmx]
        exact le_trans h2 (Nat.le_add_right _ _)
      · obtain ⟨y, hy, hyn⟩ := List.mem_map.1 h1
        have hle := ih y hy
        have hn : n = y + 3 ^ k := by simpa using hyn.symm
        rw [hmx, hn]
        exact Nat.add_le_add_right hle _

/-! ## 5. 頭 Z₀ そのもの -/

/-- 頭 Z₀（Python の `zs`）。 -/
def head (k : ℕ) : List ℕ := (build k).map (· + 1)

theorem head_length (k : ℕ) : (head k).length = 2 ^ k := by
  simp [head, build_length]

theorem head_mem_iff (k n : ℕ) :
    n ∈ head k ↔ (1 ≤ n ∧ n - 1 < 3 ^ k ∧ tri01 (n - 1)) := by
  constructor
  · intro h
    obtain ⟨y, hy, hyn⟩ := List.mem_map.1 h
    obtain ⟨hlt, htr⟩ := (build_mem_iff k y).1 hy
    have : n = y + 1 := by simpa using hyn.symm
    subst this
    simpa using ⟨hlt, htr⟩
  · rintro ⟨h1, h2, h3⟩
    refine List.mem_map.2 ⟨n - 1, (build_mem_iff k (n - 1)).2 ⟨h2, h3⟩, ?_⟩
    show n - 1 + 1 = n
    omega

/-- **頭は 3-AP を含まない**（ℕ の言葉で）。 -/
theorem head_apfree (k : ℕ) :
    ∀ x ∈ head k, ∀ y ∈ head k, ∀ w ∈ head k, x + y = 2 * w → x = y := by
  intro x hx y hy w hw hxyw
  obtain ⟨a, ha, hax⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, hby⟩ := List.mem_map.1 hy
  obtain ⟨c, hc, hcw⟩ := List.mem_map.1 hw
  have ex : x = a + 1 := by simpa using hax.symm
  have ey : y = b + 1 := by simpa using hby.symm
  have ew : w = c + 1 := by simpa using hcw.symm
  have hta := ((build_mem_iff k a).1 ha).2
  have htb := ((build_mem_iff k b).1 hb).2
  have htc := ((build_mem_iff k c).1 hc).2
  have habc : a + b = 2 * c := by omega
  obtain ⟨h1, -⟩ := ap_of_tri01 a b c hta htb htc habc
  omega

/-! ## 6. 実際の頭（k = 16）の数 -/

theorem pow_three_16 : (3 : ℕ) ^ 16 = 43046721 := by norm_num

theorem mx_16 : mx 16 = 21523360 := by
  have := two_mx 16
  rw [pow_three_16] at this
  omega

/-- 頭の要素数は 65536。 -/
theorem head16_card : (head 16).length = 65536 := by
  rw [head_length]; norm_num

/-- 頭の最大元は **21523361**（`APFreePolicyLookahead2.steps790` / `APFreePolicyRollout.steps793` の第一段の z）。 -/
theorem head16_max_mem : 21523361 ∈ head 16 :=
  List.mem_map.2 ⟨mx 16, mx_mem 16, by rw [mx_16]⟩

theorem head16_le (n : ℕ) (h : n ∈ head 16) : 1 ≤ n ∧ n ≤ 21523361 := by
  obtain ⟨y, hy, hyn⟩ := List.mem_map.1 h
  have hle := build_le 16 y hy
  rw [mx_16] at hle
  have : n = y + 1 := by simpa using hyn.symm
  omega

/-! ## 7. `APFreeWindowSeparation.IsThreeAPFree` の形に載せる（ℤ 版） -/

/-- 頭 Z₀ を ℤ の部分集合として書いたもの。 -/
def Z0 (k : ℕ) : Set ℤ := {x | ∃ n : ℕ, n < 3 ^ k ∧ tri01 n ∧ x = (n : ℤ) + 1}

/-- **本ファイルの結論**：頭 Z₀ は `APFreeWindowSeparation` の意味で 3-AP-free である。
    これで ★91 の構成の 3-AP-free 性の部品はすべて機械検査済みになる。 -/
theorem Z0_apfree (k : ℕ) : APFree.WindowSeparation.IsThreeAPFree (Z0 k) := by
  rintro x ⟨a, -, hta, rfl⟩ y ⟨b, -, htb, rfl⟩ z ⟨c, -, htc, rfl⟩ h
  have hac : a + c = 2 * b := by
    have : (a : ℤ) + c = 2 * b := by linarith
    exact_mod_cast this
  obtain ⟨-, h2⟩ := ap_of_tri01 a c b hta htc htb hac
  simp [h2]

/-- 実際に使う頭は k = 16。範囲は [1, 21523361]。 -/
theorem Z0_16_bounds (x : ℤ) (hx : x ∈ Z0 16) : 1 ≤ x ∧ x ≤ 21523361 := by
  obtain ⟨n, hn, htr, rfl⟩ := hx
  have h1 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have h2 : n ≤ 21523360 := by
    have hm : n ∈ build 16 := (build_mem_iff 16 n).2 ⟨hn, htr⟩
    have := build_le 16 n hm
    rw [mx_16] at this
    exact this
  have h2' : (n : ℤ) ≤ 21523360 := by exact_mod_cast h2
  constructor <;> omega

end APFree.SzekeresHead

/-! ### 公理の確認 -/

#print axioms APFree.SzekeresHead.head_apfree
#print axioms APFree.SzekeresHead.Z0_apfree
#print axioms APFree.SzekeresHead.Z0_16_bounds
#print axioms APFree.SzekeresHead.head16_card
#print axioms APFree.SzekeresHead.head16_le
#print axioms APFree.SzekeresHead.tri01_iff
#print axioms APFree.SzekeresHead.ap_of_tri01
#print axioms APFree.SzekeresHead.tri01_add_pow
#print axioms APFree.SzekeresHead.build_mem_iff
#print axioms APFree.SzekeresHead.build_length
#print axioms APFree.SzekeresHead.two_mx
#print axioms APFree.SzekeresHead.mx_16
#print axioms APFree.SzekeresHead.head16_max_mem
