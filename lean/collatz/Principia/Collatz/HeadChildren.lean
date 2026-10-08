/-
  頭の競争（mod 27 / mod 81）と、A_∞ の欠陥次数分解の判定式の**算術核**を機械検査する。

  記号（測度そのものの形式化はしていない）:
    u_j : Z/3^j の単位上の非負関数、d_j := min
    頭の恒等式:
      z ≡ 7 (mod 9) ⟹ u_j(z) = 4·u_j(z/4) − 3·u_{j−1}(c),  c := (z−1)/3

  本ファイルで検査するもの:
    §1 頭と子の辞書（mod 27 → mod 9）と、**凍結アドレスの言い換え**
        z ≡ −2 (mod 3^{k+1}) ⟺ c ≡ −1 (mod 3^k)
        ——「最小点の 3 進アドレスの凍結」は「引かれる子が全域最大点 −1 に 3 進的に近い」ことである。
    §2 二枝の同時制約 x₆ = 4x₄ + 1
    §3 走行分解（引き算が起きるのは類 2, 8 (mod 9) だけ／2 の位数）
    §4 欠陥次数の判定式の第一段（2^β − 1 が 3 で割れる ⟺ β 偶数）と、
        次数 1・次数 3 に妥当な軌道が無いこと
    §5 排除の論理（L(C) > d ⟹ argmin ∉ C）の Finset 版
-/
import Mathlib.Tactic

namespace Collatz.HeadChildren

/-! ### 1. 頭と子の辞書、および凍結アドレスの言い換え -/

/-- 長さ 4 の走行の頭 `z ≡ 7 (mod 9)` は `z = 3c + 1` と書ける（子 `c` が取れる）。 -/
theorem head_has_child (z : ℤ) (h : z % 9 = 7) : ∃ c : ℤ, z = 3 * c + 1 := by
  exact ⟨(z - 1) / 3, by omega⟩

/-- **辞書**：mod 27 の三つの頭 `{7, 16, 25}` は、子の mod 9 の類 `{2, 5, 8}` と一対一に対応する。 -/
theorem head_child_dictionary (z c : ℤ) (hc : z = 3 * c + 1) :
    (z % 27 = 7 ↔ c % 9 = 2) ∧ (z % 27 = 16 ↔ c % 9 = 5) ∧ (z % 27 = 25 ↔ c % 9 = 8) := by
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
    ⟨fun h => by omega, fun h => by omega⟩⟩

/-- **凍結アドレスの言い換え（本節の中心）**：
    `z ≡ −2 (mod 3^{k+1})` は `c = (z−1)/3 ≡ −1 (mod 3^k)` と同値である。
    `k = 1, 2, 3, 4` を具体化する（`3^{k+1} = 9, 27, 81, 243`）。
    ⟹ 紙の側の「最小点は `z ≡ −2 (mod 81)` に凍結」は
       **「引かれる子が全域最大点 `−1` と mod 27 まで一致する」** と同じ主張である。 -/
theorem freeze_is_child_near_minus_one (z c : ℤ) (hc : z = 3 * c + 1) :
    (z % 9 = 7 ↔ c % 3 = 2) ∧
    (z % 27 = 25 ↔ c % 9 = 8) ∧
    (z % 81 = 79 ↔ c % 27 = 26) ∧
    (z % 243 = 241 ↔ c % 81 = 80) := by
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
    ⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩⟩

/-- 検算：`−2 ≡ 7 (9)`, `−2 ≡ 25 (27)`, `−2 ≡ 79 (81)`, `−2 ≡ 241 (243)`、
    そして `−1 ≡ 2 (3)`, `−1 ≡ 8 (9)`, `−1 ≡ 26 (27)`, `−1 ≡ 80 (81)`。 -/
theorem minus_two_and_minus_one_residues :
    ((-2 : ℤ) % 9 = 7 ∧ (-2 : ℤ) % 27 = 25 ∧ (-2 : ℤ) % 81 = 79 ∧ (-2 : ℤ) % 243 = 241) ∧
    ((-1 : ℤ) % 3 = 2 ∧ (-1 : ℤ) % 9 = 8 ∧ (-1 : ℤ) % 27 = 26 ∧ (-1 : ℤ) % 81 = 80) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩⟩

/-- **紙の側の実測が示した新しい桁**：最小点は `z ≡ 79 (mod 243)` であって
    `z ≡ −2 (mod 243) = 241` ではない。この二つが異なることを機械で確認しておく
    （`79 ≡ −2 (mod 81)` だが `79 ≢ −2 (mod 243)`）。 -/
theorem seventy_nine_not_minus_two_mod_243 :
    (79 : ℤ) % 81 = (-2 : ℤ) % 81 ∧ (79 : ℤ) % 243 ≠ (-2 : ℤ) % 243 := by
  refine ⟨by decide, by decide⟩

/-! ### 2. 二枝の同時制約（紙の側） -/

/-- **同時制約**：`z ≡ 7 (mod 9)` で生きる主枝 `a = 4` と副枝 `a = 6` の落ち先
    `x₄ = (16z−1)/3`, `x₆ = (64z−1)/3` は、**`x₆ = 4·x₄ + 1`** で結ばれる。
    ⟹ 二枝は独立ではない。各々が独立に類最小を取ることは一般にできない（ここが詰まりの正体である）。 -/
theorem two_branches_linked (z x4 x6 : ℤ)
    (h4 : 3 * x4 = 16 * z - 1) (h6 : 3 * x6 = 64 * z - 1) : x6 = 4 * x4 + 1 := by omega

/-- 同じことの別表示：`3x₆ + 1 = 4·(3x₄ + 1)`（どちらも `z` の 2 冪倍である）。 -/
theorem two_branches_linked' (z x4 x6 : ℤ)
    (h4 : 3 * x4 = 16 * z - 1) (h6 : 3 * x6 = 64 * z - 1) :
    3 * x6 + 1 = 4 * (3 * x4 + 1) := by omega

/-- 枝が生きる条件：`z ≡ 7 (mod 9)` なら `x₄ ≡ 1 (mod 3)`、`x₆ ≡ 2 (mod 3)`（どちらも単位）。
    しかも `x₄` の mod 9 の類が決まれば `x₆` の類が決まる（`x₆ = 4x₄+1` から）。 -/
theorem branch_classes (z x4 x6 : ℤ) (hz : z % 9 = 7)
    (h4 : 3 * x4 = 16 * z - 1) (h6 : 3 * x6 = 64 * z - 1) :
    x4 % 3 = 1 ∧ x6 % 3 = 2 ∧
    (x4 % 9 = 1 → x6 % 9 = 5) ∧ (x4 % 9 = 4 → x6 % 9 = 8) ∧ (x4 % 9 = 7 → x6 % 9 = 2) := by
  refine ⟨by omega, by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩

/-! ### 3. 走行分解 -/

/-- 引き算が生きるのは `y ≡ 2` と `y ≡ 8 (mod 9)` の二箇所だけ（紙の側の再掲・別証明）。
    `y ≡ 5 (mod 9)` では子 `(2y−1)/3` が 3 の倍数になり、引き算が自動的に消える。 -/
theorem subtraction_sites (y : ℤ) (h : y % 3 = 2) :
    (y % 9 = 2 ∨ y % 9 = 5 ∨ y % 9 = 8) ∧ (y % 9 = 5 → (2 * y - 1) % 9 = 0) := by
  refine ⟨by omega, fun h5 => by omega⟩

/-- **走行分解**：mod 9 の 2 倍写像は単位の 6 類を一巡し、引き算は `2 → 4` と `8 → 7` の
    二箇所でだけ起きる。⟹ 巡回は **長さ 4 の走行 `7 → 5 → 1 → 2`（頭 ≡ 7）** と
    **長さ 2 の走行 `4 → 8`（頭 ≡ 4）** に割れる。 -/
theorem run_decomposition_mod_nine :
    ((2 * 7) % 9 = 5 ∧ (2 * 5) % 9 = 1 ∧ (2 * 1) % 9 = 2 ∧
     (2 * 2) % 9 = 4 ∧ (2 * 4) % 9 = 8 ∧ (2 * 8) % 9 = 7) ∧
    -- 走行の内部（引き算の無い辺）: 7→5, 5→1, 1→2 と 4→8
    (∀ y : ℤ, y % 9 = 7 ∨ y % 9 = 5 ∨ y % 9 = 1 ∨ y % 9 = 4 → y % 3 = 1 ∨ y % 9 = 5) ∧
    -- 走行の切れ目（引き算のある辺）: 2→4 と 8→7
    ((2 : ℤ) % 9 = 2 ∧ (8 : ℤ) % 9 = 8) := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun y hy => by omega, ⟨by decide, by decide⟩⟩

/-- 頭の判定：長さ 4 の走行の頭は `≡ 7 (mod 9)`、長さ 2 の走行の頭は `≡ 4 (mod 9)`。
    そして頭 `h ≡ 7 (mod 9)` に対し `h/4 ≡ 4 (mod 9)`（`4·4 = 16 ≡ 7`）。 -/
theorem head_quarter (y : ℤ) (h : y % 9 = 4) : (4 * y) % 9 = 7 := by omega

/-- 2 は `3^k` の原始根（`k = 2, 3, 4`）。位数はそれぞれ `6, 18, 54 = 2·3^{k−1}`。
    ⟹ 2 倍写像は単位全体を一本の巡回にする。 -/
theorem two_is_primitive_root :
    (2 ^ 6 % 9 = 1 ∧ 2 ^ 3 % 9 ≠ 1 ∧ 2 ^ 2 % 9 ≠ 1) ∧
    (2 ^ 18 % 27 = 1 ∧ 2 ^ 9 % 27 ≠ 1 ∧ 2 ^ 6 % 27 ≠ 1) ∧
    (2 ^ 54 % 81 = 1 ∧ 2 ^ 27 % 81 ≠ 1 ∧ 2 ^ 18 % 81 ≠ 1) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩⟩

/-! ### 4. 欠陥次数の判定式の第一段（紙の側の `c_1 = c_3 = 0`） -/

/-- `2^n mod 3` は `n` の偶奇でだけ決まる：偶数なら 1、奇数なら 2。 -/
theorem two_pow_emod_three (n : ℕ) :
    ((2 : ℤ) ^ n % 3 = 1 ∧ n % 2 = 0) ∨ ((2 : ℤ) ^ n % 3 = 2 ∧ n % 2 = 1) := by
  induction n with
  | zero => left; exact ⟨by norm_num, by norm_num⟩
  | succ k ih =>
      rw [pow_succ]
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact ⟨by omega, by omega⟩
      · left; exact ⟨by omega, by omega⟩

/-- `3` は `2` の冪を割らない。 -/
theorem three_not_dvd_two_pow (n : ℕ) : ¬ ((3 : ℤ) ∣ 2 ^ n) := by
  intro h
  have h0 := Int.emod_eq_zero_of_dvd h
  rcases two_pow_emod_three n with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- `3` は `5·2^n` を割らない（次数 3 の判定で使う）。 -/
theorem three_not_dvd_five_mul_two_pow (n : ℕ) : ¬ ((3 : ℤ) ∣ 5 * 2 ^ n) := by
  intro h
  have h0 := Int.emod_eq_zero_of_dvd h
  rcases two_pow_emod_three n with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- **判定式の第一段**：`3 ∣ 2^β − 1` ⟺ `β` は偶数。 -/
theorem three_dvd_two_pow_sub_one (b : ℕ) : (3 : ℤ) ∣ (2 ^ b - 1) ↔ b % 2 = 0 := by
  constructor
  · intro hd
    have h0 := Int.emod_eq_zero_of_dvd hd
    rcases two_pow_emod_three b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · omega
  · intro hb
    rcases two_pow_emod_three b with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Int.dvd_of_emod_eq_zero (by omega)
    · omega

/-- **系**：判定式 `Φ = 2^A·(2^β − 1) + 3·R` が `3` で割れるなら、`β` は偶数でなければならない。
    ⟹ 欠陥の並びの端（紙の側で確定した向きでは**末尾側**）の値は偶数である（`c_1 = 0` の根拠）。 -/
theorem defect_head_even (A b : ℕ) (R Φ : ℤ)
    (hΦ : Φ = 2 ^ A * (2 ^ b - 1) + 3 * R) (h3 : (3 : ℤ) ∣ Φ) : b % 2 = 0 := by
  have hd : (3 : ℤ) ∣ 2 ^ A * (2 ^ b - 1) := by
    have h' : (3 : ℤ) ∣ 3 * R := ⟨R, rfl⟩
    have := dvd_sub h3 h'
    simpa [hΦ] using this
  have hp : Prime (3 : ℤ) := by norm_num
  rcases (hp.dvd_mul.mp hd) with h | h
  · exact absurd h (three_not_dvd_two_pow A)
  · exact (three_dvd_two_pow_sub_one b).mp h

/-- **次数 1 に妥当な軌道は無い（`c_1 = 0`）**：欠陥次数 1 の分割は `β = (1)` の一つだけで、
    端の値 1 は奇数だから、判定式の第一段で落ちる。 -/
theorem c_one_is_zero (A : ℕ) (R Φ : ℤ)
    (hΦ : Φ = 2 ^ A * (2 ^ 1 - 1) + 3 * R) : ¬ ((3 : ℤ) ∣ Φ) := by
  intro h3
  have := defect_head_even A 1 R Φ hΦ h3
  omega

/-- **次数 3 に妥当な軌道は無い（`c_3 = 0`）**：偶奇の条件（**末尾側の欠陥が偶数**。
    紙の側の直接列挙で向きを確定した）を通る分割は、位置の早い順に `(1, 2)` だけである。
    このとき判定式は `Φ = 3·2^{q+1} + 3^{q−q'}·2^{q'}`（`q' < q`、`q = f₁`, `q' = 0`）の形になる。
    このとき `9 ∤ Φ` であり、要求される `3^{q+1} ∣ Φ`（`q ≥ 1` なので `9 ∣ 3^{q+1}`）は満たせない。 -/
theorem c_three_pattern_fails (q q' : ℕ) (hlt : q' < q) :
    ¬ ((9 : ℤ) ∣ (3 * 2 ^ (q + 1) + 3 ^ (q - q') * 2 ^ q')) := by
  intro h
  rcases Nat.lt_or_ge (q - q') 2 with he | he
  · -- e = 1 の場合: Φ = 15·2^{q'}
    have he1 : q - q' = 1 := by omega
    have hq : q = q' + 1 := by omega
    have hrw : (3 * 2 ^ (q + 1) + 3 ^ (q - q') * 2 ^ q' : ℤ) = 15 * 2 ^ q' := by
      rw [he1, hq]; ring
    rw [hrw] at h
    have h3 : (3 : ℤ) ∣ 5 * 2 ^ q' := by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, by linarith⟩
    exact three_not_dvd_five_mul_two_pow q' h3
  · -- e ≥ 2 の場合: 括弧の中が 3 で割れない
    obtain ⟨f, hf⟩ : ∃ f, q - q' = f + 1 := ⟨q - q' - 1, by omega⟩
    have hrw : (3 * 2 ^ (q + 1) + 3 ^ (q - q') * 2 ^ q' : ℤ)
        = 3 * (2 ^ (q + 1) + 3 ^ f * 2 ^ q') := by rw [hf]; ring
    rw [hrw] at h
    have h3 : (3 : ℤ) ∣ (2 ^ (q + 1) + 3 ^ f * 2 ^ q') := by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, by linarith⟩
    have hf1 : 1 ≤ f := by omega
    obtain ⟨g, hg⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hdvd : (3 : ℤ) ∣ 3 ^ f * 2 ^ q' := ⟨3 ^ g * 2 ^ q', by rw [hg]; ring⟩
    have h3' : (3 : ℤ) ∣ 2 ^ (q + 1) := (Int.dvd_add_right hdvd).mp (by rwa [add_comm] at h3)
    exact three_not_dvd_two_pow (q + 1) h3'

/-! ### 5. 排除の論理（紙の側の L による排除） -/

/-- **排除の補題**：類 `C` の上で `u` が二枝の和で下から押さえられ（落とした枝は非負）、
    その和の `C` 上の最小 `L` が全体の最小 `d` より真に大きいなら、**最小は `C` で取られない**。
    紙の側はこれを `L(C) := min_C [(3/16)u_{j−1}(x₄) + (3/64)u_{j−1}(x₆)]` に対して
    数値で確かめた（mod 81 の 9 類のうち 7〜8 類が排除され、残るのは常に `79 ≡ −2 (mod 81)`）。 -/
theorem exclusion_by_lower_bound {β : Type*} (C : Finset β) (hC : C.Nonempty)
    (u lo : β → ℝ) (d : ℝ)
    (hdom : ∀ b ∈ C, lo b ≤ u b)
    (hgt : d < C.inf' hC lo) :
    ∀ b ∈ C, d < u b := by
  intro b hb
  have h1 : C.inf' hC lo ≤ lo b := Finset.inf'_le _ hb
  have h2 : lo b ≤ u b := hdom b hb
  linarith

/-- 二枝が非負のとき、和は本当に下から押さえる（`u = 3Σ_a 2^{−a}u'(x_a)` の部分和）。 -/
theorem two_branch_is_lower (u4 u6 rest : ℝ) (hrest : 0 ≤ rest) :
    (3 / 16) * u4 + (3 / 64) * u6 ≤ (3 / 16) * u4 + (3 / 64) * u6 + rest := by linarith

end Collatz.HeadChildren

#print axioms Collatz.HeadChildren.head_has_child
#print axioms Collatz.HeadChildren.head_child_dictionary
#print axioms Collatz.HeadChildren.freeze_is_child_near_minus_one
#print axioms Collatz.HeadChildren.minus_two_and_minus_one_residues
#print axioms Collatz.HeadChildren.seventy_nine_not_minus_two_mod_243
#print axioms Collatz.HeadChildren.two_branches_linked
#print axioms Collatz.HeadChildren.two_branches_linked'
#print axioms Collatz.HeadChildren.branch_classes
#print axioms Collatz.HeadChildren.subtraction_sites
#print axioms Collatz.HeadChildren.run_decomposition_mod_nine
#print axioms Collatz.HeadChildren.head_quarter
#print axioms Collatz.HeadChildren.two_is_primitive_root
#print axioms Collatz.HeadChildren.two_pow_emod_three
#print axioms Collatz.HeadChildren.three_not_dvd_two_pow
#print axioms Collatz.HeadChildren.three_not_dvd_five_mul_two_pow
#print axioms Collatz.HeadChildren.three_dvd_two_pow_sub_one
#print axioms Collatz.HeadChildren.defect_head_even
#print axioms Collatz.HeadChildren.c_one_is_zero
#print axioms Collatz.HeadChildren.c_three_pattern_fails
#print axioms Collatz.HeadChildren.exclusion_by_lower_bound
#print axioms Collatz.HeadChildren.two_branch_is_lower
