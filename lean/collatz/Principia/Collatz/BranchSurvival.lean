/-
  Syracuse 測度 u_j の枝の生死について、紙の上で出した言明のうち有限・初等の部分を
  Lean 4 + mathlib で機械検査する。

  記号。u_j(y) は Z/3^j 上の Syracuse 測度 ν_j の正規化 u_j := 2·3^(j−1)·ν_j。
  3 の倍数のセルでは u = 0 と約束する。d_j := min_{y ≢ 0 (3)} u_j(y)。
  再帰は u_j(y) = 3 Σ_{k ≥ 1, 2^k y ≡ 1 (3)} 2^(−k) u_(j−1)((2^k y − 1)/3)。

  【1】u_m(−1) ≥ (2/3)(3/2)^m の**一般 m の証明**（紙の側は m ≤ 13 の実測だった）。
       核は二つ：(i) y = −1 では k = 1 の枝が生きている（2·(−1) ≡ 1 mod 3）、
       (ii) その子は (2(−1)−1)/3 = −1 で**自分自身**である。
       ⟹ u_j(−1) ≥ 3·2^(−1)·u_(j−1)(−1) = (3/2)u_(j−1)(−1) が全 j で成り立ち、帰納法で閉じる。

  【2】倍化恒等式 u_j(2y) = 2u_j(y) − 3·1{y ≡ 2 (3)}·u_(j−1)((2y−1)/3) の場合分けの算術核。
       y ≡ 1 (3) では k = 1 の枝が死ぬ ⟹ 引き算が無い。
       y ≡ 5 (9) では子が 3 の倍数で死ぬ。

  【3】重みを 2 倍にする単射があれば、像の側の最小はもとの側の最小の 2 倍。
       ⟹ argmin u_j は類 1 (mod 3) に閉じ込められ、さらに類 4 か 7 (mod 9) に落ちる。

  【4】射影性 ⟹ 単調性 d_(j+1) ≤ d_j の**一般ファイバー数の形**
       （紙の側はファイバーが 3 点の場合だけだった）。

  【5】A_j := u_j(−1)/(3/2)^j は単調非減少（u_j(−2) ≥ 0 から）、
       および「d_j ≥ c」⟹ A_j − A_(j−1) ≥ (c/2)(2/3)^j。
-/
import Mathlib.Tactic

namespace Collatz.BranchSurvival

/-! ### 【1】`u_m(−1) ≥ (2/3)(3/2)^m` の一般 m -/

/-- **`y = −1` では `k = 1` の枝が生きている。** 条件は `2y ≡ 1 (mod 3)`。 -/
theorem branch_one_alive_at_neg_one : ((2 : ZMod 3) * (-1)) = 1 := by decide

/-- **その枝の子は `−1` 自身である。** `x_1(y) = (2y − 1)/3` に `y = −1` を入れると `−1`。 -/
theorem child_of_neg_one : (2 * (-1 : ℤ) - 1) = 3 * (-1) := by ring

/-- 再帰の `k = 1` の項だけを残した下界（一段）。
    `u_j(−1) = 3 Σ_k 2^(−k) u_(j−1)(x_k)` の全項が非負だから、`k = 1` の項以上である。 -/
theorem step_lower (a b : ℝ) (hb : 0 ≤ b) (h : 3 * (1 / 2) * b ≤ a) : (3 / 2) * b ≤ a := by
  linarith

/-- **`u_m(−1) ≥ (2/3)(3/2)^m`（一般 `m`）。**
    仮定は「初期値が `2/3` 以上」と「一段で `3/2` 倍以上に増える」の二つだけ。
    後者は `−1` が `x_1` の不動点であることから来る（`branch_one_alive_at_neg_one` と
    `child_of_neg_one`）。紙の側は `m ≤ 13` の実測だったが、これで全 `m` に伸びる。 -/
theorem allones_lower (u : ℕ → ℝ) (h0 : (2 / 3 : ℝ) ≤ u 0)
    (hstep : ∀ m, (3 / 2 : ℝ) * u m ≤ u (m + 1)) :
    ∀ m, (2 / 3 : ℝ) * (3 / 2 : ℝ) ^ m ≤ u m := by
  intro m
  induction m with
  | zero => simpa using h0
  | succ n ih =>
    have h := hstep n
    have : (2 / 3 : ℝ) * (3 / 2 : ℝ) ^ (n + 1) = (3 / 2 : ℝ) * ((2 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) := by
      ring
    rw [this]
    have h32 : (0 : ℝ) < 3 / 2 := by norm_num
    calc (3 / 2 : ℝ) * ((2 / 3 : ℝ) * (3 / 2 : ℝ) ^ n)
        ≤ (3 / 2 : ℝ) * u n := by exact mul_le_mul_of_nonneg_left ih (le_of_lt h32)
      _ ≤ u (n + 1) := h

/-- 系：`sup_y u_m(y) ≥ (2/3)(3/2)^m`。最大点の値の下界がそのまま `L^∞` の下界になる。 -/
theorem sup_lower (u : ℕ → ℝ) (U : ℕ → ℝ) (hU : ∀ m, u m ≤ U m)
    (h0 : (2 / 3 : ℝ) ≤ u 0) (hstep : ∀ m, (3 / 2 : ℝ) * u m ≤ u (m + 1)) :
    ∀ m, (2 / 3 : ℝ) * (3 / 2 : ℝ) ^ m ≤ U m :=
  fun m => le_trans (allones_lower u h0 hstep m) (hU m)

/-! ### 【2】倍化恒等式の場合分けの算術核（紙の側の L-A / L-B / L-B'） -/

/-- `y ≡ 2 (mod 3)` なら `k = 1` の枝が生きる（引き算が起きる）。 -/
theorem branch_alive_class_two (y : ℤ) (h : y % 3 = 2) : (2 * y) % 3 = 1 := by omega

/-- **`y ≡ 1 (mod 3)` なら `k = 1` の枝は死ぬ（引き算が起きない）。**
    これが紙の側の L-B の算術的な中身である。 -/
theorem branch_dead_class_one (y : ℤ) (h : y % 3 = 1) : (2 * y) % 3 ≠ 1 := by omega

/-- **`y ≡ 5 (mod 9)` なら子 `(2y−1)/3` は 3 の倍数で死ぬ。**
    紙の側の C-102（`Λ(2r) = 2Λ(r) − 3·1{r≡2}` が `r = 5` で破れる理由）の算術核。 -/
theorem child_dies_class_five (y : ℤ) (h : y % 9 = 5) : (9 : ℤ) ∣ (2 * y - 1) := by omega

/-- mod 9 の単位類の上での 2 倍写像の軌道：`7 → 5 → 1 → 2 → 4 → 8 → 7`。
    引き算が起きる（`r ≡ 2 mod 3` かつ子が生きる）のは `2 → 4` と `8 → 7` の二箇所だけ。 -/
theorem doubling_orbit_mod_nine :
    (2 : ZMod 9) * 7 = 5 ∧ (2 : ZMod 9) * 5 = 1 ∧ (2 : ZMod 9) * 1 = 2 ∧
    (2 : ZMod 9) * 2 = 4 ∧ (2 : ZMod 9) * 4 = 8 ∧ (2 : ZMod 9) * 8 = 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **紙の側の座標変換：`z ≡ −2 (mod 3^4)` は `t := (z−1)/3` の言葉で `t ≡ −1 (mod 3^3)` と同値。**
    `−2 mod 81 = 79`、`−1 mod 27 = 26`。 -/
theorem freeze_coordinate (t : ℤ) : (3 * t + 1) % 81 = 79 ↔ t % 27 = 26 := by omega

/-! ### 【3】紙の側の本命 L-B：重みが 2 倍になる単射があれば、最小も 2 倍 -/

/-- 各点で厳密に大きい（重みが正で 2 倍になるから）。 -/
theorem lt_of_double (wt : ℝ) (h : 0 < wt) : wt < 2 * wt := by linarith

/-- **L-B（有限版）。** `σ : β → β` が `s` 上で単射で、重みをちょうど 2 倍にするなら、
    像 `s.image σ` の上の最小は `s` の上の最小のちょうど 2 倍。
    ⟹ `z ↦ 2z` を類 1 (mod 3) から類 2 (mod 3) への全単射として使えば
    `min_{z≡2} u_j = 2·min_{z≡1} u_j`、すなわち **`argmin u_j ⊂ {z ≡ 1 (mod 3)}`**。 -/
theorem min_image_double {β : Type*} [DecidableEq β] (s : Finset β) (hs : s.Nonempty)
    (σ : β → β) (wt : β → ℝ) (hσ : ∀ b ∈ s, wt (σ b) = 2 * wt b) :
    (s.image σ).inf' (hs.image σ) wt = 2 * s.inf' hs wt := by
  apply le_antisymm
  · obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' hs wt
    have hmem : σ b ∈ s.image σ := Finset.mem_image_of_mem σ hb
    calc (s.image σ).inf' (hs.image σ) wt ≤ wt (σ b) := Finset.inf'_le _ hmem
      _ = 2 * wt b := hσ b hb
      _ = 2 * s.inf' hs wt := by rw [hbeq]
  · apply Finset.le_inf'
    intro c hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    rw [hσ b hb]
    have : s.inf' hs wt ≤ wt b := Finset.inf'_le _ hb
    linarith

/-- **mod 9 の 6 単位類のうち、最小は類 7 か類 4 で取られる。**
    2 倍写像の厳密な連鎖 `7 → 5 → 1 → 2`（引き算なし）と `4 → 8`（引き算なし）から
    `m₅ = 2m₇`, `m₁ = 4m₇`, `m₂ = 8m₇`, `m₈ = 2m₄`。したがって
    類 7 は 5,1,2 を、類 4 は 8 を、それぞれ下回る。
    （実測：`m₄/m₇ ∈ [2.37, 5.50]` で、全 `j ≤ 13` で最小は類 7。） -/
theorem min_class_seven_or_four (m1 m2 m4 m5 m7 m8 : ℝ)
    (hp7 : 0 < m7) (hp4 : 0 < m4)
    (h5 : m5 = 2 * m7) (h1 : m1 = 4 * m7) (h2 : m2 = 8 * m7) (h8 : m8 = 2 * m4) :
    m7 ≤ m5 ∧ m7 ≤ m1 ∧ m7 ≤ m2 ∧ m4 ≤ m8 := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### 【4】射影性 ⟹ 単調性の一般ファイバー数の形（紙の側の一般化） -/

/-- 有限集合の重みの和が `S` なら、`S / card` 以下の元がある（紙の側の `exists_le_third` の一般化）。 -/
theorem exists_le_avg {β : Type*} (s : Finset β) (wt : β → ℝ) (S : ℝ) (n : ℕ)
    (hn : 0 < n) (hcard : s.card = n) (hsum : ∑ b ∈ s, wt b = S) :
    ∃ b ∈ s, wt b ≤ S / n := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  refine Finset.exists_le_of_sum_le hne ?_
  rw [Finset.sum_const, hcard, hsum, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_div_cancel₀ _ (ne_of_gt hn')]

/-- **射影系の最小は `1/n` 以下に落ちる（一般ファイバー数）。** -/
theorem min_le_avg {α β : Type*} [Fintype β] [DecidableEq α]
    (p : β → α) (wt : β → ℝ) (g : α → ℝ) (a₀ : α) (n : ℕ) (hn : 0 < n)
    (hcard : (Finset.univ.filter fun b => p b = a₀).card = n)
    (hsum : ∑ b ∈ Finset.univ.filter (fun b => p b = a₀), wt b = g a₀) :
    ∃ b, p b = a₀ ∧ wt b ≤ g a₀ / n := by
  obtain ⟨b, hb, hle⟩ := exists_le_avg _ wt (g a₀) n hn hcard hsum
  exact ⟨b, (Finset.mem_filter.mp hb).2, hle⟩

/-- **`d_(j+1) ≤ d_j`（一般形）。** ファイバーが `n` 点で、正規化がちょうど `n` 倍されるなら、
    最小値は非増加。紙の側は `n = 3` の場合だけだった。 -/
theorem d_antitone_gen (K : ℝ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) (a b : ℝ)
    (h : b ≤ a / n) : (n : ℝ) * K * b ≤ K * a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : (n : ℝ) * b ≤ a := by
    rw [le_div_iff₀ hn'] at h
    linarith
  nlinarith

/-! ### 【5】`A_j` の単調性と、最小値の一様下界の必要条件 -/

/-- **`A_j := u_j(−1)/(3/2)^j` は単調非減少。**
    倍化恒等式 `u_(j+1)(−2) = 2u_(j+1)(−1) − 3u_j(−1)` と密度の非負性 `u_(j+1)(−2) ≥ 0` から。
    （`a = u_(j+1)(−1)`, `b = u_j(−1)` と読む。） -/
theorem A_mono (j : ℕ) (a b : ℝ) (h : 0 ≤ 2 * a - 3 * b) :
    b / ((3 / 2 : ℝ) ^ j) ≤ a / ((3 / 2 : ℝ) ^ (j + 1)) := by
  have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ j := by positivity
  have hne : ((3 : ℝ) / 2) ^ j ≠ 0 := ne_of_gt hp
  have h2 : b ≤ 2 * a / 3 := by linarith
  calc b / ((3 / 2 : ℝ) ^ j) ≤ (2 * a / 3) / ((3 / 2 : ℝ) ^ j) := by gcongr
    _ = a / ((3 / 2 : ℝ) ^ (j + 1)) := by rw [pow_succ]; field_simp

/-- 系（紙の側）：`u_j(−1) > (3/2)u_(j−1)(−1)` の超過は `u_j(−2)/2` に等しく、
    `d_j ≤ u_j(−2)` だから**超過は `d_j/2` 以上**である。 -/
theorem excess_ge_half_d (a b d m : ℝ) (hid : m = 2 * a - 3 * b) (hd : d ≤ m) :
    (3 / 2 : ℝ) * b + d / 2 ≤ a := by
  rw [hid] at hd; linarith

/-- **最小値の一様下界（`d_j ≥ c`）の必要条件。** `d_j ≥ c` かつ `d_j ≤ 2(3/2)^j (A_j − A_(j−1))` なら
    `A_j − A_(j−1) ≥ (c/2)(2/3)^j`。
    ⟹ `A_j` が `(2/3)^j` より**速く**収束するなら `c = 0`、すなわち一様下界は取れない。
    最小値の問題が、最大点 `−1` の収束の速さの問題に翻訳される。 -/
theorem necessary_rate (j : ℕ) (c d A0 A1 : ℝ) (hc : c ≤ d)
    (h : d ≤ 2 * (3 / 2 : ℝ) ^ j * (A1 - A0)) :
    (c / 2) * ((2 / 3 : ℝ) ^ j) ≤ A1 - A0 := by
  have hkey : ((3 : ℝ) / 2) ^ j * ((2 : ℝ) / 3) ^ j = 1 := by
    rw [← mul_pow]; norm_num
  have hpos : (0 : ℝ) < ((2 : ℝ) / 3) ^ j := by positivity
  have h2 : c ≤ 2 * (3 / 2 : ℝ) ^ j * (A1 - A0) := le_trans hc h
  have hm := mul_le_mul_of_nonneg_right h2 (le_of_lt hpos)
  have hrw : 2 * ((3 : ℝ) / 2) ^ j * (A1 - A0) * ((2 : ℝ) / 3) ^ j = 2 * (A1 - A0) := by
    calc 2 * ((3 : ℝ) / 2) ^ j * (A1 - A0) * ((2 : ℝ) / 3) ^ j
        = 2 * (A1 - A0) * (((3 : ℝ) / 2) ^ j * ((2 : ℝ) / 3) ^ j) := by ring
      _ = 2 * (A1 - A0) := by rw [hkey]; ring
  rw [hrw] at hm
  have hgoal : (c / 2) * ((2 : ℝ) / 3) ^ j = (c * ((2 : ℝ) / 3) ^ j) / 2 := by ring
  rw [hgoal]
  linarith

/-- 逆向きの読み：`u_j(−2) = 2(3/2)^j (A_j − A_(j−1))` は恒等式である（代数だけ）。 -/
theorem um2_eq (j : ℕ) (a b : ℝ) :
    2 * a - 3 * b
      = 2 * ((3 / 2 : ℝ) ^ (j + 1)) * (a / ((3 / 2 : ℝ) ^ (j + 1)) - b / ((3 / 2 : ℝ) ^ j)) := by
  have hp : ((3 : ℝ) / 2) ^ j ≠ 0 := by positivity
  have hp1 : ((3 : ℝ) / 2) ^ (j + 1) ≠ 0 := by positivity
  field_simp
  rw [pow_succ]
  ring

/-! ### 依存公理の確認（`sorryAx` が無いこと） -/

#print axioms branch_one_alive_at_neg_one
#print axioms child_of_neg_one
#print axioms step_lower
#print axioms allones_lower
#print axioms sup_lower
#print axioms branch_alive_class_two
#print axioms branch_dead_class_one
#print axioms child_dies_class_five
#print axioms doubling_orbit_mod_nine
#print axioms freeze_coordinate
#print axioms lt_of_double
#print axioms min_image_double
#print axioms min_class_seven_or_four
#print axioms exists_le_avg
#print axioms min_le_avg
#print axioms d_antitone_gen
#print axioms A_mono
#print axioms excess_ge_half_d
#print axioms necessary_rate
#print axioms um2_eq

end Collatz.BranchSurvival
