import Mathlib

/-!
# 二桁目の帳簿が何を決め、何を決めないか——三分類と「分けられる／分けられない」の境目

前のファイル（`PadicHeightValuation13`）は、分裂の異常素点における高さの二桁目の帳簿

  `N ≡ (1 + p)·T + 2p·Q  (mod p²)`

（`N = n²h_p(P)`・`T = Θ(x(nP))`・`Q` は点の分母の Fermat 商）の算術の段を載せ、
`p ∣ N ↔ p ∣ T` と、`T = p·T₁` のときの `p² ∣ N ↔ p ∣ T₁ + 2Q` を記帳した。

本ファイルが載せるのは、その帳簿の**射程**である。二桁目の合同式から決まるのは
`min(v_p(N), 2)` という**三分類**だけで、それ以上は決まらない。言い換えると：

* `(T, Q)` の情報は `v_p(N) = 0`・`= 1`・`≥ 2` を完全に決める（§1）。
* 二つの事例の `v_p(N)` が違っていて、**小さい方が 1 以下**なら、
  三分類は必ず違う値になる（＝二桁目の帳簿だけで二つを分けられる）(§2)。
* 逆に**両方が 2 以上**なら三分類は一致してしまい、二桁目では分けられない。
  実際、同じ `(T, Q)` を持ち `v_p(N)` が違う事例が存在する（§2 の `exists_same_data_diff_val`）。

この「境目」は計算の上で意味を持った。分裂の異常素点で `p` 進正則子の付値が違う
`Q_p` 上同型な曲線の対（導手 ≤ 20000・階数 1・`p ≤ 19` で 576 対）はすべて
小さい方の付値が 1 以下であり（実測の分布は `(0,1)` が 475・`(0,2)` が 9・`(0,3)` が 74・
`(1,2)` が 2・`(1,3)` が 16）、したがって**そのすべてが二桁目の帳簿で分けられる**。
`mod p³` が要るのは「対を分けること」ではなく「`≥ 2` の側の値そのもの」である。

§3 は模型の取り替えに関する算術の一段（二乗の段と `Q₂` の加法性）を載せる。
`w = v^{p²} ≡ 1 + p³F (mod p⁴)` から `v^{2p²} ≡ 1 + 2p³F (mod p⁴)` が出る、という部分である
（`p` 乗の二段——`v ≡ 1 + pF` から `v^{p²} ≡ 1 + p³F`——は紙のままで、本ファイルには載っていない）。
-/

namespace PadicHeight

/-! ## §1 二桁目の合同式が決める三分類 -/

section Trichotomy

variable {p N T Q : ℤ}

/-- 一桁目：`p ∣ N ↔ p ∣ T`。 -/
theorem dvd_iff_dvd_first (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) :
    p ∣ N ↔ p ∣ T := by
  have h1 : p ∣ N - ((1 + p) * T + 2 * p * Q) :=
    dvd_trans (dvd_pow_self p two_ne_zero) h
  have h2 : p ∣ N - T := by
    have e : N - T = (N - ((1 + p) * T + 2 * p * Q)) + p * (T + 2 * Q) := by ring
    rw [e]
    exact dvd_add h1 ⟨T + 2 * Q, rfl⟩
  constructor
  · intro hN
    have := dvd_sub hN h2
    simpa using this
  · intro hT
    have := dvd_add h2 hT
    simpa using this

/-- 二桁目の書き換え：`T = p·T₁` なら `p² ∣ N − p(T₁ + 2Q)`。 -/
theorem sq_dvd_sub_crit (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) {T₁ : ℤ} (hT : T = p * T₁) :
    p ^ 2 ∣ N - p * (T₁ + 2 * Q) := by
  have e : N - p * (T₁ + 2 * Q) = (N - ((1 + p) * T + 2 * p * Q)) + p ^ 2 * T₁ := by
    rw [hT]; ring
  rw [e]
  exact dvd_add h ⟨T₁, rfl⟩

/-- 二桁目（否定側）：`T = p·T₁` で `p ∤ T₁ + 2Q` なら `v_p(N) = 1`。 -/
theorem val_one_of_crit_ne (hp : Prime p)
    (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) {T₁ : ℤ} (hT : T = p * T₁)
    (hcrit : ¬ p ∣ T₁ + 2 * Q) : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
  have key := sq_dvd_sub_crit h hT
  have h1 : p ∣ N - p * (T₁ + 2 * Q) := dvd_trans (dvd_pow_self p two_ne_zero) key
  refine ⟨?_, ?_⟩
  · have := dvd_add h1 (⟨T₁ + 2 * Q, rfl⟩ : p ∣ p * (T₁ + 2 * Q))
    simpa using this
  · intro hN
    apply hcrit
    have h2 : p ^ 2 ∣ p * (T₁ + 2 * Q) := by
      have := dvd_sub hN key
      simpa using this
    obtain ⟨c, hc⟩ := h2
    refine ⟨c, ?_⟩
    have hp0 : p ≠ 0 := hp.ne_zero
    have e : p * (T₁ + 2 * Q) = p * (p * c) := by rw [hc]; ring
    exact mul_left_cancel₀ hp0 e

/-- 二桁目（肯定側）：`T = p·T₁` で `p ∣ T₁ + 2Q` なら `p² ∣ N`。 -/
theorem sq_dvd_of_crit (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) {T₁ : ℤ} (hT : T = p * T₁)
    (hcrit : p ∣ T₁ + 2 * Q) : p ^ 2 ∣ N := by
  have key := sq_dvd_sub_crit h hT
  obtain ⟨c, hc⟩ := hcrit
  have h2 : p ^ 2 ∣ p * (T₁ + 2 * Q) := by rw [hc]; exact ⟨c, by ring⟩
  have := dvd_add key h2
  simpa using this

/-- §1 のまとめ：二桁目の帳簿は `min(v_p(N), 2)` を完全に決める（三分類）。 -/
theorem trichotomy (hp : Prime p) (h : p ^ 2 ∣ N - ((1 + p) * T + 2 * p * Q)) :
    (¬ p ∣ T → ¬ p ∣ N) ∧
    (∀ T₁ : ℤ, T = p * T₁ →
      ((¬ p ∣ T₁ + 2 * Q → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧ (p ∣ T₁ + 2 * Q → p ^ 2 ∣ N))) :=
  ⟨fun hT hN => hT ((dvd_iff_dvd_first h).mp hN), fun _T₁ hT =>
    ⟨fun hc => val_one_of_crit_ne hp h hT hc, fun hc => sq_dvd_of_crit h hT hc⟩⟩

end Trichotomy

/-! ## §2 分けられる／分けられないの境目 -/

/-- 付値が違っていて小さい方が 1 以下なら、三分類（`min · 2`）も違う。 -/
theorem min_two_ne_of_ne_of_min_le_one {m n : ℕ} (hne : m ≠ n) (hmin : min m n ≤ 1) :
    min m 2 ≠ min n 2 := by
  omega

/-- 逆：両方が 2 以上なら三分類は一致する（二桁目では分けられない）。 -/
theorem min_two_eq_of_two_le {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) : min m 2 = min n 2 := by
  omega

/-- 境目の言明：三分類が違う ⟺ 付値が違い、かつ小さい方が 1 以下。 -/
theorem min_two_ne_iff {m n : ℕ} : min m 2 ≠ min n 2 ↔ (m ≠ n ∧ min m n ≤ 1) := by
  omega

/-- 二桁目の帳簿は `v_p(N) ≥ 2` の側の値を決めない：
同じ `(T, Q) = (0, 0)` を持ちながら `v_p(N)` が違う事例が実際にある。 -/
theorem exists_same_data_diff_val (p : ℤ) :
    ∃ N N' : ℤ, (p ^ 2 ∣ N - ((1 + p) * 0 + 2 * p * 0)) ∧
      (p ^ 2 ∣ N' - ((1 + p) * 0 + 2 * p * 0)) ∧ N = p ^ 2 ∧ N' = p ^ 3 := by
  refine ⟨p ^ 2, p ^ 3, ?_, ?_, rfl, rfl⟩
  · simp
  · have : p ^ 2 ∣ p ^ 3 := ⟨p, by ring⟩
    simpa using this

/-! ## §3 模型の取り替え——二乗の段 -/

/-- `w ≡ 1 + p³F (mod p⁴)` なら `w² ≡ 1 + 2p³F (mod p⁴)`。 -/
theorem scaling_shift_square {p F w : ℤ} (h : p ^ 4 ∣ w - (1 + p ^ 3 * F)) :
    p ^ 4 ∣ w ^ 2 - (1 + 2 * p ^ 3 * F) := by
  obtain ⟨S, hS⟩ := h
  have hw : w = 1 + p ^ 3 * F + p ^ 4 * S := by linarith [hS]
  refine ⟨p ^ 2 * F ^ 2 + 2 * S + 2 * p ^ 3 * F * S + p ^ 4 * S ^ 2, ?_⟩
  rw [hw]; ring

/-- `Q₂` の加法性の算術の段：`u ≡ 1`・`v ≡ 1 (mod p²)` なら
`uv − 1 ≡ (u − 1) + (v − 1) (mod p⁴)`。 -/
theorem q2_additive {p u v : ℤ} (hu : p ^ 2 ∣ u - 1) (hv : p ^ 2 ∣ v - 1) :
    p ^ 4 ∣ u * v - 1 - ((u - 1) + (v - 1)) := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hu' : u = 1 + p ^ 2 * a := by linarith [ha]
  have hv' : v = 1 + p ^ 2 * b := by linarith [hb]
  refine ⟨a * b, ?_⟩
  rw [hu', hv']; ring

end PadicHeight

#print axioms PadicHeight.dvd_iff_dvd_first
#print axioms PadicHeight.sq_dvd_sub_crit
#print axioms PadicHeight.val_one_of_crit_ne
#print axioms PadicHeight.sq_dvd_of_crit
#print axioms PadicHeight.trichotomy
#print axioms PadicHeight.min_two_ne_of_ne_of_min_le_one
#print axioms PadicHeight.min_two_eq_of_two_le
#print axioms PadicHeight.min_two_ne_iff
#print axioms PadicHeight.exists_same_data_diff_val
#print axioms PadicHeight.scaling_shift_square
#print axioms PadicHeight.q2_additive
