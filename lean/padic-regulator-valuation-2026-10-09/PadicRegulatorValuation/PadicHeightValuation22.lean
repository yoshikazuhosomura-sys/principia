import Mathlib

/-!
# 異常素数の位数の場合分け・単数倍と付値・`σ` の係数の二つの恒等式・対数の第 `k` 項の深さ

草稿の §3.1（Hasse による `#E(F_p)` の場合分け）・§3.9（定理 R を還元の `p` 部分で読むときに要る
「`p` と互いに素な倍数は付値を動かさない」）・§3.11（`σ_p` の `t³`・`t⁴` の係数が
`c = (b₂−E₂)/12` と `a₃` にどう繋がるか）・§4 冒頭の帳簿（Iwasawa 対数の第 `k` 項の付値が
`k − v_p(k)` であること）と §4.13（`c_p` を一行にまとめる指数の算術）から、
Mathlib に載る算術だけを集める。

幾何と `p` 進解析（除法多項式・形式群・Mazur–Tate の `σ`・`p` 進高さ・Tate 曲線）は
Mathlib に無いので仮定として入る。**主定理は Lean の定理ではない。**

* `card_cases`・`two_p_forces_five`・`sq_not_dvd` : `p ≥ 5`・`p ∣ N`・Hasse の不等式から
  `N = p` または `N = 2p`、後者は `p = 5` のときだけ、どちらでも `p² ∤ N`。
* `dvd_of_unit_sq_mul`・`dvd_of_unit_mul` : `p ∤ m` なら `p^k ∣ m²a → p^k ∣ a`
  （`h_p(P) = h_p(mP)/m²` で付値が動かないこと）。
* `sigma_third_coeff`・`sigma_fourth_coeff` : `2g₁ − a₂ − (3/4)a₁² = −c` と
  `a₃ − 2g₂ = −a₁(a₁²/2 + a₂ + E₂/8)`。
* `log_term_depth`・`log_term_depth_five`・`log_term_depth_ne_five`・`log_term_small` :
  対数の第 `k` 項の深さ `k − v_p(k)`。`k = 5` が第五桁（深さ 4）に届くのは `p = 5` のときだけ。
* `cp_one_line` : `c_p = ε_p(−1)^{n+n(n+1)/2+M}n!2^{m_K+n+4M}` の指数の組み替え。
-/

namespace PadicHeight

/-! ## §1 異常素数での `#E(F_p)` の場合分け（草稿 §3.1）

Hasse の不等式は `(N − (p+1))² ≤ 4p` の形で入れる（`|a_p| ≤ 2√p` の整数版）。 -/

/-- `p ≥ 5` が `N` を割り、Hasse の不等式が成り立てば `N = p` か `N = 2p`。 -/
theorem card_cases {p N : ℕ} (hp : 5 ≤ p) (hdvd : p ∣ N)
    (hasse : ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ)) : N = p ∨ N = 2 * p := by
  obtain ⟨k, rfl⟩ := hdvd
  have hP : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hcast : ((p * k : ℕ) : ℤ) = (p : ℤ) * (k : ℤ) := by push_cast; ring
  rw [hcast] at hasse
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hasse
    push_cast at hasse
    nlinarith [hasse, hP]
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have hcon' : 3 ≤ k := by omega
    have hk3 : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hcon'
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by linarith
    have hmul : (p : ℤ) * 3 ≤ (p : ℤ) * (k : ℤ) :=
      mul_le_mul_of_nonneg_left hk3 hp0
    have h0 : (0 : ℤ) ≤ 2 * (p : ℤ) - 1 := by linarith
    have hu : 2 * (p : ℤ) - 1 ≤ (p : ℤ) * (k : ℤ) - ((p : ℤ) + 1) := by linarith
    have hu2 : (2 * (p : ℤ) - 1) ^ 2 ≤ ((p : ℤ) * (k : ℤ) - ((p : ℤ) + 1)) ^ 2 := by
      have := mul_self_le_mul_self h0 hu
      simpa [pow_two] using this
    nlinarith [hasse, hu2, hP]
  have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  interval_cases k
  · left; ring
  · right; ring

/-- `#E(F_p) = 2p` は `p = 5` のときだけ起こる。 -/
theorem two_p_forces_five {p : ℕ} (hp : 5 ≤ p)
    (hasse : ((p : ℤ) - 1) ^ 2 ≤ 4 * (p : ℤ)) : p = 5 := by
  have hP : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have h : (p : ℤ) ≤ 5 := by nlinarith [hasse, hP]
  have : p ≤ 5 := by exact_mod_cast h
  omega

/-- `N = p` でも `N = 2p` でも `p² ∤ N`（`p ≥ 5`）。したがって `p ∥ N` は自動。 -/
theorem sq_not_dvd {p N : ℕ} (hp : 5 ≤ p) (h : N = p ∨ N = 2 * p) : ¬ (p ^ 2 ∣ N) := by
  intro hdvd
  have hp0 : 0 < p := by omega
  rcases h with h | h
  · rw [h, pow_two] at hdvd
    have h1 : p * p ∣ p * 1 := by simpa using hdvd
    have : p ∣ 1 := (mul_dvd_mul_iff_left (a := p) (by omega)).mp h1
    have := Nat.le_of_dvd one_pos this
    omega
  · rw [h, pow_two] at hdvd
    have h2 : p * p ∣ p * 2 := by
      rw [mul_comm 2 p] at hdvd; exact hdvd
    have : p ∣ 2 := (mul_dvd_mul_iff_left (a := p) (by omega)).mp h2
    have := Nat.le_of_dvd two_pos this
    omega

/-! ## §2 `p` と互いに素な倍数は付値を動かさない（草稿 §3.9 の拡張）

`χ(P) = 0` のとき `mP` が `O` に還元するので補題 2 が `h_p(mP)` に当たり、
`h_p(P) = h_p(mP)/m²` から `h_p(P)` の付値が出る——その算術。 -/

/-- `p ∤ m` なら `p^k ∣ m·a` から `p^k ∣ a` が出る。 -/
theorem dvd_of_unit_mul {p : ℕ} (hp : p.Prime) {m : ℤ} (hm : ¬ ((p : ℤ) ∣ m)) :
    ∀ (k : ℕ) (a : ℤ), (p : ℤ) ^ k ∣ m * a → (p : ℤ) ^ k ∣ a := by
  have hpi : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  intro k
  induction k with
  | zero => intro a _; simp
  | succ n ih =>
      intro a h
      have hp1 : (p : ℤ) ∣ m * a := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) h
      have ha : (p : ℤ) ∣ a := by
        rcases (hpi.dvd_mul).mp hp1 with hcon | hgood
        · exact absurd hcon hm
        · exact hgood
      obtain ⟨b, rfl⟩ := ha
      have hne : ((p : ℤ)) ≠ 0 := hpi.ne_zero
      have hstep : (p : ℤ) ^ n ∣ m * b := by
        have h2 : (p : ℤ) * ((p : ℤ) ^ n) ∣ (p : ℤ) * (m * b) := by
          rw [← pow_succ']
          calc (p : ℤ) ^ (n + 1) ∣ m * ((p : ℤ) * b) := h
            _ = (p : ℤ) * (m * b) := by ring
        exact (mul_dvd_mul_iff_left hne).mp h2
      have hpow : (p : ℤ) ^ (n + 1) = (p : ℤ) * (p : ℤ) ^ n := by ring
      rw [hpow]
      exact mul_dvd_mul_left _ (ih b hstep)

/-- `p ∤ m` なら `p^k ∣ m²·a` から `p^k ∣ a` が出る（`h_p(P) = h_p(mP)/m²` の算術）。 -/
theorem dvd_of_unit_sq_mul {p : ℕ} (hp : p.Prime) {m a : ℤ} (hm : ¬ ((p : ℤ) ∣ m)) (k : ℕ)
    (h : (p : ℤ) ^ k ∣ m ^ 2 * a) : (p : ℤ) ^ k ∣ a := by
  have h1 : (p : ℤ) ^ k ∣ m * (m * a) := by
    have : m ^ 2 * a = m * (m * a) := by ring
    rwa [this] at h
  exact dvd_of_unit_mul hp hm k a (dvd_of_unit_mul hp hm k (m * a) h1)

/-! ## §3 `σ_p` の第三・第四係数（草稿 §3.11・§4 冒頭の付値表）

`σ_p(t)/t = 1 + (a₁/2)t + g₁t² + g₂t³ + ⋯` の
`g₁ = (a₁²+a₂)/3 + E₂/24`・`g₂ = (a₁³+2a₁a₂+2a₃)/4 + a₁E₂/16` に対し、
帳簿に現れる組み合わせが `c = (b₂−E₂)/12`（`b₂ = a₁²+4a₂`）で書けること。 -/

variable {K : Type*} [Field K] [CharZero K]

/-- `1/x(P″)` の係数は `2g₁ − a₂ − (3/4)a₁²` であり、これはちょうど `−c` である。 -/
theorem sigma_third_coeff (a₁ a₂ E₂ : K) :
    2 * ((a₁ ^ 2 + a₂) / 3 + E₂ / 24) - a₂ - 3 * a₁ ^ 2 / 4
      = -((a₁ ^ 2 + 4 * a₂ - E₂) / 12) := by
  field_simp
  ring

/-- `1/y(P″)` の係数は `a₃ − 2g₂` であり、これは `a₁` を因子に持つ。 -/
theorem sigma_fourth_coeff (a₁ a₂ a₃ E₂ : K) :
    a₃ - 2 * ((a₁ ^ 3 + 2 * a₁ * a₂ + 2 * a₃) / 4 + a₁ * E₂ / 16)
      = -(a₁ * (a₁ ^ 2 / 2 + a₂ + E₂ / 8)) := by
  field_simp
  ring

/-! ## §4 対数の第 `k` 項の深さ（草稿 §4 冒頭の帳簿）

`log(1+pF) = Σ_{k≥1}(−1)^{k+1}(pF)^k/k` の第 `k` 項の付値は `k − v_p(k)`。
`1/k` が `p` で割れるとその項が一桁浅くなる。第五桁（深さ 4）に届く `k` は
`k ≤ 4` と、`p = 5` のときだけ `k = 5`。 -/

/-- `p` が素数で `0 < k < p` なら `v_p(k) = 0`。 -/
theorem padicVal_eq_zero_of_lt {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hlt : k < p) :
    padicValNat p k = 0 := by
  have : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk hlt
  exact padicValNat.eq_zero_of_not_dvd this

/-- `p ≥ 5` なら `k ≤ 4` の項の深さは `k` そのもの。 -/
theorem log_term_depth_small {p k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hk : 0 < k) (hk4 : k ≤ 4) :
    k - padicValNat p k = k := by
  have : padicValNat p k = 0 := padicVal_eq_zero_of_lt hp hk (by omega)
  omega

/-- `p = 5` では第 5 項の深さは 4——第五桁に届く。 -/
theorem log_term_depth_five : 5 - padicValNat 5 5 = 4 := by
  have : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
  omega

/-- `p ≠ 5` の素数では第 5 項の深さは 5——第五桁には届かない。 -/
theorem log_term_depth_ne_five {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hne : p ≠ 5) :
    5 - padicValNat p 5 = 5 := by
  have hlt : 5 < p := by omega
  have : padicValNat p 5 = 0 := padicVal_eq_zero_of_lt hp (by norm_num) hlt
  omega

/-- 第 `k` 項の分解 `p^k/k = p^{k−v}·(1/u)`（`k = p^v·u`・`p ∤ u`）。 -/
theorem log_term_factor {p v u : ℕ} (hp : 0 < p) (hu : 0 < u) (hv : v ≤ p ^ v * u) :
    ((p : ℚ)) ^ (p ^ v * u) / ((p ^ v * u : ℕ) : ℚ)
      = (p : ℚ) ^ (p ^ v * u - v) * (1 / (u : ℚ)) := by
  have hpq : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have huq : ((u : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : ((p : ℚ)) ^ (p ^ v * u) = (p : ℚ) ^ v * (p : ℚ) ^ (p ^ v * u - v) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [hsplit]
  field_simp

/-- `p = 5`・`k = 5` の具体形：`5⁵/5 = 5⁴`。これが第五桁に立つ項 `(2/5)p⁵F⁵` の正体。 -/
theorem five_fifth_term : ((5 : ℚ)) ^ 5 / 5 = 5 ^ 4 := by norm_num

/-! ## §5 `c_p` の閉形を一行にまとめる指数の算術（草稿 §4.13・命題 16） -/

/-- `c_p = (−1)^{p·n}c_Kc_S` に `c_K = ε2^{m_K}`・`c_S = 2^nγ`・
`γ = (−1)^{n(n+1)/2}n!(−16)^M` を入れると、符号と 2 の冪が一つにまとまる。 -/
theorem cp_one_line {R : Type*} [CommRing R] {p np M mK : ℕ} (hp : p = 2 * np + 1)
    (eps gam cK cS : R)
    (hK : cK = eps * 2 ^ mK) (hS : cS = 2 ^ np * gam)
    (hg : gam = (-1) ^ (np * (np + 1) / 2) * (Nat.factorial np : R) * (-16) ^ M) :
    (-1 : R) ^ (p * np) * cK * cS
      = eps * (-1) ^ (np + np * (np + 1) / 2 + M) * (Nat.factorial np : R)
        * 2 ^ (mK + np + 4 * M) := by
  have h16 : (-16 : R) ^ M = (-1) ^ M * 2 ^ (4 * M) := by
    have h : (-16 : R) = (-1) * 2 ^ 4 := by norm_num
    rw [h, mul_pow, ← pow_mul]
  have hsign : (-1 : R) ^ (p * np) = (-1) ^ np := by
    have h : p * np = 2 * (np * np) + np := by rw [hp]; ring
    rw [h, pow_add, pow_mul]
    simp
  subst hK
  subst hS
  subst hg
  rw [h16, hsign]
  simp only [pow_add]
  ring

end PadicHeight

#print axioms PadicHeight.card_cases
#print axioms PadicHeight.two_p_forces_five
#print axioms PadicHeight.sq_not_dvd
#print axioms PadicHeight.dvd_of_unit_mul
#print axioms PadicHeight.dvd_of_unit_sq_mul
#print axioms PadicHeight.sigma_third_coeff
#print axioms PadicHeight.sigma_fourth_coeff
#print axioms PadicHeight.padicVal_eq_zero_of_lt
#print axioms PadicHeight.log_term_depth_small
#print axioms PadicHeight.log_term_depth_five
#print axioms PadicHeight.log_term_depth_ne_five
#print axioms PadicHeight.log_term_factor
#print axioms PadicHeight.five_fifth_term
#print axioms PadicHeight.cp_one_line
