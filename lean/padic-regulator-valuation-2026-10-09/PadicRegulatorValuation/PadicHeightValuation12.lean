import Mathlib

/-!
# 分裂の異常素点：`x` 座標の第二桁は形式群の第一桁である——`mod p` 高さ行列の閉じた形

前のファイル（`PadicHeightValuation11`）は、分裂の異常素点で二次の Fermat 商 `λ⁽²⁾` が
持ち上げ `x₀ ↦ x₀ + pk` について一次であり、その傾き `s` が局所量であること、
そして非対角成分が `b = s·κ/n²` と書けることの算術の段を載せた。そこに残ったのは

* `κ = (x(n(e₁+e_j)) − x(n e₁))/p` 自身の意味づけが無い、
* 高さ行列の `mod p` が結局どういう形の双線形形式なのかが書けていない、

の二点だった。本ファイルはその二点の**代数の核**を載せる。

## 何を載せたか

### 1. 第一桁の補題（`x` 座標の第二桁）

`x(P + R)` を `R` の形式群の径数 `t` の級数として見ると `Z_p[[t]]` の元で、
一次の係数は `c₁ = 2y(P) + a₁x(P) + a₃`（不変微分の分母）である。これを多項式の言明に
落とすと「Taylor の二次までの切り落とし」だけになる：

  `p² ∣ P(r + p·u) − P(r) − p·(P′(r)·u)`        (`eval_shift_first_digit`)

すなわち **`(P(r+pu) − P(r))/p ≡ P′(r)·u (mod p)`**（`first_digit_eq`）。
深さが二以上（`h = p²w`）なら差は `p²` で割れて第一桁は消える（`eval_shift_depth_two`）。
`P′(r)` が単数なら第一桁が消えるのは `u ≡ 0` のときに限る（`first_digit_ne_zero_iff`）。

### 2. 主公式の双線形代数

`χ`（還元の層）と `γ`（形式群の第一層）という**二つの一次形式**から作られる形

  `M(x,y) = A·χ(x)χ(y) + B·(χ(x)γ(y) + γ(x)χ(y))`

について、対称性・`ker χ` 上での消滅・`ker χ ∩ ker γ ⊆ rad`（ゆえに階数 ≤ 2）・
`γ = c·χ` なら階数 ≤ 1・`B ≠ 0` なら「非対角が非零 ⟺ `γ|_{ker χ} ≠ 0`」・
対角が消える比はちょうど一つ、を記帳する。

### 3. 三層目の非退化性（`r = 3`）

`Λ ⊇ Λ_0 ⊇ Λ_1` の三層に対応する形の 3×3 行列式の恒等式（`det_three_layer`）と、
そこから出る二つの言明：

* 下ブロックが階数 1（`γ` だけで書ける）なら**行列式は 0**（`det_eq_zero_of_rank_one_block`）
  ——「`Λ_0` 上の高さが形式群の深さだけで決まる」という仮説が計算と両立しないことの記帳、
* 非対角が単数で三層目の成分が `p·w` なら `p² ∣ det ⟺ p ∣ w`（`det_sq_dvd_iff`）
  ——`v_p(Reg_p) = r − 2 ⟺ 三層目で `p^{-1}h_p` が `mod p` 非退化`。

幾何（形式群の級数・不変微分・Vélu・`σ` 関数・高さの対自身）は Lean に載っていない。
載っているのは多項式の恒等式・体上の双線形代数・行列式の恒等式である。
-/

namespace PadicHeight

open Polynomial

/-! ## 1. Taylor の二次までの切り落ちと第一桁 -/

/-- `Q` から `coeff 0, 1` の部分を引くと `X²` で割れる。 -/
theorem X_pow_two_dvd_sub_trunc (Q : Polynomial ℤ) :
    (X : Polynomial ℤ) ^ 2 ∣ Q - (C (Q.coeff 0) + C (Q.coeff 1) * X) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub]
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X] <;> norm_num

/-- 評価版：`h² ∣ Q(h) − (Q₀ + Q₁h)`。 -/
theorem eval_sq_dvd (Q : Polynomial ℤ) (h : ℤ) :
    h ^ 2 ∣ Q.eval h - (Q.coeff 0 + Q.coeff 1 * h) := by
  obtain ⟨S, hS⟩ := X_pow_two_dvd_sub_trunc Q
  refine ⟨S.eval h, ?_⟩
  have := congrArg (Polynomial.eval h) hS
  simpa using this

/-- **第一桁の補題（算術の段）。** 任意の多項式 `P` と `r, u ∈ Z` で

> `p² ∣ P(r + p·u) − P(r) − p·(P′(r)·u)`。

（適用：`P = x∘τ_{P₀}` の Taylor 展開の代わりに、`x` 座標の差を `mod p²` で見る段。
一次の係数 `P′(r)` が形式群では `c₁ = 2y+a₁x+a₃` になる。） -/
theorem eval_shift_first_digit (p : ℤ) (P : Polynomial ℤ) (r u : ℤ) :
    p ^ 2 ∣ P.eval (r + p * u) - P.eval r - p * (P.derivative.eval r * u) := by
  set Q : Polynomial ℤ := P.comp (X + C r) with hQ
  have hev : ∀ h : ℤ, Q.eval h = P.eval (h + r) := by
    intro h; simp [hQ, eval_comp]
  have hQ0 : Q.coeff 0 = P.eval r := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev]; ring_nf
  have hdQ : Q.derivative = P.derivative.comp (X + C r) := by
    rw [hQ, Polynomial.derivative_comp]
    simp
  have hQ1 : Q.coeff 1 = P.derivative.eval r := by
    have h0 : Q.derivative.coeff 0 = Q.coeff 1 := by
      simpa using (Polynomial.coeff_derivative Q 0)
    have h1 : Q.derivative.coeff 0 = P.derivative.eval r := by
      rw [hdQ]
      simp [Polynomial.coeff_zero_eq_eval_zero, eval_comp]
    rw [← h0, h1]
  obtain ⟨S, hS⟩ := eval_sq_dvd Q (p * u)
  refine ⟨u ^ 2 * S, ?_⟩
  have hL : P.eval (r + p * u) = Q.eval (p * u) := by rw [hev]; ring_nf
  have hS' : Q.eval (p * u) = (Q.coeff 0 + Q.coeff 1 * (p * u)) + (p * u) ^ 2 * S := by
    linear_combination hS
  rw [hL, hS', hQ0, hQ1]
  ring

/-- 第一桁の式（`ZMod p` 版）：差が `p·k` なら `k ≡ P′(r)·u`。 -/
theorem first_digit_eq {p : ℕ} (hp : 0 < p) (P : Polynomial ℤ) (r u k d : ℤ)
    (hd : d = P.derivative.eval r)
    (hk : P.eval (r + (p : ℤ) * u) - P.eval r = (p : ℤ) * k) :
    ((k : ZMod p)) = (d : ZMod p) * (u : ZMod p) := by
  subst hd
  obtain ⟨S, hS⟩ := eval_shift_first_digit (p : ℤ) P r u
  have hps : (p : ℤ) * k - (p : ℤ) * (P.derivative.eval r * u) = (p : ℤ) ^ 2 * S := by
    rw [← hk]; linarith [hS]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdvd : (p : ℤ) ∣ k - P.derivative.eval r * u := by
    refine ⟨S, ?_⟩
    have : (p : ℤ) * (k - P.derivative.eval r * u) = (p : ℤ) * ((p : ℤ) * S) := by
      linear_combination hps
    exact mul_left_cancel₀ hp0 this
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - P.derivative.eval r * u) p).mpr hdvd
  push_cast at this
  linear_combination this

/-- 深さが二以上なら第一桁は消える：`p² ∣ P(r + p²w) − P(r)`。 -/
theorem eval_shift_depth_two (p : ℤ) (P : Polynomial ℤ) (r w : ℤ) :
    p ^ 2 ∣ P.eval (r + p ^ 2 * w) - P.eval r := by
  have h := Polynomial.sub_dvd_eval_sub (r + p ^ 2 * w) r P
  have : (r + p ^ 2 * w) - r = p ^ 2 * w := by ring
  rw [this] at h
  exact dvd_trans (Dvd.intro w rfl) h

/-- 一次の係数が単数なら、第一桁が消えるのは `u ≡ 0` のときに限る。 -/
theorem first_digit_ne_zero_iff {p : ℕ} [Fact p.Prime] (c u : ZMod p) (hc : c ≠ 0) :
    c * u ≠ 0 ↔ u ≠ 0 := by
  constructor
  · intro h hu; exact h (by rw [hu, mul_zero])
  · intro hu h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact hc h1
    · exact hu h2

/-! ## 2. 主公式——二つの一次形式から作られる形 -/

section Master

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `M(x,y) = A·χ(x)χ(y) + B·(χ(x)γ(y) + γ(x)χ(y))`。 -/
def master (A B : K) (chi gam : V →ₗ[K] K) (x y : V) : K :=
  A * chi x * chi y + B * (chi x * gam y + gam x * chi y)

theorem master_symm (A B : K) (chi gam : V →ₗ[K] K) (x y : V) :
    master A B chi gam x y = master A B chi gam y x := by
  simp only [master]; ring

theorem master_add_left (A B : K) (chi gam : V →ₗ[K] K) (x y z : V) :
    master A B chi gam (x + y) z
      = master A B chi gam x z + master A B chi gam y z := by
  simp only [master, map_add]; ring

theorem master_smul_left (A B : K) (chi gam : V →ₗ[K] K) (c : K) (x y : V) :
    master A B chi gam (c • x) y = c * master A B chi gam x y := by
  simp only [master, map_smul, smul_eq_mul]; ring

/-- `ker χ` の上では消える（定理 R_s の「超平面の上で消える」の形）。 -/
theorem master_vanish_on_ker_chi (A B : K) (chi gam : V →ₗ[K] K) {x y : V}
    (hx : chi x = 0) (hy : chi y = 0) : master A B chi gam x y = 0 := by
  simp only [master, hx, hy]; ring

/-- `ker χ ∩ ker γ` は根基に入る。ゆえに階数は `≤ 2`。 -/
theorem master_mem_radical (A B : K) (chi gam : V →ₗ[K] K) {x : V}
    (hx : chi x = 0) (hg : gam x = 0) (y : V) : master A B chi gam x y = 0 := by
  simp only [master, hx, hg]; ring

/-- `γ = c·χ` なら形は `χ ⊗ χ` の倍——階数 `≤ 1`。 -/
theorem master_eq_of_gam_eq_smul (A B c : K) (chi gam : V →ₗ[K] K)
    (h : ∀ z : V, gam z = c * chi z) (x y : V) :
    master A B chi gam x y = (A + 2 * B * c) * chi x * chi y := by
  simp only [master, h]; ring

/-- `B ≠ 0` のとき「非対角成分が生きている ⟺ `γ` が `ker χ` の上で非零」。
これが `ρ_1 = 2 ⟺ Λ_0 ⊄ E_2(Q_p)` の記帳である。 -/
theorem master_offdiag_ne_iff (A B : K) (chi gam : V →ₗ[K] K) (hB : B ≠ 0)
    {v : V} (hv : chi v = 1) :
    (∃ x, chi x = 0 ∧ gam x ≠ 0) ↔ (∃ x y, chi x = 0 ∧ master A B chi gam x y ≠ 0) := by
  constructor
  · rintro ⟨x, hx, hgx⟩
    refine ⟨x, v, hx, ?_⟩
    simp only [master, hx, hv]
    simpa using mul_ne_zero hB hgx
  · rintro ⟨x, y, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    intro hgx
    exact hxy (by simp only [master, hx, hgx]; ring)

/-- 対角成分が消える条件。`χ(x) ≠ 0` なら `A·χ(x) + 2B·γ(x) = 0` と同値。 -/
theorem master_diag_eq_zero_iff (A B : K) (chi gam : V →ₗ[K] K) {x : V}
    (hx : chi x ≠ 0) :
    master A B chi gam x x = 0 ↔ A * chi x + 2 * B * gam x = 0 := by
  have h : master A B chi gam x x = chi x * (A * chi x + 2 * B * gam x) := by
    simp only [master]; ring
  rw [h, mul_eq_zero]
  simp [hx]

/-- `2B ≠ 0` なら、対角が消える「悪い類」はちょうど一つ：`χ = 1` の上で
`M(x,x) = M(y,y) = 0` なら `γ(x) = γ(y)`。
（階数 1 で `v_p(Reg_p) ≥ 1` になるのが `p` 個の剰余類のうち**一つ**であることの記帳。） -/
theorem master_bad_class_unique (A B : K) (chi gam : V →ₗ[K] K) (hB : B ≠ 0)
    (h2 : (2 : K) ≠ 0) {x y : V} (hx : chi x = 1) (hy : chi y = 1)
    (hxx : master A B chi gam x x = 0) (hyy : master A B chi gam y y = 0) :
    gam x = gam y := by
  simp only [master, hx, hy] at hxx hyy
  have h : (2 * B) * (gam x - gam y) = 0 := by linear_combination hxx - hyy
  have h2B : (2 : K) * B ≠ 0 := mul_ne_zero h2 hB
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2B)

end Master

/-! ## 3. 三層 `Λ ⊇ Λ_0 ⊇ Λ_1` の行列式 -/

section Layers

variable {R : Type*} [CommRing R]

/-- 三層の形の 3×3 行列式の恒等式。`(1,1)` は `Λ/Λ_0` の成分、
`(2,2),(2,3),(3,3)` は `p·(p^{-1}h_p)` の成分。 -/
theorem det_three_layer (a b c p u v w : R) :
    (!![a, b, c; b, p * u, p * v; c, p * v, p * w]).det
      = p ^ 2 * a * (u * w - v ^ 2) - p * (b ^ 2 * w - 2 * b * c * v + c ^ 2 * u) := by
  simp [Matrix.det_fin_three]
  ring

/-- 下ブロックが「`γ` だけで書ける」階数 1 の形（`u = e s², v = e s t, w = e t²`）で、
非対角も同じ `γ` に比例する（`b = β s`, `c = β t`）なら、**行列式は 0**。
計算では `v_p(det) = r − 2` の枡が多数あるので、この形は起こっていない。 -/
theorem det_eq_zero_of_rank_one_block (a p e s t beta : R) :
    (!![a, beta * s, beta * t;
        beta * s, p * (e * s ^ 2), p * (e * s * t);
        beta * t, p * (e * s * t), p * (e * t ^ 2)]).det = 0 := by
  simp [Matrix.det_fin_three]
  ring

end Layers

/-- 三層目の非退化性の判定：非対角 `b` が単数、三層目の行が `p` で割れているとき

> `p² ∣ det ⟺ p ∣ w`。

すなわち **`v_p(Reg_p) = r − 2 ⟺ 三層目で `p^{-1}h_p` が `mod p` 非退化**（`r = 3` の場合）。 -/
theorem det_sq_dvd_iff {p : ℤ} (hp : Prime p) (a b c' u v w : ℤ) (hb : ¬ p ∣ b) :
    p ^ 2 ∣ (!![a, b, p * c'; b, p * u, p * v; p * c', p * v, p * w]).det
      ↔ p ∣ w := by
  have key : (!![a, b, p * c'; b, p * u, p * v; p * c', p * v, p * w]).det
      = p * (p * (a * (u * w - v ^ 2) + 2 * b * c' * v - p * c' ^ 2 * u) - b ^ 2 * w) := by
    simp [Matrix.det_fin_three]
    ring
  rw [key]
  have hp0 : p ≠ 0 := hp.ne_zero
  constructor
  · intro h
    obtain ⟨S, hS⟩ := h
    have h1 : p * (a * (u * w - v ^ 2) + 2 * b * c' * v - p * c' ^ 2 * u) - b ^ 2 * w = p * S := by
      have : p * (p * (a * (u * w - v ^ 2) + 2 * b * c' * v - p * c' ^ 2 * u) - b ^ 2 * w)
          = p * (p * S) := by rw [hS]; ring
      exact mul_left_cancel₀ hp0 this
    have h2 : p ∣ b ^ 2 * w := by
      refine ⟨(a * (u * w - v ^ 2) + 2 * b * c' * v - p * c' ^ 2 * u) - S, ?_⟩
      linarith [h1]
    rcases (hp.dvd_mul.mp h2) with h3 | h4
    · exact absurd (hp.dvd_of_dvd_pow h3) hb
    · exact h4
  · rintro ⟨W, rfl⟩
    exact ⟨a * (u * (p * W) - v ^ 2) + 2 * b * c' * v - p * c' ^ 2 * u - b ^ 2 * W, by ring⟩

end PadicHeight

#print axioms PadicHeight.eval_shift_first_digit
#print axioms PadicHeight.first_digit_eq
#print axioms PadicHeight.eval_shift_depth_two
#print axioms PadicHeight.first_digit_ne_zero_iff
#print axioms PadicHeight.master_symm
#print axioms PadicHeight.master_add_left
#print axioms PadicHeight.master_smul_left
#print axioms PadicHeight.master_vanish_on_ker_chi
#print axioms PadicHeight.master_mem_radical
#print axioms PadicHeight.master_eq_of_gam_eq_smul
#print axioms PadicHeight.master_offdiag_ne_iff
#print axioms PadicHeight.master_diag_eq_zero_iff
#print axioms PadicHeight.master_bad_class_unique
#print axioms PadicHeight.det_three_layer
#print axioms PadicHeight.det_eq_zero_of_rank_one_block
#print axioms PadicHeight.det_sq_dvd_iff
