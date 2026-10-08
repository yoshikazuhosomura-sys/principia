import Mathlib

/-!
# 非分裂のときの `p` 進高さの付値が「ちょうど 1」であることの算術

`p ≥ 5` の良通常・異常還元で、`P'` の還元が位数 `p`、`P = pP'`、`ψ = ψ_p(P')`、
`φ = φ_p(P')`、`ω = ω_p(P')` とする。Weierstrass の式を `ψ^6` 倍した関係式

```
ω² + a₁φωψ + a₃ωψ³ = φ³ + a₂φ²ψ² + a₄φψ⁴ + a₆ψ⁶
```

の右辺・左辺の差のうち、付値が `e = v_p(ψ)` しかない項は `a₁φωψ` だけである。
したがって

* `p ∣ a₁`（模型を `y ↦ y + sx` でずらして常に達成できる）なら、`e ≥ 1` だけで `ω² ≡ φ³ (mod p²)`、
* `p² ∣ ψ`（`e ≥ 2` ＝ 分裂）なら、`a₁` の条件なしに `ω² ≡ φ³ (mod p²)`

が成り立つ。ここから Fermat 商の二次・三次の比較 `2q_p(ω) = 3q_p(φ)` が出て、
`q_p(α/β) = q_p(φ) − q_p(ω) = −q_p(φ)/2 = −λ` となる。
`λ ≠ 0`（非分裂）なら `q_p(α/β) ≠ 0`、すなわち `c = v_p(A) = 1` である。
一方 `p ∣ a₁` の模型では `b = v_p(Λ_σ) ≥ 2e ≥ 2` だから、和の付値はちょうど `1` になる。

このファイルはその**算術の部分だけ**を形式化する。
除法多項式・`p` 進 `σ` 関数・Serre–Tate 理論・付値環そのものは Lean に載せていない。
（`λ = 0 ⟺ E(Q_p)[p] ≠ 0` の同値そのものは幾何を要するので、ここには無い。）
-/

namespace PadicHeight

/-! ## 1. Weierstrass の式の `mod p²` の記帳 -/

/-- `p ∣ a₁` かつ `p ∣ ψ` なら `ω² ≡ φ³ (mod p²)`。
（`e ≥ 1` だけでよい——これが先の版の `e ≥ 2` を外す一行である。） -/
theorem sq_sub_cube_dvd_of_dvd_a1 {p a1 a2 a3 a4 a6 f w ps : ℤ}
    (ha1 : p ∣ a1) (hps : p ∣ ps)
    (hW : w ^ 2 + a1 * f * w * ps + a3 * w * ps ^ 3
        = f ^ 3 + a2 * f ^ 2 * ps ^ 2 + a4 * f * ps ^ 4 + a6 * ps ^ 6) :
    p ^ 2 ∣ w ^ 2 - f ^ 3 := by
  have hps2 : p ^ 2 ∣ ps ^ 2 := pow_dvd_pow_of_dvd hps 2
  have h1 : p ^ 2 ∣ a1 * f * w * ps := by
    have : p * p ∣ a1 * ps := mul_dvd_mul ha1 hps
    rw [← sq] at this
    exact Dvd.dvd.trans this ⟨f * w, by ring⟩
  have key : w ^ 2 - f ^ 3
      = (a2 * f ^ 2) * ps ^ 2 + (a4 * f * ps ^ 2) * ps ^ 2 + (a6 * ps ^ 4) * ps ^ 2
        - a1 * f * w * ps - (a3 * w * ps) * ps ^ 2 := by linear_combination hW
  rw [key]
  exact dvd_sub (dvd_sub (dvd_add (dvd_add (hps2.mul_left _) (hps2.mul_left _))
    (hps2.mul_left _)) h1) (hps2.mul_left _)

/-- `p² ∣ ψ`（分裂＝`e ≥ 2`）なら `a₁` の条件なしに `ω² ≡ φ³ (mod p²)`。
これは先の版の定理 B が使っていた側である。 -/
theorem sq_sub_cube_dvd_of_sq_dvd_psi {p a1 a2 a3 a4 a6 f w ps : ℤ}
    (hps : p ^ 2 ∣ ps)
    (hW : w ^ 2 + a1 * f * w * ps + a3 * w * ps ^ 3
        = f ^ 3 + a2 * f ^ 2 * ps ^ 2 + a4 * f * ps ^ 4 + a6 * ps ^ 6) :
    p ^ 2 ∣ w ^ 2 - f ^ 3 := by
  have hps2 : p ^ 2 ∣ ps ^ 2 := dvd_trans hps (dvd_pow_self ps (by norm_num : (2 : ℕ) ≠ 0))
  have key : w ^ 2 - f ^ 3
      = (a2 * f ^ 2) * ps ^ 2 + (a4 * f * ps ^ 2) * ps ^ 2 + (a6 * ps ^ 4) * ps ^ 2
        - (a1 * f * w) * ps - (a3 * w * ps) * ps ^ 2 := by linear_combination hW
  rw [key]
  exact dvd_sub (dvd_sub (dvd_add (dvd_add (hps2.mul_left _) (hps2.mul_left _))
    (hps2.mul_left _)) (hps.mul_left _)) (hps2.mul_left _)

/-! ## 2. Fermat 商の二次・三次の比較 -/

/-- `p ∤ f` なら `f^{p−1} = 1 + p·a` を満たす整数 `a`（＝Fermat 商）が存在する。 -/
theorem exists_fermatQuot {p : ℕ} [Fact p.Prime] {f : ℤ} (hf : ¬ (p : ℤ) ∣ f) :
    ∃ a : ℤ, f ^ (p - 1) = 1 + (p : ℤ) * a := by
  have hf0 : (f : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hf
  have h1 : ((f ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one hf0, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  obtain ⟨a, ha⟩ := h1
  exact ⟨a, by linear_combination ha⟩

/-- `ω² ≡ φ³ (mod p²)` から Fermat 商の関係 `3a − 2b ≡ 0 (mod p)`
（`a = q_p(φ)`, `b = q_p(ω)`）。 -/
theorem dvd_three_mul_sub_two_mul {p : ℕ} {f w a b : ℤ} (hp : 0 < p)
    (hfw : (p : ℤ) ^ 2 ∣ w ^ 2 - f ^ 3)
    (hf : f ^ (p - 1) = 1 + (p : ℤ) * a) (hw : w ^ (p - 1) = 1 + (p : ℤ) * b) :
    (p : ℤ) ∣ 3 * a - 2 * b := by
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne'
  have hd : (p : ℤ) ^ 2 ∣ f ^ 3 - w ^ 2 := by
    rw [← neg_sub]; exact dvd_neg.mpr hfw
  have h1 : w ^ 2 ≡ f ^ 3 [ZMOD (p : ℤ) ^ 2] := Int.modEq_iff_dvd.mpr hd
  have h2 := h1.pow (p - 1)
  have e1 : (w ^ 2) ^ (p - 1) = (w ^ (p - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e2 : (f ^ 3) ^ (p - 1) = (f ^ (p - 1)) ^ 3 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [e1, e2, hw, hf] at h2
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h2
  have hk2 : (p : ℤ) * (3 * a - 2 * b)
      = (p : ℤ) * ((p : ℤ) * (k - (3 * a ^ 2 + (p : ℤ) * a ^ 3 - b ^ 2))) := by
    linear_combination hk
  exact ⟨_, mul_left_cancel₀ hp0 hk2⟩

/-! ## 3. `q_p(α/β) = −λ` と、その非零性 -/

/-- `2b = 3a` なら `2(a − b) = −a`。`a = 2λ` と置けば `a − b = −λ` である。 -/
theorem two_mul_sub_eq_neg {K : Type*} [CommRing K] {a b : K} (h : 2 * b = 3 * a) :
    2 * (a - b) = -a := by linear_combination -h

/-- **芯**：`λ ≠ 0` なら `q_p(α/β) = a − b ≠ 0`、すなわち `c = 1`。
（`2` が可逆である必要すらない。） -/
theorem sub_ne_zero_of_two_mul_eq_three_mul {K : Type*} [CommRing K] {a b : K}
    (h : 2 * b = 3 * a) (ha : a ≠ 0) : a - b ≠ 0 := by
  intro hab
  apply ha
  have key : 2 * (a - b) = -a := two_mul_sub_eq_neg h
  rw [hab, mul_zero] at key
  exact neg_eq_zero.mp key.symm

/-- `2` が可逆な体では `a − b = −(a/2)`。`λ = a/2` なので `q_p(α/β) = −λ` である。 -/
theorem sub_eq_neg_half {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    (h : 2 * b = 3 * a) : a - b = -(a / 2) := by
  field_simp
  linear_combination -h

/-! ## 4. 模型のずらし `y ↦ y + sx` で `p ∣ a₁` にできること -/

/-- `p` が奇（`p = 2m+1`）なら、どの `a₁` に対しても `p ∣ a₁ + 2s` なる整数 `s` がある。
`s ∈ ℤ` なので、大域極小模型は大域極小模型のままである。 -/
theorem exists_shift_dvd_a1 {p m : ℤ} (hp : p = 2 * m + 1) (a1 : ℤ) :
    ∃ s : ℤ, p ∣ a1 + 2 * s :=
  ⟨-(a1 * (m + 1)), -a1, by rw [hp]; ring⟩

/-! ## 5. 付値の和：`b ≥ 2` と `c = 1` なら和の付値はちょうど `1` -/

/-- `p² ∣ X`（＝`b ≥ 2`）かつ `p ∤ y`（＝`c = 1`）なら `X + p·y` の付値はちょうど `1`。 -/
theorem add_val_exactly_one {p X y : ℤ} (hp : p ≠ 0) (hX : p ^ 2 ∣ X) (hy : ¬ p ∣ y) :
    p ∣ X + p * y ∧ ¬ p ^ 2 ∣ X + p * y := by
  refine ⟨dvd_add (dvd_trans (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) hX) ⟨y, rfl⟩, ?_⟩
  intro hc
  apply hy
  have h1 : p ^ 2 ∣ p * y := by
    have e : p * y = (X + p * y) - X := by ring
    rw [e]; exact dvd_sub hc hX
  rw [sq] at h1
  exact (mul_dvd_mul_iff_left hp).mp h1

/-- `p` 進高さが `v_p(h_p(P)) = 1` なら `h_p(P') = h_p(P)/p²` は `Z_p` に入らない。 -/
theorem not_dvd_of_val_one {p y z : ℤ} (hp : p ≠ 0) (hy : ¬ p ∣ y) : p * y ≠ p ^ 2 * z := by
  intro h
  apply hy
  refine ⟨z, ?_⟩
  have : p * y = p * (p * z) := by rw [h]; ring
  exact mul_left_cancel₀ hp this

/-! ## 6. 高さ行列が整なら二次形式の値も整 -/

/-- 行列の全成分が部分環 `A` に入れば、格子の任意の点での二次形式の値も `A` に入る。
対偶：**ある点で `h_p ∉ Z_p` なら `M_Λ` は整でない。** -/
theorem quadratic_value_mem_of_entries_mem {R : Type*} [CommRing R] (A : Subring R)
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) (M : ι → ι → R)
    (hM : ∀ i ∈ s, ∀ j ∈ s, M i j ∈ A) :
    (∑ i ∈ s, ∑ j ∈ s, (c i : R) * (c j : R) * M i j) ∈ A := by
  refine Subring.sum_mem _ (fun i hi => Subring.sum_mem _ (fun j hj => ?_))
  exact A.mul_mem (A.mul_mem (intCast_mem A _) (intCast_mem A _)) (hM i hi j hj)

end PadicHeight

#print axioms PadicHeight.sq_sub_cube_dvd_of_dvd_a1
#print axioms PadicHeight.sq_sub_cube_dvd_of_sq_dvd_psi
#print axioms PadicHeight.exists_fermatQuot
#print axioms PadicHeight.dvd_three_mul_sub_two_mul
#print axioms PadicHeight.two_mul_sub_eq_neg
#print axioms PadicHeight.sub_ne_zero_of_two_mul_eq_three_mul
#print axioms PadicHeight.sub_eq_neg_half
#print axioms PadicHeight.exists_shift_dvd_a1
#print axioms PadicHeight.add_val_exactly_one
#print axioms PadicHeight.not_dvd_of_val_one
#print axioms PadicHeight.quadratic_value_mem_of_entries_mem
