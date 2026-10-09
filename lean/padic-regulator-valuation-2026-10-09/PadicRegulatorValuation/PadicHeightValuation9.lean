import Mathlib

/-!
# 非分裂の異常素点での高さ行列の `mod p` の形——階数ちょうど 1

`#E(F_p) = p`・`p ∤ ∏c_ℓ`・`ι` の下で、`Λ = E(Q)/tors`（階数 `r`）、
`Λ_0 = ker(Λ → E(F_p))`、`χ : Λ → E(F_p) ≅ Z/p` を還元とする。既に紙にある二つの事実

* `P ∈ Λ_0` なら `v_p(h_p(P)) ≥ 1`（補題 2）、
* **非分裂**（`E(Q_p)[p] = 0`）なら `P ∈ Λ∖Λ_0` で `v_p(h_p(P)) = −1` ちょうど（定理 S）

を合わせると、`Q(P) := p·h_p(P)` は `Λ` 上の `Z_p` 値二次形式で、
その `mod p` の零点集合がちょうど超平面 `Λ_0/pΛ` になる。
本ファイルの主定理 `bilin_rank_one_of_zero_iff` は、そこから

> 標数 `≠ 2` の体上で、対称双線形形式 `B` の二次形式 `x ↦ B x x` の零点集合が
> ちょうど線形形式 `χ` の核であれば、`B = c·χ⊗χ`（`c ≠ 0`）である

を示す。ゆえに `p·M_Λ mod p` は**階数ちょうど 1** の行列 `c·χχᵗ` であり、
成分ごとの付値が確定する（`v_p(h_p(P_i,P_j)) = −1 ⟺ χ_iχ_j ≠ 0`）。

残りの二定理は行列式の記帳である。`χ = (1,0,…,0)` となる `Λ` の基底を取ると
`A := p·M_Λ` は `A = D A' D`（`D = diag(1,p,…,p)`・`A'` 整）の形になり、
`det A = p^{2(r−1)} det A'` と `det A = p^r Reg_p` から `Reg_p = p^{r−2} det A'` が出る。

幾何・`p` 進解析（`σ` 関数・除法多項式・定理 S 自身）は Lean に載っていない。
載っているのは**線形代数と行列式の記帳**である。
-/

namespace PadicHeight

/-! ## 1. 二次形式の零点集合が超平面なら、双線形形式は階数 1 -/

/-- **主定理。** 標数 `≠ 2` の体上のベクトル空間 `V` 上の対称双線形形式 `B` について、
`B x x = 0 ⟺ χ x = 0`（`χ` は線形形式・`χ v = 1`）ならば、
`c := B v v ≠ 0` で `B x y = c · χ x · χ y` である。
（適用：`B = p·h_p mod p`、`χ` は還元指標。非分裂のとき `p·M_Λ mod p = c·χχᵗ`。） -/
theorem bilin_rank_one_of_zero_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (B : V →ₗ[K] V →ₗ[K] K) (hsymm : ∀ x y, B x y = B y x)
    (χ : V →ₗ[K] K) (v : V) (hv : χ v = 1)
    (hzero : ∀ x, B x x = 0 ↔ χ x = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ x y, B x y = c * χ x * χ y := by
  have haddL : ∀ x y z : V, B (x + y) z = B x z + B y z := by intro x y z; simp
  have haddR : ∀ x y z : V, B x (y + z) = B x y + B x z := by intro x y z; simp
  -- 核の上では二次形式は消える
  have hW : ∀ w : V, χ w = 0 → B w w = 0 := fun w hw => (hzero w).2 hw
  -- 核の上では双線形形式そのものが消える（標数 ≠ 2）
  have hWW : ∀ w w' : V, χ w = 0 → χ w' = 0 → B w w' = 0 := by
    intro w w' hw hw'
    have hs : χ (w + w') = 0 := by simp [hw, hw']
    have h0 : B (w + w') (w + w') = 0 := hW _ hs
    rw [haddL, haddR, haddR, hW w hw, hW w' hw', hsymm w' w] at h0
    have h2b : (2 : K) * B w w' = 0 := by linear_combination h0
    rcases mul_eq_zero.1 h2b with h | h
    · exact absurd h h2
    · exact h
  -- 核と v は直交する
  have hWv : ∀ w : V, χ w = 0 → B w v = 0 := by
    intro w hw
    by_contra hne
    have hww : B w w = 0 := hW w hw
    have hvw : B v w = B w v := hsymm v w
    obtain ⟨s, hs⟩ : ∃ s : K, 2 * B w v * s + B v v = 0 :=
      ⟨-(B v v) / (2 * B w v), by field_simp; ring⟩
    have hx : χ (s • w + v) = 1 := by simp [hw, hv]
    have hBne : B (s • w + v) (s • w + v) ≠ 0 := by
      intro h
      have h1 := (hzero _).1 h
      rw [hx] at h1
      exact one_ne_zero h1
    have hexp : B (s • w + v) (s • w + v) = 2 * B w v * s + B v v := by
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hww, hvw]
      ring
    exact hBne (by rw [hexp, hs])
  have hc : B v v ≠ 0 := by
    intro h
    have h1 := (hzero v).1 h
    rw [hv] at h1
    exact one_ne_zero h1
  refine ⟨B v v, hc, ?_⟩
  intro x y
  have hwx : χ (x - χ x • v) = 0 := by simp [hv]
  have hwy : χ (y - χ y • v) = 0 := by simp [hv]
  have hxy0 : B (x - χ x • v) (y - χ y • v) = 0 := hWW _ _ hwx hwy
  have h1 : B (x - χ x • v) v = 0 := hWv _ hwx
  have h2' : B (y - χ y • v) v = 0 := hWv _ hwy
  have h3 : B v (y - χ y • v) = 0 := by rw [hsymm]; exact h2'
  have ex : B x y = B (x - χ x • v) (y - χ y • v) + χ y * B (x - χ x • v) v
      + χ x * B v (y - χ y • v) + χ x * χ y * B v v := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [ex, hxy0, h1, h3]
  ring

/-- 上の結論から、成分の付値が確定する形（`p ∤ A i j` の側）。 -/
theorem not_dvd_of_congr_ne_zero {p : ℕ} [NeZero p] {a : ℤ} {c u w : ZMod p}
    (h : (a : ZMod p) = c * u * w) (hne : c * u * w ≠ 0) : ¬ (p : ℤ) ∣ a := by
  intro hdvd
  have h0 : ((a : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).2 hdvd
  exact hne (by rw [← h, h0])

/-! ## 2. 行列式の記帳 -/

/-- `det (D A D) = (∏ d)² · det A`。 -/
theorem det_conj_diagonal {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → R) (A : Matrix n n R) :
    (Matrix.diagonal d * A * Matrix.diagonal d).det = (∏ i, d i) ^ 2 * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

/-- `D = diag(1, p, …, p)` の場合：`det (D A D) = p^{2n} · det A`。 -/
theorem det_conj_diagonal_one_p {R : Type*} [CommRing R] {n : ℕ} (p : R)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (Matrix.diagonal (fun i : Fin (n + 1) => if i = 0 then (1 : R) else p) * A
      * Matrix.diagonal (fun i : Fin (n + 1) => if i = 0 then (1 : R) else p)).det
      = p ^ (2 * n) * A.det := by
  rw [det_conj_diagonal]
  have hprod : (∏ i : Fin (n + 1), if i = 0 then (1 : R) else p) = p ^ n := by
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_ne_zero]
  rw [hprod, ← pow_mul]
  ring_nf

/-- 付値の帳尻：`p^{r} Reg = p^{2(r−1)} D'`（`r = m+2`）から `Reg = p^{m} D'`。
すなわち `v_p(Reg_p) = (r−2) + v_p(det A')`。 -/
theorem reg_eq_of_det_eq {R : Type*} [CommRing R] [IsDomain R] {m : ℕ} {p Reg D' : R}
    (hp : p ≠ 0) (h : p ^ (m + 2) * Reg = p ^ (2 * (m + 1)) * D') :
    Reg = p ^ m * D' := by
  have e1 : 2 * (m + 1) = (m + 2) + m := by ring
  have hsplit : p ^ (2 * (m + 1)) * D' = p ^ (m + 2) * (p ^ m * D') := by rw [e1]; ring
  rw [hsplit] at h
  exact mul_left_cancel₀ (pow_ne_zero _ hp) h

end PadicHeight

#print axioms PadicHeight.bilin_rank_one_of_zero_iff
#print axioms PadicHeight.not_dvd_of_congr_ne_zero
#print axioms PadicHeight.det_conj_diagonal
#print axioms PadicHeight.det_conj_diagonal_one_p
#print axioms PadicHeight.reg_eq_of_det_eq
