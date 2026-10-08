/-
  退化 CM 型の判別式 — 芯を本物の環 `ℤ[θ] = ℤ[X]/(X³+X²−6X−7)` の上に置き直す

  独立な検証で出た指摘に答える。

  指摘：`CMHodgeDiscriminant.lean` の `F0 := ℤ × ℤ × ℤ` は `θ³ = 7 + 6θ − θ²` の還元式で
  積を自作しているだけで、結合律も分配律も証明されておらず、
  `ℤ[X]/(X³+X²−6X−7)` との同型も示されていない。ゆえに `detA_eq_neg_sq`・`detB_is_norm`
  （N22・N23 の芯）は正当性未確認の模型の上の組の計算である。

  本ファイルが足すもの：
  (1) **模型に依らない形**：可換環 `R` の任意の元 `t` が `t³+t²−6t−7 = 0` を満たせば
      `(t²−3t+1)² = −(48+41t−24t²)` であり、`19·(−(t²−3t+1))² = 19·(−(48+41t−24t²))`。
      （`linear_combination (t−7) * ht` で閉じる。模型は一切使わない。）
  (2) **本物の環での実現**：`R = AdjoinRoot (X³+X²−6X−7)`（＝`ℤ[X]/(X³+X²−6X−7)`）と
      `t = root` でこの仮定が成り立つこと、ゆえに上の二つの等式がそこで成り立つこと。
  (3) **自作の積が正しいこと**：`ev t (a·b) = ev t a · ev t b`（`ev t (c₀,c₁,c₂) = c₀+c₁t+c₂t²`）。
      すなわち自作の `mul` は還元式を通じて本物の環の積を計算している。
  (4) **結合律・分配律**：自作の `mul` について直接証明する。
  (5) **同型**：`ev (root p) : F0 → AdjoinRoot p` は単射かつ全射。
      ゆえに模型は `ℤ[X]/(X³+X²−6X−7)` と（積つきで）同一視できる。

  幾何・代数的サイクル・ホッジ予想は一切含まない。等級は［Lean］（有限の代数の等式）。
-/
import Mathlib

namespace CMHodgeDiscRing

open Polynomial

/-! ### 1. 模型に依らない核 -/

/-- **`t³+t²−6t−7 = 0` を満たすどんな可換環の元でも `(t²−3t+1)² = −(48+41t−24t²)`。**
    PARI の出力 `19⁵·det φ_A = 48+41θ−24θ²` と `= −(θ²−3θ+1)²` の芯。 -/
theorem detA_eq_neg_sq_ring {R : Type*} [CommRing R] (t : R)
    (ht : t ^ 3 + t ^ 2 - 6 * t - 7 = 0) :
    (t ^ 2 - 3 * t + 1) ^ 2 = -(48 + 41 * t - 24 * t ^ 2) := by
  linear_combination (t - 7) * ht

/-- **ノルム表示**：`N_{F/F_0}(u+v√−19) = u²+19v²` に `u = 0`・`v = −(t²−3t+1)` を入れた形。 -/
theorem detB_is_norm_ring {R : Type*} [CommRing R] (t : R)
    (ht : t ^ 3 + t ^ 2 - 6 * t - 7 = 0) :
    (0 : R) ^ 2 + 19 * (-(t ^ 2 - 3 * t + 1)) ^ 2 = 19 * -(48 + 41 * t - 24 * t ^ 2) := by
  linear_combination (19 * (t - 7)) * ht

/-- 有理数の水準（分母 `19⁵`・`19³` を入れた形）：`19·(−w/19³)² = (−(48+41t−24t²))/19⁵`。 -/
theorem detB_is_norm_field {K : Type*} [Field K] [CharZero K] (t : K)
    (ht : t ^ 3 + t ^ 2 - 6 * t - 7 = 0) :
    19 * (-(t ^ 2 - 3 * t + 1) / 19 ^ 3) ^ 2 = (-(48 + 41 * t - 24 * t ^ 2)) / 19 ^ 5 := by
  rw [← detA_eq_neg_sq_ring t ht]
  ring

/-! ### 2. 本物の環 `ℤ[θ] = ℤ[X]/(X³+X²−6X−7)` -/

/-- `p = X³+X²−6X−7`（導体 19 の巡回三次体 `F_0` の生成元の最小多項式）。 -/
noncomputable def p : ℤ[X] := X ^ 3 + X ^ 2 - C 6 * X - C 7

theorem p_eq : p = X ^ 3 + X ^ 2 - 6 * X - 7 := by simp [p]

theorem p_monic : p.Monic := by unfold p; monicity!

theorem p_natDegree : p.natDegree = 3 := by unfold p; compute_degree!

theorem p_degree : p.degree = 3 := by
  rw [Polynomial.degree_eq_natDegree p_monic.ne_zero, p_natDegree]; rfl

/-- `θ := root p ∈ ℤ[X]/(p)`。 -/
noncomputable def th : AdjoinRoot p := AdjoinRoot.root p

/-- 三次の多項式の像を `θ` の多項式として書く（`mk p` が環準同型であることだけを使う）。 -/
theorem mkCubic (a b c d : ℤ) :
    AdjoinRoot.mk p (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
      = (a : AdjoinRoot p) * th ^ 3 + (b : AdjoinRoot p) * th ^ 2
        + (c : AdjoinRoot p) * th + (d : AdjoinRoot p) := by
  simp [th, AdjoinRoot.mk_X]

theorem p_as_cubic : p = C 1 * X ^ 3 + C 1 * X ^ 2 + C (-6) * X + C (-7) := by
  simp [p]; ring

/-- **`θ³+θ²−6θ−7 = 0` が本物の環 `ℤ[X]/(p)` で成り立つ。** -/
theorem th_rel : th ^ 3 + th ^ 2 - 6 * th - 7 = 0 := by
  have h : AdjoinRoot.mk p p = 0 := AdjoinRoot.mk_self
  have h2 : AdjoinRoot.mk p p
      = AdjoinRoot.mk p (C 1 * X ^ 3 + C 1 * X ^ 2 + C (-6) * X + C (-7)) := by
    rw [← p_as_cubic]
  rw [h2, mkCubic] at h
  push_cast at h
  linear_combination h

/-- **`19⁵·det φ_A = −(θ²−3θ+1)²` が `ℤ[X]/(X³+X²−6X−7)` で成り立つ。**（N22 の芯） -/
theorem detA_eq_neg_sq_adjoin :
    (th ^ 2 - 3 * th + 1) ^ 2 = -(48 + 41 * th - 24 * th ^ 2) :=
  detA_eq_neg_sq_ring th th_rel

/-- **`det φ_B` のノルム表示が `ℤ[X]/(X³+X²−6X−7)` で成り立つ。**（N23 の芯） -/
theorem detB_is_norm_adjoin :
    (0 : AdjoinRoot p) ^ 2 + 19 * (-(th ^ 2 - 3 * th + 1)) ^ 2
      = 19 * -(48 + 41 * th - 24 * th ^ 2) :=
  detB_is_norm_ring th th_rel

/-! ### 3. 自作の模型と、その積の正しさ -/

/-- これまでの模型：`(c₀,c₁,c₂) ↦ c₀ + c₁θ + c₂θ²`。 -/
abbrev F0 := ℤ × ℤ × ℤ

/-- 自作の積（`CMHodgeDiscriminant.lean` の `mul` と同一の式）。 -/
def mul (a b : F0) : F0 :=
  let p0 := a.1 * b.1
  let p1 := a.1 * b.2.1 + a.2.1 * b.1
  let p2 := a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1
  let p3 := a.2.1 * b.2.2 + a.2.2 * b.2.1
  let p4 := a.2.2 * b.2.2
  (p0 + 7 * p3 - 7 * p4, p1 + 6 * p3 + p4, p2 - p3 + 7 * p4)

def addF (a b : F0) : F0 := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- 模型から環への評価 `ev t (c₀,c₁,c₂) = c₀ + c₁t + c₂t²`。 -/
def ev {R : Type*} [CommRing R] (t : R) (a : F0) : R :=
  (a.1 : R) + (a.2.1 : R) * t + (a.2.2 : R) * t ^ 2

theorem ev_add {R : Type*} [CommRing R] (t : R) (a b : F0) :
    ev t (addF a b) = ev t a + ev t b := by
  simp only [ev, addF, Int.cast_add]; ring

/-- 積の式（`let` を開いた形。`rfl` で同値）。 -/
theorem mul_eq (a b : F0) :
    mul a b =
      (a.1 * b.1 + 7 * (a.2.1 * b.2.2 + a.2.2 * b.2.1) - 7 * (a.2.2 * b.2.2),
       a.1 * b.2.1 + a.2.1 * b.1 + 6 * (a.2.1 * b.2.2 + a.2.2 * b.2.1) + a.2.2 * b.2.2,
       a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1 - (a.2.1 * b.2.2 + a.2.2 * b.2.1)
         + 7 * (a.2.2 * b.2.2)) := rfl

/-- **自作の積は、還元式を通じて本物の環の積を計算している。**
    ゆえに模型の計算は `ℤ[θ]` の計算である（これが検証の指摘への答え）。 -/
theorem ev_mul {R : Type*} [CommRing R] (t : R)
    (ht : t ^ 3 + t ^ 2 - 6 * t - 7 = 0) (a b : F0) :
    ev t (mul a b) = ev t a * ev t b := by
  simp only [ev, mul_eq]
  push_cast
  linear_combination
    (-((a.2.1 : R) * (b.2.2 : R) + (a.2.2 : R) * (b.2.1 : R))
      + ((a.2.2 : R) * (b.2.2 : R)) * (1 - t)) * ht

theorem ev_one {R : Type*} [CommRing R] (t : R) : ev t (1, 0, 0) = 1 := by
  simp [ev]

/-! ### 4. 自作の積の結合律・分配律（模型の中だけで） -/

theorem mul_comm' (a b : F0) : mul a b = mul b a := by
  simp only [mul_eq, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem mul_assoc' (a b c : F0) : mul (mul a b) c = mul a (mul b c) := by
  simp only [mul_eq, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem mul_add' (a b c : F0) : mul a (addF b c) = addF (mul a b) (mul a c) := by
  simp only [mul_eq, addF, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem one_mul' (a : F0) : mul (1, 0, 0) a = a := by
  have h : mul (1, 0, 0) a = (a.1, a.2.1, a.2.2) := by
    simp only [mul_eq, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩
  rw [h]

/-! ### 5. 模型は `ℤ[X]/(X³+X²−6X−7)` と同一視できる（単射性） -/

theorem mkQuad (c0 c1 c2 : ℤ) :
    AdjoinRoot.mk p (C c2 * X ^ 2 + C c1 * X + C c0) = ev th (c0, c1, c2) := by
  simp [th, AdjoinRoot.mk_X, ev]
  ring

/-- 次数 `< 3 = deg p` の多項式が `p` で割れるなら 0 なので、`ev th` の核は 0 だけ。 -/
theorem ev_th_eq_zero (c : F0) (hc : ev th c = 0) : c = (0, 0, 0) := by
  obtain ⟨c0, c1, c2⟩ := c
  have hmk : AdjoinRoot.mk p (C c2 * X ^ 2 + C c1 * X + C c0) = 0 := by
    rw [mkQuad]; exact hc
  have hdvd : p ∣ (C c2 * X ^ 2 + C c1 * X + C c0) := AdjoinRoot.mk_eq_zero.mp hmk
  have hdeg : (C c2 * X ^ 2 + C c1 * X + C c0).degree < p.degree := by
    rw [p_degree]; exact Polynomial.degree_quadratic_lt
  have hz := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have e0 := congrArg (fun q => Polynomial.eval 0 q) hz
  have e1 := congrArg (fun q => Polynomial.eval 1 q) hz
  have e2 := congrArg (fun q => Polynomial.eval 2 q) hz
  simp at e0 e1 e2
  have h0 : c0 = 0 := by omega
  have h1 : c1 = 0 := by omega
  have h2 : c2 = 0 := by omega
  simp [h0, h1, h2]

/-- **`ev th : F0 → ℤ[X]/(X³+X²−6X−7)` は単射。**
    `ev_mul`（積を保つ）・`ev_add`（和を保つ）と合わせて、模型は本物の環の部分環と同一視できる。 -/
theorem ev_th_injective : Function.Injective (ev th) := by
  intro a b hab
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  have h : ev th (a0 - b0, a1 - b1, a2 - b2) = 0 := by
    simp only [ev] at hab ⊢
    push_cast
    linear_combination hab
  have h3 := ev_th_eq_zero _ h
  simp only [Prod.mk.injEq, sub_eq_zero] at h3
  simp [h3.1, h3.2.1, h3.2.2]

end CMHodgeDiscRing

#print axioms CMHodgeDiscRing.detA_eq_neg_sq_ring
#print axioms CMHodgeDiscRing.detB_is_norm_ring
#print axioms CMHodgeDiscRing.detB_is_norm_field
#print axioms CMHodgeDiscRing.th_rel
#print axioms CMHodgeDiscRing.detA_eq_neg_sq_adjoin
#print axioms CMHodgeDiscRing.detB_is_norm_adjoin
#print axioms CMHodgeDiscRing.ev_mul
#print axioms CMHodgeDiscRing.mul_assoc'
#print axioms CMHodgeDiscRing.mul_add'
#print axioms CMHodgeDiscRing.ev_th_eq_zero
#print axioms CMHodgeDiscRing.ev_th_injective
#print axioms CMHodgeDiscRing.one_mul'
#print axioms CMHodgeDiscRing.mul_comm'
#print axioms CMHodgeDiscRing.p_eq
