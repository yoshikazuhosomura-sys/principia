/-
Q(ζ_19) の退化 CM 型 — Hazama の退化の核 K_S とその重み（組合せの部分）。

背景（紙の側。この file は幾何については何も主張しない）：
`E = Q(ζ_19)`、`G = Gal(E/Q) ≅ Z/18`、`ρ = 9`（複素共役）。CM 型 `S ⊂ G`（`S ⊔ ρS = G`）に
対して `A_S` を対応する 9 次元 CM アーベル多様体とする。Hazama（J. Math. Sci. Univ. Tokyo 10
(2003) §2、原典 J. Alg. Geom. 9 (2000)）は `h_g = Sg − Sρg ∈ Z[G]`、Hodge 行列 `H_S`、
`K_S = ker H_S`、重み `w(v) = Σ|a_g|/2`、`w(K_S) = min{max_{v∈X} w(v) : X は K_S の生成系}`
を定め、`A_S` が `N`-dominated ⟺ `w(K_S) = N` を示した。

`m = (1−ρ)·1_S ∈ Z[G]` は係数 `±1` の奇元で、`K_S = Ann_{Z[G]}(m)` に等しい。偶部分
`(1+ρ)Z[G]`（重み 1 の元＝因子の類で生成される）は常に `K_S` に含まれる。`v ∈ K_S` の奇部分
`v − ρv` を `R = Z[x]/(x^9+1)` に落とすと（`x^9 = −1`）、条件は `v̄ · m̃ = 0`
（`m̃ ∈ {±1}^9` は `m` の前半）になる。したがって「`K_S` の中で因子の外に出る元の最小重み」は
`(1/2)·min{ ‖v̄‖₁ : v̄ ∈ Ann_R(m̃), v̄ ≠ 0 }` で押さえられる。

この file が閉じるのは **有限・組合せの部分だけ** である：

  (1) `Z/18` の CM 型は 512 個、そのうち退化かつ原始的なものはちょうど **54 個**であり、
      それは「`Φ_6 = x²−x+1` が `m̃` を割り、`Φ_18 = x⁶−x³+1` が割らない」ことと同値。
      奇指標のうち位数 2 のもので消えるものは無い。
  (2) `Ann_R(Φ_6) = { (a, b, b−a, −a, −b, a−b, a, b, b−a) : a b : ℤ }`（階数 2）で、
      その非零元の `L¹` ノルムは `3(|a|+|b|+|a−b|) ≥ 6`。
  (3) 54 個すべてで `Ann_R(m̃) = Ann_R(Φ_6)`。ゆえに `K_S` の因子の外の元は重み `≥ 3` であり、
      重み 3 は達成される（`g = (x^9+1)/Φ_6` が `L¹ = 6`）。紙の側ではこれが `w(K_S) = 3`、
      すなわち `A_S` は 3-dominated であることを与える。
  (4) 代表の CM 型 `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18` について、余次元 3 の例外類に対応する
      6 個の `T ⊂ Z/18` を明示し、Pohlmann の許容条件を満たすこと・`⟨6⟩ = {0,6,12}` の
      剰余類ちょうど 2 個の合併であること・`ρ` 対の合併ではない（＝因子の積ではない）ことを確かめる。

代数性については何も述べていない。
-/
import Mathlib

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace CMHodge

/-- 環 `R = Z[x]/(x^9+1)` の元（係数 `a0 + a1 x + ⋯ + a8 x^8`）。 -/
structure V where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a5 : ℤ
  a6 : ℤ
  a7 : ℤ
  a8 : ℤ
deriving DecidableEq

/-- 零元。 -/
def O : V := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `R` の積（負巡回畳み込み、`x^9 = -1`）。 -/
def mul (u v : V) : V :=
  ⟨u.a0 * v.a0 - u.a1 * v.a8 - u.a2 * v.a7 - u.a3 * v.a6 - u.a4 * v.a5 - u.a5 * v.a4 - u.a6 * v.a3 - u.a7 * v.a2 - u.a8 * v.a1,
   u.a0 * v.a1 + u.a1 * v.a0 - u.a2 * v.a8 - u.a3 * v.a7 - u.a4 * v.a6 - u.a5 * v.a5 - u.a6 * v.a4 - u.a7 * v.a3 - u.a8 * v.a2,
   u.a0 * v.a2 + u.a1 * v.a1 + u.a2 * v.a0 - u.a3 * v.a8 - u.a4 * v.a7 - u.a5 * v.a6 - u.a6 * v.a5 - u.a7 * v.a4 - u.a8 * v.a3,
   u.a0 * v.a3 + u.a1 * v.a2 + u.a2 * v.a1 + u.a3 * v.a0 - u.a4 * v.a8 - u.a5 * v.a7 - u.a6 * v.a6 - u.a7 * v.a5 - u.a8 * v.a4,
   u.a0 * v.a4 + u.a1 * v.a3 + u.a2 * v.a2 + u.a3 * v.a1 + u.a4 * v.a0 - u.a5 * v.a8 - u.a6 * v.a7 - u.a7 * v.a6 - u.a8 * v.a5,
   u.a0 * v.a5 + u.a1 * v.a4 + u.a2 * v.a3 + u.a3 * v.a2 + u.a4 * v.a1 + u.a5 * v.a0 - u.a6 * v.a8 - u.a7 * v.a7 - u.a8 * v.a6,
   u.a0 * v.a6 + u.a1 * v.a5 + u.a2 * v.a4 + u.a3 * v.a3 + u.a4 * v.a2 + u.a5 * v.a1 + u.a6 * v.a0 - u.a7 * v.a8 - u.a8 * v.a7,
   u.a0 * v.a7 + u.a1 * v.a6 + u.a2 * v.a5 + u.a3 * v.a4 + u.a4 * v.a3 + u.a5 * v.a2 + u.a6 * v.a1 + u.a7 * v.a0 - u.a8 * v.a8,
   u.a0 * v.a8 + u.a1 * v.a7 + u.a2 * v.a6 + u.a3 * v.a5 + u.a4 * v.a4 + u.a5 * v.a3 + u.a6 * v.a2 + u.a7 * v.a1 + u.a8 * v.a0⟩

/-- `x` 倍（負巡回シフト）。 -/
def shift (v : V) : V := ⟨-v.a8, v.a0, v.a1, v.a2, v.a3, v.a4, v.a5, v.a6, v.a7⟩

/-- `x^k` 倍。 -/
def sh (k : ℕ) (v : V) : V := shift^[k] v

/-- 符号反転。 -/
def neg (v : V) : V := ⟨-v.a0, -v.a1, -v.a2, -v.a3, -v.a4, -v.a5, -v.a6, -v.a7, -v.a8⟩

/-- `L¹` ノルム。重みは `w(v) = L1 v / 2`。 -/
def L1 (v : V) : ℕ :=
  v.a0.natAbs + v.a1.natAbs + v.a2.natAbs + v.a3.natAbs + v.a4.natAbs +
  v.a5.natAbs + v.a6.natAbs + v.a7.natAbs + v.a8.natAbs

/-- `Φ_6 = x² − x + 1`。 -/
def f6 : V := ⟨1, -1, 1, 0, 0, 0, 0, 0, 0⟩

/-- `(x^9+1)/Φ_6 = (x+1)Φ_18 = 1 + x − x³ − x⁴ + x⁶ + x⁷`。 -/
def gp : V := ⟨1, 1, 0, -1, -1, 0, 1, 1, 0⟩

/-- `(x^9+1)/Φ_18 = x³ + 1`。 -/
def q3 : V := ⟨1, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- `(x^9+1)/(x+1) = 1 − x + x² − ⋯ + x⁸`（位数 2 の奇指標に対応）。 -/
def q1 : V := ⟨1, -1, 1, -1, 1, -1, 1, -1, 1⟩

/-- `n` の第 `i` ビットから符号を作る。 -/
def bitv (n i : ℕ) : ℤ := if (n / 2 ^ i) % 2 = 1 then 1 else -1

/-- `n < 512` が定める CM 型の符号ベクトル `m̃ ∈ {±1}^9`。
`m̃_j = +1 ⟺ j ∈ S`（`j = 0,…,8`）、`S ⊂ Z/18` は `S ⊔ (S+9) = Z/18`。 -/
def sg (n : ℕ) : V :=
  ⟨bitv n 0, bitv n 1, bitv n 2, bitv n 3, bitv n 4,
   bitv n 5, bitv n 6, bitv n 7, bitv n 8⟩

/-- `A_S` が退化する（消える奇指標がある）。奇指標の位数は 2, 6, 18 のいずれかで、
それぞれ `q1`, `gp`, `q3` を掛けて 0 になることに対応する。 -/
def Deg (n : ℕ) : Prop :=
  mul (sg n) gp = O ∨ mul (sg n) q3 = O ∨ mul (sg n) q1 = O

instance (n : ℕ) : Decidable (Deg n) := by unfold Deg; infer_instance

/-- `S` が原始的（`A_S` が単純）：`S + t = S` となる `t ≠ 0` が無い。 -/
def Prim (n : ℕ) : Prop :=
  ∀ k ∈ Finset.Icc 1 8, sh k (sg n) ≠ sg n ∧ sh k (sg n) ≠ neg (sg n)

instance (n : ℕ) : Decidable (Prim n) := by unfold Prim; infer_instance


/-- 位数 2 の奇指標で消える CM 型は無い（`|S| = 9` は奇数だから）。 -/
theorem no_deg_order_two : ∀ n ∈ Finset.range 512, mul (sg n) q1 ≠ O := by decide

/-- 退化かつ原始的な CM 型はちょうど 54 個。 -/
theorem card_deg_prim :
    ((Finset.range 512).filter (fun n => Deg n ∧ Prim n)).card = 54 := by decide

/-- 退化かつ原始的 ⟺ `Φ_6 ∣ m̃` かつ `Φ_18 ∤ m̃`。 -/
theorem deg_prim_iff :
    ∀ n ∈ Finset.range 512,
      ((Deg n ∧ Prim n) ↔ (mul (sg n) gp = O ∧ mul (sg n) q3 ≠ O)) := by decide


/-- `Ann_R(Φ_6)` のパラメータ表示。 -/
theorem ann_f6_param (v : V) (h : mul v f6 = O) :
    v = ⟨v.a0, v.a1, v.a1 - v.a0, -v.a0, -v.a1, v.a0 - v.a1, v.a0, v.a1, v.a1 - v.a0⟩ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [mul, f6, O, V.mk.injEq] at h ⊢
  omega

/-- 逆向き：パラメータ表示の元は `Ann_R(Φ_6)` に入る。 -/
theorem param_mem (a b : ℤ) :
    mul ⟨a, b, b - a, -a, -b, a - b, a, b, b - a⟩ f6 = O := by
  simp only [mul, f6, O, V.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- `Ann_R(Φ_6)` の非零元の `L¹` ノルムは 6 以上（＝重み 3 以上）。 -/
theorem ann_f6_L1 (v : V) (h : mul v f6 = O) : v = O ∨ 6 ≤ L1 v := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [mul, f6, O, L1, V.mk.injEq] at h ⊢
  omega


theorem mul_shift_right (u v : V) : mul u (shift v) = shift (mul u v) := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8⟩ := u
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := v
  simp [mul, shift, V.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem mul_neg_right (u v : V) : mul u (neg v) = neg (mul u v) := by
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8⟩ := u
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := v
  simp [mul, neg, V.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem shift_eq_O (v : V) : shift v = O ↔ v = O := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [shift, O, V.mk.injEq]
  all_goals omega

theorem neg_eq_O (v : V) : neg v = O ↔ v = O := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [neg, O, V.mk.injEq]
  all_goals omega

theorem sh_succ (k : ℕ) (v : V) : sh (k + 1) v = shift (sh k v) := by
  simp [sh, Function.iterate_succ_apply']

theorem mul_sh_right (u v : V) : ∀ k : ℕ, mul u (sh k v) = sh k (mul u v) := by
  intro k
  induction k with
  | zero => simp [sh]
  | succ n ih => rw [sh_succ, mul_shift_right, ih, sh_succ]

theorem sh_eq_O (k : ℕ) (v : V) : sh k v = O ↔ v = O := by
  induction k with
  | zero => simp [sh]
  | succ n ih => rw [sh_succ, shift_eq_O, ih]

/-- 平行移動軌道の代表 `M1`。 -/
def M1 : V := ⟨-1, -1, -1, -1, -1, -1, -1, 1, -1⟩

/-- 平行移動軌道の代表 `M2`。 -/
def M2 : V := ⟨-1, -1, -1, 1, -1, -1, 1, 1, -1⟩

/-- 平行移動軌道の代表 `M3`。 -/
def M3 : V := ⟨-1, -1, 1, -1, -1, 1, -1, 1, -1⟩

theorem bridge_M1 (v : V) (h : mul v M1 = O) : mul v f6 = O := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [mul, M1, f6, O, V.mk.injEq] at h ⊢
  omega

theorem bridge_M2 (v : V) (h : mul v M2 = O) : mul v f6 = O := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [mul, M2, f6, O, V.mk.injEq] at h ⊢
  omega

theorem bridge_M3 (v : V) (h : mul v M3 = O) : mul v f6 = O := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := v
  simp [mul, M3, f6, O, V.mk.injEq] at h ⊢
  omega


/-- 54 個の退化かつ原始的な CM 型は、3 個の代表の `x^k` 倍（と符号）で尽くされる。 -/
theorem cover :
    ∀ n ∈ Finset.range 512, (Deg n ∧ Prim n) →
      ∃ k ∈ Finset.range 9,
        sg n = sh k M1 ∨ sg n = neg (sh k M1) ∨
        sg n = sh k M2 ∨ sg n = neg (sh k M2) ∨
        sg n = sh k M3 ∨ sg n = neg (sh k M3) := by decide

/-- **主定理（下からの評価）**：退化かつ原始的な CM 型について、`Ann_R(m̃)` の非零元の
`L¹` ノルムは 6 以上。紙の側では「`K_S` の中で因子の類の外に出る元の重みは 3 以上」。 -/
theorem weight_ge_three (n : ℕ) (hn : n ∈ Finset.range 512) (h : Deg n ∧ Prim n)
    (v : V) (hv : mul v (sg n) = O) : v = O ∨ 6 ≤ L1 v := by
  obtain ⟨k, -, hk⟩ := cover n hn h
  have key : mul v f6 = O := by
    rcases hk with e | e | e | e | e | e
    · exact bridge_M1 v (by rwa [e, mul_sh_right, sh_eq_O] at hv)
    · exact bridge_M1 v (by rwa [e, mul_neg_right, neg_eq_O, mul_sh_right, sh_eq_O] at hv)
    · exact bridge_M2 v (by rwa [e, mul_sh_right, sh_eq_O] at hv)
    · exact bridge_M2 v (by rwa [e, mul_neg_right, neg_eq_O, mul_sh_right, sh_eq_O] at hv)
    · exact bridge_M3 v (by rwa [e, mul_sh_right, sh_eq_O] at hv)
    · exact bridge_M3 v (by rwa [e, mul_neg_right, neg_eq_O, mul_sh_right, sh_eq_O] at hv)
  exact ann_f6_L1 v key

/-- **主定理（達成）**：重み 3 はどの CM 型でも達成される。`gp = (x^9+1)/Φ_6` は
`Ann_R(m̃)` に入り `L¹ = 6`。 -/
theorem weight_three_attained :
    ∀ n ∈ Finset.range 512, (Deg n ∧ Prim n) → (mul gp (sg n) = O ∧ L1 gp = 6) := by decide

/-- 代表の CM 型 `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18`（`n = 383` に対応）。 -/
def Sset : Finset (ZMod 18) := {0, 1, 2, 3, 4, 5, 6, 8, 16}

/-- 余次元 3 の例外類に対応する 6 個の `T ⊂ Z/18`。`H = ⟨6⟩ = {0,6,12}` の剰余類 2 個の合併。 -/
def Texc : Fin 6 → Finset (ZMod 18) :=
  ![{0, 1, 6, 7, 12, 13}, {1, 2, 7, 8, 13, 14}, {2, 3, 8, 9, 14, 15}, {3, 4, 9, 10, 15, 16}, {4, 5, 10, 11, 16, 17}, {0, 5, 6, 11, 12, 17}]

/-- Pohlmann の許容条件：`|T ∩ (S+g)| = |T|/2`。 -/
def Adm (T : Finset (ZMod 18)) : Prop :=
  ∀ g : ZMod 18, (T.filter (fun x => x - g ∈ Sset)).card = 3

instance (T : Finset (ZMod 18)) : Decidable (Adm T) := by unfold Adm; infer_instance

theorem Sset_is_cm_type :
    ∀ x : ZMod 18, (x ∈ Sset ∧ x + 9 ∉ Sset) ∨ (x ∉ Sset ∧ x + 9 ∈ Sset) := by decide

theorem Texc_card : ∀ k : Fin 6, (Texc k).card = 6 := by decide

/-- 6 個とも許容（＝対応する `e_T` は `H^6(A,Q)` のホッジ類）。 -/
theorem Texc_adm : ∀ k : Fin 6, Adm (Texc k) := by decide

/-- 6 個とも `⟨6⟩ = {0,6,12}` の剰余類の合併。 -/
theorem Texc_coset : ∀ k : Fin 6, ∀ x ∈ Texc k, x + 6 ∈ Texc k := by decide

/-- どれも `ρ = 9` 対の合併ではない（＝因子の積では書けない）。 -/
theorem Texc_not_divisorial : ∀ k : Fin 6, ∃ x ∈ Texc k, x + 9 ∉ Texc k := by decide

end CMHodge

#print axioms CMHodge.no_deg_order_two
#print axioms CMHodge.card_deg_prim
#print axioms CMHodge.deg_prim_iff
#print axioms CMHodge.ann_f6_param
#print axioms CMHodge.param_mem
#print axioms CMHodge.ann_f6_L1
#print axioms CMHodge.cover
#print axioms CMHodge.weight_ge_three
#print axioms CMHodge.weight_three_attained
#print axioms CMHodge.Sset_is_cm_type
#print axioms CMHodge.Texc_card
#print axioms CMHodge.Texc_adm
#print axioms CMHodge.Texc_coset
#print axioms CMHodge.Texc_not_divisorial
