/-
  エルデシュ問題 #169。**Wróblewski 1984 の Lemma 1 の機械検査**。

  一次資料（Math. Comp. 43 (1984), 261）逐語：
    B(p,q,r) = { Σ_{i=1}^{q} k_i (2p−1)^{i−1} : 0 ≤ k_i < p, Σ T_p(k_i) = r }
    T_p(k) = (k − ⌊(p+1)/2⌋)(k − ⌊(p−1)/2⌋)/2
    Lemma 1. The set B(p,q,r) is nonaveraging.
    「The proof is similar to that of Behrend [1] whose k_i² has been replaced here
      by T_p(k_i).」 —— **論文に証明は書かれていない。**この一行に構成全体が載っている。
  記録 f(3) ≥ 3.00849 は Lemma 1 と Lemma 2（APFreeWindowSeparation で機械検査済）だけに載っているので、
  ここが埋まると構成の 3-AP-free 性は端から端まで機械検査済みになる。

  【証明の骨】
    (1) 無繰り上がり：桁は 0 ≤ k < p、底は b ≥ 2p−1 なので x_i+y_i ≤ 2p−2 < b、2z_i ≤ 2p−2 < b。
        ゆえに x+y = 2z ⟹ **桁ごとに x_i + y_i = 2 z_i**（lemma `head_eq` の反復）。
    (2) 凸性：**先頭係数が正の二次式なら何でもよい。**
        f(k) = (k−a)(k−b) に対し x+y = 2z のとき 2(f x + f y − 2 f z) = (x−y)²（lemma `convex_id`）。
        a, b が何であってもよい——**線形項は打ち消える**。
        ⟹ Behrend の k² と Wróblewski の T_p が同じ理由で効くことが、この一行で見える。
        a = b+1 という選び方は T が整数値かつ値域が最小になるようにするためであって、
        nonaveraging 性そのものには効いていない。
    (3) 総和：Σ(f x_i + f y_i − 2 f z_i) = r + r − 2r = 0、各項は非負（(2)）
        ⟹ 全項 0 ⟹ 全桁で x_i = y_i ⟹ x = y。∎

  主定理は `digits_eq`、Lemma 1 の形は `lemma1_nonaveraging`。
-/
import Mathlib.Tactic

namespace APFree.NonAveraging

/-- 桁列（下位から）を底 `b` の整数に。 -/
def val (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + b * val b ds

/-- 重み関数。`A`, `B` は任意の整数でよい（下の `convex_id` を見よ）。
    Wróblewski は `A = ⌊(p+1)/2⌋`, `B = ⌊(p−1)/2⌋` と取り、`T_p = F/2` としている。 -/
def F (A B : ℤ) (k : ℕ) : ℤ := ((k : ℤ) - A) * ((k : ℤ) - B)

/-- 桁列の重みの総和。 -/
def W (A B : ℤ) (l : List ℕ) : ℤ := (l.map (F A B)).sum

@[simp] lemma W_nil (A B : ℤ) : W A B [] = 0 := by simp [W]

@[simp] lemma W_cons (A B : ℤ) (d : ℕ) (l : List ℕ) :
    W A B (d :: l) = F A B d + W A B l := by simp [W]

/-! ### (2) 凸性：先頭係数が正の二次式なら、線形項によらず成り立つ -/

/-- **凸の恒等式**。`x + y = 2z` のとき `2(f x + f y − 2 f z) = (x − y)²`。
    `A`, `B` は任意——線形項は完全に打ち消える。 -/
lemma convex_id (A B x y z : ℤ) (h : x + y = 2 * z) :
    2 * (((x - A) * (x - B)) + ((y - A) * (y - B)) - 2 * ((z - A) * (z - B)))
      = (x - y) ^ 2 := by
  have hy : y = 2 * z - x := by linarith
  subst hy; ring

lemma F_convex (A B : ℤ) {x y z : ℕ} (h : x + y = 2 * z) :
    2 * (F A B x + F A B y - 2 * F A B z) = ((x : ℤ) - y) ^ 2 := by
  have h' : (x : ℤ) + (y : ℤ) = 2 * (z : ℤ) := by exact_mod_cast h
  simpa [F] using convex_id A B (x : ℤ) (y : ℤ) (z : ℤ) h'

/-- 一桁ぶんの余り（スラック）は非負。 -/
lemma F_slack_nonneg (A B : ℤ) {x y z : ℕ} (h : x + y = 2 * z) :
    0 ≤ F A B x + F A B y - 2 * F A B z := by
  have h2 := F_convex A B h
  nlinarith [sq_nonneg ((x : ℤ) - y)]

/-- スラックが 0 なら二つの桁は等しい。 -/
lemma F_slack_eq (A B : ℤ) {x y z : ℕ} (h : x + y = 2 * z)
    (h0 : F A B x + F A B y - 2 * F A B z = 0) : x = y := by
  have h2 := F_convex A B h
  rw [h0] at h2
  have : ((x : ℤ) - y) ^ 2 = 0 := by linarith
  have : (x : ℤ) = (y : ℤ) := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  exact_mod_cast this

/-! ### (1) 無繰り上がり -/

/-- **一桁ぶんの繰り上がり無し。**`x+y < b` かつ `2z < b` なら、
    `(x + bX) + (y + bY) = 2(z + bZ)` は `x+y = 2z` と `X+Y = 2Z` に分かれる。 -/
lemma head_eq {b x y z X Y Z : ℕ} (hb : 0 < b) (hx : x + y < b) (hz : 2 * z < b)
    (h : (x + b * X) + (y + b * Y) = 2 * (z + b * Z)) :
    x + y = 2 * z ∧ X + Y = 2 * Z := by
  have key : (x + y) + b * (X + Y) = (2 * z) + b * (2 * Z) := by
    have e1 : b * (X + Y) = b * X + b * Y := by ring
    have e2 : b * (2 * Z) = 2 * (b * Z) := by ring
    omega
  have hm : (x + y) % b = (2 * z) % b := by
    have hc := congrArg (· % b) key
    simpa [Nat.add_mul_mod_self_left] using hc
  have h1 : x + y = 2 * z := by
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hz] at hm
  refine ⟨h1, ?_⟩
  have hmul : b * (X + Y) = b * (2 * Z) := by omega
  exact Nat.eq_of_mul_eq_mul_left hb hmul

/-! ### (3) スラックの総和 -/

/-- 桁列全体のスラックは非負。 -/
lemma slack_nonneg (A B : ℤ) (b p : ℕ) (hb0 : 0 < b) (hb : 2 * p ≤ b + 1) :
    ∀ xs ys zs : List ℕ,
      (∀ d ∈ xs, d < p) → (∀ d ∈ ys, d < p) → (∀ d ∈ zs, d < p) →
      xs.length = ys.length → ys.length = zs.length →
      val b xs + val b ys = 2 * val b zs →
      0 ≤ W A B xs + W A B ys - 2 * W A B zs := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs _ _ _ h1 h2 _
      have : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using h1.symm)
      subst this
      have : zs = [] := List.eq_nil_of_length_eq_zero (by simpa using h2.symm)
      subst this
      simp
  | cons x xs ih =>
      intro ys zs hx hy hz h1 h2 hv
      match ys, zs with
      | [], _ => simp at h1
      | ys', [] =>
        have hnil : ys' = [] := List.eq_nil_of_length_eq_zero (by simpa using h2)
        subst hnil
        simp at h1
      | y :: ys, z :: zs =>
        have hxp : x < p := hx x (by simp)
        have hyp : y < p := hy y (by simp)
        have hzp : z < p := hz z (by simp)
        have hlt1 : x + y < b := by omega
        have hlt2 : 2 * z < b := by omega
        have hv' : (x + b * val b xs) + (y + b * val b ys) = 2 * (z + b * val b zs) := by
          simpa [val] using hv
        obtain ⟨hd, ht⟩ := head_eq hb0 hlt1 hlt2 hv'
        have hrest := ih ys zs (fun d hd' => hx d (by simp [hd'])) (fun d hd' => hy d (by simp [hd']))
          (fun d hd' => hz d (by simp [hd'])) (by simpa using h1) (by simpa using h2)
          (by simpa [val] using ht)
        have hhead := F_slack_nonneg A B hd
        simp only [W_cons]
        linarith

/-- **主定理（Lemma 1 の本体）。**
    桁がすべて `p` 未満、底 `b ≥ 2p−1`、値が `x + y = 2z`、
    重みの総和が `W xs + W ys = 2 W zs` なら、`xs = ys`。 -/
theorem digits_eq (A B : ℤ) (b p : ℕ) (hb0 : 0 < b) (hb : 2 * p ≤ b + 1) :
    ∀ xs ys zs : List ℕ,
      (∀ d ∈ xs, d < p) → (∀ d ∈ ys, d < p) → (∀ d ∈ zs, d < p) →
      xs.length = ys.length → ys.length = zs.length →
      val b xs + val b ys = 2 * val b zs →
      W A B xs + W A B ys = 2 * W A B zs →
      xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys zs _ _ _ h1 _ _ _
      exact (List.eq_nil_of_length_eq_zero (by simpa using h1.symm)).symm
  | cons x xs ih =>
      intro ys zs hx hy hz h1 h2 hv hw
      match ys, zs with
      | [], _ => simp at h1
      | ys', [] =>
        have hnil : ys' = [] := List.eq_nil_of_length_eq_zero (by simpa using h2)
        subst hnil
        simp at h1
      | y :: ys, z :: zs =>
        have hxp : x < p := hx x (by simp)
        have hyp : y < p := hy y (by simp)
        have hzp : z < p := hz z (by simp)
        have hlt1 : x + y < b := by omega
        have hlt2 : 2 * z < b := by omega
        have hv' : (x + b * val b xs) + (y + b * val b ys) = 2 * (z + b * val b zs) := by
          simpa [val] using hv
        obtain ⟨hd, ht⟩ := head_eq hb0 hlt1 hlt2 hv'
        have hxs : ∀ d ∈ xs, d < p := fun d hd' => hx d (by simp [hd'])
        have hys : ∀ d ∈ ys, d < p := fun d hd' => hy d (by simp [hd'])
        have hzs : ∀ d ∈ zs, d < p := fun d hd' => hz d (by simp [hd'])
        have htail : 0 ≤ W A B xs + W A B ys - 2 * W A B zs :=
          slack_nonneg A B b p hb0 hb xs ys zs hxs hys hzs (by simpa using h1)
            (by simpa using h2) (by simpa [val] using ht)
        have hhead : 0 ≤ F A B x + F A B y - 2 * F A B z := F_slack_nonneg A B hd
        simp only [W_cons] at hw
        -- 全体のスラックが 0、頭も尾も非負 ⟹ どちらも 0
        have hh0 : F A B x + F A B y - 2 * F A B z = 0 := by linarith
        have ht0 : W A B xs + W A B ys = 2 * W A B zs := by linarith
        have hxy : x = y := F_slack_eq A B hd hh0
        have := ih ys zs hxs hys hzs (by simpa using h1) (by simpa using h2)
          (by simpa [val] using ht) ht0
        rw [hxy, this]

/-! ### Lemma 1 の形 -/

/-- `B(p,q,r)` の元（桁列で表したもの）。 -/
structure Sphere (p q : ℕ) (r : ℤ) (A B : ℤ) where
  digits : List ℕ
  len    : digits.length = q
  bound  : ∀ d ∈ digits, d < p
  weight : W A B digits = r

/-- **Lemma 1（Wróblewski 1984）の機械検査済みの形。**
    底 `b = 2p−1` のもとで `B(p,q,r)` は nonaveraging：
    `val x + val y = 2 * val z` ならば `x = y`（したがって三項等差数列は自明なものだけ）。 -/
theorem lemma1_nonaveraging {p q : ℕ} {r A B : ℤ} (hp : 0 < p)
    (x y z : Sphere p q r A B)
    (h : val (2 * p - 1) x.digits + val (2 * p - 1) y.digits
          = 2 * val (2 * p - 1) z.digits) :
    x.digits = y.digits := by
  have hb0 : 0 < 2 * p - 1 := by omega
  have hb : 2 * p ≤ (2 * p - 1) + 1 := by omega
  refine digits_eq A B (2 * p - 1) p hb0 hb x.digits y.digits z.digits
    x.bound y.bound z.bound (by rw [x.len, y.len]) (by rw [y.len, z.len]) h ?_
  rw [x.weight, y.weight, z.weight]; ring

/-- 系：Wróblewski が実際に使う重み。`T_p(k) = (k − ⌊(p+1)/2⌋)(k − ⌊(p−1)/2⌋)/2` は
    `F A B / 2`（`A = ⌊(p+1)/2⌋`, `B = ⌊(p−1)/2⌋`）である。
    定理は `A`, `B` に依らないので、この特定化も直ちに従う。 -/
theorem lemma1_wroblewski {p q : ℕ} {r : ℤ} (hp : 0 < p)
    (x y z : Sphere p q r ((p + 1) / 2 : ℕ) ((p - 1) / 2 : ℕ))
    (h : val (2 * p - 1) x.digits + val (2 * p - 1) y.digits
          = 2 * val (2 * p - 1) z.digits) :
    x.digits = y.digits :=
  lemma1_nonaveraging hp x y z h

/-- 対照：`F` の代わりに **一次関数**（凸でない重み）を使うと、この論法は通らない。
    実際 `g k = k` では `g x + g y − 2 g z = 0` が `x + y = 2z` から常に従い、
    スラックが情報を持たない。 -/
example (x y z : ℕ) (h : x + y = 2 * z) :
    ((x : ℤ) + (y : ℤ)) - 2 * (z : ℤ) = 0 := by
  have : (x : ℤ) + (y : ℤ) = 2 * (z : ℤ) := by exact_mod_cast h
  linarith

end APFree.NonAveraging

/-! ### 公理の確認 -/

#print axioms APFree.NonAveraging.digits_eq
#print axioms APFree.NonAveraging.lemma1_nonaveraging
#print axioms APFree.NonAveraging.lemma1_wroblewski
