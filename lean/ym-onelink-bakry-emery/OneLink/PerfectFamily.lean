/-
超立方体の「完全な族」についての単独検査用の一枚版（`import Mathlib` だけ）。
-/
import Mathlib

/-!
# 超立方体の「完全な族」は `d ≥ 5` に存在しない

単位 `d` 立方体 `Q_d = {0,1}^d`（頂点は `Fin d → Bool`）の辺の族 `I` が **完全**であるとは、
`Q_d` のすべての 2 次元の面が `I` の辺をちょうど一本含むことをいう。

主定理 `PerfectFamily.no_perfect_of_five`：`d ≥ 5` なら完全な族は無い。
`ℤ^d` 版 `PerfectFamily.no_perfectZ_of_five`：`ℤ^d` の辺の族ですべてのプラケットを
ちょうど一本で覆うものは `d ≥ 5` に無い（周期性は仮定しない）。
`d = 3, 4` には在る（`PerfectFamily.perfect_I3`・`PerfectFamily.perfect_I4`）。

## 辺の表し方

方向 `μ` の辺は「`μ` 座標以外の値」で決まる。ここでは位置 `x : Fin d → Bool` の
`μ` 座標を `false` に正規化して `(μ, x)` と表す。面 `(μ, ν, z)`（`μ ≠ ν`・`z μ = z ν = false`）の
4 本の辺は `(μ, z)`・`(μ, z + e_ν)`・`(ν, z)`・`(ν, z + e_μ)` で、これらは相異なる
（`PerfectFamily.face_slots_ne`）。

## 証明の骨格

`cube3_bool`（`decide`）：3 次元の部分立方体の 6 枚の面の条件から、その中の方向 `μ` の
4 本の辺のうちちょうど一本が `I` に入る。これから

* `edge_ex`：どの `z` に対しても、2 座標 `{ν, lam}` の外で `z` と一致する `I` の `μ` 方向の辺が在る
* `edge_uniq`：2 座標の外で一致する `I` の `μ` 方向の辺は一本だけ（`C_μ` の最小距離は 3）

が出る。`d ≥ 5` なら `μ` 以外に相異なる 4 方向 `n1..n4` がとれて、
`x₁ = x₀ + e_{n1} + e_{n2} + e_{n3}`・`x₂ = x₀ + e_{n1} + e_{n2} + e_{n4}` が両方 `I` に
入ることが強制され、この二本は `{n3, n4}` の外で一致するので `edge_uniq` に反する。
-/

namespace PerfectFamily

/-- 単位 `d` 立方体の頂点。 -/
abbrev V (d : ℕ) : Type := Fin d → Bool

variable {d : ℕ}

/-- 第 `i` 座標を反転する（`x ↦ x + e_i`）。 -/
def flipAt (x : V d) (i : Fin d) : V d := Function.update x i (!x i)

@[simp] lemma flipAt_self (x : V d) (i : Fin d) : flipAt x i i = !x i := by
  simp [flipAt]

@[simp] lemma flipAt_of_ne (x : V d) {i j : Fin d} (h : j ≠ i) : flipAt x i j = x j :=
  Function.update_of_ne h _ _

/--
`I μ x`：方向 `μ`・位置 `x`（`x μ = false` に正規化）の辺が族に入る。

`Perfect I`：`μ ≠ ν`・`z μ = z ν = false` で決まるどの 2 次元の面についても、
その 4 本の辺 `(μ, z)`・`(μ, z+e_ν)`・`(ν, z)`・`(ν, z+e_μ)` のうちちょうど一本が `I` に入る。
-/
def Perfect (I : Fin d → V d → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ z : V d, z μ = false → z ν = false →
    (I μ z).toNat + (I μ (flipAt z ν)).toNat
      + (I ν z).toNat + (I ν (flipAt z μ)).toNat = 1

instance instDecidablePerfect (I : Fin d → V d → Bool) : Decidable (Perfect I) := by
  unfold Perfect; infer_instance

/-- 面 `(μ, ν, z)` の 4 つの枠は相異なる辺である。したがって `Perfect` の
「`toNat` の和が 1」は「4 本のうちちょうど一本」を表している。 -/
lemma face_slots_ne {μ ν : Fin d} (h : μ ≠ ν) {z : V d} (hμ : z μ = false) (hν : z ν = false) :
    ((μ, z) ≠ ((μ, flipAt z ν) : Fin d × V d)) ∧ ((ν, z) ≠ ((ν, flipAt z μ) : Fin d × V d)) ∧
      ((μ, z) ≠ ((ν, z) : Fin d × V d)) ∧ ((μ, z) ≠ ((ν, flipAt z μ) : Fin d × V d)) ∧
      ((μ, flipAt z ν) ≠ ((ν, z) : Fin d × V d)) ∧
      ((μ, flipAt z ν) ≠ ((ν, flipAt z μ) : Fin d × V d)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : z ν = flipAt z ν ν := congrArg (fun p : Fin d × V d => p.2 ν) hc
    rw [flipAt_self] at h2
    simp [hν] at h2
  · intro hc
    have h2 : z μ = flipAt z μ μ := congrArg (fun p : Fin d × V d => p.2 μ) hc
    rw [flipAt_self] at h2
    simp [hμ] at h2
  · exact fun hc => h (congrArg Prod.fst hc)
  · exact fun hc => h (congrArg Prod.fst hc)
  · exact fun hc => h (congrArg Prod.fst hc)
  · exact fun hc => h (congrArg Prod.fst hc)

/-- 3 座標 `μ, ν, lam` の値を `a, b, c` に置き換える。 -/
def upd3 (w : V d) (μ ν lam : Fin d) (a b c : Bool) : V d :=
  fun i => if i = μ then a else if i = ν then b else if i = lam then c else w i

@[simp] lemma upd3_mu (w : V d) (μ ν lam : Fin d) (a b c : Bool) :
    upd3 w μ ν lam a b c μ = a := by simp [upd3]

lemma upd3_nu (w : V d) {μ ν lam : Fin d} (h : ν ≠ μ) (a b c : Bool) :
    upd3 w μ ν lam a b c ν = b := by simp [upd3, h]

lemma upd3_lam (w : V d) {μ ν lam : Fin d} (h1 : lam ≠ μ) (h2 : lam ≠ ν) (a b c : Bool) :
    upd3 w μ ν lam a b c lam = c := by simp [upd3, h1, h2]

lemma upd3_other (w : V d) {μ ν lam i : Fin d} (h1 : i ≠ μ) (h2 : i ≠ ν) (h3 : i ≠ lam)
    (a b c : Bool) : upd3 w μ ν lam a b c i = w i := by simp [upd3, h1, h2, h3]

/-- 3 座標での一致と残りでの一致から等号。 -/
lemma ext3 {x y : V d} (μ ν lam : Fin d) (hμ : x μ = y μ) (hν : x ν = y ν) (hl : x lam = y lam)
    (h : ∀ i, i ≠ μ → i ≠ ν → i ≠ lam → x i = y i) : x = y := by
  funext i
  by_cases h1 : i = μ
  · subst h1; exact hμ
  by_cases h2 : i = ν
  · subst h2; exact hν
  by_cases h3 : i = lam
  · subst h3; exact hl
  exact h i h1 h2 h3

lemma flipAt_upd3_mu (w : V d) (μ ν lam : Fin d) (a b c : Bool) :
    flipAt (upd3 w μ ν lam a b c) μ = upd3 w μ ν lam (!a) b c := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · rw [flipAt_of_ne _ h]; simp [upd3, h]

lemma flipAt_upd3_nu (w : V d) {μ ν lam : Fin d} (hνμ : ν ≠ μ) (a b c : Bool) :
    flipAt (upd3 w μ ν lam a b c) ν = upd3 w μ ν lam a (!b) c := by
  funext i
  by_cases h : i = ν
  · subst h; rw [flipAt_self, upd3_nu w hνμ, upd3_nu w hνμ]
  · rw [flipAt_of_ne _ h]; simp [upd3, h]

lemma flipAt_upd3_lam (w : V d) {μ ν lam : Fin d} (h1 : lam ≠ μ) (h2 : lam ≠ ν) (a b c : Bool) :
    flipAt (upd3 w μ ν lam a b c) lam = upd3 w μ ν lam a b (!c) := by
  funext i
  by_cases h : i = lam
  · subst h; rw [flipAt_self, upd3_lam w h1 h2, upd3_lam w h1 h2]
  · rw [flipAt_of_ne _ h]; simp [upd3, h]

/-!
## 3 次元の部分立方体（有限判定）

`m b c`（`b` は `ν` 座標・`c` は `lam` 座標）＝方向 `μ` の 4 辺、`n a c`＝方向 `ν` の 4 辺、
`l a b`＝方向 `lam` の 4 辺。6 枚の面の条件から `Σ m = 1` が出る。
-/

/-- 3 次元の部分立方体の 6 枚の面の「ちょうど一本」から、方向 `μ` の 4 辺のうち
ちょうど一本が族に入る。`2^12 = 4096` 通りの有限判定。 -/
theorem cube3_bool : ∀ m00 m01 m10 m11 n00 n01 n10 n11 l00 l01 l10 l11 : Bool,
    m00.toNat + m10.toNat + n00.toNat + n10.toNat = 1 →
    m01.toNat + m11.toNat + n01.toNat + n11.toNat = 1 →
    m00.toNat + m01.toNat + l00.toNat + l10.toNat = 1 →
    m10.toNat + m11.toNat + l01.toNat + l11.toNat = 1 →
    n00.toNat + n01.toNat + l00.toNat + l01.toNat = 1 →
    n10.toNat + n11.toNat + l10.toNat + l11.toNat = 1 →
    m00.toNat + m01.toNat + m10.toNat + m11.toNat = 1 := by decide

/-- 相異なる 3 方向 `μ, ν, lam` と残りの座標の値 `w` で決まる 3 次元の部分立方体の中で、
方向 `μ` の 4 本の辺のうちちょうど一本が `I` に入る。 -/
theorem dir_count {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) (w : V d) :
    (I μ (upd3 w μ ν lam false false false)).toNat
      + (I μ (upd3 w μ ν lam false false true)).toNat
      + (I μ (upd3 w μ ν lam false true false)).toNat
      + (I μ (upd3 w μ ν lam false true true)).toNat = 1 := by
  have hνμ : ν ≠ μ := h1.symm
  have hlμ : lam ≠ μ := h2.symm
  have hlν : lam ≠ ν := h3.symm
  have e1 := hI μ ν h1 (upd3 w μ ν lam false false false) (upd3_mu _ _ _ _ _ _ _)
    (upd3_nu w hνμ _ _ _)
  have e2 := hI μ ν h1 (upd3 w μ ν lam false false true) (upd3_mu _ _ _ _ _ _ _)
    (upd3_nu w hνμ _ _ _)
  have e3 := hI μ lam h2 (upd3 w μ ν lam false false false) (upd3_mu _ _ _ _ _ _ _)
    (upd3_lam w hlμ hlν _ _ _)
  have e4 := hI μ lam h2 (upd3 w μ ν lam false true false) (upd3_mu _ _ _ _ _ _ _)
    (upd3_lam w hlμ hlν _ _ _)
  have e5 := hI ν lam h3 (upd3 w μ ν lam false false false) (upd3_nu w hνμ _ _ _)
    (upd3_lam w hlμ hlν _ _ _)
  have e6 := hI ν lam h3 (upd3 w μ ν lam true false false) (upd3_nu w hνμ _ _ _)
    (upd3_lam w hlμ hlν _ _ _)
  rw [flipAt_upd3_nu w hνμ, flipAt_upd3_mu] at e1 e2
  rw [flipAt_upd3_lam w hlμ hlν, flipAt_upd3_mu] at e3 e4
  rw [flipAt_upd3_lam w hlμ hlν, flipAt_upd3_nu w hνμ] at e5 e6
  simp only [Bool.not_false] at e1 e2 e3 e4 e5 e6
  exact cube3_bool _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6

/-- `Bool` を 2 つの `Bool` で選ぶ。 -/
def bsel (m00 m01 m10 m11 : Bool) : Bool → Bool → Bool
  | false, false => m00
  | false, true => m01
  | true, false => m10
  | true, true => m11

theorem four_ex : ∀ a b c e : Bool, a.toNat + b.toNat + c.toNat + e.toNat = 1 →
    a = true ∨ b = true ∨ c = true ∨ e = true := by decide

theorem four_uq : ∀ m00 m01 m10 m11 : Bool,
    m00.toNat + m01.toNat + m10.toNat + m11.toNat = 1 →
    ∀ b c b' c' : Bool, bsel m00 m01 m10 m11 b c = true →
      bsel m00 m01 m10 m11 b' c' = true → b = b' ∧ c = c' := by decide

lemma bsel_dir (I : Fin d → V d → Bool) (μ ν lam : Fin d) (w : V d) (b c : Bool) :
    bsel (I μ (upd3 w μ ν lam false false false)) (I μ (upd3 w μ ν lam false false true))
        (I μ (upd3 w μ ν lam false true false)) (I μ (upd3 w μ ν lam false true true)) b c
      = I μ (upd3 w μ ν lam false b c) := by
  cases b <;> cases c <;> rfl

/-- 3 次元の部分立方体の中の `μ` 方向の辺は一意。 -/
theorem dir_uniq {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) (w : V d) {b c b' c' : Bool}
    (hb : I μ (upd3 w μ ν lam false b c) = true)
    (hb' : I μ (upd3 w μ ν lam false b' c') = true) : b = b' ∧ c = c' :=
  four_uq _ _ _ _ (dir_count hI h1 h2 h3 w) b c b' c'
    (by rw [bsel_dir]; exact hb) (by rw [bsel_dir]; exact hb')

/-- 3 次元の部分立方体の中に `μ` 方向の辺が在る。 -/
theorem dir_ex {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) (w : V d) :
    ∃ b c : Bool, I μ (upd3 w μ ν lam false b c) = true := by
  rcases four_ex _ _ _ _ (dir_count hI h1 h2 h3 w) with h | h | h | h
  exacts [⟨false, false, h⟩, ⟨false, true, h⟩, ⟨true, false, h⟩, ⟨true, true, h⟩]

/-!
## 補題 B〜D の言い換え（射影の単射性＝最小距離 3、および全射性）
-/

/-- **最小距離 3**：`I` の `μ` 方向の二本の辺の位置が 2 座標 `{ν, lam}` の外で
一致すれば、同じ辺である。 -/
theorem edge_uniq {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) {x y : V d}
    (hxμ : x μ = false) (hyμ : y μ = false) (hx : I μ x = true) (hy : I μ y = true)
    (hag : ∀ i, i ≠ ν → i ≠ lam → x i = y i) : x = y := by
  have hνμ : ν ≠ μ := h1.symm
  have hlμ : lam ≠ μ := h2.symm
  have hlν : lam ≠ ν := h3.symm
  have ex : x = upd3 x μ ν lam false (x ν) (x lam) := by
    refine ext3 μ ν lam ?_ ?_ ?_ ?_
    · rw [upd3_mu]; exact hxμ
    · rw [upd3_nu x hνμ]
    · rw [upd3_lam x hlμ hlν]
    · intro i hi1 hi2 hi3; rw [upd3_other x hi1 hi2 hi3]
  have ey : y = upd3 x μ ν lam false (y ν) (y lam) := by
    refine ext3 μ ν lam ?_ ?_ ?_ ?_
    · rw [upd3_mu]; exact hyμ
    · rw [upd3_nu x hνμ]
    · rw [upd3_lam x hlμ hlν]
    · intro i hi1 hi2 hi3; rw [upd3_other x hi1 hi2 hi3]; exact (hag i hi2 hi3).symm
  have hx' : I μ (upd3 x μ ν lam false (x ν) (x lam)) = true := by rw [← ex]; exact hx
  have hy' : I μ (upd3 x μ ν lam false (y ν) (y lam)) = true := by rw [← ey]; exact hy
  obtain ⟨hb, hc⟩ := dir_uniq hI h1 h2 h3 x hx' hy'
  exact ext3 μ ν lam (by rw [hxμ, hyμ]) hb hc fun i _ hi2 hi3 => hag i hi2 hi3

/-- **射影の全射性**：どの `z`（`z μ = false`）についても、2 座標 `{ν, lam}` の外で
`z` と一致する `I` の `μ` 方向の辺が在る。 -/
theorem edge_ex {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) {z : V d} (hz : z μ = false) :
    ∃ x : V d, I μ x = true ∧ x μ = false ∧ ∀ i, i ≠ ν → i ≠ lam → x i = z i := by
  obtain ⟨b, c, hbc⟩ := dir_ex hI h1 h2 h3 z
  refine ⟨upd3 z μ ν lam false b c, hbc, upd3_mu _ _ _ _ _ _ _, ?_⟩
  intro i hi2 hi3
  by_cases hi1 : i = μ
  · subst hi1; rw [upd3_mu]; exact hz.symm
  · rw [upd3_other z hi1 hi2 hi3]

/-- **補題 D（射影の全単射）**：2 座標 `{ν, lam}` を落とす射影は、`I` の `μ` 方向の辺の
位置の集合 `C_μ` から `F_2^{[d]∖{μ,ν,lam}}` への全単射である。 -/
theorem proj_bijective {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) {z : V d} (hz : z μ = false) :
    ∃! x : V d, I μ x = true ∧ x μ = false ∧ ∀ i, i ≠ ν → i ≠ lam → x i = z i := by
  obtain ⟨x, hx, hxμ, hxag⟩ := edge_ex hI h1 h2 h3 hz
  refine ⟨x, ⟨hx, hxμ, hxag⟩, ?_⟩
  rintro y ⟨hy, hyμ, hyag⟩
  exact edge_uniq hI h1 h2 h3 hyμ hxμ hy hx
    fun i hi2 hi3 => (hyag i hi2 hi3).trans (hxag i hi2 hi3).symm

/-- **系 E（最小距離 3）**：`I` の `μ` 方向の相異なる二本の辺の位置が違う座標の集合は、
`μ` 以外のどの 2 座標 `{ν, lam}` にも収まらない。 -/
theorem diff_not_in_pair {I : Fin d → V d → Bool} (hI : Perfect I) {μ ν lam : Fin d}
    (h1 : μ ≠ ν) (h2 : μ ≠ lam) (h3 : ν ≠ lam) {x y : V d}
    (hxμ : x μ = false) (hyμ : y μ = false) (hx : I μ x = true) (hy : I μ y = true)
    (hne : x ≠ y) : ∃ i, i ≠ ν ∧ i ≠ lam ∧ x i ≠ y i := by
  by_contra hc
  refine hne (edge_uniq hI h1 h2 h3 hxμ hyμ hx hy fun i hi2 hi3 => ?_)
  by_contra hne2
  exact hc ⟨i, hi2, hi3, hne2⟩

/-! ## 主定理 -/

/-- `d ≥ 5` なら相異なる 5 方向がとれる。 -/
lemma exists_five {d : ℕ} (hd : 5 ≤ d) : ∃ μ n1 n2 n3 n4 : Fin d,
    μ ≠ n1 ∧ μ ≠ n2 ∧ μ ≠ n3 ∧ μ ≠ n4 ∧ n1 ≠ n2 ∧ n1 ≠ n3 ∧ n1 ≠ n4 ∧
      n2 ≠ n3 ∧ n2 ≠ n4 ∧ n3 ≠ n4 := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ne_eq, Fin.mk.injEq] <;> omega

/-- **定理 260（立方体版）**：`d ≥ 5` の単位 `d` 立方体には完全な族が無い。 -/
theorem no_perfect_of_five {d : ℕ} (hd : 5 ≤ d) (I : Fin d → V d → Bool) : ¬ Perfect I := by
  intro hI
  have bne : ∀ a b c : Bool, a ≠ c → b ≠ c → a = b := by decide
  have bnot : ∀ b : Bool, (!b) ≠ b := by decide
  obtain ⟨μ, n1, n2, n3, n4, hμ1, hμ2, hμ3, hμ4, h12, h13, h14, h23, h24, h34⟩ :=
    exists_five hd
  -- `x0` : `I` の `μ` 方向の辺（一本とる）
  obtain ⟨x0, hx0, hx0μ, -⟩ := edge_ex hI hμ1 hμ2 h12 (z := fun _ => false) rfl
  -- `x1` : `{n1, n2}` の外で `x0 + e_{n3}` と一致する `I` の `μ` 方向の辺
  obtain ⟨x1, hx1, hx1μ, hx1ag⟩ := edge_ex hI hμ1 hμ2 h12 (z := flipAt x0 n3)
    (by rw [flipAt_of_ne _ hμ3]; exact hx0μ)
  -- `x2` : `{n1, n2}` の外で `x0 + e_{n4}` と一致する `I` の `μ` 方向の辺
  obtain ⟨x2, hx2, hx2μ, hx2ag⟩ := edge_ex hI hμ1 hμ2 h12 (z := flipAt x0 n4)
    (by rw [flipAt_of_ne _ hμ4]; exact hx0μ)
  -- `x1` は `n3` で `x0` と違い、`{n1, n2, n3}` の外では一致する
  have hx1n3 : x1 n3 = !(x0 n3) := by
    have := hx1ag n3 h13.symm h23.symm
    rwa [flipAt_self] at this
  have hx1oth : ∀ i, i ≠ n1 → i ≠ n2 → i ≠ n3 → x1 i = x0 i := by
    intro i hi1 hi2 hi3
    rw [hx1ag i hi1 hi2, flipAt_of_ne _ hi3]
  -- `x1` は `n1` でも `n2` でも `x0` と違う（違わなければ距離 2 で一致してしまう）
  have hx1n1 : x1 n1 ≠ x0 n1 := by
    intro hc
    have : x1 = x0 := by
      refine edge_uniq hI hμ2 hμ3 h23 hx1μ hx0μ hx1 hx0 ?_
      intro i hi2 hi3
      by_cases hi1 : i = n1
      · subst hi1; exact hc
      · exact hx1oth i hi1 hi2 hi3
    rw [this] at hx1n3
    exact bnot (x0 n3) hx1n3.symm
  have hx1n2 : x1 n2 ≠ x0 n2 := by
    intro hc
    have : x1 = x0 := by
      refine edge_uniq hI hμ1 hμ3 h13 hx1μ hx0μ hx1 hx0 ?_
      intro i hi1 hi3
      by_cases hi2 : i = n2
      · subst hi2; exact hc
      · exact hx1oth i hi1 hi2 hi3
    rw [this] at hx1n3
    exact bnot (x0 n3) hx1n3.symm
  -- 同じことを `x2`・`n4` について
  have hx2n4 : x2 n4 = !(x0 n4) := by
    have := hx2ag n4 h14.symm h24.symm
    rwa [flipAt_self] at this
  have hx2oth : ∀ i, i ≠ n1 → i ≠ n2 → i ≠ n4 → x2 i = x0 i := by
    intro i hi1 hi2 hi4
    rw [hx2ag i hi1 hi2, flipAt_of_ne _ hi4]
  have hx2n1 : x2 n1 ≠ x0 n1 := by
    intro hc
    have : x2 = x0 := by
      refine edge_uniq hI hμ2 hμ4 h24 hx2μ hx0μ hx2 hx0 ?_
      intro i hi2 hi4
      by_cases hi1 : i = n1
      · subst hi1; exact hc
      · exact hx2oth i hi1 hi2 hi4
    rw [this] at hx2n4
    exact bnot (x0 n4) hx2n4.symm
  have hx2n2 : x2 n2 ≠ x0 n2 := by
    intro hc
    have : x2 = x0 := by
      refine edge_uniq hI hμ1 hμ4 h14 hx2μ hx0μ hx2 hx0 ?_
      intro i hi1 hi4
      by_cases hi2 : i = n2
      · subst hi2; exact hc
      · exact hx2oth i hi1 hi2 hi4
    rw [this] at hx2n4
    exact bnot (x0 n4) hx2n4.symm
  -- `x1` と `x2` は `{n3, n4}` の外で一致するので同じ辺。しかし `n3` で違う。
  have hxx : x1 = x2 := by
    refine edge_uniq hI hμ3 hμ4 h34 hx1μ hx2μ hx1 hx2 ?_
    intro i hi3 hi4
    by_cases hi1 : i = n1
    · subst hi1; exact bne _ _ _ hx1n1 hx2n1
    by_cases hi2 : i = n2
    · subst hi2; exact bne _ _ _ hx1n2 hx2n2
    · rw [hx1oth i hi1 hi2 hi3, hx2oth i hi1 hi2 hi4]
  have h3' : x2 n3 = x0 n3 := hx2oth n3 h13.symm h23.symm h34
  rw [hxx, h3'] at hx1n3
  exact bnot (x0 n3) hx1n3.symm

/-! ## `ℤ^d` 版（周期性を仮定しない） -/

/-- `ℤ^d` の頂点。 -/
abbrev W (d : ℕ) : Type := Fin d → ℤ

/-- 第 `i` 座標を 1 だけ進める（`x ↦ x + e_i`）。 -/
def shift (x : W d) (i : Fin d) : W d := Function.update x i (x i + 1)

/--
`J μ x`：`x` から `x + e_μ` へ向かう辺が族に入る。

`PerfectZ J`：どのプラケット `(μ, ν, x)`（`μ ≠ ν`）についても、その 4 辺
`(μ, x)`・`(μ, x+e_ν)`・`(ν, x)`・`(ν, x+e_μ)` のうちちょうど一本が `J` に入る。
-/
def PerfectZ (J : Fin d → W d → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : W d,
    (J μ x).toNat + (J μ (shift x ν)).toNat
      + (J ν x).toNat + (J ν (shift x μ)).toNat = 1

/-- 単位立方体 `{0,1}^d` の頂点を `ℤ^d` に埋め込む。 -/
def emb (x : V d) : W d := fun i => if x i then 1 else 0

lemma emb_flipAt {z : V d} {i : Fin d} (h : z i = false) :
    emb (flipAt z i) = shift (emb z) i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [emb, shift, h]
  · simp [emb, shift, flipAt_of_ne _ hj, Function.update_of_ne hj]

/-- **補題 A（制限）**：`ℤ^d` の完全な族を単位立方体に制限すると、
単位立方体の完全な族になる（面の 4 辺はすべてその立方体の辺だから）。 -/
theorem restrict_perfect {J : Fin d → W d → Bool} (hJ : PerfectZ J) :
    Perfect (fun μ x => J μ (emb x)) := by
  intro μ ν hμν z hzμ hzν
  simp only
  rw [emb_flipAt hzν, emb_flipAt hzμ]
  exact hJ μ ν hμν (emb z)

/-- **定理 260（格子版）**：`d ≥ 5` の `ℤ^d` には完全な族が無い（周期性は仮定しない）。 -/
theorem no_perfectZ_of_five {d : ℕ} (hd : 5 ≤ d) (J : Fin d → W d → Bool) : ¬ PerfectZ J :=
  fun hJ => no_perfect_of_five hd _ (restrict_perfect hJ)

/-! ## `d = 3, 4` には在る -/

/-- `d = 3` の完全な族の例（方向ごとに 1 本）。 -/
def I3 (μ : Fin 3) (x : V 3) : Bool :=
  if μ = 0 then (!x 1 && !x 2) else if μ = 1 then (!x 0 && x 2) else (x 0 && x 1)

/-- `d = 3` には完全な族が在る。 -/
theorem perfect_I3 : Perfect I3 := by decide

/-- `d = 4` の完全な族の例（`I_1 : x₂=x₃≠x₄`・`I_2 : x₃=x₄≠x₁`・
`I_3 : x₁=x₂=x₄`・`I_4 : x₁=x₃≠x₂` を単位立方体に制限したもの。方向ごとに 2 本で、
残り 3 座標で対心をなす＝長さ 3 の反復符号 `{000, 111}`）。 -/
def I4 (μ : Fin 4) (x : V 4) : Bool :=
  if μ = 0 then ((x 1 == x 2) && !(x 2 == x 3))
  else if μ = 1 then ((x 2 == x 3) && !(x 3 == x 0))
  else if μ = 2 then ((x 0 == x 1) && (x 1 == x 3))
  else ((x 0 == x 2) && !(x 2 == x 1))

/-- `d = 4` には完全な族が在る。 -/
theorem perfect_I4 : Perfect I4 := by decide


/-- `d = 2` の完全な族の例。 -/
def I2 (μ : Fin 2) (x : V 2) : Bool := if μ = 0 then !x 1 else false

/-- `d = 2` には完全な族が在る。 -/
theorem perfect_I2 : Perfect I2 := by decide

/-- `d ≤ 1` には 2 次元の面が無いので、どんな族も完全（空虚に真）。 -/
theorem perfect_of_le_one {d : ℕ} (hd : d ≤ 1) (I : Fin d → V d → Bool) : Perfect I := by
  intro μ ν hμν _ _ _
  exact absurd (Fin.val_injective (by have := μ.isLt; have := ν.isLt; omega)) hμν

/-! ## 対照（`decide` が機械的に真を返しているのではないことの確認） -/

/-- 陰性対照：空の族は完全でない（`d = 3`）。 -/
theorem not_perfect_empty3 : ¬ Perfect (fun (_ : Fin 3) (_ : V 3) => false) := by decide

/-- 陰性対照：全部の辺をとった族は完全でない（`d = 3`）。 -/
theorem not_perfect_full3 : ¬ Perfect (fun (_ : Fin 3) (_ : V 3) => true) := by decide

/-- 陰性対照：`I4` の方向 0 を全部に替えると完全でなくなる（`d = 4`）。 -/
theorem not_perfect_I4_broken :
    ¬ Perfect (fun (μ : Fin 4) (x : V 4) => if μ = 0 then true else I4 μ x) := by decide

/-- `d = 5` の系。 -/
theorem no_perfect_five (I : Fin 5 → V 5 → Bool) : ¬ Perfect I :=
  no_perfect_of_five (by norm_num) I

/-- `d = 5` の格子版の系。 -/
theorem no_perfectZ_five (J : Fin 5 → W 5 → Bool) : ¬ PerfectZ J :=
  no_perfectZ_of_five (by norm_num) J

/-! ## 公理の確認 -/

#print axioms PerfectFamily.cube3_bool
#print axioms PerfectFamily.dir_count
#print axioms PerfectFamily.dir_ex
#print axioms PerfectFamily.dir_uniq
#print axioms PerfectFamily.edge_ex
#print axioms PerfectFamily.edge_uniq
#print axioms PerfectFamily.face_slots_ne
#print axioms PerfectFamily.proj_bijective
#print axioms PerfectFamily.diff_not_in_pair
#print axioms PerfectFamily.exists_five
#print axioms PerfectFamily.no_perfect_of_five
#print axioms PerfectFamily.restrict_perfect
#print axioms PerfectFamily.no_perfectZ_of_five
#print axioms PerfectFamily.perfect_I3
#print axioms PerfectFamily.perfect_I4
#print axioms PerfectFamily.perfect_I2
#print axioms PerfectFamily.perfect_of_le_one
#print axioms PerfectFamily.not_perfect_empty3
#print axioms PerfectFamily.not_perfect_full3
#print axioms PerfectFamily.not_perfect_I4_broken
#print axioms PerfectFamily.no_perfect_five
#print axioms PerfectFamily.no_perfectZ_five

end PerfectFamily
