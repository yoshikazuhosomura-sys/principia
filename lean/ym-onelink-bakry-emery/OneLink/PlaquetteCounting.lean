/-
周期格子の辺の族の数え上げの上界 `4|I| ≤ d·L^d`・完全な族の密度ちょうど
`1/4`・そこから `d ≤ 4`、および `k`-cell 版 `k|I| ≤ L^d·C(d,k−1)`。
前段としてプラケットのパッキング（`PlaquettePacking`）の密度上界 `1/d` を含む。
`import Mathlib` だけで素の `lake env lean` を通る一枚版。

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/

/-
周期格子のパッキング（どのプラケットも高々一本）の密度上界 `1/d` と、その達成例。

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/
import Mathlib

namespace PlaquettePacking

/-! ## 1. 抽象版（頂点の型は何でもよい） -/

variable {d : ℕ} {X : Type*}

/--
`Packing sh I`：頂点の型 `X`・「方向 `i` に一歩進める」写像 `sh` を持つ格子の上で、
辺の族 `I : Fin d → X → Bool`（`I μ x` は `x` から `sh x μ` への辺）が
**どのプラケットも高々一本しか含まない**。

プラケット `(x; μ, ν)` の 4 辺は `(μ, x)`・`(μ, sh x ν)`・`(ν, x)`・`(ν, sh x μ)`。
-/
def Packing (sh : X → Fin d → X) (I : Fin d → X → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : X,
    (I μ x).toNat + (I μ (sh x ν)).toNat + (I ν x).toNat + (I ν (sh x μ)).toNat ≤ 1

/--
**芯（一方向性）**：`I` の辺が一つの頂点から二方向へ出ることはない。
`(μ, x)` と `(ν, x)` は同じプラケット `(x; μ, ν)` の 2 辺だから。

注意：「`I` はマッチング」は格子全体では**偽**である（同じ方向に一直線に並ぶ
`(μ, x)` と `(μ, sh x μ)` は共通のプラケットに載らないので、いくらでも繋げられる）。
言えるのは「各頂点で**正の向き**の辺は高々一本」であり、それで十分である。
-/
theorem not_two_dirs {sh : X → Fin d → X} {I : Fin d → X → Bool} (h : Packing sh I)
    {μ ν : Fin d} (hμν : μ ≠ ν) {x : X} (hμ : I μ x = true) (hν : I ν x = true) : False := by
  have hle := h μ ν hμν x
  rw [hμ, hν] at hle
  simp only [Bool.toNat_true] at hle
  omega

/-- 写像 `(μ, x) ↦ x` は `I` の辺の集合の上で単射。 -/
theorem snd_injOn {sh : X → Fin d → X} {I : Fin d → X → Bool} (h : Packing sh I)
    {p q : Fin d × X} (hp : I p.1 p.2 = true) (hq : I q.1 q.2 = true) (hpq : p.2 = q.2) :
    p = q := by
  by_cases hd : p.1 = q.1
  · exact Prod.ext hd hpq
  · exact absurd (not_two_dirs h hd hp (hpq ▸ hq)) id

/-- **抽象版の上界**：頂点が有限なら `|I| ≤ (頂点の数)`。 -/
theorem card_le_card_vertices [Fintype X] [DecidableEq X] {sh : X → Fin d → X}
    {I : Fin d → X → Bool} (h : Packing sh I) :
    (Finset.univ.filter (fun p : Fin d × X => I p.1 p.2 = true)).card ≤ Fintype.card X := by
  classical
  rw [← Finset.card_univ (α := X)]
  refine Finset.card_le_card_of_injOn (fun p => p.2) (fun p _ => Finset.mem_univ _) ?_
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
  exact snd_injOn h hp hq hpq

/-! ## 2. 周期格子 `(ZMod L)^d` -/

variable {L : ℕ}

/-- 周期格子の頂点。 -/
abbrev Wp (d L : ℕ) : Type := Fin d → ZMod L

/-- 第 `i` 座標を 1 だけ進める（`x ↦ x + e_i`）。 -/
def shiftp (x : Wp d L) (i : Fin d) : Wp d L := Function.update x i (x i + 1)

/--
`AtMostOne I`：周期格子 `(ZMod L)^d` の辺の族 `I` が、どのプラケットも高々一本しか含まない。
-/
def AtMostOne (I : Fin d → Wp d L → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wp d L,
    (I μ x).toNat + (I μ (shiftp x ν)).toNat
      + (I ν x).toNat + (I ν (shiftp x μ)).toNat ≤ 1

instance instDecidableAtMostOne [NeZero L] (I : Fin d → Wp d L → Bool) :
    Decidable (AtMostOne I) := by
  unfold AtMostOne; infer_instance

theorem atMostOne_iff_packing (I : Fin d → Wp d L → Bool) :
    AtMostOne I ↔ Packing (shiftp (d := d) (L := L)) I := Iff.rfl

/-- `I` の辺の集合（`Fin d × 頂点` の部分集合）。 -/
def edgeSet [NeZero L] (I : Fin d → Wp d L → Bool) : Finset (Fin d × Wp d L) :=
  Finset.univ.filter (fun p => I p.1 p.2 = true)

/-- 周期格子の頂点の数は `L^d`。 -/
theorem card_Wp [NeZero L] : Fintype.card (Wp d L) = L ^ d := by
  simp [Wp, ZMod.card]

/--
**主定理**：どのプラケットも高々一本しか含まない族の辺の本数は、頂点の数 `L^d` 以下。
-/
theorem card_edgeSet_le [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) :
    (edgeSet I).card ≤ L ^ d := by
  have := card_le_card_vertices (X := Wp d L) (sh := shiftp) h
  rwa [card_Wp] at this

/-- 辺の総数は `d · L^d`。 -/
theorem card_edges_total [NeZero L] : Fintype.card (Fin d × Wp d L) = d * L ^ d := by
  simp [Fintype.card_prod]

/--
**密度の形（自然数版）**：`d · |I| ≤ (辺の総数)`。すなわち密度 `|I|/(d·L^d) ≤ 1/d`。
-/
theorem density_le [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) :
    d * (edgeSet I).card ≤ Fintype.card (Fin d × Wp d L) := by
  rw [card_edges_total]
  exact Nat.mul_le_mul_left d (card_edgeSet_le h)

/-- **密度の形（有理数版）**：`|I| / (d·L^d) ≤ 1/d`（`d ≥ 1`）。 -/
theorem density_le_rat [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) (hd : 0 < d) :
    ((edgeSet I).card : ℚ) / (d * L ^ d) ≤ 1 / d := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLd : (0 : ℚ) < (L : ℚ) ^ d := pow_pos (by exact_mod_cast hL) d
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hd0 : (d : ℚ) ≠ 0 := ne_of_gt hdq
  have hL0 : ((L : ℚ)) ^ d ≠ 0 := ne_of_gt hLd
  have hcard : ((edgeSet I).card : ℚ) ≤ (L : ℚ) ^ d := by
    have := card_edgeSet_le h
    exact_mod_cast this
  calc ((edgeSet I).card : ℚ) / (d * L ^ d) ≤ ((L : ℚ) ^ d) / (d * L ^ d) := by gcongr
    _ = 1 / d := by field_simp

/-! ## 3. `ℤ^d` の有限の箱での版（周期性を仮定しない） -/

/-- `ℤ^d` の頂点。 -/
abbrev Wz (d : ℕ) : Type := Fin d → ℤ

/-- 第 `i` 座標を 1 だけ進める。 -/
def shiftz (x : Wz d) (i : Fin d) : Wz d := Function.update x i (x i + 1)

/--
`AtMostOneZ J`：`ℤ^d` の辺の族 `J` が、どのプラケットも高々一本しか含まない。
-/
def AtMostOneZ (J : Fin d → Wz d → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wz d,
    (J μ x).toNat + (J μ (shiftz x ν)).toNat
      + (J ν x).toNat + (J ν (shiftz x μ)).toNat ≤ 1

/--
**箱の版**：`ℤ^d` のパッキング `J` の辺が有限集合 `S` の頂点からしか出ていないなら、
そのような辺は高々 `|S|` 本。（`S` は箱でも何でもよい。周期性を仮定しない。）
-/
theorem card_le_of_support [DecidableEq (Wz d)] {J : Fin d → Wz d → Bool} (h : AtMostOneZ J)
    (S : Finset (Wz d)) (T : Finset (Fin d × Wz d))
    (hT : ∀ p ∈ T, J p.1 p.2 = true ∧ p.2 ∈ S) : T.card ≤ S.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => p.2) (fun p hp => (hT p hp).2) ?_
  intro p hp q hq hpq
  have hp' := hT p (by simpa using hp)
  have hq' := hT q (by simpa using hq)
  exact snd_injOn (sh := shiftz) h hp'.1 hq'.1 hpq



/-! ## 4. 完全な族（どのプラケットもちょうど一本）と上界の達成 -/


/-- 周期格子の**完全な族**：どのプラケットもちょうど一本を含む。 -/
def PerfectP (I : Fin d → Wp d L → Bool) : Prop :=
  ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wp d L,
    (I μ x).toNat + (I μ (shiftp x ν)).toNat
      + (I ν x).toNat + (I ν (shiftp x μ)).toNat = 1

instance instDecidablePerfectP [NeZero L] (I : Fin d → Wp d L → Bool) :
    Decidable (PerfectP I) := by
  unfold PerfectP; infer_instance

theorem perfectP_atMostOne {I : Fin d → Wp d L → Bool} (h : PerfectP I) : AtMostOne I :=
  fun μ ν hμν x => le_of_eq (h μ ν hμν x)

/--
`d = 4`・周期 2 の完全な族 `A4`。方向ごとに「残り 3 座標の長さ 3 の反復符号」で書ける
（全数探索が出した 8 通りのうちの一つ）。
-/
def A4 (μ : Fin 4) (x : Wp 4 2) : Bool :=
  if μ = 0 then (x 1 == x 2) && (x 2 == x 3)
  else if μ = 1 then (x 0 == x 3) && !(x 2 == x 0)
  else if μ = 2 then (x 0 == x 1) && !(x 3 == x 0)
  else (x 0 == x 2) && !(x 1 == x 0)

/-- `A4` と互いに素な、もう一つの `d = 4`・周期 2 の完全な族 `B4`。 -/
def B4 (μ : Fin 4) (x : Wp 4 2) : Bool :=
  if μ = 0 then (x 2 == x 3) && !(x 1 == x 2)
  else if μ = 1 then (x 0 == x 2) && !(x 3 == x 0)
  else if μ = 2 then (x 0 == x 1) && (x 3 == x 0)
  else (x 1 == x 2) && !(x 0 == x 1)

theorem A4_perfect : PerfectP A4 := by decide

theorem B4_perfect : PerfectP B4 := by decide

theorem A4_atMostOne : AtMostOne A4 := perfectP_atMostOne A4_perfect

/-- `A4` と `B4` は辺を共有しない。 -/
theorem A4_B4_disjoint : ∀ (μ : Fin 4) (x : Wp 4 2), A4 μ x = false ∨ B4 μ x = false := by decide

theorem A4_card : (edgeSet A4).card = 16 := by decide

theorem B4_card : (edgeSet B4).card = 16 := by decide

/--
**上界は `d = 4` でちょうど達成される**：`|A4| = 頂点の数 = 2^4`。
（密度は `16 / (4·16) = 1/4 = 1/d`。）
-/
theorem bound_tight_d4 : (edgeSet A4).card = Fintype.card (Wp 4 2) := by
  rw [A4_card, card_Wp]; norm_num

/-! ## 5. `d = 5` で密度 `1/5` を達成する族（層の偶奇で `A4`・`B4` を入れ替える） -/

/--
`d = 5`・周期 2 のパッキング：5 番目の座標 `x 4` の偶奇で `A4` と `B4` を切り替え、
方向 4 の辺は一本も採らない。
-/
def P5 (μ : Fin 5) (x : Wp 5 2) : Bool :=
  if x 4 = 0 then
    (if μ = 0 then (x 1 == x 2) && (x 2 == x 3)
     else if μ = 1 then (x 0 == x 3) && !(x 2 == x 0)
     else if μ = 2 then (x 0 == x 1) && !(x 3 == x 0)
     else if μ = 3 then (x 0 == x 2) && !(x 1 == x 0)
     else false)
  else
    (if μ = 0 then (x 2 == x 3) && !(x 1 == x 2)
     else if μ = 1 then (x 0 == x 2) && !(x 3 == x 0)
     else if μ = 2 then (x 0 == x 1) && (x 3 == x 0)
     else if μ = 3 then (x 1 == x 2) && !(x 0 == x 1)
     else false)

theorem P5_atMostOne : AtMostOne P5 := by decide

theorem P5_card : (edgeSet P5).card = 32 := by decide

/-- `P5` は完全な族ではない（`d ≥ 5` には完全な族が無い）。 -/
theorem P5_not_perfect : ¬ PerfectP P5 := by decide

/--
**`d = 5` で上界は達成される**：`|P5| = 頂点の数 = 2^5`。
つまり `density_le` の不等式 `d·|I| ≤ (辺の総数)` が等号になる（密度ちょうど `1/5`）。
-/
theorem bound_tight_d5 : (edgeSet P5).card = Fintype.card (Wp 5 2) := by
  rw [P5_card, card_Wp]; norm_num

theorem density_eq_d5 : 5 * (edgeSet P5).card = Fintype.card (Fin 5 × Wp 5 2) := by
  rw [P5_card, card_edges_total]; norm_num

/-! ## 6. 対照：格子全体では `I` はマッチングでない -/

/-- `d = 2`・周期 4 の格子で、方向 0・`x 1 = 0` の 4 本の辺（閉じた一直線）。 -/
def Line (μ : Fin 2) (x : Wp 2 4) : Bool := (μ == 0) && (x 1 == 0)

theorem Line_atMostOne : AtMostOne Line := by decide

theorem Line_card : (edgeSet Line).card = 4 := by decide

/--
**`I` はマッチングでない**：`Line` には頂点を共有する二辺（一直線に並ぶ `(0, x)` と `(0, x+e_0)`）
が在る。プラケットのパッキングはマッチングより弱い条件である。
-/
theorem Line_not_matching : ∃ x : Wp 2 4, Line 0 x = true ∧ Line 0 (shiftp x 0) = true := by
  decide

/-- 陰性対照：一つの頂点から二方向に出る族はパッキングでない。 -/
theorem not_atMostOne_two_dirs :
    ¬ AtMostOne (fun (_μ : Fin 2) (x : Wp 2 4) => (x 0 == 0) && (x 1 == 0)) := by decide

/-- 陰性対照：全部の辺を採る族はパッキングでない。 -/
theorem not_atMostOne_full : ¬ AtMostOne (fun (_ : Fin 2) (_ : Wp 2 4) => true) := by decide

/-- 陽性対照（自明な側）：空の族はパッキング。 -/
theorem atMostOne_empty : AtMostOne (fun (_ : Fin 2) (_ : Wp 2 4) => false) := by decide


/-! ## 7. 公理の確認 -/

#print axioms not_two_dirs
#print axioms snd_injOn
#print axioms card_le_card_vertices
#print axioms atMostOne_iff_packing
#print axioms card_Wp
#print axioms card_edgeSet_le
#print axioms card_edges_total
#print axioms density_le
#print axioms density_le_rat
#print axioms card_le_of_support
#print axioms perfectP_atMostOne
#print axioms A4_perfect
#print axioms B4_perfect
#print axioms A4_atMostOne
#print axioms A4_B4_disjoint
#print axioms A4_card
#print axioms B4_card
#print axioms bound_tight_d4
#print axioms P5_atMostOne
#print axioms P5_card
#print axioms P5_not_perfect
#print axioms bound_tight_d5
#print axioms density_eq_d5
#print axioms Line_atMostOne
#print axioms Line_card
#print axioms Line_not_matching
#print axioms not_atMostOne_two_dirs
#print axioms not_atMostOne_full
#print axioms atMostOne_empty

end PlaquettePacking


/-
周期格子 `(ZMod L)^d` の辺の族の **数え上げの上界** `4|I| ≤ d·L^d`（密度 `≤ 1/4`）と、
**完全な族**（どのプラケットもちょうど一本）の密度がちょうど `1/4` であること `4|I| = d·L^d`。
パッキングの `|I| ≤ L^d`（頂点の上界）と合わせると **完全な族が在れば `d ≤ 4`** が二行で出る。

二重数え上げ：組 `(辺 e ∈ I, e を含むプラケット p)` を数える。プラケットを
**順序対 `(μ,ν)`, `μ ≠ ν` と基点 `x`** で数えると、辺 `(μ,x)` は
  `(x; μ,ν)` の第 1 枠・`(x−e_ν; μ,ν)` の第 2 枠・`(x; ν,μ)` の第 3 枠・`(x−e_ν; ν,μ)` の第 4 枠
として、`ν ≠ μ` の選び方ごとに 4 回現れる ⟹ 総和は `4(d−1)|I|`。
**`L = 2`（`x + e_ν = x − e_ν`）でも数え方は変わらない**——使うのは平行移動
`x ↦ x + e_ν` が頂点の上の全単射であることだけで、`L` に条件は要らない。

自然数の引き算を避けるため、`4(d−1)N` は `S + 4N = 4dN` の形で書く。

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/

namespace PlaquetteCounting

open PlaquettePacking

variable {d L : ℕ}

/-! ## 1. 平行移動は頂点の上の全単射（ここだけが「格子」を使う） -/

/-- `x ↦ x + e_ν` は `(ZMod L)^d` の上の全単射（逆は `x ↦ x − e_ν`）。 -/
theorem shiftp_bijective [NeZero L] (ν : Fin d) :
    Function.Bijective (fun x : Wp d L => shiftp x ν) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => Function.update y ν (y ν - 1), ?_, ?_⟩
  · intro x
    funext i
    rcases eq_or_ne i ν with h | h
    · subst h; simp [shiftp]
    · simp [shiftp, h]
  · intro y
    funext i
    rcases eq_or_ne i ν with h | h
    · subst h; simp [shiftp]
    · simp [shiftp, h]

/-- 平行移動での添字の付け替え：`∑_x f(x + e_ν) = ∑_x f(x)`。 -/
theorem sum_shiftp [NeZero L] (f : Wp d L → ℕ) (ν : Fin d) :
    ∑ x : Wp d L, f (shiftp x ν) = ∑ x : Wp d L, f x :=
  Fintype.sum_bijective _ (shiftp_bijective ν) _ _ (fun _ => rfl)

/-! ## 2. プラケットの中の本数・方向ごとの本数 -/

/-- プラケット `(x; μ, ν)` の 4 辺のうち `I` に入っている本数。 -/
def plaqCount (I : Fin d → Wp d L → Bool) (μ ν : Fin d) (x : Wp d L) : ℕ :=
  (I μ x).toNat + (I μ (shiftp x ν)).toNat + (I ν x).toNat + (I ν (shiftp x μ)).toNat

/-- 方向 `μ` の辺の本数。 -/
def dirCount [NeZero L] (I : Fin d → Wp d L → Bool) (μ : Fin d) : ℕ :=
  ∑ x : Wp d L, (I μ x).toNat

theorem atMostOne_iff_plaqCount (I : Fin d → Wp d L → Bool) :
    AtMostOne I ↔ ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wp d L, plaqCount I μ ν x ≤ 1 := Iff.rfl

theorem perfectP_iff_plaqCount (I : Fin d → Wp d L → Bool) :
    PerfectP I ↔ ∀ μ ν : Fin d, μ ≠ ν → ∀ x : Wp d L, plaqCount I μ ν x = 1 := Iff.rfl

/-- 辺の本数は方向ごとの本数の和。 -/
theorem card_edgeSet_eq_sum [NeZero L] (I : Fin d → Wp d L → Bool) :
    (edgeSet I).card = ∑ μ : Fin d, dirCount I μ := by
  classical
  rw [edgeSet, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [dirCount]
  refine Finset.sum_congr rfl fun x _ => ?_
  cases I μ x <;> simp

/-- **枠の数え直し**：一つのプラケットの 4 枠を `x` 全体で足すと `2·(方向 μ) + 2·(方向 ν)`。
平行移動の全単射だけを使うので `L = 2` でも同じ。 -/
theorem sum_x_plaqCount [NeZero L] (I : Fin d → Wp d L → Bool) (μ ν : Fin d) :
    ∑ x : Wp d L, plaqCount I μ ν x = 2 * dirCount I μ + 2 * dirCount I ν := by
  have h1 : (∑ x : Wp d L, (I μ (shiftp x ν)).toNat) = ∑ x : Wp d L, (I μ x).toNat :=
    sum_shiftp (fun y => (I μ y).toNat) ν
  have h2 : (∑ x : Wp d L, (I ν (shiftp x μ)).toNat) = ∑ x : Wp d L, (I ν x).toNat :=
    sum_shiftp (fun y => (I ν y).toNat) μ
  simp only [plaqCount, dirCount]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2]
  ring

/-! ## 3. 数え上げの骨（`Fin n` の非対角の和・引き算を避けた形） -/

/-- 補助（自然数の算術）：`S + u = n·u` と `S + v = n·v` なら `u = v`（`n ≥ 2`）。 -/
theorem eq_of_add_eq_mul {S u v n : ℕ} (hn : 2 ≤ n) (hu : S + u = n * u) (hv : S + v = n * v) :
    u = v := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have he : 0 < e := by omega
  have h1 : S = e * u := Nat.add_right_cancel (m := u) (by rw [hu]; ring)
  have h2 : S = e * v := Nat.add_right_cancel (m := v) (by rw [hv]; ring)
  exact Nat.eq_of_mul_eq_mul_left he (h1.symm.trans h2)

/-- 補助（自然数の算術）：`S + u = n·u`・`W + v = n·v`・`S ≤ W` なら `u ≤ v`（`n ≥ 2`）。 -/
theorem le_of_add_eq_mul {S W u v n : ℕ} (hn : 2 ≤ n) (hu : S + u = n * u) (hv : W + v = n * v)
    (hSW : S ≤ W) : u ≤ v := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  have he : 0 < e := by omega
  have h1 : S = e * u := Nat.add_right_cancel (m := u) (by rw [hu]; ring)
  have h2 : W = e * v := Nat.add_right_cancel (m := v) (by rw [hv]; ring)
  exact Nat.le_of_mul_le_mul_left (h1 ▸ h2 ▸ hSW) he

theorem add4_of_add2 {P X T m : ℕ} (h1 : P + 2 * T = m) (h2 : X + 2 * T = m) :
    P + X + 4 * T = 2 * m := by omega

/-- **非対角の和（変数版）**：順序対 `(μ,ν)`, `μ ≠ ν` について `2A μ + 2A ν` を足すと
`4(n−1)∑A`（＝ `S + 4∑A = 4n∑A`）。 -/
theorem sum_erase_two {n : ℕ} (A : Fin n → ℕ) :
    (∑ μ : Fin n, ∑ ν ∈ Finset.univ.erase μ, (2 * A μ + 2 * A ν)) + 4 * (∑ μ : Fin n, A μ)
      = 4 * n * ∑ μ : Fin n, A μ := by
  have hsplit : (∑ μ : Fin n, ∑ ν ∈ Finset.univ.erase μ, (2 * A μ + 2 * A ν))
      = (∑ μ : Fin n, ∑ _ν ∈ Finset.univ.erase μ, 2 * A μ)
        + (∑ μ : Fin n, ∑ ν ∈ Finset.univ.erase μ, 2 * A ν) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_add_distrib
  have h1 : (∑ μ : Fin n, ∑ _ν ∈ Finset.univ.erase μ, 2 * A μ) + 2 * (∑ μ : Fin n, A μ)
      = 2 * n * ∑ μ : Fin n, A μ := by
    have step : ∀ μ : Fin n, (∑ _ν ∈ Finset.univ.erase μ, 2 * A μ) + 2 * A μ = n * (2 * A μ) :=
      fun μ => by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ μ), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
    calc (∑ μ : Fin n, ∑ _ν ∈ Finset.univ.erase μ, 2 * A μ) + 2 * (∑ μ : Fin n, A μ)
        = ∑ μ : Fin n, ((∑ _ν ∈ Finset.univ.erase μ, 2 * A μ) + 2 * A μ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ μ : Fin n, n * (2 * A μ) := Finset.sum_congr rfl fun μ _ => step μ
      _ = 2 * n * ∑ μ : Fin n, A μ := by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  have h2 : (∑ μ : Fin n, ∑ ν ∈ Finset.univ.erase μ, 2 * A ν) + 2 * (∑ μ : Fin n, A μ)
      = 2 * n * ∑ μ : Fin n, A μ := by
    have step : ∀ μ : Fin n, (∑ ν ∈ Finset.univ.erase μ, 2 * A ν) + 2 * A μ
        = 2 * ∑ ν : Fin n, A ν := fun μ => by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ μ), Finset.mul_sum]
    calc (∑ μ : Fin n, ∑ ν ∈ Finset.univ.erase μ, 2 * A ν) + 2 * (∑ μ : Fin n, A μ)
        = ∑ μ : Fin n, ((∑ ν ∈ Finset.univ.erase μ, 2 * A ν) + 2 * A μ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ _μ : Fin n, 2 * ∑ ν : Fin n, A ν := Finset.sum_congr rfl fun μ _ => step μ
      _ = 2 * n * ∑ μ : Fin n, A μ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  rw [hsplit, add4_of_add2 h1 h2]
  ring

/-- **非対角の和（定数版）**：順序対 `(μ,ν)`, `μ ≠ ν` について定数 `c` を足すと
`n(n−1)c`（＝ `S + nc = n(nc)`）。 -/
theorem sum_erase_const {n : ℕ} (c : ℕ) :
    (∑ μ : Fin n, ∑ _ν ∈ Finset.univ.erase μ, c) + n * c = n * (n * c) := by
  have step : ∀ μ : Fin n, (∑ _ν ∈ Finset.univ.erase μ, c) + c = n * c := fun μ => by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ μ), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  calc (∑ μ : Fin n, ∑ _ν ∈ Finset.univ.erase μ, c) + n * c
      = ∑ μ : Fin n, ((∑ _ν ∈ Finset.univ.erase μ, c) + c) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
    _ = ∑ _μ : Fin n, n * c := Finset.sum_congr rfl fun μ _ => step μ
    _ = n * (n * c) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## 4. 二重数え上げの恒等式 -/

/-- **恒等式（本体）**：プラケットの中の `I` の本数を順序対 `(μ,ν)` と基点 `x` で総和すると
`4(d−1)|I|`（引き算を避けた形 `S + 4|I| = 4d|I|`）。**`I` に仮定は要らない。** -/
theorem sum_plaqCount_add [NeZero L] (I : Fin d → Wp d L → Bool) :
    (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      + 4 * (edgeSet I).card = 4 * d * (edgeSet I).card := by
  have hrw : (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      = ∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, (2 * dirCount I μ + 2 * dirCount I ν) :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => sum_x_plaqCount I μ ν
  rw [hrw, card_edgeSet_eq_sum I]
  exact sum_erase_two (dirCount I)

/-- 完全な族なら、プラケットの総和はプラケットの個数（順序対で数えたもの）に等しい。 -/
theorem sum_plaqCount_perfect [NeZero L] {I : Fin d → Wp d L → Bool} (h : PerfectP I) :
    (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      + d * L ^ d = d * (d * L ^ d) := by
  have inner : ∀ μ : Fin d, ∀ ν ∈ Finset.univ.erase μ,
      (∑ x : Wp d L, plaqCount I μ ν x) = L ^ d := by
    intro μ ν hν
    have hne : μ ≠ ν := Ne.symm (Finset.mem_erase.1 hν).1
    calc (∑ x : Wp d L, plaqCount I μ ν x) = ∑ _x : Wp d L, 1 :=
          Finset.sum_congr rfl fun x _ => h μ ν hne x
      _ = L ^ d := by simp
  have hrw : (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      = ∑ μ : Fin d, ∑ _ν ∈ Finset.univ.erase μ, L ^ d :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl (inner μ)
  rw [hrw]
  exact sum_erase_const (L ^ d)

/-- どのプラケットも高々一本なら、プラケットの総和はプラケットの個数以下。 -/
theorem sum_plaqCount_le [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) :
    (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      ≤ ∑ μ : Fin d, ∑ _ν ∈ Finset.univ.erase μ, L ^ d := by
  refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν hν => ?_
  have hne : μ ≠ ν := Ne.symm (Finset.mem_erase.1 hν).1
  calc (∑ x : Wp d L, plaqCount I μ ν x) ≤ ∑ _x : Wp d L, 1 :=
        Finset.sum_le_sum fun x _ => h μ ν hne x
    _ = L ^ d := by simp

/-! ## 5. 主結果 -/

/-- **(2) 数え上げの上界**：どのプラケットも高々一本なら `4|I| ≤ d·L^d`（密度 `≤ 1/4`）。
`d ≥ 2` は落とせない（`d = 1` ではプラケットが無く、全部の辺が採れる）。 -/
theorem four_mul_card_le [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) (hd : 2 ≤ d) :
    4 * (edgeSet I).card ≤ d * L ^ d := by
  have hu : (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      + 4 * (edgeSet I).card = d * (4 * (edgeSet I).card) := by
    rw [sum_plaqCount_add I]; ring
  exact le_of_add_eq_mul hd hu (sum_erase_const (n := d) (L ^ d)) (sum_plaqCount_le h)

/-- **(1) 完全な族の密度はちょうど `1/4`**：`4|I| = d·L^d`。 -/
theorem four_mul_card_eq [NeZero L] {I : Fin d → Wp d L → Bool} (h : PerfectP I) (hd : 2 ≤ d) :
    4 * (edgeSet I).card = d * L ^ d := by
  have hu : (∑ μ : Fin d, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp d L, plaqCount I μ ν x)
      + 4 * (edgeSet I).card = d * (4 * (edgeSet I).card) := by
    rw [sum_plaqCount_add I]; ring
  exact eq_of_add_eq_mul hd hu (sum_plaqCount_perfect h)

/-- **主定理（二行）**：周期格子に完全な族が在れば `d ≤ 4`。
`d·L^d = 4|I| ≤ 4·L^d`（パッキングの頂点の上界）で割るだけ。 -/
theorem perfect_torus_d_le_four [NeZero L] {I : Fin d → Wp d L → Bool} (h : PerfectP I) :
    d ≤ 4 := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · omega
  have h1 : 4 * (edgeSet I).card = d * L ^ d := four_mul_card_eq h hd
  have h2 : (edgeSet I).card ≤ L ^ d := card_edgeSet_le (perfectP_atMostOne h)
  have hL : 0 < L ^ d := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) d
  have h3 : d * L ^ d ≤ 4 * L ^ d := by
    rw [← h1]
    exact Nat.mul_le_mul_left 4 h2
  exact Nat.le_of_mul_le_mul_right h3 hL

/-- **系（割り切れ条件）**：完全な族が在れば `4 ∣ d·L^d`。 -/
theorem four_dvd_of_perfect [NeZero L] {I : Fin d → Wp d L → Bool} (h : PerfectP I) (hd : 2 ≤ d) :
    4 ∣ d * L ^ d :=
  ⟨(edgeSet I).card, (four_mul_card_eq h hd).symm⟩

/-! ## 6. 密度（有理数版） -/

theorem density_le_quarter [NeZero L] {I : Fin d → Wp d L → Bool} (h : AtMostOne I) (hd : 2 ≤ d) :
    ((edgeSet I).card : ℚ) / ((d : ℚ) * (L : ℚ) ^ d) ≤ 1 / 4 := by
  have hLpos : (0 : ℚ) < (L : ℚ) ^ d :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) d
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hq : (4 : ℚ) * ((edgeSet I).card : ℚ) ≤ (d : ℚ) * (L : ℚ) ^ d := by
    have := four_mul_card_le h hd
    exact_mod_cast this
  rw [div_le_div_iff₀ (mul_pos hdpos hLpos) (by norm_num : (0 : ℚ) < 4)]
  linarith

theorem density_eq_quarter [NeZero L] {I : Fin d → Wp d L → Bool} (h : PerfectP I) (hd : 2 ≤ d) :
    ((edgeSet I).card : ℚ) / ((d : ℚ) * (L : ℚ) ^ d) = 1 / 4 := by
  have hLpos : (0 : ℚ) < (L : ℚ) ^ d :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) d
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hq : (4 : ℚ) * ((edgeSet I).card : ℚ) = (d : ℚ) * (L : ℚ) ^ d := by
    have := four_mul_card_eq h hd
    exact_mod_cast this
  have hcard : ((edgeSet I).card : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact absurd hq.symm (ne_of_gt (mul_pos hdpos hLpos))
  rw [← hq]
  field_simp

/-! ## 7. 具体の枡（陽性・陰性対照） -/

/-- **`d = 3`・`L = 2`**：数え上げの上界は `|I| ≤ 6`。パッキングの頂点の上界 `8` より強く、
全数探索の最大 6 と一致する。 -/
theorem card_le_six_d3L2 {I : Fin 3 → Wp 3 2 → Bool} (h : AtMostOne I) :
    (edgeSet I).card ≤ 6 := by
  have h1 := four_mul_card_le h (by norm_num)
  norm_num at h1
  omega

/-- **`d = 3`・`L = 3`**：完全な族は無い（`4 ∤ 3·27 = 81`）。
「`d ≤ 4`」とは別の理由（割り切れ）で落ちる枡。 -/
theorem no_perfect_d3L3 : ¬ ∃ I : Fin 3 → Wp 3 3 → Bool, PerfectP I := by
  rintro ⟨I, h⟩
  have h1 := four_dvd_of_perfect h (by norm_num)
  norm_num at h1

/-- **`d = 2`・`L = 3`**：完全な族は無い（`4 ∤ 2·9 = 18`）。 -/
theorem no_perfect_d2L3 : ¬ ∃ I : Fin 2 → Wp 2 3 → Bool, PerfectP I := by
  rintro ⟨I, h⟩
  have h1 := four_dvd_of_perfect h (by norm_num)
  norm_num at h1

/-- 陽性対照：`d=4`・`L=2` の完全な族 `A4` で、定理の値と実測の `|A4| = 16` が合う。 -/
theorem A4_consistent : 4 * (edgeSet A4).card = 4 * 2 ^ 4 ∧ (edgeSet A4).card = 16 :=
  ⟨four_mul_card_eq A4_perfect (by norm_num), A4_card⟩

/-- 陽性対照：`d=5`・`L=2` の `P5` は上界 `1/4` に**余裕がある**
（`4·32 = 128 < 160 = 5·2^5`）。`d ≥ 5` では `1/d` の側が効く、という両上界の住み分け。 -/
theorem P5_bound_slack : 4 * (edgeSet P5).card < 5 * 2 ^ 5 := by
  rw [P5_card]; norm_num

/-- 陰性対照：全部の辺を採る族（`d=2`・`L=4`）は上界を破る。
`4·32 = 128 > 32 = 2·4^2` ⟹ 仮定 `AtMostOne` は働いている。 -/
theorem full_violates_bound :
    ¬ (4 * (edgeSet (fun (_ : Fin 2) (_ : Wp 2 4) => true)).card ≤ 2 * 4 ^ 2) := by
  decide

/-- 陽性対照（恒等式そのものの核による検算）：`d=2`・`L=4` の `Line`（`|I| = 4`）で
プラケットの総和は `4(d−1)|I| = 4·1·4 = 16`。カーネルの評価で確かめる。 -/
theorem sum_plaq_Line :
    (∑ μ : Fin 2, ∑ ν ∈ Finset.univ.erase μ, ∑ x : Wp 2 4, plaqCount Line μ ν x) = 16 := by
  decide

end PlaquetteCounting


/-
`k`-cell 版（`k = m+1` と書く）。

`k`-cell ＝（方向集合 `S : Finset (Fin d)`, `|S| = k`）と基点 `x`。
`(k+1)`-cell `(T, x)`（`|T| = k+1`）の面は、`ν ∈ T` ごとに `(T \ {ν}, x)` と
`(T \ {ν}, x + e_ν)` の 2 枚、計 `2(k+1)` 枚。

- **芯 (i)**（`not_share_m`）：同じ基点の二つの選ばれた `k`-cell は `k−1` 個の方向を共有できない
  （共有すると `T = S ∪ S'` が `(k+1)`-cell になり、`S` と `S'` がその 2 枚の面になる）
- ⟹ 選ばれた `S` たちの `(k−1)`-部分集合の族は互いに素（`disjoint_powersetCard_of_pack`）
- ⟹ 基点ごとに `k·|F(x)| ≤ C(d, k−1)`（`card_cellsAt_le`）
- ⟹ 全体で `k·|I| ≤ L^d·C(d, k−1)`（`card_cellSet_le`）。`k`-cell の総数は `L^d·C(d,k)` なので
  密度は `C(d,k−1)/(k·C(d,k)) = 1/(d−k+1)` 以下
- `m = 0`（`k = 1`）はパッキングの `|I| ≤ L^d` と同じ値（`card_cellSet_le_zero`）

組合せの補題であって、Clay の問題（連続極限・質量ギャップ）への主張は無い。
-/

namespace PlaquetteCounting

open PlaquettePacking

variable {d L : ℕ}

/-! ## 8. `k`-cell（`k = m+1`）のパッキング -/

/-- `(k+1)`-cell `(T, x)` の面 `ν` に載っている `I` の個数（`(T\{ν}, x)` と `(T\{ν}, x+e_ν)`）。 -/
def faceCount (I : Finset (Fin d) → Wp d L → Bool) (T : Finset (Fin d)) (x : Wp d L)
    (ν : Fin d) : ℕ :=
  (I (T.erase ν) x).toNat + (I (T.erase ν) (shiftp x ν)).toNat

/--
`PackK m I`：`(m+1)`-cell の族 `I` が、どの `(m+2)`-cell も高々一つの面しか含まない。
`m = 0` が `PlaquettePacking.AtMostOne`（プラケットと辺）に当たる。
-/
def PackK (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) : Prop :=
  ∀ T : Finset (Fin d), T.card = m + 2 → ∀ x : Wp d L,
    ∑ ν ∈ T, faceCount I T x ν ≤ 1

instance instDecidablePackK [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Decidable (PackK m I) := by
  unfold PackK; infer_instance

/--
**芯 (i)**：同じ基点 `x` で選ばれた二つの `(m+1)`-cell は、`m` 個の方向を共有できない。
`T = S ∪ S'` は `(m+2)`-cell で、`S = T \ {a}`・`S' = T \ {b}`（`a ≠ b`）はその面だから。
（`S ≠ S'` は仮定に要らない——`|S ∩ S'| = m < m+1 = |S|` から従う。）
-/
theorem not_share_m [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool} (h : PackK m I)
    {S S' : Finset (Fin d)} {x : Wp d L} (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (hint : (S ∩ S').card = m) (h1 : I S x = true) (h2 : I S' x = true) :
    False := by
  classical
  have hUI := Finset.card_union_add_card_inter S S'
  have hUcard : (S ∪ S').card = m + 2 := by omega
  obtain ⟨a, ha, hins⟩ : ∃ a ∉ S, insert a S = S ∪ S' :=
    Finset.exists_eq_insert_iff.2 ⟨Finset.subset_union_left, by omega⟩
  obtain ⟨b, hb, hins'⟩ : ∃ b ∉ S', insert b S' = S ∪ S' :=
    Finset.exists_eq_insert_iff.2 ⟨Finset.subset_union_right, by omega⟩
  have haT : a ∈ S ∪ S' := hins ▸ Finset.mem_insert_self a S
  have hbT : b ∈ S ∪ S' := hins' ▸ Finset.mem_insert_self b S'
  have hea : (S ∪ S').erase a = S := by rw [← hins, Finset.erase_insert ha]
  have heb : (S ∪ S').erase b = S' := by rw [← hins', Finset.erase_insert hb]
  have hab : a ≠ b := by
    intro hh
    subst hh
    rcases Finset.mem_union.1 haT with h' | h'
    · exact ha h'
    · exact hb h'
  have hsum := h (S ∪ S') hUcard x
  have hfa : 1 ≤ faceCount I (S ∪ S') x a := by simp [faceCount, hea, h1]
  have hfb : 1 ≤ faceCount I (S ∪ S') x b := by simp [faceCount, heb, h2]
  have hsplit : faceCount I (S ∪ S') x a + ∑ ν ∈ (S ∪ S').erase a, faceCount I (S ∪ S') x ν
      = ∑ ν ∈ S ∪ S', faceCount I (S ∪ S') x ν :=
    Finset.add_sum_erase _ _ haT
  have hbmem : b ∈ (S ∪ S').erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hbT⟩
  have hfble : faceCount I (S ∪ S') x b ≤ ∑ ν ∈ (S ∪ S').erase a, faceCount I (S ∪ S') x ν :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hbmem
  omega

/-- 選ばれた二つの `(m+1)`-cell の `m`-部分集合の族は互いに素（芯 (i) の言い換え）。 -/
theorem disjoint_powersetCard_of_pack [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (h : PackK m I) {x : Wp d L} {S S' : Finset (Fin d)}
    (hS : S.card = m + 1) (hS' : S'.card = m + 1)
    (h1 : I S x = true) (h2 : I S' x = true) (hne : S ≠ S') :
    Disjoint (S.powersetCard m) (S'.powersetCard m) := by
  classical
  rw [Finset.disjoint_left]
  intro R hR hR'
  rw [Finset.mem_powersetCard] at hR hR'
  have hsub : R ⊆ S ∩ S' := Finset.subset_inter hR.1 hR'.1
  have hge : m ≤ (S ∩ S').card := by
    rw [← hR.2]; exact Finset.card_le_card hsub
  have hlecard : (S ∩ S').card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hle : (S ∩ S').card ≤ m := by
    by_contra hc
    have h5 : S ∩ S' = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h6 : S ⊆ S' := by rw [← h5]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le h6 (by omega))
  exact not_share_m h hS hS' (by omega) h1 h2

/-- 基点 `x` で選ばれた `(m+1)`-cell の方向集合の族 `F(x)`。 -/
def cellsAt [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) (x : Wp d L) :
    Finset (Finset (Fin d)) :=
  Finset.univ.filter (fun S => S.card = m + 1 ∧ I S x = true)

/-- **基点ごとの上界**：`k·|F(x)| ≤ C(d, k−1)`（`k = m+1`）。
`F(x)` の成員の `m`-部分集合は各 `m+1` 個あって互いに素で、全部 `Fin d` の `m`-部分集合。 -/
theorem card_cellsAt_le [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool}
    (h : PackK m I) (x : Wp d L) :
    (m + 1) * (cellsAt m I x).card ≤ d.choose m := by
  classical
  have hmem : ∀ S ∈ cellsAt m I x, S.card = m + 1 ∧ I S x = true := by
    intro S hS
    simpa [cellsAt] using hS
  have hdisj : ((cellsAt m I x : Finset (Finset (Fin d))) : Set (Finset (Fin d))).PairwiseDisjoint
      (fun S => S.powersetCard m) := by
    intro S hS S' hS' hne
    simp only [Function.onFun]
    have hSm := hmem S (Finset.mem_coe.1 hS)
    have hS'm := hmem S' (Finset.mem_coe.1 hS')
    exact disjoint_powersetCard_of_pack h hSm.1 hS'm.1 hSm.2 hS'm.2 hne
  have hcard : ((cellsAt m I x).biUnion (fun S => S.powersetCard m)).card
      = ∑ S ∈ cellsAt m I x, (S.powersetCard m).card := Finset.card_biUnion hdisj
  have hterm : ∀ S ∈ cellsAt m I x, (S.powersetCard m).card = m + 1 := by
    intro S hS
    rw [Finset.card_powersetCard, (hmem S hS).1, Nat.choose_succ_self_right]
  have hsum : ∑ S ∈ cellsAt m I x, (S.powersetCard m).card
      = ∑ _S ∈ cellsAt m I x, (m + 1) := Finset.sum_congr rfl hterm
  have hsub : (cellsAt m I x).biUnion (fun S => S.powersetCard m)
      ⊆ (Finset.univ : Finset (Fin d)).powersetCard m := by
    intro R hR
    obtain ⟨S, _, hRS⟩ := Finset.mem_biUnion.1 hR
    rw [Finset.mem_powersetCard] at hRS ⊢
    exact ⟨Finset.subset_univ R, hRS.2⟩
  calc (m + 1) * (cellsAt m I x).card
      = ((cellsAt m I x).biUnion (fun S => S.powersetCard m)).card := by
        rw [hcard, hsum, Finset.sum_const, smul_eq_mul]; ring
    _ ≤ ((Finset.univ : Finset (Fin d)).powersetCard m).card := Finset.card_le_card hsub
    _ = d.choose m := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- 選ばれた `(m+1)`-cell の全体（方向集合と基点の組）。 -/
def cellSet [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    Finset (Finset (Fin d) × Wp d L) :=
  Finset.univ.filter (fun p => p.1.card = m + 1 ∧ I p.1 p.2 = true)

theorem card_cellSet_eq_sum [NeZero L] (m : ℕ) (I : Finset (Fin d) → Wp d L → Bool) :
    (cellSet m I).card = ∑ x : Wp d L, (cellsAt m I x).card := by
  classical
  rw [cellSet, Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun x _ => by rw [cellsAt, Finset.card_filter]

/--
**`k`-cell 版の上界**（`k = m+1`）：`k·|I| ≤ L^d·C(d, k−1)`。
`k`-cell の総数は `L^d·C(d,k)` なので、密度は `C(d,k−1)/(k·C(d,k)) = 1/(d−k+1)` 以下。
-/
theorem card_cellSet_le [NeZero L] {m : ℕ} {I : Finset (Fin d) → Wp d L → Bool} (h : PackK m I) :
    (m + 1) * (cellSet m I).card ≤ L ^ d * d.choose m := by
  rw [card_cellSet_eq_sum, Finset.mul_sum]
  calc ∑ x : Wp d L, (m + 1) * (cellsAt m I x).card
      ≤ ∑ _x : Wp d L, d.choose m := Finset.sum_le_sum fun x _ => card_cellsAt_le h x
    _ = L ^ d * d.choose m := by
        rw [Finset.sum_const, Finset.card_univ, card_Wp, smul_eq_mul]

/-- 陽性対照（`k = 1` への特殊化）：`m = 0` では `|I| ≤ L^d`。
パッキングの頂点の上界（`card_edgeSet_le`）と同じ値で、そちらとは別の道（`m`-部分集合の
互いに素性）で出ている。 -/
theorem card_cellSet_le_zero [NeZero L] {I : Finset (Fin d) → Wp d L → Bool} (h : PackK 0 I) :
    (cellSet 0 I).card ≤ L ^ d := by
  have h1 := card_cellSet_le h
  simpa using h1

/-- 陽性対照（自明な側）：空の族はどんな `m` でもパッキング。 -/
theorem packK_empty [NeZero L] (m : ℕ) :
    PackK (d := d) (L := L) m (fun _ _ => false) := by
  intro T _ x
  simp [faceCount]

/-- 陰性対照：`d = 2`・`L = 2`・`m = 0` で全部の 1-cell を採る族はパッキングでない
（`PackK 0` は空虚な条件ではない——`|T| = 2` の `T` が実在する）。 -/
theorem not_packK_full : ¬ PackK (d := 2) (L := 2) 0 (fun _ _ => true) := by
  decide

/-- 陰性対照：`d = 3`・`L = 2`・`m = 1`（`k = 2`）でも全部採る族はパッキングでない。 -/
theorem not_packK_full_k2 : ¬ PackK (d := 3) (L := 2) 1 (fun _ _ => true) := by
  decide

end PlaquetteCounting


/-! ## 9. 使った公理 -/

namespace PlaquetteCounting

#print axioms shiftp_bijective
#print axioms sum_shiftp
#print axioms atMostOne_iff_plaqCount
#print axioms perfectP_iff_plaqCount
#print axioms card_edgeSet_eq_sum
#print axioms sum_x_plaqCount
#print axioms eq_of_add_eq_mul
#print axioms le_of_add_eq_mul
#print axioms add4_of_add2
#print axioms sum_erase_two
#print axioms sum_erase_const
#print axioms sum_plaqCount_add
#print axioms sum_plaqCount_perfect
#print axioms sum_plaqCount_le
#print axioms four_mul_card_le
#print axioms four_mul_card_eq
#print axioms perfect_torus_d_le_four
#print axioms four_dvd_of_perfect
#print axioms density_le_quarter
#print axioms density_eq_quarter
#print axioms card_le_six_d3L2
#print axioms no_perfect_d3L3
#print axioms no_perfect_d2L3
#print axioms A4_consistent
#print axioms P5_bound_slack
#print axioms full_violates_bound
#print axioms sum_plaq_Line
#print axioms not_share_m
#print axioms disjoint_powersetCard_of_pack
#print axioms card_cellsAt_le
#print axioms card_cellSet_eq_sum
#print axioms card_cellSet_le
#print axioms card_cellSet_le_zero
#print axioms packK_empty
#print axioms not_packK_full
#print axioms not_packK_full_k2

end PlaquetteCounting
