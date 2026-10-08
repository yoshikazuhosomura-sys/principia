/-
  CM アーベル多様体 A = C^9 / Φ_S(O_K)  (K = Q(ζ_19), S 退化かつ原始的な CM 型) の上で
  「非有理特異点を持つ因子」を作るための有限の部分。

  幾何については何も主張していない。ここにあるのは次の 4 つの有限の事実だけである。

  (1) K_0 = Q(ζ_19)^+ の整イデアルのノルムの集合（p の剰余次数 f(p) は
      (Z/19)^*/{±1} ≅ Z/9 における p の位数）について、
      48677 はノルムであり、48621 以上で最小のノルムである。
  (2) 9 次元で重複度 ≥ 10 を課す条件の数は C(18,9) = 48620 であり、
      h^0 = 48677 から 48676 - 48620 = 56 が残る（重複度 11 では足りない）。
  (3) 鳩の巣：同変な線形写像の固有空間分解で、定義域の次元の和が値域のそれを超えれば、
      ある固有空間で核が非自明。→ μ_38 不変な切断が取れる。
  (4) μ_38 = ⟨-ζ⟩ の固定点：Fix(ζ) ≅ Z/19 の上で -1 の固定点はただ 1 つ（原点）。
-/
import Mathlib

namespace CMHodge

/-! ## 1. K_0 = Q(ζ_19)^+ における剰余次数とイデアルノルム -/

/-- `p` の `K_0 = Q(ζ_19)^+` における剰余次数。
`(Z/19)^*/{±1} ≅ Z/9` における `p` の位数（分岐する 19 では 1）。 -/
def resdeg (p : ℕ) : ℕ :=
  if p % 19 = 0 then 1
  else if p % 19 = 1 ∨ p % 19 = 18 then 1
  else if p ^ 3 % 19 = 1 ∨ p ^ 3 % 19 = 18 then 3
  else 9

/-- `n` が `O_{K_0}` の整イデアルのノルムであること（組合せ的な特徴づけ）。
`K/Q` が Galois なので `p` の上の素イデアルは全て剰余次数 `resdeg p` を持ち、
ノルムはちょうど `∏ p ^ (resdeg p * a_p)` の形になる。 -/
def IsIdealNorm (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → resdeg p ∣ n.factorization p

theorem resdeg_19 : resdeg 19 = 1 := by decide
theorem resdeg_2 : resdeg 2 = 9 := by decide
theorem resdeg_3 : resdeg 3 = 9 := by decide
theorem resdeg_7 : resdeg 7 = 3 := by decide
theorem resdeg_11 : resdeg 11 = 3 := by decide
theorem resdeg_37 : resdeg 37 = 1 := by decide
theorem resdeg_48677 : resdeg 48677 = 1 := by decide

/-- 剰余次数は 1, 3, 9 のいずれか（`Z/9` の部分群の位数）。 -/
theorem resdeg_mem (p : ℕ) : resdeg p = 1 ∨ resdeg p = 3 ∨ resdeg p = 9 := by
  unfold resdeg
  split_ifs <;> simp

theorem norm_of_prime {p : ℕ} (hp : p.Prime) (h : resdeg p = 1) : IsIdealNorm p := by
  refine ⟨hp.pos, fun q hq => ?_⟩
  rcases eq_or_ne q p with rfl | hne
  · rw [h]; exact one_dvd _
  · rw [Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd))]
    exact dvd_zero _

/-- ある素数 `p` で `v_p(n) = e` かつ `resdeg p ∤ e` なら `n` はノルムでない。 -/
theorem not_norm_of_witness (n p e : ℕ) (hp : p.Prime) (h1 : p ^ e ∣ n)
    (h2 : ¬ p ^ (e + 1) ∣ n) (h3 : ¬ resdeg p ∣ e) : ¬ IsIdealNorm n := by
  rintro ⟨hn, hall⟩
  have hn0 : n ≠ 0 := by omega
  have hle : e ≤ n.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mp h1
  have hlt : ¬ (e + 1 ≤ n.factorization p) := fun hc =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization hp hn0).mpr hc)
  have hv : n.factorization p = e := by omega
  exact h3 (hv ▸ hall p hp)

/-- 陰性対照：2 はノルムでない（`resdeg 2 = 9`）。 -/
theorem not_norm_two : ¬ IsIdealNorm 2 :=
  not_norm_of_witness 2 2 1 (by norm_num) (by decide) (by decide) (by decide)

/-- 陽性対照：19（分岐素点）はノルム。 -/
theorem norm_nineteen : IsIdealNorm 19 := norm_of_prime (by norm_num) resdeg_19

/-- 陽性対照：37 ≡ -1 (mod 19) はノルム。 -/
theorem norm_thirtyseven : IsIdealNorm 37 := norm_of_prime (by norm_num) resdeg_37

/-- `48677` は素数で `48677 ≡ -1 (mod 19)`、ゆえに剰余次数 1 でノルムである。 -/
theorem norm_48677 : IsIdealNorm 48677 := norm_of_prime (by norm_num) resdeg_48677

/-! ### 48621 以上 48676 以下にはノルムが無い（56 個の証人） -/

theorem not_norm_48621 : ¬ IsIdealNorm 48621 :=
  not_norm_of_witness 48621 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48622 : ¬ IsIdealNorm 48622 :=
  not_norm_of_witness 48622 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48623 : ¬ IsIdealNorm 48623 :=
  not_norm_of_witness 48623 48623 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48624 : ¬ IsIdealNorm 48624 :=
  not_norm_of_witness 48624 2 4 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48625 : ¬ IsIdealNorm 48625 :=
  not_norm_of_witness 48625 5 3 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48626 : ¬ IsIdealNorm 48626 :=
  not_norm_of_witness 48626 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48627 : ¬ IsIdealNorm 48627 :=
  not_norm_of_witness 48627 3 3 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48628 : ¬ IsIdealNorm 48628 :=
  not_norm_of_witness 48628 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48629 : ¬ IsIdealNorm 48629 :=
  not_norm_of_witness 48629 7 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48630 : ¬ IsIdealNorm 48630 :=
  not_norm_of_witness 48630 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48631 : ¬ IsIdealNorm 48631 :=
  not_norm_of_witness 48631 11 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48632 : ¬ IsIdealNorm 48632 :=
  not_norm_of_witness 48632 2 3 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48633 : ¬ IsIdealNorm 48633 :=
  not_norm_of_witness 48633 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48634 : ¬ IsIdealNorm 48634 :=
  not_norm_of_witness 48634 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48635 : ¬ IsIdealNorm 48635 :=
  not_norm_of_witness 48635 5 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48636 : ¬ IsIdealNorm 48636 :=
  not_norm_of_witness 48636 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48637 : ¬ IsIdealNorm 48637 :=
  not_norm_of_witness 48637 17 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48638 : ¬ IsIdealNorm 48638 :=
  not_norm_of_witness 48638 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48639 : ¬ IsIdealNorm 48639 :=
  not_norm_of_witness 48639 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48640 : ¬ IsIdealNorm 48640 :=
  not_norm_of_witness 48640 5 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48641 : ¬ IsIdealNorm 48641 :=
  not_norm_of_witness 48641 127 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48642 : ¬ IsIdealNorm 48642 :=
  not_norm_of_witness 48642 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48643 : ¬ IsIdealNorm 48643 :=
  not_norm_of_witness 48643 7 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48644 : ¬ IsIdealNorm 48644 :=
  not_norm_of_witness 48644 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48645 : ¬ IsIdealNorm 48645 :=
  not_norm_of_witness 48645 3 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48646 : ¬ IsIdealNorm 48646 :=
  not_norm_of_witness 48646 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48647 : ¬ IsIdealNorm 48647 :=
  not_norm_of_witness 48647 48647 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48648 : ¬ IsIdealNorm 48648 :=
  not_norm_of_witness 48648 2 3 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48649 : ¬ IsIdealNorm 48649 :=
  not_norm_of_witness 48649 48649 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48650 : ¬ IsIdealNorm 48650 :=
  not_norm_of_witness 48650 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48651 : ¬ IsIdealNorm 48651 :=
  not_norm_of_witness 48651 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48652 : ¬ IsIdealNorm 48652 :=
  not_norm_of_witness 48652 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48653 : ¬ IsIdealNorm 48653 :=
  not_norm_of_witness 48653 11 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48654 : ¬ IsIdealNorm 48654 :=
  not_norm_of_witness 48654 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48655 : ¬ IsIdealNorm 48655 :=
  not_norm_of_witness 48655 5 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48656 : ¬ IsIdealNorm 48656 :=
  not_norm_of_witness 48656 2 4 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48657 : ¬ IsIdealNorm 48657 :=
  not_norm_of_witness 48657 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48658 : ¬ IsIdealNorm 48658 :=
  not_norm_of_witness 48658 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48659 : ¬ IsIdealNorm 48659 :=
  not_norm_of_witness 48659 13 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48660 : ¬ IsIdealNorm 48660 :=
  not_norm_of_witness 48660 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48661 : ¬ IsIdealNorm 48661 :=
  not_norm_of_witness 48661 48661 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48662 : ¬ IsIdealNorm 48662 :=
  not_norm_of_witness 48662 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48663 : ¬ IsIdealNorm 48663 :=
  not_norm_of_witness 48663 3 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48664 : ¬ IsIdealNorm 48664 :=
  not_norm_of_witness 48664 2 3 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48665 : ¬ IsIdealNorm 48665 :=
  not_norm_of_witness 48665 5 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48666 : ¬ IsIdealNorm 48666 :=
  not_norm_of_witness 48666 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48667 : ¬ IsIdealNorm 48667 :=
  not_norm_of_witness 48667 41 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48668 : ¬ IsIdealNorm 48668 :=
  not_norm_of_witness 48668 2 2 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48669 : ¬ IsIdealNorm 48669 :=
  not_norm_of_witness 48669 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48670 : ¬ IsIdealNorm 48670 :=
  not_norm_of_witness 48670 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48671 : ¬ IsIdealNorm 48671 :=
  not_norm_of_witness 48671 7 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48672 : ¬ IsIdealNorm 48672 :=
  not_norm_of_witness 48672 2 5 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48673 : ¬ IsIdealNorm 48673 :=
  not_norm_of_witness 48673 48673 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48674 : ¬ IsIdealNorm 48674 :=
  not_norm_of_witness 48674 2 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48675 : ¬ IsIdealNorm 48675 :=
  not_norm_of_witness 48675 3 1 (by norm_num) (by decide) (by decide) (by decide)

theorem not_norm_48676 : ¬ IsIdealNorm 48676 :=
  not_norm_of_witness 48676 2 2 (by norm_num) (by decide) (by decide) (by decide)


theorem no_ideal_norm_in_gap (n : ℕ) (h1 : 48621 ≤ n) (h2 : n ≤ 48676) :
    ¬ IsIdealNorm n := by
  interval_cases n
  exacts [not_norm_48621, not_norm_48622, not_norm_48623, not_norm_48624, not_norm_48625, not_norm_48626, not_norm_48627, not_norm_48628, not_norm_48629, not_norm_48630, not_norm_48631, not_norm_48632, not_norm_48633, not_norm_48634, not_norm_48635, not_norm_48636, not_norm_48637, not_norm_48638, not_norm_48639, not_norm_48640, not_norm_48641, not_norm_48642, not_norm_48643, not_norm_48644, not_norm_48645, not_norm_48646, not_norm_48647, not_norm_48648, not_norm_48649, not_norm_48650, not_norm_48651, not_norm_48652, not_norm_48653, not_norm_48654, not_norm_48655, not_norm_48656, not_norm_48657, not_norm_48658, not_norm_48659, not_norm_48660, not_norm_48661, not_norm_48662, not_norm_48663, not_norm_48664, not_norm_48665, not_norm_48666, not_norm_48667, not_norm_48668, not_norm_48669, not_norm_48670, not_norm_48671, not_norm_48672, not_norm_48673, not_norm_48674, not_norm_48675, not_norm_48676]

/-- **48621 以上の最小のイデアルノルムは 48677**。
（9 次元で重複度 10 を課す条件の数は 48620 なので、`h^0 = 48621` 以上が要る。） -/
theorem min_ideal_norm (n : ℕ) (h1 : 48621 ≤ n) (h2 : IsIdealNorm n) : 48677 ≤ n := by
  by_contra hc
  exact no_ideal_norm_in_gap n h1 (by omega) h2

/-! ## 2. 重複度を課す条件の数（9 次元） -/

/-- `g` 次元の滑らかな点で重複度 `≥ m` を課す線形条件の数 `C(m-1+g, g)`。 -/
def condCount (g m : ℕ) : ℕ := Nat.choose (m - 1 + g) g

theorem condCount_9_10 : condCount 9 10 = 48620 := by decide

/-- 次数別（`Sym^d` の次元）の和として数え直しても同じ（hockey stick）。 -/
theorem condCount_9_10_layers :
    ([8, 9, 10, 11, 12, 13, 14, 15, 16, 17].map (fun n => Nat.choose n 8)).sum = 48620 := by
  decide

theorem condCount_9_11 : condCount 9 11 = 92378 := by decide

/-- `h^0(L) = 48677` なら射影空間 `|L|` の次元は 48676 で、
重複度 10 の条件 48620 を課してもまだ 56 次元残る（空でない）。 -/
theorem system_nonempty : condCount 9 10 < 48677 - 1 := by decide

theorem system_dim : 48677 - 1 - condCount 9 10 = 56 := by decide

/-- 一方、重複度 11 はこの `h^0` では保証されない（条件の数が次元を超える）。
すなわち 10 はこの偏極で保証できる最大の重複度である。 -/
theorem mult_eleven_not_forced : 48677 - 1 < condCount 9 11 := by decide

/-- 重複度 10 は `dim A = 9` を超える（Kollár の `lc ⟹ mult ≤ dim` の閾値）。 -/
theorem mult_exceeds_dim : 9 < 10 := by decide

/-! ## 3. 鳩の巣：同変な線形系に固有ベクトルの解がある -/

/-- 有限群の指標分解 `f`（定義域の各固有空間の次元）と `g`（値域の各固有空間の次元）について、
`∑ g < ∑ f` ならある指標で `g i < f i`、すなわちその固有空間で核が非自明。 -/
theorem exists_eigenspace_with_kernel {ι : Type*} [Fintype ι] (f g : ι → ℕ)
    (h : ∑ i, g i < ∑ i, f i) : ∃ i, g i < f i := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  exact absurd (Finset.sum_le_sum (fun i _ => hc i)) (not_le.mpr h)

/-- `μ_38 = Aut(A, L)` の 38 個の指標について、`∑ dim H^0(L)_χ = 48677`、
`∑ dim (jets)_χ ≤ 48620` だから、ある指標 `χ` で `μ_38` 固有な切断が原点で 10 重に消える。
（jet 写像は `μ_38` 同変。条件の独立性は一切使っていない。） -/
theorem mu38_eigen_section (f g : Fin 38 → ℕ)
    (hf : ∑ i, f i = 48677) (hg : ∑ i, g i ≤ condCount 9 10) :
    ∃ i, g i < f i := by
  refine exists_eigenspace_with_kernel f g ?_
  rw [hf]
  have : condCount 9 10 = 48620 := condCount_9_10
  omega

/-! ## 4. μ_38 の A 上の固定点 -/

/-- `Fix(ζ) = A[𝔭] ≅ Z/19` の点数は 19。 -/
theorem pTorsion_card : Fintype.card (ZMod 19) = 19 := ZMod.card 19

/-- その上で `-1` の固定点はただ 1 つ（原点）。
ゆえに `Fix(μ_38) = Fix(ζ) ∩ A[2] = {0}` は 1 点である。 -/
theorem mu38_fixed_point_unique :
    (Finset.univ.filter (fun x : ZMod 19 => x = -x)).card = 1 := by decide

/-- 同じことを直接に：`x = -x` なら `x = 0`（19 は奇数）。 -/
theorem neg_fixed_iff_zero (x : ZMod 19) : x = -x ↔ x = 0 := by
  revert x; decide

/-- `A[2]` の点数 `2^18`。 -/
theorem twoTorsion_card : (2 : ℕ) ^ 18 = 262144 := by norm_num

/-! ## 5. μ_19 は W_F に自明に作用する -/

/-- `F = K^{⟨γ^6⟩}` は 6 次 CM 部分体、`Gal(K/F) = {1, γ^6, γ^12}`（`γ = 2`）。
`W_F = ∧³_F H_1(A,Q)` への `x ∈ K^*` の作用は `N_{K/F}(x)` の掛け算である。
`ζ` については `N_{K/F}(ζ) = ζ^{γ^0 + γ^6 + γ^12} = ζ^19 = 1`：
`μ_19` は `W_F`（6 次元の例外部分）に**自明に**作用する。 -/
theorem zeta_trivial_on_WF : (2 ^ 0 + 2 ^ 6 + 2 ^ 12) % 19 = 0 := by decide

/-- 6 本のコセット `C_k = {k, k+6, k+12}` のどれでも同じ。 -/
theorem zeta_trivial_on_all_cosets :
    ∀ k ∈ [0, 1, 2, 3, 4, 5], (2 ^ k + 2 ^ (k + 6) + 2 ^ (k + 12)) % 19 = 0 := by decide

/-- 陰性対照：`H^1(A)` には `ζ` の不変ベクトルが無い
（`γ^u = 2^u mod 19` はどれも 1 でない、`u = 0` を除く）。 -/
theorem zeta_nontrivial_on_H1 :
    ∀ u ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      (2 ^ u) % 19 ≠ 1 := by decide

/-! ## 6. 商 X = A/μ_19 の孤立商特異点：重みと Reid–Tai の age

`μ_19 = ⟨ζ⟩` は `A` に 19 個の固定点（`A[𝔭]`）を持ち、各固定点での接空間の重みは
CM 型 `S = {0,1,2,3,4,5,6,8,16}` に対応する `2^u mod 19`、すなわち
`(1,2,4,8,16,13,7,9,5)` である。ここは純粋に有限の算術だけを扱う。 -/

/-- 接空間での `ζ` の重み（`2^u mod 19`, `u ∈ S`）。 -/
def wt : List ℕ := [1, 2, 4, 8, 16, 13, 7, 9, 5]

/-- 重みは CM 型 `S` から来ている（定義の照合）。 -/
theorem wt_eq_cm_type :
    wt = ([0, 1, 2, 3, 4, 5, 6, 8, 16] : List ℕ).map (fun u => 2 ^ u % 19) := by decide

/-- Reid–Tai の age の分子：`ageNum k = Σ_u ((k · a_u) mod 19)`、age は `ageNum k / 19`。 -/
def ageNum (k : ℕ) : ℕ := (wt.map (fun a => k * a % 19)).sum

/-- 重みの総和は 65。 -/
theorem wt_sum : wt.sum = 65 := by decide

/-- **`65 % 19 = 8 ≠ 0`**：`ζ` は正則 9 形式に `ζ^8`（自明でない指標）で作用する。
ゆえにこの巡回商特異点は **Gorenstein ではない**（`K_X` は 19 等分点的な捩れであり、
`X` は Calabi–Yau ではない）。 -/
theorem not_gorenstein : wt.sum % 19 = 8 ∧ wt.sum % 19 ≠ 0 := by decide

/-- **Reid–Tai**：`k = 1, …, 18` のすべてで `ageNum k ≥ 58 > 19`、
すなわち age > 1。孤立巡回商特異点は **terminal**（したがって canonical）である。 -/
theorem ageNum_ge_58 :
    ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18], 58 ≤ ageNum k := by
  decide

/-- 最小値はちょうど 58（`k = 12`）：age の最小は `58/19 ≈ 3.05`。 -/
theorem ageNum_min : ageNum 12 = 58 := by decide

/-- 陽性対照：`age(k) + age(19−k) = 9 = dim A`（`171 = 9 · 19`）。 -/
theorem ageNum_pair :
    ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
      ageNum k + ageNum (19 - k) = 171 := by decide

/-- age はどれも整数でない（`ageNum k % 19 ≠ 0`）——非 Gorenstein と整合する。
ゆえに（軌道体コホモロジーの）捩れセクターは整数次数に寄与しない。 -/
theorem ageNum_not_integral :
    ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
      ageNum k % 19 ≠ 0 := by decide


end CMHodge

#print axioms CMHodge.resdeg_48677
#print axioms CMHodge.resdeg_mem
#print axioms CMHodge.norm_of_prime
#print axioms CMHodge.not_norm_of_witness
#print axioms CMHodge.not_norm_two
#print axioms CMHodge.norm_nineteen
#print axioms CMHodge.norm_thirtyseven
#print axioms CMHodge.norm_48677
#print axioms CMHodge.no_ideal_norm_in_gap
#print axioms CMHodge.min_ideal_norm
#print axioms CMHodge.condCount_9_10
#print axioms CMHodge.condCount_9_10_layers
#print axioms CMHodge.condCount_9_11
#print axioms CMHodge.system_nonempty
#print axioms CMHodge.system_dim
#print axioms CMHodge.mult_eleven_not_forced
#print axioms CMHodge.exists_eigenspace_with_kernel
#print axioms CMHodge.mu38_eigen_section
#print axioms CMHodge.pTorsion_card
#print axioms CMHodge.mu38_fixed_point_unique
#print axioms CMHodge.neg_fixed_iff_zero
#print axioms CMHodge.twoTorsion_card
#print axioms CMHodge.zeta_trivial_on_WF
#print axioms CMHodge.zeta_trivial_on_all_cosets
#print axioms CMHodge.zeta_nontrivial_on_H1
#print axioms CMHodge.wt_eq_cm_type
#print axioms CMHodge.wt_sum
#print axioms CMHodge.not_gorenstein
#print axioms CMHodge.ageNum_ge_58
#print axioms CMHodge.ageNum_min
#print axioms CMHodge.ageNum_pair
#print axioms CMHodge.ageNum_not_integral
