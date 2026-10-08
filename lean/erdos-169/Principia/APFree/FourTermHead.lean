/-
  頭の下界の骨組み —
  エルデシュ問題 #169、`k = 4`。**Kempner 集合の頭の逆数和を Lean で下から押さえる骨組み。**

  【対象】`KF b S m`：`m` 桁（先頭の 0 を許す）・全桁 ∈ S の数の Finset。頭は
    `(K(S,55)+1) ∩ [1, r₀]` を「接頭辞 `P` を固定した葉」`1 + P·55^m + KF 55 S m` の
    互いに素な合併（`unionK`）として書く（685 個。`APFreeFourTermHeadUnion`）。

  【葉の評価——4 項の展開】葉 `a + KF m` の逆数和を、`c = ⌊M₁/N⌋`（`N = |S|^m`、`M_i = Σ v^i`）、
    `D = a + c`、`w = v − c` として
        1/(a+v) = 1/(D(1+u)), u = w/D > −1,
        1/(1+u) ≥ 1 − u + u² − u³ （差は u⁴/(1+u) ≥ 0）
    で押さえる。和は `M₀..M₃` の一次式になり、`M_i` は桁の冪和 `s_j = Σ_{e∈S} e^j` から
    閉じた漸化式で出る（`mom1/mom2/mom3`）。深さ 1（13,545 葉）で取りこぼし 1e−10。
    （切り捨て `cnt/(a+max)` の葉では深さ 5・数千万葉が要る——の見積り。）

  【定理】`loK_le`：`loK` を SC で割ったものは `Σ_{v ∈ KF m} 1/(a+v)` の下界。
         `totK_le`：葉の並びが互いに素（`ordK`）なら、合併の上の Σ 1/x の下界。
  sorry 0・native_decide 不使用。
-/
import Mathlib.Tactic
import Principia.APFree.FourTermKempner

namespace APFree.FourTermRecord

/-! ## 1. `KF b S m` -/

/-- `m` 桁（先頭の 0 を許す）・全桁 ∈ S の数の全体。 -/
def KF (b : ℕ) (S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | m + 1 => S.biUnion fun e => (KF b S m).image fun v => e * b ^ m + v

/-- `m` 桁の最大値（各桁 ≤ M）。 -/
def mxK (b M : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => M * b ^ m + mxK b M m

section basic

variable (b : ℕ) (S : Finset ℕ)

theorem mem_KF_succ (m x : ℕ) :
    x ∈ KF b S (m + 1) ↔ ∃ e ∈ S, ∃ v ∈ KF b S m, x = e * b ^ m + v := by
  simp only [KF, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩; exact ⟨e, he, v, hv, rfl⟩
  · rintro ⟨e, he, v, hv, rfl⟩; exact ⟨e, he, v, hv, rfl⟩

theorem KF_lt (hS : ∀ e ∈ S, e < b) : ∀ m, ∀ v ∈ KF b S m, v < b ^ m := by
  intro m
  induction m with
  | zero => intro v hv; simp [KF] at hv; simp [hv]
  | succ m ih =>
      intro v hv
      obtain ⟨e, he, w, hw, rfl⟩ := (mem_KF_succ b S m v).1 hv
      have h1 := ih w hw
      have h2 : e + 1 ≤ b := hS e he
      calc e * b ^ m + w < e * b ^ m + b ^ m := by omega
        _ = (e + 1) * b ^ m := by ring
        _ ≤ b * b ^ m := Nat.mul_le_mul_right _ h2
        _ = b ^ (m + 1) := by ring

theorem KF_le (M : ℕ) (hM : ∀ e ∈ S, e ≤ M) : ∀ m, ∀ v ∈ KF b S m, v ≤ mxK b M m := by
  intro m
  induction m with
  | zero => intro v hv; simp [KF] at hv; simp [hv, mxK]
  | succ m ih =>
      intro v hv
      obtain ⟨e, he, w, hw, rfl⟩ := (mem_KF_succ b S m v).1 hv
      have h1 := ih w hw
      have h2 := hM e he
      simp only [mxK]
      have : e * b ^ m ≤ M * b ^ m := Nat.mul_le_mul_right _ h2
      omega

theorem KF_disj (hS : ∀ e ∈ S, e < b) (m : ℕ) :
    ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' →
      Disjoint ((KF b S m).image fun v => e * b ^ m + v)
        ((KF b S m).image fun v => e' * b ^ m + v) := by
  intro e _ e' _ hne
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, hweq⟩ := hx'
  have h1 := KF_lt b S hS m v hv
  have h2 := KF_lt b S hS m w hw
  apply hne
  rcases Nat.lt_trichotomy e e' with h | h | h
  · exfalso
    have : (e + 1) * b ^ m ≤ e' * b ^ m := Nat.mul_le_mul_right _ h
    nlinarith
  · exact h
  · exfalso
    have : (e' + 1) * b ^ m ≤ e * b ^ m := Nat.mul_le_mul_right _ h
    nlinarith

theorem KF_pairwise (hS : ∀ e ∈ S, e < b) (m : ℕ) :
    (↑S : Set ℕ).PairwiseDisjoint fun e => (KF b S m).image fun v => e * b ^ m + v := by
  intro e he e' he' hne
  exact KF_disj b S hS m e he e' he' hne

theorem sum_KF_succ (hS : ∀ e ∈ S, e < b) {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ x ∈ KF b S (m + 1), f x = ∑ e ∈ S, ∑ v ∈ KF b S m, f (e * b ^ m + v) := by
  rw [KF, Finset.sum_biUnion (KF_pairwise b S hS m)]
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [Finset.sum_image]
  intro x _ y _ h; exact Nat.add_left_cancel h

theorem card_KF (hS : ∀ e ∈ S, e < b) : ∀ m, (KF b S m).card = S.card ^ m := by
  intro m
  induction m with
  | zero => simp [KF]
  | succ m ih =>
      rw [Finset.card_eq_sum_ones, sum_KF_succ b S hS]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, ih]
      ring

/-- 接頭辞 `P` の全桁が S、`v ∈ KF m` なら `P·b^m + v` の全桁も S。 -/
theorem digIn_prefix (hb : 0 < b) (hS : ∀ e ∈ S, e < b) :
    ∀ m (P : ℕ), DigIn b S P → ∀ v ∈ KF b S m, DigIn b S (P * b ^ m + v) := by
  intro m
  induction m with
  | zero => intro P hP v hv; simp [KF] at hv; simpa [hv] using hP
  | succ m ih =>
      intro P hP v hv
      obtain ⟨e, he, w, hw, rfl⟩ := (mem_KF_succ b S m v).1 hv
      have e1 : P * b ^ (m + 1) + (e * b ^ m + w) = (P * b + e) * b ^ m + w := by ring
      rw [e1]
      apply ih (P * b + e) _ w hw
      rw [digIn_iff]
      have hlt := hS e he
      constructor
      · rw [Nat.mul_comm P b, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]; exact he
      · rw [Nat.mul_comm P b, Nat.mul_add_div hb, Nat.div_eq_of_lt hlt, add_zero]; exact hP

end basic

/-! ## 2. 冪和（モーメント）の閉じた漸化式 -/

/-- `M₁(m) = Σ_{v ∈ KF m} v`。`n = |S|`、`s₁ = Σ_{e∈S} e`。 -/
def mom1 (b n s1 : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => s1 * b ^ m * n ^ m + n * mom1 b n s1 m

/-- `M₂(m) = Σ v²`。 -/
def mom2 (b n s1 s2 : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => s2 * (b ^ m) ^ 2 * n ^ m + 2 * s1 * b ^ m * mom1 b n s1 m + n * mom2 b n s1 s2 m

/-- `M₃(m) = Σ v³`。 -/
def mom3 (b n s1 s2 s3 : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => s3 * (b ^ m) ^ 3 * n ^ m + 3 * s2 * (b ^ m) ^ 2 * mom1 b n s1 m
      + 3 * s1 * b ^ m * mom2 b n s1 s2 m + n * mom3 b n s1 s2 s3 m

/-- 三次以下の多項式の和（ℕ）。 -/
theorem sum_poly3 {ι : Type*} (s : Finset ι) (g : ι → ℕ) (A B C D : ℕ) :
    ∑ i ∈ s, (A * g i ^ 3 + B * g i ^ 2 + C * g i + D)
      = A * ∑ i ∈ s, g i ^ 3 + B * ∑ i ∈ s, g i ^ 2 + C * ∑ i ∈ s, g i + D * s.card := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
  ring

/-- 同じもの（`s : Finset ℕ`、`g = id`）。 -/
theorem sum_poly3' (s : Finset ℕ) (A B C D : ℕ) :
    ∑ i ∈ s, (A * i ^ 3 + B * i ^ 2 + C * i + D)
      = A * ∑ i ∈ s, i ^ 3 + B * ∑ i ∈ s, i ^ 2 + C * ∑ i ∈ s, i + D * s.card := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
  ring

section moments

variable (b : ℕ) (S : Finset ℕ) (hS : ∀ e ∈ S, e < b) (n s1 s2 s3 : ℕ)
  (hn : S.card = n) (hs1 : ∑ e ∈ S, e = s1) (hs2 : ∑ e ∈ S, e ^ 2 = s2)
  (hs3 : ∑ e ∈ S, e ^ 3 = s3)

include hS hn hs1 in
theorem sum_KF_one : ∀ m, ∑ v ∈ KF b S m, v = mom1 b n s1 m := by
  intro m
  induction m with
  | zero => simp [KF, mom1]
  | succ m ih =>
      rw [sum_KF_succ b S hS, mom1]
      have inner : ∀ e ∈ S, ∑ v ∈ KF b S m, (e * b ^ m + v)
          = 0 * e ^ 3 + 0 * e ^ 2 + (b ^ m * n ^ m) * e + mom1 b n s1 m := by
        intro e _
        have h := sum_poly3' (KF b S m) 0 0 1 (e * b ^ m)
        rw [Finset.sum_congr rfl (fun v _ => by ring : ∀ v ∈ KF b S m,
          e * b ^ m + v = 0 * v ^ 3 + 0 * v ^ 2 + 1 * v + e * b ^ m), h, ih, card_KF b S hS, hn]
        ring
      rw [Finset.sum_congr rfl inner, sum_poly3' S, hs1, hn]
      ring

include hS hn hs1 hs2 in
theorem sum_KF_two : ∀ m, ∑ v ∈ KF b S m, v ^ 2 = mom2 b n s1 s2 m := by
  intro m
  induction m with
  | zero => simp [KF, mom2]
  | succ m ih =>
      rw [sum_KF_succ b S hS, mom2]
      have inner : ∀ e ∈ S, ∑ v ∈ KF b S m, (e * b ^ m + v) ^ 2
          = 0 * e ^ 3 + ((b ^ m) ^ 2 * n ^ m) * e ^ 2 + (2 * b ^ m * mom1 b n s1 m) * e
            + mom2 b n s1 s2 m := by
        intro e _
        have h := sum_poly3' (KF b S m) 0 1 (2 * e * b ^ m) (e ^ 2 * (b ^ m) ^ 2)
        rw [Finset.sum_congr rfl (fun v _ => by ring : ∀ v ∈ KF b S m,
          (e * b ^ m + v) ^ 2 = 0 * v ^ 3 + 1 * v ^ 2 + (2 * e * b ^ m) * v + e ^ 2 * (b ^ m) ^ 2),
          h, ih, sum_KF_one b S hS n s1 hn hs1, card_KF b S hS, hn]
        ring
      rw [Finset.sum_congr rfl inner, sum_poly3' S, hs1, hs2, hn]
      ring

include hS hn hs1 hs2 hs3 in
theorem sum_KF_three : ∀ m, ∑ v ∈ KF b S m, v ^ 3 = mom3 b n s1 s2 s3 m := by
  intro m
  induction m with
  | zero => simp [KF, mom3]
  | succ m ih =>
      rw [sum_KF_succ b S hS, mom3]
      have inner : ∀ e ∈ S, ∑ v ∈ KF b S m, (e * b ^ m + v) ^ 3
          = ((b ^ m) ^ 3 * n ^ m) * e ^ 3 + (3 * (b ^ m) ^ 2 * mom1 b n s1 m) * e ^ 2
            + (3 * b ^ m * mom2 b n s1 s2 m) * e + mom3 b n s1 s2 s3 m := by
        intro e _
        have h := sum_poly3' (KF b S m) 1 (3 * e * b ^ m) (3 * e ^ 2 * (b ^ m) ^ 2)
          (e ^ 3 * (b ^ m) ^ 3)
        rw [Finset.sum_congr rfl (fun v _ => by ring : ∀ v ∈ KF b S m,
          (e * b ^ m + v) ^ 3 = 1 * v ^ 3 + (3 * e * b ^ m) * v ^ 2
            + (3 * e ^ 2 * (b ^ m) ^ 2) * v + e ^ 3 * (b ^ m) ^ 3),
          h, ih, sum_KF_two b S hS n s1 s2 hn hs1 hs2, sum_KF_one b S hS n s1 hn hs1,
          card_KF b S hS, hn]
        ring
      rw [Finset.sum_congr rfl inner, sum_poly3' S, hs1, hs2, hs3, hn]
      ring

end moments

/-! ## 3. 葉の評価（4 項の展開） -/

/-- 葉 `a + KF m` の逆数和の下界（SC 倍・ℤ）。`c = ⌊M₁/N⌋`、`D = a + c`、
    `Σ_v (D³ − D²(v−c) + D(v−c)² − (v−c)³) / D⁴` を `M₀..M₃` で書いたもの。 -/
def leafZ (b SC n s1 s2 s3 : ℕ) (a m : ℕ) : ℤ :=
  let N : ℤ := ((n ^ m : ℕ) : ℤ)
  let M1 : ℤ := ((mom1 b n s1 m : ℕ) : ℤ)
  let M2 : ℤ := ((mom2 b n s1 s2 m : ℕ) : ℤ)
  let M3 : ℤ := ((mom3 b n s1 s2 s3 m : ℕ) : ℤ)
  let c : ℤ := M1 / N
  let D : ℤ := (a : ℤ) + c
  ((D ^ 3 + D ^ 2 * c + D * c ^ 2 + c ^ 3) * N - (D ^ 2 + 2 * D * c + 3 * c ^ 2) * M1
      + (D + 3 * c) * M2 - M3) * (SC : ℤ) / D ^ 4

/-- ℕ に落としたもの（負なら 0。下界としてはそれで足りる）。 -/
def leafK (b SC n s1 s2 s3 : ℕ) (a m : ℕ) : ℕ := (leafZ b SC n s1 s2 s3 a m).toNat

/-- 一項の評価：`1/(1+u) ≥ 1 − u + u² − u³`（`u > −1`）を `u = (v−c)/D` で。 -/
theorem term_lower (a : ℕ) (c : ℤ) (hc : 0 ≤ c) (ha : 0 < a) (v : ℕ) :
    (((((a : ℤ) + c) ^ 3 + ((a : ℤ) + c) ^ 2 * c + ((a : ℤ) + c) * c ^ 2 + c ^ 3 : ℤ) : ℚ)
        - ((((a : ℤ) + c) ^ 2 + 2 * ((a : ℤ) + c) * c + 3 * c ^ 2 : ℤ) : ℚ) * (v : ℚ)
        + ((((a : ℤ) + c) + 3 * c : ℤ) : ℚ) * (v : ℚ) ^ 2 - (v : ℚ) ^ 3)
      / ((((a : ℤ) + c : ℤ) : ℚ) ^ 4) ≤ 1 / ((a : ℚ) + v) := by
  have hD : (0 : ℚ) < ((a : ℤ) : ℚ) + (c : ℚ) := by
    have : (0 : ℚ) < ((a : ℤ) : ℚ) := by exact_mod_cast ha
    have : (0 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
    linarith
  have hav : (0 : ℚ) < (a : ℚ) + v := by positivity
  push_cast
  rw [div_le_div_iff₀ (by positivity) hav]
  have key : ∀ (A C V : ℚ),
      ((A + C) ^ 3 + (A + C) ^ 2 * C + (A + C) * C ^ 2 + C ^ 3
        - ((A + C) ^ 2 + 2 * (A + C) * C + 3 * C ^ 2) * V + (A + C + 3 * C) * V ^ 2 - V ^ 3)
        * (A + V) = (A + C) ^ 4 - (V - C) ^ 4 := by
    intro A C V; ring
  rw [key]
  have : (0 : ℚ) ≤ ((v : ℚ) - c) ^ 4 := by positivity
  linarith

/-- 三次以下の多項式の和（ℚ、添字は ℕ）。 -/
theorem sum_poly3Q (s : Finset ℕ) (A B C D : ℚ) :
    ∑ i ∈ s, (A + B * (i : ℚ) + C * (i : ℚ) ^ 2 + D * (i : ℚ) ^ 3)
      = A * s.card + B * ∑ i ∈ s, (i : ℚ) + C * ∑ i ∈ s, (i : ℚ) ^ 2
        + D * ∑ i ∈ s, (i : ℚ) ^ 3 := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

section leaf

variable (b : ℕ) (S : Finset ℕ) (hS : ∀ e ∈ S, e < b) (n s1 s2 s3 : ℕ)
  (hn : S.card = n) (hs1 : ∑ e ∈ S, e = s1) (hs2 : ∑ e ∈ S, e ^ 2 = s2)
  (hs3 : ∑ e ∈ S, e ^ 3 = s3) (SC : ℕ) (hSC : 0 < SC)

include hS hn hs1 hs2 hs3 hSC in
/-- **葉の定理**：`leafK` を SC で割ったものは葉の逆数和の下界。 -/
theorem leafK_le (a m : ℕ) (ha : 0 < a) :
    ((leafK b SC n s1 s2 s3 a m : ℕ) : ℚ) / SC ≤ ∑ v ∈ KF b S m, (1 : ℚ) / (a + v) := by
  -- 記号
  set N : ℤ := ((n ^ m : ℕ) : ℤ) with hN
  set M1 : ℤ := ((mom1 b n s1 m : ℕ) : ℤ) with hM1
  set M2 : ℤ := ((mom2 b n s1 s2 m : ℕ) : ℤ) with hM2
  set M3 : ℤ := ((mom3 b n s1 s2 s3 m : ℕ) : ℤ) with hM3
  set c : ℤ := M1 / N with hc
  set D : ℤ := (a : ℤ) + c with hD
  set α0 : ℤ := D ^ 3 + D ^ 2 * c + D * c ^ 2 + c ^ 3 with hα0
  set α1 : ℤ := D ^ 2 + 2 * D * c + 3 * c ^ 2 with hα1
  set α2 : ℤ := D + 3 * c with hα2
  set Num : ℤ := α0 * N - α1 * M1 + α2 * M2 - M3 with hNum
  have hcnn : 0 ≤ c := Int.ediv_nonneg (by positivity) (by positivity)
  have hDpos : 0 < D := by
    have : (0 : ℤ) < a := by exact_mod_cast ha
    omega
  have hD4 : (0 : ℤ) < D ^ 4 := by positivity
  have hleaf : leafZ b SC n s1 s2 s3 a m = Num * (SC : ℤ) / D ^ 4 := rfl
  -- (1) 葉の整数は Num·SC/D⁴ 以下（ℚ で）
  have h1 : ((leafZ b SC n s1 s2 s3 a m : ℤ) : ℚ) / SC ≤ (Num : ℚ) / ((D : ℚ) ^ 4) := by
    rw [hleaf]
    have hmul := Int.ediv_mul_le (Num * (SC : ℤ)) (ne_of_gt hD4)
    have hmulq : ((Num * (SC : ℤ) / D ^ 4 : ℤ) : ℚ) * ((D : ℚ) ^ 4) ≤ (Num : ℚ) * (SC : ℚ) := by
      have := (Int.cast_le (R := ℚ)).mpr hmul
      push_cast at this
      linarith
    have hSCq : (0 : ℚ) < SC := by exact_mod_cast hSC
    have hD4q : (0 : ℚ) < (D : ℚ) ^ 4 := by positivity
    rw [div_le_div_iff₀ hSCq hD4q]
    linarith
  -- (2) Num/D⁴ は各項の下界の和
  have hterm : ∀ v ∈ KF b S m,
      (((α0 : ℚ) - (α1 : ℚ) * (v : ℚ) + (α2 : ℚ) * (v : ℚ) ^ 2 - (v : ℚ) ^ 3) / ((D : ℚ) ^ 4))
        ≤ 1 / ((a : ℚ) + v) := by
    intro v _
    exact term_lower a c hcnn ha v
  have hsum : ∑ v ∈ KF b S m,
      (((α0 : ℚ) - (α1 : ℚ) * (v : ℚ) + (α2 : ℚ) * (v : ℚ) ^ 2 - (v : ℚ) ^ 3) / ((D : ℚ) ^ 4))
      = (Num : ℚ) / ((D : ℚ) ^ 4) := by
    rw [← Finset.sum_div]
    congr 1
    have e1 : ∑ v ∈ KF b S m, (v : ℚ) = (M1 : ℚ) := by
      rw [hM1, ← sum_KF_one b S hS n s1 hn hs1 m]; simp only [Int.cast_natCast, Nat.cast_sum, Nat.cast_pow, Int.cast_sum, Int.cast_pow]
    have e2 : ∑ v ∈ KF b S m, (v : ℚ) ^ 2 = (M2 : ℚ) := by
      rw [hM2, ← sum_KF_two b S hS n s1 s2 hn hs1 hs2 m]; simp only [Int.cast_natCast, Nat.cast_sum, Nat.cast_pow, Int.cast_sum, Int.cast_pow]
    have e3 : ∑ v ∈ KF b S m, (v : ℚ) ^ 3 = (M3 : ℚ) := by
      rw [hM3, ← sum_KF_three b S hS n s1 s2 s3 hn hs1 hs2 hs3 m]; simp only [Int.cast_natCast, Nat.cast_sum, Nat.cast_pow, Int.cast_sum, Int.cast_pow]
    have e0 : ((KF b S m).card : ℚ) = (N : ℚ) := by
      rw [hN, card_KF b S hS m, hn]; simp only [Int.cast_natCast]
    have hpoly : ∀ v ∈ KF b S m,
        ((α0 : ℚ) - (α1 : ℚ) * (v : ℚ) + (α2 : ℚ) * (v : ℚ) ^ 2 - (v : ℚ) ^ 3)
          = (α0 : ℚ) + (-(α1 : ℚ)) * (v : ℚ) + (α2 : ℚ) * (v : ℚ) ^ 2 + (-1) * (v : ℚ) ^ 3 := by
      intro v _; ring
    rw [Finset.sum_congr rfl hpoly, sum_poly3Q, e0, e1, e2, e3, hNum]
    push_cast
    ring
  have h2 : (Num : ℚ) / ((D : ℚ) ^ 4) ≤ ∑ v ∈ KF b S m, (1 : ℚ) / (a + v) := by
    rw [← hsum]
    exact Finset.sum_le_sum hterm
  -- (3) toNat
  have h3 : ((leafK b SC n s1 s2 s3 a m : ℕ) : ℚ) ≤ ((leafZ b SC n s1 s2 s3 a m : ℤ) : ℚ) ∨
      leafK b SC n s1 s2 s3 a m = 0 := by
    by_cases h : 0 ≤ leafZ b SC n s1 s2 s3 a m
    · left
      have := Int.toNat_of_nonneg h
      rw [leafK, ← Int.cast_natCast (R := ℚ), this]
    · right
      rw [leafK, Int.toNat_eq_zero]; omega
  rcases h3 with h3 | h3
  · have hSCq : (0 : ℚ) < SC := by exact_mod_cast hSC
    calc ((leafK b SC n s1 s2 s3 a m : ℕ) : ℚ) / SC
        ≤ ((leafZ b SC n s1 s2 s3 a m : ℤ) : ℚ) / SC := by gcongr
      _ ≤ _ := le_trans h1 h2
  · rw [h3]; simp only [Nat.cast_zero, zero_div]
    positivity

end leaf

/-! ## 4. 深さつきの展開 `loK` -/

/-- 上位 `j` 桁を展開し、葉で `leafK` を使う下界（SC 倍・ℕ）。 -/
def loK (b SC n s1 s2 s3 : ℕ) (S : Finset ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, m => leafK b SC n s1 s2 s3 a m
  | _ + 1, a, 0 => leafK b SC n s1 s2 s3 a 0
  | j + 1, a, m + 1 => ∑ e ∈ S, loK b SC n s1 s2 s3 S j (a + e * b ^ m) m

section lo

variable (b : ℕ) (S : Finset ℕ) (hS : ∀ e ∈ S, e < b) (n s1 s2 s3 : ℕ)
  (hn : S.card = n) (hs1 : ∑ e ∈ S, e = s1) (hs2 : ∑ e ∈ S, e ^ 2 = s2)
  (hs3 : ∑ e ∈ S, e ^ 3 = s3) (SC : ℕ) (hSC : 0 < SC)

include hS hn hs1 hs2 hs3 hSC in
/-- **`loK` は葉の逆数和の下界**（`APFreeBlockBounds.loI_le` と同じ帰納）。 -/
theorem loK_le : ∀ (j a m : ℕ), 0 < a →
    ((loK b SC n s1 s2 s3 S j a m : ℕ) : ℚ) / SC ≤ ∑ v ∈ KF b S m, (1 : ℚ) / (a + v) := by
  intro j
  induction j with
  | zero =>
      intro a m ha
      exact leafK_le b S hS n s1 s2 s3 hn hs1 hs2 hs3 SC hSC a m ha
  | succ j ih =>
      intro a m ha
      match m with
      | 0 => exact leafK_le b S hS n s1 s2 s3 hn hs1 hs2 hs3 SC hSC a 0 ha
      | m + 1 =>
          rw [loK, sum_KF_succ b S hS]
          have key : ∀ e ∈ S,
              ((loK b SC n s1 s2 s3 S j (a + e * b ^ m) m : ℕ) : ℚ) / SC
                ≤ ∑ v ∈ KF b S m, (1 : ℚ) / ((a : ℚ) + ((e * b ^ m + v : ℕ) : ℚ)) := by
            intro e _
            have hpos : 0 < a + e * b ^ m := by omega
            have hih := ih (a + e * b ^ m) m hpos
            refine hih.trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun v _ => ?_
            push_cast; ring_nf
          refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
          rw [Nat.cast_sum, Finset.sum_div]

end lo

/-! ## 5. 葉（接頭辞つきの塊）の並びと、その合併の上の Σ 1/x -/

/-- 塊 `(P, m, j)`：集合 `1 + P·b^m + KF m`、展開の深さ `j`。 -/
def aOf (b : ℕ) (w : ℕ × ℕ × ℕ) : ℕ := 1 + w.1 * b ^ w.2.1

def pieceF (b : ℕ) (S : Finset ℕ) (w : ℕ × ℕ × ℕ) : Finset ℕ :=
  (KF b S w.2.1).image fun v => aOf b w + v

def unionK (b : ℕ) (S : Finset ℕ) : List (ℕ × ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | w :: ws => pieceF b S w ∪ unionK b S ws

/-- 塊の右端（各桁 ≤ M）。 -/
def hiK (b M : ℕ) (w : ℕ × ℕ × ℕ) : ℕ := aOf b w + mxK b M w.2.1

/-- 隣り合う塊が離れている（右端 < 次の左端）。並びは左端の昇順とする。 -/
def ordK (b M : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | w :: w' :: ws => decide (hiK b M w < aOf b w') && ordK b M (w' :: ws)

/-- 下界の総和（SC 倍・ℕ）。 -/
def totK (b SC n s1 s2 s3 : ℕ) (S : Finset ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | w :: ws => loK b SC n s1 s2 s3 S w.2.2 (aOf b w) w.2.1 + totK b SC n s1 s2 s3 S ws

theorem totK_append (b SC n s1 s2 s3 : ℕ) (S : Finset ℕ) :
    ∀ l₁ l₂ : List (ℕ × ℕ × ℕ),
      totK b SC n s1 s2 s3 S (l₁ ++ l₂) = totK b SC n s1 s2 s3 S l₁ + totK b SC n s1 s2 s3 S l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [totK]
  | cons w l₁ ih => intro l₂; simp only [List.cons_append, totK, ih]; ring

section pieces

variable (b : ℕ) (S : Finset ℕ) (M : ℕ) (hM : ∀ e ∈ S, e ≤ M)

omit hM in
theorem pieceF_lb (w : ℕ × ℕ × ℕ) : ∀ x ∈ pieceF b S w, aOf b w ≤ x := by
  intro x hx
  simp only [pieceF, Finset.mem_image] at hx
  obtain ⟨v, _, rfl⟩ := hx
  omega

include hM in
theorem pieceF_ub (w : ℕ × ℕ × ℕ) : ∀ x ∈ pieceF b S w, x ≤ hiK b M w := by
  intro x hx
  simp only [pieceF, Finset.mem_image] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  have := KF_le b S M hM w.2.1 v hv
  simp only [hiK]; omega

include hM in
theorem unionK_lb : ∀ (w : ℕ × ℕ × ℕ) (ws : List (ℕ × ℕ × ℕ)),
    ordK b M (w :: ws) = true → ∀ x ∈ unionK b S (w :: ws), aOf b w ≤ x := by
  intro w ws
  induction ws generalizing w with
  | nil =>
      intro _ x hx
      simp only [unionK, Finset.union_empty] at hx
      exact pieceF_lb b S w x hx
  | cons w' ws ih =>
      intro hord x hx
      simp only [ordK, Bool.and_eq_true, decide_eq_true_eq] at hord
      simp only [unionK, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact pieceF_lb b S w x hx
      · have h1 := ih w' hord.2 x (by simpa [unionK] using hx)
        have h2 : aOf b w ≤ hiK b M w := by simp only [hiK]; omega
        omega

include hM in
theorem sum_unionK (f : ℕ → ℚ) : ∀ ws : List (ℕ × ℕ × ℕ), ordK b M ws = true →
    ∑ x ∈ unionK b S ws, f x = (ws.map fun w => ∑ x ∈ pieceF b S w, f x).sum := by
  intro ws
  induction ws with
  | nil => intro _; simp [unionK]
  | cons w ws ih =>
      intro hord
      cases ws with
      | nil => simp [unionK]
      | cons w' ws =>
          simp only [ordK, Bool.and_eq_true, decide_eq_true_eq] at hord
          have hdisj : Disjoint (pieceF b S w) (unionK b S (w' :: ws)) := by
            rw [Finset.disjoint_left]
            intro x hx hx2
            have h1 := pieceF_ub b S M hM w x hx
            have h2 := unionK_lb b S M hM w' ws hord.2 x hx2
            omega
          rw [unionK, Finset.sum_union hdisj, List.map_cons, List.sum_cons, ih hord.2]

omit hM in
theorem sum_pieceF (w : ℕ × ℕ × ℕ) :
    ∑ x ∈ pieceF b S w, (1 : ℚ) / x = ∑ v ∈ KF b S w.2.1, (1 : ℚ) / (aOf b w + v) := by
  rw [pieceF, Finset.sum_image (by intro x _ y _ h; exact Nat.add_left_cancel h)]
  refine Finset.sum_congr rfl fun v _ => ?_
  push_cast; ring_nf

end pieces

section total

variable (b : ℕ) (S : Finset ℕ) (hS : ∀ e ∈ S, e < b) (M : ℕ) (hM : ∀ e ∈ S, e ≤ M)
  (n s1 s2 s3 : ℕ)
  (hn : S.card = n) (hs1 : ∑ e ∈ S, e = s1) (hs2 : ∑ e ∈ S, e ^ 2 = s2)
  (hs3 : ∑ e ∈ S, e ^ 3 = s3) (SC : ℕ) (hSC : 0 < SC)

include hS hM hn hs1 hs2 hs3 hSC in
/-- **合併の上の Σ 1/x の下界**。 -/
theorem totK_le : ∀ ws : List (ℕ × ℕ × ℕ), ordK b M ws = true →
    ((totK b SC n s1 s2 s3 S ws : ℕ) : ℚ) / SC ≤ ∑ x ∈ unionK b S ws, (1 : ℚ) / x := by
  intro ws hord
  rw [sum_unionK b S M hM _ ws hord]
  induction ws with
  | nil => simp [totK]
  | cons w ws ih =>
      have hord' : ordK b M ws = true := by
        cases ws with
        | nil => rfl
        | cons w' ws => simp only [ordK, Bool.and_eq_true] at hord; exact hord.2
      have h1 : ((loK b SC n s1 s2 s3 S w.2.2 (aOf b w) w.2.1 : ℕ) : ℚ) / SC
          ≤ ∑ x ∈ pieceF b S w, (1 : ℚ) / x := by
        rw [sum_pieceF]
        exact loK_le b S hS n s1 s2 s3 hn hs1 hs2 hs3 SC hSC _ _ _ (by simp [aOf])
      have h2 := ih hord'
      simp only [totK, List.map_cons, List.sum_cons]
      rw [Nat.cast_add, add_div]
      exact add_le_add h1 h2

end total

/-! ## 6. 合併の元の性質（`K+1` に入ること・箱） -/

section members

variable (b : ℕ) (S : Finset ℕ)

theorem mem_unionK : ∀ (ws : List (ℕ × ℕ × ℕ)) (x : ℕ),
    x ∈ unionK b S ws ↔ ∃ w ∈ ws, x ∈ pieceF b S w := by
  intro ws x
  induction ws with
  | nil => simp [unionK]
  | cons w ws ih =>
      simp only [unionK, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨w', hw', h⟩)
        · exact ⟨w, Or.inl rfl, h⟩
        · exact ⟨w', Or.inr hw', h⟩
      · rintro ⟨w', (rfl | hw'), h⟩
        · exact Or.inl h
        · exact Or.inr ⟨w', hw', h⟩

/-- 全塊の接頭辞の桁が S なら、合併の元 `x` は `x ≥ 1` かつ `x − 1 ∈ K(S,b)`。 -/
theorem unionK_digIn (hb : 0 < b) (hS : ∀ e ∈ S, e < b) (h0 : 0 ∈ S) (F : ℕ)
    (ws : List (ℕ × ℕ × ℕ)) (hdig : ws.all (fun w => digB b S F w.1) = true) :
    ∀ x ∈ unionK b S ws, 1 ≤ x ∧ DigIn b S (x - 1) := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := (mem_unionK b S ws x).1 hx
  simp only [pieceF, Finset.mem_image] at hxw
  obtain ⟨v, hv, rfl⟩ := hxw
  have hP : DigIn b S w.1 := digIn_of_digB b S h0 F w.1 ((List.all_eq_true.mp hdig) w hw)
  refine ⟨by simp only [aOf]; omega, ?_⟩
  have e : aOf b w + v - 1 = w.1 * b ^ w.2.1 + v := by simp only [aOf]; omega
  rw [e]
  exact digIn_prefix b S hb hS w.2.1 w.1 hP v hv

/-- 全塊の右端が `R` 以下なら、合併の元も `R` 以下。 -/
theorem unionK_ub (M : ℕ) (hM : ∀ e ∈ S, e ≤ M) (R : ℕ)
    (ws : List (ℕ × ℕ × ℕ)) (hub : ws.all (fun w => decide (hiK b M w ≤ R)) = true) :
    ∀ x ∈ unionK b S ws, x ≤ R := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := (mem_unionK b S ws x).1 hx
  have h1 := pieceF_ub b S M hM w x hxw
  have h2 := (List.all_eq_true.mp hub) w hw
  simp only [decide_eq_true_eq] at h2
  omega

end members

end APFree.FourTermRecord

/-! ### 公理の確認 -/

#print axioms APFree.FourTermRecord.totK_le
#print axioms APFree.FourTermRecord.unionK_ub
#print axioms APFree.FourTermRecord.unionK_digIn
