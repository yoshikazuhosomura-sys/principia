/-
  p 進高さの付値（標準高さ版）：命題 24 の閾値を素朴な高さから標準高さ ĥ へ移す算術。

  背景（形式化しない部分＝仮定として入る）：E/Q の大域極小模型、p は良還元。
  ĥ は PARI の正規化（Silverman の二倍）で、Δ^{1/12} の項を積公式で落とした局所高さ λ'_v の和：
    ĥ(Q) = λ'_∞(Q) + Σ_ℓ λ'_ℓ(Q)。
  良還元の ℓ では λ'_ℓ(Q) = max(0, log|x(Q)|_ℓ)、特異還元の点では成分ごとの補正（≤ 0）。
  p では λ'_p(Q) = 2 D(Q) log p（D は形式群の深さ）。残り R(Q) := ĥ(Q) − 2D log p は v ≠ p の和。
  本ファイルが閉じるのは：
  * R の分解と下界：R = 2 log c′ + λ'_∞ + Σ corr_ℓ、各項の下界から R ≥ m_∞ + Σ m_ℓ（＝β）
  * 深さ k の点は ĥ ≥ 2k log p + β（素朴版の補題 23 の標準高さ版）とその対偶
  * 乗法的還元 I_N の補正の下限：i(N−i) ≤ ⌊N/2⌋⌈N/2⌉、4 i(N−i) ≤ N²
  * 全射性：ker χ に ĥ < 4 log p + β の元があり、ker χ で γ が消える元は深さ ≥ 2 なら (χ,γ) は全射
  解析（局所高さの存在・分解・成分ごとの補正の値・λ'_∞ の下限）は仮定。
-/
import Mathlib

namespace PadicCanonicalHeight

open Finset

/-! ## 1. v ≠ p の局所高さの和の下界 -/

/-- 分解 `R = 2 log c′ + λ∞ + Σ_{ℓ∈S} corr ℓ` と各項の下界（`0 ≤ log c′`・`m∞ ≤ λ∞`・`m ℓ ≤ corr ℓ`）
から `m∞ + Σ m ℓ ≤ R`。仮定：`hc : 0 ≤ logc`、`hinf : mInf ≤ lamInf`、`hloc : ∀ ℓ ∈ S, m ℓ ≤ corr ℓ`、
`hR : R = 2 * logc + lamInf + Σ corr`。 -/
theorem beta_le_remainder_of_local_bounds {ι : Type*} (S : Finset ι) (m corr : ι → ℝ)
    (logc lamInf mInf R : ℝ) (hc : 0 ≤ logc) (hinf : mInf ≤ lamInf)
    (hloc : ∀ ℓ ∈ S, m ℓ ≤ corr ℓ)
    (hR : R = 2 * logc + lamInf + ∑ ℓ ∈ S, corr ℓ) :
    mInf + ∑ ℓ ∈ S, m ℓ ≤ R := by
  have hs : ∑ ℓ ∈ S, m ℓ ≤ ∑ ℓ ∈ S, corr ℓ := Finset.sum_le_sum hloc
  rw [hR]; linarith

/-- 素朴な余り `s = 2 log c′ + max(0, log|x|∞)` と標準の余り `R = 2 log c′ + λ∞ + Σ corr` の差は
`p` の外の項だけ：`R − s = (λ∞ − max(0, log|x|∞)) + Σ corr`（`c′` の項は打ち消し合う）。
仮定：`hs`・`hR` の二つの分解。 -/
theorem remainder_sub_slack {ι : Type*} (S : Finset ι) (corr : ι → ℝ)
    (logc lamInf logx R s : ℝ)
    (hs : s = 2 * logc + max 0 logx)
    (hR : R = 2 * logc + lamInf + ∑ ℓ ∈ S, corr ℓ) :
    R - s = (lamInf - max 0 logx) + ∑ ℓ ∈ S, corr ℓ := by
  rw [hR, hs]; ring

/-! ## 2. 深さと標準高さ（補題 23 の標準高さ版） -/

/-- 仮定：`hdec : h = 2 D log p + R`（p での局所高さが `2 D log p`）、`hR : β ≤ R`、`hk : k ≤ D`、
`hlogp : 0 ≤ log p`。結論：`2 k log p + β ≤ h`。 -/
theorem canonical_ge_of_depth (h R β logp : ℝ) (D k : ℕ) (hlogp : 0 ≤ logp)
    (hdec : h = 2 * (D : ℝ) * logp + R) (hR : β ≤ R) (hk : k ≤ D) :
    2 * (k : ℝ) * logp + β ≤ h := by
  have hkD : (k : ℝ) ≤ (D : ℝ) := by exact_mod_cast hk
  have : 2 * (k : ℝ) * logp ≤ 2 * (D : ℝ) * logp := by nlinarith
  linarith

/-- 対偶（同じ仮定 `hdec`・`hR`・`hlogp`）：`h < 2 k log p + β` なら深さは `k` 未満。 -/
theorem depth_lt_of_canonical_lt (h R β logp : ℝ) (D k : ℕ) (hlogp : 0 ≤ logp)
    (hdec : h = 2 * (D : ℝ) * logp + R) (hR : β ≤ R) (hlt : h < 2 * (k : ℝ) * logp + β) :
    D < k := by
  by_contra hc
  push Not at hc
  exact absurd (canonical_ge_of_depth h R β logp D k hlogp hdec hR hc) (not_le.mpr hlt)

/-! ## 3. 還元の型ごとの定数：乗法的還元 I_N -/

/-- 成分 `i`（`0 ≤ i ≤ N`）の補正 `−i(N−i)/N` は `−N/4` 以上：`4 i (N − i) ≤ N²`（実数で）。 -/
theorem four_mul_comp_le_sq (i N : ℝ) : 4 * i * (N - i) ≤ N ^ 2 := by
  nlinarith [sq_nonneg (N - 2 * i)]

/-- 自然数での鋭い形：`i (N − i) ≤ ⌊N/2⌋ (N − ⌊N/2⌋)`（`i ≤ N`）。I_N 分裂の下限 `m_ℓ` を与える。 -/
theorem comp_le_half (i N : ℕ) (hi : i ≤ N) : i * (N - i) ≤ (N / 2) * (N - N / 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = i + j := ⟨N - i, by omega⟩
  have e1 : i + j - i = j := by omega
  rw [e1]
  rcases Nat.even_or_odd (i + j) with ⟨q, hq⟩ | ⟨q, hq⟩
  · have h2 : (i + j) / 2 = q := by omega
    have h3 : i + j - q = q := by omega
    rw [h2, h3]
    have hj : (j : ℤ) = 2 * q - i := by omega
    zify; rw [hj]; nlinarith [sq_nonneg ((i : ℤ) - q)]
  · have h2 : (i + j) / 2 = q := by omega
    have h3 : i + j - q = q + 1 := by omega
    rw [h2, h3]
    have hj : (j : ℤ) = 2 * q + 1 - i := by omega
    have key : 0 ≤ ((q : ℤ) - i) * ((q : ℤ) - i + 1) := by
      rcases le_or_gt i q with h | h
      · have : (i : ℤ) ≤ q := by exact_mod_cast h
        apply mul_nonneg <;> linarith
      · have : (q : ℤ) + 1 ≤ i := by exact_mod_cast h
        apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
    zify; rw [hj]; nlinarith [key]

/-! ## 4. 全射性（命題 24 の標準高さ版の論理部分） -/

variable {M : Type*} [AddCommGroup M] {p : ℕ} [Fact p.Prime]

/-- ファイル 27 の `surjective_pair_iff` と同じ言明（このファイルは `import Mathlib` だけで閉じるため再証明）。
仮定：`hχ : χ` が全射。 -/
theorem surjective_pair_iff' (χ γ : M →+ ZMod p) (hχ : Function.Surjective χ) :
    Function.Surjective (fun m => (χ m, γ m)) ↔ ∃ x, χ x = 0 ∧ γ x ≠ 0 := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs (0, 1)
    refine ⟨x, ?_, ?_⟩
    · simpa using congrArg Prod.fst hx
    · have : γ x = 1 := by simpa using congrArg Prod.snd hx
      rw [this]; exact one_ne_zero
  · rintro ⟨x₀, hx₀χ, hx₀γ⟩ ⟨a, b⟩
    obtain ⟨z, hz⟩ := hχ a
    set t : ZMod p := (b - γ z) / γ x₀ with ht
    refine ⟨z + (t.val : ℤ) • x₀, ?_⟩
    have hc : ((t.val : ℤ) : ZMod p) = t := by
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    have h1 : χ (z + (t.val : ℤ) • x₀) = a := by
      rw [map_add, map_zsmul, hx₀χ, smul_zero, add_zero, hz]
    have h2 : γ (z + (t.val : ℤ) • x₀) = b := by
      rw [map_add, map_zsmul, zsmul_eq_mul, hc, ht]
      field_simp
      ring
    exact Prod.ext h1 h2

/-- 命題 24ᶜ の論理部分。仮定（幾何は仮定として入る）：
`hχ`：χ は全射（ι）。`hdeep`：`ker χ` の元で γ が消えるものは深さ `≥ 2`（分裂で `ker γ ∩ ker χ = Λ ∩ E_2`）。
`hdec`：`ĥ x = 2 D(x) log p + R x`（p は良還元）。`hR`：`β ≤ R x`（v ≠ p の局所高さの下界）。
`hlogp : 0 ≤ log p`。`x ∈ ker χ` で `ĥ x < 4 log p + β` なら `(χ,γ)` は全射。 -/
theorem surjective_of_canonical_lt_four_log_add_beta (χ γ : M →+ ZMod p)
    (hχ : Function.Surjective χ) (D : M → ℕ) (hc R : M → ℝ) (β logp : ℝ)
    (hlogp : 0 ≤ logp)
    (hdeep : ∀ y, χ y = 0 → γ y = 0 → 2 ≤ D y)
    (hdec : ∀ y, hc y = 2 * (D y : ℝ) * logp + R y) (hR : ∀ y, β ≤ R y)
    (x : M) (hx : χ x = 0) (hlt : hc x < 4 * logp + β) :
    Function.Surjective (fun m => (χ m, γ m)) := by
  refine (surjective_pair_iff' χ γ hχ).mpr ⟨x, hx, ?_⟩
  intro hγ
  have h2 := hdeep x hx hγ
  have hge := canonical_ge_of_depth (hc x) (R x) β logp (D x) 2 hlogp (hdec x) (hR x) h2
  have : (2 : ℝ) * ((2 : ℕ) : ℝ) * logp = 4 * logp := by push_cast; ring
  linarith

/-- 素朴版と標準版の和：どちらかの閾値の下に `ker χ` の元があれば全射。
仮定：`hχ`・`hdeep`・素朴版の下界 `hnaive : ∀ y, 2 ≤ D y → 4 log p ≤ hn y`（補題 23）・
`hdec`・`hR`・`hlogp`。 -/
theorem surjective_of_naive_or_canonical (χ γ : M →+ ZMod p)
    (hχ : Function.Surjective χ) (D : M → ℕ) (hn hc R : M → ℝ) (β logp : ℝ)
    (hlogp : 0 ≤ logp)
    (hdeep : ∀ y, χ y = 0 → γ y = 0 → 2 ≤ D y)
    (hnaive : ∀ y, 2 ≤ D y → 4 * logp ≤ hn y)
    (hdec : ∀ y, hc y = 2 * (D y : ℝ) * logp + R y) (hR : ∀ y, β ≤ R y)
    (x : M) (hx : χ x = 0) (hlt : hn x < 4 * logp ∨ hc x < 4 * logp + β) :
    Function.Surjective (fun m => (χ m, γ m)) := by
  rcases hlt with h | h
  · refine (surjective_pair_iff' χ γ hχ).mpr ⟨x, hx, ?_⟩
    intro hγ
    have := hnaive x (hdeep x hx hγ)
    linarith
  · exact surjective_of_canonical_lt_four_log_add_beta χ γ hχ D hc R β logp hlogp hdeep hdec hR x hx h

end PadicCanonicalHeight

#print axioms PadicCanonicalHeight.beta_le_remainder_of_local_bounds
#print axioms PadicCanonicalHeight.remainder_sub_slack
#print axioms PadicCanonicalHeight.canonical_ge_of_depth
#print axioms PadicCanonicalHeight.depth_lt_of_canonical_lt
#print axioms PadicCanonicalHeight.four_mul_comp_le_sq
#print axioms PadicCanonicalHeight.comp_le_half
#print axioms PadicCanonicalHeight.surjective_pair_iff'
#print axioms PadicCanonicalHeight.surjective_of_canonical_lt_four_log_add_beta
#print axioms PadicCanonicalHeight.surjective_of_naive_or_canonical
