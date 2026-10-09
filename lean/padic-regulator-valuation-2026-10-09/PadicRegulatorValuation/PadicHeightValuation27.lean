/-
  p 進高さの付値（その 27）：有理点の「深さ」と高さ、そして (χ,γ) の全射性。

  背景（形式化しない部分）：E/Q は p ≥ 5 で良還元、Λ = E(Q)/tors、
  E_k(Q_p) は形式群の第 k 層。良還元では Q ∈ E_k ∖ E_{k+1} ⟺ v_p(denom x(Q)) = 2k。
  本ファイルはそこから先の**閉じた算術と線型代数**だけを扱う：

  * 深さ k の点は高さが 2k·log p 以上（`log_denom_ge`・`height_ge_of_depth`）
  * χ が全射なら、(χ,γ) が全射でないことは「γ が ker χ の上で消える」ことと同値
  * 零仮説の濃度：(χ₁,χ₂) ≠ 0 のとき det が 0 になる (γ₁,γ₂) はちょうど p 個
  * 上の二つを繋いだ形（閉包の指数が 1 であることの十分条件）
-/
import Mathlib

namespace PadicDepthHeight

open Finset

/-! ## 1. 深さは高さで上から抑えられる（補題 D の算術） -/

/-- `p ^ m ∣ d`、`0 < d` なら `m * Real.log p ≤ Real.log d`。 -/
theorem log_denom_ge {p d : ℕ} (hp : 2 ≤ p) (hd : 0 < d) (m : ℕ) (h : p ^ m ∣ d) :
    (m : ℝ) * Real.log p ≤ Real.log d := by
  have hple : (p : ℝ) ^ m ≤ (d : ℝ) := by
    have : p ^ m ≤ d := Nat.le_of_dvd hd h
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
  have hpow : (0 : ℝ) < (p : ℝ) ^ m := by positivity
  have := Real.log_le_log hpow hple
  simpa [Real.log_pow] using this

/-- 補題 D。点の分母が `p ^ (2 k)` で割れるなら、その素朴な高さ `log (max |a| d)` は
`2 k log p` 以上。ここで `hden : d ≤ H` は `H = max |a| d` を表す（`H` が分母を上から抑える）。 -/
theorem height_ge_of_depth {p d H : ℕ} (hp : 2 ≤ p) (hd : 0 < d) (k : ℕ)
    (hdvd : p ^ (2 * k) ∣ d) (hden : d ≤ H) :
    (2 * k : ℝ) * Real.log p ≤ Real.log H := by
  have h1 : ((2 * k : ℕ) : ℝ) * Real.log p ≤ Real.log d := log_denom_ge hp hd _ hdvd
  have hH : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2 : Real.log d ≤ Real.log H := by
    apply Real.log_le_log hH
    exact_mod_cast hden
  have : ((2 * k : ℕ) : ℝ) = (2 * k : ℝ) := by push_cast; ring
  linarith [h1, h2, this.symm ▸ h1]

/-- 対偶の形（命題 U に使う向き）：高さが `2 k log p` 未満なら深さは `k` 未満。 -/
theorem depth_lt_of_height_lt {p d H : ℕ} (hp : 2 ≤ p) (hd : 0 < d) (k : ℕ)
    (hden : d ≤ H) (hlt : Real.log H < (2 * k : ℝ) * Real.log p) :
    ¬ (p ^ (2 * k) ∣ d) := by
  intro hdvd
  exact absurd (height_ge_of_depth hp hd k hdvd hden) (not_le.mpr hlt)

end PadicDepthHeight

namespace PadicSurjectivity

/-! ## 2. (χ,γ) の全射性は「γ が ker χ の上で消えないこと」 -/

variable {M : Type*} [AddCommGroup M] {p : ℕ} [Fact p.Prime]

/-- χ が全射のとき、`(χ,γ) : M → (Z/p)²` が全射 ⟺ `γ` が `ker χ` の上で零でない。 -/
theorem surjective_pair_iff (χ γ : M →+ ZMod p) (hχ : Function.Surjective χ) :
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

/-- 命題 U の論理部分。`ker χ` の元がどれも「深い」ことがないなら `(χ,γ)` は全射。
仮定 `hshallow` は「深さ 2 の元でない `x ∈ ker χ` が一つある」ことを、
補題 D（`PadicDepthHeight.depth_lt_of_height_lt`）から得た形で受け取る。 -/
theorem surjective_of_shallow_kernel_element (χ γ : M →+ ZMod p)
    (hχ : Function.Surjective χ) (x : M) (hx : χ x = 0) (hγ : γ x ≠ 0) :
    Function.Surjective (fun m => (χ m, γ m)) :=
  (surjective_pair_iff χ γ hχ).mpr ⟨x, hx, hγ⟩

end PadicSurjectivity

namespace PadicClosureIndex

/-! ## 3. 閉包の指数 `p ^ (min D_Q D_1 - 1)` の算術 -/

/-- 分裂（`2 ≤ D₁`）のとき、指数が 1（＝ `Λ` の `p` 進閉包が `E(Q_p)` 全体）であることは
`D_Q = 1` と同値。 -/
theorem index_zero_iff (DQ D1 : ℕ) (h1 : 2 ≤ D1) (hQ : 1 ≤ DQ) :
    min DQ D1 - 1 = 0 ↔ DQ = 1 := by omega

/-- 指数が `p²` 以上になるには `D_Q ≥ 3` と `D₁ ≥ 3` の両方が必要。 -/
theorem index_ge_two_iff (DQ D1 : ℕ) : 2 ≤ min DQ D1 - 1 ↔ 3 ≤ DQ ∧ 3 ≤ D1 := by omega

/-- 指数は各層の深さで上から抑えられる。 -/
theorem index_le (DQ D1 : ℕ) : min DQ D1 - 1 ≤ DQ - 1 ∧ min DQ D1 - 1 ≤ D1 - 1 := by omega

end PadicClosureIndex

namespace PadicNullModel

open Finset

/-! ## 4. 零仮説の濃度——`det ≡ 0` になる対はちょうど `p` 個 -/

variable {p : ℕ} [Fact p.Prime]

/-- `c₁ ≠ 0` のとき `c₁ b − c₂ a = 0` は `b = c₂ a / c₁` と同値。 -/
theorem det_zero_iff {c₁ c₂ a b : ZMod p} (h : c₁ ≠ 0) :
    c₁ * b - c₂ * a = 0 ↔ b = c₂ * a / c₁ := by
  rw [sub_eq_zero, eq_div_iff h, mul_comm b c₁]

/-- `c₁ ≠ 0` のとき、`det = 0` となる対 `(a,b)` はちょうど `p` 個。 -/
theorem card_det_zero_of_ne {c₁ c₂ : ZMod p} (h : c₁ ≠ 0) :
    (univ.filter (fun g : ZMod p × ZMod p => c₁ * g.2 - c₂ * g.1 = 0)).card = p := by
  classical
  have hinj : Function.Injective (fun a : ZMod p => ((a, c₂ * a / c₁) : ZMod p × ZMod p)) := by
    intro a b hab
    exact (Prod.mk.injEq _ _ _ _).mp hab |>.1
  have himg : (univ.image (fun a : ZMod p => ((a, c₂ * a / c₁) : ZMod p × ZMod p)))
      = univ.filter (fun g : ZMod p × ZMod p => c₁ * g.2 - c₂ * g.1 = 0) := by
    ext g
    simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨a, rfl⟩
      exact (det_zero_iff h).mpr rfl
    · intro hg
      exact ⟨g.1, by rw [Prod.ext_iff]; exact ⟨rfl, ((det_zero_iff h).mp hg).symm⟩⟩
  rw [← himg, card_image_of_injective _ hinj, card_univ, ZMod.card]

/-- `c₁ = 0` かつ `c₂ ≠ 0` のときも同じくちょうど `p` 個。 -/
theorem card_det_zero_of_fst_eq_zero {c₂ : ZMod p} (h : c₂ ≠ 0) :
    (univ.filter (fun g : ZMod p × ZMod p => (0 : ZMod p) * g.2 - c₂ * g.1 = 0)).card = p := by
  classical
  have hinj : Function.Injective (fun b : ZMod p => ((0, b) : ZMod p × ZMod p)) := by
    intro a b hab
    exact (Prod.mk.injEq _ _ _ _).mp hab |>.2
  have himg : (univ.image (fun b : ZMod p => ((0, b) : ZMod p × ZMod p)))
      = univ.filter (fun g : ZMod p × ZMod p => (0 : ZMod p) * g.2 - c₂ * g.1 = 0) := by
    ext g
    simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨b, rfl⟩
      simp
    · intro hg
      have : g.1 = 0 := by
        have : c₂ * g.1 = 0 := by linear_combination -hg
        exact (mul_eq_zero.mp this).resolve_left h
      exact ⟨g.2, by rw [Prod.ext_iff]; exact ⟨this.symm ▸ rfl, rfl⟩⟩
  rw [← himg, card_image_of_injective _ hinj, card_univ, ZMod.card]

/-- 零仮説：`(c₁,c₂) ≠ (0,0)` なら密度はちょうど `1/p`。 -/
theorem density_det_zero {c₁ c₂ : ZMod p} (h : ¬(c₁ = 0 ∧ c₂ = 0)) :
    (univ.filter (fun g : ZMod p × ZMod p => c₁ * g.2 - c₂ * g.1 = 0)).card * p
      = Fintype.card (ZMod p × ZMod p) := by
  have hcard : Fintype.card (ZMod p × ZMod p) = p * p := by
    simp [Fintype.card_prod, ZMod.card]
  by_cases hc₁ : c₁ = 0
  · have hc₂ : c₂ ≠ 0 := fun hh => h ⟨hc₁, hh⟩
    subst hc₁
    rw [card_det_zero_of_fst_eq_zero hc₂, hcard]
  · rw [card_det_zero_of_ne hc₁, hcard]

end PadicNullModel

/-! ## 末尾：公理の確認 -/
#print axioms PadicDepthHeight.log_denom_ge
#print axioms PadicDepthHeight.height_ge_of_depth
#print axioms PadicDepthHeight.depth_lt_of_height_lt
#print axioms PadicSurjectivity.surjective_pair_iff
#print axioms PadicSurjectivity.surjective_of_shallow_kernel_element
#print axioms PadicClosureIndex.index_zero_iff
#print axioms PadicClosureIndex.index_ge_two_iff
#print axioms PadicClosureIndex.index_le
#print axioms PadicNullModel.det_zero_iff
#print axioms PadicNullModel.card_det_zero_of_ne
#print axioms PadicNullModel.card_det_zero_of_fst_eq_zero
#print axioms PadicNullModel.density_det_zero
