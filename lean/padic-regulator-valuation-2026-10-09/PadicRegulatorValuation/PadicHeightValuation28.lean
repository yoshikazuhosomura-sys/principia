/-
  p 進高さの付値（その 28）：分母の余因子と余裕・閉包の指数 p² での三層目の潰れ・
  二点の差の付値則・二本の道の数え上げ。

  背景（形式化しない部分）：x(Q) = a/d²（既約）、d = p^D·c（p ∤ c）。
  素朴な高さ h = log max(|a|, d²)。閉包の指数 p² の箱では Λ∩E_1 ⊆ E_3。
  本ファイルはそこから先の閉じた算術と線型代数だけを扱う。
-/
import Mathlib

namespace PadicCofactor

/-! ## 1. 補題 D′：分母の余因子は余裕で上から抑えられる -/

/-- `d = p^D * c`、`d² ≤ H` なら `2 log c + 2 D log p ≤ log H`。 -/
theorem cofactor_log_le {p D c H : ℕ} (hp : 1 ≤ p) (hc : 0 < c)
    (hH : (p ^ D * c) ^ 2 ≤ H) :
    2 * Real.log c + 2 * D * Real.log p ≤ Real.log H := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hd0 : (0 : ℝ) < ((p : ℝ) ^ D * c) ^ 2 := by positivity
  have hle : ((p : ℝ) ^ D * c) ^ 2 ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 := Real.log_le_log hd0 hle
  have h2 : Real.log (((p : ℝ) ^ D * c) ^ 2) = 2 * Real.log c + 2 * D * Real.log p := by
    rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt hc0), Real.log_pow]
    push_cast; ring
  linarith [h1, h2]

/-- 余裕が `2 log 2` 未満なら余因子は 1。 -/
theorem cofactor_eq_one_of_slack_lt {c : ℕ} {s : ℝ} (hc : 0 < c)
    (hle : 2 * Real.log c ≤ s) (hs : s < 2 * Real.log 2) : c = 1 := by
  by_contra hne
  have h2 : 2 ≤ c := by omega
  have : Real.log 2 ≤ Real.log c := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast h2
  linarith

/-- 等号条件（自然数の形）：`max a (p^D c)² = p^(2D)` ⟺ `c = 1 ∧ a ≤ (p^D c)²`。 -/
theorem max_eq_iff {p D c a : ℕ} (hp : 1 ≤ p) (hc : 0 < c) :
    max a ((p ^ D * c) ^ 2) = p ^ (2 * D) ↔ c = 1 ∧ a ≤ (p ^ D * c) ^ 2 := by
  have hpD : 0 < p ^ D := pow_pos (by omega : 0 < p) D
  have hsq : (p ^ D * c) ^ 2 = p ^ (2 * D) * c ^ 2 := by ring
  constructor
  · intro h
    have hle : (p ^ D * c) ^ 2 ≤ p ^ (2 * D) := h ▸ le_max_right _ _
    rw [hsq] at hle
    have hpos : 0 < p ^ (2 * D) := pow_pos (by omega : 0 < p) _
    have hc2 : c ^ 2 ≤ 1 := by
      by_contra hh0
      have hh : 1 < c ^ 2 := not_le.mp hh0
      have : p ^ (2 * D) * 1 < p ^ (2 * D) * c ^ 2 := Nat.mul_lt_mul_of_pos_left hh hpos
      omega
    have hc1 : c = 1 := by nlinarith
    refine ⟨hc1, ?_⟩
    have ha : a ≤ p ^ (2 * D) := h ▸ le_max_left _ _
    rw [hsq, hc1]; simpa using ha
  · rintro ⟨rfl, ha⟩
    rw [hsq] at ha ⊢
    simp only [one_pow, mul_one] at ha ⊢
    exact max_eq_right ha

end PadicCofactor

namespace PadicClosureCollapse

/-! ## 2. 閉包の指数 p² の箱：三層目は χ の関数に潰れ、χ ≠ 0 の点は付値 0 -/

variable {M : Type*} [AddCommGroup M] {p : ℕ} [Fact p.Prime]

/-- `χ` が全射で `γ₂` が `ker χ` の上で消えるなら `γ₂ = c·χ`。 -/
theorem factor_through_chi (χ γ₂ : M →+ ZMod p) (hχ : Function.Surjective χ)
    (hker : ∀ x, χ x = 0 → γ₂ x = 0) : ∃ c : ZMod p, ∀ x, γ₂ x = c * χ x := by
  obtain ⟨x₀, hx₀⟩ := hχ 1
  refine ⟨γ₂ x₀, fun x => ?_⟩
  have hk : χ (x - (χ x).val • x₀) = 0 := by
    rw [map_sub, map_nsmul, hx₀, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, sub_self]
  have h := hker _ hk
  rw [map_sub, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, sub_eq_zero] at h
  rw [h, mul_comm]

/-- `p ≠ 2` なら `2 ≠ 0`（`ZMod p`）。 -/
theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h'
  exact hp2 this

/-- `M̄ = 2λχ⊗χ`（`γ ≡ 0`）で `λ ≠ 0` なら、`χ(P) ≠ 0` の点の対角成分は 0 でない。 -/
theorem diag_ne_zero (hp2 : p ≠ 2) {lam a : ZMod p} (hl : lam ≠ 0) (ha : a ≠ 0) :
    2 * lam * a ^ 2 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (two_ne_zero_of_ne_two hp2) hl) (pow_ne_zero 2 ha)

end PadicClosureCollapse

namespace PadicPairLaw

/-! ## 3. 二点の差の付値則：一項がちょうど付値 v、残りが p^(v+1) で割れるなら和もちょうど v -/

/-- `p^v ∣ x`・`p^(v+1) ∤ x`・`p^(v+1) ∣ y`・`p^(v+1) ∣ z` なら `x+y+z` もちょうど付値 `v`。 -/
theorem exact_of_deeper {p : ℤ} {v : ℕ} {x y z : ℤ}
    (hx : p ^ v ∣ x) (hx' : ¬ p ^ (v + 1) ∣ x)
    (hy : p ^ (v + 1) ∣ y) (hz : p ^ (v + 1) ∣ z) :
    p ^ v ∣ x + y + z ∧ ¬ p ^ (v + 1) ∣ x + y + z := by
  have hpv : p ^ v ∣ p ^ (v + 1) := pow_dvd_pow p (Nat.le_succ v)
  refine ⟨dvd_add (dvd_add hx (hpv.trans hy)) (hpv.trans hz), fun h => hx' ?_⟩
  have : x = (x + y + z) - y - z := by ring
  rw [this]
  exact dvd_sub (dvd_sub h hy) hz

/-- 命題 20(v) の `j = 3` の読み：`Θ` 側がちょうど付値 2、`F` 側が `p^(1+dF)`（`dF ≥ 2`）、
`ℒ` 側が `p^4` で割れるなら、差はちょうど付値 2。 -/
theorem pair_law_j3 {p : ℤ} {dF : ℕ} (hdF : 2 ≤ dF) {θ φ l : ℤ}
    (hθ : p ^ 2 ∣ θ) (hθ' : ¬ p ^ 3 ∣ θ) (hφ : p ^ (1 + dF) ∣ φ) (hl : p ^ 4 ∣ l) :
    p ^ 2 ∣ θ + φ + l ∧ ¬ p ^ 3 ∣ θ + φ + l := by
  have hφ3 : p ^ 3 ∣ φ := (pow_dvd_pow p (by omega : 3 ≤ 1 + dF)).trans hφ
  have hl3 : p ^ 3 ∣ l := (pow_dvd_pow p (by omega : 3 ≤ 4)).trans hl
  exact exact_of_deeper (v := 2) hθ hθ' hφ3 hl3

/-- 逆向き（`F` 側が先に来る）：`F` 側がちょうど付値 `1 + dF`、`Θ` 側と `ℒ` 側がそれより深いなら差はちょうど `1 + dF`。 -/
theorem pair_law_F_leads {p : ℤ} {dF : ℕ} {θ φ l : ℤ}
    (hφ : p ^ (1 + dF) ∣ φ) (hφ' : ¬ p ^ (1 + dF + 1) ∣ φ)
    (hθ : p ^ (1 + dF + 1) ∣ θ) (hl : p ^ (1 + dF + 1) ∣ l) :
    p ^ (1 + dF) ∣ φ + θ + l ∧ ¬ p ^ (1 + dF + 1) ∣ φ + θ + l :=
  exact_of_deeper hφ hφ' hθ hl

end PadicPairLaw

namespace PadicTwoRoutes

/-! ## 4. 二本の道：(c, d) ∈ (Z/p)² で「c = c₀ または d = 0」はちょうど 2p − 1 個 -/

open Finset

variable {p : ℕ} [Fact p.Prime]

theorem card_two_routes (c₀ : ZMod p) :
    (univ.filter (fun q : ZMod p × ZMod p => q.1 = c₀ ∨ q.2 = 0)).card + 1 = 2 * p := by
  have hA : (univ.filter fun q : ZMod p × ZMod p => q.1 = c₀) =
      ({c₀} : Finset (ZMod p)) ×ˢ univ := by
    ext ⟨a, b⟩; simp [eq_comm]
  have hB : (univ.filter fun q : ZMod p × ZMod p => q.2 = 0) =
      (univ : Finset (ZMod p)) ×ˢ {0} := by
    ext ⟨a, b⟩; simp [eq_comm]
  have hAB : (univ.filter fun q : ZMod p × ZMod p => q.1 = c₀) ∩
      (univ.filter fun q : ZMod p × ZMod p => q.2 = 0) = {(c₀, 0)} := by
    ext ⟨a, b⟩; simp [Prod.ext_iff]
  rw [filter_or]
  have h := card_union_add_card_inter (univ.filter fun q : ZMod p × ZMod p => q.1 = c₀)
    (univ.filter fun q : ZMod p × ZMod p => q.2 = 0)
  rw [hAB, hA, hB] at h
  rw [hA, hB]
  simp only [card_product, card_singleton, card_univ, ZMod.card, one_mul, mul_one] at h ⊢
  omega

end PadicTwoRoutes

#print axioms PadicCofactor.cofactor_log_le
#print axioms PadicCofactor.cofactor_eq_one_of_slack_lt
#print axioms PadicCofactor.max_eq_iff
#print axioms PadicClosureCollapse.factor_through_chi
#print axioms PadicClosureCollapse.two_ne_zero_of_ne_two
#print axioms PadicClosureCollapse.diag_ne_zero
#print axioms PadicPairLaw.exact_of_deeper
#print axioms PadicPairLaw.pair_law_j3
#print axioms PadicPairLaw.pair_law_F_leads
#print axioms PadicTwoRoutes.card_two_routes
