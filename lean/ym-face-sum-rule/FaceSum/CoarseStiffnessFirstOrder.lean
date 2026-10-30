import Mathlib

/-!
# From first-order bounds on the coarse corrections to a lower bound on the stiffness

`Γ_min = (1 + Γ₀) (1 + ε_φ) / (1 + ε_a) - 1 - δ - λ`.
If `ε_φ ≥ f` with `1 + f ≥ 0`, `-1 < ε_a ≤ e`, `δ ≤ d`, `λ ≤ l` and `1 + Γ₀ ≥ 0`, then
`Γ_min ≥ (1 + Γ₀)(1 + f)/(1 + e) - 1 - d - l`.  With `Γ₀ = 1`, `f = F/β`, `e = A/β`, `d = D/β`,
`l = Λ/β` (`A ≥ F`, `A ≥ 0`) this is at least `1 - (2 (A - F) + D + Λ)/β`, and the threshold
`Γ_min ≥ 0.9` holds as soon as `β ≥ 10 (2 (A - F) + D + Λ)`.
-/

namespace CoarseFirstOrder

theorem ratio_lower (g φ a f e : ℝ) (hg : 0 ≤ g) (hf : f ≤ φ) (hf1 : 0 ≤ 1 + f)
    (ha : -1 < a) (he : a ≤ e) :
    g * (1 + f) / (1 + e) ≤ g * (1 + φ) / (1 + a) := by
  have ha1 : 0 < 1 + a := by linarith
  have he1 : 0 < 1 + e := by linarith
  rw [div_le_div_iff₀ he1 ha1]
  have h1 : g * (1 + f) * (1 + a) ≤ g * (1 + φ) * (1 + a) := by
    apply mul_le_mul_of_nonneg_right _ ha1.le
    exact mul_le_mul_of_nonneg_left (by linarith) hg
  have h2 : g * (1 + φ) * (1 + a) ≤ g * (1 + φ) * (1 + e) := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    exact mul_nonneg hg (by linarith)
  linarith

theorem gamma_min_lower (Γ₀ φ a f e δ d lam l : ℝ) (hg : 0 ≤ 1 + Γ₀) (hf : f ≤ φ)
    (hf1 : 0 ≤ 1 + f) (ha : -1 < a) (he : a ≤ e) (hδ : δ ≤ d) (hl : lam ≤ l) :
    (1 + Γ₀) * (1 + f) / (1 + e) - 1 - d - l ≤ (1 + Γ₀) * (1 + φ) / (1 + a) - 1 - δ - lam := by
  have := ratio_lower (1 + Γ₀) φ a f e hg hf hf1 ha he
  linarith

/-- First-order form with `Γ₀ = 1`. -/
theorem first_order (β A F D Λ : ℝ) (hβ : 0 < β) (hA : 0 ≤ A) (hAF : F ≤ A) :
    1 - (2 * (A - F) + D + Λ) / β ≤ 2 * (1 + F / β) / (1 + A / β) - 1 - D / β - Λ / β := by
  have hb : 0 < β + A := by linarith
  have key : 2 * (1 + F / β) / (1 + A / β) = 2 - 2 * (A - F) / (β + A) := by
    field_simp; ring
  rw [key]
  have h1 : 2 * (A - F) / (β + A) ≤ 2 * (A - F) / β :=
    div_le_div_of_nonneg_left (by linarith) hβ (by linarith)
  have h2 : (2 * (A - F) + D + Λ) / β = 2 * (A - F) / β + D / β + Λ / β := by ring
  linarith

theorem threshold (β c : ℝ) (hβ : 0 < β) (h : 10 * c ≤ β) : 0.9 ≤ 1 - c / β := by
  have : c / β ≤ 1 / 10 := by rw [div_le_iff₀ hβ]; linarith
  linarith

/-- Ledger instance: `A = 1.2`, `F = 0.9`, `D = 1.1`, `Λ = 0.5` (first-order coefficients in units of
`1/β_k` on the band `0.5 ≤ y ≤ 4`) give `c = 2.2`. -/
theorem ledger_c : 2 * ((1.2 : ℝ) - 0.9) + 1.1 + 0.5 = 2.2 := by norm_num

theorem ledger_threshold (βk : ℝ) (h : 22 ≤ βk) : 0.9 ≤ 1 - 2.2 / βk :=
  threshold βk 2.2 (by linarith) (by norm_num; linarith)

theorem ledger_at_28 : (0.928 : ℝ) ≤ 1 - 2.2 / 30.74 := by norm_num

end CoarseFirstOrder

#print axioms CoarseFirstOrder.ratio_lower
#print axioms CoarseFirstOrder.gamma_min_lower
#print axioms CoarseFirstOrder.first_order
#print axioms CoarseFirstOrder.threshold
#print axioms CoarseFirstOrder.ledger_c
#print axioms CoarseFirstOrder.ledger_threshold
#print axioms CoarseFirstOrder.ledger_at_28
