import Mathlib

/-!
# Window floor: small-field threshold and analyticity angle

The small field is `β s ≤ y_h` (`s = 1 - cos ψ`); analyticity requires the plaquette angle `ψ ≤ θ_c`.
* `small_field_angle_le`: if `y_h ≤ β (1 - cos θ_c)` (floor condition), every small-field plaquette has `ψ ≤ θ_c`.
* `floor_necessary`: if the floor condition fails, the small field contains a plaquette value with `ψ > θ_c`.
* `floor_antitone`: the floor `y_h / (1 - cos θ)` is strictly decreasing on `θ ∈ (0, π]` (raising θ_c lowers the floor).
-/

open Real

namespace AnalyticFloor

theorem small_field_angle_le (β yh θc ψ : ℝ) (hβ : 0 < β)
    (hθ : θc ∈ Set.Icc 0 π) (hψ : ψ ∈ Set.Icc 0 π)
    (hfloor : yh ≤ β * (1 - cos θc)) (hs : β * (1 - cos ψ) ≤ yh) : ψ ≤ θc := by
  by_contra h
  rw [not_le] at h
  have hc : cos ψ < cos θc := strictAntiOn_cos hθ hψ h
  have : β * (1 - cos θc) < β * (1 - cos ψ) := by
    apply mul_lt_mul_of_pos_left _ hβ; linarith
  linarith

theorem floor_necessary (β yh θc : ℝ) (hβ : 0 < β) (hθ : θc ∈ Set.Icc 0 π)
    (hyh : yh ≤ 2 * β) (hbad : β * (1 - cos θc) < yh) :
    ∃ ψ ∈ Set.Icc 0 π, β * (1 - cos ψ) ≤ yh ∧ θc < ψ := by
  -- ψ := arccos (1 - yh/β)
  have h1 : -1 ≤ 1 - yh / β := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
    rw [div_le_iff₀ hβ]; linarith
  have h2 : 1 - yh / β ≤ 1 := by
    have : 0 ≤ yh / β := by
      apply div_nonneg _ hβ.le
      have := cos_le_one θc; nlinarith
    linarith
  refine ⟨arccos (1 - yh / β), ⟨arccos_nonneg _, arccos_le_pi _⟩, ?_, ?_⟩
  · rw [cos_arccos h1 h2]; field_simp; linarith
  · by_contra h
    rw [not_lt] at h
    have hc : cos θc ≤ cos (arccos (1 - yh / β)) :=
      (strictAntiOn_cos.antitoneOn) ⟨arccos_nonneg _, arccos_le_pi _⟩ hθ h
    rw [cos_arccos h1 h2] at hc
    have : β * (1 - cos θc) ≥ β * (yh / β) := by
      apply mul_le_mul_of_nonneg_left _ hβ.le; linarith
    rw [mul_div_cancel₀ _ hβ.ne'] at this
    linarith

theorem floor_antitone (yh θ1 θ2 : ℝ) (hy : 0 < yh) (h1 : 0 < θ1) (h12 : θ1 < θ2) (h2 : θ2 ≤ π) :
    yh / (1 - cos θ2) < yh / (1 - cos θ1) := by
  have hc : cos θ2 < cos θ1 :=
    strictAntiOn_cos ⟨h1.le, h12.le.trans h2⟩ ⟨(h1.trans h12).le, h2⟩ h12
  have hpos : 0 < 1 - cos θ1 := by
    have : cos θ1 < cos 0 :=
      strictAntiOn_cos ⟨le_refl 0, pi_pos.le⟩ ⟨h1.le, h12.le.trans h2⟩ h1
    rw [cos_zero] at this; linarith
  apply div_lt_div_of_pos_left hy hpos; linarith

end AnalyticFloor

#print axioms AnalyticFloor.small_field_angle_le
#print axioms AnalyticFloor.floor_necessary
#print axioms AnalyticFloor.floor_antitone
