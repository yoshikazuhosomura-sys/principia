/-
  Hidden convexity of the discrete double-well path action on the "core" box.

  Setting: sites `0, 1, …, n+1`, boundary values `z 0 = a`, `z (n+1) = b` with `a, b ≤ 0`,
  interior sites in `[-c, 0]`, and the action
      S(z) = (∑_{i ≤ n} (z(i+1) - z i)^2) / (2ε) + ε ∑_{1 ≤ i ≤ n} (z i ^ 2 - 1)^2 / 8 .
  In the coordinates `ρ = z^2` the action becomes
      S~(ρ) = (∑ kin (ρ i) (ρ (i+1))) / (2ε) + ε ∑ (ρ i - 1)^2 / 8 ,   kin p q = p + q - 2 √(p q),
  and `S~` is midpoint strongly convex (modulus coming from the potential only):
      S~(mid) ≤ (S~ p + S~ q)/2 - (ε/32) ∑ (p i - q i)^2 .
  The kinetic part is midpoint convex because the geometric mean is midpoint concave
  (a Cauchy–Schwarz inequality).  Consequence: the minimiser of `S` over the box is unique.

  Everything is elementary real algebra; no numerical input.
-/
import Mathlib

namespace LatticeGauge.HiddenConvexity

open Finset

/-- kinetic term in the squared coordinates -/
noncomputable def kin (p q : ℝ) : ℝ := p + q - 2 * Real.sqrt (p * q)

theorem cauchy_schwarz_two (x y u v : ℝ) :
    (x * y + u * v) ^ 2 ≤ (x ^ 2 + u ^ 2) * (y ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (x * v - u * y)]

/-- midpoint concavity of the geometric mean, written in square roots -/
theorem geom_mean_midpoint (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (x * y + u * v) / 2 ≤ Real.sqrt (((x ^ 2 + u ^ 2) / 2) * ((y ^ 2 + v ^ 2) / 2)) := by
  have h0 : 0 ≤ (x * y + u * v) / 2 := by positivity
  calc (x * y + u * v) / 2 = Real.sqrt (((x * y + u * v) / 2) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [cauchy_schwarz_two x y u v])

/-- midpoint convexity of the kinetic term in `ρ` -/
theorem kin_midpoint (p q p' q' : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hp' : 0 ≤ p') (hq' : 0 ≤ q') :
    kin ((p + p') / 2) ((q + q') / 2) ≤ (kin p q + kin p' q') / 2 := by
  unfold kin
  have h3 : (Real.sqrt p * Real.sqrt q + Real.sqrt p' * Real.sqrt q') / 2 ≤
      Real.sqrt (((p + p') / 2) * ((q + q') / 2)) := by
    have := geom_mean_midpoint (Real.sqrt p) (Real.sqrt q) (Real.sqrt p') (Real.sqrt q')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rwa [Real.sq_sqrt hp, Real.sq_sqrt hq, Real.sq_sqrt hp', Real.sq_sqrt hq'] at this
  rw [Real.sqrt_mul hp q, Real.sqrt_mul hp' q']
  linarith

/-- for `z, w ≤ 0` the kinetic term is the squared difference -/
theorem sq_sub_eq_kin (z w : ℝ) (hz : z ≤ 0) (hw : w ≤ 0) : (z - w) ^ 2 = kin (z ^ 2) (w ^ 2) := by
  unfold kin
  have h : Real.sqrt (z ^ 2 * w ^ 2) = z * w := by
    rw [show z ^ 2 * w ^ 2 = (z * w) ^ 2 by ring]
    exact Real.sqrt_sq (by nlinarith)
  rw [h]; ring

/-- the action in the original coordinates -/
noncomputable def act (ε : ℝ) (n : ℕ) (z : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range (n + 1), (z (i + 1) - z i) ^ 2) / (2 * ε)
    + ε * ∑ i ∈ range n, ((z (i + 1)) ^ 2 - 1) ^ 2 / 8

/-- the action in the squared coordinates -/
noncomputable def actRho (ε : ℝ) (n : ℕ) (p : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range (n + 1), kin (p i) (p (i + 1))) / (2 * ε)
    + ε * ∑ i ∈ range n, (p (i + 1) - 1) ^ 2 / 8

theorem act_eq_actRho (ε : ℝ) (n : ℕ) (z : ℕ → ℝ) (hz : ∀ i, z i ≤ 0) :
    act ε n z = actRho ε n (fun i => (z i) ^ 2) := by
  have h : ∀ i ∈ range (n + 1), (z (i + 1) - z i) ^ 2 = kin ((z i) ^ 2) ((z (i + 1)) ^ 2) := by
    intro i _
    rw [← sq_sub_eq_kin _ _ (hz i) (hz (i + 1))]; ring
  simp only [act, actRho]
  rw [Finset.sum_congr rfl h]

/-- midpoint strong convexity of the action in `ρ` (modulus from the quartic potential) -/
theorem actRho_midpoint (ε : ℝ) (hε : 0 < ε) (n : ℕ) (p q : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    actRho ε n (fun i => (p i + q i) / 2)
      ≤ (actRho ε n p + actRho ε n q) / 2 - ε / 32 * ∑ i ∈ range n, (p (i + 1) - q (i + 1)) ^ 2 := by
  have hk : (∑ i ∈ range (n + 1), kin ((p i + q i) / 2) ((p (i + 1) + q (i + 1)) / 2))
      ≤ ((∑ i ∈ range (n + 1), kin (p i) (p (i + 1)))
          + (∑ i ∈ range (n + 1), kin (q i) (q (i + 1)))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    exact kin_midpoint _ _ _ _ (hp i) (hp (i + 1)) (hq i) (hq (i + 1))
  have h2 : 0 ≤ 1 / (2 * ε) := by positivity
  have hk' := mul_le_mul_of_nonneg_right hk h2
  have hv : (∑ i ∈ range n, ((p (i + 1) + q (i + 1)) / 2 - 1) ^ 2 / 8)
      = ((∑ i ∈ range n, (p (i + 1) - 1) ^ 2 / 8) + (∑ i ∈ range n, (q (i + 1) - 1) ^ 2 / 8)) / 2
        - 1 / 32 * ∑ i ∈ range n, (p (i + 1) - q (i + 1)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hv' : ε * (∑ i ∈ range n, ((p (i + 1) + q (i + 1)) / 2 - 1) ^ 2 / 8)
      = (ε * (∑ i ∈ range n, (p (i + 1) - 1) ^ 2 / 8) + ε * (∑ i ∈ range n, (q (i + 1) - 1) ^ 2 / 8)) / 2
        - ε / 32 * ∑ i ∈ range n, (p (i + 1) - q (i + 1)) ^ 2 := by
    rw [hv]; ring
  simp only [actRho]
  have e1 : (∑ i ∈ range (n + 1), kin ((p i + q i) / 2) ((p (i + 1) + q (i + 1)) / 2)) / (2 * ε)
      = (∑ i ∈ range (n + 1), kin ((p i + q i) / 2) ((p (i + 1) + q (i + 1)) / 2)) * (1 / (2 * ε)) := by
    ring
  have e2 : ((∑ i ∈ range (n + 1), kin (p i) (p (i + 1))) / (2 * ε)
        + (∑ i ∈ range (n + 1), kin (q i) (q (i + 1))) / (2 * ε)) / 2
      = (((∑ i ∈ range (n + 1), kin (p i) (p (i + 1)))
          + (∑ i ∈ range (n + 1), kin (q i) (q (i + 1)))) / 2) * (1 / (2 * ε)) := by
    ring
  linarith [hk', hv', e1, e2]

/-- uniqueness of the minimiser of the action over the box (proposition K', uniqueness part):
  boundary values `a, b ≤ 0` (any depth), interior sites in `[-c, 0]`. -/
def box (n : ℕ) (a b c : ℝ) : Set (ℕ → ℝ) :=
  {z | z 0 = a ∧ z (n + 1) = b ∧ ∀ i, z i ≤ 0 ∧ (1 ≤ i → i ≤ n → -c ≤ z i)}

theorem act_min_unique (ε : ℝ) (hε : 0 < ε) (n : ℕ) (a b c : ℝ) (ha : a ≤ 0) (hb : b ≤ 0)
    (z w : ℕ → ℝ) (hz : z ∈ box n a b c) (hw : w ∈ box n a b c)
    (hzmin : ∀ y ∈ box n a b c, act ε n z ≤ act ε n y)
    (hwmin : ∀ y ∈ box n a b c, act ε n w ≤ act ε n y) :
    ∀ i ∈ range n, z (i + 1) = w (i + 1) := by
  obtain ⟨hz0, hzn, hzi⟩ := hz
  obtain ⟨hw0, hwn, hwi⟩ := hw
  set m : ℕ → ℝ := fun i => -Real.sqrt (((z i) ^ 2 + (w i) ^ 2) / 2) with hm
  have hmsq : ∀ i, (m i) ^ 2 = ((z i) ^ 2 + (w i) ^ 2) / 2 := by
    intro i; simp only [hm, neg_sq]; exact Real.sq_sqrt (by positivity)
  have hmle : ∀ i, m i ≤ 0 := fun i => by simp only [hm]; exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hmbox : m ∈ box n a b c := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hm, hz0, hw0, show (a ^ 2 + a ^ 2) / 2 = a ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonpos ha, neg_neg]
    · simp only [hm, hzn, hwn, show (b ^ 2 + b ^ 2) / 2 = b ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonpos hb, neg_neg]
    · intro i
      refine ⟨hmle i, fun h1 h2 => ?_⟩
      obtain ⟨hz1, hz2⟩ := hzi i
      obtain ⟨hw1, hw2⟩ := hwi i
      have hzc := hz2 h1 h2
      have hwc := hw2 h1 h2
      have hc : 0 ≤ c := by linarith
      have hle : ((z i) ^ 2 + (w i) ^ 2) / 2 ≤ c ^ 2 := by nlinarith
      have : Real.sqrt (((z i) ^ 2 + (w i) ^ 2) / 2) ≤ c := by
        calc Real.sqrt (((z i) ^ 2 + (w i) ^ 2) / 2) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hle
          _ = c := Real.sqrt_sq hc
      simp only [hm]; linarith
  have hzle : ∀ i, z i ≤ 0 := fun i => (hzi i).1
  have hwle : ∀ i, w i ≤ 0 := fun i => (hwi i).1
  have hAm : act ε n m = actRho ε n (fun i => ((fun j => (z j) ^ 2) i + (fun j => (w j) ^ 2) i) / 2) := by
    rw [act_eq_actRho ε n m hmle]
    congr 1
    funext i
    exact hmsq i
  have hmid := actRho_midpoint ε hε n (fun j => (z j) ^ 2) (fun j => (w j) ^ 2)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _)
  rw [← hAm, ← act_eq_actRho ε n z hzle, ← act_eq_actRho ε n w hwle] at hmid
  have h1 := hzmin m hmbox
  have h2 := hzmin w ⟨hw0, hwn, hwi⟩
  have h3 := hwmin z ⟨hz0, hzn, hzi⟩
  have hD : ε / 32 * ∑ i ∈ range n, ((z (i + 1)) ^ 2 - (w (i + 1)) ^ 2) ^ 2 ≤ 0 := by linarith
  have hD' : ∑ i ∈ range n, ((z (i + 1)) ^ 2 - (w (i + 1)) ^ 2) ^ 2 ≤ 0 := by
    by_contra hcon0
    have hcon := not_le.mp hcon0
    have : 0 < ε / 32 * ∑ i ∈ range n, ((z (i + 1)) ^ 2 - (w (i + 1)) ^ 2) ^ 2 := by positivity
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp
    (le_antisymm hD' (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  intro i hi
  have h := hzero i hi
  have hsq : (z (i + 1)) ^ 2 = (w (i + 1)) ^ 2 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linarith
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rw [abs_of_nonpos (hzle (i + 1)), abs_of_nonpos (hwle (i + 1))] at habs
  linarith

end LatticeGauge.HiddenConvexity

#print axioms LatticeGauge.HiddenConvexity.cauchy_schwarz_two
#print axioms LatticeGauge.HiddenConvexity.geom_mean_midpoint
#print axioms LatticeGauge.HiddenConvexity.kin_midpoint
#print axioms LatticeGauge.HiddenConvexity.sq_sub_eq_kin
#print axioms LatticeGauge.HiddenConvexity.act_eq_actRho
#print axioms LatticeGauge.HiddenConvexity.actRho_midpoint
#print axioms LatticeGauge.HiddenConvexity.act_min_unique
