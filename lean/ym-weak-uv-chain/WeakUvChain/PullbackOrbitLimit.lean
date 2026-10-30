import Mathlib

/-!
# The limit of finite orbits holds without subsequences (pull-back form)

Suppose the step maps `T k : X → X` (from scale `k+1` to scale `k`, one step from ultraviolet to infrared)
map a common closed ball `B` into itself and are `lam`-Lipschitz on `B` (`lam < 1`).
On lattice `n`, put the bare value `p n ∈ B` at scale `n` and transport it to scale `0` by `T (n-1), …, T 0`:
`a n = comp T n (p n)`.

* `orbit_cauchy`: `a` is Cauchy (`dist (a n) (a (n+1)) ≤ D lam^n`).
* `orbit_tendsto`: if complete, the whole sequence converges (no subsequence).
* `orbit_rate`: rate of convergence `D lam^n / (1 - lam)`.
* `limit_independent`: the limit does not depend on the choice of bare values `p`.
* `pushforward_tendsto`: a scale-`0` quantity that is a continuous function of the coordinates also converges along the whole sequence.
* `compact_unique_cluster`: in a compact space, a unique cluster point implies convergence of the whole sequence.
-/

open Filter Topology

namespace PullbackOrbit

variable {X : Type*} [MetricSpace X]

/-- `comp T n = T 0 ∘ T 1 ∘ ⋯ ∘ T (n-1)`. -/
def comp (T : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | n + 1 => fun x => comp T n (T n x)

variable (T : ℕ → X → X) (B : Set X) (lam D : ℝ)

omit [MetricSpace X] in
theorem comp_mem (hB : ∀ k, ∀ x ∈ B, T k x ∈ B) :
    ∀ n, ∀ x ∈ B, comp T n x ∈ B := by
  intro n
  induction n with
  | zero => intro x hx; simpa [comp] using hx
  | succ n ih => intro x hx; exact ih _ (hB n x hx)

theorem comp_dist (hlam : 0 ≤ lam) (hB : ∀ k, ∀ x ∈ B, T k x ∈ B)
    (hL : ∀ k, ∀ x ∈ B, ∀ y ∈ B, dist (T k x) (T k y) ≤ lam * dist x y) :
    ∀ n, ∀ x ∈ B, ∀ y ∈ B, dist (comp T n x) (comp T n y) ≤ lam ^ n * dist x y := by
  intro n
  induction n with
  | zero => intro x _ y _; simp [comp]
  | succ n ih =>
    intro x hx y hy
    show dist (comp T n (T n x)) (comp T n (T n y)) ≤ lam ^ (n + 1) * dist x y
    calc dist (comp T n (T n x)) (comp T n (T n y))
        ≤ lam ^ n * dist (T n x) (T n y) := ih _ (hB n x hx) _ (hB n y hy)
      _ ≤ lam ^ n * (lam * dist x y) :=
          mul_le_mul_of_nonneg_left (hL n x hx y hy) (pow_nonneg hlam n)
      _ = lam ^ (n + 1) * dist x y := by ring

section
variable (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hB : ∀ k, ∀ x ∈ B, T k x ∈ B)
  (hL : ∀ k, ∀ x ∈ B, ∀ y ∈ B, dist (T k x) (T k y) ≤ lam * dist x y)
  (hD : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ D)

include hlam hB hL hD in
theorem step_bound (p : ℕ → X) (hp : ∀ n, p n ∈ B) (n : ℕ) :
    dist (comp T n (p n)) (comp T (n + 1) (p (n + 1))) ≤ D * lam ^ n := by
  show dist (comp T n (p n)) (comp T n (T n (p (n + 1)))) ≤ D * lam ^ n
  calc dist (comp T n (p n)) (comp T n (T n (p (n + 1))))
      ≤ lam ^ n * dist (p n) (T n (p (n + 1))) :=
        comp_dist T B lam hlam hB hL n _ (hp n) _ (hB n _ (hp (n + 1)))
    _ ≤ lam ^ n * D :=
        mul_le_mul_of_nonneg_left (hD _ (hp n) _ (hB n _ (hp (n + 1)))) (pow_nonneg hlam n)
    _ = D * lam ^ n := by ring

include hlam hlam1 hB hL hD in
theorem orbit_cauchy (p : ℕ → X) (hp : ∀ n, p n ∈ B) :
    CauchySeq (fun n => comp T n (p n)) :=
  cauchySeq_of_le_geometric lam D hlam1 (step_bound T B lam D hlam hB hL hD p hp)

include hlam hlam1 hB hL hD in
theorem orbit_tendsto [CompleteSpace X] (p : ℕ → X) (hp : ∀ n, p n ∈ B) :
    ∃ xs : X, Tendsto (fun n => comp T n (p n)) atTop (𝓝 xs) :=
  cauchySeq_tendsto_of_complete (orbit_cauchy T B lam D hlam hlam1 hB hL hD p hp)

include hlam hlam1 hB hL hD in
theorem orbit_rate (p : ℕ → X) (hp : ∀ n, p n ∈ B) (xs : X)
    (hx : Tendsto (fun n => comp T n (p n)) atTop (𝓝 xs)) (n : ℕ) :
    dist (comp T n (p n)) xs ≤ D * lam ^ n / (1 - lam) :=
  dist_le_of_le_geometric_of_tendsto lam D hlam1
    (step_bound T B lam D hlam hB hL hD p hp) hx n

include hlam hlam1 hB hL hD in
theorem limit_independent (p q : ℕ → X) (hp : ∀ n, p n ∈ B) (hq : ∀ n, q n ∈ B)
    (xs ys : X) (hx : Tendsto (fun n => comp T n (p n)) atTop (𝓝 xs))
    (hy : Tendsto (fun n => comp T n (q n)) atTop (𝓝 ys)) : xs = ys := by
  have h1 : Tendsto (fun n => dist (comp T n (p n)) (comp T n (q n))) atTop
      (𝓝 (dist xs ys)) := hx.dist hy
  have hg : Tendsto (fun n => lam ^ n * D) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam hlam1).mul_const D
  have h0 : Tendsto (fun n => dist (comp T n (p n)) (comp T n (q n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hg
    calc dist (comp T n (p n)) (comp T n (q n))
        ≤ lam ^ n * dist (p n) (q n) := comp_dist T B lam hlam hB hL n _ (hp n) _ (hq n)
      _ ≤ lam ^ n * D := mul_le_mul_of_nonneg_left (hD _ (hp n) _ (hq n)) (pow_nonneg hlam n)
  exact dist_eq_zero.mp (tendsto_nhds_unique h1 h0)
end

/-- A scale-`0` quantity (e.g. the distribution of a coarse observable) that is a continuous function `Ψ` of the coordinates converges along the whole sequence. -/
theorem pushforward_tendsto {Y : Type*} [TopologicalSpace Y] (Ψ : X → Y) (hΨ : Continuous Ψ)
    (a : ℕ → X) (xs : X) (ha : Tendsto a atTop (𝓝 xs)) :
    Tendsto (fun n => Ψ (a n)) atTop (𝓝 (Ψ xs)) :=
  (hΨ.tendsto xs).comp ha

/-- In a compact space, if there is only one cluster point, the whole sequence converges. -/
theorem compact_unique_cluster {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (f : ℕ → Y) (y : Y) (h : ∀ x, MapClusterPt x atTop f → x = y) :
    Tendsto f atTop (𝓝 y) :=
  tendsto_nhds_of_unique_mapClusterPt h

end PullbackOrbit

#print axioms PullbackOrbit.orbit_tendsto
#print axioms PullbackOrbit.orbit_rate
#print axioms PullbackOrbit.limit_independent
#print axioms PullbackOrbit.pushforward_tendsto
#print axioms PullbackOrbit.compact_unique_cluster
