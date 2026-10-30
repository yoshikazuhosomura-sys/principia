/-
Counting connected sets. Single file; checks with `import Mathlib` only.

  Point type P, adjacency adj (symmetry is not used), each point has at most d neighbours (counted inside any finite set).
  §1 Paths and connectedness (copy of `Conn` and `IsConnectedSet` of PolymerComponents)
  §2 Rooted search: from the root set R every point of C is reached by a path inside C (Rooted).
     Removing one root r, a subset Q of the neighbours of r outside R becomes new roots (rooted_erase)
  §3 The generating function W(U, R) = Σ_{C ⊆ U, Rooted R C} x^{|C|}: the one-step inequality (W_step) and,
     under x(1+t)^d ≤ t, W(U, R) ≤ t^{|R|} (W_le, induction on |U|)
  §4 Extracting coefficients: the number of connected sets of size n containing a point p is ≤ e^n d^{n−1} (= e·(ed)^{n−1})
  §5 Passing to the statements of PolymerComponents: BoundedDegree adj Δ (1 ≤ Δ) ⇒ ConnectedSetCount adj Δ.
     If there is at least one adjacent pair, CountingFromDegree adj holds. With no adjacent pair and Δ = 0, ConnectedSetCount is false
-/
import Mathlib

namespace ConnectedSetCounting

open Finset

set_option linter.unusedSectionVars false

variable {P : Type*} [DecidableEq P]

open Classical

/-! ## 1. Paths and connectedness (copy) -/

def Conn (adj : P → P → Prop) (X : Finset P) : P → P → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ adj a b)

def IsConnectedSet (adj : P → P → Prop) (C : Finset P) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, Conn adj C a b

/-! ## 2. Rooted search -/

/-- The root set `R` is contained in `C`, and every point of `C` is reached from some point of `R` by a path inside `C`. -/
def Rooted (adj : P → P → Prop) (R C : Finset P) : Prop :=
  R ⊆ C ∧ ∀ c ∈ C, ∃ ρ ∈ R, Conn adj C ρ c

/-- Cutting a path inside `C` at `r`: if the end point is not `r`, then either it is reached inside `C ∖ {r}` from a start point other than `r`,
or it is reached inside `C ∖ {r}` from a neighbour `q ∈ C` of `r`. -/
theorem conn_erase (adj : P → P → Prop) (C : Finset P) (r a : P) {c : P}
    (h : Conn adj C a c) (hc : c ≠ r) :
    (a ≠ r ∧ Conn adj (C.erase r) a c) ∨
      (∃ q ∈ C, q ≠ r ∧ adj r q ∧ Conn adj (C.erase r) q c) := by
  induction h with
  | refl => exact Or.inl ⟨hc, Relation.ReflTransGen.refl⟩
  | @tail b e _ hbe ih =>
    by_cases hb : b = r
    · refine Or.inr ⟨e, hbe.2.1, hc, ?_, Relation.ReflTransGen.refl⟩
      rw [← hb]; exact hbe.2.2
    · have step : e ∈ C.erase r ∧ True := ⟨mem_erase.mpr ⟨hc, hbe.2.1⟩, trivial⟩
      have hstep : (fun x y => x ∈ C.erase r ∧ y ∈ C.erase r ∧ adj x y) b e :=
        ⟨mem_erase.mpr ⟨hb, hbe.1⟩, step.1, hbe.2.2⟩
      rcases ih hb with ⟨ha, hp⟩ | ⟨q, hq, hqr, hrq, hp⟩
      · exact Or.inl ⟨ha, hp.tail hstep⟩
      · exact Or.inr ⟨q, hq, hqr, hrq, hp.tail hstep⟩

/-- One step of removing the root `r`: adding `Q = C ∩ N` (`N` the neighbours of `r` in `U ∖ R`) to the roots,
`C ∖ {r}` is rooted at `(R ∖ {r}) ∪ Q`. -/
theorem rooted_erase (adj : P → P → Prop) (U R C : Finset P) (r : P) (hr : r ∈ R)
    (hCU : C ⊆ U) (hC : Rooted adj R C) :
    Rooted adj (R.erase r ∪ C ∩ (U \ R).filter (adj r)) (C.erase r) := by
  classical
  obtain ⟨hRC, hreach⟩ := hC
  constructor
  · intro y hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨hyr, hyR⟩ := mem_erase.mp hy
      exact mem_erase.mpr ⟨hyr, hRC hyR⟩
    · obtain ⟨hyC, hyN⟩ := mem_inter.mp hy
      have hyR : y ∉ R := (mem_sdiff.mp (mem_filter.mp hyN).1).2
      exact mem_erase.mpr ⟨fun h => hyR (h ▸ hr), hyC⟩
  · intro c hc
    obtain ⟨hcr, hcC⟩ := mem_erase.mp hc
    obtain ⟨ρ, hρ, hp⟩ := hreach c hcC
    rcases conn_erase adj C r ρ hp hcr with ⟨hρr, hp'⟩ | ⟨q, hqC, hqr, hrq, hp'⟩
    · exact ⟨ρ, mem_union_left _ (mem_erase.mpr ⟨hρr, hρ⟩), hp'⟩
    · by_cases hqR : q ∈ R
      · exact ⟨q, mem_union_left _ (mem_erase.mpr ⟨hqr, hqR⟩), hp'⟩
      · refine ⟨q, mem_union_right _ (mem_inter.mpr ⟨hqC, ?_⟩), hp'⟩
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hCU hqC, hqR⟩, hrq⟩

/-! ## 3. Generating function -/

open Classical in
/-- `W(U, R) = Σ_{C ⊆ U, Rooted R C} x^{|C|}`。 -/
noncomputable def W (adj : P → P → Prop) (x : ℝ) (U R : Finset P) : ℝ :=
  ∑ C ∈ U.powerset.filter (fun C => Rooted adj R C), x ^ C.card

/-- One-step inequality: split into cases by the subset `Q` of the neighbours of `r ∈ R` (inside `U ∖ R`). -/
theorem W_step (adj : P → P → Prop) (x : ℝ) (hx : 0 ≤ x) (U R : Finset P) (r : P) (hr : r ∈ R) :
    W adj x U R ≤ ∑ Q ∈ ((U \ R).filter (adj r)).powerset,
      x * W adj x (U.erase r) (R.erase r ∪ Q) := by
  classical
  set N := (U \ R).filter (adj r) with hN
  set S := U.powerset.filter (fun C => Rooted adj R C) with hS
  have hW : W adj x U R = ∑ C ∈ S, x ^ C.card := by
    unfold W; rfl
  rw [hW, ← sum_fiberwise_of_maps_to (s := S) (t := N.powerset) (g := fun C => C ∩ N)
    (fun C _ => mem_powerset.mpr inter_subset_right)]
  apply sum_le_sum
  intro Q _
  set A := S.filter (fun C => C ∩ N = Q) with hA
  have hmemA : ∀ C ∈ A, C ⊆ U ∧ Rooted adj R C ∧ C ∩ N = Q := by
    intro C hC
    obtain ⟨hCS, hCQ⟩ := mem_filter.mp hC
    obtain ⟨hCU, hCR⟩ := mem_filter.mp hCS
    exact ⟨mem_powerset.mp hCU, hCR, hCQ⟩
  have hrC : ∀ C ∈ A, r ∈ C := fun C hC => (hmemA C hC).2.1.1 hr
  have h1 : ∑ C ∈ A, x ^ C.card = x * ∑ C ∈ A, x ^ (C.erase r).card := by
    rw [mul_sum]
    refine sum_congr rfl fun C hC => ?_
    rw [← card_erase_add_one (hrC C hC), pow_succ, mul_comm]
  have hinj : Set.InjOn (fun C : Finset P => C.erase r) A := by
    intro C₁ h₁ C₂ h₂ he
    have := congrArg (insert r) he
    simp only at this
    rwa [insert_erase (hrC C₁ h₁), insert_erase (hrC C₂ h₂)] at this
  have h2 : ∑ C ∈ A, x ^ (C.erase r).card = ∑ C' ∈ A.image (fun C => C.erase r), x ^ C'.card :=
    (sum_image (f := fun C' : Finset P => x ^ C'.card) hinj).symm
  have hsub : A.image (fun C => C.erase r) ⊆
      (U.erase r).powerset.filter (fun C => Rooted adj (R.erase r ∪ Q) C) := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hC'
    obtain ⟨hCU, hCR, hCQ⟩ := hmemA C hC
    refine mem_filter.mpr ⟨mem_powerset.mpr (erase_subset_erase r hCU), ?_⟩
    have := rooted_erase adj U R C r hr hCU hCR
    rw [← hN, hCQ] at this
    exact this
  have h3 : ∑ C' ∈ A.image (fun C => C.erase r), x ^ C'.card ≤
      W adj x (U.erase r) (R.erase r ∪ Q) := by
    unfold W
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
  calc ∑ C ∈ A, x ^ C.card = x * ∑ C ∈ A, x ^ (C.erase r).card := h1
    _ = x * ∑ C' ∈ A.image (fun C => C.erase r), x ^ C'.card := by rw [h2]
    _ ≤ x * W adj x (U.erase r) (R.erase r ∪ Q) := mul_le_mul_of_nonneg_left h3 hx

/-- Bound on the generating function: if each point has at most d neighbours and `x (1+t)^d ≤ t`, then `W(U, R) ≤ t^{|R|}`. -/
theorem W_le (adj : P → P → Prop) (d : ℕ)
    (hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d)
    (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (hfix : x * (1 + t) ^ d ≤ t) :
    ∀ U R : Finset P, W adj x U R ≤ t ^ R.card := by
  classical
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro R
  rcases R.eq_empty_or_nonempty with hR | ⟨r, hr⟩
  · subst hR
    unfold W
    have hsub : U.powerset.filter (fun C => Rooted adj ∅ C) ⊆ {∅} := by
      intro C hC
      obtain ⟨_, _, hreach⟩ := mem_filter.mp hC
      rw [mem_singleton, eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨ρ, hρ, _⟩ := hreach c hc
      exact absurd hρ (notMem_empty ρ)
    calc ∑ C ∈ U.powerset.filter (fun C => Rooted adj ∅ C), x ^ C.card
        ≤ ∑ C ∈ ({∅} : Finset (Finset P)), x ^ C.card :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
      _ = t ^ (∅ : Finset P).card := by simp
  · by_cases hrU : r ∈ U
    · set N := (U \ R).filter (adj r) with hN
      have hNR : ∀ Q ∈ N.powerset, Disjoint (R.erase r) Q := by
        intro Q hQ
        rw [disjoint_left]
        intro y hy hyQ
        have := (mem_sdiff.mp (mem_filter.mp (mem_powerset.mp hQ hyQ)).1).2
        exact this (mem_of_mem_erase hy)
      have hcardR : (R.erase r).card + 1 = R.card := card_erase_add_one hr
      have hNd : N.card ≤ d :=
        le_trans (card_le_card (filter_subset_filter _ sdiff_subset)) (hdeg U r)
      calc W adj x U R
          ≤ ∑ Q ∈ N.powerset, x * W adj x (U.erase r) (R.erase r ∪ Q) := W_step adj x hx U R r hr
        _ ≤ ∑ Q ∈ N.powerset, x * (t ^ (R.erase r).card * t ^ Q.card) := by
            apply sum_le_sum
            intro Q hQ
            apply mul_le_mul_of_nonneg_left _ hx
            have := ih (U.erase r) (erase_ssubset hrU) (R.erase r ∪ Q)
            rwa [card_union_of_disjoint (hNR Q hQ), pow_add] at this
        _ = x * t ^ (R.erase r).card * ∑ Q ∈ N.powerset, t ^ Q.card := by
            rw [mul_assoc, mul_sum, mul_sum]
        _ = x * t ^ (R.erase r).card * (1 + t) ^ N.card := by
            congr 1
            have := sum_pow_mul_eq_add_pow t 1 N
            simp only [one_pow, mul_one] at this
            rw [this, add_comm]
        _ ≤ x * t ^ (R.erase r).card * (1 + t) ^ d := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_right₀ (by linarith) hNd
        _ = (x * (1 + t) ^ d) * t ^ (R.erase r).card := by ring
        _ ≤ t * t ^ (R.erase r).card := mul_le_mul_of_nonneg_right hfix (by positivity)
        _ = t ^ R.card := by rw [← hcardR, pow_succ, mul_comm]
    · have hempty : U.powerset.filter (fun C => Rooted adj R C) = ∅ := by
        rw [filter_eq_empty_iff]
        intro C hC hCR
        exact hrU (mem_powerset.mp hC (hCR.1 hr))
      unfold W
      rw [hempty, sum_empty]
      positivity

/-! ## 4. Extracting coefficients -/

/-- A connected set is rooted at any one of its points. -/
theorem rooted_of_connected (adj : P → P → Prop) {C : Finset P} {p : P} (hp : p ∈ C)
    (hC : IsConnectedSet adj C) : Rooted adj {p} C :=
  ⟨singleton_subset_iff.mpr hp, fun c hc => ⟨p, mem_singleton_self p, hC p hp c hc⟩⟩

/-- The generating function of the connected sets containing the point `p` is ≤ t (when `x(1+t)^d ≤ t`). -/
theorem connected_gf_le (adj : P → P → Prop) (d : ℕ)
    (hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d)
    (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (hfix : x * (1 + t) ^ d ≤ t) (U : Finset P) (p : P) (n : ℕ) :
    by classical exact
      ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ) * x ^ n
        ≤ t := by
  classical
  set A := U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C) with hA
  have hsub : A ⊆ U.powerset.filter (fun C => Rooted adj {p} C) := by
    intro C hC
    obtain ⟨hCU, hpC, _, hconn⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨hCU, rooted_of_connected adj hpC hconn⟩
  have hsum : (A.card : ℝ) * x ^ n = ∑ C ∈ A, x ^ C.card := by
    rw [sum_congr rfl (fun C hC => by rw [(mem_filter.mp hC).2.2.1]), sum_const, nsmul_eq_mul]
  have hW := W_le adj d hdeg x t hx ht hfix U {p}
  rw [card_singleton, pow_one] at hW
  calc (A.card : ℝ) * x ^ n = ∑ C ∈ A, x ^ C.card := hsum
    _ ≤ ∑ C ∈ U.powerset.filter (fun C => Rooted adj {p} C), x ^ C.card :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
    _ = W adj x U {p} := by unfold W; rfl
    _ ≤ t := hW

/-- `(1 + 1/d)^{d n} ≤ e^n`。 -/
theorem one_add_inv_pow_le (d n : ℕ) (hd : 1 ≤ d) :
    (1 + 1 / (d : ℝ)) ^ (d * n) ≤ Real.exp 1 ^ n := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : 1 + 1 / (d : ℝ) ≤ Real.exp (1 / d) := by
    have := Real.add_one_le_exp (1 / (d : ℝ)); linarith
  calc (1 + 1 / (d : ℝ)) ^ (d * n) ≤ Real.exp (1 / d) ^ (d * n) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = Real.exp 1 ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp

/-- **Counting**: if each point has at most d neighbours (1 ≤ d), the number of connected sets of size `n ≥ 1` containing the point `p`
is ≤ e^n d^{n−1}. -/
theorem connected_count_le (adj : P → P → Prop) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d)
    (U : Finset P) (p : P) (n : ℕ) (hn : 1 ≤ n) :
    by classical exact
      ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ)
        ≤ Real.exp 1 ^ n * (d : ℝ) ^ (n - 1) := by
  classical
  set c : ℝ := ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ)
    with hc
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set t : ℝ := 1 / d with htdef
  have ht : 0 < t := by positivity
  set B : ℝ := (1 + t) ^ d with hB
  have hB0 : 0 < B := by positivity
  set x : ℝ := t / B with hxdef
  have hx : 0 < x := by positivity
  have hfix : x * (1 + t) ^ d ≤ t := by rw [← hB, hxdef]; field_simp; rfl
  have key := connected_gf_le adj d hdeg x t hx.le ht.le hfix U p n
  rw [← hc] at key
  -- c * (t/B)^n ≤ t  ⇒  c ≤ t^{1-n} B^n
  have hxn : x ^ n = t ^ n / B ^ n := by rw [hxdef, div_pow]
  rw [hxn] at key
  have hBn : 0 < B ^ n := by positivity
  have htn1 : 0 < t ^ (n - 1) := by positivity
  have htn : t ^ n = t * t ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : c * t ^ (n - 1) ≤ B ^ n := by
    have h3 : c * (t ^ n / B ^ n) * B ^ n ≤ t * B ^ n := mul_le_mul_of_nonneg_right key hBn.le
    rw [mul_assoc, div_mul_cancel₀ _ hBn.ne', htn] at h3
    have h4 : t * (c * t ^ (n - 1)) ≤ t * B ^ n := by linarith
    exact le_of_mul_le_mul_left h4 ht
  have h5 : c ≤ B ^ n * (d : ℝ) ^ (n - 1) := by
    have htd : t ^ (n - 1) * (d : ℝ) ^ (n - 1) = 1 := by
      rw [← mul_pow, htdef, one_div, inv_mul_cancel₀ hd'.ne', one_pow]
    calc c = c * (t ^ (n - 1) * (d : ℝ) ^ (n - 1)) := by rw [htd, mul_one]
      _ = (c * t ^ (n - 1)) * (d : ℝ) ^ (n - 1) := by ring
      _ ≤ B ^ n * (d : ℝ) ^ (n - 1) := mul_le_mul_of_nonneg_right h2 (by positivity)
  have h6 : B ^ n ≤ Real.exp 1 ^ n := by
    rw [hB, ← pow_mul, htdef]
    exact one_add_inv_pow_le d n hd
  calc c ≤ B ^ n * (d : ℝ) ^ (n - 1) := h5
    _ ≤ Real.exp 1 ^ n * (d : ℝ) ^ (n - 1) := mul_le_mul_of_nonneg_right h6 (by positivity)

/-! ## 5. Passing to the statements of PolymerComponents (copies of the statements) -/

def BoundedDegree (adj : P → P → Prop) (Δ : ℝ) : Prop :=
  ∀ (U : Finset P) (p : P), by classical exact ((U.filter (adj p)).card : ℝ) ≤ Δ

def ConnectedSetCount (adj : P → P → Prop) (Δ : ℝ) : Prop :=
  ∀ (U : Finset P) (p : P) (n : ℕ),
    by classical exact
      ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ) ≤
        (Real.exp 1 * Δ) ^ n

def CountingFromDegree (adj : P → P → Prop) : Prop :=
  ∀ Δ : ℝ, 0 ≤ Δ → BoundedDegree adj Δ → ConnectedSetCount adj Δ

/-- Counting with a real Δ (1 ≤ Δ): ≤ e^n Δ^{n−1}. -/
theorem connected_count_real (adj : P → P → Prop) (Δ : ℝ) (hΔ : 1 ≤ Δ) (hb : BoundedDegree adj Δ)
    (U : Finset P) (p : P) (n : ℕ) (hn : 1 ≤ n) :
    by classical exact
      ((U.powerset.filter (fun C => p ∈ C ∧ C.card = n ∧ IsConnectedSet adj C)).card : ℝ)
        ≤ Real.exp 1 ^ n * Δ ^ (n - 1) := by
  classical
  set d := ⌊Δ⌋₊ with hd
  have hd1 : 1 ≤ d := Nat.le_floor (by exact_mod_cast hΔ)
  have hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d := by
    intro U p
    apply Nat.le_floor
    have := hb U p
    convert this
  have hdΔ : (d : ℝ) ≤ Δ := Nat.floor_le (by linarith)
  calc _ ≤ Real.exp 1 ^ n * (d : ℝ) ^ (n - 1) := connected_count_le adj d hd1 hdeg U p n hn
    _ ≤ Real.exp 1 ^ n * Δ ^ (n - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdΔ _) (by positivity)

/-- `ConnectedSetCount` of PolymerComponents (in the form (eΔ)^n) is a theorem for 1 ≤ Δ. -/
theorem connectedSetCount_of_bounded (adj : P → P → Prop) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (hb : BoundedDegree adj Δ) : ConnectedSetCount adj Δ := by
  classical
  intro U p n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : U.powerset.filter (fun C => p ∈ C ∧ C.card = 0 ∧ IsConnectedSet adj C) = ∅ := by
      rw [filter_eq_empty_iff]
      rintro C _ ⟨hp, h0, _⟩
      rw [card_eq_zero] at h0
      subst h0
      exact notMem_empty p hp
    rw [this]; simp
  · have h := connected_count_real adj Δ hΔ hb U p n hn
    refine le_trans h ?_
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hpow : Δ ^ (n - 1) ≤ Δ ^ n := pow_le_pow_right₀ hΔ (Nat.sub_le n 1)
    calc Real.exp 1 ^ n * Δ ^ (n - 1) ≤ Real.exp 1 ^ n * Δ ^ n :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (Real.exp 1 * Δ) ^ n := (mul_pow _ _ _).symm

/-- If there is at least one adjacent pair, `CountingFromDegree adj` is a theorem (for Δ < 1 the degree hypothesis cannot hold). -/
theorem countingFromDegree_of_exists (adj : P → P → Prop) (h : ∃ a b, adj a b) :
    CountingFromDegree adj := by
  classical
  intro Δ _ hb
  obtain ⟨a, b, hab⟩ := h
  have hΔ : 1 ≤ Δ := by
    have := hb {b} a
    have h1 : (({b} : Finset P).filter (adj a)).card = 1 := by
      rw [filter_singleton, if_pos hab, card_singleton]
    rw [h1] at this
    simpa using this
  exact connectedSetCount_of_bounded adj Δ hΔ hb

/-- A remark on the scope of the statement: with no adjacent pair the degree bound Δ = 0 holds, but (e·0)^1 = 0 < 1, so `ConnectedSetCount` is false. -/
theorem connectedSetCount_fails_at_zero (p : P) :
    BoundedDegree (fun _ _ : P => False) 0 ∧ ¬ ConnectedSetCount (fun _ _ : P => False) 0 := by
  classical
  constructor
  · intro U q
    simp
  · intro h
    have h1 := h {p} p 1
    have hmem : ({p} : Finset P) ∈ ({p} : Finset P).powerset.filter
        (fun C => p ∈ C ∧ C.card = 1 ∧ IsConnectedSet (fun _ _ : P => False) C) := by
      refine mem_filter.mpr ⟨mem_powerset_self _, mem_singleton_self p, card_singleton p, ?_⟩
      intro a ha b hb
      rw [mem_singleton] at ha hb
      subst ha; subst hb
      exact Relation.ReflTransGen.refl
    have hpos : (1 : ℝ) ≤ (({p} : Finset P).powerset.filter
        (fun C => p ∈ C ∧ C.card = 1 ∧ IsConnectedSet (fun _ _ : P => False) C)).card := by
      exact_mod_cast card_pos.mpr ⟨_, hmem⟩
    have : (({p} : Finset P).powerset.filter
        (fun C => p ∈ C ∧ C.card = 1 ∧ IsConnectedSet (fun _ _ : P => False) C)).card ≤ (0 : ℝ) := by
      convert h1 using 1
      simp
    linarith

#print axioms conn_erase
#print axioms rooted_erase
#print axioms W_step
#print axioms W_le
#print axioms rooted_of_connected
#print axioms connected_gf_le
#print axioms one_add_inv_pow_le
#print axioms connected_count_le
#print axioms connected_count_real
#print axioms connectedSetCount_of_bounded
#print axioms countingFromDegree_of_exists
#print axioms connectedSetCount_fails_at_zero

/-! ## 6. The sum per point, directly (without summing over n) -/

/-- The generating function of the connected sets containing the point `p` (of any size) is ≤ t. -/
theorem point_gf_le (adj : P → P → Prop) (d : ℕ)
    (hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d)
    (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) (hfix : x * (1 + t) ^ d ≤ t) (U : Finset P) (p : P) :
    ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C), x ^ C.card ≤ t := by
  have hsub : U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C) ⊆
      U.powerset.filter (fun C => Rooted adj {p} C) := by
    intro C hC
    obtain ⟨hCU, hpC, hconn⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨hCU, rooted_of_connected adj hpC hconn⟩
  have hW := W_le adj d hdeg x t hx ht hfix U {p}
  rw [card_singleton, pow_one] at hW
  calc _ ≤ ∑ C ∈ U.powerset.filter (fun C => Rooted adj {p} C), x ^ C.card :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx _)
    _ = W adj x U {p} := by unfold W; rfl
    _ ≤ t := hW

/-- **KP sum per point**: if the activity satisfies `|z(C)| ≤ ε^{|C|}` and `e³ d ε ≤ 1` (1 ≤ d), then
`Σ_{C ∋ p connected} |z(C)| e^{2|C|} ≤ 1/d ≤ 1` (the form of the input of KPToDobrushin). -/
theorem point_kp_sum_le (adj : P → P → Prop) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ (U : Finset P) (p : P), (U.filter (adj p)).card ≤ d)
    (z : Finset P → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hz : ∀ C, |z C| ≤ ε ^ C.card)
    (hsmall : Real.exp 1 ^ 3 * d * ε ≤ 1) (U : Finset P) (p : P) :
    ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C),
      |z C| * Real.exp 2 ^ C.card ≤ 1 / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set t : ℝ := 1 / d with htdef
  set x : ℝ := ε * Real.exp 2 with hxdef
  have hx : 0 ≤ x := by positivity
  have hfix : x * (1 + t) ^ d ≤ t := by
    have h1 : (1 + t) ^ d ≤ Real.exp 1 := by
      have := one_add_inv_pow_le d 1 hd
      simpa [htdef] using this
    have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : x * Real.exp 1 ≤ t := by
      rw [hxdef, htdef, he2, le_div_iff₀ hd']
      nlinarith
    calc x * (1 + t) ^ d ≤ x * Real.exp 1 := mul_le_mul_of_nonneg_left h1 hx
      _ ≤ t := h2
  calc _ ≤ ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C), x ^ C.card := by
        apply sum_le_sum
        intro C _
        rw [hxdef, mul_pow]
        exact mul_le_mul_of_nonneg_right (hz C) (by positivity)
    _ ≤ t := point_gf_le adj d hdeg x t hx (by positivity) hfix U p

#print axioms point_gf_le
#print axioms point_kp_sum_le

end ConnectedSetCounting
