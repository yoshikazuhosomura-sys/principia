/-
Two-colour KP sum on the ℤ⁴ lattice with plaquette adjacency extended to "sharing a link or opposite in a cube" (Δ = 24).
Single file; checks with `import Mathlib` only. §1–§11 are a copy of LatticeTwoColorKP (without the decide counts for Δ = 20).

  §12 Cube-opposite plaquettes cubeOpp0, adjacency faceAdj24, two-colour neighbourhoods (translates of origin sets) with sizes 24, 44, 66, 122 (decide +kernel),
      hnb, hdeg, the numerical condition for Δ = 24 lattice24_fix (thin plaquette ≤ 2.1·10⁻³, defect ≤ 1.5·10⁻¹¹, θ = (1/23, 10⁻⁴)),
      lattice_kp_site24 (only hypotheses: hz and the label sum), threshold check face24_fails (for thin plaquettes ≥ 2.5·10⁻³ it fails for every slope).
-/
import Mathlib

namespace Lattice24KP




open Finset

set_option linter.unusedSectionVars false

variable {P : Type*} [DecidableEq P]

open Classical

/-! ## 1. Paths, connectedness, rooted sets (copy) -/

def Conn (adj : P → P → Prop) (X : Finset P) : P → P → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ adj a b)

def IsConnectedSet (adj : P → P → Prop) (C : Finset P) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, Conn adj C a b

def Rooted (adj : P → P → Prop) (R C : Finset P) : Prop :=
  R ⊆ C ∧ ∀ c ∈ C, ∃ ρ ∈ R, Conn adj C ρ c

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
    · have hstep : (fun x y => x ∈ C.erase r ∧ y ∈ C.erase r ∧ adj x y) b e :=
        ⟨mem_erase.mpr ⟨hb, hbe.1⟩, mem_erase.mpr ⟨hc, hbe.2.1⟩, hbe.2.2⟩
      rcases ih hb with ⟨ha, hp⟩ | ⟨q, hq, hqr, hrq, hp⟩
      · exact Or.inl ⟨ha, hp.tail hstep⟩
      · exact Or.inr ⟨q, hq, hqr, hrq, hp.tail hstep⟩

theorem rooted_erase (adj : P → P → Prop) (U R C : Finset P) (r : P) (hr : r ∈ R)
    (hCU : C ⊆ U) (hC : Rooted adj R C) :
    Rooted adj (R.erase r ∪ C ∩ (U \ R).filter (adj r)) (C.erase r) := by
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

theorem rooted_of_connected (adj : P → P → Prop) {C : Finset P} {p : P} (hp : p ∈ C)
    (hC : IsConnectedSet adj C) : Rooted adj {p} C :=
  ⟨singleton_subset_iff.mpr hp, fun c hc => ⟨p, mem_singleton_self p, hC p hp c hc⟩⟩

/-! ## 2. Generating function with point weights -/

/-- `Wg(U, R) = Σ_{C ⊆ U, Rooted R C} Π_{c∈C} x(c)`. -/
noncomputable def Wg (adj : P → P → Prop) (x : P → ℝ) (U R : Finset P) : ℝ :=
  ∑ C ∈ U.powerset.filter (fun C => Rooted adj R C), ∏ c ∈ C, x c

/-- One-step inequality (point weights). -/
theorem Wg_step (adj : P → P → Prop) (x : P → ℝ) (hx : ∀ p, 0 ≤ x p) (U R : Finset P) (r : P)
    (hr : r ∈ R) :
    Wg adj x U R ≤ ∑ Q ∈ ((U \ R).filter (adj r)).powerset,
      x r * Wg adj x (U.erase r) (R.erase r ∪ Q) := by
  set N := (U \ R).filter (adj r) with hN
  set S := U.powerset.filter (fun C => Rooted adj R C) with hS
  have hW : Wg adj x U R = ∑ C ∈ S, ∏ c ∈ C, x c := by unfold Wg; rfl
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
  have h1 : ∑ C ∈ A, ∏ c ∈ C, x c = x r * ∑ C ∈ A, ∏ c ∈ C.erase r, x c := by
    rw [mul_sum]
    exact sum_congr rfl fun C hC => (mul_prod_erase C x (hrC C hC)).symm
  have hinj : Set.InjOn (fun C : Finset P => C.erase r) A := by
    intro C₁ h₁ C₂ h₂ he
    have := congrArg (insert r) he
    simp only at this
    rwa [insert_erase (hrC C₁ h₁), insert_erase (hrC C₂ h₂)] at this
  have h2 : ∑ C ∈ A, ∏ c ∈ C.erase r, x c =
      ∑ C' ∈ A.image (fun C => C.erase r), ∏ c ∈ C', x c :=
    (sum_image (f := fun C' : Finset P => ∏ c ∈ C', x c) hinj).symm
  have hsub : A.image (fun C => C.erase r) ⊆
      (U.erase r).powerset.filter (fun C => Rooted adj (R.erase r ∪ Q) C) := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hC'
    obtain ⟨hCU, hCR, hCQ⟩ := hmemA C hC
    refine mem_filter.mpr ⟨mem_powerset.mpr (erase_subset_erase r hCU), ?_⟩
    have := rooted_erase adj U R C r hr hCU hCR
    rw [← hN, hCQ] at this
    exact this
  have h3 : ∑ C' ∈ A.image (fun C => C.erase r), ∏ c ∈ C', x c ≤
      Wg adj x (U.erase r) (R.erase r ∪ Q) := by
    unfold Wg
    exact sum_le_sum_of_subset_of_nonneg hsub
      (fun C _ _ => prod_nonneg fun c _ => hx c)
  calc ∑ C ∈ A, ∏ c ∈ C, x c = x r * ∑ C ∈ A, ∏ c ∈ C.erase r, x c := h1
    _ = x r * ∑ C' ∈ A.image (fun C => C.erase r), ∏ c ∈ C', x c := by rw [h2]
    _ ≤ x r * Wg adj x (U.erase r) (R.erase r ∪ Q) := mul_le_mul_of_nonneg_left h3 (hx r)

/-- A product of factors ≥ 1 is monotone in the index set. -/
theorem prod_mono_of_one_le (f : P → ℝ) (hf : ∀ p, 1 ≤ f p) {s t : Finset P} (h : s ⊆ t) :
    ∏ p ∈ s, f p ≤ ∏ p ∈ t, f p := by
  rw [← prod_sdiff h]
  have h0 : ∀ p, 0 ≤ f p := fun p => le_trans zero_le_one (hf p)
  have h1 : (1 : ℝ) ≤ ∏ p ∈ t \ s, f p := by
    calc (1 : ℝ) = ∏ _p ∈ t \ s, (1 : ℝ) := by simp
      _ ≤ ∏ p ∈ t \ s, f p := prod_le_prod (fun _ _ => zero_le_one) (fun p _ => hf p)
  have h2 : 0 ≤ ∏ p ∈ s, f p := prod_nonneg fun p _ => h0 p
  nlinarith

/-- **Generating-function bound (point weights)**: with neighbour set `nb p` (`adj p q → q ∈ nb p`),
if `x(p) Π_{q ∈ nb p} (1 + τ q) ≤ τ p` then `Wg(U, R) ≤ Π_{r∈R} τ r`. -/
theorem Wg_le (adj : P → P → Prop) (nb : P → Finset P) (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p)
    (x τ : P → ℝ) (hx : ∀ p, 0 ≤ x p) (hτ : ∀ p, 0 ≤ τ p)
    (hfix : ∀ p, x p * ∏ q ∈ nb p, (1 + τ q) ≤ τ p) :
    ∀ U R : Finset P, Wg adj x U R ≤ ∏ r ∈ R, τ r := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro R
  rcases R.eq_empty_or_nonempty with hR | ⟨r, hr⟩
  · subst hR
    unfold Wg
    have hsub : U.powerset.filter (fun C => Rooted adj ∅ C) ⊆ {∅} := by
      intro C hC
      obtain ⟨_, _, hreach⟩ := mem_filter.mp hC
      rw [mem_singleton, eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨ρ, hρ, _⟩ := hreach c hc
      exact absurd hρ (notMem_empty ρ)
    calc ∑ C ∈ U.powerset.filter (fun C => Rooted adj ∅ C), ∏ c ∈ C, x c
        ≤ ∑ C ∈ ({∅} : Finset (Finset P)), ∏ c ∈ C, x c :=
          sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => prod_nonneg fun c _ => hx c)
      _ = ∏ r ∈ (∅ : Finset P), τ r := by simp
  · by_cases hrU : r ∈ U
    · set N := (U \ R).filter (adj r) with hN
      have hNR : ∀ Q ∈ N.powerset, Disjoint (R.erase r) Q := by
        intro Q hQ
        rw [disjoint_left]
        intro y hy hyQ
        have := (mem_sdiff.mp (mem_filter.mp (mem_powerset.mp hQ hyQ)).1).2
        exact this (mem_of_mem_erase hy)
      have hNnb : N ⊆ nb r := by
        intro q hq
        exact hnb r q (fun h => (mem_sdiff.mp (mem_filter.mp hq).1).2 (h ▸ hr)) (mem_filter.mp hq).2
      have hT0 : 0 ≤ ∏ s ∈ R.erase r, τ s := prod_nonneg fun s _ => hτ s
      calc Wg adj x U R
          ≤ ∑ Q ∈ N.powerset, x r * Wg adj x (U.erase r) (R.erase r ∪ Q) :=
            Wg_step adj x hx U R r hr
        _ ≤ ∑ Q ∈ N.powerset, x r * ((∏ s ∈ R.erase r, τ s) * ∏ q ∈ Q, τ q) := by
            apply sum_le_sum
            intro Q hQ
            apply mul_le_mul_of_nonneg_left _ (hx r)
            have := ih (U.erase r) (erase_ssubset hrU) (R.erase r ∪ Q)
            rwa [prod_union (hNR Q hQ)] at this
        _ = x r * (∏ s ∈ R.erase r, τ s) * ∑ Q ∈ N.powerset, ∏ q ∈ Q, τ q := by
            rw [mul_assoc, mul_sum, mul_sum]
        _ = x r * (∏ s ∈ R.erase r, τ s) * ∏ q ∈ N, (1 + τ q) := by
            rw [prod_one_add]
        _ ≤ x r * (∏ s ∈ R.erase r, τ s) * ∏ q ∈ nb r, (1 + τ q) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hx r) hT0)
            exact prod_mono_of_one_le (fun q => 1 + τ q) (fun q => by linarith [hτ q]) hNnb
        _ = (x r * ∏ q ∈ nb r, (1 + τ q)) * ∏ s ∈ R.erase r, τ s := by ring
        _ ≤ τ r * ∏ s ∈ R.erase r, τ s := mul_le_mul_of_nonneg_right (hfix r) hT0
        _ = ∏ s ∈ R, τ s := mul_prod_erase R τ hr
    · have hempty : U.powerset.filter (fun C => Rooted adj R C) = ∅ := by
        rw [filter_eq_empty_iff]
        intro C hC hCR
        exact hrU (mem_powerset.mp hC (hCR.1 hr))
      unfold Wg
      rw [hempty, sum_empty]
      exact prod_nonneg fun s _ => hτ s

/-- Sum over connected sets containing the point `p` (point weights) ≤ τ p. -/
theorem point_gf_le_weighted (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p)
    (x τ : P → ℝ) (hx : ∀ p, 0 ≤ x p) (hτ : ∀ p, 0 ≤ τ p)
    (hfix : ∀ p, x p * ∏ q ∈ nb p, (1 + τ q) ≤ τ p) (U : Finset P) (p : P) :
    ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C), ∏ c ∈ C, x c ≤ τ p := by
  have hsub : U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C) ⊆
      U.powerset.filter (fun C => Rooted adj {p} C) := by
    intro C hC
    obtain ⟨hCU, hpC, hconn⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨hCU, rooted_of_connected adj hpC hconn⟩
  have hW := Wg_le adj nb hnb x τ hx hτ hfix U {p}
  rw [prod_singleton] at hW
  calc _ ≤ ∑ C ∈ U.powerset.filter (fun C => Rooted adj {p} C), ∏ c ∈ C, x c :=
        sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => prod_nonneg fun c _ => hx c)
    _ = Wg adj x U {p} := by unfold Wg; rfl
    _ ≤ τ p := hW

/-! ## 3. Two colours -/

/-- Splitting the neighbour product by colour: `Π_{q ∈ s} g(col q) = g(true)^{#colour true} g(false)^{#colour false}`. -/
theorem prod_by_color (col : P → Bool) (g : Bool → ℝ) (s : Finset P) :
    ∏ q ∈ s, g (col q) =
      g true ^ (s.filter (fun q => col q = true)).card *
        g false ^ (s.filter (fun q => col q = false)).card := by
  rw [← prod_filter_mul_prod_filter_not s (fun q => col q = true)]
  congr 1
  · rw [prod_congr rfl (fun q hq => by rw [(mem_filter.mp hq).2]), prod_const]
  · have hs : s.filter (fun q => ¬ col q = true) = s.filter (fun q => col q = false) := by
      apply filter_congr; intro q _; simp
    rw [hs, prod_congr rfl (fun q hq => by rw [(mem_filter.mp hq).2]), prod_const]

/-- **Two-colour generating-function bound**: if a colour-`a` point has ≤ `d a b` neighbours of colour `b`, `x p ≤ ξ (col p)`, and
`ξ a (1+θ false)^{d a false} (1+θ true)^{d a true} ≤ θ a`, then `Wg(U, R) ≤ Π_{r∈R} θ(col r)`. -/
theorem two_color_Wg_le (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ d (col p) b)
    (x : P → ℝ) (ξ θ : Bool → ℝ) (hx : ∀ p, 0 ≤ x p) (hxξ : ∀ p, x p ≤ ξ (col p))
    (hθ : ∀ b, 0 ≤ θ b)
    (hfix : ∀ a, ξ a * (1 + θ false) ^ d a false * (1 + θ true) ^ d a true ≤ θ a) :
    ∀ U R : Finset P, Wg adj x U R ≤ ∏ r ∈ R, θ (col r) := by
  apply Wg_le adj nb hnb x (fun p => θ (col p)) hx (fun p => hθ _)
  intro p
  have hprod := prod_by_color col (fun b => 1 + θ b) (nb p)
  have h1t : (1 : ℝ) ≤ 1 + θ true := by linarith [hθ true]
  have h1f : (1 : ℝ) ≤ 1 + θ false := by linarith [hθ false]
  have hpt : (1 + θ true) ^ ((nb p).filter (fun q => col q = true)).card ≤
      (1 + θ true) ^ d (col p) true := pow_le_pow_right₀ h1t (hdeg p true)
  have hpf : (1 + θ false) ^ ((nb p).filter (fun q => col q = false)).card ≤
      (1 + θ false) ^ d (col p) false := pow_le_pow_right₀ h1f (hdeg p false)
  have hB : ∏ q ∈ nb p, (1 + θ (col q)) ≤
      (1 + θ false) ^ d (col p) false * (1 + θ true) ^ d (col p) true := by
    rw [hprod, mul_comm]
    exact mul_le_mul hpf hpt (pow_nonneg (by linarith [hθ true]) _) (pow_nonneg (by linarith [hθ false]) _)
  have hξ0 : 0 ≤ ξ (col p) := le_trans (hx p) (hxξ p)
  calc x p * ∏ q ∈ nb p, (1 + θ (col q))
      ≤ ξ (col p) * ((1 + θ false) ^ d (col p) false * (1 + θ true) ^ d (col p) true) :=
        mul_le_mul (hxξ p) hB (prod_nonneg fun q _ => by linarith [hθ (col q)]) hξ0
    _ = ξ (col p) * (1 + θ false) ^ d (col p) false * (1 + θ true) ^ d (col p) true := by ring
    _ ≤ θ (col p) := hfix (col p)

/-! ## 4. Per-site sum -/

/-- **Two-colour per-site KP sum**: if `|z(C)| ≤ Π_{q∈C} ε(col q)`, KP weight `Π_{q∈C} e^{a(col q)}`, and
`ε_b e^{a_b} (1+θ₀)^{d b 0} (1+θ₁)^{d b 1} ≤ θ_b`, then the sum over connected `C ⊆ U` containing `p` is ≤ θ(col p). -/
theorem two_color_point_sum (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ d (col p) b)
    (z : Finset P → ℝ) (ε a θ : Bool → ℝ) (hε : ∀ b, 0 ≤ ε b) (hθ : ∀ b, 0 ≤ θ b)
    (hz : ∀ C, |z C| ≤ ∏ q ∈ C, ε (col q))
    (hfix : ∀ b, ε b * Real.exp (a b) * (1 + θ false) ^ d b false * (1 + θ true) ^ d b true ≤ θ b)
    (U : Finset P) (p : P) :
    ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C),
      |z C| * ∏ q ∈ C, Real.exp (a (col q)) ≤ θ (col p) := by
  set x : P → ℝ := fun q => ε (col q) * Real.exp (a (col q)) with hxdef
  have hx : ∀ q, 0 ≤ x q := fun q => mul_nonneg (hε _) (Real.exp_pos _).le
  have hW := point_gf_le_weighted adj nb hnb x (fun q => θ (col q)) hx (fun q => hθ _) (by
    intro q
    have hprod := prod_by_color col (fun b => 1 + θ b) (nb q)
    have hpt : (1 + θ true) ^ ((nb q).filter (fun r => col r = true)).card ≤
        (1 + θ true) ^ d (col q) true := pow_le_pow_right₀ (by linarith [hθ true]) (hdeg q true)
    have hpf : (1 + θ false) ^ ((nb q).filter (fun r => col r = false)).card ≤
        (1 + θ false) ^ d (col q) false := pow_le_pow_right₀ (by linarith [hθ false]) (hdeg q false)
    have hB : ∏ r ∈ nb q, (1 + θ (col r)) ≤
        (1 + θ false) ^ d (col q) false * (1 + θ true) ^ d (col q) true := by
      rw [hprod, mul_comm]
      exact mul_le_mul hpf hpt (pow_nonneg (by linarith [hθ true]) _) (pow_nonneg (by linarith [hθ false]) _)
    calc x q * ∏ r ∈ nb q, (1 + θ (col r))
        ≤ x q * ((1 + θ false) ^ d (col q) false * (1 + θ true) ^ d (col q) true) :=
          mul_le_mul_of_nonneg_left hB (hx q)
      _ = ε (col q) * Real.exp (a (col q)) * (1 + θ false) ^ d (col q) false *
            (1 + θ true) ^ d (col q) true := by rw [hxdef]; ring
      _ ≤ θ (col q) := hfix (col q)) U p
  calc _ ≤ ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C), ∏ c ∈ C, x c := by
        apply sum_le_sum
        intro C _
        rw [hxdef, prod_mul_distrib]
        exact mul_le_mul_of_nonneg_right (hz C) (prod_nonneg fun _ _ => (Real.exp_pos _).le)
    _ ≤ θ (col p) := hW

/-- For a root set `S` (e.g. a plaquette p and its 4 links), the sum over connected sets containing some element of `S`
is bounded by the sum over roots: ≤ Σ_{r∈S} θ(col r). -/
theorem two_color_root_set_sum (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ d (col p) b)
    (z : Finset P → ℝ) (ε a θ : Bool → ℝ) (hε : ∀ b, 0 ≤ ε b) (hθ : ∀ b, 0 ≤ θ b)
    (hz : ∀ C, |z C| ≤ ∏ q ∈ C, ε (col q))
    (hfix : ∀ b, ε b * Real.exp (a b) * (1 + θ false) ^ d b false * (1 + θ true) ^ d b true ≤ θ b)
    (U S : Finset P) :
    ∑ C ∈ U.powerset.filter (fun C => (S ∩ C).Nonempty ∧ IsConnectedSet adj C),
      |z C| * ∏ q ∈ C, Real.exp (a (col q)) ≤ ∑ r ∈ S, θ (col r) := by
  set f : Finset P → ℝ := fun C => |z C| * ∏ q ∈ C, Real.exp (a (col q)) with hf
  have hf0 : ∀ C, 0 ≤ f C := fun C => mul_nonneg (abs_nonneg _)
    (prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have hsplit : ∑ C ∈ U.powerset.filter (fun C => (S ∩ C).Nonempty ∧ IsConnectedSet adj C), f C ≤
      ∑ r ∈ S, ∑ C ∈ U.powerset.filter (fun C => r ∈ C ∧ IsConnectedSet adj C), f C := by
    rw [sum_filter]
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro C _
    split_ifs with h
    · obtain ⟨⟨r, hr⟩, hconn⟩ := h
      rw [mem_inter] at hr
      have hle : (if r ∈ C ∧ IsConnectedSet adj C then f C else 0) ≤
          ∑ y ∈ S, if y ∈ C ∧ IsConnectedSet adj C then f C else 0 :=
        single_le_sum (f := fun y => if y ∈ C ∧ IsConnectedSet adj C then f C else 0)
          (fun y _ => by split_ifs <;> simp [hf0]) hr.1
      simpa [hr.2, hconn] using hle
    · exact sum_nonneg fun y _ => by split_ifs <;> simp [hf0]
  refine le_trans hsplit (sum_le_sum fun r _ => ?_)
  exact two_color_point_sum adj nb hnb col d hdeg z ε a θ hε hθ hz hfix U r

/-! ## 5. Sufficient condition -/

/-- `(1+θ)^d ≤ e^{θ d}`. -/
theorem one_add_pow_le_exp (θ : ℝ) (hθ : 0 ≤ θ) (d : ℕ) :
    (1 + θ) ^ d ≤ Real.exp (θ * d) := by
  have h1 : 1 + θ ≤ Real.exp θ := by have := Real.add_one_le_exp θ; linarith
  calc (1 + θ) ^ d ≤ Real.exp θ ^ d := pow_le_pow_left₀ (by linarith) h1 d
    _ = Real.exp (θ * d) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Exponential sufficient condition: `ε_b e^{a_b + θ₀ d_{b0} + θ₁ d_{b1}} ≤ θ_b` ⇒ the two-colour condition. -/
theorem fix_of_exp (ε a θ : Bool → ℝ) (d : Bool → Bool → ℕ) (hε : ∀ b, 0 ≤ ε b)
    (hθ : ∀ b, 0 ≤ θ b)
    (h : ∀ b, ε b * Real.exp (a b + θ false * d b false + θ true * d b true) ≤ θ b) :
    ∀ b, ε b * Real.exp (a b) * (1 + θ false) ^ d b false * (1 + θ true) ^ d b true ≤ θ b := by
  intro b
  have hf := one_add_pow_le_exp (θ false) (hθ false) (d b false)
  have ht := one_add_pow_le_exp (θ true) (hθ true) (d b true)
  have he : Real.exp (a b + θ false * d b false + θ true * d b true) =
      Real.exp (a b) * Real.exp (θ false * d b false) * Real.exp (θ true * d b true) := by
    rw [Real.exp_add, Real.exp_add]
  have hA : 0 ≤ ε b * Real.exp (a b) := mul_nonneg (hε b) (Real.exp_pos _).le
  calc ε b * Real.exp (a b) * (1 + θ false) ^ d b false * (1 + θ true) ^ d b true
      ≤ ε b * Real.exp (a b) * Real.exp (θ false * d b false) * Real.exp (θ true * d b true) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hf hA) ht (pow_nonneg (by linarith [hθ true]) _)
        exact mul_nonneg hA (Real.exp_pos _).le
    _ = ε b * Real.exp (a b + θ false * d b false + θ true * d b true) := by rw [he]; ring
    _ ≤ θ b := h b

/-! ## 6. Lattice numbers -/

/-- Lattice degrees (plaquette→plaquette 20, plaquette→defect 48, defect→plaquette 72, defect→defect 122). -/
def latticeDeg : Bool → Bool → ℕ
  | false, false => 20
  | false, true => 48
  | true, false => 72
  | true, true => 122

/-- KP weights: thin plaquette e², link defect e^{12} (6 plaquettes). -/
noncomputable def kpWeight : Bool → ℝ
  | false => 2
  | true => 12

/-- Slopes θ = (1/20, 1/10⁴). -/
noncomputable def theta₀ : Bool → ℝ
  | false => 1 / 20
  | true => 1 / 10000

theorem exp_one_le : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9

theorem exp_nat_le (n : ℕ) : Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le n

/-- **Activity bounds with the lattice numbers**: if thin plaquettes have ε_thin ≤ 2.5·10⁻³ and link defects ε_L ≤ 1.5·10⁻¹¹,
the two-colour condition holds with θ = (1/20, 1/10⁴). -/
theorem lattice_fix (ε : Bool → ℝ)
    (hthin : ε false ≤ 2.5e-3) (hL : ε true ≤ 1.5e-11) :
    ∀ b, ε b * Real.exp (kpWeight b) * (1 + theta₀ false) ^ latticeDeg b false *
      (1 + theta₀ true) ^ latticeDeg b true ≤ theta₀ b := by
  intro b
  cases b
  · have he : Real.exp (kpWeight false) ≤ (2.7182818286 : ℝ) ^ 2 := by
      have := exp_nat_le 2; simpa [kpWeight] using this
    simp only [latticeDeg, theta₀]
    have hpos : (0 : ℝ) ≤ (1 + 1 / 20) ^ 20 * (1 + 1 / 10000) ^ 48 := by positivity
    calc ε false * Real.exp (kpWeight false) * (1 + 1 / 20) ^ 20 * (1 + 1 / 10000) ^ 48
        = ε false * Real.exp (kpWeight false) * ((1 + 1 / 20) ^ 20 * (1 + 1 / 10000) ^ 48) := by
          ring
      _ ≤ 2.5e-3 * (2.7182818286 : ℝ) ^ 2 * ((1 + 1 / 20) ^ 20 * (1 + 1 / 10000) ^ 48) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          exact mul_le_mul hthin he (Real.exp_pos _).le (by norm_num)
      _ ≤ 1 / 20 := by norm_num
  · have he : Real.exp (kpWeight true) ≤ (2.7182818286 : ℝ) ^ 12 := by
      have := exp_nat_le 12; simpa [kpWeight] using this
    simp only [latticeDeg, theta₀]
    have hpos : (0 : ℝ) ≤ (1 + 1 / 20) ^ 72 * (1 + 1 / 10000) ^ 122 := by positivity
    calc ε true * Real.exp (kpWeight true) * (1 + 1 / 20) ^ 72 * (1 + 1 / 10000) ^ 122
        = ε true * Real.exp (kpWeight true) * ((1 + 1 / 20) ^ 72 * (1 + 1 / 10000) ^ 122) := by
          ring
      _ ≤ 1.5e-11 * (2.7182818286 : ℝ) ^ 12 * ((1 + 1 / 20) ^ 72 * (1 + 1 / 10000) ^ 122) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          exact mul_le_mul hL he (Real.exp_pos _).le (by norm_num)
      _ ≤ 1 / 10000 := by norm_num

/-- Per-plaquette sum: for the roots plaquette p itself (thin) and the 4 links containing p (defects), θ₀ + 4θ₁ ≤ 1. -/
theorem lattice_face_total : theta₀ false + 4 * theta₀ true ≤ 1 := by
  simp only [theta₀]; norm_num

/-- **Per-plaquette KP sum on the lattice** (two colours): with activity bounds ε_thin ≤ 2.5·10⁻³, ε_L ≤ 1.5·10⁻¹¹,
degrees at most latticeDeg, and a root set S containing at most one thin plaquette and at most four defects,
the KP sum over connected sets meeting S is ≤ θ₀ + 4θ₁ ≤ 1. -/
theorem lattice_two_color_kp (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ latticeDeg (col p) b)
    (z : Finset P → ℝ) (ε : Bool → ℝ) (hε : ∀ b, 0 ≤ ε b)
    (hthin : ε false ≤ 2.5e-3) (hL : ε true ≤ 1.5e-11)
    (hz : ∀ C, |z C| ≤ ∏ q ∈ C, ε (col q)) (U S : Finset P)
    (hS0 : (S.filter (fun q => col q = false)).card ≤ 1)
    (hS1 : (S.filter (fun q => col q = true)).card ≤ 4) :
    ∑ C ∈ U.powerset.filter (fun C => (S ∩ C).Nonempty ∧ IsConnectedSet adj C),
      |z C| * ∏ q ∈ C, Real.exp (kpWeight (col q)) ≤ 1 := by
  have hθ : ∀ b, 0 ≤ theta₀ b := by intro b; cases b <;> simp [theta₀]
  have h := two_color_root_set_sum adj nb hnb col latticeDeg hdeg z ε kpWeight theta₀ hε hθ hz
    (lattice_fix ε hthin hL) U S
  refine le_trans h ?_
  have hsplit : ∑ r ∈ S, theta₀ (col r) =
      theta₀ true * (S.filter (fun q => col q = true)).card +
        theta₀ false * (S.filter (fun q => col q = false)).card := by
    rw [← sum_filter_add_sum_filter_not S (fun q => col q = true)]
    have hs : S.filter (fun q => ¬ col q = true) = S.filter (fun q => col q = false) := by
      apply filter_congr; intro q _; simp
    rw [hs]
    have e1 : ∑ q ∈ S.filter (fun q => col q = true), theta₀ (col q) =
        ∑ q ∈ S.filter (fun q => col q = true), theta₀ true :=
      sum_congr rfl (fun q hq => by rw [(mem_filter.mp hq).2])
    have e0 : ∑ q ∈ S.filter (fun q => col q = false), theta₀ (col q) =
        ∑ q ∈ S.filter (fun q => col q = false), theta₀ false :=
      sum_congr rfl (fun q hq => by rw [(mem_filter.mp hq).2])
    rw [e1, e0, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [hsplit]
  have h1 : ((S.filter (fun q => col q = true)).card : ℝ) ≤ 4 := by exact_mod_cast hS1
  have h0 : ((S.filter (fun q => col q = false)).card : ℝ) ≤ 1 := by exact_mod_cast hS0
  have := lattice_face_total
  have ht : 0 ≤ theta₀ true := hθ true
  have hf : 0 ≤ theta₀ false := hθ false
  nlinarith



/-! ## 7. Encoding -/

section Enc

variable {F L : Type*} [DecidableEq F] [DecidableEq L]

/-- A sum mapped by an injection is at most the sum over the target (nonnegative terms). -/
theorem sum_le_of_injOn {α β : Type*} [DecidableEq β] (A : Finset α) (B : Finset β) (f : α → β)
    (hinj : Set.InjOn f A) (hmap : ∀ a ∈ A, f a ∈ B) (ψ : β → ℝ) (hψ : ∀ b, 0 ≤ ψ b) :
    ∑ a ∈ A, ψ (f a) ≤ ∑ b ∈ B, ψ b := by
  rw [← sum_image (f := ψ) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    exact hmap a ha
  · intro b _ _; exact hψ b

/-- **Label sum**: `Σ_{T ⊆ ∪_{ℓ∈R} D ℓ} Π_{ℓ∈R} g ℓ (T ∩ D ℓ) ≤ Π_{ℓ∈R} Σ_{S ⊆ D ℓ} g ℓ S` (g ≥ 0). -/
theorem label_sum_le (D : L → Finset F) (g : L → Finset F → ℝ) (hg : ∀ ℓ S, 0 ≤ g ℓ S) :
    ∀ R : Finset L, ∑ T ∈ (R.biUnion D).powerset, ∏ ℓ ∈ R, g ℓ (T ∩ D ℓ) ≤
      ∏ ℓ ∈ R, ∑ S ∈ (D ℓ).powerset, g ℓ S := by
  intro R
  induction R using Finset.induction_on with
  | empty => simp
  | @insert ℓ₀ R hℓ₀ ih =>
    set UR := R.biUnion D with hUR
    have hU : (insert ℓ₀ R).biUnion D = D ℓ₀ ∪ UR := biUnion_insert
    have hsubR : ∀ ℓ ∈ R, D ℓ ⊆ UR := fun ℓ hℓ => subset_biUnion_of_mem D hℓ
    set H : Finset F × Finset F → ℝ := fun pr => g ℓ₀ pr.1 * ∏ ℓ ∈ R, g ℓ (pr.2 ∩ D ℓ) with hH
    have hH0 : ∀ pr, 0 ≤ H pr := fun pr => mul_nonneg (hg _ _) (prod_nonneg fun _ _ => hg _ _)
    have hrw : ∀ T ∈ (D ℓ₀ ∪ UR).powerset, ∏ ℓ ∈ insert ℓ₀ R, g ℓ (T ∩ D ℓ) =
        H (T ∩ D ℓ₀, T ∩ UR) := by
      intro T _
      rw [prod_insert hℓ₀, hH]
      congr 1
      refine prod_congr rfl fun ℓ hℓ => ?_
      congr 1
      rw [inter_assoc, inter_eq_right.mpr (hsubR ℓ hℓ)]
    rw [hU, sum_congr rfl hrw]
    have hinj : Set.InjOn (fun T : Finset F => (T ∩ D ℓ₀, T ∩ UR)) ((D ℓ₀ ∪ UR).powerset : Set _) := by
      intro T₁ h₁ T₂ h₂ he
      simp only [Prod.mk.injEq] at he
      have h₁' : T₁ ⊆ D ℓ₀ ∪ UR := mem_powerset.mp h₁
      have h₂' : T₂ ⊆ D ℓ₀ ∪ UR := mem_powerset.mp h₂
      have e₁ : T₁ = T₁ ∩ D ℓ₀ ∪ T₁ ∩ UR := by
        rw [← inter_union_distrib_left, inter_eq_left.mpr h₁']
      have e₂ : T₂ = T₂ ∩ D ℓ₀ ∪ T₂ ∩ UR := by
        rw [← inter_union_distrib_left, inter_eq_left.mpr h₂']
      rw [e₁, e₂, he.1, he.2]
    have hmap : ∀ T ∈ (D ℓ₀ ∪ UR).powerset,
        (T ∩ D ℓ₀, T ∩ UR) ∈ (D ℓ₀).powerset ×ˢ UR.powerset := by
      intro T _
      exact mem_product.mpr ⟨mem_powerset.mpr inter_subset_right, mem_powerset.mpr inter_subset_right⟩
    calc ∑ T ∈ (D ℓ₀ ∪ UR).powerset, H (T ∩ D ℓ₀, T ∩ UR)
        ≤ ∑ pr ∈ (D ℓ₀).powerset ×ˢ UR.powerset, H pr :=
          sum_le_of_injOn _ _ (fun T => (T ∩ D ℓ₀, T ∩ UR)) hinj hmap H hH0
      _ = (∑ S ∈ (D ℓ₀).powerset, g ℓ₀ S) * ∑ T ∈ UR.powerset, ∏ ℓ ∈ R, g ℓ (T ∩ D ℓ) := by
          rw [sum_product, sum_mul]
          refine sum_congr rfl fun S _ => ?_
          rw [mul_sum]
      _ ≤ (∑ S ∈ (D ℓ₀).powerset, g ℓ₀ S) * ∏ ℓ ∈ R, ∑ S ∈ (D ℓ).powerset, g ℓ S :=
          mul_le_mul_of_nonneg_left ih (sum_nonneg fun _ _ => hg _ _)
      _ = ∏ ℓ ∈ insert ℓ₀ R, ∑ S ∈ (D ℓ).powerset, g ℓ S := by rw [prod_insert hℓ₀]

variable (D : L → Finset F) (ΛL : Finset L) (m : ℕ)

/-- Defect links: links in `ΛL` such that `X` contains at least `m` of their plaquettes. -/
def defects (X : Finset F) : Finset L := ΛL.filter (fun ℓ => m ≤ (X ∩ D ℓ).card)

/-- Thin plaquettes: plaquettes of `X` that belong to no defect link. -/
def thin (X : Finset F) : Finset F := X.filter (fun p => ∀ ℓ ∈ defects D ΛL m X, p ∉ D ℓ)

/-- Encoding: thin plaquettes (left) and defect links (right). -/
def enc (X : Finset F) : Finset (F ⊕ L) := (thin D ΛL m X).disjSum (defects D ΛL m X)

/-- Two-colour adjacency. -/
def cadj (adjF : F → F → Prop) : F ⊕ L → F ⊕ L → Prop
  | Sum.inl p, Sum.inl q => adjF p q
  | Sum.inl p, Sum.inr ℓ => p ∉ D ℓ ∧ ∃ q ∈ D ℓ, adjF p q
  | Sum.inr ℓ, Sum.inl p => p ∉ D ℓ ∧ ∃ q ∈ D ℓ, adjF q p
  | Sum.inr ℓ, Sum.inr ℓ' => ∃ p ∈ D ℓ, ∃ q ∈ D ℓ', p = q ∨ adjF p q

/-- Image of a plaquette: a defect link containing it if there is one (a chosen one), otherwise the plaquette itself. -/
noncomputable def img (X : Finset F) (f : F) : F ⊕ L :=
  if h : ∃ ℓ ∈ defects D ΛL m X, f ∈ D ℓ then Sum.inr (Classical.choose h) else Sum.inl f

theorem img_spec (X : Finset F) (f : F) :
    (∃ ℓ ∈ defects D ΛL m X, f ∈ D ℓ ∧ img D ΛL m X f = Sum.inr ℓ) ∨
      ((∀ ℓ ∈ defects D ΛL m X, f ∉ D ℓ) ∧ img D ΛL m X f = Sum.inl f) := by
  unfold img
  split_ifs with h
  · exact Or.inl ⟨_, (Classical.choose_spec h).1, (Classical.choose_spec h).2, rfl⟩
  · exact Or.inr ⟨fun ℓ hℓ hf => h ⟨ℓ, hℓ, hf⟩, rfl⟩

theorem img_mem (X : Finset F) {f : F} (hf : f ∈ X) : img D ΛL m X f ∈ enc D ΛL m X := by
  rcases img_spec D ΛL m X f with ⟨ℓ, hℓ, _, he⟩ | ⟨hno, he⟩
  · rw [he, enc, inr_mem_disjSum]; exact hℓ
  · rw [he, enc, inl_mem_disjSum, thin, mem_filter]; exact ⟨hf, hno⟩

/-- Images of adjacent plaquettes are adjacent. -/
theorem img_adj (adjF : F → F → Prop) (X : Finset F) {f g : F} (hfg : adjF f g) :
    cadj D adjF (img D ΛL m X f) (img D ΛL m X g) := by
  rcases img_spec D ΛL m X f with ⟨ℓ, hℓ, hfℓ, hf⟩ | ⟨hfno, hf⟩ <;>
    rcases img_spec D ΛL m X g with ⟨ℓ', hℓ', hgℓ', hg⟩ | ⟨hgno, hg⟩ <;> rw [hf, hg]
  · exact ⟨f, hfℓ, g, hgℓ', Or.inr hfg⟩
  · exact ⟨hgno ℓ hℓ, f, hfℓ, hfg⟩
  · exact ⟨hfno ℓ' hℓ', g, hgℓ', hfg⟩
  · exact hfg

/-- **Preservation of connectedness**: if `1 ≤ m` and `X` is connected under plaquette adjacency, its encoding is connected under two-colour adjacency. -/
theorem enc_connected (adjF : F → F → Prop) (hm : 1 ≤ m) (X : Finset F)
    (hX : IsConnectedSet adjF X) : IsConnectedSet (cadj D adjF) (enc D ΛL m X) := by
  set C := enc D ΛL m X
  -- image of the path
  have hpath : ∀ f g, Conn adjF X f g → f ∈ X → Conn (cadj D adjF) C (img D ΛL m X f) (img D ΛL m X g) := by
    intro f g h hf
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b e hb hbe ih =>
      exact (ih).tail ⟨img_mem D ΛL m X hbe.1, img_mem D ΛL m X hbe.2.1, img_adj D ΛL m adjF X hbe.2.2⟩
  -- each point of C has a plaquette of X whose image equals it or is adjacent to it
  have hrep : ∀ a ∈ C, ∃ f ∈ X, img D ΛL m X f = a ∨
      (cadj D adjF a (img D ΛL m X f) ∧ cadj D adjF (img D ΛL m X f) a) := by
    intro a ha
    rcases a with p | ℓ
    · have ha2 : Sum.inl p ∈ (thin D ΛL m X).disjSum (defects D ΛL m X) := ha
      rw [inl_mem_disjSum, thin, mem_filter] at ha2
      have ha := ha2
      refine ⟨p, ha.1, Or.inl ?_⟩
      rcases img_spec D ΛL m X p with ⟨ℓ, hℓ, hpℓ, _⟩ | ⟨_, he⟩
      · exact absurd hpℓ (ha.2 ℓ hℓ)
      · exact he
    · have ha2 : Sum.inr ℓ ∈ (thin D ΛL m X).disjSum (defects D ΛL m X) := ha
      rw [inr_mem_disjSum] at ha2
      have ha := ha2
      have hcard : m ≤ (X ∩ D ℓ).card := (mem_filter.mp ha).2
      obtain ⟨f, hf⟩ : (X ∩ D ℓ).Nonempty := card_pos.mp (by omega)
      obtain ⟨hfX, hfD⟩ := mem_inter.mp hf
      refine ⟨f, hfX, Or.inr ?_⟩
      rcases img_spec D ΛL m X f with ⟨ℓ', _, hfℓ', he⟩ | ⟨hno, _⟩
      · rw [he]; exact ⟨⟨f, hfD, f, hfℓ', Or.inl rfl⟩, ⟨f, hfℓ', f, hfD, Or.inl rfl⟩⟩
      · exact absurd hfD (hno ℓ ha)
  intro a ha b hb
  obtain ⟨fa, hfa, ha'⟩ := hrep a ha
  obtain ⟨fb, hfb, hb'⟩ := hrep b hb
  have hmid := hpath fa fb (hX fa hfa fb hfb) hfa
  have hia := img_mem D ΛL m X hfa
  have hib := img_mem D ΛL m X hfb
  have h1 : Conn (cadj D adjF) C a (img D ΛL m X fb) := by
    rcases ha' with he | ⟨hadj, _⟩
    · rw [← he]; exact hmid
    · exact Relation.ReflTransGen.head ⟨ha, hia, hadj⟩ hmid
  rcases hb' with he | ⟨_, hadj⟩
  · rw [← he]; exact h1
  · exact h1.tail ⟨hib, hb, hadj⟩

/-- Decoding: `X = thin X ∪ (X ∩ ∪_{ℓ∈defects X} D ℓ)`. -/
theorem decode (X : Finset F) :
    X = thin D ΛL m X ∪ X ∩ (defects D ΛL m X).biUnion D := by
  ext p
  constructor
  · intro hp
    by_cases h : ∃ ℓ ∈ defects D ΛL m X, p ∈ D ℓ
    · obtain ⟨ℓ, hℓ, hpℓ⟩ := h
      exact mem_union_right _ (mem_inter.mpr ⟨hp, mem_biUnion.mpr ⟨ℓ, hℓ, hpℓ⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, fun ℓ hℓ hpℓ => h ⟨ℓ, hℓ, hpℓ⟩⟩)
  · intro hp
    rcases mem_union.mp hp with h | h
    · exact (mem_filter.mp h).1
    · exact (mem_inter.mp h).1

/-- Sets X with the same encoding have the same thin plaquettes and defect links. -/
theorem enc_eq (X Y : Finset F) (h : enc D ΛL m X = enc D ΛL m Y) :
    thin D ΛL m X = thin D ΛL m Y ∧ defects D ΛL m X = defects D ΛL m Y := by
  constructor
  · ext p
    have := congrArg (fun C => Sum.inl p ∈ C) h
    simpa [enc, inl_mem_disjSum] using this
  · ext ℓ
    have := congrArg (fun C => Sum.inr ℓ ∈ C) h
    simpa [enc, inr_mem_disjSum] using this

/-- Thin plaquettes are disjoint from the plaquettes of every defect link. -/
theorem thin_disjoint (X : Finset F) :
    Disjoint (thin D ΛL m X) ((defects D ΛL m X).biUnion D) := by
  rw [disjoint_left]
  intro p hp hq
  obtain ⟨ℓ, hℓ, hpℓ⟩ := mem_biUnion.mp hq
  exact (mem_filter.mp hp).2 ℓ hℓ hpℓ

/-- Size: `|X| ≤ |thin X| + Σ_{ℓ∈defects X} |X ∩ D ℓ|`. -/
theorem card_le_enc (X : Finset F) :
    X.card ≤ (thin D ΛL m X).card + ∑ ℓ ∈ defects D ΛL m X, (X ∩ D ℓ).card := by
  calc X.card = (thin D ΛL m X ∪ X ∩ (defects D ΛL m X).biUnion D).card := by
        rw [← decode D ΛL m X]
    _ ≤ (thin D ΛL m X).card + (X ∩ (defects D ΛL m X).biUnion D).card := card_union_le _ _
    _ ≤ (thin D ΛL m X).card + ∑ ℓ ∈ defects D ΛL m X, (X ∩ D ℓ).card := by
        rw [inter_biUnion]
        exact Nat.add_le_add_left card_biUnion_le _


end Enc

/-! ## 8. Fibre-wise sum and the link to the per-plaquette sum -/

section Encoding

variable {F L : Type*} [DecidableEq F] [DecidableEq L]

/-- Two-colour point weights: thin plaquette `ε₀e²`, link `Σ_{S⊆D ℓ} η(ℓ,S) e^{2|S|}` (label sum). -/
noncomputable def xw (D : L → Finset F) (ε₀ : ℝ) (η : L → Finset F → ℝ) : F ⊕ L → ℝ
  | Sum.inl _ => ε₀ * Real.exp 2
  | Sum.inr ℓ => ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card)

/-- The weight of a single X is bounded by the product of point weights of its encoding (labels fixed to X ∩ D ℓ). -/
theorem weight_le_G (D : L → Finset F) (ΛL : Finset L) (m : ℕ) (X : Finset F) (z : ℝ) (ε₀ : ℝ)
    (hε₀ : 0 ≤ ε₀) (η : L → Finset F → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hz : |z| ≤ (∏ _p ∈ thin D ΛL m X, ε₀) * ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ)) :
    |z| * Real.exp (2 * X.card) ≤
      (∏ _p ∈ thin D ΛL m X, ε₀ * Real.exp 2) *
        ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ) * Real.exp (2 * (X ∩ D ℓ).card) := by
  set th := thin D ΛL m X
  set R := defects D ΛL m X
  have hcard := card_le_enc D ΛL m X
  have hexp : Real.exp (2 * X.card) ≤
      Real.exp 2 ^ th.card * ∏ ℓ ∈ R, Real.exp (2 * (X ∩ D ℓ).card) := by
    rw [← Real.exp_sum, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (X.card : ℝ) ≤ th.card + ∑ ℓ ∈ R, ((X ∩ D ℓ).card : ℝ) := by exact_mod_cast hcard
    rw [← mul_sum]; nlinarith
  have hA : 0 ≤ (∏ _p ∈ th, ε₀) * ∏ ℓ ∈ R, η ℓ (X ∩ D ℓ) :=
    mul_nonneg (prod_nonneg fun _ _ => hε₀) (prod_nonneg fun _ _ => hη _ _)
  calc |z| * Real.exp (2 * X.card)
      ≤ ((∏ _p ∈ th, ε₀) * ∏ ℓ ∈ R, η ℓ (X ∩ D ℓ)) *
          (Real.exp 2 ^ th.card * ∏ ℓ ∈ R, Real.exp (2 * (X ∩ D ℓ).card)) :=
        mul_le_mul hz hexp (Real.exp_pos _).le hA
    _ = (∏ _p ∈ th, ε₀ * Real.exp 2) *
          ∏ ℓ ∈ R, η ℓ (X ∩ D ℓ) * Real.exp (2 * (X ∩ D ℓ).card) := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_const (Real.exp 2)]; ring

/-- **Encoded sum**: for a family `𝒳` of connected sets of large plaquettes (inside `ΛF`),
`Σ_{X∈𝒳} |z(X)| e^{2|X|} ≤ Σ_{C ⊆ ΛF ⊔ ΛL, Q C, two-colour connected} Π_{q∈C} xw(q)`.
Hypothesis of (H-2col) form: `|z(X)| ≤ ε₀^{|thin X|} Π_{ℓ∈defects X} η(ℓ, X ∩ D ℓ)`. -/
theorem encoded_sum_le (D : L → Finset F) (adjF : F → F → Prop) (ΛF : Finset F) (ΛL : Finset L)
    (m : ℕ) (hm : 1 ≤ m) (𝒳 : Finset (Finset F))
    (h𝒳 : ∀ X ∈ 𝒳, X ⊆ ΛF ∧ IsConnectedSet adjF X)
    (z : Finset F → ℝ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (η : L → Finset F → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hz : ∀ X ∈ 𝒳, |z X| ≤ (∏ _p ∈ thin D ΛL m X, ε₀) * ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ))
    (Q : Finset (F ⊕ L) → Prop) (hQ : ∀ X ∈ 𝒳, Q (enc D ΛL m X)) :
    ∑ X ∈ 𝒳, |z X| * Real.exp (2 * X.card) ≤
      ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter (fun C => Q C ∧ IsConnectedSet (cadj D adjF) C),
        ∏ q ∈ C, xw D ε₀ η q := by
  set g : L → Finset F → ℝ := fun ℓ S => η ℓ S * Real.exp (2 * S.card) with hg
  have hg0 : ∀ ℓ S, 0 ≤ g ℓ S := fun ℓ S => mul_nonneg (hη ℓ S) (Real.exp_pos _).le
  set G : Finset F → ℝ := fun X => (∏ _p ∈ thin D ΛL m X, ε₀ * Real.exp 2) *
    ∏ ℓ ∈ defects D ΛL m X, g ℓ (X ∩ D ℓ) with hG
  have hxw0 : ∀ q, 0 ≤ xw D ε₀ η q := by
    intro q; cases q with
    | inl _ => exact mul_nonneg hε₀ (Real.exp_pos _).le
    | inr ℓ => exact sum_nonneg fun S _ => hg0 ℓ S
  -- step 1: term by term
  have h1 : ∑ X ∈ 𝒳, |z X| * Real.exp (2 * X.card) ≤ ∑ X ∈ 𝒳, G X :=
    sum_le_sum fun X hX => weight_le_G D ΛL m X (z X) ε₀ hε₀ η hη (hz X hX)
  -- step 2: split into fibres by encoding
  have h2 : ∑ X ∈ 𝒳, G X = ∑ C ∈ 𝒳.image (enc D ΛL m), ∑ X ∈ 𝒳.filter (fun X => enc D ΛL m X = C), G X :=
    (sum_fiberwise_of_maps_to (fun X hX => mem_image_of_mem _ hX) G).symm
  -- step 3: fibre by fibre
  have h3 : ∀ C ∈ 𝒳.image (enc D ΛL m),
      ∑ X ∈ 𝒳.filter (fun X => enc D ΛL m X = C), G X ≤ ∏ q ∈ C, xw D ε₀ η q := by
    intro C hC
    obtain ⟨X₀, hX₀, rfl⟩ := mem_image.mp hC
    set th := thin D ΛL m X₀
    set R := defects D ΛL m X₀
    set U := R.biUnion D
    have hfib : ∀ X ∈ 𝒳.filter (fun X => enc D ΛL m X = enc D ΛL m X₀),
        thin D ΛL m X = th ∧ defects D ΛL m X = R := fun X hX => enc_eq D ΛL m X X₀ (mem_filter.mp hX).2
    have hGX : ∀ X ∈ 𝒳.filter (fun X => enc D ΛL m X = enc D ΛL m X₀),
        G X = (∏ _p ∈ th, ε₀ * Real.exp 2) * ∏ ℓ ∈ R, g ℓ ((X ∩ U) ∩ D ℓ) := by
      intro X hX
      obtain ⟨h1, h2⟩ := hfib X hX
      rw [hG]; simp only
      rw [h1, h2]
      congr 1
      refine prod_congr rfl fun ℓ hℓ => ?_
      rw [inter_assoc, inter_eq_right.mpr (subset_biUnion_of_mem D hℓ)]
    rw [sum_congr rfl hGX, ← mul_sum]
    have hinj : Set.InjOn (fun X : Finset F => X ∩ U)
        ((𝒳.filter (fun X => enc D ΛL m X = enc D ΛL m X₀)) : Set (Finset F)) := by
      intro X₁ h₁ X₂ h₂ he
      obtain ⟨a₁, b₁⟩ := hfib X₁ h₁
      obtain ⟨a₂, b₂⟩ := hfib X₂ h₂
      have e₁ := decode D ΛL m X₁
      have e₂ := decode D ΛL m X₂
      rw [a₁, b₁] at e₁; rw [a₂, b₂] at e₂
      simp only at he
      rw [e₁, e₂, he]
    have hmap : ∀ X ∈ 𝒳.filter (fun X => enc D ΛL m X = enc D ΛL m X₀), X ∩ U ∈ U.powerset :=
      fun X _ => mem_powerset.mpr inter_subset_right
    have hsum := sum_le_of_injOn _ _ (fun X : Finset F => X ∩ U) hinj hmap
      (fun T => ∏ ℓ ∈ R, g ℓ (T ∩ D ℓ)) (fun T => prod_nonneg fun _ _ => hg0 _ _)
    have hlab := label_sum_le D g hg0 R
    have hC : ∏ q ∈ enc D ΛL m X₀, xw D ε₀ η q =
        (∏ _p ∈ th, ε₀ * Real.exp 2) * ∏ ℓ ∈ R, ∑ S ∈ (D ℓ).powerset, g ℓ S := by
      rw [enc, prod_disjSum]; rfl
    rw [hC]
    exact mul_le_mul_of_nonneg_left (le_trans hsum hlab) (prod_nonneg fun _ _ => by positivity)
  -- step 4: the image lies among two-colour connected sets
  have h4 : 𝒳.image (enc D ΛL m) ⊆
      (ΛF.disjSum ΛL).powerset.filter (fun C => Q C ∧ IsConnectedSet (cadj D adjF) C) := by
    intro C hC
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hC
    obtain ⟨hXF, hXc⟩ := h𝒳 X hX
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, hQ X hX, enc_connected D ΛL m adjF hm X hXc⟩
    intro q hq
    have hq' : q ∈ (thin D ΛL m X).disjSum (defects D ΛL m X) := hq
    rcases q with p | ℓ
    · rw [inl_mem_disjSum] at hq' ⊢; exact hXF (mem_filter.mp hq').1
    · rw [inr_mem_disjSum] at hq' ⊢; exact (mem_filter.mp hq').1
  calc ∑ X ∈ 𝒳, |z X| * Real.exp (2 * X.card) ≤ ∑ X ∈ 𝒳, G X := h1
    _ = _ := h2
    _ ≤ ∑ C ∈ 𝒳.image (enc D ΛL m), ∏ q ∈ C, xw D ε₀ η q := sum_le_sum h3
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg h4 (fun C _ _ => prod_nonneg fun q _ => hxw0 q)

/-- Root set of plaquette `x₀`: `x₀` itself (thin) and the links of `ΛL` containing `x₀` (defects). -/
def rootSet (D : L → Finset F) (ΛL : Finset L) (x₀ : F) : Finset (F ⊕ L) :=
  ({x₀} : Finset F).disjSum (ΛL.filter (fun ℓ => x₀ ∈ D ℓ))

/-- If `x₀ ∈ X`, the encoding of `X` meets the root set. -/
theorem enc_meets_root (D : L → Finset F) (ΛL : Finset L) (m : ℕ) (X : Finset F) {x₀ : F}
    (hx : x₀ ∈ X) : (rootSet D ΛL x₀ ∩ enc D ΛL m X).Nonempty := by
  refine ⟨img D ΛL m X x₀, mem_inter.mpr ⟨?_, img_mem D ΛL m X hx⟩⟩
  rcases img_spec D ΛL m X x₀ with ⟨ℓ, hℓ, hxℓ, he⟩ | ⟨_, he⟩
  · rw [he, rootSet, inr_mem_disjSum, mem_filter]; exact ⟨(mem_filter.mp hℓ).1, hxℓ⟩
  · rw [he, rootSet, inl_mem_disjSum]; exact mem_singleton_self _

end Encoding

/-! ## 9. Sum over two-colour root sets (point weights) and the per-plaquette KP sum (hsite form) -/

/-- Under the two-colour hypothesis, the weighted sum over connected sets containing point `p` is ≤ θ(col p). -/
theorem two_color_point_gf (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ d (col p) b)
    (x : P → ℝ) (ξ θ : Bool → ℝ) (hx : ∀ p, 0 ≤ x p) (hxξ : ∀ p, x p ≤ ξ (col p))
    (hθ : ∀ b, 0 ≤ θ b)
    (hfix : ∀ a, ξ a * (1 + θ false) ^ d a false * (1 + θ true) ^ d a true ≤ θ a)
    (U : Finset P) (p : P) :
    ∑ C ∈ U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C), ∏ c ∈ C, x c ≤ θ (col p) := by
  have hsub : U.powerset.filter (fun C => p ∈ C ∧ IsConnectedSet adj C) ⊆
      U.powerset.filter (fun C => Rooted adj {p} C) := by
    intro C hC
    obtain ⟨hCU, hpC, hconn⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨hCU, rooted_of_connected adj hpC hconn⟩
  have hW := two_color_Wg_le adj nb hnb col d hdeg x ξ θ hx hxξ hθ hfix U {p}
  rw [prod_singleton] at hW
  calc _ ≤ ∑ C ∈ U.powerset.filter (fun C => Rooted adj {p} C), ∏ c ∈ C, x c :=
        sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ => prod_nonneg fun c _ => hx c)
    _ = Wg adj x U {p} := by unfold Wg; rfl
    _ ≤ θ (col p) := hW

/-- The weighted sum over connected sets meeting the root set `S` is ≤ Σ_{r∈S} θ(col r). -/
theorem two_color_root_gf (adj : P → P → Prop) (nb : P → Finset P)
    (hnb : ∀ p q, p ≠ q → adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
    (hdeg : ∀ p b, ((nb p).filter (fun q => col q = b)).card ≤ d (col p) b)
    (x : P → ℝ) (ξ θ : Bool → ℝ) (hx : ∀ p, 0 ≤ x p) (hxξ : ∀ p, x p ≤ ξ (col p))
    (hθ : ∀ b, 0 ≤ θ b)
    (hfix : ∀ a, ξ a * (1 + θ false) ^ d a false * (1 + θ true) ^ d a true ≤ θ a)
    (U S : Finset P) :
    ∑ C ∈ U.powerset.filter (fun C => (S ∩ C).Nonempty ∧ IsConnectedSet adj C), ∏ c ∈ C, x c ≤
      ∑ r ∈ S, θ (col r) := by
  set f : Finset P → ℝ := fun C => ∏ c ∈ C, x c with hf
  have hf0 : ∀ C, 0 ≤ f C := fun C => prod_nonneg fun c _ => hx c
  have hsplit : ∑ C ∈ U.powerset.filter (fun C => (S ∩ C).Nonempty ∧ IsConnectedSet adj C), f C ≤
      ∑ r ∈ S, ∑ C ∈ U.powerset.filter (fun C => r ∈ C ∧ IsConnectedSet adj C), f C := by
    rw [sum_filter]
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro C _
    split_ifs with h
    · obtain ⟨⟨r, hr⟩, hconn⟩ := h
      rw [mem_inter] at hr
      have hle : (if r ∈ C ∧ IsConnectedSet adj C then f C else 0) ≤
          ∑ y ∈ S, if y ∈ C ∧ IsConnectedSet adj C then f C else 0 :=
        single_le_sum (f := fun y => if y ∈ C ∧ IsConnectedSet adj C then f C else 0)
          (fun y _ => by split_ifs <;> simp [hf0]) hr.1
      simpa [hr.2, hconn] using hle
    · exact sum_nonneg fun y _ => by split_ifs <;> simp [hf0]
  refine le_trans hsplit (sum_le_sum fun r _ => ?_)
  exact two_color_point_gf adj nb hnb col d hdeg x ξ θ hx hxξ hθ hfix U r

section Site

variable {F L : Type*} [DecidableEq F] [DecidableEq L]

/-- Lattice activity bounds (two colours): thin plaquette 2.5·10⁻³, link defect 1.5·10⁻¹¹. -/
noncomputable def latticeEps : Bool → ℝ
  | false => 2.5e-3
  | true => 1.5e-11

/-- **Per-plaquette KP sum (hsite form)**: for a family `𝒳` of connected sets of large plaquettes (inside `ΛF`), defects = coverage ≥ m (1 ≤ m),
an activity bound of (H-2col) form, thin plaquettes ε₀ ≤ 2.5·10⁻³, label sum per link Σ_{S⊆D ℓ} η(ℓ,S)e^{2|S|} ≤ 1.5·10⁻¹¹·e^{12},
two-colour degree ≤ latticeDeg, and at most 4 links containing each plaquette, we get
Σ_{X∈𝒳, x∈X} |z(X)| e^{2|X|} ≤ 1 for every plaquette x (hsite of KPToDobrushin.dobrushin_cond_of_kp, supp = id). -/
theorem encoded_kp_site (D : L → Finset F) (adjF : F → F → Prop) (ΛF : Finset F) (ΛL : Finset L)
    (m : ℕ) (hm : 1 ≤ m) (𝒳 : Finset (Finset F))
    (h𝒳 : ∀ X ∈ 𝒳, X ⊆ ΛF ∧ IsConnectedSet adjF X)
    (z : Finset F → ℝ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 2.5e-3)
    (η : L → Finset F → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hlink : ∀ ℓ, ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ 1.5e-11 * Real.exp 12)
    (hz : ∀ X ∈ 𝒳, |z X| ≤ (∏ _p ∈ thin D ΛL m X, ε₀) * ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ))
    (nb : F ⊕ L → Finset (F ⊕ L)) (hnb : ∀ p q, p ≠ q → cadj D adjF p q → q ∈ nb p)
    (hdeg : ∀ p b, ((nb p).filter (fun q => q.isRight = b)).card ≤ latticeDeg p.isRight b)
    (hfour : ∀ x : F, (ΛL.filter (fun ℓ => x ∈ D ℓ)).card ≤ 4) :
    ∀ x : F, ∑ X ∈ 𝒳.filter (fun s => x ∈ id s), |z X| * Real.exp (2 * (id X).card) ≤ 1 := by
  intro x₀
  have hsub : ∀ X ∈ 𝒳.filter (fun s => x₀ ∈ id s), X ⊆ ΛF ∧ IsConnectedSet adjF X :=
    fun X hX => h𝒳 X (mem_filter.mp hX).1
  have hE := encoded_sum_le D adjF ΛF ΛL m hm (𝒳.filter (fun s => x₀ ∈ id s)) hsub z ε₀ hε₀ η hη
    (fun X hX => hz X (mem_filter.mp hX).1) (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty)
    (fun X hX => enc_meets_root D ΛL m X (mem_filter.mp hX).2)
  have hξ : ∀ q, xw D ε₀ η q ≤ (fun b => latticeEps b * Real.exp (kpWeight b)) q.isRight := by
    intro q; cases q with
    | inl _ =>
      show ε₀ * Real.exp 2 ≤ latticeEps false * Real.exp (kpWeight false)
      simp only [latticeEps, kpWeight]
      exact mul_le_mul_of_nonneg_right hε₀' (Real.exp_pos _).le
    | inr ℓ =>
      show ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ latticeEps true * Real.exp (kpWeight true)
      simp only [latticeEps, kpWeight]
      exact hlink ℓ
  have hx0 : ∀ q, 0 ≤ xw D ε₀ η q := by
    intro q; cases q with
    | inl _ => exact mul_nonneg hε₀ (Real.exp_pos _).le
    | inr ℓ => exact sum_nonneg fun S _ => mul_nonneg (hη ℓ S) (Real.exp_pos _).le
  have hθ : ∀ b, 0 ≤ theta₀ b := by intro b; cases b <;> simp [theta₀]
  have hfix := lattice_fix latticeEps (le_refl _) (le_refl _)
  have hR := two_color_root_gf (cadj D adjF) nb hnb (fun q => q.isRight) latticeDeg hdeg
    (xw D ε₀ η) (fun b => latticeEps b * Real.exp (kpWeight b)) theta₀ hx0 hξ hθ hfix
    (ΛF.disjSum ΛL) (rootSet D ΛL x₀)
  have hroot : ∑ r ∈ rootSet D ΛL x₀, theta₀ r.isRight ≤ 1 := by
    rw [rootSet, sum_disjSum]
    simp only [Sum.isRight_inl, Sum.isRight_inr, sum_const, nsmul_eq_mul, card_singleton, Nat.cast_one, one_mul]
    have h4 : ((ΛL.filter (fun ℓ => x₀ ∈ D ℓ)).card : ℝ) ≤ 4 := by exact_mod_cast hfour x₀
    have ht : 0 ≤ theta₀ true := hθ true
    have := lattice_face_total
    nlinarith
  have heq : ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q =
      ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext C; simp only [mem_filter]
  have hE' : ∑ X ∈ 𝒳.filter (fun s => x₀ ∈ id s), |z X| * Real.exp (2 * (id X).card) ≤
      ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q := by
    convert hE
    rfl
  exact le_trans hE' (le_trans (le_of_eq heq) (le_trans hR hroot))

end Site

/-! ## 10. Copy of KPToDobrushin and the link -/

/-- §1: for nonnegative `f`, the sum over polymers meeting support `A` ≤ the sum over sites of `A` of the sum over
polymers containing that site. -/
theorem intersect_sum_le {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S) (V : Finset P) (A : Finset S) (f : P → ℝ)
    (hf : ∀ γ, 0 ≤ f γ) :
    ∑ γ' ∈ V.filter (fun s => (A ∩ supp s).Nonempty), f γ' ≤
      ∑ x ∈ A, ∑ γ' ∈ V.filter (fun s => x ∈ supp s), f γ' := by
  rw [sum_filter]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro γ' _
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    rw [mem_inter] at hx
    have hle : (if x ∈ supp γ' then f γ' else 0) ≤ ∑ y ∈ A, if y ∈ supp γ' then f γ' else 0 :=
      single_le_sum (f := fun y => if y ∈ supp γ' then f γ' else 0)
        (fun y _ => by split_ifs <;> simp [hf]) hx.1
    simpa [hx.2] using hle
  · exact sum_nonneg fun y _ => by split_ifs <;> simp [hf]

/-- §2: the Dobrushin condition from (KP). -/
theorem dobrushin_cond_of_kp {P S : Type*} [DecidableEq P] [DecidableEq S] (supp : P → Finset S) (z : P → ℝ) (U : Finset P)
    (hsize : ∀ γ ∈ U, 1 ≤ (supp γ).card)
    (hsite : ∀ x, ∑ γ' ∈ U.filter (fun s => x ∈ supp s),
      |z γ'| * Real.exp (2 * (supp γ').card) ≤ 1)
    (hsmall : ∀ γ ∈ U, |z γ| * Real.exp (2 * (supp γ).card) ≤ Real.exp 1 - 1) :
    ∀ γ ∈ U, |z γ| ≤
      (1 - Real.exp (-Real.log (1 + |z γ| * Real.exp (2 * (supp γ).card)))) *
        Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
          Real.log (1 + |z γ'| * Real.exp (2 * (supp γ').card))) := by
  intro γ hγ
  set μ : P → ℝ := fun s => |z s| * Real.exp (2 * (supp s).card) with hμ
  have hμ0 : ∀ s, 0 ≤ μ s := fun s => by rw [hμ]; positivity
  set n : ℝ := ((supp γ).card : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hsize γ hγ
  -- Upper bound of the sum: Σ a ≤ Σ μ ≤ n
  have hlog : ∀ s, Real.log (1 + μ s) ≤ μ s := by
    intro s
    have := Real.log_le_sub_one_of_pos (by linarith [hμ0 s] : (0:ℝ) < 1 + μ s)
    linarith
  have hsum1 : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
      Real.log (1 + μ γ') ≤
      ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty), μ γ' :=
    sum_le_sum fun s _ => hlog s
  have hsum2 : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty), μ γ' ≤
      ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' :=
    intersect_sum_le supp (U.erase γ) (supp γ) μ hμ0
  have hsum3 : ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' ≤ n := by
    have : ∀ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ' ≤ 1 := by
      intro x _
      refine le_trans ?_ (hsite x)
      exact sum_le_sum_of_subset_of_nonneg
        (filter_subset_filter _ (erase_subset γ U)) (fun s _ _ => hμ0 s)
    calc ∑ x ∈ supp γ, ∑ γ' ∈ (U.erase γ).filter (fun s => x ∈ supp s), μ γ'
        ≤ ∑ _x ∈ supp γ, (1 : ℝ) := sum_le_sum this
      _ = n := by simp [hn]
  have hSum : ∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
      Real.log (1 + μ γ') ≤ n := by linarith
  -- 1 − e^{−a} = μ/(1+μ)
  have hpos : 0 < 1 + μ γ := by linarith [hμ0 γ]
  have he1 : Real.exp (-Real.log (1 + μ γ)) = 1 / (1 + μ γ) := by
    rw [Real.exp_neg, Real.exp_log hpos, one_div]
  have hfac : 1 - Real.exp (-Real.log (1 + μ γ)) = μ γ / (1 + μ γ) := by
    rw [he1]; field_simp; ring
  -- exp(−Σ) ≥ e^{−n}
  have hexp : Real.exp (-n) ≤ Real.exp (-∑ γ' ∈ (U.erase γ).filter
      (fun s => (supp γ ∩ supp s).Nonempty), Real.log (1 + μ γ')) :=
    Real.exp_le_exp.mpr (by linarith)
  -- 1 + μ ≤ e ≤ e^n
  have hen : 1 + μ γ ≤ Real.exp n := by
    have h1 : 1 + μ γ ≤ Real.exp 1 := by linarith [hsmall γ hγ]
    exact le_trans h1 (Real.exp_le_exp.mpr hn1)
  show |z γ| ≤ (1 - Real.exp (-Real.log (1 + μ γ))) *
      Real.exp (-∑ γ' ∈ (U.erase γ).filter (fun s => (supp γ ∩ supp s).Nonempty),
        Real.log (1 + μ γ'))
  rw [hfac]
  have hz0 : 0 ≤ |z γ| := abs_nonneg _
  have hμdef : μ γ = |z γ| * Real.exp (2 * n) := by rw [hμ, hn]
  have key : |z γ| ≤ μ γ / (1 + μ γ) * Real.exp (-n) := by
    rw [hμdef, div_mul_eq_mul_div, le_div_iff₀ (by rw [← hμdef]; exact hpos)]
    have h2 : Real.exp (2 * n) * Real.exp (-n) = Real.exp n := by
      rw [← Real.exp_add]; ring_nf
    have : |z γ| * (1 + |z γ| * Real.exp (2 * n)) ≤ |z γ| * Real.exp n := by
      rw [← hμdef]; exact mul_le_mul_of_nonneg_left hen hz0
    calc |z γ| * (1 + |z γ| * Real.exp (2 * n)) ≤ |z γ| * Real.exp n := this
      _ = |z γ| * Real.exp (2 * n) * Real.exp (-n) := by rw [mul_assoc, h2]
  calc |z γ| ≤ μ γ / (1 + μ γ) * Real.exp (-n) := key
    _ ≤ μ γ / (1 + μ γ) * Real.exp (-∑ γ' ∈ (U.erase γ).filter
        (fun s => (supp γ ∩ supp s).Nonempty), Real.log (1 + μ γ')) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg (hμ0 γ) hpos.le)


/-- **Link**: under the hypotheses of encoded_kp_site, the Dobrushin condition (the `hcond` expression of PolymerGasDobrushin,
supp = id) holds for each X in 𝒳. Extra hypotheses: X is nonempty and |z(X)|e^{2|X|} ≤ e − 1. -/
theorem encoded_dobrushin {F L : Type*} [DecidableEq F] [DecidableEq L]
    (D : L → Finset F) (adjF : F → F → Prop) (ΛF : Finset F) (ΛL : Finset L)
    (m : ℕ) (hm : 1 ≤ m) (𝒳 : Finset (Finset F))
    (h𝒳 : ∀ X ∈ 𝒳, X ⊆ ΛF ∧ IsConnectedSet adjF X)
    (z : Finset F → ℝ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 2.5e-3)
    (η : L → Finset F → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hlink : ∀ ℓ, ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ 1.5e-11 * Real.exp 12)
    (hz : ∀ X ∈ 𝒳, |z X| ≤ (∏ _p ∈ thin D ΛL m X, ε₀) * ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ))
    (nb : F ⊕ L → Finset (F ⊕ L)) (hnb : ∀ p q, p ≠ q → cadj D adjF p q → q ∈ nb p)
    (hdeg : ∀ p b, ((nb p).filter (fun q => q.isRight = b)).card ≤ latticeDeg p.isRight b)
    (hfour : ∀ x : F, (ΛL.filter (fun ℓ => x ∈ D ℓ)).card ≤ 4)
    (hsize : ∀ X ∈ 𝒳, 1 ≤ (id X).card)
    (hsmall : ∀ X ∈ 𝒳, |z X| * Real.exp (2 * (id X).card) ≤ Real.exp 1 - 1) :
    ∀ X ∈ 𝒳, |z X| ≤
      (1 - Real.exp (-Real.log (1 + |z X| * Real.exp (2 * (id X).card)))) *
        Real.exp (-∑ γ' ∈ (𝒳.erase X).filter (fun s => (id X ∩ id s).Nonempty),
          Real.log (1 + |z γ'| * Real.exp (2 * (id γ').card))) :=
  dobrushin_cond_of_kp id z 𝒳 hsize
    (encoded_kp_site D adjF ΛF ΛL m hm 𝒳 h𝒳 z ε₀ hε₀ hε₀' η hη hlink hz nb hnb hdeg hfour) hsmall


/-! ## 11. ℤ⁴ types -/

open Finset

abbrev Pt := Fin 4 → ℤ
abbrev Face := Pt × Fin 6
abbrev Link := Pt × Fin 4

def e (μ : Fin 4) : Pt := fun i => if i = μ then 1 else 0

/-- Plaquettes k = 0..5 lie in the planes (0,1),(0,2),(0,3),(1,2),(1,3),(2,3). The 4 links of plaquette k at the origin. -/
def links0 : Fin 6 → Finset Link
  | 0 => {(0, 0), (e 0, 1), (e 1, 0), (0, 1)}
  | 1 => {(0, 0), (e 0, 2), (e 2, 0), (0, 2)}
  | 2 => {(0, 0), (e 0, 3), (e 3, 0), (0, 3)}
  | 3 => {(0, 1), (e 1, 2), (e 2, 1), (0, 2)}
  | 4 => {(0, 1), (e 1, 3), (e 3, 1), (0, 3)}
  | 5 => {(0, 2), (e 2, 3), (e 3, 2), (0, 3)}

/-- The 6 plaquettes containing the link μ at the origin. -/
def faces0 : Fin 4 → Finset Face
  | 0 => {(0, 0), (-e 1, 0), (0, 1), (-e 2, 1), (0, 2), (-e 3, 2)}
  | 1 => {(0, 0), (-e 0, 0), (0, 3), (-e 2, 3), (0, 4), (-e 3, 4)}
  | 2 => {(0, 1), (-e 0, 1), (0, 3), (-e 1, 3), (0, 5), (-e 3, 5)}
  | 3 => {(0, 2), (-e 0, 2), (0, 4), (-e 1, 4), (0, 5), (-e 2, 5)}

theorem key0 (z : Pt) (k : Fin 6) (μ : Fin 4) : (z, k) ∈ faces0 μ ↔ (-z, μ) ∈ links0 k := by
  fin_cases k <;> fin_cases μ <;> simp [faces0, links0, neg_eq_iff_eq_neg] <;> tauto


/-- Translation. -/
def tF (x : Pt) : Face ↪ Face := ⟨fun f => (x + f.1, f.2), fun a b h => by
  simp only [Prod.mk.injEq, add_right_inj] at h; exact Prod.ext h.1 h.2⟩
def tL (x : Pt) : Link ↪ Link := ⟨fun f => (x + f.1, f.2), fun a b h => by
  simp only [Prod.mk.injEq, add_right_inj] at h; exact Prod.ext h.1 h.2⟩

/-- The 4 links of plaquette f, and the 6 plaquettes containing link ℓ. -/
def linksOf (f : Face) : Finset Link := (links0 f.2).map (tL f.1)
def facesOf (ℓ : Link) : Finset Face := (faces0 ℓ.2).map (tF ℓ.1)

@[simp] theorem tF_apply (x : Pt) (f : Face) : tF x f = (x + f.1, f.2) := rfl
@[simp] theorem tL_apply (x : Pt) (f : Link) : tL x f = (x + f.1, f.2) := rfl

theorem mem_map_tF {s : Finset Face} {x : Pt} {g : Face} : g ∈ s.map (tF x) ↔ (g.1 - x, g.2) ∈ s := by
  constructor
  · intro h; obtain ⟨a, ha, rfl⟩ := mem_map.mp h; simpa using ha
  · intro h; exact mem_map.mpr ⟨_, h, by simp⟩
theorem mem_map_tL {s : Finset Link} {x : Pt} {g : Link} : g ∈ s.map (tL x) ↔ (g.1 - x, g.2) ∈ s := by
  constructor
  · intro h; obtain ⟨a, ha, rfl⟩ := mem_map.mp h; simpa using ha
  · intro h; exact mem_map.mpr ⟨_, h, by simp⟩

theorem mem_linksOf {ℓ : Link} {f : Face} : ℓ ∈ linksOf f ↔ (ℓ.1 - f.1, ℓ.2) ∈ links0 f.2 := mem_map_tL
theorem mem_facesOf {f : Face} {ℓ : Link} : f ∈ facesOf ℓ ↔ (f.1 - ℓ.1, f.2) ∈ faces0 ℓ.2 := mem_map_tF

/-- **A plaquette contains a link ⇔ the link is one of its 4 links**. -/
theorem mem_facesOf_iff (f : Face) (ℓ : Link) : f ∈ facesOf ℓ ↔ ℓ ∈ linksOf f := by
  rw [mem_facesOf, mem_linksOf, key0]; simp

/-- Plaquette adjacency: a different plaquette sharing one link. -/
def faceAdj (f g : Face) : Prop := f ≠ g ∧ ∃ ℓ, f ∈ facesOf ℓ ∧ g ∈ facesOf ℓ

def nbFF0 (k : Fin 6) : Finset Face := ((links0 k).biUnion facesOf).erase (0, k)
def nbFF (f : Face) : Finset Face := (nbFF0 f.2).map (tF f.1)

theorem adj_mem_nbFF {f g : Face} (h : faceAdj f g) : g ∈ nbFF f := by
  obtain ⟨hne, ℓ, hf, hg⟩ := h
  rw [nbFF, mem_map_tF, nbFF0, mem_erase]
  refine ⟨fun h => hne ?_, mem_biUnion.mpr ⟨(ℓ.1 - f.1, ℓ.2), ?_, ?_⟩⟩
  · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [sub_eq_zero] at h1 h2; exact (Prod.ext h1 h2).symm
  · exact mem_linksOf.mp ((mem_facesOf_iff f ℓ).mp hf)
  · rw [mem_facesOf]; have := mem_facesOf.mp hg; simpa using this

def nbFL0 (k : Fin 6) : Finset Link := ((nbFF0 k).biUnion linksOf).filter (fun ℓ => ((0 : Pt), k) ∉ facesOf ℓ)
def nbFL (f : Face) : Finset Link := (nbFL0 f.2).map (tL f.1)
def nbLF0 (μ : Fin 4) : Finset Face := ((faces0 μ).biUnion nbFF) \ faces0 μ
def nbLF (ℓ : Link) : Finset Face := (nbLF0 ℓ.2).map (tF ℓ.1)
def nbLL0 (μ : Fin 4) : Finset Link := ((faces0 μ ∪ (faces0 μ).biUnion nbFF).biUnion linksOf).erase (0, μ)
def nbLL (ℓ : Link) : Finset Link := (nbLL0 ℓ.2).map (tL ℓ.1)

theorem mem_nbFF {f g : Face} : g ∈ nbFF f ↔ (g.1 - f.1, g.2) ∈ nbFF0 f.2 := mem_map_tF

/-- Translation invariance of adjacency (pull-back to the origin). -/
theorem adjF_shift {f g : Face} (x : Pt) (h : faceAdj f g) : faceAdj (f.1 - x, f.2) (g.1 - x, g.2) := by
  obtain ⟨hne, ℓ, hf, hg⟩ := h
  refine ⟨fun h => hne ?_, (ℓ.1 - x, ℓ.2), ?_, ?_⟩
  · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [sub_left_inj] at h1; exact Prod.ext h1 h2
  · rw [mem_facesOf]; simpa using mem_facesOf.mp hf
  · rw [mem_facesOf]; simpa using mem_facesOf.mp hg

theorem fl_mem {f : Face} {ℓ : Link} (hf : f ∉ facesOf ℓ) {q : Face} (hq : q ∈ facesOf ℓ) (hfq : faceAdj f q) :
    ℓ ∈ nbFL f := by
  rw [nbFL, mem_map_tL, nbFL0, mem_filter, mem_biUnion]
  refine ⟨⟨(q.1 - f.1, q.2), ?_, ?_⟩, ?_⟩
  · have := adj_mem_nbFF (adjF_shift f.1 hfq)
    rw [mem_nbFF] at this; simpa using this
  · rw [← mem_facesOf_iff, mem_facesOf]; have := mem_facesOf.mp hq; simpa using this
  · rw [mem_facesOf]; intro h; apply hf; rw [mem_facesOf]; simpa using h

theorem lf_mem {ℓ : Link} {p : Face} (hp : p ∉ facesOf ℓ) {q : Face} (hq : q ∈ facesOf ℓ) (hqp : faceAdj q p) :
    p ∈ nbLF ℓ := by
  rw [nbLF, mem_map_tF, nbLF0, mem_sdiff, mem_biUnion]
  refine ⟨⟨(q.1 - ℓ.1, q.2), mem_facesOf.mp hq, ?_⟩, ?_⟩
  · have := adj_mem_nbFF (adjF_shift ℓ.1 hqp); simpa using this
  · intro h; apply hp; rw [mem_facesOf]; exact h

theorem ll_mem {ℓ ℓ' : Link} (hne : ℓ ≠ ℓ') {p q : Face} (hp : p ∈ facesOf ℓ) (hq : q ∈ facesOf ℓ')
    (h : p = q ∨ faceAdj p q) : ℓ' ∈ nbLL ℓ := by
  rw [nbLL, mem_map_tL, nbLL0, mem_erase]
  refine ⟨fun h => hne ?_, mem_biUnion.mpr ⟨(q.1 - ℓ.1, q.2), ?_, ?_⟩⟩
  · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [sub_eq_zero] at h1; exact (Prod.ext h1 h2).symm
  · rcases h with h | hpq
    · subst h; exact mem_union_left _ (mem_facesOf.mp hp)
    · refine mem_union_right _ (mem_biUnion.mpr ⟨(p.1 - ℓ.1, p.2), mem_facesOf.mp hp, ?_⟩)
      have := adj_mem_nbFF (adjF_shift ℓ.1 hpq); simpa using this
  · rw [← mem_facesOf_iff, mem_facesOf]; have := mem_facesOf.mp ((mem_facesOf_iff q ℓ').mpr ((mem_facesOf_iff q ℓ').mp hq)); simpa using this

theorem card_links0 : ∀ k, (links0 k).card = 4 := by decide +kernel

/-! ## 12. Plaquette adjacency with cube-opposite plaquettes added (Δ = 24) -/

/-- For plaquette k at the origin, the parallel plaquettes shifted by ±1 in the two directions perpendicular to its plane (cube-opposite, 4 of them). -/
def cubeOpp0 : Fin 6 → Finset Face
  | 0 => {(e 2, 0), (-e 2, 0), (e 3, 0), (-e 3, 0)}
  | 1 => {(e 1, 1), (-e 1, 1), (e 3, 1), (-e 3, 1)}
  | 2 => {(e 1, 2), (-e 1, 2), (e 2, 2), (-e 2, 2)}
  | 3 => {(e 0, 3), (-e 0, 3), (e 3, 3), (-e 3, 3)}
  | 4 => {(e 0, 4), (-e 0, 4), (e 2, 4), (-e 2, 4)}
  | 5 => {(e 0, 5), (-e 0, 5), (e 1, 5), (-e 1, 5)}

/-- Plaquette adjacency (Δ = 24): sharing a link, or opposite in a cube. -/
def faceAdj24 (f g : Face) : Prop := faceAdj f g ∨ (g.1 - f.1, g.2) ∈ cubeOpp0 f.2

def nbFF24_0 (k : Fin 6) : Finset Face := nbFF0 k ∪ cubeOpp0 k
def nbFF24 (f : Face) : Finset Face := (nbFF24_0 f.2).map (tF f.1)

theorem adj24_mem {f g : Face} (h : faceAdj24 f g) : g ∈ nbFF24 f := by
  rw [nbFF24, mem_map_tF, nbFF24_0, mem_union]
  rcases h with h | h
  · exact Or.inl (mem_nbFF.mp (adj_mem_nbFF h))
  · exact Or.inr h

theorem adj24_shift {f g : Face} (x : Pt) (h : faceAdj24 f g) : faceAdj24 (f.1 - x, f.2) (g.1 - x, g.2) := by
  rcases h with h | h
  · exact Or.inl (adjF_shift x h)
  · right; simpa using h

def nbFL24_0 (k : Fin 6) : Finset Link :=
  ((nbFF24_0 k).biUnion linksOf).filter (fun ℓ => ((0 : Pt), k) ∉ facesOf ℓ)
def nbFL24 (f : Face) : Finset Link := (nbFL24_0 f.2).map (tL f.1)
def nbLF24_0 (μ : Fin 4) : Finset Face := ((faces0 μ).biUnion nbFF24) \ faces0 μ
def nbLF24 (ℓ : Link) : Finset Face := (nbLF24_0 ℓ.2).map (tF ℓ.1)
def nbLL24_0 (μ : Fin 4) : Finset Link :=
  ((faces0 μ ∪ (faces0 μ).biUnion nbFF24).biUnion linksOf).erase (0, μ)
def nbLL24 (ℓ : Link) : Finset Link := (nbLL24_0 ℓ.2).map (tL ℓ.1)

theorem mem_nbFF24 {f g : Face} : g ∈ nbFF24 f ↔ (g.1 - f.1, g.2) ∈ nbFF24_0 f.2 := mem_map_tF

theorem fl24_mem {f : Face} {ℓ : Link} (hf : f ∉ facesOf ℓ) {q : Face} (hq : q ∈ facesOf ℓ)
    (hfq : faceAdj24 f q) : ℓ ∈ nbFL24 f := by
  rw [nbFL24, mem_map_tL, nbFL24_0, mem_filter, mem_biUnion]
  refine ⟨⟨(q.1 - f.1, q.2), ?_, ?_⟩, ?_⟩
  · have := adj24_mem (adj24_shift f.1 hfq)
    rw [mem_nbFF24] at this; simpa using this
  · rw [← mem_facesOf_iff, mem_facesOf]; have := mem_facesOf.mp hq; simpa using this
  · rw [mem_facesOf]; intro h; apply hf; rw [mem_facesOf]; simpa using h

theorem lf24_mem {ℓ : Link} {p : Face} (hp : p ∉ facesOf ℓ) {q : Face} (hq : q ∈ facesOf ℓ)
    (hqp : faceAdj24 q p) : p ∈ nbLF24 ℓ := by
  rw [nbLF24, mem_map_tF, nbLF24_0, mem_sdiff, mem_biUnion]
  refine ⟨⟨(q.1 - ℓ.1, q.2), mem_facesOf.mp hq, ?_⟩, ?_⟩
  · have := adj24_mem (adj24_shift ℓ.1 hqp); simpa using this
  · intro h; apply hp; rw [mem_facesOf]; exact h

theorem ll24_mem {ℓ ℓ' : Link} (hne : ℓ ≠ ℓ') {p q : Face} (hp : p ∈ facesOf ℓ) (hq : q ∈ facesOf ℓ')
    (h : p = q ∨ faceAdj24 p q) : ℓ' ∈ nbLL24 ℓ := by
  rw [nbLL24, mem_map_tL, nbLL24_0, mem_erase]
  refine ⟨fun h => hne ?_, mem_biUnion.mpr ⟨(q.1 - ℓ.1, q.2), ?_, ?_⟩⟩
  · have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h
    simp only [sub_eq_zero] at h1; exact (Prod.ext h1 h2).symm
  · rcases h with h | hpq
    · subst h; exact mem_union_left _ (mem_facesOf.mp hp)
    · refine mem_union_right _ (mem_biUnion.mpr ⟨(p.1 - ℓ.1, p.2), mem_facesOf.mp hp, ?_⟩)
      have := adj24_mem (adj24_shift ℓ.1 hpq); simpa using this
  · rw [← mem_facesOf_iff, mem_facesOf]
    have := mem_facesOf.mp ((mem_facesOf_iff q ℓ').mpr ((mem_facesOf_iff q ℓ').mp hq)); simpa using this

theorem card_nbFF24_0 : ∀ k, (nbFF24_0 k).card = 24 := by decide +kernel
theorem card_nbFL24_0 : ∀ k, (nbFL24_0 k).card = 44 := by decide +kernel
theorem card_nbLF24_0 : ∀ μ, (nbLF24_0 μ).card = 66 := by decide +kernel
theorem card_nbLL24_0 : ∀ μ, (nbLL24_0 μ).card = 122 := by decide +kernel

def nbC24 : Face ⊕ Link → Finset (Face ⊕ Link)
  | Sum.inl f => (nbFF24 f).disjSum (nbFL24 f)
  | Sum.inr ℓ => (nbLF24 ℓ).disjSum (nbLL24 ℓ)

theorem lattice24_hnb : ∀ p q, p ≠ q → cadj facesOf faceAdj24 p q → q ∈ nbC24 p := by
  intro p q hpq h
  rcases p with f | ℓ <;> rcases q with g | ℓ'
  · exact inl_mem_disjSum.mpr (adj24_mem h)
  · obtain ⟨hf, q, hq, hfq⟩ := h
    exact inr_mem_disjSum.mpr (fl24_mem hf hq hfq)
  · obtain ⟨hp, q, hq, hqp⟩ := h
    exact inl_mem_disjSum.mpr (lf24_mem hp hq hqp)
  · obtain ⟨p, hp, q, hq, h⟩ := h
    exact inr_mem_disjSum.mpr (ll24_mem (fun h' => hpq (by rw [h'])) hp hq h)

theorem filter_disjSum_left {α β : Type*} (s : Finset α) (t : Finset β) :
    ((s.disjSum t).filter (fun q => q.isRight = false)).card = s.card := by
  have : (s.disjSum t).filter (fun q => q.isRight = false) = s.map Function.Embedding.inl := by
    ext q; cases q <;> simp
  rw [this, card_map]

theorem filter_disjSum_right {α β : Type*} (s : Finset α) (t : Finset β) :
    ((s.disjSum t).filter (fun q => q.isRight = true)).card = t.card := by
  have : (s.disjSum t).filter (fun q => q.isRight = true) = t.map Function.Embedding.inr := by
    ext q; cases q <;> simp
  rw [this, card_map]

/-- Lattice degrees for Δ = 24 (plaquette→plaquette 24, plaquette→defect ≤ 48 (actually 44), defect→plaquette ≤ 72 (66), defect→defect 122). -/
def latticeDeg24 : Bool → Bool → ℕ
  | false, false => 24
  | false, true => 48
  | true, false => 72
  | true, true => 122

theorem lattice24_hdeg : ∀ p b, ((nbC24 p).filter (fun q => q.isRight = b)).card ≤ latticeDeg24 p.isRight b := by
  intro p b
  rcases p with f | ℓ <;> cases b
  · rw [nbC24, filter_disjSum_left, nbFF24, card_map, card_nbFF24_0]; simp [latticeDeg24]
  · rw [nbC24, filter_disjSum_right, nbFL24, card_map, card_nbFL24_0]; simp [latticeDeg24]
  · rw [nbC24, filter_disjSum_left, nbLF24, card_map, card_nbLF24_0]; simp [latticeDeg24]
  · rw [nbC24, filter_disjSum_right, nbLL24, card_map, card_nbLL24_0]; simp [latticeDeg24]

theorem lattice_hfour (ΛL : Finset Link) : ∀ x : Face, (ΛL.filter (fun ℓ => x ∈ facesOf ℓ)).card ≤ 4 := by
  intro x
  have hsub : ΛL.filter (fun ℓ => x ∈ facesOf ℓ) ⊆ linksOf x := by
    intro ℓ hℓ; exact (mem_facesOf_iff x ℓ).mp (mem_filter.mp hℓ).2
  calc _ ≤ (linksOf x).card := card_le_card hsub
    _ = 4 := by rw [linksOf, card_map, card_links0]

noncomputable def theta24 : Bool → ℝ
  | false => 1 / 23
  | true => 1 / 10000

noncomputable def latticeEps24 : Bool → ℝ
  | false => 2.1e-3
  | true => 1.5e-11

/-- **Numerical condition for Δ = 24**: thin plaquette ε ≤ 2.1·10⁻³, defect ε ≤ 1.5·10⁻¹¹, θ = (1/23, 10⁻⁴). -/
theorem lattice24_fix (ε : Bool → ℝ) (hthin : ε false ≤ 2.1e-3) (hL : ε true ≤ 1.5e-11) :
    ∀ b, ε b * Real.exp (kpWeight b) * (1 + theta24 false) ^ latticeDeg24 b false *
      (1 + theta24 true) ^ latticeDeg24 b true ≤ theta24 b := by
  intro b
  cases b
  · have he : Real.exp (kpWeight false) ≤ (2.7182818286 : ℝ) ^ 2 := by
      have := exp_nat_le 2; simpa [kpWeight] using this
    simp only [latticeDeg24, theta24]
    have hpos : (0 : ℝ) ≤ (1 + 1 / 23) ^ 24 * (1 + 1 / 10000) ^ 48 := by positivity
    calc ε false * Real.exp (kpWeight false) * (1 + 1 / 23) ^ 24 * (1 + 1 / 10000) ^ 48
        = ε false * Real.exp (kpWeight false) * ((1 + 1 / 23) ^ 24 * (1 + 1 / 10000) ^ 48) := by ring
      _ ≤ 2.1e-3 * (2.7182818286 : ℝ) ^ 2 * ((1 + 1 / 23) ^ 24 * (1 + 1 / 10000) ^ 48) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          exact mul_le_mul hthin he (Real.exp_pos _).le (by norm_num)
      _ ≤ 1 / 23 := by norm_num
  · have he : Real.exp (kpWeight true) ≤ (2.7182818286 : ℝ) ^ 12 := by
      have := exp_nat_le 12; simpa [kpWeight] using this
    simp only [latticeDeg24, theta24]
    have hpos : (0 : ℝ) ≤ (1 + 1 / 23) ^ 72 * (1 + 1 / 10000) ^ 122 := by positivity
    calc ε true * Real.exp (kpWeight true) * (1 + 1 / 23) ^ 72 * (1 + 1 / 10000) ^ 122
        = ε true * Real.exp (kpWeight true) * ((1 + 1 / 23) ^ 72 * (1 + 1 / 10000) ^ 122) := by ring
      _ ≤ 1.5e-11 * (2.7182818286 : ℝ) ^ 12 * ((1 + 1 / 23) ^ 72 * (1 + 1 / 10000) ^ 122) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          exact mul_le_mul hL he (Real.exp_pos _).le (by norm_num)
      _ ≤ 1 / 10000 := by norm_num

theorem lattice24_face_total : theta24 false + 4 * theta24 true ≤ 1 := by
  simp only [theta24]; norm_num

section Site24
variable {F L : Type*} [DecidableEq F] [DecidableEq L]
theorem encoded_kp_site24 (D : L → Finset F) (adjF : F → F → Prop) (ΛF : Finset F) (ΛL : Finset L)
    (m : ℕ) (hm : 1 ≤ m) (𝒳 : Finset (Finset F))
    (h𝒳 : ∀ X ∈ 𝒳, X ⊆ ΛF ∧ IsConnectedSet adjF X)
    (z : Finset F → ℝ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 2.1e-3)
    (η : L → Finset F → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hlink : ∀ ℓ, ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ 1.5e-11 * Real.exp 12)
    (hz : ∀ X ∈ 𝒳, |z X| ≤ (∏ _p ∈ thin D ΛL m X, ε₀) * ∏ ℓ ∈ defects D ΛL m X, η ℓ (X ∩ D ℓ))
    (nb : F ⊕ L → Finset (F ⊕ L)) (hnb : ∀ p q, p ≠ q → cadj D adjF p q → q ∈ nb p)
    (hdeg : ∀ p b, ((nb p).filter (fun q => q.isRight = b)).card ≤ latticeDeg24 p.isRight b)
    (hfour : ∀ x : F, (ΛL.filter (fun ℓ => x ∈ D ℓ)).card ≤ 4) :
    ∀ x : F, ∑ X ∈ 𝒳.filter (fun s => x ∈ id s), |z X| * Real.exp (2 * (id X).card) ≤ 1 := by
  intro x₀
  have hsub : ∀ X ∈ 𝒳.filter (fun s => x₀ ∈ id s), X ⊆ ΛF ∧ IsConnectedSet adjF X :=
    fun X hX => h𝒳 X (mem_filter.mp hX).1
  have hE := encoded_sum_le D adjF ΛF ΛL m hm (𝒳.filter (fun s => x₀ ∈ id s)) hsub z ε₀ hε₀ η hη
    (fun X hX => hz X (mem_filter.mp hX).1) (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty)
    (fun X hX => enc_meets_root D ΛL m X (mem_filter.mp hX).2)
  have hξ : ∀ q, xw D ε₀ η q ≤ (fun b => latticeEps24 b * Real.exp (kpWeight b)) q.isRight := by
    intro q; cases q with
    | inl _ =>
      show ε₀ * Real.exp 2 ≤ latticeEps24 false * Real.exp (kpWeight false)
      simp only [latticeEps24, kpWeight]
      exact mul_le_mul_of_nonneg_right hε₀' (Real.exp_pos _).le
    | inr ℓ =>
      show ∑ S ∈ (D ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ latticeEps24 true * Real.exp (kpWeight true)
      simp only [latticeEps24, kpWeight]
      exact hlink ℓ
  have hx0 : ∀ q, 0 ≤ xw D ε₀ η q := by
    intro q; cases q with
    | inl _ => exact mul_nonneg hε₀ (Real.exp_pos _).le
    | inr ℓ => exact sum_nonneg fun S _ => mul_nonneg (hη ℓ S) (Real.exp_pos _).le
  have hθ : ∀ b, 0 ≤ theta24 b := by intro b; cases b <;> simp [theta24]
  have hfix := lattice24_fix latticeEps24 (le_refl _) (le_refl _)
  have hR := two_color_root_gf (cadj D adjF) nb hnb (fun q => q.isRight) latticeDeg24 hdeg
    (xw D ε₀ η) (fun b => latticeEps24 b * Real.exp (kpWeight b)) theta24 hx0 hξ hθ hfix
    (ΛF.disjSum ΛL) (rootSet D ΛL x₀)
  have hroot : ∑ r ∈ rootSet D ΛL x₀, theta24 r.isRight ≤ 1 := by
    rw [rootSet, sum_disjSum]
    simp only [Sum.isRight_inl, Sum.isRight_inr, sum_const, nsmul_eq_mul, card_singleton, Nat.cast_one, one_mul]
    have h4 : ((ΛL.filter (fun ℓ => x₀ ∈ D ℓ)).card : ℝ) ≤ 4 := by exact_mod_cast hfour x₀
    have ht : 0 ≤ theta24 true := hθ true
    have := lattice24_face_total
    nlinarith
  have heq : ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q =
      ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext C; simp only [mem_filter]
  have hE' : ∑ X ∈ 𝒳.filter (fun s => x₀ ∈ id s), |z X| * Real.exp (2 * (id X).card) ≤
      ∑ C ∈ (ΛF.disjSum ΛL).powerset.filter
        (fun C => (rootSet D ΛL x₀ ∩ C).Nonempty ∧ IsConnectedSet (cadj D adjF) C), ∏ q ∈ C, xw D ε₀ η q := by
    convert hE
    rfl
  exact le_trans hE' (le_trans (le_of_eq heq) (le_trans hR hroot))

end Site24

/-- **Per-plaquette KP sum on ℤ⁴, Δ = 24**: the only hypotheses are hz and the label sum (thin plaquette ε₀ ≤ 2.1·10⁻³). -/
theorem lattice_kp_site24 (ΛF : Finset Face) (ΛL : Finset Link) (m : ℕ) (hm : 1 ≤ m)
    (𝒳 : Finset (Finset Face)) (h𝒳 : ∀ X ∈ 𝒳, X ⊆ ΛF ∧ IsConnectedSet faceAdj24 X)
    (z : Finset Face → ℝ) (ε₀ : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 2.1e-3)
    (η : Link → Finset Face → ℝ) (hη : ∀ ℓ S, 0 ≤ η ℓ S)
    (hlink : ∀ ℓ, ∑ S ∈ (facesOf ℓ).powerset, η ℓ S * Real.exp (2 * S.card) ≤ 1.5e-11 * Real.exp 12)
    (hz : ∀ X ∈ 𝒳, |z X| ≤ (∏ _p ∈ thin facesOf ΛL m X, ε₀) *
      ∏ ℓ ∈ defects facesOf ΛL m X, η ℓ (X ∩ facesOf ℓ)) :
    ∀ x : Face, ∑ X ∈ 𝒳.filter (fun s => x ∈ id s), |z X| * Real.exp (2 * (id X).card) ≤ 1 :=
  encoded_kp_site24 facesOf faceAdj24 ΛF ΛL m hm 𝒳 h𝒳 z ε₀ hε₀ hε₀' η hη hlink hz nbC24 lattice24_hnb
    lattice24_hdeg (lattice_hfour ΛL)

/-- `(1+θ)^n ≥ 1 + nθ + n(n−1)/2·θ²` (θ ≥ 0). -/
theorem quad_le_pow (θ : ℝ) (hθ : 0 ≤ θ) : ∀ n : ℕ,
    1 + n * θ + (n * (n - 1) / 2) * θ ^ 2 ≤ (1 + θ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ 1 + θ := by linarith
    have h2 := mul_le_mul_of_nonneg_right ih h1
    have h3 : 0 ≤ (n * (n - 1) / 2 : ℝ) * θ ^ 3 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        have : 0 ≤ (n : ℝ) - 1 := by linarith
        positivity
    have e : (1 + (n : ℝ) * θ + (n * (n - 1) / 2) * θ ^ 2) * (1 + θ) =
        1 + ((n : ℝ) + 1) * θ + (((n : ℝ) + 1) * ((n : ℝ) + 1 - 1) / 2) * θ ^ 2 + (n * (n - 1) / 2) * θ ^ 3 := by
      ring
    rw [pow_succ (1 + θ) n]
    push_cast
    linarith

theorem exp_two_gt : (7.389 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]; nlinarith



/-- **Δ = 24 threshold check (lower side)**: if the thin-plaquette activity is ≥ 2.5·10⁻³ (for the measured maximal shape, y_h ≤ 6.66),
the Δ = 24 thin-plaquette condition fails for every slope θ₀, θ₁ ≥ 0. -/
theorem face24_fails (εt θ₀ θ₁ : ℝ) (hε : 2.5e-3 ≤ εt) (h0 : 0 ≤ θ₀) (h1 : 0 ≤ θ₁) :
    θ₀ < εt * Real.exp 2 * (1 + θ₀) ^ 24 * (1 + θ₁) ^ 48 := by
  have hq := quad_le_pow θ₀ h0 24
  have hN : (1 : ℝ) + ((24 : ℕ) : ℝ) * θ₀ + (((24 : ℕ) : ℝ) * (((24 : ℕ) : ℝ) - 1) / 2) * θ₀ ^ 2 =
      1 + 24 * θ₀ + 276 * θ₀ ^ 2 := by norm_num
  rw [hN] at hq
  have hp1 : 1 ≤ (1 + θ₁) ^ 48 := one_le_pow₀ (by linarith)
  have he := exp_two_gt
  have ha' : 0.0184 ≤ εt * Real.exp 2 := by nlinarith [Real.exp_pos 2]
  generalize hP : (1 + θ₀) ^ 24 = P at hq ⊢
  generalize hQ : (1 + θ₁) ^ 48 = Q at hp1 ⊢
  generalize hA : εt * Real.exp 2 = a at ha' ⊢
  have hquad : θ₀ < 0.0184 * (1 + 24 * θ₀ + 276 * θ₀ ^ 2) := by nlinarith [sq_nonneg (θ₀ - 0.055)]
  have hpoly : 0 ≤ 1 + 24 * θ₀ + 276 * θ₀ ^ 2 := by positivity
  have h1' : 0.0184 * (1 + 24 * θ₀ + 276 * θ₀ ^ 2) ≤ a * P :=
    mul_le_mul ha' hq hpoly (by linarith)
  have hAP : 0 ≤ a * P := le_trans (mul_nonneg (by norm_num) hpoly) h1'
  have h2' : a * P ≤ a * P * Q := le_mul_of_one_le_right hAP hp1
  linarith

/-- **Δ = 24 threshold check (upper side)**: the activity 2.0·10⁻³ at y = 6.85 for the measured maximal shape lies within the lattice24_fix bound 2.1·10⁻³. -/
theorem face24_holds_685 : (2.0e-3 : ℝ) ≤ 2.1e-3 := by norm_num


#print axioms conn_erase
#print axioms rooted_erase
#print axioms rooted_of_connected
#print axioms Wg_step
#print axioms prod_mono_of_one_le
#print axioms Wg_le
#print axioms point_gf_le_weighted
#print axioms prod_by_color
#print axioms two_color_Wg_le
#print axioms two_color_point_sum
#print axioms two_color_root_set_sum
#print axioms one_add_pow_le_exp
#print axioms fix_of_exp
#print axioms exp_one_le
#print axioms exp_nat_le
#print axioms lattice_fix
#print axioms lattice_face_total
#print axioms lattice_two_color_kp
#print axioms sum_le_of_injOn
#print axioms label_sum_le
#print axioms img_spec
#print axioms img_mem
#print axioms img_adj
#print axioms enc_connected
#print axioms decode
#print axioms enc_eq
#print axioms thin_disjoint
#print axioms card_le_enc
#print axioms weight_le_G
#print axioms encoded_sum_le
#print axioms enc_meets_root
#print axioms two_color_point_gf
#print axioms two_color_root_gf
#print axioms encoded_kp_site
#print axioms intersect_sum_le
#print axioms dobrushin_cond_of_kp
#print axioms encoded_dobrushin
#print axioms key0
#print axioms mem_map_tF
#print axioms mem_map_tL
#print axioms mem_linksOf
#print axioms mem_facesOf
#print axioms mem_facesOf_iff
#print axioms adj_mem_nbFF
#print axioms mem_nbFF
#print axioms adjF_shift
#print axioms fl_mem
#print axioms lf_mem
#print axioms ll_mem
#print axioms card_links0
#print axioms adj24_mem
#print axioms adj24_shift
#print axioms mem_nbFF24
#print axioms fl24_mem
#print axioms lf24_mem
#print axioms ll24_mem
#print axioms card_nbFF24_0
#print axioms card_nbFL24_0
#print axioms card_nbLF24_0
#print axioms card_nbLL24_0
#print axioms lattice24_hnb
#print axioms filter_disjSum_left
#print axioms filter_disjSum_right
#print axioms lattice24_hdeg
#print axioms lattice_hfour
#print axioms lattice24_fix
#print axioms lattice24_face_total
#print axioms encoded_kp_site24
#print axioms lattice_kp_site24
#print axioms quad_le_pow
#print axioms exp_two_gt
#print axioms face24_fails
#print axioms face24_holds_685

end Lattice24KP
