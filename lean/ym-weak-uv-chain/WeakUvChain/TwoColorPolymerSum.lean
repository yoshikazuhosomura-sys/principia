/-
Per-site sum over two-colour connected sets (Kotecký–Preiss type). Single file; checks with `import Mathlib` only.

  Point type P, adjacency adj (symmetry not used), point weights x : P → ℝ (≥ 0).
  §1 Paths, connectedness, rooted sets (copy of ConnectedSetCounting)
  §2 Generating function with point weights Wg(U, R) = Σ_{C ⊆ U, rooted} Π_{c∈C} x(c), and
     Wg(U, R) ≤ Π_{r∈R} τ(r) under x(p)·Π_{q ∈ nb p}(1 + τ(q)) ≤ τ(p) (extension of W_le to point weights)
  §3 Two colours: colour col : P → Bool, number of colour-b neighbours of a colour-a point ≤ d a b, weight bound ξ a per colour;
     if ξ a (1+θ₀)^{d a 0}(1+θ₁)^{d a 1} ≤ θ a (a = 0, 1) then Wg(U, R) ≤ Π_{r∈R} θ(col r)
  §4 Per-site sum: with |z(C)| ≤ Π_{q∈C} ε(col q) and KP weight Π_{q∈C} e^{a(col q)},
     Σ_{C ∋ p connected} |z(C)| Π e^{a(col q)} ≤ θ(col p). For a root set S, the sum is ≤ Σ_{r∈S} θ(col r)
  §5 Sufficient condition: from (1+θ)^d ≤ e^{θd}, ε_a e^{a_a + θ₀d_{a0} + θ₁d_{a1}} ≤ θ_a suffices
  §6 Activity bounds with the lattice numbers (plaquette Δ_ff = 20, plaquette→defect 48, defect→plaquette 72, defect→defect 122, KP weights a = (2, 12)):
     with θ = (1/20, 1/10⁴), ε_thin ≤ 2.5·10⁻³ and ε_L ≤ 1.5·10⁻¹¹ give the condition, and
     the per-plaquette sum θ₀ + 4θ₁ ≤ 1
  Colour false = thin plaquette, true = link defect (all 6 plaquettes containing the link are large).
-/
import Mathlib

namespace TwoColorPolymerSum

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
theorem Wg_le (adj : P → P → Prop) (nb : P → Finset P) (hnb : ∀ p q, adj p q → q ∈ nb p)
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
        exact hnb r q (mem_filter.mp hq).2
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
    (hnb : ∀ p q, adj p q → q ∈ nb p)
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
    (hnb : ∀ p q, adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
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
    (hnb : ∀ p q, adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
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
    (hnb : ∀ p q, adj p q → q ∈ nb p) (col : P → Bool) (d : Bool → Bool → ℕ)
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
    (hnb : ∀ p q, adj p q → q ∈ nb p) (col : P → Bool)
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

end TwoColorPolymerSum
