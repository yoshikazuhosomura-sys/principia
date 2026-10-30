/-
Connectivity of nearest-neighbour edges in a box (product of coordinate intervals): if a box contains a point of A and a point
not in A, there is a nearest-neighbour edge (u, v) in the box with u ∈ A, v ∉ A. Single file; checks with `import Mathlib` only.

  Hypercubic blocks {x | L x′_i ≤ x_i < L x′_i + L} are boxes, so every partial block has an internal boundary edge
  (the content of the connectivity premise hconn of BoundaryRegulator).
-/
import Mathlib

namespace BoxConnectivity

variable {d : ℕ}

/-- Nearest-neighbour edge (one coordinate differs by 1, either direction). -/
def NNEdge (u v : Fin d → ℕ) : Prop :=
  ∃ i, v = Function.update u i (u i + 1) ∨ u = Function.update v i (v i + 1)

/-- Box. -/
def InBox (lo hi : Fin d → ℕ) (x : Fin d → ℕ) : Prop := ∀ i, lo i ≤ x i ∧ x i < hi i

/-- One step: the point moved one unit towards y in coordinate i. -/
def stepToward (x y : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update x i (if x i < y i then x i + 1 else x i - 1)

theorem dist_sum_step (x y : Fin d → ℕ) (i : Fin d) (hi : x i ≠ y i) :
    ∑ j, Nat.dist (stepToward x y i j) (y j) + 1 = ∑ j, Nat.dist (x j) (y j) := by
  rw [Fintype.sum_eq_add_sum_compl i, Fintype.sum_eq_add_sum_compl i (fun j => Nat.dist (x j) (y j))]
  have hrest : ∑ j ∈ ({i}ᶜ : Finset (Fin d)), Nat.dist (stepToward x y i j) (y j) =
      ∑ j ∈ ({i}ᶜ : Finset (Fin d)), Nat.dist (x j) (y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [stepToward, Function.update_of_ne hji]
  rw [hrest]
  have hii : Nat.dist (stepToward x y i i) (y i) + 1 = Nat.dist (x i) (y i) := by
    simp only [stepToward, Function.update_self]
    rcases lt_or_gt_of_ne hi with h | h
    · simp only [h, if_true]
      unfold Nat.dist; omega
    · have : ¬ x i < y i := by omega
      simp only [this, if_false]
      unfold Nat.dist; omega
  omega

theorem step_inBox (lo hi : Fin d → ℕ) (x y : Fin d → ℕ) (hx : InBox lo hi x) (hy : InBox lo hi y)
    (i : Fin d) (hne : x i ≠ y i) : InBox lo hi (stepToward x y i) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simp only [stepToward, Function.update_self]
    have h1 := hx j; have h2 := hy j
    split_ifs with h <;> omega
  · simp only [stepToward, Function.update_of_ne hji]
    exact hx j

theorem step_edge (x y : Fin d → ℕ) (i : Fin d) (hne : x i ≠ y i) :
    NNEdge x (stepToward x y i) := by
  refine ⟨i, ?_⟩
  by_cases h : x i < y i
  · left; simp [stepToward, h]
  · right
    have hpos : 1 ≤ x i := by omega
    unfold stepToward
    simp only [h, if_false, Function.update_self, Function.update_idem]
    have : x i - 1 + 1 = x i := by omega
    rw [this, Function.update_eq_self]

/-- Connectivity in a box: if a point x of A and a point y not in A lie in a box, there is a nearest-neighbour edge in the box leaving A. -/
theorem exists_boundary_edge (A : Set (Fin d → ℕ)) (lo hi : Fin d → ℕ) :
    ∀ n : ℕ, ∀ x y : Fin d → ℕ, ∑ j, Nat.dist (x j) (y j) = n →
      InBox lo hi x → InBox lo hi y → x ∈ A → y ∉ A →
      ∃ u v, InBox lo hi u ∧ InBox lo hi v ∧ u ∈ A ∧ v ∉ A ∧ NNEdge u v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hx hy hxA hyA
    have hxy : x ≠ y := by rintro rfl; exact hyA hxA
    obtain ⟨i, hne⟩ : ∃ i, x i ≠ y i := by
      by_contra h; push Not at h; exact hxy (funext h)
    have hbox' := step_inBox lo hi x y hx hy i hne
    by_cases hx'A : stepToward x y i ∈ A
    · have hd := dist_sum_step x y i hne
      have hlt : ∑ j, Nat.dist (stepToward x y i j) (y j) < n := by omega
      exact ih _ hlt (stepToward x y i) y rfl hbox' hy hx'A hyA
    · exact ⟨x, stepToward x y i, hx, hbox', hxA, hx'A, step_edge x y i hne⟩

/-- Hypercubic blocks (scale factor L ≥ 1) are boxes: the fibres of `x ↦ (x_i / L)_i` are the boxes `L x′_i ≤ x_i < L x′_i + L`. -/
theorem block_is_box (L : ℕ) (hL : 1 ≤ L) (x x' : Fin d → ℕ) :
    (fun i => x i / L) = x' ↔ InBox (fun i => L * x' i) (fun i => L * x' i + L) x := by
  have hLpos : 0 < L := by omega
  constructor
  · intro h i
    have hi : x i / L = x' i := congrFun h i
    show L * x' i ≤ x i ∧ x i < L * x' i + L
    rw [← hi]
    refine ⟨Nat.mul_div_le (x i) L, ?_⟩
    have := Nat.lt_mul_div_succ (x i) hLpos
    linarith [Nat.mul_comm L (x i / L)]
  · intro h
    funext i
    obtain ⟨h1, h2⟩ := h i
    simp only at h1 h2
    apply Nat.div_eq_of_lt_le
    · linarith [Nat.mul_comm L (x' i)]
    · have : (x' i + 1) * L = L * x' i + L := by ring
      omega

#print axioms dist_sum_step
#print axioms step_inBox
#print axioms step_edge
#print axioms exists_boundary_edge
#print axioms block_is_box

end BoxConnectivity
