import Mathlib

/-!
# `CensusComplete`: the chain, with the symmetry of the search in it

The foundation of the development: the definitions, the transcript checker
and its soundness, the lattice certificates, and the symmetry of the search.

* **The symmetry.**  Relabelling the six points carries a node `(pos, neg)` to
  the node `(permMaskT t pos, permMaskT t neg)`, and the census statement is
  invariant under relabelling, so a node is settled as soon as its image is.
  A transcript may therefore trade a node for the least element of its orbit,
  which is what keeps the set of nodes handed on finite.

  Nothing new is assumed.  The two hypotheses on a configuration -- general
  position and the repetition of a circumradius on every four points -- are
  invariant because they are invariant under permuting the four or three
  points inside them, and the two node conditions `Below` and `Apart` are
  invariant because `permMask` is a permutation of the ninety bits.

**Nothing here settles `n_4`.**
-/

namespace DistinctCircumradii


/-- A point of the plane. -/
abbrev Pt := ℝ × ℝ

/-- Squared distance. -/
def sqdist (p q : Pt) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Twice the signed area of `a b c`. -/
def cross (a b c : Pt) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Three points on one line. -/
def Collinear3 (a b c : Pt) : Prop := cross a b c = 0

/-- The determinant whose vanishing says that `a b c d` lie on one circle or line. -/
def det4 (a b c d : Pt) : ℝ :=
  (a.1 ^ 2 + a.2 ^ 2) * cross b c d - (b.1 ^ 2 + b.2 ^ 2) * cross a c d
    + (c.1 ^ 2 + c.2 ^ 2) * cross a b d - (d.1 ^ 2 + d.2 ^ 2) * cross a b c

/-- Four points on one circle (or line). -/
def Concyclic4 (a b c d : Pt) : Prop := det4 a b c d = 0

/-- `(a - p) ⬝ (b - p)`. -/
def qq (a b p : Pt) : ℝ := (a.1 - p.1) * (b.1 - p.1) + (a.2 - p.2) * (b.2 - p.2)

/-- The equal-circumradius form of the two triangles `a b c` and `a b d`
sharing the edge `a b`. -/
def Psi (a b c d : Pt) : ℝ := qq a b c * cross a b d + qq a b d * cross a b c

/-- `r` is the squared circumradius of the triangle `a b c`: some point is at
squared distance `r` from all three vertices. -/
def CircumRadiusSq (a b c : Pt) (r : ℝ) : Prop :=
  ∃ o : Pt, sqdist o a = r ∧ sqdist o b = r ∧ sqdist o c = r

/-- General position: no two points equal, no three collinear, no four concyclic.
Indices are taken in increasing order, so each subset is tested once. -/
def GeneralPosition {N : ℕ} (p : Fin N → Pt) : Prop :=
  (∀ i j : Fin N, i < j → p i ≠ p j) ∧
  (∀ i j k : Fin N, i < j → j < k → ¬ Collinear3 (p i) (p j) (p k)) ∧
  (∀ i j k l : Fin N, i < j → j < k → k < l → ¬ Concyclic4 (p i) (p j) (p k) (p l))

/-- The four triangles of the four-point set `a b c d`, indexed by the omitted
vertex; `face a b c d i r` says that `r` is the squared circumradius of the
`i`-th one. -/
def face (a b c d : Pt) : Fin 4 → ℝ → Prop
  | 0 => CircumRadiusSq b c d
  | 1 => CircumRadiusSq a c d
  | 2 => CircumRadiusSq a b d
  | 3 => CircumRadiusSq a b c

/-- The four triangles of `a b c d` have pairwise different circumradii. -/
def FourDistinct (a b c d : Pt) : Prop :=
  ∀ i j : Fin 4, i ≠ j → ∀ r s : ℝ, face a b c d i r → face a b c d j s → r ≠ s

/-- Every four-point subset of `p` repeats a circumradius. -/
def EveryQuadrupleRepeats {N : ℕ} (p : Fin N → Pt) : Prop :=
  ∀ i j k l : Fin N, i < j → j < k → k < l → ¬ FourDistinct (p i) (p j) (p k) (p l)
theorem ne_of_gp {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p) {i j : Fin N}
    (h : i ≠ j) : p i ≠ p j := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hgp.1 i j hlt
  · exact fun hh => hgp.1 j i hlt hh.symm

theorem collinear3_swap₁₂ {a b c : Pt} (h : Collinear3 a b c) : Collinear3 b a c := by
  simp only [Collinear3, cross] at h ⊢; linear_combination -h

theorem collinear3_swap₂₃ {a b c : Pt} (h : Collinear3 a b c) : Collinear3 a c b := by
  simp only [Collinear3, cross] at h ⊢; linear_combination -h

theorem collinear3_rot {a b c : Pt} (h : Collinear3 a b c) : Collinear3 b c a := by
  simp only [Collinear3, cross] at h ⊢; linear_combination h

theorem ncol_of_gp {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p) {x y z : Fin N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : ¬ Collinear3 (p x) (p y) (p z) := by
  intro hc
  have base := hgp.2.1
  rcases lt_or_gt_of_ne hxy with h1 | h1
  · rcases lt_or_gt_of_ne hyz with h2 | h2
    · exact base x y z h1 h2 hc
    · rcases lt_or_gt_of_ne hxz with h3 | h3
      · exact base x z y h3 h2 (collinear3_swap₂₃ hc)
      · exact base z x y h3 h1 (collinear3_rot (collinear3_rot hc))
  · rcases lt_or_gt_of_ne hxz with h2 | h2
    · exact base y x z h1 h2 (collinear3_swap₁₂ hc)
    · rcases lt_or_gt_of_ne hyz with h3 | h3
      · exact base y z x h3 h2 (collinear3_rot hc)
      · exact base z y x h3 h1 (collinear3_swap₁₂ (collinear3_rot hc))

/-- The circle determinant is alternating: swapping two neighbouring points
changes its sign, so the four-point condition does not see the order. -/
theorem concyclic4_swap0 {a b c d : Pt} (h : Concyclic4 a b c d) : Concyclic4 b a c d := by
  simp only [Concyclic4, det4, cross] at h ⊢; linear_combination -h

theorem concyclic4_swap1 {a b c d : Pt} (h : Concyclic4 a b c d) : Concyclic4 a c b d := by
  simp only [Concyclic4, det4, cross] at h ⊢; linear_combination -h

theorem concyclic4_swap2 {a b c d : Pt} (h : Concyclic4 a b c d) : Concyclic4 a b d c := by
  simp only [Concyclic4, det4, cross] at h ⊢; linear_combination -h

set_option maxHeartbeats 1000000 in
/-- General position forbids four concyclic points in any order of the indices. -/
theorem ncyc_of_gp {N : ℕ} {p : Fin N → Pt} (hgp : GeneralPosition p) {x y z w : Fin N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) : ¬ Concyclic4 (p x) (p y) (p z) (p w) := by
  intro hc
  have base := hgp.2.2
  have vxy : (x : Fin N).val ≠ (y : Fin N).val := fun h => hxy (Fin.ext h)
  have vxz : (x : Fin N).val ≠ (z : Fin N).val := fun h => hxz (Fin.ext h)
  have vxw : (x : Fin N).val ≠ (w : Fin N).val := fun h => hxw (Fin.ext h)
  have vyz : (y : Fin N).val ≠ (z : Fin N).val := fun h => hyz (Fin.ext h)
  have vyw : (y : Fin N).val ≠ (w : Fin N).val := fun h => hyw (Fin.ext h)
  have vzw : (z : Fin N).val ≠ (w : Fin N).val := fun h => hzw (Fin.ext h)
  have s1 : (x.val < y.val ∧ x.val < z.val ∧ x.val < w.val) ∨ (y.val < x.val ∧ y.val < z.val ∧ y.val < w.val) ∨ (z.val < x.val ∧ z.val < y.val ∧ z.val < w.val) ∨ (w.val < x.val ∧ w.val < y.val ∧ w.val < z.val) := by omega
  rcases s1 with ⟨h01, h02, h03⟩ | ⟨h10, h12, h13⟩ | ⟨h20, h21, h23⟩ | ⟨h30, h31, h32⟩
  · 
    have s2 : (y.val < z.val ∧ y.val < w.val) ∨ (z.val < y.val ∧ z.val < w.val) ∨ (w.val < y.val ∧ w.val < z.val) := by omega
    rcases s2 with ⟨h12, h13⟩ | ⟨h21, h23⟩ | ⟨h31, h32⟩
    · 
      have s3 : (z.val < w.val) ∨ (w.val < z.val) := by omega
      rcases s3 with h23 | h32
      · 
        exact base x y z w (show x < y from h01) (show y < z from h12) (show z < w from h23) (hc)
      · 
        exact base x y w z (show x < y from h01) (show y < w from h13) (show w < z from h32) (concyclic4_swap2 (hc))
    · 
      have s3 : (y.val < w.val) ∨ (w.val < y.val) := by omega
      rcases s3 with h13 | h31
      · 
        exact base x z y w (show x < z from h02) (show z < y from h21) (show y < w from h13) (concyclic4_swap1 (hc))
      · 
        exact base x z w y (show x < z from h02) (show z < w from h23) (show w < y from h31) (concyclic4_swap2 (concyclic4_swap1 (hc)))
    · 
      have s3 : (y.val < z.val) ∨ (z.val < y.val) := by omega
      rcases s3 with h12 | h21
      · 
        exact base x w y z (show x < w from h03) (show w < y from h31) (show y < z from h12) (concyclic4_swap1 (concyclic4_swap2 (hc)))
      · 
        exact base x w z y (show x < w from h03) (show w < z from h32) (show z < y from h21) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap2 (hc))))
  · 
    have s2 : (x.val < z.val ∧ x.val < w.val) ∨ (z.val < x.val ∧ z.val < w.val) ∨ (w.val < x.val ∧ w.val < z.val) := by omega
    rcases s2 with ⟨h02, h03⟩ | ⟨h20, h23⟩ | ⟨h30, h32⟩
    · 
      have s3 : (z.val < w.val) ∨ (w.val < z.val) := by omega
      rcases s3 with h23 | h32
      · 
        exact base y x z w (show y < x from h10) (show x < z from h02) (show z < w from h23) (concyclic4_swap0 (hc))
      · 
        exact base y x w z (show y < x from h10) (show x < w from h03) (show w < z from h32) (concyclic4_swap2 (concyclic4_swap0 (hc)))
    · 
      have s3 : (x.val < w.val) ∨ (w.val < x.val) := by omega
      rcases s3 with h03 | h30
      · 
        exact base y z x w (show y < z from h12) (show z < x from h20) (show x < w from h03) (concyclic4_swap1 (concyclic4_swap0 (hc)))
      · 
        exact base y z w x (show y < z from h12) (show z < w from h23) (show w < x from h30) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap0 (hc))))
    · 
      have s3 : (x.val < z.val) ∨ (z.val < x.val) := by omega
      rcases s3 with h02 | h20
      · 
        exact base y w x z (show y < w from h13) (show w < x from h30) (show x < z from h02) (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (hc))))
      · 
        exact base y w z x (show y < w from h13) (show w < z from h32) (show z < x from h20) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (hc)))))
  · 
    have s2 : (x.val < y.val ∧ x.val < w.val) ∨ (y.val < x.val ∧ y.val < w.val) ∨ (w.val < x.val ∧ w.val < y.val) := by omega
    rcases s2 with ⟨h01, h03⟩ | ⟨h10, h13⟩ | ⟨h30, h31⟩
    · 
      have s3 : (y.val < w.val) ∨ (w.val < y.val) := by omega
      rcases s3 with h13 | h31
      · 
        exact base z x y w (show z < x from h20) (show x < y from h01) (show y < w from h13) (concyclic4_swap0 (concyclic4_swap1 (hc)))
      · 
        exact base z x w y (show z < x from h20) (show x < w from h03) (show w < y from h31) (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (hc))))
    · 
      have s3 : (x.val < w.val) ∨ (w.val < x.val) := by omega
      rcases s3 with h03 | h30
      · 
        exact base z y x w (show z < y from h21) (show y < x from h10) (show x < w from h03) (concyclic4_swap1 (concyclic4_swap0 (concyclic4_swap1 (hc))))
      · 
        exact base z y w x (show z < y from h21) (show y < w from h13) (show w < x from h30) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap0 (concyclic4_swap1 (hc)))))
    · 
      have s3 : (x.val < y.val) ∨ (y.val < x.val) := by omega
      rcases s3 with h01 | h10
      · 
        exact base z w x y (show z < w from h23) (show w < x from h30) (show x < y from h01) (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (hc)))))
      · 
        exact base z w y x (show z < w from h23) (show w < y from h31) (show y < x from h10) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (hc))))))
  · 
    have s2 : (x.val < y.val ∧ x.val < z.val) ∨ (y.val < x.val ∧ y.val < z.val) ∨ (z.val < x.val ∧ z.val < y.val) := by omega
    rcases s2 with ⟨h01, h02⟩ | ⟨h10, h12⟩ | ⟨h20, h21⟩
    · 
      have s3 : (y.val < z.val) ∨ (z.val < y.val) := by omega
      rcases s3 with h12 | h21
      · 
        exact base w x y z (show w < x from h30) (show x < y from h01) (show y < z from h12) (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc))))
      · 
        exact base w x z y (show w < x from h30) (show x < z from h02) (show z < y from h21) (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc)))))
    · 
      have s3 : (x.val < z.val) ∨ (z.val < x.val) := by omega
      rcases s3 with h02 | h20
      · 
        exact base w y x z (show w < y from h31) (show y < x from h10) (show x < z from h02) (concyclic4_swap1 (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc)))))
      · 
        exact base w y z x (show w < y from h31) (show y < z from h12) (show z < x from h20) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc))))))
    · 
      have s3 : (x.val < y.val) ∨ (y.val < x.val) := by omega
      rcases s3 with h01 | h10
      · 
        exact base w z x y (show w < z from h32) (show z < x from h20) (show x < y from h01) (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc))))))
      · 
        exact base w z y x (show w < z from h32) (show z < y from h21) (show y < x from h10) (concyclic4_swap2 (concyclic4_swap1 (concyclic4_swap2 (concyclic4_swap0 (concyclic4_swap1 (concyclic4_swap2 (hc)))))))
/-- A triangle that is not degenerate has a circumcentre, hence a squared
circumradius.  The centre is written out by Cramer's rule. -/
theorem exists_circumRadiusSq {a b c : Pt} (h : cross a b c ≠ 0) :
    ∃ r : ℝ, CircumRadiusSq a b c r := by
  simp only [cross] at h
  obtain ⟨u, v, hu, hv⟩ :
      ∃ u v : ℝ,
        2 * (u * (b.1 - a.1) + v * (b.2 - a.2)) = (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ∧
        2 * (u * (c.1 - a.1) + v * (c.2 - a.2)) = (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 := by
    refine ⟨(((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.2 - a.2)
        - ((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.2 - a.2))
        / (2 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))),
      (((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.1 - a.1)
        - ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.1 - a.1))
        / (2 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))), ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
  refine ⟨_, (a.1 + u, a.2 + v), rfl, ?_, ?_⟩
  · show (a.1 + u - b.1) ^ 2 + (a.2 + v - b.2) ^ 2
        = (a.1 + u - a.1) ^ 2 + (a.2 + v - a.2) ^ 2
    linear_combination -hu
  · show (a.1 + u - c.1) ^ 2 + (a.2 + v - c.2) ^ 2
        = (a.1 + u - a.1) ^ 2 + (a.2 + v - a.2) ^ 2
    linear_combination -hv

/-- The squared circumradius does not depend on the order of the vertices. -/
theorem circumRadiusSq_perm {a b c : Pt} {r : ℝ} (h : CircumRadiusSq a b c r) :
    CircumRadiusSq a c b r ∧ CircumRadiusSq b a c r ∧ CircumRadiusSq b c a r ∧
      CircumRadiusSq c a b r ∧ CircumRadiusSq c b a r := by
  obtain ⟨o, h1, h2, h3⟩ := h
  exact ⟨⟨o, h1, h3, h2⟩, ⟨o, h2, h1, h3⟩, ⟨o, h2, h3, h1⟩, ⟨o, h3, h1, h2⟩, ⟨o, h3, h2, h1⟩⟩
/-- Four times the squared circumradius times the squared doubled area is the
product of the three squared side lengths (the identity `R = abc/4K`). -/
theorem circumRadiusSq_formula {a b c o : Pt} {r : ℝ}
    (ha : sqdist o a = r) (hb : sqdist o b = r) (hc : sqdist o c = r) :
    4 * r * cross a b c ^ 2 = sqdist a b * sqdist b c * sqdist c a := by
  simp only [sqdist, cross] at ha hb hc ⊢
  have f : 2 * ((o.1 - a.1) * (b.1 - a.1) + (o.2 - a.2) * (b.2 - a.2))
      = (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by linear_combination ha - hb
  have g : 2 * ((o.1 - a.1) * (c.1 - a.1) + (o.2 - a.2) * (c.2 - a.2))
      = (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 := by linear_combination ha - hc
  have hx : 2 * (o.1 - a.1) * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))
      = ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.2 - a.2)
        - ((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.2 - a.2) := by
    linear_combination (c.2 - a.2) * f - (b.2 - a.2) * g
  have hy : 2 * (o.2 - a.2) * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))
      = ((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.1 - a.1)
        - ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.1 - a.1) := by
    linear_combination (b.1 - a.1) * g - (c.1 - a.1) * f
  linear_combination
    (-4 * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) ^ 2) * ha
    + (2 * (o.1 - a.1) * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))
        + ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.2 - a.2)
        - ((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.2 - a.2)) * hx
    + (2 * (o.2 - a.2) * ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1))
        + ((c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2) * (b.1 - a.1)
        - ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) * (c.1 - a.1)) * hy

/-- The numerator of the difference of the squared circumradii of the two
triangles `a b c`, `a b d` on the edge `a b` factors as the circle
determinant times `Psi`. -/
theorem circum_diff_factor (a b c d : Pt) :
    sqdist b c * sqdist c a * cross a b d ^ 2 - sqdist b d * sqdist d a * cross a b c ^ 2
      = det4 a b c d * Psi a b c d := by
  simp only [sqdist, cross, det4, Psi, qq]
  ring

theorem sqdist_ne_zero {p q : Pt} (h : p ≠ q) : sqdist p q ≠ 0 := by
  intro hz
  simp only [sqdist] at hz
  have h1 : p.1 - q.1 = 0 ∧ p.2 - q.2 = 0 := by
    constructor <;> nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  exact h (Prod.ext (by linarith [h1.1]) (by linarith [h1.2]))

/-- **The pair criterion.**  For four points with `a ≠ b`, neither `a b c` nor
`a b d` collinear and `a b c d` not concyclic, the two triangles on the edge
`a b` have the same circumradius exactly when `Psi a b c d = 0`. -/
theorem eqRadSq_iff_psi {a b c d : Pt} {r s : ℝ}
    (hab : a ≠ b) (hc : ¬ Collinear3 a b c) (hd : ¬ Collinear3 a b d)
    (hcyc : ¬ Concyclic4 a b c d)
    (hr : CircumRadiusSq a b c r) (hs : CircumRadiusSq a b d s) :
    r = s ↔ Psi a b c d = 0 := by
  obtain ⟨o, o1, o2, o3⟩ := hr
  obtain ⟨p, p1, p2, p3⟩ := hs
  have hfc : 4 * r * cross a b c ^ 2 = sqdist a b * sqdist b c * sqdist c a :=
    circumRadiusSq_formula o1 o2 o3
  have hfd : 4 * s * cross a b d ^ 2 = sqdist a b * sqdist b d * sqdist d a :=
    circumRadiusSq_formula p1 p2 p3
  have hcc : cross a b c ≠ 0 := fun h => hc h
  have hdd : cross a b d ≠ 0 := fun h => hd h
  have hd4 : det4 a b c d ≠ 0 := fun h => hcyc h
  have hs4 : sqdist a b ≠ 0 := sqdist_ne_zero hab
  have key : sqdist a b * (det4 a b c d * Psi a b c d)
      = 4 * (r - s) * (cross a b c ^ 2 * cross a b d ^ 2) := by
    rw [← circum_diff_factor]
    linear_combination cross a b c ^ 2 * hfd - cross a b d ^ 2 * hfc
  constructor
  · intro hrs
    rw [hrs] at key
    simp only [sub_self, mul_zero, zero_mul] at key
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hs4
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hd4
      · exact h'
  · intro hpsi
    rw [hpsi, mul_zero, mul_zero] at key
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    have hcd : cross a b c ^ 2 * cross a b d ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hcc) (pow_ne_zero 2 hdd)
    have hrs : r - s = 0 := by
      rcases mul_eq_zero.mp key.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h4
        · exact h'
      · exact absurd h hcd
    linarith
/-- Bit `i` of `w`. -/
def bitAt (w i : ℕ) : Bool := decide (w / 2 ^ i % 2 = 1)

theorem bitAt_zero (w : ℕ) : bitAt w 0 = decide (w % 2 = 1) := by
  simp only [bitAt, pow_zero, Nat.div_one]

theorem bitAt_succ (w i : ℕ) : bitAt w (i + 1) = bitAt (w / 2) i := by
  have h : w / 2 / 2 ^ i = w / 2 ^ (i + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
  simp only [bitAt, h]

/-- The natural number whose bits below `n` are given by `f`. -/
def ofBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, f => (if f 0 then 1 else 0) + 2 * ofBits n (fun k => f (k + 1))

theorem ofBits_lt (n : ℕ) (f : ℕ → Bool) : ofBits n f < 2 ^ n := by
  induction n generalizing f with
  | zero => simp [ofBits]
  | succ n ih =>
    have h := ih (fun k => f (k + 1))
    simp only [ofBits, pow_succ]
    split <;> omega

theorem bitAt_of_bit_add (b : Bool) (X : ℕ) :
    bitAt ((if b then 1 else 0) + 2 * X) 0 = b := by
  cases b
  · simp only [bitAt, Bool.false_eq_true, if_false, pow_zero, Nat.div_one,
      Nat.zero_add, decide_eq_false_iff_not]
    omega
  · simp only [bitAt, if_true, pow_zero, Nat.div_one, decide_eq_true_eq]
    omega

theorem div_two_of_bit_add (b : Bool) (X : ℕ) :
    ((if b then 1 else 0) + 2 * X) / 2 = X := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [if_true]
    omega

theorem bitAt_ofBits (n : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < n) :
    bitAt (ofBits n f) i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => exact bitAt_of_bit_add (f 0) (ofBits n fun k => f (k + 1))
    | succ j =>
      have hstep : bitAt (ofBits (n + 1) f) (j + 1)
          = bitAt (ofBits n fun k => f (k + 1)) j := by
        rw [show ofBits (n + 1) f
              = (if f 0 then 1 else 0) + 2 * ofBits n (fun k => f (k + 1)) from rfl,
          bitAt_succ, div_two_of_bit_add]
      rw [hstep]
      exact ih (fun k => f (k + 1)) j (by omega)
/-- A cell: an ordered pair of two disjoint two-element subsets of the six
points, each written in increasing order.  The first component is the pair of
apexes, the second the shared edge. -/
abbrev CellData := (Fin 6 × Fin 6) × (Fin 6 × Fin 6)

/-- The 90 cells in lexicographic order: the pair of apexes runs over the 15
two-element subsets, and for each of them the edge runs over the 6
two-element subsets of the remaining four points. -/
def cellList : List CellData :=
  [((0, 1), (2, 3)), ((0, 1), (2, 4)), ((0, 1), (2, 5)),
   ((0, 1), (3, 4)), ((0, 1), (3, 5)), ((0, 1), (4, 5)),
   ((0, 2), (1, 3)), ((0, 2), (1, 4)), ((0, 2), (1, 5)),
   ((0, 2), (3, 4)), ((0, 2), (3, 5)), ((0, 2), (4, 5)),
   ((0, 3), (1, 2)), ((0, 3), (1, 4)), ((0, 3), (1, 5)),
   ((0, 3), (2, 4)), ((0, 3), (2, 5)), ((0, 3), (4, 5)),
   ((0, 4), (1, 2)), ((0, 4), (1, 3)), ((0, 4), (1, 5)),
   ((0, 4), (2, 3)), ((0, 4), (2, 5)), ((0, 4), (3, 5)),
   ((0, 5), (1, 2)), ((0, 5), (1, 3)), ((0, 5), (1, 4)),
   ((0, 5), (2, 3)), ((0, 5), (2, 4)), ((0, 5), (3, 4)),
   ((1, 2), (0, 3)), ((1, 2), (0, 4)), ((1, 2), (0, 5)),
   ((1, 2), (3, 4)), ((1, 2), (3, 5)), ((1, 2), (4, 5)),
   ((1, 3), (0, 2)), ((1, 3), (0, 4)), ((1, 3), (0, 5)),
   ((1, 3), (2, 4)), ((1, 3), (2, 5)), ((1, 3), (4, 5)),
   ((1, 4), (0, 2)), ((1, 4), (0, 3)), ((1, 4), (0, 5)),
   ((1, 4), (2, 3)), ((1, 4), (2, 5)), ((1, 4), (3, 5)),
   ((1, 5), (0, 2)), ((1, 5), (0, 3)), ((1, 5), (0, 4)),
   ((1, 5), (2, 3)), ((1, 5), (2, 4)), ((1, 5), (3, 4)),
   ((2, 3), (0, 1)), ((2, 3), (0, 4)), ((2, 3), (0, 5)),
   ((2, 3), (1, 4)), ((2, 3), (1, 5)), ((2, 3), (4, 5)),
   ((2, 4), (0, 1)), ((2, 4), (0, 3)), ((2, 4), (0, 5)),
   ((2, 4), (1, 3)), ((2, 4), (1, 5)), ((2, 4), (3, 5)),
   ((2, 5), (0, 1)), ((2, 5), (0, 3)), ((2, 5), (0, 4)),
   ((2, 5), (1, 3)), ((2, 5), (1, 4)), ((2, 5), (3, 4)),
   ((3, 4), (0, 1)), ((3, 4), (0, 2)), ((3, 4), (0, 5)),
   ((3, 4), (1, 2)), ((3, 4), (1, 5)), ((3, 4), (2, 5)),
   ((3, 5), (0, 1)), ((3, 5), (0, 2)), ((3, 5), (0, 4)),
   ((3, 5), (1, 2)), ((3, 5), (1, 4)), ((3, 5), (2, 4)),
   ((4, 5), (0, 1)), ((4, 5), (0, 2)), ((4, 5), (0, 3)),
   ((4, 5), (1, 2)), ((4, 5), (1, 3)), ((4, 5), (2, 3))]

theorem cellList_length : cellList.length = 90 := by decide

/-- The cell with index `i` (a fixed dummy outside the range). -/
def cellOf (i : ℕ) : CellData := cellList.getD i ((0, 0), (0, 0))

/-- The index of the cell whose apexes are `{a,b}` and whose edge is `{c,d}`,
in either order. -/
def cellNum (a b c d : Fin 6) : ℕ :=
  cellList.idxOf ((min a b, max a b), (min c d, max c d))

theorem cellOf_distinct : ∀ i : Fin 90,
    (cellOf i.val).1.1 ≠ (cellOf i.val).1.2 ∧ (cellOf i.val).2.1 ≠ (cellOf i.val).2.2 ∧
      (cellOf i.val).1.1 ≠ (cellOf i.val).2.1 ∧ (cellOf i.val).1.1 ≠ (cellOf i.val).2.2 ∧
      (cellOf i.val).1.2 ≠ (cellOf i.val).2.1 ∧ (cellOf i.val).1.2 ≠ (cellOf i.val).2.2 := by
  decide

/-- `cellNum` inverts `cellOf` on the cells: four pairwise different points give
an index below 90 whose cell is the one they name. -/
theorem cellNum_spec : ∀ a b c d : Fin 6, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    cellNum a b c d < 90 ∧
      cellOf (cellNum a b c d) = ((min a b, max a b), (min c d, max c d)) := by
  decide
/-- A witness set, held as the bit string of a natural number: bit `i` says that
the cell `cellOf i` is a witness. -/
abbrev Mask := ℕ

/-- The value of `Psi` at the cell `i`: the edge is `(cellOf i).2`, the apexes
are `(cellOf i).1`. -/
def cellPsi (p : Fin 6 → Pt) (i : ℕ) : ℝ :=
  Psi (p (cellOf i).2.1) (p (cellOf i).2.2) (p (cellOf i).1.1) (p (cellOf i).1.2)

/-- **`p` carries `w`**: the cells of `w` are exactly the cells where `Psi`
vanishes.  The mask is not computed from `p` -- it is quantified over and tied
to `p` by this condition, because "`Psi = 0`" is not decidable over `ℝ`. -/
def Carries (p : Fin 6 → Pt) (w : Mask) : Prop :=
  ∀ i < 90, (cellPsi p i = 0 ↔ bitAt w i = true)

/-- **`p` supports `w`**: every cell of `w` is a witness of `p`.  Weaker than
`Carries`: nothing is said about the cells outside `w`. -/
def Supports (p : Fin 6 → Pt) (w : Mask) : Prop :=
  ∀ i < 90, bitAt w i = true → cellPsi p i = 0

theorem supports_of_carries {p : Fin 6 → Pt} {w : Mask} (h : Carries p w) :
    Supports p w := fun i hi hb => (h i hi).2 hb

/-- Every configuration carries a mask.  (Classically: the mask is read off
from `p`, which is exactly what a decision procedure cannot do.) -/
theorem exists_carries (p : Fin 6 → Pt) : ∃ w : Mask, w < 2 ^ 90 ∧ Carries p w := by
  classical
  refine ⟨ofBits 90 (fun i => decide (cellPsi p i = 0)), ofBits_lt _ _, ?_⟩
  intro i hi
  rw [bitAt_ofBits 90 _ i hi]
  simp
theorem psi_eq_zero_swap₁₂ (a b c d : Pt) : Psi b a c d = 0 ↔ Psi a b c d = 0 := by
  have h : Psi b a c d = - Psi a b c d := by simp only [Psi, qq, cross]; ring
  rw [h, neg_eq_zero]

theorem psi_eq_zero_swap₃₄ (a b c d : Pt) : Psi a b d c = 0 ↔ Psi a b c d = 0 := by
  have h : Psi a b d c = Psi a b c d := by simp only [Psi, qq, cross]; ring
  rw [h]

theorem psi_minmax_eq_zero (p : Fin 6 → Pt) (a b c d : Fin 6) :
    Psi (p (min a b)) (p (max a b)) (p (min c d)) (p (max c d)) = 0
      ↔ Psi (p a) (p b) (p c) (p d) = 0 := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
  · rw [min_eq_left hab, max_eq_right hab, min_eq_right hcd, max_eq_left hcd,
      psi_eq_zero_swap₃₄]
  · rw [min_eq_right hab, max_eq_left hab, min_eq_left hcd, max_eq_right hcd,
      psi_eq_zero_swap₁₂]
  · rw [min_eq_right hab, max_eq_left hab, min_eq_right hcd, max_eq_left hcd,
      psi_eq_zero_swap₁₂, psi_eq_zero_swap₃₄]
/-- The inner product of the differences `a - b` and `c - d`. -/
def dotd (a b c d : Pt) : ℝ := (a.1 - b.1) * (c.1 - d.1) + (a.2 - b.2) * (c.2 - d.2)

/-- The cross product of the differences `a - b` and `c - d`. -/
def crossd (a b c d : Pt) : ℝ := (a.1 - b.1) * (c.2 - d.2) - (a.2 - b.2) * (c.1 - d.1)
/-- Vanishing squared distance forces equality of the points. -/
theorem eq_of_sqdist_eq_zero {p q : Pt} (h : sqdist p q = 0) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp [sqdist] at h
  have h1 : a = c := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  have h2 : b = d := by nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  rw [h1, h2]

/-- A sum of two squares vanishes only when both terms do. -/
theorem eq_zero_of_sq_add_sq_eq_zero (a b : ℝ) (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  constructor
  · nlinarith [sq_nonneg a, sq_nonneg b]
  · nlinarith [sq_nonneg a, sq_nonneg b]
/-- If a nonzero vector `g` is parallel to both `x` and `y`, then `x` and `y` are
parallel.  Stated as a polynomial consequence so that no case split is needed. -/
theorem sq_norm_mul_cross_eq_zero (g₁ g₂ x₁ x₂ y₁ y₂ : ℝ)
    (hx : g₁ * x₂ - g₂ * x₁ = 0) (hy : g₁ * y₂ - g₂ * y₁ = 0) :
    (g₁ ^ 2 + g₂ ^ 2) * (x₁ * y₂ - x₂ * y₁) = 0 := by
  linear_combination (g₁ * x₁ + g₂ * x₂) * hy - (g₁ * y₁ + g₂ * y₂) * hx

/-- Lagrange's identity in the plane. -/
theorem sq_dot_add_sq_cross (x₁ x₂ y₁ y₂ : ℝ) :
    (x₁ * y₁ + x₂ * y₂) ^ 2 + (x₁ * y₂ - x₂ * y₁) ^ 2
      = (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
  ring

/-- Two differences that are both orthogonal and parallel force one of the two
pairs of points to coincide. -/
theorem sqdist_mul_sqdist_eq_zero_of (a b c d : Pt)
    (hdot : dotd a b c d = 0) (hcross : crossd a b c d = 0) :
    sqdist a b * sqdist c d = 0 := by
  have h := sq_dot_add_sq_cross (a.1 - b.1) (a.2 - b.2) (c.1 - d.1) (c.2 - d.2)
  simp only [dotd] at hdot
  simp only [crossd] at hcross
  simp only [sqdist]
  nlinarith [h, hdot, hcross]
/-- The concyclicity determinant written in the same two pieces as `Psi`. -/
theorem det4_eq_qq_mul_cross (a b c d : Pt) :
    det4 a b c d = qq a b c * cross a b d - qq a b d * cross a b c := by
  simp only [det4, qq, cross]
  ring

/-- The certificate behind rule (C). -/
theorem cross_mul_det4_eq (u v c d f : Pt) :
    cross u v c * det4 u v d f = cross u v f * Psi u v c d - cross u v d * Psi u v c f := by
  simp only [det4, qq, cross, Psi]
  ring

/-- **Rule (C).**  Two witnesses sharing the edge `u v` whose pairs share the
point `c` force `u v d f` to be concyclic. -/
theorem concyclic_of_two_witnesses_sharing_edge (u v c d f : Pt)
    (hc : ¬ Collinear3 u v c) (h1 : Psi u v c d = 0) (h2 : Psi u v c f = 0) :
    Concyclic4 u v d f := by
  have key := cross_mul_det4_eq u v c d f
  rw [h1, h2] at key
  have : cross u v c * det4 u v d f = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hc
  · exact h

/-- `Psi` is the cross product of the two values of `w_P`. -/
theorem psi_eq_cross_of_w (u v c d : Pt) :
    Psi u v c d
      = ((u.1 - c.1) * (u.1 - d.1) - (u.2 - c.2) * (u.2 - d.2))
          * ((v.1 - c.1) * (v.2 - d.2) + (v.2 - c.2) * (v.1 - d.1))
        - ((u.1 - c.1) * (u.2 - d.2) + (u.2 - c.2) * (u.1 - d.1))
          * ((v.1 - c.1) * (v.1 - d.1) - (v.2 - c.2) * (v.2 - d.2)) := by
  simp only [Psi, qq, cross]
  ring

/-- The squared modulus of `w_P` at a point. -/
theorem sqdist_mul_sqdist_eq_sq_add_sq (v c d : Pt) :
    sqdist v c * sqdist v d
      = ((v.1 - c.1) * (v.1 - d.1) - (v.2 - c.2) * (v.2 - d.2)) ^ 2
        + ((v.1 - c.1) * (v.2 - d.2) + (v.2 - c.2) * (v.1 - d.1)) ^ 2 := by
  simp only [sqdist]
  ring

/-- **Rule (B).**  With the pair `{c, d}` fixed, being a witness is a transitive
relation on the remaining points. -/
theorem psi_trans (u v x c d : Pt) (hvc : v ≠ c) (hvd : v ≠ d)
    (h1 : Psi u v c d = 0) (h2 : Psi v x c d = 0) : Psi u x c d = 0 := by
  have hgx : ((v.1 - c.1) * (v.1 - d.1) - (v.2 - c.2) * (v.2 - d.2))
        * ((u.1 - c.1) * (u.2 - d.2) + (u.2 - c.2) * (u.1 - d.1))
      - ((v.1 - c.1) * (v.2 - d.2) + (v.2 - c.2) * (v.1 - d.1))
        * ((u.1 - c.1) * (u.1 - d.1) - (u.2 - c.2) * (u.2 - d.2)) = 0 := by
    rw [psi_eq_cross_of_w] at h1
    linarith
  have hgy : ((v.1 - c.1) * (v.1 - d.1) - (v.2 - c.2) * (v.2 - d.2))
        * ((x.1 - c.1) * (x.2 - d.2) + (x.2 - c.2) * (x.1 - d.1))
      - ((v.1 - c.1) * (v.2 - d.2) + (v.2 - c.2) * (v.1 - d.1))
        * ((x.1 - c.1) * (x.1 - d.1) - (x.2 - c.2) * (x.2 - d.2)) = 0 := by
    rw [psi_eq_cross_of_w] at h2
    linarith
  have key := sq_norm_mul_cross_eq_zero
    ((v.1 - c.1) * (v.1 - d.1) - (v.2 - c.2) * (v.2 - d.2))
    ((v.1 - c.1) * (v.2 - d.2) + (v.2 - c.2) * (v.1 - d.1))
    ((u.1 - c.1) * (u.1 - d.1) - (u.2 - c.2) * (u.2 - d.2))
    ((u.1 - c.1) * (u.2 - d.2) + (u.2 - c.2) * (u.1 - d.1))
    ((x.1 - c.1) * (x.1 - d.1) - (x.2 - c.2) * (x.2 - d.2))
    ((x.1 - c.1) * (x.2 - d.2) + (x.2 - c.2) * (x.1 - d.1)) hgx hgy
  rw [← sqdist_mul_sqdist_eq_sq_add_sq] at key
  have hbc : sqdist v c ≠ 0 := fun h => hvc (eq_of_sqdist_eq_zero h)
  have hbd : sqdist v d ≠ 0 := fun h => hvd (eq_of_sqdist_eq_zero h)
  rw [psi_eq_cross_of_w]
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hbc
    · exact absurd h' hbd
  · linarith



/-! ## Six-bit blocks

The ninety cells fall into six-cell blocks in three different ways, and each of
the three rules of the census says that the six bits of such a block lie in a
short table.  A block is held as a six-tuple of cell indices, and the six bits
are packed into a natural number with the lowest bit first. -/

/-- Six bits packed into a natural number, lowest bit first. -/
def bits6 (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  (if b0 then 1 else 0) + 2 * ((if b1 then 1 else 0) + 2 * ((if b2 then 1 else 0)
    + 2 * ((if b3 then 1 else 0) + 2 * ((if b4 then 1 else 0)
      + 2 * (if b5 then 1 else 0)))))

/-- A block: six cell indices. -/
abbrev Block := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The six bits of `w` at the cells of the block. -/
def blockVal (w : Mask) (B : Block) : ℕ :=
  bits6 (bitAt w B.1) (bitAt w B.2.1) (bitAt w B.2.2.1) (bitAt w B.2.2.2.1)
    (bitAt w B.2.2.2.2.1) (bitAt w B.2.2.2.2.2)

/-- The table for an edge block: the empty set, the six single pairs and the
three perfect matchings of the four remaining points. -/
def matchAllowed : List ℕ := [0, 1, 2, 4, 8, 12, 16, 18, 32, 33]

/-- The table for an apex-pair block: the fifteen set partitions of the four
remaining points, read as the set of edges inside the parts. -/
def partAllowed : List ℕ := [0, 1, 2, 4, 8, 11, 12, 16, 18, 21, 32, 33, 38, 56, 63]

theorem matchAllowed_length : matchAllowed.length = 10 := by decide

theorem partAllowed_length : partAllowed.length = 15 := by decide

/-- **The table for rule (C).**  Six bits no two of which are "adjacent" -- the
twelve pairs of positions whose point pairs meet -- form one of ten masks.  The
positions `0,…,5` are the pairs `(s,t),(s,y),(s,z),(t,y),(t,z),(y,z)` of the four
points left over, so the three non-adjacent pairs of positions are `(0,5)`,
`(1,4)` and `(2,3)`. -/
theorem matchTable : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (b0 = false ∨ b1 = false) → (b0 = false ∨ b2 = false) →
    (b0 = false ∨ b3 = false) → (b0 = false ∨ b4 = false) →
    (b1 = false ∨ b2 = false) → (b1 = false ∨ b3 = false) →
    (b1 = false ∨ b5 = false) → (b2 = false ∨ b4 = false) →
    (b2 = false ∨ b5 = false) → (b3 = false ∨ b4 = false) →
    (b3 = false ∨ b5 = false) → (b4 = false ∨ b5 = false) →
    matchAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true := by
  intro b0 b1 b2 b3 b4 b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    intro c01 c02 c03 c04 c12 c13 c15 c24 c25 c34 c35 c45 <;>
    first
      | decide
      | simp_all

/-- **The table for rule (B).**  Six bits closed under "two edges of a triangle
force the third" form one of fifteen masks -- exactly the set partitions of the
four points left over. -/
theorem partTable : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    (b1 = false ∨ b3 = false ∨ b0 = true) →
    (b0 = false ∨ b3 = false ∨ b1 = true) →
    (b0 = false ∨ b1 = false ∨ b3 = true) →
    (b2 = false ∨ b4 = false ∨ b0 = true) →
    (b0 = false ∨ b4 = false ∨ b2 = true) →
    (b0 = false ∨ b2 = false ∨ b4 = true) →
    (b2 = false ∨ b5 = false ∨ b1 = true) →
    (b1 = false ∨ b5 = false ∨ b2 = true) →
    (b1 = false ∨ b2 = false ∨ b5 = true) →
    (b4 = false ∨ b5 = false ∨ b3 = true) →
    (b3 = false ∨ b5 = false ∨ b4 = true) →
    (b3 = false ∨ b4 = false ∨ b5 = true) →
    partAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true := by
  intro b0 b1 b2 b3 b4 b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    intro t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 <;>
    first
      | decide
      | simp_all

/-! ## The bridge from a bit to the geometry -/

theorem cellNum_swap₁₂ (a b c d : Fin 6) : cellNum a b c d = cellNum b a c d := by
  simp only [cellNum, min_comm a b, max_comm a b]

theorem cellNum_swap₃₄ (a b c d : Fin 6) : cellNum a b c d = cellNum a b d c := by
  simp only [cellNum, min_comm c d, max_comm c d]

/-- **The bridge.**  For four pairwise different points, the bit of the mask at
the cell with apexes `{a,b}` and edge `{c,d}` says exactly that the two triangles
on the edge `c d` with apexes `a` and `b` have equal circumradius, in the form
`Psi = 0`. -/
theorem bit_iff_psi {p : Fin 6 → Pt} {w : Mask} (hw : Carries p w) {a b c d : Fin 6}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    bitAt w (cellNum a b c d) = true ↔ Psi (p c) (p d) (p a) (p b) = 0 := by
  obtain ⟨hlt, heq⟩ := cellNum_spec a b c d hab hcd hac had hbc hbd
  rw [← hw _ hlt]
  simp only [cellPsi, heq]
  exact psi_minmax_eq_zero p c d a b

/-! ## Rule (C): the edge blocks -/

/-- Two witnesses on the same edge whose apex pairs share a point are impossible
in general position: rule (C) would make four of the points concyclic. -/
theorem not_two_witnesses_sharing_edge {p : Fin 6 → Pt} (hgp : GeneralPosition p)
    {u v c d f : Fin 6} (huv : u ≠ v) (huc : u ≠ c) (hud : u ≠ d) (huf : u ≠ f)
    (hvc : v ≠ c) (hvd : v ≠ d) (hvf : v ≠ f) (hdf : d ≠ f)
    (h1 : Psi (p u) (p v) (p c) (p d) = 0) (h2 : Psi (p u) (p v) (p c) (p f) = 0) :
    False :=
  ncyc_of_gp hgp huv hud huf hvd hvf hdf
    (concyclic_of_two_witnesses_sharing_edge (p u) (p v) (p c) (p d) (p f)
      (ncol_of_gp hgp huv huc hvc) h1 h2)

/-- The bit form of rule (C): of two cells on the edge `{u,v}` whose apex pairs
both contain `c`, at least one is not a witness. -/
theorem conflict_bits {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) (u v c d f : Fin 6) (i j : ℕ)
    (hd : u ≠ v ∧ u ≠ c ∧ u ≠ d ∧ u ≠ f ∧ v ≠ c ∧ v ≠ d ∧ v ≠ f ∧ c ≠ d ∧ c ≠ f ∧ d ≠ f)
    (hi : i = cellNum c d u v) (hj : j = cellNum c f u v) :
    bitAt w i = false ∨ bitAt w j = false := by
  obtain ⟨huv, huc, hud, huf, hvc, hvd, hvf, hcd, hcf, hdf⟩ := hd
  by_cases h1 : bitAt w i = true
  · right
    rw [Bool.eq_false_iff]
    intro h2
    rw [hi] at h1
    rw [hj] at h2
    exact not_two_witnesses_sharing_edge hgp huv huc hud huf hvc hvd hvf hdf
      ((bit_iff_psi hw hcd huv huc.symm hvc.symm hud.symm hvd.symm).mp h1)
      ((bit_iff_psi hw hcf huv huc.symm hvc.symm huf.symm hvf.symm).mp h2)
  · left
    exact Bool.eq_false_iff.mpr h1

/-- **Rule (C) as a table.**  The six cells on a fixed edge `{u,v}`, indexed by
the six pairs of the four remaining points `s,t,y,z` in lexicographic order,
carry one of the ten masks of `matchAllowed`. -/
theorem edgeBlock_mem {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) (u v s t y z : Fin 6) (i0 i1 i2 i3 i4 i5 : ℕ)
    (hd : u ≠ v ∧ u ≠ s ∧ u ≠ t ∧ u ≠ y ∧ u ≠ z ∧ v ≠ s ∧ v ≠ t ∧ v ≠ y ∧ v ≠ z ∧
      s ≠ t ∧ s ≠ y ∧ s ≠ z ∧ t ≠ y ∧ t ≠ z ∧ y ≠ z)
    (h0 : i0 = cellNum s t u v) (h1 : i1 = cellNum s y u v) (h2 : i2 = cellNum s z u v)
    (h3 : i3 = cellNum t y u v) (h4 : i4 = cellNum t z u v) (h5 : i5 = cellNum y z u v) :
    matchAllowed.contains (bits6 (bitAt w i0) (bitAt w i1) (bitAt w i2) (bitAt w i3)
      (bitAt w i4) (bitAt w i5)) = true := by
  obtain ⟨nuv, nus, nut, nuy, nuz, nvs, nvt, nvy, nvz, nst, nsy, nsz, nty, ntz, nyz⟩ := hd
  exact matchTable _ _ _ _ _ _
    (conflict_bits hgp hw u v s t y i0 i1
      ⟨nuv, nus, nut, nuy, nvs, nvt, nvy, nst, nsy, nty⟩ h0 h1)
    (conflict_bits hgp hw u v s t z i0 i2
      ⟨nuv, nus, nut, nuz, nvs, nvt, nvz, nst, nsz, ntz⟩ h0 h2)
    (conflict_bits hgp hw u v t s y i0 i3
      ⟨nuv, nut, nus, nuy, nvt, nvs, nvy, nst.symm, nty, nsy⟩
      (h0.trans (cellNum_swap₁₂ s t u v)) h3)
    (conflict_bits hgp hw u v t s z i0 i4
      ⟨nuv, nut, nus, nuz, nvt, nvs, nvz, nst.symm, ntz, nsz⟩
      (h0.trans (cellNum_swap₁₂ s t u v)) h4)
    (conflict_bits hgp hw u v s y z i1 i2
      ⟨nuv, nus, nuy, nuz, nvs, nvy, nvz, nsy, nsz, nyz⟩ h1 h2)
    (conflict_bits hgp hw u v y s t i1 i3
      ⟨nuv, nuy, nus, nut, nvy, nvs, nvt, nsy.symm, nty.symm, nst⟩
      (h1.trans (cellNum_swap₁₂ s y u v)) (h3.trans (cellNum_swap₁₂ t y u v)))
    (conflict_bits hgp hw u v y s z i1 i5
      ⟨nuv, nuy, nus, nuz, nvy, nvs, nvz, nsy.symm, nyz, nsz⟩
      (h1.trans (cellNum_swap₁₂ s y u v)) h5)
    (conflict_bits hgp hw u v z s t i2 i4
      ⟨nuv, nuz, nus, nut, nvz, nvs, nvt, nsz.symm, ntz.symm, nst⟩
      (h2.trans (cellNum_swap₁₂ s z u v)) (h4.trans (cellNum_swap₁₂ t z u v)))
    (conflict_bits hgp hw u v z s y i2 i5
      ⟨nuv, nuz, nus, nuy, nvz, nvs, nvy, nsz.symm, nyz.symm, nsy⟩
      (h2.trans (cellNum_swap₁₂ s z u v)) (h5.trans (cellNum_swap₁₂ y z u v)))
    (conflict_bits hgp hw u v t y z i3 i4
      ⟨nuv, nut, nuy, nuz, nvt, nvy, nvz, nty, ntz, nyz⟩ h3 h4)
    (conflict_bits hgp hw u v y t z i3 i5
      ⟨nuv, nuy, nut, nuz, nvy, nvt, nvz, nty.symm, nyz, ntz⟩
      (h3.trans (cellNum_swap₁₂ t y u v)) h5)
    (conflict_bits hgp hw u v z t y i4 i5
      ⟨nuv, nuz, nut, nuy, nvz, nvt, nvy, ntz.symm, nyz.symm, nty⟩
      (h4.trans (cellNum_swap₁₂ t z u v)) (h5.trans (cellNum_swap₁₂ y z u v)))

/-! ## Rule (B): the apex-pair blocks -/

/-- The bit form of rule (B): with the apex pair `{c,d}` fixed, if the edges
`{s,t}` and `{t,r}` are witnesses then so is `{s,r}`. -/
theorem trans_bits {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) (c d s t r : Fin 6) (i j k : ℕ)
    (hd : c ≠ d ∧ s ≠ t ∧ t ≠ r ∧ s ≠ r ∧ c ≠ s ∧ d ≠ s ∧ c ≠ t ∧ d ≠ t ∧ c ≠ r ∧ d ≠ r)
    (hi : i = cellNum c d s t) (hj : j = cellNum c d t r) (hk : k = cellNum c d s r) :
    bitAt w i = false ∨ bitAt w j = false ∨ bitAt w k = true := by
  obtain ⟨hcd, hst, htr, hsr, hcs, hds, hct, hdt, hcr, hdr⟩ := hd
  by_cases h1 : bitAt w i = true
  · by_cases h2 : bitAt w j = true
    · right; right
      rw [hi] at h1
      rw [hj] at h2
      rw [hk]
      refine (bit_iff_psi hw hcd hsr hcs hcr hds hdr).mpr ?_
      exact psi_trans (p s) (p t) (p r) (p c) (p d)
        (ne_of_gp hgp hct.symm) (ne_of_gp hgp hdt.symm)
        ((bit_iff_psi hw hcd hst hcs hct hds hdt).mp h1)
        ((bit_iff_psi hw hcd htr hct hcr hdt hdr).mp h2)
    · right; left
      exact Bool.eq_false_iff.mpr h2
  · left
    exact Bool.eq_false_iff.mpr h1

/-- **Rule (B) as a table.**  The six cells with a fixed apex pair `{c,d}`,
indexed by the six edges of the four remaining points `s,t,y,z` in lexicographic
order, carry one of the fifteen masks of `partAllowed`. -/
theorem apexBlock_mem {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) (c d s t y z : Fin 6) (i0 i1 i2 i3 i4 i5 : ℕ)
    (hd : c ≠ d ∧ c ≠ s ∧ c ≠ t ∧ c ≠ y ∧ c ≠ z ∧ d ≠ s ∧ d ≠ t ∧ d ≠ y ∧ d ≠ z ∧
      s ≠ t ∧ s ≠ y ∧ s ≠ z ∧ t ≠ y ∧ t ≠ z ∧ y ≠ z)
    (h0 : i0 = cellNum c d s t) (h1 : i1 = cellNum c d s y) (h2 : i2 = cellNum c d s z)
    (h3 : i3 = cellNum c d t y) (h4 : i4 = cellNum c d t z) (h5 : i5 = cellNum c d y z) :
    partAllowed.contains (bits6 (bitAt w i0) (bitAt w i1) (bitAt w i2) (bitAt w i3)
      (bitAt w i4) (bitAt w i5)) = true := by
  obtain ⟨ncd, ncs, nct, ncy, ncz, nds, ndt, ndy, ndz, nst, nsy, nsz, nty, ntz, nyz⟩ := hd
  exact partTable _ _ _ _ _ _
    (trans_bits hgp hw c d s y t i1 i3 i0
      ⟨ncd, nsy, nty.symm, nst, ncs, nds, ncy, ndy, nct, ndt⟩
      h1 (h3.trans (cellNum_swap₃₄ c d t y)) h0)
    (trans_bits hgp hw c d s t y i0 i3 i1
      ⟨ncd, nst, nty, nsy, ncs, nds, nct, ndt, ncy, ndy⟩ h0 h3 h1)
    (trans_bits hgp hw c d t s y i0 i1 i3
      ⟨ncd, nst.symm, nsy, nty, nct, ndt, ncs, nds, ncy, ndy⟩
      (h0.trans (cellNum_swap₃₄ c d s t)) h1 h3)
    (trans_bits hgp hw c d s z t i2 i4 i0
      ⟨ncd, nsz, ntz.symm, nst, ncs, nds, ncz, ndz, nct, ndt⟩
      h2 (h4.trans (cellNum_swap₃₄ c d t z)) h0)
    (trans_bits hgp hw c d s t z i0 i4 i2
      ⟨ncd, nst, ntz, nsz, ncs, nds, nct, ndt, ncz, ndz⟩ h0 h4 h2)
    (trans_bits hgp hw c d t s z i0 i2 i4
      ⟨ncd, nst.symm, nsz, ntz, nct, ndt, ncs, nds, ncz, ndz⟩
      (h0.trans (cellNum_swap₃₄ c d s t)) h2 h4)
    (trans_bits hgp hw c d s z y i2 i5 i1
      ⟨ncd, nsz, nyz.symm, nsy, ncs, nds, ncz, ndz, ncy, ndy⟩
      h2 (h5.trans (cellNum_swap₃₄ c d y z)) h1)
    (trans_bits hgp hw c d s y z i1 i5 i2
      ⟨ncd, nsy, nyz, nsz, ncs, nds, ncy, ndy, ncz, ndz⟩ h1 h5 h2)
    (trans_bits hgp hw c d y s z i1 i2 i5
      ⟨ncd, nsy.symm, nsz, nyz, ncy, ndy, ncs, nds, ncz, ndz⟩
      (h1.trans (cellNum_swap₃₄ c d s y)) h2 h5)
    (trans_bits hgp hw c d t z y i4 i5 i3
      ⟨ncd, ntz, nyz.symm, nty, nct, ndt, ncz, ndz, ncy, ndy⟩
      h4 (h5.trans (cellNum_swap₃₄ c d y z)) h3)
    (trans_bits hgp hw c d t y z i3 i5 i4
      ⟨ncd, nty, nyz, ntz, nct, ndt, ncy, ndy, ncz, ndz⟩ h3 h5 h4)
    (trans_bits hgp hw c d y t z i3 i4 i5
      ⟨ncd, nty.symm, ntz, nyz, ncy, ndy, nct, ndt, ncz, ndz⟩
      (h3.trans (cellNum_swap₃₄ c d t y)) h4 h5)

/-! ## Rule (T): the four-point blocks

Inside a four-point subset the six cells are indexed by the pair of apexes
alone -- the edge is the complementary pair -- and the cell with apexes `{x,y}`
is a witness exactly when the two faces obtained by omitting `x` and by omitting
`y` have equal circumradius.  So the six bits record which of four real numbers
agree.  Equality of reals is transitive, which cuts the sixty-four masks down to
the fifteen set partitions of the four points; badness removes the empty mask;
and **Johnson's circle theorem** removes the four masks in which exactly three
of the radii agree.  Ten masks are left. -/

/-- The squared circumradius of a non-degenerate triangle is unique. -/
theorem circumRadiusSq_unique {a b c : Pt} (h : ¬ Collinear3 a b c) {r s : ℝ}
    (hr : CircumRadiusSq a b c r) (hs : CircumRadiusSq a b c s) : r = s := by
  obtain ⟨o, o1, o2, o3⟩ := hr
  obtain ⟨q, q1, q2, q3⟩ := hs
  have f1 : 4 * r * cross a b c ^ 2 = sqdist a b * sqdist b c * sqdist c a :=
    circumRadiusSq_formula o1 o2 o3
  have f2 : 4 * s * cross a b c ^ 2 = sqdist a b * sqdist b c * sqdist c a :=
    circumRadiusSq_formula q1 q2 q3
  have hsq : cross a b c ^ 2 ≠ 0 := pow_ne_zero 2 (fun hh => h hh)
  have key : (r - s) * (4 * cross a b c ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp key with h' | h'
  · linarith
  · exact absurd (by linarith : cross a b c ^ 2 = 0) hsq

/-- Four points at the same distance from one point lie on a circle. -/
theorem concyclic_of_common_center {a b c d o : Pt} {r : ℝ}
    (ha : sqdist o a = r) (hb : sqdist o b = r) (hc : sqdist o c = r)
    (hd : sqdist o d = r) : Concyclic4 a b c d := by
  simp only [sqdist] at ha hb hc hd
  simp only [Concyclic4, det4, cross]
  linear_combination
    ((c.1 - b.1) * (d.2 - b.2) - (c.2 - b.2) * (d.1 - b.1)) * ha
      - ((c.1 - a.1) * (d.2 - a.2) - (c.2 - a.2) * (d.1 - a.1)) * hb
      + ((b.1 - a.1) * (d.2 - a.2) - (b.2 - a.2) * (d.1 - a.1)) * hc
      - ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)) * hd

/-- **The rhombus step.**  Two different points `ob`, `oc` at one and the same
distance from each of two different points `x`, `d` satisfy `ob + oc = x + d`:
the quadrilateral `d ob x oc` is a rhombus, and its diagonals bisect. -/
theorem centers_sum {x d ob oc : Pt} {r : ℝ} (hxd : x ≠ d) (hoo : ob ≠ oc)
    (h1 : sqdist ob d = r) (h2 : sqdist ob x = r)
    (h3 : sqdist oc d = r) (h4 : sqdist oc x = r) :
    ob.1 + oc.1 = x.1 + d.1 ∧ ob.2 + oc.2 = x.2 + d.2 := by
  have hne : sqdist ob oc ≠ 0 := sqdist_ne_zero hoo
  simp only [sqdist] at h1 h2 h3 h4
  have hg : (x.1 - d.1) ^ 2 + (x.2 - d.2) ^ 2 ≠ 0 := by
    intro hz
    obtain ⟨g1, g2⟩ := eq_zero_of_sq_add_sq_eq_zero _ _ hz
    exact hxd (Prod.ext (by linarith) (by linarith))
  -- `ob + oc - x - d` is orthogonal to `x - d`
  have hmg : (x.1 - d.1) * (ob.1 + oc.1 - x.1 - d.1)
      + (x.2 - d.2) * (ob.2 + oc.2 - x.2 - d.2) = 0 := by
    linear_combination (h1 - h2 + h3 - h4) / 2
  -- so is `ob - oc`
  have hsg : (x.1 - d.1) * (ob.1 - oc.1) + (x.2 - d.2) * (ob.2 - oc.2) = 0 := by
    linear_combination (h1 - h2 - h3 + h4) / 2
  -- hence the two are parallel
  have hcross : (ob.1 + oc.1 - x.1 - d.1) * (ob.2 - oc.2)
      - (ob.2 + oc.2 - x.2 - d.2) * (ob.1 - oc.1) = 0 := by
    have key := sq_norm_mul_cross_eq_zero (-(x.2 - d.2)) (x.1 - d.1)
      (ob.1 + oc.1 - x.1 - d.1) (ob.2 + oc.2 - x.2 - d.2)
      (ob.1 - oc.1) (ob.2 - oc.2) (by linear_combination -hmg) (by linear_combination -hsg)
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (by linear_combination h : (x.1 - d.1) ^ 2 + (x.2 - d.2) ^ 2 = 0) hg
    · exact h
  -- and they are orthogonal
  have hdot : (ob.1 + oc.1 - x.1 - d.1) * (ob.1 - oc.1)
      + (ob.2 + oc.2 - x.2 - d.2) * (ob.2 - oc.2) = 0 := by
    linear_combination (h1 + h2 - h3 - h4) / 2
  have hz := sqdist_mul_sqdist_eq_zero_of (ob.1 + oc.1, ob.2 + oc.2)
    (x.1 + d.1, x.2 + d.2) ob oc (by simp only [dotd]; linear_combination hdot)
    (by simp only [crossd]; linear_combination hcross)
  have h0 : sqdist (ob.1 + oc.1, ob.2 + oc.2) (x.1 + d.1, x.2 + d.2) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hne
  simp only [sqdist] at h0
  obtain ⟨e1, e2⟩ := eq_zero_of_sq_add_sq_eq_zero _ _ h0
  exact ⟨by linarith, by linarith⟩

/-- **Johnson's circle theorem**, in the form the census needs: if the three
faces of `a b c d` that contain `d` have one and the same circumradius, so does
the fourth face `a b c`.

The three circumcentres `oa, ob, oc` all lie at distance `√r` from `d`, and each
of `a`, `b`, `c` is the fourth vertex of a rhombus of side `√r`, so
`a = ob + oc - d` and so on; then `oa + ob + oc - 2d` is at distance `√r` from
each of `a`, `b`, `c`. -/
theorem johnson_fourth {a b c d : Pt} {r : ℝ}
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) (hncyc : ¬ Concyclic4 a b c d)
    (hA : CircumRadiusSq b c d r) (hB : CircumRadiusSq a c d r)
    (hC : CircumRadiusSq a b d r) : CircumRadiusSq a b c r := by
  obtain ⟨oa, ha1, ha2, ha3⟩ := hA
  obtain ⟨ob, hb1, hb2, hb3⟩ := hB
  obtain ⟨oc, hc1, hc2, hc3⟩ := hC
  have hoo1 : ob ≠ oc := by
    intro h; subst h
    exact hncyc (concyclic_of_common_center hb1 hc2 hb2 hb3)
  have hoo2 : oa ≠ oc := by
    intro h; subst h
    exact hncyc (concyclic_of_common_center hc1 ha1 ha2 ha3)
  have hoo3 : oa ≠ ob := by
    intro h; subst h
    exact hncyc (concyclic_of_common_center hb1 ha1 ha2 ha3)
  obtain ⟨ea1, ea2⟩ := centers_sum had hoo1 hb3 hb1 hc3 hc1
  obtain ⟨eb1, eb2⟩ := centers_sum hbd hoo2 ha3 ha1 hc3 hc2
  obtain ⟨ec1, ec2⟩ := centers_sum hcd hoo3 ha3 ha2 hb3 hb2
  refine ⟨(oa.1 + ob.1 + oc.1 - 2 * d.1, oa.2 + ob.2 + oc.2 - 2 * d.2), ?_, ?_, ?_⟩
  · show (oa.1 + ob.1 + oc.1 - 2 * d.1 - a.1) ^ 2
        + (oa.2 + ob.2 + oc.2 - 2 * d.2 - a.2) ^ 2 = r
    simp only [sqdist] at ha3
    linear_combination ha3 + (oa.1 + ob.1 + oc.1 - 2 * d.1 - a.1 + oa.1 - d.1) * ea1
      + (oa.2 + ob.2 + oc.2 - 2 * d.2 - a.2 + oa.2 - d.2) * ea2
  · show (oa.1 + ob.1 + oc.1 - 2 * d.1 - b.1) ^ 2
        + (oa.2 + ob.2 + oc.2 - 2 * d.2 - b.2) ^ 2 = r
    simp only [sqdist] at hb3
    linear_combination hb3 + (oa.1 + ob.1 + oc.1 - 2 * d.1 - b.1 + ob.1 - d.1) * eb1
      + (oa.2 + ob.2 + oc.2 - 2 * d.2 - b.2 + ob.2 - d.2) * eb2
  · show (oa.1 + ob.1 + oc.1 - 2 * d.1 - c.1) ^ 2
        + (oa.2 + ob.2 + oc.2 - 2 * d.2 - c.2) ^ 2 = r
    simp only [sqdist] at hc3
    linear_combination hc3 + (oa.1 + ob.1 + oc.1 - 2 * d.1 - c.1 + oc.1 - d.1) * ec1
      + (oa.2 + ob.2 + oc.2 - 2 * d.2 - c.2 + oc.2 - d.2) * ec2

/-- The table for a four-point block: one pair of equal radii, two
complementary pairs, or all six cells. -/
def quadAllowed : List ℕ := [1, 2, 4, 8, 12, 16, 18, 32, 33, 63]

theorem quadAllowed_length : quadAllowed.length = 10 := by decide

/-- **The table for rule (T).**  Six bits recording which of four reals agree,
where at least two agree and no three agree without the fourth, form one of ten
masks. -/
theorem quadTable {ra rb rc rd : ℝ} {b0 b1 b2 b3 b4 b5 : Bool}
    (h0 : b0 = true ↔ ra = rb) (h1 : b1 = true ↔ ra = rc) (h2 : b2 = true ↔ ra = rd)
    (h3 : b3 = true ↔ rb = rc) (h4 : b4 = true ↔ rb = rd) (h5 : b5 = true ↔ rc = rd)
    (j1 : ra = rb → ra = rc → ra = rd) (j2 : ra = rb → ra = rd → ra = rc)
    (j3 : ra = rc → ra = rd → ra = rb) (j4 : rb = rc → rb = rd → rb = ra)
    (hsome : ra = rb ∨ ra = rc ∨ ra = rd ∨ rb = rc ∨ rb = rd ∨ rc = rd) :
    quadAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true := by
  have F : ∀ {b : Bool} {u v : ℝ}, (b = true ↔ u = v) → u ≠ v → b = false :=
    fun h hne => Bool.eq_false_iff.mpr (fun hh => hne (h.mp hh))
  rcases eq_or_ne ra rb with hab | hab
  · rcases eq_or_ne ra rc with hac | hac
    · have had : ra = rd := j1 hab hac
      rw [h0.mpr hab, h1.mpr hac, h2.mpr had, h3.mpr (by rw [← hab]; exact hac),
        h4.mpr (by rw [← hab]; exact had), h5.mpr (by rw [← hac]; exact had)]
      all_goals decide
    · rcases eq_or_ne ra rd with had | had
      · exact absurd (j2 hab had) hac
      · have hbc : rb ≠ rc := fun h => hac (hab.trans h)
        have hbd : rb ≠ rd := fun h => had (hab.trans h)
        rcases eq_or_ne rc rd with hcd | hcd
        · rw [h0.mpr hab, F h1 hac, F h2 had, F h3 hbc, F h4 hbd, h5.mpr hcd]
          all_goals decide
        · rw [h0.mpr hab, F h1 hac, F h2 had, F h3 hbc, F h4 hbd, F h5 hcd]
          all_goals decide
  · rcases eq_or_ne ra rc with hac | hac
    · rcases eq_or_ne ra rd with had | had
      · exact absurd (j3 hac had) hab
      · have hbc : rb ≠ rc := fun h => hab (hac.trans h.symm)
        have hcd : rc ≠ rd := fun h => had (hac.trans h)
        rcases eq_or_ne rb rd with hbd | hbd
        · rw [F h0 hab, h1.mpr hac, F h2 had, F h3 hbc, h4.mpr hbd, F h5 hcd]
          all_goals decide
        · rw [F h0 hab, h1.mpr hac, F h2 had, F h3 hbc, F h4 hbd, F h5 hcd]
          all_goals decide
    · rcases eq_or_ne ra rd with had | had
      · have hbd : rb ≠ rd := fun h => hab (had.trans h.symm)
        have hcd : rc ≠ rd := fun h => hac (had.trans h.symm)
        rcases eq_or_ne rb rc with hbc | hbc
        · rw [F h0 hab, F h1 hac, h2.mpr had, h3.mpr hbc, F h4 hbd, F h5 hcd]
          all_goals decide
        · rw [F h0 hab, F h1 hac, h2.mpr had, F h3 hbc, F h4 hbd, F h5 hcd]
          all_goals decide
      · rcases eq_or_ne rb rc with hbc | hbc
        · rcases eq_or_ne rb rd with hbd | hbd
          · exact absurd (j4 hbc hbd) hab.symm
          · have hcd : rc ≠ rd := fun h => hbd (hbc.trans h)
            rw [F h0 hab, F h1 hac, F h2 had, h3.mpr hbc, F h4 hbd, F h5 hcd]
            all_goals decide
        · rcases eq_or_ne rb rd with hbd | hbd
          · have hcd : rc ≠ rd := fun h => hbc (hbd.trans h.symm)
            rw [F h0 hab, F h1 hac, F h2 had, F h3 hbc, h4.mpr hbd, F h5 hcd]
            all_goals decide
          · rcases eq_or_ne rc rd with hcd | hcd
            · rw [F h0 hab, F h1 hac, F h2 had, F h3 hbc, F h4 hbd, h5.mpr hcd]
              all_goals decide
            · rcases hsome with h | h | h | h | h | h
              · exact absurd h hab
              · exact absurd h hac
              · exact absurd h had
              · exact absurd h hbc
              · exact absurd h hbd
              · exact absurd h hcd

/-- The bit at the cell with apexes `{a,b}` and edge `{c,d}` says that the two
faces omitting `a` and omitting `b` have equal circumradius. -/
theorem bit_iff_radEq {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) {a b c d : Fin 6} {r s : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hr : CircumRadiusSq (p c) (p d) (p a) r)
    (hs : CircumRadiusSq (p c) (p d) (p b) s) :
    bitAt w (cellNum a b c d) = true ↔ r = s := by
  rw [bit_iff_psi hw hab hcd hac had hbc hbd]
  exact (eqRadSq_iff_psi (ne_of_gp hgp hcd) (ncol_of_gp hgp hcd hac.symm had.symm)
    (ncol_of_gp hgp hcd hbc.symm hbd.symm)
    (ncyc_of_gp hgp hcd hac.symm hbc.symm had.symm hbd.symm hab) hr hs).symm

set_option maxHeartbeats 1000000 in
/-- **Rule (T) as a table.**  The six cells inside the four-point subset
`{a,b,c,d}`, taken in increasing order and indexed by the six pairs of apexes in
lexicographic order, carry one of the ten masks of `quadAllowed`. -/
theorem quadBlock_mem {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) (a b c d : Fin 6)
    (i0 i1 i2 i3 i4 i5 : ℕ) (hlt : a < b ∧ b < c ∧ c < d)
    (h0 : i0 = cellNum a b c d) (h1 : i1 = cellNum a c b d) (h2 : i2 = cellNum a d b c)
    (h3 : i3 = cellNum b c a d) (h4 : i4 = cellNum b d a c) (h5 : i5 = cellNum c d a b) :
    quadAllowed.contains (bits6 (bitAt w i0) (bitAt w i1) (bitAt w i2) (bitAt w i3)
      (bitAt w i4) (bitAt w i5)) = true := by
  obtain ⟨lab, lbc, lcd⟩ := hlt
  have nab : a ≠ b := ne_of_lt lab
  have nbc : b ≠ c := ne_of_lt lbc
  have ncd : c ≠ d := ne_of_lt lcd
  have nac : a ≠ c := ne_of_lt (lab.trans lbc)
  have nbd : b ≠ d := ne_of_lt (lbc.trans lcd)
  have nad : a ≠ d := ne_of_lt (lab.trans (lbc.trans lcd))
  have cABC : ¬ Collinear3 (p a) (p b) (p c) := ncol_of_gp hgp nab nac nbc
  have cABD : ¬ Collinear3 (p a) (p b) (p d) := ncol_of_gp hgp nab nad nbd
  have cACD : ¬ Collinear3 (p a) (p c) (p d) := ncol_of_gp hgp nac nad ncd
  have cBCD : ¬ Collinear3 (p b) (p c) (p d) := ncol_of_gp hgp nbc nbd ncd
  obtain ⟨RA, hRA⟩ := exists_circumRadiusSq (a := p b) (b := p c) (c := p d) cBCD
  obtain ⟨RB, hRB⟩ := exists_circumRadiusSq (a := p a) (b := p c) (c := p d) cACD
  obtain ⟨RC, hRC⟩ := exists_circumRadiusSq (a := p a) (b := p b) (c := p d) cABD
  obtain ⟨RD, hRD⟩ := exists_circumRadiusSq (a := p a) (b := p b) (c := p c) cABC
  -- the six bits, read as equalities of the four radii
  have e0 : bitAt w i0 = true ↔ RA = RB := by
    rw [h0]
    exact (bit_iff_radEq hgp hw nab nac nad nbc nbd ncd
      (circumRadiusSq_perm hRB).2.2.1 (circumRadiusSq_perm hRA).2.2.1).trans eq_comm
  have e1 : bitAt w i1 = true ↔ RA = RC := by
    rw [h1]
    exact (bit_iff_radEq hgp hw nac nab nad nbc.symm ncd nbd
      (circumRadiusSq_perm hRC).2.2.1 (circumRadiusSq_perm hRA).1).trans eq_comm
  have e2 : bitAt w i2 = true ↔ RA = RD := by
    rw [h2]
    exact (bit_iff_radEq hgp hw nad nab nac nbd.symm ncd.symm nbc
      (circumRadiusSq_perm hRD).2.2.1 hRA).trans eq_comm
  have e3 : bitAt w i3 = true ↔ RB = RC := by
    rw [h3]
    exact (bit_iff_radEq hgp hw nbc nab.symm nbd nac.symm ncd nad
      (circumRadiusSq_perm hRC).1 (circumRadiusSq_perm hRB).1).trans eq_comm
  have e4 : bitAt w i4 = true ↔ RB = RD := by
    rw [h4]
    exact (bit_iff_radEq hgp hw nbd nab.symm nbc nad.symm ncd.symm nac
      (circumRadiusSq_perm hRD).1 hRB).trans eq_comm
  have e5 : bitAt w i5 = true ↔ RC = RD := by
    rw [h5]
    exact (bit_iff_radEq hgp hw ncd nac.symm nbc.symm nad.symm nbd.symm nab
      hRD hRC).trans eq_comm
  -- Johnson's theorem in the four orientations
  have j1 : RA = RB → RA = RC → RA = RD := by
    intro q1 q2
    have hB' : CircumRadiusSq (p a) (p c) (p d) RA := by rw [q1]; exact hRB
    have hC' : CircumRadiusSq (p a) (p b) (p d) RA := by rw [q2]; exact hRC
    exact (circumRadiusSq_unique cABC hRD (johnson_fourth (ne_of_gp hgp nad)
      (ne_of_gp hgp nbd) (ne_of_gp hgp ncd)
      (ncyc_of_gp hgp nab nac nad nbc nbd ncd) hRA hB' hC')).symm
  have j2 : RA = RB → RA = RD → RA = RC := by
    intro q1 q2
    have hB' : CircumRadiusSq (p a) (p c) (p d) RA := by rw [q1]; exact hRB
    have hD' : CircumRadiusSq (p a) (p b) (p c) RA := by rw [q2]; exact hRD
    exact (circumRadiusSq_unique cABD hRC (johnson_fourth (ne_of_gp hgp nac)
      (ne_of_gp hgp nbc) (ne_of_gp hgp ncd.symm)
      (ncyc_of_gp hgp nab nad nac nbd nbc ncd.symm)
      (circumRadiusSq_perm hRA).1 (circumRadiusSq_perm hB').1 hD')).symm
  have j3 : RA = RC → RA = RD → RA = RB := by
    intro q1 q2
    have hC' : CircumRadiusSq (p a) (p b) (p d) RA := by rw [q1]; exact hRC
    have hD' : CircumRadiusSq (p a) (p b) (p c) RA := by rw [q2]; exact hRD
    exact (circumRadiusSq_unique cACD hRB (johnson_fourth (ne_of_gp hgp nab)
      (ne_of_gp hgp nbc.symm) (ne_of_gp hgp nbd.symm)
      (ncyc_of_gp hgp nac nad nab ncd nbc.symm nbd.symm)
      (circumRadiusSq_perm hRA).2.2.1 (circumRadiusSq_perm hC').1
      (circumRadiusSq_perm hD').1)).symm
  have j4 : RB = RC → RB = RD → RB = RA := by
    intro q1 q2
    have hC' : CircumRadiusSq (p a) (p b) (p d) RB := by rw [q1]; exact hRC
    have hD' : CircumRadiusSq (p a) (p b) (p c) RB := by rw [q2]; exact hRD
    exact (circumRadiusSq_unique cBCD hRA (johnson_fourth (ne_of_gp hgp nab.symm)
      (ne_of_gp hgp nac.symm) (ne_of_gp hgp nad.symm)
      (ncyc_of_gp hgp nbc nbd nab.symm ncd nac.symm nad.symm)
      (circumRadiusSq_perm hRB).2.2.1 (circumRadiusSq_perm hC').2.2.1
      (circumRadiusSq_perm hD').2.2.1)).symm
  -- badness: some two of the four radii agree
  have fA : ∀ t : ℝ, face (p a) (p b) (p c) (p d) 0 t → t = RA := fun t h =>
    circumRadiusSq_unique cBCD h hRA
  have fB : ∀ t : ℝ, face (p a) (p b) (p c) (p d) 1 t → t = RB := fun t h =>
    circumRadiusSq_unique cACD h hRB
  have fC : ∀ t : ℝ, face (p a) (p b) (p c) (p d) 2 t → t = RC := fun t h =>
    circumRadiusSq_unique cABD h hRC
  have fD : ∀ t : ℝ, face (p a) (p b) (p c) (p d) 3 t → t = RD := fun t h =>
    circumRadiusSq_unique cABC h hRD
  have hsome : RA = RB ∨ RA = RC ∨ RA = RD ∨ RB = RC ∨ RB = RD ∨ RC = RD := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hcon
    refine hrep a b c d lab lbc lcd ?_
    intro i j hij r s hri hsj
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [fA r hri, fB s hsj]; exact n1
    · rw [fA r hri, fC s hsj]; exact n2
    · rw [fA r hri, fD s hsj]; exact n3
    · rw [fB r hri, fA s hsj]; exact n1.symm
    · exact absurd rfl hij
    · rw [fB r hri, fC s hsj]; exact n4
    · rw [fB r hri, fD s hsj]; exact n5
    · rw [fC r hri, fA s hsj]; exact n2.symm
    · rw [fC r hri, fB s hsj]; exact n4.symm
    · exact absurd rfl hij
    · rw [fC r hri, fD s hsj]; exact n6
    · rw [fD r hri, fA s hsj]; exact n3.symm
    · rw [fD r hri, fB s hsj]; exact n5.symm
    · rw [fD r hri, fC s hsj]; exact n6.symm
    · exact absurd rfl hij
  exact quadTable e0 e1 e2 e3 e4 e5 j1 j2 j3 j4 hsome

/-! ### The fifteen edge blocks -/

theorem edgeBlock_0 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (54, 60, 66, 72, 78, 84)) = true :=
  edgeBlock_mem hgp hw 0 1 2 3 4 5 54 60 66 72 78 84 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_1 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (36, 42, 48, 73, 79, 85)) = true :=
  edgeBlock_mem hgp hw 0 2 1 3 4 5 36 42 48 73 79 85 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_2 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (30, 43, 49, 61, 67, 86)) = true :=
  edgeBlock_mem hgp hw 0 3 1 2 4 5 30 43 49 61 67 86 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_3 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (31, 37, 50, 55, 68, 80)) = true :=
  edgeBlock_mem hgp hw 0 4 1 2 3 5 31 37 50 55 68 80 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_4 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (32, 38, 44, 56, 62, 74)) = true :=
  edgeBlock_mem hgp hw 0 5 1 2 3 4 32 38 44 56 62 74 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_5 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (12, 18, 24, 75, 81, 87)) = true :=
  edgeBlock_mem hgp hw 1 2 0 3 4 5 12 18 24 75 81 87 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_6 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (6, 19, 25, 63, 69, 88)) = true :=
  edgeBlock_mem hgp hw 1 3 0 2 4 5 6 19 25 63 69 88 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_7 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (7, 13, 26, 57, 70, 82)) = true :=
  edgeBlock_mem hgp hw 1 4 0 2 3 5 7 13 26 57 70 82 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_8 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (8, 14, 20, 58, 64, 76)) = true :=
  edgeBlock_mem hgp hw 1 5 0 2 3 4 8 14 20 58 64 76 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_9 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (0, 21, 27, 45, 51, 89)) = true :=
  edgeBlock_mem hgp hw 2 3 0 1 4 5 0 21 27 45 51 89 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_10 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (1, 15, 28, 39, 52, 83)) = true :=
  edgeBlock_mem hgp hw 2 4 0 1 3 5 1 15 28 39 52 83 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_11 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (2, 16, 22, 40, 46, 77)) = true :=
  edgeBlock_mem hgp hw 2 5 0 1 3 4 2 16 22 40 46 77 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_12 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (3, 9, 29, 33, 53, 71)) = true :=
  edgeBlock_mem hgp hw 3 4 0 1 2 5 3 9 29 33 53 71 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_13 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (4, 10, 23, 34, 47, 65)) = true :=
  edgeBlock_mem hgp hw 3 5 0 1 2 4 4 10 23 34 47 65 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem edgeBlock_14 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    matchAllowed.contains (blockVal w (5, 11, 17, 35, 41, 59)) = true :=
  edgeBlock_mem hgp hw 4 5 0 1 2 3 5 11 17 35 41 59 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The fifteen edge blocks, one for each of the fifteen edges. -/
def edgeBlocks : List Block :=
  [(54, 60, 66, 72, 78, 84),
   (36, 42, 48, 73, 79, 85),
   (30, 43, 49, 61, 67, 86),
   (31, 37, 50, 55, 68, 80),
   (32, 38, 44, 56, 62, 74),
   (12, 18, 24, 75, 81, 87),
   (6, 19, 25, 63, 69, 88),
   (7, 13, 26, 57, 70, 82),
   (8, 14, 20, 58, 64, 76),
   (0, 21, 27, 45, 51, 89),
   (1, 15, 28, 39, 52, 83),
   (2, 16, 22, 40, 46, 77),
   (3, 9, 29, 33, 53, 71),
   (4, 10, 23, 34, 47, 65),
   (5, 11, 17, 35, 41, 59)]

theorem edgeBlocks_length : edgeBlocks.length = 15 := by decide

/-- `w` passes rule (C) on every edge block. -/
def consistentC (w : Mask) : Bool :=
  edgeBlocks.all (fun B => matchAllowed.contains (blockVal w B))

theorem edgeBlocks_ok {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    ∀ B ∈ edgeBlocks, matchAllowed.contains (blockVal w B) = true := by
  simp only [edgeBlocks]
  refine List.forall_mem_cons.mpr ⟨edgeBlock_0 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_1 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_2 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_3 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_4 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_5 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_6 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_7 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_8 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_9 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_10 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_11 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_12 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_13 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨edgeBlock_14 hgp hw, ?_⟩
  simp

/-- **Rule (C) is sound.**  A mask carried by six points in general position
passes the edge-block table. -/
theorem consistentC_of_carries {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) : consistentC w = true :=
  List.all_eq_true.mpr (edgeBlocks_ok hgp hw)

/-! ### The fifteen apex-pair blocks -/

theorem apexBlock_0 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (0, 1, 2, 3, 4, 5)) = true :=
  apexBlock_mem hgp hw 0 1 2 3 4 5 0 1 2 3 4 5 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_1 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (6, 7, 8, 9, 10, 11)) = true :=
  apexBlock_mem hgp hw 0 2 1 3 4 5 6 7 8 9 10 11 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_2 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (12, 13, 14, 15, 16, 17)) = true :=
  apexBlock_mem hgp hw 0 3 1 2 4 5 12 13 14 15 16 17 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_3 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (18, 19, 20, 21, 22, 23)) = true :=
  apexBlock_mem hgp hw 0 4 1 2 3 5 18 19 20 21 22 23 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_4 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (24, 25, 26, 27, 28, 29)) = true :=
  apexBlock_mem hgp hw 0 5 1 2 3 4 24 25 26 27 28 29 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_5 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (30, 31, 32, 33, 34, 35)) = true :=
  apexBlock_mem hgp hw 1 2 0 3 4 5 30 31 32 33 34 35 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_6 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (36, 37, 38, 39, 40, 41)) = true :=
  apexBlock_mem hgp hw 1 3 0 2 4 5 36 37 38 39 40 41 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_7 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (42, 43, 44, 45, 46, 47)) = true :=
  apexBlock_mem hgp hw 1 4 0 2 3 5 42 43 44 45 46 47 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_8 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (48, 49, 50, 51, 52, 53)) = true :=
  apexBlock_mem hgp hw 1 5 0 2 3 4 48 49 50 51 52 53 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_9 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (54, 55, 56, 57, 58, 59)) = true :=
  apexBlock_mem hgp hw 2 3 0 1 4 5 54 55 56 57 58 59 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_10 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (60, 61, 62, 63, 64, 65)) = true :=
  apexBlock_mem hgp hw 2 4 0 1 3 5 60 61 62 63 64 65 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_11 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (66, 67, 68, 69, 70, 71)) = true :=
  apexBlock_mem hgp hw 2 5 0 1 3 4 66 67 68 69 70 71 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_12 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (72, 73, 74, 75, 76, 77)) = true :=
  apexBlock_mem hgp hw 3 4 0 1 2 5 72 73 74 75 76 77 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_13 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (78, 79, 80, 81, 82, 83)) = true :=
  apexBlock_mem hgp hw 3 5 0 1 2 4 78 79 80 81 82 83 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem apexBlock_14 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    partAllowed.contains (blockVal w (84, 85, 86, 87, 88, 89)) = true :=
  apexBlock_mem hgp hw 4 5 0 1 2 3 84 85 86 87 88 89 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The fifteen apex-pair blocks, one for each of the fifteen pairs. -/
def apexBlocks : List Block :=
  [(0, 1, 2, 3, 4, 5),
   (6, 7, 8, 9, 10, 11),
   (12, 13, 14, 15, 16, 17),
   (18, 19, 20, 21, 22, 23),
   (24, 25, 26, 27, 28, 29),
   (30, 31, 32, 33, 34, 35),
   (36, 37, 38, 39, 40, 41),
   (42, 43, 44, 45, 46, 47),
   (48, 49, 50, 51, 52, 53),
   (54, 55, 56, 57, 58, 59),
   (60, 61, 62, 63, 64, 65),
   (66, 67, 68, 69, 70, 71),
   (72, 73, 74, 75, 76, 77),
   (78, 79, 80, 81, 82, 83),
   (84, 85, 86, 87, 88, 89)]

theorem apexBlocks_length : apexBlocks.length = 15 := by decide

/-- `w` passes rule (B) on every apex-pair block. -/
def consistentB (w : Mask) : Bool :=
  apexBlocks.all (fun B => partAllowed.contains (blockVal w B))

theorem apexBlocks_ok {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) :
    ∀ B ∈ apexBlocks, partAllowed.contains (blockVal w B) = true := by
  simp only [apexBlocks]
  refine List.forall_mem_cons.mpr ⟨apexBlock_0 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_1 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_2 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_3 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_4 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_5 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_6 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_7 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_8 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_9 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_10 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_11 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_12 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_13 hgp hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨apexBlock_14 hgp hw, ?_⟩
  simp

/-- **Rule (B) is sound.** -/
theorem consistentB_of_carries {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hw : Carries p w) : consistentB w = true :=
  List.all_eq_true.mpr (apexBlocks_ok hgp hw)

/-! ### The fifteen four-point blocks -/

theorem quadBlock_0 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (0, 6, 12, 30, 36, 54)) = true :=
  quadBlock_mem hgp hrep hw 0 1 2 3 0 6 12 30 36 54 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_1 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (1, 7, 18, 31, 42, 60)) = true :=
  quadBlock_mem hgp hrep hw 0 1 2 4 1 7 18 31 42 60 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_2 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (2, 8, 24, 32, 48, 66)) = true :=
  quadBlock_mem hgp hrep hw 0 1 2 5 2 8 24 32 48 66 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_3 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (3, 13, 19, 37, 43, 72)) = true :=
  quadBlock_mem hgp hrep hw 0 1 3 4 3 13 19 37 43 72 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_4 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (4, 14, 25, 38, 49, 78)) = true :=
  quadBlock_mem hgp hrep hw 0 1 3 5 4 14 25 38 49 78 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_5 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (5, 20, 26, 44, 50, 84)) = true :=
  quadBlock_mem hgp hrep hw 0 1 4 5 5 20 26 44 50 84 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_6 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (9, 15, 21, 55, 61, 73)) = true :=
  quadBlock_mem hgp hrep hw 0 2 3 4 9 15 21 55 61 73 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_7 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (10, 16, 27, 56, 67, 79)) = true :=
  quadBlock_mem hgp hrep hw 0 2 3 5 10 16 27 56 67 79 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_8 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (11, 22, 28, 62, 68, 85)) = true :=
  quadBlock_mem hgp hrep hw 0 2 4 5 11 22 28 62 68 85 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_9 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (17, 23, 29, 74, 80, 86)) = true :=
  quadBlock_mem hgp hrep hw 0 3 4 5 17 23 29 74 80 86 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_10 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (33, 39, 45, 57, 63, 75)) = true :=
  quadBlock_mem hgp hrep hw 1 2 3 4 33 39 45 57 63 75 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_11 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (34, 40, 51, 58, 69, 81)) = true :=
  quadBlock_mem hgp hrep hw 1 2 3 5 34 40 51 58 69 81 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_12 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (35, 46, 52, 64, 70, 87)) = true :=
  quadBlock_mem hgp hrep hw 1 2 4 5 35 46 52 64 70 87 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_13 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (41, 47, 53, 76, 82, 88)) = true :=
  quadBlock_mem hgp hrep hw 1 3 4 5 41 47 53 76 82 88 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem quadBlock_14 {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    quadAllowed.contains (blockVal w (59, 65, 71, 77, 83, 89)) = true :=
  quadBlock_mem hgp hrep hw 2 3 4 5 59 65 71 77 83 89 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The fifteen four-point blocks, one for each four-point subset. -/
def quadBlocks : List Block :=
  [(0, 6, 12, 30, 36, 54),
   (1, 7, 18, 31, 42, 60),
   (2, 8, 24, 32, 48, 66),
   (3, 13, 19, 37, 43, 72),
   (4, 14, 25, 38, 49, 78),
   (5, 20, 26, 44, 50, 84),
   (9, 15, 21, 55, 61, 73),
   (10, 16, 27, 56, 67, 79),
   (11, 22, 28, 62, 68, 85),
   (17, 23, 29, 74, 80, 86),
   (33, 39, 45, 57, 63, 75),
   (34, 40, 51, 58, 69, 81),
   (35, 46, 52, 64, 70, 87),
   (41, 47, 53, 76, 82, 88),
   (59, 65, 71, 77, 83, 89)]

theorem quadBlocks_length : quadBlocks.length = 15 := by decide

/-- `w` passes rule (T) on every four-point block. -/
def consistentA (w : Mask) : Bool :=
  quadBlocks.all (fun B => quadAllowed.contains (blockVal w B))

theorem quadBlocks_ok {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) :
    ∀ B ∈ quadBlocks, quadAllowed.contains (blockVal w B) = true := by
  simp only [quadBlocks]
  refine List.forall_mem_cons.mpr ⟨quadBlock_0 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_1 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_2 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_3 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_4 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_5 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_6 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_7 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_8 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_9 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_10 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_11 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_12 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_13 hgp hrep hw, ?_⟩
  refine List.forall_mem_cons.mpr ⟨quadBlock_14 hgp hrep hw, ?_⟩
  simp

/-- **Rule (T) is sound.** -/
theorem consistentA_of_carries {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) : consistentA w = true :=
  List.all_eq_true.mpr (quadBlocks_ok hgp hrep hw)

/-! ## The three rules together -/

/-- The whole node test: the forty-five six-cell blocks of a mask lie in their
tables. -/
def consistent (w : Mask) : Bool := consistentA w && consistentB w && consistentC w

/-- **The forty-five block tables are sound.**  Every mask carried by six points
in general position all of whose four-point subsets repeat a circumradius passes
the node test.  (This says nothing about the converse: a mask may pass the test
without being carried by any configuration.) -/
theorem consistent_of_carries {p : Fin 6 → Pt} {w : Mask} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) (hw : Carries p w) : consistent w = true := by
  simp only [consistent, Bool.and_eq_true]
  exact ⟨⟨consistentA_of_carries hgp hrep hw, consistentB_of_carries hgp hw⟩,
    consistentC_of_carries hgp hw⟩

/-- The mask of `fun i => p (σ i)`, read off from the mask of `p`. -/
def permMask (σ : Equiv.Perm (Fin 6)) (w : Mask) : Mask :=
  ofBits 90 (fun i =>
    bitAt w (cellNum (σ (cellOf i).1.1) (σ (cellOf i).1.2)
      (σ (cellOf i).2.1) (σ (cellOf i).2.2)))

theorem permMask_lt (σ : Equiv.Perm (Fin 6)) (w : Mask) : permMask σ w < 2 ^ 90 :=
  ofBits_lt _ _

/-- **The action is sound.**  If `p` carries `w` then the relabelled
configuration carries the relabelled mask. -/
theorem carries_comp {p : Fin 6 → Pt} {w : Mask} (σ : Equiv.Perm (Fin 6))
    (hw : Carries p w) : Carries (fun i => p (σ i)) (permMask σ w) := by
  intro i hi
  rw [permMask, bitAt_ofBits 90 _ i hi]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := cellOf_distinct ⟨i, hi⟩
  obtain ⟨hlt, heq⟩ := cellNum_spec (σ (cellOf i).1.1) (σ (cellOf i).1.2)
    (σ (cellOf i).2.1) (σ (cellOf i).2.2)
    (σ.injective.ne d1) (σ.injective.ne d2) (σ.injective.ne d3)
    (σ.injective.ne d4) (σ.injective.ne d5) (σ.injective.ne d6)
  rw [← hw _ hlt]
  simp only [cellPsi, heq]
  exact (psi_minmax_eq_zero p _ _ _ _).symm

theorem supports_comp {p : Fin 6 → Pt} {w : Mask} (σ : Equiv.Perm (Fin 6))
    (hw : Carries p w) : Supports (fun i => p (σ i)) (permMask σ w) :=
  supports_of_carries (carries_comp σ hw)

/-! ## The 35 representatives -/

/-- The mask of the octahedral configuration: the three pairs are `{0,5}`,
`{1,4}`, `{2,3}`, and every one of the 18 cells whose apex pair is one of the
three is a witness.  This is the one representative of the 35 that is known to
be realized. -/
def censusK0 : Mask := 1135184184084529152

/-- The remaining 34 representatives, in the order produced by the
enumeration.  Each is the least element of its orbit under the 720 relabellings
of the six points. -/
def censusRest : List Mask :=
  [184800786828712083585, 4907131196476393390608,
   4934540371430318555265, 19074230610381679895041,
   19101637269858998601732, 19101637269863264190496,
   19738061199847925489685, 19796266034346135666690,
   52112637776347992703680, 56763522831400264826960,
   57295614475181794314240, 57575197862118925271058,
   99354312205285548130561, 321419383917544127594562,
   321419383917544530313282, 321425873218542288273672,
   321425873218679727227136, 322027694021967371309058,
   322303244230729373130848, 322304397152704277779468,
   359787030440226329731588, 360264956801041643864353,
   453513248141008326754436, 453513356179089397942340,
   19966497677405743500001544, 19966497823737547017429508,
   19966792832064260694624258, 19967087853834598909231618,
   19967383271954623119001604, 19985977319735291164623376,
   20023166075136716235374660, 20023461099188482019461124,
   20023461225293663191439364, 20025197522889238378840144]

/-- The 35 representatives. -/
def censusList : List Mask := censusK0 :: censusRest

theorem censusRest_length : censusRest.length = 34 := by decide

theorem censusList_length : censusList.length = 35 := by decide

theorem censusList_nodup : censusList.Nodup := by decide

theorem censusList_lt : ∀ w ∈ censusList, w < 2 ^ 90 := by decide

/-- **The census statement.**  Every six-point configuration in general position
all of whose four-point subsets repeat a circumradius carries a mask whose orbit
under the relabellings of the six points meets the list of 35 representatives.

This is the statement that the search transcript is meant to establish.  It is
**not** proved in this file. -/
def CensusComplete : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → EveryQuadrupleRepeats p →
    ∀ w : Mask, w < 2 ^ 90 → Carries p w →
      ∃ σ : Equiv.Perm (Fin 6), permMask σ w ∈ censusList



/-!
## The chain

A node of the search is a pair of masks `(pos, neg)`: the cells forced to be
witnesses and the cells forced not to be.  Two statements can be attached to a
node.

* `Refutes pos neg` -- no bad configuration extends the node;
* `Settles pos neg` -- every bad configuration that extends the node carries a
  mask whose orbit meets the list of 35 representatives.

Only the second composes all the way up, because the root node `(0,0)` *is*
extended by a configuration (the octahedral one), so `Refutes 0 0` is false
while `Settles 0 0` is exactly `CensusComplete`.  `Refutes` is the node-local
form: it is what the tables give at a node they contradict, and it implies
`Settles` there.
-/

/-- Six bits as a tuple, which is the form the node test reads them in. -/
abbrev Pat := Bool × Bool × Bool × Bool × Bool × Bool

/-- The six bits of `w` at the cells of a block. -/
def patAt (w : Mask) (B : Block) : Pat :=
  (bitAt w B.1, bitAt w B.2.1, bitAt w B.2.2.1, bitAt w B.2.2.2.1,
    bitAt w B.2.2.2.2.1, bitAt w B.2.2.2.2.2)

/-- Flip all six bits. -/
def negPat (q : Pat) : Pat :=
  (!q.1, !q.2.1, !q.2.2.1, !q.2.2.2.1, !q.2.2.2.2.1, !q.2.2.2.2.2)

/-- The ten allowed patterns of a four-point block (rule (T)), in the order of
`quadAllowed`. -/
def quadPats : List Pat :=
  [(true, false, false, false, false, false),
   (false, true, false, false, false, false),
   (false, false, true, false, false, false),
   (false, false, false, true, false, false),
   (false, false, true, true, false, false),
   (false, false, false, false, true, false),
   (false, true, false, false, true, false),
   (false, false, false, false, false, true),
   (true, false, false, false, false, true),
   (true, true, true, true, true, true)]

/-- The fifteen allowed patterns of an apex-pair block (rule (B)). -/
def partPats : List Pat :=
  [(false, false, false, false, false, false),
   (true, false, false, false, false, false),
   (false, true, false, false, false, false),
   (false, false, true, false, false, false),
   (false, false, false, true, false, false),
   (true, true, false, true, false, false),
   (false, false, true, true, false, false),
   (false, false, false, false, true, false),
   (false, true, false, false, true, false),
   (true, false, true, false, true, false),
   (false, false, false, false, false, true),
   (true, false, false, false, false, true),
   (false, true, true, false, false, true),
   (false, false, false, true, true, true),
   (true, true, true, true, true, true)]

/-- The ten allowed patterns of an edge block (rule (C)). -/
def matchPats : List Pat :=
  [(false, false, false, false, false, false),
   (true, false, false, false, false, false),
   (false, true, false, false, false, false),
   (false, false, true, false, false, false),
   (false, false, false, true, false, false),
   (false, false, true, true, false, false),
   (false, false, false, false, true, false),
   (false, true, false, false, true, false),
   (false, false, false, false, false, true),
   (true, false, false, false, false, true)]

/-- The forty-five blocks of the node test: the fifteen four-point blocks first
(indices 0-14, the ones the search branches on), then the fifteen apex-pair
blocks, then the fifteen edge blocks. -/
def nodeRules : List (Block × List Pat) :=
  [((0, 6, 12, 30, 36, 54), quadPats),
   ((1, 7, 18, 31, 42, 60), quadPats),
   ((2, 8, 24, 32, 48, 66), quadPats),
   ((3, 13, 19, 37, 43, 72), quadPats),
   ((4, 14, 25, 38, 49, 78), quadPats),
   ((5, 20, 26, 44, 50, 84), quadPats),
   ((9, 15, 21, 55, 61, 73), quadPats),
   ((10, 16, 27, 56, 67, 79), quadPats),
   ((11, 22, 28, 62, 68, 85), quadPats),
   ((17, 23, 29, 74, 80, 86), quadPats),
   ((33, 39, 45, 57, 63, 75), quadPats),
   ((34, 40, 51, 58, 69, 81), quadPats),
   ((35, 46, 52, 64, 70, 87), quadPats),
   ((41, 47, 53, 76, 82, 88), quadPats),
   ((59, 65, 71, 77, 83, 89), quadPats),
   ((0, 1, 2, 3, 4, 5), partPats),
   ((6, 7, 8, 9, 10, 11), partPats),
   ((12, 13, 14, 15, 16, 17), partPats),
   ((18, 19, 20, 21, 22, 23), partPats),
   ((24, 25, 26, 27, 28, 29), partPats),
   ((30, 31, 32, 33, 34, 35), partPats),
   ((36, 37, 38, 39, 40, 41), partPats),
   ((42, 43, 44, 45, 46, 47), partPats),
   ((48, 49, 50, 51, 52, 53), partPats),
   ((54, 55, 56, 57, 58, 59), partPats),
   ((60, 61, 62, 63, 64, 65), partPats),
   ((66, 67, 68, 69, 70, 71), partPats),
   ((72, 73, 74, 75, 76, 77), partPats),
   ((78, 79, 80, 81, 82, 83), partPats),
   ((84, 85, 86, 87, 88, 89), partPats),
   ((54, 60, 66, 72, 78, 84), matchPats),
   ((36, 42, 48, 73, 79, 85), matchPats),
   ((30, 43, 49, 61, 67, 86), matchPats),
   ((31, 37, 50, 55, 68, 80), matchPats),
   ((32, 38, 44, 56, 62, 74), matchPats),
   ((12, 18, 24, 75, 81, 87), matchPats),
   ((6, 19, 25, 63, 69, 88), matchPats),
   ((7, 13, 26, 57, 70, 82), matchPats),
   ((8, 14, 20, 58, 64, 76), matchPats),
   ((0, 21, 27, 45, 51, 89), matchPats),
   ((1, 15, 28, 39, 52, 83), matchPats),
   ((2, 16, 22, 40, 46, 77), matchPats),
   ((3, 9, 29, 33, 53, 71), matchPats),
   ((4, 10, 23, 34, 47, 65), matchPats),
   ((5, 11, 17, 35, 41, 59), matchPats)]

theorem nodeRules_length : nodeRules.length = 45 := by decide



/-! ### From the packed tables of the three rules to patterns -/

theorem quadPat_of_bits {b0 b1 b2 b3 b4 b5 : Bool}
    (h : quadAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true) :
    ((b0, b1, b2, b3, b4, b5) : Pat) ∈ quadPats := by
  revert h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem partPat_of_bits {b0 b1 b2 b3 b4 b5 : Bool}
    (h : partAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true) :
    ((b0, b1, b2, b3, b4, b5) : Pat) ∈ partPats := by
  revert h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem matchPat_of_bits {b0 b1 b2 b3 b4 b5 : Bool}
    (h : matchAllowed.contains (bits6 b0 b1 b2 b3 b4 b5) = true) :
    ((b0, b1, b2, b3, b4, b5) : Pat) ∈ matchPats := by
  revert h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem pat_quad {w : Mask} {B : Block}
    (h : quadAllowed.contains (blockVal w B) = true) : patAt w B ∈ quadPats :=
  @quadPat_of_bits (bitAt w B.1) (bitAt w B.2.1) (bitAt w B.2.2.1) (bitAt w B.2.2.2.1)
    (bitAt w B.2.2.2.2.1) (bitAt w B.2.2.2.2.2) h

theorem pat_part {w : Mask} {B : Block}
    (h : partAllowed.contains (blockVal w B) = true) : patAt w B ∈ partPats :=
  @partPat_of_bits (bitAt w B.1) (bitAt w B.2.1) (bitAt w B.2.2.1) (bitAt w B.2.2.2.1)
    (bitAt w B.2.2.2.2.1) (bitAt w B.2.2.2.2.2) h

theorem pat_match {w : Mask} {B : Block}
    (h : matchAllowed.contains (blockVal w B) = true) : patAt w B ∈ matchPats :=
  @matchPat_of_bits (bitAt w B.1) (bitAt w B.2.1) (bitAt w B.2.2.1) (bitAt w B.2.2.2.1)
    (bitAt w B.2.2.2.2.1) (bitAt w B.2.2.2.2.2) h

/-- **The forty-five tables, read as patterns.**  The three soundness statements
of the packed tables are exactly what the node test needs. -/
theorem nodeRules_pat {w : Mask}
    (hq : ∀ B ∈ quadBlocks, quadAllowed.contains (blockVal w B) = true)
    (hb : ∀ B ∈ apexBlocks, partAllowed.contains (blockVal w B) = true)
    (hc : ∀ B ∈ edgeBlocks, matchAllowed.contains (blockVal w B) = true) :
    ∀ r ∈ nodeRules, patAt w r.1 ∈ r.2 := by
  simp only [nodeRules]
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_quad (hq _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_part (hb _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  refine List.forall_mem_cons.mpr ⟨pat_match (hc _ (by decide)), ?_⟩
  simp

/-! ### Bits -/

theorem bitAt_eq_testBit (w i : ℕ) : bitAt w i = w.testBit i := by
  rw [bitAt, Nat.testBit_eq_decide_div_mod_eq]

theorem bitAt_or (x y i : ℕ) : bitAt (x ||| y) i = (bitAt x i || bitAt y i) := by
  simp only [bitAt_eq_testBit, Nat.testBit_or]

theorem bitAt_zero_mask (i : ℕ) : bitAt 0 i = false := by
  simp [bitAt]

theorem bitAt_eq_false_of_lt {w n i : ℕ} (hw : w < 2 ^ n) (hi : n ≤ i) :
    bitAt w i = false := by
  have h2 : w < 2 ^ i := lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hi)
  simp [bitAt, Nat.div_eq_of_lt h2]

theorem ofBits_congr : ∀ (n : ℕ) (f g : ℕ → Bool), (∀ i < n, f i = g i) →
    ofBits n f = ofBits n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
      show (if f 0 then 1 else 0) + 2 * ofBits n (fun k => f (k + 1))
        = (if g 0 then 1 else 0) + 2 * ofBits n (fun k => g (k + 1))
      rw [h 0 (Nat.succ_pos n),
        ofBits_congr n (fun k => f (k + 1)) (fun k => g (k + 1)) (fun i hi => h (i + 1) (by omega))]

/-! ### Node states -/

/-- Every cell that the node forces to be a witness is one. -/
def Below (pos w : Mask) : Prop := ∀ i, bitAt pos i = true → bitAt w i = true

/-- No cell that the node forces not to be a witness is one. -/
def Apart (neg w : Mask) : Prop := ∀ i, bitAt neg i = true → bitAt w i = false

theorem below_zero (w : Mask) : Below 0 w := by
  intro i h; rw [bitAt_zero_mask] at h; exact absurd h (by simp)

theorem apart_zero (w : Mask) : Apart 0 w := by
  intro i h; rw [bitAt_zero_mask] at h; exact absurd h (by simp)

theorem below_or {x y w : Mask} (hx : Below x w) (hy : Below y w) : Below (x ||| y) w := by
  intro i h
  rw [bitAt_or] at h
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact hx i h'
  · exact hy i h'

theorem apart_or {x y w : Mask} (hx : Apart x w) (hy : Apart y w) : Apart (x ||| y) w := by
  intro i h
  rw [bitAt_or] at h
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact hx i h'
  · exact hy i h'

/-- **The census form of a node theorem.**  Every bad six-point configuration
whose mask extends the node carries a mask in one of the 35 orbits. -/
def Settles (pos neg : Mask) : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → EveryQuadrupleRepeats p →
    ∀ w : Mask, w < 2 ^ 90 → Carries p w → Below pos w → Apart neg w →
      ∃ σ : Equiv.Perm (Fin 6), permMask σ w ∈ censusList

/-- **The refutation form of a node theorem.**  No bad six-point configuration
extends the node at all. -/
def Refutes (pos neg : Mask) : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → EveryQuadrupleRepeats p →
    ∀ w : Mask, w < 2 ^ 90 → Carries p w → Below pos w → Apart neg w → False

theorem settles_of_refutes {pos neg : Mask} (h : Refutes pos neg) : Settles pos neg :=
  fun p hgp hrep w hlt hw hb ha => (h p hgp hrep w hlt hw hb ha).elim

/-- **The root is the census statement.**  `Settles 0 0` and `CensusComplete`
are the same statement. -/
theorem censusComplete_iff_settles : CensusComplete ↔ Settles 0 0 := by
  constructor
  · intro h p hgp hrep w hlt hw _ _
    exact h p hgp hrep w hlt hw
  · intro h p hgp hrep w hlt hw
    exact h p hgp hrep w hlt hw (below_zero w) (apart_zero w)

/-! ### The node test -/

/-- A pattern bit is compatible with what the node forces. -/
def compatBit (bp bn q : Bool) : Bool := (!bp || q) && (!bn || !q)

def compatPat (pp np q : Pat) : Bool :=
  compatBit pp.1 np.1 q.1 && compatBit pp.2.1 np.2.1 q.2.1 &&
    compatBit pp.2.2.1 np.2.2.1 q.2.2.1 && compatBit pp.2.2.2.1 np.2.2.2.1 q.2.2.2.1 &&
    compatBit pp.2.2.2.2.1 np.2.2.2.2.1 q.2.2.2.2.1 &&
    compatBit pp.2.2.2.2.2 np.2.2.2.2.2 q.2.2.2.2.2

/-- The block still has an allowed pattern compatible with the node. -/
def okBlock (pos neg : Mask) (r : Block × List Pat) : Bool :=
  r.2.any (fun q => compatPat (patAt pos r.1) (patAt neg r.1) q)

/-- **The node test.**  All forty-five blocks still have an allowed pattern. -/
def okNode (pos neg : Mask) : Bool := nodeRules.all (okBlock pos neg)

theorem compatBit_of {bp bn bw : Bool} (hp : bp = true → bw = true)
    (hn : bn = true → bw = false) : compatBit bp bn bw = true := by
  cases bp <;> cases bn <;> cases bw <;> simp_all [compatBit]

theorem okNode_of_below {pos neg w : Mask} (hb : Below pos w) (ha : Apart neg w)
    (hs : ∀ r ∈ nodeRules, patAt w r.1 ∈ r.2) : okNode pos neg = true := by
  refine List.all_eq_true.mpr ?_
  intro r hr
  refine List.any_eq_true.mpr ⟨patAt w r.1, hs r hr, ?_⟩
  simp only [compatPat, patAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨compatBit_of (hb _) (ha _), compatBit_of (hb _) (ha _)⟩,
    compatBit_of (hb _) (ha _)⟩, compatBit_of (hb _) (ha _)⟩,
    compatBit_of (hb _) (ha _)⟩, compatBit_of (hb _) (ha _)⟩

/-- The soundness of the forty-five tables, as one statement to thread through
the chain. -/
def TablesSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → EveryQuadrupleRepeats p →
    ∀ w : Mask, Carries p w → ∀ r ∈ nodeRules, patAt w r.1 ∈ r.2

/-- **Lemma 1: a node the tables contradict is refuted.** -/
theorem refutes_of_okNode_eq_false (hT : TablesSound) {pos neg : Mask}
    (h : okNode pos neg = false) : Refutes pos neg := by
  intro p hgp hrep w hlt hw hb ha
  rw [okNode_of_below hb ha (hT p hgp hrep w hw)] at h
  exact absurd h (by simp)

/-! ### Branching -/

/-- Bit `i` of the mask that a pattern on a block forces. -/
def selBit (B : Block) (q : Pat) (i : ℕ) : Bool :=
  (decide (i = B.1) && q.1) || (decide (i = B.2.1) && q.2.1) ||
    (decide (i = B.2.2.1) && q.2.2.1) || (decide (i = B.2.2.2.1) && q.2.2.2.1) ||
    (decide (i = B.2.2.2.2.1) && q.2.2.2.2.1) || (decide (i = B.2.2.2.2.2) && q.2.2.2.2.2)

/-- The mask that a pattern on a block forces. -/
def selMask (B : Block) (q : Pat) : Mask := ofBits 90 (selBit B q)

theorem of_selBit {B : Block} {q : Pat} {i : ℕ} (h : selBit B q i = true) :
    (i = B.1 ∧ q.1 = true) ∨ (i = B.2.1 ∧ q.2.1 = true) ∨
    (i = B.2.2.1 ∧ q.2.2.1 = true) ∨ (i = B.2.2.2.1 ∧ q.2.2.2.1 = true) ∨
    (i = B.2.2.2.2.1 ∧ q.2.2.2.2.1 = true) ∨ (i = B.2.2.2.2.2 ∧ q.2.2.2.2.2 = true) := by
  simp only [selBit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem bitAt_selMask {B : Block} {q : Pat} {i : ℕ} (h : bitAt (selMask B q) i = true) :
    selBit B q i = true := by
  rcases lt_or_ge i 90 with hlt | hge
  · rw [selMask, bitAt_ofBits 90 _ i hlt] at h; exact h
  · rw [selMask, bitAt_eq_false_of_lt (ofBits_lt 90 (selBit B q)) hge] at h
    exact absurd h (by simp)

theorem below_selMask {w : Mask} {B : Block} {q : Pat} (h : patAt w B = q) :
    Below (selMask B q) w := by
  intro i hi
  have e0 : bitAt w B.1 = q.1 := congrArg (fun z : Pat => z.1) h
  have e1 : bitAt w B.2.1 = q.2.1 := congrArg (fun z : Pat => z.2.1) h
  have e2 : bitAt w B.2.2.1 = q.2.2.1 := congrArg (fun z : Pat => z.2.2.1) h
  have e3 : bitAt w B.2.2.2.1 = q.2.2.2.1 := congrArg (fun z : Pat => z.2.2.2.1) h
  have e4 : bitAt w B.2.2.2.2.1 = q.2.2.2.2.1 := congrArg (fun z : Pat => z.2.2.2.2.1) h
  have e5 : bitAt w B.2.2.2.2.2 = q.2.2.2.2.2 := congrArg (fun z : Pat => z.2.2.2.2.2) h
  rcases of_selBit (bitAt_selMask hi) with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ |
    ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · rw [e0]; exact hq
  · rw [e1]; exact hq
  · rw [e2]; exact hq
  · rw [e3]; exact hq
  · rw [e4]; exact hq
  · rw [e5]; exact hq

theorem apart_selMask {w : Mask} {B : Block} {q : Pat} (h : patAt w B = q) :
    Apart (selMask B (negPat q)) w := by
  intro i hi
  have e0 : bitAt w B.1 = q.1 := congrArg (fun z : Pat => z.1) h
  have e1 : bitAt w B.2.1 = q.2.1 := congrArg (fun z : Pat => z.2.1) h
  have e2 : bitAt w B.2.2.1 = q.2.2.1 := congrArg (fun z : Pat => z.2.2.1) h
  have e3 : bitAt w B.2.2.2.1 = q.2.2.2.1 := congrArg (fun z : Pat => z.2.2.2.1) h
  have e4 : bitAt w B.2.2.2.2.1 = q.2.2.2.2.1 := congrArg (fun z : Pat => z.2.2.2.2.1) h
  have e5 : bitAt w B.2.2.2.2.2 = q.2.2.2.2.2 := congrArg (fun z : Pat => z.2.2.2.2.2) h
  rcases of_selBit (bitAt_selMask hi) with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩ |
    ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · rw [e0]; simpa [negPat] using hq
  · rw [e1]; simpa [negPat] using hq
  · rw [e2]; simpa [negPat] using hq
  · rw [e3]; simpa [negPat] using hq
  · rw [e4]; simpa [negPat] using hq
  · rw [e5]; simpa [negPat] using hq

/-- **Lemma 2: branching is exhaustive.**  One of the allowed patterns of any of
the forty-five blocks must occur, so a node is settled once all its children
are.  For a four-point block this is `quadBlock_mem`, that is, rule (T). -/
theorem settles_branch (hT : TablesSound) {pos neg : Mask} {r : Block × List Pat}
    (hmem : r ∈ nodeRules)
    (h : ∀ q ∈ r.2, Settles (pos ||| selMask r.1 q) (neg ||| selMask r.1 (negPat q))) :
    Settles pos neg := by
  intro p hgp hrep w hlt hw hb ha
  have hq : patAt w r.1 ∈ r.2 := hT p hgp hrep w hw r hmem
  exact h (patAt w r.1) hq p hgp hrep w hlt hw
    (below_or hb (below_selMask rfl)) (apart_or ha (apart_selMask rfl))

/-! ### Leaves -/

/-- Every one of the ninety cells is decided by the node. -/
def determined (pos neg : Mask) : Bool :=
  (List.range 90).all (fun i => bitAt pos i || bitAt neg i)

/-- A relabelling of the six points, held as a six-tuple. -/
abbrev Tup := Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6 × Fin 6

def apTup (t : Tup) (i : Fin 6) : Fin 6 :=
  [t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2].getD i.val 0

/-- `permMask` for a relabelling given as a tuple. -/
def permMaskT (t : Tup) (w : Mask) : Mask :=
  ofBits 90 (fun i =>
    bitAt w (cellNum (apTup t (cellOf i).1.1) (apTup t (cellOf i).1.2)
      (apTup t (cellOf i).2.1) (apTup t (cellOf i).2.2)))

/-- The leaf test: the node decides every cell, the tuple is a relabelling, and
it carries the decided mask into the list of 35 representatives. -/
def censusLeaf (pos neg : Mask) (t : Tup) : Bool :=
  determined pos neg && decide (Function.Bijective (apTup t)) &&
    censusList.contains (permMaskT t pos)

/-- **Lemma 3: a decided leaf inside the census is settled.** -/
theorem settles_leaf {pos neg : Mask} {t : Tup} (h : censusLeaf pos neg t = true) :
    Settles pos neg := by
  simp only [censusLeaf, Bool.and_eq_true] at h
  obtain ⟨⟨hdet, hbij⟩, hmem⟩ := h
  have hbij' : Function.Bijective (apTup t) := of_decide_eq_true hbij
  intro p hgp hrep w hlt hw hb ha
  have hagree : ∀ i, i < 90 → bitAt w i = bitAt pos i := by
    intro i hi
    have hd : (bitAt pos i || bitAt neg i) = true :=
      List.all_eq_true.mp hdet i (List.mem_range.mpr hi)
    cases hp : bitAt pos i with
    | true => exact hb i hp
    | false =>
      rw [hp] at hd
      simp only [Bool.false_or] at hd
      exact ha i hd
  refine ⟨Equiv.ofBijective _ hbij', ?_⟩
  have key : permMask (Equiv.ofBijective _ hbij') w = permMaskT t pos := by
    show ofBits 90 (fun i => bitAt w (cellNum (apTup t (cellOf i).1.1) (apTup t (cellOf i).1.2)
      (apTup t (cellOf i).2.1) (apTup t (cellOf i).2.2))) = permMaskT t pos
    refine ofBits_congr 90 _ _ ?_
    intro i hi
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := cellOf_distinct ⟨i, hi⟩
    obtain ⟨hlt90, -⟩ := cellNum_spec (apTup t (cellOf i).1.1) (apTup t (cellOf i).1.2)
      (apTup t (cellOf i).2.1) (apTup t (cellOf i).2.2)
      (hbij'.1.ne d1) (hbij'.1.ne d2) (hbij'.1.ne d3) (hbij'.1.ne d4)
      (hbij'.1.ne d5) (hbij'.1.ne d6)
    exact hagree _ hlt90
  rw [key]
  exact List.mem_of_elem_eq_true hmem

/-- For each of the fifteen four-point blocks, its ten allowed patterns with
the two masks each of them forces. -/
def branchTable : List (List (Pat × Mask × Mask)) :=
  [[((true, false, false, false, false, false), 1, 18014468302704704),
    ((false, true, false, false, false, false), 64, 18014468302704641),
    ((false, false, true, false, false, false), 4096, 18014468302700609),
    ((false, false, false, true, false, false), 1073741824, 18014467228962881),
    ((false, false, true, true, false, false), 1073745920, 18014467228958785),
    ((false, false, false, false, true, false), 68719476736, 18014399583227969),
    ((false, true, false, false, true, false), 68719476800, 18014399583227905),
    ((false, false, false, false, false, true), 18014398509481984, 69793222721),
    ((true, false, false, false, false, true), 18014398509481985, 69793222720),
    ((true, true, true, true, true, true), 18014468302704705, 0)],
   [((true, false, false, false, false, false), 2, 1152925904801104000),
    ((false, true, false, false, false, false), 128, 1152925904801103874),
    ((false, false, true, false, false, false), 262144, 1152925904800841858),
    ((false, false, false, true, false, false), 2147483648, 1152925902653620354),
    ((false, false, true, true, false, false), 2147745792, 1152925902653358210),
    ((false, false, false, false, true, false), 4398046511104, 1152921506754592898),
    ((false, true, false, false, true, false), 4398046511232, 1152921506754592770),
    ((false, false, false, false, false, true), 1152921504606846976, 4400194257026),
    ((true, false, false, false, false, true), 1152921504606846978, 4400194257024),
    ((true, true, true, true, true, true), 1152925904801104002, 0)],
   [((true, false, false, false, false, false), 4, 73787257774126661888),
    ((false, true, false, false, false, false), 256, 73787257774126661636),
    ((false, false, true, false, false, false), 16777216, 73787257774109884676),
    ((false, false, false, true, false, false), 4294967296, 73787257769831694596),
    ((false, false, true, true, false, false), 4311744512, 73787257769814917380),
    ((false, false, false, false, true, false), 281474976710656, 73786976299149951236),
    ((false, true, false, false, true, false), 281474976710912, 73786976299149950980),
    ((false, false, false, false, false, true), 73786976294838206464, 281479288455428),
    ((true, false, false, false, false, true), 73786976294838206468, 281479288455424),
    ((true, true, true, true, true, true), 73787257774126661892, 0)],
   [((true, false, false, false, false, false), 8, 4722366491803177721856),
    ((false, true, false, false, false, false), 8192, 4722366491803177713672),
    ((false, false, true, false, false, false), 524288, 4722366491803177197576),
    ((false, false, false, true, false, false), 137438953472, 4722366491665738768392),
    ((false, false, true, true, false, false), 137439477760, 4722366491665738244104),
    ((false, false, false, false, true, false), 8796093022208, 4722366483007084699656),
    ((false, true, false, false, true, false), 8796093030400, 4722366483007084691464),
    ((false, false, false, false, false, true), 4722366482869645213696, 8933532508168),
    ((true, false, false, false, false, true), 4722366482869645213704, 8933532508160),
    ((true, true, true, true, true, true), 4722366491803177721864, 0)],
   [((true, false, false, false, false, false), 16, 302231455466882158575616),
    ((false, true, false, false, false, false), 16384, 302231455466882158559248),
    ((false, false, true, false, false, false), 33554432, 302231455466882125021200),
    ((false, false, false, true, false, false), 274877906944, 302231455466607280668688),
    ((false, false, true, true, false, false), 274911461376, 302231455466607247114256),
    ((false, false, false, false, true, false), 562949953421312, 302231454903932205154320),
    ((false, true, false, false, true, false), 562949953437696, 302231454903932205137936),
    ((false, false, false, false, false, true), 302231454903657293676544, 563224864899088),
    ((true, false, false, false, false, true), 302231454903657293676560, 563224864899072),
    ((true, true, true, true, true, true), 302231455466882158575632, 0)],
   [((true, false, false, false, false, false), 32, 19342813114977558956343296),
    ((false, true, false, false, false, false), 1048576, 19342813114977558955294752),
    ((false, false, true, false, false, false), 67108864, 19342813114977558889234464),
    ((false, false, false, true, false, false), 17592186044416, 19342813114959966770298912),
    ((false, false, true, true, false, false), 17592253153280, 19342813114959966703190048),
    ((false, false, false, false, true, false), 1125899906842624, 19342813113851659049500704),
    ((false, true, false, false, true, false), 1125899907891200, 19342813113851659048452128),
    ((false, false, false, false, false, true), 19342813113834066795298816, 1143492161044512),
    ((true, false, false, false, false, true), 19342813113834066795298848, 1143492161044480),
    ((true, true, true, true, true, true), 19342813114977558956343328, 0)],
   [((true, false, false, false, false, false), 512, 9447074837545525215232),
    ((false, true, false, false, false, false), 32768, 9447074837545525182976),
    ((false, false, true, false, false, false), 2097152, 9447074837545523118592),
    ((false, false, false, true, false, false), 36028797018963968, 9447038808748506251776),
    ((false, false, true, true, false, false), 36028797021061120, 9447038808748504154624),
    ((false, false, false, false, true, false), 2305843009213693952, 9444768994536311521792),
    ((false, true, false, false, true, false), 2305843009213726720, 9444768994536311489024),
    ((false, false, false, false, false, true), 9444732965739290427392, 2341871806234788352),
    ((true, false, false, false, false, true), 9444732965739290427904, 2341871806234787840),
    ((true, true, true, true, true, true), 9447074837545525215744, 0)],
   [((true, false, false, false, false, false), 1024, 604610555817498435977216),
    ((false, true, false, false, false, false), 65536, 604610555817498435912704),
    ((false, false, true, false, false, false), 134217728, 604610555817498301760512),
    ((false, false, false, true, false, false), 72057594037927936, 604610483759904398050304),
    ((false, false, true, true, false, false), 72057594172145664, 604610483759904263832576),
    ((false, false, false, false, true, false), 147573952589676412928, 604462981864908759565312),
    ((false, true, false, false, true, false), 147573952589676478464, 604462981864908759499776),
    ((false, false, false, false, false, true), 604462909807314587353088, 147646010183848625152),
    ((true, false, false, false, false, true), 604462909807314587354112, 147646010183848624128),
    ((true, true, true, true, true, true), 604610555817498435978240, 0)],
   [((true, false, false, false, false, false), 2048, 38685925987259331643441152),
    ((false, true, false, false, false, false), 4194304, 38685925987259331639248896),
    ((false, false, true, false, false, false), 268435456, 38685925987259331375007744),
    ((false, false, false, true, false, false), 4611686018427387904, 38685921375573313216055296),
    ((false, false, true, true, false, false), 4611686018695823360, 38685921375573312947619840),
    ((false, false, false, false, true, false), 295147905179352825856, 38685630839354152290617344),
    ((false, true, false, false, true, false), 295147905179357020160, 38685630839354152286423040),
    ((false, false, false, false, false, true), 38685626227668133590597632, 299759591198052845568),
    ((true, false, false, false, false, true), 38685626227668133590599680, 299759591198052843520),
    ((true, true, true, true, true, true), 38685925987259331643443200, 0)],
   [((true, false, false, false, false, false), 131072, 78599067740882375482015744),
    ((false, true, false, false, false, false), 8388608, 78599067740882375473758208),
    ((false, false, true, false, false, false), 536870912, 78599067740882374945275904),
    ((false, false, false, true, false, false), 18889465931478580854784, 78580178274950896901292032),
    ((false, false, true, true, false, false), 18889465931479117725696, 78580178274950896364421120),
    ((false, false, false, false, true, false), 1208925819614629174706176, 77390141921267746307440640),
    ((false, true, false, false, true, false), 1208925819614629183094784, 77390141921267746299052032),
    ((false, false, false, false, false, true), 77371252455336267181195264, 1227815285546108300951552),
    ((true, false, false, false, false, true), 77371252455336267181326336, 1227815285546108300820480),
    ((true, true, true, true, true, true), 78599067740882375482146816, 0)],
   [((true, false, false, false, false, false), 8589934592, 37788299385916220243968),
    ((false, true, false, false, false, false), 549755813888, 37788299385375054364672),
    ((false, false, true, false, false, false), 35184372088832, 37788299350740438089728),
    ((false, false, false, true, false, false), 144115188075855872, 37788155270736734322688),
    ((false, false, true, true, false, false), 144150372447944704, 37788155235552362233856),
    ((false, false, false, false, true, false), 9223372036854775808, 37779076013887955402752),
    ((false, true, false, false, true, false), 9223372586610589696, 37779076013338199588864),
    ((false, false, false, false, false, true), 37778931862957161709568, 9367522967648468992),
    ((true, false, false, false, false, true), 37778931862965751644160, 9367522959058534400),
    ((true, true, true, true, true, true), 37788299385924810178560, 0)],
   [((true, false, false, false, false, false), 17179869184, 2418442225522892532088832),
    ((false, true, false, false, false, false), 1099511627776, 2418442225521810200330240),
    ((false, false, true, false, false, false), 2251799813685248, 2418442223271109898272768),
    ((false, false, false, true, false, false), 288230376151711744, 2418441937292533560246272),
    ((false, false, true, true, false, false), 290482175965396992, 2418441935040733746561024),
    ((false, false, false, false, true, false), 590295810358705651712, 2417851929712551006306304),
    ((false, true, false, false, true, false), 590295811458217279488, 2417851929711451494678528),
    ((false, false, false, false, false, true), 2417851639229258349412352, 590586293651362545664),
    ((true, false, false, false, false, true), 2417851639229275529281536, 590586293634182676480),
    ((true, true, true, true, true, true), 2418442225522909711958016, 0)],
   [((true, false, false, false, false, false), 34359738368, 154743703953611293854793728),
    ((false, true, false, false, false, false), 70368744177664, 154743703953540959470354432),
    ((false, false, true, false, false, false), 4503599627370496, 154743703949107728587161600),
    ((false, false, false, true, false, false), 18446744073709551616, 154743685506867254504980480),
    ((false, false, true, true, false, false), 18451247673336922112, 154743685502363654877609984),
    ((false, false, false, false, true, false), 1180591620717411303424, 154742523361990610803228672),
    ((false, true, false, false, true, false), 1180591691086155481088, 154742523361920242059051008),
    ((false, false, false, false, false, true), 154742504910672534362390528, 1199042938793852141568),
    ((true, false, false, false, false, true), 154742504910672568722128896, 1199042938759492403200),
    ((true, true, true, true, true, true), 154743703953611328214532096, 0)],
   [((true, false, false, false, false, false), 2199023255552, 314396270972677436490121216),
    ((false, true, false, false, false, false), 140737488355328, 314396270972538898025021440),
    ((false, false, true, false, false, false), 9007199254740992, 314396270963672436258635776),
    ((false, false, false, true, false, false), 75557863725914323419136, 314320713108953721189957632),
    ((false, false, true, true, false, false), 75557872733113578160128, 314320713099946521935216640),
    ((false, false, false, false, true, false), 4835703278458516698824704, 309560567694221118814552064),
    ((false, true, false, false, true, false), 4835703278599254187180032, 309560567694080381326196736),
    ((false, false, false, false, false, true), 309485009821345068724781056, 4911261151334566788595712),
    ((true, false, false, false, false, true), 309485009821347267748036608, 4911261151332367765340160),
    ((true, true, true, true, true, true), 314396270972679635513376768, 0)],
   [((true, false, false, false, false, false), 576460752303423488, 628794940003788581735759872),
    ((false, true, false, false, false, false), 36893488147419103232, 628794903686761186620080128),
    ((false, false, true, false, false, false), 2361183241434822606848, 628792579397007899216576512),
    ((false, false, false, true, false, false), 151115727451828646838272, 628643824852797505392345088),
    ((false, false, true, true, false, false), 153476910693263469445120, 628641463669556070569738240),
    ((false, false, false, false, true, false), 9671406556917033397649408, 619123534023332300641533952),
    ((false, true, false, false, true, false), 9671443450405180816752640, 619123497129844153222430720),
    ((false, false, false, false, false, true), 618970019642690137449562112, 9824920937559196589621248),
    ((true, false, false, false, false, true), 618970020219150889752985600, 9824920361098444286197760),
    ((true, true, true, true, true, true), 628794940580249334039183360, 0)]]


/-- **`TablesSound` holds.**  This is `consistent_of_carries` read as patterns:
the soundness of the forty-five block tables, which is what the chain needs. -/
theorem tables_sound : TablesSound := fun _p hgp hrep _w hw =>
  nodeRules_pat (quadBlocks_ok hgp hrep hw) (apexBlocks_ok hgp hw) (edgeBlocks_ok hgp hw)

/-- A plane point read as a complex number. -/
def toC (p : Pt) : ℂ := ⟨p.1, p.2⟩

/-- The complex conjugate of `toC p`. -/
def barC (p : Pt) : ℂ := ⟨p.1, -p.2⟩

@[simp] theorem toC_re (p : Pt) : (toC p).re = p.1 := rfl
@[simp] theorem toC_im (p : Pt) : (toC p).im = p.2 := rfl
@[simp] theorem barC_re (p : Pt) : (barC p).re = p.1 := rfl
@[simp] theorem barC_im (p : Pt) : (barC p).im = -p.2 := rfl

/-- `barC` really is the conjugate of `toC`. -/
theorem barC_eq_conj (p : Pt) : barC p = (starRingEnd ℂ) (toC p) := by
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;> simp

/-- A complex number is real exactly when it equals its conjugate.  This is the
step that turns "the direction sum vanishes mod `π`" into a polynomial equation. -/
theorem im_eq_zero_iff_eq_conj {z : ℂ} : z.im = 0 ↔ z = (starRingEnd ℂ) z := by
  constructor
  · intro h
    refine Complex.ext_iff.mpr ⟨by simp, ?_⟩
    simp [h]
  · intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith

/-- Being real is closed under multiplication. -/
theorem im_mul_eq_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : (z * w).im = 0 := by
  simp [Complex.mul_im, hz, hw]

/-- Being real is inherited by a factor, once the other factor is real and
nonzero.  Together with `im_mul_eq_zero` this is all the arithmetic of "is real"
that a lattice certificate needs. -/
theorem im_eq_zero_of_mul {z w : ℂ} (hw : w.im = 0) (hw0 : w ≠ 0) (h : (z * w).im = 0) :
    z.im = 0 := by
  have hre : w.re ≠ 0 := by
    intro hr
    apply hw0
    refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;> simp [hr, hw]
  simp only [Complex.mul_im, hw, mul_zero, zero_add] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · exact absurd h1 hre

/-- A point difference is nonzero when the points differ. -/
theorem toC_sub_ne_zero {a b : Pt} (h : a ≠ b) : toC a - toC b ≠ 0 := by
  intro hz
  refine h (Prod.ext ?_ ?_)
  · have h1 := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.zero_re, toC_re] at h1
    linarith
  · have h2 := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.zero_im, toC_im] at h2
    linarith

/-- The conjugate of a point difference is nonzero when the points differ. -/
theorem barC_sub_ne_zero {a b : Pt} (h : a ≠ b) : barC a - barC b ≠ 0 := by
  intro hz
  refine h (Prod.ext ?_ ?_)
  · have h1 := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.zero_re, barC_re] at h1
    linarith
  · have h2 := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.zero_im, barC_im] at h2
    linarith

/-! ### The witness condition as an imaginary part -/

/-- **The bridge.**  The imaginary part of the witness product is minus the
equal-circumradius form.  (`barC x - barC y = conj (toC x - toC y)`, so the
product below is `(a - c) * (a - d) * conj ((b - c) * (b - d))`.) -/
theorem im_witnessValue (a b c d : Pt) :
    ((toC a - toC c) * (toC a - toC d) * ((barC b - barC c) * (barC b - barC d))).im
      = - Psi a b c d := by
  simp only [Psi, qq, cross, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

/-- The same bridge written with `conj`. -/
theorem im_witnessValue_conj (a b c d : Pt) :
    ((toC a - toC c) * (toC a - toC d) *
        (starRingEnd ℂ) ((toC b - toC c) * (toC b - toC d))).im = - Psi a b c d := by
  have h : (starRingEnd ℂ) ((toC b - toC c) * (toC b - toC d))
      = (barC b - barC c) * (barC b - barC d) := by
    rw [map_mul, map_sub, map_sub, ← barC_eq_conj, ← barC_eq_conj, ← barC_eq_conj]
  rw [h, im_witnessValue]

/-- Witness ⟺ the witness product is real. -/
theorem psi_eq_zero_iff_im_eq_zero (a b c d : Pt) :
    Psi a b c d = 0 ↔
      ((toC a - toC c) * (toC a - toC d) *
        (starRingEnd ℂ) ((toC b - toC c) * (toC b - toC d))).im = 0 := by
  rw [im_witnessValue_conj]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith

/-- The witness condition as a polynomial equation: the witness product equals
its own conjugate.  This is the form a lattice certificate multiplies. -/
theorem witnessEq {a b c d : Pt} (h : Psi a b c d = 0) :
    (toC a - toC c) * (toC a - toC d) * ((barC b - barC c) * (barC b - barC d))
      = (barC a - barC c) * (barC a - barC d) * ((toC b - toC c) * (toC b - toC d)) := by
  simp only [Psi, qq, cross] at h
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      toC_re, toC_im, barC_re, barC_im]
  · ring
  · linear_combination (-2 : ℝ) * h

/-! ### The shape of a lattice certificate

A membership certificate `2 * G = Σ n_i F_i` with two positive and two negative
cells produces two equations `X ^ 2 * P = Y ^ 2 * Q` and `U ^ 2 * P' = V ^ 2 * Q'`
together with a monomial identity `P * Q' = P' * Q`; from these the ratio
`X ^ 2 / Y ^ 2` and `U ^ 2 / V ^ 2` are forced to agree. -/

/-- The algebraic core of a lattice certificate. -/
theorem sq_mul_sq_eq_of_two_products {X Y U V P Q P' Q' : ℂ}
    (ha : X ^ 2 * P = Y ^ 2 * Q) (hb : U ^ 2 * P' = V ^ 2 * Q')
    (hPQ : P * Q' = P' * Q) (hP : P ≠ 0) (hQ : Q' ≠ 0) :
    X ^ 2 * V ^ 2 = Y ^ 2 * U ^ 2 := by
  have key : (P * Q') * (X ^ 2 * V ^ 2) = (P * Q') * (Y ^ 2 * U ^ 2) := by
    linear_combination (V ^ 2 * Q') * ha - (Y ^ 2 * Q) * hb - (Y ^ 2 * U ^ 2) * hPQ
  exact mul_left_cancel₀ (mul_ne_zero hP hQ) key

/-! ### Reading off a right angle

`(a - b) * conj (a - c)` has real part `⟪b - a, c - a⟫` and imaginary part
`- cross a b c`, so its square has imaginary part `-2 ⟪b - a, c - a⟫ cross a b c`.
A real square therefore forces "right angle or collinear". -/

/-- The imaginary part of the square. -/
theorem im_sq_of_dir (a b c : Pt) :
    (((toC a - toC b) * (barC a - barC c)) ^ 2).im = -2 * (qq b c a * cross a b c) := by
  simp only [qq, cross, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- The imaginary part of the conjugate square. -/
theorem im_sq_of_dir_conj (a b c : Pt) :
    (((barC a - barC b) * (toC a - toC c)) ^ 2).im = 2 * (qq b c a * cross a b c) := by
  simp only [qq, cross, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, toC_re, toC_im, barC_re, barC_im]
  ring

/-- A real square forces a right angle at `a` or three collinear points. -/
theorem qq_mul_cross_eq_zero_of_sq_eq {a b c : Pt}
    (h : ((toC a - toC b) * (barC a - barC c)) ^ 2
        = ((barC a - barC b) * (toC a - toC c)) ^ 2) :
    qq b c a * cross a b c = 0 := by
  have h1 := im_sq_of_dir a b c
  rw [h, im_sq_of_dir_conj] at h1
  linarith

/-- Right angles at two different vertices of a triangle force the third side to
have length zero. -/
theorem sqdist_eq_zero_of_two_right_angles {a b c : Pt}
    (h1 : qq b c a = 0) (h2 : qq a b c = 0) : sqdist a c = 0 := by
  simp only [qq] at h1 h2
  simp only [sqdist]
  linear_combination h1 + h2



/-! ## The lattice rules as units of modulus one

A cell `(P = {a,b}, e = {c,d})` is a witness exactly when the product
`(a-c)(a-d)·conj((b-c)(b-d))` is real.  Dividing each difference by its own
conjugate turns this into an equation between **units**

  `uu a c * uu a d = uu b c * uu b d`,

so a lattice certificate `m·F = Σ c_i W_i` becomes a plain multiplicative
identity in `ℂˣ`: multiply the witness equations of the positive cells, divide
by those of the negative cells.  No `arg`, no `ℝ/ℤ`, and no lemma about the
lattice itself.
-/

/-- The imaginary part of a square, once and for all. -/
theorem im_sq (z : ℂ) : (z ^ 2).im = 2 * z.re * z.im := by
  simp only [pow_two, Complex.mul_im]; ring

/-- The barred witness product has `+Psi` for its imaginary part. -/
theorem im_witnessValue' (a b c d : Pt) :
    ((barC a - barC c) * (barC a - barC d) * ((toC b - toC c) * (toC b - toC d))).im
      = Psi a b c d := by
  simp only [Psi, qq, cross, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

/-- **Witness as a polynomial equation, both ways.** -/
theorem psi_eq_zero_iff_poly (a b c d : Pt) :
    Psi a b c d = 0 ↔
      (toC a - toC c) * (toC a - toC d) * ((barC b - barC c) * (barC b - barC d))
        = (barC a - barC c) * (barC a - barC d) * ((toC b - toC c) * (toC b - toC d)) := by
  constructor
  · exact witnessEq
  · intro h
    have h1 := congrArg Complex.im h
    rw [im_witnessValue, im_witnessValue'] at h1
    linarith

/-- The unit attached to a directed pair: the difference divided by its
conjugate.  It has modulus one, and the census cares only about its argument. -/
noncomputable def uu (x y : Pt) : ℂ := (toC x - toC y) / (barC x - barC y)

theorem uu_ne_zero {x y : Pt} (h : x ≠ y) : uu x y ≠ 0 :=
  div_ne_zero (toC_sub_ne_zero h) (barC_sub_ne_zero h)

/-- Reversing a pair does not change its unit. -/
theorem uu_swap (x y : Pt) : uu y x = uu x y := by
  rw [uu, uu]
  rw [show toC y - toC x = -(toC x - toC y) by ring,
    show barC y - barC x = -(barC x - barC y) by ring, neg_div_neg_eq]

/-- **The bridge to units.**  This is the form every lattice certificate is
read in. -/
theorem psi_eq_zero_iff_uu {a b c d : Pt} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Psi a b c d = 0 ↔ uu a c * uu a d = uu b c * uu b d := by
  rw [psi_eq_zero_iff_poly, uu, uu, uu, uu, div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (barC_sub_ne_zero hac) (barC_sub_ne_zero had))
      (mul_ne_zero (barC_sub_ne_zero hbc) (barC_sub_ne_zero hbd))]
  constructor <;> intro h <;> linear_combination h

/-! ### The reading for `col` with `m = 2`

`uu a b ^ 2 = uu a c ^ 2` says that the collinearity form `e_ab - e_ac` has
order dividing two in `ℤ¹⁵ / L(S)`.  The product `(a-b)·conj(a-c)` has the inner
product for its real part and minus the cross product for its imaginary part, so
a real square forces a right angle at `a` or three collinear points. -/

theorem re_dir (a b c : Pt) :
    ((toC a - toC b) * (barC a - barC c)).re = qq b c a := by
  simp only [qq, Complex.mul_re, Complex.sub_re, Complex.sub_im, toC_re, toC_im,
    barC_re, barC_im]
  ring

theorem im_dir (a b c : Pt) :
    ((toC a - toC b) * (barC a - barC c)).im = - cross a b c := by
  simp only [cross, Complex.mul_im, Complex.sub_re, Complex.sub_im, toC_re, toC_im,
    barC_re, barC_im]
  ring

theorem re_dir' (a b c : Pt) :
    ((barC a - barC b) * (toC a - toC c)).re = qq b c a := by
  simp only [qq, Complex.mul_re, Complex.sub_re, Complex.sub_im, toC_re, toC_im,
    barC_re, barC_im]
  ring

theorem im_dir' (a b c : Pt) :
    ((barC a - barC b) * (toC a - toC c)).im = cross a b c := by
  simp only [cross, Complex.mul_im, Complex.sub_re, Complex.sub_im, toC_re, toC_im,
    barC_re, barC_im]
  ring

/-- **The `col`, `m = 2` reading, in polynomial form.**  A right angle at `a` or
three collinear points.  (This is `qq_mul_cross_eq_zero_of_sq_eq` again, but the
two `ring` calls are now on degree two rather than degree four, because the
square is taken by `im_sq`.) -/
theorem col_reading {a b c : Pt}
    (h : ((toC a - toC b) * (barC a - barC c)) ^ 2
      = ((barC a - barC b) * (toC a - toC c)) ^ 2) :
    qq b c a * cross a b c = 0 := by
  have h1 := congrArg Complex.im h
  rw [im_sq, im_sq, re_dir, im_dir, re_dir', im_dir'] at h1
  linarith

/-- **The `col`, `m = 2` reading, in unit form.** -/
theorem col_reading_uu {a b c : Pt} (hab : a ≠ b) (hac : a ≠ c)
    (h : uu a b ^ 2 = uu a c ^ 2) : qq b c a * cross a b c = 0 := by
  refine col_reading ?_
  rw [uu, uu, div_pow, div_pow, div_eq_div_iff (pow_ne_zero 2 (barC_sub_ne_zero hab))
    (pow_ne_zero 2 (barC_sub_ne_zero hac))] at h
  linear_combination h

/-! ### The reading for `cyc` with `m = 2`

The concyclicity form is `e_ac + e_bd - e_ad - e_bc`; the product attached to it
is `(a-c)(b-d)·conj((a-d)(b-c))`, whose imaginary part is exactly the
concyclicity determinant `det4`.  A real square therefore forces "concyclic (or
collinear)" **or** "the cross ratio is purely imaginary". -/

/-- The real part of the concyclicity product. -/
noncomputable def cycRe (a b c d : Pt) : ℝ :=
  ((toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c))).re

/-- **The imaginary part of the concyclicity product is `det4`.**  (Checked
first in exact rationals on 389 four-point samples: the ratio was `1` every
time.) -/
theorem im_cyc (a b c d : Pt) :
    ((toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c))).im
      = det4 a b c d := by
  simp only [det4, cross, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

theorem re_cyc' (a b c d : Pt) :
    ((barC a - barC c) * (barC b - barC d) * ((toC a - toC d) * (toC b - toC c))).re
      = cycRe a b c d := by
  simp only [cycRe, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

theorem im_cyc' (a b c d : Pt) :
    ((barC a - barC c) * (barC b - barC d) * ((toC a - toC d) * (toC b - toC c))).im
      = - det4 a b c d := by
  simp only [det4, cross, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    toC_re, toC_im, barC_re, barC_im]
  ring

/-- **The `cyc`, `m = 2` reading, in polynomial form.** -/
theorem cyc_reading {a b c d : Pt}
    (h : ((toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c))) ^ 2
      = ((barC a - barC c) * (barC b - barC d) * ((toC a - toC d) * (toC b - toC c))) ^ 2) :
    cycRe a b c d * det4 a b c d = 0 := by
  have h1 := congrArg Complex.im h
  rw [im_sq, im_sq, im_cyc, re_cyc', im_cyc'] at h1
  have h2 : ((toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c))).re
      = cycRe a b c d := rfl
  rw [h2] at h1
  linarith

/-- **The `cyc`, `m = 2` reading, in unit form.** -/
theorem cyc_reading_uu {a b c d : Pt} (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d) (hbc : b ≠ c)
    (h : (uu a c * uu b d) ^ 2 = (uu a d * uu b c) ^ 2) :
    cycRe a b c d * det4 a b c d = 0 := by
  refine cyc_reading ?_
  rw [uu, uu, uu, uu, div_mul_div_comm, div_mul_div_comm, div_pow, div_pow,
    div_eq_div_iff
      (pow_ne_zero 2 (mul_ne_zero (barC_sub_ne_zero hac) (barC_sub_ne_zero hbd)))
      (pow_ne_zero 2 (mul_ne_zero (barC_sub_ne_zero had) (barC_sub_ne_zero hbc)))] at h
  linear_combination h

/-- **The `cyc`, `m = 2` rule (D2).**  In general position the determinant is
nonzero, so what is forced is that the cross ratio is purely imaginary. -/
theorem cycRe_eq_zero_of_cyc {a b c d : Pt} (hncyc : ¬ Concyclic4 a b c d)
    (h : cycRe a b c d * det4 a b c d = 0) : cycRe a b c d = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' hncyc

/-! ### A certificate with `m = 1`: the forcing rule (K1)

With the witness condition in unit form a certificate is multiplied out
directly.  The smallest one is length two: the witness forms of the cells
`({a,b},{c,d})` and `({b,x},{c,d})` add up to the form of `({a,x},{c,d})`, so
two witnesses on one edge force a third.  This reproduces rule (B)
(`psi_trans`) as a lattice certificate, which is the positive control for the
machinery. -/

/-- **Rule (K1), the length-two certificate.**  `W_{(ab)(cd)} + W_{(bx)(cd)} =
W_{(ax)(cd)}`. -/
theorem forced_of_cert_two {a b x c d : Pt} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hxc : x ≠ c) (hxd : x ≠ d)
    (h1 : Psi a b c d = 0) (h2 : Psi b x c d = 0) : Psi a x c d = 0 := by
  rw [psi_eq_zero_iff_uu hac had hbc hbd] at h1
  rw [psi_eq_zero_iff_uu hbc hbd hxc hxd] at h2
  rw [psi_eq_zero_iff_uu hac had hxc hxd]
  rw [h1, h2]

/-! ### The cost of a certificate, with abstract units

The unit form makes a certificate a multiplicative identity, so the per-
certificate step costs one `field_simp`/`linear_combination` on abstract
variables -- the geometry is already gone.  The two lemmas below are the
length-four and length-fourteen shapes with every unit an abstract nonzero
complex number; they are what a machine-generated certificate lemma looks like. -/

/-- **The core of a certificate, of any length and any `m`.**  Each witness
gives one equation `v i = w i` between its two monomials.  A certificate says
that the product of those monomials is the target's monomial times a common
factor `T`; once the two monomial identities are in hand -- and they are `ring`
calls, one per certificate -- the target's own equation is one cancellation. -/
theorem target_eq_of_products {n : ℕ} (v w : Fin n → ℂ) (T Z C : ℂ)
    (h : ∀ i, v i = w i) (hT : T ≠ 0)
    (hZ : Z * T = ∏ i, v i) (hC : C * T = ∏ i, w i) : Z = C := by
  have hvw : (∏ i, v i) = ∏ i, w i := Finset.prod_congr rfl (fun i _ => h i)
  exact mul_right_cancel₀ hT (hZ.trans (hvw.trans hC.symm))

/-! ## The fifteen pairs, and one unit for each

A **form** is an integer vector on the fifteen pairs of the six points.  Four
different geometric conditions are all of the shape `χ(F) = 1`, where `χ` sends
a form to the product of the units of its pairs raised to the entries of the
form:

* the witness condition of a cell (`witForm`),
* three points on a line (`colForm`),
* four points on a circle (`cycForm`),
* a right angle, that is the direction class modulo `π/2` (`halfForm`).

The census tests membership of a form in the lattice `L(S)` spanned by the
witness forms of the cells it has already placed.  Membership is **exact**, so
a certificate is an integer identity `F = Σ c_i W_i` with no denominator, and
`χ` turns it into a product of ones.  The per-certificate cost is therefore one
decidable integer identity -- no `ring`, no geometry, and nothing that grows
with the length of the certificate beyond the identity itself. -/

/-- The fifteen pairs of the six points, in lexicographic order. -/
def pairList : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

theorem pairList_length : pairList.length = 15 := by decide

/-- The pair with index `k` (a fixed dummy outside the range). -/
def pairOf (k : ℕ) : Fin 6 × Fin 6 := pairList.getD k (0, 0)

/-- The index of the pair `{a,b}`, in either order. -/
def pairNum (a b : Fin 6) : ℕ := pairList.idxOf (min a b, max a b)

theorem pairOf_ne : ∀ k : Fin 15, (pairOf k.val).1 ≠ (pairOf k.val).2 := by decide

theorem pairNum_spec : ∀ a b : Fin 6, a ≠ b →
    pairNum a b < 15 ∧ pairOf (pairNum a b) = (min a b, max a b) := by decide

theorem pairNum_lt {a b : Fin 6} (h : a ≠ b) : pairNum a b < 15 :=
  (pairNum_spec a b h).1

/-- **The unit of a pair**: the difference of the two points divided by its
conjugate.  Its modulus is one and its argument is twice the direction. -/
noncomputable def lam (p : Fin 6 → Pt) (k : ℕ) : ℂ :=
  uu (p (pairOf k).1) (p (pairOf k).2)

theorem lam_ne_zero {p : Fin 6 → Pt} (hgp : GeneralPosition p) {k : ℕ} (hk : k < 15) :
    lam p k ≠ 0 :=
  uu_ne_zero (ne_of_gp hgp (pairOf_ne ⟨k, hk⟩))

theorem lam_pairNum {p : Fin 6 → Pt} {a b : Fin 6} (h : a ≠ b) :
    lam p (pairNum a b) = uu (p a) (p b) := by
  rw [lam, (pairNum_spec a b h).2]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab]
    exact uu_swap _ _

/-! ### Forms and the character -/

/-- An integer form on the pairs.  Only the entries below fifteen matter. -/
abbrev Form := ℕ → ℤ

/-- **The character of a form**: the product of the units of the pairs, each
raised to the entry of the form. -/
noncomputable def chiF (p : Fin 6 → Pt) (F : Form) : ℂ :=
  ∏ k : Fin 15, lam p k.val ^ F k.val

theorem chiF_congr (p : Fin 6 → Pt) {F G : Form} (h : ∀ k, k < 15 → F k = G k) :
    chiF p F = chiF p G :=
  Finset.prod_congr rfl fun k _ => by rw [h k.val k.isLt]

theorem chiF_zero (p : Fin 6 → Pt) : chiF p (fun _ => 0) = 1 := by
  simp [chiF]

theorem chiF_add {p : Fin 6 → Pt} (hgp : GeneralPosition p) (F G : Form) :
    chiF p (fun m => F m + G m) = chiF p F * chiF p G := by
  rw [chiF, chiF, chiF, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => zpow_add₀ (lam_ne_zero hgp k.isLt) _ _

theorem chiF_smul (p : Fin 6 → Pt) (c : ℤ) (F : Form) :
    chiF p (fun m => c * F m) = chiF p F ^ c := by
  rw [chiF, chiF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [mul_comm, zpow_mul]

/-- The indicator form of one pair, with a weight. -/
def eOne (k : ℕ) (s : ℤ) : Form := fun m => if m = k then s else 0

theorem chiF_eOne (p : Fin 6 → Pt) {k : ℕ} (hk : k < 15) (s : ℤ) :
    chiF p (eOne k s) = lam p k ^ s := by
  rw [chiF, Finset.prod_eq_single (⟨k, hk⟩ : Fin 15)]
  · simp [eOne]
  · intro b _ hb
    have hbk : b.val ≠ k := fun h => hb (Fin.ext h)
    simp [eOne, hbk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The only place `chiF` is unfolded.**  Every form the census uses is a sum
of four indicator forms, so this one lemma covers all four kinds at once. -/
theorem chiF_quad {p : Fin 6 → Pt} (hgp : GeneralPosition p)
    {k₁ k₂ k₃ k₄ : ℕ} (h₁ : k₁ < 15) (h₂ : k₂ < 15) (h₃ : k₃ < 15) (h₄ : k₄ < 15)
    (s₁ s₂ s₃ s₄ : ℤ) :
    chiF p (fun m => eOne k₁ s₁ m + eOne k₂ s₂ m + eOne k₃ s₃ m + eOne k₄ s₄ m)
      = lam p k₁ ^ s₁ * lam p k₂ ^ s₂ * lam p k₃ ^ s₃ * lam p k₄ ^ s₄ := by
  have e3 : (fun m => eOne k₁ s₁ m + eOne k₂ s₂ m + eOne k₃ s₃ m + eOne k₄ s₄ m)
      = (fun m => (fun m' => eOne k₁ s₁ m' + eOne k₂ s₂ m' + eOne k₃ s₃ m') m
          + eOne k₄ s₄ m) := rfl
  have e2 : (fun m' => eOne k₁ s₁ m' + eOne k₂ s₂ m' + eOne k₃ s₃ m')
      = (fun m' => (fun m'' => eOne k₁ s₁ m'' + eOne k₂ s₂ m'') m' + eOne k₃ s₃ m') := rfl
  rw [e3, chiF_add hgp, e2, chiF_add hgp, chiF_add hgp, chiF_eOne p h₁, chiF_eOne p h₂,
    chiF_eOne p h₃, chiF_eOne p h₄]

/-! ### The four kinds of form -/

/-- The witness form of the cell `i`: the edge's first point paired with both
apexes counts once, the edge's second point minus once. -/
def witForm (i : ℕ) : Form := fun m =>
  eOne (pairNum (cellOf i).2.1 (cellOf i).1.1) 1 m
    + eOne (pairNum (cellOf i).2.1 (cellOf i).1.2) 1 m
    + eOne (pairNum (cellOf i).2.2 (cellOf i).1.1) (-1) m
    + eOne (pairNum (cellOf i).2.2 (cellOf i).1.2) (-1) m

/-- The collinearity form of `(a, b, c)`: `e_ab - e_ac`. -/
def colForm (a b c : Fin 6) : Form := fun m =>
  eOne (pairNum a b) 1 m + eOne (pairNum a c) (-1) m + eOne 0 0 m + eOne 0 0 m

/-- The concyclicity form of `(u, v, c, d)`: `e_uc + e_vd - e_ud - e_vc`. -/
def cycForm (u v c d : Fin 6) : Form := fun m =>
  eOne (pairNum u c) 1 m + eOne (pairNum v d) 1 m
    + eOne (pairNum u d) (-1) m + eOne (pairNum v c) (-1) m

/-- The `mod π/2` form of `(a, b, c)`: twice the collinearity form. -/
def halfForm (a b c : Fin 6) : Form := fun m =>
  eOne (pairNum a b) 2 m + eOne (pairNum a c) (-2) m + eOne 0 0 m + eOne 0 0 m

/-! ### Reading each form off its character

All four readings are at `m = 1`, because the census tests membership in `L(S)`
exactly.  The `col` and `cyc` readings therefore give the degeneracy outright,
with no "right angle or collinear" alternative; the alternative appears only in
`halfForm`, whose character is a square. -/

/-- One unit over another, equal to one. -/
theorem one_neg_one_eq_one_iff {X Y : ℂ} (hY : Y ≠ 0) :
    X ^ (1 : ℤ) * Y ^ (-1 : ℤ) = 1 ↔ X = Y := by
  rw [zpow_one, zpow_neg_one, ← div_eq_mul_inv, div_eq_one_iff_eq hY]

/-- A square of one unit over a square of another, equal to one. -/
theorem two_zpow_eq_one_iff {X Y : ℂ} (hY : Y ≠ 0) :
    X ^ (2 : ℤ) * Y ^ (-2 : ℤ) = 1 ↔ X ^ 2 = Y ^ 2 := by
  rw [show X ^ (2 : ℤ) = X ^ 2 by norm_num,
    show Y ^ (-2 : ℤ) = (Y ^ 2)⁻¹ by rw [zpow_neg]; norm_num,
    ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero 2 hY)]

/-- Four units, two over two, equal to one. -/
theorem quad_eq_one_iff {X₁ X₂ Y₁ Y₂ : ℂ} (h₁ : Y₁ ≠ 0) (h₂ : Y₂ ≠ 0) :
    X₁ ^ (1 : ℤ) * X₂ ^ (1 : ℤ) * Y₁ ^ (-1 : ℤ) * Y₂ ^ (-1 : ℤ) = 1
      ↔ X₁ * X₂ = Y₁ * Y₂ := by
  rw [zpow_one, zpow_one, zpow_neg_one, zpow_neg_one,
    show X₁ * X₂ * Y₁⁻¹ * Y₂⁻¹ = (X₁ * X₂) / (Y₁ * Y₂) by
      rw [div_eq_mul_inv, mul_inv]; ring,
    div_eq_one_iff_eq (mul_ne_zero h₁ h₂)]

/-- **The witness reading.**  The character of a witness form is one exactly
when the cell is a witness. -/
theorem chiF_wit_iff {p : Fin 6 → Pt} (hgp : GeneralPosition p) (a b c d : Fin 6)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    chiF p (fun m => eOne (pairNum c a) 1 m + eOne (pairNum c b) 1 m
        + eOne (pairNum d a) (-1) m + eOne (pairNum d b) (-1) m) = 1
      ↔ Psi (p c) (p d) (p a) (p b) = 0 := by
  rw [chiF_quad hgp (pairNum_lt hca) (pairNum_lt hcb) (pairNum_lt hda) (pairNum_lt hdb),
    lam_pairNum hca, lam_pairNum hcb, lam_pairNum hda, lam_pairNum hdb,
    quad_eq_one_iff (uu_ne_zero (ne_of_gp hgp hda)) (uu_ne_zero (ne_of_gp hgp hdb)),
    psi_eq_zero_iff_uu (ne_of_gp hgp hca) (ne_of_gp hgp hcb)
      (ne_of_gp hgp hda) (ne_of_gp hgp hdb)]

theorem chiF_witForm_iff {p : Fin 6 → Pt} (hgp : GeneralPosition p) {i : ℕ} (hi : i < 90) :
    chiF p (witForm i) = 1 ↔ cellPsi p i = 0 := by
  obtain ⟨-, -, d3, d4, d5, d6⟩ := cellOf_distinct ⟨i, hi⟩
  exact chiF_wit_iff hgp _ _ _ _ (Ne.symm d3) (Ne.symm d5) (Ne.symm d4) (Ne.symm d6)

/-- Equal units on two pairs through one point force the three points onto a
line.  This is rule (D1) at `m = 1`. -/
theorem collinear_of_uu_eq {x y z : Pt} (hxy : x ≠ y) (hxz : x ≠ z)
    (h : uu x y = uu x z) : cross x y z = 0 := by
  rw [uu, uu, div_eq_div_iff (barC_sub_ne_zero hxy) (barC_sub_ne_zero hxz)] at h
  have h1 := congrArg Complex.im h
  rw [im_dir x y z] at h1
  rw [show (toC x - toC z) * (barC x - barC y)
      = (barC x - barC y) * (toC x - toC z) by ring, im_dir' x y z] at h1
  linarith

/-- **The `col` reading at `m = 1`.** -/
theorem chiF_colForm {p : Fin 6 → Pt} (hgp : GeneralPosition p) {a b c : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (h : chiF p (colForm a b c) = 1) :
    Collinear3 (p a) (p b) (p c) := by
  rw [show colForm a b c = (fun m => eOne (pairNum a b) 1 m + eOne (pairNum a c) (-1) m
      + eOne 0 0 m + eOne 0 0 m) from rfl,
    chiF_quad hgp (pairNum_lt hab) (pairNum_lt hac)
      (by decide : (0 : ℕ) < 15) (by decide : (0 : ℕ) < 15),
    lam_pairNum hab, lam_pairNum hac, zpow_zero, mul_one, mul_one,
    one_neg_one_eq_one_iff (uu_ne_zero (ne_of_gp hgp hac))] at h
  exact collinear_of_uu_eq (ne_of_gp hgp hab) (ne_of_gp hgp hac) h

/-- Equal cross-products of units force four points onto a circle.  This is
rule (D2) at `m = 1`. -/
theorem concyclic_of_uu_eq {a b c d : Pt} (hac : a ≠ c) (hbd : b ≠ d)
    (had : a ≠ d) (hbc : b ≠ c)
    (h : uu a c * uu b d = uu a d * uu b c) : det4 a b c d = 0 := by
  rw [uu, uu, uu, uu, div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (barC_sub_ne_zero hac) (barC_sub_ne_zero hbd))
      (mul_ne_zero (barC_sub_ne_zero had) (barC_sub_ne_zero hbc))] at h
  have h1 := congrArg Complex.im h
  rw [show (toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c))
      = (toC a - toC c) * (toC b - toC d) * ((barC a - barC d) * (barC b - barC c)) from rfl]
    at h1
  rw [im_cyc a b c d] at h1
  rw [show (toC a - toC d) * (toC b - toC c) * ((barC a - barC c) * (barC b - barC d))
      = (barC a - barC c) * (barC b - barC d) * ((toC a - toC d) * (toC b - toC c)) by ring,
    im_cyc' a b c d] at h1
  linarith

/-- **The `cyc` reading at `m = 1`.** -/
theorem chiF_cycForm {p : Fin 6 → Pt} (hgp : GeneralPosition p) {u v c d : Fin 6}
    (huc : u ≠ c) (hvd : v ≠ d) (hud : u ≠ d) (hvc : v ≠ c)
    (h : chiF p (cycForm u v c d) = 1) :
    Concyclic4 (p u) (p v) (p c) (p d) := by
  rw [show cycForm u v c d = (fun m => eOne (pairNum u c) 1 m + eOne (pairNum v d) 1 m
      + eOne (pairNum u d) (-1) m + eOne (pairNum v c) (-1) m) from rfl,
    chiF_quad hgp (pairNum_lt huc) (pairNum_lt hvd) (pairNum_lt hud) (pairNum_lt hvc),
    lam_pairNum huc, lam_pairNum hvd, lam_pairNum hud, lam_pairNum hvc,
    quad_eq_one_iff (uu_ne_zero (ne_of_gp hgp hud)) (uu_ne_zero (ne_of_gp hgp hvc))] at h
  exact concyclic_of_uu_eq (ne_of_gp hgp huc) (ne_of_gp hgp hvd)
    (ne_of_gp hgp hud) (ne_of_gp hgp hvc) h

/-- **The `mod π/2` reading.**  The character of a `halfForm` is a square, so
what comes out is "a right angle at `a` **or** three points on a line". -/
theorem chiF_halfForm {p : Fin 6 → Pt} (hgp : GeneralPosition p) {a b c : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (h : chiF p (halfForm a b c) = 1) :
    qq (p b) (p c) (p a) * cross (p a) (p b) (p c) = 0 := by
  rw [show halfForm a b c = (fun m => eOne (pairNum a b) 2 m + eOne (pairNum a c) (-2) m
      + eOne 0 0 m + eOne 0 0 m) from rfl,
    chiF_quad hgp (pairNum_lt hab) (pairNum_lt hac)
      (by decide : (0 : ℕ) < 15) (by decide : (0 : ℕ) < 15),
    lam_pairNum hab, lam_pairNum hac, zpow_zero, mul_one, mul_one] at h
  exact col_reading_uu (ne_of_gp hgp hab) (ne_of_gp hgp hac)
    ((two_zpow_eq_one_iff (uu_ne_zero (ne_of_gp hgp hac))).mp h)

/-- **Three right angles at one point are impossible.**  If the direction class
of `x` modulo `π/2` is shared with both `y` and `z`, then `y` and `z` are both
perpendicular to `x` at `a`, so they lie on one line through `a`.  This is the
pigeonhole that makes rule (D3) bite. -/
theorem cross_mul_sqdist (a x y z : Pt) :
    cross a y z * sqdist x a = qq x y a * cross a x z - qq x z a * cross a x y := by
  simp only [cross, qq, sqdist]
  ring

theorem collinear_of_two_right_angles {a x y z : Pt} (hxa : x ≠ a)
    (h1 : qq x y a = 0) (h2 : qq x z a = 0) : Collinear3 a y z := by
  have key := cross_mul_sqdist a x y z
  rw [h1, h2] at key
  simp only [zero_mul, sub_self] at key
  have hs : sqdist x a ≠ 0 := fun h => hxa (eq_of_sqdist_eq_zero h)
  exact (mul_eq_zero.mp key).resolve_right hs

/-! ### Certificates

A certificate is a list of pairs `(cell, coefficient)`.  Checking it is one
decidable integer identity on the fifteen coordinates; nothing about the
geometry, the length of the certificate or the size of the coefficients enters
the Lean proof beyond that identity. -/

/-- The value of a form at a pair, as a computable integer. -/
def formVal (F : Form) (k : ℕ) : ℤ := F k

/-- **A certificate is an integer identity.**  `certOK F cert` says that the
form `F` is the integer combination, given by `cert`, of the witness forms of
the cells it lists. -/
def certOK (F : Form) (cert : List (ℕ × ℤ)) : Bool :=
  (List.range 15).all fun k =>
    (cert.map fun x => x.2 * witForm x.1 k).sum == F k

/-- The certificate only names cells the node has already placed. -/
def certSupp (pos : Mask) (cert : List (ℕ × ℤ)) : Bool :=
  cert.all fun x => decide (x.1 < 90) && bitAt pos x.1

theorem chiF_of_cert {p : Fin 6 → Pt} (hgp : GeneralPosition p)
    (cert : List (ℕ × ℤ)) (h : ∀ x ∈ cert, chiF p (witForm x.1) = 1) :
    chiF p (fun k => (cert.map fun x => x.2 * witForm x.1 k).sum) = 1 := by
  induction cert with
  | nil => simpa using chiF_zero p
  | cons x xs ih =>
    have hx : chiF p (witForm x.1) = 1 := h x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, chiF p (witForm y.1) = 1 :=
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e : (fun k => ((x :: xs).map fun z => z.2 * witForm z.1 k).sum)
        = (fun k => (fun m => x.2 * witForm x.1 m) k
            + (fun m => (xs.map fun z => z.2 * witForm z.1 m).sum) k) := by
      funext k; simp
    rw [e, chiF_add hgp, ih hxs, mul_one, chiF_smul p x.2 (witForm x.1), hx, one_zpow]

/-- **The certificate lemma.**  A checked certificate whose cells are all
witnesses of `p` makes the character of its target one.  The three parts are
independent: `certSupp` is about the node, `certOK` about the integers, and
`chiF_of_cert` about the units. -/
theorem chiF_target {p : Fin 6 → Pt} (hgp : GeneralPosition p) {w : Mask}
    (hsup : Supports p w) {pos : Mask}
    (hb : ∀ i, bitAt pos i = true → bitAt w i = true)
    (F : Form) (cert : List (ℕ × ℤ))
    (hs : certSupp pos cert = true) (hc : certOK F cert = true) :
    chiF p F = 1 := by
  have hwit : ∀ x ∈ cert, chiF p (witForm x.1) = 1 := by
    intro x hx
    have hxs := List.all_eq_true.mp hs x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxs
    exact (chiF_witForm_iff hgp hxs.1).mpr (hsup x.1 hxs.1 (hb x.1 hxs.2))
  have hval : ∀ k, k < 15 → (cert.map fun x => x.2 * witForm x.1 k).sum = F k := by
    intro k hk
    have := List.all_eq_true.mp hc k (List.mem_range.mpr hk)
    exact of_decide_eq_true (by simpa using this)
  rw [← chiF_congr p hval]
  exact chiF_of_cert hgp cert hwit
/-! ## The lattice rules in the node theorems

Four new shapes of transcript node.  One of them (`forced`) adds a bit to the
node; the other three close it.  In every case the data is a certificate: a
list of `(cell, coefficient)` pairs whose integer identity the checker tests
with `certOK`, and whose cells the checker requires the node to have already
placed (`certSupp`). -/

/-- The mask of one cell, built with `ofBits` so that `bitAt_ofBits` reads it
off. -/
def cellMask (j : ℕ) : Mask := ofBits 90 (fun i => decide (i = j))

theorem bitAt_cellMask {j i : ℕ} (hi : i < 90) : bitAt (cellMask j) i = decide (i = j) := by
  rw [cellMask, bitAt_ofBits 90 _ i hi]

theorem below_cellMask {w : Mask} {j : ℕ} (h : bitAt w j = true) : Below (cellMask j) w := by
  intro i hb
  rcases lt_or_ge i 90 with hlt | hge
  · rw [bitAt_cellMask hlt, decide_eq_true_eq] at hb
    rw [hb]; exact h
  · rw [cellMask, bitAt_eq_false_of_lt (ofBits_lt 90 _) hge] at hb
    exact absurd hb (by simp)

/-- **The soundness of the lattice rules**, as one statement to thread through
the chain, exactly as `TablesSound` is for the forty-five blocks.  The four
clauses are (K1), (D1), (D2) and (D3). -/
def LatticeSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w : Mask, Carries p w →
    ∀ pos : Mask, Below pos w →
      (∀ (j : ℕ) (cert : List (ℕ × ℤ)), j < 90 → certSupp pos cert = true →
          certOK (witForm j) cert = true → bitAt w j = true)
      ∧ (∀ (a b c : Fin 6) (cert : List (ℕ × ℤ)), a ≠ b → a ≠ c → b ≠ c →
          certSupp pos cert = true → certOK (colForm a b c) cert = true → False)
      ∧ (∀ (u v c d : Fin 6) (cert : List (ℕ × ℤ)), u ≠ v → u ≠ c → u ≠ d →
          v ≠ c → v ≠ d → c ≠ d → certSupp pos cert = true →
          certOK (cycForm u v c d) cert = true → False)
      ∧ (∀ (a x y z : Fin 6) (c₁ c₂ : List (ℕ × ℤ)), a ≠ x → a ≠ y → a ≠ z →
          x ≠ y → x ≠ z → y ≠ z → certSupp pos c₁ = true → certSupp pos c₂ = true →
          certOK (halfForm a x y) c₁ = true → certOK (halfForm a x z) c₂ = true → False)

/-- **The lattice rules are sound.**  This is the one line where the geometry
enters, the counterpart of `tables_sound`. -/
theorem lattice_sound : LatticeSound := by
  intro p hgp w hw pos hb
  have hsup : Supports p w := supports_of_carries hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j cert hj hs hc
    exact (hw j hj).1 ((chiF_witForm_iff hgp hj).mp
      (chiF_target hgp hsup hb (witForm j) cert hs hc))
  · intro a b c cert hab hac hbc hs hc
    exact ncol_of_gp hgp hab hac hbc
      (chiF_colForm hgp hab hac (chiF_target hgp hsup hb (colForm a b c) cert hs hc))
  · intro u v c d cert huv huc hud hvc hvd hcd hs hc
    exact ncyc_of_gp hgp huv huc hud hvc hvd hcd
      (chiF_cycForm hgp huc hvd hud hvc
        (chiF_target hgp hsup hb (cycForm u v c d) cert hs hc))
  · intro a x y z c₁ c₂ hax hay haz hxy hxz hyz hs₁ hs₂ hc₁ hc₂
    have r₁ := chiF_halfForm hgp hax hay
      (chiF_target hgp hsup hb (halfForm a x y) c₁ hs₁ hc₁)
    have r₂ := chiF_halfForm hgp hax haz
      (chiF_target hgp hsup hb (halfForm a x z) c₂ hs₂ hc₂)
    have q₁ : qq (p x) (p y) (p a) = 0 :=
      (mul_eq_zero.mp r₁).resolve_right (ncol_of_gp hgp hax hay hxy)
    have q₂ : qq (p x) (p z) (p a) = 0 :=
      (mul_eq_zero.mp r₂).resolve_right (ncol_of_gp hgp hax haz hxz)
    exact ncol_of_gp hgp hay haz hyz
      (collinear_of_two_right_angles (ne_of_gp hgp (Ne.symm hax)) q₁ q₂)

/-! ### The four node lemmas -/

/-- **(K1).**  A cell whose witness form lies in the lattice of the node's
cells is a witness, so the node may be strengthened by that bit. -/
theorem settles_forced (hL : LatticeSound) {pos neg : Mask} {j : ℕ}
    {cert : List (ℕ × ℤ)} (hj : j < 90) (hs : certSupp pos cert = true)
    (hc : certOK (witForm j) cert = true)
    (h : Settles (pos ||| cellMask j) neg) : Settles pos neg := by
  intro p hgp hrep w hlt hw hb ha
  exact h p hgp hrep w hlt hw (below_or hb (below_cellMask
    ((hL p hgp w hw pos hb).1 j cert hj hs hc))) ha

/-- **(D1).**  A collinearity form in the lattice contradicts general position. -/
theorem refutes_col (hL : LatticeSound) {pos neg : Mask} {a b c : Fin 6}
    {cert : List (ℕ × ℤ)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : certSupp pos cert = true) (hc : certOK (colForm a b c) cert = true) :
    Refutes pos neg := fun p hgp _ w _ hw hb _ =>
  (hL p hgp w hw pos hb).2.1 a b c cert hab hac hbc hs hc

/-- **(D2).**  A concyclicity form in the lattice contradicts general position. -/
theorem refutes_cyc (hL : LatticeSound) {pos neg : Mask} {u v c d : Fin 6}
    {cert : List (ℕ × ℤ)} (huv : u ≠ v) (huc : u ≠ c) (hud : u ≠ d) (hvc : v ≠ c)
    (hvd : v ≠ d) (hcd : c ≠ d) (hs : certSupp pos cert = true)
    (hc : certOK (cycForm u v c d) cert = true) : Refutes pos neg :=
  fun p hgp _ w _ hw hb _ =>
    (hL p hgp w hw pos hb).2.2.1 u v c d cert huv huc hud hvc hvd hcd hs hc

/-- **(D3).**  Two `mod π/2` forms in the lattice put three points of the class
around one point, and two right angles at one point put three points on a line. -/
theorem refutes_half (hL : LatticeSound) {pos neg : Mask} {a x y z : Fin 6}
    {c₁ c₂ : List (ℕ × ℤ)} (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs₁ : certSupp pos c₁ = true) (hs₂ : certSupp pos c₂ = true)
    (hc₁ : certOK (halfForm a x y) c₁ = true)
    (hc₂ : certOK (halfForm a x z) c₂ = true) : Refutes pos neg :=
  fun p hgp _ w _ hw hb _ =>
    (hL p hgp w hw pos hb).2.2.2 a x y z c₁ c₂ hax hay haz hxy hxz hyz hs₁ hs₂ hc₁ hc₂

/-! ### The extended transcript -/


/-! ## The relation space of the equal-radius classes

Two triangles with the same circumradius that share the edge `u v` have
circumcentres `o₁`, `o₂` with `o₁ + o₂ = p u + p v`: the quadrilateral they
span is a rhombus, and the diagonals of a rhombus bisect (`centers_sum`).  A
cell of the census is exactly such a pair of triangles, so an integer
combination of witness cells in which **every triangle cancels** leaves an
identity between the points alone,

  `Σ cᵢ pᵢ = 0`  with  `Σ cᵢ = 0`.

The space of these identities is the *relation space* of the node.  Rule (C4)
says it has no nonzero element with at most three nonzero coefficients: such an
element is an affine dependence between three of the six points, that is, three
points on one line, which general position forbids.  Support one and support
two are the same statement read with a coefficient equal to zero.

Nothing below constructs the relation space.  A certificate is a list of cells
with integer coefficients, and the four things checked of it are decidable: the
cells are ones the node has already placed, every triangle coefficient
vanishes, the point coefficients live on three named points, and those three
add up to zero without all vanishing.
-/

/-- The twenty triangles of the six points, as increasing triples. -/
def triList : List (Fin 6 × Fin 6 × Fin 6) :=
  [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3),
   (0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5), (0, 4, 5),
   (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5),
   (1, 4, 5), (2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]

/-- The triangle with index `t` (a fixed dummy outside the range). -/
def triOf (t : ℕ) : Fin 6 × Fin 6 × Fin 6 := triList.getD t (0, 0, 0)

/-- `i` is a vertex of the triangle `T`. -/
def memTri (i : Fin 6) (T : Fin 6 × Fin 6 × Fin 6) : Bool :=
  decide (i = T.1) || decide (i = T.2.1) || decide (i = T.2.2)

/-- The index of the triangle whose vertices are `{a, b, c}`. -/
def triNum (a b c : Fin 6) : ℕ :=
  triList.findIdx (fun T => memTri a T && memTri b T && memTri c T)

theorem triOf_distinct : ∀ t : Fin 20,
    (triOf t.val).1 ≠ (triOf t.val).2.1 ∧ (triOf t.val).1 ≠ (triOf t.val).2.2 ∧
      (triOf t.val).2.1 ≠ (triOf t.val).2.2 := by decide +kernel

/-- `triNum` inverts `triOf` on the triangles: three different points give an
index below twenty whose triangle has all three of them as vertices. -/
theorem triNum_spec : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
    triNum a b c < 20 ∧ memTri a (triOf (triNum a b c)) = true ∧
      memTri b (triOf (triNum a b c)) = true ∧
      memTri c (triOf (triNum a b c)) = true := by decide +kernel

/-- The first triangle of the cell `j`: its edge together with the first apex. -/
def cellTriA (j : ℕ) : ℕ := triNum (cellOf j).2.1 (cellOf j).2.2 (cellOf j).1.1

/-- The second triangle of the cell `j`: its edge together with the second
apex. -/
def cellTriB (j : ℕ) : ℕ := triNum (cellOf j).2.1 (cellOf j).2.2 (cellOf j).1.2

/-! ### One witness cell -/

/-- **The one-cell identity.**  The circumcentres of the two triangles of a
witness cell add up to the two endpoints of its edge.  This is the only place
where the geometry of the relation space enters. -/
theorem centers_sum_of_psi {p : Fin 6 → Pt} {oa ob : Pt} {ra rb : ℝ}
    (hgp : GeneralPosition p) {a b c d : Fin 6}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (ha1 : sqdist oa (p c) = ra) (ha2 : sqdist oa (p d) = ra) (ha3 : sqdist oa (p a) = ra)
    (hb1 : sqdist ob (p c) = rb) (hb2 : sqdist ob (p d) = rb) (hb3 : sqdist ob (p b) = rb)
    (hpsi : Psi (p c) (p d) (p a) (p b) = 0) :
    oa.1 + ob.1 = (p c).1 + (p d).1 ∧ oa.2 + ob.2 = (p c).2 + (p d).2 := by
  have hncA : ¬ Collinear3 (p c) (p d) (p a) := ncol_of_gp hgp hcd hac.symm had.symm
  have hncB : ¬ Collinear3 (p c) (p d) (p b) := ncol_of_gp hgp hcd hbc.symm hbd.symm
  have hncyc : ¬ Concyclic4 (p c) (p d) (p a) (p b) :=
    ncyc_of_gp hgp hcd hac.symm hbc.symm had.symm hbd.symm hab
  have hrr : ra = rb :=
    (eqRadSq_iff_psi (ne_of_gp hgp hcd) hncA hncB hncyc
      ⟨oa, ha1, ha2, ha3⟩ ⟨ob, hb1, hb2, hb3⟩).mpr hpsi
  have hoo : oa ≠ ob := by
    intro h
    subst h
    exact hncyc (concyclic_of_common_center ha1 ha2 ha3 (by rw [hb3, hrr]))
  exact centers_sum (ne_of_gp hgp hcd) hoo ha2 ha1 (by rw [hb2, hrr]) (by rw [hb1, hrr])

/-- Every triangle of a configuration in general position has a circumcentre;
they are chosen once and for all. -/
theorem exists_centers {p : Fin 6 → Pt} (hgp : GeneralPosition p) :
    ∃ (ctr : ℕ → Pt) (rad : ℕ → ℝ), ∀ t, t < 20 → ∀ i : Fin 6,
      memTri i (triOf t) = true → sqdist (ctr t) (p i) = rad t := by
  have key : ∀ t : ℕ, ∃ z : Pt × ℝ, t < 20 → ∀ i : Fin 6,
      memTri i (triOf t) = true → sqdist z.1 (p i) = z.2 := by
    intro t
    by_cases ht : t < 20
    · obtain ⟨d1, d2, d3⟩ := triOf_distinct ⟨t, ht⟩
      obtain ⟨r, o, h1, h2, h3⟩ :=
        exists_circumRadiusSq (fun hz => ncol_of_gp hgp d1 d2 d3 hz)
      refine ⟨(o, r), fun _ i hi => ?_⟩
      simp only [memTri, Bool.or_eq_true, decide_eq_true_eq] at hi
      rcases hi with (hi | hi) | hi
      · rw [hi]; exact h1
      · rw [hi]; exact h2
      · rw [hi]; exact h3
    · exact ⟨((0, 0), 0), fun h => absurd h ht⟩
  choose f hf using key
  exact ⟨fun t => (f t).1, fun t => (f t).2, fun t ht i hi => hf t ht i hi⟩

/-! ### The certificate -/

/-- The coefficient of the triangle `t` in a certificate. -/
def triCoef : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => 0
  | x :: xs, t => x.2 * (if cellTriA x.1 = t then 1 else 0)
      + (x.2 * (if cellTriB x.1 = t then 1 else 0) + triCoef xs t)

/-- The coefficient of the point `i` in a certificate: the endpoints of the
edges, which is what the triangle centres add up to. -/
def ptCoef : List (ℕ × ℤ) → Fin 6 → ℤ
  | [], _ => 0
  | x :: xs, i => x.2 * (if (cellOf x.1).2.1 = i then 1 else 0)
      + (x.2 * (if (cellOf x.1).2.2 = i then 1 else 0) + ptCoef xs i)

/-- Every triangle coefficient of the certificate vanishes. -/
def relTriZero (cert : List (ℕ × ℤ)) : Bool :=
  decide (∀ t : Fin 20, triCoef cert t.val = 0)

/-- The point coefficients of the certificate live on the three points `a`,
`b`, `c`. -/
def relOut (a b c : Fin 6) (cert : List (ℕ × ℤ)) : Bool :=
  decide (∀ i : Fin 6, i = a ∨ i = b ∨ i = c ∨ ptCoef cert i = 0)

/-- The three point coefficients add up to zero and do not all vanish. -/
def relTrip (a b c : Fin 6) (cert : List (ℕ × ℤ)) : Bool :=
  decide (ptCoef cert a + ptCoef cert b + ptCoef cert c = 0 ∧
    (ptCoef cert a ≠ 0 ∨ ptCoef cert b ≠ 0 ∨ ptCoef cert c ≠ 0))

/-! ### Two pieces of bookkeeping -/

/-- Peeling one Kronecker delta off a weighted sum over a finite set. -/
theorem sum_peel {α : Type} [DecidableEq α] {s : Finset α} {c u : α → ℤ}
    {f : α → ℝ} {j : α} (hj : j ∈ s) {d : ℤ}
    (h : ∀ t, c t = d * (if j = t then 1 else 0) + u t) :
    ∑ t ∈ s, (c t : ℝ) * f t = (d : ℝ) * f j + ∑ t ∈ s, (u t : ℝ) * f t := by
  have e : ∀ t ∈ s, (c t : ℝ) * f t
      = (if j = t then (d : ℝ) * f t else 0) + (u t : ℝ) * f t := by
    intro t _
    rw [h t]
    split_ifs with hh <;> push_cast <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib,
    Finset.sum_ite_eq s j (fun t => (d : ℝ) * f t), if_pos hj]

/-- A sum over the six points with only three nonzero terms. -/
theorem sum_three {g : Fin 6 → ℝ} {a b c : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : ∀ i : Fin 6, i ≠ a → i ≠ b → i ≠ c → g i = 0) :
    ∑ i : Fin 6, g i = g a + g b + g c := by
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      i ∉ ({a, b, c} : Finset (Fin 6)) → g i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h0 i hi.1 hi.2.1 hi.2.2
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b, c} : Finset (Fin 6))) hz,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ring

/-- The signed area changes sign when the first two vertices are swapped. -/
theorem cross_swap₁₂ (a b c : Pt) : cross b a c = - cross a b c := by
  simp only [cross]; ring

/-- The signed area changes sign when the last two vertices are swapped. -/
theorem cross_swap₂₃ (a b c : Pt) : cross a c b = - cross a b c := by
  simp only [cross]; ring

/-- **The affine-dependence step.**  Three coefficients that add up to zero and
annihilate the three points multiply the signed area to zero.  The plane
identity behind it is that `vb (b - a) = - vc (c - a)`. -/
theorem coef_mul_cross {va vb vc : ℝ} {a b c : Pt}
    (hs : va + vb + vc = 0)
    (h1 : va * a.1 + vb * b.1 + vc * c.1 = 0)
    (h2 : va * a.2 + vb * b.2 + vc * c.2 = 0) :
    vb * cross a b c = 0 := by
  simp only [cross]
  linear_combination (-a.1 * (c.2 - a.2) + a.2 * (c.1 - a.1)) * hs
    + (c.2 - a.2) * h1 - (c.1 - a.1) * h2

/-! ### The certificate produces a relation between the points -/

/-- **The balance identity.**  For a certificate all of whose cells are
witnesses, the triangle side and the point side of the certificate agree.  The
induction takes one cell at a time; the one-cell step is
`centers_sum_of_psi`. -/
theorem rel_balance {p : Fin 6 → Pt} {ctr : ℕ → Pt} {rad : ℕ → ℝ}
    (hgp : GeneralPosition p)
    (hctr : ∀ t, t < 20 → ∀ i : Fin 6, memTri i (triOf t) = true →
      sqdist (ctr t) (p i) = rad t) :
    ∀ cert : List (ℕ × ℤ), (∀ x ∈ cert, x.1 < 90 ∧ cellPsi p x.1 = 0) →
      (∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).1
          = ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).1) ∧
        (∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).2
          = ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).2) := by
  intro cert
  induction cert with
  | nil =>
    intro _
    constructor <;>
      simp only [triCoef, ptCoef, Int.cast_zero, zero_mul, Finset.sum_const_zero]
  | cons x xs ih =>
    intro hs
    obtain ⟨hx90, hxpsi⟩ := hs x (List.mem_cons_self ..)
    obtain ⟨e1, e2⟩ := ih (fun y hy => hs y (List.mem_cons_of_mem _ hy))
    obtain ⟨hab0, hcd0, hac0, had0, hbc0, hbd0⟩ := cellOf_distinct ⟨x.1, hx90⟩
    have hab : (cellOf x.1).1.1 ≠ (cellOf x.1).1.2 := hab0
    have hcd : (cellOf x.1).2.1 ≠ (cellOf x.1).2.2 := hcd0
    have hac : (cellOf x.1).1.1 ≠ (cellOf x.1).2.1 := hac0
    have had : (cellOf x.1).1.1 ≠ (cellOf x.1).2.2 := had0
    have hbc : (cellOf x.1).1.2 ≠ (cellOf x.1).2.1 := hbc0
    have hbd : (cellOf x.1).1.2 ≠ (cellOf x.1).2.2 := hbd0
    obtain ⟨hA, hAc, hAd, hAa⟩ :=
      triNum_spec (cellOf x.1).2.1 (cellOf x.1).2.2 (cellOf x.1).1.1
        hcd hac.symm had.symm
    obtain ⟨hB, hBc, hBd, hBb⟩ :=
      triNum_spec (cellOf x.1).2.1 (cellOf x.1).2.2 (cellOf x.1).1.2
        hcd hbc.symm hbd.symm
    have hA' : cellTriA x.1 < 20 := hA
    have hB' : cellTriB x.1 < 20 := hB
    have hAc' : memTri (cellOf x.1).2.1 (triOf (cellTriA x.1)) = true := hAc
    have hAd' : memTri (cellOf x.1).2.2 (triOf (cellTriA x.1)) = true := hAd
    have hAa' : memTri (cellOf x.1).1.1 (triOf (cellTriA x.1)) = true := hAa
    have hBc' : memTri (cellOf x.1).2.1 (triOf (cellTriB x.1)) = true := hBc
    have hBd' : memTri (cellOf x.1).2.2 (triOf (cellTriB x.1)) = true := hBd
    have hBb' : memTri (cellOf x.1).1.2 (triOf (cellTriB x.1)) = true := hBb
    have hxpsi' : Psi (p (cellOf x.1).2.1) (p (cellOf x.1).2.2)
        (p (cellOf x.1).1.1) (p (cellOf x.1).1.2) = 0 := hxpsi
    obtain ⟨g1, g2⟩ := centers_sum_of_psi hgp hab hcd hac had hbc hbd
      (hctr _ hA' _ hAc') (hctr _ hA' _ hAd') (hctr _ hA' _ hAa')
      (hctr _ hB' _ hBc') (hctr _ hB' _ hBd') (hctr _ hB' _ hBb') hxpsi'
    have tA1 : ∑ t ∈ Finset.range 20, (triCoef (x :: xs) t : ℝ) * (ctr t).1
        = (x.2 : ℝ) * (ctr (cellTriA x.1)).1
          + ∑ t ∈ Finset.range 20,
              ((x.2 * (if cellTriB x.1 = t then 1 else 0) + triCoef xs t : ℤ) : ℝ)
                * (ctr t).1 :=
      sum_peel (Finset.mem_range.mpr hA') (fun t => by simp only [triCoef])
    have tB1 : ∑ t ∈ Finset.range 20,
          ((x.2 * (if cellTriB x.1 = t then 1 else 0) + triCoef xs t : ℤ) : ℝ) * (ctr t).1
        = (x.2 : ℝ) * (ctr (cellTriB x.1)).1
          + ∑ t ∈ Finset.range 20, (triCoef xs t : ℝ) * (ctr t).1 :=
      sum_peel (Finset.mem_range.mpr hB') (fun _ => rfl)
    have tA2 : ∑ t ∈ Finset.range 20, (triCoef (x :: xs) t : ℝ) * (ctr t).2
        = (x.2 : ℝ) * (ctr (cellTriA x.1)).2
          + ∑ t ∈ Finset.range 20,
              ((x.2 * (if cellTriB x.1 = t then 1 else 0) + triCoef xs t : ℤ) : ℝ)
                * (ctr t).2 :=
      sum_peel (Finset.mem_range.mpr hA') (fun t => by simp only [triCoef])
    have tB2 : ∑ t ∈ Finset.range 20,
          ((x.2 * (if cellTriB x.1 = t then 1 else 0) + triCoef xs t : ℤ) : ℝ) * (ctr t).2
        = (x.2 : ℝ) * (ctr (cellTriB x.1)).2
          + ∑ t ∈ Finset.range 20, (triCoef xs t : ℝ) * (ctr t).2 :=
      sum_peel (Finset.mem_range.mpr hB') (fun _ => rfl)
    have pA1 : ∑ i : Fin 6, (ptCoef (x :: xs) i : ℝ) * (p i).1
        = (x.2 : ℝ) * (p (cellOf x.1).2.1).1
          + ∑ i : Fin 6,
              ((x.2 * (if (cellOf x.1).2.2 = i then 1 else 0) + ptCoef xs i : ℤ) : ℝ)
                * (p i).1 :=
      sum_peel (Finset.mem_univ _) (fun i => by simp only [ptCoef])
    have pB1 : ∑ i : Fin 6,
          ((x.2 * (if (cellOf x.1).2.2 = i then 1 else 0) + ptCoef xs i : ℤ) : ℝ) * (p i).1
        = (x.2 : ℝ) * (p (cellOf x.1).2.2).1
          + ∑ i : Fin 6, (ptCoef xs i : ℝ) * (p i).1 :=
      sum_peel (Finset.mem_univ _) (fun _ => rfl)
    have pA2 : ∑ i : Fin 6, (ptCoef (x :: xs) i : ℝ) * (p i).2
        = (x.2 : ℝ) * (p (cellOf x.1).2.1).2
          + ∑ i : Fin 6,
              ((x.2 * (if (cellOf x.1).2.2 = i then 1 else 0) + ptCoef xs i : ℤ) : ℝ)
                * (p i).2 :=
      sum_peel (Finset.mem_univ _) (fun i => by simp only [ptCoef])
    have pB2 : ∑ i : Fin 6,
          ((x.2 * (if (cellOf x.1).2.2 = i then 1 else 0) + ptCoef xs i : ℤ) : ℝ) * (p i).2
        = (x.2 : ℝ) * (p (cellOf x.1).2.2).2
          + ∑ i : Fin 6, (ptCoef xs i : ℝ) * (p i).2 :=
      sum_peel (Finset.mem_univ _) (fun _ => rfl)
    refine ⟨?_, ?_⟩
    · rw [tA1, tB1, pA1, pB1]
      linear_combination e1 + (x.2 : ℝ) * g1
    · rw [tA2, tB2, pA2, pB2]
      linear_combination e2 + (x.2 : ℝ) * g2

/-! ### Rule (C4) as a node lemma -/

/-- **The soundness of the relation rule**, as one statement to thread through
the chain, exactly as `TablesSound` is for the forty-five blocks and
`LatticeSound` for the lattice. -/
def RelationSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w : Mask, Carries p w →
    ∀ pos : Mask, Below pos w →
      ∀ (a b c : Fin 6) (cert : List (ℕ × ℤ)), a ≠ b → a ≠ c → b ≠ c →
        certSupp pos cert = true → relTriZero cert = true →
        relOut a b c cert = true → relTrip a b c cert = true → False

/-- **The relation rule is sound.**  This is the counterpart of `tables_sound`
and `lattice_sound`: the whole of (C4) in one place. -/
theorem relation_sound : RelationSound := by
  intro p hgp w hw pos hb a b c cert hab hac hbc hs htz hout htrip
  obtain ⟨ctr, rad, hctr⟩ := exists_centers hgp
  have hsup : Supports p w := supports_of_carries hw
  have hcells : ∀ x ∈ cert, x.1 < 90 ∧ cellPsi p x.1 = 0 := by
    intro x hx
    have h := List.all_eq_true.mp hs x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, hsup x.1 h.1 (hb x.1 h.2)⟩
  obtain ⟨bal1, bal2⟩ := rel_balance hgp hctr cert hcells
  have htz' : ∀ t, t < 20 → triCoef cert t = 0 := fun t ht =>
    of_decide_eq_true htz ⟨t, ht⟩
  have z1 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).1 = 0 :=
    Finset.sum_eq_zero (fun t ht => by
      rw [htz' t (Finset.mem_range.mp ht)]; simp)
  have z2 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).2 = 0 :=
    Finset.sum_eq_zero (fun t ht => by
      rw [htz' t (Finset.mem_range.mp ht)]; simp)
  have hout' : ∀ i : Fin 6, i ≠ a → i ≠ b → i ≠ c → ptCoef cert i = 0 := by
    intro i h1 h2 h3
    rcases of_decide_eq_true hout i with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  have s1 : ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).1
      = (ptCoef cert a : ℝ) * (p a).1 + (ptCoef cert b : ℝ) * (p b).1
        + (ptCoef cert c : ℝ) * (p c).1 :=
    sum_three (g := fun i => (ptCoef cert i : ℝ) * (p i).1) hab hac hbc
      (fun i h1 h2 h3 => by rw [hout' i h1 h2 h3]; simp)
  have s2 : ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).2
      = (ptCoef cert a : ℝ) * (p a).2 + (ptCoef cert b : ℝ) * (p b).2
        + (ptCoef cert c : ℝ) * (p c).2 :=
    sum_three (g := fun i => (ptCoef cert i : ℝ) * (p i).2) hab hac hbc
      (fun i h1 h2 h3 => by rw [hout' i h1 h2 h3]; simp)
  obtain ⟨hsumZ, hnzZ⟩ := of_decide_eq_true htrip
  have hsum : (ptCoef cert a : ℝ) + (ptCoef cert b : ℝ) + (ptCoef cert c : ℝ) = 0 := by
    exact_mod_cast hsumZ
  have r1 : (ptCoef cert a : ℝ) * (p a).1 + (ptCoef cert b : ℝ) * (p b).1
      + (ptCoef cert c : ℝ) * (p c).1 = 0 := by
    rw [← s1, ← bal1]; exact z1
  have r2 : (ptCoef cert a : ℝ) * (p a).2 + (ptCoef cert b : ℝ) * (p b).2
      + (ptCoef cert c : ℝ) * (p c).2 = 0 := by
    rw [← s2, ← bal2]; exact z2
  have hcol : cross (p a) (p b) (p c) = 0 := by
    have kb : (ptCoef cert b : ℝ) * cross (p a) (p b) (p c) = 0 :=
      coef_mul_cross hsum r1 r2
    have ka : (ptCoef cert a : ℝ) * cross (p b) (p a) (p c) = 0 :=
      coef_mul_cross (va := (ptCoef cert b : ℝ)) (vc := (ptCoef cert c : ℝ))
        (by linarith) (by linarith) (by linarith)
    have kc : (ptCoef cert c : ℝ) * cross (p a) (p c) (p b) = 0 :=
      coef_mul_cross (va := (ptCoef cert a : ℝ)) (vc := (ptCoef cert b : ℝ))
        (by linarith) (by linarith) (by linarith)
    rw [cross_swap₁₂] at ka
    rw [cross_swap₂₃] at kc
    rcases hnzZ with h | h | h
    · have hn : (ptCoef cert a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp ka with h' | h'
      · exact absurd h' hn
      · linarith
    · have hn : (ptCoef cert b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp kb with h' | h'
      · exact absurd h' hn
      · exact h'
    · have hn : (ptCoef cert c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp kc with h' | h'
      · exact absurd h' hn
      · linarith
  exact ncol_of_gp hgp hab hac hbc hcol

/-- **(C4).**  A relation certificate closes the node. -/
theorem refutes_rel (hR : RelationSound) {pos neg : Mask} {a b c : Fin 6}
    {cert : List (ℕ × ℤ)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : certSupp pos cert = true) (ht : relTriZero cert = true)
    (ho : relOut a b c cert = true) (hp : relTrip a b c cert = true) :
    Refutes pos neg :=
  fun p hgp _ w _ hw hb _ => hR p hgp w hw pos hb a b c cert hab hac hbc hs ht ho hp

/-! ## The closure of the equal-radius classes: rule (D4)

Equality of circumradii is transitive.  If a chain of witness cells joins the
two triangles of a cell, then those two triangles have the same circumradius,
so that cell is a witness as well -- whether or not the node has placed it.
This is what the census calls the **closure**, and it is what makes the
relation space of a node larger than the cells the node lists.  Without it,
rule (C4) sees only part of the space.  (Measured separately outside Lean: on
420 random sub-masks of the thirty-five census classes, the relation space of
the closure agrees with the census's own, and the relation space of the bare
cells does not.)

Two rules of the census drop out of this one.  Three triangles on one edge in
one class force three witnesses on that edge, which the matching table of rule
(C) already rejects; that is (C2).  And a relation space of dimension four or
more always contains a nonzero element supported on three points -- inside the
five-dimensional space `Σ cᵢ = 0`, a four-dimensional subspace meets the
two-dimensional one cut out by three coordinates -- so (C5) follows from (C4).
-/

/-- The witness condition of a cell, read off the chosen circumradii. -/
theorem psi_iff_rad {p : Fin 6 → Pt} {ctr : ℕ → Pt} {rad : ℕ → ℝ}
    (hgp : GeneralPosition p)
    (hctr : ∀ t, t < 20 → ∀ i : Fin 6, memTri i (triOf t) = true →
      sqdist (ctr t) (p i) = rad t)
    {j : ℕ} (hj : j < 90) :
    cellPsi p j = 0 ↔ rad (cellTriA j) = rad (cellTriB j) := by
  obtain ⟨hab0, hcd0, hac0, had0, hbc0, hbd0⟩ := cellOf_distinct ⟨j, hj⟩
  have hab : (cellOf j).1.1 ≠ (cellOf j).1.2 := hab0
  have hcd : (cellOf j).2.1 ≠ (cellOf j).2.2 := hcd0
  have hac : (cellOf j).1.1 ≠ (cellOf j).2.1 := hac0
  have had : (cellOf j).1.1 ≠ (cellOf j).2.2 := had0
  have hbc : (cellOf j).1.2 ≠ (cellOf j).2.1 := hbc0
  have hbd : (cellOf j).1.2 ≠ (cellOf j).2.2 := hbd0
  obtain ⟨hA, hAc, hAd, hAa⟩ :=
    triNum_spec (cellOf j).2.1 (cellOf j).2.2 (cellOf j).1.1 hcd hac.symm had.symm
  obtain ⟨hB, hBc, hBd, hBb⟩ :=
    triNum_spec (cellOf j).2.1 (cellOf j).2.2 (cellOf j).1.2 hcd hbc.symm hbd.symm
  have hA' : cellTriA j < 20 := hA
  have hB' : cellTriB j < 20 := hB
  have hAc' : memTri (cellOf j).2.1 (triOf (cellTriA j)) = true := hAc
  have hAd' : memTri (cellOf j).2.2 (triOf (cellTriA j)) = true := hAd
  have hAa' : memTri (cellOf j).1.1 (triOf (cellTriA j)) = true := hAa
  have hBc' : memTri (cellOf j).2.1 (triOf (cellTriB j)) = true := hBc
  have hBd' : memTri (cellOf j).2.2 (triOf (cellTriB j)) = true := hBd
  have hBb' : memTri (cellOf j).1.2 (triOf (cellTriB j)) = true := hBb
  have hr : CircumRadiusSq (p (cellOf j).2.1) (p (cellOf j).2.2) (p (cellOf j).1.1)
      (rad (cellTriA j)) :=
    ⟨ctr (cellTriA j), hctr _ hA' _ hAc', hctr _ hA' _ hAd', hctr _ hA' _ hAa'⟩
  have hs : CircumRadiusSq (p (cellOf j).2.1) (p (cellOf j).2.2) (p (cellOf j).1.2)
      (rad (cellTriB j)) :=
    ⟨ctr (cellTriB j), hctr _ hB' _ hBc', hctr _ hB' _ hBd', hctr _ hB' _ hBb'⟩
  have e := eqRadSq_iff_psi (ne_of_gp hgp hcd) (ncol_of_gp hgp hcd hac.symm had.symm)
    (ncol_of_gp hgp hcd hbc.symm hbd.symm)
    (ncyc_of_gp hgp hcd hac.symm hbc.symm had.symm hbd.symm hab) hr hs
  have hp : cellPsi p j = Psi (p (cellOf j).2.1) (p (cellOf j).2.2)
      (p (cellOf j).1.1) (p (cellOf j).1.2) := rfl
  rw [hp]
  exact e.symm

/-- Walking a chain of cells in the graph whose vertices are the twenty
triangles: each cell is an edge between its own two triangles. -/
def triWalk : ℕ → List ℕ → Option ℕ
  | t, [] => some t
  | t, x :: xs =>
      if cellTriA x = t then triWalk (cellTriB x) xs
      else if cellTriB x = t then triWalk (cellTriA x) xs
      else none

/-- The chain test: every cell of the chain is one the node has already placed,
and the chain walks from the first triangle of `j` to the second. -/
def chainOK (pos : Mask) (j : ℕ) (path : List ℕ) : Bool :=
  path.all (fun x => decide (x < 90) && bitAt pos x) &&
    (triWalk (cellTriA j) path == some (cellTriB j))

/-- A chain of witness cells carries one circumradius to another. -/
theorem triWalk_rad {p : Fin 6 → Pt} {ctr : ℕ → Pt} {rad : ℕ → ℝ} {w : Mask}
    (hgp : GeneralPosition p)
    (hctr : ∀ t, t < 20 → ∀ i : Fin 6, memTri i (triOf t) = true →
      sqdist (ctr t) (p i) = rad t)
    (hsup : Supports p w) :
    ∀ (path : List ℕ) (t t' : ℕ),
      path.all (fun x => decide (x < 90) && bitAt w x) = true →
      triWalk t path = some t' → rad t = rad t' := by
  intro path
  induction path with
  | nil =>
    intro t t' _ h
    simp only [triWalk, Option.some.injEq] at h
    rw [h]
  | cons x xs ih =>
    intro t t' hall h
    have hx := List.all_eq_true.mp hall x (List.mem_cons_self ..)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    have hxs : xs.all (fun y => decide (y < 90) && bitAt w y) = true :=
      List.all_eq_true.mpr
        (fun y hy => List.all_eq_true.mp hall y (List.mem_cons_of_mem _ hy))
    have hrx : rad (cellTriA x) = rad (cellTriB x) :=
      (psi_iff_rad hgp hctr hx.1).mp (hsup x hx.1 hx.2)
    simp only [triWalk] at h
    split_ifs at h with h1 h2
    · rw [← h1, hrx]; exact ih _ _ hxs h
    · rw [← h2, ← hrx]; exact ih _ _ hxs h

/-- **The soundness of the closure rule**, as one statement to thread through
the chain. -/
def ClosureSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w : Mask, Carries p w →
    ∀ pos : Mask, Below pos w →
      ∀ (j : ℕ) (path : List ℕ), j < 90 → chainOK pos j path = true →
        bitAt w j = true

/-- **The closure rule is sound.** -/
theorem closure_sound : ClosureSound := by
  intro p hgp w hw pos hb j path hj hc
  obtain ⟨ctr, rad, hctr⟩ := exists_centers hgp
  have hsup : Supports p w := supports_of_carries hw
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hall, hwalk⟩ := hc
  have hall' : path.all (fun x => decide (x < 90) && bitAt w x) = true := by
    refine List.all_eq_true.mpr (fun y hy => ?_)
    have hy' := List.all_eq_true.mp hall y hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hy'
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hy'.1, hb y hy'.2⟩
  have hrad : rad (cellTriA j) = rad (cellTriB j) :=
    triWalk_rad hgp hctr hsup path _ _ hall' hwalk
  exact (hw j hj).1 ((psi_iff_rad hgp hctr hj).mpr hrad)

/-! ### The two new node lemmas -/

/-- **(D4).**  A cell joined to the node's cells by a chain is a witness, so
the node may be strengthened by that bit. -/
theorem settles_chain (hC : ClosureSound) {pos neg : Mask} {j : ℕ} {path : List ℕ}
    (hj : j < 90) (hc : chainOK pos j path = true)
    (h : Settles (pos ||| cellMask j) neg) : Settles pos neg := by
  intro p hgp hrep w hlt hw hb ha
  exact h p hgp hrep w hlt hw
    (below_or hb (below_cellMask (hC p hgp w hw pos hb j path hj hc))) ha

/-- The `k`-th block of the node test. -/
def ruleAt (k : ℕ) : Block × List Pat := nodeRules.getD k ((0, 0, 0, 0, 0, 0), [])

/-- The children of a branch on block `k`: each allowed pattern with the two
masks it forces, precomputed so that the kernel does not rebuild them. -/
def branchOf (k : ℕ) : List (Pat × Mask × Mask) := branchTable.getD k []

def branchOk (k : ℕ) : Bool :=
  ((branchOf k).map (fun x => x.1) == (ruleAt k).2) &&
    (branchOf k).all (fun x => (selMask (ruleAt k).1 x.1 == x.2.1) &&
      (selMask (ruleAt k).1 (negPat x.1) == x.2.2))

theorem branchOk_all : (List.range 15).all branchOk = true := by decide +kernel

theorem ruleAt_mem_all : (List.range 15).all (fun k => nodeRules.contains (ruleAt k)) = true := by
  decide

theorem ruleAt_mem {k : ℕ} (hk : k < 15) : ruleAt k ∈ nodeRules :=
  List.mem_of_elem_eq_true (List.all_eq_true.mp ruleAt_mem_all k (List.mem_range.mpr hk))

def zipAll {α β : Type} (g : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => g a b && zipAll g as bs
  | _, _ => false

theorem zipAll_of {α β : Type} {g : α → β → Bool} : ∀ (as : List α) (bs : List β),
    zipAll g as bs = true → ∀ a ∈ as, ∃ b, g a b = true := by
  intro as
  induction as with
  | nil => intro bs _ a ha; simp at ha
  | cons a as ih =>
    intro bs h x hx
    cases bs with
    | nil => simp [zipAll] at h
    | cons b bs =>
      simp only [zipAll, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, h.1⟩
      · exact ih bs h.2 x hx'

/-! ## Propagation from the forty-five tables

The transcript of the earlier flights only ever added **positive** bits to a
node: rule (K1) from the lattice and rule (D4) from the closure both say "this
cell is a witness".  The forty-five tables themselves force bits in *both*
directions.  If every allowed pattern of a block that is still compatible with
the node has a given bit set, the cell is a witness; if every one of them has it
clear, the cell is not.  This is the propagation the census performs before it
branches, and leaving it out is the single largest reason a tree that branches
from the empty node is bigger than the census's own search.

Nothing new is assumed here.  The soundness of this node is `TablesSound`, the
very statement the branching node already uses; the propagation is the tables
read in the other direction.
-/

/-- Componentwise conjunction of two patterns. -/
def andPat (q r : Pat) : Pat :=
  (q.1 && r.1, q.2.1 && r.2.1, q.2.2.1 && r.2.2.1, q.2.2.2.1 && r.2.2.2.1,
    q.2.2.2.2.1 && r.2.2.2.2.1, q.2.2.2.2.2 && r.2.2.2.2.2)

/-- Componentwise disjunction of two patterns. -/
def orPat (q r : Pat) : Pat :=
  (q.1 || r.1, q.2.1 || r.2.1, q.2.2.1 || r.2.2.1, q.2.2.2.1 || r.2.2.2.1,
    q.2.2.2.2.1 || r.2.2.2.2.1, q.2.2.2.2.2 || r.2.2.2.2.2)

/-- The bits that every pattern of the list has set. -/
def andPats : List Pat → Pat
  | [] => (true, true, true, true, true, true)
  | q :: qs => andPat q (andPats qs)

/-- The bits that some pattern of the list has set. -/
def orPats : List Pat → Pat
  | [] => (false, false, false, false, false, false)
  | q :: qs => orPat q (orPats qs)

/-- A bit of the conjunction is a bit of every member.  The projection is an
argument, so the six components need no separate lemma. -/
theorem andPats_proj {ps : List Pat} {q : Pat} (hq : q ∈ ps) (f : Pat → Bool)
    (hf : ∀ x y : Pat, f (andPat x y) = (f x && f y)) (h : f (andPats ps) = true) :
    f q = true := by
  induction ps with
  | nil => exact absurd hq (by simp)
  | cons r rs ih =>
    rw [andPats, hf, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact h.1
    · exact ih hq' h.2

/-- A bit of a member is a bit of the disjunction. -/
theorem orPats_proj {ps : List Pat} {q : Pat} (hq : q ∈ ps) (f : Pat → Bool)
    (hf : ∀ x y : Pat, f (orPat x y) = (f x || f y)) (h : f q = true) :
    f (orPats ps) = true := by
  induction ps with
  | nil => exact absurd hq (by simp)
  | cons r rs ih =>
    rw [orPats, hf, Bool.or_eq_true]
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact Or.inl h
    · exact Or.inr (ih hq')

/-- The mask of the bits common to all the patterns is below every mask whose
own pattern is one of them. -/
theorem below_selMask_and {w : Mask} {B : Block} {ps : List Pat}
    (hq : patAt w B ∈ ps) : Below (selMask B (andPats ps)) w := by
  intro i hi
  rcases of_selBit (bitAt_selMask hi) with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ |
    ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · exact andPats_proj hq (fun z => z.1) (fun _ _ => rfl) hb
  · exact andPats_proj hq (fun z => z.2.1) (fun _ _ => rfl) hb
  · exact andPats_proj hq (fun z => z.2.2.1) (fun _ _ => rfl) hb
  · exact andPats_proj hq (fun z => z.2.2.2.1) (fun _ _ => rfl) hb
  · exact andPats_proj hq (fun z => z.2.2.2.2.1) (fun _ _ => rfl) hb
  · exact andPats_proj hq (fun z => z.2.2.2.2.2) (fun _ _ => rfl) hb

/-- One component of the previous lemma's companion, with the projection as an
argument. -/
theorem bit_false_of_orPats {w : Mask} {B : Block} {ps : List Pat}
    (hq : patAt w B ∈ ps) (f : Pat → Bool)
    (hf : ∀ x y : Pat, f (orPat x y) = (f x || f y))
    (hn : ∀ x : Pat, f (negPat x) = !(f x))
    (hb : f (negPat (orPats ps)) = true) {j : ℕ} (hj : f (patAt w B) = bitAt w j) :
    bitAt w j = false := by
  rw [hn] at hb
  cases hw : bitAt w j with
  | false => rfl
  | true =>
    rw [← hj] at hw
    rw [orPats_proj hq f hf hw] at hb
    simp at hb

/-- The mask of the bits no pattern has set is apart from every mask whose own
pattern is one of them. -/
theorem apart_selMask_or {w : Mask} {B : Block} {ps : List Pat}
    (hq : patAt w B ∈ ps) : Apart (selMask B (negPat (orPats ps))) w := by
  intro i hi
  rcases of_selBit (bitAt_selMask hi) with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ |
    ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · exact bit_false_of_orPats hq (fun z => z.1) (fun _ _ => rfl) (fun _ => rfl) hb rfl
  · exact bit_false_of_orPats hq (fun z => z.2.1) (fun _ _ => rfl) (fun _ => rfl) hb rfl
  · exact bit_false_of_orPats hq (fun z => z.2.2.1) (fun _ _ => rfl) (fun _ => rfl) hb rfl
  · exact bit_false_of_orPats hq (fun z => z.2.2.2.1) (fun _ _ => rfl) (fun _ => rfl) hb rfl
  · exact bit_false_of_orPats hq (fun z => z.2.2.2.2.1) (fun _ _ => rfl) (fun _ => rfl) hb rfl
  · exact bit_false_of_orPats hq (fun z => z.2.2.2.2.2) (fun _ _ => rfl) (fun _ => rfl) hb rfl

/-- All forty-five blocks of the node test are in `nodeRules`; the existing
`ruleAt_mem` only covers the fifteen four-point blocks the branching uses. -/
theorem ruleAt_mem_all45 :
    (List.range 45).all (fun k => nodeRules.contains (ruleAt k)) = true := by
  decide +kernel

theorem ruleAt_mem45 {k : ℕ} (hk : k < 45) : ruleAt k ∈ nodeRules :=
  List.mem_of_elem_eq_true
    (List.all_eq_true.mp ruleAt_mem_all45 k (List.mem_range.mpr hk))

/-- The allowed patterns of the `k`-th block still compatible with the node. -/
def compatList (k : ℕ) (pos neg : Mask) : List Pat :=
  (ruleAt k).2.filter
    (fun q => compatPat (patAt pos (ruleAt k).1) (patAt neg (ruleAt k).1) q)

/-- The cells the `k`-th block forces to be witnesses. -/
def tabOn (k : ℕ) (pos neg : Mask) : Mask :=
  if (compatList k pos neg).isEmpty then 0
  else selMask (ruleAt k).1 (andPats (compatList k pos neg))

/-- The cells the `k`-th block forces not to be witnesses. -/
def tabOff (k : ℕ) (pos neg : Mask) : Mask :=
  if (compatList k pos neg).isEmpty then 0
  else selMask (ruleAt k).1 (negPat (orPats (compatList k pos neg)))

/-- Propagation along a given list of blocks, each read at the node the earlier
ones have already strengthened. -/
def tabFold : List ℕ → Mask → Mask → Mask × Mask
  | [], pos, neg => (pos, neg)
  | k :: ks, pos, neg => tabFold ks (pos ||| tabOn k pos neg) (neg ||| tabOff k pos neg)

/-- A mask that extends the node is compatible with it on every block.  This is
the body of `okNode_of_below`, isolated. -/
theorem compatPat_of_below {pos neg w : Mask} (hb : Below pos w) (ha : Apart neg w)
    (B : Block) : compatPat (patAt pos B) (patAt neg B) (patAt w B) = true := by
  simp only [compatPat, patAt, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨compatBit_of (hb _) (ha _), compatBit_of (hb _) (ha _)⟩,
    compatBit_of (hb _) (ha _)⟩, compatBit_of (hb _) (ha _)⟩,
    compatBit_of (hb _) (ha _)⟩, compatBit_of (hb _) (ha _)⟩

theorem mem_compatList (hT : TablesSound) {p : Fin 6 → Pt} (hgp : GeneralPosition p)
    (hrep : EveryQuadrupleRepeats p) {w : Mask} (hw : Carries p w)
    {pos neg : Mask} (hb : Below pos w) (ha : Apart neg w) {k : ℕ} (hk : k < 45) :
    patAt w (ruleAt k).1 ∈ compatList k pos neg :=
  List.mem_filter.mpr ⟨hT p hgp hrep w hw _ (ruleAt_mem45 hk), compatPat_of_below hb ha _⟩

/-- **The propagation node is sound.**  Reading the forty-five tables in both
directions only strengthens the node. -/
theorem settles_tab (hT : TablesSound) : ∀ (ks : List ℕ), (∀ k ∈ ks, k < 45) →
    ∀ pos neg : Mask,
      Settles (tabFold ks pos neg).1 (tabFold ks pos neg).2 → Settles pos neg := by
  intro ks
  induction ks with
  | nil => intro _ pos neg h; exact h
  | cons k ks ih =>
    intro hk pos neg h
    simp only [tabFold] at h
    have hrec : Settles (pos ||| tabOn k pos neg) (neg ||| tabOff k pos neg) :=
      ih (fun x hx => hk x (List.mem_cons_of_mem _ hx)) _ _ h
    intro p hgp hrep w hlt hw hb ha
    have hin := mem_compatList hT hgp hrep hw hb ha (hk k (List.mem_cons_self ..))
    have hbo : Below (tabOn k pos neg) w := by
      rw [tabOn]
      split_ifs with he
      · exact below_zero w
      · exact below_selMask_and hin
    have hao : Apart (tabOff k pos neg) w := by
      rw [tabOff]
      split_ifs with he
      · exact apart_zero w
      · exact apart_selMask_or hin
    exact hrec p hgp hrep w hlt hw (below_or hb hbo) (apart_or ha hao)
/-- Four points form an orthocentric system: the two pairs of opposite
differences `u - d, v - c` and `u - c, v - d` are orthogonal.  (The third
orthogonality `⟪u - v, c - d⟫ = 0` follows; see `dotd_third_of_orthocentric`.) -/
def Orthocentric (u v c d : Pt) : Prop := dotd u d v c = 0 ∧ dotd u c v d = 0
/-- The sum of two complementary witness forms. -/
theorem psi_add_psi_complementary (u v c d : Pt) :
    Psi u v c d + Psi c d u v = 2 * dotd u d v c * crossd u c v d := by
  simp only [Psi, qq, cross, dotd, crossd]
  ring

/-- The difference of two complementary witness forms. -/
theorem psi_sub_psi_complementary (u v c d : Pt) :
    Psi c d u v - Psi u v c d = -2 * dotd u c v d * crossd u d v c := by
  simp only [Psi, qq, cross, dotd, crossd]
  ring
/-- The third orthogonality of an orthocentric system. -/
theorem dotd_third_of_orthocentric (u v c d : Pt) (h : Orthocentric u v c d) :
    dotd u v c d = 0 := by
  obtain ⟨h1, h2⟩ := h
  simp only [dotd] at h1 h2 ⊢
  nlinarith [h1, h2]

/-- In an orthocentric system every one of the six cells is a witness. -/
theorem psi_eq_zero_of_orthocentric (u v c d : Pt) (h : Orthocentric u v c d) :
    Psi u v c d = 0 ∧ Psi c d u v = 0 ∧ Psi u c v d = 0 ∧ Psi v d u c = 0 ∧
      Psi u d v c = 0 ∧ Psi v c u d = 0 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : dotd u v c d = 0 := dotd_third_of_orthocentric u v c d ⟨h1, h2⟩
  -- the split `{u,v} | {c,d}`
  have e1 := psi_add_psi_complementary u v c d
  have e2 := psi_sub_psi_complementary u v c d
  rw [h1] at e1
  rw [h2] at e2
  -- the split `{u,c} | {v,d}`
  have f1 := psi_add_psi_complementary u c v d
  have f2 := psi_sub_psi_complementary u c v d
  have hf1 : dotd u d c v = 0 := by simp only [dotd] at h1 ⊢; linarith
  have hf2 : dotd u v c d = 0 := h3
  rw [hf1] at f1
  rw [hf2] at f2
  -- the split `{u,d} | {v,c}`
  have g1 := psi_add_psi_complementary u d v c
  have g2 := psi_sub_psi_complementary u d v c
  have hg1 : dotd u c d v = 0 := by simp only [dotd] at h2 ⊢; linarith
  have hg2 : dotd u v d c = 0 := by simp only [dotd] at h3 ⊢; linarith
  rw [hg1] at g1
  rw [hg2] at g2
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
/-- **Two complementary witnesses force a parallelogram or an orthocentric
system.**  The four points are assumed distinct in the four relevant pairs and
`u c d` is assumed not collinear. -/
theorem parallelogram_or_orthocentric (u v c d : Pt)
    (huc : u ≠ c) (hud : u ≠ d) (hvc : v ≠ c) (hvd : v ≠ d)
    (hucd : ¬ Collinear3 u c d)
    (h1 : Psi u v c d = 0) (h2 : Psi c d u v = 0) :
    (u.1 + v.1 = c.1 + d.1 ∧ u.2 + v.2 = c.2 + d.2) ∨ Orthocentric u v c d := by
  have e1 := psi_add_psi_complementary u v c d
  have e2 := psi_sub_psi_complementary u v c d
  rw [h1, h2] at e1 e2
  have p1 : dotd u d v c * crossd u c v d = 0 := by linarith
  have p2 : dotd u c v d * crossd u d v c = 0 := by linarith
  rcases mul_eq_zero.mp p1 with hA | hA
  · rcases mul_eq_zero.mp p2 with hB | hB
    · exact Or.inr ⟨hA, hB⟩
    · -- `⟪u - d, v - c⟫ = 0` and `(u - d) × (v - c) = 0`: `u = d` or `v = c`
      exfalso
      rcases mul_eq_zero.mp (sqdist_mul_sqdist_eq_zero_of u d v c hA hB) with h | h
      · exact hud (eq_of_sqdist_eq_zero h)
      · exact hvc (eq_of_sqdist_eq_zero h)
  · rcases mul_eq_zero.mp p2 with hB | hB
    · -- `⟪u - c, v - d⟫ = 0` and `(u - c) × (v - d) = 0`: `u = c` or `v = d`
      exfalso
      rcases mul_eq_zero.mp (sqdist_mul_sqdist_eq_zero_of u c v d hB hA) with h | h
      · exact huc (eq_of_sqdist_eq_zero h)
      · exact hvd (eq_of_sqdist_eq_zero h)
    · -- both cross terms vanish: `u - c` and `u - d` are parallel to `u + v - c - d`
      left
      simp only [crossd] at hA hB
      have hx : (u.1 + v.1 - c.1 - d.1) * (u.2 - c.2)
          - (u.2 + v.2 - c.2 - d.2) * (u.1 - c.1) = 0 := by
        linear_combination -hA
      have hy : (u.1 + v.1 - c.1 - d.1) * (u.2 - d.2)
          - (u.2 + v.2 - c.2 - d.2) * (u.1 - d.1) = 0 := by
        linear_combination -hB
      have key := sq_norm_mul_cross_eq_zero (u.1 + v.1 - c.1 - d.1) (u.2 + v.2 - c.2 - d.2)
        (u.1 - c.1) (u.2 - c.2) (u.1 - d.1) (u.2 - d.2) hx hy
      have hz : (u.1 + v.1 - c.1 - d.1) ^ 2 + (u.2 + v.2 - c.2 - d.2) ^ 2 = 0 := by
        rcases mul_eq_zero.mp key with h | h
        · exact h
        · exact absurd (show cross u c d = 0 by simp only [cross]; linear_combination h) hucd
      obtain ⟨hG, hH⟩ := eq_zero_of_sq_add_sq_eq_zero _ _ hz
      exact ⟨by linarith, by linarith⟩
/-- **The form used by the census**: if the four points are in general position
(distinct, no three collinear) and one cell of another split is *not* a witness,
then two complementary witnesses force `u + v = c + d`. -/
theorem midpoint_of_two_complementary_witnesses (u v c d : Pt)
    (huc : u ≠ c) (hud : u ≠ d) (hvc : v ≠ c) (hvd : v ≠ d)
    (hucd : ¬ Collinear3 u c d)
    (h1 : Psi u v c d = 0) (h2 : Psi c d u v = 0) (h3 : Psi u c v d ≠ 0) :
    u.1 + v.1 = c.1 + d.1 ∧ u.2 + v.2 = c.2 + d.2 := by
  rcases parallelogram_or_orthocentric u v c d huc hud hvc hvd hucd h1 h2 with h | h
  · exact h
  · exact absurd (psi_eq_zero_of_orthocentric u v c d h).2.2.1 h3


/-! ## Rule (C6): the parallelogram

Rule (C6) of the census is about a *four*-point vector in the relation space,
`e_a + e_b - e_c - e_d`, which says that the four points make a parallelogram
with diagonals `{a,b}` and `{c,d}`.  It enters the search in two ways, and both
are needed.

**(C6a)** The relation space of the node already contains the vector.  Then the
four points *are* a parallelogram, and if the complementary pair of witnesses of
another split of the same four points is placed as well, two of the points
coincide.  The computation is short: with `p_a + p_b = p_c + p_d` the difference
`p_a - p_d` equals `p_c - p_b`, so the inner product that a witness pair forces
to vanish becomes a squared length.

**(C6b)** The relation space does *not* contain the vector, but the node places
the complementary pair of one split and rules out a cell of another; then
`midpoint_of_two_complementary_witnesses` **produces** the equation, and several
such equations combined with the cell certificate leave a nonzero element of the
relation space supported on three points, which is again three points on a line.

The two forms are separate nodes because the contradictions are different: the
first ends in two equal points, the second in three collinear ones.
-/

/-- The six distinctness conditions of a four-point split, as one decidable
test. -/
def parIdx (a b c d : Fin 6) : Bool :=
  decide (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)

/-- A sum over the six points with only four nonzero terms. -/
theorem sum_four {g : Fin 6 → ℝ} {a b c d : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h0 : ∀ i : Fin 6, i ≠ a → i ≠ b → i ≠ c → i ≠ d → g i = 0) :
    ∑ i : Fin 6, g i = g a + g b + g c + g d := by
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      i ∉ ({a, b, c, d} : Finset (Fin 6)) → g i = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h0 i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b, c, d} : Finset (Fin 6))) hz,
    Finset.sum_insert (by simp [hab, hac, had]),
    Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]
  ring

/-- **A cell read as a witness form.**  The cell whose apexes are `{a,b}` and
whose edge is `{c,d}` is a witness exactly when `Psi p_c p_d p_a p_b` vanishes,
whatever order the four points are given in. -/
theorem cellPsi_cellNum {p : Fin 6 → Pt} {a b c d : Fin 6}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    cellPsi p (cellNum a b c d) = 0 ↔ Psi (p c) (p d) (p a) (p b) = 0 := by
  obtain ⟨-, he⟩ := cellNum_spec a b c d hab hcd hac had hbc hbd
  rw [cellPsi, he]
  exact psi_minmax_eq_zero p c d a b

/-! ### (C6a): the parallelogram is already in the relation space -/

/-- **The core of (C6a).**  A parallelogram on the split `{U,C} | {V,D}`
together with the complementary pair of witnesses of the split `{U,V} | {C,D}`
forces `C = V`.  Only the sum identity of two complementary witness forms is
used; no case split on the dichotomy is needed, because the hypothesis
`U + C = V + D` turns the inner product into a squared length and the cross
product into the collinearity of `U C D`. -/
theorem eq_of_par_comp {U V C D : Pt} (hUCD : ¬ Collinear3 U C D)
    (hx : U.1 + C.1 = V.1 + D.1) (hy : U.2 + C.2 = V.2 + D.2)
    (h1 : Psi U V C D = 0) (h2 : Psi C D U V = 0) : C = V := by
  have e1 := psi_add_psi_complementary U V C D
  rw [h1, h2] at e1
  have p1 : dotd U D V C * crossd U C V D = 0 := by linear_combination (-1/2 : ℝ) * e1
  have hd : dotd U D V C = sqdist V C := by
    simp only [dotd, sqdist]
    linear_combination (V.1 - C.1) * hx + (V.2 - C.2) * hy
  rw [hd] at p1
  rcases mul_eq_zero.mp p1 with h | h
  · exact (eq_of_sqdist_eq_zero h).symm
  · exfalso
    refine hUCD ?_
    simp only [crossd] at h
    simp only [Collinear3, cross]
    linear_combination (1/2 : ℝ) * h + ((U.1 - C.1)/2) * hy - ((U.2 - C.2)/2) * hx

/-- `ptCoef cert` is a nonzero multiple of the parallelogram vector of the split
`{a,b} | {c,d}`. -/
def relPar (a b c d : Fin 6) (cert : List (ℕ × ℤ)) : Bool :=
  decide (ptCoef cert a ≠ 0 ∧ ptCoef cert b = ptCoef cert a ∧
    ptCoef cert c = - ptCoef cert a ∧ ptCoef cert d = - ptCoef cert a ∧
    ∀ i : Fin 6, i = a ∨ i = b ∨ i = c ∨ i = d ∨ ptCoef cert i = 0)

/-- **The soundness of (C6a)**, as one statement to thread through the chain. -/
def ParSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w : Mask, Carries p w →
    ∀ pos : Mask, Below pos w →
      ∀ (a b c d : Fin 6) (cert : List (ℕ × ℤ)),
        parIdx a b c d = true → certSupp pos cert = true →
        relTriZero cert = true → relPar a b c d cert = true →
        bitAt pos (cellNum b d a c) = true → bitAt pos (cellNum a c b d) = true →
        False

/-- **(C6a) is sound.** -/
theorem par_sound : ParSound := by
  intro p hgp w hw pos hb a b c d cert hidx hs htz hpar k1 k2
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := of_decide_eq_true hidx
  obtain ⟨hm, hmb, hmc, hmd, hpout⟩ := of_decide_eq_true hpar
  obtain ⟨ctr, rad, hctr⟩ := exists_centers hgp
  have hsup : Supports p w := supports_of_carries hw
  have hcells : ∀ q ∈ cert, q.1 < 90 ∧ cellPsi p q.1 = 0 := by
    intro q hq
    have h := List.all_eq_true.mp hs q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, hsup q.1 h.1 (hb q.1 h.2)⟩
  obtain ⟨bal1, bal2⟩ := rel_balance hgp hctr cert hcells
  have htz' : ∀ t, t < 20 → triCoef cert t = 0 := fun t ht =>
    of_decide_eq_true htz ⟨t, ht⟩
  have z1 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).1 = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [htz' t (Finset.mem_range.mp ht)]; simp)
  have z2 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).2 = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [htz' t (Finset.mem_range.mp ht)]; simp)
  have hout' : ∀ i : Fin 6, i ≠ a → i ≠ b → i ≠ c → i ≠ d → ptCoef cert i = 0 := by
    intro i n1 n2 n3 n4
    rcases hpout i with h | h | h | h | h
    · exact absurd h n1
    · exact absurd h n2
    · exact absurd h n3
    · exact absurd h n4
    · exact h
  have s1 : ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).1
      = (ptCoef cert a : ℝ) * (p a).1 + (ptCoef cert b : ℝ) * (p b).1
        + (ptCoef cert c : ℝ) * (p c).1 + (ptCoef cert d : ℝ) * (p d).1 :=
    sum_four (g := fun i => (ptCoef cert i : ℝ) * (p i).1) hab hac had hbc hbd hcd
      (fun i n1 n2 n3 n4 => by rw [hout' i n1 n2 n3 n4]; simp)
  have s2 : ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).2
      = (ptCoef cert a : ℝ) * (p a).2 + (ptCoef cert b : ℝ) * (p b).2
        + (ptCoef cert c : ℝ) * (p c).2 + (ptCoef cert d : ℝ) * (p d).2 :=
    sum_four (g := fun i => (ptCoef cert i : ℝ) * (p i).2) hab hac had hbc hbd hcd
      (fun i n1 n2 n3 n4 => by rw [hout' i n1 n2 n3 n4]; simp)
  have hmR : ((ptCoef cert a : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have r1 : (ptCoef cert a : ℝ) * (p a).1 + (ptCoef cert b : ℝ) * (p b).1
      + (ptCoef cert c : ℝ) * (p c).1 + (ptCoef cert d : ℝ) * (p d).1 = 0 := by
    rw [← s1, ← bal1]; exact z1
  have r2 : (ptCoef cert a : ℝ) * (p a).2 + (ptCoef cert b : ℝ) * (p b).2
      + (ptCoef cert c : ℝ) * (p c).2 + (ptCoef cert d : ℝ) * (p d).2 = 0 := by
    rw [← s2, ← bal2]; exact z2
  rw [hmb, hmc, hmd] at r1 r2
  push_cast at r1 r2
  have hx : (p a).1 + (p b).1 = (p c).1 + (p d).1 := by
    have e : ((ptCoef cert a : ℤ) : ℝ)
        * (((p a).1 + (p b).1) - ((p c).1 + (p d).1)) = 0 := by
      linear_combination r1
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h hmR
    · linarith
  have hy : (p a).2 + (p b).2 = (p c).2 + (p d).2 := by
    have e : ((ptCoef cert a : ℤ) : ℝ)
        * (((p a).2 + (p b).2) - ((p c).2 + (p d).2)) = 0 := by
      linear_combination r2
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h hmR
    · linarith
  obtain ⟨hl1, -⟩ := cellNum_spec b d a c hbd hac hab.symm hbc had.symm hcd.symm
  obtain ⟨hl2, -⟩ := cellNum_spec a c b d hac hbd hab had hbc.symm hcd
  have w1 : Psi (p a) (p c) (p b) (p d) = 0 :=
    (cellPsi_cellNum hbd hac hab.symm hbc had.symm hcd.symm).mp (hsup _ hl1 (hb _ k1))
  have w2 : Psi (p b) (p d) (p a) (p c) = 0 :=
    (cellPsi_cellNum hac hbd hab had hbc.symm hcd).mp (hsup _ hl2 (hb _ k2))
  exact ne_of_gp hgp hbc (eq_of_par_comp (ncol_of_gp hgp hab had hbd) hx hy w1 w2)

/-- **(C6a).**  A relation certificate that is a parallelogram, together with the
complementary pair of another split, closes the node. -/
theorem refutes_par (hP : ParSound) {pos neg : Mask} {a b c d : Fin 6}
    {cert : List (ℕ × ℤ)} (hidx : parIdx a b c d = true)
    (hs : certSupp pos cert = true) (htz : relTriZero cert = true)
    (hpar : relPar a b c d cert = true)
    (k1 : bitAt pos (cellNum b d a c) = true)
    (k2 : bitAt pos (cellNum a c b d) = true) : Refutes pos neg :=
  fun p hgp _ w _ hw hb _ =>
    hP p hgp w hw pos hb a b c d cert hidx hs htz hpar k1 k2

/-! ### (C6b): the parallelogram is produced by the node -/

/-- A declared parallelogram: the four points of the equation
`p_a + p_b = p_c + p_d`, together with the integer coefficient it enters the
combination with. -/
abbrev ParTerm := Fin 6 × Fin 6 × Fin 6 × Fin 6 × ℤ

/-- The point coefficients of one declared parallelogram, written so that the
four Kronecker deltas peel off one at a time. -/
def pt1 (x : ParTerm) (i : Fin 6) : ℤ :=
  x.2.2.2.2 * (if x.1 = i then 1 else 0)
    + (x.2.2.2.2 * (if x.2.1 = i then 1 else 0)
      + (-x.2.2.2.2 * (if x.2.2.1 = i then 1 else 0)
        + (-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0)))

/-- The point coefficients contributed by a list of declared parallelograms. -/
def parCoef : List ParTerm → Fin 6 → ℤ
  | [], _ => 0
  | x :: xs, i => pt1 x i + parCoef xs i

/-- What the declared parallelograms say about a function on the six points. -/
def parSum : List ParTerm → (Fin 6 → ℝ) → ℝ
  | [], _ => 0
  | x :: xs, g =>
      (x.2.2.2.2 : ℝ) * (g x.1 + g x.2.1 - g x.2.2.1 - g x.2.2.2.1) + parSum xs g

theorem sum_pt1 (g : Fin 6 → ℝ) (x : ParTerm) :
    ∑ i : Fin 6, (pt1 x i : ℝ) * g i
      = (x.2.2.2.2 : ℝ) * (g x.1 + g x.2.1 - g x.2.2.1 - g x.2.2.2.1) := by
  have s1 : ∑ i : Fin 6, (pt1 x i : ℝ) * g i
      = ((x.2.2.2.2 : ℤ) : ℝ) * g x.1
        + ∑ i : Fin 6, ((x.2.2.2.2 * (if x.2.1 = i then 1 else 0)
            + (-x.2.2.2.2 * (if x.2.2.1 = i then 1 else 0)
              + (-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0)) : ℤ) : ℝ) * g i :=
    sum_peel (Finset.mem_univ _) (fun _ => rfl)
  have s2 : ∑ i : Fin 6, ((x.2.2.2.2 * (if x.2.1 = i then 1 else 0)
        + (-x.2.2.2.2 * (if x.2.2.1 = i then 1 else 0)
          + (-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0)) : ℤ) : ℝ) * g i
      = ((x.2.2.2.2 : ℤ) : ℝ) * g x.2.1
        + ∑ i : Fin 6, ((-x.2.2.2.2 * (if x.2.2.1 = i then 1 else 0)
            + (-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0) : ℤ) : ℝ) * g i :=
    sum_peel (Finset.mem_univ _) (fun _ => rfl)
  have s3 : ∑ i : Fin 6, ((-x.2.2.2.2 * (if x.2.2.1 = i then 1 else 0)
        + (-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0) : ℤ) : ℝ) * g i
      = ((-x.2.2.2.2 : ℤ) : ℝ) * g x.2.2.1
        + ∑ i : Fin 6,
            ((-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0 : ℤ) : ℝ) * g i :=
    sum_peel (Finset.mem_univ _) (fun _ => rfl)
  have s4 : ∑ i : Fin 6,
        ((-x.2.2.2.2 * (if x.2.2.2.1 = i then 1 else 0) + 0 : ℤ) : ℝ) * g i
      = ((-x.2.2.2.2 : ℤ) : ℝ) * g x.2.2.2.1 + ∑ i : Fin 6, ((0 : ℤ) : ℝ) * g i :=
    sum_peel (Finset.mem_univ _) (fun _ => rfl)
  have s5 : ∑ i : Fin 6, ((0 : ℤ) : ℝ) * g i = 0 := by simp
  rw [s1, s2, s3, s4, s5]
  push_cast
  ring

theorem sum_parCoef (g : Fin 6 → ℝ) : ∀ pars : List ParTerm,
    ∑ i : Fin 6, (parCoef pars i : ℝ) * g i = parSum pars g := by
  intro pars
  induction pars with
  | nil => simp [parCoef, parSum]
  | cons x xs ih =>
    have hsplit : ∀ i : Fin 6, ((parCoef (x :: xs) i : ℤ) : ℝ) * g i
        = ((pt1 x i : ℤ) : ℝ) * g i + ((parCoef xs i : ℤ) : ℝ) * g i := by
      intro i; simp only [parCoef]; push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, ih,
      sum_pt1 g x]
    simp only [parSum]

/-- Each declared parallelogram is certified by the node: the complementary pair
of its own split is placed, and one cell of another split is ruled out. -/
def parsOK (pos neg : Mask) (pars : List ParTerm) : Bool :=
  pars.all fun x =>
    parIdx x.1 x.2.1 x.2.2.1 x.2.2.2.1 &&
      bitAt pos (cellNum x.2.2.1 x.2.2.2.1 x.1 x.2.1) &&
      bitAt pos (cellNum x.1 x.2.1 x.2.2.1 x.2.2.2.1) &&
      bitAt neg (cellNum x.2.1 x.2.2.2.1 x.1 x.2.2.1)

/-- **One declared parallelogram holds.**  This is
`midpoint_of_two_complementary_witnesses` read off the node. -/
theorem midpoint_of_node {p : Fin 6 → Pt} (hgp : GeneralPosition p) {w : Mask}
    (hw : Carries p w) {pos neg : Mask} (hb : Below pos w) (ha : Apart neg w)
    {a b c d : Fin 6} (hidx : parIdx a b c d = true)
    (k1 : bitAt pos (cellNum c d a b) = true) (k2 : bitAt pos (cellNum a b c d) = true)
    (k3 : bitAt neg (cellNum b d a c) = true) :
    (p a).1 + (p b).1 = (p c).1 + (p d).1 ∧
      (p a).2 + (p b).2 = (p c).2 + (p d).2 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := of_decide_eq_true hidx
  have hsup : Supports p w := supports_of_carries hw
  obtain ⟨hl1, -⟩ := cellNum_spec c d a b hcd hab hac.symm hbc.symm had.symm hbd.symm
  obtain ⟨hl2, -⟩ := cellNum_spec a b c d hab hcd hac had hbc hbd
  obtain ⟨hl3, -⟩ := cellNum_spec b d a c hbd hac hab.symm hbc had.symm hcd.symm
  have w1 : Psi (p a) (p b) (p c) (p d) = 0 :=
    (cellPsi_cellNum hcd hab hac.symm hbc.symm had.symm hbd.symm).mp
      (hsup _ hl1 (hb _ k1))
  have w2 : Psi (p c) (p d) (p a) (p b) = 0 :=
    (cellPsi_cellNum hab hcd hac had hbc hbd).mp (hsup _ hl2 (hb _ k2))
  have w3 : Psi (p a) (p c) (p b) (p d) ≠ 0 := by
    intro hz
    have hb1 : bitAt w (cellNum b d a c) = true :=
      (hw _ hl3).1
        ((cellPsi_cellNum hbd hac hab.symm hbc had.symm hcd.symm).mpr hz)
    rw [ha _ k3] at hb1
    exact absurd hb1 (by simp)
  exact midpoint_of_two_complementary_witnesses (p a) (p b) (p c) (p d)
    (ne_of_gp hgp hac) (ne_of_gp hgp had) (ne_of_gp hgp hbc) (ne_of_gp hgp hbd)
    (ncol_of_gp hgp hac had hcd) w1 w2 w3

theorem parSum_eq_zero {p : Fin 6 → Pt} (hgp : GeneralPosition p) {w : Mask}
    (hw : Carries p w) {pos neg : Mask} (hb : Below pos w) (ha : Apart neg w) :
    ∀ pars : List ParTerm, parsOK pos neg pars = true →
      parSum pars (fun i => (p i).1) = 0 ∧ parSum pars (fun i => (p i).2) = 0 := by
  intro pars
  induction pars with
  | nil => intro _; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro h
    have hx := List.all_eq_true.mp h x (List.mem_cons_self ..)
    have hxs : parsOK pos neg xs = true :=
      List.all_eq_true.mpr
        (fun y hy => List.all_eq_true.mp h y (List.mem_cons_of_mem _ hy))
    simp only [Bool.and_eq_true] at hx
    obtain ⟨⟨⟨hidx, k1⟩, k2⟩, k3⟩ := hx
    obtain ⟨e1, e2⟩ := midpoint_of_node hgp hw hb ha hidx k1 k2 k3
    obtain ⟨f1, f2⟩ := ih hxs
    refine ⟨?_, ?_⟩
    · simp only [parSum]
      linear_combination (x.2.2.2.2 : ℝ) * e1 + f1
    · simp only [parSum]
      linear_combination (x.2.2.2.2 : ℝ) * e2 + f2

/-- The point coefficients of the cell certificate together with the declared
parallelograms. -/
def ptCoefX (cert : List (ℕ × ℤ)) (pars : List ParTerm) (i : Fin 6) : ℤ :=
  ptCoef cert i + parCoef pars i

/-- The combined point coefficients live on the three points `x`, `y`, `z`. -/
def parOut (x y z : Fin 6) (cert : List (ℕ × ℤ)) (pars : List ParTerm) : Bool :=
  decide (∀ i : Fin 6, i = x ∨ i = y ∨ i = z ∨ ptCoefX cert pars i = 0)

/-- The three combined coefficients add up to zero and do not all vanish. -/
def parTrip (x y z : Fin 6) (cert : List (ℕ × ℤ)) (pars : List ParTerm) : Bool :=
  decide (ptCoefX cert pars x + ptCoefX cert pars y + ptCoefX cert pars z = 0 ∧
    (ptCoefX cert pars x ≠ 0 ∨ ptCoefX cert pars y ≠ 0 ∨ ptCoefX cert pars z ≠ 0))

/-- **The soundness of (C6b)**, as one statement to thread through the chain. -/
def ParRelSound : Prop :=
  ∀ p : Fin 6 → Pt, GeneralPosition p → ∀ w : Mask, Carries p w →
    ∀ pos neg : Mask, Below pos w → Apart neg w →
      ∀ (x y z : Fin 6) (cert : List (ℕ × ℤ)) (pars : List ParTerm),
        x ≠ y → x ≠ z → y ≠ z →
        certSupp pos cert = true → relTriZero cert = true →
        parsOK pos neg pars = true → parOut x y z cert pars = true →
        parTrip x y z cert pars = true → False

/-- **(C6b) is sound.**  The same three points on a line as in (C4), but the
relation space is the cell certificate *plus* the declared parallelograms. -/
theorem parrel_sound : ParRelSound := by
  intro p hgp w hw pos neg hb ha x y z cert pars hxy hxz hyz hs htz hpok hout htrip
  obtain ⟨ctr, rad, hctr⟩ := exists_centers hgp
  have hsup : Supports p w := supports_of_carries hw
  have hcells : ∀ q ∈ cert, q.1 < 90 ∧ cellPsi p q.1 = 0 := by
    intro q hq
    have h := List.all_eq_true.mp hs q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, hsup q.1 h.1 (hb q.1 h.2)⟩
  obtain ⟨bal1, bal2⟩ := rel_balance hgp hctr cert hcells
  have htz' : ∀ t, t < 20 → triCoef cert t = 0 := fun t ht =>
    of_decide_eq_true htz ⟨t, ht⟩
  have z1 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).1 = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [htz' t (Finset.mem_range.mp ht)]; simp)
  have z2 : ∑ t ∈ Finset.range 20, (triCoef cert t : ℝ) * (ctr t).2 = 0 :=
    Finset.sum_eq_zero (fun t ht => by rw [htz' t (Finset.mem_range.mp ht)]; simp)
  obtain ⟨q1, q2⟩ := parSum_eq_zero hgp hw hb ha pars hpok
  have split1 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).1
      = ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).1
        + ∑ i : Fin 6, (parCoef pars i : ℝ) * (p i).1 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [ptCoefX]; push_cast; ring)
  have split2 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).2
      = ∑ i : Fin 6, (ptCoef cert i : ℝ) * (p i).2
        + ∑ i : Fin 6, (parCoef pars i : ℝ) * (p i).2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [ptCoefX]; push_cast; ring)
  have tot1 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).1 = 0 := by
    rw [split1, ← bal1, z1, sum_parCoef (fun i => (p i).1) pars, q1]
    ring
  have tot2 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).2 = 0 := by
    rw [split2, ← bal2, z2, sum_parCoef (fun i => (p i).2) pars, q2]
    ring
  have hout' : ∀ i : Fin 6, i ≠ x → i ≠ y → i ≠ z → ptCoefX cert pars i = 0 := by
    intro i n1 n2 n3
    rcases of_decide_eq_true hout i with h | h | h | h
    · exact absurd h n1
    · exact absurd h n2
    · exact absurd h n3
    · exact h
  have s1 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).1
      = (ptCoefX cert pars x : ℝ) * (p x).1 + (ptCoefX cert pars y : ℝ) * (p y).1
        + (ptCoefX cert pars z : ℝ) * (p z).1 :=
    sum_three (g := fun i => (ptCoefX cert pars i : ℝ) * (p i).1) hxy hxz hyz
      (fun i n1 n2 n3 => by rw [hout' i n1 n2 n3]; simp)
  have s2 : ∑ i : Fin 6, (ptCoefX cert pars i : ℝ) * (p i).2
      = (ptCoefX cert pars x : ℝ) * (p x).2 + (ptCoefX cert pars y : ℝ) * (p y).2
        + (ptCoefX cert pars z : ℝ) * (p z).2 :=
    sum_three (g := fun i => (ptCoefX cert pars i : ℝ) * (p i).2) hxy hxz hyz
      (fun i n1 n2 n3 => by rw [hout' i n1 n2 n3]; simp)
  obtain ⟨hsumZ, hnzZ⟩ := of_decide_eq_true htrip
  have hsum : (ptCoefX cert pars x : ℝ) + (ptCoefX cert pars y : ℝ)
      + (ptCoefX cert pars z : ℝ) = 0 := by exact_mod_cast hsumZ
  have r1 : (ptCoefX cert pars x : ℝ) * (p x).1 + (ptCoefX cert pars y : ℝ) * (p y).1
      + (ptCoefX cert pars z : ℝ) * (p z).1 = 0 := by rw [← s1]; exact tot1
  have r2 : (ptCoefX cert pars x : ℝ) * (p x).2 + (ptCoefX cert pars y : ℝ) * (p y).2
      + (ptCoefX cert pars z : ℝ) * (p z).2 = 0 := by rw [← s2]; exact tot2
  have hcol : cross (p x) (p y) (p z) = 0 := by
    have kb : (ptCoefX cert pars y : ℝ) * cross (p x) (p y) (p z) = 0 :=
      coef_mul_cross hsum r1 r2
    have ka : (ptCoefX cert pars x : ℝ) * cross (p y) (p x) (p z) = 0 :=
      coef_mul_cross (va := (ptCoefX cert pars y : ℝ))
        (vc := (ptCoefX cert pars z : ℝ)) (by linarith) (by linarith) (by linarith)
    have kc : (ptCoefX cert pars z : ℝ) * cross (p x) (p z) (p y) = 0 :=
      coef_mul_cross (va := (ptCoefX cert pars x : ℝ))
        (vc := (ptCoefX cert pars y : ℝ)) (by linarith) (by linarith) (by linarith)
    rw [cross_swap₁₂] at ka
    rw [cross_swap₂₃] at kc
    rcases hnzZ with h | h | h
    · have hn : (ptCoefX cert pars x : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp ka with h' | h'
      · exact absurd h' hn
      · linarith
    · have hn : (ptCoefX cert pars y : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp kb with h' | h'
      · exact absurd h' hn
      · exact h'
    · have hn : (ptCoefX cert pars z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
      rcases mul_eq_zero.mp kc with h' | h'
      · exact absurd h' hn
      · linarith
  exact ncol_of_gp hgp hxy hxz hyz hcol

/-- **(C6b).**  A relation certificate extended by declared parallelograms
closes the node. -/
theorem refutes_parRel (hQ : ParRelSound) {pos neg : Mask} {x y z : Fin 6}
    {cert : List (ℕ × ℤ)} {pars : List ParTerm}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : certSupp pos cert = true) (htz : relTriZero cert = true)
    (hpok : parsOK pos neg pars = true) (hout : parOut x y z cert pars = true)
    (htrip : parTrip x y z cert pars = true) : Refutes pos neg :=
  fun p hgp _ w _ hw hb hap =>
    hQ p hgp w hw pos neg hb hap x y z cert pars hxy hxz hyz hs htz hpok hout htrip


/-! ## The symmetry of the search

Relabelling the six points carries a node to another node.  The census
statement is invariant under the relabelling, so a node may be traded for its
image, and in particular for the least element of its orbit.  This is the one
thing that makes the search finite: without it the queue of nodes handed on
grows without bound.

Three ingredients: the two hypotheses on a configuration survive relabelling,
the two node conditions survive it, and the relabellings compose.
-/

/-- The relabelling of the four faces induced by swapping the first two
points. -/
def sw0 : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3

/-- … the second and third. -/
def sw1 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3

/-- … the third and fourth. -/
def sw2 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

theorem sw0_inj : Function.Injective sw0 := by decide

theorem sw1_inj : Function.Injective sw1 := by decide

theorem sw2_inj : Function.Injective sw2 := by decide

theorem face_sw0 {a b c d : Pt} {r : ℝ} :
    ∀ i : Fin 4, face b a c d i r → face a b c d (sw0 i) r
  | 0, h => h
  | 1, h => h
  | 2, h => (circumRadiusSq_perm h).2.1
  | 3, h => (circumRadiusSq_perm h).2.1

theorem face_sw1 {a b c d : Pt} {r : ℝ} :
    ∀ i : Fin 4, face a c b d i r → face a b c d (sw1 i) r
  | 0, h => (circumRadiusSq_perm h).2.1
  | 1, h => h
  | 2, h => h
  | 3, h => (circumRadiusSq_perm h).1

theorem face_sw2 {a b c d : Pt} {r : ℝ} :
    ∀ i : Fin 4, face a b d c i r → face a b c d (sw2 i) r
  | 0, h => (circumRadiusSq_perm h).1
  | 1, h => (circumRadiusSq_perm h).1
  | 2, h => h
  | 3, h => h

/-- The four faces do not see the order of the four points: swapping the first
two. -/
theorem fourDistinct_swap0 {a b c d : Pt} (h : FourDistinct a b c d) :
    FourDistinct b a c d :=
  fun i j hij r s hi hj =>
    h (sw0 i) (sw0 j) (fun e => hij (sw0_inj e)) r s (face_sw0 i hi) (face_sw0 j hj)

/-- … the second and third. -/
theorem fourDistinct_swap1 {a b c d : Pt} (h : FourDistinct a b c d) :
    FourDistinct a c b d :=
  fun i j hij r s hi hj =>
    h (sw1 i) (sw1 j) (fun e => hij (sw1_inj e)) r s (face_sw1 i hi) (face_sw1 j hj)

/-- … the third and fourth. -/
theorem fourDistinct_swap2 {a b c d : Pt} (h : FourDistinct a b c d) :
    FourDistinct a b d c :=
  fun i j hij r s hi hj =>
    h (sw2 i) (sw2 j) (fun e => hij (sw2_inj e)) r s (face_sw2 i hi) (face_sw2 j hj)

/-- Four points of `p` that are pairwise different repeat a
circumradius, whatever order they are named in. -/
theorem repeats_of_ne {N : ℕ} {p : Fin N → Pt} (hrep : EveryQuadrupleRepeats p) {x y z w : Fin N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hzw : z ≠ w) : ¬ FourDistinct (p x) (p y) (p z) (p w) := by
  intro hc
  have base := hrep
  have vxy : (x : Fin N).val ≠ (y : Fin N).val := fun h => hxy (Fin.ext h)
  have vxz : (x : Fin N).val ≠ (z : Fin N).val := fun h => hxz (Fin.ext h)
  have vxw : (x : Fin N).val ≠ (w : Fin N).val := fun h => hxw (Fin.ext h)
  have vyz : (y : Fin N).val ≠ (z : Fin N).val := fun h => hyz (Fin.ext h)
  have vyw : (y : Fin N).val ≠ (w : Fin N).val := fun h => hyw (Fin.ext h)
  have vzw : (z : Fin N).val ≠ (w : Fin N).val := fun h => hzw (Fin.ext h)
  have s1 : (x.val < y.val ∧ x.val < z.val ∧ x.val < w.val) ∨ (y.val < x.val ∧ y.val < z.val ∧ y.val < w.val) ∨ (z.val < x.val ∧ z.val < y.val ∧ z.val < w.val) ∨ (w.val < x.val ∧ w.val < y.val ∧ w.val < z.val) := by omega
  rcases s1 with ⟨h01, h02, h03⟩ | ⟨h10, h12, h13⟩ | ⟨h20, h21, h23⟩ | ⟨h30, h31, h32⟩
  · 
    have s2 : (y.val < z.val ∧ y.val < w.val) ∨ (z.val < y.val ∧ z.val < w.val) ∨ (w.val < y.val ∧ w.val < z.val) := by omega
    rcases s2 with ⟨h12, h13⟩ | ⟨h21, h23⟩ | ⟨h31, h32⟩
    · 
      have s3 : (z.val < w.val) ∨ (w.val < z.val) := by omega
      rcases s3 with h23 | h32
      · 
        exact base x y z w (show x < y from h01) (show y < z from h12) (show z < w from h23) (hc)
      · 
        exact base x y w z (show x < y from h01) (show y < w from h13) (show w < z from h32) (fourDistinct_swap2 (hc))
    · 
      have s3 : (y.val < w.val) ∨ (w.val < y.val) := by omega
      rcases s3 with h13 | h31
      · 
        exact base x z y w (show x < z from h02) (show z < y from h21) (show y < w from h13) (fourDistinct_swap1 (hc))
      · 
        exact base x z w y (show x < z from h02) (show z < w from h23) (show w < y from h31) (fourDistinct_swap2 (fourDistinct_swap1 (hc)))
    · 
      have s3 : (y.val < z.val) ∨ (z.val < y.val) := by omega
      rcases s3 with h12 | h21
      · 
        exact base x w y z (show x < w from h03) (show w < y from h31) (show y < z from h12) (fourDistinct_swap1 (fourDistinct_swap2 (hc)))
      · 
        exact base x w z y (show x < w from h03) (show w < z from h32) (show z < y from h21) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap2 (hc))))
  · 
    have s2 : (x.val < z.val ∧ x.val < w.val) ∨ (z.val < x.val ∧ z.val < w.val) ∨ (w.val < x.val ∧ w.val < z.val) := by omega
    rcases s2 with ⟨h02, h03⟩ | ⟨h20, h23⟩ | ⟨h30, h32⟩
    · 
      have s3 : (z.val < w.val) ∨ (w.val < z.val) := by omega
      rcases s3 with h23 | h32
      · 
        exact base y x z w (show y < x from h10) (show x < z from h02) (show z < w from h23) (fourDistinct_swap0 (hc))
      · 
        exact base y x w z (show y < x from h10) (show x < w from h03) (show w < z from h32) (fourDistinct_swap2 (fourDistinct_swap0 (hc)))
    · 
      have s3 : (x.val < w.val) ∨ (w.val < x.val) := by omega
      rcases s3 with h03 | h30
      · 
        exact base y z x w (show y < z from h12) (show z < x from h20) (show x < w from h03) (fourDistinct_swap1 (fourDistinct_swap0 (hc)))
      · 
        exact base y z w x (show y < z from h12) (show z < w from h23) (show w < x from h30) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap0 (hc))))
    · 
      have s3 : (x.val < z.val) ∨ (z.val < x.val) := by omega
      rcases s3 with h02 | h20
      · 
        exact base y w x z (show y < w from h13) (show w < x from h30) (show x < z from h02) (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (hc))))
      · 
        exact base y w z x (show y < w from h13) (show w < z from h32) (show z < x from h20) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (hc)))))
  · 
    have s2 : (x.val < y.val ∧ x.val < w.val) ∨ (y.val < x.val ∧ y.val < w.val) ∨ (w.val < x.val ∧ w.val < y.val) := by omega
    rcases s2 with ⟨h01, h03⟩ | ⟨h10, h13⟩ | ⟨h30, h31⟩
    · 
      have s3 : (y.val < w.val) ∨ (w.val < y.val) := by omega
      rcases s3 with h13 | h31
      · 
        exact base z x y w (show z < x from h20) (show x < y from h01) (show y < w from h13) (fourDistinct_swap0 (fourDistinct_swap1 (hc)))
      · 
        exact base z x w y (show z < x from h20) (show x < w from h03) (show w < y from h31) (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (hc))))
    · 
      have s3 : (x.val < w.val) ∨ (w.val < x.val) := by omega
      rcases s3 with h03 | h30
      · 
        exact base z y x w (show z < y from h21) (show y < x from h10) (show x < w from h03) (fourDistinct_swap1 (fourDistinct_swap0 (fourDistinct_swap1 (hc))))
      · 
        exact base z y w x (show z < y from h21) (show y < w from h13) (show w < x from h30) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap0 (fourDistinct_swap1 (hc)))))
    · 
      have s3 : (x.val < y.val) ∨ (y.val < x.val) := by omega
      rcases s3 with h01 | h10
      · 
        exact base z w x y (show z < w from h23) (show w < x from h30) (show x < y from h01) (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (hc)))))
      · 
        exact base z w y x (show z < w from h23) (show w < y from h31) (show y < x from h10) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (hc))))))
  · 
    have s2 : (x.val < y.val ∧ x.val < z.val) ∨ (y.val < x.val ∧ y.val < z.val) ∨ (z.val < x.val ∧ z.val < y.val) := by omega
    rcases s2 with ⟨h01, h02⟩ | ⟨h10, h12⟩ | ⟨h20, h21⟩
    · 
      have s3 : (y.val < z.val) ∨ (z.val < y.val) := by omega
      rcases s3 with h12 | h21
      · 
        exact base w x y z (show w < x from h30) (show x < y from h01) (show y < z from h12) (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc))))
      · 
        exact base w x z y (show w < x from h30) (show x < z from h02) (show z < y from h21) (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc)))))
    · 
      have s3 : (x.val < z.val) ∨ (z.val < x.val) := by omega
      rcases s3 with h02 | h20
      · 
        exact base w y x z (show w < y from h31) (show y < x from h10) (show x < z from h02) (fourDistinct_swap1 (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc)))))
      · 
        exact base w y z x (show w < y from h31) (show y < z from h12) (show z < x from h20) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc))))))
    · 
      have s3 : (x.val < y.val) ∨ (y.val < x.val) := by omega
      rcases s3 with h01 | h10
      · 
        exact base w z x y (show w < z from h32) (show z < x from h20) (show x < y from h01) (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc))))))
      · 
        exact base w z y x (show w < z from h32) (show z < y from h21) (show y < x from h10) (fourDistinct_swap2 (fourDistinct_swap1 (fourDistinct_swap2 (fourDistinct_swap0 (fourDistinct_swap1 (fourDistinct_swap2 (hc)))))))

/-- A relabelled configuration is again in general position. -/
theorem gp_comp {p : Fin 6 → Pt} (σ : Equiv.Perm (Fin 6)) (hgp : GeneralPosition p) :
    GeneralPosition (fun i => p (σ i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact ne_of_gp hgp (σ.injective.ne hij.ne)
  · intro i j k hij hjk
    exact ncol_of_gp hgp (σ.injective.ne hij.ne) (σ.injective.ne (hij.trans hjk).ne)
      (σ.injective.ne hjk.ne)
  · intro i j k l hij hjk hkl
    exact ncyc_of_gp hgp (σ.injective.ne hij.ne) (σ.injective.ne (hij.trans hjk).ne)
      (σ.injective.ne ((hij.trans hjk).trans hkl).ne) (σ.injective.ne hjk.ne)
      (σ.injective.ne (hjk.trans hkl).ne) (σ.injective.ne hkl.ne)

/-- A relabelled configuration again repeats a circumradius on every four of
its points. -/
theorem repeats_comp {p : Fin 6 → Pt} (σ : Equiv.Perm (Fin 6))
    (hrep : EveryQuadrupleRepeats p) : EveryQuadrupleRepeats (fun i => p (σ i)) := by
  intro i j k l hij hjk hkl
  exact repeats_of_ne hrep (σ.injective.ne hij.ne) (σ.injective.ne (hij.trans hjk).ne)
    (σ.injective.ne ((hij.trans hjk).trans hkl).ne) (σ.injective.ne hjk.ne)
    (σ.injective.ne (hjk.trans hkl).ne) (σ.injective.ne hkl.ne)

/-- The index of a cell does not see the order inside the apex pair or inside
the edge, even after a relabelling. -/
theorem cellNum_map_minmax (σ : Equiv.Perm (Fin 6)) (x y z t : Fin 6) :
    cellNum (σ (min x y)) (σ (max x y)) (σ (min z t)) (σ (max z t))
      = cellNum (σ x) (σ y) (σ z) (σ t) := by
  rcases le_total x y with h | h <;> rcases le_total z t with g | g
  · rw [min_eq_left h, max_eq_right h, min_eq_left g, max_eq_right g]
  · rw [min_eq_left h, max_eq_right h, min_eq_right g, max_eq_left g]
    exact (cellNum_swap₃₄ (σ x) (σ y) (σ z) (σ t)).symm
  · rw [min_eq_right h, max_eq_left h, min_eq_left g, max_eq_right g]
    exact (cellNum_swap₁₂ (σ x) (σ y) (σ z) (σ t)).symm
  · rw [min_eq_right h, max_eq_left h, min_eq_right g, max_eq_left g]
    exact ((cellNum_swap₁₂ (σ x) (σ y) (σ z) (σ t)).trans
      (cellNum_swap₃₄ (σ y) (σ x) (σ z) (σ t))).symm

/-- The bit of a relabelled mask, below 90. -/
theorem bitAt_permMask {σ : Equiv.Perm (Fin 6)} {w : Mask} {i : ℕ} (hi : i < 90) :
    bitAt (permMask σ w) i = bitAt w (cellNum (σ (cellOf i).1.1) (σ (cellOf i).1.2)
      (σ (cellOf i).2.1) (σ (cellOf i).2.2)) := by
  rw [permMask, bitAt_ofBits 90 _ i hi]

/-- **The relabellings compose.** -/
theorem permMask_comp (σ τ : Equiv.Perm (Fin 6)) (w : Mask) :
    permMask τ (permMask σ w) = permMask (τ.trans σ) w := by
  show ofBits 90 (fun i => bitAt (permMask σ w)
      (cellNum (τ (cellOf i).1.1) (τ (cellOf i).1.2)
        (τ (cellOf i).2.1) (τ (cellOf i).2.2)))
    = ofBits 90 (fun i => bitAt w
      (cellNum (σ (τ (cellOf i).1.1)) (σ (τ (cellOf i).1.2))
        (σ (τ (cellOf i).2.1)) (σ (τ (cellOf i).2.2))))
  refine ofBits_congr 90 _ _ ?_
  intro i hi
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := cellOf_distinct ⟨i, hi⟩
  obtain ⟨hlt, heq⟩ := cellNum_spec (τ (cellOf i).1.1) (τ (cellOf i).1.2)
    (τ (cellOf i).2.1) (τ (cellOf i).2.2)
    (τ.injective.ne d1) (τ.injective.ne d2) (τ.injective.ne d3)
    (τ.injective.ne d4) (τ.injective.ne d5) (τ.injective.ne d6)
  rw [bitAt_permMask hlt, heq]
  exact congrArg (bitAt w) (cellNum_map_minmax σ (τ (cellOf i).1.1) (τ (cellOf i).1.2)
    (τ (cellOf i).2.1) (τ (cellOf i).2.2))

/-- The positive part of a node survives relabelling. -/
theorem below_permMask {pos w : Mask} (σ : Equiv.Perm (Fin 6)) (h : Below pos w) :
    Below (permMask σ pos) (permMask σ w) := by
  intro i hi
  by_cases h90 : i < 90
  · rw [bitAt_permMask h90]
    rw [bitAt_permMask h90] at hi
    exact h _ hi
  · rw [bitAt_eq_false_of_lt (permMask_lt σ pos) (Nat.le_of_not_lt h90)] at hi
    simp at hi

/-- The negative part of a node survives relabelling. -/
theorem apart_permMask {neg w : Mask} (σ : Equiv.Perm (Fin 6)) (h : Apart neg w) :
    Apart (permMask σ neg) (permMask σ w) := by
  intro i hi
  by_cases h90 : i < 90
  · rw [bitAt_permMask h90]
    rw [bitAt_permMask h90] at hi
    exact h _ hi
  · rw [bitAt_eq_false_of_lt (permMask_lt σ neg) (Nat.le_of_not_lt h90)] at hi
    simp at hi

/-- **Lemma 4: a node is settled if its relabelling is.** -/
theorem settles_perm {σ : Equiv.Perm (Fin 6)} {pos neg : Mask}
    (h : Settles (permMask σ pos) (permMask σ neg)) : Settles pos neg := by
  intro p hgp hrep w hlt hw hb ha
  obtain ⟨τ, hτ⟩ := h (fun i => p (σ i)) (gp_comp σ hgp) (repeats_comp σ hrep)
    (permMask σ w) (permMask_lt σ w) (carries_comp σ hw)
    (below_permMask σ hb) (apart_permMask σ ha)
  refine ⟨τ.trans σ, ?_⟩
  rw [← permMask_comp]
  exact hτ

/-- The same with the relabelling given as a tuple, which is the form the
transcript carries. -/
theorem settles_symmT {t : Tup} {pos neg : Mask}
    (hbij : Function.Bijective (apTup t))
    (h : Settles (permMaskT t pos) (permMaskT t neg)) : Settles pos neg := by
  have e : ∀ v : Mask, permMask (Equiv.ofBijective _ hbij) v = permMaskT t v :=
    fun _ => rfl
  refine settles_perm (σ := Equiv.ofBijective _ hbij) ?_
  rw [e, e]
  exact h

/-! ## The extended transcript -/

inductive Tr where
  | closed : Tr
  | leaf : Tup → Tr
  | assumed : Tr
  | branch : ℕ → List Tr → Tr
  | forced : ℕ → List (ℕ × ℤ) → Tr → Tr
  | colBad : Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → Tr
  | cycBad : Fin 6 → Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → Tr
  | halfBad : Fin 6 → Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → List (ℕ × ℤ) → Tr
  | chain : ℕ → List ℕ → Tr → Tr
  | relBad : Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → Tr
  | tab : List ℕ → Tr → Tr
  | parBad : Fin 6 → Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → Tr
  | parRel : Fin 6 → Fin 6 → Fin 6 → List (ℕ × ℤ) → List ParTerm → Tr
  | symm : Tup → Tr → Tr

/-- The transcript checker: the four lattice shapes, the closure, the relation
space, the propagation of the forty-five tables, and the two forms of the
parallelogram rule. -/
def check (A : List (Mask × Mask)) : ℕ → Mask → Mask → Tr → Bool
  | 0, _, _, _ => false
  | _ + 1, pos, neg, Tr.closed => !okNode pos neg
  | _ + 1, pos, neg, Tr.leaf t => censusLeaf pos neg t
  | _ + 1, pos, neg, Tr.assumed => A.contains (pos, neg)
  | f + 1, pos, neg, Tr.branch k ch =>
      decide (k < 15) &&
        zipAll (fun (x : Pat × Mask × Mask) (c : Tr) =>
          check A f (pos ||| x.2.1) (neg ||| x.2.2) c) (branchOf k) ch
  | f + 1, pos, neg, Tr.forced j cert c =>
      decide (j < 90) && certSupp pos cert && certOK (witForm j) cert &&
        check A f (pos ||| cellMask j) neg c
  | _ + 1, pos, _, Tr.colBad a b c cert =>
      decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c) &&
        certSupp pos cert && certOK (colForm a b c) cert
  | _ + 1, pos, _, Tr.cycBad u v c d cert =>
      decide (u ≠ v) && decide (u ≠ c) && decide (u ≠ d) && decide (v ≠ c) &&
        decide (v ≠ d) && decide (c ≠ d) &&
        certSupp pos cert && certOK (cycForm u v c d) cert
  | _ + 1, pos, _, Tr.halfBad a x y z c₁ c₂ =>
      decide (a ≠ x) && decide (a ≠ y) && decide (a ≠ z) && decide (x ≠ y) &&
        decide (x ≠ z) && decide (y ≠ z) &&
        certSupp pos c₁ && certSupp pos c₂ &&
        certOK (halfForm a x y) c₁ && certOK (halfForm a x z) c₂
  | f + 1, pos, neg, Tr.chain j path c =>
      decide (j < 90) && chainOK pos j path &&
        check A f (pos ||| cellMask j) neg c
  | _ + 1, pos, _, Tr.relBad a b c cert =>
      decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c) &&
        certSupp pos cert && relTriZero cert && relOut a b c cert &&
        relTrip a b c cert
  | f + 1, pos, neg, Tr.tab ks c =>
      ks.all (fun k => decide (k < 45)) &&
        check A f (tabFold ks pos neg).1 (tabFold ks pos neg).2 c
  | _ + 1, pos, _, Tr.parBad a b c d cert =>
      parIdx a b c d && certSupp pos cert && relTriZero cert &&
        relPar a b c d cert &&
        bitAt pos (cellNum b d a c) && bitAt pos (cellNum a c b d)
  | _ + 1, pos, neg, Tr.parRel x y z cert pars =>
      decide (x ≠ y) && decide (x ≠ z) && decide (y ≠ z) &&
        certSupp pos cert && relTriZero cert && parsOK pos neg pars &&
        parOut x y z cert pars && parTrip x y z cert pars
  | f + 1, pos, neg, Tr.symm t c =>
      decide (Function.Bijective (apTup t)) &&
        check A f (permMaskT t pos) (permMaskT t neg) c

/-- **The checker is sound.**  A checked transcript settles its root node, given
the soundness of the forty-five tables, of the lattice rules, of the closure, of
the relation space and of the two parallelogram rules, and given that the nodes
it hands on are settled. -/
theorem check_sound (hT : TablesSound) (hL : LatticeSound) (hC : ClosureSound)
    (hR : RelationSound) (hP : ParSound) (hQ : ParRelSound) (A : List (Mask × Mask))
    (hA : ∀ x ∈ A, Settles x.1 x.2) :
    ∀ (f : ℕ) (pos neg : Mask) (t : Tr), check A f pos neg t = true → Settles pos neg := by
  intro f
  induction f with
  | zero => intro pos neg t h; simp [check] at h
  | succ f ih =>
    intro pos neg t h
    cases t with
    | closed =>
      have hbad : okNode pos neg = false := by simpa [check] using h
      exact settles_of_refutes (refutes_of_okNode_eq_false hT hbad)
    | leaf t => exact settles_leaf (by simpa [check] using h)
    | assumed =>
      exact hA _ (List.mem_of_elem_eq_true (by simpa [check] using h))
    | branch k ch =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hk, hz⟩ := h
      have hbk : branchOk k = true :=
        List.all_eq_true.mp branchOk_all k (List.mem_range.mpr hk)
      simp only [branchOk, Bool.and_eq_true, beq_iff_eq] at hbk
      obtain ⟨hmap, hsel⟩ := hbk
      refine settles_branch hT (ruleAt_mem hk) ?_
      intro q hq
      rw [← hmap, List.mem_map] at hq
      obtain ⟨x, hxmem, hxq⟩ := hq
      obtain ⟨c, hc⟩ := zipAll_of _ _ hz x hxmem
      have hs := List.all_eq_true.mp hsel x hxmem
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      subst hxq
      rw [hs.1, hs.2]
      exact ih _ _ c hc
    | forced j cert c =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hj, hs⟩, hc⟩, hrec⟩ := h
      exact settles_forced hL hj hs hc (ih _ _ c hrec)
    | colBad a b c cert =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hab, hac⟩, hbc⟩, hs⟩, hc⟩ := h
      exact settles_of_refutes (refutes_col hL hab hac hbc hs hc)
    | cycBad u v c d cert =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨huv, huc⟩, hud⟩, hvc⟩, hvd⟩, hcd⟩, hs⟩, hc⟩ := h
      exact settles_of_refutes (refutes_cyc hL huv huc hud hvc hvd hcd hs hc)
    | halfBad a x y z c₁ c₂ =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hax, hay⟩, haz⟩, hxy⟩, hxz⟩, hyz⟩, hs₁⟩, hs₂⟩, hc₁⟩, hc₂⟩ := h
      exact settles_of_refutes (refutes_half hL hax hay haz hxy hxz hyz hs₁ hs₂ hc₁ hc₂)
    | chain j path c =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hj, hch⟩, hrec⟩ := h
      exact settles_chain hC hj hch (ih _ _ c hrec)
    | relBad a b c cert =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, hs⟩, ht⟩, ho⟩, hp⟩ := h
      exact settles_of_refutes (refutes_rel hR hab hac hbc hs ht ho hp)
    | tab ks c =>
      simp only [check, Bool.and_eq_true] at h
      obtain ⟨hks, hrec⟩ := h
      refine settles_tab hT ks ?_ pos neg (ih _ _ c hrec)
      intro k hk
      exact of_decide_eq_true (List.all_eq_true.mp hks k hk)
    | parBad a b c d cert =>
      simp only [check, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨hidx, hsu⟩, htz⟩, hpar⟩, k1⟩, k2⟩ := h
      exact settles_of_refutes (refutes_par hP hidx hsu htz hpar k1 k2)
    | parRel x y z cert pars =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hxy, hxz⟩, hyz⟩, hsu⟩, htz⟩, hpok⟩, hout⟩, htrip⟩ := h
      exact settles_of_refutes (refutes_parRel hQ hxy hxz hyz hsu htz hpok hout htrip)
    | symm t c =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hbij, hrec⟩ := h
      exact settles_symmT hbij (ih _ _ c hrec)

/-- A list of nodes contained in another, checked by `decide`. -/
theorem mem_of_subset {L M : List (Mask × Mask)} (h : L.all (fun y => M.contains y) = true) :
    ∀ y ∈ L, y ∈ M :=
  fun y hy => List.mem_of_elem_eq_true (List.all_eq_true.mp h y hy)

/-- The form a generated subtree theorem takes. -/
theorem settles_of_check {A : List (Mask × Mask)}
    (hA : ∀ x ∈ A, Settles x.1 x.2) {f : ℕ} {pos neg : Mask} {t : Tr}
    (h : check A f pos neg t = true) : Settles pos neg :=
  check_sound tables_sound lattice_sound closure_sound relation_sound par_sound
    parrel_sound A hA f pos neg t h

#print axioms DistinctCircumradii.fourDistinct_swap0
#print axioms DistinctCircumradii.fourDistinct_swap1
#print axioms DistinctCircumradii.fourDistinct_swap2
#print axioms DistinctCircumradii.repeats_of_ne
#print axioms DistinctCircumradii.gp_comp
#print axioms DistinctCircumradii.repeats_comp
#print axioms DistinctCircumradii.cellNum_map_minmax
#print axioms DistinctCircumradii.permMask_comp
#print axioms DistinctCircumradii.below_permMask
#print axioms DistinctCircumradii.apart_permMask
#print axioms DistinctCircumradii.settles_perm
#print axioms DistinctCircumradii.settles_symmT
#print axioms DistinctCircumradii.check_sound
#print axioms DistinctCircumradii.settles_of_check
#print axioms DistinctCircumradii.tables_sound
#print axioms DistinctCircumradii.lattice_sound
#print axioms DistinctCircumradii.closure_sound
#print axioms DistinctCircumradii.relation_sound
#print axioms DistinctCircumradii.par_sound
#print axioms DistinctCircumradii.parrel_sound
#print axioms DistinctCircumradii.censusComplete_iff_settles

end DistinctCircumradii
