/-
  Bombieri–Garrett の擬ラプラシアンで「捕まる零点の個数」の上界の、
  有限の核だけを取り出す。

  背景（数学の側。本ファイルの主張には使わない）：切り落ち高さ a の擬カスプ形式の空間では、
  comb（a^s + c_s a^{1−s} = 0 の根）の隣り合う歯の間に擬ラプラシアン S̃_θ の固有値は
  高々 1 個しか入らない（Bombieri–Garrett, arXiv:2002.07929, Corollary 62）。
  位相 Φ_a(t) = t·log a + arg ξ(1+2it) を座標に取ると歯は間隔 π の等間隔になるから、
  捕まる零点の集合は「Φ 座標で互いに π 以上離れた集合」である。
  その最大の大きさを与えるのが本ファイルのパッキング補題である。

  * packing_card_le      : 区間 [A,B] に入り互いに d 以上離れた有限集合の要素数は ⌊(B−A)/d⌋+1 以下
  * packing_card_le_real : 実数版 (card : ℝ) ≤ (B−A)/d + 1
  * excluded_ge          : 候補が N 個あれば、捕まらないものが N − (⌊(B−A)/d⌋+1) 個以上ある
  * packing_sharp        : 上界は達せられる（等間隔の点列が実現する）

  等級：［Lean］。実数上の有限集合のパッキングだけの言明である。
  **リーマン予想の本体の証明にも反証にも使えない。**
-/
import Mathlib

namespace PsiPacking

open Finset

variable {A B d : ℝ}

/-- `⌊u⌋ = ⌊v⌋` なら `|u − v| < 1`。 -/
lemma abs_sub_lt_one_of_floor_eq {u v : ℝ} (h : ⌊u⌋ = ⌊v⌋) : |u - v| < 1 := by
  have hu1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
  have hu2 : u < ⌊u⌋ + 1 := Int.lt_floor_add_one u
  have hv1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
  have hv2 : v < ⌊v⌋ + 1 := Int.lt_floor_add_one v
  rw [h] at hu1 hu2
  rw [abs_lt]
  constructor <;> linarith

/-- 区間 `[A, B]` に入り、互いの距離が `d` 以上である有限集合の要素数は
`⌊(B − A)/d⌋ + 1` 以下。証明は `x ↦ ⌊(x − A)/d⌋` が単射であること。 -/
theorem packing_card_le (hd : 0 < d) (hAB : A ≤ B) (S : Finset ℝ)
    (hmem : ∀ x ∈ S, A ≤ x ∧ x ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    (S.card : ℤ) ≤ ⌊(B - A) / d⌋ + 1 := by
  classical
  set n : ℤ := ⌊(B - A) / d⌋ with hn
  have hn0 : 0 ≤ n := by
    rw [hn]; exact Int.floor_nonneg.2 (div_nonneg (by linarith) hd.le)
  set f : ℝ → ℤ := fun x => ⌊(x - A) / d⌋ with hf
  have hinj : Set.InjOn f (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hsep' : d ≤ |x - y| := hsep x hx y hy hne
    have h1 : |(x - A) / d - (y - A) / d| < 1 := abs_sub_lt_one_of_floor_eq hxy
    have h2 : (x - A) / d - (y - A) / d = (x - y) / d := by ring
    rw [h2, abs_div, abs_of_pos hd, div_lt_one hd] at h1
    exact absurd hsep' (not_le.2 h1)
  have himg : S.image f ⊆ Finset.Icc (0 : ℤ) n := by
    intro k hk
    rcases Finset.mem_image.1 hk with ⟨x, hx, rfl⟩
    obtain ⟨hA, hB⟩ := hmem x hx
    have h0 : (0 : ℤ) ≤ f x := by
      rw [hf]; exact Int.floor_nonneg.2 (div_nonneg (by linarith) hd.le)
    have hle : (x - A) / d ≤ (B - A) / d := by
      gcongr
    have h1 : f x ≤ n := by rw [hf, hn]; exact Int.floor_le_floor hle
    exact Finset.mem_Icc.2 ⟨h0, h1⟩
  have hcard : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  have hIcc : ((Finset.Icc (0 : ℤ) n).card : ℤ) = n + 1 := by
    rw [Int.card_Icc]
    omega
  calc (S.card : ℤ) = ((S.image f).card : ℤ) := by rw [hcard]
    _ ≤ ((Finset.Icc (0 : ℤ) n).card : ℤ) := by
        exact_mod_cast Finset.card_le_card himg
    _ = n + 1 := hIcc

/-- 実数版。 -/
theorem packing_card_le_real (hd : 0 < d) (hAB : A ≤ B) (S : Finset ℝ)
    (hmem : ∀ x ∈ S, A ≤ x ∧ x ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    (S.card : ℝ) ≤ (B - A) / d + 1 := by
  have h := packing_card_le hd hAB S hmem hsep
  have h1 : ((S.card : ℤ) : ℝ) ≤ ((⌊(B - A) / d⌋ + 1 : ℤ) : ℝ) := by exact_mod_cast h
  have h2 : ((⌊(B - A) / d⌋ : ℤ) : ℝ) ≤ (B - A) / d := Int.floor_le _
  push_cast at h1
  linarith

/-- 候補が `Z` にあり、捕まる集合 `C ⊆ Z` が互いに `d` 以上離れているなら、
捕まらないものが `Z.card − (⌊(B−A)/d⌋+1)` 個以上ある。 -/
theorem excluded_ge (hd : 0 < d) (hAB : A ≤ B) (Z C : Finset ℝ) (hCZ : C ⊆ Z)
    (hmem : ∀ x ∈ C, A ≤ x ∧ x ≤ B)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ |x - y|) :
    (Z.card : ℤ) - (⌊(B - A) / d⌋ + 1) ≤ ((Z \ C).card : ℤ) := by
  have h1 : (C.card : ℤ) ≤ ⌊(B - A) / d⌋ + 1 := packing_card_le hd hAB C hmem hsep
  have h2 : (Z \ C).card = Z.card - C.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hCZ]
  have h3 : C.card ≤ Z.card := Finset.card_le_card hCZ
  omega

/-- 上界は達せられる：`m·d ≤ B − A` なら、`[A,B]` の中に互いに `d` 以上離れた `m+1` 点がある。 -/
theorem packing_sharp (hd : 0 < d) (m : ℕ) (h : (m : ℝ) * d ≤ B - A) :
    ∃ S : Finset ℝ, S.card = m + 1 ∧ (∀ x ∈ S, A ≤ x ∧ x ≤ B) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) := by
  classical
  have hinjf : Function.Injective (fun k : ℕ => A + (k : ℝ) * d) := by
    intro a b hab
    simp only [add_right_inj] at hab
    have h' := mul_right_cancel₀ hd.ne' hab
    exact_mod_cast h'
  refine ⟨(Finset.range (m + 1)).image (fun k : ℕ => A + (k : ℝ) * d), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjf, Finset.card_range]
  · intro x hx
    rcases Finset.mem_image.1 hx with ⟨k, hk, hxk⟩
    subst hxk
    have hkm : (k : ℝ) ≤ (m : ℝ) := by
      have h' := Finset.mem_range.1 hk
      exact_mod_cast Nat.lt_succ_iff.1 h'
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    refine ⟨by nlinarith, ?_⟩
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ)) hd.le]
  · intro x hx y hy hne
    rcases Finset.mem_image.1 hx with ⟨a, -, hxa⟩
    rcases Finset.mem_image.1 hy with ⟨b, -, hyb⟩
    subst hxa
    subst hyb
    have hab : a ≠ b := by
      intro hEq; exact hne (by rw [hEq])
    have h1 : A + (a : ℝ) * d - (A + (b : ℝ) * d) = ((a : ℝ) - (b : ℝ)) * d := by ring
    rw [h1, abs_mul, abs_of_pos hd]
    have h2 : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hc : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have hc : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| - 1) hd.le]

#print axioms packing_card_le
#print axioms packing_card_le_real
#print axioms excluded_ge
#print axioms packing_sharp

end PsiPacking
