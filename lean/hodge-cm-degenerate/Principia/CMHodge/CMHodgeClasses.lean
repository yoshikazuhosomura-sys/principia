/-
CM アーベル多様体の例外ホッジ類 — 9 次元の明示的な反例の組合せ部分。

背景（紙の側、この file は主張しない）：`A` を CM 体 `E`（次数 `2g`）と CM 型 `Φ` を持つ
`g` 次元 CM アーベル多様体とする。`E/Q` がガロアで `G = Gal(E/Q)`、`X = G`（`E` の埋め込み）、
`c ∈ G` を複素共役とすると、Pohlman の判定により `H^{2p}(A,Q)` のホッジ類は

    e_T  （`T ⊆ X`, `|T| = 2p`, すべての `σ ∈ G` で `|T ∩ σΦ| = p`）

が張る。積は `e_T · e_{T'} = ± e_{T ⊔ T'}`（交わるときは 0）だから、
「`T` が因子で生成される」は「`T` が許容な 2 元集合の直和に分かれる」ことに等しい。
Moonen–Zarhin の Weil 類 `W_F = ∧^{2g/[F:Q]}_F H_1(A,Q)`（`F ⊆ E` は CM 部分体）が
偶数次のコホモロジーに入るのは `[E:F]` が偶数のときだけである。

この file が `decide` で閉じるのは、次の具体例についての**有限集合の言明だけ**である：

    G = Z/2 × Z/3 × Z/3   （位数 18、`E` は 18 次のアーベル CM 体、`g = 9`）
    c = (1,0,0)
    S = {(0,0), (1,1), (1,2)} ⊆ Z/3 × Z/3
    Φ = { (0,b) : b ∉ S } ∪ { (1,b) : b ∈ S }
    T₀ = { (0,(x,0)) : x } ∪ { (1,(x,1)) : x }      （`|T₀| = 6`, `p = 3`）

  (1) `Φ` は CM 型（`Φ ⊔ cΦ = X`）
  (2) `T₀` は許容（= `e_{T₀}` はホッジ類、`H^6` の中）
  (3) 許容な 2 元集合は `{x, c+x}` だけ（⟹ `Φ` は原始的＝`A` は単純）
  (4) ゆえに `T₀` は許容 2 元集合の合併では書けない（= 因子で生成されない＝例外的）
  (5) `G` の対合は `c` ただ一つ ⟹ `c ∉ M` なる部分群 `M` の位数は奇数
      ⟹ `[E:F]` が偶数の CM 部分体 `F` は無い ⟹ Weil 類は一つも無い
  (6) `Stab_G(Φ) = 0`（(3) と独立な、原始性の別証）

代数性については何も述べていない（「因子で生成されない」は「代数的でない」ではない）。
-/
import Mathlib

namespace CMHodge

/-- `X = G = Gal(E/Q)`：18 点。 -/
abbrev G : Type := ZMod 2 × ZMod 3 × ZMod 3

/-- 複素共役。 -/
def cc : G := (1, 0, 0)

/-- `S ⊆ (Z/3)^2`：CM 型を決める 3 元集合。 -/
def inS : ZMod 3 × ZMod 3 → Bool := fun b => b = (0, 0) || b = (1, 1) || b = (1, 2)

/-- CM 型 `Φ` の特性関数。 -/
def isPhi (p : G) : Bool := (p.1 = 1 : Bool) == inS p.2

/-- `T` が許容（`e_T` がホッジ類）：すべての `σ` で `|T ∩ σΦ| = |T|/2`。 -/
def adm (T : Finset G) : Prop :=
  ∀ σ : G, 2 * (T.filter (fun x => isPhi (x - σ) = true)).card = T.card

instance (T : Finset G) : Decidable (adm T) := by unfold adm; infer_instance

/-- 例外ホッジ類の台。`|T₀| = 6`, `p = 3`, すなわち `H^6(A,Q)` の中の類。 -/
def T0 : Finset G :=
  {(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, 1), (1, 1, 1), (1, 2, 1)}

/-! ## (1) `Φ` は CM 型 -/

theorem cc_add_cc : cc + cc = 0 := by decide

theorem phi_is_cm_type : ∀ x : G, isPhi x = true ↔ isPhi (cc + x) = false := by decide

theorem phi_card : (Finset.univ.filter (fun x : G => isPhi x = true)).card = 9 := by decide

/-! ## (2) `T₀` は許容（ホッジ類） -/

theorem T0_card : T0.card = 6 := by decide

theorem T0_hodge : adm T0 := by decide

/-! ## (3) 許容な 2 元集合は `{x, c+x}` だけ -/

theorem two_adm : ∀ x y : G, x ≠ y → adm {x, y} → y = cc + x := by decide

/-- 許容な 2 元集合は `c` で閉じている。 -/
theorem adm_pair_cc_closed {p : Finset G} (h2 : p.card = 2) (ha : adm p) :
    ∀ x ∈ p, cc + x ∈ p := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
  have hy : y = cc + x := two_adm x y hxy ha
  subst hy
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with rfl | rfl
  · exact Or.inr rfl
  · left
    rw [← add_assoc, cc_add_cc, zero_add]

/-! ## (4) `T₀` は因子では生成されない -/

/-- `T₀` は許容な 2 元集合たちの合併では書けない。
（`e_T · e_{T'} = ± e_{T ⊔ T'}` なので、これが「因子で生成されない」の組合せ的な意味である。
 分割の disjointness すら要らない：合併で書けないことを示す。） -/
theorem T0_not_generated_by_divisors
    (P : Finset (Finset G)) (hcard : ∀ p ∈ P, p.card = 2) (hadm : ∀ p ∈ P, adm p)
    (hcover : P.biUnion id = T0) : False := by
  have hx : ((0 : ZMod 2), (0 : ZMod 3), (0 : ZMod 3)) ∈ T0 := by decide
  rw [← hcover] at hx
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
  have hcx := adm_pair_cc_closed (hcard p hp) (hadm p hp) _ hxp
  have : cc + ((0 : ZMod 2), (0 : ZMod 3), (0 : ZMod 3)) ∈ T0 := by
    rw [← hcover]; exact Finset.mem_biUnion.mpr ⟨p, hp, hcx⟩
  revert this
  decide

/-! ## (5) `c`-自由なブロックはすべて奇数サイズ（⟹ Weil 類は一つも無い） -/

/-- `G` の位数 2 の元は `c` だけ。
Cauchy の定理（紙）と合わせて「`c ∉ M` なる部分群 `M` の位数は奇数」が出る：
`|M|` が偶数なら `M` に位数 2 の元があり、それは `c` でなければならない。
CM 部分体 `F ⊆ E` は `M = Gal(E/F)` に対応し `[E:F] = |M|` なので、
**`[E:F]` が偶数の CM 部分体は無く、Weil 類 `W_F` は偶数次に一つも現れない**。 -/
theorem unique_involution : ∀ x : G, x + x = 0 → x = 0 ∨ x = cc := by decide

/-- 例外類 `T₀` を作っている `c`-自由ブロック（`x` 軸のなす位数 3 の部分群）。 -/
def Y0 : Finset G := {(0, 0, 0), (0, 1, 0), (0, 2, 0)}

/-- 同じブロック系のもう一つのブロック。 -/
def Y1 : Finset G := {(0, 0, 1), (0, 1, 1), (0, 2, 1)}

theorem Y0_subgroup : (0 : G) ∈ Y0 ∧ ∀ a ∈ Y0, ∀ b ∈ Y0, a + b ∈ Y0 := by decide

theorem Y0_card_odd : Y0.card = 3 := by decide

theorem Y0_cfree : ∀ a ∈ Y0, cc + a ∉ Y0 := by decide

theorem Y1_coset : Y1 = Y0.image (fun x => x + (0, 0, 1)) := by decide

/-- 反例は「奇数サイズの `c`-自由ブロック二つ」の直和である：`T₀ = Y₀ ⊔ c·Y₁`。
すなわち例外類は `[E:F] = 3` の CM 部分体 `F` の**奇数次の**繊維の積であって、
偶数次の Weil 類の枠の外にある（本文 §5 の修復した仮説 (H′)）。 -/
theorem T0_eq : T0 = Y0 ∪ Y1.image (fun x => cc + x) := by decide

theorem T0_disjoint : Y0 ∩ Y1.image (fun x => cc + x) = ∅ := by decide

/-! ## (6) `Φ` は原始的（`Stab_G(Φ) = 0`）⟹ `A` は単純 -/

theorem stab_trivial :
    ∀ σ : G, (∀ x : G, isPhi (x - σ) = isPhi x) → σ = 0 := by decide

/-! ## 公理の確認 -/

#print axioms phi_is_cm_type
#print axioms phi_card
#print axioms T0_card
#print axioms T0_hodge
#print axioms two_adm
#print axioms adm_pair_cc_closed
#print axioms T0_not_generated_by_divisors
#print axioms unique_involution
#print axioms Y0_subgroup
#print axioms Y0_cfree
#print axioms T0_eq
#print axioms T0_disjoint
#print axioms stab_trivial

end CMHodge
-- 主な定理の #print axioms（証明には触れていない）
#print axioms CMHodge.cc_add_cc
#print axioms CMHodge.Y0_card_odd
#print axioms CMHodge.Y1_coset
