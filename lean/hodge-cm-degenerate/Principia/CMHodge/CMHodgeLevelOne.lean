/-
  `H³(A)` の level ≤ 1 部分（54 次元の側）の組合せ構造

  `A = A_S` は `K = Q(ζ_19)` の退化かつ原始的な CM 型
  `S = {0,1,2,3,4,5,6,8,16} ⊂ Z/18`（指数座標、`γ = 2`）による 9 次元単純 CM アーベル多様体。
  `H³(A) = ∧³H¹(A)` の固有線は 3 元集合 `T ⊂ Z/18` で添字づけられ、`ω_T` のホッジ型は
  `(|T ∩ S|, 3 − |T ∩ S|)`。`Q` 上の部分ホッジ構造は平行移動で閉じた `T` の集合に対応するから、
  level ≤ 1 の最大有理部分ホッジ構造は「全ての `u` で `|T ∩ (S+u)| ∈ {1,2}`」の `T` が張る。

  その 204 個は 144（`ρ` 対を含む＝`NS ∪ H¹`）＋ 6（コセット `C_k = {k,k+6,k+12}` ＝ `W_F`）
  ＋ 54 に分かれる。このファイルは**最後の 54 の側**を決定する：
  54 は平行移動の 3 軌道（各 18 個）に分かれ、その型パターン `{u : |T ∩ (S+u)| = 2}` は
  3 個とも退化かつ原始的な CM 型であり、`S` の平行移動ではない（⟹ 対応する `A_i` は `A` と非同種）。
  さらに **2 個は互いに平行移動で移り合う**（⟹ `V ≅ H¹(A')(−1) ⊕ H¹(A'')(−1)^{⊕2}`）。

  型パターンの畳み込みは巡回的である：退化かつ原始的な 54 個の CM 型は平行移動で 3 軌道
  `O_0 ∋ S`, `O_1`, `O_2` に分かれ、`O_i` の型の `H³` の 54 の側は
  `O_{i+1}` を 1 回・`O_{i+2}` を 2 回だけ含む（対角は 0）。

  このファイルは**組合せの言明だけ**を扱う。幾何・代数的サイクル・ホッジ予想は含まない。
  Pohlmann の判定（Milne, arXiv:2010.08857, 1.2(c)）：`ω_Δ` がホッジ類 ⟺
  `|(t∘Δ) ∩ Φ| = p` が全ての `t ∈ Gal` で成り立つ。
-/
import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CMHodge

/-! ### `Z/18` の部分集合を 18 ビットのマスクで表す -/

/-- `Z/18` 全体。 -/
def M18 : ℕ := 262143

/-- ビットの取り出し（添字は `mod 18`）。 -/
def bitm (m i : ℕ) : ℕ := (m >>> (i % 18)) &&& 1

/-- 平行移動 `m ↦ m + u`。 -/
def rotm (m u : ℕ) : ℕ := ((m <<< (u % 18)) ||| (m >>> (18 - u % 18))) &&& M18

/-- 位数（18 ビット）。 -/
def pc (m : ℕ) : ℕ :=
  bitm m 0 + bitm m 1 + bitm m 2 + bitm m 3 + bitm m 4 + bitm m 5 +
  bitm m 6 + bitm m 7 + bitm m 8 + bitm m 9 + bitm m 10 + bitm m 11 +
  bitm m 12 + bitm m 13 + bitm m 14 + bitm m 15 + bitm m 16 + bitm m 17

def idx18 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]

/-- 集合をマスクに。 -/
def mk (l : List ℕ) : ℕ := l.foldl (fun m a => m ||| (1 <<< (a % 18))) 0

/-- 代表 CM 型 `S = {0,1,2,3,4,5,6,8,16}`。 -/
def SM : ℕ := mk [0,1,2,3,4,5,6,8,16]

/-- `S` の平行移動の全体（`u` 番目が `S + u`）。 -/
def rots (m : ℕ) : List ℕ := idx18.map (rotm m)

/-- CM 型であること：`m ⊔ (m+9) = Z/18`。 -/
def isCM (m : ℕ) : Bool := (m ||| rotm m 9 == M18) && (m &&& rotm m 9 == 0)

/-- 原始的：平行移動の安定化群が自明。 -/
def isPrim (m : ℕ) : Bool := idx18.all (fun u => u == 0 || rotm m u != m)

/-- `m` と `n` が平行移動で移り合う。 -/
def tEq (m n : ℕ) : Bool := idx18.any (fun u => rotm m u == n)

/-! ### 退化性（`Φ₆ ∣ m̃` による判定） -/

/-- 符号ベクトル `m̃ = Σ ε_k x^k`（`ε_k = ±1`）。 -/
def epsi (m k : ℕ) : Int := if bitm m k = 1 then 1 else -1

/-- `x^k mod (x²−x+1)` の `x` の係数（`k mod 6` で周期）。 -/
def a6 : List Int := [0,1,1,0,-1,-1]
/-- `x^k mod (x²−x+1)` の定数項。 -/
def b6 : List Int := [1,0,-1,-1,0,1]

/-- `Φ₆ ∣ m̃` ⟺ CM 型 `m` が退化。 -/
def isDeg (m : ℕ) : Bool :=
  (idx18.foldl (fun s k => s + epsi m k * (a6.getD (k % 6) 0)) 0 == 0) &&
  (idx18.foldl (fun s k => s + epsi m k * (b6.getD (k % 6) 0)) 0 == 0)

/-- `Z/18` 上の 512 個の CM 型。 -/
def cmTypes : List ℕ :=
  (List.range 512).map (fun s =>
    (List.range 9).foldl (fun m j => m ||| (1 <<< (j + 9 * ((s >>> j) &&& 1)))) 0)

theorem cmTypes_card : cmTypes.length = 512 := by rfl

theorem cmTypes_all_cm : cmTypes.all isCM = true := by decide

/-- 退化かつ原始的な CM 型はちょうど 54 個（独立な数え上げと一致）。 -/
theorem deg_prim_card : (cmTypes.filter (fun m => isDeg m && isPrim m)).length = 54 := by rfl

theorem SM_deg_prim : (isCM SM && isDeg SM && isPrim SM) = true := by decide

/-! ### `H³(A)` の level ≤ 1 部分 -/

/-- 3 元集合のマスクの全体（816 個）。 -/
def triples : List ℕ :=
  idx18.flatMap (fun a => idx18.flatMap (fun b => idx18.filterMap (fun c =>
    if a < b && b < c then some ((1 <<< a) ||| (1 <<< b) ||| (1 <<< c)) else none)))

theorem triples_card : triples.length = 816 := by rfl

/-- `T` が level ≤ 1：全ての `u` で `|T ∩ (S+u)| ∈ {1,2}`。 -/
def isL1 (S T : ℕ) : Bool :=
  (rots S).all (fun q => pc (T &&& q) == 1 || pc (T &&& q) == 2)

/-- 型パターン `{u : |T ∩ (S+u)| = 2}`。 -/
def pat (S T : ℕ) : ℕ :=
  idx18.foldl (fun m u => if pc (T &&& rotm S u) == 2 then m ||| (1 <<< u) else m) 0

/-- `ρ` 対 `{a, a+9}` を含む。 -/
def hasRho (T : ℕ) : Bool :=
  (List.range 9).any (fun a => bitm T a == 1 && bitm T (a + 9) == 1)

/-- コセット `C_k = {k, k+6, k+12}`（`W_F` の 6 本）。 -/
def cosets : List ℕ := (List.range 6).map (fun k => mk [k, k+6, k+12])

/-- level ≤ 1 の 3 元集合。 -/
def L1 (S : ℕ) : List ℕ := triples.filter (isL1 S)

/-- 54 の側：`ρ` 対もコセットも含まないもの。 -/
def rest (S : ℕ) : List ℕ := (L1 S).filter (fun T => !hasRho T && !(cosets.contains T))

/-- `H³(A)` の level ≤ 1 部分は 204 次元。 -/
theorem level1_card : (L1 SM).length = 204 := by rfl

/-- 内訳 204 = 144（`ρ` 対）＋ 6（コセット）＋ 54。 -/
theorem level1_split :
    ((L1 SM).filter hasRho).length = 144 ∧
    ((L1 SM).filter (fun T => cosets.contains T)).length = 6 ∧
    (rest SM).length = 54 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- コセットは全て level ≤ 1（`W_F`）。 -/
theorem cosets_level1 : cosets.all (isL1 SM) = true := by decide

/-! ### 54 の側の 3 軌道とその型パターン -/

/-- 3 軌道の代表 `{0,4,11}`, `{0,5,11}`, `{0,6,11}`。 -/
def R1 : ℕ := mk [0,4,11]
def R2 : ℕ := mk [0,5,11]
def R3 : ℕ := mk [0,6,11]

/-- 3 個とも 54 の側に入る。 -/
theorem reps_in_rest :
    ((rest SM).contains R1 && (rest SM).contains R2 && (rest SM).contains R3) = true := by decide

/-- 54 個は 3 個の代表の平行移動で尽くされる。 -/
theorem rest_cover :
    (rest SM).all (fun T => tEq R1 T || tEq R2 T || tEq R3 T) = true := by decide

/-- 3 個の代表は互いに平行移動で移り合わない（＝軌道は 3 個、各 18 個）。 -/
theorem reps_distinct_orbits :
    (!tEq R1 R2 && !tEq R2 R3 && !tEq R1 R3) = true := by decide

/-- 型パターン `P_i`。 -/
def P1 : ℕ := pat SM R1
def P2 : ℕ := pat SM R2
def P3 : ℕ := pat SM R3

/-- 明示値：`P_1 = {0,2,3,6,10,13,14,16,17}`, `P_2 = {0,2,3,5,7,10,13,15,17}`,
    `P_3 = {0,2,3,5,6,8,10,13,16}`。 -/
theorem pat_values :
    P1 = mk [0,2,3,6,10,13,14,16,17] ∧
    P2 = mk [0,2,3,5,7,10,13,15,17] ∧
    P3 = mk [0,2,3,5,6,8,10,13,16] := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- 3 個とも退化かつ原始的な CM 型（＝54 個の族のメンバー）。 -/
theorem pat_deg_prim :
    ((isCM P1 && isDeg P1 && isPrim P1) &&
     (isCM P2 && isDeg P2 && isPrim P2) &&
     (isCM P3 && isDeg P3 && isPrim P3)) = true := by decide

/-- どれも `S` の平行移動ではない（⟹ `A_i` は `A` と非同種）。 -/
theorem pat_not_S : (!tEq P1 SM && !tEq P2 SM && !tEq P3 SM) = true := by decide

/-- **`P_2` と `P_3` は平行移動で移り合い、`P_1` はそれらと移り合わない。**
    ゆえに 54 次元部分は `H¹(A')(−1) ⊕ H¹(A'')(−1)^{⊕2}`（`A' ≁ A''`、どちらも `A` と非同種）。 -/
theorem pat_two_of_three : (tEq P2 P3 && !tEq P1 P2 && !tEq P1 P3) = true := by decide

/-! ### 相互性（3 軌道の巡回構造） -/

/-- 54 個の退化かつ原始的な CM 型の 3 軌道を `SM`, `P1`, `P2` で代表し、その番号を返す。 -/
def cls (m : ℕ) : ℕ := if tEq SM m then 0 else if tEq P1 m then 1 else if tEq P2 m then 2 else 9

/-- 3 代表は 3 つの異なる軌道にある。 -/
theorem cls_reps : (cls SM == 0 && cls P1 == 1 && cls P2 == 2) = true := by decide

/-- 退化かつ原始的な 54 個は `SM`, `P1`, `P2` の平行移動で尽くされる。 -/
theorem deg_prim_cover :
    (cmTypes.filter (fun m => isDeg m && isPrim m)).all (fun m => cls m != 9) = true := by decide

/-- **巡回的な相互性**：`O_i` の型の `H³` の 54 の側は `O_{i+1}` を 18 本・`O_{i+2}` を 36 本含み、
    自分自身（対角）は 1 本も含まない。 -/
theorem reciprocity_S :
    ((rest SM).countP (fun T => cls (pat SM T) == 0) = 0) ∧
    ((rest SM).countP (fun T => cls (pat SM T) == 1) = 18) ∧
    ((rest SM).countP (fun T => cls (pat SM T) == 2) = 36) := by
  refine ⟨by rfl, by rfl, by rfl⟩

theorem reciprocity_P1 :
    ((rest P1).countP (fun T => cls (pat P1 T) == 1) = 0) ∧
    ((rest P1).countP (fun T => cls (pat P1 T) == 2) = 18) ∧
    ((rest P1).countP (fun T => cls (pat P1 T) == 0) = 36) := by
  refine ⟨by rfl, by rfl, by rfl⟩

theorem reciprocity_P2 :
    ((rest P2).countP (fun T => cls (pat P2 T) == 2) = 0) ∧
    ((rest P2).countP (fun T => cls (pat P2 T) == 0) = 18) ∧
    ((rest P2).countP (fun T => cls (pat P2 T) == 1) = 36) := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- 3 軌道のどれでも level ≤ 1 部分は 204 = 144 + 6 + 54 で、コセットは常に level ≤ 1。 -/
theorem level1_uniform :
    ((L1 P1).length = 204 ∧ (rest P1).length = 54 ∧ cosets.all (isL1 P1) = true) ∧
    ((L1 P2).length = 204 ∧ (rest P2).length = 54 ∧ cosets.all (isL1 P2) = true) := by
  refine ⟨⟨by rfl, by rfl, by decide⟩, ⟨by rfl, by rfl, by decide⟩⟩

/-! ### `A × A_i` のホッジ類（Pohlmann） -/

def singles : List ℕ := idx18.map (fun a => 1 <<< a)
def pairs : List ℕ :=
  idx18.flatMap (fun a => idx18.filterMap (fun b =>
    if a < b then some ((1 <<< a) ||| (1 <<< b)) else none))
def quads : List ℕ :=
  idx18.flatMap (fun a => idx18.flatMap (fun b => idx18.flatMap (fun c =>
    idx18.filterMap (fun d =>
      if a < b && b < c && c < d then
        some ((1 <<< a) ||| (1 <<< b) ||| (1 <<< c) ||| (1 <<< d)) else none))))

theorem card_lists : singles.length = 18 ∧ pairs.length = 153 ∧ quads.length = 3060 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- Pohlmann の許容性：`∀u, |T₁ ∩ (S+u)| + |T₂ ∩ (T+u)| = p`。 -/
def adm (RS RT : List ℕ) (p T1 T2 : ℕ) : Bool :=
  (RS.zip RT).all (fun q => pc (T1 &&& q.1) + pc (T2 &&& q.2) == p)

def cnt (RS RT : List ℕ) (p : ℕ) (L1 L2 : List ℕ) : ℕ :=
  L1.foldl (fun s t1 => s + L2.countP (fun t2 => adm RS RT p t1 t2)) 0

/-- 余次元 1（`p = 1`）：`A × A_1` のホッジ類は `9 + 0 + 9 = 18` 個。
    混合項が 0 であることが `A_1` と `A` が非同種であることの証拠。 -/
theorem codim1_A1 :
    cnt (rots SM) (rots P1) 1 pairs [0] = 9 ∧
    cnt (rots SM) (rots P1) 1 singles singles = 0 ∧
    cnt (rots SM) (rots P1) 1 [0] pairs = 9 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- 余次元 2：`A × A_1` は `36 + 18 + 117 + 36 + 36 = 243` 個。
    因子 2 個の積が張る単項式は `36 + 81 + 36 = 153` だから例外は **90 個**
    （`H³⊗H¹` 側 `18 + 36 = 54`、`H²⊗H²` 側 `117 − 81 = 36`）。 -/
theorem codim2_A1 :
    cnt (rots SM) (rots P1) 2 quads [0] = 36 ∧
    cnt (rots SM) (rots P1) 2 triples singles = 18 ∧
    cnt (rots SM) (rots P1) 2 pairs pairs = 117 ∧
    cnt (rots SM) (rots P1) 2 singles triples = 36 ∧
    cnt (rots SM) (rots P1) 2 [0] quads = 36 := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- `A × A_2` でも同じ 243 個で、`H³⊗H¹` の側だけが `18 ↔ 36` と入れ替わる
    （`V_2, V_3` が `A_2` の 2 つのコピーであることの数値的な現れ）。 -/
theorem codim2_A2 :
    cnt (rots SM) (rots P2) 2 triples singles = 36 ∧
    cnt (rots SM) (rots P2) 2 singles triples = 18 ∧
    cnt (rots SM) (rots P2) 2 pairs pairs = 117 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-! ### 最短路（因子の積に割る）は `V` の側でも閉じる -/

/-- `Δ = T_A ⊔ {d}` が許容であるような `d` は、各代表についてちょうど 1 個。 -/
def admD (S T Tm : ℕ) : List ℕ := singles.filter (fun d => adm (rots S) (rots T) 2 Tm d)

theorem admD_unique :
    (admD SM P1 R1).length = 1 ∧ (admD SM P2 R2).length = 1 ∧ (admD SM P3 R3).length = 1 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- `s` を引いた型（André の `A_s` の CM 型 `φ_s`）。 -/
def shiftNeg (m s : ℕ) : ℕ := rotm m ((18 - s % 18) % 18)

/-- `Δ` の 4 つの CM 型（`T_A` の 3 元は `S` 側、`d` は `A_i` 側）。 -/
def deltaTypes (S T Tm d : ℕ) : List ℕ :=
  (idx18.filterMap (fun a => if bitm Tm a == 1 then some (shiftNeg S a) else none)) ++
  (idx18.filterMap (fun e => if bitm d e == 1 then some (shiftNeg T e) else none))

/-- **`V` の側でも、`Δ` の 4 つの CM 型はどの 2 個も互いに補型でない。**
    ゆえに分裂 Weil 類を「2 つの因子類の積」として書く最短路は、54 の側でも閉じる。 -/
theorem no_complementary_pairing_V :
    ([(SM,P1,R1), (SM,P2,R2), (SM,P3,R3)].all (fun x =>
      (admD x.1 x.2.1 x.2.2).all (fun d =>
        let ts := deltaTypes x.1 x.2.1 x.2.2 d
        ts.all (fun t1 => ts.all (fun t2 => t2 != rotm t1 9))))) = true := by decide

/-- Deligne 2.2 の仮定（分裂 Weil 型）：`Δ` の 4 型の和は全ての `t` で 2。 -/
theorem split_weil_condition_V :
    ([(SM,P1,R1), (SM,P2,R2), (SM,P3,R3)].all (fun x =>
      (admD x.1 x.2.1 x.2.2).all (fun d =>
        let ts := deltaTypes x.1 x.2.1 x.2.2 d
        idx18.all (fun t => (ts.foldl (fun s q => s + bitm q t) 0) == 2)))) = true := by decide

end CMHodge

#print axioms CMHodge.cmTypes_all_cm
#print axioms CMHodge.deg_prim_card
#print axioms CMHodge.SM_deg_prim
#print axioms CMHodge.level1_card
#print axioms CMHodge.level1_split
#print axioms CMHodge.cosets_level1
#print axioms CMHodge.reps_in_rest
#print axioms CMHodge.rest_cover
#print axioms CMHodge.reps_distinct_orbits
#print axioms CMHodge.pat_values
#print axioms CMHodge.pat_deg_prim
#print axioms CMHodge.pat_not_S
#print axioms CMHodge.pat_two_of_three
#print axioms CMHodge.cls_reps
#print axioms CMHodge.deg_prim_cover
#print axioms CMHodge.reciprocity_S
#print axioms CMHodge.reciprocity_P1
#print axioms CMHodge.reciprocity_P2
#print axioms CMHodge.level1_uniform
#print axioms CMHodge.card_lists
#print axioms CMHodge.codim1_A1
#print axioms CMHodge.codim2_A1
#print axioms CMHodge.codim2_A2
#print axioms CMHodge.admD_unique
#print axioms CMHodge.no_complementary_pairing_V
#print axioms CMHodge.split_weil_condition_V
