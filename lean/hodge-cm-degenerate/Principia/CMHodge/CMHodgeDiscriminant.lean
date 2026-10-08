/-
  退化 CM 型の例外類 — `F`-エルミート形式の判別式と「分裂」の証拠

  先行の計算で `ξ`（`A × E` の余次元 2 の例外ホッジ類）は 12 次元 `B = A × E³` の
  Weil 類の引き戻しであることが分かった。`F ⊂ Q(ζ_19)` は 6 次 CM 部分体、
  `F_0 = Q[θ]/(θ³+θ²−6θ−7)`（導手 19 の巡回 3 次体・disc 361・h = 1）はその総実部分体。

  判別式の枠組み（Deligne–Milne, *Hodge cycles on abelian varieties*, §4「Hermitian forms」）：
  非退化 `F`-エルミート形式 `φ` の判別式は `det[φ] ∈ F_0^*/N_{F/F_0}(F^*)` で、
  Prop 4.1（Landherr 1936）が（署名, 判別式）で同型類を決め、Cor 4.2 が
  「全ての実素点で `a_σ = b_σ` かつ `disc = (−1)^{d/2}` ⟺ `d/2` 次元の全等方部分空間が在る（＝分裂）」。

  この PC の PARI 計算（PARI のスクリプト）が出したのは次の二つである：
  (1) `A` の主偏極から来る階数 3 の `F`-エルミート形式のグラム行列式は
      `19⁵ · det φ_A = 48 + 41θ − 24θ²`（平方倍を除く。基底 `1, η, η²`・`η = ζ+ζ^{-1}`）。
  (2) `48 + 41θ − 24θ² = −(θ² − 3θ + 1)²`。

  ここで Lean にするのは **(2) の多項式恒等式とそこから出るノルムの証拠**だけである。
  幾何・代数的サイクル・ホッジ予想は一切含まない。
  `−det φ_A = 19 · ((θ²−3θ+1)/19³)² = N_{F/F_0}( ((θ²−3θ+1)/19³)·√−19 )` であり、
  `det φ_B = (−1)·det φ_A`（`C = E³` 側の階数 1 の形が `c = −1` の類）なので `disc φ_B = 1 = (−1)^{4/2}`。
-/
import Mathlib

namespace CMHodgeDisc

/-! ### `F_0 = Z[θ]/(θ³+θ²−6θ−7)` の模型（`(c₀,c₁,c₂) ↦ c₀ + c₁θ + c₂θ²`） -/

abbrev F0 := ℤ × ℤ × ℤ

def zero : F0 := (0, 0, 0)
def one : F0 := (1, 0, 0)
def th : F0 := (0, 1, 0)

def add (a b : F0) : F0 := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def neg (a : F0) : F0 := (-a.1, -a.2.1, -a.2.2)
def smul (n : ℤ) (a : F0) : F0 := (n * a.1, n * a.2.1, n * a.2.2)

/-- `θ³ = 7 + 6θ − θ²`、`θ⁴ = −7 + θ + 7θ²` で次数を落とした積。 -/
def mul (a b : F0) : F0 :=
  let p0 := a.1 * b.1
  let p1 := a.1 * b.2.1 + a.2.1 * b.1
  let p2 := a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1
  let p3 := a.2.1 * b.2.2 + a.2.2 * b.2.1
  let p4 := a.2.2 * b.2.2
  (p0 + 7 * p3 - 7 * p4, p1 + 6 * p3 + p4, p2 - p3 + 7 * p4)

/-- 模型が正しい関係式を持つこと：`θ³ + θ² − 6θ − 7 = 0`。 -/
theorem theta_rel :
    add (mul th (mul th th)) (add (mul th th) (add (smul (-6) th) (-7, 0, 0))) = zero := by
  decide

/-- 模型の積は可換。 -/
theorem mul_comm' (a b : F0) : mul a b = mul b a := by
  simp only [mul, Prod.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

/-! ### 判別式の分子と、その「マイナス平方」表示 -/

/-- `19⁵ · det φ_A` の値（PARI 出力）。 -/
def detA : F0 := (48, 41, -24)

/-- 証拠の元 `w = θ² − 3θ + 1`。 -/
def w : F0 := (1, -3, 1)

/-- **`19⁵ · det φ_A = −(θ² − 3θ + 1)²`。** -/
theorem detA_eq_neg_sq : mul w w = neg detA := by decide

/-- 上の展開形（読み手用）。 -/
theorem w_sq_value : mul w w = (-48, -41, 24) := by decide

/-! ### `det φ_B` がノルムであることの証拠

`F = F_0(√−19)` で `N_{F/F_0}(u + v√−19) = u² + 19 v²`。
`19⁶ · det φ_B = 19⁶ · (−det φ_A) = 19 · (θ²−3θ+1)²` なので、
`u = 0`・`v = −(θ²−3θ+1)` が `19⁶ · det φ_B` のノルム表示を与える。 -/

def nrm (u v : F0) : F0 := add (mul u u) (smul 19 (mul v v))

def uW : F0 := (0, 0, 0)
def vW : F0 := (-1, 3, -1)

/-- **`N_{F/F_0}(u + v√−19) = 19 · (−det φ_A)`（両辺 `19⁶` 倍した整数版）。** -/
theorem detB_is_norm : nrm uW vW = smul 19 (neg detA) := by decide

/-- 右辺の値。 -/
theorem detB_value : smul 19 (neg detA) = (-912, -779, 456) := by decide

/-! ### 有理数版（分母 `19⁵`・`19³` を入れた形） -/

abbrev F0Q := ℚ × ℚ × ℚ

def addQ (a b : F0Q) : F0Q := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def smulQ (r : ℚ) (a : F0Q) : F0Q := (r * a.1, r * a.2.1, r * a.2.2)
def negQ (a : F0Q) : F0Q := (-a.1, -a.2.1, -a.2.2)

def mulQ (a b : F0Q) : F0Q :=
  let p0 := a.1 * b.1
  let p1 := a.1 * b.2.1 + a.2.1 * b.1
  let p2 := a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1
  let p3 := a.2.1 * b.2.2 + a.2.2 * b.2.1
  let p4 := a.2.2 * b.2.2
  (p0 + 7 * p3 - 7 * p4, p1 + 6 * p3 + p4, p2 - p3 + 7 * p4)

/-- `det φ_A = (48 + 41θ − 24θ²)/19⁵`。 -/
def detAQ : F0Q := (48 / 19 ^ 5, 41 / 19 ^ 5, -24 / 19 ^ 5)

/-- `v = −(θ²−3θ+1)/19³`。 -/
def vQ : F0Q := (-1 / 19 ^ 3, 3 / 19 ^ 3, -1 / 19 ^ 3)

/-- **`det φ_B = −det φ_A = N_{F/F_0}(v·√−19) = 19 v²`。** -/
theorem detB_is_norm_Q : smulQ 19 (mulQ vQ vQ) = negQ detAQ := by
  simp only [smulQ, mulQ, negQ, detAQ, vQ, Prod.mk.injEq]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### 署名の側（再掲・自己完結のため）

`A` の `F` に関する署名は `(2,1,2,1,2,1)`、`C` の CM 型 `Ψ = {1,3,5}` を足すと全て `2`。
ゆえに `B` の `F`-エルミート形式は 3 つの実素点すべてで `a_σ = b_σ = 2`（`d = 4`）。 -/

def SM : ℕ := 65919
def bit (m i : ℕ) : ℕ := (m >>> (i % 18)) &&& 1
def nA (k : ℕ) : ℕ := ((List.range 18).map (fun i => if i % 6 = k % 6 then bit SM i else 0)).sum
def PsiM : ℕ := 42
def bit6 (m i : ℕ) : ℕ := (m >>> (i % 6)) &&& 1
def nB (k : ℕ) : ℕ := nA k + bit6 PsiM k

theorem nA_values : (List.range 6).map nA = [2, 1, 2, 1, 2, 1] := by decide
theorem psi_is_odd : (List.range 6).map (bit6 PsiM) = [0, 1, 0, 1, 0, 1] := by decide
theorem nB_all_two : (List.range 6).map nB = [2, 2, 2, 2, 2, 2] := by decide

/-- `d = 4` のとき Cor 4.2 の判別式の目標値は `(−1)^{d/2} = 1`。 -/
theorem split_target : (-1 : ℤ) ^ (4 / 2) = 1 := by decide

end CMHodgeDisc

#print axioms CMHodgeDisc.theta_rel
#print axioms CMHodgeDisc.mul_comm'
#print axioms CMHodgeDisc.detA_eq_neg_sq
#print axioms CMHodgeDisc.w_sq_value
#print axioms CMHodgeDisc.detB_is_norm
#print axioms CMHodgeDisc.detB_value
#print axioms CMHodgeDisc.detB_is_norm_Q
#print axioms CMHodgeDisc.nA_values
#print axioms CMHodgeDisc.psi_is_odd
#print axioms CMHodgeDisc.nB_all_two
#print axioms CMHodgeDisc.split_target
