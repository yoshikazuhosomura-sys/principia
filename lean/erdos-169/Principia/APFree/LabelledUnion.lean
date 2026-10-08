/-
  エルデシュ問題 #169（3-AP を含まない集合の逆数和）の「非チェーン型の続け方」。

  自然哲学の索引に残っていた宿題：
    「枝ごとに縮小率が違う族の AP-free 条件／桁分解が効かない」。

   で紙に書いた十分条件を、ここで機械検査する。

  【定理D（剰余標識の定理）】
    A = ⋃_i B_i と分解し、q ≥ 2 に対して各 B_i が mod q でただ一つの剰余 τ_i を取るとする。
    剰余の族 {τ_i} が ZMod q の中で「非定数 3-AP を含まない」かつ相異なるなら、
    3-AP は一つの枝の中にしか入れない。よって各 B_i が 3-AP-free なら A も 3-AP-free。

  【要点】この論法は **桁分解を使わない**。使うのは剰余写像 ℤ → ZMod q ただ一つで、
    各枝の縮小率 c_i は互いに違ってよい（q の倍数でありさえすればよい）。
    記事 erdos-169.html の十分条件は c_i がすべて等しい場合（q = c）に当たる。

  【 の自己訂正 E-110 について】
    最初に紙に書いた形は「t_i mod q が相異なり Salem–Spencer」だけを課していた。
    これは誤りで、A は ⋃ B_i のほかに「どの枝にも属さない 0」を持ちうる。
    (t,c) = ([4,2],[6,15]), q=3 で 3-AP (0,2,4) が出る。
    下の形式化では A を ⋃ B_i **そのもの**と定義するので、この穴は構文的に塞がれている。
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace APFree.LabelledUnion

/-- 集合 S が 3-AP を含まない（自明な x = z を除く）。 -/
def IsThreeAPFree (S : Set ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z

/-! ### 1. 剰余標識の定理（本体） -/

/-- **定理D**：mod q の剰余が枝を識別し、剰余の族が非定数 3-AP を持たないなら、
3-AP は一つの枝の中にしか存在しえない。 -/
theorem apfree_iUnion_of_label {ι : Type*} (q : ℕ) (B : ι → Set ℤ) (τ : ι → ZMod q)
    (hlab : ∀ i, ∀ x ∈ B i, (x : ZMod q) = τ i)
    (hSS : ∀ i j k, τ i + τ k = 2 * τ j → i = j)
    (hbr : ∀ i, IsThreeAPFree (B i)) :
    IsThreeAPFree (⋃ i, B i) := by
  rintro x hx y hy z hz hxyz
  simp only [Set.mem_iUnion] at hx hy hz
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  obtain ⟨k, hk⟩ := hz
  -- 剰余を取る
  have hcast : ((x : ZMod q)) + ((z : ZMod q)) = 2 * ((y : ZMod q)) := by
    have := congrArg (fun n : ℤ => (n : ZMod q)) hxyz
    push_cast at this
    exact this
  rw [hlab i x hi, hlab j y hj, hlab k z hk] at hcast
  have hij : i = j := hSS i j k hcast
  have hkj : k = j := hSS k j i (by rw [add_comm]; exact hcast)
  rw [hij] at hi
  rw [hkj] at hk
  exact hbr j x hi y hj z hk hxyz

/-! ### 2. 仮説 hSS を「単射 ＋ Salem–Spencer」から作る -/

/-- 剰余が相異なり、その像が ZMod q の中で非定数 3-AP を含まないなら hSS が従う。 -/
theorem label_ss {ι : Type*} (q : ℕ) (τ : ι → ZMod q)
    (hinj : Function.Injective τ)
    (hset : ∀ i j k, τ i + τ k = 2 * τ j → τ i = τ j) :
    ∀ i j k, τ i + τ k = 2 * τ j → i = j :=
  fun i j k h => hinj (hset i j k h)

/-! ### 3. 枝：B = t + c·A（縮小率 c は枝ごとに違ってよい） -/

/-- 枝の定義。 -/
def block (t c : ℤ) (A : Set ℤ) : Set ℤ := (fun a => t + c * a) '' A

/-- 縮小して平行移動しても 3-AP-free は保たれる（c ≠ 0）。 -/
theorem apfree_block {t c : ℤ} (hc : c ≠ 0) {A : Set ℤ} (hA : IsThreeAPFree A) :
    IsThreeAPFree (block t c A) := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ z ⟨d, hd, rfl⟩ h
  have : c * (a + d) = c * (2 * b) := by ring_nf; ring_nf at h; linarith
  have had : a + d = 2 * b := by
    have := mul_left_cancel₀ hc this; linarith
  have : a = d := hA a ha b hb d hd had
  rw [this]

/-- **q が縮小率 c を割るなら、枝は mod q でただ一つの剰余 t を取る。**
    ここが「桁分解の代わり」である。c は枝ごとに違ってよい。 -/
theorem block_label (q : ℕ) (t c : ℤ) (hq : (q : ℤ) ∣ c) (A : Set ℤ) :
    ∀ x ∈ block t c A, (x : ZMod q) = (t : ZMod q) := by
  rintro x ⟨a, _, rfl⟩
  obtain ⟨m, rfl⟩ := hq
  push_cast
  simp

/-! ### 4. まとめ — 縮小率がばらばらでよい十分条件 -/

/-- **主結果（定理D の機械検査済みの形）**
    枝ごとに縮小率 c i が違ってよい。要求は
      (a) q ≥ 2 が全ての c i を割る、(b) 剰余 t i mod q が相異なる、
      (c) 剰余の族が ZMod q の中で非定数 3-AP を含まない、(d) 各 A i が 3-AP-free。 -/
theorem apfree_mixed_ratio {ι : Type*} (q : ℕ) (t c : ι → ℤ) (A : ι → Set ℤ)
    (hc : ∀ i, c i ≠ 0)
    (hdvd : ∀ i, (q : ℤ) ∣ c i)
    (hinj : Function.Injective (fun i => ((t i : ℤ) : ZMod q)))
    (hset : ∀ i j k, ((t i : ℤ) : ZMod q) + ((t k : ℤ) : ZMod q)
              = 2 * ((t j : ℤ) : ZMod q) → ((t i : ℤ) : ZMod q) = ((t j : ℤ) : ZMod q))
    (hA : ∀ i, IsThreeAPFree (A i)) :
    IsThreeAPFree (⋃ i, block (t i) (c i) (A i)) :=
  apfree_iUnion_of_label q _ (fun i => ((t i : ℤ) : ZMod q))
    (fun i => block_label q (t i) (c i) (hdvd i) (A i))
    (label_ss q _ hinj hset)
    (fun i => apfree_block (hc i) (hA i))

/-! ### 5. 具体例 — 縮小率が実際に違う族 -/

/-- の数値検証で使った族の骨格：q = 3、剰余 (0,1)、縮小率 (3,9)。
    剰余の族 {0,1} ⊆ ZMod 3 は非定数 3-AP を含まない。 -/
example : ∀ a b c : Fin 2, (![(0 : ZMod 3), 1]) a + (![(0 : ZMod 3), 1]) c
    = 2 * (![(0 : ZMod 3), 1]) b → (![(0 : ZMod 3), 1]) a = (![(0 : ZMod 3), 1]) b := by
  decide

/-- 剰余 (0,1) は単射。 -/
example : Function.Injective (![(0 : ZMod 3), 1]) := by decide

/-- 縮小率は違ってよい：3 と 9 はどちらも 3 の倍数。 -/
example : ((3 : ℕ) : ℤ) ∣ 3 ∧ ((3 : ℕ) : ℤ) ∣ 9 := by norm_num

/-- 対照（E-110 の反例の核）：剰余 (0,1,2) ⊆ ZMod 3 は非定数 3-AP を含む。
    ＝ 0 を枝の外に置くと条件が崩れる、という の自己訂正の中身。 -/
example : ¬ (∀ a b c : Fin 3, (![(0 : ZMod 3), 1, 2]) a + (![(0 : ZMod 3), 1, 2]) c
    = 2 * (![(0 : ZMod 3), 1, 2]) b → (![(0 : ZMod 3), 1, 2]) a = (![(0 : ZMod 3), 1, 2]) b) := by
  decide

end APFree.LabelledUnion

/-! ### 公理の確認 -/

#print axioms APFree.LabelledUnion.apfree_iUnion_of_label
#print axioms APFree.LabelledUnion.apfree_mixed_ratio
