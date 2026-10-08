import Mathlib
import Principia.GeneralizedPetersen.Base
import Principia.GeneralizedPetersen.Blocks
import Principia.GeneralizedPetersen.Count

/-!
# Principia.GeneralizedPetersen.Descent

  ダーツ、向き付き 2 因子 `hamTF` とその商への降下、巻き数の場合分け、
  三つの橋 `DartBridge`・`WindingBridge`・`CycleBridge`、跡付け、主定理 `gp3_dvd_hc_odd`。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.Descent

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### 1. ダーツの `Nodup` と、逆向きのダーツが同居しないこと -/

/-- 小道（`IsTrail`）のダーツは `Nodup`（辺が `Nodup` なので）。 -/
theorem darts_nodup_of_isTrail {u v : V} {p : G.Walk u v} (h : p.IsTrail) : p.darts.Nodup :=
  List.Nodup.of_map Dart.edge (by rw [← Walk.edges_eq_map_darts]; exact h.edges_nodup)

/-- 小道では、辺が等しいダーツは等しい。 -/
theorem dart_eq_of_edge_eq {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {δ δ' : G.Dart} (hδ : δ ∈ p.darts) (hδ' : δ' ∈ p.darts) (he : δ.edge = δ'.edge) : δ = δ' := by
  have hn : (p.darts.map Dart.edge).Nodup := by rw [← Walk.edges_eq_map_darts]; exact h.edges_nodup
  exact List.inj_on_of_nodup_map hn hδ hδ' he

/-- **逆向きのダーツは同居しない**：`δ ∈ darts` なら `δ.symm ∉ darts`。 -/
theorem symm_notMem_darts {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {δ : G.Dart} (hδ : δ ∈ p.darts) : δ.symm ∉ p.darts := by
  intro hs
  have he : δ.edge = δ.symm.edge := (Dart.edge_symm δ).symm
  have := dart_eq_of_edge_eq h hδ hs he
  have h2 := congrArg (fun d : G.Dart => d.fst) this
  exact δ.adj.ne (by simp at h2)

/-! ### 2. 出るダーツ・入るダーツの一意性 -/

/-- 閉路では、始点 `fst` が等しいダーツは等しい。 -/
theorem dart_eq_of_fst_eq {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    {δ δ' : G.Dart} (hδ : δ ∈ p.darts) (hδ' : δ' ∈ p.darts) (he : δ.fst = δ'.fst) : δ = δ' := by
  have hn : (p.darts.map (fun d : G.Dart => d.fst)).Nodup := by
    rw [Walk.map_fst_darts]; exact hp.nodup_dropLast_support
  exact List.inj_on_of_nodup_map hn hδ hδ' he

/-- 閉路では、終点 `snd` が等しいダーツは等しい。 -/
theorem dart_eq_of_snd_eq {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    {δ δ' : G.Dart} (hδ : δ ∈ p.darts) (hδ' : δ' ∈ p.darts) (he : δ.snd = δ'.snd) : δ = δ' := by
  have hn : (p.darts.map (fun d : G.Dart => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]; exact hp.support_nodup
  exact List.inj_on_of_nodup_map hn hδ hδ' he

/-- 台の各頂点から出るダーツがある。 -/
theorem exists_out_dart {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    ∃ δ ∈ p.darts, δ.fst = v := by
  rw [← Walk.dropLast_support_concat p, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · rw [← Walk.map_fst_darts] at hv
    obtain ⟨δ, hδ, hδv⟩ := List.mem_map.mp hv
    exact ⟨δ, hδ, hδv⟩
  · cases p with
    | nil => exact absurd rfl hp.ne_nil
    | cons h q => exact ⟨⟨(_, _), h⟩, List.mem_cons_self, rfl⟩

/-- 台の各頂点に入るダーツがある。 -/
theorem exists_in_dart {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    ∃ δ ∈ p.darts, δ.snd = v := by
  have hv' : v ∈ p.support.tail := by
    rw [← Walk.cons_tail_support p, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Walk.end_mem_tail_support hp.not_nil
    · exact hv
  rw [← Walk.map_snd_darts] at hv'
  obtain ⟨δ, hδ, hδv⟩ := List.mem_map.mp hv'
  exact ⟨δ, hδ, hδv⟩

/-! ### 3. 局所構造 -/

/-- **閉路の局所構造**：台の各頂点 `v` に、出るダーツ `δo`・入るダーツ `δi` がちょうど一つずつあり、
  `δo` の行き先と `δi` の来し方は異なる（＝`v` に接する閉路の辺はちょうど 2 本）。 -/
theorem cycle_local {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    ∃ δo ∈ p.darts, ∃ δi ∈ p.darts, δo.fst = v ∧ δi.snd = v ∧ δo.snd ≠ δi.fst ∧
      (∀ δ ∈ p.darts, δ.fst = v → δ = δo) ∧ (∀ δ ∈ p.darts, δ.snd = v → δ = δi) := by
  obtain ⟨δo, ho, hov⟩ := exists_out_dart hp hv
  obtain ⟨δi, hi, hiv⟩ := exists_in_dart hp hv
  refine ⟨δo, ho, δi, hi, hov, hiv, ?_, ?_, ?_⟩
  · intro hc
    -- `δi = δo.symm` になり、逆向きの同居に反する
    have hsym : δi = δo.symm := by
      apply Dart.ext
      simp only [Dart.symm_toProd, Prod.swap]
      exact Prod.ext hc.symm (by rw [hiv, hov])
    exact symm_notMem_darts hp.isCircuit.isTrail ho (hsym ▸ hi)
  · intro δ hδ hδv
    exact dart_eq_of_fst_eq hp hδ ho (by rw [hδv, hov])
  · intro δ hδ hδv
    exact dart_eq_of_snd_eq hp hδ hi (by rw [hδv, hiv])

/-! ### 4. 「ダーツがある」を頂点対で言う -/

/-- 歩道 `p` が `x` から `y` へのダーツを持つ。 -/
def HasDart {u v : V} (p : G.Walk u v) (x y : V) : Prop := ∃ δ ∈ p.darts, δ.fst = x ∧ δ.snd = y

instance [DecidableEq V] {u v : V} (p : G.Walk u v) (x y : V) : Decidable (HasDart p x y) := by
  unfold HasDart; infer_instance

theorem hasDart_iff {u v : V} (p : G.Walk u v) (x y : V) :
    HasDart p x y ↔ ∃ δ ∈ p.darts, δ.fst = x ∧ δ.snd = y := Iff.rfl

/-- ダーツがあれば隣接している。 -/
theorem HasDart.adj {u v : V} {p : G.Walk u v} {x y : V} (h : HasDart p x y) : G.Adj x y := by
  obtain ⟨δ, -, rfl, rfl⟩ := h
  exact δ.adj

/-- ダーツがあれば辺がある。 -/
theorem HasDart.edge_mem {u v : V} {p : G.Walk u v} {x y : V} (h : HasDart p x y) :
    s(x, y) ∈ p.edges := by
  obtain ⟨δ, hδ, rfl, rfl⟩ := h
  rw [Walk.edges_eq_map_darts]
  exact List.mem_map.mpr ⟨δ, hδ, rfl⟩

/-- 逆向きは同居しない（`HasDart` 版）。 -/
theorem HasDart.not_rev {u v : V} {p : G.Walk u v} (h : p.IsTrail) {x y : V}
    (hxy : HasDart p x y) : ¬ HasDart p y x := by
  rintro ⟨δ', hδ', h1, h2⟩
  obtain ⟨δ, hδ, rfl, rfl⟩ := hxy
  have : δ' = δ.symm := by
    apply Dart.ext
    simp only [Dart.symm_toProd, Prod.swap]
    exact Prod.ext h1 h2
  exact symm_notMem_darts h hδ (this ▸ hδ')

/-- 辺があれば、どちらかの向きのダーツがある。 -/
theorem hasDart_of_edge_mem {u v : V} {p : G.Walk u v} {x y : V} (h : s(x, y) ∈ p.edges) :
    HasDart p x y ∨ HasDart p y x := by
  rw [Walk.edges_eq_map_darts] at h
  obtain ⟨δ, hδ, he⟩ := List.mem_map.mp h
  have he' : s(δ.fst, δ.snd) = s(x, y) := he
  rw [Sym2.eq_iff] at he'
  rcases he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨δ, hδ, h1, h2⟩
  · exact Or.inr ⟨δ, hδ, h1, h2⟩

/-- **閉路の局所構造（`HasDart` 版）**：`v` から出る先はちょうど一つ、`v` に入る元もちょうど一つ、
  そして両者は異なる。 -/
theorem cycle_local' {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    ∃ a b : V, a ≠ b ∧ (∀ y, HasDart p v y ↔ y = a) ∧ (∀ x, HasDart p x v ↔ x = b) := by
  obtain ⟨δo, ho, δi, hi, hov, hiv, hne, huo, hui⟩ := cycle_local hp hv
  refine ⟨δo.snd, δi.fst, hne, ?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨δ, hδ, h1, h2⟩
      rw [← h2, huo δ hδ h1]
    · rintro rfl
      exact ⟨δo, ho, hov, rfl⟩
  · intro x
    constructor
    · rintro ⟨δ, hδ, h1, h2⟩
      rw [← h1, hui δ hδ h2]
    · rintro rfl
      exact ⟨δi, hi, rfl, hiv⟩

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open Finset GeneralizedPetersen.Base

/-! ### 1. 巻き数を仮定しない 2 因子 -/

/-- 商グラフ `GP(d,3)` の向き付き 2 因子（巻き数の仮定なし）。 -/
structure TwoFactor (d : ℕ) extends Flow d where
  o_mem : ∀ j, o j = 0 ∨ o j = 1 ∨ o j = -1
  i_mem : ∀ j, i j = 0 ∨ i j = 1 ∨ i j = -1
  degO : ∀ j, |o (j - 1)| + |o j| + |sp j| = 2
  degI : ∀ j, |i (j - 3)| + |i j| + |sp j| = 2

namespace TwoFactor

variable {d : ℕ}

/-- 外辺の欠けの個数 `p`。 -/
def p (T : TwoFactor d) [NeZero d] : ℕ := (Finset.univ.filter (fun j : ZMod d => T.o j = 0)).card

/-- 内辺の欠けの個数 `q`。 -/
def q (T : TwoFactor d) [NeZero d] : ℕ := (Finset.univ.filter (fun j : ZMod d => T.i j = 0)).card

/-- `Σ |o| = d − p`。 -/
theorem sum_abs_o (T : TwoFactor d) [NeZero d] : ∑ j : ZMod d, |T.o j| = (d : ℤ) - (T.p : ℤ) := by
  have : ∀ j : ZMod d, |T.o j| = 1 - (if T.o j = 0 then (1 : ℤ) else 0) := by
    intro j
    rcases T.o_mem j with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, Finset.sum_boole]
  simp [p]

/-- `Σ |i| = d − q`。 -/
theorem sum_abs_i (T : TwoFactor d) [NeZero d] : ∑ j : ZMod d, |T.i j| = (d : ℤ) - (T.q : ℤ) := by
  have : ∀ j : ZMod d, |T.i j| = 1 - (if T.i j = 0 then (1 : ℤ) else 0) := by
    intro j
    rcases T.i_mem j with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, Finset.sum_boole]
  simp [q]

/-- スポークの本数を外側と内側から数えて `p = q`（`Base` の `Win.p_eq_q` と同じ証明。`w2` は使わない）。 -/
theorem p_eq_q (T : TwoFactor d) [NeZero d] : T.p = T.q := by
  have hO : ∑ j : ZMod d, (|T.o (j - 1)| + |T.o j| + |T.sp j|) = 2 * (d : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ => T.degO j), Finset.sum_const, Finset.card_univ, ZMod.card]
    simp [mul_comm]
  have hI : ∑ j : ZMod d, (|T.i (j - 3)| + |T.i j| + |T.sp j|) = 2 * (d : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ => T.degI j), Finset.sum_const, Finset.card_univ, ZMod.card]
    simp [mul_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift (fun j => |T.o j|) (1 : ZMod d)] at hO
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift (fun j => |T.i j|) (3 : ZMod d)] at hI
  have habs : ∑ j : ZMod d, |T.o j| = ∑ j : ZMod d, |T.i j| := by linarith
  rw [T.sum_abs_o, T.sum_abs_i] at habs
  omega

/-! ### 2. 補題：`|Σ| ≤ 4(d − p)`・`Σ` 偶 -/

/-- `Σ o` と `Σ |o|` の差は偶数。 -/
theorem sum_o_parity (T : TwoFactor d) [NeZero d] :
    Even (∑ j : ZMod d, T.o j - ∑ j : ZMod d, |T.o j|) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.even_sum _ (fun j _ => ?_)
  rcases T.o_mem j with h | h | h <;> simp [h]

theorem sum_i_parity (T : TwoFactor d) [NeZero d] :
    Even (∑ j : ZMod d, T.i j - ∑ j : ZMod d, |T.i j|) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.even_sum _ (fun j _ => ?_)
  rcases T.i_mem j with h | h | h <;> simp [h]

/-- **総変位の評価**：`w` が巻き数（`W ≡ w`）なら `|d w| ≤ 4 (d − p)`。 -/
theorem abs_winding_le (T : TwoFactor d) [NeZero d] (w : ℤ) (hw : ∀ j, T.toFlow.W j = w) :
    |(d : ℤ) * w| ≤ 4 * ((d : ℤ) - T.p) := by
  have h := T.toFlow.winding w hw
  have h1 : |∑ j : ZMod d, T.o j| ≤ ∑ j : ZMod d, |T.o j| := Finset.abs_sum_le_sum_abs _ _
  have h2 : |∑ j : ZMod d, T.i j| ≤ ∑ j : ZMod d, |T.i j| := Finset.abs_sum_le_sum_abs _ _
  rw [T.sum_abs_o] at h1
  rw [T.sum_abs_i, ← T.p_eq_q] at h2
  rw [h]
  calc |∑ j : ZMod d, T.o j + 3 * ∑ j : ZMod d, T.i j|
      ≤ |∑ j : ZMod d, T.o j| + |3 * ∑ j : ZMod d, T.i j| := abs_add_le _ _
    _ = |∑ j : ZMod d, T.o j| + 3 * |∑ j : ZMod d, T.i j| := by
        rw [abs_mul]; norm_num
    _ ≤ 4 * ((d : ℤ) - T.p) := by linarith

/-- **総変位は偶数**：`d w` は偶数。 -/
theorem even_winding (T : TwoFactor d) [NeZero d] (w : ℤ) (hw : ∀ j, T.toFlow.W j = w) :
    Even ((d : ℤ) * w) := by
  have h := T.toFlow.winding w hw
  obtain ⟨a, ha⟩ := T.sum_o_parity
  obtain ⟨b, hb⟩ := T.sum_i_parity
  have ho := T.sum_abs_o
  have hi := T.sum_abs_i
  have hpq := T.p_eq_q
  refine ⟨2 * (d : ℤ) - 2 * T.p + a + 3 * b, ?_⟩
  rw [h]
  have hq : (T.q : ℤ) = T.p := by exact_mod_cast hpq.symm
  linear_combination ha + 3 * hb + ho + 3 * hi - 3 * hq

/-- **`d` 奇・`p ≥ 1` なら巻き数は `0` か `±2`**（紙の証明の「`w ∈ {0, ±2}`」）。 -/
theorem winding_cases (T : TwoFactor d) [NeZero d] (hodd : Odd d) (hp : 0 < T.p)
    (w : ℤ) (hw : ∀ j, T.toFlow.W j = w) : w = 0 ∨ w = 2 ∨ w = -2 := by
  have hle := T.abs_winding_le w hw
  have hev := T.even_winding w hw
  have hdpos : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hp' : (1 : ℤ) ≤ T.p := by exact_mod_cast hp
  -- `|w| ≤ 3`
  have hw3 : |w| ≤ 3 := by
    by_contra hc
    have h4 : 4 ≤ |w| := by have := not_le.mp hc; omega
    have : (d : ℤ) * 4 ≤ |(d : ℤ) * w| := by
      rw [abs_mul, abs_of_pos hdpos]
      exact mul_le_mul_of_nonneg_left h4 hdpos.le
    linarith
  -- `w` は偶数
  have hwe : Even w := by
    rcases Int.even_mul.mp hev with hd | hw
    · exfalso
      have : Even d := by exact_mod_cast hd
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · exact hw
  obtain ⟨k, hk⟩ := hwe
  rw [abs_le] at hw3
  omega

/-! ### 3. 向きの反転と `Win d` の構成 -/

/-- 向きの反転：すべての流量の符号を変える。 -/
def neg (T : TwoFactor d) : TwoFactor d where
  o := fun j => -T.o j
  i := fun j => -T.i j
  sp := fun j => -T.sp j
  outer := fun j => by have := T.outer j; linarith
  inner := fun j => by have := T.inner j; linarith
  o_mem := fun j => by rcases T.o_mem j with h | h | h <;> simp [h]
  i_mem := fun j => by rcases T.i_mem j with h | h | h <;> simp [h]
  degO := fun j => by have := T.degO j; simpa [abs_neg] using this
  degI := fun j => by have := T.degI j; simpa [abs_neg] using this

theorem neg_W (T : TwoFactor d) (j : ZMod d) : T.neg.toFlow.W j = -T.toFlow.W j := by
  simp only [Flow.W, neg]
  ring

/-- 巻き数 `2` の 2 因子は `Win d`。 -/
def toWin (T : TwoFactor d) (hw : ∀ j, T.toFlow.W j = 2) : Win d :=
  { T with w2 := hw }

/-- **`w ≠ 0` なら `Win d` が作れる**（`w = −2` なら反転する）。得られる `F` の流量は
  `T` のものと一致するか、すべて符号が反対か。 -/
theorem exists_win (T : TwoFactor d) [NeZero d] (hodd : Odd d) (hp : 0 < T.p)
    (w : ℤ) (hw : ∀ j, T.toFlow.W j = w) (hw0 : w ≠ 0) :
    ∃ F : Win d, (∀ j, F.o j = T.o j ∧ F.i j = T.i j ∧ F.sp j = T.sp j) ∨
      (∀ j, F.o j = -T.o j ∧ F.i j = -T.i j ∧ F.sp j = -T.sp j) := by
  rcases T.winding_cases hodd hp w hw with h0 | h2 | h2
  · exact absurd h0 hw0
  · subst h2
    exact ⟨T.toWin hw, Or.inl (fun j => ⟨rfl, rfl, rfl⟩)⟩
  · subst h2
    refine ⟨T.neg.toWin (fun j => by rw [T.neg_W, hw j]; norm_num), ?_⟩
    exact Or.inr (fun j => ⟨rfl, rfl, rfl⟩)

end TwoFactor

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks

variable {n : ℕ} {u : V n}

/-! ### 1. ダーツの指示関数と三つの流量 -/

/-- ダーツの指示関数。 -/
def ind (p : (GP n 3).Walk u u) (x y : V n) : ℤ := if HasDart p x y then 1 else 0

theorem ind_nonneg (p : (GP n 3).Walk u u) (x y : V n) : 0 ≤ ind p x y := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (p : (GP n 3).Walk u u) (x y : V n) : ind p x y ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem ind_eq_zero_iff (p : (GP n 3).Walk u u) (x y : V n) : ind p x y = 0 ↔ ¬ HasDart p x y := by
  unfold ind; split_ifs with h <;> simp [h]

theorem ind_eq_one_iff (p : (GP n 3).Walk u u) (x y : V n) : ind p x y = 1 ↔ HasDart p x y := by
  unfold ind; split_ifs with h <;> simp [h]

/-- 逆向きは同居しないので、`ind x y · ind y x = 0`。 -/
theorem ind_mul_rev (p : (GP n 3).Walk u u) (hp : p.IsTrail) (x y : V n) :
    ind p x y = 0 ∨ ind p y x = 0 := by
  by_cases h : HasDart p x y
  · exact Or.inr ((ind_eq_zero_iff p y x).mpr (h.not_rev hp))
  · exact Or.inl ((ind_eq_zero_iff p x y).mpr h)

/-- `|ind x y − ind y x| = ind x y + ind y x`。 -/
theorem abs_ind_sub (p : (GP n 3).Walk u u) (hp : p.IsTrail) (x y : V n) :
    |ind p x y - ind p y x| = ind p x y + ind p y x := by
  have h1 := ind_nonneg p x y
  have h2 := ind_nonneg p y x
  have h3 := ind_le_one p x y
  have h4 := ind_le_one p y x
  rcases ind_mul_rev p hp x y with h | h <;> rw [h] <;> simp <;> omega

/-- 差は `{0, ±1}`。 -/
theorem ind_sub_mem (p : (GP n 3).Walk u u) (hp : p.IsTrail) (x y : V n) :
    ind p x y - ind p y x = 0 ∨ ind p x y - ind p y x = 1 ∨ ind p x y - ind p y x = -1 := by
  have h1 := ind_nonneg p x y
  have h2 := ind_nonneg p y x
  have h3 := ind_le_one p x y
  have h4 := ind_le_one p y x
  rcases ind_mul_rev p hp x y with h | h <;> rw [h] <;> omega

/-- 外辺 `{j, j+1}` の流量。 -/
def oW (p : (GP n 3).Walk u u) (j : ZMod n) : ℤ :=
  ind p (j, false) (j + 1, false) - ind p (j + 1, false) (j, false)

/-- 内辺 `{j, j+3}` の流量。 -/
def iW (p : (GP n 3).Walk u u) (j : ZMod n) : ℤ :=
  ind p (j, true) (j + 3, true) - ind p (j + 3, true) (j, true)

/-- スポーク `O_j → I_j` の流量。 -/
def spW (p : (GP n 3).Walk u u) (j : ZMod n) : ℤ :=
  ind p (j, false) (j, true) - ind p (j, true) (j, false)

/-! ### 2. 隣は三つ -/

theorem out_nbr_O (p : (GP n 3).Walk u u) (j : ZMod n) {y : V n} (hy : HasDart p (j, false) y) :
    y = (j + 1, false) ∨ y = (j - 1, false) ∨ y = (j, true) := by
  rcases GP_neighbor n 3 j false y hy.adj with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

theorem in_nbr_O (p : (GP n 3).Walk u u) (j : ZMod n) {y : V n} (hy : HasDart p y (j, false)) :
    y = (j + 1, false) ∨ y = (j - 1, false) ∨ y = (j, true) := by
  rcases GP_neighbor n 3 j false y hy.adj.symm with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

theorem out_nbr_I (p : (GP n 3).Walk u u) (j : ZMod n) {y : V n} (hy : HasDart p (j, true) y) :
    y = (j + 3, true) ∨ y = (j - 3, true) ∨ y = (j, false) := by
  rcases GP_neighbor n 3 j true y hy.adj with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h (by decide)
  · simpa using h

theorem in_nbr_I (p : (GP n 3).Walk u u) (j : ZMod n) {y : V n} (hy : HasDart p y (j, true)) :
    y = (j + 3, true) ∨ y = (j - 3, true) ∨ y = (j, false) := by
  rcases GP_neighbor n 3 j true y hy.adj.symm with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h (by decide)
  · simpa using h

/-! ### 3. 三つの隣への出入りの和は 1 -/

/-- 出るダーツはちょうど一つ：三つの（相異なる）候補への指示関数の和は 1。 -/
theorem ind_out_sum (p : (GP n 3).Walk u u) (hp : p.IsCycle) {v : V n} (hv : v ∈ p.support)
    (y1 y2 y3 : V n) (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3)
    (hnb : ∀ y, HasDart p v y → y = y1 ∨ y = y2 ∨ y = y3) :
    ind p v y1 + ind p v y2 + ind p v y3 = 1 := by
  obtain ⟨a, b, -, hout, -⟩ := cycle_local' hp hv
  have ha := hnb a ((hout a).mpr rfl)
  simp only [ind, hout]
  rcases ha with rfl | rfl | rfl <;> simp [h12, h13, h23, h12.symm, h13.symm, h23.symm]

/-- 入るダーツはちょうど一つ。 -/
theorem ind_in_sum (p : (GP n 3).Walk u u) (hp : p.IsCycle) {v : V n} (hv : v ∈ p.support)
    (y1 y2 y3 : V n) (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3)
    (hnb : ∀ y, HasDart p y v → y = y1 ∨ y = y2 ∨ y = y3) :
    ind p y1 v + ind p y2 v + ind p y3 v = 1 := by
  obtain ⟨a, b, -, -, hin⟩ := cycle_local' hp hv
  have hb := hnb b ((hin b).mpr rfl)
  simp only [ind, hin]
  rcases hb with rfl | rfl | rfl <;> simp [h12, h13, h23, h12.symm, h13.symm, h23.symm]

theorem ne_pm_one (h2 : (2 : ZMod n) ≠ 0) (j : ZMod n) : (j + 1, false) ≠ (j - 1, false) := by
  intro h
  have h1 : j + 1 = j - 1 := congrArg Prod.fst h
  exact h2 (by linear_combination h1)

theorem ne_pm_three (h6 : (6 : ZMod n) ≠ 0) (j : ZMod n) : (j + 3, true) ≠ (j - 3, true) := by
  intro h
  have h1 : j + 3 = j - 3 := congrArg Prod.fst h
  exact h6 (by linear_combination h1)

/-! ### 4. 流量保存と次数 -/

theorem outer_cons (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (j : ZMod n) : oW p j - oW p (j - 1) + spW p j = 0 := by
  have hout := ind_out_sum p hp.isCycle (hp.mem_support (j, false)) (j + 1, false) (j - 1, false)
    (j, true) (ne_pm_one h2 j) (by simp) (by simp) (fun _ hy => out_nbr_O p j hy)
  have hin := ind_in_sum p hp.isCycle (hp.mem_support (j, false)) (j + 1, false) (j - 1, false)
    (j, true) (ne_pm_one h2 j) (by simp) (by simp) (fun _ hy => in_nbr_O p j hy)
  simp only [oW, spW]
  rw [show (j - 1 + 1 : ZMod n) = j by ring]
  linarith

theorem inner_cons (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h6 : (6 : ZMod n) ≠ 0)
    (j : ZMod n) : iW p j - iW p (j - 3) - spW p j = 0 := by
  have hout := ind_out_sum p hp.isCycle (hp.mem_support (j, true)) (j + 3, true) (j - 3, true)
    (j, false) (ne_pm_three h6 j) (by simp) (by simp) (fun _ hy => out_nbr_I p j hy)
  have hin := ind_in_sum p hp.isCycle (hp.mem_support (j, true)) (j + 3, true) (j - 3, true)
    (j, false) (ne_pm_three h6 j) (by simp) (by simp) (fun _ hy => in_nbr_I p j hy)
  simp only [iW, spW]
  rw [show (j - 3 + 3 : ZMod n) = j by ring]
  linarith

theorem degO_eq (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (j : ZMod n) : |oW p (j - 1)| + |oW p j| + |spW p j| = 2 := by
  have ht := hp.isCycle.isCircuit.isTrail
  have hout := ind_out_sum p hp.isCycle (hp.mem_support (j, false)) (j + 1, false) (j - 1, false)
    (j, true) (ne_pm_one h2 j) (by simp) (by simp) (fun _ hy => out_nbr_O p j hy)
  have hin := ind_in_sum p hp.isCycle (hp.mem_support (j, false)) (j + 1, false) (j - 1, false)
    (j, true) (ne_pm_one h2 j) (by simp) (by simp) (fun _ hy => in_nbr_O p j hy)
  simp only [oW, spW]
  rw [show (j - 1 + 1 : ZMod n) = j by ring, abs_ind_sub p ht, abs_ind_sub p ht, abs_ind_sub p ht]
  linarith

theorem degI_eq (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h6 : (6 : ZMod n) ≠ 0)
    (j : ZMod n) : |iW p (j - 3)| + |iW p j| + |spW p j| = 2 := by
  have ht := hp.isCycle.isCircuit.isTrail
  have hout := ind_out_sum p hp.isCycle (hp.mem_support (j, true)) (j + 3, true) (j - 3, true)
    (j, false) (ne_pm_three h6 j) (by simp) (by simp) (fun _ hy => out_nbr_I p j hy)
  have hin := ind_in_sum p hp.isCycle (hp.mem_support (j, true)) (j + 3, true) (j - 3, true)
    (j, false) (ne_pm_three h6 j) (by simp) (by simp) (fun _ hy => in_nbr_I p j hy)
  simp only [iW, spW]
  rw [show (j - 3 + 3 : ZMod n) = j by ring, abs_ind_sub p ht, abs_ind_sub p ht, abs_ind_sub p ht]
  linarith

/-- **ハミルトン閉路の上側の 2 因子** `TwoFactor n`。 -/
def hamTF (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (h6 : (6 : ZMod n) ≠ 0) : TwoFactor n where
  o := oW p
  i := iW p
  sp := spW p
  outer := outer_cons p hp h2
  inner := inner_cons p hp h6
  o_mem := fun j => ind_sub_mem p hp.isCycle.isCircuit.isTrail _ _
  i_mem := fun j => ind_sub_mem p hp.isCycle.isCircuit.isTrail _ _
  degO := degO_eq p hp h2
  degI := degI_eq p hp h6

@[simp] theorem hamTF_o (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (h6 : (6 : ZMod n) ≠ 0) (j : ZMod n) :
    (hamTF p hp h2 h6).o j = oW p j := rfl
@[simp] theorem hamTF_i (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (h6 : (6 : ZMod n) ≠ 0) (j : ZMod n) :
    (hamTF p hp h2 h6).i j = iW p j := rfl
@[simp] theorem hamTF_sp (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0)
    (h6 : (6 : ZMod n) ≠ 0) (j : ZMod n) :
    (hamTF p hp h2 h6).sp j = spW p j := rfl

/-! ### 5. 台はダーツで閉じた集合を出ない -/

/-- **閉じた集合の補題**：始点が `T` に入り、`T` がダーツで閉じていれば、台はすべて `T` に入る。 -/
theorem support_subset_of_closed {W : Type*} {G : SimpleGraph W} :
    ∀ {a b : W} (p : G.Walk a b) (T : Set W), a ∈ T →
      (∀ x y, HasDart p x y → x ∈ T → y ∈ T) → ∀ z ∈ p.support, z ∈ T := by
  intro a b p
  induction p with
  | nil =>
      intro T ha _ z hz
      rw [Walk.support_nil, List.mem_singleton] at hz
      exact hz ▸ ha
  | @cons a c b h q ih =>
      intro T ha hT z hz
      have hc : c ∈ T := hT a c ⟨⟨(a, c), h⟩, by simp [Walk.darts_cons], rfl, rfl⟩ ha
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ha
      · refine ih T hc (fun x y hxy hx => hT x y ?_ hx) z hz
        obtain ⟨δ, hδ, h1, h2⟩ := hxy
        exact ⟨δ, by simp [Walk.darts_cons, hδ], h1, h2⟩

/-- 閉じた歩道では、台の**どこか**の点が `T` に入れば台はすべて `T` に入る（`rotate` で始点を取り直す）。 -/
theorem support_subset_of_closed' {W : Type*} {G : SimpleGraph W} {a : W}
    (p : G.Walk a a) (T : Set W) {v : W} (hv : v ∈ p.support) (hvT : v ∈ T)
    (hT : ∀ x y, HasDart p x y → x ∈ T → y ∈ T) : ∀ z ∈ p.support, z ∈ T := by
  classical
  intro z hz
  by_cases hnil : p.Nil
  · -- 台は一点
    have : z = a := by
      rw [Walk.nil_iff_length_eq] at hnil
      have h1 : p.support = [a] := by
        cases p with
        | nil => rfl
        | cons _ _ => simp at hnil
      rw [h1, List.mem_singleton] at hz
      exact hz
    have hva : v = a := by
      have h1 : p.support = [a] := by
        rw [Walk.nil_iff_length_eq] at hnil
        cases p with
        | nil => rfl
        | cons _ _ => simp at hnil
      rw [h1, List.mem_singleton] at hv
      exact hv
    rw [this, ← hva]
    exact hvT
  · have hrotD : ∀ x y, HasDart (p.rotate v hv) x y → HasDart p x y := by
      rintro x y ⟨δ, hδ, h1, h2⟩
      exact ⟨δ, (Walk.rotate_darts p v hv).mem_iff.mp hδ, h1, h2⟩
    have hz' : z ∈ (p.rotate v hv).support := by
      have hzt : z ∈ p.support.tail := by
        rw [← Walk.cons_tail_support p, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Walk.end_mem_tail_support hnil
        · exact hz
      exact List.mem_of_mem_tail ((Walk.support_rotate p v hv).mem_iff.mpr hzt)
    exact support_subset_of_closed (p.rotate v hv) T hvT
      (fun x y hxy hx => hT x y (hrotD x y hxy) hx) z hz'

/-- スポークが無ければ、`O_j`・`I_j` の間にダーツは無い（`spW j = 0` ⟹ 両向きとも無い）。 -/
theorem no_spoke_of_spW_zero (p : (GP n 3).Walk u u) (hp : p.IsTrail) {j : ZMod n}
    (h : spW p j = 0) : ¬ HasDart p (j, false) (j, true) ∧ ¬ HasDart p (j, true) (j, false) := by
  simp only [spW] at h
  have h1 := ind_nonneg p (j, false) (j, true)
  have h2 := ind_nonneg p (j, true) (j, false)
  rcases ind_mul_rev p hp (j, false) (j, true) with h0 | h0
  · have : ind p (j, true) (j, false) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp h0, (ind_eq_zero_iff p _ _).mp this⟩
  · have : ind p (j, false) (j, true) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp this, (ind_eq_zero_iff p _ _).mp h0⟩

theorem abs_oW_eq_one (p : (GP n 3).Walk u u) (hp : p.IsTrail) {j : ZMod n} (h : oW p j ≠ 0) :
    |oW p j| = 1 := by
  unfold oW at h ⊢
  rcases ind_sub_mem p hp (j, false) (j + 1, false) with h0 | h0 | h0
  · exact absurd h0 h
  · rw [h0]; norm_num
  · rw [h0]; norm_num

theorem abs_iW_eq_one (p : (GP n 3).Walk u u) (hp : p.IsTrail) {j : ZMod n} (h : iW p j ≠ 0) :
    |iW p j| = 1 := by
  unfold iW at h ⊢
  rcases ind_sub_mem p hp (j, true) (j + 3, true) with h0 | h0 | h0
  · exact absurd h0 h
  · rw [h0]; norm_num
  · rw [h0]; norm_num

/-- **`p ≥ 1`**：外辺がすべて使われていれば、スポークが一本も無く、内輪に届かない。 -/
theorem exists_oW_zero (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h2 : (2 : ZMod n) ≠ 0) : ∃ j : ZMod n, oW p j = 0 := by
  by_contra hc
  push Not at hc
  have ht := hp.isCycle.isCircuit.isTrail
  -- どのスポークも使われない
  have hsp : ∀ j, spW p j = 0 := by
    intro j
    have hd := degO_eq p hp h2 j
    rw [abs_oW_eq_one p ht (hc _), abs_oW_eq_one p ht (hc _)] at hd
    have := abs_nonneg (spW p j)
    exact abs_eq_zero.mp (by linarith)
  -- 外輪は閉じている
  have hclosed : ∀ x y, HasDart p x y → x ∈ {v : V n | v.2 = false} →
      y ∈ {v : V n | v.2 = false} := by
    intro x y hxy hx
    obtain ⟨a, s⟩ := x
    simp only [Set.mem_ofPred_eq] at hx
    subst hx
    rcases out_nbr_O p a hxy with rfl | rfl | rfl
    · rfl
    · rfl
    · exact absurd hxy (no_spoke_of_spW_zero p ht (hsp a)).1
  have hall := support_subset_of_closed' p {v : V n | v.2 = false} (hp.mem_support (0, false))
    rfl hclosed (0, true) (hp.mem_support _)
  simp at hall

/-! ### 6. `hall3` の上側 -/

/-- **糸の補題（上側）**：`3 ∣ n` のとき、どの剰余類 `c : ZMod 3` にも欠けた内辺 `iW x = 0` がある。
  （その糸に欠けが無ければ、糸の内輪頂点はスポークを使わず、糸だけで閉じてしまう。） -/
theorem exists_iW_zero_thread (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h6 : (6 : ZMod n) ≠ 0) (h3 : 3 ∣ n) (c : ZMod 3) :
    ∃ x : ZMod n, iW p x = 0 ∧ ZMod.castHom h3 (ZMod 3) x = c := by
  by_contra hc
  push Not at hc
  have ht := hp.isCycle.isCircuit.isTrail
  have hthree : ∀ x : ZMod n, ZMod.castHom h3 (ZMod 3) (x + 3) = ZMod.castHom h3 (ZMod 3) x ∧
      ZMod.castHom h3 (ZMod 3) (x - 3) = ZMod.castHom h3 (ZMod 3) x := by
    intro x
    have h30 : ZMod.castHom h3 (ZMod 3) (3 : ZMod n) = 0 := by
      rw [show (3 : ZMod n) = ((3 : ℕ) : ZMod n) by norm_num, map_natCast]
      exact ZMod.natCast_self 3
    constructor
    · rw [map_add, h30, add_zero]
    · rw [map_sub, h30, sub_zero]
  -- 糸の上ではスポークを使わない
  have hsp : ∀ x : ZMod n, ZMod.castHom h3 (ZMod 3) x = c → spW p x = 0 := by
    intro x hx
    have hne1 : iW p x ≠ 0 := fun h => hc x h hx
    have hne2 : iW p (x - 3) ≠ 0 := fun h => hc (x - 3) h (by rw [(hthree x).2, hx])
    have hd := degI_eq p hp h6 x
    rw [abs_iW_eq_one p ht hne2, abs_iW_eq_one p ht hne1] at hd
    have := abs_nonneg (spW p x)
    exact abs_eq_zero.mp (by linarith)
  -- 糸 `T` は閉じている
  have hclosed : ∀ x y, HasDart p x y →
      x ∈ {v : V n | v.2 = true ∧ ZMod.castHom h3 (ZMod 3) v.1 = c} →
      y ∈ {v : V n | v.2 = true ∧ ZMod.castHom h3 (ZMod 3) v.1 = c} := by
    intro x y hxy hx
    obtain ⟨a, s⟩ := x
    simp only [Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨hs, ha⟩ := hx
    subst hs
    rcases out_nbr_I p a hxy with rfl | rfl | rfl
    · exact ⟨rfl, by rw [(hthree a).1, ha]⟩
    · exact ⟨rfl, by rw [(hthree a).2, ha]⟩
    · exact absurd hxy (no_spoke_of_spW_zero p ht (hsp a ha)).2
  have hT0 : (((c.val : ℕ) : ZMod n), true) ∈
      {v : V n | v.2 = true ∧ ZMod.castHom h3 (ZMod 3) v.1 = c} := by
    simp only [Set.mem_ofPred_eq, map_natCast]
    exact ⟨trivial, ZMod.natCast_zmod_val c⟩
  have hall := support_subset_of_closed' p _ (hp.mem_support (((c.val : ℕ) : ZMod n), true)) hT0
    hclosed (0, false) (hp.mem_support _)
  simp at hall

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open GeneralizedPetersen.Base

variable {n d : ℕ}

/-! ### 1. 切断と周期性 -/

/-- 切断 `ZMod d → ZMod n`。 -/
def lift (d n : ℕ) [NeZero d] (j : ZMod d) : ZMod n := ((j.val : ℕ) : ZMod n)

theorem castHom_lift [NeZero d] (h : d ∣ n) (j : ZMod d) :
    ZMod.castHom h (ZMod d) (lift d n j) = j := by
  simp only [lift, map_natCast]
  exact ZMod.natCast_zmod_val j

/-- `d`-周期性。 -/
def Periodic (f : ZMod n → ℤ) (d : ℕ) : Prop := ∀ x, f (x + (d : ZMod n)) = f x

theorem Periodic.iterate {f : ZMod n → ℤ} (hf : Periodic f d) (x : ZMod n) :
    ∀ t : ℕ, f (x + ((d * t : ℕ) : ZMod n)) = f x := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have e : x + ((d * (t + 1) : ℕ) : ZMod n) = (x + ((d * t : ℕ) : ZMod n)) + (d : ZMod n) := by
        push_cast; ring
      rw [e, hf, ih]

/-- **周期的な関数は商で決まる**：`castHom x = castHom y` なら `f x = f y`。 -/
theorem Periodic.eq_of_castHom [NeZero n] {f : ZMod n → ℤ} (hf : Periodic f d) (h : d ∣ n)
    {x y : ZMod n} (hxy : ZMod.castHom h (ZMod d) x = ZMod.castHom h (ZMod d) y) : f x = f y := by
  have hri : ∀ z : ZMod n, ((z.val : ℕ) : ZMod n) = z := ZMod.natCast_rightInverse
  have hc0 : ZMod.castHom h (ZMod d) (y - x) = 0 := by rw [map_sub, hxy, sub_self]
  have hcast : (((y - x).val : ℕ) : ZMod d) = 0 := by
    have hq := congrArg (ZMod.castHom h (ZMod d)) (hri (y - x))
    rw [map_natCast] at hq
    rw [hq]; exact hc0
  rw [ZMod.natCast_eq_zero_iff] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hy : y = x + ((d * t : ℕ) : ZMod n) := by
    rw [← ht, hri]; ring
  rw [hy, hf.iterate x t]

theorem Periodic.eq_lift [NeZero n] [NeZero d] {f : ZMod n → ℤ} (hf : Periodic f d) (h : d ∣ n)
    (x : ZMod n) : f x = f (lift d n (ZMod.castHom h (ZMod d) x)) :=
  hf.eq_of_castHom h (by rw [castHom_lift])

/-! ### 2. 降下 -/

namespace TwoFactor

variable [NeZero n] [NeZero d]

/-- `lift (j − c) = lift j − c` の代わり：`castHom` の値が一致するので周期関数の値が一致する。 -/
theorem lift_sub_eq {f : ZMod n → ℤ} (hf : Periodic f d) (h : d ∣ n) (j : ZMod d) (c : ℕ) :
    f (lift d n (j - (c : ZMod d))) = f (lift d n j - (c : ZMod n)) :=
  hf.eq_of_castHom h (by rw [castHom_lift, map_sub, castHom_lift, map_natCast])

/-- **降下**：`d`-周期的な `TwoFactor n` から `TwoFactor d`。 -/
def descend (T : TwoFactor n) (h : d ∣ n) (ho : Periodic T.o d) (hi : Periodic T.i d)
    (hs : Periodic T.sp d) : TwoFactor d where
  o := fun j => T.o (lift d n j)
  i := fun j => T.i (lift d n j)
  sp := fun j => T.sp (lift d n j)
  outer := fun j => by
    have e := lift_sub_eq ho h j 1
    simp only [Nat.cast_one] at e
    rw [e]
    exact T.outer _
  inner := fun j => by
    have e := lift_sub_eq hi h j 3
    simp only [Nat.cast_ofNat] at e
    rw [e]
    exact T.inner _
  o_mem := fun j => T.o_mem _
  i_mem := fun j => T.i_mem _
  degO := fun j => by
    have e := lift_sub_eq ho h j 1
    simp only [Nat.cast_one] at e
    rw [e]
    exact T.degO _
  degI := fun j => by
    have e := lift_sub_eq hi h j 3
    simp only [Nat.cast_ofNat] at e
    rw [e]
    exact T.degI _

@[simp] theorem descend_o (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (j : ZMod d) :
    (T.descend h ho hi hs).o j = T.o (lift d n j) := rfl
@[simp] theorem descend_i (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (j : ZMod d) :
    (T.descend h ho hi hs).i j = T.i (lift d n j) := rfl
@[simp] theorem descend_sp (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (j : ZMod d) :
    (T.descend h ho hi hs).sp j = T.sp (lift d n j) := rfl

/-- 降下した値は、商の像で読める。 -/
theorem descend_o_eq (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (x : ZMod n) :
    (T.descend h ho hi hs).o (ZMod.castHom h (ZMod d) x) = T.o x := by
  rw [descend_o, ← ho.eq_lift h]

theorem descend_i_eq (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (x : ZMod n) :
    (T.descend h ho hi hs).i (ZMod.castHom h (ZMod d) x) = T.i x := by
  rw [descend_i, ← hi.eq_lift h]

/-- **巻き数は降下で変わらない**：`W_d j = W_n (lift j)`。 -/
theorem descend_W (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (j : ZMod d) :
    (T.descend h ho hi hs).toFlow.W j = T.toFlow.W (lift d n j) := by
  have e1 := lift_sub_eq hi h j 1
  have e2 := lift_sub_eq hi h j 2
  simp only [Nat.cast_one, Nat.cast_ofNat] at e1 e2
  simp only [Flow.W, descend_o, descend_i]
  rw [e1, e2]

theorem descend_W_eq (T : TwoFactor n) (h : d ∣ n) (ho) (hi) (hs) (x : ZMod n) :
    (T.descend h ho hi hs).toFlow.W (ZMod.castHom h (ZMod d) x) = T.toFlow.W x := by
  rw [descend_W]
  exact (T.toFlow.W_const _ _).trans (by
    have e : ∀ c : ℕ, T.i (lift d n (ZMod.castHom h (ZMod d) x) - (c : ZMod n)) = T.i (x - c) :=
      fun c => hi.eq_of_castHom h (by rw [map_sub, castHom_lift, map_sub])
    have e1 := e 1
    have e2 := e 2
    simp only [Nat.cast_one, Nat.cast_ofNat] at e1 e2
    simp only [Flow.W]
    rw [e1, e2, ← ho.eq_lift h, ← hi.eq_lift h])

end TwoFactor

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count

variable {n : ℕ} {u : V n}

/-! ### 1. `n` 奇・`n ≥ 7` で要る `ZMod n` の事実 -/

theorem two_ne_zero_of_odd (hn : Odd n) (h3 : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro hc
  rw [show (2 : ZMod n) = ((2 : ℕ) : ZMod n) by norm_num, ZMod.natCast_eq_zero_iff] at hc
  have := Nat.le_of_dvd (by norm_num) hc
  omega

theorem six_ne_zero_of_odd (hn : Odd n) (h7 : 7 ≤ n) : (6 : ZMod n) ≠ 0 := by
  intro hc
  rw [show (6 : ZMod n) = ((6 : ℕ) : ZMod n) by norm_num, ZMod.natCast_eq_zero_iff] at hc
  have := Nat.le_of_dvd (by norm_num) hc
  omega

/-! ### 2. ダーツの `ρ^d` 不変性と周期性 -/

/-- **ダーツの `ρ^d` 不変性**（向きも込み）。 -/
def DartInv (p : (GP n 3).Walk u u) (d : ℕ) : Prop :=
  ∀ x y : V n, HasDart p x y ↔ HasDart p (((rot n) ^ d) x) (((rot n) ^ d) y)

theorem ind_iff (p : (GP n 3).Walk u u) {x y x' y' : V n}
    (h : HasDart p x y ↔ HasDart p x' y') : ind p x y = ind p x' y' := by
  unfold ind
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.mp h1) h2
  · exact absurd (h.mpr h2) h1
  · rfl

theorem ind_rot (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d) (x y : V n) :
    ind p (((rot n) ^ d) x) (((rot n) ^ d) y) = ind p x y :=
  ind_iff p (hD x y).symm

theorem periodic_oW (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d) : Periodic (oW p) d := by
  intro j
  have h1 := ind_rot p hD (j, false) (j + 1, false)
  have h2 := ind_rot p hD (j + 1, false) (j, false)
  rw [rot_pow_apply, rot_pow_apply] at h1 h2
  simp only [oW]
  rw [show j + (d : ZMod n) + 1 = j + 1 + (d : ZMod n) by ring, h1, h2]

theorem periodic_iW (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d) : Periodic (iW p) d := by
  intro j
  have h1 := ind_rot p hD (j, true) (j + 3, true)
  have h2 := ind_rot p hD (j + 3, true) (j, true)
  rw [rot_pow_apply, rot_pow_apply] at h1 h2
  simp only [iW]
  rw [show j + (d : ZMod n) + 3 = j + 3 + (d : ZMod n) by ring, h1, h2]

theorem periodic_spW (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d) : Periodic (spW p) d := by
  intro j
  have h1 := ind_rot p hD (j, false) (j, true)
  have h2 := ind_rot p hD (j, true) (j, false)
  rw [rot_pow_apply, rot_pow_apply] at h1 h2
  simp only [spW]
  rw [h1, h2]

/-- **商の 2 因子**：ハミルトン閉路の上側の 2 因子を `ZMod d` に降ろしたもの。 -/
noncomputable def quotTF [NeZero n] (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) (d : ℕ) [NeZero d] (hd : d ∣ n)
    (hD : DartInv p d) : TwoFactor d :=
  (hamTF p hp h2 h6).descend hd (periodic_oW p hD) (periodic_iW p hD) (periodic_spW p hD)

theorem quotTF_o [NeZero n] (p : (GP n 3).Walk u u) (hp) (h2) (h6) (d : ℕ) [NeZero d] (hd : d ∣ n)
    (hD : DartInv p d) (x : ZMod n) :
    (quotTF p hp h2 h6 d hd hD).o (ZMod.castHom hd (ZMod d) x) = oW p x := by
  exact ((periodic_oW p hD).eq_lift hd x).symm

theorem quotTF_i [NeZero n] (p : (GP n 3).Walk u u) (hp) (h2) (h6) (d : ℕ) [NeZero d] (hd : d ∣ n)
    (hD : DartInv p d) (x : ZMod n) :
    (quotTF p hp h2 h6 d hd hD).i (ZMod.castHom hd (ZMod d) x) = iW p x := by
  exact ((periodic_iW p hD).eq_lift hd x).symm

/-! ### 3. `Win d` と、`Gi ≠ ∅`・`hall3` -/

/-- `F : Win d` が `T : TwoFactor d` と（符号を込めて）一致する。 -/
def Agrees {d : ℕ} (F : Win d) (T : TwoFactor d) : Prop :=
  (∀ j, F.o j = T.o j ∧ F.i j = T.i j ∧ F.sp j = T.sp j) ∨
    (∀ j, F.o j = -T.o j ∧ F.i j = -T.i j ∧ F.sp j = -T.sp j)

theorem Agrees.i_eq_zero {d : ℕ} {F : Win d} {T : TwoFactor d} (h : Agrees F T) (j : ZMod d) :
    F.i j = 0 ↔ T.i j = 0 := by
  rcases h with h | h
  · rw [(h j).2.1]
  · rw [(h j).2.1]; simp

/-- **`WinBridge` の中身（巻き数 `≠ 0` を仮定して）**：`Win d` が作れ、`Gi ≠ ∅`・`hall3` が成り立つ。 -/
theorem win_of_dartInv [NeZero n] (hn : Odd n) (h7 : 7 ≤ n) (p : (GP n 3).Walk u u)
    (hp : p.IsHamiltonianCycle) (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0)
    (d : ℕ) [NeZero d] (hd : d ∣ n) (hD : DartInv p d)
    (hw : ∀ j, (quotTF p hp h2 h6 d hd hD).toFlow.W j ≠ 0) :
    ∃ F : Win d, Odd d ∧ (Gi F).Nonempty ∧
      (∀ h3 : 3 ∣ d, ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c) ∧
      Agrees F (quotTF p hp h2 h6 d hd hD) := by
  set T := quotTF p hp h2 h6 d hd hD with hT
  have hodd : Odd d := Odd.of_dvd_nat hn hd
  -- `p ≥ 1`
  have hp0 : 0 < T.p := by
    obtain ⟨j, hj⟩ := exists_oW_zero p hp h2
    apply Finset.card_pos.mpr
    refine ⟨ZMod.castHom hd (ZMod d) j, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hT, quotTF_o]
    exact hj
  -- 巻き数
  have hwc : ∀ j, T.toFlow.W j = T.toFlow.W 0 := fun j => T.toFlow.W_const j 0
  obtain ⟨F, hF⟩ := T.exists_win hodd hp0 (T.toFlow.W 0) hwc (hw 0)
  refine ⟨F, hodd, ?_, ?_, hF⟩
  · -- `Gi ≠ ∅`：`q = p ≥ 1`
    have hq : 0 < T.q := by rw [← T.p_eq_q]; exact hp0
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact ⟨r, (mem_Gi F r).mpr ((Agrees.i_eq_zero hF r).mpr hr)⟩
  · -- `hall3`
    intro h3 c
    have h3n : 3 ∣ n := dvd_trans h3 hd
    obtain ⟨x, hx0, hxc⟩ := exists_iW_zero_thread p hp h6 h3n c
    refine ⟨ZMod.castHom hd (ZMod d) x, ?_, ?_⟩
    · rw [mem_Gi, Agrees.i_eq_zero hF, hT, quotTF_i]
      exact hx0
    · have := RingHom.congr_fun (ZMod.castHom_comp h3 hd) x
      simp only [RingHom.comp_apply] at this
      rw [this]
      exact hxc

/-! ### 4. 三つの残りと、`WinBridge n` の還元 -/

/-- **残り 1（ダーツの不変性）**：`ρ^i` 不変な辺集合を持つハミルトン閉路 `p` に対し、
  ある `d ∣ n`（`0 < d < n`）でダーツが `ρ^d` 不変（向きも込み）。
  紙では `d = gcd(i,n)`、向きの一貫性は「閉路の自己同型は回転か反転、`n/d` 奇なら回転」。 -/
def DartBridge (n : ℕ) [NeZero n] : Prop :=
  ∀ i, 0 < i → i < n → ∀ E ∈ HamEdges n 3, (rotE n)^[i] E = E →
    ∃ (u : V n) (p : (GP n 3).Walk u u) (d : ℕ), p.IsHamiltonianCycle ∧ p.edges.toFinset = E ∧
      d ∣ n ∧ 0 < d ∧ d < n ∧ DartInv p d

/-- **残り 2（巻き数 `≠ 0`）**：`d < n` なら降下した 2 因子の巻き数は `0` でない。
  紙では「`w = 0` なら持ち上げが `2d < 2n` 歩で閉じてしまう」（基本領域の補題）。 -/
def WindingBridge (n : ℕ) [NeZero n] : Prop :=
  ∀ (u : V n) (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) (d : ℕ) [NeZero d] (hd : d ∣ n), d < n →
    ∀ (hD : DartInv p d) (j : ZMod d), (quotTF p hp h2 h6 d hd hD).toFlow.W j ≠ 0

/-- **残り 3（一本の閉路）**：降下した 2 因子に一致する `Win d` に対し、`next₃ ∘ θ` は
  `G_i` 全体を回る巡回。紙では紙の証明の「`H_Q` がハミルトン ⟺ `F ≅ next₃ ∘ θ` が `2q` 巡回」。 -/
def CycleBridge (n : ℕ) [NeZero n] : Prop :=
  ∀ (u : V n) (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) (d : ℕ) [NeZero d] (hd : d ∣ n), d < n →
    ∀ (hD : DartInv p d) (F : Win d), Agrees F (quotTF p hp h2 h6 d hd hD) →
      (next3 F * theta F).IsCycle ∧ (next3 F * theta F).support = Finset.univ

/-- **`WinBridge n` は三つの残りから出る。** -/
theorem winBridge_of [NeZero n] (hn : Odd n) (h7 : 7 ≤ n)
    (hA : DartBridge n) (hB : WindingBridge n) (hC : CycleBridge n) : WinBridge n := by
  intro i hi hin E hE hfix
  obtain ⟨u, p, d, hp, -, hd, hd0, hdn, hD⟩ := hA i hi hin E hE hfix
  haveI : NeZero d := ⟨by omega⟩
  have h2 := two_ne_zero_of_odd hn (by omega)
  have h6 := six_ne_zero_of_odd hn h7
  obtain ⟨F, hodd, hne, hall3, hF⟩ :=
    win_of_dartInv hn h7 p hp h2 h6 d hd hD (hB u p hp h2 h6 d hd hdn hD)
  obtain ⟨hc1, hc2⟩ := hC u p hp h2 h6 d hd hdn hD F hF
  exact ⟨d, inferInstance, F, hodd, hne, hall3, hc1, hc2⟩

/-- **一般 `n`（三つの残りを仮定）**：`n ∣ #HC(GP(n,3))`。 -/
theorem gp3_dvd_hc' (n : ℕ) [NeZero n] (hn : Odd n) (h7 : 7 ≤ n)
    (hA : DartBridge n) (hB : WindingBridge n) (hC : CycleBridge n) : n ∣ numHC n 3 :=
  gp3_dvd_hc n hn h7 (winBridge_of hn h7 hA hB hC)

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `σ` が `p` の辺集合を保つ。 -/
def EdgeInv {u : V} (p : G.Walk u u) (σ : V → V) : Prop :=
  ∀ x y, s(x, y) ∈ p.edges ↔ s(σ x, σ y) ∈ p.edges

/-- `σ` がダーツを保つ。 -/
def Fwd {u : V} (p : G.Walk u u) (σ : V → V) : Prop :=
  ∀ x y, HasDart p x y → HasDart p (σ x) (σ y)

/-- `σ` がダーツを反転する。 -/
def Bwd {u : V} (p : G.Walk u u) (σ : V → V) : Prop :=
  ∀ x y, HasDart p x y → HasDart p (σ y) (σ x)

/-! ### 1. 一段の伝播 -/

/-- `x → y → z` と進むとき、`σx → σy` なら `σy → σz`。 -/
theorem fwd_step {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V} (hinj : Function.Injective σ)
    (hE : EdgeInv p σ) {x y z : V} (hxy : HasDart p x y) (hyz : HasDart p y z)
    (h : HasDart p (σ x) (σ y)) : HasDart p (σ y) (σ z) := by
  have he : s(σ y, σ z) ∈ p.edges := (hE y z).mp hyz.edge_mem
  rcases hasDart_of_edge_mem he with h1 | h1
  · exact h1
  · exfalso
    -- `σz → σy` と `σx → σy` がともに入るダーツ：`σz = σx`、ゆえに `z = x`
    have hσy : σ y ∈ p.support := by
      obtain ⟨δ, hδ, -, h2⟩ := h
      rw [← h2]; exact p.dart_snd_mem_support_of_mem_darts hδ
    obtain ⟨a, b, hab, hout, hin⟩ := cycle_local' hp hσy
    have e1 : σ z = b := (hin (σ z)).mp h1
    have e2 : σ x = b := (hin (σ x)).mp h
    have hxz : x = z := hinj (e2.trans e1.symm)
    subst hxz
    -- `x → y` と `y → x`：逆向きの同居
    exact hxy.not_rev hp.isCircuit.isTrail hyz

/-- `x → y → z` と進むとき、`σy → σx` なら `σz → σy`。 -/
theorem bwd_step {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V} (hinj : Function.Injective σ)
    (hE : EdgeInv p σ) {x y z : V} (hxy : HasDart p x y) (hyz : HasDart p y z)
    (h : HasDart p (σ y) (σ x)) : HasDart p (σ z) (σ y) := by
  have he : s(σ y, σ z) ∈ p.edges := (hE y z).mp hyz.edge_mem
  rcases hasDart_of_edge_mem he with h1 | h1
  · exfalso
    have hσy : σ y ∈ p.support := by
      obtain ⟨δ, hδ, h1, -⟩ := h
      rw [← h1]; exact p.dart_fst_mem_support_of_mem_darts hδ
    obtain ⟨a, b, hab, hout, hin⟩ := cycle_local' hp hσy
    have e1 : σ z = a := (hout (σ z)).mp h1
    have e2 : σ x = a := (hout (σ x)).mp h
    have hxz : x = z := hinj (e2.trans e1.symm)
    subst hxz
    exact hxy.not_rev hp.isCircuit.isTrail hyz
  · exact h1

/-! ### 2. 歩道に沿った伝播 -/

/-- `p` のダーツだけを使う歩道 `q` の上で、最初のダーツが保たれれば全部保たれる。 -/
theorem fwd_along {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V}
    (hinj : Function.Injective σ) (hE : EdgeInv p σ) :
    ∀ {a b : V} (q : G.Walk a b), (∀ δ ∈ q.darts, δ ∈ p.darts) →
      (∀ c, HasDart q a c → HasDart p (σ a) (σ c)) →
      ∀ x y, HasDart q x y → HasDart p (σ x) (σ y) := by
  intro a b q
  induction q with
  | nil =>
      intro _ _ x y hxy
      obtain ⟨δ, hδ, -, -⟩ := hxy
      simp at hδ
  | @cons a c b h q ih =>
      intro hsub hfirst x y hxy
      have hac : HasDart (Walk.cons h q) a c := ⟨⟨(a, c), h⟩, by simp [Walk.darts_cons], rfl, rfl⟩
      have hσac : HasDart p (σ a) (σ c) := hfirst c hac
      have hsub' : ∀ δ ∈ q.darts, δ ∈ p.darts := fun δ hδ => hsub δ (by simp [Walk.darts_cons, hδ])
      obtain ⟨δ, hδ, h1, h2⟩ := hxy
      rw [Walk.darts_cons, List.mem_cons] at hδ
      rcases hδ with rfl | hδ
      · exact h1 ▸ h2 ▸ hσac
      · refine ih hsub' ?_ x y ⟨δ, hδ, h1, h2⟩
        intro c' hcc'
        have hpac : HasDart p a c := ⟨⟨(a, c), h⟩, hsub _ (by simp [Walk.darts_cons]), rfl, rfl⟩
        have hpcc' : HasDart p c c' := by
          obtain ⟨δ', hδ', h1', h2'⟩ := hcc'
          exact ⟨δ', hsub' δ' hδ', h1', h2'⟩
        exact fwd_step hp hinj hE hpac hpcc' hσac

theorem bwd_along {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V}
    (hinj : Function.Injective σ) (hE : EdgeInv p σ) :
    ∀ {a b : V} (q : G.Walk a b), (∀ δ ∈ q.darts, δ ∈ p.darts) →
      (∀ c, HasDart q a c → HasDart p (σ c) (σ a)) →
      ∀ x y, HasDart q x y → HasDart p (σ y) (σ x) := by
  intro a b q
  induction q with
  | nil =>
      intro _ _ x y hxy
      obtain ⟨δ, hδ, -, -⟩ := hxy
      simp at hδ
  | @cons a c b h q ih =>
      intro hsub hfirst x y hxy
      have hac : HasDart (Walk.cons h q) a c := ⟨⟨(a, c), h⟩, by simp [Walk.darts_cons], rfl, rfl⟩
      have hσac : HasDart p (σ c) (σ a) := hfirst c hac
      have hsub' : ∀ δ ∈ q.darts, δ ∈ p.darts := fun δ hδ => hsub δ (by simp [Walk.darts_cons, hδ])
      obtain ⟨δ, hδ, h1, h2⟩ := hxy
      rw [Walk.darts_cons, List.mem_cons] at hδ
      rcases hδ with rfl | hδ
      · exact h1 ▸ h2 ▸ hσac
      · refine ih hsub' ?_ x y ⟨δ, hδ, h1, h2⟩
        intro c' hcc'
        have hpac : HasDart p a c := ⟨⟨(a, c), h⟩, hsub _ (by simp [Walk.darts_cons]), rfl, rfl⟩
        have hpcc' : HasDart p c c' := by
          obtain ⟨δ', hδ', h1', h2'⟩ := hcc'
          exact ⟨δ', hsub' δ' hδ', h1', h2'⟩
        exact bwd_step hp hinj hE hpac hpcc' hσac

/-- 閉路 `p` の最初のダーツ。 -/
theorem exists_first_dart {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∃ c, HasDart p u c ∧ ∀ c', HasDart p u c' → c' = c := by
  obtain ⟨a, b, -, hout, -⟩ := cycle_local' hp (Walk.start_mem_support p)
  exact ⟨a, (hout a).mpr rfl, fun c' h => (hout c').mp h⟩

/-- **二者択一**：辺集合を保つ単射は、ダーツを一斉に保つか一斉に反転する。 -/
theorem fwd_or_bwd {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V}
    (hinj : Function.Injective σ) (hE : EdgeInv p σ) : Fwd p σ ∨ Bwd p σ := by
  obtain ⟨c, huc, hunique⟩ := exists_first_dart hp
  have he : s(σ u, σ c) ∈ p.edges := (hE u c).mp huc.edge_mem
  rcases hasDart_of_edge_mem he with h1 | h1
  · left
    intro x y hxy
    exact fwd_along hp hinj hE p (fun _ h => h) (fun c' hc' => (hunique c' hc') ▸ h1) x y hxy
  · right
    intro x y hxy
    exact bwd_along hp hinj hE p (fun _ h => h) (fun c' hc' => (hunique c' hc') ▸ h1) x y hxy

/-! ### 3. 奇数位数なら保つ -/

theorem Fwd.comp {u : V} {p : G.Walk u u} {σ τ : V → V} (hσ : Fwd p σ) (hτ : Fwd p τ) :
    Fwd p (σ ∘ τ) := fun x y h => hσ _ _ (hτ x y h)

theorem Bwd.comp_self {u : V} {p : G.Walk u u} {σ : V → V} (hσ : Bwd p σ) : Fwd p (σ ∘ σ) :=
  fun x y h => hσ _ _ (hσ x y h)

theorem Fwd.iterate {u : V} {p : G.Walk u u} {σ : V → V} (hσ : Fwd p σ) :
    ∀ k : ℕ, Fwd p σ^[k] := by
  intro k
  induction k with
  | zero => intro x y h; simpa using h
  | succ k ih =>
      intro x y h
      rw [Function.iterate_succ']
      exact hσ _ _ (ih x y h)

/-- **奇数位数の辺不変な単射はダーツを保つ**：`σ^[m] = id`、`m` 奇。 -/
theorem preserves_of_odd_order {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V}
    (hinj : Function.Injective σ) (hE : EdgeInv p σ) {m : ℕ} (hm : Odd m)
    (hσm : ∀ x, σ^[m] x = x) : Fwd p σ := by
  rcases fwd_or_bwd hp hinj hE with h | h
  · exact h
  · -- `σ²` は保つ、ゆえに `σ^{m+1}` は保つ、しかし `σ^{m+1} = σ`
    have h2 : Fwd p (σ ∘ σ) := h.comp_self
    obtain ⟨k, hk⟩ := hm
    have hiter : Fwd p (σ ∘ σ)^[k + 1] := h2.iterate (k + 1)
    have hcomp : ∀ x, (σ ∘ σ)^[k + 1] x = σ x := by
      intro x
      have : (σ ∘ σ)^[k + 1] x = σ^[2 * (k + 1)] x := by
        rw [Function.iterate_mul]
        rfl
      rw [this, show 2 * (k + 1) = m + 1 by omega, Function.iterate_succ_apply', hσm]
    intro x y hxy
    have h1 := hiter x y hxy
    rw [hcomp, hcomp] at h1
    exact h1

/-- 奇数位数なら、保つことと同値（`↔` 版）。 -/
theorem dartInv_iff_of_odd_order {u : V} {p : G.Walk u u} (hp : p.IsCycle) {σ : V → V}
    (hinj : Function.Injective σ) (hE : EdgeInv p σ) {m : ℕ} (hm : Odd m)
    (hσm : ∀ x, σ^[m] x = x) : ∀ x y, HasDart p x y ↔ HasDart p (σ x) (σ y) := by
  have hf := preserves_of_odd_order hp hinj hE hm hσm
  intro x y
  refine ⟨hf x y, fun h => ?_⟩
  -- `σ^[m−1]` を当てて戻す
  obtain ⟨k, hk⟩ := hm
  have := hf.iterate (2 * k) (σ x) (σ y) h
  have e : ∀ z, σ^[2 * k] (σ z) = z := by
    intro z
    rw [← Function.iterate_succ_apply, show (2 * k).succ = m by omega, hσm]
  rw [e, e] at this
  exact this

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count

variable {n : ℕ} [NeZero n] {u : V n}

/-! ### 1. 辺集合の不変性 -/

/-- `rotE` の反復で辺集合が固定されるなら、`ρ^t` は辺集合を保つ。 -/
theorem edgeInv_of_rotE (p : (GP n 3).Walk u u) (t : ℕ)
    (hfix : (rotE n)^[t] p.edges.toFinset = p.edges.toFinset) : EdgeInv p ⇑((rot n) ^ t) := by
  rw [rotE_iterate] at hfix
  intro x y
  rw [← List.mem_toFinset, ← List.mem_toFinset]
  constructor
  · intro h
    rw [← hfix]
    exact Finset.mem_image_of_mem _ h
  · intro h
    rw [← hfix] at h
    obtain ⟨e, he, hee⟩ := Finset.mem_image.mp h
    have : e = s(x, y) := Sym2.map.injective ((rot n) ^ t).injective (by rw [hee]; rfl)
    rw [← this]; exact he

theorem EdgeInv.iterate {W : Type*} {G : SimpleGraph W} {a : W} {p : G.Walk a a} {σ : W → W}
    (h : EdgeInv p σ) : ∀ k : ℕ, EdgeInv p σ^[k] := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← h, ih]

theorem EdgeInv.congr {W : Type*} {G : SimpleGraph W} {a : W} {p : G.Walk a a} {σ τ : W → W}
    (h : EdgeInv p σ) (he : ∀ x, σ x = τ x) : EdgeInv p τ := by
  intro x y
  rw [← he, ← he]
  exact h x y

/-- `ρ^{n q + d} = ρ^d`。 -/
theorem rot_pow_mod (q d : ℕ) (x : V n) : ((rot n) ^ (n * q + d)) x = ((rot n) ^ d) x := by
  rw [rot_pow_apply, rot_pow_apply]
  push_cast
  rw [ZMod.natCast_self]
  simp

/-- **`ρ^{gcd(i,n)}` も辺集合を保つ。** -/
theorem edgeInv_gcd (p : (GP n 3).Walk u u) (i : ℕ) (hi : 0 < i) (hin : i < n)
    (hfix : (rotE n)^[i] p.edges.toFinset = p.edges.toFinset) :
    EdgeInv p ⇑((rot n) ^ (Nat.gcd i n)) := by
  have hE := edgeInv_of_rotE p i hfix
  have hlt : Nat.gcd i n < n := lt_of_le_of_lt (Nat.gcd_le_left n hi) hin
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_gcd hlt
  have hEa := hE.iterate a
  refine hEa.congr (fun x => ?_)
  have e1 : (⇑((rot n) ^ i))^[a] x = ((rot n) ^ (i * a)) x := by
    rw [pow_mul]
    simp only [Equiv.Perm.coe_pow]
  rw [e1, ← Nat.div_add_mod (i * a) n, ha, rot_pow_mod]

/-! ### 2. 位数は奇数 -/

omit [NeZero n] in
theorem rot_pow_gcd_order (i : ℕ) (x : V n) :
    (⇑((rot n) ^ (Nat.gcd i n)))^[n / Nat.gcd i n] x = x := by
  rw [← Equiv.Perm.coe_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right i n), rot_pow_card]
  rfl

/-- **`DartBridge n` が閉じる**（`n` 奇）。 -/
theorem dartBridge (hn : Odd n) : DartBridge n := by
  intro i hi hin E hE hfix
  obtain ⟨u, p, hp, hpE⟩ := (mem_HamEdges n 3 E).mp hE
  subst hpE
  have hdvd : Nat.gcd i n ∣ n := Nat.gcd_dvd_right i n
  have hpos : 0 < Nat.gcd i n := Nat.gcd_pos_of_pos_left n hi
  have hlt : Nat.gcd i n < n := lt_of_le_of_lt (Nat.gcd_le_left n hi) hin
  refine ⟨u, p, Nat.gcd i n, hp, rfl, hdvd, hpos, hlt, ?_⟩
  have hE := edgeInv_gcd p i hi hin hfix
  have hm : Odd (n / Nat.gcd i n) := by
    obtain ⟨m, hm⟩ := hdvd
    rw [Nat.div_eq_of_eq_mul_right hpos hm]
    have hn' : Odd (Nat.gcd i n * m) := by rw [← hm]; exact hn
    exact (Nat.odd_mul.mp hn').2
  exact dartInv_iff_of_odd_order hp.isCycle ((rot n) ^ (Nat.gcd i n)).injective hE hm
    (rot_pow_gcd_order i)

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### 1. 接頭辞 -/

/-- **同じ点から出る二本の歩道**（ダーツは閉路 `p` のもの）：短い方は長い方の接頭辞。 -/
theorem darts_prefix {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∀ {a b : V} (q : G.Walk a b) {b' : V} (q' : G.Walk a b'),
      (∀ δ ∈ q.darts, δ ∈ p.darts) → (∀ δ ∈ q'.darts, δ ∈ p.darts) → q.length ≤ q'.length →
      q.darts <+: q'.darts := by
  intro a b q
  induction q with
  | nil =>
      intro b' q' _ _ _
      simp
  | @cons a c b h q1 ih =>
      intro b' q' hq hq' hlen
      cases q' with
      | nil => simp at hlen
      | @cons _ c' _ h' q1' =>
          have hd : (⟨(a, c), h⟩ : G.Dart) ∈ p.darts := hq _ (by simp [Walk.darts_cons])
          have hd' : (⟨(a, c'), h'⟩ : G.Dart) ∈ p.darts := hq' _ (by simp [Walk.darts_cons])
          have heq := dart_eq_of_fst_eq hp hd hd' rfl
          have hc : c = c' := congrArg (fun δ : G.Dart => δ.snd) heq
          subst hc
          rw [Walk.darts_cons, Walk.darts_cons, List.cons_prefix_cons]
          refine ⟨rfl, ih q1' ?_ ?_ ?_⟩
          · intro δ hδ; exact hq δ (by simp [Walk.darts_cons, hδ])
          · intro δ hδ; exact hq' δ (by simp [Walk.darts_cons, hδ])
          · simpa using hlen

/-- 接頭辞で長さが等しければダーツ列が等しい。 -/
theorem darts_eq_of_prefix {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    {a b b' : V} (q : G.Walk a b) (q' : G.Walk a b')
    (hq : ∀ δ ∈ q.darts, δ ∈ p.darts) (hq' : ∀ δ ∈ q'.darts, δ ∈ p.darts)
    (hlen : q.length = q'.length) : q.darts = q'.darts :=
  (darts_prefix hp q q' hq hq' hlen.le).eq_of_length (by rw [Walk.length_darts, Walk.length_darts, hlen])

/-- ダーツ列が等しければ終点が等しい。 -/
theorem end_eq_of_darts_eq {a b b' : V} (q : G.Walk a b) (q' : G.Walk a b')
    (h : q.darts = q'.darts) : b = b' := by
  have hs : q.support = q'.support := by
    rw [← Walk.cons_map_snd_darts q, ← Walk.cons_map_snd_darts q', h]
  have h1 := Walk.getLast_support q
  have h2 := Walk.getLast_support q'
  rw [← h1, ← h2]
  simp only [hs]

/-! ### 2. 閉じた歩道は閉路の繰り返し -/

/-- `p` の接頭辞の長さ `t` の歩道が `u` で終わり `0 < t ≤ length` なら `t = length`。 -/
theorem length_eq_of_closed_prefix {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    {a : V} (q : G.Walk u a) (ha : a = u) (hq : ∀ δ ∈ q.darts, δ ∈ p.darts)
    (h0 : 0 < q.length) (hle : q.length ≤ p.length) : q.length = p.length := by
  have hd : (p.take q.length).darts = q.darts := by
    refine (darts_eq_of_prefix hp (p.take q.length) q ?_ hq ?_).symm.symm
    · intro δ hδ
      rw [Walk.darts_take] at hδ
      exact List.mem_of_mem_take hδ
    · rw [Walk.take_length]; exact min_eq_left hle
  have he : p.getVert q.length = u := (end_eq_of_darts_eq _ _ hd).trans ha
  have hL : p.getVert p.length = u := Walk.getVert_length p
  have hinj := hp.getVert_injOn
  exact hinj (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; omega)
    (he.trans hL.symm)

/-- **閉じた歩道のダーツ列は閉路の繰り返し。** -/
theorem closed_walk_darts {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    ∀ (t : ℕ) {a' a : V} (q : G.Walk a' a), u = a' → a = u → (∀ δ ∈ q.darts, δ ∈ p.darts) →
      q.length = t → ∃ j : ℕ, q.darts = (List.replicate j p.darts).flatten ∧ t = j * p.length := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a' a q ha' ha hq hlen
    subst ha'
    have hLpos : 0 < p.length := by
      have := hp.three_le_length; omega
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · refine ⟨0, ?_, by simp⟩
      have : q.darts = [] := List.length_eq_zero_iff.mp (by rw [Walk.length_darts, hlen])
      simp [this]
    rcases le_or_gt t p.length with hle | hgt
    · -- `t = length`、ちょうど一周
      have ht : t = p.length := by
        rw [← hlen]
        exact length_eq_of_closed_prefix hp q ha hq (by omega) (by omega)
      refine ⟨1, ?_, by omega⟩
      have hd := darts_eq_of_prefix hp q p hq (fun _ h => h) (by omega)
      simp [hd]
    · -- 最初の一周を切り離す
      have hdt : (q.take p.length).darts = p.darts := by
        refine darts_eq_of_prefix hp (q.take p.length) p ?_ (fun _ h => h) ?_
        · intro δ hδ
          rw [Walk.darts_take] at hδ
          exact hq δ (List.mem_of_mem_take hδ)
        · rw [Walk.take_length]; exact min_eq_left (by omega)
      have hmid : q.getVert p.length = u := end_eq_of_darts_eq _ _ hdt
      obtain ⟨j, hj, hjt⟩ := ih (t - p.length) (by omega) (q.drop p.length) hmid.symm ha
        (by
          intro δ hδ
          rw [Walk.darts_drop] at hδ
          exact hq δ (List.mem_of_mem_drop hδ))
        (by rw [Walk.drop_length, hlen])
      refine ⟨j + 1, ?_, ?_⟩
      · rw [← List.take_append_drop p.length q.darts, ← Walk.darts_take, hdt, ← Walk.darts_drop, hj,
          List.replicate_succ, List.flatten_cons]
      · rw [Nat.add_mul, one_mul]; omega

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count Finset

variable {n : ℕ} {u : V n}

/-! ### A. 変位 -/

/-- ダーツ `x → y` の変位（外辺 `±1`・内辺 `±3`・スポーク `0`）。 -/
def disp (x y : V n) : ℤ :=
  if x.2 = false ∧ y.2 = false then (if y.1 = x.1 + 1 then 1 else -1)
  else if x.2 = true ∧ y.2 = true then (if y.1 = x.1 + 3 then 3 else -3) else 0

theorem disp_cast (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) {x y : V n}
    (h : (GP n 3).Adj x y) : ((disp x y : ℤ) : ZMod n) = y.1 - x.1 := by
  obtain ⟨a, s⟩ := x
  rcases GP_neighbor n 3 a s y h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
  · simp [disp]
  · have hne : ¬ (a - 1 = a + 1) := fun h => h2 (by linear_combination -h)
    simp [disp, hne]
  · simp [disp]
  · simp [disp]
  · have hne : ¬ (a - 3 = a + 3) := fun h => h6 (by linear_combination -h)
    simp [disp, hne]
  · simp [disp]

theorem disp_rot (t : ℕ) (x y : V n) :
    disp (((rot n) ^ t) x) (((rot n) ^ t) y) = disp x y := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, s'⟩ := y
  rw [rot_pow_apply, rot_pow_apply]
  have e1 : (b + (t : ZMod n) = a + (t : ZMod n) + 1) ↔ (b = a + 1) := by
    constructor <;> intro h <;> linear_combination h
  have e3 : (b + (t : ZMod n) = a + (t : ZMod n) + 3) ↔ (b = a + 3) := by
    constructor <;> intro h <;> linear_combination h
  simp only [disp, e1, e3]

/-! ### B. 歩道に沿った変位の和 -/

/-- 頂点対のリストの変位の和。 -/
def WSl (l : List (V n × V n)) : ℤ := (l.map (fun z => disp z.1 z.2)).sum

/-- 歩道の変位の和。 -/
def WS {a b : V n} (q : (GP n 3).Walk a b) : ℤ := WSl (q.darts.map Dart.toProd)

theorem WSl_append (l1 l2 : List (V n × V n)) : WSl (l1 ++ l2) = WSl l1 + WSl l2 := by
  simp [WSl]

theorem WSl_flatten_replicate (l : List (V n × V n)) : ∀ j : ℕ,
    WSl (List.replicate j l).flatten = j * WSl l := by
  intro j
  induction j with
  | zero => simp [WSl]
  | succ j ih => rw [List.replicate_succ, List.flatten_cons, WSl_append, ih]; push_cast; ring

theorem WS_nil (a : V n) : WS (Walk.nil : (GP n 3).Walk a a) = 0 := by simp [WS, WSl]

theorem WS_cons {a c b : V n} (h : (GP n 3).Adj a c) (q : (GP n 3).Walk c b) :
    WS (Walk.cons h q) = disp a c + WS q := by
  simp [WS, WSl, Walk.darts_cons]

theorem WS_append {a b c : V n} (q : (GP n 3).Walk a b) (r : (GP n 3).Walk b c) :
    WS (q.append r) = WS q + WS r := by
  simp [WS, Walk.darts_append, WSl_append]

/-- **変位の和の像は終点 − 始点**。 -/
theorem WS_cast (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) :
    ∀ {a b : V n} (q : (GP n 3).Walk a b), ((WS q : ℤ) : ZMod n) = b.1 - a.1 := by
  intro a b q
  induction q with
  | nil => simp [WS_nil]
  | cons h q ih =>
      rw [WS_cons]
      push_cast
      rw [disp_cast h2 h6 h, ih]
      ring

/-! ### C. 平行移動 -/

theorem exists_shift_darts (t : ℕ) : ∀ {a b : V n} (q : (GP n 3).Walk a b),
    ∃ q' : (GP n 3).Walk (((rot n) ^ t) a) (((rot n) ^ t) b),
      q'.darts.map Dart.toProd
        = q.darts.map (fun δ => (((rot n) ^ t) δ.fst, ((rot n) ^ t) δ.snd)) ∧
      q'.length = q.length := by
  intro a b q
  induction q with
  | nil => exact ⟨Walk.nil, by simp, by simp⟩
  | cons h q ih =>
      obtain ⟨q', hq', hl⟩ := ih
      exact ⟨Walk.cons ((GP_adj_rot_pow n 3 t _ _).mpr h) q', by simp [Walk.darts_cons, hq'],
        by simp [hl]⟩

theorem WS_of_shift (t : ℕ) {a b : V n} (q : (GP n 3).Walk a b) {a' b' : V n}
    (q' : (GP n 3).Walk a' b')
    (h : q'.darts.map Dart.toProd
      = q.darts.map (fun δ => (((rot n) ^ t) δ.fst, ((rot n) ^ t) δ.snd))) :
    WS q' = WS q := by
  simp only [WS, h, WSl, List.map_map]
  congr 1
  refine List.map_congr_left (fun δ _ => ?_)
  simp [disp_rot]

/-- ダーツの不変性の反復。 -/
theorem dartInv_pow (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d) :
    ∀ (k : ℕ) (x y : V n), HasDart p x y → HasDart p (((rot n) ^ (d * k)) x) (((rot n) ^ (d * k)) y) := by
  intro k
  induction k with
  | zero => intro x y h; simpa using h
  | succ k ih =>
      intro x y h
      have := (hD _ _).mp (ih x y h)
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add,
        show d + d * k = d * (k + 1) by ring] at this
      exact this

theorem mem_darts_of_hasDart (p : (GP n 3).Walk u u) (δ : (GP n 3).Dart)
    (h : HasDart p δ.fst δ.snd) : δ ∈ p.darts := by
  obtain ⟨δ', hδ', h1, h2⟩ := h
  have : δ' = δ := Dart.ext _ _ (Prod.ext h1 h2)
  rw [← this]; exact hδ'

/-! ### D. 並べ替え：`WS p = Σ oW + 3 Σ iW` -/

theorem disp_ff (a b : ZMod n) : disp (a, false) (b, false) = if b = a + 1 then 1 else -1 := by
  simp [disp]

theorem disp_tt (a b : ZMod n) : disp (a, true) (b, true) = if b = a + 3 then 3 else -3 := by
  simp [disp]

theorem disp_ft (a b : ZMod n) : disp (a, false) (b, true) = 0 := by simp [disp]
theorem disp_tf (a b : ZMod n) : disp (a, true) (b, false) = 0 := by simp [disp]

/-- 外輪の頂点 `O_a` から出るダーツの変位の和。 -/
theorem sum_disp_O [NeZero n] (p : (GP n 3).Walk u u) (h2 : (2 : ZMod n) ≠ 0) (a : ZMod n) :
    ∑ b : ZMod n, ind p (a, false) (b, false) * disp (a, false) (b, false)
      = ind p (a, false) (a + 1, false) - ind p (a, false) (a - 1, false) := by
  have hne : a + 1 ≠ a - 1 := fun h => h2 (by linear_combination h)
  rw [Finset.sum_eq_add (a + 1) (a - 1) hne]
  · rw [disp_ff, disp_ff, if_pos rfl, if_neg (fun h => hne (by linear_combination -h))]
    ring
  · intro c _ ⟨hc1, hc2⟩
    have h0 : ind p (a, false) (c, false) = 0 := by
      rw [ind_eq_zero_iff]
      intro hc
      rcases out_nbr_O p a hc with h | h | h
      · exact hc1 (congrArg Prod.fst h)
      · exact hc2 (congrArg Prod.fst h)
      · simp at h
    rw [h0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- 内輪の頂点 `I_a` から出るダーツの変位の和。 -/
theorem sum_disp_I [NeZero n] (p : (GP n 3).Walk u u) (h6 : (6 : ZMod n) ≠ 0) (a : ZMod n) :
    ∑ b : ZMod n, ind p (a, true) (b, true) * disp (a, true) (b, true)
      = 3 * ind p (a, true) (a + 3, true) - 3 * ind p (a, true) (a - 3, true) := by
  have hne : a + 3 ≠ a - 3 := fun h => h6 (by linear_combination h)
  rw [Finset.sum_eq_add (a + 3) (a - 3) hne]
  · rw [disp_tt, disp_tt, if_pos rfl, if_neg (fun h => hne (by linear_combination -h))]
    ring
  · intro c _ ⟨hc1, hc2⟩
    have h0 : ind p (a, true) (c, true) = 0 := by
      rw [ind_eq_zero_iff]
      intro hc
      rcases out_nbr_I p a hc with h | h | h
      · exact hc1 (congrArg Prod.fst h)
      · exact hc2 (congrArg Prod.fst h)
      · simp at h
    rw [h0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `WS p` を指示関数の二重和で書く。 -/
theorem WS_eq_sum_ind [NeZero n] (p : (GP n 3).Walk u u) (hp : p.IsTrail) :
    WS p = ∑ z : V n × V n, ind p z.1 z.2 * disp z.1 z.2 := by
  have hnd : (p.darts.map Dart.toProd).Nodup :=
    (darts_nodup_of_isTrail hp).map (fun δ δ' h => Dart.ext _ _ h)
  have h1 : WS p = ∑ z ∈ (p.darts.map Dart.toProd).toFinset, disp z.1 z.2 := by
    rw [WS, WSl, List.sum_toFinset _ hnd]
  have hmem : ∀ z : V n × V n, z ∈ (p.darts.map Dart.toProd).toFinset ↔ HasDart p z.1 z.2 := by
    intro z
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨δ, hδ, rfl⟩; exact ⟨δ, hδ, rfl, rfl⟩
    · rintro ⟨δ, hδ, h1, h2⟩; exact ⟨δ, hδ, Prod.ext h1 h2⟩
  have h3 : ∑ z ∈ (p.darts.map Dart.toProd).toFinset, disp z.1 z.2
      = ∑ z ∈ (p.darts.map Dart.toProd).toFinset, ind p z.1 z.2 * disp z.1 z.2 := by
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [(ind_eq_one_iff p _ _).mpr ((hmem z).mp hz), one_mul]
  rw [h1, h3]
  refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
  rw [(ind_eq_zero_iff p _ _).mpr (fun h => hz ((hmem z).mpr h)), zero_mul]

/-- **並べ替え**：`WS p = Σ oW + 3 Σ iW`。 -/
theorem WS_eq_flow [NeZero n] (p : (GP n 3).Walk u u) (hp : p.IsTrail) (h2 : (2 : ZMod n) ≠ 0)
    (h6 : (6 : ZMod n) ≠ 0) :
    WS p = ∑ j : ZMod n, oW p j + 3 * ∑ j : ZMod n, iW p j := by
  rw [WS_eq_sum_ind p hp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [disp_ft, disp_tf, mul_zero, add_zero, zero_add]
  simp only [sum_disp_O p h2, sum_disp_I p h6, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  have eO : ∑ a : ZMod n, ind p (a, false) (a - 1, false)
      = ∑ a : ZMod n, ind p (a + 1, false) (a, false) := by
    rw [← sum_shift (fun a : ZMod n => ind p (a + 1, false) (a, false)) 1]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show a - 1 + 1 = a by ring]
  have eI : ∑ a : ZMod n, ind p (a, true) (a - 3, true)
      = ∑ a : ZMod n, ind p (a + 3, true) (a, true) := by
    rw [← sum_shift (fun a : ZMod n => ind p (a + 3, true) (a, true)) 3]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show a - 3 + 3 = a by ring]
  simp only [oW, iW, Finset.sum_sub_distrib]
  rw [eO, eI]
  ring

/-! ### E. `m` 周の接続と総合 -/

/-- `P`（`u` から `ρ^d u` へ）を `ρ^{dk}` で写しながら `k` 回繋ぐ。 -/
theorem exists_loop_darts (p : (GP n 3).Walk u u) {d : ℕ} (hD : DartInv p d)
    (P : (GP n 3).Walk u (((rot n) ^ d) u)) (hP : ∀ δ ∈ P.darts, δ ∈ p.darts) :
    ∀ k : ℕ, ∃ (y : V n) (q : (GP n 3).Walk u y), y = ((rot n) ^ (d * k)) u ∧
      (∀ δ ∈ q.darts, δ ∈ p.darts) ∧ WS q = k * WS P := by
  intro k
  induction k with
  | zero => exact ⟨u, Walk.nil, by simp, by simp, by simp [WS_nil]⟩
  | succ k ih =>
      obtain ⟨y, q, hy, hq, hWS⟩ := ih
      subst hy
      obtain ⟨P', hP', -⟩ := exists_shift_darts (d * k) P
      have hend : ((rot n) ^ (d * k)) (((rot n) ^ d) u) = ((rot n) ^ (d * (k + 1))) u := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show d * k + d = d * (k + 1) by ring]
      refine ⟨_, q.append P', hend, ?_, ?_⟩
      · intro δ hδ
        rw [Walk.darts_append, List.mem_append] at hδ
        rcases hδ with hδ | hδ
        · exact hq δ hδ
        · have hz : δ.toProd ∈ P'.darts.map Dart.toProd := List.mem_map.mpr ⟨δ, hδ, rfl⟩
          rw [hP'] at hz
          obtain ⟨δ0, hδ0, he⟩ := List.mem_map.mp hz
          have h0 : HasDart p δ0.fst δ0.snd := ⟨δ0, hP δ0 hδ0, rfl, rfl⟩
          have h1 := dartInv_pow p hD k _ _ h0
          refine mem_darts_of_hasDart p δ ?_
          have e1 : δ.fst = ((rot n) ^ (d * k)) δ0.fst := (congrArg Prod.fst he).symm
          have e2 : δ.snd = ((rot n) ^ (d * k)) δ0.snd := (congrArg Prod.snd he).symm
          rw [e1, e2]; exact h1
      · rw [WS_append, hWS, WS_of_shift (d * k) P P' hP']
        push_cast; ring

/-- **`WindingBridge n` が閉じる**（`n` 奇でなくてもよい）。 -/
theorem windingBridge [NeZero n] : WindingBridge n := by
  intro u p hp h2 h6 d _ hd hdn hD j
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  -- 商の `W` は上側の `W`、上側の `W` は定数 `w`
  set T := hamTF p hp h2 h6 with hT
  set w := T.toFlow.W 0 with hw
  have hwc : ∀ x, T.toFlow.W x = w := fun x => T.toFlow.W_const x 0
  have hWq : (quotTF p hp h2 h6 d hd hD).toFlow.W j = w := by
    rw [← castHom_lift hd j]
    exact (TwoFactor.descend_W_eq (hamTF p hp h2 h6) hd _ _ _ (lift d n j)).trans (hwc _)
  rw [hWq]
  intro hw0
  -- `n w = WS p`
  have hwind := T.toFlow.winding w hwc
  have hWS : WS p = (n : ℤ) * w := by
    rw [hwind, WS_eq_flow p hp.isCycle.isCircuit.isTrail h2 h6]
    rfl
  -- `P := p.takeUntil (ρ^d u)`
  have hmem : ((rot n) ^ d) u ∈ p.support := hp.mem_support _
  have hPd : ∀ δ ∈ (p.takeUntil _ hmem).darts, δ ∈ p.darts :=
    fun δ h => Walk.darts_takeUntil_subset_darts p hmem h
  have hPcast : ((WS (p.takeUntil _ hmem) : ℤ) : ZMod n) = (d : ZMod n) := by
    rw [WS_cast h2 h6, rot_pow_apply]
    simp
  -- `m` 周
  have hd' := hd
  obtain ⟨m, hm⟩ := hd'
  obtain ⟨y, Q, hy, hQd, hQWS⟩ := exists_loop_darts p hD (p.takeUntil _ hmem) hPd m
  have hyu : y = u := by
    rw [hy, ← hm, rot_pow_card]; rfl
  obtain ⟨j', hj', -⟩ := closed_walk_darts hp.isCycle Q.length Q rfl hyu hQd rfl
  have hQWS' : WS Q = j' * WS p := by
    unfold WS
    rw [hj', List.map_flatten, List.map_replicate, WSl_flatten_replicate]
  -- `m · WS P = j' · n · w = 0`
  have hm0 : (m : ℤ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hm
    exact NeZero.ne n hm
  have hP0 : WS (p.takeUntil _ hmem) = 0 := by
    have : (m : ℤ) * WS (p.takeUntil _ hmem) = 0 := by
      rw [← hQWS, hQWS', hWS, hw0]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hm0
    · exact h
  have hd0 : (d : ZMod n) = 0 := by rw [← hPcast, hP0]; simp
  rw [ZMod.natCast_eq_zero_iff] at hd0
  exact absurd (Nat.le_of_dvd hdpos hd0) (by omega)

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ### 1. 後者写像 -/

/-- ハミルトン閉路の後者写像。 -/
noncomputable def nxt {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) (v : V) : V :=
  (exists_out_dart hp.isCycle (hp.mem_support v)).choose.snd

theorem hasDart_nxt {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) (v : V) :
    HasDart p v (nxt hp v) := by
  obtain ⟨hδ, hv⟩ := (exists_out_dart hp.isCycle (hp.mem_support v)).choose_spec
  exact ⟨_, hδ, hv, rfl⟩

/-- 出るダーツは一つなので、`HasDart p v y` なら `y = nxt v`。 -/
theorem nxt_eq {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) {v y : V}
    (h : HasDart p v y) : nxt hp v = y := by
  obtain ⟨a, b, -, hout, -⟩ := cycle_local' hp.isCycle (hp.mem_support v)
  rw [(hout _).mp (hasDart_nxt hp v), (hout _).mp h]

/-- 入る元は行き先と異なる。 -/
theorem nxt_ne_of_hasDart {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) {v b : V}
    (hb : HasDart p b v) : nxt hp v ≠ b := by
  obtain ⟨a, b', hab, hout, hin⟩ := cycle_local' hp.isCycle (hp.mem_support v)
  rw [(hout _).mp (hasDart_nxt hp v)]
  rw [(hin _).mp hb]
  exact hab

/-- **強制手**：`b → v` があり、`v` から出る先の候補が `{b, c}` なら `nxt v = c`。 -/
theorem nxt_forced {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) {v b c : V}
    (hb : HasDart p b v) (hc : ∀ y, HasDart p v y → y = b ∨ y = c) : nxt hp v = c := by
  rcases hc _ (hasDart_nxt hp v) with h | h
  · exact absurd h (nxt_ne_of_hasDart hp hb)
  · exact h

/-! ### 2. 歩道に沿った反復 -/

/-- `p` のダーツだけを使う歩道 `q : a → b` に沿って、`nxt^[q.length] a = b`。 -/
theorem nxt_iterate_walk {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) :
    ∀ {a b : V} (q : G.Walk a b), (∀ δ ∈ q.darts, δ ∈ p.darts) →
      (nxt hp)^[q.length] a = b := by
  intro a b q
  induction q with
  | nil => intro _; simp
  | @cons a c b h q ih =>
      intro hq
      have hac : HasDart p a c := ⟨⟨(a, c), h⟩, hq _ (by simp [Walk.darts_cons]), rfl, rfl⟩
      rw [Walk.length_cons, Function.iterate_succ_apply, nxt_eq hp hac]
      exact ih (fun δ hδ => hq δ (by simp [Walk.darts_cons, hδ]))

/-- `p` のダーツだけを使う歩道 `q : a → b` の台の点は `a` から `nxt` の反復で届く。 -/
theorem nxt_reach_walk {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) :
    ∀ {a b : V} (q : G.Walk a b), (∀ δ ∈ q.darts, δ ∈ p.darts) →
      ∀ z ∈ q.support, ∃ k, (nxt hp)^[k] a = z := by
  intro a b q
  induction q with
  | nil =>
      intro _ z hz
      rw [Walk.support_nil, List.mem_singleton] at hz
      exact ⟨0, by simp [hz]⟩
  | @cons a c b h q ih =>
      intro hq z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨0, by simp⟩
      · obtain ⟨k, hk⟩ := ih (fun δ hδ => hq δ (by simp [Walk.darts_cons, hδ])) z hz
        have hac : HasDart p a c := ⟨⟨(a, c), h⟩, hq _ (by simp [Walk.darts_cons]), rfl, rfl⟩
        exact ⟨k + 1, by rw [Function.iterate_succ_apply, nxt_eq hp hac, hk]⟩

/-- **推移性**：任意の `x, y` は `nxt` の反復で結ばれる。 -/
theorem nxt_reach {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) (x y : V) :
    ∃ k, (nxt hp)^[k] x = y := by
  have hx : x ∈ p.support := hp.mem_support x
  have hyt : y ∈ p.support.tail := by
    have hy := hp.mem_support y
    rw [← Walk.cons_tail_support p, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Walk.end_mem_tail_support hp.isCycle.not_nil
    · exact hy
  have hy' : y ∈ (p.rotate x hx).support :=
    List.mem_of_mem_tail ((Walk.support_rotate p x hx).mem_iff.mpr hyt)
  exact nxt_reach_walk hp (p.rotate x hx)
    (fun δ hδ => (Walk.rotate_darts p x hx).mem_iff.mp hδ) y hy'

/-- 一周すると戻る：`0 < K` で `nxt^[K] x = x`。 -/
theorem nxt_return {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) (x : V) :
    ∃ K, 0 < K ∧ (nxt hp)^[K] x = x := by
  have hx : x ∈ p.support := hp.mem_support x
  refine ⟨(p.rotate x hx).length, ?_, ?_⟩
  · rw [Walk.length_rotate]
    have := hp.isCycle.three_le_length
    omega
  · exact nxt_iterate_walk hp (p.rotate x hx) (fun δ hδ => (Walk.rotate_darts p x hx).mem_iff.mp hδ)

/-! ### 3. 逆向き -/

/-- 逆向きのダーツ。 -/
theorem hasDart_reverse {a b : V} (q : G.Walk a b) (x y : V) :
    HasDart q.reverse x y ↔ HasDart q y x := by
  constructor
  · rintro ⟨δ, hδ, h1, h2⟩
    rw [Walk.darts_reverse, List.mem_reverse, List.mem_map] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    exact ⟨δ', hδ', by simpa using h2, by simpa using h1⟩
  · rintro ⟨δ, hδ, h1, h2⟩
    refine ⟨δ.symm, ?_, by simpa using h2, by simpa using h1⟩
    rw [Walk.darts_reverse, List.mem_reverse, List.mem_map]
    exact ⟨δ, hδ, rfl⟩

/-- 逆向きもハミルトン閉路。 -/
theorem IsHamiltonianCycle.reverse' {u : V} {p : G.Walk u u} (hp : p.IsHamiltonianCycle) :
    p.reverse.IsHamiltonianCycle := by
  classical
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hp ⊢
  refine ⟨hp.1.reverse, fun a => ?_⟩
  rw [Walk.support_reverse, List.tail_reverse, List.count_reverse,
    ← (p.tail_support_perm_dropLast_support).count_eq]
  exact hp.2 a

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count

/-! ### 1. `Win d` の次数条件から出るスポークの有無 -/

namespace WinAux

variable {d : ℕ}

theorem abs_eq_one_of_mem {z : ℤ} (hm : z = 0 ∨ z = 1 ∨ z = -1) (h : z ≠ 0) : |z| = 1 := by
  rcases hm with h0 | h1 | h1
  · exact absurd h0 h
  · rw [h1]; norm_num
  · rw [h1]; norm_num

/-- `G_i` の点ではスポークを使う。 -/
theorem sp_ne_zero_of_i_zero (F : Win d) (r : ZMod d) (h : F.i r = 0) : F.sp r ≠ 0 := by
  intro hs
  have hd := F.degI r
  rw [h, hs] at hd
  have h1 : |F.i (r - 3)| ≤ 1 := by
    rcases F.i_mem (r - 3) with h0 | h0 | h0 <;> rw [h0] <;> norm_num
  simp at hd
  omega

/-- 両側の内辺があればスポークは無い。 -/
theorem sp_eq_zero_of_i (F : Win d) (r : ZMod d) (h1 : F.i (r - 3) ≠ 0) (h2 : F.i r ≠ 0) :
    F.sp r = 0 := by
  have hd := F.degI r
  rw [abs_eq_one_of_mem (F.i_mem _) h1, abs_eq_one_of_mem (F.i_mem _) h2] at hd
  exact abs_eq_zero.mp (by linarith)

/-- 両側の外辺があればスポークは無い。 -/
theorem sp_eq_zero_of_o (F : Win d) (j : ZMod d) (h1 : F.o (j - 1) ≠ 0) (h2 : F.o j ≠ 0) :
    F.sp j = 0 := by
  have hd := F.degO j
  rw [abs_eq_one_of_mem (F.o_mem _) h1, abs_eq_one_of_mem (F.o_mem _) h2] at hd
  exact abs_eq_zero.mp (by linarith)

end WinAux

/-! ### 2. 上側：欠けた辺にダーツは無い -/

variable {n : ℕ} {u : V n}

theorem no_dart_of_iW_zero (p : (GP n 3).Walk u u) (hp : p.IsTrail) {x : ZMod n}
    (h : iW p x = 0) : ¬ HasDart p (x, true) (x + 3, true) ∧ ¬ HasDart p (x + 3, true) (x, true) := by
  simp only [iW] at h
  have h1 := ind_nonneg p (x, true) (x + 3, true)
  have h2 := ind_nonneg p (x + 3, true) (x, true)
  rcases ind_mul_rev p hp (x, true) (x + 3, true) with h0 | h0
  · have : ind p (x + 3, true) (x, true) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp h0, (ind_eq_zero_iff p _ _).mp this⟩
  · have : ind p (x, true) (x + 3, true) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp this, (ind_eq_zero_iff p _ _).mp h0⟩

theorem no_dart_of_oW_zero (p : (GP n 3).Walk u u) (hp : p.IsTrail) {x : ZMod n}
    (h : oW p x = 0) :
    ¬ HasDart p (x, false) (x + 1, false) ∧ ¬ HasDart p (x + 1, false) (x, false) := by
  simp only [oW] at h
  have h1 := ind_nonneg p (x, false) (x + 1, false)
  have h2 := ind_nonneg p (x + 1, false) (x, false)
  rcases ind_mul_rev p hp (x, false) (x + 1, false) with h0 | h0
  · have : ind p (x + 1, false) (x, false) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp h0, (ind_eq_zero_iff p _ _).mp this⟩
  · have : ind p (x, false) (x + 1, false) = 0 := by linarith
    exact ⟨(ind_eq_zero_iff p _ _).mp this, (ind_eq_zero_iff p _ _).mp h0⟩

/-- ダーツがあれば `iW ≠ 0`（`x → x+3` の向き）。 -/
theorem iW_ne_zero_of_hasDart (p : (GP n 3).Walk u u) (hp : p.IsTrail) {x : ZMod n}
    (h : HasDart p (x, true) (x + 3, true) ∨ HasDart p (x + 3, true) (x, true)) : iW p x ≠ 0 := by
  intro h0
  have := no_dart_of_iW_zero p hp h0
  rcases h with h | h
  · exact this.1 h
  · exact this.2 h

/-! ### 3. 逆向きの歩道での `iW`・`oW`・`spW` -/

theorem ind_reverse (p : (GP n 3).Walk u u) (x y : V n) : ind p.reverse x y = ind p y x := by
  unfold ind
  simp only [hasDart_reverse]

theorem iW_reverse (p : (GP n 3).Walk u u) (x : ZMod n) : iW p.reverse x = -iW p x := by
  simp only [iW, ind_reverse]; ring

theorem oW_reverse (p : (GP n 3).Walk u u) (x : ZMod n) : oW p.reverse x = -oW p x := by
  simp only [oW, ind_reverse]; ring

theorem spW_reverse (p : (GP n 3).Walk u u) (x : ZMod n) : spW p.reverse x = -spW p x := by
  simp only [spW, ind_reverse]; ring

/-! ### 4. 辞書 -/

variable {d : ℕ}

/-- **辞書**：上側の欠けと商の欠けが一致する（符号は問わない）。 -/
structure Dict (p : (GP n 3).Walk u u) (hd : d ∣ n) (F : Win d) : Prop where
  i_iff : ∀ x : ZMod n, iW p x = 0 ↔ F.i (ZMod.castHom hd (ZMod d) x) = 0
  o_iff : ∀ x : ZMod n, oW p x = 0 ↔ F.o (ZMod.castHom hd (ZMod d) x) = 0
  sp_iff : ∀ x : ZMod n, spW p x = 0 ↔ F.sp (ZMod.castHom hd (ZMod d) x) = 0

theorem Dict.reverse {p : (GP n 3).Walk u u} {hd : d ∣ n} {F : Win d} (h : Dict p hd F) :
    Dict p.reverse hd F where
  i_iff := fun x => by rw [iW_reverse, neg_eq_zero]; exact h.i_iff x
  o_iff := fun x => by rw [oW_reverse, neg_eq_zero]; exact h.o_iff x
  sp_iff := fun x => by rw [spW_reverse, neg_eq_zero]; exact h.sp_iff x

theorem quotTF_sp [NeZero n] (p : (GP n 3).Walk u u) (hp) (h2) (h6) (d : ℕ) [NeZero d] (hd : d ∣ n)
    (hD : DartInv p d) (x : ZMod n) :
    (quotTF p hp h2 h6 d hd hD).sp (ZMod.castHom hd (ZMod d) x) = spW p x :=
  ((periodic_spW p hD).eq_lift hd x).symm

/-- `Agrees` と `quotTF` から辞書が出る。 -/
theorem dict_of_agrees [NeZero n] (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle)
    (h2 : (2 : ZMod n) ≠ 0) (h6 : (6 : ZMod n) ≠ 0) [NeZero d] (hd : d ∣ n) (hD : DartInv p d)
    (F : Win d) (hF : Agrees F (quotTF p hp h2 h6 d hd hD)) : Dict p hd F where
  i_iff := fun x => by
    rw [← quotTF_i p hp h2 h6 d hd hD x]
    rcases hF with h | h
    · rw [(h _).2.1]
    · rw [(h _).2.1]; simp
  o_iff := fun x => by
    rw [← quotTF_o p hp h2 h6 d hd hD x]
    rcases hF with h | h
    · rw [(h _).1]
    · rw [(h _).1]; simp
  sp_iff := fun x => by
    rw [← quotTF_sp p hp h2 h6 d hd hD x]
    rcases hF with h | h
    · rw [(h _).2.2]
    · rw [(h _).2.2]; simp

/-! ### 5. `ret`・`prev` の値の決定 -/

variable [NeZero d]

/-- 最初に `G_i` に当たる歩数（歩幅 `+3`）が `T`（`0 < T ≤ d`）なら `ret r = r + 3T`。 -/
theorem ret_eq_of_first (F : Win d) (r : ZMod d) (T : ℕ) (hT : 0 < T) (hTd : T ≤ d)
    (hr : F.i (r + 3 * (T : ZMod d)) = 0) (hmin : ∀ t, 0 < t → t < T → F.i (r + 3 * (t : ZMod d)) ≠ 0) :
    ret F r = r + 3 * (T : ZMod d) := by
  have hle : retT F r ≤ T := Nat.find_le ⟨hT, Or.inr hr⟩
  have hge : T ≤ retT F r := by
    by_contra hlt
    push Not at hlt
    have hspec : retP F r (retT F r) := Nat.find_spec (retP_ex F r)
    rcases hspec.2 with hge | h0
    · omega
    · exact hmin _ (retT_pos F r) hlt h0
  have : retT F r = T := le_antisymm hle hge
  rw [ret, this]

/-- 最初に `G_i` に当たる歩数（歩幅 `−1`）が `T`（`0 < T ≤ d`）なら `prev r = r − T`。 -/
theorem prev_eq_of_first (F : Win d) (r : ZMod d) (T : ℕ) (hT : 0 < T) (hTd : T ≤ d)
    (hr : F.i (r - (T : ZMod d)) = 0) (hmin : ∀ t, 0 < t → t < T → F.i (r - (t : ZMod d)) ≠ 0) :
    prev F r = r - (T : ZMod d) := by
  have hle : prevT F r ≤ T := Nat.find_le ⟨hT, Or.inr hr⟩
  have hge : T ≤ prevT F r := by
    by_contra hlt
    push Not at hlt
    have hspec : prevP F r (prevT F r) := Nat.find_spec (prevP_ex F r)
    rcases hspec.2 with hge | h0
    · omega
    · exact hmin _ (prevT_pos F r) hlt h0
  have : prevT F r = T := le_antisymm hle hge
  rw [prev, this]

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count

variable {n : ℕ} [NeZero n] {u : V n} {d : ℕ} [NeZero d]

section Trace

variable (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (hd : d ∣ n) (F : Win d)
  (hodd : Odd d) (hDict : Dict p hd F)

/-! ### 1. 辞書で降ろした `Win` の性質 -/

include hDict in
theorem U_no_gap (x : ZMod n) (h : iW p x = 0) : iW p (x + 3) ≠ 0 := by
  intro h3
  rw [hDict.i_iff] at h h3
  simp only [map_add, map_ofNat] at h3
  exact F.no_gap_dist_three _ ⟨h, h3⟩

include hDict in
theorem U_no_three (x : ZMod n) (h0 : iW p x = 0) (h1 : iW p (x + 1) = 0) : iW p (x + 2) ≠ 0 := by
  intro h2
  rw [hDict.i_iff] at h0 h1 h2
  simp only [map_add, map_ofNat, map_one] at h1 h2
  exact F.no_three_consecutive _ ⟨h0, h1, h2⟩

include hDict hodd in
theorem U_odd_pair (x : ZMod n) (h : iW p x = 0) : iW p (x + 1) = 0 ∨ iW p (x - 1) = 0 := by
  rw [hDict.i_iff] at h
  rw [hDict.i_iff, hDict.i_iff]
  simp only [map_add, map_sub, map_one]
  exact odd_pair F hodd h

include hDict hodd in
theorem U_outer_zero_iff (j : ZMod n) :
    oW p j = 0 ↔ (iW p j = 0 ∧ iW p (j + 1) = 0) ∨ (iW p (j - 3) = 0 ∧ iW p (j - 2) = 0) := by
  rw [hDict.o_iff, hDict.i_iff, hDict.i_iff, hDict.i_iff, hDict.i_iff]
  simp only [map_add, map_sub, map_one, map_ofNat]
  exact outer_zero_iff F hodd _

include hDict in
theorem U_sp_ne_zero (x : ZMod n) (h : iW p x = 0) : spW p x ≠ 0 := by
  rw [hDict.i_iff] at h
  rw [Ne, hDict.sp_iff]
  exact WinAux.sp_ne_zero_of_i_zero F _ h

include hDict in
theorem U_sp_zero_of_i (x : ZMod n) (h1 : iW p (x - 3) ≠ 0) (h2 : iW p x ≠ 0) : spW p x = 0 := by
  rw [Ne, hDict.i_iff] at h1 h2
  rw [hDict.sp_iff]
  simp only [map_sub, map_ofNat] at h1
  exact WinAux.sp_eq_zero_of_i F _ h1 h2

include hDict in
theorem U_sp_zero_of_o (j : ZMod n) (h1 : oW p (j - 1) ≠ 0) (h2 : oW p j ≠ 0) : spW p j = 0 := by
  rw [Ne, hDict.o_iff] at h1 h2
  rw [hDict.sp_iff]
  simp only [map_sub, map_one] at h1
  exact WinAux.sp_eq_zero_of_o F _ h1 h2

include hDict in
theorem U_block_sep (b : ZMod n) (h0 : iW p b = 0) (h1 : iW p (b + 1) = 0) :
    iW p (b + 2) ≠ 0 ∧ iW p (b + 3) ≠ 0 ∧ iW p (b + 4) ≠ 0 ∧ iW p (b - 1) ≠ 0 ∧ iW p (b - 2) ≠ 0
      ∧ iW p (b - 3) ≠ 0 := by
  rw [hDict.i_iff] at h0 h1
  simp only [map_add, map_one] at h1
  simp only [Ne, hDict.i_iff, map_add, map_sub, map_ofNat, map_one]
  exact block_sep F h0 h1

include hDict in
/-- 零であることは商で決まる。 -/
theorem U_zero_iff_of_castHom_eq (y y' : ZMod n)
    (h : ZMod.castHom hd (ZMod d) y = ZMod.castHom hd (ZMod d) y') : iW p y = 0 ↔ iW p y' = 0 := by
  rw [hDict.i_iff, hDict.i_iff, h]

/-! ### 2. 強制手（`GP(n,3)` 版） -/

include hp in
theorem nxt_O_spoke (a : ZMod n) (h1 : ¬ HasDart p (a, false) (a + 1, false))
    (h2 : ¬ HasDart p (a, false) (a - 1, false)) : nxt hp (a, false) = (a, true) := by
  rcases out_nbr_O p a (hasDart_nxt hp (a, false)) with h | h | h
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h1
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h2
  · exact h

include hp in
theorem nxt_O_up (a : ZMod n) (h2 : ¬ HasDart p (a, false) (a - 1, false))
    (h3 : ¬ HasDart p (a, false) (a, true)) : nxt hp (a, false) = (a + 1, false) := by
  rcases out_nbr_O p a (hasDart_nxt hp (a, false)) with h | h | h
  · exact h
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h2
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h3

include hp in
theorem nxt_O_down (a : ZMod n) (h1 : ¬ HasDart p (a, false) (a + 1, false))
    (h3 : ¬ HasDart p (a, false) (a, true)) : nxt hp (a, false) = (a - 1, false) := by
  rcases out_nbr_O p a (hasDart_nxt hp (a, false)) with h | h | h
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h1
  · exact h
  · exact absurd (h ▸ hasDart_nxt hp (a, false)) h3

include hp in
theorem nxt_I_spoke (a : ZMod n) (h1 : ¬ HasDart p (a, true) (a + 3, true))
    (h2 : ¬ HasDart p (a, true) (a - 3, true)) : nxt hp (a, true) = (a, false) := by
  rcases out_nbr_I p a (hasDart_nxt hp (a, true)) with h | h | h
  · exact absurd (h ▸ hasDart_nxt hp (a, true)) h1
  · exact absurd (h ▸ hasDart_nxt hp (a, true)) h2
  · exact h

include hp in
theorem nxt_I_down (a : ZMod n) (h1 : ¬ HasDart p (a, true) (a + 3, true))
    (h3 : ¬ HasDart p (a, true) (a, false)) : nxt hp (a, true) = (a - 3, true) := by
  rcases out_nbr_I p a (hasDart_nxt hp (a, true)) with h | h | h
  · exact absurd (h ▸ hasDart_nxt hp (a, true)) h1
  · exact h
  · exact absurd (h ▸ hasDart_nxt hp (a, true)) h3

/-! ### 3. 跡付け -/

include hp hodd hDict in
/-- **跡付けの補題**。 -/
theorem trace (x : ZMod n) (hx : iW p x = 0) (hdir : HasDart p (x, false) (x, true)) :
    ∃ (t : ℕ) (x' : ZMod n), 0 < t ∧ (nxt hp)^[t] (x, false) = (x', false) ∧ iW p x' = 0 ∧
      HasDart p (x', false) (x', true) ∧
      ret F (prev F (ZMod.castHom hd (ZMod d) x')) = ZMod.castHom hd (ZMod d) x ∧
      ∀ s, 0 < s → s < t → ∀ z, (nxt hp)^[s] (x, false) = (z, false) → iW p z ≠ 0 := by
  have ht := hp.isCycle.isCircuit.isTrail
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  -- ### 内側：歩幅 −3 で最初に `G_i` に当たる歩数 `S+1`
  have hS_ex : ∃ s : ℕ, iW p (x - 3 * ((s + 1 : ℕ) : ZMod n)) = 0 := by
    refine ⟨n - 1, ?_⟩
    rw [Nat.sub_add_cancel hn1, ZMod.natCast_self, mul_zero, sub_zero]
    exact hx
  set S := Nat.find hS_ex with hSdef
  have hS_spec : iW p (x - 3 * ((S + 1 : ℕ) : ZMod n)) = 0 := Nat.find_spec hS_ex
  have hS_min : ∀ s, s < S → iW p (x - 3 * ((s + 1 : ℕ) : ZMod n)) ≠ 0 :=
    fun s hs => Nat.find_min hS_ex hs
  have hS_pos : 1 ≤ S := by
    by_contra h0
    have h0' : S = 0 := by omega
    have := hS_spec
    rw [h0'] at this
    simp only [Nat.zero_add, Nat.cast_one, mul_one] at this
    exact U_no_gap p hd F hDict (x - 3) this (by rw [sub_add_cancel]; exact hx)
  have hS_le : S + 1 ≤ d := by
    have : S ≤ d - 1 := Nat.find_le (by
      rw [Nat.sub_add_cancel hd1]
      refine (U_zero_iff_of_castHom_eq p hd F hDict _ x ?_).mpr hx
      rw [map_sub, map_mul, map_ofNat, map_natCast, ZMod.natCast_self, mul_zero, sub_zero])
    omega
  -- 内側の道
  have hnxt0 : nxt hp (x, false) = (x, true) := nxt_eq hp hdir
  have inner : ∀ s, 1 ≤ s → s ≤ S →
      (nxt hp)^[s + 1] (x, false) = (x - 3 * (s : ZMod n), true) ∧
      HasDart p (x - 3 * (s : ZMod n) + 3, true) (x - 3 * (s : ZMod n), true) := by
    intro s hs1
    induction s, hs1 using Nat.le_induction with
    | base =>
        intro _
        have h1 : nxt hp (x, true) = (x - 3, true) :=
          nxt_I_down p hp x (no_dart_of_iW_zero p ht hx).1 (hdir.not_rev ht)
        have e1 : x - 3 * ((1 : ℕ) : ZMod n) = x - 3 := by push_cast; ring
        have e2 : x - 3 * ((1 : ℕ) : ZMod n) + 3 = x := by push_cast; ring
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', Function.iterate_one, hnxt0, h1, e1]
        · convert h1 ▸ hasDart_nxt hp (x, true) using 3 <;> push_cast <;> ring
    | succ s hs ih =>
        intro hsS
        obtain ⟨hv, hin⟩ := ih (by omega)
        have hm3 : iW p (x - 3 * (s : ZMod n) - 3) ≠ 0 := by
          have := hS_min s (by omega)
          rwa [show x - 3 * ((s + 1 : ℕ) : ZMod n) = x - 3 * (s : ZMod n) - 3 by push_cast; ring] at this
        have hm0 : iW p (x - 3 * (s : ZMod n)) ≠ 0 := by
          have := hS_min (s - 1) (by omega)
          rwa [show ((s - 1 + 1 : ℕ) : ZMod n) = (s : ZMod n) by rw [Nat.sub_add_cancel hs]] at this
        have hsp : spW p (x - 3 * (s : ZMod n)) = 0 := U_sp_zero_of_i p hd F hDict _ hm3 hm0
        have hnx : nxt hp (x - 3 * (s : ZMod n), true) = (x - 3 * (s : ZMod n) - 3, true) :=
          nxt_I_down p hp _ (hin.not_rev ht) (no_spoke_of_spW_zero p ht hsp).2
        have e1 : x - 3 * ((s + 1 : ℕ) : ZMod n) = x - 3 * (s : ZMod n) - 3 := by push_cast; ring
        have e2 : x - 3 * ((s + 1 : ℕ) : ZMod n) + 3 = x - 3 * (s : ZMod n) := by push_cast; ring
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', hv, hnx, e1]
        · convert hnx ▸ hasDart_nxt hp (x - 3 * (s : ZMod n), true) using 3 <;> push_cast <;> ring
  obtain ⟨hvS, hinS⟩ := inner S hS_pos le_rfl
  -- `z₀`
  obtain ⟨z0, hz0def⟩ : ∃ z0 : ZMod n, z0 = x - 3 * ((S + 1 : ℕ) : ZMod n) := ⟨_, rfl⟩
  have hz0 : iW p z0 = 0 := by rw [hz0def]; exact hS_spec
  have ey : x - 3 * (S : ZMod n) = z0 + 3 := by rw [hz0def]; push_cast; ring
  rw [ey] at hvS hinS
  have hxz0 : x = z0 + 3 * ((S + 1 : ℕ) : ZMod n) := by rw [hz0def]; ring
  -- `I_{z₀+3} → O_{z₀+3}`
  have hnxtY : nxt hp (z0 + 3, true) = (z0 + 3, false) := by
    refine nxt_I_spoke p hp _ (hinS.not_rev ht) ?_
    have := (no_dart_of_iW_zero p ht hz0).2
    rwa [show z0 + 3 - 3 = z0 by ring]
  have hvS2 : (nxt hp)^[S + 2] (x, false) = (z0 + 3, false) := by
    rw [show S + 2 = S + 1 + 1 by ring, Function.iterate_succ_apply', hvS, hnxtY]
  have hinY : HasDart p (z0 + 3, true) (z0 + 3, false) := hnxtY ▸ hasDart_nxt hp _
  -- 商：`ret (π z₀) = π x`
  have hret : ret F (ZMod.castHom hd (ZMod d) z0) = ZMod.castHom hd (ZMod d) x := by
    have hπx : ZMod.castHom hd (ZMod d) z0 + 3 * ((S + 1 : ℕ) : ZMod d) = ZMod.castHom hd (ZMod d) x := by
      rw [hxz0, map_add, map_mul, map_ofNat, map_natCast]
    rw [ret_eq_of_first F _ (S + 1) (by omega) hS_le]
    · exact hπx
    · rw [hπx]; exact (hDict.i_iff x).mp hx
    · intro t ht0 htS h
      have h' : iW p (z0 + 3 * (t : ZMod n)) = 0 := by
        rw [hDict.i_iff, map_add, map_mul, map_ofNat, map_natCast]; exact h
      refine hS_min (S - t) (by omega) ?_
      have hcast : ((S - t + 1 : ℕ) : ZMod n) = ((S + 1 : ℕ) : ZMod n) - (t : ZMod n) := by
        rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_add]; ring
      rw [hcast, show x - 3 * (((S + 1 : ℕ) : ZMod n) - (t : ZMod n)) = z0 + 3 * (t : ZMod n) by
        rw [hz0def]; ring]
      exact h'
  -- 内側の点は外輪の `G_i` の点ではない
  have hinner_notO : ∀ s, 0 < s → s < S + 2 → ∀ z, (nxt hp)^[s] (x, false) = (z, false) → False := by
    intro s hs0 hs2 z hz
    rcases Nat.lt_or_ge s 2 with h1 | h2
    · have : s = 1 := by omega
      subst this
      rw [Function.iterate_one, hnxt0] at hz
      simp at hz
    · obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      obtain ⟨hv, -⟩ := inner k (by omega) (by omega)
      rw [hv] at hz
      simp at hz
  -- ### 外側：ドミノの左端か右端か
  rcases U_odd_pair p hd F hodd hDict z0 hz0 with hL | hR
  · -- **左端**：`O_{z₀+3} → O_{z₀+2} → O_{z₀+1}`
    have hm1 : iW p (z0 - 1) ≠ 0 := fun h =>
      U_no_three p hd F hDict (z0 - 1) h (by rw [sub_add_cancel]; exact hz0)
        (by rw [show z0 - 1 + 2 = z0 + 1 by ring]; exact hL)
    have hp2 : iW p (z0 + 2) ≠ 0 := U_no_three p hd F hDict z0 hz0 hL
    have hp3 : iW p (z0 + 3) ≠ 0 := U_no_gap p hd F hDict z0 hz0
    have ho3 : oW p (z0 + 3) = 0 :=
      (U_outer_zero_iff p hd F hodd hDict (z0 + 3)).mpr (Or.inr ⟨by rw [add_sub_cancel_right]; exact hz0,
        by rw [show z0 + 3 - 2 = z0 + 1 by ring]; exact hL⟩)
    have hnA : nxt hp (z0 + 3, false) = (z0 + 2, false) := by
      have := nxt_O_down p hp (z0 + 3) (no_dart_of_oW_zero p ht ho3).1 (hinY.not_rev ht)
      rwa [show z0 + 3 - 1 = z0 + 2 by ring] at this
    have hv3 : (nxt hp)^[S + 3] (x, false) = (z0 + 2, false) := by
      rw [show S + 3 = S + 2 + 1 by ring, Function.iterate_succ_apply', hvS2, hnA]
    have hin2 : HasDart p (z0 + 3, false) (z0 + 2, false) := hnA ▸ hasDart_nxt hp _
    have ho2 : oW p (z0 + 2) ≠ 0 := by
      intro h
      rcases (U_outer_zero_iff p hd F hodd hDict (z0 + 2)).mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hp2 h1
      · rw [show z0 + 2 - 3 = z0 - 1 by ring] at h1
        exact hm1 h1
    have ho1 : oW p (z0 + 1) ≠ 0 := by
      intro h
      rcases (U_outer_zero_iff p hd F hodd hDict (z0 + 1)).mp h with ⟨-, h1⟩ | ⟨-, h1⟩
      · rw [show z0 + 1 + 1 = z0 + 2 by ring] at h1
        exact hp2 h1
      · rw [show z0 + 1 - 2 = z0 - 1 by ring] at h1
        exact hm1 h1
    have hsp2 : spW p (z0 + 2) = 0 :=
      U_sp_zero_of_o p hd F hDict (z0 + 2) (by rw [show z0 + 2 - 1 = z0 + 1 by ring]; exact ho1) ho2
    have hnB : nxt hp (z0 + 2, false) = (z0 + 1, false) := by
      have h1 : ¬ HasDart p (z0 + 2, false) (z0 + 2 + 1, false) := by
        rw [show z0 + 2 + 1 = z0 + 3 by ring]; exact hin2.not_rev ht
      have := nxt_O_down p hp (z0 + 2) h1 (no_spoke_of_spW_zero p ht hsp2).1
      rwa [show z0 + 2 - 1 = z0 + 1 by ring] at this
    have hv4 : (nxt hp)^[S + 4] (x, false) = (z0 + 1, false) := by
      rw [show S + 4 = S + 3 + 1 by ring, Function.iterate_succ_apply', hv3, hnB]
    have hin1 : HasDart p (z0 + 2, false) (z0 + 1, false) := hnB ▸ hasDart_nxt hp _
    have ho0 : oW p z0 = 0 := (U_outer_zero_iff p hd F hodd hDict z0).mpr (Or.inl ⟨hz0, hL⟩)
    have hdir' : HasDart p (z0 + 1, false) (z0 + 1, true) := by
      have h1 : ¬ HasDart p (z0 + 1, false) (z0 + 1 + 1, false) := by
        rw [show z0 + 1 + 1 = z0 + 2 by ring]; exact hin1.not_rev ht
      have h2 : ¬ HasDart p (z0 + 1, false) (z0 + 1 - 1, false) := by
        rw [show z0 + 1 - 1 = z0 by ring]; exact (no_dart_of_oW_zero p ht ho0).2
      exact (nxt_O_spoke p hp (z0 + 1) h1 h2) ▸ hasDart_nxt hp _
    have hprev : prev F (ZMod.castHom hd (ZMod d) (z0 + 1)) = ZMod.castHom hd (ZMod d) z0 := by
      rw [prev_eq_of_first F _ 1 one_pos hd1]
      · rw [map_add, map_one, Nat.cast_one, add_sub_cancel_right]
      · rw [map_add, map_one, Nat.cast_one, add_sub_cancel_right]
        exact (hDict.i_iff z0).mp hz0
      · intro t h0 h1; omega
    refine ⟨S + 4, z0 + 1, by omega, hv4, hL, hdir', by rw [hprev, hret], ?_⟩
    intro s hs0 hs4 z hz
    rcases Nat.lt_or_ge s (S + 2) with hlt | hge
    · exact absurd hz (fun h => hinner_notO s hs0 hlt z h)
    · obtain h | h : s = S + 2 ∨ s = S + 3 := by omega
      · subst h
        rw [hvS2] at hz
        simp only [Prod.mk.injEq, and_true] at hz
        rw [← hz]; exact hp3
      · subst h
        rw [hv3] at hz
        simp only [Prod.mk.injEq, and_true] at hz
        rw [← hz]; exact hp2
  · -- **右端**：`O_{z₀+3} → O_{z₀+4} → … → O_z`
    have hp1 : iW p (z0 + 1) ≠ 0 := fun h =>
      U_no_three p hd F hDict (z0 - 1) hR (by rw [sub_add_cancel]; exact hz0)
        (by rw [show z0 - 1 + 2 = z0 + 1 by ring]; exact h)
    obtain ⟨-, hp2, hp3, -, -, -⟩ := U_block_sep p hd F hDict (z0 - 1) hR (by rw [sub_add_cancel]; exact hz0)
    rw [show z0 - 1 + 3 = z0 + 2 by ring] at hp2
    rw [show z0 - 1 + 4 = z0 + 3 by ring] at hp3
    have ho3 : oW p (z0 + 3) ≠ 0 := by
      intro h
      rcases (U_outer_zero_iff p hd F hodd hDict (z0 + 3)).mp h with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact hp3 h1
      · rw [show z0 + 3 - 2 = z0 + 1 by ring] at h1
        exact hp1 h1
    have ho2 : oW p (z0 + 2) = 0 :=
      (U_outer_zero_iff p hd F hodd hDict (z0 + 2)).mpr (Or.inr ⟨by rw [show z0 + 2 - 3 = z0 - 1 by ring]; exact hR,
        by rw [add_sub_cancel_right]; exact hz0⟩)
    have hnC : nxt hp (z0 + 3, false) = (z0 + 4, false) := by
      have h2 : ¬ HasDart p (z0 + 3, false) (z0 + 3 - 1, false) := by
        rw [show z0 + 3 - 1 = z0 + 2 by ring, show z0 + 3 = z0 + 2 + 1 by ring]
        exact (no_dart_of_oW_zero p ht ho2).2
      have := nxt_O_up p hp (z0 + 3) h2 (hinY.not_rev ht)
      rwa [show z0 + 3 + 1 = z0 + 4 by ring] at this
    have hv3 : (nxt hp)^[S + 3] (x, false) = (z0 + 4, false) := by
      rw [show S + 3 = S + 2 + 1 by ring, Function.iterate_succ_apply', hvS2, hnC]
    have hin4 : HasDart p (z0 + 3, false) (z0 + 4, false) := hnC ▸ hasDart_nxt hp _
    -- `Z`：`z₀+1` から歩幅 `+1` で最初に `G_i` に当たる歩数
    have hZ_ex : ∃ k : ℕ, iW p (z0 + 1 + (k : ZMod n)) = 0 := by
      refine ⟨n - 1, ?_⟩
      rw [show z0 + 1 + ((n - 1 : ℕ) : ZMod n) = z0 + ((n : ℕ) : ZMod n) by
        rw [Nat.cast_sub hn1]; push_cast; ring]
      rw [ZMod.natCast_self, add_zero]
      exact hz0
    set Z := Nat.find hZ_ex with hZdef
    have hZ_spec : iW p (z0 + 1 + (Z : ZMod n)) = 0 := Nat.find_spec hZ_ex
    have hZ_min : ∀ k, k < Z → iW p (z0 + 1 + (k : ZMod n)) ≠ 0 := fun k hk => Nat.find_min hZ_ex hk
    have hZ3 : 3 ≤ Z := by
      by_contra h
      obtain h0 | h0 | h0 : Z = 0 ∨ Z = 1 ∨ Z = 2 := by omega
      · rw [h0] at hZ_spec; simp at hZ_spec; exact hp1 hZ_spec
      · rw [h0] at hZ_spec; simp at hZ_spec
        rw [show z0 + 1 + 1 = z0 + 2 by ring] at hZ_spec; exact hp2 hZ_spec
      · rw [h0] at hZ_spec; simp at hZ_spec
        rw [show z0 + 1 + 2 = z0 + 3 by ring] at hZ_spec; exact hp3 hZ_spec
    have hZ_le : Z + 1 ≤ d := by
      have : Z ≤ d - 1 := Nat.find_le (by
        refine (U_zero_iff_of_castHom_eq p hd F hDict _ z0 ?_).mpr hz0
        rw [map_add, map_add, map_one, map_natCast, Nat.cast_sub hd1, ZMod.natCast_self]; ring)
      omega
    -- 外側の道の途中では外辺が使われる
    have houter : ∀ k', 2 ≤ k' → k' < Z → oW p (z0 + 1 + (k' : ZMod n)) ≠ 0 := by
      intro k' hk2 hkZ h
      rcases (U_outer_zero_iff p hd F hodd hDict _).mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hZ_min k' hkZ h1
      · rcases Nat.lt_or_ge k' 3 with hk3 | hk3
        · have hk : k' = 2 := by omega
          subst hk
          rw [show z0 + 1 + ((2 : ℕ) : ZMod n) - 2 = z0 + 1 by push_cast; ring] at h2
          exact hp1 h2
        · rw [show z0 + 1 + (k' : ZMod n) - 3 = z0 + 1 + ((k' - 3 : ℕ) : ZMod n) by
            rw [Nat.cast_sub hk3]; push_cast; ring] at h1
          exact hZ_min (k' - 3) (by omega) h1
    -- 外側の道
    have run : ∀ k, 3 ≤ k → k ≤ Z →
        (nxt hp)^[S + k] (x, false) = (z0 + 1 + (k : ZMod n), false) ∧
        HasDart p (z0 + (k : ZMod n), false) (z0 + 1 + (k : ZMod n), false) := by
      intro k hk3
      induction k, hk3 using Nat.le_induction with
      | base =>
          intro _
          refine ⟨?_, ?_⟩
          · rw [hv3]; congr 1; push_cast; ring
          · rw [show z0 + ((3 : ℕ) : ZMod n) = z0 + 3 by push_cast; ring,
              show z0 + 1 + ((3 : ℕ) : ZMod n) = z0 + 4 by push_cast; ring]
            exact hin4
      | succ k hk ih =>
          intro hkZ
          obtain ⟨hv, hin⟩ := ih (by omega)
          have hsp : spW p (z0 + 1 + (k : ZMod n)) = 0 := by
            refine U_sp_zero_of_o p hd F hDict _ ?_ (houter k (by omega) (by omega))
            have := houter (k - 1) (by omega) (by omega)
            rwa [show z0 + 1 + ((k - 1 : ℕ) : ZMod n) = z0 + 1 + (k : ZMod n) - 1 by
              rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring] at this
          have hnk : nxt hp (z0 + 1 + (k : ZMod n), false) = (z0 + 1 + (k : ZMod n) + 1, false) := by
            refine nxt_O_up p hp _ ?_ (no_spoke_of_spW_zero p ht hsp).1
            rw [show z0 + 1 + (k : ZMod n) - 1 = z0 + (k : ZMod n) by ring]
            exact hin.not_rev ht
          have e1 : z0 + 1 + ((k + 1 : ℕ) : ZMod n) = z0 + 1 + (k : ZMod n) + 1 := by push_cast; ring
          have e2 : z0 + ((k + 1 : ℕ) : ZMod n) = z0 + 1 + (k : ZMod n) := by push_cast; ring
          refine ⟨?_, ?_⟩
          · rw [show S + (k + 1) = S + k + 1 by ring, Function.iterate_succ_apply', hv, hnk, e1]
          · rw [e1, e2]
            exact hnk ▸ hasDart_nxt hp _
    obtain ⟨hvZ, hinZ⟩ := run Z hZ3 le_rfl
    have hz1 : iW p (z0 + 1 + (Z : ZMod n) + 1) = 0 := by
      rcases U_odd_pair p hd F hodd hDict _ hZ_spec with h | h
      · exact h
      · exfalso
        refine hZ_min (Z - 1) (by omega) ?_
        rwa [show z0 + 1 + ((Z - 1 : ℕ) : ZMod n) = z0 + 1 + (Z : ZMod n) - 1 by
          rw [Nat.cast_sub (by omega : 1 ≤ Z)]; push_cast; ring]
    have hoz : oW p (z0 + 1 + (Z : ZMod n)) = 0 :=
      (U_outer_zero_iff p hd F hodd hDict _).mpr (Or.inl ⟨hZ_spec, hz1⟩)
    have hdir' : HasDart p (z0 + 1 + (Z : ZMod n), false) (z0 + 1 + (Z : ZMod n), true) := by
      have h2 : ¬ HasDart p (z0 + 1 + (Z : ZMod n), false) (z0 + 1 + (Z : ZMod n) - 1, false) := by
        rw [show z0 + 1 + (Z : ZMod n) - 1 = z0 + (Z : ZMod n) by ring]
        exact hinZ.not_rev ht
      exact (nxt_O_spoke p hp _ (no_dart_of_oW_zero p ht hoz).1 h2) ▸ hasDart_nxt hp _
    have hprev : prev F (ZMod.castHom hd (ZMod d) (z0 + 1 + (Z : ZMod n)))
        = ZMod.castHom hd (ZMod d) z0 := by
      rw [prev_eq_of_first F _ (Z + 1) (by omega) hZ_le]
      · rw [map_add, map_add, map_one, map_natCast]; push_cast; ring
      · have : ZMod.castHom hd (ZMod d) (z0 + 1 + (Z : ZMod n)) - ((Z + 1 : ℕ) : ZMod d)
            = ZMod.castHom hd (ZMod d) z0 := by
          rw [map_add, map_add, map_one, map_natCast]; push_cast; ring
        rw [this]
        exact (hDict.i_iff z0).mp hz0
      · intro t h0 h1 h
        have h' : iW p (z0 + 1 + (Z : ZMod n) - (t : ZMod n)) = 0 := by
          rw [hDict.i_iff, map_sub, map_natCast]; exact h
        refine hZ_min (Z - t) (by omega) ?_
        rwa [show z0 + 1 + ((Z - t : ℕ) : ZMod n) = z0 + 1 + (Z : ZMod n) - (t : ZMod n) by
          rw [Nat.cast_sub (by omega : t ≤ Z)]; ring]
    refine ⟨S + Z, z0 + 1 + (Z : ZMod n), by omega, hvZ, hZ_spec, hdir', by rw [hprev, hret], ?_⟩
    intro s hs0 hsZ z hz
    rcases Nat.lt_or_ge s (S + 2) with hlt | hge
    · exact absurd hz (fun h => hinner_notO s hs0 hlt z h)
    · rcases eq_or_lt_of_le hge with h | h
      · subst h
        rw [hvS2] at hz
        simp only [Prod.mk.injEq, and_true] at hz
        rw [← hz]; exact hp3
      · obtain ⟨k, rfl⟩ : ∃ k, s = S + k := ⟨s - S, by omega⟩
        obtain ⟨hv, -⟩ := run k (by omega) (by omega)
        rw [hv] at hz
        simp only [Prod.mk.injEq, and_true] at hz
        rw [← hz]; exact hZ_min k (by omega)

end Trace

end GeneralizedPetersen.Descent

namespace GeneralizedPetersen.Descent

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks GeneralizedPetersen.Count

/-! ### 1. 推移的な置換は一本の巡回 -/

theorem isCycle_of_transitive {γ : Type*} [Fintype γ] [DecidableEq γ] (σ : Equiv.Perm γ)
    (h2 : 2 ≤ Fintype.card γ) (htr : ∀ x y : γ, ∃ k : ℕ, (⇑σ)^[k] x = y) :
    σ.IsCycle ∧ σ.support = Finset.univ := by
  have hnofix : ∀ x, σ x ≠ x := by
    intro x hfix
    obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
    obtain ⟨k, hk⟩ := htr x y
    have : (⇑σ)^[k] x = x := Function.iterate_fixed hfix k
    exact hy (hk ▸ this)
  obtain ⟨x0⟩ : Nonempty γ := Fintype.card_pos_iff.mp (by omega)
  refine ⟨⟨x0, hnofix x0, fun y _ => ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := htr x0 y
    exact ⟨(k : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hk⟩
  · exact Finset.eq_univ_iff_forall.mpr (fun y => Equiv.Perm.mem_support.mpr (hnofix y))

theorem transitive_of_inv {γ : Type*} (σ : Equiv.Perm γ)
    (htr : ∀ x y : γ, ∃ k : ℕ, (⇑σ⁻¹)^[k] x = y) : ∀ x y : γ, ∃ k : ℕ, (⇑σ)^[k] x = y := by
  intro x y
  obtain ⟨k, hk⟩ := htr y x
  refine ⟨k, ?_⟩
  rw [← Equiv.Perm.coe_pow] at hk ⊢
  rw [← hk, ← Equiv.Perm.mul_apply, inv_pow, mul_inv_cancel, Equiv.Perm.one_apply]

/-! ### 2. 跡付けを繋ぐ -/

variable {n : ℕ} [NeZero n] {u : V n} {d : ℕ} [NeZero d]

theorem sigma_val (F : Win d) (y : ↥(Gi F)) :
    (((next3 F * theta F) y : ↥(Gi F)) : ZMod d) = ret F (prev F (y : ZMod d)) := by
  rw [Equiv.Perm.mul_apply, next3_val, theta_val]

/-- **帰納**：`nxt^[k] O_x = O_y` なら向きが伝わり、`σ⁻¹` の反復で `π x` から `π y` へ届く。 -/
theorem reach_of_nxt (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (hd : d ∣ n) (F : Win d)
    (hodd : Odd d) (hDict : Dict p hd F) :
    ∀ k : ℕ, ∀ x : ZMod n, iW p x = 0 → HasDart p (x, false) (x, true) →
      ∀ y : ZMod n, iW p y = 0 → (nxt hp)^[k] (x, false) = (y, false) →
      HasDart p (y, false) (y, true) ∧
      ∀ (rx ry : ↥(Gi F)), (rx : ZMod d) = ZMod.castHom hd (ZMod d) x →
        (ry : ZMod d) = ZMod.castHom hd (ZMod d) y →
        ∃ j : ℕ, (⇑(next3 F * theta F)⁻¹)^[j] rx = ry := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hdir y hy hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [Function.iterate_zero, id_eq, Prod.mk.injEq, and_true] at hk
      subst hk
      refine ⟨hdir, fun rx ry hrx hry => ⟨0, ?_⟩⟩
      simp only [Function.iterate_zero, id_eq]
      exact Subtype.ext (hrx.trans hry.symm)
    · obtain ⟨t, x', ht0, hvt, hx', hdir', hret, hmid⟩ := trace p hp hd F hodd hDict x hx hdir
      have htk : t ≤ k := by
        by_contra hlt
        push Not at hlt
        exact hmid k hkpos hlt y hk hy
      have hk' : (nxt hp)^[k - t] (x', false) = (y, false) := by
        rw [← hvt, ← Function.iterate_add_apply, Nat.sub_add_cancel htk]; exact hk
      obtain ⟨hdiry, hreach⟩ := ih (k - t) (by omega) x' hx' hdir' y hy hk'
      refine ⟨hdiry, fun rx ry hrx hry => ?_⟩
      have hx'mem : ZMod.castHom hd (ZMod d) x' ∈ Gi F :=
        (mem_Gi F _).mpr ((hDict.i_iff x').mp hx')
      obtain ⟨j, hj⟩ := hreach ⟨_, hx'mem⟩ ry rfl hry
      refine ⟨j + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      convert hj using 2
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      apply Subtype.ext
      rw [sigma_val]
      change (rx : ZMod d) = ret F (prev F (ZMod.castHom hd (ZMod d) x'))
      rw [hrx, hret]

/-- **推移性**：向きが一点で `O → I` なら、`σ⁻¹` は `G_i` の上で推移的。 -/
theorem transitive_of_dir (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (hd : d ∣ n)
    (F : Win d) (hodd : Odd d) (hDict : Dict p hd F) (x0 : ZMod n) (hx0 : iW p x0 = 0)
    (hdir0 : HasDart p (x0, false) (x0, true)) :
    ∀ rx ry : ↥(Gi F), ∃ j : ℕ, (⇑(next3 F * theta F)⁻¹)^[j] rx = ry := by
  intro rx ry
  have hx : iW p (lift d n (rx : ZMod d)) = 0 :=
    (hDict.i_iff _).mpr (by rw [castHom_lift]; exact (mem_Gi F _).mp rx.2)
  have hy : iW p (lift d n (ry : ZMod d)) = 0 :=
    (hDict.i_iff _).mpr (by rw [castHom_lift]; exact (mem_Gi F _).mp ry.2)
  obtain ⟨k0, hk0⟩ := nxt_reach hp (x0, false) (lift d n (rx : ZMod d), false)
  obtain ⟨hdirx, -⟩ := reach_of_nxt p hp hd F hodd hDict k0 x0 hx0 hdir0 _ hx hk0
  obtain ⟨k, hk⟩ := nxt_reach hp (lift d n (rx : ZMod d), false) (lift d n (ry : ZMod d), false)
  obtain ⟨-, hreach⟩ := reach_of_nxt p hp hd F hodd hDict k _ hx hdirx _ hy hk
  exact hreach rx ry (castHom_lift hd _).symm (castHom_lift hd _).symm

/-- 向きは `p` か `p.reverse` のどちらかで取れる。 -/
theorem transitive_sigma_inv (p : (GP n 3).Walk u u) (hp : p.IsHamiltonianCycle) (hd : d ∣ n)
    (F : Win d) (hodd : Odd d) (hDict : Dict p hd F) (hne : (Gi F).Nonempty) :
    ∀ rx ry : ↥(Gi F), ∃ j : ℕ, (⇑(next3 F * theta F)⁻¹)^[j] rx = ry := by
  obtain ⟨r0, hr0⟩ := hne
  have hx0 : iW p (lift d n r0) = 0 :=
    (hDict.i_iff _).mpr (by rw [castHom_lift]; exact (mem_Gi F _).mp hr0)
  have hsp : spW p (lift d n r0) ≠ 0 := U_sp_ne_zero p hd F hDict _ hx0
  by_cases hOI : HasDart p (lift d n r0, false) (lift d n r0, true)
  · exact transitive_of_dir p hp hd F hodd hDict _ hx0 hOI
  · have hIO : HasDart p (lift d n r0, true) (lift d n r0, false) := by
      by_contra h
      apply hsp
      simp only [spW]
      rw [(ind_eq_zero_iff p _ _).mpr hOI, (ind_eq_zero_iff p _ _).mpr h]
      simp
    exact transitive_of_dir p.reverse (IsHamiltonianCycle.reverse' hp) hd F hodd hDict.reverse _
      (by rw [iW_reverse, neg_eq_zero]; exact hx0) ((hasDart_reverse p _ _).mpr hIO)

/-! ### 3. `CycleBridge n` と総合 -/

/-- **残り 3 が閉じる**。 -/
theorem cycleBridge (hn : Odd n) : CycleBridge n := by
  intro u p hp h2 h6 d _ hd hdn hD F hF
  have hodd : Odd d := Odd.of_dvd_nat hn hd
  have hDict := dict_of_agrees p hp h2 h6 hd hD F hF
  have hne : (Gi F).Nonempty := by
    obtain ⟨j, hj⟩ := exists_oW_zero p hp h2
    have hp0 : 0 < (quotTF p hp h2 h6 d hd hD).p := by
      apply Finset.card_pos.mpr
      refine ⟨ZMod.castHom hd (ZMod d) j, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [quotTF_o]; exact hj
    have hq : 0 < (quotTF p hp h2 h6 d hd hD).q := by rw [← TwoFactor.p_eq_q]; exact hp0
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact ⟨r, (mem_Gi F r).mpr ((Agrees.i_eq_zero hF r).mpr hr)⟩
  have hcard : 2 ≤ Fintype.card ↥(Gi F) := by
    rw [Fintype.card_coe]; exact two_le_card_Gi F hodd hne
  exact isCycle_of_transitive _ hcard
    (transitive_of_inv _ (transitive_sigma_inv p hp hd F hodd hDict hne))

/-- **一般 `n`（無条件）**：`n` 奇・`n ≥ 7` なら `n ∣ #HC(GP(n,3))`。 -/
theorem gp3_dvd_hc_odd (n : ℕ) [NeZero n] (hn : Odd n) (h7 : 7 ≤ n) : n ∣ numHC n 3 :=
  gp3_dvd_hc' n hn h7 (dartBridge hn) windingBridge (cycleBridge hn)

/-- 同じ言明（`NeZero n` を `7 ≤ n` から作る形）。 -/
theorem gp3_dvd_hc_odd' (n : ℕ) (hn : Odd n) (h7 : 7 ≤ n) :
    haveI : NeZero n := ⟨by omega⟩
    n ∣ numHC n 3 :=
  haveI : NeZero n := ⟨by omega⟩
  gp3_dvd_hc_odd n hn h7

end GeneralizedPetersen.Descent
