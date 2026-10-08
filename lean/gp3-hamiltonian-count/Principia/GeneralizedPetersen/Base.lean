import Mathlib

/-!
# Principia.GeneralizedPetersen.Base

  一般化ペテルセングラフ `GP n k` とその回転、向き付き 2 因子 `Flow`／`Win`、
  局所恒等式と窓の勘定、`d` が偶のときの反例 `winEx`。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.Base

open SimpleGraph

/-! ### 1. グラフの定義 -/

/-- 一般化ペテルセングラフの頂点。`(a, false) = O_a`（外輪）、`(a, true) = I_a`（内輪）。 -/
abbrev V (n : ℕ) := ZMod n × Bool

/-- 隣接の生成関係。対称化と非反射性は `SimpleGraph.fromRel` が付ける。
  外輪 `O_a — O_{a+1}`、内輪 `I_a — I_{a+k}`、スポーク `O_a — I_a`。 -/
def GPrel (n k : ℕ) (x y : V n) : Prop :=
  (x.2 = false ∧ y.2 = false ∧ y.1 = x.1 + 1) ∨
  (x.2 = true ∧ y.2 = true ∧ y.1 = x.1 + (k : ZMod n)) ∨
  (x.2 = false ∧ y.2 = true ∧ y.1 = x.1)

/-- 一般化ペテルセングラフ `GP(n, k)`。 -/
def GP (n k : ℕ) : SimpleGraph (V n) := SimpleGraph.fromRel (GPrel n k)

theorem GP_adj (n k : ℕ) (x y : V n) :
    (GP n k).Adj x y ↔ x ≠ y ∧ (GPrel n k x y ∨ GPrel n k y x) :=
  SimpleGraph.fromRel_adj _ x y

/-- 外輪の辺。 -/
theorem GP_adj_outer (n k : ℕ) (a : ZMod n) (h : (1 : ZMod n) ≠ 0) :
    (GP n k).Adj (a, false) (a + 1, false) := by
  rw [GP_adj]
  refine ⟨?_, Or.inl (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  intro hc
  have h1 : a = a + 1 := congrArg Prod.fst hc
  exact h (by linear_combination -h1)

/-- スポーク。 -/
theorem GP_adj_spoke (n k : ℕ) (a : ZMod n) : (GP n k).Adj (a, false) (a, true) := by
  rw [GP_adj]
  exact ⟨by simp, Or.inl (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

/-- 内輪の辺。 -/
theorem GP_adj_inner (n k : ℕ) (a : ZMod n) (h : (k : ZMod n) ≠ 0) :
    (GP n k).Adj (a, true) (a + (k : ZMod n), true) := by
  rw [GP_adj]
  refine ⟨?_, Or.inl (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  intro hc
  have h1 : a = a + (k : ZMod n) := congrArg Prod.fst hc
  exact h (by linear_combination -h1)

/-! ### 2. 回転 `ρ` -/

/-- 回転 `ρ : (a, b) ↦ (a + 1, b)`（外輪も内輪も一つずらす）。 -/
def rot (n : ℕ) : Equiv.Perm (V n) where
  toFun x := (x.1 + 1, x.2)
  invFun x := (x.1 - 1, x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem rot_apply (n : ℕ) (x : V n) : rot n x = (x.1 + 1, x.2) := rfl

/-- `ρ^d` は第一座標に `d` を足す。 -/
theorem rot_pow_apply (n d : ℕ) (x : V n) :
    ((rot n) ^ d) x = (x.1 + (d : ZMod n), x.2) := by
  induction d generalizing x with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, rot_apply]
      simp only [Prod.mk.injEq, and_true]
      push_cast
      ring

/-- 生成関係は第一座標の平行移動で不変。 -/
theorem GPrel_shift (n k : ℕ) (c a b : ZMod n) (s t : Bool) :
    GPrel n k (a + c, s) (b + c, t) ↔ GPrel n k (a, s) (b, t) := by
  simp only [GPrel]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, h2, by linear_combination h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, by linear_combination h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by linear_combination h3⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h1, h2, by linear_combination h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, by linear_combination h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by linear_combination h3⟩)

/-- 隣接関係は第一座標の平行移動で不変。 -/
theorem GP_adj_shift (n k : ℕ) (c a b : ZMod n) (s t : Bool) :
    (GP n k).Adj (a + c, s) (b + c, t) ↔ (GP n k).Adj (a, s) (b, t) := by
  simp only [GP_adj, GPrel_shift, ne_eq, Prod.mk.injEq, add_left_inj]

/-- `ρ^d` は `GP n k` の自己同型。**これが段階 1 の本体で、`n, k, d` について一般である。** -/
theorem GP_adj_rot_pow (n k d : ℕ) (x y : V n) :
    (GP n k).Adj (((rot n) ^ d) x) (((rot n) ^ d) y) ↔ (GP n k).Adj x y := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  rw [rot_pow_apply, rot_pow_apply]
  exact GP_adj_shift n k (d : ZMod n) a b s t

/-- 回転による自己同型（`SimpleGraph.Aut`）。 -/
def rotIso (n k : ℕ) : GP n k ≃g GP n k where
  toEquiv := rot n
  map_rel_iff' {x y} := by
    have := GP_adj_rot_pow n k 1 x y
    simpa using this

@[simp] theorem rotIso_apply (n k : ℕ) (x : V n) : rotIso n k x = (x.1 + 1, x.2) := rfl

/-- `ρ` の位数は `n` を割る：`ρ^n = 1`。 -/
theorem rot_pow_card (n : ℕ) : (rot n) ^ n = 1 := by
  apply Equiv.ext
  intro x
  rw [rot_pow_apply, ZMod.natCast_self]
  simp

/-- **`ρ` の頂点上の作用は自由**：`0 < d < n` なら `ρ^d` は頂点を一つも固定しない。 -/
theorem rot_pow_free (n d : ℕ) (hd : 0 < d) (hdn : d < n) (x : V n) :
    ((rot n) ^ d) x ≠ x := by
  rw [rot_pow_apply]
  intro hc
  have h1 : x.1 + (d : ZMod n) = x.1 := congrArg Prod.fst hc
  have h0 : (d : ZMod n) = 0 := by linear_combination h1
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact absurd (Nat.le_of_dvd hd h0) (by omega)

/-! ### 3. `ρ` が閉路の集合に作用すること -/

/-- 自己同型は歩道を歩道に写す（Mathlib の `SimpleGraph.Walk.map`）。
  ハミルトン閉路はハミルトン閉路に写る。 -/
theorem rotIso_hamiltonian {n k : ℕ} {x : V n} {p : (GP n k).Walk x x}
    (hp : p.IsHamiltonianCycle) :
    (p.map (rotIso n k).toHom).IsHamiltonianCycle := by
  refine SimpleGraph.Walk.IsHamiltonianCycle.map ?_ hp
  exact (rotIso n k).toEquiv.bijective

/-! ### 4. `Fin (2n)` の版 -/

/-- 頂点集合と `Fin (2n)` の間の全単射（`n > 0`）。 -/
noncomputable def vFin (n : ℕ) [NeZero n] : V n ≃ Fin (2 * n) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_prod, ZMod.card, Fintype.card_bool, Nat.mul_comm])

/-- 課題が求めた形：`Fin (2n)` 上のグラフとしての `GP(n,k)`。 -/
noncomputable def GPfin (n k : ℕ) [NeZero n] : SimpleGraph (Fin (2 * n)) :=
  (GP n k).map (vFin n).toEmbedding

/-- `GPfin` は `GP` と同型。したがって以下の結果はすべて `Fin (2n)` 版に移る。 -/
noncomputable def GPfin_iso (n k : ℕ) [NeZero n] : GP n k ≃g GPfin n k :=
  SimpleGraph.Iso.map (vFin n) (GP n k)

end GeneralizedPetersen.Base

namespace GeneralizedPetersen.Base

open SimpleGraph

/-! ### 1. 商写像 -/

/-- 商写像 `π : V n → V d`（`d ∣ n`）。第一座標を `ZMod d` に落とす。 -/
def quotMap (n d : ℕ) (h : d ∣ n) (x : V n) : V d := (ZMod.castHom h (ZMod d) x.1, x.2)

@[simp] theorem quotMap_apply (n d : ℕ) (h : d ∣ n) (x : V n) :
    quotMap n d h x = (ZMod.castHom h (ZMod d) x.1, x.2) := rfl

/-- 商写像は生成関係を保つ。 -/
theorem quotMap_rel (n k d : ℕ) (h : d ∣ n) {x y : V n} (hr : GPrel n k x y) :
    GPrel d k (quotMap n d h x) (quotMap n d h y) := by
  obtain ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ := hr
  · refine Or.inl ⟨h1, h2, ?_⟩
    simp only [quotMap_apply, h3, map_add, map_one]
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    simp only [quotMap_apply, h3, map_add, map_natCast]
  · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
    simp only [quotMap_apply, h3]

/-- 商写像は隣接を保つ。**`GP(d,k)` が単純グラフであるために `1 ≠ 0` と `k ≠ 0`（`ZMod d` で）が要る**
  ——これが「`d ≥ 7` で `Q_d = GP(d,3)`」（紙の証明）の形式的な中身である。 -/
theorem quotMap_adj (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0) (hk : (k : ZMod d) ≠ 0)
    {x y : V n} (hxy : (GP n k).Adj x y) :
    (GP d k).Adj (quotMap n d h x) (quotMap n d h y) := by
  rw [GP_adj] at hxy ⊢
  obtain ⟨hne, hr⟩ := hxy
  refine ⟨?_, hr.imp (quotMap_rel n k d h) (quotMap_rel n k d h)⟩
  -- 像が相異なること：外輪の辺は `1 ≠ 0`、内輪の辺は `k ≠ 0`、スポークは `Bool` が違う
  intro hc
  have hfst : ZMod.castHom h (ZMod d) x.1 = ZMod.castHom h (ZMod d) y.1 := congrArg Prod.fst hc
  have hsnd : x.2 = y.2 := congrArg (fun z : V d => z.2) hc
  obtain (⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩) |
      (⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩) := hr
  · rw [p3] at hfst
    simp only [map_add, map_one] at hfst
    exact h1 (by first | linear_combination hfst | linear_combination -hfst)
  · rw [p3] at hfst
    simp only [map_add, map_natCast] at hfst
    exact hk (by first | linear_combination hfst | linear_combination -hfst)
  · rw [p1, p2] at hsnd; exact absurd hsnd (by decide)
  · rw [p3] at hfst
    simp only [map_add, map_one] at hfst
    exact h1 (by linear_combination hfst)
  · rw [p3] at hfst
    simp only [map_add, map_natCast] at hfst
    exact hk (by linear_combination hfst)
  · rw [p1, p2] at hsnd; exact absurd hsnd (by decide)

/-- 商写像はグラフ準同型 `GP(n,k) →g GP(d,k)`。 -/
def quotHom (n k d : ℕ) (h : d ∣ n) (h1 : (1 : ZMod d) ≠ 0) (hk : (k : ZMod d) ≠ 0) :
    GP n k →g GP d k where
  toFun := quotMap n d h
  map_rel' := quotMap_adj n k d h h1 hk

/-! ### 2. 商は `⟨ρ^d⟩` によるもの -/

/-- `π` は回転と可換：`π ∘ ρ_n = ρ_d ∘ π`。 -/
theorem quotMap_rot (n d : ℕ) (h : d ∣ n) (x : V n) :
    quotMap n d h (rot n x) = rot d (quotMap n d h x) := by
  simp only [quotMap_apply, rot_apply, map_add, map_one]

/-- **`ρ^d` は商の上で自明に働く。** -/
theorem quotMap_rot_pow_self (n d : ℕ) (h : d ∣ n) (x : V n) :
    quotMap n d h (((rot n) ^ d) x) = quotMap n d h x := by
  rw [rot_pow_apply]
  simp only [quotMap_apply, map_add, map_natCast, ZMod.natCast_self, add_zero]

/-- **繊維はちょうど `⟨ρ^d⟩` の軌道**（`π x = π y ⟺ y = ρ^{dj} x`）。
  これが「商グラフ `Q_d = GP(n,k)/⟨ρ^d⟩`」の形式的な内容である。 -/
theorem quotMap_eq_iff (n d : ℕ) [NeZero n] (h : d ∣ n) (x y : V n) :
    quotMap n d h x = quotMap n d h y ↔ ∃ j : ℕ, ((rot n) ^ (d * j)) x = y := by
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  have hri : ∀ z : ZMod n, ((z.val : ℕ) : ZMod n) = z := ZMod.natCast_rightInverse
  constructor
  · intro hc
    simp only [quotMap_apply, Prod.mk.injEq] at hc
    obtain ⟨hfst, hsnd⟩ := hc
    have hc0 : ZMod.castHom h (ZMod d) (b - a) = 0 := by
      rw [map_sub, hfst, sub_self]
    have hcast : (((b - a).val : ℕ) : ZMod d) = 0 := by
      have hq := congrArg (ZMod.castHom h (ZMod d)) (hri (b - a))
      rw [map_natCast] at hq
      rw [hq]; exact hc0
    rw [ZMod.natCast_eq_zero_iff] at hcast
    obtain ⟨j, hj⟩ := hcast
    refine ⟨j, ?_⟩
    rw [rot_pow_apply]
    have hdj : ((d * j : ℕ) : ZMod n) = b - a := by rw [← hj, hri]
    simp only [Prod.mk.injEq, hsnd, and_true, hdj]
    ring
  · rintro ⟨j, hj⟩
    rw [rot_pow_apply] at hj
    simp only [Prod.mk.injEq] at hj
    obtain ⟨hj1, hj2⟩ := hj
    subst hj2
    subst hj1
    have hsplit : ((d * j : ℕ) : ZMod n) = (d : ZMod n) * (j : ZMod n) := by push_cast; ring
    simp only [quotMap_apply, Prod.mk.injEq, and_true, map_add, left_eq_add]
    first
      | rw [hsplit, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
      | rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
      | (rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).mpr ⟨j, rfl⟩)

/-! ### 3. 巻き数と持ち上げの連結性（群論的な核） -/

/-- **持ち上げが一本に繋がる条件の核。**
  `ρ^d` の生成する位数 `m = n/d` の巡回群の中で、商の閉路を一周するごとに `w` ずつ進む。
  これが全体を覆う（＝持ち上げが一本の閉路）のは `gcd(w, m) = 1` のときちょうど。
  紙の証明の「`H_Q` がハミルトン閉路で `w ≢ 0 (mod 3)`」（`m = 3` の場合）はこの特別な場合。 -/
theorem lift_connected_iff (m w : ℕ) [NeZero m] :
    (∀ t : ZMod m, ∃ j : ℕ, (j : ZMod m) * (w : ZMod m) = t) ↔ Nat.Coprime w m := by
  constructor
  · intro hgen
    obtain ⟨j, hj⟩ := hgen 1
    have : IsUnit ((w : ℕ) : ZMod m) := IsUnit.of_mul_eq_one (j : ZMod m) (by
      rw [mul_comm]; exact hj)
    exact (ZMod.isUnit_iff_coprime w m).mp this
  · intro hcop t
    have hu : IsUnit ((w : ℕ) : ZMod m) := (ZMod.isUnit_iff_coprime w m).mpr hcop
    obtain ⟨u, hu'⟩ := hu
    have hri : ∀ z : ZMod m, ((z.val : ℕ) : ZMod m) = z := ZMod.natCast_rightInverse
    refine ⟨((t * (↑u⁻¹ : ZMod m)).val : ℕ), ?_⟩
    rw [hri, ← hu', mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- `m = 3` の形（紙の証明の「`w ≢ 0 (mod 3)`」）。 -/
theorem lift_connected_three (w : ℕ) :
    (∀ t : ZMod 3, ∃ j : ℕ, (j : ZMod 3) * (w : ZMod 3) = t) ↔ ¬ (3 ∣ w) := by
  rw [lift_connected_iff]
  constructor
  · intro hcop hdvd
    have : (3 : ℕ) ∣ Nat.gcd w 3 := Nat.dvd_gcd hdvd dvd_rfl
    rw [Nat.Coprime] at hcop
    omega
  · intro hnd
    have h3 : Nat.Prime 3 := by norm_num
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd h3).mpr hnd))

end GeneralizedPetersen.Base

namespace GeneralizedPetersen.Base

open Finset

/-! ### 0. `ZMod d` 上の和のずらし -/

theorem sum_shift {d : ℕ} [NeZero d] {M : Type*} [AddCommMonoid M] (f : ZMod d → M) (c : ZMod d) :
    ∑ j : ZMod d, f (j - c) = ∑ j : ZMod d, f j :=
  Fintype.sum_equiv (Equiv.subRight c) _ _ (fun _ => rfl)

/-! ### 1. 向き付き 2 因子の公理化 -/

/-- 商グラフ `GP(d,k)`（`k = 3`）の向き付き 2 因子。
  `o j` は外辺 `{j, j+1}`、`i j` は内辺 `{j, j+3}`、`sp j` はスポーク `O_j → I_j` の流量。
  `outer` は外輪頂点 `O_j` での、`inner` は内輪頂点 `I_j` での流量保存。 -/
structure Flow (d : ℕ) where
  o : ZMod d → ℤ
  i : ZMod d → ℤ
  sp : ZMod d → ℤ
  outer : ∀ j, o j - o (j - 1) + sp j = 0
  inner : ∀ j, i j - i (j - 3) - sp j = 0

namespace Flow

variable {d : ℕ}

/-- 環帯を `j` と `j+1` の間で切った切り口を横切る本数（符号つき）。 -/
def W (F : Flow d) (j : ZMod d) : ℤ := F.o j + F.i (j - 2) + F.i (j - 1) + F.i j

/-- **補題 A の一段**：`W` は一つずらしても変わらない。
  スポークの流量 `sp j` が打ち消し合う（telescoping）だけで、場合分けは要らない。 -/
theorem W_sub_one (F : Flow d) (j : ZMod d) : F.W j = F.W (j - 1) := by
  have h1 := F.outer j
  have h2 := F.inner j
  have e1 : j - 1 - 2 = j - 3 := by ring
  have e2 : j - 1 - 1 = j - 2 := by ring
  simp only [W, e1, e2]
  linarith

/-- `W` を自然数ぶんずらしても変わらない。 -/
theorem W_sub_nat (F : Flow d) (m : ℕ) (j : ZMod d) : F.W (j - (m : ZMod d)) = F.W j := by
  induction m generalizing j with
  | zero => simp
  | succ p ih =>
      have e : j - ((p + 1 : ℕ) : ZMod d) = (j - (p : ZMod d)) - 1 := by push_cast; ring
      rw [e, ← F.W_sub_one, ih]

/-- **補題 A（局所恒等式）**：`W j` は `j` に依らない。 -/
theorem W_const (F : Flow d) [NeZero d] (j j' : ZMod d) : F.W j = F.W j' := by
  have hri : ∀ z : ZMod d, ((z.val : ℕ) : ZMod d) = z := ZMod.natCast_rightInverse
  have e : j - (((j - j').val : ℕ) : ZMod d) = j' := by rw [hri]; ring
  rw [← F.W_sub_nat ((j - j').val) j, e]

/-- `W` の総和は `Σ o + 3 Σ i`（各内辺はちょうど 3 つの窓に入る）。 -/
theorem sum_W (F : Flow d) [NeZero d] :
    ∑ j : ZMod d, F.W j = (∑ j : ZMod d, F.o j) + 3 * ∑ j : ZMod d, F.i j := by
  simp only [W, Finset.sum_add_distrib, sum_shift F.i]
  ring

/-- **総変位の式**：巻き数を `w`（＝定数 `W`）とすると `d · w = Σ o + 3 Σ i`。
  紙の証明の `Σ = d w` はこれである。 -/
theorem winding (F : Flow d) [NeZero d] (w : ℤ) (hw : ∀ j, F.W j = w) :
    (d : ℤ) * w = (∑ j : ZMod d, F.o j) + 3 * ∑ j : ZMod d, F.i j := by
  rw [← F.sum_W]
  rw [Finset.sum_congr rfl (fun j _ => hw j), Finset.sum_const, Finset.card_univ, ZMod.card]
  simp [mul_comm]

end Flow

/-! ### 2. 窓の勘定（紙の証明） -/

/-- `w = 2` のときの 2 因子。指標が `{0, ±1}` に入ることと、各頂点の次数が 2 であることを足す。 -/
structure Win (d : ℕ) extends Flow d where
  o_mem : ∀ j, o j = 0 ∨ o j = 1 ∨ o j = -1
  i_mem : ∀ j, i j = 0 ∨ i j = 1 ∨ i j = -1
  degO : ∀ j, |o (j - 1)| + |o j| + |sp j| = 2
  degI : ∀ j, |i (j - 3)| + |i j| + |sp j| = 2
  w2 : ∀ j, toFlow.W j = 2

namespace Win

variable {d : ℕ}

/-- 窓 `{i (j−2), i (j−1), i j}` に含まれる零の個数。 -/
def Z (F : Win d) (j : ZMod d) : ℕ :=
  (if F.i (j - 2) = 0 then 1 else 0) + (if F.i (j - 1) = 0 then 1 else 0) +
    (if F.i j = 0 then 1 else 0)

/-- **窓の型**：零は 3 個にならず（`Z ≤ 2`）、零をちょうど 1 個含む窓は外辺の欠けと一対一。 -/
theorem Z_spec (F : Win d) (j : ZMod d) : F.Z j ≤ 2 ∧ (F.Z j = 1 ↔ F.o j = 0) := by
  have hT : F.i (j - 2) + F.i (j - 1) + F.i j = 2 - F.o j := by
    have h := F.w2 j
    simp only [Flow.W] at h
    linarith
  rcases F.o_mem j with ho | ho | ho <;>
    rcases F.i_mem (j - 2) with h2 | h2 | h2 <;>
      rcases F.i_mem (j - 1) with h1 | h1 | h1 <;>
        rcases F.i_mem j with h0 | h0 | h0 <;>
          (try simp only [Z, ho, h2, h1, h0] at hT ⊢) <;>
          (try norm_num at hT ⊢) <;>
          (try omega)

/-- 外辺の欠けの個数 `p`。 -/
def p (F : Win d) [NeZero d] : ℕ := (Finset.univ.filter (fun j : ZMod d => F.o j = 0)).card

/-- 内辺の欠けの個数 `q`。 -/
def q (F : Win d) [NeZero d] : ℕ := (Finset.univ.filter (fun j : ZMod d => F.i j = 0)).card

/-- 零をちょうど 2 個含む窓の個数 `x`。 -/
def x (F : Win d) [NeZero d] : ℕ := (Finset.univ.filter (fun j : ZMod d => F.Z j = 2)).card

/-- スポークの本数を外側と内側から数えて、欠けの個数が等しいこと（`p = q`）。 -/
theorem p_eq_q (F : Win d) [NeZero d] : F.p = F.q := by
  -- 絶対値の和を二通りに
  have hO : ∑ j : ZMod d, (|F.o (j - 1)| + |F.o j| + |F.sp j|) = 2 * (d : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ => F.degO j), Finset.sum_const, Finset.card_univ, ZMod.card]
    simp [mul_comm]
  have hI : ∑ j : ZMod d, (|F.i (j - 3)| + |F.i j| + |F.sp j|) = 2 * (d : ℤ) := by
    rw [Finset.sum_congr rfl (fun j _ => F.degI j), Finset.sum_const, Finset.card_univ, ZMod.card]
    simp [mul_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift (fun j => |F.o j|) (1 : ZMod d)] at hO
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift (fun j => |F.i j|) (3 : ZMod d)] at hI
  have habs : ∑ j : ZMod d, |F.o j| = ∑ j : ZMod d, |F.i j| := by linarith
  -- `|o j| = 1 - [o j = 0]`
  have hOsum : ∑ j : ZMod d, |F.o j| = (d : ℤ) - (F.p : ℤ) := by
    have : ∀ j : ZMod d, |F.o j| = 1 - (if F.o j = 0 then (1 : ℤ) else 0) := by
      intro j
      rcases F.o_mem j with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ZMod.card, Finset.sum_boole]
    simp [p]
  have hIsum : ∑ j : ZMod d, |F.i j| = (d : ℤ) - (F.q : ℤ) := by
    have : ∀ j : ZMod d, |F.i j| = 1 - (if F.i j = 0 then (1 : ℤ) else 0) := by
      intro j
      rcases F.i_mem j with h | h | h <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ZMod.card, Finset.sum_boole]
    simp [q]
  rw [hOsum, hIsum] at habs
  omega

/-- 窓の零の総数は `3q`（各内辺の零は 3 つの窓に入る）。 -/
theorem sum_Z_eq (F : Win d) [NeZero d] : ∑ j : ZMod d, F.Z j = 3 * F.q := by
  simp only [Z, Finset.sum_add_distrib]
  rw [sum_shift (fun j => if F.i j = 0 then 1 else 0) (2 : ZMod d),
    sum_shift (fun j => if F.i j = 0 then 1 else 0) (1 : ZMod d)]
  rw [Finset.sum_boole]
  simp only [q, Nat.cast_id]
  ring

/-- 窓の零の総数を型で数え直すと `p + 2x`。 -/
theorem sum_Z_eq' (F : Win d) [NeZero d] : ∑ j : ZMod d, F.Z j = F.p + 2 * F.x := by
  have hcong : ∀ j : ZMod d, F.Z j =
      (if F.o j = 0 then 1 else 0) + 2 * (if F.Z j = 2 then 1 else 0) := by
    intro j
    obtain ⟨hle, hiff⟩ := F.Z_spec j
    by_cases h2 : F.Z j = 2
    · have : ¬ (F.o j = 0) := by rw [← hiff]; omega
      simp [h2, this]
    · by_cases h1 : F.Z j = 1
      · have : F.o j = 0 := hiff.mp h1
        simp [h1, this]
      · have h0 : F.Z j = 0 := by omega
        have : ¬ (F.o j = 0) := by rw [← hiff]; omega
        simp [h0, this]
  rw [Finset.sum_congr rfl (fun j _ => hcong j), Finset.sum_add_distrib, Finset.sum_boole,
    ← Finset.mul_sum, Finset.sum_boole]
  simp [p, x]

/-- **紙の証明の窓の勘定**：`w = 2` なら零をちょうど 2 個含む窓の数は外辺の欠けの数に等しい
  （`x = p`）。**`d` について一般。** -/
theorem x_eq_p (F : Win d) [NeZero d] : F.x = F.p := by
  have h1 := F.sum_Z_eq
  have h2 := F.sum_Z_eq'
  have h3 := F.p_eq_q
  omega

end Win

end GeneralizedPetersen.Base

namespace GeneralizedPetersen.Base

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- 置換 `σ` の軌道の本数（不動点も 1 本と数える）。
  `cycleType` は非自明な巡回の長さの重複集合なので、その個数に不動点の個数を足したもの。 -/
def orbCount (σ : Equiv.Perm α) : ℕ :=
  Multiset.card σ.cycleType + (Fintype.card α - σ.support.card)

/-- **符号は「全体の大きさ − 軌道の本数」の偶奇**。
  （`Equiv.Perm.sign_of_cycleType` を軌道の本数で書き直したもの。） -/
theorem sign_eq_orbCount (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card α + orbCount σ) := by
  have hs : σ.support.card ≤ Fintype.card α := by
    simpa [Finset.card_univ] using Finset.card_le_univ σ.support
  have key : Fintype.card α + orbCount σ
      = (σ.support.card + Multiset.card σ.cycleType) + 2 * (Fintype.card α - σ.support.card) := by
    unfold orbCount
    omega
  have h2 : (-1 : ℤˣ) ^ (Fintype.card α + orbCount σ)
      = (-1 : ℤˣ) ^ (σ.support.card + Multiset.card σ.cycleType) := by
    rw [key, pow_add, pow_mul]
    simp
  rw [h2, Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType]

/-- 頂点数が偶数のとき、軌道の本数が奇数の置換の符号は `−1`。
  紙の証明の「`sgn(next₃) = (−1)^c`、`c` は奇」がこれ。 -/
theorem sign_eq_neg_one_of_odd_orbCount (σ : Equiv.Perm α)
    (hcard : Even (Fintype.card α)) (hodd : Odd (orbCount σ)) :
    Equiv.Perm.sign σ = -1 := by
  rw [sign_eq_orbCount]
  exact Odd.neg_one_pow (hcard.add_odd hodd)

/-- 全体を一本で回す巡回置換は、頂点数が偶数なら符号 `−1`。 -/
theorem sign_eq_neg_one_of_full_cycle (θ : Equiv.Perm α)
    (hθ : θ.IsCycle) (hsupp : θ.support = Finset.univ) (hcard : Even (Fintype.card α)) :
    Equiv.Perm.sign θ = -1 := by
  rw [hθ.sign, hsupp, Finset.card_univ]
  obtain ⟨m, hm⟩ := hcard
  rw [hm, ← two_mul, pow_mul]
  simp

/-- **紙の証明の定理 2 の符号の段。**
  `θ` が全体を回す巡回で、`ν` の軌道の本数が奇数なら、`ν ∘ θ` は全体を回す巡回になれない。
  （`sgn(ν θ) = (−1)(−1) = +1` だが、全体を回す巡回の符号は `−1`。） -/
theorem not_full_cycle_of_odd_orbCount (θ ν : Equiv.Perm α)
    (hcard : Even (Fintype.card α))
    (hθ : θ.IsCycle) (hθs : θ.support = Finset.univ)
    (hν : Odd (orbCount ν))
    (hc : (ν * θ).IsCycle) (hcs : (ν * θ).support = Finset.univ) : False := by
  have h1 : Equiv.Perm.sign (ν * θ) = -1 := sign_eq_neg_one_of_full_cycle _ hc hcs hcard
  have h2 : Equiv.Perm.sign (ν * θ) = 1 := by
    rw [map_mul, sign_eq_neg_one_of_odd_orbCount ν hcard hν,
      sign_eq_neg_one_of_full_cycle θ hθ hθs hcard]
    simp
  rw [h1] at h2
  have h3 := congrArg (Units.val : ℤˣ → ℤ) h2
  norm_num at h3

/-- 紙の証明の形：`|G_i| = 2q` の上で `θ`（円周上の前者置換）が `2q` 巡回、
  `next₃` の巡回の本数 `c` が奇数なら、`next₃ ∘ θ` は `2q` 巡回にならない
  ——すなわち商グラフの 2 因子は一本の閉路にならない。**`q` に依らない。** -/
theorem next_theta_not_full_cycle (q : ℕ) (hq : Fintype.card α = 2 * q)
    (θ ν : Equiv.Perm α) (hθ : θ.IsCycle) (hθs : θ.support = Finset.univ)
    (hc : Odd (orbCount ν)) :
    ¬ ((ν * θ).IsCycle ∧ (ν * θ).support = Finset.univ) := by
  rintro ⟨h1, h2⟩
  exact not_full_cycle_of_odd_orbCount θ ν (by rw [hq]; exact ⟨q, by ring⟩) hθ hθs hc h1 h2

/-- 不動点を持たない置換では `orbCount` は `cycleType` の長さそのもの
  （紙の証明で `next₃` が不動点を持たないことに対応）。 -/
theorem orbCount_of_no_fixed (σ : Equiv.Perm α) (h : σ.support = Finset.univ) :
    orbCount σ = Multiset.card σ.cycleType := by
  unfold orbCount
  rw [h, Finset.card_univ]
  simp

end GeneralizedPetersen.Base

namespace GeneralizedPetersen.Base

open Finset

namespace Win

variable {d : ℕ}

/-! ### 1. スポークの流量は `{0, ±1}`（仮定ではなく従う） -/

/-- 次数条件と流量保存から、スポークの流量の絶対値は 1 以下。 -/
theorem sp_abs_le_one (F : Win d) (j : ZMod d) : |F.sp j| ≤ 1 := by
  have hsp : F.sp j = F.o (j - 1) - F.o j := by linarith [F.outer j]
  rcases F.o_mem (j - 1) with h1 | h1 | h1 <;>
    rcases F.o_mem j with h0 | h0 | h0 <;>
      (have hd := F.degO j) <;>
      (try rw [hsp, h1, h0] at hd ⊢) <;>
      (first | decide | (exfalso; revert hd; decide))

/-! ### 2. `G_i` の局所の禁止則 -/

/-- **距離 3 の対は禁止**：`i r = 0` かつ `i (r+3) = 0` なら内輪頂点 `I_{r+3}` の次数が足りない。 -/
theorem no_gap_dist_three (F : Win d) (r : ZMod d) : ¬ (F.i r = 0 ∧ F.i (r + 3) = 0) := by
  rintro ⟨h1, h2⟩
  have hd := F.degI (r + 3)
  have e : r + 3 - 3 = r := by ring
  rw [e, h1, h2] at hd
  have hle := F.sp_abs_le_one (r + 3)
  simp only [abs_zero, zero_add] at hd
  linarith

/-- **3 連続は禁止**（窓に零が 3 個入らないこと、＝`Z ≤ 2`）。 -/
theorem no_three_consecutive (F : Win d) (r : ZMod d) :
    ¬ (F.i r = 0 ∧ F.i (r + 1) = 0 ∧ F.i (r + 2) = 0) := by
  rintro ⟨h0, h1, h2⟩
  have hle := (F.Z_spec (r + 2)).1
  have e1 : r + 2 - 2 = r := by ring
  have e2 : r + 2 - 1 = r + 1 := by ring
  simp only [Z, e1, e2, h0, h1, h2] at hle
  norm_num at hle

/-! ### 3. 対の勘定 -/

/-- 距離 1 の対（ドミノ）の個数 `n₁`。 -/
def n1 (F : Win d) [NeZero d] : ℕ :=
  ∑ r : ZMod d, (if F.i r = 0 ∧ F.i (r + 1) = 0 then 1 else 0)

/-- 間が空いた距離 2 の対の個数 `n₂`。 -/
def n2 (F : Win d) [NeZero d] : ℕ :=
  ∑ r : ZMod d, (if F.i r = 0 ∧ F.i (r + 1) ≠ 0 ∧ F.i (r + 2) = 0 then 1 else 0)

/-- 零をちょうど 2 個含む窓は、距離 1 の対（2 つの窓が見る）か距離 2 の対（1 つの窓が見る）。 -/
theorem x_eq_pairs (F : Win d) [NeZero d] : F.x = 2 * F.n1 + F.n2 := by
  have hx : F.x = ∑ j : ZMod d, (if F.Z j = 2 then (1 : ℕ) else 0) := by
    rw [Finset.sum_boole]
    simp [x]
  have hpt : ∀ j : ZMod d, (if F.Z j = 2 then (1 : ℕ) else 0)
      = (if F.i (j - 2) = 0 ∧ F.i (j - 1) = 0 then 1 else 0)
      + (if F.i (j - 1) = 0 ∧ F.i j = 0 then 1 else 0)
      + (if F.i (j - 2) = 0 ∧ F.i (j - 1) ≠ 0 ∧ F.i j = 0 then 1 else 0) := by
    intro j
    have hle := (F.Z_spec j).1
    by_cases h2 : F.i (j - 2) = 0 <;> by_cases h1 : F.i (j - 1) = 0 <;>
      by_cases h0 : F.i j = 0 <;>
        (try simp [Z, h2, h1, h0] at hle ⊢) <;>
        (try omega)
  have e1 : ∑ j : ZMod d, (if F.i (j - 2) = 0 ∧ F.i (j - 1) = 0 then (1 : ℕ) else 0) = F.n1 :=
    Fintype.sum_equiv (Equiv.subRight (2 : ZMod d)) _ _ (fun j => by
      show (if F.i (j - 2) = 0 ∧ F.i (j - 1) = 0 then (1 : ℕ) else 0)
          = (if F.i (j - 2) = 0 ∧ F.i (j - 2 + 1) = 0 then (1 : ℕ) else 0)
      rw [show j - (2 : ZMod d) + 1 = j - 1 from by ring])
  have e2 : ∑ j : ZMod d, (if F.i (j - 1) = 0 ∧ F.i j = 0 then (1 : ℕ) else 0) = F.n1 :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ (fun j => by
      show (if F.i (j - 1) = 0 ∧ F.i j = 0 then (1 : ℕ) else 0)
          = (if F.i (j - 1) = 0 ∧ F.i (j - 1 + 1) = 0 then (1 : ℕ) else 0)
      rw [show j - (1 : ZMod d) + 1 = j from by ring])
  have e3 : ∑ j : ZMod d,
      (if F.i (j - 2) = 0 ∧ F.i (j - 1) ≠ 0 ∧ F.i j = 0 then (1 : ℕ) else 0) = F.n2 :=
    Fintype.sum_equiv (Equiv.subRight (2 : ZMod d)) _ _ (fun j => by
      show (if F.i (j - 2) = 0 ∧ F.i (j - 1) ≠ 0 ∧ F.i j = 0 then (1 : ℕ) else 0)
          = (if F.i (j - 2) = 0 ∧ F.i (j - 2 + 1) ≠ 0 ∧ F.i (j - 2 + 2) = 0 then (1 : ℕ) else 0)
      rw [show j - (2 : ZMod d) + 1 = j - 1 from by ring,
        show j - (2 : ZMod d) + 2 = j from by ring])
  rw [hx, Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    e1, e2, e3]
  ring

/-- **紙の証明の勘定**：`2 n₁ + n₂ = |G_i|`。
  （`x = p`（`Principia.GeneralizedPetersen.Base` の `x_eq_p`）と `p = q` を通す。）**`d` について一般。** -/
theorem pairs_eq_q (F : Win d) [NeZero d] : 2 * F.n1 + F.n2 = F.q := by
  rw [← F.x_eq_pairs, F.x_eq_p, F.p_eq_q]

end Win

end GeneralizedPetersen.Base

namespace GeneralizedPetersen.Base

set_option maxRecDepth 8000

/-- `d = 10` の向き付き 2 因子（外輪の偶位置の辺・内輪の奇位置の辺・全スポーク）。 -/
def flowEx : Flow 10 where
  o := fun j => if j.val % 2 = 0 then 1 else 0
  i := fun r => if r.val % 2 = 1 then 1 else 0
  sp := fun j => if j.val % 2 = 0 then -1 else 1
  outer := by decide
  inner := by decide

/-- 上の 2 因子は巻き数 `w = 2` の条件をすべて満たす。**`Win` は空でない。** -/
def winEx : Win 10 where
  toFlow := flowEx
  o_mem := by decide
  i_mem := by decide
  degO := by decide
  degI := by decide
  w2 := by decide

/-- 巻き数は確かに 2。 -/
theorem winEx_W : ∀ j : ZMod 10, flowEx.W j = 2 := winEx.w2

/-- **紙の証明の「`d` 偶の抜け道」**：この例では欠けの集合は公差 2 の巡回塊で、
  ドミノが一つも無い（`n₁ = 0`）のに `2n₁ + n₂ = q` は成り立つ。
  したがって対の勘定だけでブロック構造を出すことはできず、`d` の奇偶が要る。 -/
theorem winEx_counts : winEx.n1 = 0 ∧ winEx.n2 = 5 ∧ winEx.q = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- 窓の勘定はこの例でも成り立つ（`x = p = q = 5`）。 -/
theorem winEx_x_p : winEx.x = 5 ∧ winEx.p = 5 := by
  constructor <;> decide

end GeneralizedPetersen.Base
