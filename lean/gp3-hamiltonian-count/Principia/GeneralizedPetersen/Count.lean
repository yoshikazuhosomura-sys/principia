import Mathlib
import Principia.GeneralizedPetersen.Blocks
import Principia.GeneralizedPetersen.FreeAction

/-!
# Principia.GeneralizedPetersen.Count

  符号の補題、初回帰置換 `θ`、辺集合としてのハミルトン閉路 `HamEdges`・その個数 `numHC`、
  自由作用への還元 `gp_dvd_numHC`、条件つきの `gp3_dvd_hc`。

  sorry 0・native_decide 不使用。
-/

namespace GeneralizedPetersen.Count

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### 0. 部分型への制限と反復 -/

/-- 制限した置換の反復は、もとの置換の反復の制限。 -/
theorem subtypePerm_pow_val {β : Type*} (σ : Equiv.Perm β) {p : β → Prop}
    (hp : ∀ x, p (σ x) ↔ p x) :
    ∀ (k : ℕ) (x : {y : β // p y}),
      (((σ.subtypePerm hp ^ k) x : {y : β // p y}) : β) = (σ ^ k) (x : β) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ.subtypePerm hp x)]
      simp [pow_succ]

/-! ### 1. 不変な述語による分割 -/

/-- **不変な述語で置換を割ると、符号は二つの制限の符号の積**。
  （`σ = ofSubtype (σ|p) * ofSubtype (σ|¬p)` を示し、`sign_ofSubtype` を使う。） -/
theorem sign_split (σ : Equiv.Perm α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) (hp' : ∀ x, ¬ p (σ x) ↔ ¬ p x) :
    Equiv.Perm.sign σ
      = Equiv.Perm.sign (σ.subtypePerm hp)
        * Equiv.Perm.sign (σ.subtypePerm (p := fun a => ¬ p a) hp') := by
  have key : σ = (Equiv.Perm.ofSubtype (σ.subtypePerm hp))
      * (Equiv.Perm.ofSubtype (σ.subtypePerm (p := fun a => ¬ p a) hp')) := by
    ext x
    simp only [Equiv.Perm.mul_apply]
    by_cases hx : p x
    · have h1 : Equiv.Perm.ofSubtype (σ.subtypePerm (p := fun a => ¬ p a) hp') x = x :=
        Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun a => ¬ p a) _ (not_not_intro hx)
      rw [h1, Equiv.Perm.ofSubtype_apply_of_mem (p := p) _ hx]
      rfl
    · have h1 : Equiv.Perm.ofSubtype (σ.subtypePerm (p := fun a => ¬ p a) hp') x = σ x := by
        rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun a => ¬ p a) _ hx]
        rfl
      rw [h1]
      exact (Equiv.Perm.ofSubtype_apply_of_not_mem (p := p) _
        (fun h => hx ((hp x).mp h))).symm
  conv_lhs => rw [key]
  rw [map_mul, Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_ofSubtype]

/-! ### 2. 推移的な置換の符号 -/

/-- **推移的な置換の符号は `(−1)^(card+1)`**。
  一点なら恒等（`(−1)^2 = 1`）、二点以上なら不動点が無く、全体を回す一本の巡回になる。 -/
theorem sign_transitive {γ : Type*} [Fintype γ] [DecidableEq γ] (σ : Equiv.Perm γ)
    (hne : Nonempty γ) (htr : ∀ x y : γ, ∃ k : ℕ, (σ ^ k) x = y) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card γ + 1) := by
  obtain ⟨x0⟩ := hne
  have hpos : 0 < Fintype.card γ := Fintype.card_pos_iff.mpr ⟨x0⟩
  by_cases h1 : Fintype.card γ = 1
  · have hss : Subsingleton γ := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
    have hone : σ = 1 := Equiv.ext (fun x => hss.allEq (σ x) x)
    rw [hone, h1]
    simp
  · have hcard : 2 ≤ Fintype.card γ := by omega
    have hnofix : ∀ x : γ, σ x ≠ x := by
      intro x hx
      have hall : ∀ k : ℕ, (σ ^ k) x = x := by
        intro k
        induction k with
        | zero => simp
        | succ m ih => rw [pow_succ, Equiv.Perm.mul_apply, hx, ih]
      have hev : ∀ y : γ, y = x := by
        intro y
        obtain ⟨k, hk⟩ := htr x y
        rw [← hk, hall k]
      have hss : Subsingleton γ := ⟨fun a b => (hev a).trans (hev b).symm⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hss
      omega
    have hsupp : σ.support = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun y => Equiv.Perm.mem_support.mpr (hnofix y))
    have hcyc : σ.IsCycle := by
      refine ⟨x0, hnofix x0, fun y _ => ?_⟩
      obtain ⟨k, hk⟩ := htr x0 y
      exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩
    rw [hcyc.sign, hsupp, Finset.card_univ, pow_succ, mul_neg_one]

/-! ### 3. 三本の繊維への分割 -/

/-- 部分型の濃度の和。 -/
theorem card_subtype_add (p : α → Prop) [DecidablePred p] :
    Fintype.card {x : α // p x} + Fintype.card {x : α // ¬ p x} = Fintype.card α := by
  rw [Fintype.card_subtype_compl]
  have := Fintype.card_subtype_le p
  omega

/-- **`ZMod 3` に値を取る不変写像で、繊維ごとに推移的なら、符号は `(−1)^(card+3)`**。
  紙の証明の「糸が 3 本なら `sgn(next₃) = (−1)^{2q−3}」の一般形。 -/
theorem sign_split3 (σ : Equiv.Perm α) (f : α → ZMod 3)
    (hf : ∀ x, f (σ x) = f x)
    (htr : ∀ x y : α, f x = f y → ∃ k : ℕ, (σ ^ k) x = y)
    (hsur : ∀ c : ZMod 3, ∃ x : α, f x = c) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card α + 3) := by
  have hp : ∀ x, (f (σ x) = 0) ↔ (f x = 0) := fun x => by rw [hf]
  have hp' : ∀ x, ¬ (f (σ x) = 0) ↔ ¬ (f x = 0) := fun x => by rw [hf]
  rw [sign_split σ (fun x => f x = 0) hp hp']
  -- 第一の糸
  have h0 : Equiv.Perm.sign (σ.subtypePerm (p := fun x => f x = 0) hp)
      = (-1 : ℤˣ) ^ (Fintype.card {x : α // f x = 0} + 1) := by
    refine sign_transitive _ ?_ ?_
    · obtain ⟨x, hx⟩ := hsur 0
      exact ⟨⟨x, hx⟩⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨k, hk⟩ := htr x y (by rw [show f x = 0 from hx, show f y = 0 from hy])
      refine ⟨k, Subtype.ext ?_⟩
      rw [subtypePerm_pow_val]
      exact hk
  rw [h0]
  -- 残りを `f = 1` かどうかで割る
  set τ := σ.subtypePerm (p := fun a => ¬ (f a = 0)) hp' with hτdef
  have hr : ∀ y : {x : α // ¬ (f x = 0)}, (f ((τ y : {x : α // ¬ (f x = 0)}) : α) = 1)
      ↔ (f (y : α) = 1) := by
    intro y
    rw [hτdef]
    simp only [Equiv.Perm.subtypePerm_apply, hf]
  have hr' : ∀ y : {x : α // ¬ (f x = 0)}, ¬ (f ((τ y : {x : α // ¬ (f x = 0)}) : α) = 1)
      ↔ ¬ (f (y : α) = 1) := by
    intro y
    rw [hτdef]
    simp only [Equiv.Perm.subtypePerm_apply, hf]
  rw [sign_split τ (fun y => f (y : α) = 1) hr hr']
  -- 第二の糸
  have h1 : Equiv.Perm.sign (τ.subtypePerm (p := fun y : {x : α // ¬ (f x = 0)} => f (y : α) = 1) hr)
      = (-1 : ℤˣ) ^ (Fintype.card {y : {x : α // ¬ (f x = 0)} // f (y : α) = 1} + 1) := by
    refine sign_transitive _ ?_ ?_
    · obtain ⟨x, hx⟩ := hsur 1
      have hx0 : ¬ (f x = 0) := by rw [hx]; decide
      exact ⟨⟨⟨x, hx0⟩, hx⟩⟩
    · rintro ⟨⟨x, hx0⟩, hx1⟩ ⟨⟨y, hy0⟩, hy1⟩
      obtain ⟨k, hk⟩ := htr x y (by rw [show f x = 1 from hx1, show f y = 1 from hy1])
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      rw [subtypePerm_pow_val, hτdef, subtypePerm_pow_val]
      exact hk
  -- 第三の糸
  have h2 : Equiv.Perm.sign (τ.subtypePerm (p := fun y : {x : α // ¬ (f x = 0)} => ¬ (f (y : α) = 1)) hr')
      = (-1 : ℤˣ) ^ (Fintype.card {y : {x : α // ¬ (f x = 0)} // ¬ (f (y : α) = 1)} + 1) := by
    refine sign_transitive _ ?_ ?_
    · obtain ⟨x, hx⟩ := hsur 2
      have hx0 : ¬ (f x = 0) := by rw [hx]; decide
      have hx1 : ¬ (f x = 1) := by rw [hx]; decide
      exact ⟨⟨⟨x, hx0⟩, hx1⟩⟩
    · rintro ⟨⟨x, hx0⟩, hx1⟩ ⟨⟨y, hy0⟩, hy1⟩
      have tri : ∀ a b : ZMod 3, ¬ (a = 0) → ¬ (a = 1) → ¬ (b = 0) → ¬ (b = 1) → a = b := by
        decide
      obtain ⟨k, hk⟩ := htr x y (tri _ _ hx0 hx1 hy0 hy1)
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      rw [subtypePerm_pow_val, hτdef, subtypePerm_pow_val]
      exact hk
  rw [h1, h2]
  have e1 : Fintype.card {y : {x : α // ¬ (f x = 0)} // f (y : α) = 1}
      + Fintype.card {y : {x : α // ¬ (f x = 0)} // ¬ (f (y : α) = 1)}
      = Fintype.card {x : α // ¬ (f x = 0)} := card_subtype_add _
  have e2 : Fintype.card {x : α // f x = 0} + Fintype.card {x : α // ¬ (f x = 0)}
      = Fintype.card α := card_subtype_add _
  rw [← pow_add, ← pow_add]
  congr 1
  omega

end GeneralizedPetersen.Count

namespace GeneralizedPetersen.Count

open Finset GeneralizedPetersen.Base GeneralizedPetersen.Blocks

variable {d : ℕ} [NeZero d]

/-! ### 1. `3 ∣ d` のときの糸の番号付け -/

/-- **`ZMod d → ZMod 3` の値が等しい ⟺ 同じ糸に載っている。**
  `Blocks` の `thrHom_eq_iff` の `3 ∣ d` 版だが、型の添字が `3` に固定されるので
  Bezout が要らず、`(s − r).val` が `3` で割れることを見るだけで済む。 -/
theorem castHom3_eq_iff (h3 : 3 ∣ d) (r s : ZMod d) :
    ZMod.castHom h3 (ZMod 3) r = ZMod.castHom h3 (ZMod 3) s ↔ sameThread d r s := by
  have hri : ∀ z : ZMod d, ((z.val : ℕ) : ZMod d) = z := ZMod.natCast_rightInverse
  constructor
  · intro h
    have h1 : ZMod.castHom h3 (ZMod 3) (s - r) = 0 := by rw [map_sub, h, sub_self]
    rw [← hri (s - r), map_natCast] at h1
    obtain ⟨m, hm⟩ := (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mp h1
    refine ⟨m, ?_⟩
    have hv : (((s - r).val : ℕ) : ZMod d) = ((3 * m : ℕ) : ZMod d) := by rw [hm]
    rw [hri] at hv
    push_cast at hv
    linear_combination hv
  · rintro ⟨t, rfl⟩
    have h30 : ZMod.castHom h3 (ZMod 3) (3 : ZMod d) = 0 := by
      rw [show (3 : ZMod d) = ((3 : ℕ) : ZMod d) by norm_num, map_natCast]
      decide
    rw [map_add, map_mul, h30, zero_mul, add_zero]

/-- 糸の番号（`3 ∣ d` のとき）。 -/
def thr3 (h3 : 3 ∣ d) (F : Win d) (x : ↥(Gi F)) : ZMod 3 :=
  ZMod.castHom h3 (ZMod 3) (x : ZMod d)

/-- `next₃` は糸を変えない。 -/
theorem thr3_next3 (h3 : 3 ∣ d) (F : Win d) (x : ↥(Gi F)) :
    thr3 h3 F (next3 F x) = thr3 h3 F x := by
  have h := (castHom3_eq_iff h3 (x : ZMod d) (ret F (x : ZMod d))).mpr (ret_sameThread F _)
  simp only [thr3, next3_val]
  exact h.symm

/-- **糸の上で `next₃` は推移的**（`Blocks` の `reach` をそのまま使う）。 -/
theorem thr3_trans (h3 : 3 ∣ d) (F : Win d) (x y : ↥(Gi F))
    (h : thr3 h3 F x = thr3 h3 F y) : ∃ k : ℕ, ((next3 F) ^ k) x = y := by
  obtain ⟨t, ht⟩ := (castHom3_eq_iff h3 (x : ZMod d) (y : ZMod d)).mp h
  obtain ⟨k, hk⟩ := reach F t (x : ZMod d) ((mem_Gi F _).mp x.2)
    (by rw [← ht]; exact (mem_Gi F _).mp y.2)
  refine ⟨k, Subtype.ext ?_⟩
  rw [next3_pow_val, hk, ← ht]

/-! ### 2. `3 ∣ d` のときの符号 -/

/-- `3 ∣ d`・`d` 奇で、三本の糸がすべて `G_i` と交わるなら
  `sign (next₃) = −1`。（`|G_i| = 2q` は偶数、糸は 3 本なので `(−1)^{2q+3} = −1`。） -/
theorem sign_next3_dvd (F : Win d) (hodd : Odd d) (h3 : 3 ∣ d)
    (hall3 : ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c) :
    Equiv.Perm.sign (next3 F) = -1 := by
  have hmain : Equiv.Perm.sign (next3 F)
      = (-1 : ℤˣ) ^ (Fintype.card ↥(Gi F) + 3) := by
    refine sign_split3 (next3 F) (thr3 h3 F) (thr3_next3 h3 F) (thr3_trans h3 F) ?_
    intro c
    obtain ⟨r, hr, hc⟩ := hall3 c
    exact ⟨⟨r, hr⟩, hc⟩
  rw [hmain, card_Gi_type, q_eq_two_n1 F hodd, pow_add, pow_mul]
  norm_num

/-- **`d` が 3 で割れるかどうかに依らず `sign (next₃) = −1`。** -/
theorem sign_next3_all (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty)
    (hall3 : ∀ h3 : 3 ∣ d, ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c) :
    Equiv.Perm.sign (next3 F) = -1 := by
  by_cases h3 : 3 ∣ d
  · exact sign_next3_dvd F hodd h3 (hall3 h3)
  · exact sign_next3 F hodd h3 hne

/-- **紙の証明の定理 2 の符号の段が、橋の仮定なしで一般の `d`（奇）で閉じる。**
  `θ` が `G_i` 全体を回す巡回なら、`next₃ ∘ θ` は全体を回す巡回になれない。 -/
theorem next3_theta_not_full_cycle_general (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty)
    (hall3 : ∀ h3 : 3 ∣ d, ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c)
    (θ : Equiv.Perm ↥(Gi F)) (hθ : θ.IsCycle) (hθs : θ.support = Finset.univ) :
    ¬ ((next3 F * θ).IsCycle ∧ (next3 F * θ).support = Finset.univ) := by
  rintro ⟨h1, h2⟩
  have hev := card_Gi_even F hodd
  have e1 : Equiv.Perm.sign (next3 F * θ) = -1 :=
    GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle _ h1 h2 hev
  have e2 : Equiv.Perm.sign (next3 F * θ) = 1 := by
    rw [map_mul, sign_next3_all F hodd hne hall3,
      GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle θ hθ hθs hev]
    simp
  rw [e1] at e2
  have e3 := congrArg (Units.val : ℤˣ → ℤ) e2
  norm_num at e3

end GeneralizedPetersen.Count

namespace GeneralizedPetersen.Count

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks

/-! ### 1. `ρ^t` による歩道の平行移動 -/

/-- **`ρ^t` で歩道を写す**。`SimpleGraph.Hom` と `Walk.map` を使うと、できた歩道の型の
  添字が `⇑(rotHomPow …) a` の形になり、`Walk.append` の項が
  「implicit 透明度では型が付かない」状態になって `simp`／`rw` が一切入らなくなる。
  そこで **`Walk` の再帰で直接作り、型の添字を `ρ^t a` の形に揃える**。 -/
theorem exists_shift (n k t : ℕ) : ∀ {a b : V n} (p : (GP n k).Walk a b),
    ∃ q : (GP n k).Walk (((rot n) ^ t) a) (((rot n) ^ t) b),
      q.length = p.length ∧ q.support = p.support.map ((rot n) ^ t) := by
  intro a b p
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  | cons h p ih =>
      obtain ⟨q, hl, hs⟩ := ih
      exact ⟨SimpleGraph.Walk.cons ((GP_adj_rot_pow n k t _ _).mpr h) q, by simp [hl],
        by simp [hs]⟩

/-! ### 2. `m` 周ぶんの接続 -/

/-- **歩道の接続**：終点が `ρ^e x` の歩道を `ρ^{e t}` で写しながら `i` 回繋ぐと、
  終点が `ρ^{e i} x` の歩道になり、台は `⋃_{t<i} ρ^{e t}(もとの台)`（と始点）である。
  `support_append` の `tail` は使わず、`mem_support_append_iff`（membership）で押す。 -/
theorem exists_loop (n k e : ℕ) (x : V n) (w : (GP n k).Walk x (((rot n) ^ e) x)) :
    ∀ i : ℕ, ∃ (y : V n) (u : (GP n k).Walk x y),
      y = ((rot n) ^ (e * i)) x ∧ u.length = i * w.length ∧
      ∀ v : V n, (v ∈ u.support ↔
        (v = x ∨ ∃ t < i, ∃ z ∈ w.support, v = ((rot n) ^ (e * t)) z)) := by
  intro i
  induction i with
  | zero =>
      refine ⟨x, SimpleGraph.Walk.nil, by simp, by simp, ?_⟩
      intro v
      simp
  | succ i ih =>
      obtain ⟨y, u, hy, hlen, hsup⟩ := ih
      subst hy
      obtain ⟨q, hql, hqs⟩ := exists_shift n k (e * i) w
      have hend : ((rot n) ^ (e * i)) (((rot n) ^ e) x) = ((rot n) ^ (e * (i + 1))) x := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, show e * i + e = e * (i + 1) by ring]
      refine ⟨_, u.append q, hend, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_append, hlen, hql]
        ring
      · intro v
        rw [SimpleGraph.Walk.mem_support_append_iff, hsup v, hqs]
        constructor
        · rintro (h | h)
          · rcases h with h | ⟨t, ht, z, hz, hv⟩
            · exact Or.inl h
            · exact Or.inr ⟨t, by omega, z, hz, hv⟩
          · obtain ⟨z, hz, hv⟩ := List.mem_map.mp h
            exact Or.inr ⟨i, by omega, z, hz, hv.symm⟩
        · rintro (h | ⟨t, ht, z, hz, hv⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge t i with hti | hti
            · exact Or.inl (Or.inr ⟨t, hti, z, hz, hv⟩)
            · have hti' : t = i := by omega
              subst hti'
              exact Or.inr (List.mem_map.mpr ⟨z, hz, hv.symm⟩)

/-! ### 3. 覆いの条件（`gcd(j, m) = 1`） -/

/-- **`m` 周で全頂点を覆う条件**。`S` が商 `V d` の全点に当たり（商でハミルトン）、
  巻き数 `j` が `m = n/d` と互いに素なら、`ρ^{d j t}` (`t < m`) の像の和は全頂点。
  `Base` の `lift_connected_iff`（群論の核）がここで効く。 -/
theorem loop_covers (n d j m : ℕ) [NeZero n] (hm : n = d * m) (hmpos : 0 < m)
    (S : List (V n)) (hS : ∀ z : V d, ∃ y ∈ S, quotMap n d ⟨m, hm⟩ y = z)
    (hcop : Nat.Coprime j m) :
    ∀ v : V n, ∃ t < m, ∃ y ∈ S, v = ((rot n) ^ (d * j * t)) y := by
  haveI : NeZero m := ⟨by omega⟩
  intro v
  obtain ⟨y, hy, hq⟩ := hS (quotMap n d ⟨m, hm⟩ v)
  obtain ⟨a, ha⟩ := (quotMap_eq_iff n d ⟨m, hm⟩ y v).mp hq
  obtain ⟨t', ht'⟩ := (lift_connected_iff m j).mpr hcop ((a : ℕ) : ZMod m)
  have hmod : (t' % m) * j ≡ a [MOD m] := by
    have h1 : ((t' * j : ℕ) : ZMod m) = ((a : ℕ) : ZMod m) := by
      rw [Nat.cast_mul]
      exact ht'
    have h2 : t' * j ≡ a [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
    exact (Nat.ModEq.mul_right j (Nat.mod_modEq t' m)).trans h2
  have hbig : d * ((t' % m) * j) ≡ d * a [MOD n] := by
    rw [hm]
    exact Nat.ModEq.mul_left' d hmod
  have hcast : ((d * j * (t' % m) : ℕ) : ZMod n) = ((d * a : ℕ) : ZMod n) := by
    rw [show d * j * (t' % m) = d * ((t' % m) * j) by ring]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hbig
  refine ⟨t' % m, Nat.mod_lt _ hmpos, y, hy, ?_⟩
  rw [← ha, rot_pow_apply, rot_pow_apply, hcast]

/-- **(β) の到達点**：商 `GP(d,k)` の閉路の持ち上げ（終点 `ρ^{dj}x`）を `m` 周繋ぐと、
  `gcd(j,m)=1` かつ持ち上げの台が各繊維に当たるとき、台は全頂点になる。 -/
theorem exists_loop_covering (n k d j m : ℕ) [NeZero n] (hm : n = d * m) (hmpos : 0 < m)
    (x : V n) (w : (GP n k).Walk x (((rot n) ^ (d * j)) x))
    (hS : ∀ z : V d, ∃ y ∈ w.support, quotMap n d ⟨m, hm⟩ y = z)
    (hcop : Nat.Coprime j m) :
    ∃ u : (GP n k).Walk x (((rot n) ^ (d * j * m)) x),
      u.length = m * w.length ∧ ∀ v : V n, v ∈ u.support := by
  obtain ⟨y, u, hy, hlen, hsup⟩ := exists_loop n k (d * j) x w m
  subst hy
  refine ⟨u, hlen, fun v => ?_⟩
  rw [hsup v]
  obtain ⟨t, ht, y, hy, hv⟩ := loop_covers n d j m hm hmpos w.support hS hcop v
  exact Or.inr ⟨t, ht, y, hy, hv⟩

end GeneralizedPetersen.Count

namespace GeneralizedPetersen.Count

open Finset GeneralizedPetersen.Base GeneralizedPetersen.Blocks

variable {d : ℕ} [NeZero d]

/-! ### 1. 歩幅 `−1` の初回帰 -/

/-- `t` 歩（後ろ向き）で `G_i` に戻る。`d` 歩目は無条件に許す（`(d : ZMod d) = 0`）。 -/
def prevP (F : Win d) (r : ZMod d) (t : ℕ) : Prop :=
  0 < t ∧ (d ≤ t ∨ F.i (r - (t : ZMod d)) = 0)

instance decPrevP (F : Win d) (r : ZMod d) : DecidablePred (prevP F r) := fun t => by
  unfold prevP; infer_instance

theorem prevP_ex (F : Win d) (r : ZMod d) : ∃ t, prevP F r t :=
  ⟨d, Nat.pos_of_ne_zero (NeZero.ne d), Or.inl le_rfl⟩

/-- 戻り時間（後ろ向き）。 -/
def prevT (F : Win d) (r : ZMod d) : ℕ := Nat.find (prevP_ex F r)

/-- `θ` の値。 -/
def prev (F : Win d) (r : ZMod d) : ZMod d := r - ((prevT F r : ℕ) : ZMod d)

theorem prevT_pos (F : Win d) (r : ZMod d) : 0 < prevT F r := (Nat.find_spec (prevP_ex F r)).1

theorem prevT_le (F : Win d) (r : ZMod d) : prevT F r ≤ d :=
  Nat.find_le ⟨Nat.pos_of_ne_zero (NeZero.ne d), Or.inl le_rfl⟩

theorem prevT_min (F : Win d) {r : ZMod d} {t : ℕ} (ht : t < prevT F r) : ¬ prevP F r t :=
  Nat.find_min _ ht

theorem prev_mem (F : Win d) {r : ZMod d} (hr : F.i r = 0) : F.i (prev F r) = 0 := by
  rcases (Nat.find_spec (prevP_ex F r)).2 with hge | h
  · have he : prevT F r = d := le_antisymm (prevT_le F r) hge
    rw [prev, he, ZMod.natCast_self, sub_zero]
    exact hr
  · exact h

/-! ### 2. 単射性 -/

theorem prev_inj_aux (F : Win d) {r r' : ZMod d} (hr : F.i r = 0) (hr' : F.i r' = 0)
    (he : prev F r = prev F r') (hle : prevT F r ≤ prevT F r') : r = r' := by
  have hp := prevT_pos F r
  have hp' := prevT_pos F r'
  rcases eq_or_lt_of_le hle with heq | hlt
  · simp only [prev, heq] at he
    exact sub_left_injective he
  · exfalso
    refine prevT_min F (r := r') (t := prevT F r' - prevT F r) (by omega) ⟨by omega, Or.inr ?_⟩
    have hcast : ((prevT F r' - prevT F r : ℕ) : ZMod d)
        = ((prevT F r' : ℕ) : ZMod d) - ((prevT F r : ℕ) : ZMod d) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have hrw : r' - (((prevT F r' : ℕ) : ZMod d) - ((prevT F r : ℕ) : ZMod d)) = r := by
      simp only [prev] at he
      linear_combination -he
    rw [hrw]
    exact hr

theorem prev_inj (F : Win d) {r r' : ZMod d} (hr : F.i r = 0) (hr' : F.i r' = 0)
    (he : prev F r = prev F r') : r = r' := by
  rcases le_total (prevT F r) (prevT F r') with hle | hle
  · exact prev_inj_aux F hr hr' he hle
  · exact (prev_inj_aux F hr' hr he.symm hle).symm

/-! ### 3. 置換 `θ` -/

/-- **`θ`：`G_i` の円周上の前者置換**（紙の証明の `θ`）。 -/
noncomputable def theta (F : Win d) : Equiv.Perm ↥(Gi F) :=
  Equiv.ofBijective (fun x => ⟨prev F (x : ZMod d), by
      rw [mem_Gi]
      exact prev_mem F ((mem_Gi F _).mp x.2)⟩)
    (Finite.injective_iff_bijective.mp (fun x y hxy => by
      apply Subtype.ext
      exact prev_inj F ((mem_Gi F _).mp x.2) ((mem_Gi F _).mp y.2) (congrArg Subtype.val hxy)))

@[simp] theorem theta_val (F : Win d) (x : ↥(Gi F)) :
    ((theta F x : ↥(Gi F)) : ZMod d) = prev F (x : ZMod d) := rfl

theorem theta_pow_val (F : Win d) : ∀ (k : ℕ) (x : ↥(Gi F)),
    (((theta F ^ k) x : ↥(Gi F)) : ZMod d) = (prev F)^[k] (x : ZMod d) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ m ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (theta F x), Function.iterate_succ_apply, theta_val]

/-! ### 4. 到達可能性と一本巡回 -/

/-- `x` から `x − u`（どちらも `G_i` の元）へは `θ` の反復で届く。 -/
theorem reach_prev (F : Win d) : ∀ (u : ℕ) (x : ZMod d), F.i x = 0 →
    F.i (x - (u : ZMod d)) = 0 → ∃ k : ℕ, (prev F)^[k] x = x - (u : ZMod d) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro x hx hxu
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · exact ⟨0, by simp⟩
    · have hprevP : prevP F x u := ⟨hu, Or.inr hxu⟩
      have hle : prevT F x ≤ u := Nat.find_le hprevP
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact ⟨1, by rw [Function.iterate_one]; simp only [prev, heq]⟩
      · have hp := prevT_pos F x
        have hx' : F.i (prev F x) = 0 := prev_mem F hx
        have hcast : prev F x - ((u - prevT F x : ℕ) : ZMod d) = x - (u : ZMod d) := by
          rw [Nat.cast_sub hle]
          simp only [prev]
          ring
        obtain ⟨k, hk⟩ := ih (u - prevT F x) (by omega) (prev F x) hx' (by rw [hcast]; exact hxu)
        exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk, hcast]⟩

/-- `|G_i| ≥ 2`（`d` 奇のブロック構造から）。 -/
theorem two_le_card_Gi (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty) :
    2 ≤ (Gi F).card := by
  have h1 : F.q = 2 * F.n1 := q_eq_two_n1 F hodd
  have h2 : 0 < (Gi F).card := Finset.card_pos.mpr hne
  rw [card_Gi] at h2 ⊢
  omega

/-- **不動点なし**：`d` 奇なら `θ` は `G_i` の元を固定しない。 -/
theorem theta_ne_self (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty) (x : ↥(Gi F)) :
    theta F x ≠ x := by
  intro hfix
  have hxG : F.i (x : ZMod d) = 0 := (mem_Gi F _).mp x.2
  have hprev : prev F (x : ZMod d) = (x : ZMod d) := by
    have := congrArg Subtype.val hfix
    rwa [theta_val] at this
  have h0 : ((prevT F (x : ZMod d) : ℕ) : ZMod d) = 0 := by
    simp only [prev] at hprev
    linear_combination -hprev
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hpos := prevT_pos F (x : ZMod d)
  have hle := prevT_le F (x : ZMod d)
  have heqd : prevT F (x : ZMod d) = d := Nat.le_antisymm hle (Nat.le_of_dvd hpos h0)
  -- `G_i` には `x` 以外の元があるので、`d` より手前で戻れてしまう
  have hcard2 : 1 < (Gi F).card := by
    have := two_le_card_Gi F hodd hne
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard2
  obtain ⟨y, hyG, hyx⟩ : ∃ y ∈ Gi F, y ≠ (x : ZMod d) := by
    by_cases hax : a = (x : ZMod d)
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  have hri : ∀ z : ZMod d, ((z.val : ℕ) : ZMod d) = z := ZMod.natCast_rightInverse
  set u : ℕ := ((x : ZMod d) - y).val with hudef
  have hu0 : u ≠ 0 := by
    intro hz
    apply hyx
    have : ((x : ZMod d) - y) = 0 := by
      rw [← hri ((x : ZMod d) - y), ← hudef, hz]
      simp
    linear_combination -this
  have hlt : u < d := ZMod.val_lt _
  have hsub : (x : ZMod d) - ((u : ℕ) : ZMod d) = y := by
    rw [hudef, hri]
    ring
  have hsP : prevP F (x : ZMod d) u := ⟨Nat.pos_of_ne_zero hu0, Or.inr (by
    rw [hsub]; exact (mem_Gi F y).mp hyG)⟩
  have hfin : prevT F (x : ZMod d) ≤ u := Nat.find_le hsP
  omega

/-- **`θ` は `G_i` 全体を回る一本の巡回**（`d` 奇・`G_i ≠ ∅`）。
  歩幅が `−1` なので、`3 ∤ d` のような条件は要らない。 -/
theorem theta_isCycle (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty) :
    (theta F).IsCycle ∧ (theta F).support = Finset.univ := by
  obtain ⟨x0, hx0⟩ := hne
  have hri : ∀ z : ZMod d, ((z.val : ℕ) : ZMod d) = z := ZMod.natCast_rightInverse
  refine ⟨⟨⟨x0, hx0⟩, theta_ne_self F hodd ⟨x0, hx0⟩ _, fun y _ => ?_⟩, ?_⟩
  · have hsub : x0 - (((x0 - (y : ZMod d)).val : ℕ) : ZMod d) = (y : ZMod d) := by
      rw [hri]; ring
    obtain ⟨k, hk⟩ := reach_prev F ((x0 - (y : ZMod d)).val) x0 ((mem_Gi F _).mp hx0)
      (by rw [hsub]; exact (mem_Gi F _).mp y.2)
    refine ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    rw [theta_pow_val, hk, hsub]
  · refine Finset.eq_univ_iff_forall.mpr (fun y => ?_)
    rw [Equiv.Perm.mem_support]
    exact theta_ne_self F hodd ⟨x0, hx0⟩ y

/-! ### 5. (α)＋(γ)：紙の証明の定理 2 の完成形 -/

/-- **紙の証明の定理 2（符号の矛盾）が、`Win d` だけから出る形になった。**
  `d` 奇・`G_i ≠ ∅`・（`3 ∣ d` なら三本の糸がすべて `G_i` と交わる）なら、
  `next₃ ∘ θ` は `G_i` 全体を回る巡回になれない
  ——すなわち商 `GP(d,3)` の対応する 2 因子は一本の閉路にならない。 -/
theorem next3_theta_of_Win (F : Win d) (hodd : Odd d) (hne : (Gi F).Nonempty)
    (hall3 : ∀ h3 : 3 ∣ d, ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c) :
    ¬ ((next3 F * theta F).IsCycle ∧ (next3 F * theta F).support = Finset.univ) := by
  obtain ⟨hc, hs⟩ := theta_isCycle F hodd hne
  exact next3_theta_not_full_cycle_general F hodd hne hall3 (theta F) hc hs

end GeneralizedPetersen.Count

namespace GeneralizedPetersen.Count

open SimpleGraph GeneralizedPetersen.Base GeneralizedPetersen.Blocks

/-! ### 1. 一般の `n` での `#HC` -/

open scoped Classical in
/-- **ハミルトン閉路の辺集合の全体**（一般の `n`）。 -/
noncomputable def HamEdges (n k : ℕ) [NeZero n] : Finset (Finset (Sym2 (V n))) :=
  Finset.univ.filter (fun E => ∃ (x : V n) (p : (GP n k).Walk x x),
    p.IsHamiltonianCycle ∧ p.edges.toFinset = E)

open scoped Classical in
theorem mem_HamEdges (n k : ℕ) [NeZero n] (E : Finset (Sym2 (V n))) :
    E ∈ HamEdges n k ↔ ∃ (x : V n) (p : (GP n k).Walk x x),
      p.IsHamiltonianCycle ∧ p.edges.toFinset = E := by
  unfold HamEdges
  simp

/-- **`#HC(GP(n,k))`**：ハミルトン閉路の個数（辺集合として数える）。 -/
noncomputable def numHC (n k : ℕ) [NeZero n] : ℕ := (HamEdges n k).card

/-! ### 2. 回転の辺集合への作用 -/

/-- 回転の辺集合への作用。 -/
noncomputable def rotE (n : ℕ) [NeZero n] (E : Finset (Sym2 (V n))) : Finset (Sym2 (V n)) :=
  E.image (Sym2.map (rot n))

theorem toFinset_map_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp

/-- `ρ^i` の反復は `Sym2.map (ρ^i)` による像。 -/
theorem rotE_iterate (n : ℕ) [NeZero n] (E : Finset (Sym2 (V n))) :
    ∀ i : ℕ, (rotE n)^[i] E = E.image (Sym2.map ((rot n) ^ i)) := by
  intro i
  induction i with
  | zero => simp [Sym2.map_id]
  | succ i ih =>
      have hfun : ⇑((rot n) ^ (i + 1)) = ⇑(rot n) ∘ ⇑((rot n) ^ i) := by
        rw [pow_succ', Equiv.Perm.coe_mul]
      rw [Function.iterate_succ_apply', ih, rotE, Finset.image_image, hfun]
      refine Finset.image_congr ?_
      intro z _
      simp only [Function.comp_apply, Sym2.map_map]

/-- 回転はハミルトン閉路をハミルトン閉路に写す（辺集合の言葉で）。 -/
theorem rotE_mem (n k : ℕ) [NeZero n] {E : Finset (Sym2 (V n))} (hE : E ∈ HamEdges n k) :
    rotE n E ∈ HamEdges n k := by
  rw [mem_HamEdges] at hE ⊢
  obtain ⟨x, p, hp, hedges⟩ := hE
  refine ⟨rotIso n k x, p.map (rotIso n k).toHom, rotIso_hamiltonian hp, ?_⟩
  rw [SimpleGraph.Walk.edges_map, toFinset_map_eq, hedges]
  rfl

/-- `ρ^n = 1` なので、`n` 回の作用は恒等。 -/
theorem rotE_pow_card (n : ℕ) [NeZero n] (E : Finset (Sym2 (V n))) :
    (rotE n)^[n] E = E := by
  rw [rotE_iterate, rot_pow_card]
  simp [Sym2.map_id]

/-! ### 3. 自由な作用から割り切れへ -/

/-- **段階 1→2（一般の `n`・`k`）**：`0 < i < n` の `ρ^i` がハミルトン閉路を
  一つも固定しなければ `n ∣ #HC(GP(n,k))`。 -/
theorem gp_dvd_numHC (n k : ℕ) [NeZero n]
    (hfree : ∀ i, 0 < i → i < n → ∀ E ∈ HamEdges n k, (rotE n)^[i] E ≠ E) :
    n ∣ numHC n k := by
  refine GeneralizedPetersen.FreeAction.dvd_card_of_iterate_free (HamEdges n k) (rotE n) n
    (Nat.pos_of_ne_zero (NeZero.ne n)) ?_ ?_ hfree
  · intro E hE
    exact rotE_mem n k hE
  · intro E _
    exact rotE_pow_card n E

/-! ### 4. `k = 3`：残る橋を明示した条件つき定理 -/

/-- **(δ) の橋**。`ρ^i` 不変なハミルトン閉路があれば、紙の証明–§2 の手順で
  商 `GP(d,3)`（`d = gcd(i,n)`、`n` 奇なので `d` 奇）の 2 因子から `Win d` が作れ、
  三本の糸はすべて `G_i` と交わり、しかもその 2 因子が**一本の閉路**である
  ——すなわち `next₃ ∘ θ` が `G_i` 全体を回る巡回になる——という言明。
  `θ` は(γ) で構成済みなので、**残る中身は「2 因子から `Win d` を作る」一点**である。 -/
def WinBridge (n : ℕ) [NeZero n] : Prop :=
  ∀ i, 0 < i → i < n → ∀ E ∈ HamEdges n 3, (rotE n)^[i] E = E →
    ∃ (d : ℕ) (_ : NeZero d) (F : Win d), Odd d ∧ (Gi F).Nonempty ∧
      (∀ h3 : 3 ∣ d, ∀ c : ZMod 3, ∃ r ∈ Gi F, ZMod.castHom h3 (ZMod 3) r = c) ∧
      (next3 F * theta F).IsCycle ∧ (next3 F * theta F).support = Finset.univ

/-- **一般 `n`（条件つき）**：`n` 奇・`n ≥ 7` で橋 `WinBridge n` を仮定すれば
  `n ∣ #HC(GP(n,3))`。橋の外側——符号の矛盾（(α)）・`θ` の構成（(γ)）・
  数え上げ（段階 1→2）——はすべて Lean に入っている。 -/
theorem gp3_dvd_hc (n : ℕ) [NeZero n] (_hn : Odd n) (_h7 : 7 ≤ n) (hbridge : WinBridge n) :
    n ∣ numHC n 3 := by
  refine gp_dvd_numHC n 3 ?_
  intro i hi hin E hE hfix
  obtain ⟨d, hd, F, hodd, hne, hall3, hc1, hc2⟩ := hbridge i hi hin E hE hfix
  haveI : NeZero d := hd
  exact next3_theta_of_Win F hodd hne hall3 ⟨hc1, hc2⟩

end GeneralizedPetersen.Count
