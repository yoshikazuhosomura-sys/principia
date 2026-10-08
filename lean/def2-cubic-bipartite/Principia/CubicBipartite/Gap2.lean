import Mathlib

/-!
# Principia.CubicBipartite.Gap2

  周長欠損 2 の三価二部グラフ：30 頂点の三例 `G30`・`G30b`・`G30c` と 20 頂点の例 `G20`。
  隣接はビット符号化され、辺リストとの一致は `decide` で確かめる。
  非ハミルトン性は歩道の構造帰納法で完全性を示した深さ優先探索を核で回して得る。

  sorry 0・native_decide 不使用。
-/

namespace CubicBipartite.ClassI

set_option maxRecDepth 20000

open SimpleGraph

/-! ### 1. グラフの定義（ビット符号化） -/

/-- 隣接リストの符号化：頂点 v の第 i 近傍（i < 3、昇順）が 5 ビットずつ。 -/
def NBD : ℕ := 2587580477521153695637155132899306804861065942779289447327358346456278316160386608297113721942309965977811622865585985746609850816688993

/-- 頂点 v の第 i 近傍。 -/
def nb (v i : ℕ) : ℕ := (NBD >>> (15 * v + 5 * i)) &&& 31

/-- 隣接行列の符号化（30 × 30 ビット。30*a + b 番目のビットが辺 a-b）。 -/
def AMD : ℕ := 2113452207062420123101439952436967664171188295138201627142956757879482176816941441827612295729359574182013470513068875062996316484524851409461875106259099002909648617403640491085142162935315526865164204292493008689081452264127298580489815216695632261072187823743014273026

/-- 隣接判定。 -/
def adjB (a b : ℕ) : Bool := Nat.testBit AMD (30 * a + b)

theorem adjB_symm : ∀ a b : Fin 30, adjB a.val b.val = true → adjB b.val a.val = true := by
  decide

theorem adjB_irrefl : ∀ a : Fin 30, ¬ (adjB a.val a.val = true) := by decide

/-- 類 I のグラフ（45 辺）。 -/
def G30 : SimpleGraph (Fin 30) where
  Adj a b := adjB a.val b.val = true
  symm := ⟨fun a b h => adjB_symm a b h⟩
  loopless := ⟨fun a h => adjB_irrefl a h⟩

instance : DecidableRel G30.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB a.val b.val = true))

/-! ### 2. 辺リストとの一致（監査用） -/

/-- 「類 I」の辺リスト（x = 28, y = 29）。 -/
def edgeList : List (Fin 30 × Fin 30) :=
  [
   (0, 1), (0, 27), (0, 28), (1, 2), (1, 14),
   (2, 3), (2, 17), (3, 4), (3, 12), (4, 5),
   (4, 28), (5, 6), (5, 8), (6, 7), (6, 9),
   (7, 8), (7, 10), (8, 9), (9, 10), (10, 11),
   (11, 12), (11, 29), (12, 13), (13, 14), (13, 26),
   (14, 15), (15, 16), (15, 29), (16, 17), (16, 25),
   (17, 18), (18, 19), (18, 27), (19, 20), (19, 22),
   (20, 21), (20, 23), (21, 22), (21, 24), (22, 23),
   (23, 24), (24, 25), (25, 26), (26, 27), (28, 29)
  ]

theorem edgeList_card : edgeList.length = 45 := by rfl

/-- ビット符号化されたグラフは辺リストそのものである。 -/
theorem adj_iff_mem_edgeList : ∀ a b : Fin 30,
    G30.Adj a b ↔ ((a, b) ∈ edgeList ∨ (b, a) ∈ edgeList) := by decide

/-! ### 3. 三価・二部（明示の 2-彩色）・連結 -/

theorem G30_degree : ∀ v : Fin 30, G30.degree v = 3 := by decide

/-- 2-彩色のマスク（C 上の偶位置と y = 29 が一方、奇位置と x = 28 が他方）。 -/
def CMASK : ℕ := 447392426

/-- 明示の 2-彩色。 -/
def col2 (v : Fin 30) : Fin 2 := if Nat.testBit CMASK v.val then 1 else 0

theorem col2_ne : ∀ a b : Fin 30, G30.Adj a b → col2 a ≠ col2 b := by decide

theorem G30_colorable : G30.Colorable 2 :=
  ⟨⟨col2, fun {a b} hab => col2_ne a b hab⟩⟩

theorem G30_connected : G30.Connected := by
  have step : ∀ (u v : Fin 30), G30.Adj u v → G30.Reachable 0 u → G30.Reachable 0 v :=
    fun u v h hr => hr.trans h.reachable
  have r0 : G30.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have r1 : G30.Reachable 0 1 := step 0 1 (by decide) r0
  have r2 : G30.Reachable 0 2 := step 1 2 (by decide) r1
  have r3 : G30.Reachable 0 3 := step 2 3 (by decide) r2
  have r4 : G30.Reachable 0 4 := step 3 4 (by decide) r3
  have r5 : G30.Reachable 0 5 := step 4 5 (by decide) r4
  have r6 : G30.Reachable 0 6 := step 5 6 (by decide) r5
  have r7 : G30.Reachable 0 7 := step 6 7 (by decide) r6
  have r8 : G30.Reachable 0 8 := step 7 8 (by decide) r7
  have r9 : G30.Reachable 0 9 := step 8 9 (by decide) r8
  have r10 : G30.Reachable 0 10 := step 9 10 (by decide) r9
  have r11 : G30.Reachable 0 11 := step 10 11 (by decide) r10
  have r12 : G30.Reachable 0 12 := step 11 12 (by decide) r11
  have r13 : G30.Reachable 0 13 := step 12 13 (by decide) r12
  have r14 : G30.Reachable 0 14 := step 13 14 (by decide) r13
  have r15 : G30.Reachable 0 15 := step 14 15 (by decide) r14
  have r16 : G30.Reachable 0 16 := step 15 16 (by decide) r15
  have r17 : G30.Reachable 0 17 := step 16 17 (by decide) r16
  have r18 : G30.Reachable 0 18 := step 17 18 (by decide) r17
  have r19 : G30.Reachable 0 19 := step 18 19 (by decide) r18
  have r20 : G30.Reachable 0 20 := step 19 20 (by decide) r19
  have r21 : G30.Reachable 0 21 := step 20 21 (by decide) r20
  have r22 : G30.Reachable 0 22 := step 21 22 (by decide) r21
  have r23 : G30.Reachable 0 23 := step 22 23 (by decide) r22
  have r24 : G30.Reachable 0 24 := step 23 24 (by decide) r23
  have r25 : G30.Reachable 0 25 := step 24 25 (by decide) r24
  have r26 : G30.Reachable 0 26 := step 25 26 (by decide) r25
  have r27 : G30.Reachable 0 27 := step 26 27 (by decide) r26
  have r28 : G30.Reachable 0 28 := step 0 28 (by decide) r0
  have r29 : G30.Reachable 0 29 := step 28 29 (by decide) r28
  have key : ∀ v : Fin 30, G30.Reachable 0 v := by
    intro v
    fin_cases v <;> assumption
  exact ⟨fun u v => (key u).symm.trans (key v)⟩

/-! ### 4. 長さ 28 の閉路 0-1-2-…-27-0 -/

def p27 : G30.Walk 27 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
def p26 : G30.Walk 26 0 := SimpleGraph.Walk.cons (by decide) p27
def p25 : G30.Walk 25 0 := SimpleGraph.Walk.cons (by decide) p26
def p24 : G30.Walk 24 0 := SimpleGraph.Walk.cons (by decide) p25
def p23 : G30.Walk 23 0 := SimpleGraph.Walk.cons (by decide) p24
def p22 : G30.Walk 22 0 := SimpleGraph.Walk.cons (by decide) p23
def p21 : G30.Walk 21 0 := SimpleGraph.Walk.cons (by decide) p22
def p20 : G30.Walk 20 0 := SimpleGraph.Walk.cons (by decide) p21
def p19 : G30.Walk 19 0 := SimpleGraph.Walk.cons (by decide) p20
def p18 : G30.Walk 18 0 := SimpleGraph.Walk.cons (by decide) p19
def p17 : G30.Walk 17 0 := SimpleGraph.Walk.cons (by decide) p18
def p16 : G30.Walk 16 0 := SimpleGraph.Walk.cons (by decide) p17
def p15 : G30.Walk 15 0 := SimpleGraph.Walk.cons (by decide) p16
def p14 : G30.Walk 14 0 := SimpleGraph.Walk.cons (by decide) p15
def p13 : G30.Walk 13 0 := SimpleGraph.Walk.cons (by decide) p14
def p12 : G30.Walk 12 0 := SimpleGraph.Walk.cons (by decide) p13
def p11 : G30.Walk 11 0 := SimpleGraph.Walk.cons (by decide) p12
def p10 : G30.Walk 10 0 := SimpleGraph.Walk.cons (by decide) p11
def p9 : G30.Walk 9 0 := SimpleGraph.Walk.cons (by decide) p10
def p8 : G30.Walk 8 0 := SimpleGraph.Walk.cons (by decide) p9
def p7 : G30.Walk 7 0 := SimpleGraph.Walk.cons (by decide) p8
def p6 : G30.Walk 6 0 := SimpleGraph.Walk.cons (by decide) p7
def p5 : G30.Walk 5 0 := SimpleGraph.Walk.cons (by decide) p6
def p4 : G30.Walk 4 0 := SimpleGraph.Walk.cons (by decide) p5
def p3 : G30.Walk 3 0 := SimpleGraph.Walk.cons (by decide) p4
def p2 : G30.Walk 2 0 := SimpleGraph.Walk.cons (by decide) p3
def p1 : G30.Walk 1 0 := SimpleGraph.Walk.cons (by decide) p2

theorem h01 : G30.Adj 0 1 := by decide

/-- 閉路 0-1-2-…-27-0（長さ 28）。 -/
def c28 : G30.Walk 0 0 := SimpleGraph.Walk.cons h01 p1

theorem c28_length : c28.length = 28 := by rfl

theorem c28_isCycle : c28.IsCycle := by
  have h : (SimpleGraph.Walk.cons h01 p1).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, by decide⟩
    rw [SimpleGraph.Walk.isPath_def]
    decide
  exact h

/-! ### 5. 二部性から「閉じた歩道の長さは偶数」 -/

theorem col_ne_of_adj : ∀ a b : Fin 30, G30.Adj a b →
    (Nat.testBit CMASK a.val ≠ Nat.testBit CMASK b.val) := by decide

theorem walk_parity : ∀ {u v : Fin 30} (w : G30.Walk u v),
    (Nat.testBit CMASK u.val = Nat.testBit CMASK v.val) ↔ (w.length % 2 = 0) := by
  intro u v w
  induction w with
  | nil => simp
  | @cons a b c hadj w' ih =>
      have hne := col_ne_of_adj a b hadj
      rw [SimpleGraph.Walk.length_cons]
      generalize hA : Nat.testBit CMASK a.val = A at hne ⊢
      generalize hB : Nat.testBit CMASK b.val = B at hne ih
      generalize hC : Nat.testBit CMASK c.val = C at ih ⊢
      cases A <;> cases B <;> cases C <;> simp_all <;> omega

theorem closed_walk_even {v : Fin 30} (w : G30.Walk v v) : w.length % 2 = 0 :=
  (walk_parity w).mp rfl

/-! ### 6. 深さ優先探索 go -/

/-- go k v vis：v から未訪問（vis のビットが 0）の頂点を k 個たどり、
  最後に頂点 0 に隣接する道があるかを探す。 -/
def go : ℕ → ℕ → ℕ → Bool
  | 0, v, _ => adjB v 0
  | (k + 1), v, vis =>
      (!Nat.testBit vis (nb v 0) && go k (nb v 0) (vis ||| 2 ^ nb v 0)) ||
      (!Nat.testBit vis (nb v 1) && go k (nb v 1) (vis ||| 2 ^ nb v 1)) ||
      (!Nat.testBit vis (nb v 2) && go k (nb v 2) (vis ||| 2 ^ nb v 2))

theorem adjB_of_adj {a b : Fin 30} (h : G30.Adj a b) : adjB a.val b.val = true := h

theorem go_zero (a : Fin 30) (vis : ℕ) (h : G30.Adj a 0) : go 0 a.val vis = true := by
  have h2 := adjB_of_adj h
  simpa [go] using h2

theorem nb_spec : ∀ a b : Fin 30, G30.Adj a b →
    (b.val = nb a.val 0 ∨ b.val = nb a.val 1 ∨ b.val = nb a.val 2) := by decide

theorem go_succ_of {k : ℕ} {v u : Fin 30} {vis : ℕ} (hadj : G30.Adj v u)
    (h0 : Nat.testBit vis u.val = false)
    (hgo : go k u.val (vis ||| 2 ^ u.val) = true) :
    go (k + 1) v.val vis = true := by
  have h := nb_spec v u hadj
  simp only [go]
  rcases h with h | h | h
  · rw [← h, h0, hgo]; simp
  · rw [← h, h0, hgo]; simp
  · rw [← h, h0, hgo]; simp

/-- 完全性：頂点 0 で終わる、始点以外が未訪問で頂点の重複がない歩道があれば
  go は true を返す。（go の健全性は要らない。必要なのはこの向きだけ。） -/
theorem go_of_walk : ∀ {v z : Fin 30} (w : G30.Walk v z), z = (0 : Fin 30) →
    ∀ (k vis : ℕ), w.length = k + 1 → w.support.Nodup →
      (∀ x ∈ w.support.tail, x ≠ (0 : Fin 30) → Nat.testBit vis x.val = false) →
      go k v.val vis = true := by
  intro v z w
  induction w with
  | nil => intro _ k vis hl _ _; simp at hl
  | @cons a b c hadj w' ih =>
      intro hz k vis hl hnd hvis
      subst hz
      rw [SimpleGraph.Walk.support_cons] at hnd hvis
      rw [List.tail_cons] at hvis
      obtain ⟨-, hnd'⟩ := List.nodup_cons.mp hnd
      rw [SimpleGraph.Walk.length_cons] at hl
      have hlk : w'.length = k := by omega
      cases k with
      | zero =>
          have hb : b = 0 := SimpleGraph.Walk.eq_of_length_eq_zero hlk
          subst hb
          exact go_zero a vis hadj
      | succ m =>
          have hb0 : b ≠ 0 := by
            intro h
            subst h
            have hnil : w' = SimpleGraph.Walk.nil :=
              SimpleGraph.Walk.isPath_iff_eq_nil.mp (SimpleGraph.Walk.IsPath.mk' hnd')
            rw [hnil] at hlk
            simp at hlk
          refine go_succ_of hadj (hvis b w'.start_mem_support hb0) ?_
          refine ih rfl m (vis ||| 2 ^ b.val) (by omega) hnd' ?_
          intro x hx hx0
          have hxb : x ≠ b := by
            have h2 := hnd'
            rw [w'.support_eq_cons] at h2
            exact fun h => (List.nodup_cons.mp h2).1 (h ▸ hx)
          have h1 : Nat.testBit vis x.val = false :=
            hvis x (List.mem_of_mem_tail hx) hx0
          have h2 : Nat.testBit (2 ^ b.val) x.val = false :=
            Nat.testBit_two_pow_of_ne (fun h => hxb (Fin.val_injective h).symm)
          rw [Nat.testBit_or, h1, h2]
          rfl

end CubicBipartite.ClassI

namespace CubicBipartite.ClassI

set_option maxRecDepth 400000

theorem go_sub1 : go 28 1 (1 ||| 2 ^ 1) = false := by
  decide +kernel

end CubicBipartite.ClassI

namespace CubicBipartite.ClassI

set_option maxRecDepth 400000

theorem go_sub27 : go 28 27 (1 ||| 2 ^ 27) = false := by
  decide +kernel

end CubicBipartite.ClassI

namespace CubicBipartite.ClassI

set_option maxRecDepth 400000

theorem go_sub28 : go 28 28 (1 ||| 2 ^ 28) = false := by
  decide +kernel

end CubicBipartite.ClassI

namespace CubicBipartite.ClassI

set_option maxRecDepth 20000

open SimpleGraph

/-- 頂点 0 を通るハミルトン閉路は無い。 -/
theorem no_hamCycle_at_zero : ¬ ∃ p : G30.Walk 0 0, p.IsHamiltonianCycle := by
  rintro ⟨p, hp⟩
  have hlen : p.length = 30 := by simpa using hp.length_eq
  cases p with
  | nil => simp at hlen
  | @cons _ u _ hadj q =>
      rw [SimpleGraph.Walk.length_cons] at hlen
      have hq : q.length = 28 + 1 := by omega
      have hnd : q.support.Nodup := by
        have h := hp.isCycle.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.tail_cons] at h
        exact h
      have hu0 : u ≠ 0 := by
        intro h
        subst h
        have hnil : q = SimpleGraph.Walk.nil :=
          SimpleGraph.Walk.isPath_iff_eq_nil.mp (SimpleGraph.Walk.IsPath.mk' hnd)
        rw [hnil] at hq
        simp at hq
      have hvis : ∀ x ∈ q.support.tail, x ≠ (0 : Fin 30) →
          Nat.testBit (1 ||| 2 ^ u.val) x.val = false := by
        intro x hx hx0
        have hxu : x ≠ u := by
          have h2 := hnd
          rw [q.support_eq_cons] at h2
          exact fun h => (List.nodup_cons.mp h2).1 (h ▸ hx)
        have hx0' : x.val ≠ 0 := fun h => hx0 (Fin.val_injective h)
        have e1 : Nat.testBit 1 x.val = false := by
          have h1 : (1 : ℕ) = 2 ^ 0 := by norm_num
          rw [h1]
          exact Nat.testBit_two_pow_of_ne (Ne.symm hx0')
        have e2 : Nat.testBit (2 ^ u.val) x.val = false :=
          Nat.testBit_two_pow_of_ne (fun h => hxu (Fin.val_injective h).symm)
        rw [Nat.testBit_or, e1, e2]
        rfl
      have hgo := go_of_walk q rfl 28 (1 ||| 2 ^ u.val) hq hnd hvis
      have hu : u = 1 ∨ u = 27 ∨ u = 28 := by
        have h : ∀ b : Fin 30, G30.Adj 0 b → (b = 1 ∨ b = 27 ∨ b = 28) := by decide
        exact h u hadj
      rcases hu with rfl | rfl | rfl
      · rw [show ((1 : Fin 30) : ℕ) = 1 from rfl, go_sub1] at hgo
        exact absurd hgo (by decide)
      · rw [show ((27 : Fin 30) : ℕ) = 27 from rfl, go_sub27] at hgo
        exact absurd hgo (by decide)
      · rw [show ((28 : Fin 30) : ℕ) = 28 from rfl, go_sub28] at hgo
        exact absurd hgo (by decide)

theorem G30_not_hamiltonian : ¬ G30.IsHamiltonian := by
  intro h
  obtain ⟨a, p, hp⟩ := h (by simp)
  exact no_hamCycle_at_zero
    ⟨p.rotate 0 (hp.mem_support 0),
      (SimpleGraph.Walk.isHamiltonianCycle_rotate (hp.mem_support 0)).mpr hp⟩

/-- 閉路の長さは 28 以下（30 はハミルトンだから不可、29 は二部性から不可）。 -/
theorem G30_cycle_length_le : ∀ (v : Fin 30) (c : G30.Walk v v), c.IsCycle → c.length ≤ 28 := by
  intro v c hc
  have h1 : c.support.tail.Nodup := hc.support_nodup
  have h2 : c.support.tail.length ≤ 30 := by simpa using h1.length_le_card
  have h3 : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have h4 : c.length % 2 = 0 := closed_walk_even c
  have h5 : c.length ≠ 30 := by
    intro h
    refine G30_not_hamiltonian (fun _ => ⟨v, c, ?_⟩)
    exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hc, by simpa using h⟩
  omega

/-- 主定理（類 I の実例を Lean で閉じたもの）。
  G30 は 30 頂点 45 辺の三価・二部・連結グラフで、長さ 28 の閉路を持ち、
  ハミルトン閉路を持たず、すべての閉路の長さは 28 以下。ゆえに周長 = 28 = 30 - 2。 -/
theorem G30_def2 :
    (∀ v : Fin 30, G30.degree v = 3) ∧
    G30.Colorable 2 ∧
    G30.Connected ∧
    (∃ c : G30.Walk 0 0, c.IsCycle ∧ c.length = 28) ∧
    (∀ (v : Fin 30) (c : G30.Walk v v), c.IsCycle → c.length ≤ 28) ∧
    ¬ G30.IsHamiltonian :=
  ⟨G30_degree, G30_colorable, G30_connected, ⟨c28, c28_isCycle, c28_length⟩,
    G30_cycle_length_le, G30_not_hamiltonian⟩

end CubicBipartite.ClassI

namespace CubicBipartite.Search

set_option maxRecDepth 20000

open SimpleGraph

/-! ### 1. ビット符号化 -/

/-- 隣接行列の符号化（n × n ビット。n * a + b 番目のビットが辺 a-b）。 -/
def adjB (AMD n a b : ℕ) : Bool := Nat.testBit AMD (n * a + b)

/-- 隣接リストの符号化：頂点 v の第 i 近傍（i < 3、昇順）が 5 ビットずつ、頂点ごとに 15 ビット。 -/
def nb (NBD v i : ℕ) : ℕ := (NBD >>> (15 * v + 5 * i)) &&& 31

/-- 深さ優先探索。gl NBD AMD n s k v vis は「v から、vis のビットが立っていない頂点を
  k 個たどり、最後に頂点 s に隣接する道があるか」を返す。 -/
def gl (NBD AMD n s : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, v, _ => adjB AMD n v s
  | (k + 1), v, vis =>
      (!Nat.testBit vis (nb NBD v 0) && gl NBD AMD n s k (nb NBD v 0) (vis ||| 2 ^ nb NBD v 0)) ||
      (!Nat.testBit vis (nb NBD v 1) && gl NBD AMD n s k (nb NBD v 1) (vis ||| 2 ^ nb NBD v 1)) ||
      (!Nat.testBit vis (nb NBD v 2) && gl NBD AMD n s k (nb NBD v 2) (vis ||| 2 ^ nb NBD v 2))

/-- gl の 1 段の展開（部分木に分けて核で評価するために使う）。 -/
theorem gl_succ_eq (NBD AMD n s k v vis : ℕ) :
    gl NBD AMD n s (k + 1) v vis =
      ((!Nat.testBit vis (nb NBD v 0) && gl NBD AMD n s k (nb NBD v 0) (vis ||| 2 ^ nb NBD v 0)) ||
       (!Nat.testBit vis (nb NBD v 1) && gl NBD AMD n s k (nb NBD v 1) (vis ||| 2 ^ nb NBD v 1)) ||
       (!Nat.testBit vis (nb NBD v 2) && gl NBD AMD n s k (nb NBD v 2) (vis ||| 2 ^ nb NBD v 2))) :=
  rfl

section

variable {n : ℕ} {G : SimpleGraph (Fin n)} {NBD AMD CMASK : ℕ}

/-! ### 2. gl の完全性（一方向） -/

theorem gl_succ_of
    (hnb : ∀ a b : Fin n, G.Adj a b →
      (b.val = nb NBD a.val 0 ∨ b.val = nb NBD a.val 1 ∨ b.val = nb NBD a.val 2))
    {s : Fin n} {k : ℕ} {v u : Fin n} {vis : ℕ} (hadj : G.Adj v u)
    (h0 : Nat.testBit vis u.val = false)
    (hgo : gl NBD AMD n s.val k u.val (vis ||| 2 ^ u.val) = true) :
    gl NBD AMD n s.val (k + 1) v.val vis = true := by
  have h := hnb v u hadj
  simp only [gl]
  rcases h with h | h | h
  · rw [← h, h0, hgo]; simp
  · rw [← h, h0, hgo]; simp
  · rw [← h, h0, hgo]; simp

/-- 完全性：頂点 s で終わり、頂点の重複がなく、始点以外が未訪問である歩道があれば
  gl は true を返す。（gl の健全性は要らない。必要なのはこの向きだけ。） -/
theorem gl_of_walk
    (hadjB : ∀ a b : Fin n, G.Adj a b → adjB AMD n a.val b.val = true)
    (hnb : ∀ a b : Fin n, G.Adj a b →
      (b.val = nb NBD a.val 0 ∨ b.val = nb NBD a.val 1 ∨ b.val = nb NBD a.val 2))
    : ∀ {v z : Fin n} (w : G.Walk v z),
    ∀ (k vis : ℕ), w.length = k + 1 → w.support.Nodup →
      (∀ x ∈ w.support.tail, x ≠ z → Nat.testBit vis x.val = false) →
      gl NBD AMD n z.val k v.val vis = true := by
  intro v z w
  induction w with
  | nil => intro k vis hl _ _; simp at hl
  | @cons a b cc hadj w' ih =>
      intro k vis hl hnd hvis
      rw [SimpleGraph.Walk.support_cons] at hnd hvis
      rw [List.tail_cons] at hvis
      obtain ⟨-, hnd'⟩ := List.nodup_cons.mp hnd
      rw [SimpleGraph.Walk.length_cons] at hl
      have hlk : w'.length = k := by omega
      cases k with
      | zero =>
          have hb : b = cc := SimpleGraph.Walk.eq_of_length_eq_zero hlk
          rw [hb] at hadj
          simpa [gl] using hadjB a cc hadj
      | succ m =>
          have hb0 : b ≠ cc := by
            intro h
            subst h
            have hnil : w' = SimpleGraph.Walk.nil :=
              SimpleGraph.Walk.isPath_iff_eq_nil.mp (SimpleGraph.Walk.IsPath.mk' hnd')
            rw [hnil] at hlk
            simp at hlk
          refine gl_succ_of hnb hadj (hvis b w'.start_mem_support hb0) ?_
          refine ih m (vis ||| 2 ^ b.val) (by omega) hnd' ?_
          intro x hx hx0
          have hxb : x ≠ b := by
            have h2 := hnd'
            rw [w'.support_eq_cons] at h2
            exact fun h => (List.nodup_cons.mp h2).1 (h ▸ hx)
          have h1 : Nat.testBit vis x.val = false :=
            hvis x (List.mem_of_mem_tail hx) hx0
          have h2 : Nat.testBit (2 ^ b.val) x.val = false :=
            Nat.testBit_two_pow_of_ne (fun h => hxb (Fin.val_injective h).symm)
          rw [Nat.testBit_or, h1, h2]
          rfl

/-! ### 3. 閉路を核の探索に渡す -/

/-- 長さ k + 2 の閉路が頂点 s を通り、vis がその閉路の頂点のうち s だけを
  立てているならば、gl NBD AMD n s (k+1) s vis は true。 -/
theorem cycle_kernel_true
    (hadjB : ∀ a b : Fin n, G.Adj a b → adjB AMD n a.val b.val = true)
    (hnb : ∀ a b : Fin n, G.Adj a b →
      (b.val = nb NBD a.val 0 ∨ b.val = nb NBD a.val 1 ∨ b.val = nb NBD a.val 2))
    {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle) (s : Fin n) (hs : s ∈ c.support)
    (vis : ℕ) (hout : ∀ x : Fin n, x ∈ c.support → x ≠ s → Nat.testBit vis x.val = false)
    (k : ℕ) (hL : c.length = k + 2) :
    gl NBD AMD n s.val (k + 1) s.val vis = true := by
  obtain ⟨d, hdc, hdl, hdm⟩ :
      ∃ d : G.Walk s s, d.IsCycle ∧ d.length = k + 2 ∧
        ∀ x : Fin n, x ∈ d.support → x ∈ c.support :=
    ⟨c.rotate s hs, hc.rotate hs, by rw [SimpleGraph.Walk.length_rotate]; exact hL,
      fun x hx => (SimpleGraph.Walk.mem_support_rotate_iff c s hs).mp hx⟩
  cases d with
  | nil => simp at hdl
  | @cons _ u _ hadj q =>
      rw [SimpleGraph.Walk.length_cons] at hdl
      have hq : q.length = k + 1 := by omega
      have hnd : q.support.Nodup := by
        have h := hdc.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.tail_cons] at h
        exact h
      have humem : u ∈ c.support := hdm u (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ q.start_mem_support)
      have hus : u ≠ s := by
        intro h
        subst h
        have hnil : q = SimpleGraph.Walk.nil :=
          SimpleGraph.Walk.isPath_iff_eq_nil.mp (SimpleGraph.Walk.IsPath.mk' hnd)
        rw [hnil] at hq
        simp at hq
      refine gl_succ_of hnb hadj (hout u humem hus) ?_
      refine gl_of_walk hadjB hnb q k (vis ||| 2 ^ u.val) hq hnd ?_
      intro x hx hxs
      have hxu : x ≠ u := by
        have h2 := hnd
        rw [q.support_eq_cons] at h2
        exact fun h => (List.nodup_cons.mp h2).1 (h ▸ hx)
      have hxc : x ∈ c.support := hdm x (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ (List.mem_of_mem_tail hx))
      have e1 : Nat.testBit vis x.val = false := hout x hxc hxs
      have e2 : Nat.testBit (2 ^ u.val) x.val = false :=
        Nat.testBit_two_pow_of_ne (fun h => hxu (Fin.val_injective h).symm)
      rw [Nat.testBit_or, e1, e2]
      rfl

/-- 核が false を返したら、その長さの閉路は s を通らない。 -/
theorem no_long_cycle_at
    (hadjB : ∀ a b : Fin n, G.Adj a b → adjB AMD n a.val b.val = true)
    (hnb : ∀ a b : Fin n, G.Adj a b →
      (b.val = nb NBD a.val 0 ∨ b.val = nb NBD a.val 1 ∨ b.val = nb NBD a.val 2))
    {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle) (s : Fin n) (hs : s ∈ c.support)
    (vis : ℕ) (hout : ∀ x : Fin n, x ∈ c.support → x ≠ s → Nat.testBit vis x.val = false)
    (k : ℕ) (hL : c.length = k + 2) (sv : ℕ) (hsv : s.val = sv)
    (hker : gl NBD AMD n sv (k + 1) sv vis = false) : False := by
  have h := cycle_kernel_true (NBD := NBD) hadjB hnb c hc s hs vis hout k hL
  rw [hsv, hker] at h
  exact absurd h (by decide)

/-! ### 4. 二部性からの偶奇 -/

theorem col_parity
    (hcol : ∀ a b : Fin n, G.Adj a b →
      (Nat.testBit CMASK a.val ≠ Nat.testBit CMASK b.val)) :
    ∀ {u v : Fin n} (w : G.Walk u v),
      (Nat.testBit CMASK u.val = Nat.testBit CMASK v.val) ↔ (w.length % 2 = 0) := by
  intro u v w
  induction w with
  | nil => simp
  | @cons a b c hadj w' ih =>
      have hne := hcol a b hadj
      rw [SimpleGraph.Walk.length_cons]
      generalize hA : Nat.testBit CMASK a.val = A at hne ⊢
      generalize hB : Nat.testBit CMASK b.val = B at hne ih
      generalize hC : Nat.testBit CMASK c.val = C at ih ⊢
      cases A <;> cases B <;> cases C <;> simp_all <;> omega

theorem closed_walk_even
    (hcol : ∀ a b : Fin n, G.Adj a b →
      (Nat.testBit CMASK a.val ≠ Nat.testBit CMASK b.val))
    {v : Fin n} (w : G.Walk v v) : w.length % 2 = 0 :=
  (col_parity hcol w).mp rfl

/-! ### 5. 閉路の長さの上限と鳩の巣 -/

theorem cycle_len_le_card {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle) : c.length ≤ n := by
  have h1 : c.support.tail.Nodup := hc.support_nodup
  have h2 : c.support.tail.length ≤ n := by simpa using h1.length_le_card
  have h3 : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  omega

/-- 閉路が Finset S のどの点も通らなければ、長さ + #S ≤ n。 -/
theorem cycle_avoid_card {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle)
    (S : Finset (Fin n)) (h : ∀ x ∈ S, x ∉ c.support) : c.length + S.card ≤ n := by
  have hnd : c.support.tail.Nodup := hc.support_nodup
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have hsub : c.support.tail.toFinset ⊆ Finset.univ \ S := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have hxs : x ∈ c.support := List.mem_of_mem_tail hx
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ x, fun hxS => h x hxS hxs⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, hlen] at hcard
  have hc2 : (Finset.univ \ S : Finset (Fin n)).card = n - S.card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

end

end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 20000

open SimpleGraph

/-- 隣接リストの符号化（頂点ごとに 15 ビット、第 i 近傍が 5 ビット）。 -/
def NBDb : ℕ := 2592904523209433297733880015068652995707725116815664207659813103211671276814301697027820793394966353780475010791995614852127396695405409

/-- 隣接行列の符号化（30 × 30 ビット）。 -/
def AMDb : ℕ := 2114210961376745513974220925201147693156609340402152461964046580420950138783158681276599465401594752715137422786749857149546114568597777572660222453656323445009851594602314877762952934087868900665039718913037033773275844403787123810973965793985247820119616849062209257474

/-- 2-彩色のマスク。 -/
def CMb : ℕ := 447392426

theorem adjBb_symm : ∀ a b : Fin 30,
    adjB AMDb 30 a.val b.val = true → adjB AMDb 30 b.val a.val = true := by decide

theorem adjBb_irrefl : ∀ a : Fin 30,
    ¬ (adjB AMDb 30 a.val a.val = true) := by decide

/-- 「類 II」のグラフ（45 辺） -/
def G30b : SimpleGraph (Fin 30) where
  Adj a b := adjB AMDb 30 a.val b.val = true
  symm := ⟨fun a b h => adjBb_symm a b h⟩
  loopless := ⟨fun a h => adjBb_irrefl a h⟩

instance decRelb : DecidableRel G30b.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB AMDb 30 a.val b.val = true))

/-! ### 辺リストとの一致（監査用） -/

/-- 「類 II」のグラフ（45 辺） の辺リスト。 -/
def edgeListb : List (Fin 30 × Fin 30) :=
  [
   (0, 1), (0, 27), (0, 28), (1, 2), (1, 4),
   (2, 3), (2, 5), (3, 4), (3, 6), (4, 5),
   (5, 6), (6, 7), (7, 8), (7, 29), (8, 9),
   (8, 19), (9, 10), (9, 26), (10, 11), (10, 28),
   (11, 12), (11, 14), (12, 13), (12, 15), (13, 14),
   (13, 16), (14, 15), (15, 16), (16, 17), (17, 18),
   (17, 29), (18, 19), (18, 27), (19, 20), (20, 21),
   (20, 23), (21, 22), (21, 24), (22, 23), (22, 25),
   (23, 24), (24, 25), (25, 26), (26, 27), (28, 29)
  ]

theorem edgeListb_card : edgeListb.length = 45 := by rfl

/-- ビット符号化されたグラフは上の辺リストそのものである。 -/
theorem adj_iff_mem_edgeListb : ∀ a b : Fin 30,
    G30b.Adj a b ↔ ((a, b) ∈ edgeListb ∨ (b, a) ∈ edgeListb) := by decide

/-! ### 三価・二部（明示の 2-彩色）・連結 -/

theorem G30b_degree : ∀ v : Fin 30, G30b.degree v = 3 := by decide

/-- 明示の 2-彩色。 -/
def col2b (v : Fin 30) : Fin 2 := if Nat.testBit CMb v.val then 1 else 0

theorem col2b_ne : ∀ a b : Fin 30, G30b.Adj a b → col2b a ≠ col2b b := by decide

theorem G30b_colorable : G30b.Colorable 2 :=
  ⟨⟨col2b, fun {a b} hab => col2b_ne a b hab⟩⟩

theorem G30b_connected : G30b.Connected := by
  have step : ∀ (u v : Fin 30), G30b.Adj u v → G30b.Reachable 0 u → G30b.Reachable 0 v :=
    fun u v h hr => hr.trans h.reachable
  have rb0 : G30b.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have rb1 : G30b.Reachable 0 1 := step 0 1 (by decide) rb0
  have rb27 : G30b.Reachable 0 27 := step 0 27 (by decide) rb0
  have rb28 : G30b.Reachable 0 28 := step 0 28 (by decide) rb0
  have rb2 : G30b.Reachable 0 2 := step 1 2 (by decide) rb1
  have rb4 : G30b.Reachable 0 4 := step 1 4 (by decide) rb1
  have rb18 : G30b.Reachable 0 18 := step 27 18 (by decide) rb27
  have rb26 : G30b.Reachable 0 26 := step 27 26 (by decide) rb27
  have rb10 : G30b.Reachable 0 10 := step 28 10 (by decide) rb28
  have rb29 : G30b.Reachable 0 29 := step 28 29 (by decide) rb28
  have rb3 : G30b.Reachable 0 3 := step 2 3 (by decide) rb2
  have rb5 : G30b.Reachable 0 5 := step 2 5 (by decide) rb2
  have rb17 : G30b.Reachable 0 17 := step 18 17 (by decide) rb18
  have rb19 : G30b.Reachable 0 19 := step 18 19 (by decide) rb18
  have rb9 : G30b.Reachable 0 9 := step 26 9 (by decide) rb26
  have rb25 : G30b.Reachable 0 25 := step 26 25 (by decide) rb26
  have rb11 : G30b.Reachable 0 11 := step 10 11 (by decide) rb10
  have rb7 : G30b.Reachable 0 7 := step 29 7 (by decide) rb29
  have rb6 : G30b.Reachable 0 6 := step 3 6 (by decide) rb3
  have rb16 : G30b.Reachable 0 16 := step 17 16 (by decide) rb17
  have rb8 : G30b.Reachable 0 8 := step 19 8 (by decide) rb19
  have rb20 : G30b.Reachable 0 20 := step 19 20 (by decide) rb19
  have rb22 : G30b.Reachable 0 22 := step 25 22 (by decide) rb25
  have rb24 : G30b.Reachable 0 24 := step 25 24 (by decide) rb25
  have rb12 : G30b.Reachable 0 12 := step 11 12 (by decide) rb11
  have rb14 : G30b.Reachable 0 14 := step 11 14 (by decide) rb11
  have rb13 : G30b.Reachable 0 13 := step 16 13 (by decide) rb16
  have rb15 : G30b.Reachable 0 15 := step 16 15 (by decide) rb16
  have rb21 : G30b.Reachable 0 21 := step 20 21 (by decide) rb20
  have rb23 : G30b.Reachable 0 23 := step 20 23 (by decide) rb20
  have key : ∀ v : Fin 30, G30b.Reachable 0 v := by
    intro v
    fin_cases v <;> assumption
  exact ⟨fun u v => (key u).symm.trans (key v)⟩

/-! ### 一般部（`Principia.CubicBipartite.Gap2`）へ渡す橋 -/

theorem adjBb_of_adj : ∀ a b : Fin 30,
    G30b.Adj a b → adjB AMDb 30 a.val b.val = true := fun _ _ h => h

theorem nbb_spec : ∀ a b : Fin 30, G30b.Adj a b →
    (b.val = nb NBDb a.val 0 ∨ b.val = nb NBDb a.val 1 ∨
      b.val = nb NBDb a.val 2) := by decide

theorem colb_ne_of_adj : ∀ a b : Fin 30, G30b.Adj a b →
    (Nat.testBit CMb a.val ≠ Nat.testBit CMb b.val) := by decide

/-! ### 長さ 28 の閉路 0-1-2-…-27-0 -/

def pb27 : G30b.Walk 27 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
def pb26 : G30b.Walk 26 0 := SimpleGraph.Walk.cons (by decide) pb27
def pb25 : G30b.Walk 25 0 := SimpleGraph.Walk.cons (by decide) pb26
def pb24 : G30b.Walk 24 0 := SimpleGraph.Walk.cons (by decide) pb25
def pb23 : G30b.Walk 23 0 := SimpleGraph.Walk.cons (by decide) pb24
def pb22 : G30b.Walk 22 0 := SimpleGraph.Walk.cons (by decide) pb23
def pb21 : G30b.Walk 21 0 := SimpleGraph.Walk.cons (by decide) pb22
def pb20 : G30b.Walk 20 0 := SimpleGraph.Walk.cons (by decide) pb21
def pb19 : G30b.Walk 19 0 := SimpleGraph.Walk.cons (by decide) pb20
def pb18 : G30b.Walk 18 0 := SimpleGraph.Walk.cons (by decide) pb19
def pb17 : G30b.Walk 17 0 := SimpleGraph.Walk.cons (by decide) pb18
def pb16 : G30b.Walk 16 0 := SimpleGraph.Walk.cons (by decide) pb17
def pb15 : G30b.Walk 15 0 := SimpleGraph.Walk.cons (by decide) pb16
def pb14 : G30b.Walk 14 0 := SimpleGraph.Walk.cons (by decide) pb15
def pb13 : G30b.Walk 13 0 := SimpleGraph.Walk.cons (by decide) pb14
def pb12 : G30b.Walk 12 0 := SimpleGraph.Walk.cons (by decide) pb13
def pb11 : G30b.Walk 11 0 := SimpleGraph.Walk.cons (by decide) pb12
def pb10 : G30b.Walk 10 0 := SimpleGraph.Walk.cons (by decide) pb11
def pb9 : G30b.Walk 9 0 := SimpleGraph.Walk.cons (by decide) pb10
def pb8 : G30b.Walk 8 0 := SimpleGraph.Walk.cons (by decide) pb9
def pb7 : G30b.Walk 7 0 := SimpleGraph.Walk.cons (by decide) pb8
def pb6 : G30b.Walk 6 0 := SimpleGraph.Walk.cons (by decide) pb7
def pb5 : G30b.Walk 5 0 := SimpleGraph.Walk.cons (by decide) pb6
def pb4 : G30b.Walk 4 0 := SimpleGraph.Walk.cons (by decide) pb5
def pb3 : G30b.Walk 3 0 := SimpleGraph.Walk.cons (by decide) pb4
def pb2 : G30b.Walk 2 0 := SimpleGraph.Walk.cons (by decide) pb3
def pb1 : G30b.Walk 1 0 := SimpleGraph.Walk.cons (by decide) pb2

theorem hb_first : G30b.Adj 0 1 := by decide

/-- 長さ 28 の閉路。 -/
def cycb : G30b.Walk 0 0 := SimpleGraph.Walk.cons hb_first pb1

theorem cycb_length : cycb.length = 28 := by rfl

theorem cycb_isCycle : cycb.IsCycle := by
  have h : (SimpleGraph.Walk.cons hb_first pb1).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, by decide⟩
    rw [SimpleGraph.Walk.isPath_def]
    decide
  exact h

end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 400000

/-- 部分木「0 → 1」（69,967 節点）。 -/
theorem glb_sub1 : gl NBDb AMDb 30 0 28 1 (1 ||| 2 ^ 1) = false := by
  decide +kernel


end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 400000

/-- 部分木「0 → 27」（22,438 節点）。 -/
theorem glb_sub27 : gl NBDb AMDb 30 0 28 27 (1 ||| 2 ^ 27) = false := by
  decide +kernel

/-- 部分木「0 → 28」（18,270 節点）。 -/
theorem glb_sub28 : gl NBDb AMDb 30 0 28 28 (1 ||| 2 ^ 28) = false := by
  decide +kernel


end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 20000

open SimpleGraph

/-- 頂点 0 からの探索木ぜんたい（3 本の部分木を貼り合わせる）。 -/
theorem glb_top : gl NBDb AMDb 30 0 (28 + 1) 0 1 = false := by
  rw [gl_succ_eq, show nb NBDb 0 0 = 1 from rfl,
    show nb NBDb 0 1 = 27 from rfl, show nb NBDb 0 2 = 28 from rfl,
    glb_sub1, glb_sub27, glb_sub28]
  all_goals rfl

theorem G30b_not_hamiltonian : ¬ G30b.IsHamiltonian := by
  intro h
  obtain ⟨a, p, hp⟩ := h (by simp)
  have hlen : p.length = 30 := by simpa using hp.length_eq
  have hz : (0 : Fin 30) ∈ p.support := hp.mem_support 0
  have key1 : ∀ x : Fin 30, x ≠ (0 : Fin 30) → Nat.testBit 1 x.val = false := by decide
  exact no_long_cycle_at adjBb_of_adj nbb_spec p hp.isCycle 0 hz 1
    (fun x _ hx => key1 x hx) 28 (by omega) 0 rfl glb_top

/-- 閉路の長さは 28 以下（30 はハミルトンだから不可、29 は二部性から不可）。 -/
theorem G30b_cycle_length_le :
    ∀ (v : Fin 30) (c : G30b.Walk v v), c.IsCycle → c.length ≤ 28 := by
  intro v c hc
  have h4 : c.length % 2 = 0 := closed_walk_even colb_ne_of_adj c
  have h2 : c.length ≤ 30 := cycle_len_le_card c hc
  have h5 : c.length ≠ 30 := by
    intro h
    refine G30b_not_hamiltonian (fun _ => ⟨v, c, ?_⟩)
    exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hc, by simpa using h⟩
  omega

/-- 主定理。G30b（「類 II」） は 30 頂点 45 辺の三価・二部・連結グラフで、
  長さ 28 の閉路を持ち、ハミルトン閉路を持たず、すべての閉路の長さは 28 以下。
  ゆえに周長 = 28 = 30 - 2、すなわち def = 2。 -/
theorem G30b_def2 :
    (∀ v : Fin 30, G30b.degree v = 3) ∧
    G30b.Colorable 2 ∧
    G30b.Connected ∧
    (∃ c : G30b.Walk 0 0, c.IsCycle ∧ c.length = 28) ∧
    (∀ (v : Fin 30) (c : G30b.Walk v v), c.IsCycle → c.length ≤ 28) ∧
    ¬ G30b.IsHamiltonian :=
  ⟨G30b_degree, G30b_colorable, G30b_connected,
    ⟨cycb, cycb_isCycle, cycb_length⟩,
    G30b_cycle_length_le, G30b_not_hamiltonian⟩

end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 20000

open SimpleGraph

/-- 隣接リストの符号化（頂点ごとに 15 ビット、第 i 近傍が 5 ビット）。 -/
def NBDc : ℕ := 2604261724876129299055739130183509662581311604367142422345984336292207219185255975627816649153679592605837004840176904071505600428667745

/-- 隣接行列の符号化（30 × 30 ビット）。 -/
def AMDc : ℕ := 2129688340218723319603647384573159352317664326553906515762977140058099705616797464163913456304569397292595956855453016715707236356803988803793060871913515664708777517735769779552047291573948104398948078049364677120476630631347025088267385811454813789759387343697616044034

/-- 2-彩色のマスク。 -/
def CMc : ℕ := 447392426

theorem adjBc_symm : ∀ a b : Fin 30,
    adjB AMDc 30 a.val b.val = true → adjB AMDc 30 b.val a.val = true := by decide

theorem adjBc_irrefl : ∀ a : Fin 30,
    ¬ (adjB AMDc 30 a.val a.val = true) := by decide

/-- 「類 III」のグラフ（45 辺） -/
def G30c : SimpleGraph (Fin 30) where
  Adj a b := adjB AMDc 30 a.val b.val = true
  symm := ⟨fun a b h => adjBc_symm a b h⟩
  loopless := ⟨fun a h => adjBc_irrefl a h⟩

instance decRelc : DecidableRel G30c.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB AMDc 30 a.val b.val = true))

/-! ### 辺リストとの一致（監査用） -/

/-- 「類 III」のグラフ（45 辺） の辺リスト。 -/
def edgeListc : List (Fin 30 × Fin 30) :=
  [
   (0, 1), (0, 27), (0, 28), (1, 2), (1, 4),
   (2, 3), (2, 5), (3, 4), (3, 6), (4, 5),
   (5, 6), (6, 7), (7, 8), (7, 29), (8, 9),
   (8, 11), (9, 10), (9, 12), (10, 11), (10, 13),
   (11, 12), (12, 13), (13, 14), (14, 15), (14, 28),
   (15, 16), (15, 18), (16, 17), (16, 19), (17, 18),
   (17, 20), (18, 19), (19, 20), (20, 21), (21, 22),
   (21, 29), (22, 23), (22, 25), (23, 24), (23, 26),
   (24, 25), (24, 27), (25, 26), (26, 27), (28, 29)
  ]

theorem edgeListc_card : edgeListc.length = 45 := by rfl

/-- ビット符号化されたグラフは上の辺リストそのものである。 -/
theorem adj_iff_mem_edgeListc : ∀ a b : Fin 30,
    G30c.Adj a b ↔ ((a, b) ∈ edgeListc ∨ (b, a) ∈ edgeListc) := by decide

/-! ### 三価・二部（明示の 2-彩色）・連結 -/

theorem G30c_degree : ∀ v : Fin 30, G30c.degree v = 3 := by decide

/-- 明示の 2-彩色。 -/
def col2c (v : Fin 30) : Fin 2 := if Nat.testBit CMc v.val then 1 else 0

theorem col2c_ne : ∀ a b : Fin 30, G30c.Adj a b → col2c a ≠ col2c b := by decide

theorem G30c_colorable : G30c.Colorable 2 :=
  ⟨⟨col2c, fun {a b} hab => col2c_ne a b hab⟩⟩

theorem G30c_connected : G30c.Connected := by
  have step : ∀ (u v : Fin 30), G30c.Adj u v → G30c.Reachable 0 u → G30c.Reachable 0 v :=
    fun u v h hr => hr.trans h.reachable
  have rc0 : G30c.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have rc1 : G30c.Reachable 0 1 := step 0 1 (by decide) rc0
  have rc27 : G30c.Reachable 0 27 := step 0 27 (by decide) rc0
  have rc28 : G30c.Reachable 0 28 := step 0 28 (by decide) rc0
  have rc2 : G30c.Reachable 0 2 := step 1 2 (by decide) rc1
  have rc4 : G30c.Reachable 0 4 := step 1 4 (by decide) rc1
  have rc24 : G30c.Reachable 0 24 := step 27 24 (by decide) rc27
  have rc26 : G30c.Reachable 0 26 := step 27 26 (by decide) rc27
  have rc14 : G30c.Reachable 0 14 := step 28 14 (by decide) rc28
  have rc29 : G30c.Reachable 0 29 := step 28 29 (by decide) rc28
  have rc3 : G30c.Reachable 0 3 := step 2 3 (by decide) rc2
  have rc5 : G30c.Reachable 0 5 := step 2 5 (by decide) rc2
  have rc23 : G30c.Reachable 0 23 := step 24 23 (by decide) rc24
  have rc25 : G30c.Reachable 0 25 := step 24 25 (by decide) rc24
  have rc13 : G30c.Reachable 0 13 := step 14 13 (by decide) rc14
  have rc15 : G30c.Reachable 0 15 := step 14 15 (by decide) rc14
  have rc7 : G30c.Reachable 0 7 := step 29 7 (by decide) rc29
  have rc21 : G30c.Reachable 0 21 := step 29 21 (by decide) rc29
  have rc6 : G30c.Reachable 0 6 := step 3 6 (by decide) rc3
  have rc22 : G30c.Reachable 0 22 := step 23 22 (by decide) rc23
  have rc10 : G30c.Reachable 0 10 := step 13 10 (by decide) rc13
  have rc12 : G30c.Reachable 0 12 := step 13 12 (by decide) rc13
  have rc16 : G30c.Reachable 0 16 := step 15 16 (by decide) rc15
  have rc18 : G30c.Reachable 0 18 := step 15 18 (by decide) rc15
  have rc8 : G30c.Reachable 0 8 := step 7 8 (by decide) rc7
  have rc20 : G30c.Reachable 0 20 := step 21 20 (by decide) rc21
  have rc9 : G30c.Reachable 0 9 := step 10 9 (by decide) rc10
  have rc11 : G30c.Reachable 0 11 := step 10 11 (by decide) rc10
  have rc17 : G30c.Reachable 0 17 := step 16 17 (by decide) rc16
  have rc19 : G30c.Reachable 0 19 := step 16 19 (by decide) rc16
  have key : ∀ v : Fin 30, G30c.Reachable 0 v := by
    intro v
    fin_cases v <;> assumption
  exact ⟨fun u v => (key u).symm.trans (key v)⟩

/-! ### 一般部（`Principia.CubicBipartite.Gap2`）へ渡す橋 -/

theorem adjBc_of_adj : ∀ a b : Fin 30,
    G30c.Adj a b → adjB AMDc 30 a.val b.val = true := fun _ _ h => h

theorem nbc_spec : ∀ a b : Fin 30, G30c.Adj a b →
    (b.val = nb NBDc a.val 0 ∨ b.val = nb NBDc a.val 1 ∨
      b.val = nb NBDc a.val 2) := by decide

theorem colc_ne_of_adj : ∀ a b : Fin 30, G30c.Adj a b →
    (Nat.testBit CMc a.val ≠ Nat.testBit CMc b.val) := by decide

/-! ### 長さ 28 の閉路 0-1-2-…-27-0 -/

def pc27 : G30c.Walk 27 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
def pc26 : G30c.Walk 26 0 := SimpleGraph.Walk.cons (by decide) pc27
def pc25 : G30c.Walk 25 0 := SimpleGraph.Walk.cons (by decide) pc26
def pc24 : G30c.Walk 24 0 := SimpleGraph.Walk.cons (by decide) pc25
def pc23 : G30c.Walk 23 0 := SimpleGraph.Walk.cons (by decide) pc24
def pc22 : G30c.Walk 22 0 := SimpleGraph.Walk.cons (by decide) pc23
def pc21 : G30c.Walk 21 0 := SimpleGraph.Walk.cons (by decide) pc22
def pc20 : G30c.Walk 20 0 := SimpleGraph.Walk.cons (by decide) pc21
def pc19 : G30c.Walk 19 0 := SimpleGraph.Walk.cons (by decide) pc20
def pc18 : G30c.Walk 18 0 := SimpleGraph.Walk.cons (by decide) pc19
def pc17 : G30c.Walk 17 0 := SimpleGraph.Walk.cons (by decide) pc18
def pc16 : G30c.Walk 16 0 := SimpleGraph.Walk.cons (by decide) pc17
def pc15 : G30c.Walk 15 0 := SimpleGraph.Walk.cons (by decide) pc16
def pc14 : G30c.Walk 14 0 := SimpleGraph.Walk.cons (by decide) pc15
def pc13 : G30c.Walk 13 0 := SimpleGraph.Walk.cons (by decide) pc14
def pc12 : G30c.Walk 12 0 := SimpleGraph.Walk.cons (by decide) pc13
def pc11 : G30c.Walk 11 0 := SimpleGraph.Walk.cons (by decide) pc12
def pc10 : G30c.Walk 10 0 := SimpleGraph.Walk.cons (by decide) pc11
def pc9 : G30c.Walk 9 0 := SimpleGraph.Walk.cons (by decide) pc10
def pc8 : G30c.Walk 8 0 := SimpleGraph.Walk.cons (by decide) pc9
def pc7 : G30c.Walk 7 0 := SimpleGraph.Walk.cons (by decide) pc8
def pc6 : G30c.Walk 6 0 := SimpleGraph.Walk.cons (by decide) pc7
def pc5 : G30c.Walk 5 0 := SimpleGraph.Walk.cons (by decide) pc6
def pc4 : G30c.Walk 4 0 := SimpleGraph.Walk.cons (by decide) pc5
def pc3 : G30c.Walk 3 0 := SimpleGraph.Walk.cons (by decide) pc4
def pc2 : G30c.Walk 2 0 := SimpleGraph.Walk.cons (by decide) pc3
def pc1 : G30c.Walk 1 0 := SimpleGraph.Walk.cons (by decide) pc2

theorem hc_first : G30c.Adj 0 1 := by decide

/-- 長さ 28 の閉路。 -/
def cycc : G30c.Walk 0 0 := SimpleGraph.Walk.cons hc_first pc1

theorem cycc_length : cycc.length = 28 := by rfl

theorem cycc_isCycle : cycc.IsCycle := by
  have h : (SimpleGraph.Walk.cons hc_first pc1).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, by decide⟩
    rw [SimpleGraph.Walk.isPath_def]
    decide
  exact h

end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 400000

/-- 部分木「0 → 1」（29,087 節点）。 -/
theorem glc_sub1 : gl NBDc AMDc 30 0 28 1 (1 ||| 2 ^ 1) = false := by
  decide +kernel


end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 400000

/-- 部分木「0 → 27」（29,087 節点）。 -/
theorem glc_sub27 : gl NBDc AMDc 30 0 28 27 (1 ||| 2 ^ 27) = false := by
  decide +kernel

/-- 部分木「0 → 28」（6,335 節点）。 -/
theorem glc_sub28 : gl NBDc AMDc 30 0 28 28 (1 ||| 2 ^ 28) = false := by
  decide +kernel


end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 20000

open SimpleGraph

/-- 頂点 0 からの探索木ぜんたい（3 本の部分木を貼り合わせる）。 -/
theorem glc_top : gl NBDc AMDc 30 0 (28 + 1) 0 1 = false := by
  rw [gl_succ_eq, show nb NBDc 0 0 = 1 from rfl,
    show nb NBDc 0 1 = 27 from rfl, show nb NBDc 0 2 = 28 from rfl,
    glc_sub1, glc_sub27, glc_sub28]
  all_goals rfl

theorem G30c_not_hamiltonian : ¬ G30c.IsHamiltonian := by
  intro h
  obtain ⟨a, p, hp⟩ := h (by simp)
  have hlen : p.length = 30 := by simpa using hp.length_eq
  have hz : (0 : Fin 30) ∈ p.support := hp.mem_support 0
  have key1 : ∀ x : Fin 30, x ≠ (0 : Fin 30) → Nat.testBit 1 x.val = false := by decide
  exact no_long_cycle_at adjBc_of_adj nbc_spec p hp.isCycle 0 hz 1
    (fun x _ hx => key1 x hx) 28 (by omega) 0 rfl glc_top

/-- 閉路の長さは 28 以下（30 はハミルトンだから不可、29 は二部性から不可）。 -/
theorem G30c_cycle_length_le :
    ∀ (v : Fin 30) (c : G30c.Walk v v), c.IsCycle → c.length ≤ 28 := by
  intro v c hc
  have h4 : c.length % 2 = 0 := closed_walk_even colc_ne_of_adj c
  have h2 : c.length ≤ 30 := cycle_len_le_card c hc
  have h5 : c.length ≠ 30 := by
    intro h
    refine G30c_not_hamiltonian (fun _ => ⟨v, c, ?_⟩)
    exact SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hc, by simpa using h⟩
  omega

/-- 主定理。G30c（「類 III」） は 30 頂点 45 辺の三価・二部・連結グラフで、
  長さ 28 の閉路を持ち、ハミルトン閉路を持たず、すべての閉路の長さは 28 以下。
  ゆえに周長 = 28 = 30 - 2、すなわち def = 2。 -/
theorem G30c_def2 :
    (∀ v : Fin 30, G30c.degree v = 3) ∧
    G30c.Colorable 2 ∧
    G30c.Connected ∧
    (∃ c : G30c.Walk 0 0, c.IsCycle ∧ c.length = 28) ∧
    (∀ (v : Fin 30) (c : G30c.Walk v v), c.IsCycle → c.length ≤ 28) ∧
    ¬ G30c.IsHamiltonian :=
  ⟨G30c_degree, G30c_colorable, G30c_connected,
    ⟨cycc, cycc_isCycle, cycc_length⟩,
    G30c_cycle_length_le, G30c_not_hamiltonian⟩

end CubicBipartite.Search

namespace CubicBipartite.Search

set_option maxRecDepth 400000

open SimpleGraph

/-- 隣接リストの符号化（頂点ごとに 15 ビット、第 i 近傍が 5 ビット）。 -/
def NBDt : ℕ := 1049259718880592065020849457239484326143243441811099183397416776723643165099209699019176232

/-- 隣接行列の符号化（20 × 20 ビット）。 -/
def AMDt : ℕ := 282433849765627824673241963646396592448068827413772773090489442870068887175388240991148010442989094660244701945316524800

/-- 2-彩色のマスク。 -/
def CMt : ℕ := 130944

theorem adjBt_symm : ∀ a b : Fin 20,
    adjB AMDt 20 a.val b.val = true → adjB AMDt 20 b.val a.val = true := by decide

theorem adjBt_irrefl : ∀ a : Fin 20,
    ¬ (adjB AMDt 20 a.val a.val = true) := by decide

/--  20 頂点グラフ（30 辺・三価・二部・連結・非ハミルトン） -/
def G20 : SimpleGraph (Fin 20) where
  Adj a b := adjB AMDt 20 a.val b.val = true
  symm := ⟨fun a b h => adjBt_symm a b h⟩
  loopless := ⟨fun a h => adjBt_irrefl a h⟩

instance decRelt : DecidableRel G20.Adj :=
  fun a b => inferInstanceAs (Decidable (adjB AMDt 20 a.val b.val = true))

/-! ### 辺リストとの一致（監査用） -/

/--  20 頂点グラフ（30 辺・三価・二部・連結・非ハミルトン） の辺リスト。 -/
def edgeListt : List (Fin 20 × Fin 20) :=
  [
   (0, 8), (0, 9), (0, 14), (1, 7), (1, 10),
   (1, 11), (2, 8), (2, 10), (2, 11), (3, 8),
   (3, 10), (3, 11), (4, 7), (4, 12), (4, 13),
   (5, 9), (5, 12), (5, 13), (6, 9), (6, 12),
   (6, 13), (7, 17), (14, 18), (14, 19), (15, 17),
   (15, 18), (15, 19), (16, 17), (16, 18), (16, 19)
  ]

theorem edgeListt_card : edgeListt.length = 30 := by rfl

/-- ビット符号化されたグラフは上の辺リストそのものである。 -/
theorem adj_iff_mem_edgeListt : ∀ a b : Fin 20,
    G20.Adj a b ↔ ((a, b) ∈ edgeListt ∨ (b, a) ∈ edgeListt) := by decide

/-! ### 三価・二部（明示の 2-彩色）・連結 -/

theorem G20_degree : ∀ v : Fin 20, G20.degree v = 3 := by decide

/-- 明示の 2-彩色。 -/
def col2t (v : Fin 20) : Fin 2 := if Nat.testBit CMt v.val then 1 else 0

theorem col2t_ne : ∀ a b : Fin 20, G20.Adj a b → col2t a ≠ col2t b := by decide

theorem G20_colorable : G20.Colorable 2 :=
  ⟨⟨col2t, fun {a b} hab => col2t_ne a b hab⟩⟩

theorem G20_connected : G20.Connected := by
  have step : ∀ (u v : Fin 20), G20.Adj u v → G20.Reachable 0 u → G20.Reachable 0 v :=
    fun u v h hr => hr.trans h.reachable
  have rt0 : G20.Reachable 0 0 := SimpleGraph.Reachable.refl 0
  have rt8 : G20.Reachable 0 8 := step 0 8 (by decide) rt0
  have rt9 : G20.Reachable 0 9 := step 0 9 (by decide) rt0
  have rt14 : G20.Reachable 0 14 := step 0 14 (by decide) rt0
  have rt2 : G20.Reachable 0 2 := step 8 2 (by decide) rt8
  have rt3 : G20.Reachable 0 3 := step 8 3 (by decide) rt8
  have rt5 : G20.Reachable 0 5 := step 9 5 (by decide) rt9
  have rt6 : G20.Reachable 0 6 := step 9 6 (by decide) rt9
  have rt18 : G20.Reachable 0 18 := step 14 18 (by decide) rt14
  have rt19 : G20.Reachable 0 19 := step 14 19 (by decide) rt14
  have rt10 : G20.Reachable 0 10 := step 2 10 (by decide) rt2
  have rt11 : G20.Reachable 0 11 := step 2 11 (by decide) rt2
  have rt12 : G20.Reachable 0 12 := step 5 12 (by decide) rt5
  have rt13 : G20.Reachable 0 13 := step 5 13 (by decide) rt5
  have rt15 : G20.Reachable 0 15 := step 18 15 (by decide) rt18
  have rt16 : G20.Reachable 0 16 := step 18 16 (by decide) rt18
  have rt1 : G20.Reachable 0 1 := step 10 1 (by decide) rt10
  have rt4 : G20.Reachable 0 4 := step 12 4 (by decide) rt12
  have rt17 : G20.Reachable 0 17 := step 15 17 (by decide) rt15
  have rt7 : G20.Reachable 0 7 := step 1 7 (by decide) rt1
  have key : ∀ v : Fin 20, G20.Reachable 0 v := by
    intro v
    fin_cases v <;> assumption
  exact ⟨fun u v => (key u).symm.trans (key v)⟩

/-! ### 一般部（`Principia.CubicBipartite.Gap2`）へ渡す橋 -/

theorem adjBt_of_adj : ∀ a b : Fin 20,
    G20.Adj a b → adjB AMDt 20 a.val b.val = true := fun _ _ h => h

theorem nbt_spec : ∀ a b : Fin 20, G20.Adj a b →
    (b.val = nb NBDt a.val 0 ∨ b.val = nb NBDt a.val 1 ∨
      b.val = nb NBDt a.val 2) := by decide

theorem colt_ne_of_adj : ∀ a b : Fin 20, G20.Adj a b →
    (Nat.testBit CMt a.val ≠ Nat.testBit CMt b.val) := by decide

/-! ### 長さ 14 の閉路 0-8-2-10-3-11-1-7-4-12-5-13-6-9-0 -/

def pt13 : G20.Walk 9 0 := SimpleGraph.Walk.cons (by decide) SimpleGraph.Walk.nil
def pt12 : G20.Walk 6 0 := SimpleGraph.Walk.cons (by decide) pt13
def pt11 : G20.Walk 13 0 := SimpleGraph.Walk.cons (by decide) pt12
def pt10 : G20.Walk 5 0 := SimpleGraph.Walk.cons (by decide) pt11
def pt9 : G20.Walk 12 0 := SimpleGraph.Walk.cons (by decide) pt10
def pt8 : G20.Walk 4 0 := SimpleGraph.Walk.cons (by decide) pt9
def pt7 : G20.Walk 7 0 := SimpleGraph.Walk.cons (by decide) pt8
def pt6 : G20.Walk 1 0 := SimpleGraph.Walk.cons (by decide) pt7
def pt5 : G20.Walk 11 0 := SimpleGraph.Walk.cons (by decide) pt6
def pt4 : G20.Walk 3 0 := SimpleGraph.Walk.cons (by decide) pt5
def pt3 : G20.Walk 10 0 := SimpleGraph.Walk.cons (by decide) pt4
def pt2 : G20.Walk 2 0 := SimpleGraph.Walk.cons (by decide) pt3
def pt1 : G20.Walk 8 0 := SimpleGraph.Walk.cons (by decide) pt2

theorem ht_first : G20.Adj 0 8 := by decide

/-- 長さ 14 の閉路。 -/
def cyct : G20.Walk 0 0 := SimpleGraph.Walk.cons ht_first pt1

theorem cyct_length : cyct.length = 14 := by rfl

theorem cyct_isCycle : cyct.IsCycle := by
  have h : (SimpleGraph.Walk.cons ht_first pt1).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, by decide⟩
    rw [SimpleGraph.Walk.isPath_def]
    decide
  exact h

/-! ### 長さ 16・18・20 の閉路が無いこと（核での探索）

長さ 16 以上の閉路は 20 - 5 = 15 < 16 頂点には収まらないから、
S = {0, 7, 14, 15, 16} のどれかを必ず通る（鳩の巣・cycle_avoid_card）。
S の最小の添字で場合分けし、s_i の探索では s_1..s_{i-1} を訪問済みにしておく。 -/

/-- 頂点 0 を通る長さ 16 の閉路は無い（1,606 節点）。 -/
theorem gl20_s0_14 : gl NBDt AMDt 20 0 (14 + 1) 0 1 = false := by
  decide +kernel

/-- 頂点 0 を通る長さ 18 の閉路は無い（1,606 節点）。 -/
theorem gl20_s0_16 : gl NBDt AMDt 20 0 (16 + 1) 0 1 = false := by
  decide +kernel

/-- 頂点 0 を通る長さ 20 の閉路は無い（1,606 節点）。 -/
theorem gl20_s0_18 : gl NBDt AMDt 20 0 (18 + 1) 0 1 = false := by
  decide +kernel

/-- 頂点 7 を通る長さ 16 の閉路は無い（94 節点）。 -/
theorem gl20_s7_14 : gl NBDt AMDt 20 7 (14 + 1) 7 129 = false := by
  decide +kernel

/-- 頂点 7 を通る長さ 18 の閉路は無い（94 節点）。 -/
theorem gl20_s7_16 : gl NBDt AMDt 20 7 (16 + 1) 7 129 = false := by
  decide +kernel

/-- 頂点 7 を通る長さ 20 の閉路は無い（94 節点）。 -/
theorem gl20_s7_18 : gl NBDt AMDt 20 7 (18 + 1) 7 129 = false := by
  decide +kernel

/-- 頂点 14 を通る長さ 16 の閉路は無い（31 節点）。 -/
theorem gl20_s14_14 : gl NBDt AMDt 20 14 (14 + 1) 14 16513 = false := by
  decide +kernel

/-- 頂点 14 を通る長さ 18 の閉路は無い（31 節点）。 -/
theorem gl20_s14_16 : gl NBDt AMDt 20 14 (16 + 1) 14 16513 = false := by
  decide +kernel

/-- 頂点 14 を通る長さ 20 の閉路は無い（31 節点）。 -/
theorem gl20_s14_18 : gl NBDt AMDt 20 14 (18 + 1) 14 16513 = false := by
  decide +kernel

/-- 頂点 15 を通る長さ 16 の閉路は無い（13 節点）。 -/
theorem gl20_s15_14 : gl NBDt AMDt 20 15 (14 + 1) 15 49281 = false := by
  decide +kernel

/-- 頂点 15 を通る長さ 18 の閉路は無い（13 節点）。 -/
theorem gl20_s15_16 : gl NBDt AMDt 20 15 (16 + 1) 15 49281 = false := by
  decide +kernel

/-- 頂点 15 を通る長さ 20 の閉路は無い（13 節点）。 -/
theorem gl20_s15_18 : gl NBDt AMDt 20 15 (18 + 1) 15 49281 = false := by
  decide +kernel

/-- 頂点 16 を通る長さ 16 の閉路は無い（4 節点）。 -/
theorem gl20_s16_14 : gl NBDt AMDt 20 16 (14 + 1) 16 114817 = false := by
  decide +kernel

/-- 頂点 16 を通る長さ 18 の閉路は無い（4 節点）。 -/
theorem gl20_s16_16 : gl NBDt AMDt 20 16 (16 + 1) 16 114817 = false := by
  decide +kernel

/-- 頂点 16 を通る長さ 20 の閉路は無い（4 節点）。 -/
theorem gl20_s16_18 : gl NBDt AMDt 20 16 (18 + 1) 16 114817 = false := by
  decide +kernel

theorem key20_0 : ∀ x : Fin 20, x ≠ (0 : Fin 20) →
    Nat.testBit 1 x.val = false := by decide

theorem key20_7 : ∀ x : Fin 20, x ≠ (0 : Fin 20) → x ≠ (7 : Fin 20) →
    Nat.testBit 129 x.val = false := by decide

theorem key20_14 : ∀ x : Fin 20, x ≠ (0 : Fin 20) → x ≠ (7 : Fin 20) → x ≠ (14 : Fin 20) →
    Nat.testBit 16513 x.val = false := by decide

theorem key20_15 : ∀ x : Fin 20, x ≠ (0 : Fin 20) → x ≠ (7 : Fin 20) → x ≠ (14 : Fin 20) → x ≠ (15 : Fin 20) →
    Nat.testBit 49281 x.val = false := by decide

theorem key20_16 : ∀ x : Fin 20, x ≠ (0 : Fin 20) → x ≠ (7 : Fin 20) → x ≠ (14 : Fin 20) → x ≠ (15 : Fin 20) → x ≠ (16 : Fin 20) →
    Nat.testBit 114817 x.val = false := by decide

/-- すべての閉路の長さは 14 以下（周長 = 14、すなわち def = 6）。 -/
theorem G20_circ_le_14 :
    ∀ (v : Fin 20) (c : G20.Walk v v), c.IsCycle → c.length ≤ 14 := by
  intro v c hc
  have hev : c.length % 2 = 0 := closed_walk_even colt_ne_of_adj c
  have hle : c.length ≤ 20 := cycle_len_le_card c hc
  by_contra hgt
  have hL : c.length = 16 ∨ c.length = 18 ∨ c.length = 20 := by omega
  by_cases h0 : (0 : Fin 20) ∈ c.support
  · have hout : ∀ x : Fin 20, x ∈ c.support → x ≠ (0 : Fin 20) →
        Nat.testBit 1 x.val = false :=
      fun x _ hxs => key20_0 x hxs
    rcases hL with h | h | h
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (0 : Fin 20) h0 1 hout
        14 (by omega) 0 rfl gl20_s0_14
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (0 : Fin 20) h0 1 hout
        16 (by omega) 0 rfl gl20_s0_16
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (0 : Fin 20) h0 1 hout
        18 (by omega) 0 rfl gl20_s0_18
  by_cases h7 : (7 : Fin 20) ∈ c.support
  · have hout : ∀ x : Fin 20, x ∈ c.support → x ≠ (7 : Fin 20) →
        Nat.testBit 129 x.val = false :=
      fun x hx hxs => key20_7 x (fun e => h0 (e ▸ hx)) hxs
    rcases hL with h | h | h
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (7 : Fin 20) h7 129 hout
        14 (by omega) 7 rfl gl20_s7_14
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (7 : Fin 20) h7 129 hout
        16 (by omega) 7 rfl gl20_s7_16
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (7 : Fin 20) h7 129 hout
        18 (by omega) 7 rfl gl20_s7_18
  by_cases h14 : (14 : Fin 20) ∈ c.support
  · have hout : ∀ x : Fin 20, x ∈ c.support → x ≠ (14 : Fin 20) →
        Nat.testBit 16513 x.val = false :=
      fun x hx hxs => key20_14 x (fun e => h0 (e ▸ hx)) (fun e => h7 (e ▸ hx)) hxs
    rcases hL with h | h | h
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (14 : Fin 20) h14 16513 hout
        14 (by omega) 14 rfl gl20_s14_14
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (14 : Fin 20) h14 16513 hout
        16 (by omega) 14 rfl gl20_s14_16
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (14 : Fin 20) h14 16513 hout
        18 (by omega) 14 rfl gl20_s14_18
  by_cases h15 : (15 : Fin 20) ∈ c.support
  · have hout : ∀ x : Fin 20, x ∈ c.support → x ≠ (15 : Fin 20) →
        Nat.testBit 49281 x.val = false :=
      fun x hx hxs => key20_15 x (fun e => h0 (e ▸ hx)) (fun e => h7 (e ▸ hx)) (fun e => h14 (e ▸ hx)) hxs
    rcases hL with h | h | h
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (15 : Fin 20) h15 49281 hout
        14 (by omega) 15 rfl gl20_s15_14
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (15 : Fin 20) h15 49281 hout
        16 (by omega) 15 rfl gl20_s15_16
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (15 : Fin 20) h15 49281 hout
        18 (by omega) 15 rfl gl20_s15_18
  by_cases h16 : (16 : Fin 20) ∈ c.support
  · have hout : ∀ x : Fin 20, x ∈ c.support → x ≠ (16 : Fin 20) →
        Nat.testBit 114817 x.val = false :=
      fun x hx hxs => key20_16 x (fun e => h0 (e ▸ hx)) (fun e => h7 (e ▸ hx)) (fun e => h14 (e ▸ hx)) (fun e => h15 (e ▸ hx)) hxs
    rcases hL with h | h | h
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (16 : Fin 20) h16 114817 hout
        14 (by omega) 16 rfl gl20_s16_14
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (16 : Fin 20) h16 114817 hout
        16 (by omega) 16 rfl gl20_s16_16
    · exact no_long_cycle_at adjBt_of_adj nbt_spec c hc (16 : Fin 20) h16 114817 hout
        18 (by omega) 16 rfl gl20_s16_18
  have hcard : ({0, 7, 14, 15, 16} : Finset (Fin 20)).card = 5 := by decide
  have hav := cycle_avoid_card c hc ({0, 7, 14, 15, 16} : Finset (Fin 20)) (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption)
  rw [hcard] at hav
  omega

theorem G20_not_hamiltonian : ¬ G20.IsHamiltonian := by
  intro h
  obtain ⟨a, p, hp⟩ := h (by simp)
  have hlen : p.length = 20 := by simpa using hp.length_eq
  have h14 := G20_circ_le_14 a p hp.isCycle
  omega

/-- 主定理（ 20 頂点の例を Lean で閉じたもの）。
  G20 は 20 頂点 30 辺の三価・二部・連結グラフで、長さ 14 の閉路を持ち、
  ハミルトン閉路を持たず、すべての閉路の長さは 14 以下。
  ゆえに周長 = 14 = 20 - 6、すなわち def = 6。 -/
theorem G20_def6 :
    (∀ v : Fin 20, G20.degree v = 3) ∧
    G20.Colorable 2 ∧
    G20.Connected ∧
    (∃ c : G20.Walk 0 0, c.IsCycle ∧ c.length = 14) ∧
    (∀ (v : Fin 20) (c : G20.Walk v v), c.IsCycle → c.length ≤ 14) ∧
    ¬ G20.IsHamiltonian :=
  ⟨G20_degree, G20_colorable, G20_connected, ⟨cyct, cyct_isCycle, cyct_length⟩,
    G20_circ_le_14, G20_not_hamiltonian⟩

end CubicBipartite.Search
