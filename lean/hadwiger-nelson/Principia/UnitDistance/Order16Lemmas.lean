import Mathlib
import Principia.UnitDistance.Order16Core
/-
  **平行四辺形の段**（紙の草稿）を Lean に載せる。素の三辺測量では
  閉じない 4 類（添字 108・161・340・352）のために要る。

  置きたい点 `v` の隣接点 `x, y` が置かれ、`x, y` の共通隣接点 `u`（`≠ v`）も置かれていて
  `|ux| = |uy| = |vx| = |vy| = 1` なら、`u` と `v` はどちらも `xy` の垂直二等分線上にある
  2 交点で、中点について対称である。`u ≠ v` から `p_u ≠ p_v`、よって

      p_v = p_x + p_y − p_u        （加減算だけ・丸め無し・符号分岐無し）

  三辺測量の段は `√(1 − d²/4)/√(d²)` を掛けるので錨が近いと区間が発散するが、
  この段は幅が `w_x + w_y + w_u` にしかならない。

  **`p_u ≠ p_v` を使う**ので、この段を含む証明書が閉じるのは
  「異なる頂点は異なる点」を課した側（`Realiz`）だけである。`UnitDistance.Order11.Edges` の
  単射性なしの版はこの 4 類については主張しない（§ 成果メモ）。

  sorry 0・native_decide 不使用。核は `UnitDistance.Order11.trilat_core` をそのまま使う。
-/

namespace UnitDistance.Order16

open UnitDistance.Order11 (Ivl Sem addI subI mulI sc st0 isEdge upd Holds St d2I killOK triStep)

/-! ## 1. 辺の条件＋点が相異なること -/

/-- 辺は距離 1・**非辺は制約なし**・16 点は互いに異なる点。 -/
def EdgesI (E : List (ℕ × ℕ)) (x y : ℕ → ℝ) : Prop :=
  UnitDistance.Order11.Edges E x y ∧
    ∀ u w : ℕ, u < 16 → w < 16 → u ≠ w → ¬ (x u = x w ∧ y u = y w)

/-- 正規化（回転と平行移動）は「点が相異なること」を保つ。 -/
lemma normalizeI (E : List (ℕ × ℕ)) (a b : ℕ) (hab : isEdge E a b = true) (x y : ℕ → ℝ)
    (h : EdgesI E x y) :
    ∃ X Y : ℕ → ℝ, EdgesI E X Y ∧ X a = 0 ∧ Y a = 0 ∧ X b = 1 ∧ Y b = 0 := by
  obtain ⟨hE, hinj⟩ := h
  have hnorm : (x b - x a)^2 + (y b - y a)^2 = 1 := by
    have hh := UnitDistance.Order11.edge_eq hE hab
    linear_combination hh
  refine ⟨fun n => (x n - x a) * (x b - x a) + (y n - y a) * (y b - y a),
          fun n => -((x n - x a) * (y b - y a)) + (y n - y a) * (x b - x a),
          ⟨?_, ?_⟩, by ring, by ring, by linear_combination hnorm, by ring⟩
  · intro e he
    have hh := hE e he
    linear_combination ((x b - x a)^2 + (y b - y a)^2) * hh + hnorm
  · intro u w hu hw hne hc
    obtain ⟨hc1, hc2⟩ := hc
    simp only at hc1 hc2
    refine hinj u w hu hw hne ⟨?_, ?_⟩
    · linear_combination (x b - x a) * hc1 - (y b - y a) * hc2 - (x u - x w) * hnorm
    · linear_combination (y b - y a) * hc1 + (x b - x a) * hc2 - (y u - y w) * hnorm

/-! ## 2. 平行四辺形の核 -/

/-- **平行四辺形の核**：`x, y` の双方から単位距離にある 2 点 `u ≠ v` は
  中点について対称——`p_v = p_x + p_y − p_u`。 -/
lemma par_core {xa ya xb yb xu yu xv yv : ℝ}
    (hD : (xb - xa)^2 + (yb - ya)^2 ≠ 0)
    (h1 : (xu - xa)^2 + (yu - ya)^2 = 1) (h2 : (xu - xb)^2 + (yu - yb)^2 = 1)
    (h3 : (xv - xa)^2 + (yv - ya)^2 = 1) (h4 : (xv - xb)^2 + (yv - yb)^2 = 1)
    (hne : ¬ (xu = xv ∧ yu = yv)) :
    xv = xa + xb - xu ∧ yv = ya + yb - yu := by
  have hlin1 : (xu - (xa + xb)/2) * (xb - xa) + (yu - (ya + yb)/2) * (yb - ya) = 0 := by
    linear_combination (h1 - h2) / 2
  have hlin2 : (xv - (xa + xb)/2) * (xb - xa) + (yv - (ya + yb)/2) * (yb - ya) = 0 := by
    linear_combination (h3 - h4) / 2
  obtain ⟨s, hs1, hs2⟩ := UnitDistance.Order11.trilat_core hD hlin1
  obtain ⟨t, ht1, ht2⟩ := UnitDistance.Order11.trilat_core hD hlin2
  have hn1 : (xu - (xa + xb)/2)^2 + (yu - (ya + yb)/2)^2
      = 1 - ((xb - xa)^2 + (yb - ya)^2)/4 := by linear_combination (h1 + h2) / 2
  have hn2 : (xv - (xa + xb)/2)^2 + (yv - (ya + yb)/2)^2
      = 1 - ((xb - xa)^2 + (yb - ya)^2)/4 := by linear_combination (h3 + h4) / 2
  rw [hs1, hs2] at hn1
  rw [ht1, ht2] at hn2
  have key : (s - t) * (s + t) * ((xb - xa)^2 + (yb - ya)^2) = 0 := by
    linear_combination hn1 - hn2
  have hst : (s - t) * (s + t) = 0 := by
    rcases mul_eq_zero.mp key with hk | hk
    · exact hk
    · exact absurd hk hD
  rcases mul_eq_zero.mp hst with hk | hk
  · exfalso
    have hse : s = t := by linarith
    refine hne ⟨?_, ?_⟩
    · linear_combination hs1 - ht1 - (yb - ya) * hse
    · linear_combination hs2 - ht2 + (xb - xa) * hse
  · have hse : s = -t := by linarith
    refine ⟨?_, ?_⟩
    · linear_combination hs1 + ht1 - (yb - ya) * hse
    · linear_combination hs2 + ht2 + (xb - xa) * hse

/-! ## 3. 平行四辺形の段を足した証明書の木 -/

inductive TrP where
  | kill (u w : ℕ) : TrP
  | split (ll lu : ℤ) (tp tm : TrP) : TrP
  | bisx (v : ℕ) (mid : ℤ) (t1 t2 : TrP) : TrP
  | bisy (v : ℕ) (mid : ℤ) (t1 t2 : TrP) : TrP
  | free (u p : ℕ) (t : TrP) : TrP
  /-- `v` を `x, y` の共通隣接点 `u` の対称点に置く（`p_v = p_x + p_y − p_u`）。 -/
  | par (v x y u : ℕ) (t : TrP) : TrP

def chkP (E : List (ℕ × ℕ)) : TrP → List (ℕ × ℕ × ℕ) → St → Bool
  | .kill u w, _, σ =>
      match σ u, σ w with
      | some A, some B => isEdge E u w && killOK A B
      | _, _ => false
  | .split ll lu tp tm, pl, σ =>
      match pl with
      | [] => false
      | (v, a, b) :: pl' =>
          match σ a, σ b with
          | some A, some B =>
              isEdge E v a && isEdge E v b && (triStep ll lu A B).1 &&
                chkP E tp pl' (upd σ v (triStep ll lu A B).2.1) &&
                chkP E tm pl' (upd σ v (triStep ll lu A B).2.2)
          | _, _ => false
  | .bisx v mid t1 t2, pl, σ =>
      match σ v with
      | some A =>
          chkP E t1 pl (upd σ v (⟨A.1.lo, mid⟩, A.2)) &&
            chkP E t2 pl (upd σ v (⟨mid, A.1.hi⟩, A.2))
      | none => false
  | .bisy v mid t1 t2, pl, σ =>
      match σ v with
      | some A =>
          chkP E t1 pl (upd σ v (A.1, ⟨A.2.lo, mid⟩)) &&
            chkP E t2 pl (upd σ v (A.1, ⟨mid, A.2.hi⟩))
      | none => false
  | .free u p t, pl, σ =>
      match σ p with
      | some A => isEdge E u p &&
          chkP E t pl (upd σ u (addI A.1 ⟨-sc, sc⟩, addI A.2 ⟨-sc, sc⟩))
      | none => false
  | .par v x y u t, pl, σ =>
      match σ x, σ y, σ u with
      | some A, some B, some U =>
          isEdge E v x && isEdge E v y && isEdge E u x && isEdge E u y &&
            decide (u ≠ v ∧ x ≠ y ∧ u < 16 ∧ v < 16 ∧ x < 16 ∧ y < 16) &&
            chkP E t pl (upd σ v (subI (addI A.1 B.1) U.1, subI (addI A.2 B.2) U.2))
      | _, _, _ => false

/-- **検査器の健全性**（平行四辺形の段つき）。 -/
theorem chkP_sound (E : List (ℕ × ℕ)) (x y : ℕ → ℝ) (hEI : EdgesI E x y) :
    ∀ (t : TrP) (pl : List (ℕ × ℕ × ℕ)) (σ : St), Holds σ x y → chkP E t pl σ = true → False := by
  obtain ⟨hE, hinj⟩ := hEI
  intro t
  induction t with
  | kill u w =>
      intro pl σ hσ h
      rcases hu : σ u with _ | A
      · simp [chkP, hu] at h
      · rcases hw : σ w with _ | B
        · simp [chkP, hu, hw] at h
        · simp only [chkP, hu, hw, Bool.and_eq_true] at h
          obtain ⟨he, hk⟩ := h
          obtain ⟨hA1, hA2⟩ := hσ u A hu
          obtain ⟨hB1, hB2⟩ := hσ w B hw
          exact UnitDistance.Order11.killOK_false hA1 hA2 hB1 hB2 (UnitDistance.Order11.edge_eq hE he) hk
  | split ll lu tp tm ihp ihm =>
      intro pl σ hσ h
      rcases pl with _ | ⟨q, pl'⟩
      · simp [chkP] at h
      · obtain ⟨v, a, b⟩ := q
        rcases ha : σ a with _ | A
        · simp [chkP, ha] at h
        · rcases hb : σ b with _ | B
          · simp [chkP, ha, hb] at h
          · simp only [chkP, ha, hb, Bool.and_eq_true] at h
            obtain ⟨⟨⟨⟨he1, he2⟩, hok⟩, hp⟩, hm⟩ := h
            obtain ⟨hA1, hA2⟩ := hσ a A ha
            obtain ⟨hB1, hB2⟩ := hσ b B hb
            rcases UnitDistance.Order11.triStep_sound hA1 hA2 hB1 hB2 (UnitDistance.Order11.edge_eq hE he1)
              (UnitDistance.Order11.edge_eq hE he2) hok with hbox | hbox
            · exact ihp pl' _ (UnitDistance.Order11.holds_upd hσ hbox) hp
            · exact ihm pl' _ (UnitDistance.Order11.holds_upd hσ hbox) hm
  | bisx v mid t1 t2 ih1 ih2 =>
      intro pl σ hσ h
      rcases hv : σ v with _ | A
      · simp [chkP, hv] at h
      · simp only [chkP, hv, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨hA1, hA2⟩ := hσ v A hv
        rcases le_or_gt ((sc:ℝ) * x v) ((mid:ℤ) : ℝ) with hc | hc
        · refine ih1 pl _ (UnitDistance.Order11.holds_upd hσ ?_) h1
          exact ⟨⟨hA1.1, hc⟩, hA2⟩
        · refine ih2 pl _ (UnitDistance.Order11.holds_upd hσ ?_) h2
          exact ⟨⟨hc.le, hA1.2⟩, hA2⟩
  | bisy v mid t1 t2 ih1 ih2 =>
      intro pl σ hσ h
      rcases hv : σ v with _ | A
      · simp [chkP, hv] at h
      · simp only [chkP, hv, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨hA1, hA2⟩ := hσ v A hv
        rcases le_or_gt ((sc:ℝ) * y v) ((mid:ℤ) : ℝ) with hc | hc
        · refine ih1 pl _ (UnitDistance.Order11.holds_upd hσ ?_) h1
          exact ⟨hA1, ⟨hA2.1, hc⟩⟩
        · refine ih2 pl _ (UnitDistance.Order11.holds_upd hσ ?_) h2
          exact ⟨hA1, ⟨hc.le, hA2.2⟩⟩
  | free u p t ih =>
      intro pl σ hσ h
      rcases hp : σ p with _ | A
      · simp [chkP, hp] at h
      · simp only [chkP, hp, Bool.and_eq_true] at h
        obtain ⟨he, hr⟩ := h
        obtain ⟨hA1, hA2⟩ := hσ p A hp
        have hed := UnitDistance.Order11.edge_eq hE he
        obtain ⟨hx1, hx2⟩ := UnitDistance.Order11.coord_le_one hed
        have hed' : (y u - y p)^2 + (x u - x p)^2 = 1 := by linear_combination hed
        obtain ⟨hy1, hy2⟩ := UnitDistance.Order11.coord_le_one hed'
        have hdx : Sem ⟨-sc, sc⟩ (x u - x p) := by
          refine ⟨?_, ?_⟩
          · have h7 : (sc:ℝ) * (-1) ≤ (sc:ℝ) * (x u - x p) :=
              mul_le_mul_of_nonneg_left hx1 (le_of_lt UnitDistance.Order11.scR_pos)
            simp only [Int.cast_neg]
            linarith
          · have h7 : (sc:ℝ) * (x u - x p) ≤ (sc:ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hx2 (le_of_lt UnitDistance.Order11.scR_pos)
            linarith
        have hdy : Sem ⟨-sc, sc⟩ (y u - y p) := by
          refine ⟨?_, ?_⟩
          · have h7 : (sc:ℝ) * (-1) ≤ (sc:ℝ) * (y u - y p) :=
              mul_le_mul_of_nonneg_left hy1 (le_of_lt UnitDistance.Order11.scR_pos)
            simp only [Int.cast_neg]
            linarith
          · have h7 : (sc:ℝ) * (y u - y p) ≤ (sc:ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hy2 (le_of_lt UnitDistance.Order11.scR_pos)
            linarith
        have hbx := UnitDistance.Order11.addI_sound hA1 hdx
        have hby := UnitDistance.Order11.addI_sound hA2 hdy
        have ex : x p + (x u - x p) = x u := by ring
        have ey : y p + (y u - y p) = y u := by ring
        rw [ex] at hbx
        rw [ey] at hby
        refine ih pl _ (UnitDistance.Order11.holds_upd hσ ?_) hr
        exact ⟨hbx, hby⟩
  | par v xx yy u t ih =>
      intro pl σ hσ h
      rcases hx : σ xx with _ | A
      · simp [chkP, hx] at h
      · rcases hy : σ yy with _ | B
        · simp [chkP, hx, hy] at h
        · rcases hu : σ u with _ | U
          · simp [chkP, hx, hy, hu] at h
          · simp only [chkP, hx, hy, hu, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨he1, he2⟩, he3⟩, he4⟩, hcond⟩, hr⟩ := h
            obtain ⟨hne, hxy, hub, hvb, hxb, hyb⟩ := hcond
            obtain ⟨hA1, hA2⟩ := hσ xx A hx
            obtain ⟨hB1, hB2⟩ := hσ yy B hy
            obtain ⟨hU1, hU2⟩ := hσ u U hu
            -- `x ≠ y` は別の頂点だから、単射性から `p_x ≠ p_y`、よって `d ≠ 0`
            have hDne : (x yy - x xx)^2 + (y yy - y xx)^2 ≠ 0 := by
              intro h0
              have p1 : (0:ℝ) ≤ (x yy - x xx)^2 := sq_nonneg _
              have p2 : (0:ℝ) ≤ (y yy - y xx)^2 := sq_nonneg _
              have e1 : (x yy - x xx)^2 = 0 := by linarith
              have e2 : (y yy - y xx)^2 = 0 := by linarith
              have f1 : x yy - x xx = 0 := by simpa using sq_eq_zero_iff.mp e1
              have f2 : y yy - y xx = 0 := by simpa using sq_eq_zero_iff.mp e2
              exact hinj xx yy hxb hyb hxy ⟨by linarith, by linarith⟩
            have hne' : ¬ (x u = x v ∧ y u = y v) := hinj u v hub hvb hne
            obtain ⟨hvx, hvy⟩ := par_core hDne
              (UnitDistance.Order11.edge_eq hE he3) (UnitDistance.Order11.edge_eq hE he4)
              (UnitDistance.Order11.edge_eq hE he1) (UnitDistance.Order11.edge_eq hE he2) hne'
            have hbx : Sem (subI (addI A.1 B.1) U.1) (x v) := by
              have := UnitDistance.Order11.subI_sound (UnitDistance.Order11.addI_sound hA1 hB1) hU1
              rw [show x xx + x yy - x u = x v from hvx.symm] at this
              exact this
            have hby : Sem (subI (addI A.2 B.2) U.2) (y v) := by
              have := UnitDistance.Order11.subI_sound (UnitDistance.Order11.addI_sound hA2 hB2) hU2
              rw [show y xx + y yy - y u = y v from hvy.symm] at this
              exact this
            refine ih pl _ (UnitDistance.Order11.holds_upd hσ ?_) hr
            exact ⟨hbx, hby⟩

/-! ## 4. 候補を閉じる道具（平行四辺形の段つき） -/

/-- `Realiz` から `EdgesI` へ（`Fin 16` の単射性を座標の相異に落とす）。 -/
lemma realiz_edgesI {E : List (ℕ × ℕ)} {p : Fin 16 → ℝ × ℝ} (h : Realiz E p) :
    EdgesI E (fun n => (p (emb n)).1) (fun n => (p (emb n)).2) := by
  refine ⟨h.1, ?_⟩
  intro u w hu hw hne hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only at hc1 hc2
  have hpq : p (emb u) = p (emb w) := by
    have e1 : (p (emb u)).1 = (p (emb w)).1 := hc1
    have e2 : (p (emb u)).2 = (p (emb w)).2 := hc2
    rcases hpu : p (emb u) with ⟨s1, s2⟩
    rcases hpw : p (emb w) with ⟨t1, t2⟩
    rw [hpu, hpw] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  have he : emb u = emb w := h.2 hpq
  apply hne
  have : u % 16 = w % 16 := by
    simpa [emb, Fin.mk.injEq] using he
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw] at this

/-- **平行四辺形の段を含む証明書で候補を閉じる**（`Realiz` の側だけ）。 -/
theorem close_realizP (E : List (ℕ × ℕ)) (a b : ℕ) (hab : isEdge E a b = true) (t : TrP)
    (pl : List (ℕ × ℕ × ℕ)) (hchk : chkP E t pl (st0 a b) = true) :
    ∀ p : Fin 16 → ℝ × ℝ, ¬ Realiz E p := by
  intro p hp
  obtain ⟨X, Y, hXY, h1, h2, h3, h4⟩ := normalizeI E a b hab _ _ (realiz_edgesI hp)
  exact chkP_sound E X Y hXY t pl (st0 a b) (UnitDistance.Order11.holds_st0 h1 h2 h3 h4) hchk

end UnitDistance.Order16

#print axioms UnitDistance.Order16.par_core
#print axioms UnitDistance.Order16.normalizeI
#print axioms UnitDistance.Order16.chkP_sound
#print axioms UnitDistance.Order16.close_realizP
#print axioms UnitDistance.Order16.realiz_edgesI
