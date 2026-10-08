import Principia.GeneralizedPetersen.Base
import Principia.GeneralizedPetersen.Blocks
import Principia.GeneralizedPetersen.Small
import Principia.GeneralizedPetersen.FreeAction
import Principia.GeneralizedPetersen.Count
import Principia.GeneralizedPetersen.Descent

-- 段階 1：一般の GP n k と回転
#print axioms GeneralizedPetersen.Base.GP_adj
#print axioms GeneralizedPetersen.Base.GP_adj_outer
#print axioms GeneralizedPetersen.Base.GP_adj_inner
#print axioms GeneralizedPetersen.Base.GP_adj_spoke
#print axioms GeneralizedPetersen.Base.GP_adj_shift
#print axioms GeneralizedPetersen.Base.GP_adj_rot_pow
#print axioms GeneralizedPetersen.Base.rotIso
#print axioms GeneralizedPetersen.Base.rot_pow_card
#print axioms GeneralizedPetersen.Base.rot_pow_free
#print axioms GeneralizedPetersen.Base.rotIso_hamiltonian
#print axioms GeneralizedPetersen.Base.GPfin_iso

-- 段階 2：商グラフと巻き数
#print axioms GeneralizedPetersen.Base.quotMap_adj
#print axioms GeneralizedPetersen.Base.quotHom
#print axioms GeneralizedPetersen.Base.quotMap_rot
#print axioms GeneralizedPetersen.Base.quotMap_rot_pow_self
#print axioms GeneralizedPetersen.Base.quotMap_eq_iff
#print axioms GeneralizedPetersen.Base.lift_connected_iff
#print axioms GeneralizedPetersen.Base.lift_connected_three

-- 段階 3：局所恒等式・総変位・窓の勘定
#print axioms GeneralizedPetersen.Base.Flow.W_sub_one
#print axioms GeneralizedPetersen.Base.Flow.W_const
#print axioms GeneralizedPetersen.Base.Flow.sum_W
#print axioms GeneralizedPetersen.Base.Flow.winding
#print axioms GeneralizedPetersen.Base.Win.Z_spec
#print axioms GeneralizedPetersen.Base.Win.p_eq_q
#print axioms GeneralizedPetersen.Base.Win.sum_Z_eq
#print axioms GeneralizedPetersen.Base.Win.sum_Z_eq'
#print axioms GeneralizedPetersen.Base.Win.x_eq_p
#print axioms GeneralizedPetersen.Base.Win.sp_abs_le_one
#print axioms GeneralizedPetersen.Base.Win.no_gap_dist_three
#print axioms GeneralizedPetersen.Base.Win.no_three_consecutive
#print axioms GeneralizedPetersen.Base.Win.x_eq_pairs
#print axioms GeneralizedPetersen.Base.Win.pairs_eq_q

-- 段階 4：符号
#print axioms GeneralizedPetersen.Base.sign_eq_orbCount
#print axioms GeneralizedPetersen.Base.sign_eq_neg_one_of_odd_orbCount
#print axioms GeneralizedPetersen.Base.sign_eq_neg_one_of_full_cycle
#print axioms GeneralizedPetersen.Base.not_full_cycle_of_odd_orbCount
#print axioms GeneralizedPetersen.Base.next_theta_not_full_cycle
#print axioms GeneralizedPetersen.Base.orbCount_of_no_fixed

-- 公理化が空でないこと
#print axioms GeneralizedPetersen.Base.winEx
#print axioms GeneralizedPetersen.Base.winEx_counts
#print axioms GeneralizedPetersen.Base.winEx_x_p

-- 段階 5-1：ブロック構造（クラスタ分解なし）
#print axioms GeneralizedPetersen.Blocks.q_split
#print axioms GeneralizedPetersen.Blocks.n1_eq_ends
#print axioms GeneralizedPetersen.Blocks.succ_mem_Ends
#print axioms GeneralizedPetersen.Blocks.image_Doms
#print axioms GeneralizedPetersen.Blocks.ends_has_pred
#print axioms GeneralizedPetersen.Blocks.chain_two
#print axioms GeneralizedPetersen.Blocks.odd_pair
#print axioms GeneralizedPetersen.Blocks.block
#print axioms GeneralizedPetersen.Blocks.block_sep
#print axioms GeneralizedPetersen.Blocks.Z_eq_one_iff
#print axioms GeneralizedPetersen.Blocks.outer_zero_iff

-- 段階 5-2：糸の数 c と符号
#print axioms GeneralizedPetersen.Blocks.thrHom_eq_iff
#print axioms GeneralizedPetersen.Blocks.thr_card_odd
#print axioms GeneralizedPetersen.Blocks.n2_eq_zero
#print axioms GeneralizedPetersen.Blocks.q_eq_two_n1
#print axioms GeneralizedPetersen.Blocks.quot_two_factor_not_cycle

-- 段階 5-3：被覆と歩道の持ち上げ
#print axioms GeneralizedPetersen.Blocks.IsCovering.eq_of_adj
#print axioms GeneralizedPetersen.Blocks.exists_lift
#print axioms GeneralizedPetersen.Blocks.lift_unique
#print axioms GeneralizedPetersen.Blocks.GP_neighbor
#print axioms GeneralizedPetersen.Blocks.exists_nbr_lift
#print axioms GeneralizedPetersen.Blocks.quot_inj_on_nbrs
#print axioms GeneralizedPetersen.Blocks.GP_isCovering
#print axioms GeneralizedPetersen.Blocks.GP3_covering_conditions

-- 段階 5-4：巻き数
#print axioms GeneralizedPetersen.Blocks.quot_map_support
#print axioms GeneralizedPetersen.Blocks.quotMap_surjective
#print axioms GeneralizedPetersen.Blocks.exists_lift_winding
#print axioms GeneralizedPetersen.Blocks.lift_unique_GP

-- 段階 5-5：`next₃` の構成
#print axioms GeneralizedPetersen.Blocks.retP_ex
#print axioms GeneralizedPetersen.Blocks.ret_mem
#print axioms GeneralizedPetersen.Blocks.ret_sameThread
#print axioms GeneralizedPetersen.Blocks.ret_inj
#print axioms GeneralizedPetersen.Blocks.next3
#print axioms GeneralizedPetersen.Blocks.card_Gi_type
#print axioms GeneralizedPetersen.Blocks.next3_theta_not_full_cycle

-- 段階 5-6：`3 ∤ d` なら `next₃` は全体を回す巡回（橋の仮定なし）
#print axioms GeneralizedPetersen.Blocks.next3_pow_val
#print axioms GeneralizedPetersen.Blocks.reach
#print axioms GeneralizedPetersen.Blocks.sameThread_of_not_dvd
#print axioms GeneralizedPetersen.Blocks.next3_ne_self
#print axioms GeneralizedPetersen.Blocks.next3_isCycle
#print axioms GeneralizedPetersen.Blocks.sign_next3
#print axioms GeneralizedPetersen.Blocks.next3_theta_not_full_cycle_of_not_dvd

/-
  `Count` の確認：`#print axioms`（`sorry` が無いこと・`native_decide` を使っていないこと）。
-/
open GeneralizedPetersen.Count

-- (α) の土台
#print axioms GeneralizedPetersen.Count.subtypePerm_pow_val
#print axioms GeneralizedPetersen.Count.sign_split
#print axioms GeneralizedPetersen.Count.sign_transitive
#print axioms GeneralizedPetersen.Count.card_subtype_add
#print axioms GeneralizedPetersen.Count.sign_split3
-- (α)
#print axioms GeneralizedPetersen.Count.castHom3_eq_iff
#print axioms GeneralizedPetersen.Count.thr3_next3
#print axioms GeneralizedPetersen.Count.thr3_trans
#print axioms GeneralizedPetersen.Count.sign_next3_dvd
#print axioms GeneralizedPetersen.Count.sign_next3_all
#print axioms GeneralizedPetersen.Count.next3_theta_not_full_cycle_general
-- (β)
#print axioms GeneralizedPetersen.Count.exists_shift
#print axioms GeneralizedPetersen.Count.exists_loop
#print axioms GeneralizedPetersen.Count.loop_covers
#print axioms GeneralizedPetersen.Count.exists_loop_covering
-- (γ)
#print axioms GeneralizedPetersen.Count.prev_mem
#print axioms GeneralizedPetersen.Count.prev_inj
#print axioms GeneralizedPetersen.Count.theta_pow_val
#print axioms GeneralizedPetersen.Count.reach_prev
#print axioms GeneralizedPetersen.Count.two_le_card_Gi
#print axioms GeneralizedPetersen.Count.theta_ne_self
#print axioms GeneralizedPetersen.Count.theta_isCycle
#print axioms GeneralizedPetersen.Count.next3_theta_of_Win
-- 数え上げと総合
#print axioms GeneralizedPetersen.Count.mem_HamEdges
#print axioms GeneralizedPetersen.Count.toFinset_map_eq
#print axioms GeneralizedPetersen.Count.rotE_iterate
#print axioms GeneralizedPetersen.Count.rotE_mem
#print axioms GeneralizedPetersen.Count.rotE_pow_card
#print axioms GeneralizedPetersen.Count.gp_dvd_numHC
#print axioms GeneralizedPetersen.Count.gp3_dvd_hc

/-
  確認：`#print axioms`（`sorry` が無いこと・`native_decide` を使っていないこと）。
-/
open GeneralizedPetersen.Descent

-- (δ1) 閉路の局所構造
#print axioms GeneralizedPetersen.Descent.cycle_local
#print axioms GeneralizedPetersen.Descent.cycle_local'
#print axioms GeneralizedPetersen.Descent.symm_notMem_darts
-- (δ3) 代数
#print axioms GeneralizedPetersen.Descent.TwoFactor.p_eq_q
#print axioms GeneralizedPetersen.Descent.TwoFactor.abs_winding_le
#print axioms GeneralizedPetersen.Descent.TwoFactor.even_winding
#print axioms GeneralizedPetersen.Descent.TwoFactor.winding_cases
#print axioms GeneralizedPetersen.Descent.TwoFactor.exists_win
-- (δ2) 上側・`p ≥ 1`・`hall3`
#print axioms GeneralizedPetersen.Descent.hamTF
#print axioms GeneralizedPetersen.Descent.support_subset_of_closed'
#print axioms GeneralizedPetersen.Descent.exists_oW_zero
#print axioms GeneralizedPetersen.Descent.exists_iW_zero_thread
-- (δ2) 降下
#print axioms GeneralizedPetersen.Descent.TwoFactor.descend
#print axioms GeneralizedPetersen.Descent.TwoFactor.descend_W_eq
-- 総合（三つの残りへの還元）
#print axioms GeneralizedPetersen.Descent.win_of_dartInv
#print axioms GeneralizedPetersen.Descent.winBridge_of
#print axioms GeneralizedPetersen.Descent.gp3_dvd_hc'
-- 残り 1：ダーツの不変性
#print axioms GeneralizedPetersen.Descent.fwd_or_bwd
#print axioms GeneralizedPetersen.Descent.preserves_of_odd_order
#print axioms GeneralizedPetersen.Descent.dartBridge
-- 残り 2：巻き数 ≠ 0
#print axioms GeneralizedPetersen.Descent.closed_walk_darts
#print axioms GeneralizedPetersen.Descent.WS_eq_flow
#print axioms GeneralizedPetersen.Descent.windingBridge
-- 残り 3：一本の閉路
#print axioms GeneralizedPetersen.Descent.nxt_reach
#print axioms GeneralizedPetersen.Descent.IsHamiltonianCycle.reverse'
#print axioms GeneralizedPetersen.Descent.trace
#print axioms GeneralizedPetersen.Descent.reach_of_nxt
#print axioms GeneralizedPetersen.Descent.cycleBridge
-- 一般 `n`（無条件）
#print axioms GeneralizedPetersen.Descent.gp3_dvd_hc_odd
#print axioms GeneralizedPetersen.Descent.gp3_dvd_hc_odd'

-- 段階 1（実例の個数）
#print axioms GeneralizedPetersen.Small.GP7_hc_card
#print axioms GeneralizedPetersen.Small.GP9_hc_card
#print axioms GeneralizedPetersen.Small.GP11_hc_card
#print axioms GeneralizedPetersen.Small.GP13_hc_card
#print axioms GeneralizedPetersen.Small.GP15_hc_card
-- 一般部（数え上げの健全性・完全性・重複なし）
#print axioms GeneralizedPetersen.Small.card_hamRep
#print axioms GeneralizedPetersen.Small.mem_ext
#print axioms GeneralizedPetersen.Small.nodup_ext
#print axioms GeneralizedPetersen.Small.cnt_eq_length
#print axioms GeneralizedPetersen.Small.hamRep_iff
#print axioms GeneralizedPetersen.Small.hamRep_covers
-- 監査（グラフが GP(n,3) そのものであること）
#print axioms GeneralizedPetersen.Small.adjB7_iff_GP
#print axioms GeneralizedPetersen.Small.adjB15_iff_GP
#print axioms GeneralizedPetersen.Small.GP15_degree
-- 核計算
#print axioms GeneralizedPetersen.Small.num15
#print axioms GeneralizedPetersen.Small.s15_1_2
#print axioms GeneralizedPetersen.Small.s15_15_27
-- 段階 2（代数）
#print axioms GeneralizedPetersen.Small.card_dvd_of_stabilizer_bot
#print axioms GeneralizedPetersen.Small.card_dvd_of_free
#print axioms GeneralizedPetersen.Small.card_dvd_of_free_cyclic
#print axioms GeneralizedPetersen.Small.card_dvd_of_perm_free

-- 主定理（回転の自由作用から n | #HC）
#print axioms GeneralizedPetersen.FreeAction.GP7_dvd_rot
#print axioms GeneralizedPetersen.FreeAction.GP9_dvd_rot
#print axioms GeneralizedPetersen.FreeAction.GP11_dvd_rot
#print axioms GeneralizedPetersen.FreeAction.GP13_dvd_rot
#print axioms GeneralizedPetersen.FreeAction.GP15_dvd_rot
-- 割り切れの部分だけ（段階 1 の値を使わない）
#print axioms GeneralizedPetersen.FreeAction.gp7_dvd_by_rotation
#print axioms GeneralizedPetersen.FreeAction.gp13_dvd_by_rotation
#print axioms GeneralizedPetersen.FreeAction.gp15_dvd_by_rotation
-- 一般部（段階 2 への橋）
#print axioms GeneralizedPetersen.FreeAction.val_pow
#print axioms GeneralizedPetersen.FreeAction.dvd_card_of_iterate_free
#print axioms GeneralizedPetersen.FreeAction.dvd_card_of_family_free
-- 段階 1 との接続（明示的なリストが HamRep の全体であること）
#print axioms GeneralizedPetersen.FreeAction.L7_eq
#print axioms GeneralizedPetersen.FreeAction.L13_eq
#print axioms GeneralizedPetersen.FreeAction.L15_eq
-- ρ の作用の (i)〜(iv)
#print axioms GeneralizedPetersen.FreeAction.ractMem15
#print axioms GeneralizedPetersen.FreeAction.ractComp15
#print axioms GeneralizedPetersen.FreeAction.ractOrd15
#print axioms GeneralizedPetersen.FreeAction.ractEmask15
#print axioms GeneralizedPetersen.FreeAction.ractFree15
-- 表現の取り方によらない形
#print axioms GeneralizedPetersen.FreeAction.GP7_dvd_any
#print axioms GeneralizedPetersen.FreeAction.GP13_dvd_any
#print axioms GeneralizedPetersen.FreeAction.GP15_dvd_any
-- 段階 3（`Small`で届かなかった n = 13, 15）
#print axioms GeneralizedPetersen.FreeAction.no_rho_fixed13'
#print axioms GeneralizedPetersen.FreeAction.no_rho_fixed15'
