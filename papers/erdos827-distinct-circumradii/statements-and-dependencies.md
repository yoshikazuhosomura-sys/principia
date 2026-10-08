# 言明の一覧・証明の依存関係・Lean の対応表（エルデシュ #827・`n₄ = 7`）

「証明の消化」に使う見取り図。**この一覧は論文（`paper.tex`）の付属であり、
論文の本文には入っていない。**各行は「何を言っているか」「何に依るか」「Lean の名前」「等級」の四つ。

等級：**［Lean］**＝Lean 4 で閉じた（`sorry` 0・`native_decide` 不使用・`#print axioms` が
`propext`／`Classical.choice`／`Quot.sound` の部分集合）／**［紙］**＝証明はあるが Lean 未了／
**［計算］**＝計算で確かめた（外に出す主張にしない）／**［既知］**＝文献にある・言い換え。

---

## 0. 一番上の言明

| 言明 | 内容 | 依存 | Lean | 等級 |
|---|---|---|---|---|
| **T1** | `n₄ = 7` | L1 ∧ U1 | `DistinctCircumradii.sInf_isGood_eq_seven` | ［Lean］ |

`sInf_isGood_eq_seven` は `le_antisymm` で **U1**（上界）と **L1**（下界）を合わせたもの。
`{N : ℕ | IsGood N}` が最小元を持つことは `isGood_mono` と `isGood_nine` による。

```
T1  n₄ = 7
├── L1  7 ≤ n₄                        （§4）
│   └── L2 cfg6 は一般の位置で悪い
└── U1  n₄ ≤ 7                        （§5–§7）
    └── U2 悪い 6 点は八面体型
        ├── C1 censusComplete（35 類の全数性）   （§6）
        ├── R1 restUnrealizable（34 類の非実現） （§7）
        └── K0 censusK0 を支える 6 点は八面体型  （§7.5）
```

---

## 1. 下界（§4）

| # | 言明 | 依存 | Lean | 等級 |
|---|---|---|---|---|
| L3 | `cfg6 = (0,0),(1,2),(1,3),(3,3),(3,4),(4,6)` は一般の位置 | 整数の算術 | `cfg6_generalPosition`（`cfg6_ne`・`cfg6_ncol_*`・`cfg6_ncyc_*`） | ［Lean］ |
| L4 | `cfg6` の 15 個の 4 点部分集合はどれも外接半径を繰り返す | 整数の算術・補題 2.2 | `cfg6_repeats` | ［Lean］ |
| L2 | `¬ IsGood 6` | L3 ∧ L4 | `not_isGood_six` | ［Lean］ |
| L1 | `IsGood N → 7 ≤ N`、ゆえに `7 ≤ sInf` | L2 ∧ `isGood_mono` | `seven_le_of_isGood`、`seven_le_sInf_isGood_and_sInf_isGood_le_nine.1` | ［Lean］ |
| L5 | `{±a,±b,±c}` は `E(a,b,c) = 0` のとき八面体型で悪い | 紙（§4） | — | ［紙］ |
| L6 | `cfg6` は `{±(1,0),±(1,1),±(2,3)}` の平行移動で `E = 0`、共通半径² `25/2` | 有理数の算術 | — | ［計算・厳密］ |
| L7 | [S] の下界 `(0,0),(0,7),(2,6),(4,3),(6,2),(6,9)` も同じ族（`E = 0`） | 有理数の算術 | — | ［計算・厳密］ |

**L1 が下界の全部である。**L5〜L7 は説明であって、主定理には要らない。

---

## 2. 上界の外枠（§5）

| # | 言明 | 依存 | Lean | 等級 |
|---|---|---|---|---|
| P1 | 一般の位置で `等半径 ⟺ Ψ = 0` | `circum_diff_factor`（`ring`）・非共円 | `eqRadSq_iff_psi` | ［Lean］ |
| P2 | 三点非共線なら外接半径の二乗は一意 | 一次代数 | `circumRadiusSq_unique` | ［Lean］ |
| P3 | 四点から等距離の点があれば四点共円 | `linear_combination` | `concyclic4_of_common_center` | ［Lean］ |
| P4 | **外心の和** `o + o′ = u + v`（辺 `uv` を共有し等半径・非共円） | P2 ∧ P3 | `centre_sum`、`star_sum` | ［Lean］ |
| S1 | **八面体型 ⟹ 中心対称** | P4 を四回 | `central_six_of_octahedral` | ［Lean］ |
| S2 | 7 点の六点部分集合が全部中心対称にはなれない（3 点非共線の下で） | 平行移動と鳩の巣 | `not_all_erase_central` | ［Lean］ |
| S3 | 「悪い 6 点は必ず中心対称」⟹ `IsGood 7` | S2 | `isGood_seven_of_central_six` | ［Lean］ |
| S4 | 「悪い 6 点は必ず八面体型」⟹ `IsGood 7` | S1 ∧ S3 | `isGood_seven_of_octahedral_six`、`sInf_isGood_le_seven_of_octahedral_six` | ［Lean］ |
| U3 | `IsGood 9`（＝`n₄ ≤ 9`。数え上げ `C(9,4) > C(9,2)·3`） | (C) の型・非共円 | `isGood_nine` | ［Lean］／［既知］（[MaRo15]） |

**U1 = S4 を U2 に当てたもの。**

---

## 3. census（§6）

| # | 言明 | 依存 | Lean | 等級 |
|---|---|---|---|---|
| D1 | 枡 90・`cellList`・`cellNum` が逆写像 | `decide` | `cellList_length`、`cellNum_spec`、`cellOf_distinct` | ［Lean］ |
| D2 | どの配置も一つのマスクを担う（`Carries`） | 古典論理 | `exists_carries` | ［Lean］ |
| D3 | `Carries ⟹ Supports`、`S₆` の作用と両立 | — | `supports_of_carries`、`carries_comp`、`supports_comp`、`permMask_comp` | ［Lean］ |
| G1 | 一般の位置は並べ替えで不変 | — | `generalPosition_comp` | ［Lean］ |
| G2 | 「4 点集合が外接半径を繰り返す」は並べ替えで不変 | `fourDistinct_swap0/1/2` | `repeats_of_ne` | ［Lean］ |
| N1 | 規則 (T)：4 点集合の証人は 1／相補的 2／6 | Johnson の円定理・`par_or_perp_of_psi` | `par_perp_identity`、`par_or_perp_of_psi`、`fourth_eqRad_of_three` | ［Lean］ |
| N2 | 規則 (B)：apex 対を止めると証人の辺は分割（推移律） | 補題 2.4 の平行性 | `psi_trans`、`eqRadSq_trans` | ［Lean］ |
| N3 | 規則 (C)：辺を止めると証人の apex 対はマッチング | 二円・非共円 | `not_two_eqRad`、`center_pair` | ［Lean］ |
| N4 | **45 ブロックの表の健全性**（(T)(B)(C)＋悪さ） | N1 ∧ N2 ∧ N3 | `consistent_of_carries`、`TablesSound` | ［Lean］ |
| N5 | **格子の規則の健全性**（(K1)(D1)(D2)(D3)） | 補題 6.1（双対の完全性）・`chiF_of_cert` | `lattice_sound`、`LatticeSound` | ［Lean］ |
| N6 | **関係空間の規則の健全性**（(C4)(C6)） | P4・(T) | `relation_sound`、`RelationSound` | ［Lean］ |
| N7 | **閉包 (D4) の健全性** | 定義から | `ClosureSound` | ［Lean］ |
| N8 | 置換で節点を写す段の健全性 | G1 ∧ G2 ∧ D3 | `settles_symmT` | ［Lean］ |
| N9 | **検査器の健全性**：`check` が受理する transcript は節点を settle する | N4〜N8 | `check_sound`（`Tr`・`Settles`） | ［Lean］ |
| **C1** | **`censusComplete`**：悪い 6 点の担うマスクは 35 類の `S₆` 軌道に入る | N9 ＋ 1,820 本の部分木定理 | `censusComplete`（`DistinctCircumradiiCensusTree373`） | ［Lean］ |

補題 6.1（「強制 ⟺ 格子への所属」の逆向き）は**紙**で、Lean に入っているのは
使う向き（所属 ⟹ 強制）だけである。逆向きは探索の設計に効いたが、健全性には要らない。

探索の実測（［計算］）：部分木 **1,820** 本・節点 **204,890**・残り **0**。
独立な再実装（別の分岐順）でも 35 類・余分 0（55,730 節点）。

---

## 4. 34 類の非実現（§7）

`censusRest` の 34 個の各マスク `maskKₙ` について `∀ p, GeneralPosition p → ¬ Carries p maskKₙ`。
名前は `QX.not_carries_kN`（`X` は下の表のモジュールの名前空間）。**34 本すべて［Lean］。**

| 類 | 道 | 中身 | 名前空間 / モジュール |
|---|---|---|---|
| K2, K7, K8, K9, K10, K12, K15, K18, K19, K30 | 座標（次数 ≤ 6） | 根基の証書 `Σ hᵢΨᵢ = ∏ fⱼ` | `QU0` / `LinkedUnrealizable` |
| K28 | 座標（次数 8・余因子 205 項） | 同上 | `QR2` / `LinkedRadical2` |
| K14 | 座標（次数 8・432 項） | 同上 | `QR3` / `LinkedRadical3` |
| K6 | 座標（次数 8・562 項） | 同上 | `QR4` / `LinkedRadical4` |
| K13 | 座標（次数 8） | 同上 | `QR5` / `LinkedRadical5` |
| K3 | 座標（次数 8） | 同上 | `QR6` / `LinkedRadical6` |
| K4 | 座標（次数 8） | 同上 | `QR7` / `LinkedRadical7` |
| K5 | 座標（次数 8） | 同上 | `QR8` / `LinkedRadical8` |
| K22 | 偶閉路 | 外心の交代和（6 項）＝六点の一次関係 | `QR10` / `LinkedRadical10` |
| K29 | 奇閉路 | 外心が頂点に釘づけ＝半径 0 | `QR11` / `LinkedRadical11` |
| K32 | 奇閉路 | 同上 | `QR12` / `LinkedRadical12` |
| K1 | 向き（`m = 2`） | 単因子 `1⁹,2,2,4,4`・直角 2 つ ⟹ 2 点一致 | `QU1` / `LinkedUnrealizableOrientation` |
| K11, K33 | 向き | 直角の層 | `QU2` / `…Orientation2` |
| K25, K26 | 向き（`m = 4`） | 捩れの層 | `QU3` / `…Orientation3` |
| K16, K17 | 向き | 捩れの層 | `QU4` / `…Orientation4` |
| K23 | 向き（LP） | 位数 2 の共円形式 × 2 乗距離の非負結合 | `QU5` / `…Orientation5` |
| K20 | 向き（ずらした代表） | `Re W_G = 0` が次数 2・枡 7 本 | `QU6` / `…Orientation6` |
| K21 | 向き | 11 本の恒等式・生成元 11／支持 68 | `QU7` / `…Orientation7` |
| K31 | 枝の列挙 | 単因子 `(2,2,2,2,22)`・352 枝 | `QB10` / `LinkedBranches10` |
| K34 | 枝の列挙 | 同上 | `QB11` / `LinkedBranches11` |
| K27 | 枝の列挙 | 単因子 `(2,2,2,2,26)`・416 枝 | `QB12` / `LinkedBranches12` |
| K24 | 枝の列挙 | 単因子 `(2,2,2,6)＋自由 1`・48 枝・死ぬ 32 枝は全部 `p₀p₄p₅` 共線 | `QB13` / `LinkedBranches13` |

| # | 言明 | 依存 | Lean | 等級 |
|---|---|---|---|---|
| **R1** | `restUnrealizable`：34 類のどれも `Carries` されない | 上の 34 本 | `DistinctCircumradii.restUnrealizable`（`Final.lean`） | ［Lean］ |
| K0 | `censusK0` を支える 6 点は八面体型（枡 18 のうち 7 枚を使う） | P1 ∧ N2 | `octahedralSix_of_supports_K0` | ［Lean］ |
| **U2** | 悪い 6 点は八面体型 | C1 ∧ R1 ∧ K0 | `octahedral_hypothesis_carries`、`octahedralHypothesis` | ［Lean］ |

補助（［計算・厳密］、主定理には要らない）：次数 4 と 6 に証書が**無い**類があることの全走査／
陰性対照 `K0` は次数 4・6・8 のどれでも証書 0 本／独立な厳密な道が二本ある類は 11・一本が 23／
強制される一次関係を持つ類はちょうど 18 で、座標の道が落とした 18 類と一致。

---

## 5. `Supports` と `Carries`（§7.5）

| # | 言明 | 等級 |
|---|---|---|
| X1 | `Supports` 形の非実現 ⟹ `Carries` 形の非実現 | ［Lean］（`restUnrealizableCarries_of_supports`） |
| X2 | 座標の道の証明は**中点の等式を仮定**に取るので、垂心系の枝を `Supports` では殺せない | ［紙］ |
| X3 | 34 類のどのマスクも、どの 4 点集合の 6 枡のうち高々 2 枡しか含まない ⟹ `Carries` なら非証人 1 枡で即死 | ［計算・厳密］（Lean では各類の証明の中で `decide`） |
| X4 | ゆえに繋ぎは `RestUnrealizableCarries` 版で通る | ［Lean］（`octahedralSix_of_census_carries`） |

**これは形式化が見つけた穴である**（`Supports` 版では鎖が閉じない）。

---

## 6. 信頼の土台

| もの | 値 |
|---|---|
| Lean / Mathlib | Lean 4 v4.33.1 ＋ Mathlib |
| ソースの本数 | 101（土台と探索木 74・鎖 27） |
| 行数 | 27,847 ＋ 14,594 |
| `sorry` / `axiom` / `native_decide` / `maxHeartbeats 0` | **0 / 0 / 0 / 0** |
| `Final` の `#print axioms` | 4 本とも `[propext, Classical.choice, Quot.sound]` |
| 独立な組み直し | 原本を写して（md5 記録）26 本を一本ずつ・**すべて rc=0・stderr 0**・21:56→23:44 |
| 組み直しの公理の行 | 549 行すべて標準三公理の部分集合（505 行が三つ・37 行が `propext`+`Quot.sound`・7 行が `propext`） |
| 外部のソルバ・CAS | **証明の中には無い**（証書を**探す**のには浮動小数・mod p・LP を使った） |
| 核の計算（`decide +kernel`） | 探索木の節点の表にだけ使う。幾何には使わない |

---

## 7. 既知性（§10）

| 事実 | 出所と確認の状態 |
|---|---|
| 問題の言明・一般の位置の規約 | 問題ページ（2026-09-25 に取得・逐語） |
| `n_k ≪ k⁹`・`n₄ ≤ 9`・`n₅ ≤ 37` | [MaRo15]（題・著者・要約は arXiv で確認。掲載誌は問題ページから・未確認。本文未読） |
| `n_k ≪ k⁵`・`O(k⁵/log k)` | 問題ページとフォーラム（逐語）。[MRR15] にも記録との指摘（本文未読） |
| 下界 `k^{2−o(1)}` | フォーラム（逐語） |
| **`n₄ = 7` の値そのもの** | **[S]（sallerk・2026-09-22 21:27・フォーラム。逐語で確認）。計算機援用の別証明。優先権はこちらに無い** |
| `n₅ ≥ 9`・`n₆ ≥ 11`・`n₇ ≥ 13`・`n₈ ≥ 17` | [S]（逐語。本稿では使っていない） |
| 形式化された言明の有無 | 問題ページの「Formalised statement?」欄が **No**（2026-09-25 時点） |

**探した範囲**：問題ページとフォーラムの全コメント・arXiv の全文検索（"distinct circumradii"）・OEIS。
MathSciNet と zbMATH は使えない。[S] が指すリポジトリは開いていない。エルデシュの原論文は未読。
