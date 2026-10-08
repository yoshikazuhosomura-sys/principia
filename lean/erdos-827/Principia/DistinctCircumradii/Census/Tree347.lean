import Principia.DistinctCircumradii.Census.Tree346

/-!
# `CensusComplete`: subtrees 1151-1175

The transcripts of the subtrees, checked by the kernel.  Each theorem
discharges the nodes it hands on with the theorems of the deeper subtrees,
which come earlier in this chain of files.
-/

namespace DistinctCircumradii

/-- Subtree rooted at `(19055513940578004910240, 618790403091871239201865567)`: 15 nodes (branch 1, chain 2, closed 10, tab 2). -/
def tree_sub1151 : Tr := Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [27, 39, 14] (Tr.chain 26 [7, 39, 21, 67, 74, 5] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 14] (Tr.chain 4 [67, 73, 28, 77, 34] (Tr.closed)), Tr.closed, Tr.closed]

theorem hand_sub1151 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1151 : Settles 19055513940578004910240 618790403091871239201865567 :=
  settles_of_check hand_sub1151 (by decide +kernel :
    check [] 55 19055513940578004910240 618790403091871239201865567 tree_sub1151 = true)

/-- Subtree rooted at `(4906980294992748090128, 772404244410282624719645935)`: 18 nodes (branch 1, chain 2, closed 9, forced 1, leaf 1, tab 4). -/
def tree_sub1152 : Tr := Tr.branch 9 [Tr.tab [27, 44] (Tr.chain 68 [42, 12, 51, 65, 17] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [27, 13] (Tr.chain 5 [74, 4, 76] (Tr.closed)), Tr.closed, Tr.tab [27] (Tr.forced 35 [(8, 1), (26, -1), (57, -1), (72, -1), (80, 1)] (Tr.tab [12, 23, 44, 13, 29] (Tr.leaf (0, 2, 5, 4, 3, 1)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1152 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1152 : Settles 4906980294992748090128 772404244410282624719645935 :=
  settles_of_check hand_sub1152 (by decide +kernel :
    check [] 58 4906980294992748090128 772404244410282624719645935 tree_sub1152 = true)

/-- Subtree rooted at `(4724962878432696402002, 875257157998055246418343853)`: 17 nodes (branch 1, chain 3, closed 9, cyc 1, tab 3). -/
def tree_sub1153 : Tr := Tr.branch 14 [Tr.closed, Tr.tab [25, 34, 8] (Tr.chain 0 [61, 29, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 28] (Tr.chain 88 [33, 83, 46, 58] (Tr.cycBad 0 4 1 5 [(4, 1), (6, 2), (16, 1), (20, -1), (33, -1), (46, -1), (51, -1), (61, -1), (72, 1), (83, 1)])), Tr.tab [25, 28, 34, 8] (Tr.chain 0 [61, 29, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1153 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1153 : Settles 4724962878432696402002 875257157998055246418343853 :=
  settles_of_check hand_sub1153 (by decide +kernel :
    check [] 57 4724962878432696402002 875257157998055246418343853 tree_sub1153 = true)

/-- Subtree rooted at `(1197958068093067553, 463168374627734437381463774)`: 65 nodes (branch 4, chain 9, closed 36, cyc 1, forced 2, tab 13). -/
def tree_sub1154 : Tr := Tr.branch 4 [Tr.closed, Tr.closed, Tr.forced 70 [(13, -1), (25, 1), (53, 1), (55, 1), (60, -1)] (Tr.tab [12] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.tab [24, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 41] (Tr.chain 43 [25, 34, 77, 28, 55] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24] (Tr.chain 76 [34, 89, 39, 70] (Tr.closed)), Tr.tab [24, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed], Tr.tab [41] (Tr.forced 74 [(0, -1), (46, 1), (53, -1), (60, 1), (70, 1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed])), Tr.tab [34, 24] (Tr.chain 24 [60, 13, 53, 23, 38, 8] (Tr.closed)), Tr.tab [34, 24] (Tr.chain 24 [60, 13, 53, 23, 38, 8] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 7 [Tr.closed, Tr.tab [24, 41, 14, 29] (Tr.cycBad 0 1 2 3 [(16, 1), (23, -1), (39, -1), (53, 1)]), Tr.closed, Tr.tab [24, 14] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.tab [24] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)), Tr.tab [24, 41, 14, 29] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1154 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1154 : Settles 1197958068093067553 463168374627734437381463774 :=
  settles_of_check hand_sub1154 (by decide +kernel :
    check [] 105 1197958068093067553 463168374627734437381463774 tree_sub1154 = true)

/-- Subtree rooted at `(1190076773854347264, 496921637294397731173087231)`: 15 nodes (branch 1, chain 2, closed 10, tab 2). -/
def tree_sub1155 : Tr := Tr.branch 4 [Tr.closed, Tr.tab [17, 38, 7, 13, 31, 37, 12, 41, 8] (Tr.chain 16 [32, 14, 34] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 7, 13, 17, 27, 41] (Tr.chain 14 [32, 16, 34] (Tr.closed)), Tr.closed, Tr.closed]

theorem hand_sub1155 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1155 : Settles 1190076773854347264 496921637294397731173087231 :=
  settles_of_check hand_sub1155 (by decide +kernel :
    check [] 55 1190076773854347264 496921637294397731173087231 tree_sub1155 = true)

/-- Subtree rooted at `(5607955022785141674496, 453946018859022796485160447)`: 13 nodes (branch 1, closed 8, cyc 2, tab 2). -/
def tree_sub1156 : Tr := Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 14, 40] (Tr.cycBad 0 1 2 4 [(9, 1), (26, -1), (32, 1), (40, -1), (57, -1), (69, 1), (72, -1), (83, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 14, 29] (Tr.cycBad 0 5 1 4 [(9, 1), (12, 2), (26, -1), (32, 1), (42, -1), (47, -1), (57, -1), (68, 1), (79, -1)]), Tr.closed, Tr.closed]

theorem hand_sub1156 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1156 : Settles 5607955022785141674496 453946018859022796485160447 :=
  settles_of_check hand_sub1156 (by decide +kernel :
    check [] 53 5607955022785141674496 453946018859022796485160447 tree_sub1156 = true)

/-- Subtree rooted at `(4796190613938752454660, 485737759346296017737348091)`: 13 nodes (branch 1, closed 8, cyc 2, tab 2). -/
def tree_sub1157 : Tr := Tr.branch 7 [Tr.tab [16, 24, 43, 20, 12, 25, 38, 27] (Tr.cycBad 0 3 1 2 [(10, 1), (18, 1), (33, -1), (36, -1), (50, 1), (64, -1)]), Tr.closed, Tr.closed, Tr.tab [24, 34, 44, 12, 14, 20, 27] (Tr.cycBad 0 1 2 3 [(18, -1), (25, 1), (33, 1), (36, 1), (50, -1), (55, -1), (59, -1), (64, 1), (66, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1157 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1157 : Settles 4796190613938752454660 485737759346296017737348091 :=
  settles_of_check hand_sub1157 (by decide +kernel :
    check [] 53 4796190613938752454660 485737759346296017737348091 tree_sub1157 = true)

/-- Subtree rooted at `(4796190613938752454656, 485737759346225648993104895)`: 74 nodes (branch 5, chain 6, closed 41, cyc 5, forced 2, tab 15). -/
def tree_sub1158 : Tr := Tr.branch 7 [Tr.tab [16, 24, 43, 20] (Tr.branch 12 [Tr.closed, Tr.tab [22, 41] (Tr.cycBad 1 2 3 5 [(10, -1), (33, 1), (36, 1), (46, 1), (50, -1)]), Tr.closed, Tr.tab [25, 38, 27] (Tr.cycBad 0 3 1 2 [(10, 1), (18, 1), (33, -1), (36, -1), (50, 1), (64, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 24, 41] (Tr.branch 9 [Tr.closed, Tr.tab [27, 43] (Tr.cycBad 0 4 1 2 [(16, 1), (23, -1), (25, -1), (36, 1), (50, 1), (55, -1), (66, -1)]), Tr.closed, Tr.tab [27, 34, 38, 13] (Tr.chain 4 [74, 50, 72, 25] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 12 [Tr.tab [20, 43, 44, 11, 13] (Tr.chain 62 [16, 34, 25, 72, 50] (Tr.tab [8, 29, 14, 28, 40] (Tr.cycBad 0 1 2 3 [(16, -1), (18, -1), (25, 1), (34, 1), (35, -1), (36, 1), (50, -1), (62, 1), (72, -1), (82, -1), (83, 1)]))), Tr.tab [20, 22] (Tr.cycBad 0 1 2 4 [(16, 1), (25, -1), (33, -1), (46, -1), (50, 1), (72, -1)]), Tr.closed, Tr.tab [20, 25, 38] (Tr.forced 81 [(16, -1), (18, -1), (25, 1), (33, 1), (36, 1), (50, -1), (64, 1)] (Tr.tab [11] (Tr.forced 85 [(18, 1), (36, -1), (66, 1), (72, 1), (81, 1)] (Tr.tab [8, 29, 14, 28] (Tr.chain 3 [55, 85, 16, 89, 33] (Tr.closed)))))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 34, 44, 14, 20, 27] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.chain 29 [55, 28, 59] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 86 [55, 85, 56] (Tr.tab [9, 29, 39, 11, 28, 13, 22, 12] (Tr.chain 11 [50, 72, 25, 47, 59] (Tr.closed))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1158 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1158 : Settles 4796190613938752454656 485737759346225648993104895 :=
  settles_of_check hand_sub1158 (by decide +kernel :
    check [] 114 4796190613938752454656 485737759346225648993104895 tree_sub1158 = true)

/-- Subtree rooted at `(5607955022780846707456, 453946037233709246092012799)`: 23 nodes (branch 2, closed 16, cyc 3, tab 2). -/
def tree_sub1159 : Tr := Tr.branch 8 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 40] (Tr.cycBad 0 2 1 3 [(8, -1), (9, -1), (12, -1), (26, 2), (40, 1), (42, 1), (57, 1), (68, -1), (69, -1), (83, -1)]), Tr.closed, Tr.tab [29, 39] (Tr.cycBad 0 1 2 4 [(8, 1), (9, 1), (26, -1), (40, -1), (57, -1), (68, 1), (72, -1), (89, 1)]), Tr.closed, Tr.closed], Tr.cycBad 0 1 2 4 [(9, 1), (12, 1), (22, 1), (26, -1), (47, -1), (57, -1), (68, 1), (72, -1)], Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1159 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1159 : Settles 5607955022780846707456 453946037233709246092012799 :=
  settles_of_check hand_sub1159 (by decide +kernel :
    check [] 63 5607955022780846707456 453946037233709246092012799 tree_sub1159 = true)

/-- Subtree rooted at `(1190077027257417728, 497242107676881067569378303)`: 206 nodes (assumed 1, branch 14, chain 17, closed 117, cyc 9, forced 7, symm 1, tab 40). -/
def tree_sub1160 : Tr := Tr.branch 7 [Tr.tab [16, 43] (Tr.branch 8 [Tr.closed, Tr.tab [25, 41] (Tr.forced 82 [(10, -1), (22, 1), (24, 1), (30, -1), (55, 1)] (Tr.tab [13, 37, 12] (Tr.chain 79 [30, 19, 82, 35, 22] (Tr.closed)))), Tr.closed, Tr.tab [25, 38, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [25] (Tr.branch 9 [Tr.tab [29] (Tr.forced 70 [(17, 1), (38, -1), (50, 1), (55, 1), (60, -1)] (Tr.tab [12, 37] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 13 [Tr.closed, Tr.chain 58 [24, 60, 50, 17, 47] (Tr.tab [11, 26, 14] (Tr.cycBad 0 1 2 3 [(10, 3), (17, 1), (19, 2), (24, -4), (30, -2), (38, -1), (39, -3), (47, -3), (50, 5), (55, -1), (58, 2), (77, -2), (85, -1)])), Tr.closed, Tr.tab [27, 38, 14, 26, 11] (Tr.chain 5 [17, 71, 39, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [22, 41, 13, 14, 26, 38, 11] (Tr.chain 5 [17, 71, 39, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.tab [29, 42, 14, 27, 41] (Tr.cycBad 0 4 1 2 [(10, -1), (24, 1), (29, 1), (38, 1), (39, 1), (50, -1), (55, -1), (60, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39, 14] (Tr.chain 1 [55, 86, 10, 89, 39] (Tr.closed)), Tr.tab [29, 39, 14] (Tr.chain 1 [55, 86, 10, 89, 39] (Tr.closed)), Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [17, 41] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [42] (Tr.branch 14 [Tr.closed, Tr.tab [25, 43] (Tr.chain 85 [55, 29, 65, 16] (Tr.cycBad 1 5 2 3 [(29, 1), (30, 1), (39, 1), (50, -1), (55, -1), (85, 1)])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.branch 8 [Tr.tab [25, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.tab [22] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 13, 37] (Tr.cycBad 0 1 2 3 [(19, 1), (24, -1), (29, 1), (46, -1), (55, -1), (58, 1), (60, 1)]), Tr.closed, Tr.tab [26] (Tr.cycBad 0 4 1 3 [(19, 1), (24, -1), (29, 1), (38, 1), (39, 1), (46, -1), (55, -2), (60, 1), (69, 1), (89, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.tab [25, 38, 11, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.tab [25, 29, 43, 8, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.cycBad 1 5 2 3 [(16, -1), (30, 1), (39, 1), (50, -1), (65, 1)])), Tr.tab [29] (Tr.forced 3 [(30, -1), (50, 1), (55, 1), (71, -1), (86, -1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39, 8, 25] (Tr.chain 1 [85, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [31] (Tr.branch 8 [Tr.tab [25, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.tab [22, 41] (Tr.forced 20 [(11, 1), (39, -1), (50, 1), (55, 1), (60, -1), (79, -1)] (Tr.closed)))), Tr.tab [25, 41] (Tr.branch 12 [Tr.chain 82 [19, 30, 79, 22, 35] (Tr.tab [13] (Tr.forced 10 [(19, -1), (24, 1), (35, 1), (55, 1), (79, -1)] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.forced 17 [(38, 1), (50, -1), (55, -1), (60, 1), (70, 1)] (Tr.tab [9] (Tr.branch 9 [Tr.branch 13 [Tr.closed, Tr.tab [43] (Tr.chain 58 [24, 60, 50, 17, 47] (Tr.tab [11, 26, 14, 39] (Tr.cycBad 0 1 2 3 [(38, -1), (39, -1), (50, 1), (55, 1), (58, 1), (70, -1), (79, -1)]))), Tr.closed, Tr.tab [38] (Tr.cycBad 0 2 1 4 [(19, -1), (24, 1), (30, 1), (38, -1), (50, 1), (55, 1), (60, -1), (70, -2), (76, 1), (79, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 1 4 2 5 [(17, -1), (19, 1), (22, -1), (24, -1), (38, 2), (39, 1), (50, -2), (55, -2), (60, 2), (70, 2), (79, 1), (86, -1)]), Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [25, 38, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [16, 31, 43] (Tr.forced 35 [(10, 1), (19, 1), (24, -1), (55, -1), (79, 1)] (Tr.tab [12, 25, 8, 41] (Tr.chain 82 [19, 30, 79, 22, 35] (Tr.tab [13] ((Tr.symm (1, 0, 3, 2, 4, 5) Tr.assumed)))))), Tr.closed]

theorem hand_sub1160 : ∀ x ∈ ([(5607955022780846707456, 453946037233709246092012799)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1159 all_settles_nil)

theorem settles_sub1160 : Settles 1190077027257417728 497242107676881067569378303 :=
  settles_of_check hand_sub1160 (by decide +kernel :
    check [(5607955022780846707456, 453946037233709246092012799)] 246 1190077027257417728 497242107676881067569378303 tree_sub1160 = true)

/-- Subtree rooted at `(1190076752379510784, 496920986107524286818595823)`: 228 nodes (assumed 4, branch 15, chain 21, closed 120, cyc 11, forced 3, half 1, symm 3, tab 50). -/
def tree_sub1161 : Tr := Tr.branch 4 [Tr.tab [43] (Tr.branch 7 [Tr.closed, Tr.tab [17, 24, 41, 21] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 25] (Tr.cycBad 0 2 1 3 [(16, 1), (19, 1), (30, -1), (39, -1), (50, 1), (76, -1)]), Tr.closed, Tr.tab [37] (Tr.branch 12 [Tr.tab [25, 44, 8] (Tr.halfBad 1 0 2 5 [(19, 1), (24, 1), (30, -1), (39, -1), (50, 1), (55, 1), (60, 1), (82, -1), (85, -1)] [(4, 1), (19, 1), (50, 1), (82, -1)]), Tr.tab [25] (Tr.chain 11 [50, 60, 24, 46] (Tr.cycBad 0 4 1 5 [(4, 1), (30, 1), (39, 1), (46, -1), (55, -1)])), Tr.closed, Tr.tab [25, 34, 38, 8] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 34, 44, 14, 21, 25] (Tr.branch 8 [Tr.closed, Tr.tab [41, 12, 26, 37, 11, 13, 39] (Tr.chain 23 [56, 22, 59] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 86 [55, 85, 56] (Tr.tab [9, 29, 39, 11, 26, 12] (Tr.chain 11 [50, 60, 24, 46] (Tr.closed))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 31] (Tr.branch 8 [Tr.tab [25, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.tab [41, 21] (Tr.cycBad 0 4 1 5 [(4, 1), (11, 2), (24, -2), (30, 1), (39, 1), (46, -3), (50, 2), (55, -1), (60, -2)]))), Tr.tab [25, 41] (Tr.branch 12 [Tr.tab [44, 21] (Tr.chain 82 [19, 30, 79, 22, 35] (Tr.tab [13] (Tr.cycBad 1 2 3 5 [(4, 1), (19, 1), (24, -1), (35, -1), (55, -1), (79, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.branch 13 [Tr.tab [21, 44, 11] (Tr.chain 71 [39, 70, 41] (Tr.tab [14, 26, 42] (Tr.cycBad 1 5 2 3 [(30, 1), (40, 1), (41, -1), (50, -1), (55, -1), (69, -2), (70, 2), (71, -1), (79, 1)]))), Tr.closed, Tr.closed, Tr.tab [21, 27, 38] (Tr.cycBad 1 3 2 5 [(4, 1), (19, 1), (24, -1), (55, -1), (70, 1), (76, -1), (79, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [25, 34, 38, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [17, 38] (Tr.branch 7 [Tr.tab [16, 24, 43] (Tr.branch 8 [Tr.closed, Tr.tab [25, 41] (Tr.forced 82 [(10, -1), (22, 1), (24, 1), (30, -1), (55, 1)] (Tr.tab [13, 21, 37, 12] (Tr.chain 79 [30, 19, 82, 35, 22] (Tr.closed)))), Tr.closed, Tr.tab [25, 34, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [25] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [29, 42, 14, 41, 21] (Tr.cycBad 0 1 3 4 [(10, 1), (14, -1), (29, -1), (39, -1), (50, 1), (55, 1), (60, -1), (85, -1)]), Tr.tab [27, 29, 14] (Tr.chain 40 [24, 60, 50, 74, 10] (Tr.tab [11, 21, 41, 44, 12, 13, 26] (Tr.cycBad 0 1 2 3 [(10, 1), (19, 1), (24, -1), (30, -1), (40, -1), (41, 1), (50, 1), (60, 1), (69, -4), (70, 5), (71, -5), (74, -1)]))), Tr.tab [27, 29, 42] (Tr.closed), Tr.closed, Tr.closed, Tr.tab [29, 39, 14] (Tr.chain 1 [55, 86, 10, 89, 39] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [24, 34, 44, 14, 21, 25] (Tr.branch 8 [Tr.closed, Tr.tab [41, 12, 26, 37, 11, 13, 39] (Tr.chain 4 [56, 22, 59, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 86 [55, 85, 56] (Tr.tab [9, 29, 39, 11, 26, 12, 22, 13] (Tr.chain 11 [50, 60, 24, 46] (Tr.closed))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 31] (Tr.branch 8 [Tr.tab [25, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.tab [22, 41, 21, 13, 37] (Tr.cycBad 1 5 3 4 [(11, 2), (14, 1), (24, -3), (39, 1), (46, -3), (50, 2), (55, -1), (60, -2), (79, 1)]))), Tr.tab [25, 41] (Tr.branch 12 [Tr.tab [44, 21] (Tr.chain 82 [19, 30, 79, 22, 35] (Tr.forced 10 [(22, 1), (24, 1), (30, -1), (55, 1), (82, -1)] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.branch 13 [Tr.tab [21, 11] (Tr.chain 71 [39, 70, 41] (Tr.tab [14, 26, 42] (Tr.cycBad 0 3 2 5 [(14, 1), (24, -1), (30, 1), (41, -1), (50, -1), (55, -1), (69, -1), (70, 1), (79, 1)]))), Tr.tab [21, 43] (Tr.cycBad 1 5 2 3 [(14, -1), (24, 1), (30, 1), (39, 1), (47, 1), (50, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [25, 34, 12] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [16, 24, 31, 43] (Tr.forced 35 [(10, 1), (19, 1), (24, -1), (55, -1), (79, 1)] (Tr.tab [12, 25, 44, 8, 21, 41] (Tr.chain 82 [19, 30, 79, 22, 35] ((Tr.symm (1, 0, 3, 2, 4, 5) Tr.assumed))))), Tr.closed]), Tr.closed, Tr.tab [21, 34, 24] (Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] ((Tr.symm (0, 1, 3, 2, 4, 5) Tr.assumed)), Tr.tab [28, 43] ((Tr.symm (0, 1, 3, 2, 4, 5) Tr.assumed)), Tr.closed]

theorem hand_sub1161 : ∀ x ∈ ([(1190077027257417728, 497242107676881067569378303), (4796190613938752454656, 485737759346225648993104895), (4796190613938752454660, 485737759346296017737348091), (5607955022785141674496, 453946018859022796485160447)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1160 (all_settles_cons settles_sub1158 (all_settles_cons settles_sub1157 (all_settles_cons settles_sub1156 all_settles_nil))))

theorem settles_sub1161 : Settles 1190076752379510784 496920986107524286818595823 :=
  settles_of_check hand_sub1161 (by decide +kernel :
    check [(1190077027257417728, 497242107676881067569378303), (4796190613938752454656, 485737759346225648993104895), (4796190613938752454660, 485737759346296017737348091), (5607955022785141674496, 453946018859022796485160447)] 268 1190076752379510784 496920986107524286818595823 tree_sub1161 = true)

/-- Subtree rooted at `(1189232326635168001, 151791466733887316985568990)`: 224 nodes (branch 16, chain 17, closed 139, cyc 4, forced 6, leaf 1, parrel 1, tab 40). -/
def tree_sub1162 : Tr := Tr.branch 5 [Tr.tab [44, 21] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 11 [Tr.forced 43 [(5, 1), (34, -1), (39, 1), (48, 1)] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [35] (Tr.cycBad 0 3 1 4 [(0, 1), (5, -1), (13, 1), (23, 1), (28, -1), (39, -1), (81, -1)]), Tr.tab [35] (Tr.cycBad 0 3 1 4 [(0, 1), (5, -1), (13, 1), (23, 1), (28, -1), (39, -1), (81, -1)]), Tr.closed]), Tr.tab [34, 24] (Tr.branch 7 [Tr.closed, Tr.tab [41] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [42] (Tr.chain 87 [39, 71, 23, 38, 8] (Tr.tab [12, 26, 29, 35, 11, 13] (Tr.chain 26 [60, 48, 16, 34, 76] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 7 [60, 48, 16, 89, 39] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.chain 81 [0, 67, 38, 8] (Tr.tab [35] (Tr.cycBad 0 3 1 4 [(5, -1), (8, 1), (39, -1), (81, -1)]))), Tr.tab [26, 41, 14] (Tr.chain 7 [60, 48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.tab [34, 36, 24] (Tr.parRel 2 3 5 [] [(0, 2, 1, 5, -1), (0, 5, 1, 3, 1)]), Tr.closed, Tr.closed, Tr.tab [28] (Tr.forced 87 [(13, -1), (48, 1), (55, 1), (60, -1), (78, -1)] (Tr.tab [12] (Tr.branch 11 [Tr.forced 43 [(0, 1), (5, 1), (8, -1), (13, 5), (23, 1), (28, -1), (34, -1), (39, 1), (48, -3), (55, -4), (60, 4), (78, 4), (87, 4)] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 36, 29] (Tr.forced 74 [(5, 1), (8, -1), (13, 1), (23, 1), (39, 1), (55, -1), (60, 1), (69, 1), (78, 1), (87, 1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [22, 34] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 7 [Tr.closed, Tr.tab [24, 41, 21] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42, 13] (Tr.forced 81 [(8, 1), (16, -1), (44, -1), (60, 1), (76, 1)] (Tr.tab [35, 12, 20] (Tr.chain 43 [25, 76, 35, 28, 55] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.chain 7 [60, 48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 44, 14, 21] (Tr.chain 3 [55, 28, 59, 23, 56, 48, 60, 13] (Tr.closed)), Tr.closed, Tr.tab [24, 26] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 41, 21, 13] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 12 [Tr.tab [20, 44, 21, 11] (Tr.chain 17 [44, 8, 81, 0, 67, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 2 5 [(25, 1), (48, -1), (55, 1), (70, -1), (89, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [24, 26, 41, 14, 21, 29] (Tr.chain 7 [60, 48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.forced 87 [(13, -1), (48, 1), (55, 1), (60, -1), (78, -1)] (Tr.tab [12] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 7 [Tr.closed, Tr.tab [24, 41, 21] (Tr.branch 11 [Tr.chain 88 [13, 60, 48, 16, 34] (Tr.tab [13, 29, 14] (Tr.chain 2 [16, 89, 39, 87] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 36, 14] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 44, 14, 21] (Tr.chain 3 [55, 28, 59, 23, 56, 48, 60, 13] (Tr.closed)), Tr.closed, Tr.tab [24, 26] (Tr.branch 11 [Tr.tab [21] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 13] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 13] (Tr.chain 2 [48, 60, 13, 88, 34, 89, 39, 87] (Tr.closed)), Tr.closed, Tr.closed]), Tr.tab [21, 41, 13, 14, 29] (Tr.leaf (0, 3, 4, 5, 1, 2)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [24, 26, 41, 11, 14, 21, 29, 13] (Tr.chain 2 [16, 89, 39, 87] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed], Tr.tab [20, 44, 21, 24, 11, 26, 36, 7, 29, 41] (Tr.closed), Tr.closed]))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1162 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1162 : Settles 1189232326635168001 151791466733887316985568990 :=
  settles_of_check hand_sub1162 (by decide +kernel :
    check [] 264 1189232326635168001 151791466733887316985568990 tree_sub1162 = true)

/-- Subtree rooted at `(311980852021467860435969, 541116781141949095180106750)`: 15 nodes (branch 1, chain 2, closed 10, tab 2). -/
def tree_sub1163 : Tr := Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 9] (Tr.chain 1 [68, 74, 10, 77, 52] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 9] (Tr.chain 53 [63, 0, 73, 68, 17] (Tr.closed)), Tr.closed, Tr.closed]

theorem hand_sub1163 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1163 : Settles 311980852021467860435969 541116781141949095180106750 :=
  settles_of_check hand_sub1163 (by decide +kernel :
    check [] 55 311980852021467860435969 541116781141949095180106750 tree_sub1163 = true)

/-- Subtree rooted at `(4934540368131783671937, 1230681549827321069532331902)`: 13 nodes (branch 1, closed 9, leaf 1, tab 2). -/
def tree_sub1164 : Tr := Tr.branch 11 [Tr.closed, Tr.tab [21, 13] (Tr.leaf (0, 1, 2, 3, 4, 5)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 28] (Tr.closed), Tr.closed, Tr.closed]

theorem hand_sub1164 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1164 : Settles 4934540368131783671937 1230681549827321069532331902 :=
  settles_of_check hand_sub1164 (by decide +kernel :
    check [] 53 4934540368131783671937 1230681549827321069532331902 tree_sub1164 = true)

/-- Subtree rooted at `(4869976763384173969537, 140230525098533600091946878)`: 37 nodes (branch 3, chain 2, closed 27, leaf 1, tab 4). -/
def tree_sub1165 : Tr := Tr.branch 12 [Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 14] (Tr.chain 5 [44, 14, 34, 89, 33, 82] (Tr.closed)), Tr.closed, Tr.tab [29, 14] (Tr.chain 5 [44, 14, 88, 33, 83, 35] (Tr.closed)), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 29] (Tr.closed), Tr.closed, Tr.tab [29, 14] (Tr.leaf (0, 2, 4, 1, 5, 3)), Tr.closed, Tr.closed], Tr.closed]

theorem hand_sub1165 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1165 : Settles 4869976763384173969537 140230525098533600091946878 :=
  settles_of_check hand_sub1165 (by decide +kernel :
    check [] 77 4869976763384173969537 140230525098533600091946878 tree_sub1165 = true)

/-- Subtree rooted at `(2378468501284200705, 132751032107066043857362654)`: 29 nodes (branch 2, chain 1, closed 18, cyc 1, forced 2, tab 5). -/
def tree_sub1166 : Tr := Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [42, 23] (Tr.forced 80 [(0, -1), (42, -1), (49, 1), (61, 1), (71, 1)] (Tr.closed)), Tr.tab [27, 41, 21, 22] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 5] (Tr.chain 17 [50, 13, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 29, 36, 5, 44, 12] (Tr.cycBad 0 1 2 5 [(5, -1), (8, 1), (13, -1), (28, 1), (42, 1), (49, -1), (70, -1), (88, 1)]), Tr.closed, Tr.closed]), Tr.tab [27, 41, 42, 21, 22, 23, 13, 29, 36, 5, 26, 44] (Tr.closed), Tr.closed, Tr.closed, Tr.forced 16 [(0, 1), (42, 1), (49, -1), (56, 1), (61, -1), (89, 1)] (Tr.closed), Tr.closed, Tr.closed]

theorem hand_sub1166 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1166 : Settles 2378468501284200705 132751032107066043857362654 :=
  settles_of_check hand_sub1166 (by decide +kernel :
    check [] 69 2378468501284200705 132751032107066043857362654 tree_sub1166 = true)

/-- Subtree rooted at `(1188968443844501761, 151187003823869171043589886)`: 229 nodes (assumed 5, branch 17, chain 13, closed 142, cyc 4, forced 5, leaf 3, symm 5, tab 35). -/
def tree_sub1167 : Tr := Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 11 [Tr.tab [20, 21] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.forced 53 [(13, 1), (25, -1), (55, -1), (60, 1), (70, 1)] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.branch 14 [Tr.tab [24, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 41] (Tr.chain 43 [25, 34, 77, 28, 55] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24] (Tr.chain 76 [34, 89, 39, 70] (Tr.closed)), Tr.tab [24, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed], Tr.closed, Tr.tab [27] (Tr.chain 89 [39, 70, 76, 34] (Tr.forced 9 [(0, -1), (13, -1), (25, 1), (28, 1), (39, 1), (55, 1), (60, -1), (70, -1), (89, -1)] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed])), Tr.closed, Tr.tab [29] (Tr.cycBad 0 5 2 3 [(0, 1), (13, 1), (25, -1), (55, -1), (60, 1), (87, 1)]), Tr.closed, Tr.closed]), Tr.tab [21, 41, 44, 13, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14, 29, 12] (Tr.chain 5 [44, 8, 40, 89, 39, 70] (Tr.closed)), Tr.closed, Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14] (Tr.chain 5 [44, 8, 40, 89, 39, 70] (Tr.closed)), Tr.closed, Tr.tab [29, 14] (Tr.chain 5 [44, 8, 87, 39, 71, 41] (Tr.closed)), Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 28, 35] (Tr.branch 12 [Tr.tab [44, 24] (Tr.forced 77 [(0, -1), (13, -1), (25, 1), (28, 1), (35, 1), (39, 1)] (Tr.tab [14, 27, 41, 7, 13, 26] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 5 1 3 [(0, 1), (13, 2), (25, -1), (28, -1), (39, -1), (55, -1), (60, 1), (70, 1), (81, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [20, 21, 28, 35, 12, 26] (Tr.cycBad 0 5 1 3 [(0, 1), (13, 2), (25, -1), (28, -1), (39, -1), (55, -1), (60, 1), (70, 1), (81, -1)]), Tr.closed]), Tr.closed, Tr.closed, Tr.tab [23, 32] (Tr.branch 7 [Tr.closed, Tr.tab [24, 41, 21] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.forced 81 [(8, 1), (16, -1), (44, -1), (60, 1), (76, 1)] (Tr.tab [11, 35] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 12 [Tr.branch 14 [Tr.closed, Tr.closed, Tr.leaf (0, 3, 2, 1, 4, 5), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 1, 3, 4, 5, 2), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14] (Tr.chain 34 [76, 70, 39, 89] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [20, 12, 26, 14] (Tr.forced 18 [(8, -1), (13, 1), (16, 1), (28, -1), (34, -2), (39, 1), (44, 1), (60, -1), (70, -1), (76, 1), (89, -2)] (Tr.closed)), Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 29, 12, 20, 11] (Tr.cycBad 0 1 3 5 [(8, 1), (16, -1), (23, 1), (44, -1), (60, 1), (81, -1), (88, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 35, 11, 12, 20] (Tr.chain 2 [16, 89, 39, 87] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 44, 14, 21] (Tr.chain 22 [56, 23, 59] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 28] (Tr.branch 11 [Tr.tab [20, 21] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 14] (Tr.leaf (1, 4, 5, 2, 3, 0)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 14] (Tr.chain 3 [55, 28, 77, 34, 88] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, (Tr.symm (2, 0, 1, 5, 4, 3) Tr.assumed), Tr.closed, Tr.closed]), Tr.tab [21, 41, 44, 13] ((Tr.symm (0, 1, 3, 2, 4, 5) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 36, 13, 27] ((Tr.symm (1, 0, 3, 2, 5, 4) Tr.assumed)), Tr.tab [21, 36, 41, 44, 13] ((Tr.symm (0, 2, 1, 5, 3, 4) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, (Tr.symm (0, 3, 4, 1, 2, 5) Tr.assumed), Tr.closed, Tr.closed]

theorem hand_sub1167 : ∀ x ∈ ([(2378468501284200705, 132751032107066043857362654), (4869976763384173969537, 140230525098533600091946878), (4934540368131783671937, 1230681549827321069532331902), (311980852021467860435969, 541116781141949095180106750)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1166 (all_settles_cons settles_sub1165 (all_settles_cons settles_sub1164 (all_settles_cons settles_sub1163 all_settles_nil))))

theorem settles_sub1167 : Settles 1188968443844501761 151187003823869171043589886 :=
  settles_of_check hand_sub1167 (by decide +kernel :
    check [(2378468501284200705, 132751032107066043857362654), (4869976763384173969537, 140230525098533600091946878), (4934540368131783671937, 1230681549827321069532331902), (311980852021467860435969, 541116781141949095180106750)] 269 1188968443844501761 151187003823869171043589886 tree_sub1167 = true)

/-- Subtree rooted at `(1190085547658322177, 151187003832251572815847166)`: 145 nodes (branch 10, chain 18, closed 82, cyc 9, forced 1, tab 25). -/
def tree_sub1168 : Tr := Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 13 [Tr.tab [21, 41, 44, 11, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14, 29, 12] (Tr.chain 10 [23, 41, 70, 39, 89] (Tr.closed)), Tr.closed, Tr.cycBad 0 5 1 3 [(0, 1), (13, 1), (25, -1), (28, -1), (40, -1), (41, 1), (50, 1), (79, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [21, 27] (Tr.chain 35 [76, 25, 43, 55, 28] (Tr.tab [12, 20, 44, 11, 24, 28, 35] (Tr.cycBad 0 2 1 4 [(0, -1), (25, 1), (28, 1), (35, 1), (76, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [21, 34, 24] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26] (Tr.chain 87 [39, 71, 23, 38, 8] (Tr.tab [12, 26, 35, 11, 20] (Tr.cycBad 0 2 1 4 [(0, -1), (28, 2), (34, 1), (43, 1), (55, -1), (71, -1), (76, -1), (87, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.forced 67 [(0, 1), (28, -1), (39, -1), (43, -1), (50, 1), (55, 1), (89, 1)] (Tr.tab [7, 26] (Tr.chain 81 [0, 67, 38, 8] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 12 [Tr.chain 25 [43, 55, 28, 35, 76] (Tr.closed), Tr.chain 6 [43, 55, 28, 46, 81] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.chain 34 [76, 70, 39, 89] (Tr.closed), Tr.chain 6 [43, 55, 28, 46, 81] (Tr.closed), Tr.closed, Tr.closed, Tr.closed], Tr.tab [20] (Tr.chain 70 [39, 89, 34, 76] (Tr.cycBad 0 4 1 5 [(23, -1), (28, 1), (34, -1), (38, 2), (39, 1), (50, -1), (55, -1), (60, 1), (67, -1), (81, 1), (89, -1)])), Tr.closed], Tr.cycBad 0 2 1 3 [(16, 1), (23, -1), (39, -1), (50, 1), (67, -1)], Tr.closed, Tr.closed, Tr.closed])))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 11 [Tr.tab [20] (Tr.branch 7 [Tr.closed, Tr.tab [41] (Tr.chain 48 [60, 13, 88, 34, 16] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.chain 81 [0, 67, 38, 8] (Tr.closed)), Tr.tab [26, 41, 14, 29, 12] (Tr.chain 2 [16, 89, 39, 87] (Tr.closed)), Tr.cycBad 0 4 2 3 [(0, 1), (28, -1), (39, -1), (43, -1), (50, 1), (55, 1), (79, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 35, 29] (Tr.chain 67 [0, 81, 8, 38] (Tr.tab [26, 14, 41] (Tr.cycBad 0 2 1 3 [(0, 1), (23, -1), (38, 1), (39, -1), (43, -1), (50, 1), (60, 1), (67, -2), (88, 1)]))), Tr.tab [20, 28, 35, 29] (Tr.chain 67 [0, 81, 8, 38] (Tr.tab [26, 14, 41, 12] (Tr.chain 3 [55, 28, 77, 34, 88] (Tr.closed)))), Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [21, 34, 36, 13, 24, 27] (Tr.chain 35 [76, 25, 43, 55, 28] (Tr.tab [12, 20, 11, 28, 35] (Tr.chain 67 [0, 81, 8, 38] (Tr.tab [26, 14] (Tr.cycBad 0 2 1 4 [(25, 1), (35, 1), (39, -1), (43, -1), (50, 1), (55, 1), (67, -1), (76, -1), (89, 1)]))))), Tr.closed, Tr.closed, Tr.chain 46 [8, 78, 43, 55, 28] (Tr.tab [12, 41, 21] (Tr.cycBad 0 3 1 4 [(0, 1), (13, 1), (23, 1), (46, -1), (55, -1), (78, 1)])), Tr.closed, Tr.closed]

theorem hand_sub1168 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1168 : Settles 1190085547658322177 151187003832251572815847166 :=
  settles_of_check hand_sub1168 (by decide +kernel :
    check [] 185 1190085547658322177 151187003832251572815847166 tree_sub1168 = true)

/-- Subtree rooted at `(1189241139908059425, 151792057029709804678864606)`: 50 nodes (branch 3, chain 8, closed 25, cyc 3, tab 11). -/
def tree_sub1169 : Tr := Tr.branch 11 [Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 24, 27, 41, 7, 13, 26] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)))), Tr.tab [34, 24] (Tr.branch 7 [Tr.closed, Tr.tab [41] (Tr.chain 88 [13, 60, 48, 16, 34] (Tr.tab [13] (Tr.cycBad 0 3 1 4 [(16, 1), (34, -1), (48, 1), (60, -1), (88, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.chain 81 [0, 67, 38, 8] (Tr.closed)), Tr.tab [26, 41, 14] (Tr.chain 7 [60, 48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.tab [34, 36, 24] (Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 27, 41, 7, 13, 26] (Tr.chain 2 [48, 60, 13, 53, 23, 38, 8] (Tr.closed)))), Tr.closed, Tr.closed, Tr.chain 46 [8, 78, 43, 55, 28] (Tr.tab [12, 41] (Tr.cycBad 0 2 1 3 [(0, 1), (5, 1), (8, -1), (13, 1), (23, 1), (39, 1), (46, -1), (48, 1), (55, -1)])), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 35] (Tr.cycBad 0 3 1 4 [(5, -1), (8, 1), (39, -1), (81, -1)]), Tr.closed]

theorem hand_sub1169 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1169 : Settles 1189241139908059425 151792057029709804678864606 :=
  settles_of_check hand_sub1169 (by decide +kernel :
    check [] 90 1189241139908059425 151792057029709804678864606 tree_sub1169 = true)

/-- Subtree rooted at `(1188987758170341378, 954574990404202440874768365)`: 85 nodes (branch 6, chain 8, closed 50, cyc 4, forced 4, leaf 1, tab 12). -/
def tree_sub1170 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.chain 29 [55, 1, 70, 41] (Tr.closed)), Tr.closed, Tr.tab [29, 35] (Tr.branch 8 [Tr.forced 4 [(11, 1), (45, -1), (55, 1), (60, -1), (87, -1)] (Tr.tab [4, 43, 18] (Tr.forced 78 [(1, -1), (4, -1), (19, -1), (32, 1), (55, 1), (60, -1), (87, -1)] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.chain 65 [27, 36, 60, 26, 41] (Tr.tab [14] (Tr.forced 83 [(1, -1), (26, 1), (36, -1), (55, 1), (87, -1)] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.chain 69 [45, 83, 11, 74, 4] (Tr.tab [11] (Tr.cycBad 0 1 2 5 [(4, -1), (19, -1), (26, -2), (27, 1), (36, 3), (45, 1), (55, 1), (60, -1), (65, 2), (74, -1), (78, -2), (83, 1)])), Tr.closed, Tr.closed, Tr.closed, Tr.chain 58 [87, 1, 55, 86, 4] (Tr.tab [11] (Tr.leaf (0, 4, 3, 2, 1, 5))), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.chain 77 [27, 36, 60, 50, 11] (Tr.tab [14, 27, 9] (Tr.chain 58 [87, 1, 55, 86, 4] (Tr.tab [11] (Tr.cycBad 0 2 1 4 [(1, -8), (4, 2), (11, -6), (19, -5), (27, 5), (32, 6), (36, 1), (41, -6), (45, 5), (50, -1), (55, -3), (58, 3), (77, 1), (86, -3), (87, 2)])))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.tab [18, 41] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.chain 65 [27, 36, 60, 26, 41] (Tr.tab [14] (Tr.forced 49 [(22, -1), (27, 1), (36, 1), (45, 1), (65, 1)] (Tr.tab [4, 32, 9] (Tr.cycBad 0 1 3 4 [(22, 1), (26, -1), (32, -1), (36, 1), (49, 1), (55, 1), (60, -1), (65, 1), (74, -1)])))), Tr.closed, Tr.closed, Tr.tab [23] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.chain 10 [74, 50, 60, 36, 27] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 1 4 3 5 [(1, 1), (19, 1), (27, -1), (45, -1), (50, -1), (86, 1), (87, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1170 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1170 : Settles 1188987758170341378 954574990404202440874768365 :=
  settles_of_check hand_sub1170 (by decide +kernel :
    check [] 125 1188987758170341378 954574990404202440874768365 tree_sub1170 = true)

/-- Subtree rooted at `(1188959647743090689, 151168077175154562462161610)`: 179 nodes (assumed 3, branch 13, chain 10, closed 102, cyc 11, forced 5, leaf 1, parrel 1, symm 1, tab 32). -/
def tree_sub1171 : Tr := Tr.branch 9 [Tr.tab [17, 38, 44, 4, 15, 21, 24] (Tr.branch 2 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [20, 34, 5, 22, 23, 13, 36, 11, 28, 35, 29] (Tr.chain 44 [14, 88, 13, 50] (Tr.closed)), Tr.closed, Tr.tab [23, 31, 5, 22, 43, 13] (Tr.branch 7 [Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 1 2 4 5 [(10, -1), (17, 1), (43, 1), (44, -1), (47, 1), (55, 1), (60, -1), (69, -1)], Tr.closed, Tr.tab [35] (Tr.branch 12 [Tr.forced 89 [(0, -1), (10, -1), (17, 1), (28, 1), (35, 1), (39, 1), (43, 1), (44, -1)] (Tr.tab [14] (Tr.leaf (1, 5, 2, 0, 3, 4))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 4 2 3 [(0, 1), (14, 1), (17, -1), (28, -1), (39, -1), (43, -2), (44, 1), (47, -1), (60, 1), (70, 1), (81, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 11, 35] (Tr.branch 12 [Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 4 [(0, -1), (17, 1), (28, 2), (35, 1), (39, 1), (47, -1), (48, 1), (55, -1), (77, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 3 [(0, 2), (28, -1), (35, -1), (39, -1), (44, -1), (47, 2), (48, 2), (55, 1), (67, -2), (89, 2)], Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 2 3 [(0, 1), (14, 1), (17, -1), (28, -1), (39, -1), (43, -1), (60, 1), (70, 1), (81, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 18, 43, 15, 22] (Tr.forced 8 [(0, 1), (13, 1), (23, 1), (28, -1)] (Tr.tab [2, 38] (Tr.branch 2 [Tr.closed, Tr.branch 5 [Tr.tab [44, 21] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 11 [Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 24, 27, 41, 13, 42] (Tr.cycBad 0 3 1 4 [(5, -1), (23, 1), (28, 1), (34, 1), (43, 1), (53, -1), (55, -1), (77, -1)])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 35] (Tr.cycBad 0 3 1 4 [(0, 1), (5, -1), (13, 1), (23, 1), (28, -1), (39, -1), (81, -1)]), Tr.tab [28, 35] (Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 24, 27, 41, 7, 12, 13, 26] (Tr.chain 12 [60, 13, 53, 23, 67, 0] (Tr.closed)))), Tr.closed]), Tr.tab [34, 24] (Tr.branch 7 [Tr.closed, Tr.tab [41] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [42] (Tr.chain 87 [39, 71, 23, 38, 8] (Tr.tab [12, 26, 29, 35, 11, 13] (Tr.chain 62 [16, 34, 76, 5] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 3 [(8, -1), (13, 1), (16, 1), (43, 1), (55, -1), (89, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.chain 81 [0, 67, 38, 8] (Tr.tab [35] (Tr.cycBad 0 3 1 4 [(5, -1), (8, 1), (13, -1), (23, -1), (28, 1), (38, 1), (39, -1), (67, -1)]))), Tr.tab [26, 41, 14] (Tr.chain 81 [0, 67, 38, 8] (Tr.tab [35, 29] (Tr.cycBad 0 2 1 3 [(8, -1), (13, 1), (16, 1), (43, 1), (55, -1), (89, -1)]))), Tr.tab [28] (Tr.forced 46 [(0, 1), (5, 1), (8, -1), (13, 1), (23, 1), (39, 1), (55, -1), (79, 1)] (Tr.tab [12, 41] (Tr.chain 29 [55, 28, 46, 8, 38, 23] (Tr.closed)))), Tr.closed, Tr.closed]), Tr.tab [34, 36, 24] (Tr.parRel 3 4 5 [] [(0, 3, 1, 4, -1), (0, 5, 1, 3, 1)]), Tr.closed, Tr.closed, Tr.chain 46 [8, 78, 43, 55, 28] (Tr.tab [12, 41] (Tr.cycBad 0 3 1 4 [(0, 1), (13, 1), (23, 1), (46, -1), (55, -1), (78, 1)])), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23] (Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 31, 5, 44, 21] (Tr.forced 34 [(0, 1), (5, 1), (8, -1), (13, 1), (23, 1), (28, -1), (39, 1), (43, -1), (48, 1)] (Tr.tab [11] (Tr.assumed))), Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.tab [17, 27, 34, 22, 24] (Tr.forced 58 [(0, 1), (13, 1), (28, -1), (43, -1), (74, 1)] (Tr.tab [11, 21, 38] ((Tr.symm (0, 3, 4, 2, 1, 5) Tr.assumed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1171 : ∀ x ∈ ([(1188987758170341378, 954574990404202440874768365), (1189241139908059425, 151792057029709804678864606), (1190085547658322177, 151187003832251572815847166)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1170 (all_settles_cons settles_sub1169 (all_settles_cons settles_sub1168 all_settles_nil)))

theorem settles_sub1171 : Settles 1188959647743090689 151168077175154562462161610 :=
  settles_of_check hand_sub1171 (by decide +kernel :
    check [(1188987758170341378, 954574990404202440874768365), (1189241139908059425, 151792057029709804678864606), (1190085547658322177, 151187003832251572815847166)] 219 1188959647743090689 151168077175154562462161610 tree_sub1171 = true)

/-- Subtree rooted at `(37227342137393296, 1109774307026879561019684463)`: 43 nodes (branch 3, chain 3, closed 26, cyc 2, forced 1, tab 8). -/
def tree_sub1172 : Tr := Tr.branch 2 [Tr.closed, Tr.tab [16, 38, 8, 19] (Tr.chain 44 [8, 46, 11] (Tr.closed)), Tr.closed, Tr.tab [16, 34] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.tab [19, 40, 9, 14] (Tr.chain 24 [36, 27, 65, 29, 55, 28, 46] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 29, 9] (Tr.cycBad 0 1 3 4 [(4, -1), (27, -1), (41, 1), (55, 1), (85, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [16, 26] (Tr.forced 74 [(7, -1), (41, 1), (50, 1), (55, 1), (66, -1)] (Tr.tab [9, 34] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.tab [19, 40, 14] (Tr.chain 8 [66, 36, 27, 65, 29, 55, 28, 46] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19] (Tr.cycBad 0 1 3 4 [(4, -1), (7, 1), (27, -1), (50, -1), (66, 1), (74, 1), (85, -1)]), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]

theorem hand_sub1172 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1172 : Settles 37227342137393296 1109774307026879561019684463 :=
  settles_of_check hand_sub1172 (by decide +kernel :
    check [] 83 37227342137393296 1109774307026879561019684463 tree_sub1172 = true)

/-- Subtree rooted at `(4870093628215430283809, 566981296935486076476914910)`: 75 nodes (branch 5, chain 10, closed 44, cyc 2, tab 14). -/
def tree_sub1173 : Tr := Tr.branch 9 [Tr.closed, Tr.tab [43] (Tr.chain 12 [18, 57, 53, 23, 67, 0] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 2 [Tr.closed, Tr.tab [38, 24] (Tr.branch 14 [Tr.closed, Tr.tab [25, 43, 11] (Tr.chain 38 [8, 81, 0, 67] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.chain 62 [16, 89, 9, 80] (Tr.cycBad 0 3 1 5 [(0, 1), (8, 1), (9, 1), (16, -1), (18, 1), (25, -1), (46, -1), (53, 1), (57, -1), (62, 1), (80, -1), (89, 2)])), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [20, 34] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.cycBad 0 2 1 4 [(0, -1), (16, -1), (18, -1), (25, 1), (28, 1), (32, 1), (53, -1), (67, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 14] (Tr.chain 7 [72, 25, 58, 46, 59, 53, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 14] (Tr.chain 1 [85, 16, 65, 53, 57] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [31] (Tr.chain 65 [16, 48, 18, 57, 53] (Tr.tab [14, 24, 25, 43, 8, 11] (Tr.chain 73 [0, 81, 46, 28] (Tr.closed)))), Tr.tab [31, 38, 24] (Tr.chain 65 [16, 48, 18, 57, 53] (Tr.tab [14, 25, 43, 8, 11] (Tr.chain 38 [8, 81, 0, 67] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed]), Tr.tab [28, 43] (Tr.chain 12 [18, 57, 53, 23, 67, 0] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1173 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1173 : Settles 4870093628215430283809 566981296935486076476914910 :=
  settles_of_check hand_sub1173 (by decide +kernel :
    check [] 115 4870093628215430283809 566981296935486076476914910 tree_sub1173 = true)

/-- Subtree rooted at `(4725249355091693015072, 767567228685362732933836767)`: 19 nodes (branch 1, chain 2, closed 9, cyc 1, forced 1, tab 5). -/
def tree_sub1174 : Tr := Tr.branch 8 [Tr.closed, Tr.tab [18, 19] (Tr.forced 82 [(22, 1), (27, -1), (32, -1), (33, 1), (49, 1), (61, 1), (72, -1)] (Tr.tab [13, 27, 28, 37] (Tr.closed))), Tr.tab [19, 40, 9] (Tr.chain 0 [61, 29, 59, 28, 42, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 26, 33] (Tr.cycBad 2 4 3 5 [(5, -1), (12, -1), (27, -1), (40, 1), (42, 1), (61, 1), (68, -1), (72, -1)]), Tr.tab [18, 19, 26, 33, 9, 27, 38, 13] (Tr.chain 4 [74, 5, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1174 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1174 : Settles 4725249355091693015072 767567228685362732933836767 :=
  settles_of_check hand_sub1174 (by decide +kernel :
    check [] 59 4725249355091693015072 767567228685362732933836767 tree_sub1174 = true)

/-- Subtree rooted at `(2882872222048325664, 1077056960873190671311695839)`: 35 nodes (branch 2, chain 6, closed 18, cyc 1, tab 8). -/
def tree_sub1175 : Tr := Tr.branch 8 [Tr.closed, Tr.tab [19] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.chain 82 [19, 49, 74, 5] (Tr.tab [37] (Tr.cycBad 0 3 1 2 [(19, 1), (22, 1), (27, -1), (32, -1), (33, 1), (49, 1), (82, -1)]))), Tr.closed, Tr.tab [28] (Tr.chain 64 [40, 27, 61, 80, 5] (Tr.tab [12, 38, 13] (Tr.chain 14 [32, 22, 59, 47] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [19, 40, 9] (Tr.chain 0 [61, 29, 59, 28, 42, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 26, 33, 9, 27] (Tr.chain 6 [49, 74, 68, 42, 12] (Tr.closed)), Tr.tab [19, 26, 33, 9, 27] (Tr.chain 6 [49, 74, 68, 42, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1175 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1175 : Settles 2882872222048325664 1077056960873190671311695839 :=
  settles_of_check hand_sub1175 (by decide +kernel :
    check [] 75 2882872222048325664 1077056960873190671311695839 tree_sub1175 = true)

end DistinctCircumradii

#print axioms DistinctCircumradii.settles_sub1151
#print axioms DistinctCircumradii.settles_sub1152
#print axioms DistinctCircumradii.settles_sub1153
#print axioms DistinctCircumradii.settles_sub1154
#print axioms DistinctCircumradii.settles_sub1155
#print axioms DistinctCircumradii.settles_sub1156
#print axioms DistinctCircumradii.settles_sub1157
#print axioms DistinctCircumradii.settles_sub1158
#print axioms DistinctCircumradii.settles_sub1159
#print axioms DistinctCircumradii.settles_sub1160
#print axioms DistinctCircumradii.settles_sub1161
#print axioms DistinctCircumradii.settles_sub1162
#print axioms DistinctCircumradii.settles_sub1163
#print axioms DistinctCircumradii.settles_sub1164
#print axioms DistinctCircumradii.settles_sub1165
#print axioms DistinctCircumradii.settles_sub1166
#print axioms DistinctCircumradii.settles_sub1167
#print axioms DistinctCircumradii.settles_sub1168
#print axioms DistinctCircumradii.settles_sub1169
#print axioms DistinctCircumradii.settles_sub1170
#print axioms DistinctCircumradii.settles_sub1171
#print axioms DistinctCircumradii.settles_sub1172
#print axioms DistinctCircumradii.settles_sub1173
#print axioms DistinctCircumradii.settles_sub1174
#print axioms DistinctCircumradii.settles_sub1175
