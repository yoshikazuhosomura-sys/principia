import Principia.DistinctCircumradii.Census.Tree352

/-!
# `CensusComplete`: subtrees 1301-1325

The transcripts of the subtrees, checked by the kernel.  Each theorem
discharges the nodes it hands on with the theorems of the deeper subtrees,
which come earlier in this chain of files.
-/

namespace DistinctCircumradii

/-- Subtree rooted at `(4724744735866675527841, 610500452968403215285485406)`: 16 nodes (branch 1, chain 2, closed 8, cyc 2, tab 3). -/
def tree_sub1301 : Tr := Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [42, 14] (Tr.chain 34 [25, 72, 7, 39, 89] (Tr.cycBad 0 1 2 3 [(0, 1), (34, 1), (39, -1), (46, -1), (53, 1), (89, 1)])), Tr.closed, Tr.closed, Tr.tab [28, 9, 11] (Tr.chain 89 [39, 7, 72, 25, 34] (Tr.tab [14] (Tr.cycBad 0 1 2 3 [(0, -3), (5, 1), (7, -2), (23, -1), (25, 2), (28, 2), (34, -2), (39, 3), (46, 1), (56, 1), (61, 1), (72, -2), (82, -2), (89, -3)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1301 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1301 : Settles 4724744735866675527841 610500452968403215285485406 :=
  settles_of_check hand_sub1301 (by decide +kernel :
    check [] 56 4724744735866675527841 610500452968403215285485406 tree_sub1301 = true)

/-- Subtree rooted at `(1189653989604466721, 412657476662311935201434334)`: 101 nodes (branch 8, chain 7, closed 69, cyc 4, tab 13). -/
def tree_sub1302 : Tr := Tr.branch 8 [Tr.closed, Tr.tab [25, 41] (Tr.cycBad 0 5 1 3 [(0, 1), (5, 1), (13, 1), (22, -1), (29, 1), (55, -1), (60, 1)]), Tr.closed, Tr.tab [25, 34, 38, 2, 12, 24, 35] (Tr.chain 2 [62, 5, 64] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 29, 31] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.tab [40] (Tr.branch 14 [Tr.tab [24, 34, 7] (Tr.chain 1 [55, 29, 59, 52] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 27, 41, 7, 10, 16] (Tr.cycBad 0 3 1 2 [(5, 1), (29, 1), (33, 1), (47, -1), (49, 1), (55, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 7 [Tr.tab [16, 24] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 41] (Tr.branch 10 [Tr.cycBad 0 3 1 2 [(5, 1), (29, 1), (33, 1), (47, -1), (49, 1), (55, -1)], Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.chain 2 [85, 55, 29, 47, 58] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [35, 2] (Tr.chain 14 [32, 85, 55, 29, 47] (Tr.closed)), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28, 40] (Tr.branch 11 [Tr.closed, Tr.cycBad 0 1 2 3 [(0, 1), (5, -1), (10, 1), (29, -2), (40, -2), (47, 2), (55, 1), (60, -1), (70, -1), (83, 1)], Tr.closed, Tr.chain 2 [85, 55, 29, 47, 58] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [24, 41, 14, 28, 40, 11, 38] (Tr.chain 2 [85, 55, 29, 47, 58] (Tr.closed)), Tr.closed, Tr.tab [24, 34, 14] (Tr.chain 4 [56, 85, 55, 29, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1302 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1302 : Settles 1189653989604466721 412657476662311935201434334 :=
  settles_of_check hand_sub1302 (by decide +kernel :
    check [] 141 1189653989604466721 412657476662311935201434334 tree_sub1302 = true)

/-- Subtree rooted at `(1188968479022120968, 226292812007122802537511927)`: 16 nodes (branch 1, chain 2, closed 9, cyc 1, tab 3). -/
def tree_sub1303 : Tr := Tr.branch 4 [Tr.closed, Tr.tab [17, 19, 38, 9, 29, 13] (Tr.chain 28 [55, 3, 82, 35] (Tr.closed)), Tr.tab [19, 36, 39, 7, 11, 38, 13] (Tr.chain 28 [55, 3, 82, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 28, 7, 43] (Tr.cycBad 0 4 2 5 [(10, 1), (22, -1), (24, -1), (30, 1), (78, -1)]), Tr.closed, Tr.closed]

theorem hand_sub1303 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1303 : Settles 1188968479022120968 226292812007122802537511927 :=
  settles_of_check hand_sub1303 (by decide +kernel :
    check [] 56 1188968479022120968 226292812007122802537511927 tree_sub1303 = true)

/-- Subtree rooted at `(41939780125335616, 229374599359670856033492911)`: 118 nodes (branch 9, chain 3, closed 74, cyc 8, forced 3, tab 21). -/
def tree_sub1304 : Tr := Tr.branch 11 [Tr.closed, Tr.tab [21] (Tr.branch 13 [Tr.closed, Tr.tab [43, 4] (Tr.cycBad 0 3 1 2 [(20, 1), (33, 1), (47, -1), (48, -1), (50, 1), (52, -1), (55, -1), (78, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 14 [Tr.tab [24, 34, 7, 9, 19] (Tr.chain 1 [55, 29, 59, 52] (Tr.closed)), Tr.tab [24] (Tr.cycBad 0 2 4 5 [(13, -1), (20, 1), (33, 1), (65, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 39, 14, 43] (Tr.cycBad 0 2 4 5 [(13, -1), (20, 1), (33, 1), (48, -1), (50, 1), (52, -1), (65, -1)]), Tr.closed, Tr.closed, Tr.tab [32] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 0 1 2 4 [(13, 1), (48, -1), (52, -1), (58, -1), (65, 1), (67, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.forced 29 [(6, -1), (13, 1), (33, -1), (52, 1), (89, -1)] (Tr.forced 43 [(6, 1), (13, -1), (48, 1), (55, 1), (67, -1), (89, 1)] (Tr.closed))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 4 [Tr.tab [43] (Tr.branch 13 [Tr.tab [44, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 39, 14] (Tr.cycBad 0 2 4 5 [(13, -1), (20, 1), (33, 1), (48, -1), (50, 1), (52, -1), (65, -1)]), Tr.closed, Tr.closed, Tr.tab [32] (Tr.cycBad 0 2 1 3 [(20, 1), (33, 1), (41, -1), (48, -1), (50, 1), (52, -2), (55, -1), (67, 1), (81, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.chain 74 [4, 88, 13, 50] (Tr.tab [34, 24, 14] (Tr.cycBad 0 2 4 5 [(13, -1), (20, 1), (33, 1), (65, -1)]))), Tr.tab [29, 44, 14, 24] (Tr.chain 74 [4, 88, 13, 50] (Tr.cycBad 0 2 4 5 [(13, -1), (20, 1), (33, 1), (65, -1)])), Tr.closed]), Tr.closed, Tr.closed, Tr.tab [21, 34, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 39, 9, 14, 29, 43] (Tr.closed), Tr.closed, Tr.closed, Tr.tab [32, 9] (Tr.forced 43 [(29, -1), (33, -1), (50, 1), (55, 1), (67, -1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1304 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1304 : Settles 41939780125335616 229374599359670856033492911 :=
  settles_of_check hand_sub1304 (by decide +kernel :
    check [] 158 41939780125335616 229374599359670856033492911 tree_sub1304 = true)

/-- Subtree rooted at `(4875133122116264689728, 923614451052454573209763727)`: 23 nodes (branch 2, closed 16, cyc 3, tab 2). -/
def tree_sub1305 : Tr := Tr.branch 4 [Tr.tab [15, 5] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 1 5 [(4, 1), (15, 1), (24, 1), (29, -1), (40, -1), (52, 1), (82, -1)], Tr.closed, Tr.cycBad 0 1 2 5 [(24, -1), (31, 1), (40, -1), (59, 1), (67, -1), (88, 1)], Tr.closed, Tr.closed]), Tr.tab [38, 5] (Tr.cycBad 0 1 2 4 [(5, 2), (14, -1), (15, 2), (24, 1), (40, -1), (45, -1), (52, 1), (59, 1), (62, -1), (67, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1305 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1305 : Settles 4875133122116264689728 923614451052454573209763727 :=
  settles_of_check hand_sub1305 (by decide +kernel :
    check [] 63 4875133122116264689728 923614451052454573209763727 tree_sub1305 = true)

/-- Subtree rooted at `(4724817637408868925448, 306965033688824087739677623)`: 36 nodes (branch 3, closed 26, cyc 2, tab 5). -/
def tree_sub1306 : Tr := Tr.branch 0 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 4 [Tr.closed, Tr.tab [17, 38, 7, 24, 27, 43] (Tr.closed), Tr.tab [36] (Tr.branch 7 [Tr.tab [43] (Tr.cycBad 1 4 2 5 [(10, -1), (32, 1), (50, -1), (57, 1), (61, -1), (72, 1)]), Tr.tab [17] (Tr.cycBad 0 3 1 4 [(16, -1), (25, 1), (28, 1), (32, 1), (50, -1), (61, -1), (72, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [16, 36, 4, 7] (Tr.closed), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1306 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1306 : Settles 4724817637408868925448 306965033688824087739677623 :=
  settles_of_check hand_sub1306 (by decide +kernel :
    check [] 76 4724817637408868925448 306965033688824087739677623 tree_sub1306 = true)

/-- Subtree rooted at `(1225682786624479236, 413252211508694754110949307)`: 191 nodes (branch 15, chain 7, closed 125, cyc 7, forced 3, leaf 4, tab 30). -/
def tree_sub1307 : Tr := Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 36, 25] (Tr.branch 0 [Tr.closed, Tr.closed, Tr.tab [17, 35, 40, 6, 10, 20, 24] (Tr.chain 3 [29, 47, 69, 12, 60, 13] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [17, 21, 31] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [24, 39] (Tr.chain 33 [13, 60, 36, 21] (Tr.tab [20] (Tr.branch 10 [Tr.branch 12 [Tr.closed, Tr.closed, Tr.tab [40, 14] (Tr.cycBad 0 2 1 3 [(2, 1), (29, 1), (33, 1), (49, 1), (52, -2), (56, -2), (60, 1), (69, 1), (77, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.forced 77 [(2, -1), (13, 1), (20, 1), (21, -1), (33, -1), (36, -2), (56, 1), (60, 1), (87, -1)] (Tr.tab [14] (Tr.branch 8 [Tr.cycBad 1 5 2 3 [(2, -1), (11, 1), (13, 2), (20, 1), (21, -2), (29, 1), (33, -2), (36, -4), (49, 1), (56, 1), (60, 2), (77, -2), (87, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 3 1 5 [(20, 1), (29, 1), (36, -1), (49, 1), (60, 1), (68, -1), (77, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35, 12, 14] (Tr.closed), Tr.closed]))), Tr.tab [24, 33, 44, 8, 14, 29, 12] (Tr.chain 1 [55, 29, 59, 52] (Tr.closed)), Tr.tab [24, 33, 39, 44, 8, 14, 29, 12] (Tr.chain 1 [55, 29, 59, 52] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28, 35, 17] (Tr.chain 6 [49, 56, 2, 81] (Tr.tab [36, 25] (Tr.branch 0 [Tr.closed, Tr.branch 10 [Tr.tab [20] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.forced 89 [(6, -1), (13, 1), (29, -1), (33, -1), (52, 1)] (Tr.tab [14, 29, 39] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 33, 44] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24] (Tr.branch 8 [Tr.leaf (4, 3, 0, 1, 5, 2), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 5, 4, 2, 1, 3), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed])), Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 3 1 5 [(2, 1), (13, -1), (20, 1), (29, 1), (33, 1), (47, -1), (49, 1), (56, -1), (70, -1), (81, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [40] (Tr.branch 12 [Tr.tab [44, 24] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [39, 14] (Tr.cycBad 0 2 1 5 [(6, 1), (13, 1), (21, -1), (39, -1), (47, -1), (49, -1), (60, 1), (77, 1), (81, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 31, 8, 14] (Tr.leaf (0, 1, 5, 3, 4, 2)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.forced 11 [(2, -1), (6, 1), (13, -1), (20, 1), (39, 1), (49, -1), (56, 1), (70, -1)] (Tr.tab [44, 24] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [39, 14] (Tr.cycBad 0 2 1 5 [(2, 3), (6, -2), (11, 7), (13, 8), (20, -7), (21, -1), (39, -8), (47, -1), (49, 2), (56, -3), (60, 1), (70, 7), (77, 1), (81, -5)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 31, 14] (Tr.leaf (3, 0, 4, 5, 2, 1)), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 31, 10, 20] (Tr.chain 21 [36, 60, 13, 33] (Tr.tab [39] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [24, 14] (Tr.cycBad 0 1 4 5 [(6, 1), (13, -1), (33, 1), (36, 1), (47, -1), (49, -1), (77, 1)]), Tr.closed, Tr.tab [24, 33, 44, 8, 14] (Tr.chain 4 [56, 85, 55, 29, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]

theorem hand_sub1307 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1307 : Settles 1225682786624479236 413252211508694754110949307 :=
  settles_of_check hand_sub1307 (by decide +kernel :
    check [] 231 1225682786624479236 413252211508694754110949307 tree_sub1307 = true)

/-- Subtree rooted at `(4870085746989331710464, 306967803006278153386261999)`: 14 nodes (branch 1, chain 1, closed 9, cyc 1, tab 2). -/
def tree_sub1308 : Tr := Tr.branch 4 [Tr.tab [43, 9, 27, 38, 13, 24] (Tr.chain 5 [74, 4, 76] (Tr.closed)), Tr.closed, Tr.tab [36] (Tr.cycBad 0 1 2 3 [(9, -1), (16, 1), (25, -1), (46, -1), (50, 1), (72, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1308 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1308 : Settles 4870085746989331710464 306967803006278153386261999 :=
  settles_of_check hand_sub1308 (by decide +kernel :
    check [] 54 4870085746989331710464 306967803006278153386261999 tree_sub1308 = true)

/-- Subtree rooted at `(1197966863984771136, 424786137387870589982586811)`: 16 nodes (branch 1, chain 1, closed 7, cyc 3, tab 4). -/
def tree_sub1309 : Tr := Tr.branch 2 [Tr.tab [19, 41] (Tr.cycBad 0 1 2 4 [(2, 1), (6, -1), (23, -1), (26, 1), (39, -1)]), Tr.closed, Tr.tab [19, 35, 8] (Tr.chain 64 [24, 60, 26] (Tr.tab [12, 25, 34, 24] (Tr.cycBad 0 3 1 4 [(6, 1), (14, -1), (23, 1), (26, 1), (34, 1), (53, -1), (64, -1)]))), Tr.closed, Tr.closed, Tr.tab [19, 31] (Tr.cycBad 0 1 2 3 [(23, -1), (26, 1), (34, 1), (39, -1), (48, -1), (60, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1309 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1309 : Settles 1197966863984771136 424786137387870589982586811 :=
  settles_of_check hand_sub1309 (by decide +kernel :
    check [] 56 1197966863984771136 424786137387870589982586811 tree_sub1309 = true)

/-- Subtree rooted at `(1189513801872445440, 419873215756528727216349915)`: 219 nodes (assumed 2, branch 16, chain 13, closed 132, cyc 9, forced 2, leaf 2, symm 2, tab 41). -/
def tree_sub1310 : Tr := Tr.branch 5 [Tr.tab [15, 44, 21] (Tr.branch 2 [Tr.closed, Tr.tab [16, 23, 38, 25] (Tr.branch 11 [Tr.tab [43] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 8 [Tr.closed, Tr.tab [19, 41] (Tr.cycBad 0 5 2 4 [(5, -1), (22, 1), (29, -1), (34, 1), (39, -1), (55, 1), (60, -1), (76, -1)]), Tr.tab [19, 39, 7, 14, 24] (Tr.forced 87 [(5, -1), (8, 1), (12, -1), (28, -1), (39, -1), (59, -1), (76, 1)] (Tr.tab [12] (Tr.leaf (0, 4, 1, 3, 2, 5)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 29, 31, 7, 14] (Tr.chain 3 [55, 85, 56, 49, 19] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [37] (Tr.chain 74 [49, 19, 82, 5] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 12 [Tr.closed, Tr.tab [22, 41] (Tr.cycBad 0 3 1 2 [(5, 1), (29, 1), (39, 1), (46, -1), (49, 1), (55, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 0 5 1 4 [(5, -1), (8, 1), (29, -1), (39, -1), (55, 1), (60, -1), (69, -1), (87, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [20, 23, 34, 24, 25] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.forced 74 [(5, 1), (29, 1), (32, -1), (49, 1), (58, 1), (60, 1)] (Tr.closed)), Tr.closed, Tr.tab [26] (Tr.branch 12 [Tr.closed, Tr.tab [22, 41] (Tr.cycBad 0 3 1 2 [(5, 1), (29, 1), (39, 1), (46, -1), (49, 1), (55, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 8 [Tr.closed, Tr.tab [19, 41, 14, 43, 7] (Tr.cycBad 0 1 2 3 [(5, -1), (19, 1), (29, -1), (39, -1), (49, -1), (55, 1), (65, 1), (87, -1)]), Tr.tab [19, 7] (Tr.chain 59 [28, 55, 29] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [23, 31, 39, 11, 19] (Tr.chain 16 [48, 12, 51] (Tr.closed)), Tr.tab [16, 23, 31, 38, 39, 7, 11, 19, 24, 25, 8, 14, 41] (Tr.chain 3 [29, 59, 22, 56, 49, 19] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [22, 34, 25] (Tr.branch 13 [Tr.tab [21, 41, 44, 11, 23, 24, 2, 16] (Tr.cycBad 0 1 2 4 [(19, 1), (29, 1), (41, 1), (44, -1), (60, 1)]), Tr.closed, Tr.closed, Tr.tab [21, 27, 38] (Tr.branch 11 [Tr.tab [20, 23, 43] (Tr.branch 2 [Tr.tab [41] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 89 [39, 70, 76, 34] (Tr.tab [29, 39, 19, 8, 44, 24, 7] (Tr.leaf (1, 2, 5, 4, 0, 3))), Tr.closed, Tr.tab [29, 14, 24, 44, 7, 8, 19] (Tr.chain 33 [19, 49, 56, 2, 87, 39] (Tr.closed)), Tr.closed, Tr.closed]), Tr.tab [16] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 89 [39, 70, 76, 34] (Tr.tab [29, 39, 19, 8] (Tr.cycBad 0 4 1 2 [(8, 1), (22, -1), (29, 1), (55, -1), (60, 1), (89, 1)])), Tr.closed, Tr.tab [29, 14, 24, 7] (Tr.chain 28 [55, 29, 59] (Tr.tab [8, 19] (Tr.cycBad 0 2 1 3 [(8, 2), (12, -1), (27, 1), (28, -2), (29, 2), (34, 1), (39, -1), (44, -2), (49, 2), (56, -2), (59, -1), (60, 2), (76, 2), (87, -1)]))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [23, 31, 39, 2, 19] (Tr.chain 16 [48, 12, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [23, 26] (Tr.chain 26 [60, 12, 69, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [21, 37] (Tr.branch 12 [Tr.tab [20, 44, 24] (Tr.branch 8 [Tr.closed, Tr.tab [19, 41] (Tr.chain 56 [22, 35, 82, 19, 49] (Tr.closed)), Tr.tab [19, 39, 7, 23] (Tr.chain 3 [55, 28, 35, 82] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 29, 31, 7, 16, 23, 43, 2, 14] (Tr.cycBad 0 2 1 3 [(12, 1), (19, 2), (29, 1), (35, -1), (44, -1), (49, -1), (60, 1), (77, 2), (82, -2), (85, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] ((Tr.symm (3, 4, 5, 1, 0, 2) Tr.assumed)), Tr.tab [20, 29, 44, 24] ((Tr.symm (4, 3, 1, 5, 0, 2) Tr.assumed)), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1310 : ∀ x ∈ ([(1197966863984771136, 424786137387870589982586811), (4870085746989331710464, 306967803006278153386261999)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1309 (all_settles_cons settles_sub1308 all_settles_nil))

theorem settles_sub1310 : Settles 1189513801872445440 419873215756528727216349915 :=
  settles_of_check hand_sub1310 (by decide +kernel :
    check [(1197966863984771136, 424786137387870589982586811), (4870085746989331710464, 306967803006278153386261999)] 259 1189513801872445440 419873215756528727216349915 tree_sub1310 = true)

/-- Subtree rooted at `(19101637265460952317956, 1199235311420446680356173307)`: 26 nodes (branch 2, chain 4, closed 19, tab 1). -/
def tree_sub1311 : Tr := Tr.branch 6 [Tr.tab [16, 8] (Tr.chain 15 [85, 2, 64, 26, 37, 9] (Tr.closed)), Tr.branch 8 [Tr.chain 30 [54, 18, 52, 11, 74, 67] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 9 [37, 26, 64, 2, 85, 15] (Tr.closed), Tr.chain 9 [37, 26, 64, 2, 85, 15] (Tr.closed), Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1311 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1311 : Settles 19101637265460952317956 1199235311420446680356173307 :=
  settles_of_check hand_sub1311 (by decide +kernel :
    check [] 66 19101637265460952317956 1199235311420446680356173307 tree_sub1311 = true)

/-- Subtree rooted at `(199354656821608448, 1157448888793678706386189295)`: 226 nodes (assumed 1, branch 17, chain 14, closed 147, cyc 4, forced 6, leaf 2, symm 1, tab 34). -/
def tree_sub1312 : Tr := Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.tab [23] (Tr.branch 4 [Tr.forced 16 [(4, 1), (21, 1), (46, -1), (51, 1), (54, -1), (55, 1), (57, -1), (65, 1)] (Tr.tab [7, 17] (Tr.branch 7 [Tr.closed, Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 13] (Tr.chain 20 [32, 16, 65, 41] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.chain 58 [46, 28, 55, 86, 4] (Tr.closed), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [32, 9, 27, 13] (Tr.chain 20 [32, 16, 65, 41] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed])), Tr.tab [17, 38, 13] (Tr.forced 86 [(21, 1), (28, -1), (32, -1), (41, 1), (50, 1), (55, 1)] (Tr.tab [9, 32, 7] (Tr.leaf (5, 4, 3, 1, 2, 0)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 7 [Tr.closed, Tr.tab [17] (Tr.branch 4 [Tr.tab [23] (Tr.forced 51 [(4, -1), (16, 1), (18, 1), (19, -1), (46, 1), (54, 1), (55, -1), (57, 1), (65, -1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 32, 9, 13, 27] (Tr.chain 7 [50, 74, 49, 19, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 4 [Tr.tab [23] (Tr.branch 13 [Tr.tab [44] (Tr.cycBad 1 5 2 3 [(4, -1), (21, -1), (32, 1), (41, -1), (46, 1), (50, -1), (54, 1), (55, -1), (57, 1)]), Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 0 1 3 5 [(4, 1), (19, 1), (32, -1), (54, 1), (65, 1), (69, 1), (76, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 23, 38, 13] (Tr.chain 0 [79, 32, 14, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 32, 13] (Tr.chain 10 [49, 19, 53, 65] (Tr.closed)), Tr.tab [17, 23, 32, 38, 9, 13] (Tr.chain 0 [79, 32, 14, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28] (Tr.branch 7 [Tr.closed, Tr.tab [17] (Tr.branch 4 [Tr.tab [23] (Tr.forced 51 [(4, -1), (16, 1), (18, 1), (19, -1), (46, 1), (54, 1), (55, -1), (57, 1), (65, -1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 32, 9, 13, 27] (Tr.chain 7 [50, 74, 49, 19, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [32, 23] (Tr.branch 4 [Tr.forced 76 [(4, 1), (19, 1), (32, -1), (54, 1), (55, -1), (57, 1), (65, 1), (67, 1)] (Tr.tab [13, 27, 9] (Tr.leaf (5, 2, 0, 4, 3, 1))), Tr.tab [17, 38, 9, 13] (Tr.cycBad 0 1 2 3 [(14, -1), (19, -1), (21, 2), (28, 1), (32, 1), (41, 2), (46, -2), (50, 1), (54, -7), (55, 6), (57, -6), (65, -1), (67, -2), (74, 1), (81, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 32, 4, 9, 23, 27, 13] (Tr.chain 20 [32, 16, 65, 41] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [26, 42, 23] (Tr.branch 4 [Tr.tab [43] (Tr.branch 7 [Tr.closed, Tr.tab [17] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 13] (Tr.cycBad 0 3 1 2 [(16, 1), (18, 1), (28, -1), (32, -1), (46, 1), (50, 1), (54, 3), (55, -2), (57, 2), (74, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.chain 58 [46, 28, 55, 86, 4] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 11] (Tr.branch 13 [Tr.tab [44] (Tr.chain 20 [32, 79, 21, 71, 41] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 9 [Tr.chain 44 [32, 79, 21, 71, 17] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 35 [76, 4, 86, 55, 28] (Tr.closed), Tr.chain 35 [76, 4, 86, 55, 28] (Tr.closed), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [17, 38, 13] (Tr.forced 86 [(21, 1), (28, -1), (32, -1), (41, 1), (50, 1), (55, 1)] (Tr.tab [9] ((Tr.symm (5, 4, 3, 1, 2, 0) Tr.assumed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1312 : ∀ x ∈ ([(19101637265460952317956, 1199235311420446680356173307)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1311 all_settles_nil)

theorem settles_sub1312 : Settles 199354656821608448 1157448888793678706386189295 :=
  settles_of_check hand_sub1312 (by decide +kernel :
    check [(19101637265460952317956, 1199235311420446680356173307)] 266 199354656821608448 1157448888793678706386189295 tree_sub1312 = true)

/-- Subtree rooted at `(4888396486901145538560, 608084752032200264695803391)`: 41 nodes (branch 3, chain 2, closed 24, cyc 4, tab 8). -/
def tree_sub1313 : Tr := Tr.branch 6 [Tr.tab [18] (Tr.branch 9 [Tr.tab [44] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [25, 39, 14] (Tr.cycBad 0 1 2 3 [(9, -3), (12, 1), (17, -3), (22, 2), (31, 1), (40, 2), (44, -2), (45, -4), (53, -2), (64, 1), (67, -1), (72, 2), (83, 1)]), Tr.tab [25] (Tr.cycBad 1 4 2 3 [(22, -1), (31, 1), (48, -1), (57, -1), (64, 1)]), Tr.tab [25, 39, 14] (Tr.cycBad 0 1 2 3 [(12, -1), (17, -1), (22, 1), (25, 1), (31, -1), (44, 1), (45, -1), (57, 1), (64, -1), (83, -1)]), Tr.tab [25, 14] (Tr.chain 2 [48, 12, 63, 53, 65, 40] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.cycBad 1 3 4 5 [(9, -1), (25, -1), (31, 1), (53, -1), (67, -1), (72, -1), (80, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [18, 39, 43, 9, 25, 10, 24, 14, 28] (Tr.chain 0 [21, 83, 22, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1313 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1313 : Settles 4888396486901145538560 608084752032200264695803391 :=
  settles_of_check hand_sub1313 (by decide +kernel :
    check [] 81 4888396486901145538560 608084752032200264695803391 tree_sub1313 = true)

/-- Subtree rooted at `(4888396486898998055040, 608084752140286657900179327)`: 14 nodes (branch 1, chain 1, closed 9, cyc 1, tab 2). -/
def tree_sub1314 : Tr := Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [25, 39, 6, 18, 24, 33, 9, 14] (Tr.cycBad 0 2 1 3 [(7, -5), (12, 2), (17, -15), (22, 5), (25, 8), (40, 5), (44, 3), (45, -10), (48, -7), (53, -5), (64, 2), (67, -3), (72, 7), (83, -5)]), Tr.closed, Tr.closed, Tr.tab [25, 43, 14, 18, 6, 33, 9] (Tr.chain 2 [48, 12, 63, 53, 65, 40] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1314 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1314 : Settles 4888396486898998055040 608084752140286657900179327 :=
  settles_of_check hand_sub1314 (by decide +kernel :
    check [] 54 4888396486898998055040 608084752140286657900179327 tree_sub1314 = true)

/-- Subtree rooted at `(4724960838004999589896, 759045695595879414161600375)`: 50 nodes (branch 4, chain 2, closed 34, cyc 3, tab 7). -/
def tree_sub1315 : Tr := Tr.branch 1 [Tr.closed, Tr.tab [37] (Tr.branch 10 [Tr.closed, Tr.tab [40, 23, 5, 18] (Tr.cycBad 0 2 1 3 [(17, 1), (39, 1), (48, 1), (58, -1), (72, -1)]), Tr.cycBad 0 2 1 4 [(3, 1), (17, 1), (45, 1), (48, 1), (58, -1), (72, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [20, 33, 23] (Tr.branch 5 [Tr.closed, Tr.tab [18, 8, 25, 43, 14] (Tr.chain 0 [27, 65, 17, 62, 48, 12] (Tr.closed)), Tr.tab [37] (Tr.branch 8 [Tr.closed, Tr.tab [25, 41, 12, 29, 13, 22, 10, 40, 14] (Tr.cycBad 0 2 1 3 [(12, 1), (22, 1), (26, -1), (27, 1), (39, -3), (47, -4), (48, 1), (58, 3), (61, -1), (71, 4), (87, -3)]), Tr.closed, Tr.tab [25, 43, 13, 14, 29, 12, 22, 10, 40] (Tr.chain 0 [27, 65, 17, 62, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1315 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1315 : Settles 4724960838004999589896 759045695595879414161600375 :=
  settles_of_check hand_sub1315 (by decide +kernel :
    check [] 90 4724960838004999589896 759045695595879414161600375 tree_sub1315 = true)

/-- Subtree rooted at `(2594390319794098176, 1073372311650409436677533693)`: 25 nodes (branch 2, chain 1, closed 17, cyc 2, tab 3). -/
def tree_sub1316 : Tr := Tr.branch 1 [Tr.cycBad 0 3 1 5 [(1, 1), (17, 1), (19, 1), (27, -1), (58, -1)], Tr.closed, Tr.closed, Tr.tab [20, 33] (Tr.branch 8 [Tr.closed, Tr.tab [25, 41, 12, 22, 13, 42, 14] (Tr.cycBad 0 1 2 3 [(12, -1), (19, 1), (26, 1), (27, -1), (38, -1), (45, -2), (53, -1), (58, 1), (61, 1), (87, -2)]), Tr.closed, Tr.tab [25, 43, 13, 14, 22, 12] (Tr.chain 0 [27, 65, 17, 62, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1316 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1316 : Settles 2594390319794098176 1073372311650409436677533693 :=
  settles_of_check hand_sub1316 (by decide +kernel :
    check [] 65 2594390319794098176 1073372311650409436677533693 tree_sub1316 = true)

/-- Subtree rooted at `(1189513801335706624, 420475355014971317898570747)`: 89 nodes (branch 7, chain 3, closed 60, cyc 4, forced 1, tab 14). -/
def tree_sub1317 : Tr := Tr.branch 2 [Tr.tab [23, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 25] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.tab [19] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 23, 13, 37] (Tr.cycBad 0 1 2 3 [(2, -1), (19, 1), (28, 1), (49, -1), (58, 1), (60, 1), (82, -1)]), Tr.closed, Tr.tab [23, 42, 13] (Tr.chain 6 [19, 53, 17, 50, 60, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 12 [Tr.cycBad 0 3 1 4 [(2, 1), (10, 1), (17, -1), (35, -1), (39, -1), (49, 1), (55, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 37, 14] (Tr.forced 44 [(2, 1), (12, 1), (58, -1), (77, 1), (85, 1)] (Tr.tab [5, 22, 23] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.cycBad 1 2 4 5 [(10, -1), (17, 1), (55, 1), (60, -1), (69, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [20, 23, 34, 25] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.tab [19, 23, 37] (Tr.branch 8 [Tr.closed, Tr.tab [41, 12, 29, 14, 26, 11, 38, 13] (Tr.cycBad 0 1 2 3 [(12, -1), (19, 1), (22, -1), (26, 1), (39, -1), (49, -1), (58, 1), (60, 1), (87, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 12, 22, 41, 13, 14, 26, 38] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [23, 42, 13] (Tr.chain 6 [19, 53, 17, 50, 60, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [23, 31, 39, 11] (Tr.chain 6 [49, 10, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1317 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1317 : Settles 1189513801335706624 420475355014971317898570747 :=
  settles_of_check hand_sub1317 (by decide +kernel :
    check [] 129 1189513801335706624 420475355014971317898570747 tree_sub1317 = true)

/-- Subtree rooted at `(40536794764673280, 538138858112249744755912430)`: 239 nodes (assumed 5, branch 18, chain 10, closed 148, cyc 10, forced 1, symm 5, tab 42). -/
def tree_sub1318 : Tr := Tr.branch 9 [Tr.tab [44, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.cycBad 0 4 1 3 [(8, 1), (17, -1), (19, -1), (27, 1), (42, 1), (55, -1)]), Tr.closed, Tr.closed, Tr.tab [26, 32] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 11 [Tr.closed, Tr.tab [21, 23, 13, 27] (Tr.chain 44 [8, 40, 65, 17] (Tr.closed)), Tr.tab [23, 39, 42] (Tr.chain 6 [19, 53, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 28, 35, 13] (Tr.cycBad 0 5 1 2 [(8, 1), (17, -1), (19, -1), (42, 1), (55, -1), (65, -1), (76, 1), (81, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.cycBad 0 4 1 2 [(8, 1), (17, -1), (19, -1), (42, 1), (55, -1), (89, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 39, 42, 11, 28] (Tr.chain 6 [19, 53, 65, 51] (Tr.closed)), Tr.tab [23, 27] (Tr.forced 12 [(8, 1), (17, -1), (19, -1), (42, 1), (55, -1), (65, -1), (76, 1)] (Tr.tab [0, 24, 35, 10, 20, 28] (Tr.cycBad 0 3 1 5 [(8, 1), (17, -1), (19, -1), (33, -1), (42, 1), (79, -1)]))), Tr.tab [23, 27, 39, 42, 10, 11, 24, 28, 0] (Tr.chain 0 [79, 22, 52, 57, 53, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [26, 42, 23] (Tr.cycBad 0 4 1 5 [(8, 1), (17, -1), (19, -1), (42, 1), (71, -1), (79, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.cycBad 0 4 1 2 [(8, 1), (17, -1), (19, -1), (42, 1), (55, -1), (89, 1)]), Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [27, 34, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.branch 13 [Tr.tab [21] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 5 3 4 [(8, 1), (19, -1), (22, -1), (26, 1), (27, 1), (42, -1), (52, -1), (65, -1), (69, -1), (74, 1)], Tr.closed, Tr.tab [28, 35] (Tr.branch 0 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [20, 24, 32, 4] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 10] (Tr.chain 1 [42, 54, 19, 57] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [26, 42] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 30, 0] (Tr.chain 1 [42, 54, 19, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 35, 0, 11] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [43, 14, 26, 42] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [32] (Tr.branch 0 [Tr.closed, Tr.closed, Tr.tab [24, 35] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 10] (Tr.chain 1 [42, 54, 19, 57] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28, 30, 11, 24, 10, 35, 0] (Tr.cycBad 0 2 1 4 [(8, 1), (22, 1), (26, 1), (27, 1), (30, -2), (40, -1), (42, 1), (71, -1), (74, -1), (78, 2)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [26, 32] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 13 [Tr.tab [21, 23, 11, 28, 35, 4, 15, 0, 24, 10] (Tr.chain 1 [42, 54, 19, 57] (Tr.closed)), Tr.closed, Tr.tab [23, 39, 42, 11] (Tr.chain 6 [19, 53, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.cycBad 0 4 1 5 [(8, 1), (19, -1), (42, 1), (74, -1), (89, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.branch 13 [Tr.tab [21, 23] (Tr.branch 14 [Tr.closed, Tr.tab [43] ((Tr.symm (5, 4, 2, 1, 3, 0) Tr.assumed)), Tr.tab [26, 42] ((Tr.symm (5, 4, 2, 1, 3, 0) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 1 5 [(8, 1), (19, -1), (42, 1), (74, -1), (89, 1)], Tr.closed, Tr.closed]), Tr.tab [23, 43] ((Tr.symm (4, 5, 2, 0, 3, 1) Tr.assumed)), Tr.tab [23, 39, 42, 11, 14, 28, 4] (Tr.chain 6 [19, 53, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 32] ((Tr.symm (4, 2, 5, 0, 1, 3) Tr.assumed)), Tr.tab [29, 32, 44, 24] ((Tr.symm (4, 5, 2, 0, 3, 1) Tr.assumed)), Tr.closed]

theorem hand_sub1318 : ∀ x ∈ ([(1189513801335706624, 420475355014971317898570747), (2594390319794098176, 1073372311650409436677533693), (4724960838004999589896, 759045695595879414161600375), (4888396486898998055040, 608084752140286657900179327), (4888396486901145538560, 608084752032200264695803391)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1317 (all_settles_cons settles_sub1316 (all_settles_cons settles_sub1315 (all_settles_cons settles_sub1314 (all_settles_cons settles_sub1313 all_settles_nil)))))

theorem settles_sub1318 : Settles 40536794764673280 538138858112249744755912430 :=
  settles_of_check hand_sub1318 (by decide +kernel :
    check [(1189513801335706624, 420475355014971317898570747), (2594390319794098176, 1073372311650409436677533693), (4724960838004999589896, 759045695595879414161600375), (4888396486898998055040, 608084752140286657900179327), (4888396486901145538560, 608084752032200264695803391)] 279 40536794764673280 538138858112249744755912430 tree_sub1318 = true)

/-- Subtree rooted at `(40536794764148992, 228649116701005788495604390)`: 188 nodes (assumed 6, branch 14, chain 11, closed 113, cyc 7, leaf 1, symm 5, tab 31). -/
def tree_sub1319 : Tr := Tr.branch 3 [Tr.tab [15, 22, 42, 19, 23] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 34, 24] (Tr.branch 9 [Tr.branch 10 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 0, 16] (Tr.chain 1 [55, 3, 57] (Tr.closed)), Tr.closed, Tr.tab [24, 25, 36, 16] (Tr.chain 12 [42, 55, 3, 63] (Tr.tab [35, 11, 20, 43, 13] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 1 3 4 [(3, 1), (12, -1), (34, -1), (38, 1), (52, -1), (55, -1), (63, 1), (71, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 4, 1, 2, 5, 3), Tr.closed, Tr.cycBad 1 2 4 5 [(3, 2), (8, 2), (12, -2), (17, -3), (26, -3), (34, -3), (38, 1), (42, 2), (55, -2), (76, 3), (79, -1), (89, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed]))), Tr.closed, Tr.tab [24, 27, 35] (Tr.branch 0 [Tr.closed, Tr.tab [16, 36, 43, 7] (Tr.closed), Tr.closed, Tr.tab [16, 20, 32, 11, 26, 36, 13, 43, 14, 39, 7] (Tr.chain 0 [79, 22, 52, 75] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 32] (Tr.chain 24 [42, 55, 86, 38, 8] (Tr.closed)), Tr.tab [29, 32] (Tr.chain 24 [42, 55, 86, 38, 8] (Tr.closed)), Tr.closed]), Tr.closed, Tr.tab [32] (Tr.branch 9 [Tr.tab [44, 24] (Tr.branch 0 [Tr.closed, Tr.tab [16, 24, 36, 43, 7, 10, 27, 35, 11] (Tr.chain 2 [22, 52, 75, 6, 49, 10, 40] (Tr.closed)), Tr.tab [16, 24, 35, 10, 25, 36] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 14] (Tr.cycBad 0 1 2 5 [(12, -1), (26, 1), (42, 1), (49, -1), (71, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 11 [Tr.tab [43, 13] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.cycBad 0 1 2 5 [(12, -1), (26, 1), (42, 1), (49, -1), (71, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 1 2 4 [(8, -1), (12, 1), (22, 1), (42, -1), (49, 1), (52, -1), (55, 1), (79, -1), (89, -1)], Tr.closed, Tr.closed]), Tr.cycBad 0 4 1 5 [(3, 1), (8, 1), (26, -1), (40, -1), (49, 1), (79, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [16, 24, 10] (Tr.chain 1 [55, 3, 57] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [27, 34, 24] (Tr.branch 0 [Tr.closed, Tr.tab [16, 24, 36, 43, 7, 10, 35, 11, 21] (Tr.chain 2 [22, 52, 75, 6, 49, 10, 40] (Tr.closed)), Tr.tab [16, 24, 35, 10, 25, 36] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 14] (Tr.cycBad 0 1 2 5 [(12, -1), (26, 1), (42, 1), (49, -1), (71, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, (Tr.symm (1, 3, 0, 4, 2, 5) Tr.assumed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [16, 24, 10] (Tr.chain 1 [55, 3, 57] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [30, 24] ((Tr.symm (0, 1, 3, 2, 5, 4) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [22, 36, 16, 19] (Tr.assumed), Tr.closed, Tr.closed, Tr.tab [22, 32, 39, 10, 23] (Tr.chain 54 [42, 55, 43] (Tr.tab [0, 16, 24, 30] ((Tr.symm (1, 0, 2, 3, 4, 5) Tr.assumed)))), Tr.closed, Tr.tab [22, 27, 30, 24] ((Tr.symm (4, 2, 5, 0, 1, 3) Tr.assumed)), Tr.tab [15, 22, 27, 30, 42, 19, 23, 24, 10, 25, 36, 16] (Tr.chain 12 [42, 55, 3, 63] (Tr.tab [35] ((Tr.symm (1, 0, 2, 3, 4, 5) Tr.assumed)))), Tr.closed]

theorem hand_sub1319 : ∀ x ∈ ([(40536794764673280, 538138858112249744755912430), (199354656821608448, 1157448888793678706386189295), (1189513801872445440, 419873215756528727216349915), (1225682786624479236, 413252211508694754110949307), (4724817637408868925448, 306965033688824087739677623), (4875133122116264689728, 923614451052454573209763727)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1318 (all_settles_cons settles_sub1312 (all_settles_cons settles_sub1310 (all_settles_cons settles_sub1307 (all_settles_cons settles_sub1306 (all_settles_cons settles_sub1305 all_settles_nil))))))

theorem settles_sub1319 : Settles 40536794764148992 228649116701005788495604390 :=
  settles_of_check hand_sub1319 (by decide +kernel :
    check [(40536794764673280, 538138858112249744755912430), (199354656821608448, 1157448888793678706386189295), (1189513801872445440, 419873215756528727216349915), (1225682786624479236, 413252211508694754110949307), (4724817637408868925448, 306965033688824087739677623), (4875133122116264689728, 923614451052454573209763727)] 228 40536794764148992 228649116701005788495604390 tree_sub1319 = true)

/-- Subtree rooted at `(1189266962317316096, 1000438613029484228516293583)`: 61 nodes (branch 4, chain 6, closed 32, cyc 5, tab 14). -/
def tree_sub1320 : Tr := Tr.branch 5 [Tr.tab [15, 18, 44] (Tr.branch 4 [Tr.closed, Tr.tab [17, 38, 41, 7, 11, 19, 24] (Tr.chain 32 [14, 69, 12, 48] (Tr.closed)), Tr.closed, Tr.tab [17, 21, 34, 24] (Tr.cycBad 2 5 3 4 [(5, -1), (12, -1), (19, 1), (28, -1), (38, 1), (45, -1), (48, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 28] (Tr.cycBad 1 2 4 5 [(19, 1), (45, -1), (48, -1), (78, 1)]), Tr.closed, Tr.closed]), Tr.tab [18, 38, 43, 9, 17, 19, 22, 7, 24, 34, 44, 4, 14, 28, 13] (Tr.chain 0 [30, 19, 53, 23, 56, 48, 12] (Tr.closed)), Tr.closed, Tr.tab [18, 22, 34] (Tr.branch 4 [Tr.tab [17, 43] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 24, 42, 9] (Tr.chain 59 [28, 55, 29] (Tr.closed)), Tr.tab [19, 24, 44, 9, 14] (Tr.chain 9 [86, 56, 48, 12, 45] (Tr.closed)), Tr.tab [19, 24, 42, 44, 9, 14] (Tr.chain 69 [12, 48, 56, 4] (Tr.tab [26, 12] (Tr.cycBad 0 3 4 5 [(4, 1), (12, -1), (19, 1), (28, -1), (29, 1), (56, -1), (60, 1), (69, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 38, 41, 7, 11, 19, 24, 9] (Tr.chain 32 [14, 69, 12, 48] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 28] (Tr.cycBad 1 2 4 5 [(19, 1), (45, -1), (48, -1), (78, 1)]), Tr.tab [17, 28, 43] (Tr.cycBad 1 2 4 5 [(19, 1), (45, -1), (48, -1), (78, 1)]), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1320 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1320 : Settles 1189266962317316096 1000438613029484228516293583 :=
  settles_of_check hand_sub1320 (by decide +kernel :
    check [] 101 1189266962317316096 1000438613029484228516293583 tree_sub1320 = true)

/-- Subtree rooted at `(36319351556808768, 277824876472445772088661919)`: 146 nodes (branch 11, chain 9, closed 95, cyc 5, forced 2, tab 24). -/
def tree_sub1321 : Tr := Tr.branch 9 [Tr.closed, Tr.tab [18, 43] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 40, 11, 20, 23, 44, 5, 8, 12] (Tr.chain 4 [38, 84, 13, 33, 83, 35, 76] (Tr.closed)), Tr.closed, Tr.tab [39] (Tr.cycBad 1 4 2 5 [(23, -1), (38, 1), (48, -1), (89, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 5 [Tr.tab [23, 44, 20] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.cycBad 0 1 2 3 [(5, 1), (6, 1), (18, -1), (33, 1), (43, -1), (48, 1), (58, -1), (88, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 14, 41] (Tr.cycBad 0 2 1 4 [(13, 1), (18, -1), (23, 1), (48, 1), (55, -1), (77, -1), (81, -1), (88, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 40, 12, 14, 20, 41] (Tr.chain 16 [48, 18, 52, 77] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 18] (Tr.branch 11 [Tr.tab [20, 43, 44, 12, 23, 5] (Tr.chain 77 [34, 76, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [20, 28] (Tr.branch 14 [Tr.closed, Tr.tab [25] (Tr.chain 40 [81, 6, 43, 29, 65] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39, 19] (Tr.forced 50 [(6, 1), (13, -1), (29, 1), (33, 1), (48, 1), (89, 1)] (Tr.tab [5, 23, 12] (Tr.chain 22 [48, 18, 52] (Tr.closed)))), Tr.closed, Tr.closed]), Tr.tab [20, 28, 43, 44, 12, 14, 23, 39, 5, 19, 8] (Tr.chain 4 [38, 84, 13, 33, 89, 34] (Tr.closed)), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.forced 70 [(6, 1), (13, -1), (29, 1), (33, 1), (88, 1)] (Tr.tab [12, 20, 23] (Tr.branch 5 [Tr.tab [18, 44] (Tr.chain 62 [48, 18, 70, 5] (Tr.tab [25] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [19] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 1 2 3 [(6, -2), (13, 3), (29, -3), (33, -2), (43, -1), (58, -1), (62, 1), (70, 2), (88, -2)], Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 14, 41, 7] (Tr.cycBad 0 3 1 2 [(6, 1), (13, -1), (48, 1), (55, 1), (62, -1), (67, -1), (77, 1)]), Tr.closed, Tr.closed]), Tr.tab [19, 40, 7, 14, 41] (Tr.chain 0 [27, 77, 28, 55, 43, 6] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.tab [18, 41, 8, 19, 7] (Tr.chain 32 [20, 70, 18, 48] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1321 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1321 : Settles 36319351556808768 277824876472445772088661919 :=
  settles_of_check hand_sub1321 (by decide +kernel :
    check [] 186 36319351556808768 277824876472445772088661919 tree_sub1321 = true)

/-- Subtree rooted at `(36319076679049280, 277900434624242908806094783)`: 37 nodes (branch 3, chain 3, closed 27, forced 1, leaf 1, tab 2). -/
def tree_sub1322 : Tr := Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 39, 8, 25, 34, 22, 13, 29, 5, 23, 40, 12, 14, 20, 41, 11] (Tr.chain 7 [50, 62, 48, 18] (Tr.closed)), Tr.closed, Tr.closed, Tr.forced 89 [(6, -1), (13, 1), (43, 1), (48, -1), (55, -1), (67, 1)] (Tr.tab [14, 29, 13, 22, 34, 43, 5, 8, 20, 23] (Tr.branch 11 [Tr.closed, Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.chain 26 [13, 33, 89, 40, 64] (Tr.closed), Tr.closed, Tr.leaf (2, 0, 1, 5, 4, 3), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 46 [81, 6, 43, 55, 28] (Tr.closed), Tr.closed, Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1322 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1322 : Settles 36319076679049280 277900434624242908806094783 :=
  settles_of_check hand_sub1322 (by decide +kernel :
    check [] 77 36319076679049280 277900434624242908806094783 tree_sub1322 = true)

/-- Subtree rooted at `(36319076678901824, 277503754902930661663348623)`: 222 nodes (assumed 3, branch 15, chain 20, closed 118, cyc 13, forced 5, parrel 2, symm 1, tab 45). -/
def tree_sub1323 : Tr := Tr.branch 4 [Tr.tab [15, 17, 43, 20, 22] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.branch 11 [Tr.closed, Tr.tab [21, 41] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 18] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 40, 12, 19] (Tr.chain 22 [48, 18, 52] (Tr.closed)), Tr.closed, Tr.tab [23, 12] (Tr.chain 56 [48, 18, 70, 76, 4] (Tr.tab [7, 24, 34, 44, 8, 14, 19, 39] (Tr.cycBad 0 1 2 3 [(6, 1), (13, -1), (18, -1), (27, -1), (28, 1), (29, -1), (33, 1), (48, 1), (55, -7), (56, 7), (59, -8), (70, -1), (76, 1), (84, -1)]))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.forced 70 [(6, 1), (13, -1), (29, 1), (33, 1), (88, 1)] (Tr.tab [12, 23, 5, 18, 8, 19] (Tr.chain 32 [20, 70, 18, 48] (Tr.closed)))), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 38] (Tr.branch 13 [Tr.branch 5 [Tr.closed, Tr.tab [18, 23, 41, 8, 12, 19, 7] (Tr.chain 1 [55, 29, 41, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [18, 23, 40, 12, 19] (Tr.chain 22 [48, 18, 52] (Tr.closed)), Tr.tab [18, 23, 40, 41, 8, 12, 19, 7] (Tr.chain 78 [43, 29, 41, 20] (Tr.closed)), Tr.tab [18, 23] (Tr.forced 16 [(18, -1), (33, 1), (41, 1), (43, 1), (84, -1)] (Tr.tab [7, 19, 41] (Tr.branch 7 [Tr.closed, Tr.branch 8 [Tr.cycBad 0 2 1 3 [(4, -1), (11, 1), (13, 1), (16, 1), (18, 1), (43, -1), (58, -1), (84, 1)], Tr.closed, Tr.closed, Tr.tab [25] (Tr.cycBad 0 1 2 3 [(13, 1), (29, -1), (43, -1), (58, -1), (62, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 5 [(4, 1), (33, 1), (43, 1), (55, -1), (58, -1), (67, 1), (84, -1)], Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 0 2 4 5 [(4, 1), (6, 1), (13, -1), (33, 1), (58, -1), (88, 1)]), Tr.tab [29] (Tr.cycBad 0 2 4 5 [(4, 1), (6, 1), (13, -1), (33, 1), (58, -1), (88, 1)]), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 5 [Tr.closed, Tr.tab [18, 23, 38, 41, 8, 12, 19] (Tr.chain 32 [20, 70, 18, 48] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [18, 23, 40, 12, 19] (Tr.chain 22 [48, 18, 52] (Tr.closed)), Tr.tab [18, 23, 38, 40, 41, 8, 12, 19] (Tr.forced 67 [(29, -1), (33, -1), (43, -1), (48, 1), (52, 1), (55, 1)] (Tr.tab [7, 24] (Tr.forced 89 [(6, -1), (13, 1), (43, 1), (48, -2), (50, 1), (52, -1), (55, -1), (67, 1)] (Tr.tab [14, 29, 13] (Tr.chain 8 [20, 41, 29, 43, 6, 81] (Tr.closed)))))), Tr.tab [18, 23, 29] (Tr.branch 13 [Tr.tab [44, 24] (Tr.chain 64 [81, 6, 43, 29, 41] (Tr.tab [12, 25] (Tr.cycBad 0 3 1 5 [(4, 1), (6, 1), (13, -1), (41, -1), (48, 1), (81, -1), (84, -1)]))), Tr.closed, Tr.closed, Tr.tab [27, 38] (Tr.branch 12 [Tr.closed, Tr.chain 28 [55, 43, 6, 81, 46] (Tr.tab [8, 19, 39, 7] (Tr.chain 59 [28, 55, 29] (Tr.tab [14, 24, 34] (Tr.chain 70 [18, 48, 56, 4, 76] (Tr.closed))))), Tr.closed, Tr.closed, Tr.closed, Tr.chain 56 [48, 18, 70, 76, 4] (Tr.tab [7, 24, 34, 44, 8, 14, 19, 39] (Tr.chain 46 [81, 6, 43, 29, 59] (Tr.closed))), Tr.chain 28 [55, 43, 6, 81, 46] (Tr.tab [8, 19, 39, 7] (Tr.chain 56 [48, 18, 70, 76, 4] (Tr.tab [24, 34, 14] (Tr.cycBad 0 1 2 3 [(13, -1), (28, 1), (29, -1), (33, 1), (46, 1), (48, 1), (55, -1), (56, 1), (59, -2), (70, -1), (81, 1), (84, -1)])))), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed], Tr.tab [27, 34, 24] (Tr.branch 8 [Tr.tab [18] (Tr.cycBad 0 5 1 2 [(4, 1), (11, -1), (43, 1), (55, -1)]), Tr.tab [18, 38, 41, 5] (Tr.chain 52 [18, 48, 22] (Tr.tab [12, 23, 40] (Tr.chain 88 [13, 50, 74, 4] (Tr.tab [29, 14] (Tr.cycBad 0 2 4 5 [(4, -1), (20, 1), (33, 1), (48, -1), (52, -1), (65, -1), (74, 1), (88, -1)]))))), Tr.tab [18, 19, 40, 23, 5, 29, 13, 21] (Tr.forced 16 [(18, -1), (33, 1), (41, 1), (43, 1), (84, -1)] (Tr.branch 7 [Tr.closed, Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.cycBad 0 2 1 5 [(6, 1), (13, 1), (16, 2), (18, 1), (28, -1), (33, -1), (41, -1), (43, -2), (58, -2), (74, 1), (84, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.chain 46 [81, 6, 43, 55, 28] (Tr.tab [12] (Tr.cycBad 0 1 2 3 [(6, -2), (28, 2), (33, 1), (41, 2), (43, 3), (48, -1), (55, -1), (74, -2), (81, 3), (84, 1)])), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 5 [(4, 2), (6, -1), (13, -1), (16, 1), (18, 2), (28, 1), (41, -2), (43, 1), (55, -2), (67, 2), (74, -1)], Tr.closed, Tr.closed, Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [27, 34, 24] (Tr.parRel 1 3 5 [] [(0, 3, 1, 4, -1), (0, 5, 3, 4, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 38, 44, 9, 18, 24] (Tr.assumed), Tr.closed, Tr.tab [17, 21, 34, 22, 24] (Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 28, 30] ((Tr.symm (1, 3, 0, 4, 2, 5) Tr.assumed)), Tr.tab [15, 17, 28, 30, 43, 20, 22] (Tr.parRel 0 4 5 [] [(0, 3, 1, 4, 1), (0, 1, 3, 5, 1)]), Tr.closed]

theorem hand_sub1323 : ∀ x ∈ ([(36319076679049280, 277900434624242908806094783), (36319351556808768, 277824876472445772088661919), (1189266962317316096, 1000438613029484228516293583)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1322 (all_settles_cons settles_sub1321 (all_settles_cons settles_sub1320 all_settles_nil)))

theorem settles_sub1323 : Settles 36319076678901824 277503754902930661663348623 :=
  settles_of_check hand_sub1323 (by decide +kernel :
    check [(36319076679049280, 277900434624242908806094783), (36319351556808768, 277824876472445772088661919), (1189266962317316096, 1000438613029484228516293583)] 262 36319076678901824 277503754902930661663348623 tree_sub1323 = true)

/-- Subtree rooted at `(18315664737435912, 451935920919159315835287159)`: 40 nodes (branch 3, chain 1, closed 26, cyc 2, forced 1, tab 7). -/
def tree_sub1324 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 37, 16, 24] (Tr.branch 8 [Tr.closed, Tr.tab [18, 39, 41, 1, 6, 7, 14, 28, 40, 21, 11] (Tr.chain 4 [67, 21, 83, 22, 48, 54, 25] (Tr.closed)), Tr.tab [18, 40] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 32, 7, 41, 14, 21, 39, 10, 35, 1, 11] (Tr.cycBad 0 2 1 5 [(16, 1), (34, -1), (41, -1), (44, 1), (61, -1), (70, -1), (75, 1)]), Tr.closed, Tr.tab [27, 14, 39] (Tr.cycBad 1 2 3 5 [(28, 1), (54, -1), (70, -1), (73, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29, 35] (Tr.forced 55 [(3, 1), (23, -1), (44, 1), (48, -1), (54, 1), (87, 1)] (Tr.tab [6, 24, 33, 37] (Tr.closed))), Tr.closed, Tr.closed]

theorem hand_sub1324 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1324 : Settles 18315664737435912 451935920919159315835287159 :=
  settles_of_check hand_sub1324 (by decide +kernel :
    check [] 80 18315664737435912 451935920919159315835287159 tree_sub1324 = true)

/-- Subtree rooted at `(18315664737435656, 451935902112127271936096119)`: 151 nodes (branch 10, chain 13, closed 85, cyc 6, forced 6, tab 31). -/
def tree_sub1325 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 38, 24] (Tr.branch 7 [Tr.closed, Tr.tab [17, 41, 18, 21] (Tr.chain 34 [25, 54, 48, 16] (Tr.branch 11 [Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 33, 37, 1, 10] (Tr.chain 1 [55, 3, 57] (Tr.closed)), Tr.closed, Tr.tab [24] (Tr.forced 81 [(23, 1), (44, -1), (48, 1), (54, -1), (61, 1)] (Tr.closed)), Tr.closed, Tr.tab [24, 27, 10, 39] (Tr.cycBad 0 4 1 2 [(16, -2), (23, 1), (25, 2), (34, 2), (45, 1), (48, -1), (54, 1), (64, -1)]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 35] (Tr.forced 61 [(23, -1), (44, 1), (48, -1), (54, 1), (81, 1)] (Tr.tab [6, 24, 10, 39, 14, 26] (Tr.cycBad 0 4 1 2 [(16, -2), (23, 2), (25, 2), (34, 2), (44, -1), (45, 1), (61, 1), (64, -1), (81, -1)]))), Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.tab [32] (Tr.branch 1 [Tr.closed, Tr.tab [16, 37, 24] (Tr.branch 6 [Tr.closed, Tr.tab [18, 40, 8, 21, 26, 14] (Tr.chain 5 [68, 15, 71, 41] (Tr.closed)), Tr.tab [18, 39, 41, 8] (Tr.chain 71 [21, 67, 23] (Tr.tab [14, 26] (Tr.cycBad 0 5 1 3 [(3, -1), (7, 1), (21, -1), (22, 2), (23, -1), (25, -1), (48, 1), (54, -1), (64, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [18, 27] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.tab [26, 40, 14, 39, 10, 21, 11] (Tr.chain 1 [73, 67, 23, 41, 64, 40, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [26, 14] (Tr.chain 5 [68, 73, 67, 23, 41] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [18, 35] (Tr.branch 6 [Tr.closed, Tr.tab [24, 40, 10, 21, 39] (Tr.cycBad 0 2 1 3 [(3, -1), (15, 1), (23, 1), (48, 1), (54, -1), (64, -1)]), Tr.closed, Tr.tab [24, 33, 10, 21, 26] (Tr.chain 1 [55, 3, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 27] (Tr.cycBad 0 1 4 5 [(18, -1), (25, 1), (67, -1), (73, 1)]), Tr.closed, Tr.closed]), Tr.tab [33, 24, 26] (Tr.forced 89 [(3, 1), (23, -1), (25, 1), (31, -1), (44, 1), (48, -1), (54, 1)] (Tr.tab [14, 39, 18] (Tr.branch 6 [Tr.closed, Tr.tab [40, 8, 10, 21, 35, 11] (Tr.chain 16 [48, 54, 25, 34] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 10, 21, 11] (Tr.chain 1 [73, 67, 23, 41, 64, 40, 89, 39] (Tr.closed)), Tr.closed, Tr.closed]))), Tr.tab [18, 33, 35, 24, 26] (Tr.forced 89 [(3, 1), (23, -1), (25, 1), (31, -1), (44, 1), (48, -1), (54, 1)] (Tr.tab [14, 39, 10, 21, 40, 6, 11] (Tr.chain 1 [73, 67, 23, 41, 64, 40, 89, 39] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 32, 41, 18, 21] (Tr.chain 34 [25, 54, 48, 16] (Tr.cycBad 0 5 1 2 [(3, 1), (16, -1), (23, -1), (25, 1), (41, 1), (44, 1), (48, -1), (54, 1), (67, -1)])), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [26, 37, 24] (Tr.branch 1 [Tr.closed, Tr.closed, Tr.tab [18, 35] (Tr.chain 4 [23, 41, 70, 18, 54, 25] (Tr.closed)), Tr.forced 80 [(3, 1), (23, -1), (31, -1), (44, 1), (54, 1), (70, 1)] (Tr.closed), Tr.tab [18, 35] (Tr.chain 4 [23, 41, 70, 18, 54, 25] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29, 35] (Tr.forced 55 [(3, 1), (23, -1), (44, 1), (48, -1), (54, 1), (87, 1)] (Tr.tab [6, 24, 33, 37] (Tr.closed))), Tr.closed, Tr.closed]

theorem hand_sub1325 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1325 : Settles 18315664737435656 451935902112127271936096119 :=
  settles_of_check hand_sub1325 (by decide +kernel :
    check [] 191 18315664737435656 451935902112127271936096119 tree_sub1325 = true)

end DistinctCircumradii

#print axioms DistinctCircumradii.settles_sub1301
#print axioms DistinctCircumradii.settles_sub1302
#print axioms DistinctCircumradii.settles_sub1303
#print axioms DistinctCircumradii.settles_sub1304
#print axioms DistinctCircumradii.settles_sub1305
#print axioms DistinctCircumradii.settles_sub1306
#print axioms DistinctCircumradii.settles_sub1307
#print axioms DistinctCircumradii.settles_sub1308
#print axioms DistinctCircumradii.settles_sub1309
#print axioms DistinctCircumradii.settles_sub1310
#print axioms DistinctCircumradii.settles_sub1311
#print axioms DistinctCircumradii.settles_sub1312
#print axioms DistinctCircumradii.settles_sub1313
#print axioms DistinctCircumradii.settles_sub1314
#print axioms DistinctCircumradii.settles_sub1315
#print axioms DistinctCircumradii.settles_sub1316
#print axioms DistinctCircumradii.settles_sub1317
#print axioms DistinctCircumradii.settles_sub1318
#print axioms DistinctCircumradii.settles_sub1319
#print axioms DistinctCircumradii.settles_sub1320
#print axioms DistinctCircumradii.settles_sub1321
#print axioms DistinctCircumradii.settles_sub1322
#print axioms DistinctCircumradii.settles_sub1323
#print axioms DistinctCircumradii.settles_sub1324
#print axioms DistinctCircumradii.settles_sub1325
