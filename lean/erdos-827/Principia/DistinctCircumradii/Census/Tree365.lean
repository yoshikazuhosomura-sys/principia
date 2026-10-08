import Principia.DistinctCircumradii.Census.Tree364

/-!
# `CensusComplete`: subtrees 1601-1625

The transcripts of the subtrees, checked by the kernel.  Each theorem
discharges the nodes it hands on with the theorems of the deeper subtrees,
which come earlier in this chain of files.
-/

namespace DistinctCircumradii

/-- Subtree rooted at `(1227248491739234306, 835316937036674163109371389)`: 14 nodes (branch 1, chain 1, closed 9, cyc 1, tab 2). -/
def tree_sub1601 : Tr := Tr.branch 10 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 37, 12, 17, 44, 13, 29, 36, 3, 33] (Tr.chain 68 [1, 57, 88, 14, 44] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 0 5 1 4 [(14, 1), (22, -1), (24, -1), (30, 1), (51, -1), (60, -1), (75, -1)]), Tr.closed, Tr.closed]

theorem hand_sub1601 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1601 : Settles 1227248491739234306 835316937036674163109371389 :=
  settles_of_check hand_sub1601 (by decide +kernel :
    check [] 54 1227248491739234306 835316937036674163109371389 tree_sub1601 = true)

/-- Subtree rooted at `(1227248491739234304, 835316937023162814471413239)`: 84 nodes (branch 6, chain 6, closed 50, cyc 5, forced 1, tab 16). -/
def tree_sub1602 : Tr := Tr.branch 10 [Tr.closed, Tr.tab [21, 40, 23] (Tr.branch 12 [Tr.tab [44, 24] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 37, 17] (Tr.forced 86 [(22, -1), (35, 1), (51, 1), (60, 1), (82, 1)] (Tr.tab [9, 18] (Tr.chain 3 [86, 56, 22, 35, 82] (Tr.tab [3, 42, 6] (Tr.cycBad 0 4 1 2 [(3, 1), (22, 1), (24, 1), (56, -1), (82, -1), (86, 1)]))))), Tr.closed, Tr.tab [29, 36] (Tr.branch 3 [Tr.tab [17, 42] (Tr.chain 80 [3, 88, 14, 44] (Tr.cycBad 0 4 1 2 [(3, 1), (24, 1), (35, 1), (51, 1), (56, -1), (60, 1)])), Tr.tab [17, 9, 18] (Tr.chain 8 [14, 88, 13, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 37, 13, 29, 36] (Tr.branch 3 [Tr.tab [17, 42] (Tr.chain 80 [3, 88, 14, 44] (Tr.tab [33, 24, 14, 43, 18, 6] (Tr.cycBad 0 2 1 4 [(14, 1), (30, 1), (44, -1), (56, -1), (65, 1), (70, -1), (80, 1)]))), Tr.tab [17, 44, 9, 14, 18, 24] (Tr.chain 8 [14, 88, 13, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 37, 17] (Tr.branch 12 [Tr.tab [23, 44, 13, 29, 36] (Tr.cycBad 1 5 2 4 [(24, 1), (35, 1), (44, -1), (51, 1), (57, 1), (60, 1), (88, -1)]), Tr.closed, Tr.tab [23, 40, 42, 13, 14, 43, 18] (Tr.chain 10 [56, 22, 52, 57, 53, 65] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 0 5 1 4 [(14, 1), (22, -1), (24, -1), (30, 1), (51, -1), (60, -1), (75, -1)]), Tr.closed, Tr.closed]

theorem hand_sub1602 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1602 : Settles 1227248491739234304 835316937023162814471413239 :=
  settles_of_check hand_sub1602 (by decide +kernel :
    check [] 124 1227248491739234304 835316937023162814471413239 tree_sub1602 = true)

/-- Subtree rooted at `(37189904115179520, 847510107688851157416452095)`: 103 nodes (branch 8, chain 10, closed 68, cyc 4, forced 2, leaf 1, tab 10). -/
def tree_sub1603 : Tr := Tr.branch 11 [Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.forced 81 [(13, 1), (18, -1), (28, -1), (30, 1), (32, -1), (45, -1), (64, 1)] (Tr.closed)), Tr.closed, Tr.tab [26, 14, 27, 41] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 9, 17, 4] (Tr.chain 14 [78, 30, 27, 34] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 28] (Tr.chain 78 [30, 79, 32] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 64 [(13, -1), (18, 1), (28, 1), (30, -1), (32, 1), (45, 1), (81, 1)] (Tr.tab [12, 38] (Tr.branch 4 [Tr.closed, Tr.tab [17, 28, 44, 7, 9, 13] (Tr.closed), Tr.tab [17, 19, 28, 36, 7, 13, 41, 14] (Tr.chain 14 [32, 16, 34] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 28, 7, 19] (Tr.branch 9 [Tr.closed, Tr.branch 13 [Tr.chain 71 [45, 81, 64, 41] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.leaf (1, 0, 2, 5, 3, 4), Tr.closed, Tr.cycBad 0 2 1 4 [(18, 1), (28, 1), (30, -1), (32, 2), (34, -1), (41, -2), (45, -1), (50, -1), (55, -1), (71, -1), (77, 1), (78, 1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.chain 41 [64, 81, 45, 71] (Tr.closed), Tr.chain 3 [55, 28, 77, 34, 88] (Tr.closed), Tr.chain 3 [55, 28, 77, 34, 88] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.chain 71 [45, 81, 64, 41] (Tr.cycBad 0 2 1 3 [(32, 1), (55, -1), (64, -1), (71, 1), (88, 1)]), Tr.closed], Tr.closed, Tr.tab [27, 14] (Tr.chain 41 [64, 81, 45, 71] (Tr.cycBad 0 2 1 5 [(18, 1), (28, 1), (30, -1), (32, 2), (34, -1), (41, -1), (50, -1), (55, -1), (64, -1), (74, 1), (78, -1), (79, 1), (81, -1)])), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 13] (Tr.chain 71 [45, 81, 64, 41] (Tr.cycBad 0 1 2 3 [(28, 1), (32, 1), (50, -1), (55, -1), (64, -1), (71, 1), (81, 1), (86, 1)])), Tr.closed, Tr.closed]), Tr.closed, Tr.closed])), Tr.closed]

theorem hand_sub1603 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1603 : Settles 37189904115179520 847510107688851157416452095 :=
  settles_of_check hand_sub1603 (by decide +kernel :
    check [] 143 37189904115179520 847510107688851157416452095 tree_sub1603 = true)

/-- Subtree rooted at `(37189882640343296, 847509498297565885153074927)`: 210 nodes (branch 16, chain 12, closed 133, cyc 12, forced 2, tab 35). -/
def tree_sub1604 : Tr := Tr.branch 11 [Tr.closed, Tr.tab [21, 41, 22] (Tr.branch 12 [Tr.tab [44, 24] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [19, 42, 9, 14] (Tr.chain 20 [8, 40, 65, 29, 55, 28, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 28] (Tr.branch 4 [Tr.tab [43] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 13] (Tr.branch 14 [Tr.closed, Tr.cycBad 0 2 1 3 [(8, -1), (13, 1), (28, -1), (30, 1), (65, 1), (79, -1)], Tr.cycBad 0 1 4 5 [(4, -1), (8, 1), (30, -1), (40, -1), (55, 1), (71, -1), (74, 1), (79, -1), (88, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 13] (Tr.cycBad 0 1 2 3 [(8, 2), (28, 3), (30, -1), (35, 1), (40, -1), (45, -2), (50, -1), (55, -1), (76, -2), (86, 3)]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [36, 13, 27] (Tr.chain 22 [79, 30, 25, 76, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 14 [Tr.tab [24, 7] (Tr.chain 29 [55, 28, 59] (Tr.tab [9, 19] (Tr.chain 78 [30, 27, 40, 8] (Tr.cycBad 0 3 1 2 [(8, 1), (13, -1), (18, 2), (28, 2), (29, -1), (30, -2), (40, -1), (45, 1), (50, 1), (55, 2), (56, -1), (59, 2), (70, -1), (76, -1)])))), Tr.tab [24, 43] (Tr.cycBad 0 1 2 4 [(8, -1), (13, 1), (30, 1), (50, -1), (65, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 36] (Tr.cycBad 1 4 2 5 [(8, -1), (13, 1), (28, -1), (30, 1), (40, 1), (50, -1), (70, 1), (88, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 13 [Tr.tab [21, 22, 44, 12, 24, 26, 42, 14, 19] (Tr.chain 12 [18, 70, 41, 71, 45] (Tr.closed)), Tr.tab [22, 41, 43, 12] (Tr.chain 71 [45, 69, 47] (Tr.tab [14, 24, 26, 42, 19] (Tr.cycBad 0 3 1 2 [(8, 1), (13, -1), (18, 1), (28, 1), (30, -1), (47, -1), (50, 1), (69, 1), (70, -2), (71, 1)]))), Tr.closed, Tr.tab [22, 27] (Tr.branch 12 [Tr.tab [26, 44, 14, 24, 43] (Tr.chain 9 [55, 28, 35, 76, 69, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 42, 14, 19, 24] (Tr.chain 12 [18, 70, 76, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [21, 36, 41, 22, 13, 27] (Tr.branch 12 [Tr.tab [26, 44, 14, 24, 43] (Tr.chain 9 [55, 28, 35, 76, 69, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 42, 14, 19, 24, 7, 28, 4, 43, 9] (Tr.chain 1 [55, 86, 4, 76, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.branch 12 [Tr.tab [22, 44, 24] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 0 1 2 4 [(8, -1), (13, 1), (30, 1), (50, -1), (65, 1)]), Tr.tab [42, 19] (Tr.forced 62 [(18, -1), (28, -1), (30, 1), (71, 1), (76, 1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 36] (Tr.forced 16 [(8, 1), (18, -1), (45, -1), (81, -1), (88, 1)] (Tr.tab [7, 19, 28, 41] (Tr.branch 4 [Tr.tab [43, 9] (Tr.branch 14 [Tr.closed, Tr.cycBad 0 1 2 4 [(8, 1), (13, 1), (16, -2), (18, -2), (30, 1), (45, -2), (50, -1), (65, 1), (81, -2), (88, 2)], Tr.cycBad 0 2 1 3 [(4, -1), (8, 2), (13, 2), (16, -2), (18, -3), (28, -1), (30, 1), (45, -3), (50, -1), (55, -1), (71, 1), (74, 1), (81, -3), (88, 2)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [34, 9, 43, 14] (Tr.cycBad 0 2 1 3 [(13, 1), (16, 1), (18, 1), (23, 1), (28, -1), (35, 1), (38, -3), (45, -1), (50, 2), (55, 1), (71, -2), (81, -2)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]), Tr.tab [22, 41, 43, 13] (Tr.chain 9 [55, 28, 46, 81, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 26] (Tr.cycBad 0 4 1 3 [(13, 1), (18, -1), (28, -1), (30, 1), (45, -1), (55, -1), (70, 1), (81, -1)]), Tr.tab [22, 26, 41, 43, 13, 14, 24, 34, 7, 28, 4, 19, 9] (Tr.chain 0 [30, 25, 47, 59, 46, 81] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]

theorem hand_sub1604 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1604 : Settles 37189882640343296 847509498297565885153074927 :=
  settles_of_check hand_sub1604 (by decide +kernel :
    check [] 250 37189882640343296 847509498297565885153074927 tree_sub1604 = true)

/-- Subtree rooted at `(37189882640343040, 847509405775615118978620139)`: 181 nodes (assumed 5, branch 14, chain 6, closed 112, cyc 9, forced 1, leaf 1, symm 3, tab 30). -/
def tree_sub1605 : Tr := Tr.branch 2 [Tr.tab [15, 20, 41, 22] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 38, 17] (Tr.branch 12 [Tr.tab [44, 13, 29, 36] (Tr.chain 62 [2, 58, 88, 13, 50] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.forced 41 [(13, -1), (18, 1), (28, 1), (58, 1), (70, -1)] (Tr.tab [21] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [19, 36] (Tr.chain 79 [30, 25, 58, 2] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 2, 1, 3, 4, 5), Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 3 1 2 [(13, -3), (18, 3), (25, 1), (28, 2), (30, -1), (41, -2), (45, 1), (50, 1), (55, 1), (58, 2), (70, -3), (86, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.tab [27] (Tr.cycBad 0 1 2 5 [(2, -1), (13, 1), (18, -1), (25, -1), (28, -1), (30, 2), (45, -1), (50, -1), (70, 1), (77, 1), (79, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [43, 14, 27, 9] (Tr.cycBad 0 3 1 2 [(2, 2), (10, 2), (13, -4), (18, 4), (25, 3), (28, 5), (30, -3), (41, -3), (45, 1), (50, 1), (55, -1), (58, 1), (70, -4), (77, -2), (79, 2), (86, 1)]), Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.cycBad 0 3 2 4 [(13, 1), (18, -1), (30, 1), (45, -1), (50, -1), (55, -1), (70, 1), (78, 1)]), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [36] (Tr.branch 13 [Tr.tab [21, 44, 17, 24, 4, 28] (Tr.cycBad 1 3 2 4 [(2, 1), (41, -1), (45, -1), (55, -1), (69, 1), (78, 1)]), Tr.closed, Tr.closed, Tr.tab [27, 38, 17] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [34, 24] (Tr.branch 12 [Tr.tab [26, 14, 43] (Tr.chain 9 [55, 28, 35, 76, 69, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 42, 14, 19] (Tr.chain 12 [18, 70, 76, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 12 [Tr.tab [26, 44, 14, 24, 43, 7, 19, 9] (Tr.chain 0 [27, 65, 29, 55, 28, 35, 76, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 42, 14, 19, 24, 7, 43, 9] (Tr.chain 12 [18, 70, 76, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.branch 12 [Tr.tab [44, 24] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 17] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 1 3 2 5 [(2, 1), (13, -1), (18, 1), (28, 1), (30, -1), (35, 1), (50, 1), (65, -1), (76, -1), (81, 1)]), Tr.tab [42, 19] (Tr.cycBad 1 3 2 4 [(2, 1), (13, -1), (18, 1), (28, 1), (30, -1), (50, 1), (71, -1), (76, -1), (81, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 36] ((Tr.symm (1, 3, 0, 5, 4, 2) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [25, 38] (Tr.cycBad 0 1 2 4 [(2, -1), (13, 1), (18, -1), (30, 1), (45, -1), (50, -1), (64, 1), (81, -1)]), Tr.closed, Tr.tab [26] (Tr.cycBad 0 4 1 3 [(13, 1), (18, -1), (28, -1), (30, 1), (45, -1), (55, -1), (70, 1), (81, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.tab [16, 20, 38, 17] (Tr.assumed), Tr.closed, Tr.tab [20, 34, 43, 11, 22, 24] (Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [20, 26, 30] ((Tr.symm (0, 1, 2, 3, 5, 4) Tr.assumed)), Tr.tab [15, 20, 26, 30, 41, 22] ((Tr.symm (0, 1, 2, 3, 5, 4) Tr.assumed)), Tr.closed]

theorem hand_sub1605 : ∀ x ∈ ([(37189882640343296, 847509498297565885153074927), (37189904115179520, 847510107688851157416452095), (1227248491739234304, 835316937023162814471413239), (1227248491739234306, 835316937036674163109371389), (4727559133517583516672, 923613998674738112348781566)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1604 (all_settles_cons settles_sub1603 (all_settles_cons settles_sub1602 (all_settles_cons settles_sub1601 (all_settles_cons settles_sub1600 all_settles_nil)))))

theorem settles_sub1605 : Settles 37189882640343040 847509405775615118978620139 :=
  settles_of_check hand_sub1605 (by decide +kernel :
    check [(37189882640343296, 847509498297565885153074927), (37189904115179520, 847510107688851157416452095), (1227248491739234304, 835316937023162814471413239), (1227248491739234306, 835316937036674163109371389), (4727559133517583516672, 923613998674738112348781566)] 221 37189882640343040 847509405775615118978620139 tree_sub1605 = true)

/-- Subtree rooted at `(4888423508497026646145, 614129381814855731605536638)`: 14 nodes (branch 1, chain 1, closed 9, cyc 1, tab 2). -/
def tree_sub1606 : Tr := Tr.branch 10 [Tr.tab [25, 42, 13, 14] (Tr.cycBad 0 1 2 3 [(0, 1), (17, 1), (25, -1), (48, 1), (64, -1), (72, -1), (82, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 14] (Tr.chain 5 [17, 65, 40, 64] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1606 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1606 : Settles 4888423508497026646145 614129381814855731605536638 :=
  settles_of_check hand_sub1606 (by decide +kernel :
    check [] 54 4888423508497026646145 614129381814855731605536638 tree_sub1606 = true)

/-- Subtree rooted at `(1371354951380402432, 1043073614125389890619145951)`: 60 nodes (branch 4, chain 8, closed 36, cyc 1, forced 1, tab 10). -/
def tree_sub1607 : Tr := Tr.branch 8 [Tr.closed, Tr.tab [18, 41] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [19, 42, 5, 14, 23, 43, 22] (Tr.chain 6 [43, 29, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 33] (Tr.forced 52 [(8, 1), (43, -1), (51, 1), (56, -1), (60, 1), (80, 1)] (Tr.tab [12, 23, 42, 13, 14, 22, 5] (Tr.chain 10 [56, 22, 52, 57, 53, 65] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 33] (Tr.branch 9 [Tr.closed, Tr.tab [19, 43, 14, 22, 27, 41, 5, 44, 13, 23, 12] (Tr.chain 10 [23, 53, 57, 52, 77] (Tr.closed)), Tr.tab [19, 42, 5, 23] (Tr.chain 47 [25, 43, 29] (Tr.tab [13, 22, 43, 14] (Tr.branch 12 [Tr.chain 0 [36, 60, 26, 35, 77, 51] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 1 [68, 44, 8, 87] (Tr.closed), Tr.chain 0 [36, 60, 26, 35, 77, 51] (Tr.closed), Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [18, 26, 33, 41, 9, 14, 19, 42, 43, 5, 22, 23] (Tr.chain 6 [43, 29, 65, 51] (Tr.closed)), Tr.tab [29] (Tr.cycBad 0 3 1 4 [(8, 1), (15, 1), (36, 1), (43, -1), (51, 1), (56, -1), (57, -1), (85, 1)]), Tr.closed, Tr.closed]

theorem hand_sub1607 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1607 : Settles 1371354951380402432 1043073614125389890619145951 :=
  settles_of_check hand_sub1607 (by decide +kernel :
    check [] 100 1371354951380402432 1043073614125389890619145951 tree_sub1607 = true)

/-- Subtree rooted at `(1371354951382597890, 1034611133401600484915937021)`: 16 nodes (branch 1, chain 2, closed 9, cyc 1, tab 3). -/
def tree_sub1608 : Tr := Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 43, 13] (Tr.chain 14 [44, 17, 47] (Tr.closed)), Tr.closed, Tr.tab [22, 33, 8, 13, 27, 29] (Tr.chain 71 [21, 36, 60, 50, 17] (Tr.tab [14] (Tr.cycBad 0 4 1 2 [(1, -3), (8, 1), (21, 1), (43, -2), (50, 2), (51, 1), (56, 1), (57, 1), (76, -2), (85, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1608 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1608 : Settles 1371354951382597890 1034611133401600484915937021 :=
  settles_of_check hand_sub1608 (by decide +kernel :
    check [] 56 1371354951382597890 1034611133401600484915937021 tree_sub1608 = true)

/-- Subtree rooted at `(218428981066612736, 820702081519722926048262103)`: 203 nodes (assumed 1, branch 14, chain 17, closed 114, cyc 11, forced 6, leaf 1, symm 1, tab 38). -/
def tree_sub1609 : Tr := Tr.branch 3 [Tr.tab [15, 42, 23] (Tr.branch 12 [Tr.tab [22, 44] (Tr.cycBad 0 5 1 2 [(3, 1), (35, 1), (42, 1), (51, 1), (56, -1)]), Tr.tab [22, 41, 5, 18] (Tr.chain 28 [42, 24, 46] (Tr.tab [8, 19, 40] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 88 [3, 80, 44, 14] (Tr.forced 65 [(14, -1), (26, 1), (30, -1), (42, 1), (46, 1), (56, 1), (80, -1)] (Tr.tab [14] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 2, 5, 4, 1, 3), Tr.cycBad 0 3 2 5 [(3, -1), (21, -1), (24, -1), (26, 1), (41, -1), (46, 1), (51, -1), (56, 1), (65, -1), (80, -1)], Tr.closed]))), Tr.closed, Tr.tab [29, 13] (Tr.cycBad 0 2 1 3 [(3, 1), (14, -1), (21, 2), (24, 2), (26, -1), (28, 1), (30, -1), (41, 1), (44, 2), (46, -2), (51, 1), (86, -1)]), Tr.closed, Tr.closed]))), Tr.closed, Tr.tab [22, 25] (Tr.forced 77 [(3, 1), (21, 1), (30, -1), (42, 1), (51, 1), (57, -1), (64, 1)] (Tr.tab [14, 41, 18] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [33] (Tr.cycBad 0 2 3 4 [(14, 1), (42, -1), (57, -1), (77, -1), (80, 1)]), Tr.closed, Tr.cycBad 0 4 2 5 [(21, 1), (30, -1), (42, 1), (51, 1), (56, 1), (77, -1), (86, -1)], Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [21, 33] (Tr.branch 9 [Tr.closed, Tr.tab [18, 41, 43, 8, 19, 22] (Tr.chain 59 [22, 56, 23] (Tr.closed)), Tr.tab [18, 19, 42, 23] (Tr.forced 83 [(21, 1), (29, 1), (30, -1), (42, 1), (51, 1)] (Tr.tab [14] (Tr.branch 8 [Tr.tab [44] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 12, 13] (Tr.chain 1 [42, 24, 46, 11, 44, 14, 88, 57] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 29, 12, 13, 25] (Tr.cycBad 0 1 2 4 [(11, -1), (14, 1), (21, -1), (24, -1), (29, -1), (30, 1), (42, -1), (47, -1), (51, -2), (57, -1), (64, 1), (83, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 13 [Tr.closed, Tr.tab [22, 43] (Tr.chain 84 [37, 29, 47, 14] (Tr.cycBad 1 3 2 5 [(29, 1), (30, 1), (37, -1), (57, 1), (68, -1), (84, 1)])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 1 5 2 3 [(14, -1), (24, 1), (30, 1), (37, -1), (56, 1), (57, 1), (68, -1), (83, 1), (88, -1)]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [18] (Tr.cycBad 1 2 3 5 [(14, 1), (21, -1), (24, -1), (30, 1), (42, -1), (51, -1), (56, -1), (86, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [30] (Tr.branch 5 [Tr.tab [19, 22, 44] (Tr.branch 8 [Tr.closed, Tr.tab [18, 41, 43, 9] (Tr.chain 59 [22, 56, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [18, 26, 33] (Tr.chain 64 [24, 42, 68, 5] (Tr.tab [25] (Tr.forced 52 [(14, 1), (42, -1), (56, -1), (68, 1), (72, 1)] (Tr.tab [23, 40, 42, 9, 13, 14] (Tr.chain 59 [52, 57, 53] (Tr.closed)))))), Tr.tab [18, 26, 33, 41, 43, 9, 14, 40, 12, 23, 13] (Tr.chain 49 [30, 21, 83, 22, 56] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [19, 22, 40, 8, 18, 23] (Tr.chain 46 [24, 42, 28] (Tr.closed)), Tr.tab [19, 22, 41, 12, 18, 23] (Tr.chain 28 [42, 24, 46] (Tr.closed)), Tr.tab [19, 22, 40, 41, 8, 12, 18, 23] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 65 [(14, -1), (26, 1), (30, -1), (42, 1), (46, 1), (56, 1), (80, -1)] (Tr.tab [14] (Tr.branch 13 [Tr.chain 0 [30, 72, 26, 41, 65, 51] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 3 [80, 44, 14, 88] (Tr.closed), Tr.chain 0 [30, 72, 26, 41, 65, 51] (Tr.closed), Tr.closed])), Tr.closed, Tr.tab [29, 13] (Tr.chain 71 [21, 30, 72, 26, 41] (Tr.tab [14] (Tr.cycBad 0 4 2 5 [(26, -1), (41, -1), (42, 1), (51, 1), (56, 1), (72, -1), (86, -1)]))), Tr.closed, Tr.closed]), Tr.tab [19, 22, 23, 33] (Tr.branch 8 [Tr.tab [18, 44, 12, 25] (Tr.chain 83 [21, 30, 72, 50, 11] (Tr.tab [14] (Tr.cycBad 0 1 2 4 [(11, -14), (14, 9), (21, 9), (30, -4), (50, -5), (51, -5), (56, -4), (57, -5), (64, 9), (72, 13), (83, -4)]))), Tr.tab [18, 41, 43, 9] (Tr.chain 59 [22, 56, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [15, 30, 42, 23] (Tr.forced 11 [(3, -1), (14, 1), (42, -1), (51, -1), (72, 1)] (Tr.tab [8, 18, 19, 44] ((Tr.symm (0, 1, 3, 2, 4, 5) Tr.assumed)))), Tr.closed]

theorem hand_sub1609 : ∀ x ∈ ([(1371354951382597890, 1034611133401600484915937021)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1608 all_settles_nil)

theorem settles_sub1609 : Settles 218428981066612736 820702081519722926048262103 :=
  settles_of_check hand_sub1609 (by decide +kernel :
    check [(1371354951382597890, 1034611133401600484915937021)] 243 218428981066612736 820702081519722926048262103 tree_sub1609 = true)

/-- Subtree rooted at `(216464154878283776, 1052896414271512756200794079)`: 40 nodes (branch 3, chain 2, closed 26, cyc 1, leaf 1, tab 7). -/
def tree_sub1610 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [25, 38] (Tr.branch 13 [Tr.closed, Tr.tab [22, 43, 5, 18] (Tr.chain 29 [43, 25, 47] (Tr.tab [9, 19, 42, 8, 14] (Tr.leaf (2, 1, 0, 3, 5, 4)))), Tr.tab [22, 42, 14, 19, 28, 40] (Tr.branch 8 [Tr.tab [18, 44, 5] (Tr.closed), Tr.tab [18, 9] (Tr.chain 0 [21, 83, 22, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 0 5 1 3 [(12, 1), (21, 1), (25, -1), (31, 1), (40, 1), (56, -1), (57, -1), (87, 1)]), Tr.closed, Tr.closed]

theorem hand_sub1610 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1610 : Settles 216464154878283776 1052896414271512756200794079 :=
  settles_of_check hand_sub1610 (by decide +kernel :
    check [] 80 216464154878283776 1052896414271512756200794079 tree_sub1610 = true)

/-- Subtree rooted at `(36081574919544832, 847528295233577633634097899)`: 178 nodes (assumed 4, branch 13, chain 9, closed 104, cyc 9, leaf 1, symm 4, tab 34). -/
def tree_sub1611 : Tr := Tr.branch 12 [Tr.tab [44, 24] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [42, 19] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 7 [Tr.closed, Tr.tab [17, 41, 9] (Tr.cycBad 0 5 1 2 [(13, 1), (16, -1), (18, -1), (30, -1), (35, -1), (44, 2), (53, -2), (86, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [31] (Tr.branch 9 [Tr.tab [17, 38, 4, 28] (Tr.chain 34 [14, 44, 17, 65] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [17] (Tr.cycBad 0 1 2 3 [(30, 1), (35, 1), (44, -1), (45, -1), (53, 1), (79, -1), (86, 1)]), Tr.tab [17, 38, 4, 28] (Tr.chain 34 [14, 44, 17, 65] (Tr.closed)), Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [41] (Tr.cycBad 1 2 4 5 [(28, 1), (30, -1), (44, 1), (53, -1), (77, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [27, 38, 17] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [19, 7] (Tr.chain 25 [30, 27, 65, 29, 55, 28, 35, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19] (Tr.chain 4 [86, 55, 28, 35, 76] (Tr.tab [4, 15] (Tr.cycBad 0 5 1 2 [(4, 1), (18, 1), (28, 1), (55, -1), (76, -1), (86, 1)]))), Tr.closed, Tr.closed]), Tr.tab [26, 42, 19] (Tr.cycBad 0 5 1 2 [(18, 1), (28, 1), (30, -1), (44, 1), (71, -1), (76, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [27, 38, 42, 14, 17, 19, 43, 9] (Tr.chain 4 [86, 55, 28, 35, 76] (Tr.tab [4, 15] (Tr.cycBad 0 1 2 3 [(4, -2), (13, 1), (18, -2), (28, -1), (30, -1), (44, 2), (45, -1), (53, -1), (55, 1), (65, -1), (76, 1), (86, -2)]))), Tr.closed, Tr.closed, Tr.tab [29, 36] (Tr.branch 9 [Tr.tab [17, 19, 38, 4] (Tr.chain 47 [14, 44, 17] (Tr.closed)), Tr.tab [17, 19, 43, 4, 30] (Tr.branch 7 [Tr.closed, Tr.tab [28, 41, 11, 14, 38, 2] (Tr.leaf (0, 1, 5, 3, 2, 4)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 31, 11] (Tr.chain 32 [78, 30, 79] (Tr.closed)), Tr.closed, Tr.closed]), Tr.tab [17, 19, 42, 7] (Tr.chain 41 [35, 28, 55, 29] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [25, 38] (Tr.branch 2 [Tr.tab [15, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 36] (Tr.branch 4 [Tr.closed, Tr.tab [17, 44, 9, 13, 14, 19, 24] (Tr.chain 33 [53, 17, 44, 14, 69, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 28] (Tr.branch 13 [Tr.tab [44, 14, 24] (Tr.cycBad 0 3 1 4 [(2, 1), (18, 1), (30, 1), (41, -1), (44, -1), (45, -1), (55, -1), (77, 1), (78, 1)]), Tr.closed, Tr.tab [42, 19] ((Tr.symm (1, 0, 2, 5, 3, 4) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.cycBad 0 5 2 4 [(13, 1), (18, -1), (28, -1), (30, 1), (44, -1), (45, -1), (64, 1), (81, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [31] ((Tr.symm (2, 0, 1, 4, 5, 3) Tr.assumed)), Tr.closed, Tr.tab [26, 30] ((Tr.symm (0, 2, 1, 4, 3, 5) Tr.assumed)), Tr.tab [15, 26, 30, 41, 11, 28] (Tr.cycBad 0 3 1 2 [(2, -1), (13, 1), (18, -1), (28, -1), (30, 1), (45, -1), (64, 1), (66, -1), (81, -2)]), Tr.closed]), Tr.closed, Tr.tab [26] ((Tr.symm (2, 0, 4, 1, 5, 3) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1611 : ∀ x ∈ ([(216464154878283776, 1052896414271512756200794079), (218428981066612736, 820702081519722926048262103), (1371354951380402432, 1043073614125389890619145951), (4888423508497026646145, 614129381814855731605536638)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1610 (all_settles_cons settles_sub1609 (all_settles_cons settles_sub1607 (all_settles_cons settles_sub1606 all_settles_nil))))

theorem settles_sub1611 : Settles 36081574919544832 847528295233577633634097899 :=
  settles_of_check hand_sub1611 (by decide +kernel :
    check [(216464154878283776, 1052896414271512756200794079), (218428981066612736, 820702081519722926048262103), (1371354951380402432, 1043073614125389890619145951), (4888423508497026646145, 614129381814855731605536638)] 218 36081574919544832 847528295233577633634097899 tree_sub1611 = true)

/-- Subtree rooted at `(36064054959669408, 1184217604636687934508415839)`: 63 nodes (branch 5, chain 2, closed 43, cyc 3, tab 10). -/
def tree_sub1612 : Tr := Tr.branch 8 [Tr.closed, Tr.tab [41, 22] (Tr.branch 7 [Tr.tab [43, 14, 28, 40, 12, 13] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 32, 11, 38, 4, 12, 13] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [32] (Tr.cycBad 1 3 2 5 [(7, 1), (24, -1), (36, 1), (45, 1), (49, -1), (55, -1), (85, 1)]), Tr.closed, Tr.tab [28, 13, 22, 41, 43, 12, 14] (Tr.chain 0 [36, 24, 46, 83, 45] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [26] (Tr.branch 7 [Tr.tab [43] (Tr.cycBad 0 1 2 3 [(7, -1), (10, -1), (24, 1), (32, 1), (36, -1), (45, -1), (55, 1), (85, -1)]), Tr.tab [17, 41] (Tr.chain 65 [16, 85, 55, 29] (Tr.tab [25, 43, 22, 12, 40] (Tr.cycBad 0 3 1 2 [(7, 1), (16, 4), (29, 3), (32, -1), (36, 1), (45, 1), (55, -4), (65, -3), (69, -1), (85, 4)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]

theorem hand_sub1612 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1612 : Settles 36064054959669408 1184217604636687934508415839 :=
  settles_of_check hand_sub1612 (by decide +kernel :
    check [] 103 36064054959669408 1184217604636687934508415839 tree_sub1612 = true)

/-- Subtree rooted at `(36063982733500416, 828166592652474785765825227)`: 187 nodes (assumed 8, branch 13, chain 13, closed 106, cyc 4, forced 1, symm 6, tab 36). -/
def tree_sub1613 : Tr := Tr.branch 5 [Tr.tab [15, 44, 17] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.tab [19, 36] (Tr.branch 9 [Tr.closed, Tr.tab [43, 22] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 13, 42] (Tr.branch 14 [Tr.tab [24, 34, 7, 20] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 41, 7, 28, 31, 11, 20, 2] (Tr.chain 14 [32, 79, 30, 25] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [26] (Tr.branch 14 [Tr.tab [24, 34, 7, 20] (Tr.chain 22 [56, 23, 59] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 27, 41, 7, 13, 28, 31] (Tr.cycBad 0 3 1 2 [(5, -1), (18, 1), (25, -1), (28, -1), (30, 1), (77, 1), (79, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [27, 34, 24] (Tr.branch 13 [Tr.closed, Tr.tab [22, 41, 43, 12, 14, 20, 26] (Tr.chain 0 [30, 25, 47, 71, 45] (Tr.closed)), Tr.tab [22, 42, 14, 25, 43, 12, 20, 26] (Tr.cycBad 0 3 2 4 [(13, 1), (18, -1), (25, -1), (30, 1), (45, -1), (53, -1), (55, -1), (70, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.branch 12 [Tr.closed, Tr.tab [22, 41, 43, 13, 20] (Tr.forced 8 [(25, 1), (28, -1), (46, 1), (55, 1), (86, -1)] (Tr.tab [2, 16, 38, 11, 28] (Tr.chain 9 [55, 28, 46, 81, 45] (Tr.closed)))), Tr.closed, Tr.tab [22, 25, 38, 13, 42] (Tr.branch 14 [Tr.tab [24, 34, 7, 20] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [24, 41] (Tr.chain 10 [86, 55, 28, 77] (Tr.tab [43, 11, 20, 28] (Tr.cycBad 0 1 3 5 [(10, 1), (13, -1), (18, 1), (28, 1), (45, 1), (64, -1), (81, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [22, 26] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.cycBad 0 3 1 5 [(13, -1), (18, 1), (25, 1), (45, 1), (53, 1), (55, 1), (70, -1), (86, -1)], Tr.tab [27, 38] (Tr.chain 36 [18, 70, 76, 25, 30] (Tr.closed)), Tr.tab [27, 38] (Tr.chain 36 [18, 70, 76, 25, 30] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [22, 26, 41, 43, 13, 14, 20, 24, 7, 11] (Tr.chain 0 [30, 25, 47, 59, 46, 81] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.tab [21, 34, 20, 24] (Tr.branch 9 [Tr.closed, Tr.tab [19, 43, 22] (Tr.branch 7 [Tr.closed, Tr.tab [41, 14, 42] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 38, 11, 13] (Tr.chain 8 [38, 23, 71, 45, 81] (Tr.closed)), Tr.closed, Tr.tab [26, 36, 11, 13] (Tr.chain 4 [23, 71, 45, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 31] ((Tr.symm (3, 0, 1, 4, 2, 5) Tr.assumed)), Tr.closed, Tr.closed]), Tr.tab [19, 42, 7] (Tr.chain 59 [28, 55, 29] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [19, 29] ((Tr.symm (0, 4, 1, 3, 2, 5) Tr.assumed)), Tr.closed, Tr.closed]), Tr.tab [19, 21, 34, 36, 20, 24] ((Tr.symm (0, 1, 3, 2, 4, 5) Tr.assumed)), Tr.closed, Tr.closed, Tr.tab [30] ((Tr.symm (3, 0, 1, 4, 2, 5) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [22, 34, 20] (Tr.assumed), Tr.closed, Tr.tab [23] (Tr.assumed), Tr.closed, Tr.tab [30] ((Tr.symm (0, 4, 2, 1, 3, 5) Tr.assumed)), Tr.tab [15, 30, 44, 17] ((Tr.symm (0, 4, 2, 1, 3, 5) Tr.assumed)), Tr.closed]

theorem hand_sub1613 : ∀ x ∈ ([(36064054959669408, 1184217604636687934508415839), (36081574919544832, 847528295233577633634097899), (37189882640343040, 847509405775615118978620139), (1189513801352347649, 574594470010428528139760606), (1189513801352364033, 574670028162384818624508894), (1197958067833536513, 501835088329334558151718878), (1197958342761775361, 347414908639772757894430462), (4724744946431507304706, 105019820390144483667078909)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1612 (all_settles_cons settles_sub1611 (all_settles_cons settles_sub1605 (all_settles_cons settles_sub0498 (all_settles_cons settles_sub1599 (all_settles_cons settles_sub1598 (all_settles_cons settles_sub1597 (all_settles_cons settles_sub1596 all_settles_nil))))))))

theorem settles_sub1613 : Settles 36063982733500416 828166592652474785765825227 :=
  settles_of_check hand_sub1613 (by decide +kernel :
    check [(36064054959669408, 1184217604636687934508415839), (36081574919544832, 847528295233577633634097899), (37189882640343040, 847509405775615118978620139), (1189513801352347649, 574594470010428528139760606), (1189513801352364033, 574670028162384818624508894), (1197958067833536513, 501835088329334558151718878), (1197958342761775361, 347414908639772757894430462), (4724744946431507304706, 105019820390144483667078909)] 227 36063982733500416 828166592652474785765825227 tree_sub1613 = true)

/-- Subtree rooted at `(4796190613870536310785, 253113248820785122331309054)`: 44 nodes (branch 3, chain 3, closed 25, cyc 3, forced 1, tab 9). -/
def tree_sub1614 : Tr := Tr.branch 12 [Tr.tab [20, 43, 44, 11, 24, 26, 7, 28, 31, 8] (Tr.chain 6 [72, 50, 62, 79, 0] (Tr.closed)), Tr.tab [20, 22, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 36, 7, 24] (Tr.chain 4 [67, 0, 69] (Tr.closed)), Tr.closed, Tr.tab [26, 28] (Tr.forced 89 [(0, -1), (18, -1), (29, -1), (33, -1), (50, 1), (55, 1), (66, -1), (72, -1), (81, -1)] (Tr.tab [14, 28, 29, 13, 44, 24, 7, 16, 8] (Tr.cycBad 0 3 1 5 [(0, 4), (14, 1), (18, 4), (29, 4), (33, 3), (41, -1), (50, -4), (55, -4), (66, 4), (72, 4), (81, 3), (89, 3)]))), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [20, 25] (Tr.branch 8 [Tr.tab [16, 44, 24] (Tr.cycBad 0 3 1 5 [(0, 1), (11, 1), (18, 1), (29, 1), (64, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 31] (Tr.cycBad 0 4 1 3 [(0, 1), (14, 1), (29, 1), (55, -1), (64, -1), (85, 1)]), Tr.tab [16, 29, 31, 44, 24, 7, 26, 36, 11] (Tr.chain 4 [67, 0, 69] (Tr.closed)), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1614 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1614 : Settles 4796190613870536310785 253113248820785122331309054 :=
  settles_of_check hand_sub1614 (by decide +kernel :
    check [] 84 4796190613870536310785 253113248820785122331309054 tree_sub1614 = true)

/-- Subtree rooted at `(1189513801604006145, 456119763034855337941597918)`: 97 nodes (branch 8, chain 2, closed 65, cyc 6, forced 1, leaf 2, tab 13). -/
def tree_sub1615 : Tr := Tr.branch 9 [Tr.tab [17, 44, 21, 24, 7, 28] (Tr.cycBad 0 3 1 4 [(8, 1), (17, -1), (19, -1), (39, -1), (49, 1), (79, -1)]), Tr.closed, Tr.closed, Tr.tab [27, 34, 24] (Tr.branch 5 [Tr.tab [23, 44, 21] (Tr.chain 82 [19, 49, 74, 5] (Tr.tab [28, 37] (Tr.branch 7 [Tr.closed, Tr.branch 11 [Tr.tab [43] (Tr.branch 12 [Tr.closed, Tr.cycBad 0 2 3 4 [(0, -1), (16, 1), (19, -1), (28, -1), (34, -1), (39, -1), (46, 2), (49, 1), (55, 1), (74, -2), (82, 1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 14] (Tr.cycBad 0 2 1 3 [(16, 1), (28, -1), (39, -1), (49, 1), (71, 1), (74, -1), (82, 1), (87, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 12 [Tr.closed, Tr.tab [22] (Tr.cycBad 0 5 2 4 [(5, -1), (16, 1), (28, -1), (39, -1), (46, 1), (55, 1), (74, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 14, 43] (Tr.cycBad 0 1 2 3 [(0, -1), (5, 2), (8, -1), (49, 1), (55, 1), (60, 1), (65, 2), (69, 2), (74, -3), (82, 1), (87, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 46 [(5, 1), (28, 1), (39, 1), (55, -1), (79, 1)] (Tr.tab [12, 22] (Tr.branch 11 [Tr.tab [43] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.leaf (2, 4, 1, 5, 3, 0), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (3, 0, 4, 1, 2, 5), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 1 2 3 4 [(0, -1), (19, 1), (28, 1), (39, 1), (49, -1), (55, -1), (60, 1), (69, 1), (79, 1), (82, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed])), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 42, 13, 21] (Tr.chain 13 [50, 74, 49, 19] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1615 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1615 : Settles 1189513801604006145 456119763034855337941597918 :=
  settles_of_check hand_sub1615 (by decide +kernel :
    check [] 137 1189513801604006145 456119763034855337941597918 tree_sub1615 = true)

/-- Subtree rooted at `(36063982599284736, 819099649649379848868321259)`: 212 nodes (assumed 2, branch 16, chain 11, closed 132, cyc 10, forced 1, leaf 1, symm 2, tab 37). -/
def tree_sub1616 : Tr := Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 34, 20] (Tr.branch 9 [Tr.closed, Tr.tab [43, 4, 28, 30] (Tr.chain 77 [27, 30, 78, 44, 11] (Tr.tab [14, 27, 41] (Tr.cycBad 1 4 3 5 [(11, 1), (13, 1), (27, 1), (30, -1), (77, -1), (78, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 4 [Tr.tab [15] (Tr.forced 71 [(4, -1), (30, -1), (44, 1), (55, 1), (86, -1)] (Tr.tab [14, 42] (Tr.branch 2 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23] (Tr.cycBad 1 2 3 4 [(13, 1), (18, -1), (27, -1), (30, 1), (45, -1), (48, -1), (55, -1), (86, 1)]), Tr.closed, Tr.tab [26] (Tr.chain 52 [18, 66, 44, 11] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.branch 13 [Tr.tab [21] (Tr.cycBad 0 2 4 5 [(13, -1), (18, 1), (27, 1), (30, -1), (41, -1), (44, 1), (55, 1), (71, -1), (86, -1)]), Tr.closed, Tr.closed, Tr.tab [27, 38] (Tr.branch 11 [Tr.closed, Tr.leaf (2, 4, 0, 1, 3, 5), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 3 [(4, -1), (13, 1), (18, -1), (44, 1), (45, -1), (52, -1), (66, -1), (81, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.tab [38, 13, 21, 11] (Tr.cycBad 0 2 1 3 [(4, -2), (11, 1), (13, 1), (30, -1), (41, 2), (44, 1), (45, 1), (55, 1), (64, -2), (71, 1), (81, 1), (86, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed])), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 30] (Tr.chain 77 [27, 30, 78, 44, 11] (Tr.tab [14, 27, 41] (Tr.cycBad 1 4 3 5 [(11, 1), (13, 1), (27, 1), (30, -1), (77, -1), (78, 1)]))), Tr.tab [15, 28, 30, 2, 23] (Tr.chain 77 [27, 30, 78, 44, 11] (Tr.tab [14, 27, 41] (Tr.cycBad 0 5 1 3 [(27, 1), (30, -1), (44, 1), (45, 1), (48, 1), (77, -1), (86, -1)]))), Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [23] (Tr.branch 9 [Tr.closed, Tr.tab [43, 22] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 34, 20] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 2 [Tr.tab [23, 12, 26, 14] (Tr.chain 4 [23, 71, 45, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [23, 40, 12, 14] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28, 14, 26, 12, 23, 2] (Tr.chain 7 [50, 11, 52] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.chain 46 [58, 88, 13, 50, 11] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.cycBad 0 2 1 4 [(13, 1), (18, -1), (27, -1), (30, 1), (45, -1), (55, -1), (81, -1), (88, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 30] (Tr.branch 2 [Tr.tab [20, 23, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 12, 26] (Tr.cycBad 0 1 2 3 [(11, 2), (13, 2), (18, -1), (23, -1), (27, 1), (45, -2), (50, -1), (55, -1), (58, -1), (70, 2), (78, 2)]), Tr.closed, Tr.tab [36] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 38, 13] (Tr.chain 56 [2, 64, 41, 23] (Tr.closed)), Tr.closed, Tr.tab [26, 14] (Tr.chain 4 [23, 71, 45, 69] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [20, 23, 11] (Tr.chain 14 [78, 30, 27, 34] (Tr.closed)), Tr.closed, Tr.tab [20, 23, 40, 12] (Tr.chain 7 [50, 11, 52] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [27, 34] (Tr.cycBad 0 2 3 4 [(11, -1), (13, 1), (18, -1), (27, -1), (30, 1), (50, -1), (55, -1), (74, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] ((Tr.symm (0, 4, 1, 2, 3, 5) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [30] ((Tr.symm (0, 4, 2, 1, 3, 5) Tr.assumed)), Tr.closed, Tr.closed]

theorem hand_sub1616 : ∀ x ∈ ([(1189513801604006145, 456119763034855337941597918), (4796190613870536310785, 253113248820785122331309054)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub1615 (all_settles_cons settles_sub1614 all_settles_nil))

theorem settles_sub1616 : Settles 36063982599284736 819099649649379848868321259 :=
  settles_of_check hand_sub1616 (by decide +kernel :
    check [(1189513801604006145, 456119763034855337941597918), (4796190613870536310785, 253113248820785122331309054)] 252 36063982599284736 819099649649379848868321259 tree_sub1616 = true)

/-- Subtree rooted at `(19101637269858998568964, 1237920937648110415898425339)`: 12 nodes (branch 1, chain 1, closed 9, leaf 1). -/
def tree_sub1617 : Tr := Tr.branch 6 [Tr.closed, Tr.leaf (0, 1, 2, 3, 4, 5), Tr.chain 39 [52, 11, 74, 67, 21] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1617 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1617 : Settles 19101637269858998568964 1237920937648110415898425339 :=
  settles_of_check hand_sub1617 (by decide +kernel :
    check [] 52 19101637269858998568964 1237920937648110415898425339 tree_sub1617 = true)

/-- Subtree rooted at `(4724746635350053486850, 1028638556277079554245132029)`: 81 nodes (branch 6, chain 3, closed 50, cyc 2, forced 3, leaf 3, tab 14). -/
def tree_sub1618 : Tr := Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [41] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 33, 12] (Tr.chain 44 [8, 87, 1, 68] (Tr.tab [22] (Tr.forced 26 [(8, 1), (36, 1), (44, -1), (56, -1), (68, 1), (77, 1)] (Tr.tab [19, 37, 9, 13] (Tr.chain 30 [72, 26, 41, 29, 61] (Tr.closed)))))), Tr.closed, Tr.tab [29, 12, 37, 19] (Tr.forced 50 [(1, 1), (36, 1), (56, -1), (77, 1), (85, 1)] (Tr.tab [5, 33] (Tr.branch 9 [Tr.tab [44, 13] (Tr.leaf (2, 0, 1, 4, 3, 5)), Tr.tab [43, 13] (Tr.cycBad 0 4 1 3 [(1, 1), (23, -2), (25, 1), (41, 3), (51, -3), (56, -1), (70, 2), (72, 3), (85, -2)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28] (Tr.branch 13 [Tr.tab [44] (Tr.cycBad 0 4 1 3 [(1, 1), (25, 1), (41, 1), (51, -1), (56, -1), (72, 1)]), Tr.tab [22, 43] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.tab [19, 37, 9, 12, 29] (Tr.chain 30 [25, 47, 29, 61] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 33, 9] (Tr.forced 22 [(1, 1), (17, 1), (33, -1), (51, -1), (83, 1)] (Tr.tab [8] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (0, 1, 2, 3, 5, 4), Tr.closed, Tr.leaf (1, 3, 4, 0, 2, 5), Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1618 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1618 : Settles 4724746635350053486850 1028638556277079554245132029 :=
  settles_of_check hand_sub1618 (by decide +kernel :
    check [] 121 4724746635350053486850 1028638556277079554245132029 tree_sub1618 = true)

/-- Subtree rooted at `(1227231449306906632, 806198530910664269536147447)`: 34 nodes (branch 2, chain 4, closed 17, cyc 1, forced 1, leaf 1, tab 8). -/
def tree_sub1619 : Tr := Tr.branch 5 [Tr.closed, Tr.closed, Tr.tab [19, 37, 8, 18] (Tr.chain 64 [24, 60, 26] (Tr.closed)), Tr.tab [19, 22] (Tr.cycBad 0 4 2 5 [(3, -1), (14, 1), (21, -1), (24, -1), (30, 1), (39, 1), (44, -1), (51, -1)]), Tr.tab [19, 22, 37, 8, 12, 13, 18, 29, 9] (Tr.chain 31 [26, 35, 28] (Tr.closed)), Tr.tab [19, 33] (Tr.branch 9 [Tr.closed, Tr.tab [18, 41, 43, 8, 14, 26, 12] (Tr.chain 41 [35, 22, 56, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [18, 29, 8, 44] (Tr.chain 46 [24, 60, 50, 11] (Tr.tab [22, 41, 13, 37] (Tr.forced 65 [(3, -1), (30, -1), (50, 1), (56, 1), (86, -1)] (Tr.tab [14] (Tr.leaf (2, 5, 0, 1, 3, 4)))))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1619 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1619 : Settles 1227231449306906632 806198530910664269536147447 :=
  settles_of_check hand_sub1619 (by decide +kernel :
    check [] 74 1227231449306906632 806198530910664269536147447 tree_sub1619 = true)

/-- Subtree rooted at `(1227231449305333760, 1115674095386554049121203679)`: 27 nodes (branch 2, chain 1, closed 16, cyc 2, leaf 1, tab 5). -/
def tree_sub1620 : Tr := Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [19, 42] (Tr.cycBad 1 5 2 4 [(19, -1), (29, -1), (30, 1), (39, 1), (51, -1), (60, -1)]), Tr.closed, Tr.closed, Tr.tab [28, 33, 13, 22, 24, 43] (Tr.branch 5 [Tr.tab [19, 44, 12, 26, 14, 27, 41, 6, 8] (Tr.leaf (0, 5, 1, 4, 3, 2)), Tr.closed, Tr.tab [19, 37, 8, 12] (Tr.chain 31 [26, 35, 28] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29] (Tr.cycBad 1 2 3 5 [(14, 1), (19, -1), (24, -1), (30, 1), (51, -1), (56, -1), (60, -1), (86, 1)]), Tr.closed, Tr.closed]

theorem hand_sub1620 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1620 : Settles 1227231449305333760 1115674095386554049121203679 :=
  settles_of_check hand_sub1620 (by decide +kernel :
    check [] 67 1227231449305333760 1115674095386554049121203679 tree_sub1620 = true)

/-- Subtree rooted at `(4796190613870301413377, 533490333834940288842923006)`: 62 nodes (branch 4, chain 7, closed 34, cyc 3, forced 1, tab 13). -/
def tree_sub1621 : Tr := Tr.branch 12 [Tr.tab [20, 43, 44, 11, 24] (Tr.forced 16 [(25, 1), (28, 1), (34, 1), (50, -1), (72, 1)] (Tr.tab [7, 17, 41, 14, 29] (Tr.chain 13 [72, 25, 34, 89, 33] (Tr.closed)))), Tr.tab [20, 22, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 38, 27] (Tr.chain 11 [50, 72, 25, 58, 46] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.chain 61 [0, 81, 46, 28, 55] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [20, 25, 38, 27] (Tr.branch 11 [Tr.closed, Tr.tab [21, 41] (Tr.branch 13 [Tr.closed, Tr.tab [43] (Tr.chain 17 [50, 72, 25, 47] (Tr.tab [44, 14, 24, 29] (Tr.chain 82 [33, 89, 40, 64] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.chain 89 [33, 82, 64, 40] (Tr.tab [29] (Tr.cycBad 0 2 3 4 [(0, -1), (18, -1), (40, -1), (50, 1), (55, 1), (64, 1), (66, -1), (72, -1), (82, -2), (89, 1)])), Tr.tab [43] (Tr.chain 17 [50, 72, 25, 47] (Tr.tab [44, 14, 24, 29] (Tr.cycBad 0 1 3 4 [(0, -1), (28, 1), (33, -1), (40, 1), (47, -1), (89, -1)]))), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.cycBad 0 4 2 3 [(0, 1), (18, 1), (28, 1), (33, 1), (50, -1), (55, -1), (66, 1), (72, 1), (81, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1621 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1621 : Settles 4796190613870301413377 533490333834940288842923006 :=
  settles_of_check hand_sub1621 (by decide +kernel :
    check [] 102 4796190613870301413377 533490333834940288842923006 tree_sub1621 = true)

/-- Subtree rooted at `(1190077026720546817, 574615573743757963604456446)`: 60 nodes (branch 4, chain 5, closed 33, cyc 4, forced 1, tab 13). -/
def tree_sub1622 : Tr := Tr.branch 11 [Tr.tab [20, 43] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 14, 25, 29] (Tr.chain 70 [39, 89, 34, 76] (Tr.cycBad 0 5 1 2 [(0, -1), (19, 1), (24, -1), (38, 1), (55, -1), (70, 1), (76, -1)])), Tr.closed, Tr.tab [37] (Tr.forced 22 [(0, 1), (29, 1), (38, 1), (50, -1), (55, -1), (60, 1), (82, 1)] (Tr.tab [8, 25, 41] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [38, 25] (Tr.branch 13 [Tr.closed, Tr.tab [22, 43] (Tr.chain 17 [50, 60, 24, 58, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.cycBad 0 1 3 5 [(0, 1), (19, -1), (24, 1), (38, 1), (50, -1), (58, -1), (82, 1)]), Tr.tab [22, 37, 43, 12, 44] (Tr.chain 17 [50, 60, 24, 58, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [26] (Tr.branch 12 [Tr.tab [25, 44] (Tr.cycBad 0 2 1 5 [(19, 1), (29, 1), (35, -1), (38, 1), (50, -1), (55, -1), (60, 1)]), Tr.tab [22, 25, 41] (Tr.chain 11 [50, 60, 24, 46] (Tr.tab [16] (Tr.cycBad 0 3 1 4 [(0, 1), (11, -1), (24, 1), (29, 1), (38, 1), (50, -1), (55, -1), (60, 1)]))), Tr.closed, Tr.tab [25, 38, 8] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1622 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1622 : Settles 1190077026720546817 574615573743757963604456446 :=
  settles_of_check hand_sub1622 (by decide +kernel :
    check [] 100 1190077026720546817 574615573743757963604456446 tree_sub1622 = true)

/-- Subtree rooted at `(1190076756137607169, 574313365347281422035366910)`: 44 nodes (branch 3, chain 3, closed 25, cyc 3, tab 10). -/
def tree_sub1623 : Tr := Tr.branch 4 [Tr.closed, Tr.tab [17, 38] (Tr.branch 11 [Tr.closed, Tr.tab [21, 41, 12, 13] (Tr.chain 1 [55, 29, 41, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 26, 12, 22, 41, 13] (Tr.chain 11 [50, 60, 24, 46] (Tr.tab [16, 7, 31] (Tr.cycBad 0 1 2 3 [(0, 1), (14, 1), (24, -1), (46, -1), (55, -1), (69, -1), (79, 1), (82, 1)]))), Tr.tab [21, 26, 41] (Tr.closed), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 12 [Tr.closed, Tr.tab [22, 41, 21, 13, 38, 11, 26] (Tr.chain 11 [50, 60, 24, 46] (Tr.tab [16, 7] (Tr.cycBad 0 3 1 2 [(16, 1), (24, 1), (29, -1), (32, -1), (39, -1), (46, 1), (50, 1), (55, 1), (60, -1), (69, -1), (76, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 3 2 4 [(0, 1), (19, -1), (39, -1), (50, 1), (55, 1), (60, -1), (70, -1), (78, -1)]), Tr.tab [22, 26, 41, 11, 21, 38] (Tr.closed), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1623 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1623 : Settles 1190076756137607169 574313365347281422035366910 :=
  settles_of_check hand_sub1623 (by decide +kernel :
    check [] 84 1190076756137607169 574313365347281422035366910 tree_sub1623 = true)

/-- Subtree rooted at `(1190076756120829953, 417153008797379629340341246)`: 119 nodes (branch 9, chain 6, closed 73, cyc 9, tab 22). -/
def tree_sub1624 : Tr := Tr.branch 4 [Tr.closed, Tr.tab [17, 38] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 1 4 2 3 [(0, 1), (19, -1), (29, -1), (39, -1), (50, 1), (55, 1), (60, -1), (67, -1)]), Tr.closed, Tr.tab [28, 31] (Tr.chain 69 [0, 79, 32, 14] (Tr.tab [26] (Tr.cycBad 2 3 4 5 [(19, 1), (29, 1), (39, 1), (50, -1), (55, -1), (60, 1), (79, 1)]))), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [41, 21] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 12, 29, 8, 16, 7] (Tr.cycBad 0 3 2 4 [(11, -1), (29, 1), (32, 1), (50, -1), (55, -1), (60, 1), (69, 1)]), Tr.closed, Tr.tab [28, 35, 12, 13] (Tr.chain 85 [55, 29, 47, 14, 32] (Tr.cycBad 0 3 1 2 [(14, 1), (29, 1), (47, -1), (55, -1), (81, -1), (85, 1)])), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.branch 8 [Tr.tab [16] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 5 2 3 [(19, 1), (29, 1), (39, 1), (50, -1), (55, -1), (60, 1), (67, 1), (89, -1)]), Tr.closed, Tr.tab [28] (Tr.chain 69 [0, 79, 32, 14] (Tr.tab [26, 12, 22, 41, 21, 13] (Tr.chain 24 [60, 50, 11, 46] (Tr.closed)))), Tr.closed, Tr.closed]), Tr.tab [41, 12, 26, 37] (Tr.cycBad 0 4 1 3 [(0, 1), (14, 1), (32, -1), (50, 1), (70, -1), (89, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 13 [Tr.tab [21, 41, 11, 28] (Tr.cycBad 1 5 2 4 [(19, -1), (29, -1), (32, 1), (41, -1), (60, -1)]), Tr.tab [21, 22, 43] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.cycBad 0 3 2 4 [(0, 1), (19, -1), (39, -1), (50, 1), (55, 1), (60, -1), (70, -1), (78, -1)]), Tr.closed, Tr.tab [29, 35, 14, 28, 41, 8, 16, 7, 26, 11] (Tr.chain 1 [55, 29, 47, 58, 87] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [21, 27, 38] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 28] (Tr.cycBad 0 4 2 3 [(0, 1), (19, -1), (29, -1), (39, -1), (50, 1), (55, 1), (60, -1), (69, -1), (78, -1)]), Tr.closed, Tr.tab [28, 31, 35, 7] (Tr.chain 2 [79, 0, 81] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub1624 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1624 : Settles 1190076756120829953 417153008797379629340341246 :=
  settles_of_check hand_sub1624 (by decide +kernel :
    check [] 159 1190076756120829953 417153008797379629340341246 tree_sub1624 = true)

/-- Subtree rooted at `(1190076751842656257, 574691131247192884081308670)`: 63 nodes (branch 4, chain 7, closed 34, cyc 3, forced 1, tab 14). -/
def tree_sub1625 : Tr := Tr.branch 11 [Tr.tab [20, 21, 43, 13, 37] (Tr.branch 12 [Tr.closed, Tr.tab [25, 41] (Tr.chain 11 [50, 60, 24, 46] (Tr.tab [44, 14, 24, 29] (Tr.cycBad 0 1 2 4 [(0, 1), (11, 1), (24, -1), (29, 1), (34, 1), (39, -1), (46, -2), (50, 1), (60, -1), (89, 1)]))), Tr.closed, Tr.tab [25, 34, 8, 24] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [21, 41, 44, 13, 24] (Tr.forced 10 [(24, 1), (29, 1), (40, 1), (50, -1), (60, 1)] (Tr.tab [7, 16, 43, 14, 29] (Tr.chain 7 [60, 24, 40, 89, 39] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 26] (Tr.branch 12 [Tr.tab [25, 44, 24] (Tr.branch 8 [Tr.closed, Tr.tab [41] (Tr.cycBad 0 4 1 3 [(0, 1), (14, 1), (22, -1), (29, 1), (55, -1), (60, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 31, 7, 43, 14] (Tr.cycBad 0 1 2 3 [(0, 2), (10, -6), (14, 3), (19, -3), (24, 4), (29, 2), (35, 1), (39, 1), (50, -4), (55, 2), (60, 1), (69, -3), (77, 2), (85, 1)]), Tr.closed, Tr.closed]), Tr.tab [22, 25, 41, 13] (Tr.chain 11 [50, 60, 24, 46] (Tr.tab [16, 44, 24, 7, 31] (Tr.chain 32 [14, 69, 0, 79] (Tr.closed)))), Tr.closed, Tr.tab [25, 34, 8, 24] (Tr.chain 2 [62, 50, 60, 24] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [21, 26, 41, 44, 12, 13, 24, 25, 8, 14] (Tr.chain 1 [55, 29, 41, 64, 40, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub1625 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub1625 : Settles 1190076751842656257 574691131247192884081308670 :=
  settles_of_check hand_sub1625 (by decide +kernel :
    check [] 103 1190076751842656257 574691131247192884081308670 tree_sub1625 = true)

end DistinctCircumradii

#print axioms DistinctCircumradii.settles_sub1601
#print axioms DistinctCircumradii.settles_sub1602
#print axioms DistinctCircumradii.settles_sub1603
#print axioms DistinctCircumradii.settles_sub1604
#print axioms DistinctCircumradii.settles_sub1605
#print axioms DistinctCircumradii.settles_sub1606
#print axioms DistinctCircumradii.settles_sub1607
#print axioms DistinctCircumradii.settles_sub1608
#print axioms DistinctCircumradii.settles_sub1609
#print axioms DistinctCircumradii.settles_sub1610
#print axioms DistinctCircumradii.settles_sub1611
#print axioms DistinctCircumradii.settles_sub1612
#print axioms DistinctCircumradii.settles_sub1613
#print axioms DistinctCircumradii.settles_sub1614
#print axioms DistinctCircumradii.settles_sub1615
#print axioms DistinctCircumradii.settles_sub1616
#print axioms DistinctCircumradii.settles_sub1617
#print axioms DistinctCircumradii.settles_sub1618
#print axioms DistinctCircumradii.settles_sub1619
#print axioms DistinctCircumradii.settles_sub1620
#print axioms DistinctCircumradii.settles_sub1621
#print axioms DistinctCircumradii.settles_sub1622
#print axioms DistinctCircumradii.settles_sub1623
#print axioms DistinctCircumradii.settles_sub1624
#print axioms DistinctCircumradii.settles_sub1625
