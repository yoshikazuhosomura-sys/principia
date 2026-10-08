import Principia.DistinctCircumradii.Census.Tree338

/-!
# `CensusComplete`: subtrees 951-975

The transcripts of the subtrees, checked by the kernel.  Each theorem
discharges the nodes it hands on with the theorems of the deeper subtrees,
which come earlier in this chain of files.
-/

namespace DistinctCircumradii

/-- Subtree rooted at `(40537069646256132, 308646042337430270226982899)`: 55 nodes (branch 4, chain 3, closed 33, cyc 4, forced 1, tab 10). -/
def tree_sub0951 : Tr := Tr.branch 7 [Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 14, 26, 42, 11] (Tr.cycBad 0 2 1 3 [(2, -1), (11, 1), (12, 1), (27, 2), (38, 1), (42, -1), (52, -1), (71, 2), (76, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.cycBad 1 2 3 4 [(2, -1), (11, 1), (12, 1), (27, 1), (42, -1), (55, 1), (88, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 0 3 1 4 [(12, -1), (26, 1), (38, 1), (55, -1), (77, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39, 22, 23, 13, 27, 38, 3, 11, 20, 10] (Tr.cycBad 0 2 1 4 [(3, -2), (11, -1), (12, 2), (23, 2), (26, 1), (34, 2), (38, -1), (42, -1), (52, -1), (55, 1), (63, -1), (67, 1), (76, -2), (89, 2)]), Tr.closed, Tr.closed]), Tr.closed, Tr.branch 10 [Tr.tab [20, 22, 42, 3, 23, 27, 13, 29, 36, 11, 14] (Tr.chain 21 [79, 2, 58, 88, 33] (Tr.closed)), Tr.closed, Tr.tab [22, 39, 3, 23] (Tr.chain 6 [43, 55, 42, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [22, 36] (Tr.chain 3 [55, 42, 12, 63] (Tr.tab [42, 13, 23, 27, 38, 11] (Tr.forced 27 [(2, 1), (23, -1), (34, -1), (63, -1), (76, 1)] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed]

theorem hand_sub0951 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0951 : Settles 40537069646256132 308646042337430270226982899 :=
  settles_of_check hand_sub0951 (by decide +kernel :
    check [] 95 40537069646256132 308646042337430270226982899 tree_sub0951 = true)

/-- Subtree rooted at `(38298190109804560, 1145944741879177203068368877)`: 79 nodes (branch 6, chain 5, closed 55, forced 2, tab 11). -/
def tree_sub0952 : Tr := Tr.branch 9 [Tr.closed, Tr.closed, Tr.tab [42, 23] (Tr.branch 10 [Tr.closed, Tr.tab [21, 40, 14, 25] (Tr.chain 85 [55, 29, 65, 16] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 13 [Tr.forced 78 [(16, -1), (41, 1), (55, 1), (75, -1)] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 37, 14, 25, 12, 22, 1] (Tr.chain 1 [55, 29, 65, 51, 75] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 71 [(4, -1), (30, -1), (44, 1), (55, 1), (86, -1)] (Tr.tab [14, 26, 42, 23] (Tr.branch 10 [Tr.closed, Tr.tab [21, 40] (Tr.branch 1 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 12] (Tr.chain 8 [44, 11, 46] (Tr.closed)), Tr.closed, Tr.tab [22, 25] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 12 [Tr.closed, Tr.tab [22, 1] (Tr.chain 8 [44, 11, 46] (Tr.closed)), Tr.closed, Tr.tab [22, 25, 1] (Tr.chain 10 [86, 55, 1, 75, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed])), Tr.closed, Tr.closed]

theorem hand_sub0952 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0952 : Settles 38298190109804560 1145944741879177203068368877 :=
  settles_of_check hand_sub0952 (by decide +kernel :
    check [] 119 38298190109804560 1145944741879177203068368877 tree_sub0952 = true)

/-- Subtree rooted at `(4879200964460886884488, 413296630477548303335552627)`: 15 nodes (branch 1, chain 1, closed 8, cyc 2, tab 3). -/
def tree_sub0953 : Tr := Tr.branch 12 [Tr.closed, Tr.tab [41] (Tr.cycBad 0 3 1 5 [(3, -1), (7, 1), (36, 1), (41, -1), (46, 1), (50, -1), (63, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 35] (Tr.chain 58 [87, 7, 72, 25] (Tr.tab [11, 38, 16] (Tr.cycBad 0 5 1 3 [(3, -2), (7, 1), (25, -1), (36, 1), (41, -1), (58, 1), (63, -1), (72, -1), (87, -1)]))), Tr.closed, Tr.closed]

theorem hand_sub0953 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0953 : Settles 4879200964460886884488 413296630477548303335552627 :=
  settles_of_check hand_sub0953 (by decide +kernel :
    check [] 55 4879200964460886884488 413296630477548303335552627 tree_sub0953 = true)

/-- Subtree rooted at `(1225542203242201152, 256090096068969348812715935)`: 66 nodes (branch 5, chain 4, closed 43, cyc 3, tab 11). -/
def tree_sub0954 : Tr := Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 37, 19] (Tr.branch 5 [Tr.tab [44, 20] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [22, 39, 12, 18] (Tr.chain 71 [45, 6, 49, 23] (Tr.tab [26, 8, 31, 6] (Tr.cycBad 0 3 2 4 [(6, 1), (14, -1), (45, -1), (56, 1), (85, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 6 [Tr.closed, Tr.tab [18] (Tr.branch 8 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14] (Tr.chain 20 [14, 34, 89, 15, 68, 5] (Tr.closed)), Tr.closed, Tr.tab [29, 14] (Tr.chain 1 [85, 56, 49, 6, 75] (Tr.closed)), Tr.closed, Tr.closed]), Tr.tab [18, 39, 41, 8, 12, 14, 26] (Tr.chain 0 [21, 71, 23, 49, 6] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [22] (Tr.cycBad 0 4 1 3 [(6, 1), (23, 1), (34, 1), (44, -1), (49, 1), (56, -1), (60, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29] (Tr.cycBad 0 5 3 4 [(6, -1), (14, 1), (23, -1), (34, -1), (56, 1), (60, -1), (88, -1)]), Tr.closed, Tr.closed]

theorem hand_sub0954 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0954 : Settles 1225542203242201152 256090096068969348812715935 :=
  settles_of_check hand_sub0954 (by decide +kernel :
    check [] 106 1225542203242201152 256090096068969348812715935 tree_sub0954 = true)

/-- Subtree rooted at `(36319076680732674, 739312827705538147529827309)`: 231 nodes (assumed 2, branch 17, chain 18, closed 142, cyc 10, forced 2, symm 2, tab 38). -/
def tree_sub0955 : Tr := Tr.branch 8 [Tr.tab [16, 18, 44, 20, 24] (Tr.branch 7 [Tr.closed, Tr.tab [17, 38, 41, 4, 11, 26, 36] (Tr.chain 32 [14, 69, 12, 48] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [17, 26] (Tr.branch 11 [Tr.closed, Tr.tab [21, 41] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.cycBad 0 5 2 4 [(1, 1), (29, -1), (33, -1), (43, -1), (48, 1), (55, 1), (67, -1)], Tr.tab [27, 34, 22] (Tr.chain 83 [21, 67, 74, 11] (Tr.tab [28, 13, 29, 36] (Tr.chain 4 [67, 21, 33, 88] (Tr.cycBad 0 2 1 4 [(1, 1), (4, 2), (11, -11), (12, -1), (21, 10), (40, -1), (43, 1), (48, 1), (55, -2), (67, -10), (74, 10), (83, -10), (88, 1)])))), Tr.tab [27, 34, 22] (Tr.chain 83 [21, 67, 74, 11] (Tr.tab [28, 13, 29, 36, 19, 5, 38, 12] (Tr.chain 4 [67, 21, 33, 88] (Tr.chain 41 [70, 1, 55, 29] (Tr.closed))))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [38] (Tr.forced 60 [(11, 1), (33, 1), (58, -1), (67, 1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [17, 26, 38, 41, 4] (Tr.closed), Tr.closed, Tr.closed, Tr.closed]), Tr.tab [18, 41, 43, 9, 17, 22] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.tab [19, 37] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 34, 7, 24, 26, 14] (Tr.chain 0 [21, 83, 22, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.forced 83 [(1, -1), (22, 1), (23, -1), (26, 1), (33, 1), (48, -1), (78, 1)] (Tr.tab [14, 24, 7, 26] (Tr.chain 0 [21, 83, 22, 48, 12] (Tr.closed))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 30] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 34, 44, 4, 14, 20, 36, 11] (Tr.cycBad 0 1 4 5 [(33, 1), (40, -1), (43, 1), (48, -1), (59, 1)]), Tr.closed, Tr.tab [24, 26, 14, 28] (Tr.chain 0 [21, 83, 22, 48, 12] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [18, 25, 34, 22, 24] (Tr.branch 9 [Tr.tab [17, 44] (Tr.branch 7 [Tr.tab [43, 20] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 41] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37, 13, 29, 36, 5] (Tr.chain 78 [43, 55, 1, 70, 20] (Tr.tab [4] (Tr.cycBad 0 1 2 3 [(1, -1), (17, 1), (21, 2), (43, -1), (48, 1), (55, 1), (62, -1), (70, 1), (88, -1)]))), Tr.closed, Tr.tab [29, 13, 28, 37, 5] (Tr.chain 25 [43, 55, 1, 87, 58] (Tr.cycBad 0 1 2 3 [(1, -30), (10, 28), (12, 49), (17, -56), (20, -25), (21, -2), (25, 58), (33, -1), (43, -29), (48, -53), (55, 27), (58, -24), (62, 55), (77, 22), (82, -52), (87, -6)])), Tr.closed, Tr.closed], Tr.closed, Tr.tab [26, 36, 12, 13, 28, 29, 37, 4, 5] (Tr.chain 27 [21, 33, 82, 20, 38, 10] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.cycBad 0 2 3 5 [(12, 1), (17, 1), (33, -1), (43, -1), (55, 1), (76, -1), (83, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 36] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 11] (Tr.chain 46 [58, 88, 33, 83] (Tr.cycBad 1 4 3 5 [(1, -1), (17, -2), (21, 1), (38, 2), (46, -2), (48, -2), (55, -1), (58, 1), (62, 1), (88, -1)])), Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 5 [(17, 1), (33, -1), (48, 1), (55, 1), (62, -1), (78, -1), (83, 1), (88, -1)], Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 41] (Tr.branch 11 [Tr.tab [20, 43, 12] (Tr.chain 76 [34, 77, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [20] (Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37, 13, 29, 36, 5] (Tr.chain 4 [67, 21, 33, 88] (Tr.tab [4] (Tr.chain 78 [43, 55, 1, 70, 20] (Tr.cycBad 0 1 2 3 [(1, 4), (4, -24), (12, 13), (17, -2), (20, 8), (21, -9), (33, 5), (43, -6), (48, -15), (55, 12), (58, 3), (62, 12), (67, -5), (70, -23), (77, 3), (78, 2), (88, 1)])))), Tr.closed, Tr.tab [29, 13, 28, 37, 5] (Tr.chain 25 [43, 55, 1, 87, 58] (Tr.tab [4] (Tr.chain 38 [20, 82, 33, 21, 67] (Tr.cycBad 0 1 2 3 [(1, -1), (12, -1), (17, 1), (20, 3), (21, -1), (38, -5), (48, 3), (55, 3), (58, 3), (62, -2), (67, 1), (82, -1), (87, -4)])))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28] ((Tr.symm (2, 3, 1, 0, 4, 5) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, (Tr.symm (0, 2, 1, 4, 5, 3) Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0955 : ∀ x ∈ ([(1225542203242201152, 256090096068969348812715935), (4879200964460886884488, 413296630477548303335552627)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0954 (all_settles_cons settles_sub0953 all_settles_nil))

theorem settles_sub0955 : Settles 36319076680732674 739312827705538147529827309 :=
  settles_of_check hand_sub0955 (by decide +kernel :
    check [(1225542203242201152, 256090096068969348812715935), (4879200964460886884488, 413296630477548303335552627)] 271 36319076680732674 739312827705538147529827309 tree_sub0955 = true)

/-- Subtree rooted at `(36046492552675460, 224663440205168567538662259)`: 74 nodes (branch 5, chain 7, closed 42, cyc 4, forced 2, tab 14). -/
def tree_sub0956 : Tr := Tr.branch 7 [Tr.tab [19, 43, 9, 20, 29, 32, 22] (Tr.chain 77 [10, 86, 55, 28] (Tr.tab [27] (Tr.forced 71 [(2, -1), (36, -1), (44, 1), (55, 1), (86, -1)] (Tr.tab [26, 42, 13, 28, 11, 39, 10, 36] (Tr.chain 3 [55, 28, 35, 82] (Tr.cycBad 0 1 2 5 [(2, 3), (3, -1), (10, 1), (28, 1), (35, 1), (36, 3), (44, -3), (51, 1), (55, -3), (63, -2), (71, 2), (77, -2), (82, 2), (86, 3)])))))), Tr.closed, Tr.tab [19, 39, 42, 9] (Tr.chain 41 [35, 28, 55, 29] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 26, 32, 9, 18, 43, 22] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.forced 72 [(2, 1), (14, -1), (28, -1), (35, -1), (36, 1), (77, 1)] (Tr.branch 3 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 10 [Tr.tab [20, 42, 11] (Tr.chain 5 [44, 14, 34, 77, 35] (Tr.closed)), Tr.closed, Tr.tab [20, 39, 11, 28] (Tr.cycBad 2 3 4 5 [(23, -1), (28, 1), (35, 1), (67, -1), (72, 1), (81, 1)]), Tr.closed, Tr.closed, Tr.tab [20, 36] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.tab [23, 13] (Tr.chain 3 [55, 28, 35, 82] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 13] (Tr.chain 0 [67, 23, 53, 63] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [42, 20] (Tr.chain 82 [3, 55, 28, 35] (Tr.tab [13, 28, 11, 39, 10] (Tr.cycBad 0 1 2 5 [(2, -3), (3, -1), (14, 4), (28, 4), (36, -3), (44, -1), (51, -4), (63, 3), (72, 4), (82, -3)]))), Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.cycBad 0 1 2 3 [(7, -1), (14, 1), (23, -1), (28, 1), (89, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0956 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0956 : Settles 36046492552675460 224663440205168567538662259 :=
  settles_of_check hand_sub0956 (by decide +kernel :
    check [] 114 36046492552675460 224663440205168567538662259 tree_sub0956 = true)

/-- Subtree rooted at `(36033487258517572, 681636998800716168302548915)`: 66 nodes (branch 5, chain 4, closed 43, cyc 3, forced 1, tab 10). -/
def tree_sub0957 : Tr := Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 42, 19, 20] (Tr.branch 8 [Tr.tab [44, 9, 32, 22] (Tr.chain 66 [42, 55, 86, 38] (Tr.closed)), Tr.closed, Tr.closed, Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 2 3 4 5 [(6, 1), (27, -1), (38, -1), (55, 1), (70, -1), (77, 1)]), Tr.closed, Tr.tab [40] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [22, 32, 3, 9, 17] (Tr.chain 9 [43, 6, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 27, 3, 17, 9] (Tr.chain 1 [55, 86, 38, 20, 70] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.tab [35] (Tr.cycBad 1 3 2 4 [(2, 1), (20, -1), (34, -1), (38, 1), (53, 1), (55, -1), (87, 1)]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [28, 37] (Tr.cycBad 0 1 3 4 [(2, -1), (20, 1), (42, -1), (55, 1), (82, -1)]), Tr.closed, Tr.tab [29] (Tr.forced 28 [(2, -1), (20, 1), (27, 1), (42, -1), (55, 1), (88, -1)] (Tr.tab [8, 19, 40, 42, 9, 14, 27] (Tr.chain 3 [55, 28, 77, 34, 88] (Tr.closed)))), Tr.closed, Tr.closed]

theorem hand_sub0957 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0957 : Settles 36033487258517572 681636998800716168302548915 :=
  settles_of_check hand_sub0957 (by decide +kernel :
    check [] 106 36033487258517572 681636998800716168302548915 tree_sub0957 = true)

/-- Subtree rooted at `(1226114894181449729, 256241506335888113043191294)`: 53 nodes (branch 4, chain 1, closed 33, cyc 2, forced 2, leaf 2, tab 9). -/
def tree_sub0958 : Tr := Tr.branch 12 [Tr.tab [20, 44, 8, 21, 24, 29, 31] (Tr.forced 75 [(14, 1), (24, -1), (40, -1), (60, -1), (85, 1)] (Tr.tab [10] (Tr.branch 6 [Tr.tab [42, 14, 28, 13] (Tr.cycBad 0 2 1 4 [(9, 1), (14, -3), (24, 3), (35, 1), (40, 3), (50, 1), (56, -1), (60, 4), (75, 3), (83, -1), (85, -4), (88, 1)]), Tr.tab [40, 14] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.leaf (4, 3, 1, 5, 0, 2), Tr.closed, Tr.leaf (1, 2, 4, 0, 3, 5), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 37] (Tr.branch 8 [Tr.tab [16, 44, 24] (Tr.chain 46 [24, 60, 50, 11] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 31] (Tr.forced 75 [(14, 1), (24, -1), (40, -1), (60, -1), (85, 1)] (Tr.tab [10, 21, 13] (Tr.cycBad 0 4 3 5 [(0, -1), (14, 2), (23, -1), (24, -2), (40, -2), (43, 1), (50, -1), (56, 1), (60, -2), (70, 1), (75, -2), (85, 1), (88, -1)]))), Tr.tab [16, 29, 31, 44, 14, 24, 40] (Tr.closed), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0958 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0958 : Settles 1226114894181449729 256241506335888113043191294 :=
  settles_of_check hand_sub0958 (by decide +kernel :
    check [] 93 1226114894181449729 256241506335888113043191294 tree_sub0958 = true)

/-- Subtree rooted at `(18032025323716740, 222845326821434524949789555)`: 220 nodes (assumed 1, branch 17, chain 7, closed 141, cyc 12, forced 4, symm 1, tab 37). -/
def tree_sub0959 : Tr := Tr.branch 6 [Tr.closed, Tr.closed, Tr.tab [18, 39, 19] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 33] (Tr.branch 3 [Tr.tab [22, 42, 13, 20, 36] (Tr.branch 7 [Tr.tab [43] (Tr.branch 10 [Tr.closed, Tr.cycBad 0 1 2 5 [(10, 1), (21, 1), (35, -1), (39, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35, 11, 14] (Tr.cycBad 0 2 1 3 [(3, 2), (10, -2), (28, -1), (35, 1), (44, 1), (54, 1), (71, 2), (75, -1), (80, -2), (88, 2)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] (Tr.branch 10 [Tr.closed, Tr.cycBad 0 3 4 5 [(2, 1), (3, 2), (14, -2), (21, 1), (28, -1), (35, -1), (39, -1), (44, 2), (67, -1), (80, -1), (88, 2)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35, 11, 14] (Tr.cycBad 0 2 1 5 [(21, -1), (28, 1), (44, 1), (51, -1), (65, -1), (75, -1), (80, -1), (88, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 43, 13, 20] (Tr.chain 17 [44, 14, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29, 32, 22] (Tr.branch 3 [Tr.tab [42, 13, 20, 28] (Tr.chain 55 [28, 35, 82, 3] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [21] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 42, 20] (Tr.cycBad 0 5 2 3 [(7, 1), (21, 1), (28, -1), (37, -1), (53, 1), (54, 1)]), Tr.closed, Tr.closed, Tr.tab [28] (Tr.forced 87 [(7, 1), (28, -1), (37, -1), (54, 1), (82, 1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [25, 32, 22] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 42, 19, 20] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.cycBad 2 4 3 5 [(7, 1), (28, -1), (44, -1), (61, 1), (69, -1), (77, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [39] (Tr.forced 37 [(7, 1), (28, -1), (53, 1), (54, 1), (89, 1)] (Tr.tab [21, 33, 9, 10, 18, 43, 7] (Tr.chain 0 [61, 37, 7, 75] (Tr.closed)))), Tr.closed, Tr.closed], Tr.closed, Tr.tab [28, 35, 7, 43, 9, 33, 3] (Tr.cycBad 0 1 2 5 [(2, -1), (10, 1), (28, 1), (61, 1), (80, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [28] (Tr.forced 10 [(2, 1), (28, -1), (54, 1), (61, -1), (82, 1)] (Tr.tab [7, 19, 43] (Tr.closed))), Tr.closed, Tr.tab [29, 36] (Tr.branch 3 [Tr.tab [42, 19, 20] (Tr.chain 80 [3, 88, 14, 44] (Tr.tab [28, 7, 43] (Tr.cycBad 0 1 2 5 [(2, -1), (10, 1), (28, 1), (61, 1), (80, -1)]))), Tr.closed, Tr.closed, Tr.tab [21, 33] (Tr.branch 9 [Tr.closed, Tr.tab [19, 43, 7, 28] (Tr.chain 87 [7, 37, 61, 79, 2] (Tr.closed)), Tr.tab [19, 39, 42, 7, 14, 27] (Tr.chain 1 [28, 77, 27, 61, 37, 7] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [27, 31] (Tr.branch 7 [Tr.tab [19, 43, 20] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 33] (Tr.forced 39 [(2, 1), (28, -1), (35, -1), (73, -1), (80, 1)] (Tr.tab [10] (Tr.branch 10 [Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42] (Tr.cycBad 0 2 1 3 [(10, -1), (14, 1), (28, -1), (54, 1), (71, 1), (73, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.cycBad 0 3 1 2 [(2, -1), (7, 1), (10, 1), (14, -1), (44, 1), (80, -1), (89, 1)]), Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [36] (Tr.cycBad 1 5 3 4 [(2, 1), (10, -1), (14, 1), (28, -1), (44, -1), (63, -1), (80, 1)]), Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.tab [29, 32, 14, 22, 26, 42, 13, 28, 11, 39] (Tr.cycBad 0 2 1 3 [(10, -1), (14, 1), (28, -1), (54, 1), (71, 1), (73, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [19, 39, 42, 9, 14, 25, 43, 20, 22] (Tr.chain 41 [35, 28, 73, 27, 65] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 26, 32] ((Tr.symm (0, 2, 4, 1, 3, 5) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub0959 : ∀ x ∈ ([(1226114894181449729, 256241506335888113043191294)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0958 all_settles_nil)

theorem settles_sub0959 : Settles 18032025323716740 222845326821434524949789555 :=
  settles_of_check hand_sub0959 (by decide +kernel :
    check [(1226114894181449729, 256241506335888113043191294)] 260 18032025323716740 222845326821434524949789555 tree_sub0959 = true)

/-- Subtree rooted at `(221239333846909185, 597121361393153428250033406)`: 79 nodes (branch 7, chain 2, closed 57, cyc 5, forced 1, leaf 2, tab 5). -/
def tree_sub0960 : Tr := Tr.branch 13 [Tr.closed, Tr.tab [22, 43] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 40 [(19, 1), (26, -1), (52, 1), (56, 1), (61, -1)] (Tr.tab [11] (Tr.leaf (0, 1, 2, 3, 5, 4))), Tr.closed, Tr.branch 11 [Tr.closed, Tr.cycBad 0 4 1 2 [(0, -1), (8, 1), (19, 2), (22, -2), (26, -1), (40, -1), (49, -1), (52, 3), (56, 2), (57, -2), (73, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 20 [8, 81, 0, 73, 31, 26] (Tr.closed), Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 1 5 [(8, 1), (22, -1), (31, 1), (49, -1), (57, -1), (89, 1)], Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 2 4 3 5 [(19, 2), (22, -1), (47, -1), (49, -2), (52, 1), (56, 2), (57, -1), (61, -1), (84, 1)], Tr.closed, Tr.chain 81 [0, 73, 31, 84, 8] (Tr.tab [11] (Tr.leaf (3, 2, 4, 1, 5, 0))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 1 5 [(8, 1), (19, -2), (22, 1), (31, 1), (49, 1), (52, -2), (56, -2), (57, 1), (89, 1)], Tr.closed, Tr.closed], Tr.closed, Tr.closed]), Tr.closed, Tr.cycBad 0 4 2 3 [(0, 1), (19, 1), (22, -2), (31, 1), (49, -2), (52, 1), (56, 1), (57, -2), (76, 1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0960 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0960 : Settles 221239333846909185 597121361393153428250033406 :=
  settles_of_check hand_sub0960 (by decide +kernel :
    check [] 119 221239333846909185 597121361393153428250033406 tree_sub0960 = true)

/-- Subtree rooted at `(4874553248512080887874, 294925801587572403137920957)`: 30 nodes (branch 2, chain 1, closed 18, forced 2, leaf 1, tab 6). -/
def tree_sub0961 : Tr := Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.forced 21 [(1, 1), (29, -1), (35, 1), (40, -1), (83, 1)] (Tr.tab [6, 27, 39, 10, 24] (Tr.forced 88 [(24, 1), (50, -1), (67, 1), (83, 1)] (Tr.tab [13] (Tr.leaf (5, 0, 3, 2, 1, 4)))))), Tr.closed, Tr.tab [29, 39] (Tr.branch 6 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 27] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 10] (Tr.chain 0 [73, 1, 75] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub0961 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0961 : Settles 4874553248512080887874 294925801587572403137920957 :=
  settles_of_check hand_sub0961 (by decide +kernel :
    check [] 70 4874553248512080887874 294925801587572403137920957 tree_sub0961 = true)

/-- Subtree rooted at `(36319068365521025, 127576325195936299134926686)`: 236 nodes (assumed 4, branch 17, chain 15, closed 136, cyc 14, forced 3, symm 4, tab 43). -/
def tree_sub0962 : Tr := Tr.branch 5 [Tr.tab [44] (Tr.branch 12 [Tr.closed, Tr.tab [41] (Tr.branch 7 [Tr.closed, Tr.tab [17, 24] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38] (Tr.branch 10 [Tr.closed, Tr.cycBad 0 1 2 3 [(0, 2), (5, 4), (7, -1), (16, -3), (23, 2), (28, 3), (39, 5), (43, -2), (46, -4), (48, 3), (55, -1), (71, -2), (76, 1)], Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 2 1 4 [(0, -1), (16, 1), (28, 1), (48, 1), (55, -1), (63, 1), (76, -1)], Tr.cycBad 0 1 2 3 [(0, 2), (5, 4), (7, -1), (16, -3), (23, 2), (28, 3), (39, 5), (43, -2), (46, -4), (48, 3), (55, -1), (71, -2), (76, 1)], Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [28] (Tr.branch 11 [Tr.cycBad 0 2 1 3 [(28, 1), (34, 1), (43, 1), (46, -1), (55, -1)], Tr.closed, Tr.closed, Tr.chain 25 [43, 55, 28, 46, 58] (Tr.cycBad 0 2 1 4 [(7, 1), (16, 1), (25, -1), (48, 1), (55, -1), (58, -1), (71, -1), (82, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [36] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 4 1 5 [(0, -1), (7, 1), (16, 1), (38, -1), (43, 1), (71, -1), (88, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.chain 8 [78, 43, 55, 28, 46] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29] (Tr.cycBad 0 2 1 3 [(0, -1), (16, 1), (23, -1), (28, 1), (43, 1), (55, -1), (89, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [24, 34, 14] (Tr.chain 2 [56, 23, 59, 46] (Tr.closed)), Tr.closed, Tr.tab [24, 26, 14, 29] (Tr.cycBad 2 4 3 5 [(0, 1), (28, -1), (43, -1), (48, 1), (55, 1), (67, -1), (89, 1)]), Tr.tab [17, 24, 26, 14, 29] (Tr.cycBad 0 2 1 3 [(0, -1), (16, 1), (23, -1), (28, 1), (43, 1), (55, -1), (89, -1)]), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [25, 38] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [42] (Tr.branch 10 [Tr.closed, Tr.tab [21] (Tr.forced 34 [(5, 1), (39, 1), (43, -1), (48, 1)] (Tr.tab [11] (Tr.branch 11 [Tr.branch 7 [Tr.closed, Tr.tab [17, 24, 41, 14] (Tr.chain 18 [48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.tab [24, 34, 14] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.tab [24] (Tr.chain 63 [0, 67, 23, 53] (Tr.closed)), Tr.tab [17, 24, 41, 14] (Tr.chain 18 [48, 16, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 4 [Tr.closed, Tr.tab [17] (Tr.cycBad 0 2 1 4 [(0, -1), (5, 1), (7, 1), (14, -2), (23, 1), (28, 3), (34, 2), (39, 1), (43, 2), (53, -2), (55, -2), (64, -2), (81, 3)]), Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 24, 41, 7] (Tr.chain 17 [5, 64, 81, 0, 67, 23] (Tr.closed))), Tr.tab [34, 24] (Tr.cycBad 0 1 2 5 [(5, 1), (23, 1), (28, 1), (38, -1), (39, 1), (48, 1), (53, -1), (64, -1), (81, 1)]), Tr.tab [34, 24] (Tr.chain 77 [34, 25, 43, 55, 28] (Tr.tab [14, 41, 7] (Tr.chain 8 [38, 67, 0, 81] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35] (Tr.branch 14 [Tr.tab [24, 34, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [24] (Tr.forced 56 [(0, 1), (23, 1), (28, -1), (43, -1), (48, 1), (55, 1), (89, 1)] (Tr.closed)), Tr.tab [24, 34, 7] (Tr.chain 3 [55, 28, 59, 53] (Tr.closed)), Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [28] (Tr.cycBad 0 1 2 3 [(0, 1), (5, 1), (43, -1), (48, 1), (64, -1), (82, 1)]), Tr.closed, Tr.tab [29, 36] (Tr.branch 4 [Tr.closed, Tr.tab [17] (Tr.branch 7 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [24, 14] (Tr.chain 22 [56, 23, 59] (Tr.closed)), Tr.closed, Tr.tab [24, 26, 14, 27, 41] (Tr.forced 81 [(5, -1), (7, -1), (14, 1), (64, 1), (77, -1)] (Tr.chain 17 [5, 64, 81, 0, 67, 23] (Tr.closed))), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [21, 34, 24] (Tr.branch 7 [Tr.closed, Tr.tab [41, 14, 42] (Tr.cycBad 0 4 1 5 [(0, -1), (7, 1), (16, 1), (38, -1), (43, 1), (71, -1), (88, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [26, 14, 27] (Tr.cycBad 0 2 1 3 [(5, 1), (7, 1), (38, -1), (48, 1), (64, -1), (77, 1)]), Tr.tab [26, 41] (Tr.closed), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] ((Tr.symm (0, 4, 5, 2, 3, 1) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [35] ((Tr.symm (2, 4, 1, 0, 5, 3) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 30] ((Tr.symm (2, 4, 1, 0, 5, 3) Tr.assumed)), Tr.tab [29, 30, 44] ((Tr.symm (0, 2, 4, 1, 5, 3) Tr.assumed)), Tr.closed]

theorem hand_sub0962 : ∀ x ∈ ([(4724744420873505607680, 1033471806136218972356339321), (4724744664947873859585, 300862537935525393131583486), (4724888505275255885824, 453188593168944392538416891), (4874553248512080887874, 294925801587572403137920957)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0848 (all_settles_cons settles_sub0845 (all_settles_cons settles_sub0844 (all_settles_cons settles_sub0961 all_settles_nil))))

theorem settles_sub0962 : Settles 36319068365521025 127576325195936299134926686 :=
  settles_of_check hand_sub0962 (by decide +kernel :
    check [(4724744420873505607680, 1033471806136218972356339321), (4724744664947873859585, 300862537935525393131583486), (4724888505275255885824, 453188593168944392538416891), (4874553248512080887874, 294925801587572403137920957)] 276 36319068365521025 127576325195936299134926686 tree_sub0962 = true)

/-- Subtree rooted at `(7083765916897153912832, 965924553867666370003461883)`: 32 nodes (branch 2, chain 3, closed 17, cyc 2, forced 2, tab 6). -/
def tree_sub0963 : Tr := Tr.branch 9 [Tr.closed, Tr.tab [18, 41, 8] (Tr.chain 35 [41, 23, 56, 22] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [18] (Tr.cycBad 0 3 2 5 [(25, -1), (34, -1), (41, -1), (44, 1), (56, 1), (72, -1), (80, -1)]), Tr.tab [18, 41, 8] (Tr.chain 35 [41, 23, 56, 22] (Tr.closed)), Tr.tab [18, 29] (Tr.forced 2 [(12, -1), (44, 1), (57, 1), (71, -1), (86, -1)] (Tr.tab [2] (Tr.forced 66 [(25, -1), (31, 1), (57, -1), (72, -1), (86, 1)] (Tr.branch 8 [Tr.cycBad 0 4 1 2 [(2, -1), (11, -1), (21, 1), (25, -1), (31, 1), (34, 1), (44, 1), (57, -1), (66, -2), (71, -1)], Tr.closed, Tr.tab [40] (Tr.chain 77 [34, 25, 72, 31, 28] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed])))), Tr.closed, Tr.closed]

theorem hand_sub0963 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0963 : Settles 7083765916897153912832 965924553867666370003461883 :=
  settles_of_check hand_sub0963 (by decide +kernel :
    check [] 72 7083765916897153912832 965924553867666370003461883 tree_sub0963 = true)

/-- Subtree rooted at `(36319068122382465, 427692709348637175651892094)`: 230 nodes (assumed 3, branch 16, chain 14, closed 132, cyc 10, forced 8, symm 3, tab 44). -/
def tree_sub0964 : Tr := Tr.branch 7 [Tr.tab [43] (Tr.branch 11 [Tr.closed, Tr.tab [21, 41] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [42] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [25] (Tr.branch 8 [Tr.closed, Tr.tab [18] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 23, 13] (Tr.chain 9 [43, 25, 47, 71] (Tr.closed)), Tr.closed, Tr.tab [22, 23, 12] (Tr.chain 11 [50, 7, 52] (Tr.closed)), Tr.closed, Tr.tab [22, 23, 29, 12] (Tr.cycBad 0 3 1 2 [(25, -1), (35, -1), (40, 1), (43, 1), (48, 1), (55, -1), (84, -1)]), Tr.closed, Tr.closed]), Tr.tab [40, 23] (Tr.branch 5 [Tr.closed, Tr.tab [22, 38, 13] (Tr.cycBad 0 3 1 2 [(0, -1), (10, 1), (20, -1), (25, 1), (28, 1), (43, 1), (55, -1), (63, 1), (71, 1), (82, -1)]), Tr.closed, Tr.tab [22, 13] (Tr.chain 9 [43, 25, 47, 71] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 29, 12] (Tr.chain 76 [25, 43, 55, 28, 35] (Tr.tab [13] (Tr.cycBad 0 1 2 3 [(0, -1), (10, -1), (25, 3), (35, 3), (40, -1), (43, -1), (48, -2), (55, 2), (63, -1), (71, 1), (76, -1), (84, 1)]))), Tr.closed, Tr.closed]), Tr.tab [34, 22] (Tr.cycBad 0 4 1 2 [(0, -1), (7, 1), (17, -1), (43, 1), (48, -1), (55, -1), (62, 1), (63, -1), (71, -1)]), Tr.tab [34, 40, 22, 23] (Tr.cycBad 0 4 1 2 [(0, -1), (7, 1), (17, -1), (43, 1), (48, -1), (55, -1), (62, 1), (63, -1), (71, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [27, 35] (Tr.branch 13 [Tr.closed, Tr.tab [22, 34, 5, 23] (Tr.chain 9 [43, 25, 47, 71] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [22] (Tr.forced 50 [(7, 1), (10, -1), (17, 1), (25, -1), (48, 1), (75, -1), (82, 1)] (Tr.tab [5, 23, 40, 12] (Tr.chain 11 [50, 7, 52] (Tr.closed)))), Tr.tab [22, 34, 5, 23] (Tr.chain 9 [43, 25, 47, 71] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [28, 40, 23] (Tr.branch 8 [Tr.closed, Tr.tab [18] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 13] (Tr.chain 14 [44, 17, 47] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 29] (Tr.cycBad 0 1 4 5 [(10, 1), (25, 1), (40, -1), (48, -1), (84, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [25, 34, 22] (Tr.forced 58 [(0, -1), (17, -1), (25, 1), (40, 1), (48, -1), (62, 1), (83, -1)] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [29] (Tr.cycBad 0 3 2 4 [(0, 1), (7, 1), (17, 1), (25, -1), (40, -1), (43, -1), (48, 1), (89, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [38] (Tr.branch 8 [Tr.closed, Tr.tab [18, 41] (Tr.branch 5 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [22, 23, 13] (Tr.chain 8 [44, 17, 47, 58] (Tr.closed)), Tr.closed, Tr.tab [22, 23, 40, 12, 13] (Tr.chain 11 [50, 7, 52] (Tr.closed)), Tr.closed, Tr.tab [22, 23, 29, 12, 20] (Tr.cycBad 0 1 2 4 [(25, 1), (35, 1), (43, -1), (55, 1), (58, -1)]), Tr.closed, Tr.closed]), Tr.tab [40, 23] (Tr.chain 46 [58, 25, 43, 55, 28] (Tr.tab [12, 22, 41] (Tr.branch 5 [Tr.closed, Tr.forced 75 [(10, -1), (20, 1), (25, -1), (46, -1), (58, 1)] (Tr.tab [10] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [42, 14] (Tr.cycBad 0 1 2 4 [(0, 1), (20, 1), (25, -1), (43, -1), (46, -1), (48, 1), (89, 1)]), Tr.closed, Tr.closed, Tr.cycBad 0 1 2 4 [(7, -1), (10, 1), (17, -1), (25, 1), (28, 1), (75, 1), (82, -1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [42, 13, 14] (Tr.chain 38 [20, 82, 33, 89, 10] (Tr.closed)), Tr.closed])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.forced 39 [(10, 1), (17, -1), (25, 4), (28, -3), (43, -3), (46, 3), (48, -1), (55, 3), (58, -3), (84, 1)] (Tr.tab [10] (Tr.forced 63 [(10, -1), (25, -3), (28, 2), (43, 3), (46, -2), (55, -2), (58, 3), (84, -1)] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [42, 14] (Tr.chain 38 [84, 7, 39, 89, 10] (Tr.closed)), Tr.closed, Tr.closed, Tr.forced 38 [(0, -1), (10, -1), (17, 1), (25, -1), (28, 1), (39, 1), (43, 1), (48, 1), (58, 1), (82, -1), (84, -1)] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed]))), Tr.tab [34, 22] (Tr.forced 82 [(0, -1), (17, -1), (25, 1), (48, -1), (62, 1)] (Tr.tab [13, 28] ((Tr.symm (1, 3, 2, 0, 5, 4) Tr.assumed)))), Tr.tab [34, 40, 22, 23] (Tr.chain 46 [58, 25, 43, 55, 28] (Tr.tab [12, 41] (Tr.forced 38 [(17, 1), (25, -1), (28, 1), (43, 1), (48, 1), (58, 1), (62, -1)] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [35] ((Tr.symm (0, 3, 1, 5, 4, 2) Tr.assumed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [26] ((Tr.symm (0, 2, 1, 4, 5, 3) Tr.assumed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0964 : ∀ x ∈ ([(1225559641325306113, 137692940610706821325741822), (1226106098365239560, 381931964221076279098470135), (7083765916897153912832, 965924553867666370003461883)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0759 (all_settles_cons settles_sub0757 (all_settles_cons settles_sub0963 all_settles_nil)))

theorem settles_sub0964 : Settles 36319068122382465 427692709348637175651892094 :=
  settles_of_check hand_sub0964 (by decide +kernel :
    check [(1225559641325306113, 137692940610706821325741822), (1226106098365239560, 381931964221076279098470135), (7083765916897153912832, 965924553867666370003461883)] 270 36319068122382465 427692709348637175651892094 tree_sub0964 = true)

/-- Subtree rooted at `(4874589281123014033472, 147331779082235202848669627)`: 53 nodes (branch 4, chain 3, closed 35, cyc 2, tab 9). -/
def tree_sub0965 : Tr := Tr.branch 2 [Tr.tab [41, 21] (Tr.chain 81 [6, 72, 50, 62, 2] (Tr.tab [11, 28, 35] (Tr.cycBad 1 5 3 4 [(2, 1), (6, -1), (29, -1), (50, 1), (62, -1), (81, 1)]))), Tr.closed, Tr.tab [35] (Tr.branch 12 [Tr.tab [20, 44, 21, 11, 39, 14] (Tr.chain 5 [50, 72, 6, 51, 77, 35] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [37] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [41, 21] (Tr.cycBad 1 5 3 4 [(6, -1), (14, 1), (29, -1), (42, -1), (50, 1), (77, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.branch 11 [Tr.tab [21, 43] (Tr.closed), Tr.tab [21, 13] (Tr.chain 1 [55, 29, 41, 70] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0965 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0965 : Settles 4874589281123014033472 147331779082235202848669627 :=
  settles_of_check hand_sub0965 (by decide +kernel :
    check [] 93 4874589281123014033472 147331779082235202848669627 tree_sub0965 = true)

/-- Subtree rooted at `(4869977595104588742720, 766301743384693114872510395)`: 13 nodes (branch 1, closed 8, cyc 2, tab 2). -/
def tree_sub0966 : Tr := Tr.branch 8 [Tr.tab [44] (Tr.cycBad 0 2 1 5 [(11, -1), (14, 1), (21, 1), (39, -1), (67, -1), (72, 1)]), Tr.closed, Tr.closed, Tr.tab [25, 34, 14, 41, 21] (Tr.cycBad 1 5 3 4 [(6, -1), (14, 1), (29, -1), (42, -1), (50, 1), (77, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0966 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0966 : Settles 4869977595104588742720 766301743384693114872510395 :=
  settles_of_check hand_sub0966 (by decide +kernel :
    check [] 53 4869977595104588742720 766301743384693114872510395 tree_sub0966 = true)

/-- Subtree rooted at `(4869977595104586647616, 147331728353689030212171707)`: 107 nodes (branch 7, chain 9, closed 58, cyc 6, forced 2, tab 25). -/
def tree_sub0967 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [25] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [41, 21] (Tr.chain 51 [6, 72, 50, 11, 77] (Tr.tab [11] (Tr.cycBad 0 2 1 5 [(6, 2), (11, -1), (29, 4), (39, 3), (42, 4), (50, -5), (51, -1), (55, -3), (64, -1), (67, 3), (72, 1), (77, 2)]))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.branch 2 [Tr.tab [41, 21] (Tr.branch 11 [Tr.tab [43, 13] (Tr.cycBad 0 2 1 3 [(6, -1), (11, 1), (29, -3), (34, -1), (39, -2), (42, -2), (50, 4), (55, 3), (67, -3), (72, -2), (82, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 13] (Tr.chain 5 [50, 72, 6, 81, 64] (Tr.closed)), Tr.tab [28, 43] (Tr.closed), Tr.closed]), Tr.closed, Tr.tab [35] (Tr.chain 41 [64, 24, 42, 55, 29] (Tr.tab [13, 21, 11] (Tr.chain 1 [42, 24, 40, 89, 39] (Tr.closed)))), Tr.tab [20] (Tr.forced 82 [(11, 1), (29, -1), (32, -1), (39, -1), (42, -1), (50, 2), (55, 2), (67, -1), (72, -1)] (Tr.tab [13, 21, 28] (Tr.closed))), Tr.tab [20, 35, 11, 21, 13] (Tr.chain 1 [42, 24, 40, 89, 39] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [37] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 1 4 2 3 [(6, 1), (11, -1), (29, 1), (39, 1), (42, 1), (50, -2), (55, -1), (65, 1), (67, 1), (72, 1)]), Tr.closed, Tr.tab [41, 21] (Tr.chain 51 [6, 72, 50, 11, 77] (Tr.tab [11] (Tr.cycBad 1 5 3 4 [(11, -1), (14, 1), (39, 1), (50, -1), (51, -1), (55, -1), (67, 1), (72, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39] (Tr.branch 13 [Tr.tab [21, 41, 11] (Tr.chain 1 [55, 29, 41, 70] (Tr.closed)), Tr.tab [21, 43, 11, 35] (Tr.chain 46 [81, 6, 72, 50, 11] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [35] (Tr.branch 2 [Tr.tab [41, 21] (Tr.cycBad 1 4 2 3 [(2, 1), (11, -1), (29, 1), (39, 1), (42, 1), (50, -1), (55, -2), (67, 1), (72, 1), (87, 1)]), Tr.closed, Tr.closed, Tr.tab [20] (Tr.forced 82 [(11, 1), (29, -1), (32, -1), (39, -1), (42, -1), (50, 2), (55, 2), (67, -1), (72, -1)] (Tr.tab [13, 21, 29, 11] (Tr.chain 77 [51, 6, 72, 50, 11] (Tr.tab [14] (Tr.cycBad 1 5 3 4 [(6, -2), (14, 1), (29, -2), (32, 1), (39, -1), (42, -2), (50, 2), (51, 1), (67, -1), (77, -2), (82, 1)]))))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub0967 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0967 : Settles 4869977595104586647616 147331728353689030212171707 :=
  settles_of_check hand_sub0967 (by decide +kernel :
    check [] 147 4869977595104586647616 147331728353689030212171707 tree_sub0967 = true)

/-- Subtree rooted at `(4796189558880069746760, 190304169442108456912336823)`: 37 nodes (branch 3, chain 1, closed 25, cyc 3, tab 5). -/
def tree_sub0968 : Tr := Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 34, 38, 4, 9, 23, 24] (Tr.chain 4 [49, 72, 26, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29] (Tr.branch 9 [Tr.tab [17, 44, 24] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.cycBad 0 5 1 4 [(3, -1), (17, -1), (18, -1), (38, 2), (46, -1), (66, -1), (72, -1), (88, -1)], Tr.closed, Tr.tab [23] (Tr.cycBad 0 3 2 4 [(18, -1), (39, -1), (49, 1), (55, 1), (66, -1), (72, -1), (88, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [43] (Tr.cycBad 0 4 1 3 [(6, 1), (23, 1), (39, 1), (46, -1), (55, -1), (66, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]

theorem hand_sub0968 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0968 : Settles 4796189558880069746760 190304169442108456912336823 :=
  settles_of_check hand_sub0968 (by decide +kernel :
    check [] 77 4796189558880069746760 190304169442108456912336823 tree_sub0968 = true)

/-- Subtree rooted at `(4869943819765240840260, 763883891781635087559276475)`: 15 nodes (branch 1, chain 2, closed 9, cyc 1, tab 2). -/
def tree_sub0969 : Tr := Tr.branch 8 [Tr.chain 77 [51, 6, 72, 50, 11] (Tr.tab [14] (Tr.cycBad 0 4 1 2 [(11, -1), (14, 1), (29, -1), (33, -1), (42, -1), (50, 1), (51, -1), (67, -1), (72, 1)])), Tr.closed, Tr.closed, Tr.tab [25] (Tr.chain 16 [62, 50, 72, 6, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0969 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0969 : Settles 4869943819765240840260 763883891781635087559276475 :=
  settles_of_check hand_sub0969 (by decide +kernel :
    check [] 55 4869943819765240840260 763883891781635087559276475 tree_sub0969 = true)

/-- Subtree rooted at `(4869942691670085615680, 912581771629319000023873439)`: 71 nodes (branch 5, chain 7, closed 44, cyc 2, tab 13). -/
def tree_sub0970 : Tr := Tr.branch 12 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [25] (Tr.branch 5 [Tr.tab [19, 44, 8, 18, 41, 43, 9] (Tr.chain 53 [33, 21, 67, 23] (Tr.closed)), Tr.closed, Tr.tab [19, 37, 40, 8, 18, 9] (Tr.chain 12 [24, 64, 26, 72, 6] (Tr.closed)), Tr.closed, Tr.closed, Tr.tab [19, 33] (Tr.branch 8 [Tr.tab [18, 44, 9] (Tr.chain 77 [51, 6, 72, 50, 11] (Tr.tab [14] (Tr.cycBad 0 1 2 3 [(6, -1), (11, 3), (14, -1), (29, 1), (33, 1), (42, 1), (50, 1), (51, 2), (64, -1), (67, 1), (72, -3), (77, -1)]))), Tr.tab [18, 41, 43, 9] (Tr.chain 53 [33, 21, 67, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.tab [37, 19] (Tr.branch 5 [Tr.tab [44, 8, 18, 41, 43, 9, 13] (Tr.chain 4 [67, 21, 33, 88] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [33] (Tr.branch 8 [Tr.tab [18, 44, 9] (Tr.chain 77 [51, 6, 72, 50, 11] (Tr.tab [14] (Tr.cycBad 0 3 1 2 [(11, 1), (14, -1), (24, 1), (29, 1), (33, 1), (42, 1), (51, 2), (70, -1), (72, -1)]))), Tr.tab [18, 41, 43, 9] (Tr.chain 53 [33, 21, 67, 23] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0970 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0970 : Settles 4869942691670085615680 912581771629319000023873439 :=
  settles_of_check hand_sub0970 (by decide +kernel :
    check [] 111 4869942691670085615680 912581771629319000023873439 tree_sub0970 = true)

/-- Subtree rooted at `(4796189558880069746752, 190304169433101257657595823)`: 218 nodes (assumed 3, branch 16, chain 15, closed 135, cyc 7, forced 2, symm 3, tab 37). -/
def tree_sub0971 : Tr := Tr.branch 8 [Tr.tab [44, 24] (Tr.branch 7 [Tr.closed, Tr.tab [17] (Tr.branch 4 [Tr.tab [43] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 38, 13] (Tr.chain 5 [74, 4, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 13, 23, 42, 14] (Tr.cycBad 0 2 3 4 [(4, 1), (16, -1), (18, -1), (26, 1), (53, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [34, 27] (Tr.branch 9 [Tr.closed, Tr.tab [43] (Tr.chain 71 [39, 18, 66, 38, 23] (Tr.tab [14, 42, 13] (Tr.cycBad 0 3 1 2 [(6, -1), (16, 1), (23, -3), (26, 1), (38, 1), (39, -2), (46, 1), (66, -2), (71, 1), (72, 1), (88, -1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 13, 23, 42, 14, 43] (Tr.chain 1 [55, 86, 38, 66, 18] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [23, 32] (Tr.branch 9 [Tr.closed, Tr.tab [27, 43, 13, 29, 14] (Tr.chain 7 [72, 49, 23, 71, 39] (Tr.closed)), Tr.closed, Tr.tab [27, 38, 13] (Tr.chain 4 [49, 72, 26, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [39] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 34, 38, 11, 13] (Tr.chain 4 [74, 11, 46, 81, 6, 72, 26, 76] (Tr.tab [4] (Tr.chain 5 [74, 4, 76] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 32, 13] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.branch 4 [Tr.chain 28 [55, 86, 4, 58, 46] (Tr.closed), Tr.closed, Tr.closed, Tr.chain 1 [55, 86, 38, 66, 18] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.chain 5 [11, 46, 81, 6, 72, 26] (Tr.closed), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [42] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 34, 38, 9] (Tr.chain 25 [72, 26, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 9, 43] (Tr.chain 38 [66, 18, 39, 71, 23] (Tr.tab [4] (Tr.cycBad 0 2 1 3 [(6, -1), (11, 1), (18, 3), (23, 1), (26, 1), (27, 1), (38, -2), (39, 2), (66, 2), (71, -2), (88, -1)]))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 9 [Tr.closed, Tr.tab [27, 43] (Tr.cycBad 0 4 1 3 [(6, 1), (23, 1), (39, 1), (46, -1), (55, -1), (66, 1)]), Tr.closed, Tr.tab [27, 34, 38, 13] (Tr.chain 25 [72, 26, 76] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 29, 32, 13, 23, 42, 14, 43, 11, 38] (Tr.cycBad 2 3 4 5 [(11, 1), (39, 1), (58, -1), (72, -1), (79, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [25, 34, 24, 27] (Tr.branch 13 [Tr.closed, Tr.closed, Tr.tab [23, 42, 14, 29, 39] (Tr.branch 7 [Tr.closed, Tr.tab [17, 9, 43, 4] (Tr.chain 10 [38, 66, 18, 39, 89] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [28] (Tr.branch 9 [Tr.tab [17] (Tr.forced 58 [(17, 1), (39, 1), (72, -1), (79, 1)] (Tr.tab [11] (Tr.branch 4 [Tr.cycBad 1 4 2 3 [(4, -1), (17, 2), (39, 1), (46, 1), (55, 1), (58, -1), (62, -1), (72, -1), (79, 1), (89, -1)], Tr.closed, Tr.closed, Tr.chain 10 [38, 66, 18, 39, 89] (Tr.closed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.tab [43] (Tr.cycBad 0 4 1 3 [(6, 1), (23, 1), (39, 1), (46, -1), (55, -1), (66, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 14] (Tr.forced 34 [(6, -1), (18, 1), (39, 1), (62, 1), (71, -1), (72, -1), (88, -1)] (Tr.tab [11, 43] ((Tr.symm (4, 2, 0, 1, 3, 5) Tr.assumed)))), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [31] ((Tr.symm (4, 2, 0, 1, 3, 5) Tr.assumed)), Tr.tab [31, 44, 24] ((Tr.symm (4, 2, 0, 1, 3, 5) Tr.assumed)), Tr.closed]

theorem hand_sub0971 : ∀ x ∈ ([(4869942691665790648384, 912581767017545024961230751), (4869942691670085615680, 912581771629319000023873439), (4869943819765240840260, 763883891781635087559276475)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0277 (all_settles_cons settles_sub0970 (all_settles_cons settles_sub0969 all_settles_nil)))

theorem settles_sub0971 : Settles 4796189558880069746752 190304169433101257657595823 :=
  settles_of_check hand_sub0971 (by decide +kernel :
    check [(4869942691665790648384, 912581767017545024961230751), (4869942691670085615680, 912581771629319000023873439), (4869943819765240840260, 763883891781635087559276475)] 258 4796189558880069746752 190304169433101257657595823 tree_sub0971 = true)

/-- Subtree rooted at `(1193453974339452928, 538743320391523644814506991)`: 144 nodes (branch 11, chain 8, closed 90, cyc 10, forced 1, tab 24). -/
def tree_sub0972 : Tr := Tr.branch 7 [Tr.tab [43] (Tr.branch 14 [Tr.closed, Tr.closed, Tr.tab [26, 42, 23] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [22] (Tr.forced 14 [(10, 1), (19, 1), (45, -1), (52, 1), (71, -1)] (Tr.tab [4, 17, 38, 11, 13] (Tr.chain 0 [36, 60, 26, 41, 71, 45] (Tr.closed)))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35, 11, 38] (Tr.cycBad 0 1 2 5 [(10, 1), (26, 1), (36, -1), (58, -1), (60, 1), (71, -1), (75, 1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 39, 23] (Tr.branch 9 [Tr.tab [17, 44] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.chain 33 [19, 49, 10, 89] (Tr.cycBad 0 1 2 3 [(10, -1), (22, 1), (33, 1), (52, -1)]), Tr.closed, Tr.tab [28] (Tr.chain 57 [52, 22, 32, 78, 19] (Tr.closed)), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 13 [Tr.cycBad 0 2 1 5 [(10, 1), (19, 1), (32, -1), (36, 1), (41, 1), (52, 1), (60, 1), (74, -1)], Tr.branch 10 [Tr.chain 49 [19, 33, 89, 10] (Tr.tab [4] (Tr.cycBad 0 1 2 3 [(10, -1), (22, 1), (33, 1), (52, -1)])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [35] (Tr.cycBad 0 1 4 5 [(10, 1), (47, -1), (52, 1), (55, -1), (60, 1), (75, 1)]), Tr.tab [35] (Tr.chain 49 [19, 33, 89, 10] (Tr.tab [4] (Tr.cycBad 0 1 2 3 [(10, 1), (22, -1), (26, 1), (33, -1), (36, -1), (47, 1), (60, 2), (74, -1), (75, 1), (89, 1)]))), Tr.closed], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.tab [39, 23] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.chain 41 [26, 60, 36, 27, 65] (Tr.tab [13, 44] (Tr.cycBad 0 5 2 4 [(19, -1), (26, 1), (32, 1), (36, -1), (52, -1), (65, -1)]))), Tr.tab [26, 42] (Tr.cycBad 1 2 4 5 [(26, -1), (27, 1), (36, 1), (60, -1), (71, 1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [26, 32] (Tr.branch 9 [Tr.tab [17, 44] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 0 5 2 4 [(19, -1), (26, 1), (32, 1), (36, -1), (52, -1), (65, -1)]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [39, 23] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38, 13, 43, 4] (Tr.chain 57 [52, 22, 32, 78, 19] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.tab [28, 35, 4, 10, 43, 13] (Tr.cycBad 0 3 2 5 [(4, 1), (19, 1), (22, 1), (32, -1), (67, 1), (76, -1), (89, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.tab [27] (Tr.chain 5 [74, 67, 36, 60, 26] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0972 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0972 : Settles 1193453974339452928 538743320391523644814506991 :=
  settles_of_check hand_sub0972 (by decide +kernel :
    check [] 184 1193453974339452928 538743320391523644814506991 tree_sub0972 = true)

/-- Subtree rooted at `(1193453974335258624, 499906578436403682577003503)`: 179 nodes (assumed 3, branch 13, chain 8, closed 105, cyc 10, forced 5, symm 2, tab 33). -/
def tree_sub0973 : Tr := Tr.branch 8 [Tr.tab [16, 44] (Tr.branch 9 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [27] (Tr.branch 13 [Tr.tab [23] (Tr.cycBad 0 1 2 5 [(11, 1), (26, 1), (32, -1), (41, 1), (55, 1), (60, 1), (74, -1)]), Tr.tab [22, 23, 43] (Tr.forced 49 [(11, -1), (32, 1), (47, -1), (55, -1), (74, 1)] (Tr.tab [4, 32] (Tr.chain 57 [52, 11, 74, 49, 19] (Tr.closed)))), Tr.tab [23, 39, 42, 10, 11, 14] (Tr.chain 6 [19, 53, 65, 51] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.tab [29, 32] (Tr.branch 7 [Tr.closed, Tr.tab [17, 41] (Tr.branch 14 [Tr.closed, Tr.tab [43] (Tr.cycBad 0 5 2 4 [(19, -1), (26, 1), (32, 1), (36, -1), (52, -1), (65, -1)]), Tr.tab [26, 42, 23] (Tr.branch 10 [Tr.closed, Tr.closed, Tr.tab [22] (Tr.forced 81 [(11, 1), (16, -1), (26, 1), (36, -1), (45, -1), (55, 1), (71, -1)] (Tr.tab [11, 28, 4] (Tr.cycBad 0 2 1 4 [(4, 1), (11, -2), (16, 1), (36, 1), (45, 2), (52, -1), (55, -2), (60, 1), (71, 1), (81, 1)]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 35, 11] (Tr.cycBad 0 5 1 4 [(11, -1), (19, 1), (26, -1), (36, 1), (58, 1), (75, -1), (86, -1)]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [39, 23] (Tr.branch 11 [Tr.closed, Tr.closed, Tr.closed, Tr.tab [38] (Tr.forced 78 [(19, -1), (32, 1), (58, -1), (60, -1), (86, 1)] (Tr.branch 4 [Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.branch 13 [Tr.chain 65 [27, 36, 60, 26, 41] (Tr.tab [14] (Tr.cycBad 0 5 2 4 [(19, -1), (26, 1), (32, 1), (36, -1), (52, -1), (65, -1)])), Tr.tab [22, 43] (Tr.branch 10 [Tr.tab [42, 14] (Tr.chain 5 [11, 77, 27, 36, 60, 26] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [27, 14] (Tr.cycBad 0 3 1 2 [(26, -1), (27, 1), (36, 2), (47, -1), (55, -1), (58, 1), (60, -1), (71, 2), (75, -1)]), Tr.tab [27, 42] (Tr.closed), Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed], Tr.tab [43, 13] (Tr.chain 65 [27, 36, 60, 26, 41] (Tr.tab [14] (Tr.cycBad 0 2 1 4 [(4, 1), (26, 2), (36, -1), (52, -1), (55, -1), (60, 1), (65, -1), (78, 1)]))), Tr.closed])), Tr.closed, Tr.tab [26] (Tr.forced 77 [(11, 1), (19, -1), (26, 1), (27, 1), (60, -1), (69, -1), (86, 1)] (Tr.tab [14] (Tr.chain 5 [11, 77, 27, 36, 60, 26] (Tr.closed)))), Tr.closed, Tr.tab [28, 35] (Tr.branch 4 [Tr.tab [43] (Tr.branch 10 [Tr.tab [42] (Tr.cycBad 0 3 1 2 [(4, -1), (11, 1), (33, 1), (36, 1), (60, -1), (81, -1)]), Tr.closed, Tr.cycBad 0 2 1 4 [(4, 1), (11, -1), (26, 1), (45, 1), (52, -1), (55, -1), (60, 1)], Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.tab [38] (Tr.forced 33 [(11, -1), (14, 1), (27, -1), (36, -1), (60, 1)] (Tr.tab [10, 42] (Tr.branch 13 [Tr.chain 65 [27, 36, 60, 26, 41] (Tr.tab [14] (Tr.cycBad 0 5 2 4 [(19, -1), (26, 1), (32, 1), (36, -1), (52, -1), (65, -1)])), Tr.tab [43, 14] (Tr.chain 5 [11, 77, 27, 36, 60, 26] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]))), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed]), Tr.closed, Tr.closed]), Tr.tab [41] (Tr.assumed), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, (Tr.symm (2, 0, 1, 5, 4, 3) Tr.assumed), Tr.tab [16, 44] ((Tr.symm (2, 0, 1, 5, 4, 3) Tr.assumed)), Tr.closed]

theorem hand_sub0973 : ∀ x ∈ ([(1193453974339452928, 538743320391523644814506991), (4796189558880069746752, 190304169433101257657595823), (4796189558880069746760, 190304169442108456912336823)] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  (all_settles_cons settles_sub0972 (all_settles_cons settles_sub0971 (all_settles_cons settles_sub0968 all_settles_nil)))

theorem settles_sub0973 : Settles 1193453974335258624 499906578436403682577003503 :=
  settles_of_check hand_sub0973 (by decide +kernel :
    check [(1193453974339452928, 538743320391523644814506991), (4796189558880069746752, 190304169433101257657595823), (4796189558880069746760, 190304169442108456912336823)] 219 1193453974335258624 499906578436403682577003503 tree_sub0973 = true)

/-- Subtree rooted at `(19516677758978160099600, 1199196822300145433473416943)`: 17 nodes (branch 1, chain 2, closed 9, cyc 1, tab 4). -/
def tree_sub0974 : Tr := Tr.branch 1 [Tr.closed, Tr.closed, Tr.tab [18, 22, 35, 10] (Tr.cycBad 0 4 1 3 [(15, -1), (18, -1), (26, 1), (33, 1), (41, 1), (43, 1), (74, -1)]), Tr.tab [20, 22, 33, 10] (Tr.chain 11 [74, 4, 69, 75, 52] (Tr.closed)), Tr.tab [18, 20, 22, 33, 35, 8] (Tr.closed), Tr.tab [22, 31, 10] (Tr.chain 6 [54, 42, 15, 45] (Tr.closed)), Tr.closed, Tr.closed, Tr.closed, Tr.closed]

theorem hand_sub0974 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0974 : Settles 19516677758978160099600 1199196822300145433473416943 :=
  settles_of_check hand_sub0974 (by decide +kernel :
    check [] 57 19516677758978160099600 1199196822300145433473416943 tree_sub0974 = true)

/-- Subtree rooted at `(4934541199362570078209, 1230681549826489834434181118)`: 14 nodes (branch 1, chain 1, closed 9, cyc 1, tab 2). -/
def tree_sub0975 : Tr := Tr.branch 11 [Tr.closed, Tr.tab [21, 13] (Tr.chain 24 [42, 55, 29, 41, 64] (Tr.cycBad 0 5 1 2 [(29, 1), (40, 1), (42, 1), (55, -1), (65, -1)])), Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.closed, Tr.tab [21, 28, 35, 2] (Tr.closed), Tr.closed, Tr.closed]

theorem hand_sub0975 : ∀ x ∈ ([] : List (Mask × Mask)),
    Settles x.1 x.2 :=
  all_settles_nil

theorem settles_sub0975 : Settles 4934541199362570078209 1230681549826489834434181118 :=
  settles_of_check hand_sub0975 (by decide +kernel :
    check [] 54 4934541199362570078209 1230681549826489834434181118 tree_sub0975 = true)

end DistinctCircumradii

#print axioms DistinctCircumradii.settles_sub0951
#print axioms DistinctCircumradii.settles_sub0952
#print axioms DistinctCircumradii.settles_sub0953
#print axioms DistinctCircumradii.settles_sub0954
#print axioms DistinctCircumradii.settles_sub0955
#print axioms DistinctCircumradii.settles_sub0956
#print axioms DistinctCircumradii.settles_sub0957
#print axioms DistinctCircumradii.settles_sub0958
#print axioms DistinctCircumradii.settles_sub0959
#print axioms DistinctCircumradii.settles_sub0960
#print axioms DistinctCircumradii.settles_sub0961
#print axioms DistinctCircumradii.settles_sub0962
#print axioms DistinctCircumradii.settles_sub0963
#print axioms DistinctCircumradii.settles_sub0964
#print axioms DistinctCircumradii.settles_sub0965
#print axioms DistinctCircumradii.settles_sub0966
#print axioms DistinctCircumradii.settles_sub0967
#print axioms DistinctCircumradii.settles_sub0968
#print axioms DistinctCircumradii.settles_sub0969
#print axioms DistinctCircumradii.settles_sub0970
#print axioms DistinctCircumradii.settles_sub0971
#print axioms DistinctCircumradii.settles_sub0972
#print axioms DistinctCircumradii.settles_sub0973
#print axioms DistinctCircumradii.settles_sub0974
#print axioms DistinctCircumradii.settles_sub0975
