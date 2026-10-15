/-
  `FractionalInstanton` — root module of the bundle.

  The modules under `FractionalInstanton/` each import Mathlib only and check on their own,
  so this root imports none of them; `lake build` builds every module through
  the glob in `lakefile.lean`.

  * `FractionalInstanton.ColumnChessboard`
-/
