#!/bin/bash
# Re-run W-half(T).  Usage:
#   bash run.sh lift   LO HI REL     # cell test as in the original logs
#   bash run.sh strong LO HI REL     # cell test with the decrease test against the lower end of the cell
#   bash run.sh drop   LO HI REL     # decrease of the cell index, one box per cell
#   bash run.sh kappa  SMAX          # part (ii), e.g. SMAX=0.01658
#   bash run.sh cover                # coverage of the original logs (lift_cover.py, first 0.198)
# The programs read each other from their own directory (programs/).
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
PY=${PYTHON:-python3}
mode=$1; shift || true
case "$mode" in
  lift)   "$PY" "$HERE/programs/tube_lift.py" "$@" ;;
  strong) "$PY" "$HERE/programs/tube_lift_strong.py" "$@" ;;
  drop)   "$PY" "$HERE/programs/drop_check.py" "$@" ;;
  kappa)  "$PY" "$HERE/programs/tube_be_lift.py" "$@" ;;
  cover)  "$PY" "$HERE/programs/lift_cover.py" ;;
  *) echo "usage: run.sh lift|strong|drop LO HI REL | kappa SMAX | cover" >&2; exit 2 ;;
esac
