#!/bin/bash
# 四本目（10-17 13:5x）：本線の残りの小さい側 2 区間、別の状態ファイル。設定は run905_full.sh と同じ行。
D=.
echo $$ > $D/W4.pid
ulimit -v 2000000
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 IVX_WIDEN=rel IVX_POLY=fast M904_HFAST=1 M905_RB=4
cd $D
echo "W4 start $(date '+%Y-%m-%d %H:%M:%S') N=2"
timeout 86400 nice -n 19 python3 $D/m904_full.py $D/FULL_W4_state.json $D/FULL_W4_out.json 80000 2 small
echo "W4 exit=$? $(date '+%Y-%m-%d %H:%M:%S')"
echo W4_FINISHED
