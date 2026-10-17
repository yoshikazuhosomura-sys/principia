#!/bin/bash
# 二本目（10-17 07:2x）：小さい ħ の側から 9 区間、別の状態ファイル。設定は run905_full.sh と同じ。
D=.
echo $$ > $D/W2.pid
ulimit -v 2000000
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 IVX_WIDEN=rel IVX_POLY=fast M904_HFAST=1 M905_RB=4
cd $D
echo "W2 start $(date '+%Y-%m-%d %H:%M:%S') N=9"
timeout 86400 nice -n 19 python3 $D/m904_full.py $D/FULL_W2_state.json $D/FULL_W2_out.json 80000 9 small
echo "W2 exit=$? $(date '+%Y-%m-%d %H:%M:%S')"
echo W2_FINISHED
