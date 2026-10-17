#!/bin/bash
# 第905便：全 239 区間の本番（この PC、同時一本）。状態ファイル FULL_state.json から続きへ。
# 一回の python は CPU・壁時計とも予算 80000 s（外側の timeout 86400）。予算で止まったら自動で次の回へ（最大 6 回）。
# 途中で止まっても、この台本を同じ行で起動し直せば続きから。
D=.
echo $$ > $D/FULL.pid
ulimit -v 2000000
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 IVX_WIDEN=rel IVX_POLY=fast M904_HFAST=1 M905_RB=4
cd $D
for seg in 1 2 3 4 5 6; do
  echo "SEGMENT $seg start $(date '+%Y-%m-%d %H:%M:%S')"
  timeout 86400 nice -n 19 python3 $D/m904_full.py $D/FULL_state.json $D/FULL_out.json 80000
  rc=$?
  echo "SEGMENT $seg exit=$rc $(date '+%Y-%m-%d %H:%M:%S')"
  if tail -n 3 $D/FULL.log | grep -q ALL_DONE; then echo "FULL_FINISHED $(date '+%Y-%m-%d %H:%M:%S')"; exit 0; fi
  if [ $rc -ne 0 ]; then echo "FULL_ABORTED rc=$rc"; exit $rc; fi
done
echo "FULL_SEGMENTS_EXHAUSTED"
