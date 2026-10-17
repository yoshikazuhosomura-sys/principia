#!/bin/bash
# 見張り v2（10-17 09:5x）：W2 が 6 区間で止め、本線が 230 で止め、W2・W3 の完了を待って合流し、本線の台本を起動し直す。
D=.; cd $D; echo $$ > finish_w4.pid
cnt() { python3 -c "import json;print(len(json.load(open('$1'))['done']))" 2>/dev/null || echo 0; }
k2=0; km=0
while :; do
  if [ $k2 -eq 0 ] && [ "$(cnt FULL_W2_state.json)" -ge 6 ]; then for c in $(ps -o pid= --ppid $(cat W2.pid)); do kill $c; done; k2=1; echo "W2 stopped at 6 $(date '+%H:%M:%S')"; fi
  if [ $km -eq 0 ] && [ "$(cnt FULL_state.json)" -ge 228 ]; then for c in $(ps -o pid= --ppid $(cat FULL.pid)); do kill $c; done; km=1; echo "main stopped at 228 $(date '+%H:%M:%S')"; fi
  if grep -q W2_FINISHED W2.log && grep -q W3_FINISHED W3.log && grep -q W4_FINISHED W4.log && [ $km -eq 1 ]; then break; fi
  sleep 60
done
sleep 5; python3 merge_w4.py
setsid nohup $D/run905_full.sh >> $D/FULL.log 2>&1 < /dev/null &
sleep 120; tail -n 4 FULL.log
