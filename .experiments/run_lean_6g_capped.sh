#!/usr/bin/env bash
set -euo pipefail

lean6g_root=/home/g/proximity-prize-vm-clean-20260901
lean6g_experiments="$lean6g_root/yukon-6900-work/.experiments"
lean6g_legacy="$lean6g_root/yukon-6800-promoted/.lake/build/lib/lean"

exec {lean6g_slot_one}>>"$lean6g_experiments/.lean-probe-slot-1.lock"
exec {lean6g_slot_two}>>"$lean6g_experiments/.lean-probe-slot-2.lock"
while ! flock -n "$lean6g_slot_one"; do
  if flock -n "$lean6g_slot_two"; then
    break
  fi
  sleep 1
done

cd "$lean6g_root/yukon-6800-packed"
lean6g_path=$(env LEAN_PATH="$lean6g_experiments:$lean6g_legacy" \
  lake env printenv LEAN_PATH)

exec env LEAN_PATH="$lean6g_path" \
  /home/g/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean \
  -j1 -s4096 -M5500 --root="$lean6g_experiments" "$@"
