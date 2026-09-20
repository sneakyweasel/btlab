#!/bin/bash
# [2^40, 2^44) as 96 chunks of 5*2^35 numbers, 24 at a time, with the archived jump verifier compiled as ./j
# (gcc -O3 -march=native verify_3x1_jump.c). Used on 20 September 2026 under WSL2 on the laboratory machine;
# run.sh is the driver, chunk.sh the per-chunk worker it calls through xargs.

# ---- run.sh ----
cd ~/p44 || exit 1
mkdir -p out; rm -f out/DONE out/progress.log out/p44_*.out
echo "start $(date -u +%FT%TZ) gcc=$(gcc -dumpfullversion) nproc=$(nproc) binary_sha256=$(sha256sum j | cut -c1-16) source_sha256=$(sha256sum verify_3x1_jump.c | cut -c1-16)" >> out/progress.log
seq 0 95 | xargs -P 24 -n 1 ./chunk.sh
echo "end $(date -u +%FT%TZ)" >> out/progress.log
touch out/DONE

# ---- chunk.sh ----
# one chunk of [2^40, 2^44) with the archived jump verifier; called as ./chunk.sh <i>
i=$1
LO=1099511627776; HI=17592186044416; N=96
SPAN=$(( (HI-LO)/N ))
lo=$(( LO + i*SPAN )); hi=$(( LO + (i+1)*SPAN )); [ "$i" -eq $((N-1)) ] && hi=$HI
t0=$(date +%s)
nice -n 10 ./j "$lo" "$hi" > "out/p44_$i.out" 2>&1; rc=$?
echo "$(date -u +%T) chunk $i [$lo,$hi) rc=$rc secs=$(( $(date +%s)-t0 )) $(grep -o 'fails=[0-9]* new_cycles=[0-9]*' "out/p44_$i.out" | head -1)" >> out/progress.log
