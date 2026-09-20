#!/bin/sh
# [2^40, 2^44) in 32 chunks, four at a time, in order.
# Batch-ordered so the completed prefix is always contiguous: if the container dies,
# whatever batches finished still certify a real floor.
LO=1099511627776
HI=17592186044416
N=32
SPAN=$(( (HI-LO)/N ))
for b in 0 1 2 3 4 5 6 7; do
  for k in 0 1 2 3; do
    i=$(( b*4 + k ))
    lo=$(( LO + i*SPAN ))
    hi=$(( LO + (i+1)*SPAN ))
    [ $i -eq $((N-1)) ] && hi=$HI
    ./j $lo $hi > p44_$i.out 2>&1 &
  done
  wait
  echo "batch $b done: chunks $((b*4))..$((b*4+3)) covered to $(( LO + (b+1)*4*SPAN ))" >> p44.progress
done
echo DONE > p44.flag
