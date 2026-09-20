/* 3x-1 shortcut map g(y)=y/2 (even), (3y-1)/2 (odd) on positive integers.
   Verify every odd y in [3, LIMIT) reaches one of the three known cycles.
   Ascending induction: stop as soon as an iterate drops below y. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
typedef unsigned __int128 u128;

static int known(u64 v){ return v==1ULL||v==5ULL||v==7ULL||v==10ULL||
  v==17ULL||v==25ULL||v==37ULL||v==55ULL||v==82ULL||v==41ULL||v==61ULL||
  v==91ULL||v==136ULL||v==68ULL||v==34ULL; }

int main(int argc,char**argv){
  u64 lo = strtoull(argv[1],0,0), limit = strtoull(argv[2],0,0); if(!(lo&1)) lo++; if(lo<3) lo=3;
  u64 fails=0, cycles=0, wide=0; u64 maxsteps=0; u128 peak=0;
  for(u64 y=lo; y<limit; y+=2){
    u128 v=y; u64 steps=0;
    for(;;){
      if(v&1){ v = (3*v-1)>>1; } else { v >>= 1; }
      steps++;
      if(v>peak) peak=v;
      if(v < (u128)y){ break; }                 /* dropped: covered by induction */
      if(v==(u128)y){ if(!known(y)){ printf("NEW CYCLE at %llu\n",y); cycles++; } break; }
      if(v <= (u128)136 && known((u64)v)){ break; }
      if(steps>4000){ printf("STEPCAP at %llu\n",y); fails++; break; }
    }
    if(steps>maxsteps) maxsteps=steps;
    if(v > (u128)6000000000000000000ULL) wide++;
  }
  printf("limit=%llu odd_starts=%llu fails=%llu new_cycles=%llu max_steps=%llu wide=%llu\n",
         limit,(limit-lo)/2,fails,cycles,maxsteps,wide);
  { u64 hi=(u64)(peak>>64), lo=(u64)peak; printf("peak_hi=%llu peak_lo=%llu\n",hi,lo); }
  return 0;
}
