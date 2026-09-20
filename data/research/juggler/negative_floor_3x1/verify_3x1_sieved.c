/* 3x-1 shortcut verifier with a mod-2^K residue sieve.
 *
 * A start y whose first j steps have word w (a odd letters) satisfies
 *     2^j * y_j = 3^a * y - C(w),   C(w) >= 0,
 * because every odd step (3y-1)/2 SUBTRACTS. Hence
 *     y_j < y  <=>  y(3^a - 2^j) < C(w),
 * and when the prefix contracts (3^a < 2^j) the left side is negative while C >= 0, so the
 * drop holds for EVERY member of the class with no threshold at all. Only the classes whose
 * every prefix is non-contracting need walking; they are counted by OEIS A076227.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
typedef unsigned __int128 u128;

#define K 24
#define NRES (1ULL << K)

static unsigned char *bm;               /* bit r set  <=>  class r must be walked */

static int known(u64 y){ return y==1||y==5||y==7||y==10||y==17||y==25||y==37||y==55||y==82||y==41||y==61||y==91||y==136||y==68||y==34; }

/* build: keep r iff every prefix of its K-step word is non-contracting (3^a >= 2^j) */
static u64 build_sieve(void){
    bm = calloc(NRES/8 + 1, 1);
    if(!bm){ fprintf(stderr,"alloc failed\n"); exit(1); }
    u64 kept=0;
    /* pow3[a] and pow2[j] as long doubles avoid bignums; K=24 is far inside double range */
    double l2=0.6931471805599453, l3=1.0986122886681098;
    for(u64 r=0;r<NRES;r++){
        u64 v=r, a=0; int ok=1;
        for(int j=1;j<=K;j++){
            if(v&1){ v=(3*v-1)>>1; a++; } else { v>>=1; }
            v &= (NRES-1);                       /* only the low K bits matter for parity */
            if((double)a*l3 < (double)j*l2){ ok=0; break; }   /* 3^a < 2^j : contracts here */
        }
        if(ok){ bm[r>>3] |= (unsigned char)(1u<<(r&7)); kept++; }
    }
    return kept;
}

int main(int argc,char**argv){
    if(argc<3){ fprintf(stderr,"usage: %s lo hi [nosieve]\n",argv[0]); return 2; }
    u64 lo=strtoull(argv[1],0,10), hi=strtoull(argv[2],0,10);
    int use_sieve = (argc<4);
    u64 kept = use_sieve ? build_sieve() : 0;
    if(lo%2==0) lo++;
    u64 fails=0,cycles=0,maxsteps=0,walked=0,skipped=0; u128 peak=0;
    for(u64 y=lo;y<hi;y+=2){
        if(use_sieve && !((bm[(y&(NRES-1))>>3]>>((y&(NRES-1))&7))&1)){ skipped++; continue; }
        walked++;
        u128 v=y; u64 steps=0;
        for(;;){
            if(v&1){ v=(3*v-1)>>1; } else { v>>=1; }
            steps++; if(v>peak) peak=v;
            if(v<(u128)y) break;
            if(v==(u128)y){ if(!known(y)){ printf("NEW CYCLE at %llu\n",y); cycles++; } break; }
            if(v<=(u128)136 && known((u64)v)) break;
            if(steps>4000){ printf("STEPCAP at %llu\n",y); fails++; break; }
        }
        if(steps>maxsteps) maxsteps=steps;
    }
    printf("limit=%llu walked=%llu skipped=%llu fails=%llu new_cycles=%llu max_steps=%llu sieve_classes=%llu\n",
           hi,walked,skipped,fails,cycles,maxsteps,kept);
    { u64 h=(u64)(peak>>64), l=(u64)peak; printf("peak_hi=%llu peak_lo=%llu\n",h,l); }
    return 0;
}
