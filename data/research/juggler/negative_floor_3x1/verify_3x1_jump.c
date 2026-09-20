/* 3x-1 verifier: mod-2^K sieve + a 2^J jump table.
 *
 * SIEVE: a contracting prefix forces a drop for every member of the class, with no threshold,
 * because the odd step (3y-1)/2 subtracts. Only prefix-noncontracting classes need walking;
 * at K=24 there are 286581 of them, which is OEIS A076227(24).
 *
 * JUMP: for r mod 2^J, J steps send y = q*2^J + r to  y' = q*3^a + t(r),  where a = a(r) is the
 * odd-letter count of r's J-step word and t(r) is r's own J-step image. One multiply-add
 * replaces J iterations. This is the jump function of A368877 in the Eliahou-Fromentin-Simonetto
 * sense, used as an accelerator rather than as an object of study.
 */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
typedef unsigned __int128 u128;

#define K 24
#define NRES (1ULL<<K)
#define J 16
#define NJMP (1ULL<<J)

static unsigned char *bm;
static u64 jp3[NJMP];      /* 3^a(r) */
static u64 jpt[NJMP];      /* t(r), r's own J-step image (may exceed 2^J) */

static int known(u64 y){ return y==1||y==5||y==7||y==10||y==17||y==25||y==37||y==55||y==82||y==41||y==61||y==91||y==136||y==68||y==34; }

static void build(void){
    bm = calloc(NRES/8+1,1);
    double l2=0.6931471805599453, l3=1.0986122886681098;
    for(u64 r=0;r<NRES;r++){
        u64 v=r,a=0; int ok=1;
        for(int j=1;j<=K;j++){
            if(v&1){ v=(3*v-1)>>1; a++; } else { v>>=1; }
            v &= (NRES-1);
            if((double)a*l3 < (double)j*l2){ ok=0; break; }
        }
        if(ok) bm[r>>3] |= (unsigned char)(1u<<(r&7));
    }
    for(u64 r=0;r<NJMP;r++){
        u128 v=r; u64 a=0, p3=1;
        for(int j=0;j<J;j++){
            if(v&1){ v=(3*v-1)/2; a++; p3*=3; } else { v/=2; }
        }
        jp3[r]=p3; jpt[r]=(u64)v;
    }
}

int main(int argc,char**argv){
    if(argc<3){ fprintf(stderr,"usage: %s lo hi\n",argv[0]); return 2; }
    u64 lo=strtoull(argv[1],0,10), hi=strtoull(argv[2],0,10);
    build();
    if(lo%2==0) lo++;
    u64 fails=0,cycles=0,walked=0,skipped=0,maxsteps=0; u128 peak=0;
    for(u64 y=lo;y<hi;y+=2){
        if(!((bm[(y&(NRES-1))>>3]>>((y&(NRES-1))&7))&1)){ skipped++; continue; }
        walked++;
        u128 v=y; u64 steps=0;
        for(;;){
            if(v>>64){                                  /* too wide for the table: plain steps */
                if(v&1) v=(3*v-1)>>1; else v>>=1;
                steps++;
            } else {
                u64 w=(u64)v;
                if(w>=NJMP){
                    u64 r=w&(NJMP-1), q=w>>J;
                    v=(u128)q*jp3[r]+jpt[r];
                    steps+=J;
                } else { if(w&1) v=(3*(u128)w-1)>>1; else v=w>>1; steps++; }
            }
            if(v>peak) peak=v;
            if(v<(u128)y) break;
            if(v==(u128)y){ if(!known(y)){ printf("NEW CYCLE at %llu\n",y); cycles++; } break; }
            if(v<=(u128)136 && known((u64)v)) break;
            if(steps>40000){ printf("STEPCAP at %llu\n",y); fails++; break; }
        }
        if(steps>maxsteps) maxsteps=steps;
    }
    printf("limit=%llu walked=%llu skipped=%llu fails=%llu new_cycles=%llu max_steps=%llu\n",
           hi,walked,skipped,fails,cycles,maxsteps);
    { u64 h=(u64)(peak>>64), l=(u64)peak; printf("peak_hi=%llu peak_lo=%llu\n",h,l); }
    return 0;
}
