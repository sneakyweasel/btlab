/* 3x-1 GPU verifier: the descent certificate of verify_3x1_jump.c on CUDA.
 *
 * MAP.   g(y) = y/2 (y even), (3y-1)/2 (y odd) on the positive integers, the shortcut 3n+1 map
 *        read on the negative integers. Every odd start y0 >= 3 in [lo, hi) is iterated until an
 *        iterate drops below y0 (covered by induction on the starts below), returns to y0 (a
 *        cycle), or lands on an element of the three known cycles (1), (5,7,10), (17,...,34).
 *        A step cap turns a runaway into a reported failure. Same semantics as the C verifiers.
 *
 * SIEVE. A contracting prefix forces a drop for every member of a residue class mod 2^K, with
 *        no threshold, because the odd step subtracts: (3^c y - D)/2^k < y when 3^c < 2^k. Only
 *        prefix-noncontracting classes are walked; at K = 24 there are 286581, OEIS A076227(24),
 *        exactly as in verify_3x1_jump.c. The comparison 3^a >= 2^j is done in integers.
 *
 * STEPS. Barina's domain switch, which on this side is the run identity g^a(y) - 1 =
 *        (3/2)^a (y - 1): with u = y - 1 and a = ctz(u), the whole odd run is u -> (u >> a) 3^a,
 *        and the following even run is b = ctz(y) halvings at once. The value after an odd run
 *        is the trajectory's local maximum, so the recorded peak is the exact trajectory peak
 *        (the jump verifier only saw landings). The first halving that drops below y0 is found
 *        exactly, so max_steps is the plain walker's count, not the jump verifier's granular one.
 *
 * WIDTH. 128-bit state in two 64-bit limbs; a multiplication that would exceed 2^128 stops that
 *        start and reports it for a wide re-walk on the host. Below 2^44 the peak is 2^86.6.
 *
 * REPORT. One line in the format of the C verifiers, plus walked/skipped/odd_starts/overflows,
 *        exact peak, seconds; optionally the same as JSON (--json PATH).
 *
 * usage: verify_3x1_gpu lo hi [--sieve K] [--slabs S] [--cap C] [--forget-17] [--json PATH]
 */
#include <cuda_runtime.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

typedef unsigned long long u64;
typedef unsigned int u32;

#define CUDA_CHECK(call)                                                                 \
    do {                                                                                 \
        cudaError_t err__ = (call);                                                      \
        if (err__ != cudaSuccess) {                                                      \
            fprintf(stderr, "CUDA error: %s at %s:%d\n", cudaGetErrorString(err__),      \
                    __FILE__, __LINE__);                                                 \
            exit(3);                                                                     \
        }                                                                                \
    } while (0)

static const int POW3_MAX = 40;  /* 3^40 < 2^64 */
__constant__ u64 c_pow3[POW3_MAX + 1];
__constant__ u64 c_known[16];
__constant__ int c_nknown;

struct U128 {
    u64 lo, hi;
};

__device__ __forceinline__ int ctz128(const U128 v) {
    return v.lo ? (__ffsll((long long)v.lo) - 1) : (64 + __ffsll((long long)v.hi) - 1);
}

__device__ __forceinline__ U128 shr128(const U128 v, int s) { /* 1 <= s <= 127 */
    U128 r;
    if (s >= 64) {
        r.lo = v.hi >> (s - 64);
        r.hi = 0;
    } else {
        r.lo = (v.lo >> s) | (v.hi << (64 - s));
        r.hi = v.hi >> s;
    }
    return r;
}

/* v *= m for m < 2^64; returns true on overflow past 2^128 */
__device__ __forceinline__ bool mul128_u64(U128& v, u64 m) {
    u64 lo = v.lo * m;
    u64 c = __umul64hi(v.lo, m);
    u64 hh = __umul64hi(v.hi, m);
    u64 hl = v.hi * m;
    u64 hi = hl + c;
    bool overflow = (hh != 0) || (hi < hl);
    v.lo = lo;
    v.hi = hi;
    return overflow;
}

__device__ __forceinline__ bool lt128_u64(const U128 v, u64 y) { return v.hi == 0 && v.lo < y; }
__device__ __forceinline__ bool eq128_u64(const U128 v, u64 y) { return v.hi == 0 && v.lo == y; }
__device__ __forceinline__ bool gt128(const U128 a, const U128 b) {
    return a.hi > b.hi || (a.hi == b.hi && a.lo > b.lo);
}
__device__ __forceinline__ bool is_known(u64 y) {
    for (int i = 0; i < c_nknown; ++i)
        if (c_known[i] == y) return true;
    return false;
}

enum Status { ST_DROP = 0, ST_STEPCAP = 1, ST_CYCLE = 2, ST_OVERFLOW = 3 };

/* Walk one start; returns the status, fills steps and peak. */
__device__ __forceinline__ int walk(u64 y0, u64 cap, u64& steps, U128& peak) {
    U128 y;
    y.lo = y0;
    y.hi = 0;
    peak = y;
    steps = 0;
    for (;;) {
        /* y is odd and >= y0 >= 3 here */
        U128 u = y;
        u.lo -= 1; /* y odd: no borrow */
        int a = ctz128(u); /* u even, nonzero */
        u = shr128(u, a);
        int rem = a;
        while (rem > 0) {
            int c = rem > POW3_MAX ? POW3_MAX : rem;
            if (mul128_u64(u, c_pow3[c])) return ST_OVERFLOW;
            rem -= c;
        }
        y = u;
        y.lo += 1;
        if (y.lo == 0) {
            y.hi += 1;
            if (y.hi == 0) return ST_OVERFLOW;
        }
        steps += (u64)a;
        if (gt128(y, peak)) peak = y;
        int b = ctz128(y); /* y even, nonzero */
        U128 yb = shr128(y, b);
        if (lt128_u64(yb, y0)) {
            /* the first halving t with (y >> t) < y0 is the plain walker's stopping step */
            int t = 1;
            for (; t < b; ++t)
                if (lt128_u64(shr128(y, t), y0)) break;
            steps += (u64)t;
            return ST_DROP;
        }
        y = yb;
        steps += (u64)b;
        if (eq128_u64(y, y0)) return ST_CYCLE;
        if (y.hi == 0 && y.lo <= 136 && is_known(y.lo)) return ST_DROP;
        if (steps > cap) return ST_STEPCAP;
    }
}

__global__ void descend_kernel(u64 slab0, u32 nslabs, const u32* __restrict__ surv, u32 nsurv, int K,
                               u64 lo, u64 hi, u64 cap, u64* g_counts /* [stepcap, cycle, overflow] */,
                               u64* g_maxsteps, u64* bad_list, u64 bad_cap, u64* g_nbad,
                               u64* blk_peak_hi, u64* blk_peak_lo) {
    __shared__ u64 sh_hi[256];
    __shared__ u64 sh_lo[256];
    __shared__ u64 sh_steps[256];
    const u64 idx = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    const u64 total = (u64)nslabs * nsurv;
    U128 peak;
    peak.lo = 0;
    peak.hi = 0;
    u64 steps = 0;
    if (idx < total) {
        const u64 slab = idx / nsurv;
        const u32 s = (u32)(idx - slab * nsurv);
        const u64 y0 = ((slab0 + slab) << K) + surv[s];
        if (y0 >= lo && y0 < hi && y0 >= 3) {
            int st = walk(y0, cap, steps, peak);
            if (st != ST_DROP) {
                atomicAdd(&g_counts[st - 1], 1ull);
                u64 slot = atomicAdd(g_nbad, 1ull);
                if (slot < bad_cap) bad_list[2 * slot] = y0, bad_list[2 * slot + 1] = (u64)st;
            }
        }
    }
    sh_hi[threadIdx.x] = peak.hi;
    sh_lo[threadIdx.x] = peak.lo;
    sh_steps[threadIdx.x] = steps;
    __syncthreads();
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            const int o = threadIdx.x + stride;
            if (sh_hi[o] > sh_hi[threadIdx.x] || (sh_hi[o] == sh_hi[threadIdx.x] && sh_lo[o] > sh_lo[threadIdx.x])) {
                sh_hi[threadIdx.x] = sh_hi[o];
                sh_lo[threadIdx.x] = sh_lo[o];
            }
            if (sh_steps[o] > sh_steps[threadIdx.x]) sh_steps[threadIdx.x] = sh_steps[o];
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        blk_peak_hi[blockIdx.x] = sh_hi[0];
        blk_peak_lo[blockIdx.x] = sh_lo[0];
        atomicMax(g_maxsteps, sh_steps[0]);
    }
}

__global__ void reduce_peak_kernel(const u64* blk_hi, const u64* blk_lo, u32 n, u64* out /* [hi, lo] */) {
    __shared__ u64 sh_hi[1024];
    __shared__ u64 sh_lo[1024];
    u64 h = 0, l = 0;
    for (u32 i = threadIdx.x; i < n; i += blockDim.x) {
        if (blk_hi[i] > h || (blk_hi[i] == h && blk_lo[i] > l)) {
            h = blk_hi[i];
            l = blk_lo[i];
        }
    }
    sh_hi[threadIdx.x] = h;
    sh_lo[threadIdx.x] = l;
    __syncthreads();
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            const int o = threadIdx.x + stride;
            if (sh_hi[o] > sh_hi[threadIdx.x] || (sh_hi[o] == sh_hi[threadIdx.x] && sh_lo[o] > sh_lo[threadIdx.x])) {
                sh_hi[threadIdx.x] = sh_hi[o];
                sh_lo[threadIdx.x] = sh_lo[o];
            }
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        if (sh_hi[0] > out[0] || (sh_hi[0] == out[0] && sh_lo[0] > out[1])) {
            out[0] = sh_hi[0];
            out[1] = sh_lo[0];
        }
    }
}

/* ------------------------------------------------------------------ host side */

/* prefix-noncontracting residues mod 2^K: for every j <= K, 3^{a_j} >= 2^j, in integers */
static std::vector<u32> build_sieve(int K) {
    std::vector<int> amin(K + 1, 0); /* least a with 3^a >= 2^j */
    for (int j = 1; j <= K; ++j) {
        u64 p3 = 1;
        int a = 0;
        while (p3 < (1ull << j)) {
            p3 *= 3;
            ++a;
        }
        amin[j] = a;
    }
    std::vector<u32> out;
    const u64 mask = (1ull << K) - 1;
    for (u64 r = 0; r < (1ull << K); ++r) {
        u64 v = r;
        int a = 0;
        bool ok = true;
        for (int j = 1; j <= K; ++j) {
            if (v & 1) {
                v = ((3 * v - 1) >> 1) & mask;
                ++a;
            } else {
                v >>= 1;
            }
            if (a < amin[j]) {
                ok = false;
                break;
            }
        }
        if (ok) out.push_back((u32)r);
    }
    return out;
}

static u64 odd_count(u64 lo, u64 hi) { /* odd integers in [lo, hi) */
    if (hi <= lo) return 0;
    u64 first = lo | 1ull;
    if (first >= hi) return 0;
    return (hi - first + 1) / 2;
}

static u64 survivors_in(const std::vector<u32>& surv, u64 base, u64 lo, u64 hi) {
    /* number of r in surv with lo <= base + r < hi (surv sorted ascending) */
    u64 rlo = lo > base ? lo - base : 0;
    u64 rhi = hi > base ? hi - base : 0;
    if (rhi <= rlo) return 0;
    auto it_lo = std::lower_bound(surv.begin(), surv.end(), (u32)(rlo > 0xffffffffull ? 0xffffffffull : rlo));
    auto it_hi = rhi > 0xffffffffull ? surv.end() : std::lower_bound(surv.begin(), surv.end(), (u32)rhi);
    return (u64)(it_hi - it_lo);
}

int main(int argc, char** argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s lo hi [--sieve K] [--slabs S] [--cap C] [--forget-17] [--json PATH]\n", argv[0]);
        return 2;
    }
    u64 lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int K = 24;
    u32 slabs_per_launch = 1024;
    u64 cap = 40000;
    bool forget17 = false;
    std::string json_path;
    for (int i = 3; i < argc; ++i) {
        if (!strcmp(argv[i], "--sieve") && i + 1 < argc) K = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--slabs") && i + 1 < argc) slabs_per_launch = (u32)strtoul(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--cap") && i + 1 < argc) cap = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "--forget-17")) forget17 = true;
        else if (!strcmp(argv[i], "--json") && i + 1 < argc) json_path = argv[++i];
        else {
            fprintf(stderr, "unknown argument %s\n", argv[i]);
            return 2;
        }
    }
    if (K < 8 || K > 30) {
        fprintf(stderr, "sieve K must be in [8, 30]\n");
        return 2;
    }
    if (lo < 3) lo = 3;
    if (hi <= lo) {
        printf("limit=%llu lo=%llu walked=0 skipped=0 odd_starts=0 fails=0 new_cycles=0 overflows=0 max_steps=0\n", hi, lo);
        return 0;
    }
    auto t_start = std::chrono::steady_clock::now();

    std::vector<u32> surv = build_sieve(K);
    const u32 nsurv = (u32)surv.size();
    auto t_sieve = std::chrono::steady_clock::now();

    /* constants */
    u64 pow3[POW3_MAX + 1];
    pow3[0] = 1;
    for (int i = 1; i <= POW3_MAX; ++i) pow3[i] = pow3[i - 1] * 3;
    CUDA_CHECK(cudaMemcpyToSymbol(c_pow3, pow3, sizeof(pow3)));
    u64 known_all[15] = {1, 5, 7, 10, 17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34};
    u64 known[16];
    int nknown = 0;
    for (int i = 0; i < 15; ++i)
        if (!(forget17 && i >= 4)) known[nknown++] = known_all[i];
    CUDA_CHECK(cudaMemcpyToSymbol(c_known, known, sizeof(u64) * 16));
    CUDA_CHECK(cudaMemcpyToSymbol(c_nknown, &nknown, sizeof(int)));

    /* device buffers */
    u32* d_surv;
    CUDA_CHECK(cudaMalloc(&d_surv, sizeof(u32) * nsurv));
    CUDA_CHECK(cudaMemcpy(d_surv, surv.data(), sizeof(u32) * nsurv, cudaMemcpyHostToDevice));
    const u64 threads_per_launch = (u64)slabs_per_launch * nsurv;
    const u32 blocks_per_launch = (u32)((threads_per_launch + 255) / 256);
    u64 *d_counts, *d_maxsteps, *d_bad, *d_nbad, *d_blk_hi, *d_blk_lo, *d_peak;
    const u64 bad_cap = 4096;
    CUDA_CHECK(cudaMalloc(&d_counts, sizeof(u64) * 3));
    CUDA_CHECK(cudaMalloc(&d_maxsteps, sizeof(u64)));
    CUDA_CHECK(cudaMalloc(&d_bad, sizeof(u64) * 2 * bad_cap));
    CUDA_CHECK(cudaMalloc(&d_nbad, sizeof(u64)));
    CUDA_CHECK(cudaMalloc(&d_blk_hi, sizeof(u64) * blocks_per_launch));
    CUDA_CHECK(cudaMalloc(&d_blk_lo, sizeof(u64) * blocks_per_launch));
    CUDA_CHECK(cudaMalloc(&d_peak, sizeof(u64) * 2));
    CUDA_CHECK(cudaMemset(d_counts, 0, sizeof(u64) * 3));
    CUDA_CHECK(cudaMemset(d_maxsteps, 0, sizeof(u64)));
    CUDA_CHECK(cudaMemset(d_nbad, 0, sizeof(u64)));
    CUDA_CHECK(cudaMemset(d_peak, 0, sizeof(u64) * 2));

    /* slabs of 2^K numbers covering [lo, hi) */
    const u64 slab_first = lo >> K, slab_last = (hi - 1) >> K;
    u64 walked = 0;
    for (u64 q = slab_first; q <= slab_last; q += slabs_per_launch) {
        u64 n = slab_last - q + 1;
        if (n > slabs_per_launch) n = slabs_per_launch;
        /* walked starts, exactly, on the host */
        for (u64 s = 0; s < n; ++s) {
            const u64 base = (q + s) << K;
            if (base >= lo && base + (1ull << K) <= hi) walked += nsurv;
            else walked += survivors_in(surv, base, lo, hi);
        }
        const u64 threads = n * nsurv;
        const u32 blocks = (u32)((threads + 255) / 256);
        descend_kernel<<<blocks, 256>>>(q, (u32)n, d_surv, nsurv, K, lo, hi, cap, d_counts, d_maxsteps, d_bad, bad_cap,
                                        d_nbad, d_blk_hi, d_blk_lo);
        CUDA_CHECK(cudaGetLastError());
        reduce_peak_kernel<<<1, 1024>>>(d_blk_hi, d_blk_lo, blocks, d_peak);
        CUDA_CHECK(cudaGetLastError());
    }
    CUDA_CHECK(cudaDeviceSynchronize());
    auto t_end = std::chrono::steady_clock::now();

    u64 counts[3], maxsteps, nbad, peak[2];
    CUDA_CHECK(cudaMemcpy(counts, d_counts, sizeof(counts), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaMemcpy(&maxsteps, d_maxsteps, sizeof(u64), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaMemcpy(&nbad, d_nbad, sizeof(u64), cudaMemcpyDeviceToHost));
    CUDA_CHECK(cudaMemcpy(peak, d_peak, sizeof(peak), cudaMemcpyDeviceToHost));
    std::vector<u64> bad(2 * bad_cap);
    CUDA_CHECK(cudaMemcpy(bad.data(), d_bad, sizeof(u64) * 2 * bad_cap, cudaMemcpyDeviceToHost));

    /* the cycle minima 5 and 17 return to themselves; they are known, not new */
    u64 new_cycles = 0, known_cycles = 0;
    std::vector<u64> new_cycle_starts, overflow_starts, stepcap_starts;
    const u64 nlisted = nbad < bad_cap ? nbad : bad_cap;
    for (u64 i = 0; i < nlisted; ++i) {
        const u64 y0 = bad[2 * i], st = bad[2 * i + 1];
        if (st == ST_CYCLE) {
            bool kn = false;
            for (int k = 0; k < nknown; ++k)
                if (known[k] == y0) kn = true;
            if (kn) ++known_cycles;
            else {
                ++new_cycles;
                new_cycle_starts.push_back(y0);
                printf("NEW CYCLE at %llu\n", y0);
            }
        } else if (st == ST_OVERFLOW) {
            overflow_starts.push_back(y0);
            printf("OVERFLOW at %llu\n", y0);
        } else {
            stepcap_starts.push_back(y0);
            printf("STEPCAP at %llu\n", y0);
        }
    }
    if (nbad > bad_cap) printf("WARNING: %llu reported starts, only %llu listed\n", nbad, bad_cap);
    const u64 odd_starts = odd_count(lo, hi);
    const double secs = std::chrono::duration<double>(t_end - t_start).count();
    const double sieve_secs = std::chrono::duration<double>(t_sieve - t_start).count();
    printf("limit=%llu lo=%llu walked=%llu skipped=%llu odd_starts=%llu fails=%llu new_cycles=%llu overflows=%llu max_steps=%llu\n",
           hi, lo, walked, odd_starts - walked, odd_starts, counts[0], new_cycles, counts[2], maxsteps);
    printf("peak_hi=%llu peak_lo=%llu\n", peak[0], peak[1]);
    printf("sieve_K=%d classes=%u known_cycle_returns=%llu seconds=%.3f sieve_seconds=%.3f\n", K, nsurv, known_cycles, secs,
           sieve_secs);
    if (!json_path.empty()) {
        FILE* f = fopen(json_path.c_str(), "w");
        if (!f) {
            fprintf(stderr, "cannot write %s\n", json_path.c_str());
            return 4;
        }
        fprintf(f, "{\n \"verifier\": \"verify_3x1_gpu.cu\",\n \"lo\": %llu,\n \"limit\": %llu,\n \"sieve_K\": %d,\n \"classes\": %u,\n",
                lo, hi, K, nsurv);
        fprintf(f, " \"odd_starts\": %llu,\n \"walked\": %llu,\n \"skipped\": %llu,\n \"fails\": %llu,\n \"new_cycles\": %llu,\n",
                odd_starts, walked, odd_starts - walked, counts[0], new_cycles);
        fprintf(f, " \"overflows\": %llu,\n \"known_cycle_returns\": %llu,\n \"max_steps\": %llu,\n \"step_cap\": %llu,\n",
                counts[2], known_cycles, maxsteps, cap);
        fprintf(f, " \"peak_hi\": %llu,\n \"peak_lo\": %llu,\n \"forget_17\": %s,\n \"seconds\": %.3f,\n \"sieve_seconds\": %.3f,\n",
                peak[0], peak[1], forget17 ? "true" : "false", secs, sieve_secs);
        fprintf(f, " \"new_cycle_starts\": [");
        for (size_t i = 0; i < new_cycle_starts.size(); ++i) fprintf(f, "%s%llu", i ? ", " : "", new_cycle_starts[i]);
        fprintf(f, "],\n \"overflow_starts\": [");
        for (size_t i = 0; i < overflow_starts.size(); ++i) fprintf(f, "%s%llu", i ? ", " : "", overflow_starts[i]);
        fprintf(f, "],\n \"stepcap_starts\": [");
        for (size_t i = 0; i < stepcap_starts.size(); ++i) fprintf(f, "%s%llu", i ? ", " : "", stepcap_starts[i]);
        fprintf(f, "]\n}\n");
        fclose(f);
    }
    return (counts[0] || new_cycles || counts[2]) ? 1 : 0;
}
