/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/**********************************************************************/
/***                                                                ***/
/***                     Public prime table                         ***/
/***                                                                ***/
/**********************************************************************/

static ulong _maxprimelim = 0;
static GEN _prodprimes, _prodprimeslim;
typedef unsigned char *byteptr;

/* Build/Rebuild table of prime differences. The actual work is done by the
 * following two subroutines;  the user entry point is the function
 * initprimes() below; initprimes1() is the basecase, called when
 * maxnum (size) is moderate. Must be called after pari_init_stack() )*/
static void
initprimes1(ulong size, long *lenp, pari_prime *p1)
{
  pari_sp av = avma;
  long k;
  byteptr q, r, s, p = (byteptr)stack_calloc(size+2), fin = p + size;
  pari_prime *re;

  for (r=q=p,k=1; r<=fin; )
  {
    do { r+=k; k+=2; r+=k; } while (*++q);
    for (s=r; s<=fin; s+=k) *s = 1;
  }
  re = p1; *re++ = 2; *re++ = 3; /* 2 and 3 */
  for (s=q=p+1; ; s=q)
  {
    do q++; while (*q);
    if (q > fin) break;
    *re++ = (pari_prime) 2*(q-p)+1;
  }
  *re++ = 0;
  *lenp = re - p1;
  set_avma(av);
}

/*  Timing in ms (Athlon/850; reports 512K of secondary cache; looks
    like there is 64K of quickier cache too).

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
      16K       1.1053  1.1407  1.2589  1.4368   1.6086
      24K       1.0000  1.0625  1.1320  1.2443   1.3095
      32K       1.0000  1.0469  1.0761  1.1336   1.1776
      48K       1.0000  1.0000  1.0254  1.0445   1.0546
      50K       1.0000  1.0000  1.0152  1.0345   1.0464
      52K       1.0000  1.0000  1.0203  1.0273   1.0362
      54K       1.0000  1.0000  1.0812  1.0216   1.0281
      56K       1.0526  1.0000  1.0051  1.0144   1.0205
      58K       1.0000  1.0000  1.0000  1.0086   1.0123
      60K       0.9473  0.9844  1.0051  1.0014   1.0055
      62K       1.0000  0.9844  0.9949  0.9971   0.9993
      64K       1.0000  1.0000  1.0000  1.0000   1.0000
      66K       1.2632  1.2187  1.2183  1.2055   1.1953
      68K       1.4211  1.4844  1.4721  1.4425   1.4188
      70K       1.7368  1.7188  1.7107  1.6767   1.6421
      72K       1.9474  1.9531  1.9594  1.9023   1.8573
      74K       2.2105  2.1875  2.1827  2.1207   2.0650
      76K       2.4211  2.4219  2.4010  2.3305   2.2644
      78K       2.5789  2.6250  2.6091  2.5330   2.4571
      80K       2.8421  2.8125  2.8223  2.7213   2.6380
      84K       3.1053  3.1875  3.1776  3.0819   2.9802
      88K       3.5263  3.5312  3.5228  3.4124   3.2992
      92K       3.7895  3.8438  3.8375  3.7213   3.5971
      96K       4.0000  4.1093  4.1218  3.9986   3.9659
      112K      4.3684  4.5781  4.5787  4.4583   4.6115
      128K      4.7368  4.8750  4.9188  4.8075   4.8997
      192K      5.5263  5.7188  5.8020  5.6911   5.7064
      256K      6.0000  6.2187  6.3045  6.1954   6.1033
      384K      6.7368  6.9531  7.0405  6.9181   6.7912
      512K      7.3158  7.5156  7.6294  7.5000   7.4654
      768K      9.1579  9.4531  9.6395  9.5014   9.1075
      1024K    10.368  10.7497 10.9999 10.878   10.8201
      1536K    12.579  13.3124 13.7660 13.747   13.4739
      2048K    13.737  14.4839 15.0509 15.151   15.1282
      3076K    14.789  15.5780 16.2993 16.513   16.3365

    Now the same number relative to the model

    (1 + 0.36*sqrt(primelimit)/arena) * (arena <= 64 ? 1.05 : (arena-64)**0.38)

     [SLOW2_IN_ROOTS = 0.36, ALPHA = 0.38]

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
        16K    1.014    0.9835  0.9942  0.9889  1.004
        24K    0.9526   0.9758  0.9861  0.9942  0.981
        32K    0.971    0.9939  0.9884  0.9849  0.9806
        48K    0.9902   0.9825  0.996   0.9945  0.9885
        50K    0.9917   0.9853  0.9906  0.9926  0.9907
        52K    0.9932   0.9878  0.9999  0.9928  0.9903
        54K    0.9945   0.9902  1.064   0.9939  0.9913
        56K    1.048    0.9924  0.9925  0.993   0.9921
        58K    0.9969   0.9945  0.9909  0.9932  0.9918
        60K    0.9455   0.9809  0.9992  0.9915  0.9923
        62K    0.9991   0.9827  0.9921  0.9924  0.9929
        64K    1        1       1       1       1
        66K    1.02     0.9849  0.9857  0.9772  0.9704
        68K    0.8827   0.9232  0.9176  0.9025  0.8903
        70K    0.9255   0.9177  0.9162  0.9029  0.8881
        72K    0.9309   0.936   0.9429  0.9219  0.9052
        74K    0.9715   0.9644  0.967   0.9477  0.9292
        76K    0.9935   0.9975  0.9946  0.9751  0.9552
        78K    0.9987   1.021   1.021   1.003   0.9819
        80K    1.047    1.041   1.052   1.027   1.006
        84K    1.052    1.086   1.092   1.075   1.053
        88K    1.116    1.125   1.133   1.117   1.096
        92K    1.132    1.156   1.167   1.155   1.134
        96K    1.137    1.177   1.195   1.185   1.196
       112K    1.067    1.13    1.148   1.15    1.217
       128K    1.04     1.083   1.113   1.124   1.178
       192K    0.9368   0.985   1.025   1.051   1.095
       256K    0.8741   0.9224  0.9619  0.995   1.024
       384K    0.8103   0.8533  0.8917  0.9282  0.9568
       512K    0.7753   0.8135  0.8537  0.892   0.935
       768K    0.8184   0.8638  0.9121  0.9586  0.9705
      1024K    0.8241   0.8741  0.927   0.979   1.03
      1536K    0.8505   0.9212  0.9882  1.056   1.096
      2048K    0.8294   0.8954  0.9655  1.041   1.102

*/

#ifndef SLOW2_IN_ROOTS
  /* SLOW2_IN_ROOTS below 3: some slowdown starts to be noticable
   * when things fit into the cache on Sparc.
   * The choice of 2.6 gives a slowdown of 1-2% on UltraSparcII,
   * but makes calculations for "maximum" of 436273009
   * fit into 256K cache (still common for some architectures).
   *
   * One may change it when small caches become uncommon, but the gain
   * is not going to be very noticable... */
#  ifdef i386           /* gcc defines this? */
#    define SLOW2_IN_ROOTS      0.36
#  else
#    define SLOW2_IN_ROOTS      2.6
#  endif
#endif
#ifndef CACHE_ARENA
#  ifdef i386           /* gcc defines this? */
   /* Due to smaller SLOW2_IN_ROOTS, smaller arena is OK; fit L1 cache */
#    define CACHE_ARENA (63 * 1024UL) /* No slowdown even with 64K L1 cache */
#  else
#    define CACHE_ARENA (200 * 1024UL) /* No slowdown even with 256K L2 cache */
#  endif
#endif

#define CACHE_ALPHA     (0.38)          /* Cache performance model parameter */
#define CACHE_CUTOFF    (0.018)         /* Cache performance not smooth here */

static double slow2_in_roots = SLOW2_IN_ROOTS;

typedef struct {
    ulong arena;
    double power;
    double cutoff;
    ulong bigarena;
} cache_model_t;

static cache_model_t cache_model = { CACHE_ARENA, CACHE_ALPHA, CACHE_CUTOFF, 0 };

/* Assume that some calculation requires a chunk of memory to be
   accessed often in more or less random fashion (as in sieving).
   Assume that the calculation can be done in steps by subdividing the
   chunk into smaller subchunks (arenas) and treating them
   separately.  Assume that the overhead of subdivision is equivalent
   to the number of arenas.

   Find an optimal size of the arena taking into account the overhead
   of subdivision, and the overhead of arena not fitting into the
   cache.  Assume that arenas of size slow2_in_roots slows down the
   calculation 2x (comparing to very big arenas; when cache hits do
   not matter).  Since cache performance varies wildly with
   architecture, load, and wheather (especially with cache coloring
   enabled), use an idealized cache model based on benchmarks above.

   Assume that an independent region of FIXED_TO_CACHE bytes is accessed
   very often concurrently with the arena access.
 */
static ulong
good_arena_size(ulong slow2_size, ulong total, ulong fixed_to_cache,
                cache_model_t *cache_model)
{
  ulong asize, cache_arena = cache_model->arena;
  double Xmin, Xmax, A, B, C1, C2, D, V;
  double alpha = cache_model->power, cut_off = cache_model->cutoff;

  /* Estimated relative slowdown,
     with overhead = max((fixed_to_cache+arena)/cache_arena - 1, 0):

     1 + slow2_size/arena due to initialization overhead;

     max(1, 4.63 * overhead^0.38 ) due to footprint > cache size.

     [The latter is hard to substantiate theoretically, but this
     function describes benchmarks pretty close; it does not hurt that
     one can minimize it explicitly too ;-).  The switch between
     different choices of max() happens when overhead=0.018.]

     Thus the problem is minimizing (1 + slow2_size/arena)*overhead**0.29.
     This boils down to F=((X+A)/(X+B))X^alpha, X=overhead,
     B = (1 - fixed_to_cache/cache_arena), A = B + slow2_size/cache_arena,
     alpha = 0.38, and X>=0.018, X>-B.

     We need to find the rightmost root of (X+A)*(X+B) - alpha(A-B)X to the
     right of 0.018 (if such exists and is below Xmax).  Then we manually
     check the remaining region [0, 0.018].

     Since we cannot trust the purely-experimental cache-hit slowdown
     function, as a sanity check always prefer fitting into the
     cache (or "almost fitting") if F-law predicts that the larger
     value of the arena provides less than 10% speedup.
   */

  /* The simplest case: we fit into cache */
  asize = cache_arena - fixed_to_cache;
  if (total <= asize) return total;
  /* The simple case: fitting into cache doesn't slow us down more than 10% */
  if (asize > 10 * slow2_size) return asize;
  /* Slowdown of not fitting into cache is significant.  Try to optimize.
     Do not be afraid to spend some time on optimization - in trivial
     cases we do not reach this point; any gain we get should
     compensate the time spent on optimization.  */

  B = (1 - ((double)fixed_to_cache)/cache_arena);
  A = B + ((double)slow2_size)/cache_arena;
  C2 = A*B;
  C1 = (A + B - 1/alpha*(A - B))/2;
  D = C1*C1 - C2;
  if (D > 0)
    V = cut_off*cut_off + 2*C1*cut_off + C2; /* Value at CUT_OFF */
  else
    V = 0; /* Peacify the warning */
  Xmin = cut_off;
  Xmax = ((double)total - fixed_to_cache)/cache_arena; /* Two candidates */

  if ( D <= 0 || (V >= 0 && C1 + cut_off >= 0) ) /* slowdown increasing */
    Xmax = cut_off; /* Only one candidate */
  else if (V >= 0 && /* slowdown concave down */
           ((Xmax + C1) <= 0 || (Xmax*Xmax + 2*C1*Xmax + C2) <= 0))
      /* DO NOTHING */;  /* Keep both candidates */
  else if (V <= 0 && (Xmax*Xmax + 2*C1*Xmax + C2) <= 0) /*slowdown decreasing*/
      Xmin = cut_off; /* Only one candidate */
  else /* Now we know: 2 roots, the largest is in CUT_OFF..Xmax */
      Xmax = sqrt(D) - C1;
  if (Xmax != Xmin) { /* Xmin == CUT_OFF; Check which one is better */
    double v1 = (cut_off + A)/(cut_off + B);
    double v2 = 2.33 * (Xmax + A)/(Xmax + B) * pow(Xmax, alpha);

    if (1.1 * v2 >= v1) /* Prefer fitting into the cache if slowdown < 10% */
      V = v1;
    else
    { Xmin = Xmax; V = v2; }
  } else if (B > 0) /* We need V */
    V = 2.33 * (Xmin + A)/(Xmin + B) * pow(Xmin, alpha);
  if (B > 0 && 1.1 * V > A/B)  /* Now Xmin is the minumum.  Compare with 0 */
    Xmin = 0;

  asize = (ulong)((1 + Xmin)*cache_arena - fixed_to_cache);
  if (asize > total) asize = total; /* May happen due to approximations */
  return asize;
}

/* Use as in
    install(set_optimize,lLDG)          \\ Through some M too?
    set_optimize(2,1) \\ disable dependence on limit
    \\ 1: how much cache usable, 2: slowdown of setup, 3: alpha, 4: cutoff,
    \\ 5: cache size (typically whole L2 or L3) in bytes to use in forprime()
    \\ 2,3,4 are in units of 0.001

    { time_primes_arena(ar,limit) =     \\ ar = arena size in K
        set_optimize(1,floor(ar*1024));
        default(primelimit, 200 000);   \\ 100000 results in *larger* malloc()!
        gettime;
        default(primelimit, floor(limit));
        if(ar >= 1, ar=floor(ar));
        print("arena "ar"K => "gettime"ms");
    }
*/
long
set_optimize(long what, GEN g)
{
  long ret = 0;

  switch (what) {
  case 1:
    ret = (long)cache_model.arena;
    break;
  case 2:
    ret = (long)(slow2_in_roots * 1000);
    break;
  case 3:
    ret = (long)(cache_model.power * 1000);
    break;
  case 4:
    ret = (long)(cache_model.cutoff * 1000);
    break;
  case 5:
    ret = (long)(cache_model.bigarena);
    break;
  default:
    pari_err_BUG("set_optimize");
    break;
  }
  if (g != NULL) {
    ulong val = itou(g);

    switch (what) {
    case 1: cache_model.arena = val; break;
    case 2: slow2_in_roots     = (double)val / 1000.; break;
    case 3: cache_model.power  = (double)val / 1000.; break;
    case 4: cache_model.cutoff = (double)val / 1000.; break;
    case 5: cache_model.bigarena = val; break;
    }
  }
  return ret;
}

/* s is odd; prime (starting from 3 = known_primes[2]), terminated by a 0 byte.
 * Checks n odd numbers starting at 'start', setting bytes to 0 (composite)
 * or 1 (prime), starting at data */
static void
sieve_chunk(pari_prime *known_primes, ulong s, byteptr data, ulong n)
{
  ulong p, cnt = n-1, start = s;
  pari_prime *q;

  memset(data, 0, n);
  start >>= 1;  /* (start - 1)/2 */
  start += n; /* Corresponds to the end */
  /* data corresponds to start, q runs over primediffs */
  for (q = known_primes + 1, p = 3; p; p = *++q)
  { /* first odd number >= start > p and divisible by p
       = last odd number <= start + 2p - 2 and 0 (mod p)
       = p + last number <= start + p - 2 and 0 (mod 2p)
       = p + start+p-2 - (start+p-2) % 2p
       = start + 2(p - 1 - ((start-1)/2 + (p-1)/2) % p). */
    long off = cnt - ((start+(p>>1)) % p);
    while (off >= 0) { data[off] = 1; off -= p; }
  }
}

static long
ZV_size(GEN x)
{
  long i, l = lg(x), s = l;
  for (i = 1; i < l; i++) s += lgefint(gel(x,i));
  return s;
}
/* avoid gcopy_avma so as to deallocate using free() in pari_close_primes */
static GEN
ZV_copy_alloc(GEN x)
{
  long i, l = lg(x), s = ZV_size(x);
  GEN z = (GEN)pari_malloc(s * sizeof(long)), av = z + s;
  for (i = 1; i < l; i++) gel(z,i) = av = icopy_avma(gel(x,i), (pari_sp)av);
  z[0] = x[0] & (TYPBITS|LGBITS); return z;
}

static void
set_prodprimes(void)
{
  pari_sp av = avma;
  ulong b = 1UL << 8, M = minuu(maxprime(), GP_DATA->factorlimit);
  GEN W, v = primes_interval_zv(3, M);
  long u, j, jold, l = lg(v);

  W = cgetg(64+1, t_VEC);
  M = v[l-1]; /* = precprime(M) */
  _prodprimeslim = cgetalloc(64+1, t_VECSMALL);
  if (b > M) b = M;
  for (jold = j = u = 1; j < l; j++)
    if (uel(v,j) >= b) /* if j = l-1, then b = M = v[j] */
    {
      long lw = (j == l-1? l: j) - jold + 1;
      GEN w = v+jold-1;
      w[0] = evaltyp(t_VECSMALL) | _evallg(lw);
      _prodprimeslim[u] = w[lw - 1];
      /* product of primes from
       *   p_jold = 3 if first entry, else nextprime(_prodprime_lim[u - 1] + 1)
       * to
       *   p_{j-1} = _prodprimeslim[u] = precprime(M or 2^{u+7}) */
      gel(W,u++) = zv_prod_Z(w);
      jold = j; b *= 2;
      if (b > M) b = M; /* truncate last run */
    }
  for (j = 2; j < u; j++) gel(W,j) = mulii(gel(W,j-1), gel(W,j));
  setlg(W, u); _prodprimes = ZV_copy_alloc(W);
  setlg(_prodprimeslim, u); set_avma(av);
}

static void
initprimes0(ulong maxnum, long *lenp, pari_prime *p1)
{
  pari_sp av = avma, bot = pari_mainstack->bot;
  long alloced, psize;
  byteptr q, end, p;
  ulong remains, curlow, rootnum, asize, prime_above, last;
  pari_prime *end1, *curdiff, *p_prime_above;

  if (!odd(maxnum)) maxnum--; /* make it odd. */
  /* base case */
  if (maxnum < 1ul<<17) { initprimes1(maxnum>>1, lenp, p1); return; }

  /* Checked to be enough up to 40e6, attained at 155893 */
  rootnum = usqrt(maxnum) | 1;
  initprimes1(rootnum>>1, &psize, p1);
  last = rootnum;
  end1 = p1 + psize - 1;
  remains = (maxnum - last) >> 1; /* number of odd numbers to check */
  /* we access primes array of psize too; but we access it consecutively,
   * thus we do not include it in fixed_to_cache */
  asize = good_arena_size((ulong)(rootnum * slow2_in_roots), remains+1, 0,
                          &cache_model) - 1;
  /* enough room on the stack ? */
  alloced = (((byteptr)avma) <= ((byteptr)bot) + asize);
  p = (byteptr)(alloced? pari_malloc(asize+1): stack_malloc(asize+1));
  end = p + asize; /* the 0 sentinel goes at end. */
  curlow = last + 2; /* First candidate: know primes up to last (odd). */
  curdiff = end1;

  /* During each iteration p..end-1 represents a range of odd
     numbers.   */
  p_prime_above = p1 + 2;
  prime_above = 3;
  while (remains)
  { /* cycle over arenas; performance not crucial */
    pari_prime was_delta;
    if (asize > remains) { asize = remains; end = p + asize; }
    /* Fake the upper limit appropriate for the given arena */
    while (prime_above*prime_above <= curlow + (asize << 1) && *p_prime_above)
      prime_above = *p_prime_above++;
    was_delta = *p_prime_above;
    *p_prime_above = 0; /* sentinel for sieve_chunk */
    sieve_chunk(p1, curlow, p, asize);
    *p_prime_above = was_delta; /* restore */

    p[asize] = 0; /* sentinel */
    for (q = p; ; q++)
    { /* q runs over addresses corresponding to primes */
      while (*q) q++; /* use sentinel at end */
      if (q >= end) break;
      *curdiff++ = (pari_prime) 2*(q-p) + curlow;
    }
    remains -= asize;
    curlow += (asize<<1);
  }
  *curdiff++ = 0; /* sentinel */
  *lenp = curdiff - p1;
  if (alloced) pari_free(p); else set_avma(av);
}

ulong
maxprime(void) { return pari_PRIMES? pari_PRIMES[pari_PRIMES[0]]: 0; }
ulong
maxprimelim(void) { return pari_PRIMES? _maxprimelim: 0; }
ulong
maxprimeN(void) { return pari_PRIMES? pari_PRIMES[0]: 0; }
GEN
prodprimes(void) { return pari_PRIMES? _prodprimes: NULL; }
GEN
prodprimeslim(void) { return pari_PRIMES? _prodprimeslim: NULL; }
void
maxprime_check(ulong c) { if (maxprime() < c) pari_err_MAXPRIME(c); }

static pari_prime*
initprimes(ulong maxnum)
{
  pari_prime *t;
  long len;
  ulong N;
  if (maxnum < 65537)
  {
    maxnum = 65537;
    N = 6543;
  }
  else
    N = (long) ceil(primepi_upper_bound((double)maxnum));
  t = (pari_prime*) pari_malloc(sizeof(*t) * (N+2));
  initprimes0(maxnum, &len, t+1); t[0] = (pari_prime)(len-1);
  _maxprimelim = maxnum;
  return (pari_prime*) pari_realloc(t, sizeof(*t) * (len+1));
}

void
initprimetable(ulong maxnum)
{
  pari_prime *old = pari_PRIMES;
#ifdef LONG_IS_64BIT
  maxnum = minuu(maxnum, 4294967295);
#endif
  pari_PRIMES = initprimes(maxnum);
  if (old) free(old);
  set_prodprimes();
}

/**********************************************************************/
/***                                                                ***/
/***                     forprime                                   ***/
/***                                                                ***/
/**********************************************************************/

/* return good chunk size for sieve, 16 | chunk + 2 */
static ulong
optimize_chunk(ulong a, ulong b)
{
  /* TODO: Optimize size (surely < 512k to stay in L2 cache, but not so large
   * as to force recalculating too often). */
  /* bigarena is in bytes, we use bits, and only odds */
  ulong defchunk = (a>>31) > 1 ? 0x80000UL : 0x8000;
  ulong chunk = (cache_model.bigarena ? cache_model.bigarena : defchunk)<<4;
  ulong tmp = (b - a) / chunk + 1;

  if (tmp == 1)
    chunk = b - a + 16;
  else
    chunk = (b - a) / tmp + 15;
  /* ensure 16 | chunk + 2 */
  return (((chunk + 2)>>4)<<4) - 2;
}
static void
sieve_init(forprime_t *T, ulong a, ulong b)
{
  T->sieveb = b;
  T->chunk = optimize_chunk(a, b);
  /* >> 1 [only odds] + 3 [convert from bits to bytes] */
  T->isieve = (unsigned char*)stack_malloc(((T->chunk+2) >> 4) + 1);
  T->cache[0] = 0;
  T->a = a;
  T->end = minuu(a + T->chunk, b);
  T->pos = T->maxpos = 0;
}

enum {PRST_none, PRST_diffptr, PRST_sieve, PRST_unextprime, PRST_nextprime};

static void
u_forprime_set_prime_table(forprime_t *T, ulong a)
{
  T->strategy = PRST_diffptr;
  if (a < 3)
  {
    T->p = 0;
    T->n = 0;
  }
  else
  {
    long n = PRIMES_search(a - 1);
    if (n < 0) n = - n - 1;
    T->n = n;
    T->p = pari_PRIMES[n];
  }
}

/* Set p so that p + q the smallest integer = c (mod q) and > original p.
 * Assume 0 < c < q. */
static void
arith_set(forprime_t *T)
{
  ulong r = T->p % T->q; /* 0 <= r <= min(p, q-1) */
  pari_sp av = avma;
  GEN d = adduu(T->p - r, T->c); /* = c mod q */
  if (T->c > r) d = subiu(d, T->q);
  /* d = c mod q,  d = c > r? p-r+c-q: p-r+c, so that
   *  d <= p  and  d+q = c>r? p-r+c  : p-r+c+q > p */
  if (signe(d) <= 0)
  {
    T->p = 0;
    T->strategy = PRST_nextprime;
    affii(d, T->pp);
  }
  else
    T->p = itou_or_0(d);
  set_avma(av);
}

/* Run through primes in arithmetic progression = c (mod q).
 * Warning: b = ULONG_MAX may signal that we are called by higher level
 * function handling a continuation for larger b; this sentinel value
 * must not be modified */
static int
u_forprime_sieve_arith_init(forprime_t *T, struct pari_sieve *psieve,
                            ulong a, ulong b, ulong c, ulong q)
{
#ifdef LONG_IS_64BIT
  const ulong UPRIME_MAX = 18446744073709551557UL;
#else
  const ulong UPRIME_MAX = 4294967291UL;
#endif
  ulong Plim, P, P2, Y, sieveb;

  if (!odd(b) && b > 2) b--;
  if (a > b || b < 2)
  {
    T->strategy = PRST_diffptr; /* paranoia */
    T->p = 0; /* empty */
    T->b = 0; /* empty */
    T->n = 0;
    return 0;
  }
  P = maxprime();
  if (b != ULONG_MAX && b > UPRIME_MAX) b = UPRIME_MAX;
  if (q != 1)
  {
    ulong D;
    c %= q; D = ugcd(c, q);
    if (D != 1) { a = maxuu(a,D); if (b != ULONG_MAX) b = minuu(b,D); }
    if (odd(q) && (a > 2 || c != 2))
    { /* only *odd* primes. If a <= c = 2, then p = 2 must be included :-( */
      if (!odd(c)) c += q;
      q <<= 1;
    }
  }
  T->q = q;
  T->c = c;
  T->strategy = PRST_none; /* unknown */
  T->psieve = psieve; /* unused for now */
  T->isieve = NULL; /* unused for now */
  T->b = b;
  if (P >= b) { /* [a,b] \subset prime table */
    u_forprime_set_prime_table(T, a);
    return 1;
  }
  /* b > P */
  if (a >= P)
  {
    T->p = a - 1;
    if (T->q != 1) arith_set(T);
  }
  else
    u_forprime_set_prime_table(T, a);
  if (T->strategy == PRST_none) T->strategy = PRST_unextprime;
  /* now strategy is either PRST_diffptr or PRST_unextprime */

  P2 = (P & HIGHMASK)? 0 : P*P;
  sieveb = b; if (P2 && P2 < b) sieveb = P2;
  /* maxprime^2 >= sieveb */
  Plim = maxprimelim();
  if (a <= Plim) a = Plim + 1;
  if (sieveb < a + 16) return 1;
  Y = sieveb - a + 1; /* number of integers in sievable interval > 16 */
  P = usqrt(sieveb); /* largest sieving prime */
  /* FIXME: should sieve as well if q != 1, adapt sieve code */
  if (q == 1 && (!P2 || P2 > a) && 3/M_LN2 * Y >= uprimepi(P))
  /* Sieve implemented & possible & not too costly. Cost model is
   * - nextprime: about Y / log(b) primes to test [neglect cost for composites]
   *   individual cost average = 3 log2(b) mulmod, total = 3 Y / log(2) mulmod
   * - sieve: pi(P) mod + Y loglog(b) add
   * Since loglog(b) < 4, and add < 10*mulmod, we neglect the Y loglog(b) term.
   * We have mod < mulmod < 2*mod; for now, assume mulmod ~ mod. */
  {
    if (T->strategy == PRST_unextprime) T->strategy = PRST_sieve;
    sieve_init(T, a, sieveb);
  }
  return 1;
}

int
u_forprime_arith_init(forprime_t *T, ulong a, ulong b, ulong c, ulong q)
{ return u_forprime_sieve_arith_init(T, NULL, a, b, c, q); }

/* will run through primes in [a,b] */
int
u_forprime_init(forprime_t *T, ulong a, ulong b)
{ return u_forprime_arith_init(T, a,b, 0,1); }

/* will run through primes in [a,b] */
static int
u_forprime_sieve_init(forprime_t *T, struct pari_sieve *s, ulong b)
{ return u_forprime_sieve_arith_init(T, s, s->start, b, s->c, s->q); }

/* now only run through primes <= c; assume c <= b above */
void
u_forprime_restrict(forprime_t *T, ulong c) { T->b = c; }

/* b = NULL: loop forever */
int
forprimestep_init(forprime_t *T, GEN a, GEN b, GEN q)
{
  GEN c = NULL;
  long lb;

  a = gceil(a); if (typ(a) != t_INT) pari_err_TYPE("forprime_init",a);
  T->qq = NULL; T->q = 1; T->c = 0;
  if (q)
  {
    switch(typ(q))
    {
      case t_INT:
        c = a; break;
      case t_INTMOD:
        c = gel(q,2); q = gel(q,1);
        /* first int >= initial a which is = c (mod q) */
        a = addii(a, modii(subii(c,a), q)); break;
      default: pari_err_TYPE("forprimestep_init",q);
    }
    if (signe(q) <= 0) pari_err_TYPE("forprimestep_init (q <= 0)",q);
    if (equali1(q)) c = q = NULL;
    else
    {
      GEN D = gcdii(c, q);
      if (!is_pm1(D))
      { /* at most one prime: c */
        if (cmpii(a, D) < 0) a = D;
        if (gcmp(b, D) > 0) b = D;
      }
      if ((T->q = itou_or_0(q)))
        T->c = umodiu(c, T->q);
      else
        T->qq = q;
    }
  }
  if (signe(a) <= 0) a = q? modii(a, q): gen_1;
  if (b && typ(b) != t_INFINITY)
  {
    b = gfloor(b);
    if (typ(b) != t_INT) pari_err_TYPE("forprime_init",b);
    if (signe(b) < 0 || cmpii(a,b) > 0)
    {
      T->strategy = PRST_nextprime; /* paranoia */
      T->bb = T->pp = gen_0; return 0;
    }
    lb = lgefint(b);
    T->bb = b;
  }
  else if (!b || inf_get_sign(b) > 0)
  {
    lb = lgefint(a) + 4;
    T->bb = NULL;
  }
  else /* b == -oo */
  {
    T->strategy = PRST_nextprime; /* paranoia */
    T->bb = T->pp = gen_0; return 0;
  }
  T->pp = cgeti(T->qq? maxuu(lb, lgefint(T->qq)): lb);
  /* a, b are positive integers, a <= b */
  if (!T->qq && lgefint(a) == 3) /* lb == 3 implies b != NULL */
    return u_forprime_arith_init(T, uel(a,2), lb == 3? uel(b,2): ULONG_MAX,
                                    T->c, T->q);
  T->strategy = PRST_nextprime;
  affii(T->qq? subii(a,T->qq): subiu(a,T->q), T->pp); return 1;
}
int
forprime_init(forprime_t *T, GEN a, GEN b)
{ return forprimestep_init(T,a,b,NULL); }

/* assume a <= b <= maxprime()^2, a,b odd, sieve[n] corresponds to
 *   a+16*n, a+16*n+2, ..., a+16*n+14 (bits 0 to 7)
 * maxpos = index of last sieve cell.
 * b-a+2 must be divisible by 16 for use by u_forprime_next */
static void
sieve_block(ulong a, ulong b, ulong maxpos, unsigned char* sieve)
{
  ulong i, N = pari_PRIMES[0], lim = usqrt(b), sz = (b-a) >> 1;
  (void)memset(sieve, 0, maxpos+1);
  for (i = 2; i <= N; i++)
  { /* p is odd */
    ulong k, r, p = pari_PRIMES[i]; /* starts at p = 3 */
    if (p > lim) break;

    /* solve a + 2k = 0 (mod p) */
    r = a % p;
    if (r == 0)
      k = 0;
    else
    {
      k = p - r;
      if (odd(k)) k += p;
      k >>= 1;
    }
    /* m = a + 2k is the smallest odd m >= a, p | m */
    /* position n (corresponds to a+2n) is sieve[n>>3], bit n&7 */
    while (k <= sz) { sieve[k>>3] |= 1 << (k&7); k += p; /* 2k += 2p */ }
  }
}

static void
pari_sieve_init(struct pari_sieve *s, ulong a, ulong b)
{
  ulong maxpos= (b - a) >> 4;
  s->start = a; s->end = b;
  s->sieve = (unsigned char*) pari_malloc(maxpos+1);
  s->c = 0; s->q = 1;
  sieve_block(a, b, maxpos, s->sieve);
  s->maxpos = maxpos; /* must be last in case of SIGINT */
}

static struct pari_sieve pari_sieve_modular;
void
pari_init_primes(ulong maxprime)
{
  ulong a = (1UL<<31) + 1, b = a + (1UL<<20)-2;
  initprimetable(maxprime);
  pari_sieve_init(&pari_sieve_modular, a, b);
}

void
pari_close_primes(void)
{
  if (pari_PRIMES)
  {
    pari_free(pari_PRIMES);
    pari_free(_prodprimes);
    pari_free(_prodprimeslim);
  }
  pari_free(pari_sieve_modular.sieve);
}

void
init_modular_small(forprime_t *S)
{
#ifdef LONG_IS_64BIT
  u_forprime_sieve_init(S, &pari_sieve_modular, ULONG_MAX);
#else
  ulong a = (1UL<<((BITS_IN_LONG-2)>>1))+1;
  u_forprime_init(S, a, ULONG_MAX);
#endif
}

void
init_modular_big(forprime_t *S)
{
#ifdef LONG_IS_64BIT
  u_forprime_init(S, HIGHBIT + 1, ULONG_MAX);
#else
  u_forprime_sieve_init(S, &pari_sieve_modular, ULONG_MAX);
#endif
}

/* T->cache is a 0-terminated list of primes, return the first one and
 * remove it from list. Most of the time the list contains a single prime */
static ulong
shift_cache(forprime_t *T)
{
  long i;
  T->p = T->cache[0];
  for (i = 1;; i++)  /* remove one prime from cache */
    if (! (T->cache[i-1] = T->cache[i]) ) break;
  return T->p;
}

ulong
u_forprime_next(forprime_t *T)
{
  if (T->strategy == PRST_diffptr)
  {
    for(;;)
    {
      if (++T->n <= pari_PRIMES[0])
      {
        T->p = pari_PRIMES[T->n];
        if (T->p > T->b) return 0;
        if (T->q == 1 || T->p % T->q == T->c) return T->p;
      }
      else
      { /* beyond the table */
        T->strategy = T->isieve? PRST_sieve: PRST_unextprime;
        if (T->q != 1) { arith_set(T); if (!T->p) return 0; }
        /* T->p possibly not a prime if q != 1 */
        break;
      }
    }
  }
  if (T->strategy == PRST_sieve)
  { /* require sieveb - a >= 16 */
    ulong n;
    if (T->cache[0]) return shift_cache(T);
NEXT_CHUNK:
    if (T->psieve)
    {
      T->sieve = T->psieve->sieve;
      T->end = T->psieve->end;
      if (T->end > T->sieveb) T->end = T->sieveb;
      T->maxpos = T->psieve->maxpos;
      T->pos = 0;
      T->psieve = NULL;
    }
    for (n = T->pos; n < T->maxpos; n++)
      if (T->sieve[n] != 0xFF)
      {
        unsigned char mask = T->sieve[n];
        ulong p = T->a + (n<<4);
        long i = 0;
        T->pos = n;
        if (!(mask &  1)) T->cache[i++] = p;
        if (!(mask &  2)) T->cache[i++] = p+2;
        if (!(mask &  4)) T->cache[i++] = p+4;
        if (!(mask &  8)) T->cache[i++] = p+6;
        if (!(mask & 16)) T->cache[i++] = p+8;
        if (!(mask & 32)) T->cache[i++] = p+10;
        if (!(mask & 64)) T->cache[i++] = p+12;
        if (!(mask &128)) T->cache[i++] = p+14;
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    /* n = T->maxpos, last cell: check p <= b */
    if (T->maxpos && n == T->maxpos && T->sieve[n] != 0xFF)
    {
      unsigned char mask = T->sieve[n];
      ulong p = T->a + (n<<4);
      long i = 0;
      T->pos = n;
      if (!(mask &  1) && p <= T->sieveb) T->cache[i++] = p;
      if (!(mask &  2) && p <= T->sieveb-2) T->cache[i++] = p+2;
      if (!(mask &  4) && p <= T->sieveb-4) T->cache[i++] = p+4;
      if (!(mask &  8) && p <= T->sieveb-6) T->cache[i++] = p+6;
      if (!(mask & 16) && p <= T->sieveb-8) T->cache[i++] = p+8;
      if (!(mask & 32) && p <= T->sieveb-10) T->cache[i++] = p+10;
      if (!(mask & 64) && p <= T->sieveb-12) T->cache[i++] = p+12;
      if (!(mask &128) && p <= T->sieveb-14) T->cache[i++] = p+14;
      if (i)
      {
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    }

    if (T->maxpos && T->end >= T->sieveb) /* done with sieves ? */
    {
      if (T->sieveb == T->b && T->b != ULONG_MAX) return 0;
      T->strategy = PRST_unextprime;
    }
    else
    { /* initialize next chunk */
      T->sieve = T->isieve;
      if (T->maxpos == 0)
        T->a |= 1; /* first time; ensure odd */
      else
        T->a = (T->end + 2) | 1;
      T->end = T->a + T->chunk; /* may overflow */
      if (T->end < T->a || T->end > T->sieveb) T->end = T->sieveb;
      /* end and a are odd; sieve[k] contains the a + 8*2k + (0,2,...,14).
       * The largest k is (end-a) >> 4 */
      T->pos = 0;
      T->maxpos = (T->end - T->a) >> 4; /* >= 1 */
      sieve_block(T->a, T->end, T->maxpos, T->sieve);
      goto NEXT_CHUNK;
    }
  }
  if (T->strategy == PRST_unextprime)
  {
    if (T->q == 1)
    {
#ifdef LONG_IS_64BIT
      switch(T->p)
      {
#define retp(x) return T->p = (HIGHBIT+x <= T->b)? HIGHBIT+x: 0
        case HIGHBIT: retp(29);
        case HIGHBIT + 29: retp(99);
        case HIGHBIT + 99: retp(123);
        case HIGHBIT +123: retp(131);
        case HIGHBIT +131: retp(155);
        case HIGHBIT +155: retp(255);
        case HIGHBIT +255: retp(269);
        case HIGHBIT +269: retp(359);
        case HIGHBIT +359: retp(435);
        case HIGHBIT +435: retp(449);
        case HIGHBIT +449: retp(453);
        case HIGHBIT +453: retp(485);
        case HIGHBIT +485: retp(491);
        case HIGHBIT +491: retp(543);
        case HIGHBIT +543: retp(585);
        case HIGHBIT +585: retp(599);
        case HIGHBIT +599: retp(753);
        case HIGHBIT +753: retp(849);
        case HIGHBIT +849: retp(879);
        case HIGHBIT +879: retp(885);
        case HIGHBIT +885: retp(903);
        case HIGHBIT +903: retp(995);
#undef retp
      }
#endif
      T->p = unextprime(T->p + 1);
      if (T->p > T->b) return 0;
    }
    else do {
      T->p += T->q;
      if (T->p < T->q || T->p > T->b) { T->p = 0; break; } /* overflow */
    } while (!uisprime(T->p));
    if (T->p && T->p <= T->b) return T->p;
    /* overflow ulong, switch to GEN */
    T->strategy = PRST_nextprime;
  }
  return 0; /* overflow */
}

GEN
forprime_next(forprime_t *T)
{
  pari_sp av;
  GEN p;
  if (T->strategy != PRST_nextprime)
  {
    ulong u = u_forprime_next(T);
    if (u) { affui(u, T->pp); return T->pp; }
    /* failure */
    if (T->strategy != PRST_nextprime) return NULL; /* we're done */
    /* overflow ulong, switch to GEN */
    u = ULONG_MAX;
    if (T->q > 1) u -= (ULONG_MAX-T->c) % T->q;
    affui(u, T->pp);
  }
  av = avma; p = T->pp;
  if (T->q == 1)
  {
    p = nextprime(addiu(p, 1));
    if (T->bb && abscmpii(p, T->bb) > 0) return gc_NULL(av);
  } else do {
    p = T->qq? addii(p, T->qq): addiu(p, T->q);
    if (T->bb && abscmpii(p, T->bb) > 0) return gc_NULL(av);
  } while (!BPSW_psp(p));
  affii(p, T->pp); return gc_const(av, T->pp);
}

void
forprimestep(GEN a, GEN b, GEN q, GEN code)
{
  pari_sp av = avma;
  forprime_t T;

  if (!forprimestep_init(&T, a,b,q)) { set_avma(av); return; }

  push_lex(T.pp,code);
  while(forprime_next(&T))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* p changed in 'code', complain */
    if (get_lex(-1) != T.pp)
      pari_err(e_MISC,"prime index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); set_avma(av);
}
void
forprime(GEN a, GEN b, GEN code) { return forprimestep(a,b,NULL,code); }

int
forcomposite_init(forcomposite_t *C, GEN a, GEN b)
{
  pari_sp av = avma;
  a = gceil(a);
  if (typ(a)!=t_INT) pari_err_TYPE("forcomposite",a);
  if (b) {
    if (typ(b) == t_INFINITY) b = NULL;
    else
    {
      b = gfloor(b);
      if (typ(b)!=t_INT) pari_err_TYPE("forcomposite",b);
    }
  }
  if (signe(a) < 0) pari_err_DOMAIN("forcomposite", "a", "<", gen_0, a);
  if (abscmpiu(a, 4) < 0) a = utoipos(4);
  C->first = 1;
  if (!forprime_init(&C->T, a,b) && cmpii(a,b) > 0)
  {
    C->n = gen_1; /* in case caller forgets to check the return value */
    C->b = gen_0; return gc_bool(av,0);
  }
  C->n = setloop(a);
  C->b = b;
  C->p = NULL; return 1;
}

GEN
forcomposite_next(forcomposite_t *C)
{
  if (C->first) /* first call ever */
  {
    C->first = 0;
    C->p = forprime_next(&C->T);
  }
  else
    C->n = incloop(C->n);
  if (C->p)
  {
    if (cmpii(C->n, C->p) < 0) return C->n;
    C->n = incloop(C->n);
    /* n = p+1 */
    C->p = forprime_next(&C->T); /* nextprime(p) > n */
    if (C->p) return C->n;
  }
  if (!C->b || cmpii(C->n, C->b) <= 0) return C->n;
  return NULL;
}

void
forcomposite(GEN a, GEN b, GEN code)
{
  pari_sp av = avma;
  forcomposite_t T;
  GEN n;
  if (!forcomposite_init(&T,a,b)) return;
  push_lex(T.n,code);
  while((n = forcomposite_next(&T)))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* n changed in 'code', complain */
    if (get_lex(-1) != n)
      pari_err(e_MISC,"index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); set_avma(av);
}
