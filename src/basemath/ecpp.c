/* Copyright (C) 2014 The PARI group.

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

#define DEBUGLEVEL DEBUGLEVEL_isprime

#define dbg_mode()  if (DEBUGLEVEL >= 2)
#define dbg_mode1() if (DEBUGLEVEL >= 3)

#define ANSI_RED     "\x1b[31m"
#define ANSI_GREEN   "\x1b[32m"
#define ANSI_YELLOW  "\x1b[33m"
#define ANSI_BLUE    "\x1b[34m"
#define ANSI_MAGENTA "\x1b[35m"
#define ANSI_CYAN    "\x1b[36m"
#define ANSI_WHITE   "\x1b[37m"

#define ANSI_BRIGHT_RED     "\x1b[31;1m"
#define ANSI_BRIGHT_GREEN   "\x1b[32;1m"
#define ANSI_BRIGHT_YELLOW  "\x1b[33;1m"
#define ANSI_BRIGHT_BLUE    "\x1b[34;1m"
#define ANSI_BRIGHT_MAGENTA "\x1b[35;1m"
#define ANSI_BRIGHT_CYAN    "\x1b[36;1m"
#define ANSI_BRIGHT_WHITE   "\x1b[37;1m"

#define ANSI_RESET   "\x1b[0m"

/* THINGS THAT DON'T BELONG */

/* Assume that x is a vector such that
   f(x) = 1 for x <= k
   f(x) = 0 otherwise.
   Return k.
*/
static long
zv_binsearch0(void *E, long (*f)(void* E, GEN x), GEN x)
{
  long lo = 1;
  long hi = lg(x)-1;
  while (lo < hi) {
    long mi = lo + (hi - lo)/2 + 1;
    if (f(E,gel(x,mi))) lo = mi;
    else hi = mi - 1;
  }
  if (f(E,gel(x,lo))) return lo;
  return 0;
}

INLINE long
time_record(GEN* X0, const char* Xx, long t)
{
  long i = Xx[0]-'A'+1, j = Xx[1]-'1'+1;
  umael3(*X0, 1, i, j) += t;
  umael3(*X0, 2, i, j) ++; return t;
}

INLINE long
timer_record(GEN* X0, const char* Xx, pari_timer* ti)
{ return time_record(X0, Xx, timer_delay(ti)); }

INLINE long
FpJ_is_inf(GEN P) { return signe(gel(P, 3)) == 0; }

/*****************************************************************/

/* D < 0 fundamental: return the number of units in Q(sqrt(D)) */
INLINE long
D_get_wD(long D)
{
  if (D == -4) return 4;
  if (D == -3) return 6;
  return 2;
}

/* Dinfo contains information related to the discirminant
 *    D: the discriminant (D < 0)
 *    h: the class number associated to D
 *   bi: the "best invariant" for computing polclass(D, bi)
 *   pd: the degree of polclass; equal to h except when bi is a double
 *       eta-quotient w_p,q with p|D and q|D, where pd = h/2.
 * Dfac: the prime factorization of D; we have D = q0 q1* q2* ... qn*
 *       where q0 = 1, -4, 8, -8, qi* = 1 mod 4 and |qi| is a prime.
 *       The factorization is a vecsmall listing the indices of the qi* as
 *       they appear in the primelist (q0 = 1 is omitted) */
INLINE long
Dinfo_get_D(GEN Dinfo) { return gel(Dinfo, 1)[1]; }
INLINE long
Dinfo_get_h(GEN Dinfo) { return gel(Dinfo, 1)[2]; }
INLINE long
Dinfo_get_bi(GEN Dinfo) { return gel(Dinfo, 1)[3]; }
INLINE ulong
Dinfo_get_pd(GEN Dinfo) { return umael(Dinfo, 1, 4); }
INLINE GEN
Dinfo_get_Dfac(GEN Dinfo) { return gel(Dinfo, 2); }

/* primelist and indexlist
 *
 * primelist begins with 8, -4, -8; subsequent elements are the p^* for
 * successive odd primes <= maxsqrt, by increasing absolute value
 *
 *        i |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 |  10 |  11 |
 * ---------+----+----+----+----+----+----+----+----+----+-----+-----+
 *        i |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 |  10 |  11 |
 * Plist[i] |  8 | -4 | -8 | -3 |  5 | -7 |-11 | 13 | 17 | -19 | -23 |
 *        p |  3 |  5 |  7 |  9 | 11 | 13 | 15 | 17 | 19 |  21 |  23 |
 * ---------+----+----+----+----+----+----+----+----+----+-----+-----+*/

/* primelist containing primes whose absolute value is at most maxsqrt */
static GEN
ecpp_primelist_init(long maxsqrt)
{
  GEN P = cgetg(maxsqrt, t_VECSMALL);
  forprime_t T;
  long p, j = 4;
  u_forprime_init(&T, 3, maxsqrt);
  P[1] =  8; P[2] = -4; P[3] = -8;
  while((p = u_forprime_next(&T))) P[j++] = ((p & 3UL) == 1)? p: -p;
  setlg(P,j); return P;
}

static GEN
Dfac_to_p(GEN x, GEN P) { pari_APPLY_long(uel(P,x[i])); }
static GEN
Dfac_to_roots(GEN x, GEN P) { pari_APPLY_type(t_VEC, gel(P,x[i])); }

#if 0
INLINE ulong
ecpp_param_get_maxsqrt(GEN param) { return umael3(param, 1, 1, 1); }
INLINE ulong
ecpp_param_get_maxdisc(GEN param) { return umael3(param, 1, 1, 2); }
#endif
INLINE ulong
ecpp_param_get_maxpcdg(GEN param) { return umael3(param, 1, 1, 3); }
INLINE GEN
ecpp_param_get_uprimelist(GEN param) { return gmael(param, 1, 2); }
INLINE GEN
ecpp_param_get_primelist(GEN param) { return gmael(param, 1, 3); }
INLINE GEN
ecpp_param_get_disclist(GEN param) { return gmael(param, 1, 4); }
INLINE GEN
ecpp_param_get_primeord(GEN param) { return gmael(param, 1, 5); }
INLINE GEN
ecpp_param_get_primorial_vec(GEN param) { return gel(param, 2); }
INLINE GEN
ecpp_param_get_tune(GEN param) { return gel(param, 3); }

/*  Input: x, 20 <= x <= 35
 * Output: a vector whose ith entry is the product of all primes below 2^x */
static GEN
primorial_vec(ulong x)
{
  pari_sp av = avma;
  long i, y = x-19;
  GEN v = primes_upto_zv(1UL << x), w = cgetg(y+1, t_VEC);
  /* ind[i]th prime number is the largest prime <= 2^(20+i) */
  long ind[] = { 0, 82025L, 155611L, 295947L, 564163L, 1077871L, 2063689L,
                 3957809L, 7603553L, 14630843L, 28192750L, 54400028L,
                 105097565L, 203280221L, 393615806L, 762939111L, 1480206279L};
  gel(w,1) = zv_prod_Z(vecslice(v,1,ind[1]));
  for (i = 2; i <= y; i++)
  {
    pari_sp av2 = avma;
    GEN q = mulii(gel(w,i-1), zv_prod_Z(vecslice(v,ind[i-1]+1,ind[i])));
    gel(w,i) = gc_INT(av2, q);
  }
  return gc_upto(av, w);
}

/* NDmqg contains
   N, as in the theorem in ??ecpp
   Dinfo, as discussed in the comment about Dinfo
   m, as in the theorem in ??ecpp
   q, as in the theorem in ??ecpp
   g, a quadratic nonresidue modulo N
   sqrt, a list of squareroots
*/
INLINE GEN
NDmqg_get_N(GEN x) { return gel(x,1); }
INLINE GEN
NDmqg_get_Dinfo(GEN x) { return gel(x,2); }
INLINE GEN
NDmqg_get_m(GEN x) { return gel(x,3); }
INLINE GEN
NDmqg_get_q(GEN x) { return gel(x,4); }
INLINE GEN
NDmqg_get_g(GEN x) { return gel(x,5); }
INLINE GEN
NDmqg_get_sqrt(GEN x) { return gel(x,6); }

/* COMPARATOR FUNCTIONS */

static int
sort_disclist(void *data, GEN x, GEN y)
{
  long d1, h1, g1, o1, pd1, hf1, wD1, d2, h2, g2, o2, pd2, hf2, wD2;
  (void)data;
  d1 = Dinfo_get_D(x); wD1 = D_get_wD(d1);
  d2 = Dinfo_get_D(y); wD2 = D_get_wD(d2);
  /* higher number of units means more elliptic curves to try */
  if (wD1 != wD2) return wD2 > wD1 ? 1 : -1;
  /* lower polclass degree is better: faster computation of roots modulo N */
  pd1 = Dinfo_get_pd(x); /* degree of polclass */
  pd2 = Dinfo_get_pd(y);
  if (pd1 != pd2) return pd1 > pd2 ? 1 : -1;
  g1 = lg(Dinfo_get_Dfac(x))-1; /* genus number */
  h1 = Dinfo_get_h(x); /* class number */
  o1 = h1 >> (g1-1); /* odd class number */
  g2 = lg(Dinfo_get_Dfac(y))-1;
  h2 = Dinfo_get_h(y);
  o2 = h2 >> (g2-1);
  if (o1 != o2) return g1 > g2 ? 1 : -1;
  /* lower class number is better: higher probability of succesful cornacchia */
  if (h1 != h2) return h1 > h2 ? 1 : -1;
  /* higher height factor is better: polclass would have lower coefficients */
  hf1 = modinv_height_factor(Dinfo_get_bi(x)); /* height factor for best inv. */
  hf2 = modinv_height_factor(Dinfo_get_bi(y));
  if (hf1 != hf2) return hf2 > hf1 ? 1 : -1;
  /* "higher" discriminant is better since its absolute value is lower */
  if (d1 != d2) return d2 > d1 ? 1 : -1;
  return 0;
}

INLINE long
NDmqg_get_D(GEN x) { return Dinfo_get_D(NDmqg_get_Dinfo(x)); }
static int
sort_NDmq_by_D(void *data, GEN x, GEN y)
{
  long d1 = NDmqg_get_D(x);
  long d2 = NDmqg_get_D(y);
  (void)data; return d2 > d1 ? 1 : -1;
}

static int
sort_Dmq_by_q(void *data, GEN x, GEN y)
{ (void)data; return cmpii(gel(x,3), gel(y,3)); }

INLINE long
Dmq_get_D(GEN Dmq) { return Dinfo_get_D(gel(Dmq,1)); }
INLINE long
Dmq_get_h(GEN Dmq) { return Dinfo_get_h(gel(Dmq,1)); }
static int
sort_Dmq_by_cnum(void *data, GEN x, GEN y)
{
  ulong h1 = Dmq_get_h(x);
  ulong h2 = Dmq_get_h(y);
  if (h1 != h2) return h1 > h2 ? 1 : -1;
  return sort_Dmq_by_q(data, x, y);
}

static void
allh_r(GEN H, ulong minD, ulong maxD)
{
  ulong a, A = usqrt(maxD/3), minD2 = (minD-1) >> 1, maxD2 = maxD >> 1;
  for (a = 1; a <= A; a++)
  {
    ulong a2 = a << 1, aa = a*a, aa4 = aa << 2, b, B;
    { /* b = 0 */
      ulong D = aa << 1;
      if (D <= minD2)
        D += a2 * ((minD2 - D + a2) / a2);
      for (; D <= maxD2; D += a2) H[D]++;
    }
    B = aa4 - 1; /* 4a^2 - b^2 */
    for (b = 1; b < a; b++)
    {
      ulong D = B >> 1; /* (4a^2 - b^2) / 2 */
      B -= (b << 1) + 1; if (D > maxD2) continue;
      if (D > minD2)
      {
        H[D]++; D += a2; /* c = a */
      } else
        D += a2 * ((minD2 - D + a2) / a2);
      for (; D <= maxD2; D += a2) H[D] += 2;
    }
    { /* b = a */
      ulong D = (aa4 - aa) >> 1;
      if (D <= minD2)
        D += a2 * ((minD2 - D + a2) / a2);
      for (; D <= maxD2; D += a2) H[D] ++;
    }
  }
}

/* return H s.t if -maxD <= D < 0 is fundamental then H[(-D)>>1] is the
 * ordinary class number of Q(sqrt(D)); junk at other entries. */

static GEN
allh(ulong maxD)
{
  ulong maxD2 = maxD>>1, s = 1UL<<16;
  GEN H = zero_zv(maxD2);
  ulong a;
  for (a = 0; a < maxD; a += s)
    allh_r(H, a+1, minss(a+s,maxD));
  return H;
}

static GEN
mkDinfo(GEN c, long D, long h)
{
  long bi, pd, p1, p2;
  bi = disc_best_modinv(D);
  pd = (modinv_degree(&p1,&p2,bi) && (-D)%p1==0 && (-D)%p2==0)? h/2: h;
  return mkvec2(mkvecsmall4(D, h, bi, pd), c);
}

static GEN
ecpp_disclist_init(ulong maxdisc, GEN primelist)
{
  pari_sp av = avma;
  long t, ip, u, lp, lmerge;
  GEN merge, ev, od, Harr = allh(maxdisc); /* table of class numbers*/
  long lenv = maxdisc/4; /* max length of od/ev */
  long N = maxomegau(maxdisc) + 1;

  /* od[t] attached to discriminant 1-4*t, ev[t] attached to -4*t */
  od = cgetg(lenv + 1, t_VEC); /* contains 'long' at first: save memory */
  ev = cgetg(lenv + 1, t_VEC);
  /* first pass: squarefree sieve and restrict to maxsqrt-smooth disc */
  for (t = 1; t <= lenv; t++)
  {
    od[t] = 1;
    switch(t&7)
    {
      case 0: case 4: ev[t] = 0; break;
      case 2: ev[t] =-8; break;
      case 6: ev[t] = 8; break;
      default:ev[t] =-4; break;
    }
  }
  lp = lg(primelist);
  for (ip = 4; ip < lp; ip++) /* skip 8,-4,-8 */
  { /* sieve by squares of primes */
    long s, q = primelist[ip], p = labs(q);
    s = (q == p)? 3: 1;
    for (t = (s*p+1)>>2; t <= lenv; t += p, s += 4)
    {
      long c = od[t];
      if (c) { if (s%p == 0) od[t] = 0; else  od[t] = c*q; }
    }
    s = 1;
    for (t = p; t <= lenv; t += p, s++)
    {
      long c = ev[t];
      if (c) { if (s%p == 0) ev[t] = 0; else  ev[t] = c*q; }
    }
  }
  for (u = 0, t = 1; t <= lenv; t++)
  { /* restrict to maxsqrt-smooth disc */
    if (od[t] != -4*t+1) od[t] = 0; else u++;
    if (ev[t] != -4*t)   ev[t] = 0; else u++;
  }

  /* second pass: sieve by primes and record factorization */
  for (t = 1; t <= lenv; t++)
  {
    if (od[t]) gel(od,t) = vecsmalltrunc_init(N);
    if (ev[t])
    {
      GEN F = vecsmalltrunc_init(N);
      long id;
      switch(t&7)
      {
        case 2: id = 3; break;
        case 6: id = 1; break;
        default:id = 2; break;
      }
      vecsmalltrunc_append(F, id);
      gel(ev,t) = F;
    }
  }
  lp = lg(primelist);
  for (ip = 4; ip < lp; ip++) /* skip 8,-4,-8 */
  {
    long s, q = primelist[ip], p = labs(q);
    s = (q == p)? 3: 1;
    for (t = (s*p+1)>>2; t <= lenv; t += p, s += 4)
    {
      GEN c = gel(od,t);
      if (c) vecsmalltrunc_append(c, ip);
    }
    s = 1;
    for (t = p; t <= lenv; t += p, s++)
    {
      GEN c = gel(ev,t);
      if (c) vecsmalltrunc_append(c, ip);
    }
  }
  /* merging the two arrays */
  merge = cgetg(u+1, t_VEC); lmerge = 0;
  for (t = 1; t <= lenv; t++)
  {
    GEN c;
    c = gel(od,t); if (c) gel(merge, ++lmerge) = mkDinfo(c,1-4*t, Harr[2*t-1]);
    c = gel(ev,t); if (c) gel(merge, ++lmerge) = mkDinfo(c, -4*t, Harr[2*t]);
  }
  setlg(merge, lmerge);
  gen_sort_inplace(merge, NULL, &sort_disclist, NULL);
  return gc_GEN(av, merge);
}

static GEN
ecpp_primeord_init(GEN primelist, GEN disclist)
{
  long i, k=1, lgdisclist = lg(disclist), lprimelist = lg(primelist);
  GEN primeord = zero_Flv(lprimelist-1);
  for (i=1;i < lgdisclist; i++)
  {
    GEN Dinfo = gel(disclist, i), Dfac = Dinfo_get_Dfac(Dinfo);
    long j, l = lg(Dfac);
    for (j = 1; j < l; j++)
    {
      long ip = Dfac[j];
      if (primeord[ip]==0)
        primeord[ip]=k++;
    }
  }
  return perm_inv(primeord);
}

/*  Input: a vector tune whose components are [maxsqrt,maxpcdg,tdivexp,expiN]
 * Output: vector param of precomputations
 *   let x =  be a component of tune then
 *   param[1][1] = [maxsqrt, maxdisc, maxpcdg]
 *   param[1][2] = primelist = Vecsmall of primes
 *   param[1][3] = disclist  = vector of Dinfos, sorted by quality
 *   param[2]    = primorial_vec
 *   param[3]    = tune */
static GEN
ecpp_param_set(GEN tune, GEN x)
{
  pari_timer ti;
  pari_sp av = avma;
  ulong maxsqrt = uel(x,1), maxpcdg = uel(x,2), tdivexp = uel(x,3);
  ulong maxdisc = maxsqrt * maxsqrt;
  GEN Plist, U, Utree, Dlist, Olist, primorial, T;
  T = mkvecsmall3(maxsqrt, maxdisc, maxpcdg);
  dbg_mode() {
    err_printf(ANSI_BRIGHT_WHITE "\nECPP: parameters %Ps:\n"
               "init time: " ANSI_RESET, x);
    timer_start(&ti);
  }
  Plist = ecpp_primelist_init(maxsqrt);
  U = zv_abs(Plist);
  Utree = mkvec2(U, ZV_producttree(U));
  dbg_mode() err_printf("%ld",timer_delay(&ti));
  Dlist = ecpp_disclist_init(maxdisc, Plist);
  dbg_mode() err_printf(", %ld",timer_delay(&ti));
  Olist = ecpp_primeord_init(Plist, Dlist);
  dbg_mode() err_printf(", %ld",timer_delay(&ti));
  primorial = primorial_vec(tdivexp);
  dbg_mode() err_printf(", %ld\n",timer_delay(&ti));
  return gc_GEN(av, mkvec3(mkvec5(T,Utree,Plist,Dlist,Olist),
                                 primorial, tune));
}

/* cert contains [N, t, s, a4, [x, y]] as documented in ??ecpp; the following
 * information can be obtained:
 * D = squarefreepart(t^2-4N)
 * m = (N+1-t), q = m/s, a6 = y^3 - x^2 - a4*x, J */
INLINE GEN
cert_get_N(GEN x) { return gel(x,1); }
INLINE GEN
cert_get_t(GEN x) { return gel(x,2); }
INLINE GEN
cert_get_D(GEN x)
{
  GEN N = cert_get_N(x), t = cert_get_t(x);
  return coredisc(subii(sqri(t), shifti(N, 2)));
}
INLINE GEN
cert_get_m(GEN x)
{
  GEN N = cert_get_N(x), t = cert_get_t(x);
  return subii(addiu(N, 1), t);
}
INLINE GEN
cert_get_s(GEN x) { return gel(x,3); }
INLINE GEN
cert_get_q(GEN x) { return diviiexact(cert_get_m(x), cert_get_s(x)); }
INLINE GEN
cert_get_qlast(GEN x) { return cert_get_q(veclast(x)); }
INLINE GEN
cert_get_a4(GEN x) { return gel(x,4); }
INLINE GEN
cert_get_P(GEN x) { return gel(x,5); }
INLINE GEN
cert_get_x(GEN x) { return gel(cert_get_P(x), 1); }
INLINE GEN
cert_get_a6(GEN z)
{
  GEN N = cert_get_N(z), a = cert_get_a4(z), P = cert_get_P(z);
  GEN x = gel(P,1), xx = Fp_sqr(x, N);
  GEN y = gel(P,2), yy = Fp_sqr(y, N);
  return Fp_sub(yy, Fp_mul(x, Fp_add(xx,a,N), N), N);
}
INLINE GEN
cert_get_E(GEN x) { return mkvec2(cert_get_a4(x), cert_get_a6(x)); }
INLINE GEN
cert_get_J(GEN x)
{
  GEN a = cert_get_a4(x), b = cert_get_a6(x), N = cert_get_N(x);
  return Fp_ellj(a, b, N);
}

/* "Twist factor". Does not cover J = 0, 1728 */
static GEN
cert_get_lambda(GEN z)
{
  GEN N, J, a, b, A, B;
  J = cert_get_J(z);
  N = cert_get_N(z);
  a = cert_get_a4(z);
  b = cert_get_a6(z);
  Fp_ellj_to_a4a6(J, N, &A, &B);
  return Fp_div(Fp_mul(a,B,N), Fp_mul(b,A,N), N);
}

/* Solves for T such that if
   [A, B] = [3*J*(1728-J), 2*J*(1728-J)^2]
   and you let
   L = T^3 + A*T + B, A = A*L^2, B = B*L^3
   then
   x == TL and y == L^2
*/
static GEN
cert_get_T(GEN z)
{
  GEN N = cert_get_N(z), x = cert_get_x(z);
  GEN l = cert_get_lambda(z); /* l = 1/L */
  return Fp_mul(x, l, N);
}

/* database for all invariants, stolen from Hamish's code */
static GEN
polmodular_db_init_allinv(void)
{
  const long DEFAULT_MODPOL_DB_LEN = 32;
  GEN a, b = cgetg(INV_LAST+1, t_VEC);
  long i;
  for (i = 1; i <= INV_LAST; i++) gel(b,i) = zerovec_block(DEFAULT_MODPOL_DB_LEN);
  a = zerovec_block(DEFAULT_MODPOL_DB_LEN);
  return mkvec2(a, b);
}

/* Given D and a database of modular polynomials, return polclass(D, inv) */
static GEN
D_polclass(long D, long inv, GEN *db)
{
  GEN HD, t = mkvec2(gel(*db, 1), inv == 0? gen_0: gmael(*db, 2, inv));
  HD = polclass0(D, inv, 0, &t);
  gel(*db, 1) = gel(t,1);
  if (inv != 0) gmael(*db, 2, inv) = gel(t,2);
  return HD;
}

static GEN
NqE_check(GEN N, GEN q, GEN a, GEN b, GEN s)
{
  GEN mP, sP, P = random_FpE(a, b, N);
  GEN PJ = mkvec3(gel(P,1), gel(P,2), gen_1);
  sP = FpJ_mul(PJ, s, a, N); if (FpJ_is_inf(sP)) return NULL;
  mP = FpJ_mul(sP, q, a, N); return FpJ_is_inf(mP)? mkvec2(a, P): NULL;
}

/* Find an elliptic curve E modulo N and a point P on E which corresponds to
 * the ith element of the certificate; uses N, D, m, q, J from previous steps.
 * All computations are modulo N unless stated otherwise */

/* g is a quadratic and cubic nonresidue modulo N */
static GEN
j0_find_g(GEN N)
{
  GEN n = diviuexact(subiu(N, 1), 3);
  for(;;)
  {
    GEN g = randomi(N);
    if (kronecker(g, N) == -1 && !equali1(Fp_pow(g, n, N))) return g;
  }
}

static GEN
find_EP(GEN N, long D, GEN q, GEN g, GEN J, GEN s)
{
  GEN A0, B0;
  Fp_ellj_to_a4a6(J, N, &A0, &B0);
  for(;;)
  { /* expect one iteration: not worth saving the A's and B's */
    GEN gg, v, A = A0, B = B0;
    long i;
    if ((v = NqE_check(N, q, A, B, s))) return v;
    switch (D_get_wD(D))
    {
      case 2:
        gg = Fp_sqr(g, N);
        A = Fp_mul(A, gg, N);
        B = Fp_mul(Fp_mul(B, gg, N), g, N);
        if ((v = NqE_check(N, q, A, B, s))) return v;
        break;
      case 4:
        for (i = 1; i < 4; i++)
        {
          A = Fp_mul(A, g, N);
          if ((v = NqE_check(N, q, A, B, s))) return v;
        }
        break;
      default: /* 6 */
        B = Fp_mul(B, g, N);
        if ((v = NqE_check(N, q, A, B, s))) return v;
        g = j0_find_g(N);
        for (i = 1; i < 6; i++)
        {
          B = Fp_mul(B, g, N);
          if (i == 3) continue;
          if ((v = NqE_check(N, q, A, B, s))) return v;
        }
        break;
    }
  }
}

/* Return the genus field. If real is set only the real part */
static GEN
genusfield(GEN Dfac, GEN sq, GEN p, long real)
{
  long i, j, l = lg(Dfac), dn, n = 0;
  GEN sn, s = gen_0, R = cgetg(l-1+!real, t_VECSMALL);
  for (i = 1; i < l; i++)
    if (Dfac[i] < 0) { n = i; break; }
  if (n == 0) pari_err_BUG("realgenusfield");
  dn = Dfac[n]; sn = gel(sq, n);
  for (j = i = 1; i < l; i++)
    if (i != n)
    {
      long d = Dfac[i];
      GEN si = gel(sq,i);
      R[j++] = d > 0 ? d : d * dn;
      s = Fp_add(s, d > 0? si: Fp_mul(si, sn, p), p);
    }
  if (!real)
  {
    R[j++] = dn;
    s = Fp_add(s,sn, p);
  }
  return mkvec2(R, s);
}

static GEN
realpart(GEN P, GEN R)
{
  GEN G = galoisinit(rnfequation(P,R), NULL);
  GEN T = galoisfixedfield(G, gel(gal_get_gen(G),2), 1, -1);
  setvarn(T,1); return polredbest(T,0);
}

static GEN
dihedralpol(long D, long l)
{
  GEN P = quadpoly0(utoineg(-D), 1);
  GEN bnf = Buchall(P, 1, BIGDEFAULTPREC);
  GEN x = bnrclassfield(bnf, utoipos(l), 0, BIGDEFAULTPREC);
  pari_APPLY_same(realpart(P, gel(x,i)))
}

static GEN
FpX_classtower_oneroot(GEN P, GEN Dinfo, GEN Dfac, GEN sq, GEN p)
{
  long D = Dinfo_get_D(Dinfo), h = Dinfo_get_h(Dinfo);
  if (degpol(P) > 1)
  {
    long real = !modinv_is_double_eta(Dinfo_get_bi(Dinfo));
    GEN V = genusfield(Dfac, sq, p, real), v = gel(V,1), R = gel(V,2);
    GEN N = NULL;
    long i, l = lg(v);
    for (i = 1; i < l; i++)
    {
      GEN Q = deg2pol_shallow(gen_1, gen_0, stoi(-v[i]), 1);
      if (!N) N = Q;
      else
      {
        GEN cm = polcompositum0(N,Q,3);
        N = gel(cm,1); P = QXY_QXQ_evalx(P,gmael(cm,2,2),N);
      }
      P = liftpol_shallow(gmael(nffactor(N,P),1,1));
    }
    if (h%3 == 0 && (!N || degpol(N)*3<degpol(P)))
    {
      GEN v = dihedralpol(D,3);
      long i, l = lg(v);
      for (i = 1; i < l; i++)
      {
        GEN Q = gel(v,i);
        if (!N) N = Q;
        else
        {
          GEN cm = polcompositum0(N, Q, 3);
          N = gel(cm,1); P = QXY_QXQ_evalx(P,gmael(cm,2,2),N);
          R = Fp_mul(R, gel(cm,4),p);
        }
        R = Fp_add(R, FpX_oneroot_split(Q, p), p);
        P = liftpol_shallow(gmael(nffactor(N,P),1,1));
        if (degpol(N)*3>=degpol(P)) break;
      }
    }
    if (N)
      P = FpXY_evalx(Q_primpart(P), R, p);
  }
  return P;
}

GEN
ecpp_step2_worker(GEN S, GEN HD, GEN primelist, long dbg)
{
  pari_sp av = avma;
  pari_timer ti;
  GEN J, t, s, EP, rt, res;
  GEN N = NDmqg_get_N(S), Dinfo = NDmqg_get_Dinfo(S);
  GEN m = NDmqg_get_m(S), q = NDmqg_get_q(S);
  GEN g = NDmqg_get_g(S), sq = NDmqg_get_sqrt(S);
  long D = Dinfo_get_D(Dinfo), inv = Dinfo_get_bi(Dinfo);
  GEN Dfacp = Dfac_to_p(Dinfo_get_Dfac(Dinfo), primelist);
  long C2 = 0, C3 = 0, C4 = 0, D1 = 0;
  GEN P, c = getrand();
  setrand(gen_1); /* for reproducibility */
  /* C2: Find a root modulo N of polclass(D,inv) */
  if (dbg >= 2) timer_start(&ti);
  P = FpX_classtower_oneroot(HD, Dinfo, Dfacp, sq, N);
  if (dbg >= 2) C2 = timer_delay(&ti);
  rt = FpX_oneroot_split(P, N);
  if (dbg >= 2) C3 = timer_delay(&ti);
  /* C3: Convert root from previous step into the appropriate j-invariant */
  J = Fp_modinv_to_j(rt, inv, N); /* root of polclass(D) */
  if (dbg >= 2) C4 = timer_delay(&ti);
  /* D1: Find an elliptic curve E with a point P satisfying the theorem */
  s = diviiexact(m, q);
  EP = find_EP(N, D, q, g, J, s);
  if (dbg >= 2) D1 = timer_delay(&ti);

  /* D2: Compute for t and s */
  t = subii(addiu(N, 1), m); /* t = N+1-m */
  res = mkvec2(mkvec5(N, t, s, gel(EP,1), gel(EP,2)),mkvecsmall4(C2,C3,C4,D1));
  setrand(c);
  return gc_GEN(av, res);
}

/* This uses [N, D, m, q] from step 1 to find the appropriate j-invariants
 * to be used in step 3. Step 2 is divided into substeps 2a, 2b, 2c */
static GEN
ecpp_step2(GEN step1, GEN *X0, GEN primelist)
{
  long j, Dprev = 0;
  pari_timer ti;
  GEN perm = gen_indexsort(step1, NULL, &sort_NDmq_by_D);
  GEN step2 = cgetg(lg(step1), t_VEC);
  GEN HD = NULL, db = polmodular_db_init_allinv();
  long ls = lg(step2), pending = 0;
  GEN worker;
  struct pari_mt pt;
  GEN Hi = cgetg(ls, t_VEC);
  for (j = 1; j < ls; j++)
  {
    long i = uel(perm, j);
    GEN S = gel(step1, i);
    GEN Dinfo = NDmqg_get_Dinfo(S);
    long D = Dinfo_get_D(Dinfo), inv = Dinfo_get_bi(Dinfo);
    /* C1: Find the appropriate class polynomial modulo N */
    dbg_mode() timer_start(&ti);
    if (D != Dprev) HD = D_polclass(D, inv, &db);
    dbg_mode() {
      GEN N = NDmqg_get_N(S);
      long tt = timer_record(X0, "C1", &ti);
      err_printf(ANSI_BRIGHT_GREEN "\n[ %3d | %4ld bits]" ANSI_RESET, i, expi(N));
      err_printf(ANSI_GREEN " D = %8ld inv = %3ld poldeg = %4ld" ANSI_RESET, D, inv, degpol(HD));
      if (D == Dprev) err_printf(" %6ld", tt);
      else err_printf(ANSI_BRIGHT_WHITE " %6ld" ANSI_RESET, tt);
    }
    gel(Hi, i) = HD;
  }
  gunclone_deep(db);
  worker = snm_closure(is_entry("_ecpp_step2_worker"),
                       mkvec2(primelist,stoi(DEBUGLEVEL)));
  mt_queue_start_lim(&pt, worker, ls-1);
  for (j = 1; j < ls || pending; j++)
  {
    long jj;
    GEN S = gel(step1, j), HD = gel(Hi, j), done;
    mt_queue_submit(&pt, j, j < ls ? mkvec2(S, HD) : NULL);
    done = mt_queue_get(&pt, &jj, &pending);
    if (!done) continue;
    dbg_mode() {
      GEN T = gel(done,2);
      GEN N = NDmqg_get_N(gel(step1, jj));
      err_printf(ANSI_BRIGHT_GREEN "\n[ %3d | %4ld bits]" ANSI_RESET, jj, expi(N));
      err_printf(" %6ld", time_record(X0, "C2", T[1]));
      err_printf(" %6ld", time_record(X0, "C3", T[2]));
      err_printf(" %6ld", time_record(X0, "C4", T[3]));
      err_printf(" %6ld", time_record(X0, "D1", T[4]));
    }
    gel(step2, jj) = gel(done,1);
  }
  mt_queue_end(&pt);
  return step2;
}
/* end of functions for step 2 */

GEN
ecpp_sqrt_worker(GEN p, GEN g, GEN N)
{
  GEN r = Fp_sqrt_i(p, g, N);
  return r ? r: gen_0;
}

static void
ecpp_parsqrt(GEN N, GEN param, GEN kroP, GEN sqrtlist, GEN g, long nb, long *nbsqrt)
{
  GEN primelist = ecpp_param_get_primelist(param);
  GEN ordinv = ecpp_param_get_primeord(param);
  long i, k, l = lg(ordinv), n = *nbsqrt+1;
  GEN worker = snm_closure(is_entry("_ecpp_sqrt_worker"), mkvec2(g, N));
  GEN W = cgetg(nb+1,t_VEC), V;
  for (i=n, k=1; k<=nb && i<l; i++)
  {
    long pi = ordinv[i];
    if (kroP[pi] > 0)
      gel(W,k++) = stoi(primelist[pi]);
  }
  *nbsqrt=i-1;
  setlg(W,k);
  V = gen_parapply(worker, W);
  for (i=n, k=1; k<=nb && i<l; i++)
  {
    long pi = ordinv[i];
    if (kroP[pi] > 0)
    {
      dbg_mode() err_printf(ANSI_MAGENTA "S" ANSI_RESET);
      if (!signe(gel(V,k)))
        pari_err_BUG("D_find_discsqrt"); /* possible if N composite */
      gel(sqrtlist,pi) = gel(V,k++);
    }
  }
}

/* start of functions for step 1 */

/* This finds the square root of D modulo N [given by Dfac]: find the square
 * root modulo N of each prime p dividing D and multiply them out */
static GEN
D_find_discsqrt(GEN N, GEN param, GEN Dfac, GEN kroP, GEN sqrtlist, GEN g, long *nbsqrt)
{
  GEN s = NULL, sj;
  long i, l = lg(Dfac);
  for (i = 1; i < l; i++)
  {
    long j = Dfac[i];
    while(!signe(gel(sqrtlist,j)))
      ecpp_parsqrt(N, param, kroP, sqrtlist, g, mt_nbthreads(), nbsqrt);
    sj = gel(sqrtlist,j);
    s = s? Fp_mul(s, sj, N): sj;
  }
  return s;/* != NULL */
}

/* Given a solution U, V to U^2 + |D|V^2 = 4N, this find all the possible
     cardinalities of the elliptic curves over the finite field F_N
     whose endomorphism ring is isomorphic to the maximal order
     in the imaginary quadratic number field K = Q(sqrt(D)). ???
*/
static GEN
NUV_find_m(GEN Dinfo, GEN N, GEN U, GEN V, long wD)
{
  GEN m, Nplus1 = addiu(N, 1), u = U, mvec = cgetg(wD+1, t_VEC);
  long i;
  for (i = 0; i < wD; i++)
  {
    if (odd(i)) m = subii(Nplus1, u);
    else
    {
      if (wD == 4 && i==2) u = shifti(V, 1);
      else if (wD == 6 && i==2) u = shifti(submuliu(U, V, 3), -1);
      else if (wD == 6 && i==4) u = shifti(addmuliu(U, V, 3), -1);
      m = addii(Nplus1, u);
    }
    gel(mvec, i+1) = mkvec2(Dinfo, m);
  }
  return mvec;
}

/* Populates Dmbatch with Dmvec's -- whose components are of the form [D,m],
   where m is a cardinalities of an elliptic curve with endomorphism ring
   isomorphic to the maximal order of imaginary quadratic K = Q(sqrt(D)).
   It returns 0 if:
     * Any of the p* dividing D is not a quadratic residue mod N
     * Cornacchia cannot find a solution U^2 + |D|V^2 = 4N.
   Otherwise, it returns the number of cardinalities added to Dmbatch.
   Finally, sqrtlist and g help compute the square root modulo N of D.
*/
static long
D_collectcards(GEN N, GEN param, GEN* X0, GEN Dinfo, GEN sqrtlist, GEN g, GEN Dmbatch, GEN kroP, long *nbsqrt)
{
  long i, l, corn_succ, wD, D = Dinfo_get_D(Dinfo);
  GEN U, V, sqrtofDmodN, Dfac = Dinfo_get_Dfac(Dinfo);
  pari_timer ti;

  /* A1: Check (p*|N) = 1 for all primes dividing D */
  l = lg(Dfac);
  for (i = 1; i < l; i++)
  {
    long j = Dfac[i];
    if (kroP[j] < 0) return 0;
  }
  /* A3: Get square root of D mod N */
  dbg_mode() timer_start(&ti);
  sqrtofDmodN = D_find_discsqrt(N, param, Dfac, kroP, sqrtlist, g, nbsqrt);
  dbg_mode() timer_record(X0, "A3", &ti);
  /* A5: Use square root with Cornacchia to solve U^2 + |D|V^2 = 4N */
  dbg_mode() timer_start(&ti);
  corn_succ = cornacchia2_sqrt( utoi(labs(D)), N, sqrtofDmodN, &U, &V);
  dbg_mode() timer_record(X0, "A5", &ti);
  if (!corn_succ) {
    dbg_mode1() err_printf(ANSI_YELLOW "c" ANSI_RESET);
    return 0;
  }
  /* A6: Collect the w(D) cardinalities of E/(F_N) with CM by D */
  dbg_mode() err_printf(ANSI_BRIGHT_YELLOW "D" ANSI_RESET);
  wD = D_get_wD(D);
  vectrunc_append_batch(Dmbatch, NUV_find_m(Dinfo,N,U,V,wD));
  return wD;
}

/* Compute (S(16N, 2) + S(4096N, 4) + 4)\4 + 1,  where S is the nth root
 * rounded down. This is at most one more than (N^1/4 + 1)^2. */
static GEN
ecpp_qlo(GEN N)
{
  GEN a = sqrtnint(shifti(N, 4), 2);
  GEN b = sqrtnint(shifti(N, 12), 4);
  return addiu(shifti(addii(a, b), -2), 2);
}

static long
lessthan_qlo(void* E, GEN Dmq) { return (cmpii(gel(Dmq,3), (GEN)E) < 0); }
static long
gained_bits(void* E, GEN Dmq) { return (expi(gel(Dmq,3)) <= (long)E); }

/*  Input: Dmqvec
 * Output: Dmqvec such that q satisfies (N^1/4 + 1)^2 < q < N/2 */
static GEN
Dmqvec_slice(GEN N, GEN Dmqvec)
{
  long lo, hi;

  gen_sort_inplace(Dmqvec, NULL, &sort_Dmq_by_q, NULL); /* sort wrt q */
  lo = zv_binsearch0((void*)ecpp_qlo(N), &lessthan_qlo, Dmqvec); lo++;
  if (lo >= lg(Dmqvec)) return NULL;

  hi = zv_binsearch0((void*)(expi(N)-1), &gained_bits, Dmqvec);
  if (hi == 0) return NULL;

  return vecslice(Dmqvec, lo, hi);
}

/* Given a Dmvec of [D,m]'s, simultaneously remove all prime factors of each
 * m less then BOUND_PRIMORIAL. This implements Franke 2004: Proving the
 * Primality of Very Large Numbers with fastECPP */
static GEN
Dmvec_batchfactor(GEN Dmvec, GEN primorial)
{
  long i, l = lg(Dmvec);
  GEN leaf, v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  { /* cheaply remove powers of 2 */
    GEN m = gmael(Dmvec, i, 2);
    long v2 = vali(m);
    gel(v,i) = v2? shifti(m,-v2): m;
  }
  leaf = Z_ZV_mod_tree(primorial, v, ZV_producttree(v));
  /* Go through each leaf and remove small factors. */
  for (i = 1; i < l; i++)
  {
    GEN q = gel(v,i), Dm = gel(Dmvec,i), L = gel(leaf,i);
    while (!equali1(L)) { L = gcdii(q, L); q = diviiexact(q, L); }
    gel(v,i) = mkvec3(gel(Dm,1), gel(Dm,2), q);
  }
  return v;
}

/* return good parameters [maxsqrt, maxpcdg, tdivexp] for ecpp(N) */
static GEN
tunevec(long expiN, GEN param)
{
  GEN T = ecpp_param_get_tune(param);
  long i, n = lg(T)-1;
  for (i = 1; i < n; i++) { GEN x = gel(T,i); if (expiN <= x[4]) return x; }
  return gel(T,n);
}
static long
tunevec_tdivbd(long expiN, GEN param) { return uel(tunevec(expiN, param), 3); }
static long
tunevec_batchsize(long expiN, GEN param)
{
  long t, b = 28 - tunevec_tdivbd(expiN, param);
  if (b < 0) return expiN;
  t = expiN >> b; return t < 1? 1: t;
}

static GEN
Dmbatch_factor_Dmqvec(GEN N, long expiN, GEN* X0, GEN Dmbatch, GEN param)
{
  pari_sp av = avma;
  pari_timer ti;
  GEN Dmqvec, primorial_vec = ecpp_param_get_primorial_vec(param);
  GEN primorial = gel(primorial_vec, tunevec_tdivbd(expiN, param)-19);

  /* B1: Factor by batch */
  dbg_mode() timer_start(&ti);
  Dmqvec = Dmvec_batchfactor(Dmbatch, primorial);
  dbg_mode() timer_record(X0, "B1", &ti);

  /* B2: For each batch, remove cardinalities lower than (N^(1/4)+1)^2
   *     and cardinalities in which we didn't win enough bits */
  Dmqvec = Dmqvec_slice(N, Dmqvec);
  if (!Dmqvec) return gc_NULL(av); /* nothing is left */
  return gc_GEN(av, Dmqvec);
}

GEN
ecpp_ispsp_worker(GEN N)
{ return mkvecsmall(BPSW_psp_nosmalldiv(N)); }

static GEN
mkNDmqg(GEN z, GEN N, GEN Dmq, GEN g, GEN sqrtlist)
{
  GEN Dinfo = gel(Dmq,1), sq =  Dfac_to_roots(Dinfo_get_Dfac(Dinfo),sqrtlist);
  GEN NDmqg = mkcol6(N, Dinfo, gel(Dmq,2), gel(Dmq,3), g, sq);
  return mkvec2(NDmqg, z);
}
/* expi(N) > 64. Return [ NDmqg, N_downrun(q) ]; NDmqg is a vector of the form
 * [N,D,m,q,g,sqrt]. For successive D, find a square root of D mod N (g is a
 * quadratic nonresidue), solve U^2 + |D|V^2 = 4N, then find candidates for m.
 * When enough m's, batch-factor them to produce the q's. If one of the q's is
 * pseudoprime, recursive call with N = q. May return gen_0 at toplevel
 * => N has a small prime divisor */
static GEN
N_downrun(GEN N, GEN param, GEN worker, GEN *X0, long *depth, long persevere, long stopat)
{
  pari_timer T, ti;
  long lgdisclist, lprimelist, nbsqrt = 0, t, i, j, expiN = expi(N);
  long persevere_next = 0, FAIL = 0;
  ulong maxpcdg;
  GEN primelist, uprimelist, disclist, sqrtlist, g, Dmbatch, kroP, Np;

  dbg_mode() timer_start(&T);
  (*depth)++; /* we're going down the tree. */
  maxpcdg = ecpp_param_get_maxpcdg(param);
  primelist = ecpp_param_get_primelist(param);
  uprimelist = ecpp_param_get_uprimelist(param);
  disclist = ecpp_param_get_disclist(param);
  lgdisclist = lg(disclist);
  t = tunevec_batchsize(expiN, param);

  /* Precomputation for taking square roots, g needed for Fp_sqrt_i */
  g = Fp_2gener(N); if (!g) return gen_0; /* Composite if this happens. */

  /* Initialize sqrtlist for this N. */
  lprimelist = lg(primelist);
  sqrtlist = zerovec(lprimelist-1);

  /* A2: Check (p*|N) = 1 for all p */
  dbg_mode() timer_start(&ti);
  /* kroP[i] will contain (primelist[i] | N) */
  kroP = cgetg(lprimelist,t_VECSMALL);
  switch(mod8(N))
  { /* primelist[1,2,3] = [8,-4,-8]; N is odd */
    case 1: kroP[1] = kroP[2] = kroP[3] = 1; break;
    case 3: kroP[1] = -1; kroP[2] =-1; kroP[3] = 1; break;
    case 5: kroP[1] = -1; kroP[2] = 1; kroP[3] =-1; break;
    case 7: kroP[1] =  1; kroP[2] =-1; kroP[3] =-1; break;
  }
  Np = Z_ZV_mod_tree(N, gel(uprimelist,1), gel(uprimelist,2));
  for(i=4; i<lprimelist; i++)
  {
    if (Np[i]==0) return gen_0;
    kroP[i] = kross(Np[i],primelist[i]);
  }
  dbg_mode() timer_record(X0, "A2", &ti);

  /* Print the start of this iteration. */
  dbg_mode() {
    char o = persevere? '<': '[';
    char c = persevere? '>': ']';
    err_printf(ANSI_BRIGHT_CYAN "\n%c %3d | %4ld bits%c "
               ANSI_RESET, o, *depth, expiN, c);
  }
  /* Initialize Dmbatch, populated with candidate cardinalities in Phase I
   * (until #Dmbatch >= t); its elements will be factored on Phase II */
  Dmbatch = vectrunc_init(t+7);

  /* Number of cardinalities so far; should always be equal to lg(Dmbatch)-1. */
  /* i determines which discriminant we are considering. */
  i = 1;
  while (!FAIL)
  {
    pari_timer F;
    long lgDmqlist, last_i = i, numcard = 0; /* #Dmbatch */
    GEN Dmqlist;

    /* Dmbatch begins "empty", but keep the allocated memory. */
    setlg(Dmbatch, 1);

    /* PHASE I: Go through the D's and search for candidate m's.
     * Fill up Dmbatch until there are at least t elements. */
    while (i < lgdisclist )
    {
      GEN Dinfo = gel(disclist, i);
      long n;
      if (!persevere && Dinfo_get_pd(Dinfo) > maxpcdg) { FAIL = 1; break; }
      n = D_collectcards(N,param, X0, Dinfo, sqrtlist, g, Dmbatch, kroP, &nbsqrt);
      if (n < 0) return gen_0;
      last_i = i++;
      numcard += n; if (numcard >= t) break;
    }

    /* We have exhausted disclist and there are no card. to be factored */
    if (numcard <= 0 && (FAIL || i >= lgdisclist)) break;

    /* PHASE II: Find the corresponding q's for the m's found. Use Dmbatch */
    /* Find coresponding q of the candidate m's. */
    dbg_mode() timer_start(&F);
    Dmqlist = Dmbatch_factor_Dmqvec(N, expiN, X0, Dmbatch, param);
    if (Dmqlist == NULL) continue; /* none left => next discriminant. */

    /* If we are cheating by adding class numbers, sort by class number */
    if (Dinfo_get_pd(gel(disclist, last_i)) > maxpcdg)
      gen_sort_inplace(Dmqlist, NULL, &sort_Dmq_by_cnum, NULL);

    /* Check pseudoprimality before going down. */
    lgDmqlist = lg(Dmqlist);
    for (j = 1; j < lgDmqlist; j++)
    {
      GEN z, Dmq, q;
      struct pari_mt pt;
      pari_timer ti2;
      long running, stop = 0, pending = 0;
      mt_queue_start_lim(&pt, worker, lgDmqlist-j);
      dbg_mode() timer_start(&ti2);
      while ((running = (!stop && j < lgDmqlist)) || pending)
      {
        long jj;
        GEN done;
        mt_queue_submit(&pt, j, running ? mkvec(gmael(Dmqlist,j,3)) : NULL);
        done = mt_queue_get(&pt, &jj, &pending);
        if (done)
        {
          if (done[1] == 0)
          { dbg_mode() err_printf(ANSI_WHITE "." ANSI_RESET); }
          else if (!stop || jj < stop)
            stop = jj;
        }
        j++;
      }
      mt_queue_end(&pt);
      dbg_mode() timer_record(X0, "B3", &ti2);
      if (!stop && j >= lgDmqlist) break;
      j = stop; Dmq = gel(Dmqlist,j); q = gel(Dmq,3);

      dbg_mode() {
        err_printf(ANSI_BRIGHT_RED "\n       %5ld bits " ANSI_RESET,
                   expi(q)-expiN);
        err_printf("  D = %ld", Dmq_get_D(Dmq));
        err_printf(ANSI_BRIGHT_BLUE "  h = %ld" ANSI_RESET, Dmq_get_h(Dmq));
      }
      /* q is pseudoprime */
      if (expi(q) < stopat) z = gen_1; /* q is prime; sentinel */
      else
      {
        z = N_downrun(q, param, worker, X0, depth, persevere_next, stopat);
        if (!z) {
          dbg_mode() { char o = persevere? '<': '[', c = persevere? '>': ']';
                       err_printf(ANSI_CYAN "\n%c %3d | %4ld bits%c "
                                  ANSI_RESET, o, *depth, expiN, c); }
          continue; /* downrun failed */
        }
        if (isintzero(z)) return z;
      }
      return mkNDmqg(z, N, Dmq, g, sqrtlist); /* SUCCESS */
    }
    if (i >= lgdisclist) break; /* discriminants exhausted: FAIL */
    if (Dinfo_get_pd(gel(disclist, last_i)) > maxpcdg)
    {
      dbg_mode() err_printf(ANSI_BRIGHT_RED "  !" ANSI_RESET);
      persevere_next = 1;
    }
  }
  /* FAILED: Out of discriminants. */
  umael(*X0, 3, 1)++; /* FAILS++ */
  dbg_mode() err_printf(ANSI_BRIGHT_RED "  X" ANSI_RESET);
  (*depth)--; return NULL;
}

/* x: the output of the (recursive) downrun function; return a vector
 * whose components are [N, D, m, q, g] */
static GEN
ecpp_flattencert(GEN x, long depth)
{
  long i, l = depth+1;
  GEN ret = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) { gel(ret, i) = gel(x,1); x = gel(x,2); }
  return ret;
}

/* Call the first downrun then unravel the skeleton of the certificate.
 * Assume expi(N) < 64. This returns one of the following:
 * - a vector of the form [N, D, m, q, y]
 * - gen_0 (if N is composite)
 * - NULL (if FAIL) */
static GEN
ecpp_step1(GEN N, GEN param, GEN* X0, long stopat)
{
  pari_sp av = avma;
  long depth = 0;
  GEN worker = strtofunction("_ecpp_ispsp_worker");
  GEN downrun = N_downrun(N, param, worker, X0, &depth, 1, stopat);
  if (downrun == NULL) return gc_NULL(av);
  if (typ(downrun) != t_VEC) return gen_0;
  return gc_GEN(av, ecpp_flattencert(downrun, depth));
}

/* The input is an integer N.
   It uses the precomputation step0 done in ecpp_step0. */
static GEN
ecpp_param(GEN N, GEN param, long stopat)
{

  GEN step1, answer, Tv, Cv, X0;
  pari_sp av = avma;
  long i, j;

  /* Check if N is pseudoprime to begin with. */
  if (!BPSW_psp(N)) return gen_0;

  /* Check if we should even prove it. */
  if (expi(N) < stopat) return N;

  /* Timers and Counters */
  Tv = mkvec4(zero_zv(5), zero_zv(3), zero_zv(4), zero_zv(1));
  Cv = mkvec4(zero_zv(5), zero_zv(3), zero_zv(4), zero_zv(1));
  X0 = mkvec3(Tv, Cv, zero_zv(1));

  step1 = ecpp_step1(N, param, &X0, stopat);
  if (step1 == NULL) return gc_NULL(av);
  if (typ(step1) != t_VEC) { set_avma(av); return gen_0; }

  answer = ecpp_step2(step1, &X0, ecpp_param_get_primelist(param));

  dbg_mode() {
  for (i = 1; i < lg(Tv); i++)
  {
    GEN v = gel(Tv, i);
    long l = lg(v);
    for (j = 1; j < l; j++)
    {
      long t = umael3(X0,1, i,j), n = umael3(X0,2, i,j);
      if (!t) continue;
      err_printf("\n  %c%ld: %16ld %16ld %16.3f", 'A'+i-1,j, t,n, (double)t/n);
    }
  }
    err_printf("\n" ANSI_BRIGHT_RED "\nFAILS: %16ld" ANSI_RESET "\n", umael(X0, 3, 1));
  }
  return gc_GEN(av, answer);
}

static const long ecpp_tune[][4]=
{
  {  100,  2,  20,   500 },
  {  350, 14,  21,  1000 },
  {  450, 18,  21,  1500 },
  {  750, 22,  22,  2000 },
  {  900, 26,  23,  2500 },
  { 1000, 32,  23,  3000 },
  { 1200, 38,  24,  3500 },
  { 1400, 44,  24,  4000 },
  { 1600, 50,  24,  4500 },
  { 1800, 56,  25,  5000 },
  { 2000, 62,  25,  5500 },
  { 2200, 68,  26,  6000 },
  { 2400, 74,  26,  6500 },
  { 2600, 80,  26,  7000 },
  { 2800, 86,  26,  7500 },
  { 3000, 92,  27,  8000 },
  { 3200, 98,  27,  8500 },
  { 3400, 104, 28,  9000 },
  { 3600, 110, 28,  9500 },
  { 3800, 116, 29, 10000 },
  { 4000, 122, 29,     0 }
};

/* assume N BPSW-pseudoprime */
GEN
ecpp0(GEN C, long stopat)
{
  pari_sp av = avma;
  long expiN, i, tunelen;
  GEN N = C, tune;

  /* Is it a partial certificate? */
  if (typ(C) == t_VEC && check_ecppcert(C))
    N = cert_get_qlast(C);
  if (typ(N) != t_INT)
    pari_err_TYPE("ecpp",C);

  /* Check if we should even prove it. */
  expiN = expi(N);
  if (stopat < 64) stopat = 64;
  if (expiN < stopat) return C;

  tunelen = (expiN+499)/500;
  tune = cgetg(tunelen+1, t_VEC);
  for (i = 1; i <= tunelen && ecpp_tune[i-1][3]; i++)
    gel(tune,i) = mkvecsmall4(ecpp_tune[i-1][0], ecpp_tune[i-1][1],
                              ecpp_tune[i-1][2], ecpp_tune[i-1][3]);
  for (; i <= tunelen; i++) gel(tune,i) = mkvecsmall4(100*(i+20),4*i+42,30,500*i);
  for(;;)
  {
    GEN C2, param, x = gel(tune, tunelen);
    param = ecpp_param_set(tune, x);
    C2 = ecpp_param(N, param, stopat);
    if (C2)
      return typ(C)==t_INT? C2: gc_GEN(av, shallowconcat(C,C2));
    x[1] *= 2;
    x[2] *= 2;
    x[3] = minss(x[3]+1, 30);
  }
}

GEN
ecpp(GEN N)
{ return ecpp0(N, 0); }

long
isprimeECPP(GEN N)
{
  pari_sp av = avma;
  if (!BPSW_psp(N)) return 0;
  return gc_long(av, !isintzero(ecpp(N)));
}

/* PARI ECPP Certificate -> Human-readable format */
static GEN
cert_out(GEN x)
{
  long i, l = lg(x);
  pari_str str;
  str_init(&str, 1);
  if (typ(x) == t_INT)
  {
    str_printf(&str, "%Ps is prime.\nIndeed, ispseudoprime(%Ps) = 1 and %Ps < 2^64.\n", x, x, x);
    return strtoGENstr(str.string);
  }
  for (i = 1; i < l; i++)
  {
    GEN xi = gel(x, i);
    str_printf(&str, "[%ld]\n", i);
    str_printf(&str, " N = %Ps\n", cert_get_N(xi));
    str_printf(&str, " t = %Ps\n", cert_get_t(xi));
    str_printf(&str, " s = %Ps\n", cert_get_s(xi));
    str_printf(&str, "a = %Ps\n", cert_get_a4(xi));
    str_printf(&str, "D = %Ps\n", cert_get_D(xi));
    str_printf(&str, "m = %Ps\n", cert_get_m(xi));
    str_printf(&str, "q = %Ps\n", cert_get_q(xi));
    str_printf(&str, "E = %Ps\n", cert_get_E(xi));
    str_printf(&str, "P = %Ps\n", cert_get_P(xi));
  }
  return strtoGENstr(str.string);
}

/* PARI ECPP Certificate -> Magma Certificate
 * [* [*
 *     N, |D|, -1, m,
 *     [* a, b *],
 *     [* x, y, 1 *],
 *     [* [* q, 1 *] *]
 *   *], ... *] */
static GEN
magma_out(GEN x)
{
  long i, n = lg(x)-1;
  pari_str ret;
  str_init(&ret, 1);
  if (typ(x) == t_INT)
  {
    str_printf(&ret, "Operation not supported.");
    return strtoGENstr(ret.string);
  }
  str_printf(&ret, "[* ");
  for (i = 1; i<=n; i++)
  {
    GEN xi = gel(x,i), E = cert_get_E(xi), P = cert_get_P(xi);
    str_printf(&ret, "[* %Ps, %Ps, -1, %Ps, ",
              cert_get_N(xi), negi(cert_get_D(xi)), cert_get_m(xi));
    str_printf(&ret, "[* %Ps, %Ps *], ", gel(E,1), gel(E,2));
    str_printf(&ret, "[* %Ps, %Ps, 1 *], ", gel(P,1), gel(P,2));
    str_printf(&ret, "[* [* %Ps, 1 *] *] *]", cert_get_q(xi));
    if (i != n) str_printf(&ret, ", ");
  }
  str_printf(&ret, " *]");
  return strtoGENstr(ret.string);
}

/* Prints: label=(sign)hexvalue\n
 *   where sign is + or -
 *   hexvalue is value in hex, of the form: 0xABC123 */
static void
primo_printval(pari_str *ret, const char* label, GEN value)
{
  str_printf(ret, label);
  if (signe(value) >= 0) str_printf(ret, "=0x%P0X\n", value);
  else str_printf(ret, "=-0x%P0X\n", negi(value));
}

/* Input: PARI ECPP Certificate / Output: PRIMO Certificate
 *
 * Let Y^2 = X^3 + aX + b be the elliptic curve over N with the point (x,y)
 * as described in the PARI certificate.
 *
 * If J != 0, 1728, PRIMO asks for [J,T], where T = a/A * B/b * x,
 * A = 3J(1728-J) and B = 2J(1728-J)^2.
 *
 * If J=0 or J=1728, PRIMO asks for [A,B,T]; we let A=a and B=b => T = x */
static GEN
primo_out(GEN x)
{
  long i, l = (typ(x) == t_INT) ? 1 : lg(x);
  pari_str ret;
  str_init(&ret, 1);
  str_printf(&ret, "[PRIMO - Primality Certificate]\nFormat=4\n");
  str_printf(&ret, "TestCount=%ld\n\n[Comments]\n", l-1);
  str_printf(&ret, "Generated by %s\n",paricfg_version);
  str_printf(&ret, "https://pari.math.u-bordeaux.fr/\n\n[Candidate]\n");
  if (typ(x) == t_INT)
  {
    str_printf(&ret, "N=0x%P0X\n", x);
    return strtoGENstr(ret.string);
  }
  str_printf(&ret, "N=0x%P0X\n\n", cert_get_N(gel(x,1)));
  for (i = 1; i < l; i++)
  {
    GEN a4, a6, N, Nover2, xi = gel(x,i);
    long Ais0, Bis0;
    str_printf(&ret, "[%ld]\n", i);
    N = cert_get_N(xi);
    Nover2 = shifti(N, -1);
    primo_printval(&ret, "S", cert_get_s(xi));
    primo_printval(&ret, "W", cert_get_t(xi));
    a4 = cert_get_a4(xi); Ais0 = isintzero(a4);
    a6 = cert_get_a6(xi); Bis0 = isintzero(a6);
    if (!Ais0 && !Bis0) { /* J != 0, 1728 */
      primo_printval(&ret, "J", Fp_center_i(cert_get_J(xi), N, Nover2));
      primo_printval(&ret, "T", cert_get_T(xi));
    } else {
      if (!Ais0) a4 = Fp_center_i(a4, N, Nover2);
      if (!Bis0) a6 = Fp_center_i(a6, N, Nover2);
      primo_printval(&ret, "A", a4);
      primo_printval(&ret, "B", a6);
      primo_printval(&ret, "T", cert_get_x(xi));
    }
    str_printf(&ret, "\n");
  }
  return strtoGENstr(ret.string);
}

/* return 1 if q > (N^1/4 + 1)^2, 0 otherwise */
static long
Nq_isvalid(GEN N, GEN q)
{
  GEN c = subii(sqri(subiu(q,1)), N);
  if (signe(c) <= 0) return 0;
  /* (q-1)^2 > N; check that (N - (q-1)^2)^2 > 16Nq */
  return (cmpii(sqri(c), shifti(mulii(N,q), 4)) > 0);
}

GEN
primecertisvalid_ecpp_worker(GEN certi)
{
  GEN N, W, mP, sP, r, m, s, a, P, q;
  if (lg(certi)-1 != 5) return gen_0;

  N = cert_get_N(certi);
  if (typ(N) != t_INT || signe(N) <= 0) return gen_0;
  switch(umodiu(N,6))
  {
    case 1: case 5: break; /* Check if N is not divisible by 2 or 3 */
    default: return gen_0;
  }

  W = cert_get_t(certi);
  if (typ(W) != t_INT) return gen_0;
  /* Check if W^2 < 4N (Hasse interval) */
  if (!(cmpii(sqri(W), shifti(N,2)) < 0)) return gen_0;

  s = cert_get_s(certi);
  if (typ(s) != t_INT || signe(s) < 0) return gen_0;

  m = cert_get_m(certi);
  q = dvmdii(m, s, &r);
  /* Check m%s == 0 */
  if (!isintzero(r)) return gen_0;
  /* Check q > (N^(1/4) + 1)^2 */
  if (!Nq_isvalid(N, q)) return gen_0;

  a = cert_get_a4(certi);
  if (typ(a) != t_INT) return gen_0;

  P = cert_get_P(certi);
  if (typ(P) != t_VEC || lg(P) != 3) return gen_0;
  P = FpE_to_FpJ(P);

  /* Check sP != 0 and third component is coprime to N */
  sP = FpJ_mul(P, s, a, N);
  if (!isint1(gcdii(gel(sP, 3), N))) return gen_0;

  /* Check mP == 0 */
  mP = FpJ_mul(sP, q, a, N);
  if (!FpJ_is_inf(mP)) return gen_0;

  return q;
}

/* return 1 if 'cert' is a valid PARI ECPP certificate */
static long
ecppisvalid_i(GEN cert)
{
  const long trustbits = 64;/* a pseudoprime < 2^trustbits is prime */
  long i, lgcert = lg(cert);
  GEN ql, q = gen_0, worker, check;

  if (typ(cert) == t_INT)
  {
    if (expi(cert) >= trustbits) return 0; /* >= 2^trustbits */
    return BPSW_psp(cert);
  }
  if (typ(cert) != t_VEC || lgcert <= 1) return 0;
  ql = veclast(cert); if (lg(ql)-1 != 5) return 0;
  ql = cert_get_q(ql);
  if (expi(ql) >= trustbits || !BPSW_psp(ql)) return 0;
  worker = strtofunction("_primecertisvalid_ecpp_worker");
  check = gen_parapply(worker, cert);
  for (i = 1; i < lgcert; i++)
  {
    GEN certi = gel(cert, i);
    GEN qq = gel(check,i), N = cert_get_N(certi);
    if (isintzero(qq)) return 0;
    if (i > 1 && !equalii(N, q)) return 0; /* N of this entry doesn't match q of previous */
    q = qq;
  }
  return 1;
}
long
ecppisvalid(GEN cert)
{ pari_sp av = avma; return gc_long(av, ecppisvalid_i(cert)); }

GEN
ecppexport(GEN cert, long flag)
{
  switch(flag)
  {
    case 0: return cert_out(cert);
    case 1: return primo_out(cert);
    case 2: return magma_out(cert);
  }
  pari_err_FLAG("primecertexport");
  return NULL;/*LCOV_EXCL_LINE*/
}
