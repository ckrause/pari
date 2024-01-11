/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/*****************************************************************/
/*             Program to compute L(chi,s)                       */
/*      for Im(s) large, chi primitive Dirichlet character       */
/*      In the present branch, only Tyagi's method is used      */
/*****************************************************************/
/*
   In addition, C can also be a polynomial defining an abelian
   extension of Q.
*/

/*******************************************************************/
/*                     parallel dirpowerssumfun                    */
/*******************************************************************/
/*   Should be in dirichlet.c, but since incompatible with existing
     one, for now in lfunlarge.c */
/* Assume f is a totally multiplicative function of modulus 0 or 1
   (essentially a Dirichlet character). Compute simultaneously
   \sum_{1\le n\le N} f(n)n^s and \sum_{1\le n\le N} f(n)n^{-1-conj(s)}.
   Warning: s is conjugated, but not f. Main application for RS, where
   we need R(chi,s) and conj(R(chi,1-conj(s))). */

static GEN
Qtor(GEN x, long prec)
{ return typ(x) == t_FRAC? fractor(x, prec): x; }

static GEN
mycallvec(GEN f, long n, long prec)
{
  long N;
  if (typ(f) == t_CLOSURE) return closure_callgen1prec(f, stoi(n), prec);
  N = lg(f) - 1; return gel(f, (n - 1) % N + 1);
}

static GEN
smalldirpowerssum(ulong N, GEN s, long fl, long prec)
{
  GEN vg = vecpowug(N, s, prec), S1 = Qtor(RgV_sum(vg), prec);
  long n;
  if (!fl) return mkvec2(S1, S1);
  for (n = 1; n <= N; n++) gel(vg, n) = ginv(gmulsg(n, gconj(gel(vg, n))));
  return mkvec2(S1, Qtor(RgV_sum(vg), prec));
}

static GEN
gmulvecsqlv(GEN Q, GEN V)
{
  long lq, i;
  GEN W;
  if (typ(V) != t_VEC) return RgV_Rg_mul(Q, V);
  lq = lg(Q); W = cgetg(lq, t_VEC);
  for (i = 1; i < lq; i++) gel(W, i) = vecmul(gel(Q, i), V);
  return W;
}

/* P = prime divisors of (squarefree) n, V[i] = i^s for i <= sq.
 * Return NULL if n is not sq-smooth, else f(n)n^s */
static GEN
smallfactvec(ulong n, GEN P, ulong sq, GEN V)
{
  long i, l;
  ulong p, m, o;
  GEN c;
  if (n <= sq) return gel(V,n);
  l = lg(P); m = p = uel(P, l-1); if (p > sq) return NULL;
  for (i = l-2; i > 1; i--, m = o) { p = uel(P,i); o = m*p; if (o > sq) break; }
  c = gel(V,m); n /= m; /* m <= sq, o = m * p > sq */
  if (n > sq) { c = vecmul(c, gel(V,p)); n /= p; }
  return vecmul(c, gel(V,n));
}

GEN
parsqfboth_worker(GEN gk, GEN vZ, GEN vVQ, GEN vV, GEN P, GEN Nsqstep)
{
  pari_sp av2 = avma;
  GEN Z1 = gel(vZ, 1), Z2 = gel(vZ, 2), V1 = gel(vV, 1), V2 = gel(vV, 2);
  GEN VQ1 = gel(vVQ, 1), VQN, v, S1, S2;
  GEN Q1 = gel(VQ1, 1), Q2 = gel(VQ1, 2), Q3 = gel(VQ1, 3), Q6 = gel(VQ1, 4);
  GEN QN = gen_0, Q2N = gen_0, Q3N = gen_0, Q6N = gen_0;
  long k = itos(gk), N = Nsqstep[1], sq = Nsqstep[2], step = Nsqstep[3];
  long x1 = 1 + step * k, x2, j, lv, fl = !gcmp0(V2), lvv = 0;
  ulong a, b, c, e, q;
  if (typ(gel(V1, 1)) == t_VEC)
  { lvv = lg(gel(V1, 1)) - 1; S1 = zerovec(lvv); S2 = zerovec(lvv); }
  else { S1 = gen_0; S2 = gen_0; }
  if (fl)
  { VQN = gel(vVQ, 2); QN = gel(VQN, 1); Q2N = gel(VQN, 2);
    Q3N = gel(VQN, 3); Q6N = gel(VQN, 4); }
  /* beware overflow, fuse last two bins (avoid a tiny remainder) */
  x2 = (N >= 2*step && N - 2*step >= x1)? x1 - 1 + step: N;
  v = vecfactorsquarefreeu_coprime(x1, x2, P);
  lv = lg(v);
  for (j = 1; j < lv; j++)
    if (gel(v,j))
    {
      ulong d = x1 - 1 + j; /* squarefree, coprime to 6 */
      GEN t1 = smallfactvec(d, gel(v,j), sq, V1), t2 = gen_0, u1, u2 = gen_0;
      /* = f(d) d^s */
      if (!t1 || gequal0(t1)) continue;
      if (fl) t2 = vecinv(gmulsg(d, gconj(t1)));
      /* warning: gives 1/conj(f(d)) d^(-1-conj(s)), equal to
         f(d) d^(-1-conj(s)) only if |f(d)|=1. */
      /* S += f(d) d^s * Z[q] */
      q = N / d;
      if (q == 1)
      {
        S1 = gadd(S1, t1); if (fl) S2 = gadd(S2, t2);
        continue;
      }
      if (q <= sq) { u1 = gel(Z1, q); if (fl) u2 = gel(Z2, q); }
      else
      {
        a = usqrt(q); b = usqrt(q / 2); c = usqrt(q / 3); e = usqrt(q / 6);
        u1 = gadd(gadd(gel(Q1,a), gel(Q2,b)), gadd(gel(Q3,c), gel(Q6,e)));
        if (fl)
          u2 = gadd(gadd(gel(QN,a), gel(Q2N,b)), gadd(gel(Q3N,c), gel(Q6N,e)));
      }
      S1 = gadd(S1, vecmul(t1, u1)); if (fl) S2 = gadd(S2, vecmul(t2, u2));
    }
  return gerepilecopy(av2, mkvec2(S1, S2));
}

/* does n^s require log(x) ? */
static long
get_needlog(GEN s)
{
  switch(typ(s))
  {
    case t_REAL: return 2; /* yes but no powcx */
    case t_COMPLEX: return 1; /* yes using powcx */
    default: return 0; /* no */
  }
}

GEN
parsumprimeWfunboth_worker(GEN gk, GEN s, GEN W1, GEN W2, GEN f, GEN Nsqprec)
{
  pari_sp av2;
  GEN S1, S2 = gen_0, logp;
  forprime_t T;
  long k = itou(gk), N = Nsqprec[1], sq = Nsqprec[2], precp;
  long STEP = Nsqprec[3], prec0 = Nsqprec[4], prec1 = Nsqprec[5], p;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  long needlog = get_needlog(s), fl = !gequal0(W2), lv;

  if (f && gequal0(f)) f = NULL;
  if (!f) lv = 0;
  else
  {
    GEN tmp = mycallvec(f, 1, prec1);
    lv = typ(tmp) == t_VEC ? lg(tmp) - 1 : 0;
  }
  precp = 0; logp = NULL;
  if (lv) { S1 = const_vec(lv, real_0(prec1)); if (fl) S2 = const_vec(lv, real_0(prec1)); }
  else { S1 = real_0(prec1); if (fl) S2 = real_0(prec1); }
  u_forprime_init(&T, k * STEP + sq + 1, minss(N, (k + 1) * STEP + sq));
  av2 = avma;
  while ((p = u_forprime_next(&T)))
  {
    GEN u = gen_0, ks = f ? mycallvec(f, p, prec1) : gen_1;
    long zks = !gequal0(ks);
    gp[2] = p;
    if (needlog)
    {
      if (!logp)
        logp = logr_abs(utor(p, prec1));
      else
      { /* log p = log(precp) + 2 atanh((p - precp) / (p + precp)) */
        ulong a = p >> 1, b = precp >> 1; /* p = 2a + 1, precp = 2b + 1 */
        GEN z = atanhuu(a - b, a + b + 1, prec1); /* avoid overflow */
        shiftr_inplace(z, 1); logp = addrr(logp, z);
      }
      if (zks)
        u = needlog == 1? powcx(gp, logp, s, prec0) : mpexp(gmul(s, logp));
    }
    else { if (zks) u = gpow(gp, s, prec0); }
    if (zks)
    {
      S1 = gadd(S1, vecmul(gel(W1, N / p), gmul(ks, u)));
      if (fl)
        S2 = gadd(S2, gdiv(vecmul(ks, gel(W2, N / p)), gmulsg(p, gconj(u))));
    }
    precp = p;
    if ((p & 0x1ff) == 1)
    {
      if (!logp) gerepileall(av2, 2, &S1, &S2);
      else gerepileall(av2, 3, &S1, &S2, &logp);
    }
  }
  return gcopy(mkvec2(S1, S2));
}

static GEN
smalldirpowerssumfunvec_i(GEN f, ulong N, GEN s, long prec)
{
  long n;
  GEN S = real_0(prec);
  if (f && gequal0(f)) f = NULL;
  if (f)
  {
    GEN tmp = mycallvec(f, 1, prec);
    if (typ(tmp) == t_VEC) S = const_vec(lg(tmp) - 1, real_0(prec));
  }
  for (n = 1; n <= N; n++)
  {
    GEN ks = mycallvec(f, n, prec);
    if (!gequal0(ks)) S = gadd(S, gmul(ks, gpow(utoipos(n), s, prec)));
  }
  return S;
}

static GEN
smalldirpowerssumfunvec(GEN f, ulong N, GEN s, long fl, long prec)
{
  GEN tmp = smalldirpowerssumfunvec_i(f, N, s, prec);
  if (fl) return mkvec2(tmp, smalldirpowerssumfunvec_i(f, N, gsubgs(gneg(gconj(s)), 1), prec));
  else return mkvec2(tmp, tmp);
}

static GEN
getscal(GEN V, long isscal)
{
  long lv;
  if (isscal != 1 || typ(V) != t_VEC) return V;
  lv = lg(V);
  switch (lv)
  {
    case 2: return gel(V, 1);
    case 3: return mkvec2(getscal(gel(V, 1), 1), getscal(gel(V, 2), 1));
    default: pari_err_TYPE("getscal", V);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

GEN
pardirpowerssumfun(GEN f, ulong N, GEN s, long both, long prec)
{
  const ulong step = 2048;
  pari_sp av = avma;
  GEN P, V1, W1, Q1, V2 = gen_0, W2 = gen_0, QN = gen_0, c2, c2N;
  GEN Q2, Q2N = gen_0, Q3, Q3N = gen_0, Q6, Q6N = gen_0;
  GEN S1, S2, RES, Z1, Z2 = gen_0, logp;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  ulong a, b, c, e, q, n, sq, fl;
  long prec0, prec1, needlog, lv = 0, isscal = 1;
  GEN unvec = gen_1, zervec = gen_0, re0, re1, tmp2 = NULL;

  if (f)
  {
    if (typ(f) == t_CLOSURE) isscal = -1; else isscal = 0;
    tmp2 = mycallvec(f, 2, prec + EXTRAPRECWORD);
    if (typ(tmp2) == t_VEC)
    {
      lv = lg(tmp2) - 1;
      unvec = const_vec(lv, gen_1);
      zervec = const_vec(lv, gen_0);
    }
  }
  if (N <= 0)
  { GEN v = mkvec2(gen_0, gen_0); return f ? const_vec(lv, v) : v; }
  fl = both && gcmp(real_i(s), gneg(ghalf));
  if (f && N < 49)
    return gerepilecopy(av, getscal(smalldirpowerssumfunvec(f, N, s, fl, prec), isscal));
  if (!f && N < 10000UL)
    return gerepilecopy(av, smalldirpowerssum(N, s, fl, prec));
  sq = usqrt(N);
  V1 = cgetg(sq+1, t_VEC); W1 = cgetg(sq+1, t_VEC); Q1 = cgetg(sq+1, t_VEC);
  if (fl)
  {
    V2 = cgetg(sq+1, t_VEC); W2 = cgetg(sq+1, t_VEC); QN = cgetg(sq+1, t_VEC);
  }
  prec1 = prec0 = prec + EXTRAPRECWORD;
  s = gprec_w(s, prec0);
  needlog = get_needlog(s);
  if (needlog == 1) prec1 = powcx_prec(log2((double)N), s, prec);
  gel(V1,1) = gel(W1,1) = gel(Q1,1) = unvec;
  if (fl) { gel(V2,1) = gel(W2,1) = gel(QN,1) = unvec; }
  c2 = gpow(gen_2, s, prec0); c2N = ginv(gmul2n(gconj(c2), 1));
  re0 = real_0(prec0); re1 = real_1(prec0);
  if (f) { c2 = gmul(c2, tmp2); c2N = gmul(c2N, tmp2); }
  gel(V1,2) = c2; /* f(2) 2^s */
  gel(W1,2) = gmul(re1, gadd(c2, unvec));
  gel(Q1,2) = gmul(re1, gadd(vecsqr(c2), unvec));
  if (fl)
  {
    gel(V2,2) = c2N; gel(W2,2) = gmul(re1, gadd(c2N, unvec));
    gel(QN,2) = gmul(re1, gadd(vecsqr(c2N), unvec));
  }
  logp = NULL;
  for (n = 3; n <= sq; n++)
  {
    GEN u1 = zervec, u2 = zervec, ks = f ? mycallvec(f, n, prec) : gen_1;
    long zks = !gequal0(ks);
    if (odd(n))
    {
      gp[2] = n;
      if (needlog)
      {
        if (!logp)
          logp = logr_abs(utor(n, prec1));
        else
        { /* log n = log(n-2) + 2 atanh(1 / (n - 1)) */
          GEN z = atanhuu(1, n - 1, prec1);
          shiftr_inplace(z, 1); logp = addrr(logp, z);
        }
        if (zks)
          u1 = needlog == 1? powcx(gp, logp, s, prec0) : mpexp(gmul(s, logp));
      }
      else { if (zks) u1 = gpow(gp, s, prec0); }
      if (zks)
      {
        if(fl) u2 = gmul(ks, ginv(gmulsg(n, gconj(u1))));
        u1 = gmul(ks, u1); /* f(n) n^s */
      }
    }
    else
    {
      u1 = vecmul(c2, gel(V1, n >> 1));
      if (fl) u2 = vecmul(c2N, gel(V2, n >> 1));
    }
    gel(V1,n) = u1; /* f(n) n^s */
    gel(W1,n) = gadd(gel(W1,n-1), gel(V1,n));       /* = sum_{i<=n} f(i)i^s */
    gel(Q1,n) = gadd(gel(Q1,n-1), vecsqr(gel(V1,n))); /* = sum_{i<=n} f(i^2)i^2s */
    if (fl)
    {
      gel(V2,n) = u2;
      gel(W2,n) = gadd(gel(W2,n-1), gel(V2,n));
      gel(QN,n) = gadd(gel(QN,n-1), vecsqr(gel(V2,n)));
    }
  }
  Q2 = gmulvecsqlv(Q1, gel(V1,2));
  Q3 = gmulvecsqlv(Q1, gel(V1,3));
  Q6 = gmulvecsqlv(Q1, gel(V1,6));
  if (fl)
  {
    Q2N = gmulvecsqlv(QN, gel(V2,2));
    Q3N = gmulvecsqlv(QN, gel(V2,3));
    Q6N = gmulvecsqlv(QN, gel(V2,6));
  }
  if (typ(zervec) == t_VEC)
  { S1 = const_vec(lv, re0); S2 = const_vec(lv, re0); }
  else { S1 = re0; S2 = re0; }
  RES = mkvec2(S1, S2);
  {
    GEN fspec = f ? f : gen_0;
    long m = mt_nbthreads();
    long STEP = maxss(N / (m * m), 1);
    GEN VS = mkvecsmalln(5, N, sq, STEP, prec0, prec1);
    GEN FUN = strtoclosure("_parsumprimeWfunboth_worker", 5, s, W1, W2, fspec, VS);
    RES = gadd(RES, parsum(gen_0, utoipos((N - 1) / STEP), FUN));
  }
  P = mkvecsmall2(2, 3);
  Z1 = cgetg(sq+1, t_VEC);
  /* a,b,c,e = sqrt(q), sqrt(q/2), sqrt(q/3), sqrt(q/6)
   * Z[q] = Q[a] + 2^s Q[b] + 3^s Q[c] + 6^s Q[e], with Q[0] = 0 */
  gel(Z1, 1) = unvec;
  gel(Z1, 2) = gel(W1, 2);
  gel(Z1, 3) = gel(W1, 3);
  gel(Z1, 4) = gel(Z1, 5) = gel(W1, 4);
  gel(Z1, 6) = gel(Z1, 7) = gadd(gel(W1, 4), gel(V1, 6));
  if (fl)
  {
    Z2 = cgetg(sq+1, t_VEC);
    gel(Z2, 1) = unvec;
    gel(Z2, 2) = gel(W2, 2);
    gel(Z2, 3) = gel(W2, 3);
    gel(Z2, 4) = gel(Z2, 5) = gel(W2, 4);
    gel(Z2, 6) = gel(Z2, 7) = gadd(gel(W2, 4), gel(V2, 6));
  }
  a = 2; b = c = e = 1;
  for (q = 8; q <= sq; q++)
  { /* Gray code: at most one of a,b,c,d differs (by 1) from previous value */
    GEN z1 = gel(Z1, q - 1), z2 = gen_0;
    ulong na, nb, nc, ne, na2, nb2, nc2, ne2;
    if (fl) z2 = gel(Z2, q - 1);
    if ((na = usqrt(q)) != a)
    { a = na; na2 = na * na; z1 = gadd(z1, gel(V1, na2)); if (fl) z2 = gadd(z2, gel(V2, na2)); }
    else if ((nb = usqrt(q / 2)) != b)
    { b = nb; nb2 = 2 * nb * nb; z1 = gadd(z1, gel(V1, nb2)); if (fl) z2 = gadd(z2, gel(V2, nb2)); }
    else if ((nc = usqrt(q / 3)) != c)
    { c = nc; nc2 = 3 * nc * nc; z1 = gadd(z1, gel(V1, nc2)); if (fl) z2 = gadd(z2, gel(V2, nc2)); }
    else if ((ne = usqrt(q / 6)) != e)
    { e = ne; ne2 = 6 * ne * ne; z1 = gadd(z1, gel(V1, ne2)); if (fl) z2 = gadd(z2, gel(V2, ne2)); }
    gel(Z1,q) = z1; if (fl) gel(Z2,q) = z2;
  }
  {
    GEN vQ1 = mkvec4(Q1, Q2, Q3, Q6), vQ2 = gen_0, FUN;
    if (fl) vQ2 = mkvec4(QN, Q2N, Q3N, Q6N);
    FUN = strtoclosure("_parsqfboth_worker", 5, mkvec2(Z1, Z2), mkvec2(vQ1, vQ2), mkvec2(V1, V2), P, mkvecsmall3(N, sq, step));
    RES = gadd(RES, parsum(gen_0, utoipos(maxss(0, (N - 1) / step - 1)), FUN));
  }
  if (!fl) gel(RES, 2) = gel(RES, 1);
  return gerepilecopy(av, getscal(RES, isscal));
}

GEN
pardirpowerssum0(GEN N, GEN s, GEN f, long both, long prec)
{
  pari_sp av = avma;
  GEN R;
  if (typ(N) != t_INT) pari_err_TYPE("pardirpowerssum", N);
  R = pardirpowerssumfun(f, itou(N), s, both, prec);
  return both ? R : gerepilecopy(av, gel(R, 1));
}

GEN
pardirpowerssum(ulong N, GEN s, long prec)
{
  pari_sp av = avma;
  return gerepilecopy(av, gel(pardirpowerssumfun(NULL, N, s, 0, prec), 1));
}

/*****************************************************************/
/*                      Character programs                       */
/*****************************************************************/
/* A character, always assumed primitive can be given in the following formats:
   -- omitted or 0: special to zetaRS,
   -- a t_INT: assumed to be a discriminant,
   -- a t_INTMOD: a conrey character,
   -- a pair [G,chi] or [bnr,chi],
   -- [C1,C2,...]~ where the Ci are characters as above having
   the same moduli. */

/* Given a list of ldata for chars of same conductor F, return
 * [Vecan, F, Parities, Gaussums], with Vecan transposed so
 * as to be callable directly. */
static GEN
mycharinit(GEN C, long prec)
{
  GEN L, LVC, LE, LGA;
  long F = 0, i, j, lc = lg(C);

  L = cgetg(lc, t_VEC);
  LE = cgetg(lc, t_VECSMALL);
  LGA = cgetg(lc, t_VEC);
  for (i = 1; i < lc; i++)
  {
    GEN gv, ga, gm, ro, ldata = gel(C, i);
    long e;
    gv = ldata_get_gammavec(ldata); e = itou(gel(gv, 1));
    gm = ldata_get_conductor(ldata);
    ro = ldata_get_rootno(ldata);
    if (isintzero(ro)) ro = lfunrootno(ldata, prec2nbits(prec));
    ga = gmul(ro, gsqrt(gm, prec)); if (e) ga = mulcxI(ga);
    gel(LGA, i) = ga;
    LE[i] = e;
    if (i == 1) F = itos(gm); /* constant */
    gel(L, i) = lfunan(ldata, F, prec);
  }
  if (lc == 2 && is_vec_t(typ(gmael(L,1,1))))
  { /* multichar */
    LGA = gel(LGA,1); lc = lg(LGA);
    LVC = gel(L,1);
    LE = const_vecsmall(lc-1, LE[1]); /* FIXME: can handle mixed values */
  }
  else
  {
    LVC = cgetg(F + 1, t_VEC);
    for (j = 1; j <= F; j++)
    {
      GEN v = cgetg(lc, t_VEC);
      for (i = 1; i < lc; i++) gel(v, i) = gmael(L, i, j);
      gel(LVC, j) = v;
    }
  }
  return mkvec4(LVC, stoi(F), LE, LGA);
}

/* n >= 1 and #VC = F, the conductor of the character or multicharacter X.
 * VC contains [X(1),X(2),...X(F)] */
static GEN
mycall(GEN VC, long n)
{
  long F = lg(VC) - 1;
  GEN z = n <= F ? gel(VC, n) : gel(VC, ((n - 1) % F) + 1);
  return gequal0(z)? NULL: z;
}

static GEN get_chivec(GEN VCALL) { return gel(VCALL, 1); }
static long get_modulus(GEN VCALL) { return itos(gel(VCALL, 2)); }
static GEN get_signat(GEN VCALL) { return gel(VCALL, 3); }
static GEN get_gauss(GEN VCALL) { return gel(VCALL, 4); }

/* (-1)^A[i] * conj(B[i]) */
static GEN
gnegconj(GEN A, GEN B)
{
  long i, l = lg(A);
  GEN W = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  { GEN b = gconj(gel(B,i)); gel(W,i) = A[i]? gneg(b): b; }
  return W;
}
/* g(conj(CHI)) */
static GEN
gaussconj(GEN VCALL)
{ return gnegconj(get_signat(VCALL), get_gauss(VCALL)); }

static GEN
myinitconj(GEN VCALL)
{
  GEN CONJ = shallowcopy(VCALL);
  gel(CONJ, 1) = gconj(get_chivec(VCALL));
  gel(CONJ, 4) = gaussconj(VCALL); return CONJ;
}

/********************************************************************/
/*                          Driver Program                          */
/********************************************************************/

/* assume |Im(s)| >> 1, in particular s is not a negative integer */
static GEN
applyfuneq(GEN gau, GEN s, GEN z, long odd, long q, long bitprec)
{
  GEN t, S;
  long prec;
  if (!gequal0(s)) bitprec += maxss(gexpo(s), 0);
  prec = nbits2prec(bitprec);
  if (odd) gau = mulcxmI(gau);
  S = gmul(Pi2n(-1, prec), gsubgs(s, odd));
  t = ginv(gmul2n(gmul(gcos(S, prec), ggamma(s, prec)), 1));
  t = gmul(gpow(gdivgs(Pi2n(1, prec), q), s, prec), t);
  return gmul(gmul(gau, t), z);
}

static GEN RZchi(GEN VCALL, GEN s, long prec);

/* VCALL already initialized */
static GEN
lfunlarge_char(GEN VCALL, GEN s, long bitprec)
{
  pari_sp av = avma;
  GEN sig, tau, z;
  long funeq = 0, ts = typ(s), stau, flconj, q;
  if (!is_real_t(ts) && ts != t_COMPLEX) pari_err_TYPE("lfunlarge_char", s);
  sig = real_i(s); tau = imag_i(s);
  if (gexpo(tau) < 1) pari_err_DOMAIN("lfun","im(s)", "<", gen_2, tau);
  stau = gsigne(tau);
  if (stau < 0) { tau = gneg(tau); VCALL = myinitconj(VCALL); }
  if (gcmp(sig, ghalf) < 0) { funeq = 1; sig = gsubsg(1, sig); }
  flconj = ((stau > 0 && funeq) || (stau < 0 && !funeq));
  q = get_modulus(VCALL); bitprec += gexpo(stoi(q));
  z = RZchi(VCALL, mkcomplex(sig, tau), nbits2prec(bitprec));
  if (flconj) z = gconj(z);
  if (funeq)
  {
    GEN odd = get_signat(VCALL), gau = get_gauss(VCALL), Vz;
    long lC = lg(gau), j;
    Vz = cgetg(lC, t_VEC);
    for (j = 1; j < lC; j++)
      gel(Vz,j) = applyfuneq(gel(gau,j), s, gel(z,j), odd[j], q, bitprec);
    z = Vz;
  }
  return gerepilecopy(av, z);
}

static GEN
lfungetchars(GEN pol)
{
  GEN L, F, v, bnf = Buchall(pol_x(1), 0, LOWDEFAULTPREC);
  GEN w, condall, bnr;
  long i, l, lc;
  condall = rnfconductor(bnf, pol); bnr = gel(condall, 2);
  L = bnrchar(bnr, gel(condall, 3), NULL); lc = lg(L);
  F = cgetg(lc, t_VEC);
  for (i = 1; i < lc; i++)
  {
    GEN chi = gel(L, i), cond = bnrconductor_raw(bnr, chi);
    gel(F, i) = gcoeff(gel(cond,1), 1, 1);
  }
  w = vec_equiv(F); l = lg(w); v = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN wi = gel(w, i), vi;
    long j, li = lg(wi);
    gel(v,i) = vi = cgetg(li, t_VEC);
    if (li == 2 && equali1(gel(F, wi[1]))) /* common conductor is 1 */
      gel(vi,1) = lfunmisc_to_ldata_shallow(gen_1);
    else
    {
      for (j = 1; j < li; j++)
        gel(vi,j) = lfunmisc_to_ldata_shallow(mkvec2(bnr, gel(L, wi[j])));
    }
  }
  return v;
}

/********************************************************************/
/*            NEW RS IMPLEMENTATION FROM SANDEEP TYAGI              */
/********************************************************************/
/* See arXiv:2203.02509v2 */

static long m_n0(GEN sel) { return itos(gel(sel, 1)); }
static GEN m_r0(GEN sel) { return gel(sel, 2); }
static GEN m_al(GEN sel) { return gel(sel, 3); }
static GEN m_aleps(GEN sel) { return gel(sel, 4); }
static GEN m_h(GEN sel) { return gel(sel, 5); }
static GEN m_lin(GEN sel) { return gel(sel, 6); }
static GEN m_np(GEN sel) { return gel(sel, 7); }
static GEN m_pz(GEN sel) { return gel(sel, 8); }

static GEN
phi_hat(GEN x, long prec)
{
  GEN y;
  if (signe(imag_i(x)) > 0)
    y = gsubsg(1, gexp(gneg(gmul(PiI2(prec), x)), prec));
  else
    y = gsubgs(gexp(gmul(PiI2(prec), x), prec), 1);
  return ginv(y);
}

static GEN
phi_hat_h0(GEN sel, long k, long prec)
{
  GEN t = gdiv(gsubsg(m_n0(sel) + k, m_r0(sel)), m_aleps(sel));
  return phi_hat(gdiv(gasinh(t, prec), m_h(sel)), prec);
}

/* v[i] = A[i] * (a + (-1)^E[i] b) */
static GEN
mul_addsub(GEN A, GEN a, GEN b, GEN E)
{
  long i, l = lg(E);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
    gel(v,i) = gmul(gel(A,i), E[i]? gsub(a, b): gadd(a, b));
  return v;
}

static GEN
wd(GEN VCALL, GEN pmd, GEN x, GEN PZ, long prec)
{
  GEN VC = get_chivec(VCALL), E = get_signat(VCALL), y = NULL;
  long md = get_modulus(VCALL), k;
  for (k = 1; k <= (md-1) / 2; k++)
  {
    GEN xc = mycall(VC, k);
    if (xc)
    {
      GEN p1 = gmul(xc, gel(PZ, Fl_sqr(k, 2 * md) + 1));
      GEN p2 = gmul(pmd, gsubgs(x, k)), p3 = gmul(pmd, gaddgs(x, k));
      p2 = odd(md)? ginv(gsin(p2, prec)): gcotan(p2, prec);
      p3 = odd(md)? ginv(gsin(p3, prec)): gcotan(p3, prec);
      p1 = mul_addsub(p1, p2, p3, E);
      y = y ? gadd(y, p1) : p1;
    }
  }
  return mulcxmI(gdivgs(y, 2*md));
}

static GEN
series_h0(long n0, GEN s, GEN VCALL, long fl, long prec)
{
  GEN C = get_modulus(VCALL) == 1? NULL: get_chivec(VCALL);
  GEN R = pardirpowerssumfun(C, n0, gneg(s), fl, prec);
  if (fl)
  {
    if (C) return R;
    return mkvec2(mkvec(gel(R,1)), mkvec(gel(R,2)));
  }
  return C? gel(R,1): mkvec(gel(R,1));
}

static GEN
series_residues_h0(GEN sel, GEN s, GEN VCALL, long prec)
{
  long n0 = m_n0(sel), num_of_poles = itos(m_np(sel)), k;
  GEN val = gen_0, VC = get_chivec(VCALL);
  for (k = maxss(1 - num_of_poles, 1 - n0); k <= 1 + num_of_poles; k++)
  {
    GEN nk = mycall(VC, n0 + k); /* n0 + k > 0 */
    if (nk) val = gadd(val, gmul(gmul(phi_hat_h0(sel, k, prec), nk),
                                 gpow(stoi(n0 + k), gneg(s), prec)));
  }
  return val;
}

static GEN
integrand_h0(GEN sel, GEN s, GEN VCALL, GEN x, long prec)
{
  long md = get_modulus(VCALL);
  GEN r0 = m_r0(sel), aleps = m_aleps(sel), zn, p1;
  GEN pmd = divru(mppi(prec), md), ix = ginv(x);
  zn = gadd(r0, gdivgs(gmul(aleps, gsub(x, ix)), 2));
  p1 = gmul(expIxy(pmd, gsqr(zn), prec),
            gmul(gpow(zn, gneg(s), prec), gmul(aleps, gadd(x, ix))));
  if (md == 1)
    p1 = gdiv(mkvec(mulcxI(p1)), gmul2n(gsin(gmul(pmd, zn), prec), 2));
  else
    p1 = gdivgs(gmul(p1, wd(VCALL, pmd, zn, m_pz(sel), prec)), -2);
  return p1;
}

static GEN
integral_h0(GEN sel, GEN s, GEN VCALL, long prec)
{
  GEN lin_grid = m_lin(sel), S = gen_0;
  pari_sp av = avma;
  long j, l = lg(lin_grid);
  for (j = 1; j < l; j++)
  {
    S = gadd(S, integrand_h0(sel, s, VCALL, gel(lin_grid, j), prec));
    if ((j & 0xff) == 0) S = gerepileupto(av, S);
  }
  return gerepileupto(av, gmul(m_h(sel), S));
}

/* log |x| */
static GEN
mylog(GEN x, long prec)
{
  if (gequal0(x)) return gneg(powis(stoi(10), 20)); /* FIXME ! */
  switch(typ(x))
  {
    case t_COMPLEX: return gmul2n(glog(cxnorm(x), prec), -1);
    case t_REAL: break;
    default: x = gtofp(x, prec);
  }
  return logr_abs(x);
}

struct fun_q_t { GEN sel, s, VCALL, B; };
static GEN
fun_q(void *E, GEN x)
{
  struct fun_q_t *S = (struct fun_q_t *)E;
  long prec = DEFAULTPREC;
  GEN z = integrand_h0(S->sel, S->s, S->VCALL, gexp(x, prec), prec);
  if (typ(z) == t_VEC) z = vecsum(z);
  return addrr(S->B, mylog(z, prec));
}
static GEN
brent_q(void *E, GEN (*f)(void*,GEN), GEN q_low, GEN q_hi)
{
  GEN low_val = f(E, q_low), high_val = f(E, q_hi);
  if (gsigne(low_val) * gsigne(high_val) >= 0) return NULL;
  return zbrent(E, f, q_low, q_hi, LOWDEFAULTPREC);
}
static GEN
findq(void *E, GEN (*f)(void*,GEN), GEN lq, long B)
{
  GEN q_low, q_hi, q_right, q_left, q_est = gasinh(lq, LOWDEFAULTPREC);
  q_low = gdivgs(gmulsg(4, q_est), 5);
  q_hi = gdivgs(gmulsg(3, q_est), 2);
  q_right = brent_q(E, f, q_low, q_hi); if (!q_right) q_right = q_est;
  q_left = brent_q(E, f, gneg(q_low), gneg(q_hi)); if (!q_left) q_left = q_est;
  return bitprecision0(gmax(q_right, q_left), B);
}

static GEN
set_q_value(GEN sel, GEN s, GEN VCALL, long prec)
{
  struct fun_q_t E;
  GEN al = m_al(sel), lq;
  long md = get_modulus(VCALL), LD = DEFAULTPREC;
  E.sel = sel; E.s = s; E.VCALL = VCALL, E.B = mulur(prec, mplog2(LD));
  lq = gdiv(gsqrt(gdiv(gmulsg(md, E.B), Pi2n(1, LD)), LD), al);
  return findq((void*)&E, &fun_q, lq, prec);
}

static GEN
setlin_grid_exp(GEN h, long m, long prec)
{
  GEN w, vex = gpowers(gexp(h, prec), (m - 1)/2);
  long i;
  w = cgetg(m+1, t_VEC); gel(w, (m + 1)/2) = gen_1;
  for (i = (m + 3)/2; i <= m; i++)
  {
    GEN t1 = gel(vex, i - ((m - 1)/2));
    gel(w, i) = t1; gel(w, (m + 1) - i) = ginv(t1);
  }
  return w;
}

static long
get_m(GEN q, long prec)
{
  GEN t = divrr(mulur(4 * prec2nbits(prec), mplog2(prec)), sqrr(mppi(prec)));
  return 2*itos(gfloor(mulrr(q, t))) + 1;
}

static GEN
RZinit(GEN s, GEN VCALL, GEN num_of_poles, long prec)
{
  GEN sel, al, aleps, n0, r0, q, h, PZ;
  long md = get_modulus(VCALL), m;
  al = gcmpgs(gabs(imag_i(s), prec), 100) < 0 ? ginv(stoi(4)) : gen_1;
  r0 = gsqrt(gdiv(gmulgs(s, md), PiI2(prec)), prec);
  n0 = gfloor(gsub(real_i(r0), imag_i(r0)));
  aleps = gmul(al, gexp(PiI2n(-2, prec), prec));
  PZ = gpowers(gexp(gdivgs(PiI2n(0, prec), -md), prec), 2*md);
  sel = mkvecn(8, n0, r0, al, aleps, NULL, NULL, NULL, PZ);
  q = set_q_value(sel, s, VCALL, prec);
  m = get_m(q, prec);
  gel(sel,5) = h = divru(q, (m - 1) >> 1);
  gel(sel,6) = setlin_grid_exp(h, m, prec);
  gel(sel,7) = num_of_poles;
  return sel;
}

/* fl = 0: compute only for s; fl = 1 compute for s and 1-conj(s)
   and put second result in *ptaux; fl = -1 take *ptaux as serh0. */
static GEN
total_value(GEN sel, GEN s, GEN VCALL, GEN *ptaux, long fl, long prec)
{
  GEN serh0, serh0aux;
  if (fl == -1) serh0 = *ptaux;
  else
  {
    serh0aux = series_h0(m_n0(sel), s, VCALL, fl, prec);
    if (fl == 0) serh0 = serh0aux;
    else { serh0 = gel(serh0aux, 1); *ptaux = gel(serh0aux, 2); }
  }
  return gadd(integral_h0(sel, s, VCALL, prec),
              gsub(serh0, series_residues_h0(sel, s, VCALL, prec)));
}

static GEN
xpquo_one(GEN s, GEN cs, GEN ga, long odd, long md, long prec)
{
  GEN rho, a = odd? gen_1: gen_0, z = divsr(md, mppi(prec));
  rho = gmul(gdiv(gpow(gen_I(), gdivgs(gneg(a), 2), prec), gsqrt(ga, prec)),
             gpow(stoi(md), ginv(stoi(4)), prec));
  return gmul(gdiv(gconj(gmul(rho, gpow(z, gdivgs(cs, 2), prec))),
                   gmul(rho, gpow(z, gdivgs(s, 2), prec))),
              gexp(gsub(gconj(glngamma(gdivgs(gadd(cs, a), 2), prec)),
                        glngamma(gdivgs(gadd(s, a), 2), prec)), prec));
}

static GEN
xpquo(GEN s, GEN VCALL, long prec)
{
  long md = get_modulus(VCALL), n, lve, i;
  GEN cd = NULL, z, pz, cs, VC = get_chivec(VCALL), ve, R;
  if (!gequal0(s)) prec = nbits2prec(prec2nbits(prec) + maxss(gexpo(s), 0));
  z = gexp(gdivgs(PiI2(prec), -md), prec);
  if (md == 1)
    return gmul(gpow(mppi(prec), gsub(s, ghalf), prec),
                gexp(gsub(glngamma(gdivgs(gsubsg(1, s), 2), prec),
                          glngamma(gdivgs(s, 2), prec)), prec));
  pz = gpowers(z, md - 1);
  for (n = 1; n < md; n++)
  {
    GEN xn = mycall(VC, n);
    if (xn)
    {
      GEN tmp = gmul(xn, gel(pz, n + 1));
      cd = cd ? gadd(cd, tmp) : tmp;
    }
  }
  cs = gsubsg(1, gconj(s));
  ve = get_signat(VCALL); lve = lg(ve); R = cgetg(lve, t_VEC);
  for (i = 1; i < lve; i++)
    gel(R, i) = xpquo_one(s, cs, gel(cd, i), ve[i], md, prec);
  if (lve == 2) R = gel(R, 1);
  return R;
}

static GEN
dirichlet_ours(GEN s, GEN VCALL, long prec)
{
  GEN sel = RZinit(s, VCALL, gen_1, prec);
  GEN cs, sum1, sum2, aux, pre_fac = xpquo(s, VCALL, prec);
  if (gequal(real_i(s), ghalf))
  { sum1 = total_value(sel, s, VCALL, NULL, 0, prec); sum2 = sum1; }
  else
  {
    sum1 = total_value(sel, s, VCALL, &aux, 1, prec);
    cs = gsubsg(1, gconj(s));
    sum2 = total_value(sel, cs, VCALL, &aux, -1, prec);
  }
  return gadd(sum1, vecmul(pre_fac, gconj(sum2)));
}

/* assume |Im(s)| > 2^-bitprec */
static GEN
RZchi(GEN VCALL, GEN s, long prec)
{
  long prec2 = prec + EXTRAPRECWORD;
  return gprec_wtrunc(dirichlet_ours(gprec_w(s, prec2), VCALL, prec2), prec);
}

/********************************************************************/
/*                         Utility Functions                        */
/********************************************************************/
/* lam = 0, return L(s); else Lambda(s) */
static GEN
lfuncharall(GEN VCALL, GEN s, long lam, long bitprec)
{
  GEN ve, P, Q, R, z = lfunlarge_char(VCALL, s, bitprec);
  long l, i, q, prec;
  if (!lam) return z;
  ve = get_signat(VCALL); l = lg(ve);
  q = get_modulus(VCALL); prec = nbits2prec(bitprec);
  R = cgetg(l, t_VEC);
  Q = divur(q, mppi(prec));
  P = (q == 1 || zv_equal0(ve))? NULL: gsqrt(utoipos(q), prec);
  for (i = 1; i < l; i++)
  {
    GEN se = gmul2n(gaddgs(s, ve[i]), -1), r;
    if (lam == 1)
    {
      r = gmul(gpow(Q, se, prec), ggamma(se, prec));
      if (P && ve[i]) r = gdiv(r, P);
    }
    else
    {
      r = gadd(gmul(se, glog(Q, prec)), glngamma(se, prec));
      if (P && ve[i]) r = gsub(r, glog(P, prec));
    }
    gel(R, i) = r;
  }
  return lam == 1 ? vecmul(R, z) : gadd(R, glog(z, prec));
}

static GEN
lfunlargeall(GEN ldata, GEN s, long lam, long bit)
{
  long prec = nbits2prec(bit) + EXTRAPRECWORD;
  GEN w, an = gel(ldata_get_an(ldata), 2);
  switch(ldata_get_type(ldata))
  {
    case t_LFUN_NF:
    {
      GEN C = nf_get_pol(an), v = lfungetchars(C);
      long i, l = lg(v), fl = lam == 0 || lam == 1;
      for (i = 1; i < l; i++)
      {
        GEN L;
        w = mycharinit(gel(v, i), prec);
        L = lfuncharall(w, s, lam, bit);
        gel(v, i) = fl ? vecprod(L) : vecsum(L);
      }
      return fl ? vecprod(v) : vecsum(v);
    }
    case t_LFUN_CHIGEN:
    {
      GEN chi = gmael(an, 2, 2);
      if (lg(chi) > 1 && is_vec_t(typ(gel(chi,1))))
      { /* multi char */
        w = mycharinit(mkcol(ldata), prec);
        return lfuncharall(w, s, lam, bit);
      }
    }
    default: /* single char */
      w = mycharinit(mkcol(ldata), prec);
      return gel(lfuncharall(w, s, lam, bit), 1);
  }
}

GEN
lfunlarge(GEN CHI, GEN s, long bit)
{ return lfunlargeall(CHI, s, 0, bit); }

GEN
lfunlambdalarge(GEN CHI, GEN s, long bit)
{ return lfunlargeall(CHI, s, 1, bit); }

GEN
lfunloglambdalarge(GEN CHI, GEN s, long bit)
{ return lfunlargeall(CHI, s, -1, bit); }

/********************************************************************/
/*           LERCH RS IMPLEMENTATION FROM SANDEEP TYAGI             */
/********************************************************************/

static GEN
double_exp_residue_pos_h(GEN selsm, long k, long ind, long prec)
{
  long nk = itos(gel(selsm, 1)) + k;
  GEN r = gel(selsm, 2), ale = gel(selsm, 3), aor = gel(selsm, 4);
  GEN h = gel(selsm, 5), t = gen_0;
  switch(ind)
  {
    case 0: t = gaddsg(nk, aor); break;
    case 1: t = gneg(gaddsg(nk, aor)); break;
    case 2: t = gsubsg(nk, aor); break;
  }
  return gdiv(gasinh(gdiv(gsub(t, r), ale), prec), h);
}

static GEN
phi_hat_h(GEN selsm, long m, long ind, long prec)
{ return phi_hat(double_exp_residue_pos_h(selsm, m, ind, prec), prec); }

static long
myex(GEN is)
{ return gequal0(is) ? 0 : maxss(0, 2 + gexpo(is)); }

static GEN
gaminus(GEN s, long prec)
{
  GEN is = imag_i(s), tmp;
  long B = prec2nbits(prec);
  if (gcmpgs(is, -5*B) < 0) return gen_0;
  prec = nbits2prec(B + myex(is));
  tmp = gexp(gsub(glngamma(s, prec), gmul(PiI2n(-1, prec), s)), prec);
  return bitprecision0(tmp, B);
}

static GEN
gaplus(GEN s, long prec)
{
  GEN is = imag_i(s), tmp;
  long B = prec2nbits(prec);
  if (gcmpgs(is, 5*B) > 0) return gen_0;
  prec = nbits2prec(B + myex(is));
  tmp = gexp(gadd(glngamma(s, prec), gmul(PiI2n(-1, prec), s)), prec);
  return bitprecision0(tmp, B);
}

GEN
serh_worker(GEN gk, GEN z, GEN a, GEN ns, GEN gprec)
{
  long k = itos(gk);
  return gmul(gpowgs(z, k), gpow(gaddsg(k, a), ns, itos(gprec)));
}

static GEN
allparsums(long ini, long fin, GEN z, GEN a, GEN ns, long prec)
{
  return parsum(stoi(ini), stoi(fin), strtoclosure("_serh_worker", 4, z, a, ns, stoi(prec)));
}

static GEN
series_h0l(long n0, GEN s, GEN a, GEN lam, long prec)
{
  GEN z = typ(lam) == t_INT ? gen_1 : gexp(gmul(PiI2(prec), lam), prec);
  return allparsums(0, n0, z, a, gneg(s), prec);
}

static GEN
series_h1(long n1, GEN s, GEN a, GEN lam, long prec)
{
  GEN sum1, pre_factor, z, sn = gsubgs(s, 1);
  GEN ini = gequal0(lam) ? gen_1 : gen_0;
  pre_factor = gaplus(gneg(sn), prec);
  if (gequal0(pre_factor)) return gen_0;
  pre_factor = gmul(gmul(pre_factor, gexp(gneg(gmul(PiI2(prec), gmul(a, lam))), prec)), gpow(Pi2n(1, prec), sn, prec));
  z = typ(a) == t_INT ? gen_1 : gexp(gneg(gmul(PiI2(prec), a)), prec);
  sum1 = allparsums(itos(ini), n1 - 1, z, lam, sn, prec);
  return gmul(pre_factor, sum1);
}

static GEN
series_h2(long n2, GEN s, GEN a, GEN lam, long prec)
{
  GEN sum2, pre_factor, z, sn = gsubgs(s, 1);
  pre_factor = gaminus(gneg(sn), prec);
  if (gequal0(pre_factor)) return gen_0;
  pre_factor = gmul(gmul(pre_factor, gexp(gneg(gmul(PiI2(prec), gmul(a, lam))), prec)), gpow(Pi2n(1, prec), sn, prec));
  z = typ(a) == t_INT ? gen_1 : gexp(gmul(PiI2(prec), a), prec);
  sum2 = allparsums(1, n2, z, gneg(lam), sn, prec);
  return gmul(pre_factor, sum2);
}

static GEN
series_residues_h0l(long num_of_poles, GEN selsm0, GEN s, GEN a, GEN lam, long prec)
{
  GEN val = gen_0, ra = real_i(a);
  long n0 = m_n0(selsm0), k;
  for (k = -num_of_poles + 1; k <= num_of_poles; k++)
  {
    if (gsigne(gaddsg(n0 + k, ra)) > 0)
      val = gadd(val, gmul(gmul(phi_hat_h(selsm0, k, 0, prec), gexp(gmul(PiI2(prec), gmulgs(lam, n0 + k)), prec)), gpow(gaddsg(n0 + k, a), gneg(s), prec)));
  }
  return val;
}

static GEN
series_residues_h1(long num_of_poles, GEN selsm1, GEN s, GEN a, GEN lam, long prec)
{
  GEN val = gen_0, rlam = real_i(lam), pre_factor, sn = gsubgs(s, 1);
  long n1 = m_n0(selsm1), k;
  pre_factor = gaplus(gneg(sn), prec);
  if (gequal0(pre_factor)) return gen_0;
  pre_factor = gmul(gmul(pre_factor, gexp(gneg(gmul(PiI2(prec), gmul(a, lam))), prec)), gpow(Pi2n(1, prec), sn, prec));
  for (k = -num_of_poles; k <= num_of_poles - 1; k++)
  {
    if (gsigne(gaddsg(n1 + k, rlam)) > 0)
      val = gadd(val, gmul(gmul(phi_hat_h(selsm1, k, 1, prec), gexp(gneg(gmul(PiI2(prec), gmulgs(a, n1 + k))), prec)), gpow(gaddsg(n1 + k, lam), sn, prec)));
  }
  return gmul(pre_factor, val);
}

static GEN
series_residues_h2(long num_of_poles, GEN selsm2, GEN s, GEN a, GEN lam, long prec)
{
  GEN val = gen_0, rlam = real_i(lam), pre_factor, sn = gsubgs(s, 1);
  long n2 = m_n0(selsm2), k;
  pre_factor = gaminus(gneg(sn), prec);
  if (gequal0(pre_factor)) return gen_0;
  pre_factor = gmul(gmul(pre_factor, gexp(gneg(gmul(PiI2(prec), gmul(a, lam))), prec)), gpow(Pi2n(1, prec), sn, prec));
  for (k = -num_of_poles + 1; k <= num_of_poles; k++)
  {
    if (gsigne(gsubsg(n2 + k, rlam)) > 0)
      val = gsub(val, gmul(gmul(phi_hat_h(selsm2, k, 2, prec), gexp(gmul(PiI2(prec), gmulgs(a, n2 + k)), prec)), gpow(gsubsg(n2 + k, lam), sn, prec)));
  }
  return gmul(pre_factor, val);
}

static GEN
integrand_h0l(GEN selsm0, GEN s, GEN alam, GEN x, long prec)
{
  GEN r0 = gel(selsm0, 2), ale = gel(selsm0, 3), a = gel(selsm0, 4);
  GEN ix = ginv(x), zn = gadd(r0, gmul2n(gmul(ale, gsub(x, ix)), -1));
  GEN pii = PiI2n(0, prec), den, num;
  den = gsub(gexp(gmul(pii, gsub(zn, gmul2n(a, 1))), prec), gexp(gneg(gmul(pii, zn)), prec));
  num = gexp(gmul(gmul(pii, zn), gsub(gmul2n(alam, 1), zn)), prec);
  num = gmul(gmul(gmul(num, ale), gmul2n(gadd(x, ix), -1)), gpow(zn, gneg(s), prec));
  return gdiv(num, den);
}

static GEN
integrand_h12(GEN selsm1, GEN s, GEN alam, GEN x, long prec)
{
  GEN r1 = gel(selsm1, 2), ale = gel(selsm1, 3), lam = gel(selsm1, 4);
  GEN ix = ginv(x), zn = gadd(r1, gmul2n(gmul(ale, gsub(x, ix)), -1));
  GEN pii = PiI2n(0, prec), den, num, y;
  den = gsub(gexp(gmul(pii, gadd(zn, gmul2n(lam, 1))), prec), gexp(gneg(gmul(pii, zn)), prec));
  num = gexp(gmul(gmul(pii, zn), gadd(gmul2n(alam, 1), zn)), prec);
  num = gmul(gmul(gmul(num, ale), gmul2n(gadd(x, ix), -1)), gpow(zn, gsubgs(s, 1), prec));
  y = gdiv(num, den);
  if (gcmp(garg(zn, prec), Pi2n(-2, prec)) > 0)
    y = gmul(y, gexp(gmul(PiI2(prec), gsubsg(1, s)), prec));
  return y;
}

static GEN
integral_h0l(GEN lin_grid, GEN selsm0, GEN s, GEN a, GEN lam, long prec)
{
  GEN alam = gadd(a, lam), S = gen_0;
  pari_sp av = avma;
  long j, l = lg(lin_grid);
  for (j = 1; j < l; j++)
  {
    S = gadd(S, integrand_h0l(selsm0, s, alam, gel(lin_grid, j), prec));
    if ((j & 0xff) == 0) S = gerepileupto(av, S);
  }
  S = gmul(m_h(selsm0), S);
  return gmul(S, gexp(gneg(gmul(PiI2n(0, prec), gmul(a, gaddsg(1, gadd(a, gmul2n(lam, 1)))))), prec));
}

/* do not forget a minus sign for index 2 */
static GEN
integral_h12(GEN lin_grid, GEN selsm1, GEN s, GEN a, GEN lam, long prec)
{
  GEN alam = gadd(a, lam), S = gen_0, ga = gaminus(gsubsg(1, s), prec);
  pari_sp av = avma;
  long j, l = lg(lin_grid);
  if (gequal0(ga)) return S;
  for (j = 1; j < l; j++)
  {
    S = gadd(S, integrand_h12(selsm1, s, alam, gel(lin_grid, j), prec));
    if ((j & 0xff) == 0) S = gerepileupto(av, S);
  }
  if (gequal0(S)) return gen_0;
  S = gmul(m_h(selsm1), S);
  return gmul(gmul(gmul(S, ga), gexp(gmul(PiI2n(0, prec), gmul(lam, gaddgs(lam, 1))), prec)), gpow(Pi2n(1, prec), gsubgs(s, 1), prec));
}

struct _fun_q0_t { GEN sel, s, alam, B; };
static GEN
_fun_q0(void *E, GEN x)
{
  struct _fun_q0_t *S = (struct _fun_q0_t*)E;
  GEN z = integrand_h0l(S->sel, S->s, S->alam, x, DEFAULTPREC);
  return addrr(S->B, mylog(z, DEFAULTPREC));
}
static GEN
_fun_q12(void *E, GEN x)
{
  struct _fun_q0_t *S = (struct _fun_q0_t*)E;
  GEN z = integrand_h12(S->sel, S->s, S->alam, x, DEFAULTPREC);
  return addrr(S->B, mylog(z, DEFAULTPREC));
}

static GEN
RZLERinit(GEN s, GEN a, GEN lam, GEN al, GEN num_of_poles, long prec)
{
  GEN eps, r0, r1, r2, h, lin_grid, q, q0, q1, q2, sel0, sel1, sel2, lq;
  GEN pinv = ginv(PiI2(prec)), c = gmul2n(gadd(a, lam), -1), n0, n1, n2, c2;
  long m, LD = DEFAULTPREC;
  struct _fun_q0_t E;
  if (!al || gequal0(al))
    al = gcmpgs(gabs(imag_i(s), prec), 100) < 0 ? ginv(stoi(4)) : gen_1;
  c2 = gsub(gsqr(c), gmul(s, pinv));
  r0 = gadd(c, gsqrt(c2, prec));
  r1 = gsqrt(gadd(c2, pinv), prec);
  r2 = gsub(r1, c);
  r1 = gneg(gadd(r1, c));
  n0 = gfloor(gsub(gadd(real_i(r0), imag_i(r0)), a));
  n1 = gneg(gfloor(gadd(gsub(real_i(r1), imag_i(r1)), lam)));
  n2 = gfloor(gadd(gsub(real_i(r2), imag_i(r2)), lam));

  eps = gexp(PiI2n(-2, prec), prec);
  E.s = s; E.alam = gadd(a, lam), E.B = mulur(prec, mplog2(prec));
  lq = gmul(gsqrt(gmul(gdivsg(prec, Pi2n(1, LD)), mplog2(LD)), LD), al);
  E.sel = sel0 = mkvec5(n0, r0, gdiv(al, eps), a, gen_0);
  q0 = findq(&E, &_fun_q0, lq, prec);

  if (!gequal1(al)) lq = gdiv(lq, gsqr(al));
  E.sel = sel1 = mkvec5(n1, r1, gmul(al, eps), lam, gen_0);
  q1 = findq(&E, &_fun_q12, lq, prec);
  E.sel = sel2 = mkvec5(n2, r2, gmul(al, eps), lam, gen_0);
  q2 = findq(&E, &_fun_q12, lq, prec);
  q = vecmax(mkvec3(q0, q1, q2));
  m = get_m(q, prec);
  gel(sel0, 5) = gel(sel1, 5) = gel(sel2, 5) = h = divru(q, (m-1) >> 1);
  lin_grid = setlin_grid_exp(h, m, prec);
  if (!num_of_poles) num_of_poles = gen_1;
  return mkvec5(sel0, sel1, sel2, lin_grid, num_of_poles);
}

static GEN
lerch_ours(GEN sel, GEN s, GEN a, GEN lam, long prec)
{
  GEN selsm0 = gel(sel, 1), selsm1 = gel(sel, 2), selsm2 = gel(sel, 3);
  GEN lin_grid = gel(sel, 4), val_h0, val_h1, val_h2;
  GEN serandres_h0, serandres_h1, serandres_h2;
  long num_of_poles = itos(gel(sel, 5));
  serandres_h0 = gadd(series_h0l(m_n0(selsm0), s, a, lam, prec), series_residues_h0l(num_of_poles, selsm0, s, a, lam, prec));
  val_h0 = gadd(integral_h0l(lin_grid, selsm0, s, a, lam, prec), serandres_h0);
  serandres_h1 = gadd(series_h1(m_n0(selsm1), s, a, lam, prec), series_residues_h1(num_of_poles, selsm1, s, a, lam, prec));
  val_h1 = gadd(integral_h12(lin_grid, selsm1, s, a, lam, prec), serandres_h1);  serandres_h2 = gadd(series_h2(m_n0(selsm2), s, a, lam, prec), series_residues_h2(num_of_poles, selsm2, s, a, lam, prec));
  val_h2 = gadd(gneg(integral_h12(lin_grid, selsm2, s, a, lam, prec)), serandres_h2);
  return gadd(gadd(val_h0, val_h1), val_h2);
}

GEN
serhlong_worker(GEN gk, GEN z, GEN a, GEN ns, GEN gprec)
{
  long k = itos(gk);
  return gmul(gpowgs(z, k), gpow(gaddsg(k, a), ns, itos(gprec)));
}

static GEN
RZlerch_easy(GEN s, GEN a, GEN lam, long prec)
{
  pari_sp ltop = avma;
  GEN z, y, gnlim;
  long B = prec2nbits(prec), nlim, LD = LOWDEFAULTPREC;
  gnlim = gceil(gdiv(gmulsg(B + 5, mplog2(LD)), gmul(Pi2n(1, prec), imag_i(lam))));
  if (gexpo(gnlim) > 40)
    pari_err(e_MISC, "imag(lam) too small for RZlerch_easy");
  nlim = itos(gnlim); prec += EXTRAPRECWORD;
  z = typ(lam) == t_INT ? gen_1 : gexp(gmul(PiI2(prec), lam), prec);
  if (nlim < 10000000) y = allparsums(0, nlim, z, a, gneg(s), prec);
  else
    y = parsum(gen_0, gnlim, strtoclosure("_serhlong_worker", 4, z, a, gneg(s), stoi(prec)));
  return gerepileupto(ltop, bitprecision0(y, B));
}

static GEN
lerchlarge(GEN s, GEN a, GEN lam, GEN al, GEN num_of_poles, long prec)
{
  pari_sp ltop = avma;
  GEN val, sel;
  long B = prec2nbits(prec), NB = B + EXTRAPRECWORD, sl = gsigne(imag_i(lam));
  if (sl < 0) pari_err_IMPL("imag(lam) < 0");
  if (sl > 0) return RZlerch_easy(s, a, lam, prec);
  if (gcmpgs(real_i(a), 1) < 0)
    return gerepileupto(ltop, gadd(gpow(a, gneg(s), prec), gmul(gexp(gmul(PiI2(prec), lam), prec), lerchlarge(s, gaddgs(a, 1), lam, al, num_of_poles, prec))));
  if (gcmpgs(real_i(a), 2) >= 0)
    return gerepileupto(ltop, gmul(gexp(gneg(gmul(PiI2(prec), lam)), prec), gsub(lerchlarge(s, gsubgs(a, 1), lam, al, num_of_poles, prec), gpow(gsubgs(a, 1), gneg(s), prec))));
  if (gsigne(imag_i(s)) > 0)
    return gerepileupto(ltop, gconj(lerchlarge(gconj(s), a, gfrac(gneg(lam)), al, num_of_poles, prec)));
  a = bitprecision0(a, NB);
  s = bitprecision0(s, NB);
  lam = bitprecision0(lam, NB); prec = nbits2prec(NB);
  sel = RZLERinit(s, a, lam, al, num_of_poles, prec);
  val = lerch_ours(sel, s, a, lam, prec);
  return gerepilecopy(ltop, bitprecision0(val, B));
}

GEN
zetahurwitzlarge(GEN s, GEN a, long prec)
{ return lerchlarge(s, a, gen_0, gen_1, gen_1, prec); }

GEN
lerchzetalarge(GEN s, GEN a, GEN lam, long prec)
{ return lerchlarge(s, a, lam, gen_1, gen_1, prec); }
