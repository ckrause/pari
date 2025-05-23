/* Copyright (C) 2015  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**           Dirichlet series through Euler product               **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static void
err_direuler(GEN x)
{ pari_err_DOMAIN("direuler","constant term","!=", gen_1,x); }

/* s = t_POL (tolerate t_SER of valuation 0) of constant term = 1
 * d = minimal such that p^d > X
 * V indexed by 1..X will contain the a_n
 * v[1..n] contains the indices nj such that V[nj] != 0 */
static long
dirmuleuler_small(GEN V, GEN v, long n, ulong p, GEN s, long d)
{
  long i, j, m = n, D = minss(d+2, lg(s));
  ulong q = 1, X = lg(V)-1;

  for (i = 3, q = p; i < D; i++, q *= p) /* q*p does not overflow */
  {
    GEN aq = gel(s,i);
    if (gequal0(aq)) continue;
    /* j = 1 */
    gel(V,q) = aq;
    v[++n] = q;
    for (j = 2; j <= m; j++)
    {
      ulong nj = umuluu_le(uel(v,j), q, X);
      if (!nj) continue;
      gel(V,nj) = gmul(aq, gel(V,v[j]));
      v[++n] = nj;
    }
  }
  return n;
}

/* ap != 0 for efficiency, p > sqrt(X) */
static void
dirmuleuler_large(GEN V, ulong p, GEN ap)
{
  long j, jp, X = lg(V)-1;
  gel(V,p) = ap;
  for (j = 2, jp = 2*p; jp <= X; j++, jp += p) gel(V,jp) = gmul(ap, gel(V,j));
}

static ulong
direulertou(GEN a, GEN fl(GEN))
{
  if (typ(a) != t_INT)
  {
    a = fl(a);
    if (typ(a) != t_INT) pari_err_TYPE("direuler", a);
  }
  return signe(a)<=0 ? 0: itou(a);
}

static GEN
direuler_Sbad(GEN V, GEN v, GEN Sbad, ulong *n)
{
  long i, l = lg(Sbad);
  ulong X = lg(V)-1;
  GEN pbad = gen_1;
  for (i = 1; i < l; i++)
  {
    GEN ai = gel(Sbad,i);
    ulong q;
    if (typ(ai) != t_VEC || lg(ai) != 3)
      pari_err_TYPE("direuler [bad primes]",ai);
    q = gtou(gel(ai,1));
    if (q <= X)
    {
      long d = ulogint(X, q) + 1;
      GEN s = direuler_factor(gel(ai,2), d);
      *n = dirmuleuler_small(V, v, *n, q, s, d);
      pbad = muliu(pbad, q);
    }
  }
  return pbad;
}

GEN
direuler_bad(void *E, GEN (*eval)(void *,GEN,long), GEN a,GEN b,GEN c, GEN Sbad)
{
  ulong au, bu, X, sqrtX, n, p;
  pari_sp av0 = avma;
  GEN gp, v, V;
  forprime_t T;
  au = direulertou(a, gceil);
  bu = direulertou(b, gfloor);
  X = c ? direulertou(c, gfloor): bu;
  if (X == 0) return cgetg(1,t_VEC);
  if (bu > X) bu = X;
  if (!u_forprime_init(&T, au, bu)) { set_avma(av0); return mkvec(gen_1); }
  v = vecsmall_ei(X, 1);
  V = vec_ei(X, 1);
  n = 1;
  if (Sbad) Sbad = direuler_Sbad(V, v, Sbad, &n);
  p = 1; gp = cgetipos(3); sqrtX = usqrt(X);
  while (p <= sqrtX && (p = u_forprime_next(&T)))
    if (!Sbad || umodiu(Sbad, p))
    {
      long d = ulogint(X, p) + 1; /* minimal d such that p^d > X */
      GEN s;
      gp[2] = p; s = eval(E, gp, d);
      n = dirmuleuler_small(V, v, n, p, s, d);
    }
  while ((p = u_forprime_next(&T))) /* sqrt(X) < p <= X */
    if (!Sbad || umodiu(Sbad, p))
    {
      GEN s;
      gp[2] = p; s = eval(E, gp, 2); /* s either t_POL or t_SER of val 0 */
      if (lg(s) > 3 && !gequal0(gel(s,3)))
        dirmuleuler_large(V, p, gel(s,3));
    }
  return gc_GEN(av0,V);
}

/* return a t_SER or a truncated t_POL to precision n */
GEN
direuler_factor(GEN s, long n)
{
  long t = typ(s);
  if (is_scalar_t(t))
  {
    if (!gequal1(s)) err_direuler(s);
    return scalarpol_shallow(s,0);
  }
  switch(t)
  {
    case t_POL: break; /* no need to RgXn_red */
    case t_RFRAC:
    {
      GEN p = gel(s,1), q = gel(s,2);
      q = RgXn_red_shallow(q,n);
      s = RgXn_inv(q, n);
      if (typ(p) == t_POL && varn(p) == varn(q))
      {
        p = RgXn_red_shallow(p, n);
        s = RgXn_mul(s, p, n);
      }
      else
        if (!gequal1(p)) s = RgX_Rg_mul(s, p);
      if (!signe(s) || !gequal1(gel(s,2))) err_direuler(s);
      break;
    }
    case t_SER:
      if (!signe(s) || valser(s) || !gequal1(gel(s,2))) err_direuler(s);
      break;
    default: pari_err_TYPE("direuler", s);
  }
  return s;
}

struct eval_bad
{
  void *E;
  GEN (*eval)(void *, GEN);
};
static GEN
eval_bad(void *E, GEN p, long n)
{
  struct eval_bad *d = (struct eval_bad*) E;
  return direuler_factor(d->eval(d->E, p), n);
}
GEN
direuler(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, GEN c)
{
  struct eval_bad d;
  d.E= E; d.eval = eval;
  return direuler_bad((void*)&d, eval_bad, a, b, c, NULL);
}

static GEN
primelist(forprime_t *T, GEN Sbad, long n, long *running)
{
  GEN P = cgetg(n+1, t_VECSMALL);
  long i, j;
  for (i = 1, j = 1; i <= n; i++)
  {
    ulong p = u_forprime_next(T);
    if (!p) { *running = 0; break; }
    if (Sbad && umodiu(Sbad, p)==0) continue;
    uel(P,j++) = p;
  }
  setlg(P, j);
  return P;
}

GEN
pardireuler(GEN worker, GEN a, GEN b, GEN c, GEN Sbad)
{
  ulong au, bu, X, sqrtX, n, snX, nX;
  pari_sp av0 = avma;
  GEN v, V;
  forprime_t T;
  struct pari_mt pt;
  long running = 1, pending = 0;
  au = direulertou(a, gceil);
  bu = direulertou(b, gfloor);
  X = c ? direulertou(c, gfloor): bu;
  if (X == 0) return cgetg(1,t_VEC);
  if (bu > X) bu = X;
  if (!u_forprime_init(&T, au, bu)) { set_avma(av0); return mkvec(gen_1); }
  v = vecsmall_ei(X, 1);
  V = vec_ei(X, 1);
  n = 1;
  if (Sbad) Sbad = direuler_Sbad(V, v, Sbad, &n);
  sqrtX = usqrt(X); snX = uprimepi(sqrtX); nX = uprimepi(X);
  if (snX)
  {
    GEN P = primelist(&T, Sbad, snX, &running);
    GEN R = gel(closure_callgenvec(worker, mkvec2(P, utoi(X))), 2);
    long i, l = lg(P);
    for (i = 1; i < l; i++)
    {
      GEN s = gel(R,i);
      n = dirmuleuler_small(V, v, n, uel(P,i), s, lg(s));
    }
  } else snX = 1;
  mt_queue_start_lim(&pt, worker, (nX+snX-1)/snX);
  while (running || pending)
  {
    GEN done;
    GEN P = running? primelist(&T, Sbad, snX, &running): NULL;
    mt_queue_submit(&pt, 0, P ? mkvec2(P, utoi(X)): NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (done)
    {
      GEN P = gel(done,1), R = gel(done,2);
      long j, l = lg(P);
      for (j=1; j<l; j++)
      {
        GEN F = gel(R,j);
        if (degpol(F) && !gequal0(gel(F,3)))
          dirmuleuler_large(V, uel(P,j), gel(F,3));
      }
    }
  }
  mt_queue_end(&pt);
  return gc_GEN(av0,V);
}

/********************************************************************/
/**                                                                **/
/**                 DIRPOWERS and DIRPOWERSSUM                     **/
/**                                                                **/
/********************************************************************/

/* [1^B,...,N^B] */
GEN
vecpowuu(long N, ulong B)
{
  GEN v;
  long p, i;
  forprime_t T;

  if (B <= 8000)
  {
    if (!B) return const_vec(N,gen_1);
    v = cgetg(N+1, t_VEC); if (N == 0) return v;
    gel(v,1) = gen_1;
    if (B == 1)
      for (i = 2; i <= N; i++) gel(v,i) = utoipos(i);
    else if (B == 2)
    {
      ulong o, s;
      if (N & HIGHMASK)
        for (i = 2, o = 3; i <= N; i++, o += 2)
          gel(v,i) = addiu(gel(v,i-1), o);
      else
        for (i = 2, s = 1, o = 3; i <= N; i++, s += o, o += 2)
          gel(v,i) = utoipos(s + o);
    }
    else if (B == 3)
      for (i = 2; i <= N; i++) gel(v,i) = powuu(i, B);
    else
    {
      long k, Bk, e = expu(N);
      for (i = 3; i <= N; i += 2) gel(v,i) = powuu(i, B);
      for (k = 1; k <= e; k++)
      {
        N >>= 1; Bk = B * k;
        for (i = 1; i <= N; i += 2) gel(v, i << k) = shifti(gel(v, i), Bk);
      }
    }
    return v;
  }
  v = const_vec(N, NULL);
  u_forprime_init(&T, 3, N);
  while ((p = u_forprime_next(&T)))
  {
    long m, pk, oldpk;
    gel(v,p) = powuu(p, B);
    for (pk = p, oldpk = p; pk; oldpk = pk, pk = umuluu_le(pk,p,N))
    {
      if (pk != p) gel(v,pk) = mulii(gel(v,oldpk), gel(v,p));
      for (m = N/pk; m > 1; m--)
        if (gel(v,m) && m%p) gel(v, m*pk) = mulii(gel(v,m), gel(v,pk));
    }
  }
  gel(v,1) = gen_1;
  for (i = 2; i <= N; i+=2)
  {
    long vi = vals(i);
    gel(v,i) = shifti(gel(v,i >> vi), B * vi);
  }
  return v;
}

/* does x^s require log(x) ? */
static long
get_needlog(GEN s)
{
  switch(typ(s))
  {
    case t_REAL: return 2; /* yes but not powcx */
    case t_COMPLEX: return 1; /* yes using powcx */
    default: return 0; /* no */
  }
}
/* [1^B,...,N^B] */
GEN
vecpowug(long N, GEN B, long prec)
{
  GEN v, logp = NULL;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  long p, precp = 2, prec0, prec1, needlog;
  forprime_t T;
  if (N == 1) return mkvec(gen_1);
  if (typ(B) == t_INT && lgefint(B) <= 3 && signe(B) >= 0)
    return vecpowuu(N, itou(B));
  needlog = get_needlog(B);
  prec1 = prec0 = prec;
  if (needlog == 1) prec1 = powcx_prec(log2((double)N), B, prec);
  u_forprime_init(&T, 2, N);
  v = const_vec(N, NULL);
  gel(v,1) = gen_1;
  while ((p = u_forprime_next(&T)))
  {
    long m, pk, oldpk;
    GEN u;
    gp[2] = p;
    if (needlog)
    {
      if (!logp)
        logp = logr_abs(utor(p, prec1));
      else
      { /* Assuming p and precp are odd,
         * log p = log(precp) + 2 atanh((p - precp) / (p + precp)) */
        ulong a = p >> 1, b = precp >> 1; /* p = 2a + 1, precp = 2b + 1 */
        GEN z = atanhuu(a - b, a + b + 1, prec1); /* avoid overflow */
        shiftr_inplace(z, 1); logp = addrr(logp, z);
      }
      u = needlog == 1? powcx(gp, logp, B, prec0)
                      : mpexp(gmul(B, logp));
      if (p == 2) logp = NULL; /* reset: precp must be odd */
    }
    else
      u = gpow(gp, B, prec0);
    precp = p;
    gel(v,p) = u; /* p^B */
    if (prec0 != prec) gel(v,p) = gprec_wtrunc(gel(v,p), prec);
    for (pk = p, oldpk = p; pk; oldpk = pk, pk = umuluu_le(pk,p,N))
    {
      if (pk != p) gel(v,pk) = gmul(gel(v,oldpk), gel(v,p));
      for (m = N/pk; m > 1; m--)
        if (gel(v,m) && m%p) gel(v, m*pk) = gmul(gel(v,m), gel(v,pk));
    }
  }
  return v;
}

GEN
dirpowers(long n, GEN x, long prec)
{
  pari_sp av;
  GEN v;
  if (n <= 0) return cgetg(1, t_VEC);
  av = avma; v = vecpowug(n, x, prec);
  if (typ(x) == t_INT && lgefint(x) <= 3 && signe(x) >= 0 && cmpiu(x, 2) <= 0)
    return v;
  return gc_GEN(av, v);
}

/* f is a totally multiplicative function of modulus 0 or 1
 * (essentially a Dirichlet character). Compute simultaneously
 * sum_{0 < n <= N} f(n)n^s and sum_{0 < n <= N} f(n)n^{-1-conj(s)}
 * Warning: s is conjugated, but not f. Main application for Riemann-Siegel,
 * where we need R(chi,s) and conj(R(chi,1-conj(s))). */

static GEN
vecmulsqlv(GEN Q, GEN V)
{
  long l, i;
  GEN W;
  if (typ(V) != t_VEC) return RgV_Rg_mul(Q, V);
  l = lg(Q); W = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(W, i) = vecmul(gel(Q, i), V);
  return W;
}

/* P = prime divisors of (squarefree) n, V[i] = i^s for i <= sq.
 * Return NULL if n is not sq-smooth, else f(n)n^s */
static GEN
smallfact(ulong n, GEN P, ulong sq, GEN V)
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

static GEN
_Qtor(GEN x, long prec)
{ return typ(x) == t_FRAC? fractor(x, prec): x; }
static GEN
Qtor(GEN x, long prec)
{
  long tx = typ(x);
  if (tx == t_VEC || tx == t_COL) pari_APPLY_same(_Qtor(gel(x, i), prec));
  return tx == t_FRAC? fractor(x, prec): x;
}

static GEN
vecf(long N, void *E, GEN (*f)(void *, ulong, long), long prec)
{
  GEN v;
  long n;
  if (!f) return NULL;
  v = cgetg(N + 1, t_VEC);
  for (n = 1; n <= N; n++) gel(v,n) = f(E, n, prec);
  return v;
}

/* Here #V = #F > 0 is small. Analogous to dotproduct, with following
 * semantic differences: uses V[1] = 1; V has scalar values but F may have
 * vector values */
static GEN
naivedirpowerssum(GEN V, GEN F, long prec)
{
  GEN S;
  if (!F) S = RgV_sum(V);
  else
  {
    long n, l = lg(V);
    S = gel(F,1); /* V[1] = 1 */
    for (n = 2; n < l; n++) S = gadd(S, gmul(gel(V, n), gel(F, n)));
  }
  return Qtor(S, prec);
}

static GEN
smalldirpowerssum(long N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                  long both, long prec)
{
  GEN F, V, S, SB;
  if (!N)
  {
    if (!f) return both? mkvec2(gen_0, gen_0): gen_0;
    return gmul(gen_0, f(E, 1, prec));
  }
  V = vecpowug(N, s, prec);
  F = vecf(N, E, f, prec);
  S = naivedirpowerssum(V, F, prec);
  if (!both) return S;
  if ((both==2 || !f) && gequalm1(gmul2n(real_i(s), 1)))
    SB = S;
  else
  {
    GEN FB = (both == 1 && F)? conj_i(F): F;
    long n;
    for (n = 2; n <= N; n++) gel(V, n) = ginv(gmulsg(n, gel(V, n)));
    SB = naivedirpowerssum(V, FB, prec);
  }
  return mkvec2(S, SB);
}

static void
v2unpack(GEN v, GEN *pV, GEN *pVB)
{
  if (typ(v) == t_COL) { *pV = gel(v,1); *pVB = gel(v,2); }
  else { *pV = v; *pVB = NULL; }
}
static GEN
v2pack(GEN V, GEN VB) { return VB? mkcol2(V,VB): V; }

static GEN
dirpowsuminit(GEN s, GEN onef, GEN zerf, void *E, GEN (*f)(void *, ulong, long),              GEN data, long both)
{
  long needlog = data[1], prec0 = data[2], prec1 = data[3];
  ulong a, b, c, e, q, n, sq = usqrt(data[4]);
  GEN V = cgetg(sq+1, t_VEC), W = cgetg(sq+1, t_VEC), VB = NULL, WB = NULL;
  GEN Q = cgetg(sq+1, t_VEC), Z = cgetg(sq+1, t_VEC), QB = NULL, ZB = NULL;
  GEN logp, c2, Q2, Q3, Q6, c2B = NULL, Q2B = NULL, Q3B = NULL, Q6B = NULL;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};

  if (both == 1 || (both == 2 && !gequal(real_i(s), gneg(ghalf))))
  { VB = cgetg(sq+1, t_VEC); WB = cgetg(sq+1, t_VEC); QB = cgetg(sq+1, t_VEC);}
  gel(V, 1) = gel(W, 1) = gel(Q, 1) = onef;
  if (VB) { gel(VB, 1) = gel(WB, 1) = gel(QB, 1) = onef; }
  c2 = gpow(gen_2, s, prec0); if (VB) c2B = ginv(gmul2n(conj_i(c2), 1));
  if (f)
  {
    GEN tmp2 = f(E, 2, prec0);
    c2 = gmul(c2, tmp2); if (VB) c2B = gmul(c2B, tmp2);
  }
  gel(V,2) = c2; /* f(2) 2^s */
  gel(W,2) = Qtor(gadd(c2, onef), prec0);
  gel(Q,2) = Qtor(gadd(vecsqr(c2), onef), prec0);
  if (VB)
  {
    gel(VB, 2) = c2B; gel(WB, 2) = Qtor(gadd(c2B, onef), prec0);
    gel(QB, 2) = Qtor(gadd(vecsqr(c2B), onef), prec0);
  }
  logp = NULL;
  for (n = 3; n <= sq; n++)
  {
    GEN u = NULL, uB = NULL, ks = f ? f(E, n, prec0) : gen_1;
    if (gequal0(ks)) ks = NULL;
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
        if (ks)
          u = needlog == 1? powcx(gp, logp, s, prec0) : mpexp(gmul(s, logp));
      }
      else if (ks) u = gpow(gp, s, prec0);
      if (ks)
      {
        if (VB) uB = gmul(ginv(gmulsg(n, conj_i(u))), ks);
        u = gmul(u, ks); /* f(n) n^s */
      }
    }
    else
    {
      u = vecmul(c2, gel(V, n >> 1));
      if (VB) uB = vecmul(c2B, gel(VB, n >> 1));
    }
    if (ks)
    {
      gel(V,n) = u; /* f(n) n^s */
      gel(W,n) = gadd(gel(W, n-1), gel(V,n));        /*= sum_{i<=n} f(i)i^s */
      gel(Q,n) = gadd(gel(Q, n-1), vecsqr(gel(V,n)));/*= sum_{i<=n} f(i^2)i^2s*/
      if (VB)
      {
        gel(VB,n) = uB;
        gel(WB,n) = gadd(gel(WB,n-1), gel(VB,n));
        gel(QB,n) = gadd(gel(QB,n-1), vecsqr(gel(VB,n)));
      }
    }
    else
    {
      gel(V,n) = zerf; gel(W,n) = gel(W, n-1); gel(Q,n) = gel(Q, n-1);
      if (VB)
      { gel(VB,n) = zerf; gel(WB,n) = gel(WB, n-1); gel(QB,n) = gel(QB, n-1); }
    }
  }
  Q2 = vecmulsqlv(Q, gel(V,2));
  Q3 = vecmulsqlv(Q, gel(V,3));
  Q6 = vecmulsqlv(Q, gel(V,6));
  if (VB)
  {
    Q2B = vecmulsqlv(QB, gel(VB,2));
    Q3B = vecmulsqlv(QB, gel(VB,3));
    Q6B = vecmulsqlv(QB, gel(VB,6));
  }
  /* a,b,c,e = sqrt(q), sqrt(q/2), sqrt(q/3), sqrt(q/6)
   * Z[q] = Q[a] + 2^s Q[b] + 3^s Q[c] + 6^s Q[e], with Q[0] = 0 */
  gel(Z, 1) = onef;
  gel(Z, 2) = gel(W, 2);
  gel(Z, 3) = gel(W, 3);
  gel(Z, 4) = gel(Z, 5) = gel(W, 4);
  gel(Z, 6) = gel(Z, 7) = gadd(gel(W, 4), gel(V, 6));
  if (VB)
  {
    ZB = cgetg(sq+1, t_VEC);
    gel(ZB, 1) = onef;
    gel(ZB, 2) = gel(WB, 2);
    gel(ZB, 3) = gel(WB, 3);
    gel(ZB, 4) = gel(ZB, 5) = gel(WB, 4);
    gel(ZB, 6) = gel(ZB, 7) = gadd(gel(WB, 4), gel(VB, 6));
  }
  a = 2; b = c = e = 1;
  for (q = 8; q <= sq; q++)
  { /* Gray code: at most one of a,b,c,d differs (by 1) from previous value */
    GEN z = gel(Z, q - 1), zB = NULL;
    ulong na, nb, nc, ne, na2, nb2, nc2, ne2;
    if (VB) zB = gel(ZB, q - 1);
    if ((na = usqrt(q)) != a)
    { a = na; na2 = na * na; z = gadd(z, gel(V, na2));
      if (VB) zB = gadd(zB, gel(VB, na2)); }
    else if ((nb = usqrt(q / 2)) != b)
    { b = nb; nb2 = 2 * nb * nb; z = gadd(z, gel(V, nb2));
      if (VB) zB = gadd(zB, gel(VB, nb2)); }
    else if ((nc = usqrt(q / 3)) != c)
    { c = nc; nc2 = 3 * nc * nc; z = gadd(z, gel(V, nc2));
      if (VB) zB = gadd(zB, gel(VB, nc2)); }
    else if ((ne = usqrt(q / 6)) != e)
    { e = ne; ne2 = 6 * ne * ne; z = gadd(z, gel(V, ne2));
      if (VB) zB = gadd(zB, gel(VB, ne2)); }
    gel(Z, q) = z; if (VB) gel(ZB, q) = zB;
  }
  return v2pack(mkvecn(7, V, W, Q, Q2, Q3, Q6, Z),
                VB? mkvecn(7, VB, WB, QB, Q2B, Q3B, Q6B, ZB): NULL);
}

static GEN
sumprimeloop(forprime_t *pT, GEN s, long N, GEN data, GEN S, GEN W, GEN WB,
             void *E, GEN (*f)(void *, ulong, long))
{
  pari_sp av = avma;
  long needlog = data[1], prec0 = data[2], prec1 = data[3];
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  ulong p, precp = 0;
  GEN logp = NULL, SB = WB? S: NULL;

  while ((p = u_forprime_next(pT)))
  {
    GEN u = NULL, ks;
    if (!f) ks = gen_1;
    else
    {
      ks = f(E, p, prec1);
      if (gequal0(ks)) ks = NULL;
      if (ks && gequal1(ks)) ks = gen_1;
    }
    gp[2] = p;
    if (needlog)
    {
      if (!logp)
        logp = logr_abs(utor(p, prec1));
      else
      { /* Assuming p and precp are odd,
         * log p = log(precp) + 2 atanh((p - precp) / (p + precp)) */
        ulong a = p >> 1, b = precp >> 1; /* p = 2a + 1, precp = 2b + 1 */
        GEN z = atanhuu(a - b, a + b + 1, prec1); /* avoid overflow */
        shiftr_inplace(z, 1); logp = addrr(logp, z);
      }
      if (ks) u = needlog == 1? powcx(gp, logp, s, prec0)
                              : mpexp(gmul(s, logp));
    }
    else if (ks) u = gpow(gp, s, prec0);
    if (ks)
    {
      S = gadd(S, vecmul(gel(W, N / p), ks == gen_1? u: gmul(ks, u)));
      if (WB)
      {
        GEN w = gel(WB, N / p);
        if (ks != gen_1) w = vecmul(ks, w);
        SB = gadd(SB, gdiv(w, gmulsg(p, conj_i(u))));
      }
    }
    precp = p;
    if ((p & 0x1ff) == 1)
    {
      if (!logp) (void)gc_all(av, SB? 2: 1, &S, &SB);
      else (void)gc_all(av, SB? 3: 2, &S, &logp, &SB);
    }
  }
  return v2pack(S, SB);
}

static GEN
add4(GEN a, GEN b, GEN c, GEN d) { return gadd(gadd(a,b), gadd(c,d)); }

static const long step = 2048;
static int
mksqfloop(long N, long x1, GEN R, GEN RB, GEN *pS, GEN *pSB)
{
  GEN V = gel(R,1), Q = gel(R,3), Q2 = gel(R,4);
  GEN Q3 = gel(R,5), Q6 = gel(R,6), Z = gel(R,7);
  GEN v, VB = NULL, QB = NULL, Q2B = NULL, Q3B = NULL, Q6B = NULL, ZB = NULL;
  long x2, j, lv, sq = lg(V)-1;

  if (RB)
  { VB = gel(RB,1); QB = gel(RB,3); Q2B = gel(RB,4);
    Q3B = gel(RB,5), Q6B = gel(RB,6); ZB = gel(RB,7); }
  /* beware overflow, fuse last two bins (avoid a tiny remainder) */
  x2 = (N >= 2*step && N - 2*step >= x1)? x1-1 + step: N;
  v = vecfactorsquarefreeu_coprime(x1, x2, mkvecsmall2(2, 3));
  lv = lg(v);
  for (j = 1; j < lv; j++)
    if (gel(v,j))
    {
      ulong d = x1 - 1 + j; /* squarefree, coprime to 6 */
      GEN t = smallfact(d, gel(v,j), sq, V), u;
      GEN tB = NULL, uB = NULL; /* = f(d) d^s */
      long a, b, c, e, q;
      if (!t || gequal0(t)) continue;
      if (VB) tB = vecinv(gmulsg(d, conj_i(t)));
      /* warning: gives 1/conj(f(d)) d^(-1-conj(s)), equal to
         f(d) d^(-1-conj(s)) only if |f(d)|=1. */
      /* S += f(d) * d^s * Z[q] */
      q = N / d;
      if (q == 1)
      {
        *pS = gadd(*pS, t); if (VB) *pSB = gadd(*pSB, tB);
        continue;
      }
      if (q <= sq) { u = gel(Z, q); if (VB) uB = gel(ZB, q); }
      else
      {
        a = usqrt(q); b = usqrt(q / 2); c = usqrt(q / 3); e = usqrt(q / 6);
        u = add4(gel(Q,a), gel(Q2,b), gel(Q3,c), gel(Q6,e));
        if (VB) uB = add4(gel(QB,a), gel(Q2B,b), gel(Q3B,c), gel(Q6B,e));
      }
      *pS = gadd(*pS, vecmul(t, u)); if (VB) *pSB = gadd(*pSB, vecmul(tB, uB));
    }
  return x2 == N;
}

static GEN
mkdata(long N, GEN s, long prec)
{
  long needlog, prec0, prec1, m = mt_nbthreads(), STEP = maxss(N / (m * m), 1);
  prec1 = prec0 = prec + EXTRAPRECWORD;
  needlog = get_needlog(s);
  if (needlog == 1) prec1 = powcx_prec(log2((double)N), s, prec);
  return mkvecsmalln(5, needlog, prec0, prec1, N, STEP);
}

static GEN
gp_callUp(void *E, ulong x, long prec)
{
  long n[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  n[2] = x; return gp_callprec(E, n, prec);
}

/* set *p0 and *p1 to 0 and 1 in the algebra where f takes its values */
static int
mk01(void *E, GEN (*f)(void*,ulong,long), long prec, GEN *p0, GEN *p1)
{
  *p0 = gen_0; *p1 = gen_1;
  if (!f) return 1;
  *p1 = f(E, 1, prec);
  if (is_vec_t(typ(*p1)))
  {
    long l = lg(*p1);
    if (l == 1) { *p0 = *p1 = NULL; return 0; }
    *p0 = const_vec(l-1, gen_0);
  }
  return 1;
}
static GEN
mktrivial(long both)
{
  if (!both) return cgetg(1, t_VEC);
  return mkvec2(cgetg(1,t_VEC), cgetg(1,t_VEC));
}

/* both is
 * 0: sum_{n<=N}f(n)n^s
 * 1: sum for (f,s) and (conj(f),-1-s)
 * 2: sum for (f,s) and (f,-1-s), assuming |f(n)| in {0,1} */
static GEN
dirpowerssumfun_i(ulong N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                  long both, long prec)
{
  forprime_t T;
  pari_sp av;
  GEN onef, zerf, R, RB, W, WB, S, SB, data;
  ulong x1;

  if ((f && N < 49) || (!f && N < 1000))
    return smalldirpowerssum(N, s, E, f, both, prec);
  if (!mk01(E, f, prec, &zerf, &onef)) return mktrivial(both);
  data = mkdata(N, s, prec); s = gprec_w(s, prec + EXTRAPRECWORD);
  v2unpack(dirpowsuminit(s, onef, zerf, E, f, data, both), &R, &RB);
  W = gel(R,2); WB = RB? gel(RB,2): NULL;
  av = avma; u_forprime_init(&T, lg(W), N);
  v2unpack(sumprimeloop(&T, s, N, data, zerf, W, WB, E, f), &S, &SB);
  for(x1 = 1;; x1 += step)
  {
    if (mksqfloop(N, x1, R, RB, &S, &SB))
      return both? mkvec2(S, conj_i(SB? SB: S)): S;
    (void)gc_all(av, SB? 2: 1, &S, &SB);
  }
}
GEN
dirpowerssumfun(ulong N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                long both, long prec)
{
  pari_sp av = avma;
  return gc_GEN(av, dirpowerssumfun_i(N, s, E, f, both, prec));
}

GEN
dirpowerssum(ulong N, GEN s, long both, long prec)
{ return dirpowerssumfun(N, s, NULL, NULL, both, prec); }

GEN
dirpowerssum0(GEN N, GEN s, GEN f, long both, long prec)
{
  if (typ(N) != t_INT) pari_err_TYPE("dirpowerssum", N);
  if (signe(N) <= 0) N = gen_0;
  if (!f) return dirpowerssum(itou(N), s, both, prec);
  if (typ(f) != t_CLOSURE) pari_err_TYPE("dirpowerssum", f);
  return dirpowerssumfun(itou(N), s, (void*)f, gp_callUp, both, prec);
}

GEN
parsqf_worker(GEN gk, GEN vR, GEN gN)
{
  pari_sp av = avma;
  GEN R, RB, onef, S, SB;
  long k = itou(gk), N = itou(gN), x1 = 1 + step * k;
  v2unpack(vR, &R, &RB); onef = gmael(R,1,1);
  S = SB = is_vec_t(typ(onef)) ? zerovec(lg(onef) - 1): gen_0;
  (void)mksqfloop(N, x1, R, RB, &S, &SB);
  return gc_GEN(av, v2pack(S, RB? SB: NULL));
}

static GEN
mycallvec(void *f, ulong n, long prec)
{
  GEN F = (GEN)f;
  if (!f) return gen_1;
  if (typ(F) == t_CLOSURE) return gp_callUp(f, n, prec);
  return gel(F, (n-1) % (lg(F)-1) + 1);
}

GEN
parsumprimefun_worker(GEN gk, GEN s, GEN zerf, GEN data, GEN vW, GEN f)
{
  pari_sp av = avma;
  forprime_t T;
  GEN W, WB, S;
  long k = itou(gk), sq, N = data[4], STEP = data[5];

  v2unpack(vW, &W, &WB); sq = lg(W)-1;
  if (isintzero(f)) f = NULL;
  u_forprime_init(&T, k * STEP + sq + 1, minss(N, (k + 1) * STEP + sq));
  S = sumprimeloop(&T, s, N, data, zerf, W, WB, (void*)f, mycallvec);
  return gc_GEN(av, S);
}

static GEN
vR_get_vW(GEN vR)
{
  GEN R, RB, W, WB;
  v2unpack(vR, &R, &RB); W = gel(R,2); WB = RB? gel(RB,2): NULL;
  return v2pack(W, WB);
}

static GEN
halfconj(long both, GEN V)
{ return both ? mkvec2(gel(V, 1), gconj(gel(V, 2))) : V; }

static GEN
pardirpowerssumfun_i(GEN f, ulong N, GEN s, long both, long prec)
{
  GEN worker, worker2, data, vR, onef, zerf;

  if ((f && N < 49) || (!f && N < 10000UL))
    return smalldirpowerssum(N, s, (void*)f, mycallvec, both, prec);
  if (!mk01((void*)f, mycallvec, prec, &zerf, &onef)) return mktrivial(both);
  data = mkdata(N, s, prec); s = gprec_w(s, prec + EXTRAPRECWORD);
  vR = dirpowsuminit(s, onef, zerf, (void*)f, mycallvec, data, both);
  worker = snm_closure(is_entry("_parsumprimefun_worker"),
                       mkvecn(5, s, zerf, data, vR_get_vW(vR), f? f: gen_0));
  worker2 = snm_closure(is_entry("_parsqf_worker"), mkvec2(vR, utoi(N)));
  return halfconj(both,
                  gadd(parsum(gen_0, utoipos((N-1) / data[5]), worker),
                       parsum(gen_0, utoipos(maxss((N-1) / step - 1, 0)), worker2)));
}

GEN
pardirpowerssumfun(GEN f, ulong N, GEN s, long both, long prec)
{
  pari_sp av = avma;
  return gc_GEN(av, pardirpowerssumfun_i(f, N, s, both, prec));
}
GEN
pardirpowerssum0(GEN N, GEN s, GEN f, long both, long prec)
{
  if (typ(N) != t_INT) pari_err_TYPE("pardirpowerssum", N);
  return pardirpowerssumfun(f, itou(N), s, both, prec);
}
GEN
pardirpowerssum(ulong N, GEN s, long prec)
{ return pardirpowerssumfun(NULL, N, s, 0, prec); }
