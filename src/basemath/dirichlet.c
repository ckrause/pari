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
  return gerepilecopy(av0,V);
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
  return gerepilecopy(av0,V);
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

/* does n^s require log(x) ? */
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
  return gerepilecopy(av, v);
}

static GEN
vecmulsqlv(GEN Q, GEN V)
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

/* Here N > 0 is small */
static GEN
naivedirpowerssum(long N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                  long prec)
{
  GEN V = vecpowug(N, s, prec), S;
  if (!f) S = RgV_sum(V);
  else
  {
    long n;
    S = f(E, 1, prec);
    for (n = 2; n <= N; n++) S = gadd(S, gmul(gel(V, n), f(E, n, prec)));
  }
  return Qtor(S, prec);
}

static GEN
smalldirpowerssum(long N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                  long both, long prec)
{
  GEN S = naivedirpowerssum(N, s, E, f, prec), SB, sb;
  if (!both) return S;
  sb = gconj(gsubsg(-1, s));
  SB = both==2 && gequal(s,sb)? S: gconj(naivedirpowerssum(N,sb,E,f,prec));
  return mkvec2(S, SB);
}

static GEN
dirpowsuminit(GEN s, void *E, GEN (*f)(void *, ulong, long), GEN data,
              long both, long prec)
{
  GEN onef = gel(data, 1), zervec = gel(data, 2), sqlpp = gel(data, 3);
  long sq = sqlpp[1], needlog = sqlpp[2], prec0 = sqlpp[3], prec1 = sqlpp[4];
  GEN V = cgetg(sq+1, t_VEC), W = cgetg(sq+1, t_VEC), Q = cgetg(sq+1, t_VEC);
  GEN VB = NULL, WB = NULL, QB = NULL, c2, c2B = NULL;
  GEN Q2, Q3, Q6, Q2B = NULL, Q3B = NULL, Q6B = NULL;
  GEN logp, R, RB = NULL;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  long n;
  if (both == 1 || (both == 2 && !gequal(real_i(s), gneg(ghalf))))
  { VB = cgetg(sq+1, t_VEC); WB = cgetg(sq+1, t_VEC); QB = cgetg(sq+1, t_VEC);}
  gel(V, 1) = gel(W, 1) = gel(Q, 1) = onef;
  if (VB) { gel(VB, 1) = gel(WB, 1) = gel(QB, 1) = onef; }
  c2 = gpow(gen_2, s, prec0); if (VB) c2B = ginv(gmul2n(gconj(c2), 1));
  if (f)
  {
    GEN tmp2 = f(E, 2, prec);
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
          u = needlog == 1? powcx(gp, logp, s, prec0) : mpexp(gmul(s, logp));
      }
      else if (zks) u = gpow(gp, s, prec0);
      if (zks)
      {
        if (VB) uB = gmul(ginv(gmulsg(n, gconj(u))), ks);
        u = gmul(u, ks); /* f(n) n^s */
      }
    }
    else
    {
      u = vecmul(c2, gel(V, n >> 1));
      if (VB) uB = vecmul(c2B, gel(VB, n >> 1));
    }
    if (zks)
    { /* V[n]=f(n)n^s, W[n]=sum_{i<=n} f(i)i^s, Q[n]=sum_{i<=n} f(i^2)i^2s */
      gel(V,n) = u;
      gel(W,n) = gadd(gel(W, n-1), gel(V,n));
      gel(Q,n) = gadd(gel(Q, n-1), vecsqr(gel(V,n)));
      if (VB)
      {
        gel(VB,n) = uB;
        gel(WB,n) = gadd(gel(WB,n-1), gel(VB,n));
        gel(QB,n) = gadd(gel(QB,n-1), vecsqr(gel(VB,n)));
      }
    }
    else
    {
      gel(V,n) = zervec; gel(W,n) = gel(W, n-1); gel(Q,n) = gel(Q, n-1);
      if (VB)
      {
        gel(VB,n) = zervec; gel(WB,n) = gel(WB, n-1);
        gel(QB,n) = gel(QB, n-1);
      }
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
  R = mkvecn(6, V, W, Q, Q2, Q3, Q6);
  if (VB) RB = mkvecn(6, VB, WB, QB, Q2B, Q3B, Q6B);
  return VB ? mkvec2(R, RB) : mkvec(R);
}

static GEN
dirpowsumprimeloop(ulong N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                   GEN data, GEN W, GEN WB)
{
  pari_sp av2;
  GEN zervec = gel(data, 2), S = zervec, SB = zervec, logp = NULL;
  GEN sqlpp = gel(data, 3);
  forprime_t T;
  long gp[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  long p, precp = 0, sq = sqlpp[1], needlog = sqlpp[2];
  long prec0 = sqlpp[3], prec1 = sqlpp[4];
  u_forprime_init(&T, sq + 1, N);
  av2 = avma;
  while ((p = u_forprime_next(&T)))
  {
    GEN u = NULL, ks = f ? f(E, p, prec1) : gen_1;
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
      S = gadd(S, vecmul(gel(W, N / p), gmul(ks, u)));
      if (WB)
        SB = gadd(SB, gdiv(vecmul(ks, gel(WB, N / p)), gmulsg(p, gconj(u))));
    }
    precp = p;
    if ((p & 0x1ff) == 1)
    {
      if (!logp) gerepileall(av2, SB? 2: 1, &S, &SB);
      else gerepileall(av2, SB? 3: 2, &S, &logp, &SB);
    }
  }
  return SB ? mkvec2(S, SB) : mkvec(S);
}

static GEN
dirpowsumsqfloop(long N, long x1, long x2, long sq, GEN P, GEN allvecs, GEN S,
                 GEN allvecsB, GEN SB)
{
  GEN V = gel(allvecs, 1), Q1 = gel(allvecs, 2), Q2 = gel(allvecs, 3);
  GEN Q3 = gel(allvecs, 4), Q6 = gel(allvecs, 5), Z = gel(allvecs, 6);
  GEN VB = NULL, QB = NULL, Q2B = NULL, Q3B = NULL, Q6B = NULL, ZB = NULL;
  GEN v = vecfactorsquarefreeu_coprime(x1, x2, P);
  long lv = lg(v), j;
  if (allvecsB)
  {
    VB = gel(allvecsB, 1), QB = gel(allvecsB, 2), Q2B = gel(allvecsB, 3);
    Q3B = gel(allvecsB, 4), Q6B = gel(allvecsB, 5), ZB = gel(allvecsB, 6);
  }
  for (j = 1; j < lv; j++)
    if (gel(v,j))
    {
      ulong d = x1 - 1 + j; /* squarefree, coprime to 6 */
      GEN t = smallfact(d, gel(v,j), sq, V), u;
      GEN tB = NULL, uB = NULL; /* = d^s */
      long a, b, c, e, q;
      if (!t || gequal0(t)) continue;
      if (VB) tB = vecinv(gmulsg(d, gconj(t)));
      /* warning: gives 1/conj(f(d)) d^(-1-conj(s)), equal to
         f(d) d^(-1-conj(s)) only if |f(d)|=1. */
      /* S += f(d) * d^s * Z[q] */
      q = N / d;
      if (q == 1)
      {
        S = gadd(S, t); if (VB) SB = gadd(SB, tB);
        continue;
      }
      if (q <= sq) { u = gel(Z, q); if (VB) uB = gel(ZB, q); }
      else
      {
        a = usqrt(q); b = usqrt(q / 2); c = usqrt(q / 3); e = usqrt(q / 6);
        u = gadd(gadd(gel(Q1,a), gel(Q2,b)), gadd(gel(Q3,c), gel(Q6,e)));
        if (VB)
          uB = gadd(gadd(gel(QB,a), gel(Q2B,b)), gadd(gel(Q3B,c), gel(Q6B,e)));
      }
      S = gadd(S, vecmul(t, u)); if (VB) SB = gadd(SB, vecmul(tB, uB));
    }
  return VB ? mkvec2(S, SB) : mkvec(S);
}

static GEN
dirpowsummakez(GEN V, GEN W, GEN VB, GEN WB, GEN onef, ulong sq)
{
  GEN Z = cgetg(sq+1, t_VEC), ZB = NULL;
  ulong a, b, c, e, q;
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
  return VB ? mkvec2(Z, ZB) : mkvec(Z);
}

static const long step = 2048;

/* both =
 * 0: sum_{n<=N}f(n)n^s
 * 1: sum for (f,s) and (conj(f),-1-s)
 * 2: sum for (f,s) and (f,-1-s), assuming |f(n)| in {0,1} */
GEN
dirpowerssumfun(ulong N, GEN s, void *E, GEN (*f)(void *, ulong, long),
                long both, long prec)
{
  pari_sp av = avma, av2;
  GEN P, V, W, Q, Q2, Q3, Q6, S, Z, onef, zervec;
  GEN VB = NULL, WB = NULL, QB = NULL;
  GEN Q2B = NULL, Q3B = NULL, Q6B = NULL, SB = NULL, ZB = NULL;
  GEN R, RS, data, allvecs, allvecsB = NULL;
  ulong x1, sq;
  long prec0, prec1, needlog;

  if ((f && N < 49) || (!f && N < 1000))
  {
    if (!N)
    {
      if (!f) return gen_0;
      return gerepileupto(av, gmul(gen_0, f(E, 1, prec)));
    }
    return gerepilecopy(av, smalldirpowerssum(N, s, E, f, both, prec));
  }
  onef = f ? f(E, 1, prec) : gen_1;
  zervec = gmul(gen_0, onef);
  sq = usqrt(N);
  prec1 = prec0 = prec + EXTRAPREC64;
  s = gprec_w(s, prec0);
  needlog = get_needlog(s);
  if (needlog == 1) prec1 = powcx_prec(log2((double)N), s, prec);
  data = mkvec3(onef, zervec, mkvecsmall4(sq, needlog, prec0, prec1));
  RS = dirpowsuminit(s, E, f, data, both, prec);
  R = gel(RS, 1); V = gel(R, 1); W = gel(R, 2); Q = gel(R, 3);
  Q2 = gel(R, 4); Q3 = gel(R, 5); Q6 = gel(R, 6);
  if (lg(RS) > 2)
  {
    GEN RB = gel(RS, 2);
    VB = gel(RB, 1); WB = gel(RB, 2); QB = gel(RB, 3);
    Q2B = gel(RB, 4); Q3B = gel(RB, 5); Q6B = gel(RB, 6);
  }
  RS = dirpowsumprimeloop(N, s, E, f, data, W, WB);
  S = gel(RS, 1); if (VB) SB = gel(RS, 2);
  RS = dirpowsummakez(V, W, VB, WB, onef, sq);
  Z = gel(RS, 1); if (VB) ZB = gel(RS, 2);
  P = mkvecsmall2(2, 3);
  allvecs = mkvecn(6, V, Q, Q2, Q3, Q6, Z);
  if (VB) allvecsB = mkvecn(6, VB, QB, Q2B, Q3B, Q6B, ZB);
  av2 = avma;
  for(x1 = 1;; x1 += step)
  { /* beware overflow, fuse last two bins (avoid a tiny remainder) */
    ulong x2 = (N >= 2*step && N - 2*step >= x1)? x1-1 + step: N;
    RS = dirpowsumsqfloop(N, x1, x2, sq, P, allvecs, S, allvecsB, SB);
    S = gel(RS, 1); if (VB) SB = gel(RS, 2);
    if (x2 == N) break;
    gerepileall(av2, SB? 2: 1, &S, &SB);
  }
  if (both == 0) return gerepileupto(av, S);
  return gerepilecopy(av, mkvec2(S, gconj(VB? SB: S)));
}

GEN
dirpowerssum(ulong N, GEN s, long both, long prec)
{ return dirpowerssumfun(N, s, NULL, NULL, both, prec); }

static GEN
gp_callUp(void *E, ulong x, long prec)
{
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  court[2] = x; return gp_callprec(E, court, prec);
}

GEN
dirpowerssum0(GEN N, GEN s, GEN f, long both, long prec)
{
  if (typ(N) != t_INT) pari_err_TYPE("dirpowerssum", N);
  if (signe(N) <= 0) N = gen_0;
  if (!f) return dirpowerssum(itou(N), s, both, prec);
  if (typ(f) != t_CLOSURE) pari_err_TYPE("dirpowerssum", f);
  return dirpowerssumfun(itou(N), s, (void*)f, gp_callUp, both, prec);
}

/*******************************************************************/
/*                     Parallel dirpowerssumfun                    */
/*******************************************************************/
/* f is a totally multiplicative function of modulus 0 or 1
 * (essentially a Dirichlet character). Compute simultaneously
 * sum_{0 < n <= N} f(n)n^s and sum_{0 < n <= N} f(n)n^{-1-conj(s)}
 * Warning: s is conjugated, but not f. Main application for Riemann-Siegel,
 * where we need R(chi,s) and conj(R(chi,1-conj(s))). */

static GEN
mycallvec(GEN f, ulong n, long prec)
{
  if (typ(f) == t_CLOSURE) return gp_callUp((void*)f, n, prec);
  return gel(f, (n-1) % (lg(f)-1) + 1);
}

static GEN
_smalldirpowerssum(long N, GEN s, long fl, long prec)
{
  GEN vg = vecpowug(N, s, prec), S1 = _Qtor(RgV_sum(vg), prec);
  long n;
  if (!fl) return mkvec2(S1, S1);
  for (n = 1; n <= N; n++) gel(vg, n) = ginv(gmulsg(n, gconj(gel(vg, n))));
  return mkvec2(S1, _Qtor(RgV_sum(vg), prec));
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

GEN
parsqfboth_worker(GEN gk, GEN vZ, GEN vVQ, GEN vV, GEN P, GEN Nsq)
{
  pari_sp av2 = avma;
  GEN Z1 = gel(vZ, 1), Z2 = gel(vZ, 2), V1 = gel(vV, 1), V2 = gel(vV, 2);
  GEN VQ1 = gel(vVQ, 1), VQN, v, S, SB;
  GEN Q1 = gel(VQ1, 1), Q2 = gel(VQ1, 2), Q3 = gel(VQ1, 3), Q6 = gel(VQ1, 4);
  GEN QB = NULL, Q2B = NULL, Q3B = NULL, Q6B = NULL;
  long k = itos(gk), N = Nsq[1];
  long x1 = 1 + step * k, x2, j, lv, fl = !gcmp0(V2);
  ulong sq = Nsq[2];
  if (typ(gel(V1, 1)) == t_VEC)
  { long lvv = lg(gel(V1, 1)) - 1; S = zerovec(lvv); SB = zerovec(lvv); }
  else { S = gen_0; SB = gen_0; }
  if (fl)
  { VQN = gel(vVQ, 2); QB = gel(VQN, 1); Q2B = gel(VQN, 2);
    Q3B = gel(VQN, 3); Q6B = gel(VQN, 4); }
  /* beware overflow, fuse last two bins (avoid a tiny remainder) */
  x2 = (N >= 2*step && N - 2*step >= x1)? x1 - 1 + step: N;

  v = vecfactorsquarefreeu_coprime(x1, x2, P);
  lv = lg(v);
  for (j = 1; j < lv; j++)
    if (gel(v,j))
    {
      ulong d = x1 - 1 + j; /* squarefree, coprime to 6 */
      GEN t = smallfact(d, gel(v,j), sq, V1), u;
      GEN tB = NULL, uB = NULL; /* = f(d) d^s */
      ulong a, b, c, e, q;
      if (!t || gequal0(t)) continue;
      if (fl) tB = vecinv(gmulsg(d, gconj(t)));
      /* warning: gives 1/conj(f(d)) d^(-1-conj(s)), equal to
         f(d) d^(-1-conj(s)) only if |f(d)|=1. */
      /* S += f(d) d^s * Z[q] */
      q = N / d;
      if (q == 1)
      {
        S = gadd(S, t); if (fl) SB = gadd(SB, tB);
        continue;
      }
      if (q <= sq) { u = gel(Z1, q); if (fl) uB = gel(Z2, q); }
      else
      {
        a = usqrt(q); b = usqrt(q / 2); c = usqrt(q / 3); e = usqrt(q / 6);
        u = gadd(gadd(gel(Q1,a), gel(Q2,b)), gadd(gel(Q3,c), gel(Q6,e)));
        if (fl)
          uB = gadd(gadd(gel(QB,a), gel(Q2B,b)), gadd(gel(Q3B,c), gel(Q6B,e)));
      }
      S = gadd(S, vecmul(t, u)); if (fl) SB = gadd(SB, vecmul(tB, uB));
    }
  return gerepilecopy(av2, mkvec2(S, SB));
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
  GEN S = real_0(prec);
  ulong n;
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
  if (isscal != 1 || typ(V) != t_VEC) return V;
  switch (lg(V))
  {
    case 2: return gel(V,1);
    case 3: return mkvec2(getscal(gel(V,1), 1), getscal(gel(V,2), 1));
  }
  pari_err_TYPE("getscal", V);
  return NULL; /*LCOV_EXCL_LINE*/
}

GEN
pardirpowerssumfun(GEN f, ulong N, GEN s, long both, long prec)
{
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
  fl = both && !gequal(real_i(s), gneg(ghalf));
  if (f && N < 49)
    return gerepilecopy(av, getscal(smalldirpowerssumfunvec(f, N, s, fl, prec), isscal));
  if (!f && N < 10000UL)
    return gerepilecopy(av, _smalldirpowerssum(N, s, fl, prec));
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
  S1 = S2 = typ(zervec) == t_VEC? const_vec(lv, re0): re0;
  RES = mkvec2(S1, S2);
  {
    GEN fspec = f ? f : gen_0;
    long m = mt_nbthreads();
    long STEP = maxss(N / (m * m), 1);
    GEN VS = mkvecsmalln(5, N, sq, STEP, prec0, prec1);
    GEN FUN = snm_closure(is_entry("_parsumprimeWfunboth_worker"),
                          mkvec5(s, W1, W2, fspec, VS));
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
    GEN vQ1 = mkvec4(Q1, Q2, Q3, Q6);
    GEN vQ2 = fl? mkvec4(QN, Q2N, Q3N, Q6N): gen_0;
    GEN worker = snm_closure(is_entry("_parsqfboth_worker"),
                   mkvec5(mkvec2(Z1, Z2), mkvec2(vQ1, vQ2), mkvec2(V1, V2),
                   P, mkvecsmall2(N, sq)));
    RES = gadd(RES, parsum(gen_0, utoipos(maxss((N-1) / step - 1, 0)), worker));
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
