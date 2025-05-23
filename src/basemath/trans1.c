/* Copyright (C) 2000  The PARI group.

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
/**                   TRANSCENDENTAL FUNCTIONS                     **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_trans

#ifdef LONG_IS_64BIT
static const long SQRTVERYBIGINT = 3037000500L; /* ceil(sqrt(LONG_MAX)) */
#else
static const long SQRTVERYBIGINT = 46341L;
#endif

static THREAD GEN gcatalan, geuler, glog2, gpi;
void
pari_init_floats(void)
{
  gcatalan = geuler = gpi = zetazone = bernzone = glog2 = eulerzone = NULL;
}

void
pari_close_floats(void)
{
  guncloneNULL(gcatalan);
  guncloneNULL(geuler);
  guncloneNULL(gpi);
  guncloneNULL(glog2);
  guncloneNULL(zetazone);
  guncloneNULL_deep(bernzone);
  guncloneNULL_deep(eulerzone);
}

/********************************************************************/
/**                   GENERIC BINARY SPLITTING                     **/
/**                    (Haible, Papanikolaou)                      **/
/********************************************************************/
void
abpq_init(struct abpq *A, long n)
{
  A->a = (GEN*)new_chunk(n+1);
  A->b = (GEN*)new_chunk(n+1);
  A->p = (GEN*)new_chunk(n+1);
  A->q = (GEN*)new_chunk(n+1);
}
static GEN
mulii3(GEN a, GEN b, GEN c) { return mulii(mulii(a,b),c); }

/* T_{n1,n1+1} */
static GEN
T2(struct abpq *A, long n1)
{
  GEN u = mulii3(A->a[n1], A->b[n1+1], A->q[n1+1]);
  GEN v = mulii3(A->b[n1], A->a[n1+1], A->p[n1+1]);
  return mulii(A->p[n1], addii(u, v));
}

/* assume n2 > n1. Compute sum_{n1 <= n < n2} a/b(n) p/q(n1)... p/q(n) */
void
abpq_sum(struct abpq_res *r, long n1, long n2, struct abpq *A)
{
  struct abpq_res L, R;
  GEN u1, u2;
  pari_sp av;
  long n;
  switch(n2 - n1)
  {
    GEN b, q;
    case 1:
      r->P = A->p[n1];
      r->Q = A->q[n1];
      r->B = A->b[n1];
      r->T = mulii(A->a[n1], A->p[n1]);
      return;
    case 2:
      r->P = mulii(A->p[n1], A->p[n1+1]);
      r->Q = mulii(A->q[n1], A->q[n1+1]);
      r->B = mulii(A->b[n1], A->b[n1+1]);
      av = avma;
      r->T = gc_INT(av, T2(A, n1));
      return;

    case 3:
      q = mulii(A->q[n1+1], A->q[n1+2]);
      b = mulii(A->b[n1+1], A->b[n1+2]);
      r->P = mulii3(A->p[n1], A->p[n1+1], A->p[n1+2]);
      r->Q = mulii(A->q[n1], q);
      r->B = mulii(A->b[n1], b);
      av = avma;
      u1 = mulii3(b, q, A->a[n1]);
      u2 = mulii(A->b[n1], T2(A, n1+1));
      r->T = gc_INT(av, mulii(A->p[n1], addii(u1, u2)));
      return;
  }

  av = avma;
  n = (n1 + n2) >> 1;
  abpq_sum(&L, n1, n, A);
  abpq_sum(&R, n, n2, A);

  r->P = mulii(L.P, R.P);
  r->Q = mulii(L.Q, R.Q);
  r->B = mulii(L.B, R.B);
  u1 = mulii3(R.B, R.Q, L.T);
  u2 = mulii3(L.B, L.P, R.T);
  r->T = addii(u1,u2);
  set_avma(av);
  r->P = icopy(r->P);
  r->Q = icopy(r->Q);
  r->B = icopy(r->B);
  r->T = icopy(r->T);
}

/********************************************************************/
/**                                                                **/
/**                               PI                               **/
/**                                                                **/
/********************************************************************/
/* replace *old clone by c. Protect against SIGINT */
static void
swap_clone(GEN *old, GEN c)
{ GEN tmp = *old; *old = c; guncloneNULL(tmp); }

/*                         ----
 *  53360 (640320)^(1/2)   \    (6n)! (545140134 n + 13591409)
 *  -------------------- = /    ------------------------------
 *        Pi               ----   (n!)^3 (3n)! (-640320)^(3n)
 *                         n>=0
 *
 * Ramanujan's formula + binary splitting */
static GEN
pi_ramanujan(long prec)
{
  const ulong B = 545140134, A = 13591409, C = 640320;
  const double alpha2 = 47.11041314; /* 3log(C/12) / log(2) */
  long n, nmax, prec2;
  struct abpq_res R;
  struct abpq S;
  GEN D, u;

  nmax = (long)(1 + prec2nbits(prec)/alpha2);
#ifdef LONG_IS_64BIT
  D = utoipos(10939058860032000UL); /* C^3/24 */
#else
  D = uutoi(2546948UL,495419392UL);
#endif
  abpq_init(&S, nmax);
  S.a[0] = utoipos(A);
  S.b[0] = S.p[0] = S.q[0] = gen_1;
  for (n = 1; n <= nmax; n++)
  {
    S.a[n] = addiu(muluu(B, n), A);
    S.b[n] = gen_1;
    S.p[n] = mulis(muluu(6*n-5, 2*n-1), 1-6*n);
    S.q[n] = mulii(sqru(n), muliu(D,n));
  }
  abpq_sum(&R, 0, nmax, &S); prec2 = prec+EXTRAPREC64;
  u = itor(muliu(R.Q,C/12), prec2);
  return rtor(mulrr(divri(u, R.T), sqrtr_abs(utor(C,prec2))), prec);
}

#if 0 /* Much slower than binary splitting at least up to prec = 10^8 */
/* Gauss - Brent-Salamin AGM iteration */
static GEN
pi_brent_salamin(long prec)
{
  GEN A, B, C;
  pari_sp av2;
  long i, G;

  G = - prec2nbits(prec);
  incrprec(prec);

  A = real2n(-1, prec);
  B = sqrtr_abs(A); /* = 1/sqrt(2) */
  setexpo(A, 0);
  C = real2n(-2, prec); av2 = avma;
  for (i = 0;; i++)
  {
    GEN y, a, b, B_A = subrr(B, A);
    pari_sp av3 = avma;
    if (expo(B_A) < G) break;
    a = addrr(A,B); shiftr_inplace(a, -1);
    b = mulrr(A,B);
    affrr(a, A);
    affrr(sqrtr_abs(b), B); set_avma(av3);
    y = sqrr(B_A); shiftr_inplace(y, i - 2);
    affrr(subrr(C, y), C); set_avma(av2);
  }
  shiftr_inplace(C, 2);
  return divrr(sqrr(addrr(A,B)), C);
}
#endif

GEN
constpi(long prec)
{
  pari_sp av;
  GEN tmp;
  if (gpi && realprec(gpi) >= prec) return gpi;

  av = avma;
  tmp = gclone(pi_ramanujan(prec));
  swap_clone(&gpi,tmp);
  return gc_const(av, gpi);
}

GEN
mppi(long prec) { return rtor(constpi(prec), prec); }

/* Pi * 2^n */
GEN
Pi2n(long n, long prec)
{
  GEN x = mppi(prec); shiftr_inplace(x, n);
  return x;
}

/* I * Pi * 2^n */
GEN
PiI2n(long n, long prec) { retmkcomplex(gen_0, Pi2n(n, prec)); }

/* 2I * Pi */
GEN
PiI2(long prec) { return PiI2n(1, prec); }

/********************************************************************/
/**                                                                **/
/**                       EULER CONSTANT                           **/
/**                                                                **/
/********************************************************************/

GEN
consteuler(long prec)
{
  GEN u,v,a,b,tmpeuler;
  long l, n1, n, k, x;
  pari_sp av1, av2;

  if (geuler && realprec(geuler) >= prec) return geuler;

  av1 = avma; tmpeuler = cgetr_block(prec);

  incrprec(prec);

  l = prec+EXTRAPREC64; x = (long) (1 + prec2nbits_mul(l, M_LN2/4));
  a = utor(x,l); u=logr_abs(a); setsigne(u,-1); affrr(u,a);
  b = real_1(l);
  v = real_1(l);
  n = (long)(1+3.591*x); /* z=3.591: z*[ ln(z)-1 ]=1 */
  n1 = minss(n, SQRTVERYBIGINT);
  if (x < SQRTVERYBIGINT)
  {
    ulong xx = x*x;
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulur(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); set_avma(av2);
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulur(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); set_avma(av2);
    }
  }
  else
  {
    GEN xx = sqru(x);
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulir(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); set_avma(av2);
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulir(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); set_avma(av2);
    }
  }
  affrr(divrr(u,v),tmpeuler);
  swap_clone(&geuler,tmpeuler);
  return gc_const(av1, geuler);
}

GEN
mpeuler(long prec) { return rtor(consteuler(prec), prec); }

/********************************************************************/
/**                                                                **/
/**                       CATALAN CONSTANT                         **/
/**                                                                **/
/********************************************************************/
/*        inf  256^i (580i^2 - 184i + 15) (2i)!^3 (3i)!^2
 * 64 G = SUM  ------------------------------------------
 *        i=1             i^3 (2i-1) (6i)!^2           */
static GEN
catalan(long prec)
{
  long i, nmax = 1 + prec2nbits(prec) / 7.509; /* / log2(729/4) */
  struct abpq_res R;
  struct abpq A;
  GEN u;
  abpq_init(&A, nmax);
  A.a[0] = gen_0; A.b[0] = A.p[0] = A.q[0] = gen_1;
  for (i = 1; i <= nmax; i++)
  {
    A.a[i] = addiu(muluu(580*i - 184, i), 15);
    A.b[i] = muliu(powuu(i, 3), 2*i - 1);
    A.p[i] = mului(64*i-32, powuu(i,3));
    A.q[i] = sqri(muluu(6*i - 1, 18*i - 15));
  }
  abpq_sum(&R, 0, nmax, &A);
  u = rdivii(R.T, mulii(R.B,R.Q),prec);
  shiftr_inplace(u, -6); return u;
}

GEN
constcatalan(long prec)
{
  pari_sp av = avma;
  GEN tmp;
  if (gcatalan && realprec(gcatalan) >= prec) return gcatalan;
  tmp = gclone(catalan(prec));
  swap_clone(&gcatalan,tmp);
  return gc_const(av, gcatalan);
}

GEN
mpcatalan(long prec) { return rtor(constcatalan(prec), prec); }

/********************************************************************/
/**                                                                **/
/**          TYPE CONVERSION FOR TRANSCENDENTAL FUNCTIONS          **/
/**                                                                **/
/********************************************************************/
static GEN
transvec(GEN (*f)(GEN,long), GEN x, long prec)
{ pari_APPLY_same(f(gel(x,i), prec)); }
static GEN
transvecgen(void *E, GEN (*f)(void *,GEN,long), GEN x, long prec)
{ pari_APPLY_same(f(E, gel(x,i), prec)); }

GEN
trans_eval(const char *fun, GEN (*f)(GEN,long), GEN x, long prec)
{
  pari_sp av = avma;
  if (prec < LOWDEFAULTPREC) pari_err_BUG("trans_eval [prec < 3]");
  switch(typ(x))
  {
    case t_INT:    x = f(itor(x,prec),prec); break;
    case t_FRAC:   x = f(fractor(x, prec),prec); break;
    case t_QUAD:   x = f(quadtofp(x,prec),prec); break;
    case t_POLMOD: x = transvec(f, polmod_to_embed(x,prec), prec); break;
    case t_VEC:
    case t_COL:
    case t_MAT: return transvec(f, x, prec);
    default: pari_err_TYPE(fun,x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  return gc_upto(av, x);
}

GEN
trans_evalgen(const char *fun, void *E, GEN (*f)(void*,GEN,long),
              GEN x, long prec)
{
  pari_sp av = avma;
  if (prec < LOWDEFAULTPREC) pari_err_BUG("trans_eval [prec < 3]");
  switch(typ(x))
  {
    case t_INT:    x = f(E, itor(x,prec),prec); break;
    case t_FRAC:   x = f(E, fractor(x, prec),prec); break;
    case t_QUAD:   x = f(E, quadtofp(x,prec),prec); break;
    case t_POLMOD: x = transvecgen(E, f, polmod_to_embed(x,prec), prec); break;
    case t_VEC:
    case t_COL:
    case t_MAT: return transvecgen(E, f, x, prec);
    default: pari_err_TYPE(fun,x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  return gc_upto(av, x);
}

/*******************************************************************/
/*                                                                 */
/*                            POWERING                             */
/*                                                                 */
/*******************************************************************/
/* x a t_REAL 0, return exp(x) */
static GEN
mpexp0(GEN x)
{
  long e = expo(x);
  return e >= 0? real_0_bit(e): real_1_bit(-e);
}
static GEN
powr0(GEN x)
{ return signe(x)? real_1(realprec(x)): mpexp0(x); }

/* assume typ(x) = t_VEC */
static int
is_ext_qfr(GEN x)
{ return lg(x) == 3 && typ(gel(x,1)) == t_QFB && !qfb_is_qfi(gel(x,1))
                    && typ(gel(x,2)) == t_REAL; }

/* x t_POL or t_SER, return scalarpol(Rg_get_1(x)) */
static GEN
scalarpol_get_1(GEN x)
{
  GEN y = cgetg(3,t_POL);
  y[1] = evalvarn(varn(x)) | evalsigne(1);
  gel(y,2) = Rg_get_1(x); return y;
}
/* to be called by the generic function gpowgs(x,s) when s = 0 */
static GEN
gpowg0(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_PADIC:
      return gen_1;

    case t_QUAD: x++; /*fall through*/
    case t_COMPLEX: {
      pari_sp av = avma;
      GEN a = gpowg0(gel(x,1));
      GEN b = gpowg0(gel(x,2));
      if (a == gen_1) return b;
      if (b == gen_1) return a;
      return gc_upto(av, gmul(a,b));
    }
    case t_INTMOD:
      y = cgetg(3,t_INTMOD);
      gel(y,1) = icopy(gel(x,1));
      gel(y,2) = is_pm1(gel(x,1))? gen_0: gen_1;
      return y;

    case t_FFELT: return FF_1(x);

    case t_POLMOD:
      retmkpolmod(scalarpol_get_1(gel(x,1)), gcopy(gel(x,1)));

    case t_RFRAC:
      return scalarpol_get_1(gel(x,2));
    case t_POL: case t_SER:
      return scalarpol_get_1(x);

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (lx != lgcols(x)) pari_err_DIM("gpow");
      y = matid(lx-1);
      for (i=1; i<lx; i++) gcoeff(y,i,i) = gpowg0(gcoeff(x,i,i));
      return y;
    case t_VEC: if (!is_ext_qfr(x)) break;
    /* fall through handle extended t_QFB */
    case t_QFB: return qfbpow(x, gen_0);
    case t_VECSMALL: return identity_perm(lg(x) - 1);
  }
  pari_err_TYPE("gpow",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
_sqr(void *data /* ignored */, GEN x) { (void)data; return gsqr(x); }
static GEN
_mul(void *data /* ignored */, GEN x, GEN y) { (void)data; return gmul(x,y); }
static GEN
_one(void *x) { return gpowg0((GEN) x); }
static GEN
_sqri(void *data /* ignored */, GEN x) { (void)data; return sqri(x); }
static GEN
_muli(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulii(x,y); }
static GEN
_sqrr(void *data /* ignored */, GEN x) { (void)data; return sqrr(x); }
static GEN
_mulr(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulrr(x,y); }
static GEN
_oner(void *data /* prec */) { return real_1( *(long*) data); }

/* INTEGER POWERING (a^n for integer a != 0 and integer n > 0)
 *
 * Use left shift binary algorithm (RS is wasteful: multiplies big numbers,
 * with LS one of them is the base, hence small). Sign of result is set
 * to s (= 1,-1). Makes life easier for caller, which otherwise might do a
 * setsigne(gen_1 / gen_m1) */
static GEN
powiu_sign(GEN a, ulong N, long s)
{
  pari_sp av;
  GEN y;

  if (lgefint(a) == 3)
  { /* easy if |a| < 3 */
    ulong q = a[2];
    if (q == 1) return (s>0)? gen_1: gen_m1;
    if (q == 2) { a = int2u(N); setsigne(a,s); return a; }
    q = upowuu(q, N);
    if (q) return s>0? utoipos(q): utoineg(q);
  }
  if (N <= 2) {
    if (N == 2) return sqri(a);
    a = icopy(a); setsigne(a,s); return a;
  }
  av = avma;
  y = gen_powu_i(a, N, NULL, &_sqri, &_muli);
  setsigne(y,s); return gc_INT(av, y);
}
/* a^n */
GEN
powiu(GEN a, ulong n)
{
  long s;
  if (!n) return gen_1;
  s = signe(a);
  if (!s) return gen_0;
  return powiu_sign(a, n, (s < 0 && odd(n))? -1: 1);
}
GEN
powis(GEN a, long n)
{
  long s;
  GEN t, y;
  if (n >= 0) return powiu(a, n);
  s = signe(a);
  if (!s) pari_err_INV("powis",gen_0);
  t = (s < 0 && odd(n))? gen_m1: gen_1;
  if (is_pm1(a)) return t;
  /* n < 0, |a| > 1 */
  y = cgetg(3,t_FRAC);
  gel(y,1) = t;
  gel(y,2) = powiu_sign(a, -n, 1); /* force denominator > 0 */
  return y;
}
GEN
powuu(ulong p, ulong N)
{
  pari_sp av;
  ulong pN;
  GEN y;
  if (!p) return gen_0;
  if (N <= 2)
  {
    if (N == 2) return sqru(p);
    if (N == 1) return utoipos(p);
    return gen_1;
  }
  pN = upowuu(p, N);
  if (pN) return utoipos(pN);
  if (p == 2) return int2u(N);
  av = avma;
  y = gen_powu_i(utoipos(p), N, NULL, &_sqri, &_muli);
  return gc_INT(av, y);
}

/* return 0 if overflow */
static ulong
usqru(ulong p) { return p & HIGHMASK? 0: p*p; }
ulong
upowuu(ulong p, ulong k)
{
#ifdef LONG_IS_64BIT
  const ulong CUTOFF3 = 2642245;
  const ulong CUTOFF4 = 65535;
  const ulong CUTOFF5 = 7131;
  const ulong CUTOFF6 = 1625;
  const ulong CUTOFF7 = 565;
  const ulong CUTOFF8 = 255;
  const ulong CUTOFF9 = 138;
  const ulong CUTOFF10 = 84;
  const ulong CUTOFF11 = 56;
  const ulong CUTOFF12 = 40;
  const ulong CUTOFF13 = 30;
  const ulong CUTOFF14 = 23;
  const ulong CUTOFF15 = 19;
  const ulong CUTOFF16 = 15;
  const ulong CUTOFF17 = 13;
  const ulong CUTOFF18 = 11;
  const ulong CUTOFF19 = 10;
  const ulong CUTOFF20 =  9;
#else
  const ulong CUTOFF3 = 1625;
  const ulong CUTOFF4 =  255;
  const ulong CUTOFF5 =   84;
  const ulong CUTOFF6 =   40;
  const ulong CUTOFF7 =   23;
  const ulong CUTOFF8 =   15;
  const ulong CUTOFF9 =   11;
  const ulong CUTOFF10 =   9;
  const ulong CUTOFF11 =   7;
  const ulong CUTOFF12 =   6;
  const ulong CUTOFF13 =   5;
  const ulong CUTOFF14 =   4;
  const ulong CUTOFF15 =   4;
  const ulong CUTOFF16 =   3;
  const ulong CUTOFF17 =   3;
  const ulong CUTOFF18 =   3;
  const ulong CUTOFF19 =   3;
  const ulong CUTOFF20 =   3;
#endif

  if (p <= 2)
  {
    if (p < 2) return p;
    return k < BITS_IN_LONG? 1UL<<k: 0;
  }
  switch(k)
  {
    ulong p2, p3, p4, p5, p8;
    case 0:  return 1;
    case 1:  return p;
    case 2:  return usqru(p);
    case 3:  if (p > CUTOFF3) return 0; return p*p*p;
    case 4:  if (p > CUTOFF4) return 0; p2=p*p; return p2*p2;
    case 5:  if (p > CUTOFF5) return 0; p2=p*p; return p2*p2*p;
    case 6:  if (p > CUTOFF6) return 0; p2=p*p; return p2*p2*p2;
    case 7:  if (p > CUTOFF7) return 0; p2=p*p; return p2*p2*p2*p;
    case 8:  if (p > CUTOFF8) return 0; p2=p*p; p4=p2*p2; return p4*p4;
    case 9:  if (p > CUTOFF9) return 0; p2=p*p; p4=p2*p2; return p4*p4*p;
    case 10: if (p > CUTOFF10)return 0; p2=p*p; p4=p2*p2; return p4*p4*p2;
    case 11: if (p > CUTOFF11)return 0; p2=p*p; p4=p2*p2; return p4*p4*p2*p;
    case 12: if (p > CUTOFF12)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4;
    case 13: if (p > CUTOFF13)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4*p;
    case 14: if (p > CUTOFF14)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4*p2;
    case 15: if (p > CUTOFF15)return 0;
      p2=p*p; p3=p2*p; p5=p3*p2; return p5*p5*p5;
    case 16: if (p > CUTOFF16)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p8*p8;
    case 17: if (p > CUTOFF17)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p*p8*p8;
    case 18: if (p > CUTOFF18)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p2*p8*p8;
    case 19: if (p > CUTOFF19)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p*p2*p8*p8;
    case 20: if (p > CUTOFF20)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p4*p8*p8;
  }
#ifdef LONG_IS_64BIT
  switch(p)
  {
    case 3: if (k > 40) return 0;
      break;
    case 4: if (k > 31) return 0;
      return 1UL<<(2*k);
    case 5: if (k > 27) return 0;
      break;
    case 6: if (k > 24) return 0;
      break;
    case 7: if (k > 22) return 0;
      break;
    default: return 0;
  }
  /* no overflow */
  {
    ulong q = upowuu(p, k >> 1);
    q *= q ;
    return odd(k)? q*p: q;
  }
#else
  return 0;
#endif
}

GEN
upowers(ulong x, long n)
{
  long i;
  GEN p = cgetg(n + 2, t_VECSMALL);
  uel(p,1) = 1; if (n == 0) return p;
  uel(p,2) = x;
  for (i = 3; i <= n; i++)
    uel(p,i) = uel(p,i-1)*x;
  return p;
}

typedef struct {
  long prec, a;
  GEN (*sqr)(GEN);
  GEN (*mulug)(ulong,GEN);
} sr_muldata;

static GEN
_rpowuu_sqr(void *data, GEN x)
{
  sr_muldata *D = (sr_muldata *)data;
  if (typ(x) == t_INT && lg2prec(lgefint(x)) >= D->prec)
  { /* switch to t_REAL */
    D->sqr   = &sqrr;
    D->mulug = &mulur; x = itor(x, D->prec);
  }
  return D->sqr(x);
}

static GEN
_rpowuu_msqr(void *data, GEN x)
{
  GEN x2 = _rpowuu_sqr(data, x);
  sr_muldata *D = (sr_muldata *)data;
  return D->mulug(D->a, x2);
}

/* return a^n as a t_REAL of precision prec. Assume a > 0, n > 0 */
GEN
rpowuu(ulong a, ulong n, long prec)
{
  pari_sp av;
  GEN y, z;
  sr_muldata D;

  if (a == 1) return real_1(prec);
  if (a == 2) return real2n(n, prec);
  if (n == 1) return utor(a, prec);
  z = cgetr(prec);
  av = avma;
  D.sqr   = &sqri;
  D.mulug = &mului;
  D.prec = prec;
  D.a = (long)a;
  y = gen_powu_fold_i(utoipos(a), n, (void*)&D, &_rpowuu_sqr, &_rpowuu_msqr);
  affgr(y, z); return gc_const(av,z);
}

GEN
powrs(GEN x, long n)
{
  pari_sp av = avma;
  GEN y;
  if (!n) return powr0(x);
  y = gen_powu_i(x, (ulong)labs(n), NULL, &_sqrr, &_mulr);
  if (n < 0) y = invr(y);
  return gc_leaf(av,y);
}
GEN
powru(GEN x, ulong n)
{
  pari_sp av = avma;
  GEN y;
  if (!n) return powr0(x);
  y = gen_powu_i(x, n, NULL, &_sqrr, &_mulr);
  return gc_leaf(av,y);
}

GEN
powersr(GEN x, long n)
{
  long prec = realprec(x);
  return gen_powers(x, n, 1, &prec, &_sqrr, &_mulr, &_oner);
}

/* x^(s/2), assume x t_REAL */
GEN
powrshalf(GEN x, long s)
{
  if (s & 1) return sqrtr(powrs(x, s));
  return powrs(x, s>>1);
}
/* x^(s/2), assume x t_REAL */
GEN
powruhalf(GEN x, ulong s)
{
  if (s & 1) return sqrtr(powru(x, s));
  return powru(x, s>>1);
}
/* x^(n/d), assume x t_REAL, return t_REAL */
GEN
powrfrac(GEN x, long n, long d)
{
  long z;
  if (!n) return powr0(x);
  z = cgcd(n, d); if (z > 1) { n /= z; d /= z; }
  if (d == 1) return powrs(x, n);
  x = powrs(x, n);
  if (d == 2) return sqrtr(x);
  return sqrtnr(x, d);
}

/* assume x != 0 */
static GEN
pow_monome(GEN x, long n)
{
  long i, d, dx = degpol(x);
  GEN A, b, y;

  if (n < 0) { n = -n; y = cgetg(3, t_RFRAC); } else y = NULL;

  if (HIGHWORD(dx) || HIGHWORD(n))
  {
    LOCAL_HIREMAINDER;
    d = (long)mulll((ulong)dx, (ulong)n);
    if (hiremainder || (d &~ LGBITS)) d = LGBITS; /* overflow */
    d += 2;
  }
  else
    d = dx*n + 2;
  if ((d + 1) & ~LGBITS) pari_err(e_OVERFLOW,"pow_monome [degree]");
  A = cgetg(d+1, t_POL); A[1] = x[1];
  for (i=2; i < d; i++) gel(A,i) = gen_0;
  b = gpowgs(gel(x,dx+2), n); /* not memory clean if (n < 0) */
  if (!y) y = A;
  else {
    GEN c = denom_i(b);
    gel(y,1) = c; if (c != gen_1) b = gmul(b,c);
    gel(y,2) = A;
  }
  gel(A,d) = b; return y;
}

/* q*p^v */
static GEN
mulpowu(GEN q, GEN p, ulong v)
{
  pari_sp av = avma;
  if (v == 0) return icopy(q);
  return gc_INT(av, mulii(q, powiu(p,v)));
}

/* x t_PADIC, n != 0 */
static GEN
powps(GEN x, long n)
{
  long e = valp(x), v;
  GEN p = padic_p(x);

  if (e)
  {
    pari_sp av = avma;
    e = itos_or_0(mulss(e, n));
    if (!e) pari_err_OVERFLOW("valp()");
    set_avma(av);
  }
  if (!signe(padic_u(x))) {
    if (n < 0) pari_err_INV("powps",x);
    return zeropadic(p, e);
  }
  v = z_pval(n, p);
  if (v && precp(x) == 1 && absequaliu(p, 2)) v++;
  retmkpadic_i(Fp_pows(padic_u(x), n, _pd), icopy(p),
               mulpowu(padic_pd(x), p, v), e, precp(x) + v);
}
/* x t_PADIC */
static GEN
powp(GEN x, GEN n)
{
  GEN p = padic_p(x);
  long v;

  if (valp(x)) pari_err_OVERFLOW("valp()");
  if (!signe(padic_u(x))) {
    if (signe(n) < 0) pari_err_INV("powp",x);
    return zeropadic(p, 0);
  }
  v = Z_pval(n, p);
  retmkpadic_i(Fp_pow(padic_u(x), n, _pd), icopy(p),
               mulpowu(padic_pd(x), p, v), 0, precp(x) + v);
}
static GEN
pow_polmod(GEN x, GEN n)
{
  GEN z = cgetg(3, t_POLMOD), a = gel(x,2), T = gel(x,1);
  gel(z,1) = gcopy(T);
  if (typ(a) != t_POL || varn(a) != varn(T) || lg(a) <= 3)
    a = powgi(a, n);
  else {
    pari_sp av = avma;
    GEN p = NULL;
    if (RgX_is_FpX(T, &p) && RgX_is_FpX(a, &p) && p)
    {
      T = RgX_to_FpX(T, p); a = RgX_to_FpX(a, p);
      if (lgefint(p) == 3)
      {
        ulong pp = p[2];
        a = Flxq_pow(ZX_to_Flx(a, pp), n, ZX_to_Flx(T, pp), pp);
        a = Flx_to_ZX(a);
      }
      else
        a = FpXQ_pow(a, n, T, p);
      a = FpX_to_mod(a, p);
      a = gc_upto(av, a);
    }
    else
    {
      set_avma(av);
      a = RgXQ_pow(a, n, gel(z,1));
    }
  }
  gel(z,2) = a; return z;
}

GEN
gpowgs(GEN x, long n)
{
  long m;
  pari_sp av;
  GEN y;

  if (n == 0) return gpowg0(x);
  if (n == 1)
  {
    long t = typ(x);
    if (is_scalar_t(t)) return gcopy(x);
    switch(t)
    {
      case t_POL: case t_SER: case t_RFRAC: case t_MAT: case t_VECSMALL:
        return gcopy(x);
      case t_VEC: if (!is_ext_qfr(x)) break;
      /* fall through handle extended t_QFB */
      case t_QFB: return qfbred(x);
    }
    pari_err_TYPE("gpow", x);
  }
  if (n ==-1) return ginv(x);
  switch(typ(x))
  {
    case t_INT: return powis(x,n);
    case t_REAL: return powrs(x,n);
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pows(gel(x,2), n, gel(x,1));
      return y;
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      long s = (signe(a) < 0 && odd(n))? -1: 1;
      if (n < 0) {
        n = -n;
        if (is_pm1(a)) return powiu_sign(b, n, s); /* +-1/x[2] inverts to t_INT */
        swap(a, b);
      }
      y = cgetg(3, t_FRAC);
      gel(y,1) = powiu_sign(a, n, s);
      gel(y,2) = powiu_sign(b, n, 1);
      return y;
    }
    case t_PADIC: return powps(x, n);
    case t_RFRAC:
    {
      av = avma; y = cgetg(3, t_RFRAC); m = labs(n);
      gel(y,1) = gpowgs(gel(x,1),m);
      gel(y,2) = gpowgs(gel(x,2),m);
      if (n < 0) y = ginv(y);
      return gc_upto(av,y);
    }
    case t_POLMOD: {
      long N[] = {evaltyp(t_INT) | _evallg(3),0,0};
      affsi(n,N); return pow_polmod(x, N);
    }
    case t_VEC: if (!is_ext_qfr(x)) pari_err_TYPE("gpow", x);
    /* fall through handle extended t_QFB */
    case t_QFB: return qfbpows(x, n);
    case t_POL:
      if (RgX_is_monomial(x)) return pow_monome(x, n);
    default: {
      pari_sp av = avma;
      y = gen_powu_i(x, (ulong)labs(n), NULL, &_sqr, &_mul);
      if (n < 0) y = ginv(y);
      return gc_upto(av,y);
    }
  }
}

/* n a t_INT */
GEN
powgi(GEN x, GEN n)
{
  GEN y;

  if (!is_bigint(n)) return gpowgs(x, itos(n));
  /* probable overflow for nonmodular types (typical exception: (X^0)^N) */
  switch(typ(x))
  {
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pow(gel(x,2), n, gel(x,1));
      return y;
    case t_FFELT: return FF_pow(x,n);
    case t_PADIC: return powp(x, n);

    case t_INT:
      if (is_pm1(x)) return (signe(x) < 0 && mpodd(n))? gen_m1: gen_1;
      if (signe(x)) pari_err_OVERFLOW("lg()");
      if (signe(n) < 0) pari_err_INV("powgi",gen_0);
      return gen_0;
    case t_FRAC:
      pari_err_OVERFLOW("lg()");

    case t_VEC: if (!is_ext_qfr(x)) pari_err_TYPE("gpow",x);
    /* fall through handle extended t_QFB */
    case t_QFB: return qfbpow(x, n);
    case t_POLMOD: return pow_polmod(x, n);
    default: {
      pari_sp av = avma;
      y = gen_pow_i(x, n, NULL, &_sqr, &_mul);
      if (signe(n) < 0) return gc_upto(av, ginv(y));
      return gc_GEN(av,y);
    }
  }
}

/* Assume x = 1 + O(t), n a scalar. Return x^n */
static GEN
ser_pow_1(GEN x, GEN n)
{
  long lx, mi, i, j, d;
  GEN y = cgetg_copy(x, &lx), X = x+2, Y = y + 2;
  y[1] = evalsigne(1) | _evalvalser(0) | evalvarn(varn(x));
  d = mi = lx-3; while (mi>=1 && isrationalzero(gel(X,mi))) mi--;
  gel(Y,0) = gen_1;
  for (i=1; i<=d; i++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=minss(i,mi); j++)
    {
      GEN t = gsubgs(gmulgu(n,j),i-j);
      s = gadd(s, gmul(gmul(t, gel(X,j)), gel(Y,i-j)));
    }
    gel(Y,i) = gc_upto(av, gdivgu(s,i));
  }
  return y;
}

/* we suppose n != 0, valser(x) = 0 and leading-term(x) != 0. Not stack clean */
static GEN
ser_pow(GEN x, GEN n, long prec)
{
  GEN y, c, lead;
  if (varncmp(gvar(n), varn(x)) <= 0) return gexp(gmul(n, glog(x,prec)), prec);
  lead = gel(x,2);
  if (gequal1(lead)) return ser_pow_1(x, n);
  x = ser_normalize(x);
  if (typ(n) == t_FRAC && !isinexact(lead) && ispower(lead, gel(n,2), &c))
    c = powgi(c, gel(n,1));
  else
    c = gpow(lead,n, prec);
  y = gmul(c, ser_pow_1(x, n));
  /* gpow(t_POLMOD,n) can be a t_COL [conjvec] */
  if (typ(y) != t_SER) pari_err_TYPE("gpow", y);
  return y;
}

static long
val_from_i(GEN E)
{
  if (is_bigint(E)) pari_err_OVERFLOW("sqrtn [valuation]");
  return itos(E);
}

/* return x^q, assume typ(x) = t_SER, typ(q) = t_INT/t_FRAC and q != 0 */
static GEN
ser_powfrac(GEN x, GEN q, long prec)
{
  GEN y, E = gmulsg(valser(x), q);
  long e;

  if (!signe(x))
  {
    if (gsigne(q) < 0) pari_err_INV("gpow", x);
    return zeroser(varn(x), val_from_i(gfloor(E)));
  }
  if (typ(E) != t_INT)
    pari_err_DOMAIN("sqrtn", "valuation", "!=", mkintmod(gen_0, gel(q,2)), x);
  e = val_from_i(E);
  y = leafcopy(x); setvalser(y, 0);
  y = ser_pow(y, q, prec);
  setvalser(y, e); return y;
}

static GEN
gpow0(GEN z, GEN x, long prec)
{
  pari_sp av = avma;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
      break;
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(gpow0(z,gel(x,i),prec));
    default: pari_err_TYPE("gpow(0,x)", x);
  }
  x = real_i(x);
  if (gsigne(x) <= 0) pari_err_DOMAIN("gpow(0,x)", "x", "<=", gen_0, x);
  if (!precision(z)) return gcopy(z);

  z = ground(gmulsg(gexpo(z),x));
  if (is_bigint(z) || uel(z,2) >= HIGHEXPOBIT)
    pari_err_OVERFLOW("gpow");
  set_avma(av); return real_0_bit(itos(z));
}

/* centermod(x, log(2)), set *sh to the quotient */
static GEN
modlog2(GEN x, long *sh)
{
  double d = rtodbl(x), qd = (fabs(d) + M_LN2/2)/M_LN2;
  long q;
  if (dblexpo(qd) >= BITS_IN_LONG-1) pari_err_OVERFLOW("expo()");
  q = d < 0 ? - (long) qd: (long) qd;
  *sh = q;
  if (q) {
    long l = realprec(x) + EXTRAPRECWORD;
    x = subrr(rtor(x,l), mulsr(q, mplog2(l)));
    if (!signe(x)) return NULL;
  }
  return x;
}

/* x^n, n a t_FRAC */
static GEN
powfrac(GEN x, GEN n, long prec)
{
  GEN a = gel(n,1), d = gel(n,2);
  long D = itos_or_0(d);
  if (D == 2)
  {
    GEN y = gsqrt(x,prec);
    if (!equali1(a)) y = gmul(y, powgi(x, shifti(subiu(a,1), -1)));
    return y;
  }
  if (D && is_real_t(typ(x)) && gsigne(x) > 0)
  { /* x^n = x^q * x^(r/D) */
    GEN z, r, q = truedvmdis(a, D, &r);
    if (typ(x) == t_REAL)
    {
      z = sqrtnr(x, D);
      if (!equali1(r)) z = powgi(z, r);
      if (signe(q)) z = gmul(z, powgi(x, q));
    }
    else
    {
      GEN X = x;
      x = gtofp(x, prec + nbits2extraprec(expi(r)));
      z = sqrtnr(x, D);
      if (!equali1(r)) z = powgi(z, r);
      if (signe(q))
      {
        long e = typ(X)==t_INT? expi(X): maxuu(expi(gel(X,1)), expi(gel(X,2)));
        z = gmul(z, powgi(cmpiu(muliu(q,e), realprec(x)) > 0? x: X, q));
      }
    }
    return z;
  }
  return NULL;
}

/* n = a+ib, x > 0 real, ex ~ |log2(x)|; return precision at which
 * log(x) must be computed to evaluate x^n */
long
powcx_prec(long ex, GEN n, long prec)
{
  GEN a = gel(n,1), b = gel(n,2);
  long e = (ex < 2)? 0: expu(ex);
  e += gexpo_safe(is_rational_t(typ(a))? b: n);
  return e > 2? prec + nbits2extraprec(e): prec;
}
GEN
powcx(GEN x, GEN logx, GEN n, long prec)
{
  GEN sxb, cxb, xa, a = gel(n,1), xb = gmul(gel(n,2), logx);
  long sh, p = realprec(logx);
  switch(typ(a))
  {
    case t_INT: xa = powgi(x, a); break;
    case t_FRAC: xa = powfrac(x, a, prec);
                 if (xa) break;
    default:
      xa = modlog2(gmul(gel(n,1), logx), &sh);
      if (!xa) xa = real2n(sh, prec);
      else
      {
        if (signe(xa) && realprec(xa) > prec) setprec(xa, prec);
        xa = mpexp(xa); shiftr_inplace(xa, sh);
      }
  }
  if (typ(xb) != t_REAL) return xa;
  if (gexpo(xb) > 30)
  {
    GEN q, P = Pi2n(-2, p), z = addrr(xb,P); /* = x + Pi/4 */
    shiftr_inplace(P, 1);
    q = floorr(divrr(z, P)); /* round ( x / (Pi/2) ) */
    xb = subrr(xb, mulir(q, P)); /* x mod Pi/2  */
    sh = Mod4(q);
  }
  else
  {
    long q = floor(rtodbl(xb) / (M_PI/2) + 0.5);
    if (q) xb = subrr(xb, mulsr(q, Pi2n(-1,p))); /* x mod Pi/2  */
    sh = q & 3;
  }
  if (signe(xb) && realprec(xb) > prec) setprec(xb, prec);
  mpsincos(xb, &sxb, &cxb);
  return gmul(xa, mulcxpowIs(mkcomplex(cxb, sxb), sh));
}

GEN
gpow(GEN x, GEN n, long prec)
{
  long i, prec0, tx, tn = typ(n);
  pari_sp av;
  GEN y;

  if (tn == t_INT) return powgi(x,n);
  tx = typ(x);
  if (is_matvec_t(tx)) pari_APPLY_same(gpow(gel(x,i),n,prec));
  av = avma;
  switch (tx)
  {
    case t_POL: case t_RFRAC: x = toser_i(x); /* fall through */
    case t_SER:
      if (tn == t_FRAC) return gc_upto(av, ser_powfrac(x, n, prec));
      if (valser(x))
        pari_err_DOMAIN("gpow [irrational exponent]",
                        "valuation", "!=", gen_0, x);
      if (lg(x) == 2) return gc_GEN(av, x); /* O(1) */
      return gc_upto(av, ser_pow(x, n, prec));
  }
  if (gequal0(x)) return gpow0(x, n, prec);
  if (tn == t_FRAC)
  {
    GEN p, z, a = gel(n,1), d = gel(n,2);
    switch (tx)
    {
    case t_INT:
      if (signe(x) < 0)
      {
        if (equaliu(d, 2) && Z_issquareall(negi(x), &z))
        {
          z = powgi(z, a);
          if (Mod4(a) == 3) z = gneg(z);
          return gc_GEN(av, mkcomplex(gen_0, z));
        }
        break;
      }
      if (ispower(x, d, &z)) return powgi(z, a);
      break;
    case t_FRAC:
      if (signe(gel(x,1)) < 0)
      {
        if (equaliu(d, 2) && ispower(absfrac(x), d, &z))
          return gc_GEN(av, mkcomplex(gen_0, powgi(z, a)));
        break;
      }
      if (ispower(x, d, &z)) return powgi(z, a);
      break;

    case t_INTMOD:
      p = gel(x,1);
      if (!BPSW_psp(p)) pari_err_PRIME("gpow",p);
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(p);
      av = avma;
      z = Fp_sqrtn(gel(x,2), d, p, NULL);
      if (!z) pari_err_SQRTN("gpow",x);
      gel(y,2) = gc_INT(av, Fp_pow(z, a, p));
      return y;

    case t_PADIC:
      z = Qp_sqrtn(x, d, NULL); if (!z) pari_err_SQRTN("gpow",x);
      return gc_upto(av, powgi(z, a));

    case t_FFELT:
      return gc_upto(av,FF_pow(FF_sqrtn(x,d,NULL),a));
    }
    z = powfrac(x, n, prec);
    if (z) return gc_upto(av, z);
  }
  if (tn == t_COMPLEX && is_real_t(typ(x)) && gsigne(x) > 0)
  {
    long p = powcx_prec(fabs(dbllog2(x)), n, prec);
    return gc_upto(av, powcx(x, glog(x, p), n, prec));
  }
  if (tn == t_PADIC) x = gcvtop(x, padic_p(n), precp(n));
  i = precision(n);
  if (i) prec = i;
  prec0 = prec;
  if (!gprecision(x))
  {
    long e = gexpo_safe(n); /* avoided if n = 0 or gexpo not defined */
    if (e > 2) prec += nbits2extraprec(e);
  }
  y = gmul(n, glog(x,prec));
  y = gexp(y,prec);
  if (prec0 == prec) return gc_upto(av, y);
  return gc_GEN(av, gprec_wtrunc(y,prec0));
}
GEN
powPis(GEN s, long prec)
{
  pari_sp av = avma;
  GEN x;
  if (typ(s) != t_COMPLEX) return gpow(mppi(prec), s, prec);
  x = mppi(powcx_prec(1, s, prec));
  return gc_upto(av, powcx(x, logr_abs(x), s, prec));
}
GEN
pow2Pis(GEN s, long prec)
{
  pari_sp av = avma;
  GEN x;
  if (typ(s) != t_COMPLEX) return gpow(Pi2n(1,prec), s, prec);
  x = Pi2n(1, powcx_prec(2, s, prec));
  return gc_upto(av, powcx(x, logr_abs(x), s, prec));
}

GEN
gpowers0(GEN x, long n, GEN x0)
{
  long i, l;
  GEN V;
  if (!x0) return gpowers(x,n);
  if (n < 0) return cgetg(1,t_VEC);
  l = n+2; V = cgetg(l, t_VEC); gel(V,1) = gcopy(x0);
  for (i = 2; i < l; i++) gel(V,i) = gmul(gel(V,i-1),x);
  return V;
}

GEN
gpowers(GEN x, long n)
{
  if (n < 0) return cgetg(1,t_VEC);
  return gen_powers(x, n, 0, (void*)x, &_sqr, &_mul, &_one);
}

/* return [q^1,q^4,...,q^{n^2}] */
GEN
gsqrpowers(GEN q, long n)
{
  pari_sp av = avma;
  GEN L = gpowers0(gsqr(q), n, q); /* L[i] = q^(2i - 1), i <= n+1 */
  GEN v = cgetg(n+1, t_VEC);
  long i;
  gel(v, 1) = gcopy(q);
  for (i = 2; i <= n ; ++i) gel(v, i) = q = gmul(q, gel(L,i)); /* q^(i^2) */
  return gc_upto(av, v);
}

/* 4 | N. returns a vector RU which contains exp(2*i*k*Pi/N), k=0..N-1 */
static GEN
grootsof1_4(long N, long prec)
{
  GEN z, RU = cgetg(N+1,t_COL), *v  = ((GEN*)RU) + 1;
  long i, N2 = (N>>1), N4 = (N>>2), N8 = (N>>3);
  /* z^N2 = -1, z^N4 = I; if z^k = a+I*b, then z^(N4-k) = I*conj(z) = b+a*I */

  v[0] = gen_1; v[1] = z = rootsof1u_cx(N, prec);
  if (odd(N4)) N8++;
  for (i=1; i<N8; i++)
  {
    GEN t = v[i];
    v[i+1] = gmul(z, t);
    v[N4-i] = mkcomplex(gel(t,2), gel(t,1));
  }
  for (i=0; i<N4; i++) v[i+N4] = mulcxI(v[i]);
  for (i=0; i<N2; i++) v[i+N2] = gneg(v[i]);
  return RU;
}

/* as above, N arbitrary */
GEN
grootsof1(long N, long prec)
{
  GEN z, RU, *v;
  long i, k;

  if (N <= 0) pari_err_DOMAIN("rootsof1", "N", "<=", gen_0, stoi(N));
  if ((N & 3) == 0) return grootsof1_4(N, prec);
  if (N <= 2) return N == 1? mkcol(gen_1): mkcol2(gen_1, gen_m1);
  k = (N+1)>>1;
  RU = cgetg(N+1,t_COL);
  v  = ((GEN*)RU) + 1;
  v[0] = gen_1; v[1] = z = rootsof1u_cx(N, prec);
  for (i=2; i<k; i++) v[i] = gmul(z, v[i-1]);
  if (!odd(N)) v[i++] = gen_m1; /*avoid loss of accuracy*/
  for (   ; i<N; i++) v[i] = gconj(v[N-i]);
  return RU;
}

/********************************************************************/
/**                                                                **/
/**                        RACINE CARREE                           **/
/**                                                                **/
/********************************************************************/
/* assume x unit, e = precp(x) */
GEN
Z2_sqrt(GEN x, long e)
{
  ulong r = signe(x)>=0?mod16(x):16-mod16(x);
  GEN z;
  long ez;
  pari_sp av;

  switch(e)
  {
    case 1: return gen_1;
    case 2: return (r & 3UL) == 1? gen_1: NULL;
    case 3: return (r & 7UL) == 1? gen_1: NULL;
    case 4: if (r == 1) return gen_1;
            else return (r == 9)? utoipos(3): NULL;
    default: if ((r&7UL) != 1) return NULL;
  }
  av = avma; z = (r==1)? gen_1: utoipos(3);
  ez = 3; /* number of correct bits in z (compared to sqrt(x)) */
  for(;;)
  {
    GEN mod;
    ez = (ez<<1) - 1;
    if (ez > e) ez = e;
    mod = int2n(ez);
    z = addii(z, remi2n(mulii(x, Fp_inv(z,mod)), ez));
    z = shifti(z, -1); /* (z + x/z) / 2 */
    if (e == ez) return gc_INT(av, z);
    if (ez < e) ez--;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"Qp_sqrt");
      z = gc_INT(av,z);
    }
  }
}

static GEN
Up_sqrt(GEN u, GEN p, GEN pd, long d, long D)
{ retmkpadic(Zp_sqrt(u, p, d), icopy(p), icopy(pd), 0, D); }

/* x unit defined modulo p^e, e > 0 */
GEN
Qp_sqrt(GEN x)
{
  long D, d, e = valp(x);
  GEN y, mod, p = padic_p(x);

  if (gequal0(x)) return zeropadic(p, (e+1) >> 1);
  if (e & 1) return NULL;

  mod = padic_pd(x); D = d = precp(x); e >>= 1;
  if (absequaliu(p,2)) { D = (d <= 3) ? 1 : d-1; mod = int2n(D); }
  y = Up_sqrt(padic_u(x), p, mod, d, D);
  if (!padic_u(y)) return NULL;
  setvalp(y, e); return y;
}

GEN
Zn_sqrt(GEN d, GEN fn)
{
  pari_sp ltop = avma, btop;
  GEN b = gen_0, m = gen_1;
  long j, np;
  if (typ(d) != t_INT) pari_err_TYPE("Zn_sqrt",d);
  if (typ(fn) == t_INT)
    fn = absZ_factor(fn);
  else if (!is_Z_factorpos(fn))
    pari_err_TYPE("Zn_sqrt",fn);
  np = nbrows(fn);
  btop = avma;
  for (j = 1; j <= np; ++j)
  {
    GEN  bp, mp, pr, r;
    GEN  p = gcoeff(fn, j, 1);
    long e = itos(gcoeff(fn, j, 2));
    long v = Z_pvalrem(d,p,&r);
    if (v >= e) bp =gen_0;
    else
    {
      if (odd(v)) return NULL;
      bp = Zp_sqrt(r, p, e-v);
      if (!bp)    return NULL;
      if (v) bp = mulii(bp, powiu(p, v>>1L));
    }
    mp = powiu(p, e);
    pr = mulii(m, mp);
    b = Z_chinese_coprime(b, bp, m, mp, pr);
    m = pr;
    if (gc_needed(btop, 1))
      (void)gc_all(btop, 2, &b, &m);
  }
  return gc_upto(ltop, b);
}

static GEN
sqrt_ser(GEN b, long prec)
{
  long e = valser(b), vx = varn(b), lx, lold, j;
  ulong mask;
  GEN a, x, lta, ltx;

  if (!signe(b)) return zeroser(vx, e>>1);
  a = leafcopy(b);
  x = cgetg_copy(b, &lx);
  if (e & 1)
    pari_err_DOMAIN("sqrtn", "valuation", "!=", mkintmod(gen_0, gen_2), b);
  a[1] = x[1] = evalsigne(1) | evalvarn(0) | _evalvalser(0);
  lta = gel(a,2);
  if (gequal1(lta)) ltx = lta;
  else if (!issquareall(lta,&ltx)) ltx = gsqrt(lta,prec);
  gel(x,2) = ltx;
  for (j = 3; j < lx; j++) gel(x,j) = gen_0;
  setlg(x,3);
  mask = quadratic_prec_mask(lx - 2);
  lold = 1;
  while (mask > 1)
  {
    GEN y, x2 = gmul2n(x,1);
    long l = lold << 1, lx;

    if (mask & 1) l--;
    mask >>= 1;
    setlg(a, l + 2);
    setlg(x, l + 2);
    y = sqr_ser_part(x, lold, l-1) - lold;
    for (j = lold+2; j < l+2; j++) gel(y,j) = gsub(gel(y,j), gel(a,j));
    y += lold; setvalser(y, lold);
    y = normalizeser(y);
    y = gsub(x, gdiv(y, x2)); /* = gmul2n(gsub(x, gdiv(a,x)), -1); */
    lx = minss(l+2, lg(y));
    for (j = lold+2; j < lx; j++) gel(x,j) = gel(y,j);
    lold = l;
  }
  x[1] = evalsigne(1) | evalvarn(vx) | _evalvalser(e >> 1);
  return x;
}

GEN
gsqrt(GEN x, long prec)
{
  pari_sp av;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      if (!signe(x)) return real_0(prec); /* no loss of accuracy */
      x = itor(x,prec); /* fall through */
    case t_REAL: return sqrtr(x);

    case t_INTMOD:
    {
      GEN p = gel(x,1), a;
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(p);
      a = Fp_sqrt(gel(x,2),p);
      if (!a)
      {
        if (!BPSW_psp(p)) pari_err_PRIME("sqrt [modulus]",p);
        pari_err_SQRTN("gsqrt",x);
      }
      gel(y,2) = a; return y;
    }

    case t_COMPLEX:
    { /* (u+iv)^2 = a+ib <=> u^2+v^2 = sqrt(a^2+b^2), u^2-v^2=a, 2uv=b */
      GEN a = gel(x,1), b = gel(x,2), r, u, v;
      if (isrationalzero(b)) return gsqrt(a, prec);
      y = cgetg(3,t_COMPLEX); av = avma;

      r = cxnorm(x);
      if (typ(r) == t_INTMOD || typ(r) == t_PADIC)
        pari_err_IMPL("sqrt(complex of t_INTMODs)");
      r = gsqrt(r, prec); /* t_REAL, |a+Ib| */
      if (!signe(r))
        u = v = gc_leaf(av, sqrtr(r));
      else if (gsigne(a) < 0)
      {
        /* v > 0 since r > 0, a < 0, rounding errors can't make the sum of two
         * positive numbers = 0 */
        v = sqrtr( gmul2n(gsub(r,a), -1) );
        if (gsigne(b) < 0) togglesign(v);
        v = gc_leaf(av, v); av = avma;
        /* v = 0 is impossible */
        u = gc_leaf(av, gdiv(b, shiftr(v,1)));
      } else {
        u = sqrtr( gmul2n(gadd(r,a), -1) );
        u = gc_leaf(av, u); av = avma;
        if (!signe(u)) /* possible if a = 0.0, e.g. sqrt(0.e-10+1e-10*I) */
          v = u;
        else
          v = gc_leaf(av, gdiv(b, shiftr(u,1)));
      }
      gel(y,1) = u;
      gel(y,2) = v; return y;
    }

    case t_PADIC:
      y = Qp_sqrt(x);
      if (!y) pari_err_SQRTN("Qp_sqrt",x);
      return y;

    case t_FFELT: return FF_sqrt(x);

    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gc_GEN(av, sqrt_ser(y, prec));
  }
  return trans_eval("sqrt",gsqrt,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                          N-th ROOT                             **/
/**                                                                **/
/********************************************************************/

static GEN
Z_to_padic(GEN a, GEN p, long e)
{
  if (!signe(a))
    return zeropadic(p, e);
  else
  {
    long v = Z_pvalrem(a, p, &a), d = e - v;
    retmkpadic(icopy(a), icopy(p), powiu(p, d), v, d);
  }
}

GEN
Qp_log(GEN x)
{
  pari_sp av = avma;
  GEN y, p = padic_p(x), a = padic_u(x);
  long e = precp(x);

  if (!signe(a)) pari_err_DOMAIN("Qp_log", "argument", "=", gen_0, x);
  if (absequaliu(p,2) || equali1(modii(a, p)))
    y = Zp_log(a, p, e);
  else
  { /* compute log(x^(p-1)) / (p-1) */
    GEN q = padic_pd(x), t = subiu(p, 1);
    a = Fp_pow(a, t, q);
    y = Fp_mul(Zp_log(a, p, e), diviiexact(subsi(1, q), t), q);
  }
  return gc_upto(av, Z_to_padic(y, p, e));
}

static GEN Qp_exp_safe(GEN x);

/*compute the p^e th root of x p-adic, ignoring valuation; assume x != 0 */
static GEN
Up_sqrtn_ram(GEN x, long e)
{
  GEN a, p = padic_p(x), n = powiu(p,e);
  long va;
  /*If p = 2, -1 is a root of 1 in U1: need extra check*/
  if (absequaliu(p, 2) && mod8(padic_u(x)) != 1) return NULL;
  a = Qp_log(x); va = valp(a) - e;
  if (va <= 0)
  {
    if (signe(padic_u(a))) return NULL;
    /* all accuracy lost */
    a = cvtop(remii(padic_u(x),p), p, 1);
  }
  else
  {
    setvalp(a, va); /* divide by p^e */
    a = Qp_exp_safe(a);
    if (!a) return NULL;
    /* n=p^e and a^n=z*x where z is a (p-1)th-root of 1.
     * Since z^n=z, we have (a/z)^n = x. */
    a = gdiv(x, powgi(a,subiu(n,1))); /* = a/z = x/a^(n-1)*/
  }
  return a;
}

/* set q = s/n if n | s */
static int
dvdsi_quot(long s, GEN n, long *q)
{
  long r;
  *q = sdivsi_rem(s, n, &r);
  return !r;
}

GEN
Qp_sqrtn(GEN x, GEN n, GEN *zetan)
{
  pari_sp av = avma;
  GEN a, u, q, p = padic_p(x);
  long e, v, prec;
  if (absequaliu(n, 2))
  {
    if (zetan) *zetan = gen_m1;
    if (signe(n) < 0) x = ginv(x);
    return Qp_sqrt(x);
  }
  if (!signe(padic_u(x)))
  {
    if (signe(n) < 0) pari_err_INV("Qp_sqrtn", x);
    q = divii(addis(n, valp(x)-1), n);
    if (zetan) *zetan = gen_1;
    set_avma(av); return zeropadic(p, itos(q));
  }
  if (!dvdsi_quot(valp(x), n, &v)) return NULL;
  /* treat the ramified part using logarithms */
  e = Z_pvalrem(n, p, &q);
  if (e) { x = Up_sqrtn_ram(x,e); if (!x) return NULL; }
  if (is_pm1(q))
  { /* finished */
    if (signe(q) < 0) x = ginv(x);
    if (v) setvalp(x, v);
    x = gc_upto(av, x);
    if (zetan) *zetan = (e && absequaliu(p, 2))? gen_m1 /*-1 in Q_2*/
                                               : gen_1;
    return x;
  }
  /* Hensel lift for unramified case */
  u = padic_u(x); prec = precp(x);
  a = Fp_sqrtn(u, q, p, zetan); if (!a) return NULL;
  u = Zp_sqrtnlift(u, q, a, p, prec);
  x = mkpadic(u, p, padic_pd(x), v, prec);
  if (!zetan) return gc_GEN(av, x);

  u = Zp_sqrtnlift(gen_1, q, *zetan, p, prec);
  *zetan = mkpadic(u, p,  padic_pd(x), 0, prec);
  if (e && absequaliu(p, 2)) *zetan = gneg(*zetan); /*-1 in Q_2*/
  return gc_all(av, 2, &x, zetan);
}

GEN
sqrtnint(GEN a, long n)
{
  pari_sp av = avma;
  GEN x, b, q;
  long s, k, e;
  const ulong nm1 = n - 1;
  if (n == 2) return sqrtint(a);
  if (typ(a) != t_INT)
  {
    if (typ(a) == t_REAL)
    {
      long e;
      switch(signe(a))
      {
        case 0: return gen_0;
        case -1: pari_err_DOMAIN("sqrtnint", "argument", "<", gen_0,a);
      }
      e = expo(a); if (e < 0) return gen_0;
      if (nbits2lg(e+1) > lg(a))
        a = floorr(sqrtnr(a,n)); /* try to avoid precision loss in truncation */
      else
        a = sqrtnint(truncr(a),n);
    }
    else
    {
      GEN b = gfloor(a);
      if (typ(b) != t_INT) pari_err_TYPE("sqrtint",a);
      if (signe(b) < 0) pari_err_DOMAIN("sqrtnint", "argument", "<", gen_0,b);
      a = sqrtnint(b, n);
    }
    return gc_INT(av, a);
  }
  if (n <= 0) pari_err_DOMAIN("sqrtnint", "n", "<=", gen_0, stoi(n));
  if (n == 1) return icopy(a);
  s = signe(a);
  if (s < 0) pari_err_DOMAIN("sqrtnint", "x", "<", gen_0, a);
  if (!s) return gen_0;
  if (lgefint(a) == 3) return utoi(usqrtn(itou(a), n));
  e = expi(a); k = e/(2*n);
  if (k == 0)
  {
    long flag;
    if (n > e) return gc_const(av, gen_1);
    flag = cmpii(a, powuu(3, n)); set_avma(av);
    return (flag < 0) ? gen_2: stoi(3);
  }
  if (e < n*BITS_IN_LONG - 1)
  {
    ulong xs, qs;
    b = itor(a, (2*e < n*BITS_IN_LONG)? DEFAULTPREC: MEDDEFAULTPREC);
    x = mpexp(divru(logr_abs(b), n));
    xs = itou(floorr(x)) + 1; /* >= a^(1/n) */
    for(;;) {
      q = divii(a, powuu(xs, nm1));
      if (lgefint(q) > 3) break;
      qs = itou(q); if (qs >= xs) break;
      xs -= (xs - qs + nm1)/n;
    }
    return utoi(xs);
  }
  b = addui(1, shifti(a, -n*k));
  x = shifti(addui(1, sqrtnint(b, n)), k);
  q = divii(a, powiu(x, nm1));
  while (cmpii(q, x) < 0) /* a priori one iteration, no GC necessary */
  {
    x = subii(x, divis(addui(nm1, subii(x, q)), n));
    q = divii(a, powiu(x, nm1));
  }
  return gc_leaf(av, x);
}

ulong
usqrtn(ulong a, ulong n)
{
  ulong x, s, q;
  const ulong nm1 = n - 1;
  if (!n) pari_err_DOMAIN("sqrtnint", "n", "=", gen_0, utoi(n));
  if (n == 1 || a == 0) return a;
  s = 1 + expu(a)/n; x = 1UL << s;
  q = (nm1*s >= BITS_IN_LONG)? 0: a >> (nm1*s);
  while (q < x) {
    ulong X;
    x -= (x - q + nm1)/n;
    X = upowuu(x, nm1);
    q = X? a/X: 0;
  }
  return x;
}

static ulong
cubic_prec_mask(long n)
{
  long a = n, i;
  ulong mask = 0;
  for(i = 1;; i++, mask *= 3)
  {
    long c = a%3;
    if (c) mask += 3 - c;
    a = (a+2)/3;
    if (a==1) return mask + upowuu(3, i);
  }
}

/* cubic Newton iteration, |a|^(1/n), assuming a != 0 */
GEN
sqrtnr_abs(GEN a, long n)
{
  pari_sp av;
  GEN x, b;
  long eextra, eold, n1, n2, prec, B, v;
  ulong mask;
  double K = n, X;

  if (n == 1) return mpabs(a);
  if (n == 2) return sqrtr_abs(a);

  prec = realprec(a); v = expo(a) / n; av = avma;
  if (v) a = shiftr(a, -n*v);
  b = rtor(a, DEFAULTPREC);
  x = mpexp(divru(logr_abs(b), n));
  if (prec == DEFAULTPREC)
  {
    if (v) shiftr_inplace(x, v);
    return gc_leaf(av, x);
  }
  X = rtodbl(x);
  K = (K*K-1) / (12*X*X); /* |x_{n+1} - x| < K |x_n - x|^3 */
  eextra = dblexpo(K);
  n1 = n+1;
  n2 = 2*n;
  B = prec2nbits(prec);
  mask = cubic_prec_mask(B + 63);
  eold = 1;
  for(;;)
  { /* reach 64 */
    long enew = eold * 3;
    enew -= mask % 3;
    if (enew > 64) break; /* back up one step */
    mask /= 3;
    eold = enew;
  }
  for(;;)
  {
    long pr, enew = eold * 3;
    GEN y, z;
    enew -= mask % 3;
    mask /= 3;
    pr = nbits2prec(enew + eextra);
    b = rtor(a, pr); setsigne(b,1);
    x = rtor(x, pr);
    y = subrr(powru(x, n), b);
    z = divrr(y, addrr(mulur(n1, y), mulur(n2, b)));
    shiftr_inplace(z,1);
    x = subrr(x, mulrr(x,z));
    if (mask == 1)
    {
      if (v) shiftr_inplace(x, v);
      return gc_leaf(av, gprec_wtrunc(x,prec));
    }
    eold = enew;
  }
}

static void
shiftc_inplace(GEN z, long d)
{
  shiftr_inplace(gel(z,1), d);
  shiftr_inplace(gel(z,2), d);
}

/* exp(2*Pi*I/n), same iteration as sqrtnr_abs, different initial point */
static GEN
sqrtnof1(ulong n, long prec)
{
  pari_sp av;
  GEN x;
  long eold, n1, n2, B;
  ulong mask;

  B = prec2nbits(prec);
  n1 = n+1;
  n2 = 2*n; av = avma;

  x = expIr(divru(Pi2n(1, LOWDEFAULTPREC), n));
  if (prec == LOWDEFAULTPREC) return gc_upto(av, x);
  mask = cubic_prec_mask(B + BITS_IN_LONG-1);
  eold = 1;
  for(;;)
  { /* reach BITS_IN_LONG */
    long enew = eold * 3;
    enew -= mask % 3;
    if (enew > BITS_IN_LONG) break; /* back up one step */
    mask /= 3;
    eold = enew;
  }
  for(;;)
  {
    long pr, enew = eold * 3;
    GEN y, z;
    enew -= mask % 3;
    mask /= 3;
    pr = nbits2prec(enew);
    x = cxtofp(x, pr);
    y = gsub(gpowgs(x, n), gen_1);
    z = gdiv(y, gaddgs(gmulsg(n1, y), n2));
    shiftc_inplace(z,1);
    x = gmul(x, gsubsg(1, z));
    if (mask == 1) return gc_GEN(av, gprec_w(x,prec));
    eold = enew;
  }
}

/* exp(2iPi/d) */
GEN
rootsof1u_cx(ulong n, long prec)
{
  switch(n)
  {
    case 1: return gen_1;
    case 2: return gen_m1;
    case 4: return gen_I();
    case 3: case 6: case 12:
    {
      pari_sp av = avma;
      GEN a = (n == 3)? mkfrac(gen_m1,gen_2): ghalf;
      GEN sq3 = sqrtr_abs(utor(3, prec));
      shiftr_inplace(sq3, -1);
      a = (n == 12)? mkcomplex(sq3, a): mkcomplex(a, sq3);
      return gc_GEN(av, a);
    }
    case 8:
    {
      pari_sp av = avma;
      GEN sq2 = sqrtr_abs(utor(2, prec));
      shiftr_inplace(sq2,-1);
      return gc_GEN(av, mkcomplex(sq2, sq2));
    }
  }
  return sqrtnof1(n, prec);
}
/* e(a/b) */
GEN
rootsof1q_cx(long a, long b, long prec)
{
  long g = cgcd(a,b);
  GEN z;
  if (g != 1) { a /= g; b /= g; }
  if (b < 0) { b = -b; a = -a; }
  z = rootsof1u_cx(b, prec);
  if (a < 0) { z = conj_i(z); a = -a; }
  return gpowgs(z, a);
}

/* initializes powers of e(a/b) */
GEN
rootsof1powinit(long a, long b, long prec)
{
  long g = cgcd(a,b);
  if (g != 1) { a /= g; b /= g; }
  if (b < 0) { b = -b; a = -a; }
  a %= b; if (a < 0) a += b;
  return mkvec2(grootsof1(b,prec), mkvecsmall2(a,b));
}
/* T = rootsof1powinit(a,b); return  e(a/b)^c */
GEN
rootsof1pow(GEN T, long c)
{
  GEN vz = gel(T,1), ab = gel(T,2);
  long a = ab[1], b = ab[2]; /* a >= 0, b > 0 */
  c %= b; if (c < 0) c += b;
  a = Fl_mul(a, c, b);
  return gel(vz, a + 1);
}

/* exp(2iPi/d), assume d a t_INT */
GEN
rootsof1_cx(GEN d, long prec)
{
  if (lgefint(d) == 3) return rootsof1u_cx((ulong)d[2], prec);
  return expIr(divri(Pi2n(1,prec), d));
}

GEN
gsqrtn(GEN x, GEN n, GEN *zetan, long prec)
{
  long i, tx;
  pari_sp av;
  GEN y, z;
  if (typ(n)!=t_INT) pari_err_TYPE("sqrtn",n);
  if (!signe(n)) pari_err_DOMAIN("sqrtn", "n", "=", gen_0, n);
  if (is_pm1(n))
  {
    if (zetan) *zetan = gen_1;
    return (signe(n) > 0)? gcopy(x): ginv(x);
  }
  if (zetan) *zetan = gen_0;
  tx = typ(x);
  if (is_matvec_t(tx)) pari_APPLY_same(gsqrtn(gel(x,i),n,NULL,prec));
  av = avma;
  switch(tx)
  {
  case t_INTMOD:
    {
      GEN p = gel(x,1), s;
      z = gen_0;
      y = cgetg(3,t_INTMOD);  gel(y,1) = icopy(p);
      if (zetan) { z = cgetg(3,t_INTMOD); gel(z,1) = gel(y,1); }
      s = Fp_sqrtn(gel(x,2),n,p,zetan);
      if (!s) {
        if (zetan) return gc_const(av,gen_0);
        if (!BPSW_psp(p)) pari_err_PRIME("sqrtn [modulus]",p);
        pari_err_SQRTN("gsqrtn",x);
      }
      gel(y,2) = s;
      if (zetan) { gel(z,2) = *zetan; *zetan = z; }
      return y;
    }

  case t_PADIC:
    y = Qp_sqrtn(x,n,zetan);
    if (!y) {
      if (zetan) return gen_0;
      pari_err_SQRTN("gsqrtn",x);
    }
    return y;

  case t_FFELT: return FF_sqrtn(x,n,zetan);

  case t_INT: case t_FRAC: case t_REAL: case t_COMPLEX:
    i = precision(x); if (i) prec = i;
    if (isint1(x))
      y = real_1(prec);
    else if (gequal0(x))
    {
      long b;
      if (signe(n) < 0) pari_err_INV("gsqrtn",x);
      if (isinexactreal(x))
        b = sdivsi(gexpo(x), n);
      else
        b = -prec2nbits(prec);
      if (typ(x) == t_COMPLEX)
      {
        y = cgetg(3,t_COMPLEX);
        gel(y,1) = gel(y,2) = real_0_bit(b);
      }
      else
        y = real_0_bit(b);
    }
    else
    {
      long nn = itos_or_0(n);
      if (tx == t_INT) { x = itor(x,prec); tx = t_REAL; }
      if (nn > 0 && tx == t_REAL && signe(x) > 0)
        y = sqrtnr(x, nn);
      else
        y = gexp(gdiv(glog(x,prec), n), prec);
      y = gc_upto(av, y);
    }
    if (zetan) *zetan = rootsof1_cx(n, prec);
    return y;

  case t_QUAD:
    return gsqrtn(quadtofp(x, prec), n, zetan, prec);

  default:
    av = avma; if (!(y = toser_i(x))) break;
    return gc_upto(av, ser_powfrac(y, ginv(n), prec));
  }
  pari_err_TYPE("sqrtn",x);
  return NULL;/* LCOV_EXCL_LINE */
}

/********************************************************************/
/**                                                                **/
/**                             EXP(X) - 1                         **/
/**                                                                **/
/********************************************************************/
/* exp(|x|) - 1, assume x != 0.
 * For efficiency, x should be reduced mod log(2): if so, we have a < 0 */
GEN
exp1r_abs(GEN x)
{
  long l = realprec(x), a = expo(x), b = prec2nbits(l), L, i, n, m, B;
  GEN y, p2, X;
  pari_sp av;
  double d;

  if (b + a <= 0) return mpabs(x);

  y = cgetr(l); av = avma;
  B = b/3 + BITS_IN_LONG + (BITS_IN_LONG*BITS_IN_LONG)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 */
  if (m < (-a) * 0.1) m = 0; /* not worth it */
 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum_{k <= n} Y^k/k!: this costs roughly
  *    m b^2 + sum_{k <= n} (k e + BITS_IN_LONG)^2
  * bit operations with n ~ b/e, |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and
  * b bits of accuracy needed, so
  *    B := (b / 3 + BITS_IN_LONG + BITS_IN_LONG^2 / b) ~ m(m-a)
  * we want b ~ 3 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + B),  b + a )
  * NB: e ~ (b/3)^(1/2) as b -> oo
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  *   sum_{k >= n+1} Y^k / k! < Y^(n+1) / (n+1)! (1-Y) < Y^(n+1) / n!
  * We want Y^(n+1) / n! <= Y 2^-b, hence -n log_2 |Y| + log_2 n! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * n (-1/log(2) -log_2 |Y| + log_2(n+1)) >= b  */
  d = m-dbllog2(x)-1/M_LN2; /* ~ -log_2 Y - 1/log(2) */
  while (d <= 0) { d++; m++; } /* d < 0 can occur from expm1 */
  L = l + nbits2extraprec(m);
  b += m;
  n = (long)(b / d); /* > 0 */
  if (n == 1)
    n = (long)(b / (d + log2((double)n+1))); /* log ~ const in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

  X = rtor(x,L); shiftr_inplace(X, -m); setsigne(X, 1);
  if (n == 1) p2 = X;
  else
  {
    long s = 0, l1 = nbits2prec((long)(d + n + 16));
    GEN unr = real_1(L);
    pari_sp av2;

    p2 = cgetr(L); av2 = avma;
    for (i=n; i>=2; i--, set_avma(av2))
    { /* compute X^(n-1)/n! + ... + X/2 + 1 */
      GEN p1, p3;
      setprec(X,l1); p3 = divru(X,i);
      l1 += nbits2extraprec(dvmdsBIL(s - expo(p3), &s)<<TWOPOTBITS_IN_LONG);
      if (l1>L) l1=L;
      setprec(unr,l1); p1 = addrr_sign(unr,1, i == n? p3: mulrr(p3,p2),1);
      setprec(p2,l1); affrr(p1,p2); /* p2 <- 1 + (X/i)*p2 */
    }
    setprec(X,L); p2 = mulrr(X,p2);
  }

  B = prec2nbits(L);
  for (i = 1; i <= m; i++)
  {
    if (realprec(p2) > L) setprec(p2,L);
    if (expo(p2) < -B)
      shiftr_inplace(p2, 1); /* 2 + p2 ~ 2 and may blow up accuracy */
    else
      p2 = mulrr(p2, addsr(2,p2));
  }
  affrr_fixlg(p2,y); return gc_const(av,y);
}

GEN
mpexpm1(GEN x)
{
  const long s = 6;
  long B, l, sx = signe(x);
  GEN y, z;
  pari_sp av;
  if (!sx) return real_0_bit(expo(x));
  l = realprec(x);
  if (l > maxss(EXPNEWTON_LIMIT, BITS_IN_LONG<<s))
  {
    long e = expo(x);
    if (e < 0) x = rtor(x, l + nbits2extraprec(-e));
    return subrs(mpexp(x), 1);
  }
  if (sx > 0) return exp1r_abs(x);
  B = prec2nbits(l);
  if (cmpsr(-B, x) > 0) return real_m1(l);
  /* compute exp(x) * (1 - exp(-x)) */
  av = avma; y = exp1r_abs(x); /* > 0 */
  if (expo(y) >= -B) { z = addsr(1, y); y = divrr(y, z); }
  setsigne(y, -1);
  return gc_leaf(av, y);
}

static GEN serexp(GEN x, long prec);
GEN
gexpm1(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mpexpm1(x);
    case t_COMPLEX: return cxexpm1(x,prec);
    case t_PADIC: return gsubgs(Qp_exp(x), 1);
    default:
    {
      pari_sp av = avma;
      long ey;
      GEN y;
      if (!(y = toser_i(x))) break;
      ey = valser(y);
      if (ey < 0) pari_err_DOMAIN("expm1","valuation", "<", gen_0, x);
      if (gequal0(y)) return gcopy(y);
      if (ey)
        return gc_upto(av, gsubgs(serexp(y,prec), 1));
      else
      {
        GEN e1 = gexpm1(gel(y,2), prec), e = gaddgs(e1,1);
        y = gmul(e, serexp(serchop0(y),prec));
        gel(y,2) = e1;
        return gc_GEN(av, y);
      }
    }
  }
  return trans_eval("expm1",gexpm1,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             EXP(X)                             **/
/**                                                                **/
/********************************************************************/
static GEN
mpexp_basecase(GEN x)
{
  pari_sp av = avma;
  long sh, l = realprec(x);
  GEN y, z;

  y = modlog2(x, &sh);
  if (!y) { set_avma(av); return real2n(sh, l); }
  z = addsr(1, exp1r_abs(y));
  if (signe(y) < 0) z = invr(z);
  if (sh) {
    shiftr_inplace(z, sh);
    if (realprec(z) > l) z = rtor(z, l); /* spurious precision increase */
  }
#ifdef DEBUG
{
  GEN t = mplog(z), u = divrr(subrr(x, t),x);
  if (signe(u) && expo(u) > 5-prec2nbits(minss(l,realprec(t))))
    pari_err_BUG("exp");
}
#endif
  return gc_leaf(av, z); /* NOT affrr, precision often increases */
}

GEN
mpexp(GEN x)
{
  const long s = 6; /*Initial steps using basecase*/
  long i, p, l = realprec(x), sh;
  GEN a, t, z;
  ulong mask;

  if (l <= maxss(EXPNEWTON_LIMIT, (BITS_IN_LONG<<s) + 2))
  {
    if (!signe(x)) return mpexp0(x);
    return mpexp_basecase(x);
  }
  z = cgetr(l); /* room for result */
  x = modlog2(x, &sh);
  if (!x) { set_avma((pari_sp)(z+lg(z))); return real2n(sh, l); }
  constpi(l); /* precompute for later logr_abs() */
  mask = quadratic_prec_mask(prec2nbits(l)+BITS_IN_LONG);
  for(i=0, p=1; i<s+TWOPOTBITS_IN_LONG; i++) { p <<= 1; if (mask & 1) p-=1; mask >>= 1; }
  a = mpexp_basecase(rtor(x, nbits2prec(p)));
  x = addrs(x,1);
  if (realprec(x) < l+EXTRAPREC64) x = rtor(x, l+EXTRAPREC64);
  a = rtor(a, l+EXTRAPREC64); /*append 0s */
  t = NULL;
  for(;;)
  {
    p <<= 1; if (mask & 1) p--;
    mask >>= 1;
    setprec(x, nbits2prec(p));
    setprec(a, nbits2prec(p));
    t = mulrr(a, subrr(x, logr_abs(a))); /* a (x - log(a)) */
    if (mask == 1) break;
    affrr(t, a); set_avma((pari_sp)a);
  }
  affrr(t,z);
  if (sh) shiftr_inplace(z, sh);
  return gc_const((pari_sp)z, z);
}

/* x != 0; k = ceil(tn / (te-1)), t = p-1 */
long
Qp_exp_prec(GEN x)
{
  long e = valp(x), n = precp(x);
  ulong a, b, q, r, p, t;

  if (e < 1) return -1;
  if (e > n) return 1;
  p = itos_or_0(padic_p(x));
  if (!p) return n / e + 1;
  if (p == 2) return e < 2? -1: ceildivuu(n, e - 1);
  /* n >= e > 0, n = qe + r */
  /* tn = q (te-1) + rt + q = (q+1)(te-1) - t(e-r) + q + 1 */
  t = p - 1;
  if (e == 1) return n + ceildivuu(n, t - 1);
  q = n / e;
  r = n % e; /* k = q + 1 if rt + q < te */
  a = umuluu_or_0(e - r, t); if (!a || a > q) return q + 1;
  b = umuluu_or_0(e, t); if (!b) return q + 2;
  return q + 1 + ceildivuu(q + 1 - a, b - 1);
}

static GEN
Qp_exp_safe(GEN x)
{
  pari_sp av = avma;
  GEN p = padic_p(x), a = padic_u(x), z;
  long d = precp(x), v = valp(x), e = d+v;
  if (gequal0(x)) return gaddgs(x,1);
  if (v < (equaliu(p,2)? 2:1)) return NULL;
  z = Zp_exp(mulii(a,powiu(p,v)), p, e);
  return gc_upto(av, Z_to_padic(z, p, e));
}

GEN
Qp_exp(GEN x)
{
  GEN y = Qp_exp_safe(x);
  if (!y) pari_err_DOMAIN("gexp(t_PADIC)","argument","",gen_0,x);
  return y;
}

static GEN
cos_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k-1));
    y = gsubsg(1, t);
  }
  return gc_upto(av, y);
}
static GEN
sin_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gcopy(x);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k+1));
    y = gsubsg(1, t);
  }
  return gc_upto(av, gmul(y, x));
}

static GEN
cxexp(GEN x, long prec)
{
  GEN r, p1, p2, y = cgetg(3,t_COMPLEX);
  pari_sp av = avma, tetpil;
  long l;
  l = precision(x); if (l > prec) prec = l;
  if (gequal0(gel(x,1)))
  {
    gsincos(gel(x,2),&gel(y,2),&gel(y,1),prec);
    return y;
  }
  r = gexp(gel(x,1),prec);
  gsincos(gel(x,2),&p2,&p1,prec);
  tetpil = avma;
  gel(y,1) = gmul(r,p1);
  gel(y,2) = gmul(r,p2);
  gc_slice_unsafe(av,tetpil,y+1,2);
  return y;
}

/* given a t_SER x^v s(x), with s(0) != 0, return x^v(s - s(0)), shallow */
GEN
serchop0(GEN s)
{
  long i, l = lg(s);
  GEN y;
  if (l == 2) return s;
  if (l == 3 && isexactzero(gel(s,2))) return s;
  y = cgetg(l, t_SER); y[1] = s[1];
  gel(y,2) = gen_0; for (i=3; i <l; i++) gel(y,i) = gel(s,i);
  return normalizeser(y);
}

GEN
serchop_i(GEN s, long n)
{
  long i, m, l = lg(s);
  GEN y;
  if (l == 2 || (l == 3 && isexactzero(gel(s,2))))
  {
    if (valser(s) < n) { s = shallowcopy(s); setvalser(s,n); }
    return s;
  }
  m = n - valser(s); if (m < 0) return s;
  if (l-m <= 2) return zeroser(varn(s), n);
  y = cgetg(l-m, t_SER); y[1] = s[1]; setvalser(y, valser(y)+m);
  for (i=m+2; i < l; i++) gel(y,i-m) = gel(s,i);
  return normalizeser(y);
}
GEN
serchop(GEN s, long n)
{
  pari_sp av = avma;
  if (typ(s) != t_SER) pari_err_TYPE("serchop",s);
  return gc_GEN(av, serchop_i(s,n));
}

static GEN
serexp(GEN x, long prec)
{
  long i, j, lx, ly, mi, e = valser(x);
  GEN y, xd, yd;
  pari_sp av;

  if (e < 0) pari_err_DOMAIN("exp","valuation", "<", gen_0, x);
  if (gequal0(x)) return gaddsg(1,x);
  lx = lg(x);
  if (e)
  {
    GEN X;
    ly = lx+e; y = cgetg(ly,t_SER);
    mi = lx-1; while (mi>=3 && isrationalzero(gel(x,mi))) mi--;
    mi += e-2;
    y[1] = evalsigne(1) | _evalvalser(0) | evalvarn(varn(x));
    /* zd[i] = coefficient of X^i in z */
    xd = x+2-e; yd = y+2; ly -= 2;
    X = gel(xd,e); if (e != 1) X = gmulgu(X, e); /* left on stack */
    X = isint1(X)? NULL: X;
    gel(yd,0) = gen_1;
    for (i = 1; i < e; i++) gel(yd,i) = gen_0;
    for (     ; i < ly; i++)
    {
      GEN t = gel(yd,i-e);
      long J = minss(i, mi);
      av = avma; if (X) t = gmul(t, X);
      for (j = e + 1; j <= J; j++)
        t = gadd(t, gmulgu(gmul(gel(xd,j),gel(yd,i-j)), j));
      gel(yd,i) = gc_upto(av, gdivgu(t, i));
    }
    return y;
  }
  av = avma;
  return gc_upto(av, gmul(gexp(gel(x,2),prec), serexp(serchop0(x),prec)));
}

static GEN
expQ(GEN x, long prec)
{
  GEN p, q, z, z0 = NULL;
  pari_sp av;
  long n, nmax, s, e, b = prec2nbits(prec);
  double ex;
  struct abpq_res R;
  struct abpq S;

  if (typ(x) == t_INT)
  {
    if (!signe(x)) return real_1(prec);
    p = x; q = gen_1;
    e = expi(p);
    if (e > b) return mpexp(itor(x, prec));
  }
  else
  {
    long ep, eq, B = usqrt(b) / 2;
    p = gel(x,1); ep = expi(p);
    q = gel(x,2); eq = expi(q);
    if (ep > B || eq > B) return mpexp(fractor(x, prec));
    e = ep - eq;
    if (e < -3) prec += nbits2extraprec(-e); /* see addrr 'extend' rule */
  }
  if (e > 2) { z0 = cgetr(prec); prec += EXTRAPREC64; b += BITS_IN_LONG; }
  z = cgetr(prec); av = avma;
  if (e > 0)
  { /* simplify x/2^e = p / (q * 2^e) */
    long v = minss(e, vali(p));
    if (v) p = shifti(p, -v);
    if (e - v) q = shifti(q, e - v);
  }
  s = signe(p);
  if (s < 0) p = negi(p);
  ex = exp2(dbllog2(x) - e) * 2.718281828; /* exp(1) * x / 2^e,  x / 2^e < 2 */
  nmax = (long)(1 + exp(dbllambertW0(M_LN2 * b / ex)) * ex);
  abpq_init(&S, nmax);
  S.a[0] = S.b[0] = S.p[0] = S.q[0] = gen_1;
  for (n = 1; n <= nmax; n++)
  {
    S.a[n] = gen_1;
    S.b[n] = gen_1;
    S.p[n] = p;
    S.q[n] = muliu(q, n);
  }
  abpq_sum(&R, 0, nmax, &S);
  if (s > 0) rdiviiz(R.T, R.Q, z); else rdiviiz(R.Q, R.T, z);
  if (e > 0)
  {
    q = z; while (e--) q = sqrr(q);
    if (z0) { affrr(q, z0); z = z0; } else affrr(q,z);
  }
  return gc_const(av,z);
}

GEN
gexp(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC: return expQ(x, prec);
    case t_REAL: return mpexp(x);
    case t_COMPLEX: return cxexp(x,prec);
    case t_PADIC: return Qp_exp(x);
    default:
    {
      pari_sp av = avma;
      GEN y;
      if (!(y = toser_i(x))) break;
      return gc_upto(av, serexp(y,prec));
    }
  }
  return trans_eval("exp",gexp,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                           AGM(X, Y)                            **/
/**                                                                **/
/********************************************************************/
static int
agmr_gap(GEN a, GEN b, long L)
{
  GEN d = subrr(b, a);
  return (signe(d) && expo(d) - expo(b) >= L);
}
/* assume x > 0 */
static GEN
agm1r_abs(GEN x)
{
  long l = realprec(x), L = 5-prec2nbits(l);
  GEN a1, b1, y = cgetr(l);
  pari_sp av = avma;

  a1 = addrr(real_1(l), x); shiftr_inplace(a1, -1);
  b1 = sqrtr_abs(x);
  while (agmr_gap(a1,b1,L))
  {
    GEN a = a1;
    a1 = addrr(a,b1); shiftr_inplace(a1, -1);
    b1 = sqrtr_abs(mulrr(a,b1));
  }
  affrr_fixlg(a1,y); return gc_const(av,y);
}

struct agmcx_gap_t { long L, ex, cnt; };

static void
agmcx_init(GEN x, long *prec, struct agmcx_gap_t *S)
{
  long l = precision(x);
  if (l) *prec = l;
  S->L = 1-prec2nbits(*prec);
  S->cnt = 0;
  S->ex = LONG_MAX;
}

static long
agmcx_a_b(GEN x, GEN *a1, GEN *b1, long prec)
{
  long rotate = 0;
  if (gsigne(real_i(x))<0)
  { /* Rotate by +/-Pi/2, so that the choice of the principal square
     * root gives the optimal AGM. So a1 = +/-I*a1, b1=sqrt(-x). */
    if (gsigne(imag_i(x))<0) { *a1=mulcxI(*a1);  rotate=-1; }
    else                     { *a1=mulcxmI(*a1); rotate=1; }
    x = gneg(x);
  }
  *b1 = gsqrt(x, prec);
  return rotate;
}
/* return 0 if we must stop the AGM loop (a=b or a ~ b), 1 otherwise */
static int
agmcx_gap(GEN a, GEN b, struct agmcx_gap_t *S)
{
  GEN d = gsub(b, a);
  long ex = S->ex;
  S->ex = gexpo(d);
  if (gequal0(d) || S->ex - gexpo(b) < S->L) return 0;
  /* if (S->ex >= ex) we're no longer making progress; twice in a row */
  if (S->ex < ex) S->cnt = 0;
  else
    if (S->cnt++) return 0;
  return 1;
}
static GEN
agm1cx(GEN x, long prec)
{
  struct agmcx_gap_t S;
  GEN a1, b1;
  pari_sp av = avma;
  long rotate;
  agmcx_init(x, &prec, &S);
  a1 = gtofp(gmul2n(gadd(real_1(prec), x), -1), prec);
  rotate = agmcx_a_b(x, &a1, &b1, prec);
  while (agmcx_gap(a1,b1,&S))
  {
    GEN a = a1;
    a1 = gmul2n(gadd(a,b1),-1);
    b1 = gsqrt(gmul(a,b1), prec);
  }
  if (rotate) a1 = rotate>0 ? mulcxI(a1):mulcxmI(a1);
  return gc_GEN(av,a1);
}

GEN
zellagmcx(GEN a0, GEN b0, GEN r, GEN t, long prec)
{
  struct agmcx_gap_t S;
  pari_sp av = avma;
  GEN x = gdiv(a0, b0), a1, b1;
  long rotate;
  agmcx_init(x, &prec, &S);
  a1 = gtofp(gmul2n(gadd(real_1(prec), x), -1), prec);
  r = gsqrt(gdiv(gmul(a1,gaddgs(r, 1)),gadd(r, x)), prec);
  t = gmul(r, t);
  rotate = agmcx_a_b(x, &a1, &b1, prec);
  while (agmcx_gap(a1,b1,&S))
  {
    GEN a = a1, b = b1;
    a1 = gmul2n(gadd(a,b),-1);
    b1 = gsqrt(gmul(a,b), prec);
    r = gsqrt(gdiv(gmul(a1,gaddgs(r, 1)),gadd(gmul(b, r), a )), prec);
    t = gmul(r, t);
  }
  if (rotate) a1 = rotate>0 ? mulcxI(a1):mulcxmI(a1);
  a1 = gmul(a1, b0);
  t = gatan(gdiv(a1,t), prec);
  /* send t to the fundamental domain if necessary */
  if (gsigne(real_i(t))<0) t = gadd(t, mppi(prec));
  return gc_upto(av,gdiv(t,a1));
}

static long
ser_cmp_expo(GEN A, GEN B)
{
  long e = -(long)HIGHEXPOBIT, d = valser(B) - valser(A);
  long i, la = lg(A), v = varn(B);
  for (i = 2; i < la; i++)
  {
    GEN a = gel(A,i), b;
    long ei;
    if (isexactzero(a)) continue;
    b = polcoef_i(B, i-2 + d, v);
    ei = gexpo(a);
    if (!isexactzero(b)) ei -= gexpo(b);
    e = maxss(e, ei);
  }
  return e;
}

static GEN
ser_agm1(GEN y, long prec)
{
  GEN a1 = y, b1 = gen_1;
  long l = lg(y)-2, l2 = 6-prec2nbits(prec), eold = LONG_MAX;
  for(;;)
  {
    GEN a = a1, p1;
    a1 = gmul2n(gadd(a,b1),-1);
    b1 = gsqrt(gmul(a,b1), prec);
    p1 = gsub(b1,a1);
    if (isinexactreal(p1))
    {
      long e = ser_cmp_expo(p1, b1);
      if (e < l2 || e >= eold) break;
      eold = e;
    }
    else if (valser(p1)-valser(b1) >= l || gequal0(p1)) break;
  }
  return a1;
}

/* agm(1,x) */
static GEN
agm1(GEN x, long prec)
{
  GEN y;
  pari_sp av;

  if (gequal0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_INT:
      if (!is_pm1(x)) break;
      return (signe(x) > 0)? real_1(prec): real_0(prec);

    case t_REAL: return signe(x) > 0? agm1r_abs(x): agm1cx(x, prec);

    case t_COMPLEX:
      if (gequal0(gel(x,2))) return agm1(gel(x,1), prec);
      return agm1cx(x, prec);

    case t_PADIC:
    {
      GEN a1 = x, b1 = gen_1;
      long l = precp(x);
      av = avma;
      for(;;)
      {
        GEN a = a1, p1;
        long ep;
        a1 = gmul2n(gadd(a,b1),-1);
        a = gmul(a,b1);
        b1 = Qp_sqrt(a); if (!b1) pari_err_SQRTN("Qp_sqrt",a);
        p1 = gsub(b1,a1); ep = valp(p1)-valp(b1);
        if (ep<=0) { b1 = gneg_i(b1); p1 = gsub(b1,a1); ep=valp(p1)-valp(b1); }
        if (ep >= l || gequal0(p1)) return gc_GEN(av,a1);
      }
    }

    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gc_GEN(av, ser_agm1(y, prec));
  }
  return trans_eval("agm",agm1,x,prec);
}

GEN
agm(GEN x, GEN y, long prec)
{
  pari_sp av;
  if (is_matvec_t(typ(y)))
  {
    if (is_matvec_t(typ(x))) pari_err_TYPE2("agm",x,y);
    swap(x, y);
  }
  if (gequal0(y)) return gcopy(y);
  av = avma;
  return gc_upto(av, gmul(y, agm1(gdiv(x,y), prec)));
}

/* b2 != 0 */
static GEN
ellK_i(GEN b2, long prec)
{ return gdiv(Pi2n(-1, prec), agm1(gsqrt(b2, prec), prec)); }
GEN
ellK(GEN k, long prec)
{
  pari_sp av = avma;
  GEN k2 = gsqr(k), b2 = gsubsg(1, k2);
  if (gequal0(b2)) pari_err_DOMAIN("ellK", "k^2", "=", gen_1, k2);
  return gc_upto(av, ellK_i(b2, prec));
}

static int
magm_gap(GEN a, GEN b, long L)
{
  GEN d = gsub(b, a);
  return !gequal0(d) && gexpo(d) - gexpo(b) >= L;
}

/* http://www.ams.org/notices/201208/rtx120801094p.pdf
 * An Eloquent Formula for the Perimeter of an Ellipse
 * Semjon Adlaj, Notices of the AMS */
static GEN
magm(GEN a, GEN b, long prec)
{
  long L = -prec2nbits(prec) + 16;
  GEN c = gen_0;
  while (magm_gap(a, b, L))
  {
    GEN u = gsqrt(gmul(gsub(a, c), gsub(b, c)), prec);
    a = gmul2n(gadd(a, b), -1);
    b = gadd(c, u); c = gsub(c, u);
  }
  return gmul2n(gadd(a, b), -1);
}

GEN
ellE(GEN k, long prec)
{
  pari_sp av = avma;
  GEN b2 = gsubsg(1, gsqr(k));
  if (gequal0(b2)) { set_avma(av); return real_1(prec); }
  return gc_upto(av, gmul(ellK_i(b2, prec), magm(gen_1, b2, prec)));
}

/********************************************************************/
/**                                                                **/
/**                             LOG(X)                             **/
/**                                                                **/
/********************************************************************/
/* log(2) = 18*atanh(1/26)-2*atanh(1/4801)+8*atanh(1/8749)
 * faster than 10*atanh(1/17)+4*atanh(13/499) for all precisions,
 * and than Pi/2M(1,4/2^n) ~ n log(2) for bitprec at least up to 10^8 */
static GEN
log2_split(long prec)
{
  GEN u = atanhuu(1, 26, prec);
  GEN v = atanhuu(1, 4801, prec);
  GEN w = atanhuu(1, 8749, prec);
  shiftr_inplace(v, 1); setsigne(v, -1);
  shiftr_inplace(w, 3);
  return addrr(mulur(18, u), addrr(v, w));
}
GEN
constlog2(long prec)
{
  pari_sp av;
  GEN tmp;
  if (glog2 && realprec(glog2) >= prec) return glog2;

  tmp = cgetr_block(prec);
  av = avma;
  affrr(log2_split(prec+EXTRAPREC64), tmp);
  swap_clone(&glog2,tmp);
  return gc_const(av,glog2);
}

GEN
mplog2(long prec) { return rtor(constlog2(prec), prec); }

/* dont check that q != 2^expo(q), done in logr_abs */
static GEN
logagmr_abs(GEN q)
{
  long prec = realprec(q), e = expo(q), lim;
  GEN z = cgetr(prec), y, Q, _4ovQ;
  pari_sp av = avma;

  incrprec(prec);
  lim = prec2nbits(prec) >> 1;
  Q = rtor(q,prec);
  shiftr_inplace(Q,lim-e); setsigne(Q,1);

  _4ovQ = invr(Q); shiftr_inplace(_4ovQ, 2); /* 4/Q */
  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^(e-lim) */
  y = divrr(Pi2n(-1, prec), agm1r_abs(_4ovQ));
  y = addrr(y, mulsr(e - lim, mplog2(prec)));
  affrr_fixlg(y, z); return gc_const(av,z);
}

/* sum_{k >= 0} y^(2k+1) / (2k+1), y close to 0 */
static GEN
logr_aux(GEN y)
{
  long k, L = realprec(y); /* should be ~ l+1 - (k-2) */
  /* log(x) = log(1+y) - log(1-y) = 2 sum_{k odd} y^k / k
   * Truncate the sum at k = 2n+1, the remainder is
   *   2 sum_{k >= 2n+3} y^k / k < 2y^(2n+3) / (2n+3)(1-y) < y^(2n+3)
   * We want y^(2n+3) < y 2^(-prec2nbits(L)), hence
   *   n+1 > -prec2nbits(L) /-log_2(y^2) */
  double d = -2*dbllog2r(y); /* ~ -log_2(y^2) */
  k = (long)(2*(prec2nbits(L) / d));
  k |= 1;
  if (k >= 3)
  {
    GEN T, S = cgetr(L), y2 = sqrr(y), unr = real_1(L);
    pari_sp av = avma;
    long s = 0, incs = (long)d, l1 = nbits2prec((long)d);
    setprec(S,  l1);
    setprec(unr,l1); affrr(divru(unr,k), S);
    for (k -= 2;; k -= 2) /* k = 2n+1, ..., 1 */
    { /* S = y^(2n+1-k)/(2n+1) + ... + 1 / k */
      setprec(y2, l1); T = mulrr(S,y2);
      if (k == 1) break;

      l1 += nbits2extraprec(dvmdsBIL(s + incs, &s)<<TWOPOTBITS_IN_LONG);
      if (l1>L) l1=L;
      setprec(S, l1);
      setprec(unr,l1);
      affrr(addrr(divru(unr, k), T), S); set_avma(av);
    }
    /* k = 1 special-cased for eficiency */
    y = mulrr(y, addsr(1,T)); /* = log(X)/2 */
  }
  return y;
}
/*return log(|x|), assuming x != 0 */
GEN
logr_abs(GEN X)
{
  long EX, L, m, k, a, b, l = lg(X), p = realprec(X);
  GEN z, x, y;
  ulong u;
  double d;

 /* Assuming 1 < x < 2, we want delta = x-1, 1-x/2, 1-1/x, or 2/x-1 small.
  * We have 2/x-1 > 1-x/2, 1-1/x < x-1. So one should be choosing between
  * 1-1/x and 1-x/2 ( crossover sqrt(2), worse ~ 0.29 ). To avoid an inverse,
  * we choose between x-1 and 1-x/2 ( crossover 4/3, worse ~ 0.33 ) */
  EX = expo(X);
  u = uel(X,2);
  k = 2;
  if (u > (~0UL / 3) * 2) { /* choose 1-x/2 */
    EX++; u = ~u;
    while (!u && ++k < l) { u = uel(X,k); u = ~u; }
  } else { /* choose x - 1 */
    u &= ~HIGHBIT; /* u - HIGHBIT, assuming HIGHBIT set */
    while (!u && ++k < l) u = uel(X,k);
  }
  if (k == l) return EX? mulsr(EX, mplog2(p)): real_0(p);
  a = bit_accuracy(k) + bfffo(u); /* ~ -log2 |1-x| */
  L = p+EXTRAPRECWORD;
  b = prec2nbits(L - (bit_accuracy(k))); /* take loss of accuracy into account */
  if (b > 24*a*log2(prec2lg(L)) && p > LOGAGM_LIMIT) return logagmr_abs(X);

  z = cgetr(EX? p: p - bit_accuracy(k));

 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use AGM). Set Y = x^(1/2^m), y = (Y - 1) / (Y + 1) and compute truncated
  * series sum y^(2k+1)/(2k+1): the costs is less than
  *    m b^2 + sum_{k <= n} ((2k+1) e + BITS_IN_LONG)^2
  * bit operations with |x-1| <  2^(1-a), |Y| < 2^(1-e) , m = e-a and b bits of
  * accuracy needed (+ BITS_IN_LONG since bit accuracies increase by
  * increments of BITS_IN_LONG), so
  * 4n^3/3 e^2 + n^2 2e BITS_IN_LONG+ n BITS_IN_LONG ~ m b^2, with n ~ b/2e
  * or b/6e + BITS_IN_LONG/2e + BITS_IN_LONG/2be ~ m
  *    B := (b / 6 + BITS_IN_LONG/2 + BITS_IN_LONG^2 / 2b) ~ m(m+a)
  *     m = min( -a/2 + sqrt(a^2/4 + B),  b - a )
  * NB: e ~ (b/6)^(1/2) as b -> oo
  * Instead of the above pessimistic estimate for the cost of the sum, use
  * optimistic estimate (BITS_IN_LONG -> 0) */
  d = -a/2.; m = (long)(d + sqrt(d*d + b/6)); /* >= 0 */

  if (m > b-a) m = b-a;
  if (m < 0.2*a) m = 0; else L += nbits2extraprec(m);
  x = rtor(X,L);
  setsigne(x,1); shiftr_inplace(x,-EX);
  /* 2/3 < x < 4/3 */
  for (k=1; k<=m; k++) x = sqrtr_abs(x);

  y = divrr(subrs(x,1), addrs(x,1)); /* = (x-1) / (x+1), close to 0 */
  y = logr_aux(y); /* log(1+y) - log(1-y) = log(x) */
  shiftr_inplace(y, m + 1);
  if (EX) y = addrr(y, mulsr(EX, mplog2(p+EXTRAPRECWORD)));
  affrr_fixlg(y, z); return gc_const((pari_sp)z, z);
}

/* assume Im(q) != 0 and precision(q) >= prec. Compute log(q) with accuracy
 * prec [disregard input accuracy] */
GEN
logagmcx(GEN q, long prec)
{
  GEN z = cgetc(prec), y, Q, a, b;
  long lim, e, ea, eb;
  pari_sp av = avma;
  int neg = 0;

  incrprec(prec);
  if (gsigne(gel(q,1)) < 0) { q = gneg(q); neg = 1; }
  lim = prec2nbits(prec) >> 1;
  Q = gtofp(q, prec);
  a = gel(Q,1);
  b = gel(Q,2);
  if (gequal0(a)) {
    affrr_fixlg(logr_abs(b), gel(z,1));
    y = Pi2n(-1, prec);
    if (signe(b) < 0) setsigne(y, -1);
    affrr_fixlg(y, gel(z,2)); return gc_const(av,z);
  }
  ea = expo(a);
  eb = expo(b);
  e = ea <= eb ? lim - eb : lim - ea;
  shiftr_inplace(a, e);
  shiftr_inplace(b, e);

  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^e */
  y = gdiv(Pi2n(-1, prec), agm1cx( gdivsg(4, Q), prec ));
  a = gel(y,1);
  b = gel(y,2);
  a = addrr(a, mulsr(-e, mplog2(prec)));
  if (realprec(a) <= LOWDEFAULTPREC) a = real_0_bit(expo(a));
  if (neg) b = gsigne(b) <= 0? gadd(b, mppi(prec))
                             : gsub(b, mppi(prec));
  affrr_fixlg(a, gel(z,1));
  affrr_fixlg(b, gel(z,2)); return gc_const(av,z);
}

GEN
mplog(GEN x)
{
  if (signe(x)<=0) pari_err_DOMAIN("mplog", "argument", "<=", gen_0, x);
  return logr_abs(x);
}

/* pe = p^e, p prime, 0 < x < pe a t_INT coprime to p. Return the (p-1)-th
 * root of 1 in (Z/pe)^* congruent to x mod p, resp x mod 4 if p = 2.
 * Simplified form of Zp_sqrtnlift: 1/(p-1) is trivial to compute */
GEN
Zp_teichmuller(GEN x, GEN p, long e, GEN pe)
{
  GEN q, z, p1;
  pari_sp av;
  ulong mask;
  if (absequaliu(p,2)) return (mod4(x) & 2)? subiu(pe,1): gen_1;
  if (e == 1) return icopy(x);
  av = avma;
  p1 = subiu(p, 1);
  mask = quadratic_prec_mask(e);
  q = p; z = remii(x, p);
  while (mask > 1)
  { /* Newton iteration solving z^{1 - p} = 1, z = x (mod p) */
    GEN w, t, qold = q;
    if (mask <= 3) /* last iteration */
      q = pe;
    else
    {
      q = sqri(q);
      if (mask & 1) q = diviiexact(q, p);
    }
    mask >>= 1;
    /* q <= qold^2 */
    if (lgefint(q) == 3)
    {
      ulong Z = uel(z,2), Q = uel(q,2), P1 = uel(p1,2);
      ulong W = (Q-1) / P1; /* -1/(p-1) + O(qold) */
      ulong T = Fl_mul(W, Fl_powu(Z,P1,Q) - 1, Q);
      Z = Fl_mul(Z, 1 + T, Q);
      z = utoi(Z);
    }
    else
    {
      w = diviiexact(subiu(qold,1),p1); /* -1/(p-1) + O(qold) */
      t = Fp_mul(w, subiu(Fp_pow(z,p1,q), 1), q);
      z = Fp_mul(z, addui(1,t), q);
    }
  }
  return gc_INT(av, z);
}

GEN
teichmullerinit(long p, long n)
{
  GEN t, pn, g, v;
  ulong gp, tp;
  long a, m;

  if (p == 2) return mkvec(gen_1);
  if (!uisprime(p)) pari_err_PRIME("teichmullerinit",utoipos(p));

  m = p >> 1; /* (p-1)/2 */
  tp= gp= pgener_Fl(p); /* order (p-1), gp^m = -1 */
  pn = powuu(p, n);
  v = cgetg(p, t_VEC);
  t = g = Zp_teichmuller(utoipos(gp), utoipos(p), n, pn);
  gel(v, 1) = gen_1;
  gel(v, p-1) = subiu(pn,1);
  for (a = 1; a < m; a++)
  {
    gel(v, tp) = t;
    gel(v, p - tp) = Fp_neg(t, pn); /* g^(m+a) = -g^a */
    if (a < m-1)
    {
      t = Fp_mul(t, g, pn); /* g^(a+1) */
      tp = Fl_mul(tp, gp, p); /* t mod p  */
    }
  }
  return v;
}

/* tab from teichmullerinit or NULL */
GEN
teichmuller(GEN x, GEN tab)
{
  GEN p, q, z;
  long n, tx = typ(x);

  if (!tab)
  {
    if (tx == t_VEC && lg(x) == 3)
    {
      p = gel(x,1);
      q = gel(x,2);
      if (typ(p) == t_INT && typ(q) == t_INT)
        return teichmullerinit(itos(p), itos(q));
    }
  }
  else if (typ(tab) != t_VEC) pari_err_TYPE("teichmuller",tab);
  if (tx!=t_PADIC) pari_err_TYPE("teichmuller",x);
  z = padic_u(x);
  if (!signe(z)) return gcopy(x);
  p = padic_p(x);
  q = padic_pd(x);
  n = precp(x);
  if (tab)
  {
    ulong pp = itou_or_0(p);
    if (lg(tab) != (long)pp) pari_err_TYPE("teichmuller",tab);
    z = gel(tab, umodiu(z, pp));
    if (typ(z) != t_INT) pari_err_TYPE("teichmuller",tab);
  }
  retmkpadic(tab? remii(z, q): Zp_teichmuller(z, p, n, q),
             icopy(p), icopy(q), 0, n);
}
GEN
teich(GEN x) { return teichmuller(x, NULL); }

GEN
glog(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;
  long l;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x) >= 0)
      {
        if (!signe(x)) pari_err_DOMAIN("log", "argument", "=", gen_0, x);
        return logr_abs(x);
      }
      retmkcomplex(logr_abs(x), mppi(realprec(x)));

    case t_FRAC:
    {
      GEN a, b;
      long e1, e2;
      av = avma;
      a = gel(x,1);
      b = gel(x,2);
      e1 = expi(subii(a,b)); e2 = expi(b);
      if (e2 > e1) prec += nbits2extraprec(e2 - e1);
      x = fractor(x, prec);
      return gc_upto(av, glog(x, prec));
    }
    case t_COMPLEX:
      if (ismpzero(gel(x,2))) return glog(gel(x,1), prec);
      l = precision(x); if (l > prec) prec = l;
      if (ismpzero(gel(x,1)))
      {
        GEN a = gel(x,2), b;
        av = avma; b = Pi2n(-1,prec);
        if (gsigne(a) < 0) { setsigne(b, -1); a = gabs(a,prec); }
        a = isint1(a) ? gen_0: glog(a,prec);
        return gc_GEN(av, mkcomplex(a, b));
      }
      if (prec >= LOGAGMCX_LIMIT) return logagmcx(x, prec);
      y = cgetg(3,t_COMPLEX);
      gel(y,2) = garg(x,prec); av = avma;
      gel(y,1) = gc_upto(av, gmul2n(glog(cxnorm(x),prec),-1)); return y;

    case t_PADIC: return Qp_log(x);
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (!signe(y)) pari_err_DOMAIN("log", "argument", "=", gen_0, x);
      if (valser(y)) pari_err_DOMAIN("log", "series valuation", "!=", gen_0, x);
      p1 = integser(gdiv(derivser(y), y)); /* log(y)' = y'/y */
      if (!gequal1(gel(y,2))) p1 = gadd(p1, glog(gel(y,2),prec));
      return gc_upto(av, p1);
  }
  return trans_eval("log",glog,x,prec);
}

static GEN
mplog1p(GEN x)
{
  long ex, a, b, l, L;
  if (!signe(x)) return rcopy(x);
  ex = expo(x); if (ex >= -3) return glog(addrs(x,1), 0);
  a = -ex;
  b = realprec(x); L = b+1;
  if (b > a*log2(L) && b > LOGAGM_LIMIT)
  {
    x = addrs(x,1); l = b + nbits2extraprec(a);
    if (realprec(x) < l) x = rtor(x,l);
    return logagmr_abs(x);
  }
  x = rtor(x, L);
  x = logr_aux(divrr(x, addrs(x,2)));
  if (realprec(x) > b) fixlg(x, b);
  shiftr_inplace(x,1); return x;
}

static GEN log1p_i(GEN x, long prec);
static GEN
cxlog1p(GEN x, long prec)
{
  pari_sp av;
  GEN z, a, b = gel(x,2);
  long l;
  if (ismpzero(b)) return log1p_i(gel(x,1), prec);
  l = precision(x); if (l > prec) prec = l;
  if (prec >= LOGAGMCX_LIMIT) return logagmcx(gaddgs(x,1), prec);
  a = gel(x,1);
  z = cgetg(3,t_COMPLEX); av = avma;
  a = gadd(gadd(gmul2n(a,1), gsqr(a)), gsqr(b));
  a = log1p_i(a, prec); shiftr_inplace(a,-1);
  gel(z,1) = gc_upto(av, a);
  gel(z,2) = garg(gaddgs(x,1),prec); return z;
}
static GEN
log1p_i(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mplog1p(x);
    case t_COMPLEX: return cxlog1p(x, prec);
    case t_PADIC: return Qp_log(gaddgs(x,1));
    default:
    {
      long ey;
      GEN y;
      if (!(y = toser_i(x))) break;
      ey = valser(y);
      if (ey < 0) pari_err_DOMAIN("log1p","valuation", "<", gen_0, x);
      if (gequal0(y)) return gcopy(y);
      if (ey)
        return glog(gaddgs(y,1),prec);
      else
      {
        GEN a = gel(y,2), a1 = gaddgs(a,1);
        y = gdiv(y, a1); gel(y,2) = gen_1;
        return gadd(glog1p(a,prec), glog(y, prec));
      }
    }
  }
  return trans_eval("log1p",glog1p,x,prec);
}
GEN
glog1p(GEN x, long prec)
{
  pari_sp av = avma;
  return gc_upto(av, log1p_i(x, prec));
}
/********************************************************************/
/**                                                                **/
/**                        SINE, COSINE                            **/
/**                                                                **/
/********************************************************************/

/* Reduce x0 mod Pi/2 to x in [-Pi/4, Pi/4]. Return cos(x)-1 */
static GEN
mpcosm1(GEN x, long *ptmod8)
{
  long a = expo(x), l = realprec(x), b, L, i, n, m, B;
  GEN y, u, x2;
  double d;

  n = 0;
  if (a >= 0)
  {
    long p;
    GEN q;
    if (a > 30)
    {
      GEN z, P = Pi2n(-2, nbits2prec(a + 32));
      z = addrr(x,P); /* = x + Pi/4 */
      if (expo(z) >= bit_prec(z) + 3) pari_err_PREC("mpcosm1");
      shiftr_inplace(P, 1);
      q = floorr(divrr(z, P)); /* round ( x / (Pi/2) ) */
      p = l+EXTRAPREC64; x = rtor(x,p);
    } else {
      q = stoi((long)floor(rtodbl(x) / (M_PI/2) + 0.5));
      p = l;
    }
    if (signe(q))
    {
      GEN y = subrr(x, mulir(q, Pi2n(-1,p))); /* x mod Pi/2  */
      long b = expo(y);
      if (a - b < 7) x = y;
      else
      {
        p += nbits2extraprec(a-b); x = rtor(x, p);
        x = subrr(x, mulir(q, Pi2n(-1,p)));
      }
      a = b;
      if (!signe(x) && a >= 0) pari_err_PREC("mpcosm1");
      n = Mod4(q);
    }
  }
  /* a < 0 */
  b = signe(x); *ptmod8 = (b < 0)? 4 + n: n;
  if (!b) return real_0_bit(expo(x)*2 - 1);

  b = prec2nbits(l);
  if (b + 2*a <= 0) {
    y = sqrr(x); shiftr_inplace(y, -1); setsigne(y, -1);
    return y;
  }

  y = cgetr(l);
  B = b/6 + BITS_IN_LONG/2 + (BITS_IN_LONG*BITS_IN_LONG/2)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 ,*/
  if (m < (-a) * 0.1) m = 0; /* not worth it */
  L = l + nbits2extraprec(m);

  b += m;
  d = 2.0 * (m-dbllog2r(x)-1/M_LN2); /* ~ 2( - log_2 Y - 1/log(2) ) */
  n = (long)(b / d);
  if (n > 1)
    n = (long)(b / (d + log2((double)n+1))); /* log~constant in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum Y^2k/(2k)!: this costs roughly
  *   m b^2 + sum_{k <= n} (2k e + BITS_IN_LONG)^2
  *   ~ (b/2e) b^2 / 3  + m b^2
  * bit operations with n ~ b/2e, |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and
  * b bits of accuracy needed, so
  *    B := (b / 6 + BITS_IN_LONG/2 + BITS_IN_LONG^2 / 2b) ~ m(m-a)
  * we want b ~ 6 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + b/6),  b/2 + a )
  * NB: e ~ (b/6)^(1/2) or b/2.
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  * < sum_{k >= n+1} Y^2k / 2k! < Y^(2n+2) / (2n+2)!(1-Y^2) < Y^(2n+2)/(2n+1)!
  * We want ... <= Y^2 2^-b, hence -2n log_2 |Y| + log_2 (2n+1)! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * 2n (-1/log(2) - log_2 |Y| + log_2(2n+2)) >= b  */
  x = rtor(x, L); shiftr_inplace(x, -m); setsigne(x, 1);
  x2 = sqrr(x);
  if (n == 1) { u = x2; shiftr_inplace(u, -1); setsigne(u, -1); } /*-Y^2/2*/
  else
  {
    GEN un = real_1(L);
    pari_sp av;
    long s = 0, l1 = nbits2prec((long)(d + n + 16));

    u = cgetr(L); av = avma;
    for (i = n; i >= 2; i--)
    {
      GEN t;
      setprec(x2,l1); t = divrunextu(x2, 2*i-1);
      l1 += nbits2extraprec(dvmdsBIL(s - expo(t), &s)<<TWOPOTBITS_IN_LONG);
      if (l1 > L) l1 = L;
      if (i != n) t = mulrr(t,u);
      setprec(un,l1); t = addrr_sign(un,1, t,-signe(t));
      setprec(u,l1); affrr(t,u); set_avma(av);
    }
    shiftr_inplace(u, -1); togglesign(u); /* u := -u/2 */
    setprec(x2,L); u = mulrr(x2,u);
  }
  /* Now u = sum {1<= i <=n} (-1)^i x^(2i) / (2i)! ~ cos(x) - 1 */
  for (i = 1; i <= m; i++)
  { /* u = cos(x)-1 <- cos(2x)-1 = 2cos(x)^2 - 2 = 4u + 2u^2*/
    GEN q = sqrr(u);
    shiftr_inplace(u, 1); u = addrr(u, q);
    shiftr_inplace(u, 1);
    if ((i & 31) == 0) u = gc_leaf((pari_sp)y, u);
  }
  affrr_fixlg(u, y); return y;
}

/* sqrt (|1 - (1+x)^2|) = sqrt(|x*(x+2)|). Sends cos(x)-1 to |sin(x)| */
static GEN
mpaut(GEN x)
{
  GEN t = mulrr(x, addsr(2,x)); /* != 0 */
  if (!signe(t)) return real_0_bit(expo(t) >> 1);
  return sqrtr_abs(t);
}

/********************************************************************/
/**                            COSINE                              **/
/********************************************************************/

GEN
mpcos(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y, z;

  if (!signe(x)) {
    long l = nbits2prec(-expo(x));
    if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
    return real_1(l);
  }
  av = avma; z = mpcosm1(x,&mod8);
  switch(mod8)
  {
    case 0: case 4: y = addsr(1,z); break;
    case 1: case 7: y = mpaut(z); togglesign(y); break;
    case 2: case 6: y = subsr(-1,z); break;
    default:        y = mpaut(z); break; /* case 3: case 5: */
  }
  return gc_leaf(av, y);
}

/* convert INT or FRAC to REAL, which is later reduced mod 2Pi : avoid
 * cancellation */
static GEN
tofp_safe(GEN x, long prec)
{
  return (typ(x) == t_INT || gexpo(x) > 0)? gadd(x, real_0(prec))
                                          : fractor(x, prec);
}

GEN
gcos(GEN x, long prec)
{
  pari_sp av;
  GEN a, b, u, v, y, u1, v1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpcos(x);
    case t_COMPLEX:
      a = gel(x,1);
      b = gel(x,2);
      if (isintzero(a)) return gcosh(b, prec);
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      if (typ(b) != t_REAL) b = gtofp(b, prec);
      mpsinhcosh(b, &u1, &v1); u1 = mpneg(u1);
      if (typ(a) != t_REAL) a = gtofp(a, prec);
      mpsincos(a, &u, &v);
      affrr_fixlg(gmul(v1,v), gel(y,1));
      affrr_fixlg(gmul(u1,u), gel(y,2)); return gc_const(av,y);

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcos(tofp_safe(x,prec)), y); return gc_const(av,y);

    case t_PADIC: y = cos_p(x);
      if (!y) pari_err_DOMAIN("gcos(t_PADIC)","argument","",gen_0,x);
      return y;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gc_upto(av, gaddsg(1,y));
      if (valser(y) < 0)
        pari_err_DOMAIN("cos","valuation", "<", gen_0, x);
      gsincos(y,&u,&v,prec);
      return gc_GEN(av,v);
  }
  return trans_eval("cos",gcos,x,prec);
}
/********************************************************************/
/**                             SINE                               **/
/********************************************************************/

GEN
mpsin(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y, z;

  if (!signe(x)) return real_0_bit(expo(x));
  av = avma; z = mpcosm1(x,&mod8);
  switch(mod8)
  {
    case 0: case 6: y = mpaut(z); break;
    case 1: case 5: y = addsr(1,z); break;
    case 2: case 4: y = mpaut(z); togglesign(y); break;
    default:        y = subsr(-1,z); break; /* case 3: case 7: */
  }
  return gc_leaf(av, y);
}

GEN
gsin(GEN x, long prec)
{
  pari_sp av;
  GEN a, b, u, v, y, v1, u1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpsin(x);
    case t_COMPLEX:
      a = gel(x,1);
      b = gel(x,2);
      if (isintzero(a)) retmkcomplex(gen_0,gsinh(b,prec));
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      if (typ(b) != t_REAL) b = gtofp(b, prec);
      mpsinhcosh(b, &u1, &v1);
      if (typ(a) != t_REAL) a = gtofp(a, prec);
      mpsincos(a, &u, &v);
      affrr_fixlg(gmul(v1,u), gel(y,1));
      affrr_fixlg(gmul(u1,v), gel(y,2)); return gc_const(av,y);

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpsin(tofp_safe(x,prec)), y); return gc_const(av,y);

    case t_PADIC: y = sin_p(x);
      if (!y) pari_err_DOMAIN("gsin(t_PADIC)","argument","",gen_0,x);
      return y;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gc_GEN(av, y);
      if (valser(y) < 0)
        pari_err_DOMAIN("sin","valuation", "<", gen_0, x);
      gsincos(y,&u,&v,prec);
      return gc_GEN(av,u);
  }
  return trans_eval("sin",gsin,x,prec);
}
/********************************************************************/
/**                       SINE, COSINE together                    **/
/********************************************************************/

void
mpsincos(GEN x, GEN *s, GEN *c)
{
  long mod8;
  pari_sp av, tetpil;
  GEN z;

  if (!signe(x))
  {
    long e = expo(x);
    *s = real_0_bit(e);
    *c = e >= 0? real_0_bit(e): real_1_bit(-e);
    return;
  }

  av = avma; z = mpcosm1(x, &mod8); tetpil = avma;
  switch(mod8)
  {
    case 0: *c = addsr( 1,z); *s = mpaut(z); break;
    case 1: *s = addsr( 1,z); *c = mpaut(z); togglesign(*c); break;
    case 2: *c = subsr(-1,z); *s = mpaut(z); togglesign(*s); break;
    case 3: *s = subsr(-1,z); *c = mpaut(z); break;
    case 4: *c = addsr( 1,z); *s = mpaut(z); togglesign(*s); break;
    case 5: *s = addsr( 1,z); *c = mpaut(z); break;
    case 6: *c = subsr(-1,z); *s = mpaut(z); break;
    case 7: *s = subsr(-1,z); *c = mpaut(z); togglesign(*c); break;
  }
  (void)gc_all_unsafe(av,tetpil,2,s,c);
}

/* SINE and COSINE - 1 */
void
mpsincosm1(GEN x, GEN *s, GEN *c)
{
  long mod8;
  pari_sp av, tetpil;
  GEN z;

  if (!signe(x))
  {
    long e = expo(x);
    *s = real_0_bit(e);
    *c = real_0_bit(2*e-1);
    return;
  }
  av = avma; z = mpcosm1(x,&mod8); tetpil = avma;
  switch(mod8)
  {
    case 0: *c = rcopy(z); *s = mpaut(z); break;
    case 1: *s = addsr(1,z); *c = addrs(mpaut(z),1); togglesign(*c); break;
    case 2: *c = subsr(-2,z); *s = mpaut(z); togglesign(*s); break;
    case 3: *s = subsr(-1,z); *c = subrs(mpaut(z),1); break;
    case 4: *c = rcopy(z); *s = mpaut(z); togglesign(*s); break;
    case 5: *s = addsr( 1,z); *c = subrs(mpaut(z),1); break;
    case 6: *c = subsr(-2,z); *s = mpaut(z); break;
    case 7: *s = subsr(-1,z); *c = subsr(-1,mpaut(z)); break;
  }
  (void)gc_all_unsafe(av,tetpil,2,s,c);
}

/* return exp(ix), x a t_REAL */
GEN
expIr(GEN x)
{
  pari_sp av = avma;
  GEN v = cgetg(3,t_COMPLEX);
  mpsincos(x, (GEN*)(v+2), (GEN*)(v+1));
  if (!signe(gel(v,2))) return gc_GEN(av, gel(v,1));
  return v;
}

/* return exp(ix)-1, x a t_REAL */
static GEN
expm1_Ir(GEN x)
{
  pari_sp av = avma;
  GEN v = cgetg(3,t_COMPLEX);
  mpsincosm1(x, (GEN*)(v+2), (GEN*)(v+1));
  if (!signe(gel(v,2))) return gc_GEN(av, gel(v,1));
  return v;
}

/* return exp(z)-1, z complex */
GEN
cxexpm1(GEN z, long prec)
{
  pari_sp av = avma;
  GEN X, Y, x = real_i(z), y = imag_i(z);
  long l = precision(z);
  if (l) prec = l;
  if (typ(x) != t_REAL) x = gtofp(x, prec);
  if (typ(y) != t_REAL) y = gtofp(y, prec);
  if (gequal0(y)) return mpexpm1(x);
  if (gequal0(x)) return expm1_Ir(y);
  X = mpexpm1(x); /* t_REAL */
  Y = expm1_Ir(y);
  /* exp(x+iy) - 1 = (exp(x)-1)(exp(iy)-1) + exp(x)-1 + exp(iy)-1 */
  return gc_upto(av, gadd(gadd(X,Y), gmul(X,Y)));
}

void
gsincos(GEN x, GEN *s, GEN *c, long prec)
{
  long i, j, ex, ex2, lx, ly, mi;
  pari_sp av, tetpil;
  GEN y, r, u, v, u1, v1, p1, p2, p3, p4, ps, pc;

  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      *s = cgetr(prec);
      *c = cgetr(prec); av = avma;
      mpsincos(tofp_safe(x, prec), &ps, &pc);
      affrr_fixlg(ps,*s);
      affrr_fixlg(pc,*c); set_avma(av); return;

    case t_REAL:
      mpsincos(x,s,c); return;

    case t_COMPLEX:
      i = precision(x); if (i) prec = i;
      ps = cgetc(prec); *s = ps;
      pc = cgetc(prec); *c = pc; av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1), &u,&v, prec);
      affrr_fixlg(mulrr(v1,u), gel(ps,1));
      affrr_fixlg(mulrr(u1,v), gel(ps,2));
      affrr_fixlg(mulrr(v1,v), gel(pc,1));
      affrr_fixlg(mulrr(u1,u), gel(pc,2)); togglesign(gel(pc,2));
      set_avma(av); return;

    case t_QUAD:
      av = avma; gsincos(quadtofp(x, prec), s, c, prec);
      (void)gc_all(av, 2, s, c); return;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) { *s = gc_GEN(av,y); *c = gaddsg(1,*s); return; }

      ex = valser(y); lx = lg(y); ex2 = 2*ex+2;
      if (ex < 0) pari_err_DOMAIN("gsincos","valuation", "<", gen_0, x);
      if (ex2 > lx)
      {
        *s = x == y? gcopy(y): gc_GEN(av, y); av = avma;
        *c = gc_upto(av, gsubsg(1, gdivgu(gsqr(y),2)));
        return;
      }
      if (!ex)
      {
        gsincos(serchop0(y),&u,&v,prec);
        gsincos(gel(y,2),&u1,&v1,prec);
        p1 = gmul(v1,v);
        p2 = gmul(u1,u);
        p3 = gmul(v1,u);
        p4 = gmul(u1,v); tetpil = avma;
        *c = gsub(p1,p2);
        *s = gadd(p3,p4);
        gc_all_unsafe(av,tetpil,2,s,c); return;
      }

      ly = lx+2*ex;
      mi = lx-1; while (mi>=3 && isrationalzero(gel(y,mi))) mi--;
      mi += ex-2;
      pc = cgetg(ly,t_SER); *c = pc;
      ps = cgetg(lx,t_SER); *s = ps;
      pc[1] = evalsigne(1) | _evalvalser(0) | evalvarn(varn(y));
      gel(pc,2) = gen_1; ps[1] = y[1];
      for (i=2; i<ex+2; i++) gel(ps,i) = gcopy(gel(y,i));
      for (i=3; i< ex2; i++) gel(pc,i) = gen_0;
      for (i=ex2; i<ly; i++)
      {
        long ii = i-ex;
        av = avma; p1 = gen_0;
        for (j=ex; j<=minss(ii-2,mi); j++)
          p1 = gadd(p1, gmulgu(gmul(gel(y,j-ex+2),gel(ps,ii-j)),j));
        gel(pc,i) = gc_upto(av, gdivgs(p1,2-i));
        if (ii < lx)
        {
          av = avma; p1 = gen_0;
          for (j=ex; j<=minss(i-ex2,mi); j++)
            p1 = gadd(p1,gmulgu(gmul(gel(y,j-ex+2),gel(pc,i-j)),j));
          p1 = gdivgu(p1,i-2);
          gel(ps,ii) = gc_upto(av, gadd(p1,gel(y,ii)));
        }
      }
      return;
  }
  pari_err_TYPE("gsincos",x);
}

/********************************************************************/
/**                                                                **/
/**                              SINC                              **/
/**                                                                **/
/********************************************************************/
static GEN
mpsinc(GEN x)
{
  pari_sp av = avma;
  GEN s, c;

  if (!signe(x)) {
    long l = nbits2prec(-expo(x));
    if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
    return real_1(l);
  }
  mpsincos(x,&s,&c);
  return gc_leaf(av, divrr(s,x));
}

GEN
gsinc(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, u1, v1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpsinc(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1)))
      {
        av = avma; x = gel(x,2);
        if (gequal0(x)) return gcosh(x,prec);
        return gc_leaf(av,gdiv(gsinh(x,prec),x));
      }
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affc_fixlg(gdiv(mkcomplex(gmul(v1,u), gmul(u1,v)), x), y);
      return gc_const(av,y);

    case t_INT:
      if (!signe(x)) return real_1(prec); /*fall through*/
    case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpsinc(tofp_safe(x,prec)), y); return gc_const(av,y);

    case t_PADIC:
      if (gequal0(x)) return cvtop(gen_1, padic_p(x), valp(x));
      av = avma; y = sin_p(x);
      if (!y) pari_err_DOMAIN("gsinc(t_PADIC)","argument","",gen_0,x);
      return gc_upto(av, gdiv(y,x));

    default:
    {
      long ex;
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gc_upto(av, gaddsg(1,y));
      ex = valser(y);
      if (ex < 0) pari_err_DOMAIN("sinc","valuation", "<", gen_0, x);
      if (ex)
      {
        gsincos(y,&u,&v,prec);
        y = gc_upto(av, gdiv(u,y));
        if (lg(y) > 2) gel(y,2) = gen_1;
        return y;
      }
      else
      {
        GEN z0, y0 = gel(y,2), y1 = serchop0(y), y10 = y1;
        if (!gequal1(y0)) y10 = gdiv(y10, y0);
        gsincos(y1,&u,&v,prec);
        z0 = gdiv(gcos(y0,prec), y0);
        y = gaddsg(1, y10);
        u = gadd(gmul(gsinc(y0, prec),v), gmul(z0, u));
        return gc_upto(av,gdiv(u,y));
      }
    }
  }
  return trans_eval("sinc",gsinc,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                     TANGENT and COTANGENT                      **/
/**                                                                **/
/********************************************************************/
static GEN
mptan(GEN x)
{
  pari_sp av = avma;
  GEN s, c;

  mpsincos(x,&s,&c);
  if (!signe(c))
    pari_err_DOMAIN("tan", "argument", "=", strtoGENstr("Pi/2 + kPi"),x);
  return gc_leaf(av, divrr(s,c));
}

/* If exp(-|im(x)|) << 1, avoid overflow in sincos(x) */
static int
tan_huge_im(GEN ix, long prec)
{
  long b, p = precision(ix);
  if (!p) p = prec;
  b = prec2nbits(p);
  return (gexpo(ix) > b || fabs(gtodouble(ix)) > (M_LN2 / 2) * b);
}
/* \pm I */
static GEN
real_I(long s, long prec)
{
  GEN z = cgetg(3, t_COMPLEX);
  gel(z,1) = real_0(prec);
  gel(z,2) = s > 0? real_1(prec): real_m1(prec); return z;
}

GEN
gtan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL: return mptan(x);

    case t_COMPLEX: {
      if (isintzero(gel(x,1))) retmkcomplex(gen_0,gtanh(gel(x,2),prec));
      if (tan_huge_im(gel(x,2), prec)) return real_I(gsigne(gel(x,2)), prec);
      av = avma; y = mulcxmI(gtanh(mulcxI(x), prec)); /* tan x = -I th(I x) */
      gel(y,1) = gcopy(gel(y,1)); return gc_upto(av, y);
    }
    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mptan(tofp_safe(x,prec)), y); return gc_const(av,y);

    case t_PADIC:
      av = avma;
      return gc_upto(av, gdiv(gsin(x,prec), gcos(x,prec)));

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gc_GEN(av, y);
      if (valser(y) < 0)
        pari_err_DOMAIN("tan","valuation", "<", gen_0, x);
      gsincos(y,&s,&c,prec);
      return gc_upto(av, gdiv(s,c));
  }
  return trans_eval("tan",gtan,x,prec);
}

static GEN
mpcotan(GEN x)
{
  pari_sp av = avma;
  GEN s,c;
  mpsincos(x,&s,&c); return gc_leaf(av, divrr(c,s));
}

GEN
gcotan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL:
      return mpcotan(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) {
        GEN z = cgetg(3, t_COMPLEX);
        gel(z,1) = gen_0; av = avma;
        gel(z,2) = gc_upto(av, gneg(ginv(gtanh(gel(x,2),prec))));
        return z;
      }
      if (tan_huge_im(gel(x,2), prec)) return real_I(-gsigne(gel(x,2)), prec);
      av = avma; gsincos(x,&s,&c,prec);
      return gc_upto(av, gdiv(c,s));

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcotan(tofp_safe(x,prec)), y); return gc_const(av,y);

    case t_PADIC:
      av = avma;
      return gc_upto(av, gdiv(gcos(x,prec), gsin(x,prec)));

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) pari_err_DOMAIN("cotan", "argument", "=", gen_0, y);
      if (valser(y) < 0) pari_err_DOMAIN("cotan","valuation", "<", gen_0, x);
      gsincos(y,&s,&c,prec);
      return gc_upto(av, gdiv(c,s));
  }
  return trans_eval("cotan",gcotan,x,prec);
}
