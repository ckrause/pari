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
/**                         LINEAR ALGEBRA                         **/
/**                         (second part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_mat

/*******************************************************************/
/*                                                                 */
/*                   CHARACTERISTIC POLYNOMIAL                     */
/*                                                                 */
/*******************************************************************/

static GEN
Flm_charpoly_i(GEN x, ulong p)
{
  long lx = lg(x), r, i;
  GEN H, y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol1_Flx(0); H = Flm_hess(x, p);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    ulong a = 1;
    GEN z, b = zero_Flx(0);
    for (i = r-1; i; i--)
    {
      a = Fl_mul(a, ucoeff(H,i+1,i), p);
      if (!a) break;
      b = Flx_add(b, Flx_Fl_mul(gel(y,i), Fl_mul(a,ucoeff(H,i,r),p), p), p);
    }
    z = Flx_sub(Flx_shift(gel(y,r), 1),
                Flx_Fl_mul(gel(y,r), ucoeff(H,r,r), p), p);
    /* (X - H[r,r])y[r] - b */
    gel(y,r+1) = gc_leaf(av2, Flx_sub(z, b, p));
  }
  return gel(y,lx);
}

GEN
Flm_charpoly(GEN x, ulong p)
{
  pari_sp av = avma;
  return gc_leaf(av, Flm_charpoly_i(x,p));
}

GEN
FpM_charpoly(GEN x, GEN p)
{
  pari_sp av = avma;
  long lx, r, i;
  GEN y, H;

  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    y = Flx_to_ZX(Flm_charpoly_i(ZM_to_Flm(x,pp), pp));
    return gc_upto(av, y);
  }
  lx = lg(x); y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol_1(0); H = FpM_hess(x, p);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    GEN z, a = gen_1, b = pol_0(0);
    for (i = r-1; i; i--)
    {
      a = Fp_mul(a, gcoeff(H,i+1,i), p);
      if (!signe(a)) break;
      b = ZX_add(b, ZX_Z_mul(gel(y,i), Fp_mul(a,gcoeff(H,i,r),p)));
    }
    b = FpX_red(b, p);
    z = FpX_sub(RgX_shift_shallow(gel(y,r), 1),
                FpX_Fp_mul(gel(y,r), gcoeff(H,r,r), p), p);
    z = FpX_sub(z,b,p);
    if (r+1 == lx) { gel(y,lx) = z; break; }
    gel(y,r+1) = gc_upto(av2, z); /* (X - H[r,r])y[r] - b */
  }
  return gc_upto(av, gel(y,lx));
}

GEN
charpoly0(GEN x, long v, long flag)
{
  if (v<0) v = 0;
  switch(flag)
  {
    case 0: return caradj(x,v,NULL);
    case 1: return caract(x,v);
    case 2: return carhess(x,v);
    case 3: return carberkowitz(x,v);
    case 4:
      if (typ(x) != t_MAT) pari_err_TYPE("charpoly",x);
      RgM_check_ZM(x, "charpoly");
      x = ZM_charpoly(x); setvarn(x, v); return x;
    case 5:
      return charpoly(x, v);
  }
  pari_err_FLAG("charpoly");
  return NULL; /* LCOV_EXCL_LINE */
}

/* (v - x)^d */
static GEN
caract_const(pari_sp av, GEN x, long v, long d)
{ return gc_upto(av, gpowgs(deg1pol_shallow(gen_1, gneg_i(x), v), d)); }

/* characteristic pol. Easy cases. Return NULL in case it's not so easy. */
static GEN
easychar(GEN x, long v)
{
  pari_sp av;
  long lx;
  GEN p1;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_FRAC: case t_PADIC:
      p1=cgetg(4,t_POL);
      p1[1]=evalsigne(1) | evalvarn(v);
      gel(p1,2) = gneg(x); gel(p1,3) = gen_1;
      return p1;

    case t_COMPLEX: case t_QUAD:
      p1 = cgetg(5,t_POL);
      p1[1] = evalsigne(1) | evalvarn(v);
      gel(p1,2) = gnorm(x); av = avma;
      gel(p1,3) = gc_upto(av, gneg(gtrace(x)));
      gel(p1,4) = gen_1; return p1;

    case t_FFELT: {
      pari_sp ltop=avma;
      p1 = FpX_to_mod(FF_charpoly(x), FF_p_i(x));
      setvarn(p1,v); return gc_upto(ltop,p1);
    }

    case t_POLMOD:
    {
      GEN A = gel(x,2), T = gel(x,1);
      long vx, vp;
      if (typ(A) != t_POL) return caract_const(avma, A, v, degpol(T));
      vx = varn(A);
      vp = varn(T);
      if (varncmp(vx, vp) > 0) return caract_const(avma, A, v, degpol(T));
      if (varncmp(vx, vp) < 0) pari_err_PRIORITY("charpoly", x, "<", vp);
      return RgXQ_charpoly(A, T, v);
    }
    case t_MAT:
      lx=lg(x);
      if (lx==1) return pol_1(v);
      if (lgcols(x) != lx) break;
      return NULL;
  }
  pari_err_TYPE("easychar",x);
  return NULL; /* LCOV_EXCL_LINE */
}
/* compute charpoly by mapping to Fp first, return lift to Z */
static GEN
RgM_Fp_charpoly(GEN x, GEN p, long v)
{
  GEN T;
  if (lgefint(p) == 3)
  {
    ulong pp = itou(p);
    T = Flm_charpoly_i(RgM_to_Flm(x, pp), pp);
    T = Flx_to_ZX(T);
  }
  else
    T = FpM_charpoly(RgM_to_FpM(x, p), p);
  setvarn(T, v); return T;
}
GEN
charpoly(GEN x, long v)
{
  GEN T, p = NULL;
  long prec;
  if ((T = easychar(x,v))) return T;
  switch(RgM_type(x, &p,&T,&prec))
  {
    case t_INT:
      T = ZM_charpoly(x); setvarn(T, v); break;
    case t_INTMOD:
      if (!BPSW_psp(p)) T = carberkowitz(x, v);
      else
      {
        pari_sp av = avma;
        T = RgM_Fp_charpoly(x,p,v);
        T = gc_upto(av, FpX_to_mod(T,p));
      }
      break;
    case t_REAL:
    case t_COMPLEX:
    case t_PADIC:
      T = carhess(x, v);
      break;
    default:
      T = carberkowitz(x, v);
  }
  return T;
}

/* p a t_POL in fetch_var_higher(); return p(pol_x(v)) and delete variable */
static GEN
fix_pol(GEN p, long v)
{
  long w = gvar2(p);
  if (w != NO_VARIABLE && varncmp(w, v) <= 0)
    p = poleval(p, pol_x(v));
  else
    setvarn(p, v);
  (void)delete_var(); return p;
}
/* characteristic polynomial of 1x1 matrix */
static GEN
RgM1_char(GEN x, long v)
{
  pari_sp av = avma;
  return gc_upto(av, gsub(pol_x(v), gcoeff(x,1,1)));
}
GEN
caract(GEN x, long v)
{
  pari_sp av = avma;
  GEN  T, C, x_k, Q;
  long k, n, w;

  if ((T = easychar(x,v))) return T;

  n = lg(x)-1;
  if (n == 1) return RgM1_char(x, v);

  w = fetch_var_higher();
  x_k = pol_x(w); /* to be modified in place */
  T = scalarpol(det(x), w); C = utoineg(n); Q = pol_x(w);
  for (k=1; k<=n; k++)
  {
    GEN mk = utoineg(k), d;
    gel(x_k,2) = mk;
    d = det(RgM_Rg_add_shallow(x, mk));
    T = RgX_add(RgX_mul(T, x_k), RgX_Rg_mul(Q, gmul(C, d)));
    if (k == n) break;

    Q = RgX_mul(Q, x_k);
    C = diviuexact(mulsi(k-n,C), k+1); /* (-1)^k binomial(n,k) */
  }
  return gc_upto(av, fix_pol(RgX_Rg_div(T, mpfact(n)), v));
}

/* C = charpoly(x, v) */
static GEN
RgM_adj_from_char(GEN x, long v, GEN C)
{
  if (varn(C) != v) /* problem with variable priorities */
  {
    C = gdiv(gsub(C, gsubst(C, v, gen_0)), pol_x(v));
    if (odd(lg(x))) C = RgX_neg(C); /* even dimension */
    return gsubst(C, v, x);
  }
  else
  {
    C = RgX_shift_shallow(C, -1);
    if (odd(lg(x))) C = RgX_neg(C); /* even dimension */
    return RgX_RgM_eval(C, x);
  }
}

GEN
FpM_trace(GEN x, GEN p)
{
  return Fp_red(ZM_trace(x), p);
}

ulong
Flm_trace(GEN x, ulong p)
{
  long i, lx = lg(x);
  ulong t;
  if (lx < 3) return lx == 1? 0: ucoeff(x,1,1);
  t = ucoeff(x,1,1);
  for (i = 2; i < lx; i++) t = Fl_add(t, ucoeff(x,i,i), p);
  return t;
}

/* assume x square matrice */
static GEN
mattrace(GEN x)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = gadd(t, gcoeff(x,i,i));
  return t;
}
static int
bad_char(GEN q, long n)
{
  forprime_t S;
  ulong p;
  if (!signe(q)) return 0;
  (void)u_forprime_init(&S, 2, n);
  while ((p = u_forprime_next(&S)))
    if (!umodiu(q, p)) return 1;
  return 0;
}
/* Using traces: return the characteristic polynomial of x (in variable v).
 * If py != NULL, the adjoint matrix is put there. */
GEN
caradj(GEN x, long v, GEN *py)
{
  pari_sp av, av0;
  long i, k, n, w;
  GEN T, y, t;

  if ((T = easychar(x, v)))
  {
    if (py)
    {
      if (typ(x) != t_MAT) pari_err_TYPE("matadjoint",x);
      *py = cgetg(1,t_MAT);
    }
    return T;
  }

  n = lg(x)-1;
  if (n == 0) { if (py) *py = cgetg(1,t_MAT); return pol_1(v); }
  if (n == 1) { if (py) *py = matid(1); return RgM1_char(x, v); }
  av0 = avma; w = fetch_var_higher();
  T = cgetg(n+3,t_POL); T[1] = evalsigne(1) | evalvarn(w);
  gel(T,n+2) = gen_1;
  av = avma; t = gc_upto(av, gneg(mattrace(x)));
  gel(T,n+1) = t;
  if (n == 2) {
    GEN a = gcoeff(x,1,1), b = gcoeff(x,1,2);
    GEN c = gcoeff(x,2,1), d = gcoeff(x,2,2);
    av = avma;
    gel(T,2) = gc_upto(av, gsub(gmul(a,d), gmul(b,c)));
    T = gc_upto(av, fix_pol(T, v));
    if (py) {
      y = cgetg(3, t_MAT);
      gel(y,1) = mkcol2(gcopy(d), gneg(c));
      gel(y,2) = mkcol2(gneg(b), gcopy(a));
      *py = y;
    }
    return T;
  }
  /* l > 3 */
  if (bad_char(residual_characteristic(x), n))
  { /* n! not invertible in base ring */
    (void)delete_var();
    T = charpoly(x, v);
    if (!py) return gc_upto(av, T);
    *py = RgM_adj_from_char(x, v, T); return gc_all(av, 2, &T,py);
  }
  av = avma; y = RgM_shallowcopy(x);
  for (i = 1; i <= n; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
  for (k = 2; k < n; k++)
  {
    GEN y0 = y;
    y = RgM_mul(y, x);
    t = gdivgs(mattrace(y), -k);
    for (i = 1; i <= n; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
    y = gclone(y);
    gel(T,n-k+2) = gc_GEN(av, t); av = avma;
    if (k > 2) gunclone(y0);
  }
  t = gmul(gcoeff(x,1,1),gcoeff(y,1,1));
  for (i=2; i<=n; i++) t = gadd(t, gmul(gcoeff(x,1,i),gcoeff(y,i,1)));
  gel(T,2) = gc_upto(av, gneg(t));
  T = gc_upto(av0, fix_pol(T, v));
  if (py) *py = odd(n)? gcopy(y): RgM_neg(y);
  gunclone(y); return T;
}

GEN
adj(GEN x)
{
  GEN y;
  (void)caradj(x, fetch_var(), &y);
  (void)delete_var(); return y;
}

GEN
adjsafe(GEN x)
{
  const long v = fetch_var();
  pari_sp av = avma;
  GEN C, A;
  if (typ(x) != t_MAT) pari_err_TYPE("matadjoint",x);
  if (lg(x) < 3) return gcopy(x);
  C = charpoly(x,v);
  A = RgM_adj_from_char(x, v, C);
  (void)delete_var(); return gc_upto(av, A);
}

GEN
matadjoint0(GEN x, long flag)
{
  switch(flag)
  {
    case 0: return adj(x);
    case 1: return adjsafe(x);
  }
  pari_err_FLAG("matadjoint");
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                       Frobenius form                            */
/*                                                                 */
/*******************************************************************/

/* The following section implement a mix of Ozello and Storjohann algorithms

P. Ozello, doctoral thesis (in French):
Calcul exact des formes de Jordan et de Frobenius d'une matrice, Chapitre 2
http://tel.archives-ouvertes.fr/tel-00323705

A. Storjohann,  Diss. ETH No. 13922
Algorithms for Matrix Canonical Forms, Chapter 9
https://cs.uwaterloo.ca/~astorjoh/diss2up.pdf

We use Storjohann Lemma 9.14 (step1, step2, step3) Ozello theorem 4,
and Storjohann Lemma 9.18
*/

/* Elementary transforms */

/* M <- U^(-1) M U, U = E_{i,j}(k) => U^(-1) = E{i,j}(-k)
 * P = U * P */
static void
transL(GEN M, GEN P, GEN k, long i, long j)
{
  long l, n = lg(M)-1;
  for(l=1; l<=n; l++) /* M[,j]-=k*M[,i] */
    gcoeff(M,l,j) = gsub(gcoeff(M,l,j), gmul(gcoeff(M,l,i), k));
  for(l=1; l<=n; l++) /* M[i,]+=k*M[j,] */
    gcoeff(M,i,l) = gadd(gcoeff(M,i,l), gmul(gcoeff(M,j,l), k));
  if (P)
    for(l=1; l<=n; l++)
      gcoeff(P,i,l) = gadd(gcoeff(P,i,l), gmul(gcoeff(P,j,l), k));
}

/* j = a or b */
static void
transD(GEN M, GEN P, long a, long b, long j)
{
  long l, n;
  GEN k = gcoeff(M,a,b), ki;

  if (gequal1(k)) return;
  ki = ginv(k); n = lg(M)-1;
  for(l=1; l<=n; l++)
    if (l!=j)
    {
      gcoeff(M,l,j) = gmul(gcoeff(M,l,j), k);
      gcoeff(M,j,l) = (j==a && l==b)? gen_1: gmul(gcoeff(M,j,l), ki);
    }
  if (P)
    for(l=1; l<=n; l++)
      gcoeff(P,j,l) = gmul(gcoeff(P,j,l), ki);
}

static void
transS(GEN M, GEN P, long i, long j)
{
  long l, n = lg(M)-1;
  swap(gel(M,i), gel(M,j));
  for (l=1; l<=n; l++)
    swap(gcoeff(M,i,l), gcoeff(M,j,l));
  if (P)
    for (l=1; l<=n; l++)
      swap(gcoeff(P,i,l), gcoeff(P,j,l));
}

/* Convert companion matrix to polynomial*/
static GEN
minpoly_polslice(GEN M, long i, long j, long v)
{
  long k, d = j+1-i;
  GEN P = cgetg(d+3,t_POL);
  P[1] = evalsigne(1)|evalvarn(v);
  for (k=0; k<d; k++)
    gel(P,k+2) = gneg(gcoeff(M,i+k, j));
  gel(P,d+2) = gen_1;
  return P;
}

static GEN
minpoly_listpolslice(GEN M, GEN V, long v)
{
  long i, n = lg(M)-1, nb = lg(V)-1;
  GEN W = cgetg(nb+1, t_VEC);
  for (i=1; i<=nb; i++)
    gel(W,i) = minpoly_polslice(M, V[i], i < nb? V[i+1]-1: n, v);
  return W;
}

static int
minpoly_dvdslice(GEN M, long i, long j, long k)
{
  pari_sp av = avma;
  long r = signe(RgX_rem(minpoly_polslice(M, i, j-1, 0),
                        minpoly_polslice(M, j, k, 0)));
  return gc_bool(av, r == 0);
}

static void
RgM_replace(GEN M, GEN M2)
{
  long n = lg(M)-1, m = nbrows(M), i, j;
  for(i=1; i<=n; i++)
    for(j=1; j<=m; j++) gcoeff(M, i, j) = gcoeff(M2, i, j);
}

static void
gc_mat2(pari_sp av, GEN M, GEN P)
{
  GEN M2 = M, P2 = P;
  (void)gc_all(av, P ? 2: 1, &M2, &P2);
  RgM_replace(M, M2);
  if (P) RgM_replace(P, P2);
}

/* Lemma 9.14 */
static long
weakfrobenius_step1(GEN M, GEN P, long j0)
{
  pari_sp av = avma;
  long n = lg(M)-1, k, j;
  for (j = j0; j < n; ++j)
  {
    if (gequal0(gcoeff(M, j+1, j)))
    {
      for (k = j+2; k <= n; ++k)
        if (!gequal0(gcoeff(M,k,j))) break;
      if (k > n) return j;
      transS(M, P, k, j+1);
    }
    transD(M, P, j+1, j, j+1);
    /* Now M[j+1,j] = 1 */
    for (k = 1; k <= n; ++k)
      if (k != j+1 && !gequal0(gcoeff(M,k,j))) /* zero M[k,j] */
      {
        transL(M, P, gneg(gcoeff(M,k,j)), k, j+1);
        gcoeff(M,k,j) = gen_0; /* avoid approximate 0 */
      }
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"RgM_minpoly stage 1: j0=%ld, j=%ld", j0, j);
      gc_mat2(av, M, P);
    }
  }
  return n;
}

static void
weakfrobenius_step2(GEN M, GEN P, long j)
{
  pari_sp av = avma;
  long i, k, n = lg(M)-1;
  for(i=j; i>=2; i--)
  {
    for(k=j+1; k<=n; k++)
      if (!gequal0(gcoeff(M,i,k)))
        transL(M, P, gcoeff(M,i,k), i-1, k);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"RgM_minpoly stage 2: j=%ld, i=%ld", j, i);
      gc_mat2(av, M, P);
    }
  }
}

static long
weakfrobenius_step3(GEN M, GEN P, long j0, long j)
{
  long i, k, n = lg(M)-1;
  if (j == n) return 0;
  if (gequal0(gcoeff(M, j0, j+1)))
  {
    for (k=j+2; k<=n; k++)
      if (!gequal0(gcoeff(M, j0, k))) break;
    if (k > n) return 0;
    transS(M, P, k, j+1);
  }
  transD(M, P, j0, j+1, j+1);
  for (i=j+2; i<=n; i++)
    if (!gequal0(gcoeff(M, j0, i)))
      transL(M, P, gcoeff(M, j0, i),j+1, i);
  return 1;
}

/* flag: 0 -> full Frobenius from , 1 -> weak Frobenius form */
static GEN
RgM_Frobenius(GEN M, long flag, GEN *pt_P, GEN *pt_v)
{
  pari_sp av = avma, av2, ltop;
  long n = lg(M)-1, eps, j0 = 1, nb = 0;
  GEN v, P;
  v = cgetg(n+1, t_VECSMALL);
  ltop = avma;
  P = pt_P ? matid(n): NULL;
  M = RgM_shallowcopy(M);
  av2 = avma;
  while (j0 <= n)
  {
    long j = weakfrobenius_step1(M, P, j0);
    weakfrobenius_step2(M, P, j);
    eps = weakfrobenius_step3(M, P, j0, j);
    if (eps == 0)
    {
      v[++nb] = j0;
      if (flag == 0 && nb > 1 && !minpoly_dvdslice(M, v[nb-1], j0, j))
      {
        j = j0; j0 = v[nb-1]; nb -= 2;
        transL(M, P, gen_1, j, j0); /*lemma 9.18*/
      } else
        j0 = j+1;
    }
    else
      transS(M, P, j0, j+1); /*theorem 4*/
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"weakfrobenius j0=%ld",j0);
      gc_mat2(av2, M, P);
    }
  }
  fixlg(v, nb+1);
  if (pt_v) *pt_v = v;
  (void)gc_all(pt_v ? ltop: av, P? 2: 1, &M, &P);
  if (pt_P) *pt_P = P;
  return M;
}

static GEN
RgM_minpoly(GEN M, long v)
{
  pari_sp av = avma;
  GEN V, W;
  if (lg(M) == 1) return pol_1(v);
  M = RgM_Frobenius(M, 1, NULL, &V);
  W = minpoly_listpolslice(M, V, v);
  if (varncmp(v,gvar2(W)) >= 0)
    pari_err_PRIORITY("matfrobenius", M, "<=", v);
  return gc_upto(av, RgX_normalize(glcm0(W, NULL)));
}

GEN
Frobeniusform(GEN V, long n)
{
  long i, j, k;
  GEN M = zeromatcopy(n,n);
  for (k=1,i=1;i<lg(V);i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (k+d-1 > n) pari_err_PREC("matfrobenius");
    for (j=0; j<d-1; j++, k++) gcoeff(M,k+1,k) = gen_1;
    for (j=0; j<d; j++) gcoeff(M,k-j,k) = gneg(gel(P, 1+d-j));
  }
  return M;
}

GEN
matfrobenius(GEN M, long flag, long v)
{
  long n;
  if (typ(M)!=t_MAT) pari_err_TYPE("matfrobenius",M);
  if (v < 0) v = 0;
  n = lg(M)-1;
  if (n && lgcols(M)!=n+1) pari_err_DIM("matfrobenius");
  if (flag > 2) pari_err_FLAG("matfrobenius");
  switch (flag)
  {
  case 0:
    return RgM_Frobenius(M, 0, NULL, NULL);
  case 1:
    {
      pari_sp av = avma;
      GEN V, W, F;
      F = RgM_Frobenius(M, 0, NULL, &V);
      W = minpoly_listpolslice(F, V, v);
      if (varncmp(v, gvar2(W)) >= 0)
        pari_err_PRIORITY("matfrobenius", M, "<=", v);
      return gc_upto(av, W);
    }
  case 2:
    {
      GEN P, F, R = cgetg(3, t_VEC);
      F = RgM_Frobenius(M, 0, &P, NULL);
      gel(R,1) = F; gel(R,2) = P;
      return R;
    }
  default:
    pari_err_FLAG("matfrobenius");
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/*******************************************************************/
/*                                                                 */
/*                       MINIMAL POLYNOMIAL                        */
/*                                                                 */
/*******************************************************************/

static GEN
RgXQ_minpoly_naive(GEN y, GEN P)
{
  long n = lgpol(P);
  GEN M = ker(RgXQ_matrix_pow(y,n,n,P));
  return content(RgM_to_RgXV(M,varn(P)));
}

static GEN
RgXQ_minpoly_FpXQ(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flxq_minpoly(RgX_to_Flx(x, pp),
                                   RgX_to_Flx(y, pp), pp));
  }
  else
    r = FpXQ_minpoly(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgXQ_minpoly_FpXQXQ(GEN x, GEN S, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r;
  GEN T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("minpoly",x,S);
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    GEN Tp = ZX_to_Flx(T, pp);
    r = FlxX_to_ZXX(FlxqXQ_minpoly(RgX_to_FlxqX(x, Tp, pp),
                                   RgX_to_FlxqX(S, Tp, pp), Tp, pp));
  }
  else
    r = FpXQXQ_minpoly(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(S, T, p), T, p);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
RgXQ_minpoly_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return RgXQ_minpoly_FpXQ(x, y, p);
    case t_FFELT:  return FFXQ_minpoly(x, y, pol);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgXQ_minpoly_FpXQXQ(x, y, pol, p);
    default:       return NULL;
  }
}

/* return caract(Mod(x,T)) in variable v */
GEN
RgXQ_minpoly(GEN x, GEN T, long v)
{
  pari_sp av = avma;
  GEN R = RgXQ_minpoly_fast(x,T);
  if (R) { setvarn(R, v); return R; }
  if (!issquarefree(T))
  {
    R = RgXQ_minpoly_naive(x, T);
    setvarn(R,v); return R;
  }
  R = RgXQ_charpoly(x, T, v);
  return gc_upto(av, RgX_div(R,RgX_gcd(R, RgX_deriv(R))));
}

static GEN
easymin(GEN x, long v)
{
  GEN G, R, dR;
  long tx = typ(x);
  if (tx == t_FFELT)
  {
    R = FpX_to_mod(FF_minpoly(x), FF_p_i(x));
    setvarn(R,v); return R;
  }
  if (tx == t_POLMOD)
  {
    GEN a = gel(x,2), b = gel(x,1);
    if (degpol(b)==0) return pol_1(v);
    if (typ(a) != t_POL || varn(a) != varn(b))
    {
      if (varncmp(gvar(a), v) <= 0) pari_err_PRIORITY("minpoly", x, "<", v);
      return deg1pol(gen_1, gneg_i(a), v);
    }
    return RgXQ_minpoly(a, b, v);
  }
  R = easychar(x, v); if (!R) return NULL;
  dR = RgX_deriv(R);  if (!lgpol(dR)) return NULL;
  G = RgX_normalize(RgX_gcd(R,dR));
  return RgX_div(R,G);
}
GEN
minpoly(GEN x, long v)
{
  pari_sp av = avma;
  GEN P;
  if (v < 0) v = 0;
  P = easymin(x,v);
  if (P) return gc_upto(av,P);
  /* typ(x) = t_MAT */
  set_avma(av); return RgM_minpoly(x,v);
}

/*******************************************************************/
/*                                                                 */
/*                       HESSENBERG FORM                           */
/*                                                                 */
/*******************************************************************/
static int
relative0(GEN a, GEN a0, long bit)
{
  if (gequal0(a)) return 1;
  if (gequal0(a0)) return gexpo(a) < bit;
  return (gexpo(a)-gexpo(a0) < bit);
}
/* x0 a nonempty square t_MAT that can be written to */
static GEN
RgM_hess(GEN x0, long prec)
{
  pari_sp av = avma;
  long lx = lg(x0), bit = prec? 8 - prec2nbits(prec): 0, m, i, j;
  GEN x = bit? RgM_shallowcopy(x0): x0;

  for (m=2; m<lx-1; m++)
  {
    GEN t = NULL;
    if (!bit)
    { /* first non-zero pivot */
      for (i=m+1; i<lx; i++)
        if (!gequal0(t = gcoeff(x,i,m-1))) break;
    }
    else
    { /* maximal pivot */
      long E = -(long)HIGHEXPOBIT, k = lx;
      for (i=m+1; i<lx; i++)
      {
        long e = gexpo(gcoeff(x,i,m-1));
        if (e > E) { E = e; k = i; t = gcoeff(x,i,m-1); }
      }
      if (k != lx && relative0(t, gcoeff(x0,k,m-1), bit)) k = lx;
      i = k;
    }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
    swap(gel(x,i), gel(x,m));
    if (bit)
    {
      for (j=m-1; j<lx; j++) swap(gcoeff(x0,i,j), gcoeff(x0,m,j));
      swap(gel(x0,i), gel(x0,m));
    }
    t = ginv(t);

    for (i=m+1; i<lx; i++)
    {
      GEN c = gcoeff(x,i,m-1);
      if (gequal0(c)) continue;

      c = gmul(c,t); gcoeff(x,i,m-1) = gen_0;
      for (j=m; j<lx; j++)
        gcoeff(x,i,j) = gsub(gcoeff(x,i,j), gmul(c,gcoeff(x,m,j)));
      for (j=1; j<lx; j++)
        gcoeff(x,j,m) = gadd(gcoeff(x,j,m), gmul(c,gcoeff(x,j,i)));
      if (gc_needed(av,2))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
        (void)gc_all(av,2, &x, &t);
      }
    }
  }
  return x;
}

GEN
hess(GEN x)
{
  pari_sp av = avma;
  GEN p = NULL, T = NULL;
  long prec, lx = lg(x);
  if (typ(x) != t_MAT) pari_err_TYPE("hess",x);
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");
  switch(RgM_type(x, &p, &T, &prec))
  {
    case t_REAL:
    case t_COMPLEX: break;
    default: prec = 0;
  }
  return gc_GEN(av, RgM_hess(RgM_shallowcopy(x),prec));
}

GEN
Flm_hess_pre(GEN x, ulong p, ulong pi)
{
  long lx = lg(x), m, i, j;
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");

  x = Flm_copy(x);
  for (m=2; m<lx-1; m++)
  {
    ulong t = 0;
    for (i=m+1; i<lx; i++) { t = ucoeff(x,i,m-1); if (t) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) lswap(ucoeff(x,i,j), ucoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = Fl_inv(t, p);

    for (i=m+1; i<lx; i++)
    {
      ulong c = ucoeff(x,i,m-1);
      if (!c) continue;
      if (pi)
      {
        c = Fl_mul_pre(c,t,p,pi); ucoeff(x,i,m-1) = 0;
        for (j=m; j<lx; j++)
          ucoeff(x,i,j) = Fl_sub(ucoeff(x,i,j), Fl_mul_pre(c,ucoeff(x,m,j), p, pi), p);
        for (j=1; j<lx; j++)
          ucoeff(x,j,m) = Fl_add(ucoeff(x,j,m), Fl_mul_pre(c,ucoeff(x,j,i), p, pi), p);
      } else
      {
        c = Fl_mul(c,t,p); ucoeff(x,i,m-1) = 0;
        for (j=m; j<lx; j++)
          ucoeff(x,i,j) = Fl_sub(ucoeff(x,i,j), Fl_mul(c,ucoeff(x,m,j), p), p);
        for (j=1; j<lx; j++)
          ucoeff(x,j,m) = Fl_add(ucoeff(x,j,m), Fl_mul(c,ucoeff(x,j,i), p), p);
      }
    }
  }
  return x;
}

GEN
Flm_hess(GEN x, ulong p)
{ return Flm_hess_pre(x, p, SMALL_ULONG(p)? 0: get_Fl_red(p)); }

GEN
FpM_hess(GEN x, GEN p)
{
  pari_sp av = avma;
  long lx = lg(x), m, i, j;
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    x = Flm_hess(ZM_to_Flm(x, pp), pp);
    return gc_upto(av, Flm_to_ZM(x));
  }
  x = RgM_shallowcopy(x);
  for (m=2; m<lx-1; m++)
  {
    GEN t = NULL;
    for (i=m+1; i<lx; i++) { t = gcoeff(x,i,m-1); if (signe(t)) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = Fp_inv(t, p);

    for (i=m+1; i<lx; i++)
    {
      GEN c = gcoeff(x,i,m-1);
      if (!signe(c)) continue;

      c = Fp_mul(c,t, p); gcoeff(x,i,m-1) = gen_0;
      for (j=m; j<lx; j++)
        gcoeff(x,i,j) = Fp_sub(gcoeff(x,i,j), Fp_mul(c,gcoeff(x,m,j),p), p);
      for (j=1; j<lx; j++)
        gcoeff(x,j,m) = Fp_add(gcoeff(x,j,m), Fp_mul(c,gcoeff(x,j,i),p), p);
      if (gc_needed(av,2))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
        (void)gc_all(av,2, &x, &t);
      }
    }
  }
  return gc_GEN(av,x);
}
/* H in Hessenberg form */
static GEN
RgM_hess_charpoly(GEN H, long v)
{
  long n = lg(H), r, i;
  GEN y = cgetg(n+1, t_VEC);
  gel(y,1) = pol_1(v);
  for (r = 1; r < n; r++)
  {
    pari_sp av2 = avma;
    GEN z, a = gen_1, b = pol_0(v);
    for (i = r-1; i; i--)
    {
      a = gmul(a, gcoeff(H,i+1,i));
      if (gequal0(a)) break;
      b = RgX_add(b, RgX_Rg_mul(gel(y,i), gmul(a,gcoeff(H,i,r))));
    }
    z = RgX_sub(RgX_shift_shallow(gel(y,r), 1),
                RgX_Rg_mul(gel(y,r), gcoeff(H,r,r)));
    gel(y,r+1) = gc_upto(av2, RgX_sub(z, b)); /* (X - H[r,r])y[r] - b */
  }
  return gel(y,n);
}
GEN
carhess(GEN x, long v)
{
  pari_sp av;
  GEN y;
  if ((y = easychar(x,v))) return y;
  av = avma; y = RgM_hess_charpoly(hess(x), fetch_var_higher());
  return gc_upto(av, fix_pol(y, v));
}

/* Bound for sup norm of charpoly(M/dM), M integral: let B = |M|oo / |dM|,
 *   s = max_k binomial(n,k) (kB^2)^(k/2),
 * return ceil(log2(s)) */
static long
charpoly_bound(GEN M, GEN dM, GEN N)
{
  pari_sp av = avma;
  GEN B = itor(N, LOWDEFAULTPREC);
  GEN s = real_0(LOWDEFAULTPREC), bin, B2;
  long n = lg(M)-1, k;
  bin = gen_1;
  if (dM) B = divri(B, dM);
  B2 = sqrr(B);
  for (k = n; k >= (n+1)>>1; k--)
  {
    GEN t = mulri(powruhalf(mulur(k, B2), k), bin);
    if (abscmprr(t, s) > 0) s = t;
    bin = diviuexact(muliu(bin, k), n-k+1);
  }
  return gc_long(av, ceil(dbllog2(s)));
}

static GEN
QM_charpoly_ZX_slice(GEN A, GEN dM, GEN P, GEN *mod)
{
  pari_sp av = avma;
  long i, n = lg(P)-1;
  GEN H, T;
  if (n == 1)
  {
    ulong p = uel(P,1), dp = dM ? umodiu(dM, p): 1;
    GEN Hp, a = ZM_to_Flm(A, p);
    Hp = Flm_charpoly_i(a, p);
    if (dp != 1) Hp = Flx_rescale(Hp, Fl_inv(dp, p), p);
    Hp = gc_upto(av, Flx_to_ZX(Hp));
    *mod = utoipos(p); return Hp;
  }
  T = ZV_producttree(P);
  A = ZM_nv_mod_tree(A, P, T);
  H = cgetg(n+1, t_VEC);
  for(i=1; i <= n; i++)
  {
    ulong p = uel(P,i), dp = dM ? umodiu(dM, p): 1;
    gel(H,i) = Flm_charpoly(gel(A, i), p);
    if (dp != 1) gel(H,i) = Flx_rescale(gel(H,i), Fl_inv(dp, p), p);
  }
  H = nxV_chinese_center_tree(H, P, T, ZV_chinesetree(P,T));
  *mod = gmael(T, lg(T)-1, 1); return gc_all(av, 2, &H, mod);
}

GEN
QM_charpoly_ZX_worker(GEN P, GEN M, GEN dM)
{
  GEN V = cgetg(3, t_VEC);
  gel(V,1) = QM_charpoly_ZX_slice(M, equali1(dM) ? NULL:dM, P, &gel(V,2));
  return V;
}

/* Assume M a square ZM, dM integer. Return charpoly(M / dM) in Z[X] */
static GEN
QM_charpoly_ZX_i(GEN M, GEN dM, long bound)
{
  long n = lg(M)-1;
  forprime_t S;
  GEN worker = snm_closure(is_entry("_QM_charpoly_ZX_worker"),
                           mkvec2(M, dM? dM: gen_1));
  if (!n) return pol_1(0);
  if (bound < 0)
  {
    GEN N = ZM_supnorm(M);
    if (signe(N) == 0) return monomial(gen_1, n, 0);
    bound = charpoly_bound(M, dM, N) + 1;
  }
  if (DEBUGLEVEL>5) err_printf("ZM_charpoly: bound 2^%ld\n", bound);
  init_modular_big(&S);
  return gen_crt("QM_charpoly_ZX", worker, &S, dM, bound, 0, NULL,
                 nxV_chinese_center, FpX_center);
}

GEN
QM_charpoly_ZX_bound(GEN M, long bit)
{
  pari_sp av = avma;
  GEN dM; M = Q_remove_denom(M, &dM);
  return gc_GEN(av, QM_charpoly_ZX_i(M, dM, bit));
}
GEN
QM_charpoly_ZX(GEN M)
{
  pari_sp av = avma;
  GEN dM; M = Q_remove_denom(M, &dM);
  return gc_GEN(av, QM_charpoly_ZX_i(M, dM, -1));
}
GEN
ZM_charpoly(GEN M)
{
  pari_sp av = avma;
  return gc_GEN(av, QM_charpoly_ZX_i(M, NULL, -1));
}

GEN
ZM_trace(GEN x)
{
  pari_sp av = avma;
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = addii(t, gcoeff(x,i,i));
  return gc_INT(av, t);
}

/*******************************************************************/
/*                                                                 */
/*        CHARACTERISTIC POLYNOMIAL (BERKOWITZ'S ALGORITHM)        */
/*                                                                 */
/*******************************************************************/
GEN
carberkowitz(GEN x, long v)
{
  long lx, i, j, k, r;
  GEN V, S, C, Q;
  pari_sp av0, av;
  if ((V = easychar(x,v))) return V;
  lx = lg(x); av0 = avma;
  V = cgetg(lx+1, t_VEC);
  S = cgetg(lx+1, t_VEC);
  C = cgetg(lx+1, t_VEC);
  Q = cgetg(lx+1, t_VEC);
  av = avma;
  gel(C,1) = gen_m1;
  gel(V,1) = gen_m1;
  for (i=2;i<=lx; i++) gel(C,i) = gel(Q,i) = gel(S,i) = gel(V,i) = gen_0;
  gel(V,2) = gcoeff(x,1,1);
  for (r = 2; r < lx; r++)
  {
    pari_sp av2;
    GEN t;

    for (i = 1; i < r; i++) gel(S,i) = gcoeff(x,i,r);
    gel(C,2) = gcoeff(x,r,r);
    for (i = 1; i < r-1; i++)
    {
      av2 = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
      for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
      gel(C,i+2) = gc_upto(av2, t);
      for (j = 1; j < r; j++)
      {
        av2 = avma; t = gmul(gcoeff(x,j,1), gel(S,1));
        for (k = 2; k < r; k++) t = gadd(t, gmul(gcoeff(x,j,k), gel(S,k)));
        gel(Q,j) = gc_upto(av2, t);
      }
      for (j = 1; j < r; j++) gel(S,j) = gel(Q,j);
    }
    av2 = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
    for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
    gel(C,r+1) = gc_upto(av2, t);
    if (gc_needed(av0,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"carberkowitz");
      (void)gc_all(av, 2, &C, &V);
    }
    for (i = 1; i <= r+1; i++)
    {
      av2 = avma; t = gmul(gel(C,i), gel(V,1));
      for (j = 2; j <= minss(r,i); j++)
        t = gadd(t, gmul(gel(C,i+1-j), gel(V,j)));
      gel(Q,i) = gc_upto(av2, t);
    }
    for (i = 1; i <= r+1; i++) gel(V,i) = gel(Q,i);
  }
  V = gtopoly(V, fetch_var_higher());
  if (!odd(lx)) V = RgX_neg(V);
  return gc_upto(av0, fix_pol(V, v));
}

/*******************************************************************/
/*                                                                 */
/*                            NORMS                                */
/*                                                                 */
/*******************************************************************/
GEN
gnorm(GEN x)
{
  pari_sp av;
  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return sqrr(x);
    case t_FRAC: return sqrfrac(x);
    case t_COMPLEX: av = avma; return gc_upto(av, cxnorm(x));
    case t_QUAD:    av = avma; return gc_upto(av, quadnorm(x));

    case t_POL: case t_SER: case t_RFRAC: av = avma;
      return gc_upto(av, greal(gmul(conj_i(x),x)));

    case t_FFELT:
      retmkintmod(FF_norm(x), FF_p(x));

    case t_POLMOD:
    {
      GEN T = gel(x,1), a = gel(x,2);
      if (typ(a) != t_POL || varn(a) != varn(T)) return gpowgs(a, degpol(T));
      return RgXQ_norm(a, T);
    }
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(gnorm(gel(x,i)));
  }
  pari_err_TYPE("gnorm",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* return |q|^2, complex modulus */
static GEN
cxquadnorm(GEN q, long prec)
{
  GEN X = gel(q,1), c = gel(X,2); /* (1-D)/4, -D/4 */
  if (signe(c) > 0) return quadnorm(q); /* imaginary */
  if (!prec) pari_err_TYPE("gnorml2", q);
  return sqrr(quadtofp(q, prec));
}

static GEN
gnorml2_i(GEN x, long prec)
{
  pari_sp av;
  long i, lx;
  GEN s;

  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return sqrr(x);
    case t_FRAC: return sqrfrac(x);
    case t_COMPLEX: av = avma; return gc_upto(av, cxnorm(x));
    case t_QUAD:    av = avma; return gc_upto(av, cxquadnorm(x,prec));

    case t_POL: lx = lg(x)-1; x++; break;

    case t_VEC:
    case t_COL:
    case t_MAT: lx = lg(x); break;

    default: pari_err_TYPE("gnorml2",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (lx == 1) return gen_0;
  av = avma;
  s = gnorml2(gel(x,1));
  for (i=2; i<lx; i++)
  {
    s = gadd(s, gnorml2(gel(x,i)));
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gnorml2");
      s = gc_upto(av, s);
    }
  }
  return gc_upto(av,s);
}
GEN
gnorml2(GEN x) { return gnorml2_i(x, 0); }

static GEN pnormlp(GEN,GEN,long);
static GEN
pnormlpvec(long i0, GEN x, GEN p, long prec)
{
  pari_sp av = avma;
  long i, lx = lg(x);
  GEN s = gen_0;
  for (i=i0; i<lx; i++)
  {
    s = gadd(s, pnormlp(gel(x,i),p,prec));
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gnormlp, i = %ld", i);
      s = gc_upto(av, s);
    }
  }
  return s;
}
/* (||x||_p)^p */
static GEN
pnormlp(GEN x, GEN p, long prec)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: x = mpabs(x); break;
    case t_FRAC: x = absfrac(x); break;
    case t_COMPLEX: case t_QUAD: x = gabs(x,prec); break;
    case t_POL: return pnormlpvec(2, x, p, prec);
    case t_VEC: case t_COL: case t_MAT: return pnormlpvec(1, x, p, prec);
    default: pari_err_TYPE("gnormlp",x);
  }
  return gpow(x, p, prec);
}

GEN
gnormlp(GEN x, GEN p, long prec)
{
  pari_sp av = avma;
  if (!p || (typ(p) == t_INFINITY && inf_get_sign(p) > 0))
    return gsupnorm(x, prec);
  if (gsigne(p) <= 0) pari_err_DOMAIN("normlp", "p", "<=", gen_0, p);
  if (is_scalar_t(typ(x))) return gabs(x, prec);
  if (typ(p) == t_INT)
  {
    ulong pp = itou_or_0(p);
    switch(pp)
    {
      case 1: return gnorml1(x, prec);
      case 2: x = gnorml2_i(x, prec); break;
      default: x = pnormlp(x, p, prec); break;
    }
    if (pp && typ(x) == t_INT && Z_ispowerall(x, pp, &x))
      return gc_leaf(av, x);
    if (pp == 2) return gc_upto(av, gsqrt(x, prec));
  }
  else
    x = pnormlp(x, p, prec);
  x = gpow(x, ginv(p), prec);
  return gc_upto(av, x);
}

GEN
gnorml1(GEN x,long prec)
{
  pari_sp av = avma;
  long lx,i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: return mpabs(x);
    case t_FRAC: return absfrac(x);

    case t_COMPLEX: case t_QUAD:
      return gabs(x,prec);

    case t_POL:
      lx = lg(x); s = gen_0;
      for (i=2; i<lx; i++) s = gadd(s, gnorml1(gel(x,i),prec));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gen_0;
      for (i=1; i<lx; i++) s = gadd(s, gnorml1(gel(x,i),prec));
      break;

    default: pari_err_TYPE("gnorml1",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return gc_upto(av, s);
}
/* As gnorml1, except for t_QUAD and t_COMPLEX: |x + wy| := |x| + |y|
 * Still a norm of R-vector spaces, and can be cheaply computed without
 * square roots */
GEN
gnorml1_fake(GEN x)
{
  pari_sp av = avma;
  long lx, i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: return mpabs(x);
    case t_FRAC: return absfrac(x);

    case t_COMPLEX:
      s = gadd(gnorml1_fake(gel(x,1)), gnorml1_fake(gel(x,2)));
      break;
    case t_QUAD:
      s = gadd(gnorml1_fake(gel(x,2)), gnorml1_fake(gel(x,3)));
      break;

    case t_POL:
      lx = lg(x); s = gen_0;
      for (i=2; i<lx; i++) s = gadd(s, gnorml1_fake(gel(x,i)));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gen_0;
      for (i=1; i<lx; i++) s = gadd(s, gnorml1_fake(gel(x,i)));
      break;

    default: pari_err_TYPE("gnorml1_fake",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return gc_upto(av, s);
}

static void
store(GEN z, GEN *m) { if (!*m || gcmp(z, *m) > 0) *m = z; }
/* compare |x| to *m or |x|^2 to *msq, whichever is easiest, and update
 * the pointed value if x is larger */
void
gsupnorm_aux(GEN x, GEN *m, GEN *msq, long prec)
{
  long i, lx;
  GEN z;
  switch(typ(x))
  {
    case t_COMPLEX: z = cxnorm(x); store(z, msq); return;
    case t_QUAD:  z = cxquadnorm(x,prec); store(z, msq); return;
    case t_INT: case t_REAL: z = mpabs(x); store(z,m); return;
    case t_FRAC: z = absfrac(x); store(z,m); return;
    case t_INFINITY: store(mkoo(), m);

    case t_POL: lx = lg(x)-1; x++; break;

    case t_VEC:
    case t_COL:
    case t_MAT: lx = lg(x); break;

    default: pari_err_TYPE("gsupnorm",x);
      return; /* LCOV_EXCL_LINE */
  }
  for (i=1; i<lx; i++) gsupnorm_aux(gel(x,i), m, msq, prec);
}
GEN
gsupnorm(GEN x, long prec)
{
  GEN m = NULL, msq = NULL;
  pari_sp av = avma;
  gsupnorm_aux(x, &m, &msq, prec);
  /* now set m = max (m, sqrt(msq)) */
  if (msq) {
    msq = gsqrt(msq, prec);
    if (!m || gcmp(m, msq) < 0) m = msq;
  } else if (!m) m = gen_0;
  return gc_GEN(av, m);
}

/*******************************************************************/
/*                                                                 */
/*                            TRACES                               */
/*                                                                 */
/*******************************************************************/
GEN
matcompanion(GEN x)
{
  long n = degpol(x), j;
  GEN y, c;

  if (typ(x)!=t_POL) pari_err_TYPE("matcompanion",x);
  if (!signe(x)) pari_err_DOMAIN("matcompanion","polynomial","=",gen_0,x);
  if (n == 0) return cgetg(1, t_MAT);

  y = cgetg(n+1,t_MAT);
  for (j=1; j < n; j++) gel(y,j) = col_ei(n, j+1);
  c = cgetg(n+1,t_COL); gel(y,n) = c;
  if (gequal1(gel(x, n+2)))
    for (j=1; j<=n; j++) gel(c,j) = gneg(gel(x,j+1));
  else
  { /* not monic. Hardly ever used */
    pari_sp av = avma;
    GEN d = gclone(gneg(gel(x,n+2)));
    set_avma(av);
    for (j=1; j<=n; j++) gel(c,j) = gdiv(gel(x,j+1), d);
    gunclone(d);
  }
  return y;
}

GEN
gtrace(GEN x)
{
  pari_sp av;
  long lx, tx = typ(x);
  GEN y, z;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gmul2n(x,1);

    case t_COMPLEX:
      return gmul2n(gel(x,1),1);

    case t_QUAD:
      y = gel(x,1);
      if (!gequal0(gel(y,3)))
      { /* assume quad. polynomial is either x^2 + d or x^2 - x + d */
        av = avma;
        return gc_upto(av, gadd(gel(x,3), gmul2n(gel(x,2),1)));
      }
      return gmul2n(gel(x,2),1);

    case t_POL:
      pari_APPLY_pol(gtrace(gel(x,i)));
    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      pari_APPLY_ser(gtrace(gel(x,i)));

    case t_POLMOD:
      y = gel(x,1); z = gel(x,2);
      if (typ(z) != t_POL || varn(y) != varn(z)) return gmulsg(degpol(y), z);
      av = avma;
      return gc_upto(av, RgXQ_trace(z, y));

    case t_FFELT:
      retmkintmod(FF_trace(x), FF_p(x));

    case t_RFRAC:
      av = avma; return gc_upto(av, gadd(x, conj_i(x)));

    case t_VEC: case t_COL:
      pari_APPLY_same(gtrace(gel(x,i)));

    case t_MAT:
      lx = lg(x); if (lx == 1) return gen_0;
      /*now lx >= 2*/
      if (lx != lgcols(x)) pari_err_DIM("gtrace");
      av = avma; return gc_upto(av, mattrace(x));
  }
  pari_err_TYPE("gtrace",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* Cholesky decomposition for positive definite matrix a
 * [GTM138, Algo 2.7.6, matrix Q]
 * If a is not positive definite return NULL. */
GEN
qfgaussred_positive(GEN a)
{
  pari_sp av = avma;
  GEN b;
  long i,j,k, n = lg(a);

  if (typ(a)!=t_MAT) pari_err_TYPE("qfgaussred_positive",a);
  if (n == 1) return cgetg(1, t_MAT);
  if (lgcols(a)!=n) pari_err_DIM("qfgaussred_positive");
  b = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN p1=cgetg(n,t_COL), p2=gel(a,j);

    gel(b,j) = p1;
    for (i=1; i<=j; i++) gel(p1,i) = gel(p2,i);
    for (   ; i<n ; i++) gel(p1,i) = gen_0;
  }
  for (k=1; k<n; k++)
  {
    GEN bk, p = gcoeff(b,k,k), invp;
    if (gsigne(p)<=0) return gc_NULL(av); /* not positive definite */
    invp = ginv(p);
    bk = row(b, k);
    for (i=k+1; i<n; i++) gcoeff(b,k,i) = gmul(gel(bk,i), invp);
    for (i=k+1; i<n; i++)
    {
      GEN c = gel(bk, i);
      for (j=i; j<n; j++)
        gcoeff(b,i,j) = gsub(gcoeff(b,i,j), gmul(c,gcoeff(b,k,j)));
    }
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"qfgaussred_positive");
      b=gc_GEN(av,b);
    }
  }
  return gc_GEN(av,b);
}

GEN
RgM_Cholesky(GEN M, long prec)
{
  pari_sp av = avma;
  long i, j, lM = lg(M);
  GEN R, L = qfgaussred_positive(M);
  if (!L) return gc_NULL(av);
  R = cgetg(lM, t_MAT); for (j = 1; j < lM; j++) gel(R,j) = cgetg(lM, t_COL);
  for (i = 1; i < lM; i++)
  {
    GEN r = gsqrt(gcoeff(L,i,i), prec);
    for (j = 1; j < lM; j++)
      gcoeff(R, i, j) = (i == j) ? r: gmul(r, gcoeff(L, i, j));
  }
  return gc_upto(av, R);
}

/* Maximal pivot strategy: x is a suitable pivot if it is non zero and either
 * - an exact type, or
 * - it is maximal among remaining nonzero (t_REAL) pivots */
static int
suitable(GEN x, long k, GEN *pp, long *pi)
{
  long t = typ(x);
  switch(t)
  {
    case t_INT: return signe(x) != 0;
    case t_FRAC: return 1;
    case t_REAL: {
      GEN p = *pp;
      if (signe(x) && (!p || abscmprr(p, x) < 0)) { *pp = x; *pi = k; }
      return 0;
    }
    default: return !gequal0(x);
  }
}

/* Gauss reduction (arbitrary symmetric matrix, only the part above the
 * diagonal is considered). If signature is nonzero, return only the
 * signature, in which case gsigne() should be defined for elements of a. */
static GEN
gaussred(GEN a, long signature)
{
  GEN r, ak, al;
  pari_sp av = avma, av1;
  long n = lg(a), i, j, k, l, sp, sn, t;

  if (typ(a) != t_MAT) pari_err_TYPE("gaussred",a);
  if (n == 1) return signature? mkvec2(gen_0, gen_0): cgetg(1, t_MAT);
  if (lgcols(a) != n) pari_err_DIM("gaussred");
  n--;
  r = const_vecsmall(n, 1); av1= avma;
  a = RgM_shallowcopy(a);
  t = n; sp = sn = 0;
  while (t)
  {
    long pind = 0;
    GEN invp, p = NULL;
    k=1; while (k<=n && (!r[k] || !suitable(gcoeff(a,k,k), k, &p, &pind))) k++;
    if (k > n && p) k = pind;
    if (k <= n)
    {
      p = gcoeff(a,k,k); invp = ginv(p); /* != 0 */
      if (signature) { /* skip if (!signature): gsigne may fail ! */
        if (gsigne(p) > 0) sp++; else sn++;
      }
      r[k] = 0; t--;
      ak = row(a, k);
      for (i=1; i<=n; i++)
        gcoeff(a,k,i) = r[i]? gmul(gcoeff(a,k,i), invp): gen_0;

      for (i=1; i<=n; i++) if (r[i])
      {
        GEN c = gel(ak,i); /* - p * a[k,i] */
        if (gequal0(c)) continue;
        for (j=1; j<=n; j++) if (r[j])
          gcoeff(a,i,j) = gsub(gcoeff(a,i,j), gmul(c,gcoeff(a,k,j)));
      }
      gcoeff(a,k,k) = p;
      if (gc_needed(av1,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gaussred (t = %ld)", t);
        a = gc_GEN(av1, a);
      }
    }
    else
    { /* all remaining diagonal coeffs are currently 0 */
      for (k=1; k<=n; k++) if (r[k])
      {
        l=k+1; while (l<=n && (!r[l] || !suitable(gcoeff(a,k,l), l, &p, &pind))) l++;
        if (l > n && p) l = pind;
        if (l > n) continue;

        p = gcoeff(a,k,l); invp = ginv(p);
        sp++; sn++;
        r[k] = r[l] = 0; t -= 2;
        ak = row(a, k);
        al = row(a, l);
        for (i=1; i<=n; i++) if (r[i])
        {
          gcoeff(a,k,i) = gmul(gcoeff(a,k,i), invp);
          gcoeff(a,l,i) = gmul(gcoeff(a,l,i), invp);
        } else {
          gcoeff(a,k,i) = gen_0;
          gcoeff(a,l,i) = gen_0;
        }

        for (i=1; i<=n; i++) if (r[i])
        { /* c = a[k,i] * p, d = a[l,i] * p; */
          GEN c = gel(ak,i), d = gel(al,i);
          for (j=1; j<=n; j++) if (r[j])
            gcoeff(a,i,j) = gsub(gcoeff(a,i,j),
                                 gadd(gmul(gcoeff(a,l,j), c),
                                      gmul(gcoeff(a,k,j), d)));
        }
        for (i=1; i<=n; i++) if (r[i])
        {
          GEN c = gcoeff(a,k,i), d = gcoeff(a,l,i);
          gcoeff(a,k,i) = gadd(c, d);
          gcoeff(a,l,i) = gsub(c, d);
        }
        gcoeff(a,k,l) = gen_1;
        gcoeff(a,l,k) = gen_m1;
        gcoeff(a,k,k) = gmul2n(p,-1);
        gcoeff(a,l,l) = gneg(gcoeff(a,k,k));
        if (gc_needed(av1,1))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"gaussred");
          a = gc_GEN(av1, a);
        }
        break;
      }
      if (k > n) break;
    }
  }
  if (!signature) return gc_GEN(av, a);
  set_avma(av); return mkvec2s(sp, sn);
}

GEN
qfgaussred(GEN a) { return gaussred(a,0); }

GEN
qfgaussred2(GEN a)
{
  pari_sp av = avma;
  GEN M = qfgaussred(a);
  long i, l = lg(M);
  GEN D = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    gel(D,i) = gcoeff(M,i,i);
    gcoeff(M,i,i) = gen_1;
  }
  return gc_GEN(av, mkvec2(M,D));
}

GEN
qfgaussred0(GEN a, long flag)
{
  switch (flag)
  {
    case 0: return qfgaussred(a);
    case 1: return qfgaussred2(a);
    default: pari_err_FLAG("qfgaussred");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
qfcholesky(GEN a, long prec)
{
  GEN M;
  long n = lg(a);
  if (typ(a) != t_MAT) pari_err_TYPE("qfcholesky",a);
  if (n == 1) return cgetg(1, t_MAT);
  if (lgcols(a) != lg(a)) pari_err_DIM("qfcholesky");
  M =  RgM_Cholesky(a, prec);
  if (!M) return cgetg(1, t_VEC);
  return M;
}

GEN
qfsign(GEN a) { return gaussred(a,1); }

/* x -= s(y+u*x) */
/* y += s(x-u*y), simultaneously */
static void
rot(GEN x, GEN y, GEN s, GEN u) {
  GEN x1 = subrr(x, mulrr(s,addrr(y,mulrr(u,x))));
  GEN y1 = addrr(y, mulrr(s,subrr(x,mulrr(u,y))));
  affrr(x1,x);
  affrr(y1,y);
}

/* Diagonalization of a REAL symmetric matrix. Return a vector [L, r]:
 * L = vector of eigenvalues
 * r = matrix of eigenvectors */
GEN
jacobi(GEN a, long prec)
{
  pari_sp av;
  long de, e, e1, e2, i, j, p, q, l = lg(a);
  GEN c, ja, L, r, L2, r2, unr, sqrt2;

  if (typ(a) != t_MAT) pari_err_TYPE("jacobi",a);
  ja = cgetg(3,t_VEC);
  L = cgetg(l,t_COL); gel(ja,1) = L;
  r = cgetg(l,t_MAT); gel(ja,2) = r;
  if (l == 1) return ja;
  if (lgcols(a) != l) pari_err_DIM("jacobi");

  e1 = HIGHEXPOBIT-1;
  for (j=1; j<l; j++)
  {
    GEN z = gtofp(gcoeff(a,j,j), prec);
    gel(L,j) = z;
    e = expo(z); if (e < e1) e1 = e;
  }
  for (j=1; j<l; j++)
  {
    gel(r,j) = cgetg(l,t_COL);
    for (i=1; i<l; i++) gcoeff(r,i,j) = utor(i==j? 1: 0, prec);
  }
  av = avma;

  e2 = -(long)HIGHEXPOBIT; p = q = 1;
  c = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    gel(c,j) = cgetg(j,t_COL);
    for (i=1; i<j; i++)
    {
      GEN z = gtofp(gcoeff(a,i,j), prec);
      gcoeff(c,i,j) = z;
      if (!signe(z)) continue;
      e = expo(z); if (e > e2) { e2 = e; p = i; q = j; }
    }
  }
  a = c; unr = real_1(prec);
  sqrt2 = sqrtr_abs(shiftr(unr, 1));
  de = prec2nbits(prec);

 /* e1 = min expo(a[i,i])
  * e2 = max expo(a[i,j]), i < j, occurs at a[p,q] (p < q)*/
  while (e1-e2 < de)
  {
    pari_sp av2 = avma;
    GEN x, y, t, c, s, u;
    /* compute attached rotation in the plane formed by basis vectors p and q */
    x = subrr(gel(L,q),gel(L,p));
    if (signe(x))
    {
      x = divrr(x, shiftr(gcoeff(a,p,q),1));
      y = sqrtr(addrr(unr, sqrr(x)));
      t = invr((signe(x)>0)? addrr(x,y): subrr(x,y));
      c = sqrtr(addrr(unr,sqrr(t)));
      s = divrr(t,c);
      u = divrr(t,addrr(unr,c));
    }
    else /* same formulas for t = 1.0 */
    {
      t = NULL; /* 1.0 */
      c = sqrt2;
      s = shiftr(c, -1);
      u = subrr(c, unr);
    }

    /* compute successive transforms of a and the matrix of accumulated
     * rotations (r) */
    for (i=1;   i<p; i++) rot(gcoeff(a,i,p), gcoeff(a,i,q), s,u);
    for (i=p+1; i<q; i++) rot(gcoeff(a,p,i), gcoeff(a,i,q), s,u);
    for (i=q+1; i<l; i++) rot(gcoeff(a,p,i), gcoeff(a,q,i), s,u);
    y = gcoeff(a,p,q); t = t? mulrr(t, y): rcopy(y);
    shiftr_inplace(y, -de - 1);
    affrr(subrr(gel(L,p),t), gel(L,p));
    affrr(addrr(gel(L,q),t), gel(L,q));
    for (i=1; i<l; i++) rot(gcoeff(r,i,p), gcoeff(r,i,q), s,u);

    e2 = -(long)HIGHEXPOBIT; p = q = 1;
    for (j=1; j<l; j++)
      for (i=1; i<j; i++)
      {
        GEN z = gcoeff(a,i,j);
        if (!signe(z)) continue;
        e = expo(z); if (e > e2) { e2 = e; p = i; q = j; }
      }
    set_avma(av2);
  }
  /* sort eigenvalues from smallest to largest */
  c = indexsort(L);
  r2 = vecpermute(r, c); for (i=1; i<l; i++) gel(r,i) = gel(r2,i);
  L2 = vecpermute(L, c); for (i=1; i<l; i++) gel(L,i) = gel(L2,i);
  set_avma(av); return ja;
}

/*************************************************************************/
/**                                                                     **/
/**                   Q-vector space -> Z-modules                       **/
/**                                                                     **/
/*************************************************************************/

GEN
matrixqz0(GEN x,GEN p)
{
  if (typ(x) != t_MAT) pari_err_TYPE("matrixqz",x);
  if (!p) return QM_minors_coprime(x,NULL);
  if (typ(p) != t_INT) pari_err_TYPE("matrixqz",p);
  if (signe(p)>=0) return QM_minors_coprime(x,p);
  if (!RgM_is_QM(x)) pari_err_TYPE("matrixqz", x);
  if (absequaliu(p,1)) return QM_ImZ(x); /* p = -1 */
  if (absequaliu(p,2)) return QM_ImQ(x); /* p = -2 */
  pari_err_FLAG("QM_minors_coprime");
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
QM_minors_coprime(GEN x, GEN D)
{
  pari_sp av = avma, av1;
  long i, j, m, n, lP;
  GEN P, y;

  n = lg(x)-1; if (!n) return gcopy(x);
  m = nbrows(x);
  if (n > m) pari_err_DOMAIN("QM_minors_coprime","n",">",strtoGENstr("m"),x);
  y = x; x = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(x,j) = Q_primpart(gel(y,j));
    RgV_check_ZV(gel(x,j), "QM_minors_coprime");
  }
  /* x now a ZM */
  if (n==m)
  {
    if (gequal0(ZM_det(x)))
      pari_err_DOMAIN("QM_minors_coprime", "rank(A)", "<",stoi(n),x);
    set_avma(av); return matid(n);
  }
  /* m > n */
  if (!D || gequal0(D))
  {
    pari_sp av2 = avma;
    D = ZM_detmult(shallowtrans(x));
    if (is_pm1(D)) { set_avma(av2); return ZM_copy(x); }
  }
  P = gel(Z_factor(D), 1); lP = lg(P);
  av1 = avma;
  for (i=1; i < lP; i++)
  {
    GEN p = gel(P,i), pov2 = shifti(p, -1);
    for(;;)
    {
      GEN N, M = FpM_ker(x, p);
      long lM = lg(M);
      if (lM==1) break;

      FpM_center_inplace(M, p, pov2);
      N = ZM_Z_divexact(ZM_mul(x,M), p);
      for (j=1; j<lM; j++)
      {
        long k = n; while (!signe(gcoeff(M,k,j))) k--;
        gel(x,k) = gel(N,j);
      }
      if (gc_needed(av1,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"QM_minors_coprime, p = %Ps", p);
        x = gc_GEN(av1, x); pov2 = shifti(p, -1);
      }
    }
  }
  return gc_GEN(av, x);
}

static GEN
QM_ImZ_all_i(GEN A, GEN *U, long remove, long hnf, long linindep)
{
  GEN V = NULL, D;
  A = Q_remove_denom(A,&D);
  if (D)
  {
    long l, lA;
    V = matkermod(A,D,NULL);
    l = lg(V); lA = lg(A);
    if (l == 1) V = scalarmat_shallow(D, lA-1);
    else
    {
      if (l < lA) V = hnfmodid(V,D);
      A = ZM_Z_divexact(ZM_mul(A, V), D);
    }
  }
  if (!linindep && ZM_rank(A)==lg(A)-1) linindep = 1;
  if (hnf || !linindep) A = ZM_hnflll(A, U, remove);
  if (U && V)
  {
    if (hnf)    *U = ZM_mul(V,*U);
    else        *U = V;
  }
  return A;
}
GEN
QM_ImZ_all(GEN x, GEN *U, long remove, long hnf)
{
  pari_sp av = avma;
  x = QM_ImZ_all_i(x, U, remove, hnf, 0);
  return gc_all(av, U?2:1, &x, &U);
}
GEN
QM_ImZ_hnfall(GEN x, GEN *U, long remove) { return QM_ImZ_all(x, U, remove, 1); }
GEN
QM_ImZ_hnf(GEN x) { return QM_ImZ_hnfall(x, NULL, 1); }
GEN
QM_ImZ(GEN x) { return QM_ImZ_all(x, NULL, 1, 0); }

GEN
QM_ImQ_all(GEN x, GEN *U, long remove, long hnf)
{
  pari_sp av = avma;
  long i, n = lg(x), m;
  GEN ir, V, D, c, K = NULL;

  if (U) *U = matid(n-1);
  if (n==1) return gcopy(x);
  m = lg(gel(x,1));

  x = RgM_shallowcopy(x);
  for (i=1; i<n; i++)
  {
    gel(x,i) = Q_primitive_part(gel(x,i), &c);
    if (U && c && signe(c)) gcoeff(*U,i,i) = ginv(c);
  }

  ir = ZM_indexrank(x);
  if (U)
  {
    *U = vecpermute(*U, gel(ir,2));
    if (remove < 2) K = ZM_ker(x);
  }
  x = vecpermute(x, gel(ir,2));

  D = absi(ZM_det(rowpermute(x,gel(ir,1))));
  x = RgM_Rg_div(x, D);
  x = QM_ImZ_all_i(x, U? &V: NULL, remove, hnf, 1);

  if (U)
  {
    *U = RgM_Rg_div(RgM_mul(*U,V),D);
    if (remove < 2) *U = shallowconcat(K,*U);
    if (!remove) x = shallowconcat(zeromatcopy(m-1,lg(K)-1), x);
    (void)gc_all(av, 2, &x, U);
  }
  else x = gc_GEN(av,x);
  return x;
}
GEN
QM_ImQ_hnfall(GEN x, GEN *U, long remove) { return QM_ImQ_all(x, U, remove, 1); }
GEN
QM_ImQ_hnf(GEN x) { return QM_ImQ_hnfall(x, NULL, 1); }
GEN
QM_ImQ(GEN x) { return QM_ImQ_all(x, NULL, 1, 0); }

GEN
intersect(GEN x, GEN y)
{
  long j, lx = lg(x);
  pari_sp av;
  GEN z;

  if (typ(x)!=t_MAT) pari_err_TYPE("intersect",x);
  if (typ(y)!=t_MAT) pari_err_TYPE("intersect",y);
  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);

  av = avma; z = ker(shallowconcat(x,y));
  for (j=lg(z)-1; j; j--) setlg(z[j], lx);
  return gc_upto(av, image(RgM_mul(x,z)));
}
