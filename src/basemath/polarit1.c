/* Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (first part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"
/*******************************************************************/
/*                                                                 */
/*                  POLYNOMIAL EUCLIDEAN DIVISION                  */
/*                                                                 */
/*******************************************************************/
/* x t_POLMOD, y t_POL in the same variable as x[1], return x % y */
static GEN
polmod_mod(GEN x, GEN y)
{
  GEN z, a, T = gel(x,1);
  if (RgX_equal(T, y)) return gcopy(x);
  z = cgetg(3,t_POLMOD); T = RgX_gcd(T,y); a = gel(x,2);
  gel(z,1) = T;
  gel(z,2) = (typ(a)==t_POL && varn(a)==varn(T))? RgX_rem(a, T): gcopy(a);
  return z;
}
/* x,y two "scalars", return 0 with type info */
static GEN
rem_scal_scal(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z = gadd(gmul(gen_0,x), gmul(gen_0,y));
  if (gequal0(y)) pari_err_INV("grem",y);
  return gc_upto(av, simplify(z));
}
/* x pol, y "scalar", return 0 with type info */
static GEN
rem_pol_scal(GEN x, GEN y)
{
  pari_sp av = avma;
  if (gequal0(y)) pari_err_INV("grem",y);
  return gc_upto(av, simplify(gmul(Rg_get_0(x),y)));
}
/* x "scalar", y pol, return x % y with type info */
static GEN
rem_scal_pol(GEN x, GEN y)
{
  if (degpol(y))
  {
    if (!signe(y)) pari_err_INV("grem",y);
    return gmul(x, Rg_get_1(y));
  }
  y = gel(y,2); return rem_scal_scal(x,y);
}
GEN
poldivrem(GEN x, GEN y, GEN *pr)
{
  const char *f = "euclidean division";
  long tx = typ(x), ty = typ(y), vx = gvar(x), vy = gvar(y);
  GEN z;

  if (!is_extscalar_t(tx) || !is_extscalar_t(ty)) pari_err_TYPE2(f,x,y);
  if (vx == vy && ((tx==t_POLMOD) ^ (ty==t_POLMOD))) pari_err_TYPE2(f,x,y);
  if (ty != t_POL || varncmp(vx, vy) < 0) /* y "scalar" */
  {
    if (!pr || pr == ONLY_DIVIDES) return gdiv(x,y);
    if (tx != t_POL || varncmp(vy, vx) < 0) /* x "scalar" */
      z = rem_scal_scal(x,y);
    else
      z = rem_pol_scal(x,y);
    if (pr == ONLY_REM) return z;
    *pr = z; return gdiv(x,y);
  }
  if (tx != t_POL || varncmp(vx, vy) > 0) /* x "scalar" */
  {
    if (!degpol(y)) /* constant t_POL, treat as scalar */
    {
      y = gel(y,2);
      if (!pr || pr == ONLY_DIVIDES) gdiv(x,y);
      z = rem_scal_scal(x,y);
      if (pr == ONLY_REM) return z;
      *pr = z; return gdiv(x,y);
    }
    if (!signe(y)) pari_err_INV("poldivrem",y);
    if (!pr || pr == ONLY_DIVIDES) return gequal0(x)? Rg_get_0(y): NULL;
    z = gmul(x, Rg_get_1(y));
    if (pr == ONLY_REM) return z;
    *pr = z; return Rg_get_0(y);
  }
  return RgX_divrem(x,y,pr);
}
GEN
gdeuc(GEN x, GEN y)
{
  const char *f = "euclidean division";
  long tx = typ(x), ty = typ(y), vx = gvar(x), vy = gvar(y);
  if (!is_extscalar_t(tx) || !is_extscalar_t(ty)) pari_err_TYPE2(f,x,y);
  if (vx == vy && ((tx==t_POLMOD) ^ (ty==t_POLMOD))) pari_err_TYPE2(f,x,y);
  if (ty != t_POL || varncmp(vx, vy) < 0) return gdiv(x,y); /* y "scalar" */
  if (tx != t_POL || varncmp(vx, vy) > 0)
  { /* x "scalar" */
    if (!signe(y)) pari_err_INV("gdeuc",y);
    if (!degpol(y)) return gdiv(x, gel(y,2)); /* constant */
    return Rg_get_0(y);
  }
  return RgX_div(x,y);
}
GEN
grem(GEN x, GEN y)
{
  const char *f = "euclidean division";
  long tx = typ(x), ty = typ(y), vx = gvar(x), vy = gvar(y);

  if (ty == t_POL)
  {
    if (varncmp(vx,vy) >= 0)
    {
      pari_sp av;
      GEN z;
      if (!signe(y)) pari_err_INV("grem",y);
      if (vx != vy) return rem_scal_pol(x,y);
      switch(tx)
      {
        case t_POLMOD: return polmod_mod(x,y);
        case t_POL: return RgX_rem(x,y);
        case t_RFRAC:
        {
          GEN a = gel(x,1), b = gel(x,2), p, pol;
          if (typ(a) == t_POL && RgX_is_ZX(y) && ZX_is_monic(y))
          {
            long pa, t = RgX_type2(a,b, &p,&pol,&pa);
            if (t == t_FRAC || t == t_INT) return QXQ_div(a, b, y);
          }
          av = avma; z = RgXQ_inv(RgX_rem(b, y), y);
          return gc_upto(av, grem(gmul(a, z), y));
        }
        case t_SER:
          if (RgX_is_monomial(y))
          {
            if (lg(x)-2 + valser(x) < degpol(y)) pari_err_OP("%",x,y);
            av = avma;
            return gc_upto(av, gmod(ser2rfrac_i(x), y));
          }
        default: pari_err_TYPE2("%",x,y);
      }
    }
    else switch(tx)
    {
      case t_POL:
      case t_RFRAC: return rem_pol_scal(x,y);
      default: pari_err_TYPE2("%",x,y);
    }
  }
  if (!is_extscalar_t(tx) || !is_extscalar_t(ty)) pari_err_TYPE2(f,x,y);
  if (vx == vy && ty==t_POLMOD) pari_err_TYPE2(f,x,y);
  if (tx != t_POL || varncmp(vx,vy) > 0)
  { /* x a "scalar" */
    if (ty != t_POL || varncmp(vx, vy) < 0) return rem_scal_scal(x,y);
    return rem_scal_pol(x,y);
  }
  if (ty != t_POL || varncmp(vx, vy) < 0) /* y a "scalar" */
    return rem_pol_scal(x,y);
  return RgX_rem(x,y);
}

/*******************************************************************/
/*                                                                 */
/*                  CONVERSIONS RELATED TO p-ADICS                 */
/*                                                                 */
/*******************************************************************/
/* x t_PADIC, p a prime or NULL (unset). Consistency check */
static void
check_padic_p(GEN x, GEN p)
{
  GEN q = padic_p(x);
  if (p && !equalii(p, q)) pari_err_MODULUS("Zp_to_Z", p,q);
}
/* shallow */
static GEN
Zp_to_Z(GEN x, GEN p) {
  switch(typ(x))
  {
    case t_INT: break;
    case t_PADIC:
      check_padic_p(x, p);
      x = gtrunc(x); break;
    default: pari_err_TYPE("Zp_to_Z",x);
  }
  return x;
}
/* shallow */
static GEN
ZpX_to_ZX(GEN x, GEN p)
{ pari_APPLY_pol_normalized(Zp_to_Z(gel(x,i), p)); }

static GEN
get_padic_content(GEN f, GEN p)
{
  GEN c = content(f);
  if (gequal0(c)) /*  O(p^n) can occur */
  {
    if (typ(c) != t_PADIC) pari_err_TYPE("QpX_to_ZX",f);
    check_padic_p(c, p);
    c = powis(p, valp(c));
  }
  return c;
}
/* make f suitable for [root|factor]padic. Shallow */
static GEN
QpX_to_ZX(GEN f, GEN p)
{
  GEN c = get_padic_content(f, p);
  f = RgX_Rg_div(f, c);
  return ZpX_to_ZX(f, p);
}

/* x in Z return x + O(pr), pr = p^r. Shallow */
static GEN
Z_to_Zp(GEN x, GEN p, GEN pr, long r)
{
  long v, sx = signe(x);

  if (!sx) return zeropadic_shallow(p,r);
  v = Z_pvalrem(x,p,&x);
  if (v) {
    if (r <= v) return zeropadic_shallow(p,r);
    r -= v;
    pr = powiu(p,r);
  }
  retmkpadic(modii(x,pr), p, pr, v, r);
}
/* shallow */
static GEN
ZV_to_ZpV(GEN z, GEN p, long r)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, typ(z)), q = powiu(p, r);
  for (i=1; i<l; i++) gel(Z,i) = Z_to_Zp(gel(z,i),p,q,r);
  return Z;
}
/* shallow */
static GEN
ZX_to_ZpX(GEN z, GEN p, GEN q, long r)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, t_POL); Z[1] = z[1];
  for (i=2; i<l; i++) gel(Z,i) = Z_to_Zp(gel(z,i),p,q,r);
  return Z;
}
/* return (x + O(p^r)) normalized (multiply by a unit such that leading coeff
 * is a power of p), x in Z[X] (or Z_p[X]). Shallow */
static GEN
ZX_to_ZpX_normalized(GEN x, GEN p, GEN pr, long r)
{
  long i, lx = lg(x);
  GEN z, lead = leading_coeff(x);

  if (gequal1(lead)) return ZX_to_ZpX(x, p, pr, r);
  (void)Z_pvalrem(lead, p, &lead); lead = Fp_inv(lead, pr);
  z = cgetg(lx,t_POL);
  for (i=2; i < lx; i++) gel(z,i) = Z_to_Zp(mulii(lead,gel(x,i)),p,pr,r);
  z[1] = x[1]; return z;
}
static GEN
ZXV_to_ZpXQV(GEN z, GEN T, GEN p, long r)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, typ(z)), q = powiu(p, r);
  T = ZX_copy(T);
  for (i=1; i<lg(z); i++) gel(Z,i) = mkpolmod(ZX_to_ZpX(gel(z,i),p,q,r),T);
  return Z;
}
/* shallow */
static GEN
QpXQX_to_ZXY(GEN f, GEN p)
{
  GEN c = get_padic_content(f, p);
  long i, l = lg(f);
  f = RgX_Rg_div(f,c);
  for (i=2; i<l; i++)
  {
    GEN t = gel(f,i);
    switch(typ(t))
    {
      case t_POLMOD:
        t = gel(t,2);
        t = (typ(t) == t_POL)? ZpX_to_ZX(t, p): Zp_to_Z(t, p);
        break;
      case t_POL: t = ZpX_to_ZX(t, p); break;
      default: t = Zp_to_Z(t, p); break;
    }
    gel(f,i) = t;
  }
  return f;
}

/*******************************************************************/
/*                                                                 */
/*                         p-ADIC ROOTS                            */
/*                                                                 */
/*******************************************************************/

/* f primitive ZX, squarefree, leading term prime to p; 0 <= a < p such that
 * f(a) = 0 mod p. Return p-adic roots of f equal to a mod p, in
 * precision >= prec */
GEN
ZX_Zp_root(GEN f, GEN a, GEN p, long prec)
{
  GEN z, R;
  long i, j, k;

  if (signe(FpX_eval(FpX_deriv(f, p), a, p)))
  { /* simple zero mod p, go all the way to p^prec */
    if (prec > 1) a = ZpX_liftroot(f, a, p, prec);
    return mkcol(a);
  }

  f = ZX_unscale_div(ZX_Z_translate(f,a), p); /* f(pX + a) / p */
  (void)ZX_pvalrem(f,p,&f);
  z = cgetg(degpol(f)+1,t_COL);

  R = FpX_roots(f, p);
  for (j=i=1; i<lg(R); i++)
  {
    GEN u = ZX_Zp_root(f, gel(R,i), p, prec-1);
    for (k=1; k<lg(u); k++) gel(z,j++) = addii(a, mulii(p, gel(u,k)));
  }
  setlg(z,j); return z;
}

/* a t_PADIC, return vector of p-adic roots of f equal to a (mod p) */
GEN
Zp_appr(GEN f, GEN a)
{
  pari_sp av = avma;
  GEN z, p = padic_p(a);
  long v = valp(a), prec = v;

  if (signe(padic_u(a))) prec += precp(a);
  f = QpX_to_ZX(f, p);
  if (degpol(f) <= 0) pari_err_CONSTPOL("Zp_appr");
  if (v < 0) pari_err_DOMAIN("padicappr", "v(a)", "<", gen_0, stoi(v));
  f = ZX_radical(f);
  a = padic_to_Fp(a, p);
  if (signe(FpX_eval(f,a,p))) retgc_const(av, cgetg(1, t_COL));
  z = ZX_Zp_root(f, a, p, prec);
  return gc_GEN(av, ZV_to_ZpV(z, p, prec));
}
static long
pval(GEN x, GEN p) { return typ(x) == t_INT? Z_pval(x,p): ZX_pval(x,p); }
/* f a ZXX, f(0) != 0 */
static GEN
pnormalize(GEN f, GEN p, GEN T, long prec, long n,
           GEN *plead, long *pprec, int *prev)
{
  *plead = leading_coeff(f);
  *pprec = prec;
  *prev = 0;
  if (!isint1(*plead))
  {
    long v = pval(*plead,p), v1 = pval(constant_coeff(f),p);
    if (v1 < v)
    {
      *prev = 1;
      f = RgX_recip_i(f); /* f(0) != 0 so degree is the same */
     /* beware loss of precision from lc(factor), whose valuation is <= v */
      *pprec += v; v = v1;
    }
    *pprec += v * n;
  }
  if (!T) return ZX_Q_normalize(f, plead);
  *plead = gen_1;
  return FpXQX_normalize(f, T, powiu(p,*pprec));
}

/**************************************************************************/

static void
scalar_getprec(GEN x, long *pprec, GEN *pp)
{
  if (typ(x)==t_PADIC)
  {
    long e = valp(x); if (signe(padic_u(x))) e += precp(x);
    if (e < *pprec) *pprec = e;
    check_padic_p(x, *pp);
    *pp = padic_p(x);
  }
}
static void
getprec(GEN x, long *pprec, GEN *pp)
{
  long i;
  if (typ(x) != t_POL) scalar_getprec(x, pprec, pp);
  else
    for (i = lg(x)-1; i>1; i--) scalar_getprec(gel(x,i), pprec, pp);
}

/* assume f(a) = 0 (mod T,p) */
static GEN
ZXY_ZpQ_root(GEN f, GEN a, GEN T, GEN p, long prec)
{
  GEN z, R;
  long i, j, k, lR;
  if (signe(FqX_eval(FqX_deriv(f,T,p), a, T,p)))
  { /* simple zero mod (T,p), go all the way to p^prec */
    if (prec > 1) a = ZpXQX_liftroot(f, a, T, p, prec);
    return mkcol(a);
  }
  f = RgX_unscale(RgXQX_RgXQ_translate(f, a, T), p);
  f = RgX_Rg_div(f, powiu(p, gvaluation(f,p)));
  z = cgetg(degpol(f)+1,t_COL);
  R = FpXQX_roots(FqX_red(f,T,p), T, p); lR = lg(R);
  for(j=i=1; i<lR; i++)
  {
    GEN u = ZXY_ZpQ_root(f, gel(R,i), T, p, prec-1);
    for (k=1; k<lg(u); k++) gel(z,j++) = gadd(a, gmul(p, gel(u,k)));
  }
  setlg(z,j); return z;
}

/* a belongs to finite extension of Q_p, return all roots of f equal to a
 * mod p. Don't assume f(a) = 0 (mod p) */
GEN
padicappr(GEN f, GEN a)
{
  GEN p, z, T, Tp;
  long prec;
  pari_sp av = avma;

  if (typ(f)!=t_POL) pari_err_TYPE("padicappr",f);
  switch(typ(a)) {
    case t_PADIC: return Zp_appr(f,a);
    case t_POLMOD: break;
    default: pari_err_TYPE("padicappr",a);
  }
  if (gequal0(f)) pari_err_ROOTS0("padicappr");
  T = gel(a,1);
  a = gel(a,2);
  p = NULL; prec = LONG_MAX;
  getprec(a, &prec, &p);
  getprec(T, &prec, &p); if (!p) pari_err_TYPE("padicappr",T);
  f = QpXQX_to_ZXY(f, p);
  if (typ(a) != t_POL) a = scalarpol_shallow(a, varn(T));
  a = ZpX_to_ZX(a,p);
  T = QpX_to_ZX(T,p);
  /* ensure that f /= (f,f') is separable */
  (void)nfgcd_all(f, RgX_deriv(f), T, NULL, &f);

  Tp = FpX_red(T, p); a = FqX_red(a, Tp, p);
  if (!gequal0(FqX_eval(FqX_red(f,Tp,p), a, Tp,p)))
  retgc_const(av, cgetg(1, t_COL)); /* f(a) != 0 (mod p,T) */
  z = ZXY_ZpQ_root(f, a, T, p, prec);
  return gc_GEN(av, ZXV_to_ZpXQV(z, T, p, prec));
}

/* vector of p-adic roots of the ZX f, leading term prime to p. Shallow */
static GEN
ZX_Zp_roots(GEN f, GEN p, long prec)
{
  long l, i;
  GEN r;

  f = ZX_radical(f);
  r = FpX_roots(f, p);
  l = lg(r); if (l == 1) return r;
  for (i = 1; i < l; i++) gel(r,i) = ZX_Zp_root(f, gel(r,i), p, prec);
  return ZV_to_ZpV(shallowconcat1(r), p, prec);
}
/* vector of p-adic roots of the ZXX f, leading term prime to p. Shallow */
static GEN
ZXY_ZpQ_roots(GEN f, GEN T, GEN p, long prec)
{
  long l, i;
  GEN r;

  (void)nfgcd_all(f, RgX_deriv(f), T, NULL, &f);
  r = FqX_roots(f, FpX_red(T,p), p);
  l = lg(r); if (l == 1) return r;
  for (i = 1; i < l; i++) gel(r,i) = ZXY_ZpQ_root(f, gel(r,i), T, p, prec);
  return ZXV_to_ZpXQV(shallowconcat1(r), T, p, prec);
}

/* return p-adic roots of f, precision prec */
GEN
polrootspadic(GEN f, GEN Tp, long prec)
{
  pari_sp av = avma;
  GEN lead, y, T, p;
  long PREC, i, k, v;
  int reverse;

  if (!ff_parse_Tp(Tp, &T,&p,0)) pari_err_TYPE("polrootspadic",Tp);
  if (typ(f)!=t_POL) pari_err_TYPE("polrootspadic",f);
  if (gequal0(f)) pari_err_ROOTS0("polrootspadic");
  if (prec <= 0)
    pari_err_DOMAIN("polrootspadic", "precision", "<=",gen_0,stoi(prec));
  f = T? QpXQX_to_ZXY(f, p): QpX_to_ZX(f, p);
  v = RgX_valrem(f, &f);
  f = pnormalize(f, p, T, prec, 1, &lead, &PREC, &reverse);
  y = T? ZXY_ZpQ_roots(f,T,p,PREC): ZX_Zp_roots(f,p,PREC);
  k = lg(y);
  if (lead != gen_1) y = RgC_Rg_div(y, lead);
  if (reverse)
    for (i=1; i<k; i++) gel(y,i) = ginv(gel(y,i));
  if (v) y = shallowconcat(zeropadic_shallow(p, prec), y);
  return gc_GEN(av, y);
}

/*******************************************************************/
/*                                                                 */
/*             FACTORIZATION in Zp[X], using ROUND4                */
/*                                                                 */
/*******************************************************************/

int
cmp_padic(GEN x, GEN y)
{
  long vx, vy;
  if (x == gen_0) return -1;
  if (y == gen_0) return  1;
  vx = valp(x);
  vy = valp(y);
  if (vx < vy) return  1;
  if (vx > vy) return -1;
  return cmpii(padic_u(x), padic_u(y));
}

/* replace p^e by p*...*p [ factors are not known to be equal, only close at
 * input accuracy ] */
static GEN
famat_flatten(GEN fa)
{
  GEN y, P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(E);
  y = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i);
    long e = itou(gel(E,i));
    gel(y,i) = const_col(e, p);
  }
  y = shallowconcat1(y); return mkmat2(y, const_col(lg(y)-1, gen_1));
}

GEN
factorpadic(GEN f, GEN p, long r)
{
  pari_sp av = avma;
  GEN y, ppow;
  long v, n;
  int reverse = 0, exact;

  if (typ(f)!=t_POL) pari_err_TYPE("factorpadic",f);
  if (typ(p)!=t_INT) pari_err_TYPE("factorpadic",p);
  if (r <= 0) pari_err_DOMAIN("factorpadic", "precision", "<=",gen_0,stoi(r));
  if (!signe(f)) return prime_fact(f);
  if (!degpol(f)) return trivial_fact();

  exact = RgX_is_QX(f); /* before RgX_valrem which may lose type information */
  v = RgX_valrem_inexact(f, &f);
  ppow = powiu(p,r);
  n = degpol(f);
  if (!n)
    y = trivial_fact();
  else
  {
    GEN P, lead;
    long i, l, pr;

    f = QpX_to_ZX(f, p);
    f = pnormalize(f, p, NULL, r, n-1, &lead, &pr, &reverse);
    y = ZpX_monic_factor(f, p, pr);
    P = gel(y,1); l = lg(P);
    if (!isint1(lead))
      for (i=1; i<l; i++) gel(P,i) = Q_primpart(RgX_unscale(gel(P,i), lead));
    for (i=1; i<l; i++)
    {
      GEN t = gel(P,i);
      if (reverse) t = RgX_recip_shallow(t);
      gel(P,i) = ZX_to_ZpX_normalized(t,p,ppow,r);
    }
  }
  if (v)
  { /* v > 0 */
    GEN X = ZX_to_ZpX(pol_x(varn(f)), p, ppow, r);
    y = famat_mulpow_shallow(y, X, utoipos(v));
  }
  if (!exact) y = famat_flatten(y);
  return gc_GEN(av, sort_factor_pol(y, cmp_padic));
}
