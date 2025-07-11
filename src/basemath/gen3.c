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
/**                      GENERIC OPERATIONS                        **/
/**                         (third part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                 PRINCIPAL VARIABLE NUMBER                      **/
/**                                                                **/
/********************************************************************/
static void
recvar(hashtable *h, GEN x)
{
  long i = 1, lx = lg(x);
  void *v;
  switch(typ(x))
  {
    case t_POL: case t_SER:
      v = (void*)varn(x);
      if (!hash_search(h, v)) hash_insert(h, v, NULL);
      i = 2; break;
    case t_POLMOD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT: break;
    case t_LIST:
      x = list_data(x);
      lx = x? lg(x): 1; break;
    default:
      return;
  }
  for (; i < lx; i++) recvar(h, gel(x,i));
}

GEN
variables_vecsmall(GEN x)
{
  hashtable *h = hash_create_ulong(100, 1);
  recvar(h, x);
  return vars_sort_inplace(hash_keys(h));
}

GEN
variables_vec(GEN x)
{ return x? vars_to_RgXV(variables_vecsmall(x)): gpolvar(NULL); }

long
gvar(GEN x)
{
  long i, v, w, lx;
  switch(typ(x))
  {
    case t_POL: case t_SER: return varn(x);
    case t_POLMOD: return varn(gel(x,1));
    case t_RFRAC:  return varn(gel(x,2));
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); break;
    case t_LIST:
      x = list_data(x);
      lx = x? lg(x): 1; break;
    default:
      return NO_VARIABLE;
  }
  v = NO_VARIABLE;
  for (i=1; i < lx; i++) { w = gvar(gel(x,i)); if (varncmp(w,v) < 0) v = w; }
  return v;
}
/* T main polynomial in R[X], A auxiliary in R[X] (possibly degree 0).
 * Guess and return the main variable of R */
static long
var2_aux(GEN T, GEN A)
{
  long a = gvar2(T);
  long b = (typ(A) == t_POL && varn(A) == varn(T))? gvar2(A): gvar(A);
  if (varncmp(a, b) > 0) a = b;
  return a;
}
static long
var2_rfrac(GEN x)  { return var2_aux(gel(x,2), gel(x,1)); }
static long
var2_polmod(GEN x) { return var2_aux(gel(x,1), gel(x,2)); }

/* main variable of x, with the convention that the "natural" main
 * variable of a POLMOD is mute, so we want the next one. */
static long
gvar9(GEN x)
{ return (typ(x) == t_POLMOD)? var2_polmod(x): gvar(x); }

/* main variable of the ring over wich x is defined */
long
gvar2(GEN x)
{
  long i, v, w;
  switch(typ(x))
  {
    case t_POLMOD:
      return var2_polmod(x);
    case t_POL: case t_SER:
      v = NO_VARIABLE;
      for (i=2; i < lg(x); i++) {
        w = gvar9(gel(x,i));
        if (varncmp(w,v) < 0) v=w;
      }
      return v;
    case t_RFRAC:
      return var2_rfrac(x);
    case t_VEC: case t_COL: case t_MAT:
      v = NO_VARIABLE;
      for (i=1; i < lg(x); i++) {
        w = gvar2(gel(x,i));
        if (varncmp(w,v)<0) v=w;
      }
      return v;
  }
  return NO_VARIABLE;
}

/*******************************************************************/
/*                                                                 */
/*                    PRECISION OF SCALAR OBJECTS                  */
/*                                                                 */
/*******************************************************************/
static long
prec0(long e) { return (e < 0)? nbits2prec(-e): LOWDEFAULTPREC; }
static long
precREAL(GEN x) { return signe(x) ? realprec(x): prec0(expo(x)); }
/* x t_REAL, y an exact noncomplex type. Return precision(|x| + |y|) */
static long
precrealexact(GEN x, GEN y)
{
  long lx, ey = gexpo(y), ex, e;
  if (ey == -(long)HIGHEXPOBIT) return precREAL(x);
  ex = expo(x);
  e = ey - ex;
  if (!signe(x)) return prec0((e >= 0)? -e: ex);
  lx = realprec(x);
  return (e > 0)? lx + nbits2extraprec(e): lx;
}
static long
precCOMPLEX(GEN z)
{ /* ~ precision(|x| + |y|) */
  GEN x = gel(z,1), y = gel(z,2);
  long e, ex, ey, lz, lx, ly;
  if (typ(x) != t_REAL) {
    if (typ(y) != t_REAL) return 0;
    return precrealexact(y, x);
  }
  if (typ(y) != t_REAL) return precrealexact(x, y);
  /* x, y are t_REALs, cf addrr_sign */
  ex = expo(x);
  ey = expo(y);
  e = ey - ex;
  if (!signe(x)) {
    if (!signe(y)) return prec0( minss(ex,ey) );
    if (e <= 0) return prec0(ex);
    lz = nbits2prec(e);
    ly = realprec(y); if (lz > ly) lz = ly;
    return lz;
  }
  if (!signe(y)) {
    if (e >= 0) return prec0(ey);
    lz = nbits2prec(-e);
    lx = realprec(x); if (lz > lx) lz = lx;
    return lz;
  }
  if (e < 0) { swap(x, y); e = -e; }
  lx = realprec(x);
  ly = realprec(y);
  if (e) {
    long d = nbits2extraprec(e), l = ly-d;
    return (l > lx)? lx + d: ly;
  }
  return minss(lx, ly);
}
long
precision(GEN z)
{
  switch(typ(z))
  {
    case t_REAL: return precREAL(z);
    case t_COMPLEX: return precCOMPLEX(z);
  }
  return 0;
}

long
gprecision(GEN x)
{
  long i, k, l;

  switch(typ(x))
  {
    case t_REAL: return precREAL(x);
    case t_COMPLEX: return precCOMPLEX(x);
    case t_INT: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_PADIC: case t_QUAD: case t_POLMOD:
      return 0;

    case t_POL: case t_SER:
      k = LONG_MAX;
      for (i=lg(x)-1; i>1; i--)
      {
        l = gprecision(gel(x,i));
        if (l && l<k) k = l;
      }
      return (k==LONG_MAX)? 0: k;
    case t_VEC: case t_COL: case t_MAT:
      k = LONG_MAX;
      for (i=lg(x)-1; i>0; i--)
      {
        l = gprecision(gel(x,i));
        if (l && l<k) k = l;
      }
      return (k==LONG_MAX)? 0: k;

    case t_RFRAC:
    {
      k=gprecision(gel(x,1));
      l=gprecision(gel(x,2)); if (l && (!k || l<k)) k=l;
      return k;
    }
    case t_QFB:
      return gprecision(gel(x,4));
  }
  return 0;
}

static long
vec_padicprec_relative(GEN x, long imin)
{
  long s, t, i;
  for (s=LONG_MAX, i=lg(x)-1; i>=imin; i--)
  {
    t = padicprec_relative(gel(x,i)); if (t<s) s = t;
  }
  return s;
}
/* RELATIVE padic precision. Only accept decent types: don't try to make sense
 * of everything like padicprec */
long
padicprec_relative(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return LONG_MAX;
    case t_PADIC:
      return signe(padic_u(x))? precp(x): 0;
    case t_POLMOD: case t_VEC: case t_COL: case t_MAT:
      return vec_padicprec_relative(x, 1);
    case t_POL: case t_SER:
      return vec_padicprec_relative(x, 2);
  }
  pari_err_TYPE("padicprec_relative",x);
  return 0; /* LCOV_EXCL_LINE */
}

static long
vec_padicprec(GEN x, GEN p, long imin)
{
  long s, t, i;
  for (s=LONG_MAX, i=lg(x)-1; i>=imin; i--)
  {
    t = padicprec(gel(x,i),p); if (t<s) s = t;
  }
  return s;
}
static long
vec_serprec(GEN x, long v, long imin)
{
  long s, t, i;
  for (s=LONG_MAX, i=lg(x)-1; i>=imin; i--)
  {
    t = serprec(gel(x,i),v); if (t<s) s = t;
  }
  return s;
}

/* ABSOLUTE padic precision */
long
padicprec(GEN x, GEN p)
{
  if (typ(p) != t_INT) pari_err_TYPE("padicprec",p);
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return LONG_MAX;

    case t_INTMOD:
      return Z_pval(gel(x,1),p);

    case t_PADIC:
      if (!equalii(padic_p(x),p)) pari_err_MODULUS("padicprec", padic_p(x), p);
      return precp(x)+valp(x);

    case t_POL: case t_SER:
      return vec_padicprec(x, p, 2);
    case t_COMPLEX: case t_QUAD: case t_POLMOD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      return vec_padicprec(x, p, 1);
  }
  pari_err_TYPE("padicprec",x);
  return 0; /* LCOV_EXCL_LINE */
}
GEN
gppadicprec(GEN x, GEN p)
{
  long v = padicprec(x,p);
  return v == LONG_MAX? mkoo(): stoi(v);
}

/* ABSOLUTE X-adic precision */
long
serprec(GEN x, long v)
{
  long w;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_COMPLEX: case t_PADIC: case t_QUAD: case t_QFB:
      return LONG_MAX;

    case t_POL:
      w = varn(x);
      if (varncmp(v,w) <= 0) return LONG_MAX;
      return vec_serprec(x, v, 2);
    case t_SER:
      w = varn(x);
      if (w == v)
      {
        long l = lg(x); /* Mod(0,2) + O(x) */
        if (l == 3 && !signe(x) && !isinexact(gel(x,2))) l--;
        return l - 2 + valser(x);
      }
      if (varncmp(v,w) < 0) return LONG_MAX;
      return vec_serprec(x, v, 2);
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      return vec_serprec(x, v, 1);
  }
  pari_err_TYPE("serprec",x);
  return 0; /* LCOV_EXCL_LINE */
}
GEN
gpserprec(GEN x, long v)
{
  long p = serprec(x,v);
  return p == LONG_MAX? mkoo(): stoi(p);
}

/* Degree of x (scalar, t_POL, t_RFRAC) wrt variable v if v >= 0,
 * wrt to main variable if v < 0. */
long
poldegree(GEN x, long v)
{
  const long DEGREE0 = -LONG_MAX;
  long tx = typ(x), lx,w,i,d;

  if (is_scalar_t(tx)) return gequal0(x)? DEGREE0: 0;
  switch(tx)
  {
    case t_POL:
      if (!signe(x)) return DEGREE0;
      w = varn(x);
      if (v < 0 || v == w) return degpol(x);
      if (varncmp(v, w) < 0) return 0;
      lx = lg(x); d = DEGREE0;
      for (i=2; i<lx; i++)
      {
        long e = poldegree(gel(x,i), v);
        if (e > d) d = e;
      }
      return d;

    case t_RFRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      if (gequal0(a)) return DEGREE0;
      if (v < 0)
      {
        v = varn(b); d = -degpol(b);
        if (typ(a) == t_POL && varn(a) == v) d += degpol(a);
        return d;
      }
      return poldegree(a,v) - poldegree(b,v);
    }
  }
  pari_err_TYPE("degree",x);
  return 0; /* LCOV_EXCL_LINE  */
}
GEN
gppoldegree(GEN x, long v)
{
  long d = poldegree(x,v);
  return d == -LONG_MAX? mkmoo(): stoi(d);
}

/* assume v >= 0 and x is a POLYNOMIAL in v, return deg_v(x) */
long
RgX_degree(GEN x, long v)
{
  long tx = typ(x), lx, w, i, d;

  if (is_scalar_t(tx)) return gequal0(x)? -1: 0;
  switch(tx)
  {
    case t_POL:
      if (!signe(x)) return -1;
      w = varn(x);
      if (v == w) return degpol(x);
      if (varncmp(v, w) < 0) return 0;
      lx = lg(x); d = -1;
      for (i=2; i<lx; i++)
      {
        long e = RgX_degree(gel(x,i), v);
        if (e > d) d = e;
      }
      return d;

    case t_RFRAC:
      w = varn(gel(x,2));
      if (varncmp(v, w) < 0) return 0;
      if (RgX_degree(gel(x,2),v)) pari_err_TYPE("RgX_degree", x);
      return RgX_degree(gel(x,1),v);
  }
  pari_err_TYPE("RgX_degree",x);
  return 0; /* LCOV_EXCL_LINE  */
}

long
degree(GEN x)
{
  return poldegree(x,-1);
}

/* If v<0, leading coeff with respect to the main variable, otherwise wrt v. */
GEN
pollead(GEN x, long v)
{
  long tx = typ(x), w;
  pari_sp av;

  if (is_scalar_t(tx)) return gcopy(x);
  w = varn(x);
  switch(tx)
  {
    case t_POL:
      if (v < 0 || v == w)
      {
        long l = lg(x);
        return (l==2)? gen_0: gcopy(gel(x,l-1));
      }
      break;

    case t_SER:
      if (v < 0 || v == w) return signe(x)? gcopy(gel(x,2)): gen_0;
      if (varncmp(v, w) > 0) x = polcoef_i(x, valser(x), v);
      break;

    default:
      pari_err_TYPE("pollead",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (varncmp(v, w) < 0) return gcopy(x);
  av = avma; w = fetch_var_higher();
  x = gsubst(x, v, pol_x(w));
  x = pollead(x, w);
  delete_var(); return gc_upto(av, x);
}

/* returns 1 if there's a real component in the structure, 0 otherwise */
int
isinexactreal(GEN x)
{
  long i;
  switch(typ(x))
  {
    case t_REAL: return 1;
    case t_COMPLEX: return (typ(gel(x,1))==t_REAL || typ(gel(x,2))==t_REAL);

    case t_INT: case t_INTMOD: case t_FRAC:
    case t_FFELT: case t_PADIC: case t_QUAD:
    case t_QFB: return 0;

    case t_RFRAC: case t_POLMOD:
      return isinexactreal(gel(x,1)) || isinexactreal(gel(x,2));

    case t_POL: case t_SER:
      for (i=lg(x)-1; i>1; i--)
        if (isinexactreal(gel(x,i))) return 1;
      return 0;

    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (isinexactreal(gel(x,i))) return 1;
      return 0;
    default: return 0;
  }
}
/* Check if x is approximately real with precision e */
int
isrealappr(GEN x, long e)
{
  long i;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return 1;
    case t_COMPLEX:
      return (gexpo(gel(x,2)) < e);

    case t_POL: case t_SER:
      for (i=lg(x)-1; i>1; i--)
        if (! isrealappr(gel(x,i),e)) return 0;
      return 1;

    case t_RFRAC: case t_POLMOD:
      return isrealappr(gel(x,1),e) && isrealappr(gel(x,2),e);

    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (! isrealappr(gel(x,i),e)) return 0;
      return 1;
    default: pari_err_TYPE("isrealappr",x); return 0;
  }
}

/* returns 1 if there's an inexact component in the structure, and
 * 0 otherwise. */
int
isinexact(GEN x)
{
  long lx, i;

  switch(typ(x))
  {
    case t_REAL: case t_PADIC: case t_SER:
      return 1;
    case t_INT: case t_INTMOD: case t_FFELT: case t_FRAC:
    case t_QFB:
      return 0;
    case t_COMPLEX: case t_QUAD: case t_RFRAC: case t_POLMOD:
      return isinexact(gel(x,1)) || isinexact(gel(x,2));
    case t_POL:
      for (i=lg(x)-1; i>1; i--)
        if (isinexact(gel(x,i))) return 1;
      return 0;
    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(x)-1; i>0; i--)
        if (isinexact(gel(x,i))) return 1;
      return 0;
    case t_LIST:
      x = list_data(x); lx = x? lg(x): 1;
      for (i=1; i<lx; i++)
        if (isinexact(gel(x,i))) return 1;
      return 0;
  }
  return 0;
}

int
isrationalzeroscalar(GEN g)
{
  switch (typ(g))
  {
    case t_INT:     return !signe(g);
    case t_COMPLEX: return isintzero(gel(g,1)) && isintzero(gel(g,2));
    case t_QUAD:    return isintzero(gel(g,2)) && isintzero(gel(g,3));
  }
  return 0;
}

int
iscomplex(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return 0;
    case t_COMPLEX:
      return !gequal0(gel(x,2));
    case t_QUAD:
      return signe(gmael(x,1,2)) > 0;
  }
  pari_err_TYPE("iscomplex",x);
  return 0; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                    GENERIC REMAINDER                            */
/*                                                                 */
/*******************************************************************/
static int
is_realquad(GEN x) { GEN Q = gel(x,1); return signe(gel(Q,2)) < 0; }
static int
is_realext(GEN x)
{ long t = typ(x);
  return (t == t_QUAD)? is_realquad(x): is_real_t(t);
}
/* euclidean quotient for scalars of admissible types */
static GEN
_quot(GEN x, GEN y)
{
  GEN q = gdiv(x,y), f = gfloor(q);
  if (gsigne(y) < 0 && !gequal(f,q)) f = addiu(f, 1);
  return f;
}
/* y t_REAL, x \ y */
static GEN
_quotsr(long x, GEN y)
{
  GEN q, f;
  if (!x) return gen_0;
  q = divsr(x,y); f = floorr(q);
  if (signe(y) < 0 && signe(subir(f,q))) f = addiu(f, 1);
  return f;
}
/* x t_REAL, x \ y */
static GEN
_quotrs(GEN x, long y)
{
  GEN q = divrs(x,y), f = floorr(q);
  if (y < 0 && signe(subir(f,q))) f = addiu(f, 1);
  return f;
}
static GEN
_quotri(GEN x, GEN y)
{
  GEN q = divri(x,y), f = floorr(q);
  if (signe(y) < 0 && signe(subir(f,q))) f = addiu(f, 1);
  return f;
}
static GEN
_quotsq(long x, GEN y)
{
  GEN f = gfloor(gdivsg(x,y));
  if (gsigne(y) < 0) f = gaddgs(f, 1);
  return f;
}
static GEN
_quotqs(GEN x, long y)
{
  GEN f = gfloor(gdivgs(x,y));
  if (y < 0) f = addiu(f, 1);
  return f;
}

/* y t_FRAC, x \ y */
static GEN
_quotsf(long x, GEN y)
{ return truedivii(mulis(gel(y,2),x), gel(y,1)); }
/* x t_FRAC, x \ y */
static GEN
_quotfs(GEN x, long y)
{ return truedivii(gel(x,1),mulis(gel(x,2),y)); }
/* x t_FRAC, y t_INT, x \ y */
static GEN
_quotfi(GEN x, GEN y)
{ return truedivii(gel(x,1),mulii(gel(x,2),y)); }

static GEN
quot(GEN x, GEN y)
{ pari_sp av = avma; return gc_upto(av, _quot(x, y)); }
static GEN
quotrs(GEN x, long y)
{ pari_sp av = avma; return gc_leaf(av, _quotrs(x,y)); }
static GEN
quotfs(GEN x, long s)
{ pari_sp av = avma; return gc_leaf(av, _quotfs(x,s)); }
static GEN
quotsr(long x, GEN y)
{ pari_sp av = avma; return gc_leaf(av, _quotsr(x, y)); }
static GEN
quotsf(long x, GEN y)
{ pari_sp av = avma; return gc_leaf(av, _quotsf(x, y)); }
static GEN
quotsq(long x, GEN y)
{ pari_sp av = avma; return gc_leaf(av, _quotsq(x, y)); }
static GEN
quotqs(GEN x, long y)
{ pari_sp av = avma; return gc_leaf(av, _quotqs(x, y)); }
static GEN
quotfi(GEN x, GEN y)
{ pari_sp av = avma; return gc_leaf(av, _quotfi(x, y)); }
static GEN
quotri(GEN x, GEN y)
{ pari_sp av = avma; return gc_leaf(av, _quotri(x, y)); }

static GEN
modrs(GEN x, long y)
{
  pari_sp av = avma;
  GEN q = _quotrs(x,y);
  if (!signe(q)) { set_avma(av); return rcopy(x); }
  return gc_leaf(av, subri(x, mulis(q,y)));
}
static GEN
modsr(long x, GEN y)
{
  pari_sp av = avma;
  GEN q = _quotsr(x,y);
  if (!signe(q)) return gc_stoi(av, x);
  return gc_leaf(av, subsr(x, mulir(q,y)));
}
static GEN
modsf(long x, GEN y)
{
  pari_sp av = avma;
  return gc_upto(av, Qdivii(modii(mulis(gel(y,2),x), gel(y,1)), gel(y,2)));
}

/* assume y a t_REAL, x a t_INT, t_FRAC or t_REAL.
 * Return x mod y or NULL if accuracy error */
GEN
modRr_safe(GEN x, GEN y)
{
  GEN q, f;
  long e;
  if (isintzero(x)) return gen_0;
  q = gdiv(x,y); /* t_REAL */

  e = expo(q);
  if (e >= 0 && nbits2prec(e+1) > realprec(q)) return NULL;
  f = floorr(q);
  if (signe(y) < 0 && signe(subri(q,f))) f = addiu(f, 1);
  return signe(f)? gsub(x, mulir(f,y)): x;
}
GEN
modRr_i(GEN x, GEN y, GEN iy)
{
  GEN q, f;
  long e;
  if (isintzero(x)) return gen_0;
  q = gmul(x, iy); /* t_REAL */

  e = expo(q);
  if (e >= 0 && nbits2prec(e+1) > realprec(q)) return NULL;
  f = floorr(q);
  if (signe(y) < 0 && signe(subri(q,f))) f = addiu(f, 1);
  return signe(f)? gsub(x, mulir(f,y)): x;
}

GEN
gmod(GEN x, GEN y)
{
  pari_sp av;
  long ty, tx;
  GEN z;

  tx = typ(x); if (tx == t_INT && !is_bigint(x)) return gmodsg(itos(x),y);
  ty = typ(y); if (ty == t_INT && !is_bigint(y)) return gmodgs(x,itos(y));
  if (is_matvec_t(tx)) pari_APPLY_same(gmod(gel(x,i), y));
  if (tx == t_POL || ty == t_POL) return grem(x,y);
  if (!is_scalar_t(tx) || !is_scalar_t(ty)) pari_err_TYPE2("%",x,y);
  switch(ty)
  {
    case t_INT:
      switch(tx)
      {
        case t_INT: return modii(x,y);
        case t_INTMOD: z=cgetg(3, t_INTMOD);
          gel(z,1) = gcdii(gel(x,1),y);
          gel(z,2) = modii(gel(x,2),gel(z,1)); return z;
        case t_FRAC: return Fp_div(gel(x,1),gel(x,2),y);
        case t_PADIC: return padic_to_Fp(x, y);
        case t_QUAD: if (!is_realquad(x)) break;
        case t_REAL:
          av = avma; /* NB: conflicting semantic with lift(x * Mod(1,y)). */
          return gc_upto(av, gsub(x, gmul(_quot(x,y),y)));
      }
      break;
    case t_QUAD:
      if (!is_realquad(y)) break;
    case t_REAL: case t_FRAC:
      if (!is_realext(x)) break;
      av = avma;
      return gc_upto(av, gsub(x, gmul(_quot(x,y),y)));
  }
  pari_err_TYPE2("%",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gmodgs(GEN x, long y)
{
  ulong u;
  long i, tx = typ(x);
  GEN z;
  if (is_matvec_t(tx)) pari_APPLY_same(gmodgs(gel(x,i), y));
  if (!y) pari_err_INV("gmodgs",gen_0);
  switch(tx)
  {
    case t_INT: return modis(x,y);
    case t_REAL: return modrs(x,y);

    case t_INTMOD: z=cgetg(3, t_INTMOD);
      u = (ulong)labs(y);
      i = ugcdiu(gel(x,1), u);
      gel(z,1) = utoi(i);
      gel(z,2) = modis(gel(x,2), i); return z;

    case t_FRAC:
      u = (ulong)labs(y);
      return utoi( Fl_div(umodiu(gel(x,1), u),
                          umodiu(gel(x,2), u), u) );
    case t_QUAD:
    {
      pari_sp av = avma;
      if (!is_realquad(x)) break;
      return gc_upto(av, gsub(x, gmulgs(_quotqs(x,y),y)));
    }
    case t_PADIC: return padic_to_Fp(x, stoi(y));
    case t_POL: return scalarpol(Rg_get_0(x), varn(x));
    case t_POLMOD: return gmul(gen_0,x);
  }
  pari_err_TYPE2("%",x,stoi(y));
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
gmodsg(long x, GEN y)
{
  switch(typ(y))
  {
    case t_INT: return modsi(x,y);
    case t_REAL: return modsr(x,y);
    case t_FRAC: return modsf(x,y);
    case t_QUAD:
    {
      pari_sp av = avma;
      if (!is_realquad(y)) break;
      return gc_upto(av, gsubsg(x, gmul(_quotsq(x,y),y)));
    }
    case t_POL:
      if (!signe(y)) pari_err_INV("gmodsg",y);
      return degpol(y)? gmulsg(x, Rg_get_1(y)): Rg_get_0(y);
  }
  pari_err_TYPE2("%",stoi(x),y);
  return NULL; /* LCOV_EXCL_LINE */
}
/* divisibility: return 1 if y | x, 0 otherwise */
int
gdvd(GEN x, GEN y)
{
  pari_sp av = avma;
  return gc_bool(av, gequal0( gmod(x,y) ));
}

GEN
gmodulss(long x, long y)
{
  if (!y) pari_err_INV("%",gen_0);
  y = labs(y);
  retmkintmod(utoi(umodsu(x, y)), utoipos(y));
}
GEN
gmodulsg(long x, GEN y)
{
  switch(typ(y))
  {
    case t_INT:
      if (!is_bigint(y)) return gmodulss(x,itos(y));
      retmkintmod(modsi(x,y), absi(y));
    case t_POL:
      if (!signe(y)) pari_err_INV("%", y);
      retmkpolmod(degpol(y)? stoi(x): gen_0,RgX_copy(y));
  }
  pari_err_TYPE2("%",stoi(x),y);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
gmodulo(GEN x,GEN y)
{
  long tx = typ(x), vx, vy;
  if (tx == t_INT && !is_bigint(x)) return gmodulsg(itos(x), y);
  if (is_matvec_t(tx)) pari_APPLY_same(gmodulo(gel(x,i), y));
  switch(typ(y))
  {
    case t_INT:
      if (!is_const_t(tx)) return gmul(x, gmodulsg(1,y));
      if (tx == t_INTMOD) return gmod(x,y);
      retmkintmod(Rg_to_Fp(x,y), absi(y));
    case t_POL:
      vx = gvar(x); vy = varn(y);
      if (varncmp(vy, vx) > 0) return gmul(x, gmodulsg(1,y));
      if (vx == vy && tx == t_POLMOD) return grem(x,y);
      retmkpolmod(grem(x,y), RgX_copy(y));
  }
  pari_err_TYPE2("%",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                 GENERIC EUCLIDEAN DIVISION                      */
/*                                                                 */
/*******************************************************************/
GEN
gdivent(GEN x, GEN y)
{
  long tx, ty;
  tx = typ(x); if (tx == t_INT && !is_bigint(x)) return gdiventsg(itos(x),y);
  ty = typ(y); if (ty == t_INT && !is_bigint(y)) return gdiventgs(x,itos(y));
  if (is_matvec_t(tx)) pari_APPLY_same(gdivent(gel(x,i), y));
  if (tx == t_POL || ty == t_POL) return gdeuc(x,y);
  switch(ty)
  {
    case t_INT:
      switch(tx)
      {
        case t_INT: return truedivii(x,y);
        case t_REAL: return quotri(x,y);
        case t_FRAC: return quotfi(x,y);
        case t_QUAD:
          if (!is_realquad(x)) break;
          return quot(x,y);
      }
      break;
    case t_QUAD:
      if (!is_realext(x) || !is_realquad(y)) break;
    case t_REAL: case t_FRAC:
      return quot(x,y);
  }
  pari_err_TYPE2("\\",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gdiventgs(GEN x, long y)
{
  switch(typ(x))
  {
    case t_INT:  return truedivis(x,y);
    case t_REAL: return quotrs(x,y);
    case t_FRAC: return quotfs(x,y);
    case t_QUAD: if (!is_realquad(x)) break;
                 return quotqs(x,y);
    case t_POL:  return gdivgs(x,y);
    case t_VEC: case t_COL: case t_MAT: pari_APPLY_same(gdiventgs(gel(x,i),y));
  }
  pari_err_TYPE2("\\",x,stoi(y));
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
gdiventsg(long x, GEN y)
{
  switch(typ(y))
  {
    case t_INT:  return truedivsi(x,y);
    case t_REAL: return quotsr(x,y);
    case t_FRAC: return quotsf(x,y);
    case t_QUAD: if (!is_realquad(y)) break;
                 return quotsq(x,y);
    case t_POL:
      if (!signe(y)) pari_err_INV("gdiventsg",y);
      return degpol(y)? Rg_get_0(y): gdivsg(x,gel(y,2));
  }
  pari_err_TYPE2("\\",stoi(x),y);
  return NULL; /* LCOV_EXCL_LINE */
}

/* with remainder */
static GEN
quotrem(GEN x, GEN y, GEN *r)
{
  GEN q = quot(x,y);
  pari_sp av = avma;
  *r = gc_upto(av, gsub(x, gmul(q,y)));
  return q;
}

GEN
gdiventres(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  GEN z;

  if (is_matvec_t(tx)) pari_APPLY_same(gdiventres(gel(x,i), y));
  z = cgetg(3,t_COL);
  if (tx == t_POL || ty == t_POL)
  {
    gel(z,1) = poldivrem(x,y,(GEN*)(z+2));
    return z;
  }
  switch(ty)
  {
    case t_INT:
      switch(tx)
      { /* equal to, but more efficient than next case */
        case t_INT:
          gel(z,1) = truedvmdii(x,y,(GEN*)(z+2));
          return z;
        case t_QUAD:
          if (!is_realquad(x)) break;
        case t_REAL: case t_FRAC:
          gel(z,1) = quotrem(x,y,&gel(z,2));
          return z;
      }
      break;
    case t_QUAD:
      if (!is_realext(x) || !is_realquad(y)) break;
    case t_REAL: case t_FRAC:
      gel(z,1) = quotrem(x,y,&gel(z,2));
      return z;
  }
  pari_err_TYPE2("\\",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
divrem(GEN x, GEN y, long v)
{
  pari_sp av = avma;
  long vx, vy, vz;
  GEN q, r;
  if (v < 0 || typ(y) != t_POL || typ(x) != t_POL) return gdiventres(x,y);
  vz = v; vx = varn(x); vy = varn(y);
  if (varncmp(vx, vz) < 0 || varncmp(vy, vz) < 0) vz = fetch_var_higher();
  if (vx != vz) x = swap_vars(x, v, vz);
  if (vy != vz) y = swap_vars(y, v, vz);
  q = RgX_divrem(x,y, &r);
  if (vx != v || vy != v)
  {
    GEN X = pol_x(v);
    q = gsubst(q, vz, X); /* poleval broken for t_RFRAC, subst is safe */
    r = gsubst(r, vz, X);
    if (vz != v) (void)delete_var();
  }
  return gc_GEN(av, mkcol2(q, r));
}

GEN
diviiround(GEN x, GEN y)
{
  pari_sp av1, av = avma;
  GEN q,r;
  int fl;

  q = dvmdii(x,y,&r); /* q = x/y rounded towards 0, sgn(r)=sgn(x) */
  if (r==gen_0) return q;
  av1 = avma;
  fl = abscmpii(shifti(r,1),y);
  set_avma(av1); cgiv(r);
  if (fl >= 0) /* If 2*|r| >= |y| */
  {
    long sz = signe(x)*signe(y);
    if (fl || sz > 0) q = gc_INT(av, addis(q,sz));
  }
  return q;
}

static GEN
_abs(GEN x)
{
  if (typ(x) == t_QUAD) return (gsigne(x) < 0)? gneg(x): x;
  return R_abs_shallow(x);
}

/* If x and y are not both scalars, same as gdivent.
 * Otherwise, compute the quotient x/y, rounded to the nearest integer
 * (towards +oo in case of tie). */
GEN
gdivround(GEN x, GEN y)
{
  pari_sp av;
  long tx = typ(x), ty = typ(y);
  GEN q, r;

  if (tx == t_INT && ty == t_INT) return diviiround(x,y);
  av = avma;
  if (is_realext(x) && is_realext(y))
  { /* same as diviiround, less efficient */
    pari_sp av1;
    int fl;
    q = quotrem(x,y,&r); av1 = avma;
    fl = gcmp(gmul2n(_abs(r),1), _abs(y));
    set_avma(av1); cgiv(r);
    if (fl >= 0) /* If 2*|r| >= |y| */
    {
      long sz = gsigne(y);
      if (fl || sz > 0) q = gc_upto(av, gaddgs(q, sz));
    }
    return q;
  }
  if (is_matvec_t(tx)) pari_APPLY_same(gdivround(gel(x,i),y));
  return gdivent(x,y);
}

GEN
gdivmod(GEN x, GEN y, GEN *pr)
{
  switch(typ(x))
  {
    case t_INT:
      switch(typ(y))
      {
        case t_INT: return dvmdii(x,y,pr);
        case t_POL: *pr=icopy(x); return gen_0;
      }
      break;
    case t_POL: return poldivrem(x,y,pr);
  }
  pari_err_TYPE2("gdivmod",x,y);
  return NULL;/*LCOV_EXCL_LINE*/
}

/*******************************************************************/
/*                                                                 */
/*                               SHIFT                             */
/*                                                                 */
/*******************************************************************/

/* Shift tronque si n<0 (multiplication tronquee par 2^n)  */

GEN
gshift(GEN x, long n)
{
  switch(typ(x))
  {
    case t_INT: return shifti(x,n);
    case t_REAL:return shiftr(x,n);
    case t_VEC: case t_COL: case t_MAT: pari_APPLY_same(gshift(gel(x,i),n));
  }
  return gmul2n(x,n);
}

/*******************************************************************/
/*                                                                 */
/*           SUBSTITUTION DANS UN POLYNOME OU UNE SERIE            */
/*                                                                 */
/*******************************************************************/

/* Convert t_SER --> t_POL, ignoring valser. INTERNAL ! */
GEN
ser2pol_i(GEN x, long lx)
{
  long i = lx-1;
  GEN y;
  while (i > 1 && isrationalzero(gel(x,i))) i--;
  if (!signe(x))
  { /* danger */
    if (i == 1) return zeropol(varn(x));
    y = cgetg(3,t_POL); y[1] = x[1] & ~VALSERBITS;
    gel(y,2) = gel(x,2); return y;
  }
  y = cgetg(i+1, t_POL); y[1] = x[1] & ~VALSERBITS;
  for ( ; i > 1; i--) gel(y,i) = gel(x,i);
  return y;
}

GEN
ser2pol_i_normalize(GEN x, long l, long *v)
{
  long i = 2, j = l-1, k;
  GEN y;
  while (i < l && gequal0(gel(x,i))) i++;
  *v = i - 2; if (i == l) return zeropol(varn(x));
  while (j > i && gequal0(gel(x,j))) j--;
  l = j - *v + 1;
  y = cgetg(l, t_POL); y[1] = x[1] & ~VALSERBITS;
  k = l; while (k > 2) gel(y, --k) = gel(x,j--);
  return y;
}

GEN
ser_inv(GEN b)
{
  pari_sp av = avma;
  long e, l = lg(b);
  GEN x, y;
  y = ser2pol_i_normalize(b, l, &e);
  if (e)
  {
    pari_warn(warner,"normalizing a series with 0 leading term");
    l -= e; if (l <= 2) pari_err_INV("inv_ser", b);
  }
  y = RgXn_inv_i(y, l-2);
  x = RgX_to_ser(y, l); setvalser(x, - valser(b) - e);
  return gc_GEN(av, x);
}

/* T t_POL in var v, mod out by T components of x which are t_POL/t_RFRAC in v.
 * Recursively. Make sure that resulting polynomials of degree 0 in v are
 * simplified (map K[X]_0 to K) */
static GEN
mod_r(GEN x, long v, GEN T)
{
  long w, tx = typ(x);
  GEN y;

  if (is_const_t(tx)) return x;
  switch(tx)
  {
    case t_POLMOD:
      w = varn(gel(x,1));
      if (w == v) pari_err_PRIORITY("subst", gel(x,1), "=", v);
      if (varncmp(v, w) < 0) return x;
      return gmodulo(mod_r(gel(x,2),v,T), mod_r(gel(x,1),v,T));
    case t_SER:
      w = varn(x);
      if (w == v) break; /* fail */
      if (varncmp(v, w) < 0 || ser_isexactzero(x)) return x;
      pari_APPLY_ser(mod_r(gel(x,i),v,T));
    case t_POL:
      w = varn(x);
      if (w == v)
      {
        x = RgX_rem(x, T);
        if (!degpol(x)) x = gel(x,2);
        return x;
      }
      if (varncmp(v, w) < 0) return x;
      pari_APPLY_pol(mod_r(gel(x,i),v,T));
    case t_RFRAC:
      x = gdiv(mod_r(gel(x,1),v,T), mod_r(gel(x,2),v,T));
      if (typ(x) == t_POL && varn(x) == v && lg(x) == 3) x = gel(x,2);
      return x;
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(mod_r(gel(x,i),v,T));
    case t_LIST:
      y = mklist();
      list_data(y) = list_data(x)? mod_r(list_data(x),v,T): NULL;
      return y;
  }
  pari_err_TYPE("substpol",x);
  return NULL;/*LCOV_EXCL_LINE*/
}
GEN
gsubstpol(GEN x, GEN T, GEN y)
{
  pari_sp av = avma;
  long v;
  GEN z;
  if (typ(T) == t_POL && RgX_is_monomial(T) && gequal1(leading_coeff(T)))
  { /* T = t^d */
    long d = degpol(T);
    v = varn(T); z = (d==1)? x: gdeflate(x, v, d);
    if (z) return gc_upto(av, gsubst(z, v, y));
  }
  v = fetch_var(); T = simplify_shallow(T);
  if (typ(T) == t_RFRAC)
    z = gsub(gel(T,1), gmul(pol_x(v), gel(T,2)));
  else
    z = gsub(T, pol_x(v));
  z = mod_r(x, gvar(T), z);
  z = gsubst(z, v, y); (void)delete_var();
  return gc_upto(av, z);
}

long
RgX_deflate_order(GEN x)
{
  ulong d = 0, i, lx = (ulong)lg(x);
  for (i=3; i<lx; i++)
    if (!gequal0(gel(x,i))) { d = ugcd(d,i-2); if (d == 1) return 1; }
  return d? (long)d: 1;
}
long
ZX_deflate_order(GEN x)
{
  ulong d = 0, i, lx = (ulong)lg(x);
  for (i=3; i<lx; i++)
    if (signe(gel(x,i))) { d = ugcd(d,i-2); if (d == 1) return 1; }
  return d? (long)d: 1;
}

/* deflate (non-leaf) x recursively */
static GEN
vdeflate(GEN x, long v, long d)
{
  long i, lx, tx = typ(x);
  GEN y = cgetg_copy(x, &lx);
  for(i = 1; i < lontyp[tx]; i++) y[i] = x[i];
  for (; i < lx; i++)
  {
    gel(y,i) = gdeflate(gel(x,i),v,d);
    if (!y[i]) return NULL;
  }
  return y;
}

/* don't return NULL if substitution fails (fallback won't be able to handle
 * t_SER anyway), fail with a meaningful message */
static GEN
serdeflate(GEN x, long v, long d)
{
  long V, dy, lx, vx = varn(x);
  pari_sp av;
  GEN y;
  if (varncmp(vx, v) < 0) return vdeflate(x,v,d);
  if (varncmp(vx, v) > 0) return gcopy(x);
  av = avma;
  V = valser(x);
  lx = lg(x);
  if (lx == 2) return zeroser(v, V / d);
  y = ser2pol_i(x, lx);
  dy = degpol(y);
  if (V % d != 0 || (dy > 0 && RgX_deflate_order(y) % d != 0))
  {
    const char *s = stack_sprintf("valuation(x) %% %ld", d);
    pari_err_DOMAIN("gdeflate", s, "!=", gen_0,x);
  }
  if (dy > 0) y = RgX_deflate(y, d);
  y = RgX_to_ser(y, 3 + (lx-3)/d);
  setvalser(y, V/d); return gc_GEN(av, y);
}
static GEN
poldeflate(GEN x, long v, long d)
{
  long vx = varn(x);
  pari_sp av;
  if (varncmp(vx, v) < 0) return vdeflate(x,v,d);
  if (varncmp(vx, v) > 0 || degpol(x) <= 0) return gcopy(x);
  av = avma;
  /* x nonconstant */
  if (RgX_deflate_order(x) % d != 0) return NULL;
  return gc_GEN(av, RgX_deflate(x,d));
}
static GEN
listdeflate(GEN x, long v, long d)
{
  GEN y = NULL, z = mklist();
  if (list_data(x))
  {
    y = vdeflate(list_data(x),v,d);
    if (!y) return NULL;
  }
  list_data(z) = y; return z;
}
/* return NULL if substitution fails */
GEN
gdeflate(GEN x, long v, long d)
{
  if (d <= 0) pari_err_DOMAIN("gdeflate", "degree", "<=", gen_0,stoi(d));
  switch(typ(x))
  {
    case t_INT:
    case t_REAL:
    case t_INTMOD:
    case t_FRAC:
    case t_FFELT:
    case t_COMPLEX:
    case t_PADIC:
    case t_QUAD: return gcopy(x);
    case t_POL: return poldeflate(x,v,d);
    case t_SER: return serdeflate(x,v,d);
    case t_POLMOD:
      if (varncmp(varn(gel(x,1)), v) >= 0) return gcopy(x);
      /* fall through */
    case t_RFRAC:
    case t_VEC:
    case t_COL:
    case t_MAT: return vdeflate(x,v,d);
    case t_LIST: return listdeflate(x,v,d);
  }
  pari_err_TYPE("gdeflate",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* set *m to the largest d such that x0 = A(X^d); return A */
GEN
RgX_deflate_max(GEN x, long *m)
{
  *m = RgX_deflate_order(x);
  return RgX_deflate(x, *m);
}
GEN
ZX_deflate_max(GEN x, long *m)
{
  *m = ZX_deflate_order(x);
  return RgX_deflate(x, *m);
}

static int
serequalXk(GEN x)
{
  long i, l = lg(x);
  if (l == 2 || !isint1(gel(x,2))) return 0;
  for (i = 3; i < l; i++)
    if (!isintzero(gel(x,i))) return 0;
  return 1;
}

static GEN
gsubst_v(GEN e, long v, GEN x)
{ pari_APPLY_same(gsubst(e, v, gel(x,i))); }

static GEN
constmat(GEN z, long n)
{
  GEN y = cgetg(n+1, t_MAT), c = const_col(n, gcopy(z));
  long i;
  for (i = 1; i <= n; i++) gel(y, i) = c;
  return y;
}
static GEN
scalarmat2(GEN o, GEN z, long n)
{
  GEN y;
  long i;
  if (n == 0) return cgetg(1, t_MAT);
  if (n == 1) retmkmat(mkcol(gcopy(o)));
  y = cgetg(n+1, t_MAT); z = gcopy(z); o = gcopy(o);
  for (i = 1; i <= n; i++) { gel(y, i) = const_col(n, z); gcoeff(y,i,i) = o; }
  return y;
}
/* x * y^0, n = dim(y) if t_MAT, else -1 */
static GEN
subst_higher(GEN x, GEN y, long n)
{
  GEN o = Rg_get_1(y);
  if (o == gen_1) return n < 0? gcopy(x): scalarmat(x,n);
  x = gmul(x,o); return n < 0? x: scalarmat2(x, Rg_get_0(y), n);
}

/* x t_POLMOD, v strictly lower priority than var(x) */
static GEN
subst_polmod(GEN x, long v, GEN y)
{
  long l, i;
  GEN a = gsubst(gel(x,2),v,y), b = gsubst(gel(x,1),v,y), z;

  if (typ(b) != t_POL) pari_err_TYPE2("substitution",x,y);
  if (typ(a) != t_POL || varncmp(varn(a), varn(b)) >= 0) return gmodulo(a, b);
  l = lg(a); z = cgetg(l,t_POL); z[1] = a[1];
  for (i = 2; i < l; i++) gel(z,i) = gmodulo(gel(a,i),b);
  return normalizepol_lg(z, l);
}
/* Trunc to n terms; x + O(t^(n + v(x))). FIXME: export ? */
static GEN
sertrunc(GEN x, long n)
{
  long i, l = n + 2;
  GEN y;
  if (l >= lg(x)) return x;
  if (n <= 0) return zeroser(varn(x), n + valser(x));
  y = cgetg(l, t_SER);
  for (i = 2; i < l; i++) gel(y,i) = gel(x,i);
  y[1] = x[1]; return y;
}
/* FIXME: export ? */
static GEN
sertrunc_copy(GEN x, long n)
{
  long i, l = minss(n + 2, lg(x));
  GEN y = cgetg(l, t_SER);
  for (i = 2; i < l; i++) gel(y,i) = gcopy(gel(x,i));
  y[1] = x[1]; return y;
}

GEN
gsubst(GEN x, long v, GEN y)
{
  long tx = typ(x), ty = typ(y), lx = lg(x), ly = lg(y);
  long l, vx, vy, ex, ey, i, j, k, jb, matn;
  pari_sp av, av2;
  GEN X, t, z;

  switch(ty)
  {
    case t_VEC: case t_COL:
      return gsubst_v(x, v, y);
    case t_MAT:
      if (ly==1) return cgetg(1,t_MAT);
      if (ly == lgcols(y)) { matn = ly - 1; break; }
      /* fall through */
    case t_QFB:
      pari_err_TYPE2("substitution",x,y);
    default: matn = -1;
  }
  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD && varncmp(v, varn(gel(x,1))) > 0)
    {
      av = avma;
      return gc_upto(av, subst_polmod(x, v, y));
    }
    return subst_higher(x, y, matn);
  }

  switch(tx)
  {
    case t_POL:
      vx = varn(x);
      if (varncmp(vx, v) > 0) return subst_higher(x, y, matn);
      if (varncmp(vx, v) < 0)
      {
        if (lx == 2) return zeropol(vx);
        av = avma;
        if (lx == 3)
        {
          z = gsubst(gel(x,2), v, y);
          if (typ(z) == t_POL && varn(z) == vx) return z;
          return gc_upto(av, gmul(pol_1(vx), z));
        }
        z = cgetg(lx-1, t_VEC);
        for (i = 2; i < lx; i++) gel(z,i-1) = gsubst(gel(x,i),v,y);
        return gc_upto(av, poleval(z, pol_x(vx)));
      }
      /* v = vx */
      if (lx == 2)
      {
        z = Rg_get_0(y);
        return matn >= 0? constmat(z, matn): z;
      }
      if (lx == 3)
      {
        x = subst_higher(gel(x,2), y, matn);
        if (matn >= 0) return x;
        vy = gvar(y);
        return (vy == NO_VARIABLE)? x: gmul(x, pol_1(vy));
      }
      return matn >= 0? RgX_RgM_eval(x, y): poleval(x,y);

    case t_SER:
      vx = varn(x);
      if (varncmp(vx, v) > 0) return subst_higher(x, y, matn);
      ex = valser(x);
      if (varncmp(vx, v) < 0)
      {
        if (lx == 2) return matn >= 0? scalarmat(x, matn): gcopy(x);
        av = avma; X = pol_x(vx);
        av2 = avma;
        z = gadd(gsubst(gel(x,lx-1),v,y), zeroser(vx,1));
        for (i = lx-2; i>=2; i--)
        {
          z = gadd(gmul(z,X), gsubst(gel(x,i),v,y));
          if (gc_needed(av2,1))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"gsubst (i = %ld)", i);
            z = gc_upto(av2, z);
          }
        }
        if (ex) z = gmul(z, pol_xnall(ex,vx));
        return gc_upto(av, z);
      }
      switch(ty) /* here vx == v */
      {
        case t_SER:
          vy = varn(y); ey = valser(y);
          if (ey < 1 || lx == 2) return zeroser(vy, ey*(ex+lx-2));
          if (ey == 1 && serequalXk(y)
                      && (varncmp(vx,vy) >= 0 || varncmp(gvar2(x), vy) >= 0))
          { /* y = t + O(t^N) */
            if (lx > ly)
            { /* correct number of significant terms */
              l = ly;
              if (!ex)
                for (i = 3; i < lx; i++)
                  if (++l >= lx || !gequal0(gel(x,i))) break;
              lx = l;
            }
            z = sertrunc_copy(x, lx - 2); if (vx != vy) setvarn(z,vy);
            return z;
          }
          if (vy != vx)
          {
            long nx = lx - 2, n = minss(ey * nx, ly - 2);
            av = avma; z = gel(x, nx+1);
            for (i = nx; i > 1; i--)
            {
              z = gadd(gmul(y,z), gel(x,i));
              if (gc_needed(av,1))
              {
                if(DEBUGMEM>1) pari_warn(warnmem,"gsubst (i = %ld)", i);
                z = gc_upto(av, z);
              }
            }
            if (ex)
            {
              if (ex < 0) { y = ginv(y); ex = -ex; }
              z = gmul(z, gpowgs(sertrunc(y, n), ex));
            }
            if (lg(z)-2 > n) z = sertrunc_copy(z, n);
            return gc_upto(av,z);
          }
          l = (lx-2)*ey + 2;
          if (ex) { if (l>ly) l = ly; }
          else if (lx != 3)
          {
            for (i = 3; i < lx; i++)
              if (!isexactzero(gel(x,i))) break;
            l = minss(l, (i-2)*ey + (gequal0(y)? 2 : ly));
          }
          av = avma; t = leafcopy(y);
          if (l < ly) setlg(t, l);
          z = scalarser(gen_1, varn(y), l-2);
          gel(z,2) = gel(x,2); /* ensure lg(z) = l even if x[2] = 0 */
          for (i = 3, jb = ey; jb <= l-2; i++,jb += ey)
          {
            if (i < lx) {
              for (j = jb+2; j < minss(l, jb+ly); j++)
                gel(z,j) = gadd(gel(z,j), gmul(gel(x,i),gel(t,j-jb)));
            }
            for (j = minss(ly-1, l-1-jb-ey); j > 1; j--)
            {
              GEN a = gmul(gel(t,2), gel(y,j));
              for (k=2; k<j; k++) a = gadd(a, gmul(gel(t,j-k+2), gel(y,k)));
              gel(t,j) = a;
            }
            if (gc_needed(av,1))
            {
              if(DEBUGMEM>1) pari_warn(warnmem,"gsubst");
              (void)gc_all(av,2, &z,&t);
            }
          }
          if (!ex) return gc_GEN(av,z);
          if (ex < 0) { ex = -ex; y = ginv(y); }
          return gc_upto(av, gmul(z, gpowgs(sertrunc(y, l-2), ex)));

        case t_POL: case t_RFRAC:
        {
          long N, n = lx-2;
          vy = gvar(y); ey = gval(y,vy);
          if (ey == LONG_MAX)
          { /* y = 0 */
            if (ex < 0) pari_err_INV("gsubst",y);
            if (!n) return gcopy(x);
            if (ex > 0) return Rg_get_0(ty == t_RFRAC? gel(y,2): y);
            y = Rg_get_1(ty == t_RFRAC? gel(y,2): y);
            return gmul(y, gel(x,2));
          }
          if (ey < 1 || n == 0) return zeroser(vy, ey*(ex+n));
          av = avma;
          n *= ey;
          N = ex? n: maxss(n-ey,1);
          y = (ty == t_RFRAC)? rfrac_to_ser_i(y, N+2): RgX_to_ser(y, N+2);
          if (lg(y)-2 > n) setlg(y, n+2);
          x = ser2pol_i(x, lx);
          if (varncmp(vy,vx) > 0)
            z = gadd(poleval(x, y), zeroser(vy,n));
          else
          {
            z = RgXn_eval(x, ser2rfrac_i(y), n);
            if (varn(z) == vy) z = RgX_to_ser(z, n+2);
            else z = scalarser(z, vy, n);
          }
          if (!ex) return gc_GEN(av, z);
          return gc_upto(av,  gmul(z, gpowgs(y,ex)));
        }

        default:
          if (isexactzero(y))
          {
            if (ex < 0) pari_err_INV("gsubst",y);
            if (ex > 0) return gcopy(y);
            if (lx > 2) return gadd(gel(x,2), y); /*add maps to correct ring*/
          }
          pari_err_TYPE2("substitution",x,y);
      }
      break;

    case t_RFRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      av = avma;
      a = gsubst(a, v, y);
      b = gsubst(b, v, y); return gc_upto(av, gdiv(a, b));
    }

    case t_VEC: case t_COL: case t_MAT: pari_APPLY_same(gsubst(gel(x,i),v,y));
    case t_LIST:
      z = mklist();
      list_data(z) = list_data(x)? gsubst(list_data(x),v,y): NULL;
      return z;
  }
  return gcopy(x);
}

/* Return P(x * h), not memory clean */
GEN
ser_unscale(GEN P, GEN h)
{
  long l = lg(P);
  GEN Q = cgetg(l,t_SER);
  Q[1] = P[1];
  if (l != 2)
  {
    long i = 2;
    GEN hi = gpowgs(h, valser(P));
    gel(Q,i) = gmul(gel(P,i), hi);
    for (i++; i<l; i++) { hi = gmul(hi,h); gel(Q,i) = gmul(gel(P,i), hi); }
  }
  return Q;
}

static int
safe_polmod(GEN r)
{
  GEN a = gel(r,1), b = gel(r,2);
  long t = typ(a);
  return 0;
  if (gvar2(b) != NO_VARIABLE) return 0;
  if (is_scalar_t(t)) return 1;
  return (t == t_POL && varn(a) == varn(b) && gvar2(a) == NO_VARIABLE);
}
GEN
gsubstvec(GEN e, GEN v, GEN r)
{
  pari_sp av = avma;
  long i, j, k, l = lg(v);
  GEN w, z, R;
  if ( !is_vec_t(typ(v)) ) pari_err_TYPE("substvec",v);
  if ( !is_vec_t(typ(r)) ) pari_err_TYPE("substvec",r);
  if (lg(r)!=l) pari_err_DIM("substvec");
  w = cgetg(l, t_VECSMALL);
  z = cgetg(l, t_VECSMALL);
  R = cgetg(l, t_VEC); k = 0;
  for(i = j = 1; i < l; i++)
  {
    GEN T = gel(v,i), ri = gel(r,i);
    if (!gequalX(T)) pari_err_TYPE("substvec [not a variable]", T);
    if (gvar(ri) == NO_VARIABLE || (typ(ri) == t_POLMOD && safe_polmod(ri)))
    { /* no need to take precautions */
      e = gsubst(e, varn(T), ri);
      if (is_vec_t(typ(ri)) && k++) e = shallowconcat1(e);
    }
    else
    {
      w[j] = varn(T);
      z[j] = fetch_var_higher();
      gel(R,j) = ri; j++;
    }
  }
  for(i = 1; i < j; i++) e = gsubst(e,w[i],pol_x(z[i]));
  for(i = 1; i < j; i++)
  {
    e = gsubst(e,z[i],gel(R,i));
    if (is_vec_t(typ(gel(R,i))) && k++) e = shallowconcat1(e);
  }
  for(i = 1; i < j; i++) (void)delete_var();
  return k > 1? gc_GEN(av, e): gc_upto(av, e);
}

/*******************************************************************/
/*                                                                 */
/*                SERIE RECIPROQUE D'UNE SERIE                     */
/*                                                                 */
/*******************************************************************/

GEN
serreverse(GEN x)
{
  long v=varn(x), lx = lg(x), i, mi;
  pari_sp av0 = avma, av;
  GEN a, y, u;

  if (typ(x)!=t_SER) pari_err_TYPE("serreverse",x);
  if (valser(x)!=1) pari_err_DOMAIN("serreverse", "valuation", "!=", gen_1,x);
  if (lx < 3) pari_err_DOMAIN("serreverse", "x", "=", gen_0,x);
  y = ser_normalize(x);
  if (y == x) a = NULL; else { a = gel(x,2); x = y; }
  av = avma;
  mi = lx-1; while (mi>=3 && gequal0(gel(x,mi))) mi--;
  u = cgetg(lx,t_SER);
  y = cgetg(lx,t_SER);
  u[1] = y[1] = evalsigne(1) | _evalvalser(1) | evalvarn(v);
  gel(u,2) = gel(y,2) = gen_1;
  if (lx > 3)
  {
    gel(u,3) = gmulsg(-2,gel(x,3));
    gel(y,3) = gneg(gel(x,3));
  }
  for (i=3; i<lx-1; )
  {
    pari_sp av2;
    GEN p1;
    long j, k, K = minss(i,mi);
    for (j=3; j<i+1; j++)
    {
      av2 = avma; p1 = gel(x,j);
      for (k = maxss(3,j+2-mi); k < j; k++)
        p1 = gadd(p1, gmul(gel(u,k),gel(x,j-k+2)));
      p1 = gneg(p1);
      gel(u,j) = gc_upto(av2, gadd(gel(u,j), p1));
    }
    av2 = avma;
    p1 = gmulsg(i,gel(x,i+1));
    for (k = 2; k < K; k++)
    {
      GEN p2 = gmul(gel(x,k+1),gel(u,i-k+2));
      p1 = gadd(p1, gmulsg(k,p2));
    }
    i++;
    gel(u,i) = gc_upto(av2, gneg(p1));
    gel(y,i) = gdivgu(gel(u,i), i-1);
    if (gc_needed(av,2))
    {
      GEN dummy = cgetg(1,t_VEC);
      if(DEBUGMEM>1) pari_warn(warnmem,"serreverse");
      for(k=i+1; k<lx; k++) gel(u,k) = gel(y,k) = dummy;
      (void)gc_all(av,2, &u,&y);
    }
  }
  if (a) y = ser_unscale(y, ginv(a));
  return gc_GEN(av0,y);
}

/*******************************************************************/
/*                                                                 */
/*                    DERIVATION ET INTEGRATION                    */
/*                                                                 */
/*******************************************************************/
GEN
derivser(GEN x)
{
  long i, vx = varn(x), e = valser(x), lx = lg(x);
  GEN y;
  if (ser_isexactzero(x))
  {
    x = gcopy(x);
    if (e) setvalser(x,e-1);
    return x;
  }
  if (e)
  {
    y = cgetg(lx,t_SER); y[1] = evalsigne(1)|evalvalser(e-1) | evalvarn(vx);
    for (i=2; i<lx; i++) gel(y,i) = gmulsg(i+e-2,gel(x,i));
  } else {
    if (lx == 3) return zeroser(vx, 0);
    lx--;
    y = cgetg(lx,t_SER); y[1] = evalsigne(1)|_evalvalser(0) | evalvarn(vx);
    for (i=2; i<lx; i++) gel(y,i) = gmulsg(i-1,gel(x,i+1));
  }
  return normalizeser(y);
}

static GEN
rfrac_deriv(GEN x, long v)
{
  pari_sp av = avma;
  GEN y = cgetg(3,t_RFRAC), a = gel(x,1), b = gel(x,2), bp, b0, t, T;
  long vx = varn(b);

  bp = deriv(b, v);
  t = simplify_shallow(RgX_gcd(bp, b));
  if (typ(t) != t_POL || varn(t) != vx)
  {
    if (gequal1(t)) b0 = b;
    else
    {
      b0 = RgX_Rg_div(b, t);
      bp = RgX_Rg_div(bp, t);
    }
    a = gsub(gmul(b0, deriv(a,v)), gmul(a, bp));
    if (isexactzero(a)) return gc_upto(av, a);
    if (b0 == b)
    {
      gel(y,1) = gc_upto((pari_sp)y, a);
      gel(y,2) = RgX_sqr(b);
    }
    else
    {
      gel(y,1) = a;
      gel(y,2) = RgX_Rg_mul(RgX_sqr(b0), t);
      y = gc_GEN(av, y);
    }
    return y;
  }
  b0 = gdivexact(b, t);
  bp = gdivexact(bp,t);
  a = gsub(gmul(b0, deriv(a,v)), gmul(a, bp));
  if (isexactzero(a)) return gc_upto(av, a);
  T = RgX_gcd(a, t);
  if (typ(T) != t_POL || varn(T) != vx)
  {
    a = gdiv(a, T);
    t = gdiv(t, T);
  }
  else if (!gequal1(T))
  {
    a = gdivexact(a, T);
    t = gdivexact(t, T);
  }
  gel(y,1) = a;
  gel(y,2) = gmul(RgX_sqr(b0), t);
  return gc_GEN(av, y);
}

GEN
deriv(GEN x, long v)
{
  long tx = typ(x);
  if (is_const_t(tx))
    switch(tx)
    {
      case t_INTMOD: retmkintmod(gen_0, icopy(gel(x,1)));
      case t_FFELT: return FF_zero(x);
      default: return gen_0;
    }
  if (v < 0)
  {
    if (tx == t_CLOSURE) return closure_deriv(x);
    v = gvar9(x);
  }
  switch(tx)
  {
    case t_POLMOD:
    {
      GEN a = gel(x,2), b = gel(x,1);
      if (v == varn(b)) return Rg_get_0(b);
      retmkpolmod(deriv(a,v), RgX_copy(b));
    }
    case t_POL:
      switch(varncmp(varn(x), v))
      {
        case 1: return Rg_get_0(x);
        case 0: return RgX_deriv(x);
      }
      pari_APPLY_pol(deriv(gel(x,i),v));

    case t_SER:
      switch(varncmp(varn(x), v))
      {
        case 1: return Rg_get_0(x);
        case 0: return derivser(x);
      }
      if (ser_isexactzero(x)) return gcopy(x);
      pari_APPLY_ser(deriv(gel(x,i),v));

    case t_RFRAC:
      return rfrac_deriv(x,v);

    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(deriv(gel(x,i),v));
  }
  pari_err_TYPE("deriv",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* n-th derivative of t_SER x, n > 0 */
static GEN
derivnser(GEN x, long n)
{
  long i, vx = varn(x), e = valser(x), lx = lg(x);
  GEN y;
  if (ser_isexactzero(x))
  {
    x = gcopy(x);
    if (e) setvalser(x,e-n);
    return x;
  }
  if (e < 0 || e >= n)
  {
    y = cgetg(lx,t_SER);
    y[1] = evalsigne(1)| evalvalser(e-n) | evalvarn(vx);
    for (i=0; i<lx-2; i++)
      gel(y,i+2) = gmul(muls_interval(i+e-n+1,i+e), gel(x,i+2));
  } else {
    if (lx <= n+2) return zeroser(vx, 0);
    lx -= n;
    y = cgetg(lx,t_SER);
    y[1] = evalsigne(1)|_evalvalser(0) | evalvarn(vx);
    for (i=0; i<lx-2; i++)
      gel(y,i+2) = gmul(mulu_interval(i+1,i+n),gel(x,i+2+n-e));
  }
  return normalizeser(y);
}

/* n-th derivative of t_POL x, n > 0 */
static GEN
RgX_derivn(GEN x, long n)
{
  long i, vx = varn(x), lx = lg(x);
  GEN y;
  if (lx <= n+2) return pol_0(vx);
  lx -= n;
  y = cgetg(lx,t_POL);
  y[1] = evalsigne(1)| evalvarn(vx);
  for (i=0; i<lx-2; i++)
    gel(y,i+2) = gmul(mulu_interval(i+1,i+n),gel(x,i+2+n));
  return normalizepol_lg(y, lx);
}

static GEN
rfrac_derivn(GEN x, long n, long vs)
{
  pari_sp av = avma;
  GEN u  = gel(x,1), v = gel(x,2);
  GEN dv = deriv(v, vs);
  long i;
  for (i=1; i<=n; i++)
  {
    GEN du = deriv(u, vs);
    u = gadd(gmul(du, v), gmulsg (-i, gmul(dv, u)));
  }
  v = gpowgs(v, n+1);
  return gc_upto(av, gdiv(u, v));
}

GEN
derivn(GEN x, long n, long v)
{
  long tx;
  if (n < 0)  pari_err_DOMAIN("derivn","n","<", gen_0, stoi(n));
  if (n == 0) return gcopy(x);
  tx = typ(x);
  if (is_const_t(tx))
    switch(tx)
    {
      case t_INTMOD: retmkintmod(gen_0, icopy(gel(x,1)));
      case t_FFELT: return FF_zero(x);
      default: return gen_0;
    }
  if (v < 0)
  {
    if (tx == t_CLOSURE) return closure_derivn(x, n);
    v = gvar9(x);
  }
  switch(tx)
  {
    case t_POLMOD:
    {
      GEN a = gel(x,2), b = gel(x,1);
      if (v == varn(b)) return Rg_get_0(b);
      retmkpolmod(derivn(a,n,v), RgX_copy(b));
    }
    case t_POL:
      switch(varncmp(varn(x), v))
      {
        case 1: return Rg_get_0(x);
        case 0: return RgX_derivn(x,n);
      }
      pari_APPLY_pol(derivn(gel(x,i),n,v));

    case t_SER:
      switch(varncmp(varn(x), v))
      {
        case 1: return Rg_get_0(x);
        case 0: return derivnser(x, n);
      }
      if (ser_isexactzero(x)) return gcopy(x);
      pari_APPLY_ser(derivn(gel(x,i),n,v));

    case t_RFRAC:
      return rfrac_derivn(x, n, v);

    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(derivn(gel(x,i),n,v));
  }
  pari_err_TYPE("derivn",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static long
lookup(GEN v, long vx)
{
  long i ,l = lg(v);
  for(i=1; i<l; i++)
    if (varn(gel(v,i)) == vx) return i;
  return 0;
}

static GEN
serdiffop(GEN x, GEN v, GEN dv) { pari_APPLY_ser(diffop(gel(x,i),v,dv)); }
GEN
diffop(GEN x, GEN v, GEN dv)
{
  pari_sp av;
  long i, idx, lx, tx = typ(x), vx;
  GEN y;
  if (!is_vec_t(typ(v))) pari_err_TYPE("diffop",v);
  if (!is_vec_t(typ(dv))) pari_err_TYPE("diffop",dv);
  if (lg(v)!=lg(dv)) pari_err_DIM("diffop");
  if (is_const_t(tx)) return gen_0;
  switch(tx)
  {
    case t_POLMOD:
      av = avma;
      vx  = varn(gel(x,1)); idx = lookup(v,vx);
      if (idx) /*Assume the users now what they are doing */
        y = gmodulo(diffop(gel(x,2),v,dv), gel(x,1));
      else
      {
        GEN m = gel(x,1), pol=gel(x,2);
        GEN u = gneg(gdiv(diffop(m,v,dv),RgX_deriv(m)));
        y = diffop(pol,v,dv);
        if (typ(pol)==t_POL && varn(pol)==varn(m))
          y = gadd(y, gmul(u,RgX_deriv(pol)));
        y = gmodulo(y, gel(x,1));
      }
      return gc_upto(av, y);
    case t_POL:
      if (signe(x)==0) return gen_0;
      vx  = varn(x); idx = lookup(v,vx);
      av = avma; lx = lg(x);
      y = diffop(gel(x,lx-1),v,dv);
      for (i=lx-2; i>=2; i--) y = gadd(gmul(y,pol_x(vx)),diffop(gel(x,i),v,dv));
      if (idx) y = gadd(y, gmul(gel(dv,idx),RgX_deriv(x)));
      return gc_upto(av, y);

    case t_SER:
      if (signe(x)==0) return gen_0;
      vx  = varn(x); idx = lookup(v,vx);
      if (!idx) return gen_0;
      av = avma;
      if (ser_isexactzero(x)) y = x;
      else
      {
        y = serdiffop(x, v, dv); /* y is probably invalid */
        y = gsubst(y, vx, pol_x(vx)); /* Fix that */
      }
      y = gadd(y, gmul(gel(dv,idx), derivser(x)));
      return gc_upto(av, y);

    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2), ap, bp;
      av = avma;
      ap = diffop(a, v, dv); bp = diffop(b, v, dv);
      y = gsub(gdiv(ap,b),gdiv(gmul(a,bp),gsqr(b)));
      return gc_upto(av, y);
    }

    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(diffop(gel(x,i),v,dv));
  }
  pari_err_TYPE("diffop",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
diffop0(GEN x, GEN v, GEN dv, long n)
{
  pari_sp av=avma;
  long i;
  for(i=1; i<=n; i++)
    x = gc_upto(av, diffop(x,v,dv));
  return x;
}

/********************************************************************/
/**                                                                **/
/**                         TAYLOR SERIES                          **/
/**                                                                **/
/********************************************************************/
/* swap vars (vx,v) in x (assume vx < v, vx main variable in x), then call
 * act(data, v, x). FIXME: use in other places */
static GEN
swapvar_act(GEN x, long vx, long v, GEN (*act)(void*, long, GEN), void *data)
{
  long v0 = fetch_var();
  GEN y = act(data, v, gsubst(x,vx,pol_x(v0)));
  y = gsubst(y,v0,pol_x(vx));
  (void)delete_var(); return y;
}
/* x + O(v^data) */
static GEN
tayl_act(void *data, long v, GEN x) { return gadd(zeroser(v, (long)data), x); }
static  GEN
integ_act(void *data, long v, GEN x) { (void)data; return integ(x,v); }

GEN
tayl(GEN x, long v, long precS)
{
  long vx = gvar9(x);
  pari_sp av;

  if (varncmp(v, vx) <= 0) return gadd(zeroser(v,precS), x);
  av = avma;
  return gc_upto(av, swapvar_act(x, vx, v, tayl_act, (void*)precS));
}

GEN
ggrando(GEN x, long n)
{
  long m, v;

  switch(typ(x))
  {
  case t_INT:/* bug 3 + O(1) */
    if (signe(x) <= 0) pari_err_DOMAIN("O", "x", "<=", gen_0, x);
    if (!is_pm1(x)) return zeropadic(x,n);
    /* +/-1 = x^0 */
    v = m = 0; break;
  case t_POL:
    if (!signe(x)) pari_err_DOMAIN("O", "x", "=", gen_0, x);
    v = varn(x);
    m = n * RgX_val(x); break;
  case t_RFRAC:
    if (gequal0(gel(x,1))) pari_err_DOMAIN("O", "x", "=", gen_0, x);
    v = gvar(x);
    m = n * gval(x,v); break;
    default:  pari_err_TYPE("O", x);
      v = m = 0; /* LCOV_EXCL_LINE */
  }
  return zeroser(v,m);
}

/*******************************************************************/
/*                                                                 */
/*                    FORMAL INTEGRATION                           */
/*                                                                 */
/*******************************************************************/
GEN
RgX_integ(GEN x)
{
  long i, lx = lg(x);
  GEN y;
  if (lx == 2) return RgX_copy(x);
  y = cgetg(lx+1, t_POL); y[1] = x[1]; gel(y,2) = gen_0;
  for (i=3; i<=lx; i++) gel(y,i) = gdivgu(gel(x,i-1),i-2);
  return y;
}

static void
err_intformal(GEN x)
{ pari_err_DOMAIN("intformal", "residue(series, pole)", "!=", gen_0, x); }

GEN
integser(GEN x)
{
  long i, lx = lg(x), vx = varn(x), e = valser(x);
  GEN y;
  if (lx == 2) return zeroser(vx, e+1);
  y = cgetg(lx, t_SER);
  for (i=2; i<lx; i++)
  {
    long j = i+e-1;
    GEN c = gel(x,i);
    if (j)
      c = gdivgs(c, j);
    else
    { /* should be isexactzero, but try to avoid error */
      if (!gequal0(c)) err_intformal(x);
      c = gen_0;
    }
    gel(y,i) = c;
  }
  y[1] = evalsigne(1) | evalvarn(vx) | evalvalser(e+1); return y;
}

GEN
integ(GEN x, long v)
{
  long tx = typ(x), vx, n;
  pari_sp av = avma;
  GEN y, p1;

  if (v < 0) { v = gvar9(x); if (v == NO_VARIABLE) v = 0; }
  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD)
    {
      GEN a = gel(x,2), b = gel(x,1);
      vx = varn(b);
      if (varncmp(v, vx) > 0) retmkpolmod(integ(a,v), RgX_copy(b));
      if (v == vx) pari_err_PRIORITY("intformal",x,"=",v);
    }
    return deg1pol(x, gen_0, v);
  }

  switch(tx)
  {
    case t_POL:
      vx = varn(x);
      if (v == vx) return RgX_integ(x);
      if (lg(x) == 2) {
        if (varncmp(vx, v) < 0) v = vx;
        return zeropol(v);
      }
      if (varncmp(vx, v) > 0) return deg1pol(x, gen_0, v);
      pari_APPLY_pol(integ(gel(x,i),v));

    case t_SER:
      vx = varn(x);
      if (v == vx) return integser(x);
      if (lg(x) == 2) {
        if (varncmp(vx, v) < 0) v = vx;
        return zeroser(v, valser(x));
      }
      if (varncmp(vx, v) > 0) return deg1pol(x, gen_0, v);
      pari_APPLY_ser(integ(gel(x,i),v));

    case t_RFRAC:
    {
      GEN a = gel(x,1), b = gel(x,2), c, d, s;
      vx = varn(b);
      if (varncmp(vx, v) > 0) return deg1pol(x, gen_0, v);
      if (varncmp(vx, v) < 0)
        return gc_upto(av, swapvar_act(x, vx, v, integ_act, NULL));

      n = degpol(b);
      if (typ(a) == t_POL && varn(a) == vx) n += degpol(a);
      y = integ(gadd(x, zeroser(v,n + 2)), v);
      y = gdiv(gtrunc(gmul(b, y)), b);
      if (typ(y) != t_RFRAC) pari_err_BUG("intformal(t_RFRAC)");
      c = gel(y,1); d = gel(y,2);
      s = gsub(gmul(deriv(c,v),d), gmul(c,deriv(d,v)));
      /* (c'd-cd')/d^2 = y' = x = a/b ? */
      if (!gequal(gmul(s,b), gmul(a,gsqr(d)))) err_intformal(x);
      if (typ(y)==t_RFRAC && lg(gel(y,1)) == lg(gel(y,2)))
      {
        GEN p2 = leading_coeff(gel(y,2));
        p1 = gel(y,1);
        if (typ(p1) == t_POL && varn(p1) == vx) p1 = leading_coeff(p1);
        y = gsub(y, gdiv(p1,p2));
      }
      return gc_upto(av,y);
    }

    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(integ(gel(x,i),v));
  }
  pari_err_TYPE("integ",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                             FLOOR                               */
/*                                                                 */
/*******************************************************************/
static GEN
quad_floor(GEN x)
{
  GEN Q = gel(x,1), D = quad_disc(x), u, v, b, d, z;
  if (signe(D) < 0) return NULL;
  x = Q_remove_denom(x, &d);
  u = gel(x,2);
  v = gel(x,3); b = gel(Q,3);
  if (typ(u) != t_INT || typ(v) != t_INT) return NULL;
  /* x0 = (2u + v*(-b + sqrt(D))) / (2d) */
  z = sqrti(mulii(D, sqri(v)));
  if (signe(v) < 0) { z = addiu(z,1); togglesign(z); }
  /* z = floor(v * sqrt(D)) */
  z = addii(subii(shifti(u,1), mulii(v,b)), z);
  return truedivii(z, d? shifti(d,1): gen_2);
}
GEN
gfloor(GEN x)
{
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_POL: return RgX_copy(x);
    case t_REAL: return floorr(x);
    case t_FRAC: return truedivii(gel(x,1),gel(x,2));
    case t_QUAD:
    {
      pari_sp av = avma;
      GEN y;
      if (!(y = quad_floor(x))) break;
      return gc_INT(av, y);
    }
    case t_RFRAC: return gdeuc(gel(x,1),gel(x,2));
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(gfloor(gel(x,i)));
  }
  pari_err_TYPE("gfloor",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gfrac(GEN x)
{
  pari_sp av;
  GEN y;
  switch(typ(x))
  {
    case t_INT: return gen_0;
    case t_POL: return pol_0(varn(x));
    case t_REAL: av = avma; return gc_leaf(av, subri(x, floorr(x)));
    case t_FRAC: retmkfrac(modii(gel(x,1),gel(x,2)), icopy(gel(x,2)));
    case t_QUAD:
      av = avma; if (!(y = quad_floor(x))) break;
      return gc_upto(av, gsub(x, y));
    case t_RFRAC: retmkrfrac(grem(gel(x,1),gel(x,2)), gcopy(gel(x,2)));
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(gfrac(gel(x,i)));
  }
  pari_err_TYPE("gfrac",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* assume x t_REAL */
GEN
ceilr(GEN x)
{
  pari_sp av = avma;
  GEN y = floorr(x);
  if (cmpri(x, y)) return gc_INT(av, addui(1,y));
  return y;
}

GEN
gceil(GEN x)
{
  pari_sp av;
  GEN y;
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_POL: return RgX_copy(x);
    case t_REAL: return ceilr(x);
    case t_FRAC:
      av = avma; y = divii(gel(x,1),gel(x,2));
      if (signe(gel(x,1)) > 0) y = gc_INT(av, addui(1,y));
      return y;
    case t_QUAD:
      if (!is_realquad(x)) break;
      if (gequal0(gel(x,3))) return gceil(gel(x,2));
      av = avma; return gc_upto(av, addiu(gfloor(x), 1));
    case t_RFRAC:
      return gdeuc(gel(x,1),gel(x,2));
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(gceil(gel(x,i)));
  }
  pari_err_TYPE("gceil",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
round0(GEN x, GEN *pte)
{
  if (pte) { long e; x = grndtoi(x,&e); *pte = stoi(e); }
  return ground(x);
}

/* x t_REAL, return q=floor(x+1/2), set e = expo(x-q) */
static GEN
round_i(GEN x, long *pe)
{
  long e;
  GEN B, q,r, m = mantissa_real(x, &e); /* x = m/2^e */
  if (e <= 0)
  {
    if (e) m = shifti(m,-e);
    if (pe) *pe = -e;
    return m;
  }
  B = int2n(e-1);
  m = addii(m, B);
  q = shifti(m, -e);
  r = remi2n(m, e);
  /* 2^e (x+1/2) = m = 2^e q + r, sgn(r)=sgn(m), |r|<2^e */
  if (!signe(r))
  { if (pe) *pe = -1; }
  else
  {
    if (signe(m) < 0)
    {
      q = subiu(q,1);
      r = addii(r, B);
    }
    else
      r = subii(r, B);
    /* |x - q| = |r| / 2^e */
    if (pe) *pe = signe(r)? expi(r) - e: -e;
    cgiv(r);
  }
  return q;
}
/* assume x a t_REAL */
GEN
roundr(GEN x)
{
  long ex, s = signe(x);
  pari_sp av;
  if (!s || (ex=expo(x)) < -1) return gen_0;
  if (ex == -1) return s>0? gen_1:
                            absrnz_equal2n(x)? gen_0: gen_m1;
  av = avma; x = round_i(x, &ex);
  if (ex >= 0) pari_err_PREC( "roundr (precision loss in truncation)");
  return gc_INT(av, x);
}
GEN
roundr_safe(GEN x)
{
  long ex, s = signe(x);
  pari_sp av;

  if (!s || (ex = expo(x)) < -1) return gen_0;
  if (ex == -1) return s>0? gen_1:
                            absrnz_equal2n(x)? gen_0: gen_m1;
  av = avma; x = round_i(x, NULL);
  return gc_INT(av, x);
}

GEN
ground(GEN x)
{
  pari_sp av;
  GEN y;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_INTMOD: return gcopy(x);
    case t_REAL: return roundr(x);
    case t_FRAC: return diviiround(gel(x,1), gel(x,2));
    case t_QUAD:
    {
      GEN Q = gel(x,1), u, v, b, d, z;
      av = avma;
      if (is_realquad(x)) return gc_upto(av, gfloor(gadd(x, ghalf)));
      u = gel(x,2);
      v = gel(x,3); b = gel(Q,3);
      u = ground(gsub(u, gmul2n(gmul(v,b),-1)));
      v = Q_remove_denom(v, &d);
      if (!d) d = gen_1;
      /* Im x = v sqrt(|D|) / (2d),
       * Im(round(x)) = floor((d + v sqrt(|D|)) / (2d))
       *              = floor(floor(d + v sqrt(|D|)) / (2d)) */
      z = sqrti(mulii(sqri(v), quad_disc(x)));
      if (signe(v) < 0) { z = addiu(z,1); togglesign(z); }
      /* z = floor(v * sqrt(|D|)) */
      v = truedivii(addii(z, d), shifti(d,1));
      return gc_GEN(av, signe(v)? mkcomplex(u,v): u);
    }
    case t_POLMOD:
      retmkpolmod(ground(gel(x,2)), RgX_copy(gel(x,1)));

    case t_COMPLEX:
      av = avma; y = cgetg(3, t_COMPLEX);
      gel(y,2) = ground(gel(x,2));
      if (!signe(gel(y,2))) { set_avma(av); return ground(gel(x,1)); }
      gel(y,1) = ground(gel(x,1)); return y;

    case t_POL:
      pari_APPLY_pol(ground(gel(x,i)));
    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      pari_APPLY_ser(ground(gel(x,i)));
    case t_RFRAC:
      av = avma;
      return gc_upto(av, gdiv(ground(gel(x,1)), ground(gel(x,2))));
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(ground(gel(x,i)));
  }
  pari_err_TYPE("ground",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* e = number of error bits on integral part */
GEN
grndtoi(GEN x, long *e)
{
  GEN y;
  long i, lx, e1;
  pari_sp av;

  if (e) *e = -(long)HIGHEXPOBIT;
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_REAL: {
      long ex = expo(x);
      if (!signe(x) || ex < -1)
      {
        if (e) *e = ex;
        return gen_0;
      }
      av = avma; x = round_i(x, e);
      return gc_INT(av, x);
    }
    case t_FRAC:
      y = diviiround(gel(x,1), gel(x,2)); if (!e) return y;
      av = avma; *e = gexpo(gsub(x, y)); set_avma(av);
      return y;
    case t_INTMOD: return gcopy(x);
    case t_QUAD:
      y = ground(x); av = avma; if (!e) return y;
      *e = gexpo(gsub(x,y)); set_avma(avma); return y;
    case t_COMPLEX:
      av = avma; y = cgetg(3, t_COMPLEX);
      gel(y,2) = grndtoi(gel(x,2), e);
      if (!signe(gel(y,2))) {
        set_avma(av);
        y = grndtoi(gel(x,1), e? &e1: NULL);
      }
      else
        gel(y,1) = grndtoi(gel(x,1), e? &e1: NULL);
      if (e && e1 > *e) *e = e1;
      return y;

    case t_POLMOD:
      retmkpolmod(grndtoi(gel(x,2), e), RgX_copy(gel(x,1)));

    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i), &e1);
        if (e && e1 > *e) *e = e1;
      }
      return normalizepol_lg(y, lx);
    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i), &e1);
        if (e && e1 > *e) *e = e1;
      }
      return normalizeser(y);
    case t_RFRAC:
      y = cgetg(3,t_RFRAC);
      gel(y,1) = grndtoi(gel(x,1), e? &e1: NULL); if (e && e1 > *e) *e = e1;
      gel(y,2) = grndtoi(gel(x,2), e? &e1: NULL); if (e && e1 > *e) *e = e1;
      return y;
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        gel(y,i) = grndtoi(gel(x,i), e? &e1: NULL);
        if (e && e1 > *e) *e = e1;
      }
      return y;
  }
  pari_err_TYPE("grndtoi",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* trunc(x * 2^s). lindep() sanity checks rely on this function to return a
 * t_INT or fail when fed a non-t_COMPLEX input; so do not make this one
 * recursive [ or change the lindep call ] */
GEN
gtrunc2n(GEN x, long s)
{
  GEN z;
  switch(typ(x))
  {
    case t_INT:  return shifti(x, s);
    case t_REAL: return trunc2nr(x, s);
    case t_FRAC: {
      pari_sp av;
      GEN a = gel(x,1), b = gel(x,2), q;
      if (s == 0) return divii(a, b);
      av = avma;
      if (s < 0) q = divii(shifti(a, s), b);
      else {
        GEN r;
        q = dvmdii(a, b, &r);
        q = addii(shifti(q,s), divii(shifti(r,s), b));
      }
      return gc_INT(av, q);
    }
    case t_COMPLEX:
      z = cgetg(3, t_COMPLEX);
      gel(z,2) = gtrunc2n(gel(x,2), s);
      if (!signe(gel(z,2))) {
        set_avma((pari_sp)(z + 3));
        return gtrunc2n(gel(x,1), s);
      }
      gel(z,1) = gtrunc2n(gel(x,1), s);
      return z;
    default: pari_err_TYPE("gtrunc2n",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
}

/* e = number of error bits on integral part */
GEN
gcvtoi(GEN x, long *e)
{
  long tx = typ(x), lx, e1;
  GEN y;

  if (tx == t_REAL)
  {
    long ex = expo(x); if (ex < 0) { *e = ex; return gen_0; }
    e1 = ex - bit_prec(x) + 1;
    y = mantissa2nr(x, e1);
    if (e1 <= 0) { pari_sp av = avma; e1 = expo(subri(x,y)); set_avma(av); }
    *e = e1; return y;
  }
  *e = -(long)HIGHEXPOBIT;
  if (is_matvec_t(tx))
  {
    long i;
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++)
    {
      gel(y,i) = gcvtoi(gel(x,i),&e1);
      if (e1 > *e) *e = e1;
    }
    return y;
  }
  return gtrunc(x);
}

int
isint(GEN n, GEN *ptk)
{
  switch(typ(n))
  {
    case t_INT: *ptk = n; return 1;
    case t_REAL: {
      pari_sp av0 = avma;
      GEN z = floorr(n);
      pari_sp av = avma;
      long s = signe(subri(n, z));
      if (s) return gc_bool(av0,0);
      *ptk = z; return gc_bool(av,1);
    }
    case t_FRAC:    return 0;
    case t_COMPLEX: return gequal0(gel(n,2)) && isint(gel(n,1),ptk);
    case t_QUAD:    return gequal0(gel(n,3)) && isint(gel(n,2),ptk);
    default: pari_err_TYPE("isint",n);
             return 0; /* LCOV_EXCL_LINE */
  }
}

int
issmall(GEN n, long *ptk)
{
  pari_sp av = avma;
  GEN z;
  long k;
  if (!isint(n, &z)) return 0;
  k = itos_or_0(z); set_avma(av);
  if (k || lgefint(z) == 2) { *ptk = k; return 1; }
  return 0;
}

/* smallest integer greater than any incarnations of the real x
 * Avoid "precision loss in truncation" */
GEN
ceil_safe(GEN x)
{
  pari_sp av = avma;
  long e, tx = typ(x);
  GEN y;

  if (is_rational_t(tx)) return gceil(x);
  y = gcvtoi(x,&e);
  if (gsigne(x) >= 0)
  {
    if (e < 0) e = 0;
    y = addii(y, int2n(e));
  }
  return gc_INT(av, y);
}
/* largest integer smaller than any incarnations of the real x
 * Avoid "precision loss in truncation" */
GEN
floor_safe(GEN x)
{
  pari_sp av = avma;
  long e, tx = typ(x);
  GEN y;

  if (is_rational_t(tx)) return gfloor(x);
  y = gcvtoi(x,&e);
  if (gsigne(x) <= 0)
  {
    if (e < 0) e = 0;
    y = subii(y, int2n(e));
  }
  return gc_INT(av, y);
}

GEN
ser2rfrac_i(GEN x)
{
  long e = valser(x);
  GEN a = ser2pol_i(x, lg(x));
  if (e) {
    if (e > 0) a = RgX_shift_shallow(a, e);
    else a = gred_rfrac_simple(a, pol_xn(-e, varn(a)));
  }
  return a;
}

static GEN
ser2rfrac(GEN x)
{
  pari_sp av = avma;
  return gc_GEN(av, ser2rfrac_i(x));
}

/* x t_PADIC, truncate to rational (t_INT/t_FRAC) */
GEN
padic_to_Q(GEN x)
{
  GEN u = padic_u(x), p;
  long v;
  if (!signe(u)) return gen_0;
  v = valp(x);
  if (!v) return icopy(u);
  p = padic_p(x);
  if (v > 0)
  {
    pari_sp av = avma;
    return gc_INT(av, mulii(u, powiu(p,v)));
  }
  retmkfrac(icopy(u), powiu(p,-v));
}
GEN
padic_to_Q_shallow(GEN x)
{
  GEN u = padic_u(x), p, q, q2;
  long v;
  if (!signe(u)) return gen_0;
  q = padic_pd(x); q2 = shifti(q,-1);
  v = valp(x);
  u = Fp_center_i(u, q, q2);
  if (!v) return u;
  p = padic_p(x);
  if (v > 0) return mulii(u, powiu(p,v));
  return mkfrac(u, powiu(p,-v));
}
static GEN
Qp_to_Q(GEN c)
{
  switch(typ(c))
  {
    case t_INT:
    case t_FRAC: break;
    case t_PADIC: c = padic_to_Q_shallow(c); break;
    default: pari_err_TYPE("padic_to_Q", c);
  }
  return c;
}
GEN
QpV_to_QV(GEN x) { pari_APPLY_same(Qp_to_Q(gel(x,i))); }

GEN
gtrunc(GEN x)
{
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_REAL: return truncr(x);
    case t_FRAC: return divii(gel(x,1),gel(x,2));
    case t_PADIC: return padic_to_Q(x);
    case t_POL: return RgX_copy(x);
    case t_RFRAC: return gdeuc(gel(x,1),gel(x,2));
    case t_SER: return ser2rfrac(x);
    case t_VEC: case t_COL: case t_MAT: pari_APPLY_same(gtrunc(gel(x,i)));
  }
  pari_err_TYPE("gtrunc",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
trunc0(GEN x, GEN *pte)
{
  if (pte) { long e; x = gcvtoi(x,&e); *pte = stoi(e); }
  return gtrunc(x);
}
/*******************************************************************/
/*                                                                 */
/*                  CONVERSIONS -->  INT, POL & SER                */
/*                                                                 */
/*******************************************************************/

/* return a_(n-1) B^(n-1) + ... + a_0, where B = 2^32.
 * The a_i are 32bits integers */
GEN
mkintn(long n, ...)
{
  va_list ap;
  GEN x, y;
  long i;
#ifdef LONG_IS_64BIT
  long e = (n&1);
  n = (n+1) >> 1;
#endif
  va_start(ap,n);
  x = cgetipos(n+2);
  y = int_MSW(x);
  for (i=0; i <n; i++)
  {
#ifdef LONG_IS_64BIT
    ulong a = (e && !i)? 0: (ulong) va_arg(ap, unsigned int);
    ulong b = (ulong) va_arg(ap, unsigned int);
    *y = (a << 32) | b;
#else
    *y = (ulong) va_arg(ap, unsigned int);
#endif
    y = int_precW(y);
  }
  va_end(ap);
  return int_normalize(x, 0);
}

/* 2^32 a + b */
GEN
uu32toi(ulong a, ulong b)
{
#ifdef LONG_IS_64BIT
  return utoi((a<<32) | b);
#else
  return uutoi(a, b);
#endif
}
/* - (2^32 a + b), assume a or b != 0 */
GEN
uu32toineg(ulong a, ulong b)
{
#ifdef LONG_IS_64BIT
  return utoineg((a<<32) | b);
#else
  return uutoineg(a, b);
#endif
}

/* return a_(n-1) x^(n-1) + ... + a_0 */
GEN
mkpoln(long n, ...)
{
  va_list ap;
  GEN x, y;
  long i, l = n+2;
  va_start(ap,n);
  x = cgetg(l, t_POL); y = x + 2;
  x[1] = evalvarn(0);
  for (i=n-1; i >= 0; i--) gel(y,i) = va_arg(ap, GEN);
  va_end(ap); return normalizepol_lg(x, l);
}

/* return [a_1, ..., a_n] */
GEN
mkvecn(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_VEC);
  for (i=1; i <= n; i++) gel(x,i) = va_arg(ap, GEN);
  va_end(ap); return x;
}

GEN
mkcoln(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_COL);
  for (i=1; i <= n; i++) gel(x,i) = va_arg(ap, GEN);
  va_end(ap); return x;
}

GEN
mkvecsmalln(long n, ...)
{
  va_list ap;
  GEN x;
  long i;
  va_start(ap,n);
  x = cgetg(n+1, t_VECSMALL);
  for (i=1; i <= n; i++) x[i] = va_arg(ap, long);
  va_end(ap); return x;
}

GEN
scalarpol(GEN x, long v)
{
  GEN y;
  if (isrationalzero(x)) return zeropol(v);
  y = cgetg(3,t_POL);
  y[1] = gequal0(x)? evalvarn(v)
                   : evalvarn(v) | evalsigne(1);
  gel(y,2) = gcopy(x); return y;
}
GEN
scalarpol_shallow(GEN x, long v)
{
  GEN y;
  if (isrationalzero(x)) return zeropol(v);
  y = cgetg(3,t_POL);
  y[1] = gequal0(x)? evalvarn(v)
                   : evalvarn(v) | evalsigne(1);
  gel(y,2) = x; return y;
}

/* x0 + x1*T, do not assume x1 != 0 */
GEN
deg1pol(GEN x1, GEN x0,long v)
{
  GEN x = cgetg(4,t_POL);
  x[1] = evalsigne(1) | evalvarn(v);
  gel(x,2) = x0 == gen_0? x0: gcopy(x0); /* gen_0 frequent */
  gel(x,3) = gcopy(x1); return normalizepol_lg(x,4);
}

/* same, no copy */
GEN
deg1pol_shallow(GEN x1, GEN x0,long v)
{
  GEN x = cgetg(4,t_POL);
  x[1] = evalsigne(1) | evalvarn(v);
  gel(x,2) = x0;
  gel(x,3) = x1; return normalizepol_lg(x,4);
}

GEN
deg2pol_shallow(GEN x2, GEN x1, GEN x0, long v)
{
  GEN x = cgetg(5,t_POL);
  x[1] = evalsigne(1) | evalvarn(v);
  gel(x,2) = x0;
  gel(x,3) = x1;
  gel(x,4) = x2;
  return normalizepol_lg(x,5);
}

static GEN
_gtopoly(GEN x, long v, int reverse)
{
  long tx = typ(x);
  GEN y;

  if (v<0) v = 0;
  switch(tx)
  {
    case t_POL:
      if (varncmp(varn(x), v) < 0) pari_err_PRIORITY("gtopoly", x, "<", v);
      y = RgX_copy(x); break;
    case t_SER:
      if (varncmp(varn(x), v) < 0) pari_err_PRIORITY("gtopoly", x, "<", v);
      y = ser2rfrac(x);
      if (typ(y) != t_POL)
        pari_err_DOMAIN("gtopoly", "valuation", "<", gen_0, x);
      break;
    case t_RFRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      long vb = varn(b);
      if (varncmp(vb, v) < 0) pari_err_PRIORITY("gtopoly", x, "<", v);
      if (typ(a) != t_POL || varn(a) != vb) return zeropol(v);
      y = RgX_div(a,b); break;
    }
    case t_VECSMALL: x = zv_to_ZV(x); /* fall through */
    case t_QFB: case t_VEC: case t_COL: case t_MAT:
    {
      long j, k, lx = lg(x);
      GEN z;
      if (tx == t_QFB) lx--;
      if (varncmp(gvar(x), v) <= 0) pari_err_PRIORITY("gtopoly", x, "<=", v);
      y = cgetg(lx+1, t_POL);
      y[1] = evalvarn(v);
      if (reverse) {
        x--;
        for (j=2; j<=lx; j++) gel(y,j) = gel(x,j);
      } else {
        for (j=2, k=lx; k>=2; j++) gel(y,j) = gel(x,--k);
      }
      z = RgX_copy(normalizepol_lg(y,lx+1));
      settyp(y, t_VECSMALL);/* left on stack */
      return z;
    }
    default:
      if (is_scalar_t(tx)) return scalarpol(x,v);
      pari_err_TYPE("gtopoly",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  setvarn(y,v); return y;
}

GEN
gtopolyrev(GEN x, long v) { return _gtopoly(x,v,1); }

GEN
gtopoly(GEN x, long v) { return _gtopoly(x,v,0); }

static GEN
gtovecpost(GEN x, long n)
{
  long i, imax, lx, tx = typ(x);
  GEN y = zerovec(n);

  if (is_scalar_t(tx) || tx == t_RFRAC) { gel(y,1) = gcopy(x); return y; }
  switch(tx)
  {
    case t_POL:
      lx = lg(x); imax = minss(lx-2, n);
      for (i=1; i<=imax; i++) gel(y,i) = gcopy(gel(x,lx-i));
      return y;
    case t_SER:
      lx = lg(x); imax = minss(lx-2, n); x++;
      for (i=1; i<=imax; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_QFB:
      lx = lg(x)-1; /* remove discriminant */
      imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_VEC: case t_COL:
      lx = lg(x); imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_LIST:
      if (list_typ(x) == t_LIST_MAP) pari_err_TYPE("gtovec",x);
      x = list_data(x); lx = x? lg(x): 1;
      imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_STR:
    {
      char *s = GSTR(x);
      imax = minss(strlen(s), n); s--;
      for (i=1; i<=imax; i++) gel(y,i) = chartoGENstr(s[i]);
      return y;
    }
    case t_VECSMALL:
      lx = lg(x); imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) gel(y,i) = stoi(x[i]);
      return y;
    default: pari_err_TYPE("gtovec",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}

static GEN
init_vectopre(long a, long n, GEN y, long *imax)
{
  if (n <= a) { *imax = n; return y; }
  *imax = a; return y + n - a;
}
/* assume n > 0 */
static GEN
gtovecpre(GEN x, long n)
{
  long a, i, imax, lx, tx = typ(x);
  GEN y = zerovec(n), y0;

  if (is_scalar_t(tx) || tx == t_RFRAC) { gel(y,n) = gcopy(x); return y; }
  switch(tx)
  {
    case t_POL:
      lx = lg(x); a = lx-2;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x -= a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = gcopy(gel(x,lx-i));
      return y;
    case t_SER:
      a = lg(x)-2; x++;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = gcopy(gel(x,i));
      return y;
    case t_QFB:
      a = lg(x)-2; /* remove discriminant */
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = gcopy(gel(x,i));
      return y;
    case t_VEC: case t_COL:
      a = lg(x)-1;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = gcopy(gel(x,i));
      return y;
    case t_LIST:
      if (list_typ(x) == t_LIST_MAP) pari_err_TYPE("gtovec",x);
      x = list_data(x); a = x? lg(x)-1: 0;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = gcopy(gel(x,i));
      return y;
    case t_STR:
    {
      char *s = GSTR(x);
      a = strlen(s);
      y0 = init_vectopre(a, n, y, &imax); s--; if (imax == n) s += a-imax;
      for (i=1; i<=imax; i++) gel(y,i) = chartoGENstr(s[i]);
      return y;
    }
    case t_VECSMALL:
      a = lg(x)-1;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) gel(y0,i) = stoi(x[i]);
      return y;
    default: pari_err_TYPE("gtovec",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}
GEN
gtovec0(GEN x, long n)
{
  if (!n) return gtovec(x);
  if (n > 0) return gtovecpost(x, n);
  return gtovecpre(x, -n);
}

GEN
gtovec(GEN x)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (is_scalar_t(tx)) return mkveccopy(x);
  switch(tx)
  {
    case t_POL:
      lx=lg(x); y=cgetg(lx-1,t_VEC);
      for (i=1; i<=lx-2; i++) gel(y,i) = gcopy(gel(x,lx-i));
      return y;
    case t_SER:
      lx=lg(x); y=cgetg(lx-1,t_VEC); x++;
      for (i=1; i<=lx-2; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_RFRAC: return mkveccopy(x);
    case t_QFB:
      retmkvec3(icopy(gel(x,1)), icopy(gel(x,2)), icopy(gel(x,3)));
    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_LIST:
      if (list_typ(x) == t_LIST_MAP) return mapdomain(x);
      x = list_data(x); lx = x? lg(x): 1;
      y = cgetg(lx, t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    case t_STR:
    {
      char *s = GSTR(x);
      lx = strlen(s)+1; y = cgetg(lx, t_VEC);
      s--;
      for (i=1; i<lx; i++) gel(y,i) = chartoGENstr(s[i]);
      return y;
    }
    case t_VECSMALL:
      return vecsmall_to_vec(x);
    case t_ERROR:
      lx=lg(x); y = cgetg(lx,t_VEC);
      gel(y,1) = errname(x);
      for (i=2; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
      return y;
    default: pari_err_TYPE("gtovec",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}

GEN
gtovecrev0(GEN x, long n)
{
  GEN y = gtovec0(x, -n);
  vecreverse_inplace(y);
  return y;
}
GEN
gtovecrev(GEN x) { return gtovecrev0(x, 0); }

GEN
gtocol0(GEN x, long n)
{
  GEN y;
  if (!n) return gtocol(x);
  y = gtovec0(x, n);
  settyp(y, t_COL); return y;
}
GEN
gtocol(GEN x)
{
  long lx, tx, i, j, h;
  GEN y;
  tx = typ(x);
  if (tx != t_MAT) { y = gtovec(x); settyp(y, t_COL); return y; }
  lx = lg(x); if (lx == 1) return cgetg(1, t_COL);
  h = lgcols(x); y = cgetg(h, t_COL);
  for (i = 1 ; i < h; i++) {
    gel(y,i) = cgetg(lx, t_VEC);
    for (j = 1; j < lx; j++) gmael(y,i,j) = gcopy(gcoeff(x,i,j));
  }
  return y;
}

GEN
gtocolrev0(GEN x, long n)
{
  GEN y = gtocol0(x, -n);
  long ly = lg(y), lim = ly>>1, i;
  for (i = 1; i <= lim; i++) swap(gel(y,i), gel(y,ly-i));
  return y;
}
GEN
gtocolrev(GEN x) { return gtocolrev0(x, 0); }

static long
Itos(GEN x)
{
   if (typ(x) != t_INT) pari_err_TYPE("vectosmall",x);
   return itos(x);
}

static GEN
gtovecsmallpost(GEN x, long n)
{
  long i, imax, lx;
  GEN y = zero_Flv(n);

  switch(typ(x))
  {
    case t_INT:
      y[1] = itos(x); return y;
    case t_POL:
      lx=lg(x); imax = minss(lx-2, n);
      for (i=1; i<=imax; i++) y[i] = Itos(gel(x,lx-i));
      return y;
    case t_SER:
      lx=lg(x); imax = minss(lx-2, n); x++;
      for (i=1; i<=imax; i++) y[i] = Itos(gel(x,i));
      return y;
    case t_VEC: case t_COL:
      lx=lg(x); imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) y[i] = Itos(gel(x,i));
      return y;
    case t_LIST:
      x = list_data(x); lx = x? lg(x): 1;
      imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) y[i] = Itos(gel(x,i));
      return y;
    case t_VECSMALL:
      lx=lg(x);
      imax = minss(lx-1, n);
      for (i=1; i<=imax; i++) y[i] = x[i];
      return y;
    case t_STR:
    {
      unsigned char *s = (unsigned char*)GSTR(x);
      imax = minss(strlen((const char *)s), n); s--;
      for (i=1; i<=imax; i++) y[i] = (long)s[i];
      return y;
    }
    default: pari_err_TYPE("gtovecsmall",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}
static GEN
gtovecsmallpre(GEN x, long n)
{
  GEN y = zero_Flv(n), y0;
  long a, i, imax, lx;

  switch(typ(x))
  {
    case t_INT:
      y[n] = itos(x); return y;
    case t_POL:
      lx = lg(x); a = lx-2;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x -= a-imax;
      for (i=1; i<=imax; i++) y0[i] = Itos(gel(x,lx-i));
      return y;
    case t_SER:
      a = lg(x)-2; x++;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) y0[i] = Itos(gel(x,i));
      return y;
    case t_VEC: case t_COL:
      a = lg(x)-1;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) y0[i] = Itos(gel(x,i));
      return y;
    case t_LIST:
      x = list_data(x); a = x? lg(x)-1: 0;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) y0[i] = Itos(gel(x,i));
      return y;
    case t_VECSMALL:
      a = lg(x)-1;
      y0 = init_vectopre(a, n, y, &imax); if (imax == n) x += a-imax;
      for (i=1; i<=imax; i++) y0[i] = x[i];
      return y;
    case t_STR:
    {
      unsigned char *s = (unsigned char*)GSTR(x);
      a = strlen((const char *)s);
      y0 = init_vectopre(a, n, y, &imax); s--; if (imax == n) s += a-imax;
      for (i=1; i<=imax; i++) y0[i] = (long)s[i];
      return y;
    }
    default: pari_err_TYPE("gtovecsmall",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
}

GEN
gtovecsmall0(GEN x, long n)
{
  if (!n) return gtovecsmall(x);
  if (n > 0) return gtovecsmallpost(x, n);
  return gtovecsmallpre(x, -n);
}

GEN
gtovecsmall(GEN x)
{
  GEN V;
  long l, i;

  switch(typ(x))
  {
    case t_INT: return mkvecsmall(itos(x));
    case t_STR:
    {
      unsigned char *s = (unsigned char*)GSTR(x);
      l = strlen((const char *)s);
      V = cgetg(l+1, t_VECSMALL);
      s--;
      for (i=1; i<=l; i++) V[i] = (long)s[i];
      return V;
    }
    case t_VECSMALL: return leafcopy(x);
    case t_LIST:
      x = list_data(x);
      if (!x) return cgetg(1, t_VECSMALL);
      /* fall through */
    case t_VEC: case t_COL:
      l = lg(x); V = cgetg(l,t_VECSMALL);
      for(i=1; i<l; i++) V[i] = Itos(gel(x,i));
      return V;
    case t_POL:
      l = lg(x); V = cgetg(l-1,t_VECSMALL);
      for (i=1; i<=l-2; i++) V[i] = Itos(gel(x,l-i));
      return V;
    case t_SER:
      l = lg(x); V = cgetg(l-1,t_VECSMALL); x++;
      for (i=1; i<=l-2; i++) V[i] = Itos(gel(x,i));
      return V;
    default:
      pari_err_TYPE("vectosmall",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
}

GEN
compo(GEN x, long n)
{
  long tx = typ(x);
  ulong l, lx = (ulong)lg(x);

  if (!is_recursive_t(tx))
  {
    if (tx == t_VECSMALL)
    {
      if (n < 1) pari_err_COMPONENT("", "<", gen_1, stoi(n));
      if ((ulong)n >= lx) pari_err_COMPONENT("", ">", utoi(lx-1), stoi(n));
      return stoi(x[n]);
    }
    pari_err_TYPE("component [leaf]", x);
  }
  if (n < 1) pari_err_COMPONENT("", "<", gen_1, stoi(n));
  if (tx == t_LIST) {
    x = list_data(x); tx = t_VEC;
    lx = (ulong)(x? lg(x): 1);
  }
  l = (ulong)lontyp[tx] + (ulong)n-1; /* beware overflow */
  if (l >= lx) pari_err_COMPONENT("", ">", utoi(lx-lontyp[tx]), stoi(n));
  return gcopy(gel(x,l));
}

/* assume x a t_POL */
static GEN
_polcoef(GEN x, long n, long v)
{
  long i, w, lx = lg(x), dx = lx-3;
  GEN z;
  if (dx < 0) return gen_0;
  if (v < 0 || v == (w=varn(x)))
    return (n < 0 || n > dx)? gen_0: gel(x,n+2);
  if (varncmp(w,v) > 0) return n? gen_0: x;
  /* w < v */
  z = cgetg(lx, t_POL); z[1] = x[1];
  for (i = 2; i < lx; i++) gel(z,i) = polcoef_i(gel(x,i), n, v);
  z = normalizepol_lg(z, lx);
  switch(lg(z))
  {
    case 2: z = gen_0; break;
    case 3: z = gel(z,2); break;
  }
  return z;
}

/* assume x a t_SER */
static GEN
_sercoef(GEN x, long n, long v)
{
  long i, w = varn(x), lx = lg(x), dx = lx-3, N;
  GEN z;
  if (v < 0) v = w;
  N = v == w? n - valser(x): n;
  if (dx < 0)
  {
    if (N >= 0) pari_err_DOMAIN("polcoef", "t_SER", "=", x, x);
    return gen_0;
  }
  if (v == w)
  {
    if (!dx && !signe(x) && !isinexact(gel(x,2))) dx = -1;
    if (N > dx)
      pari_err_DOMAIN("polcoef", "degree", ">", stoi(dx+valser(x)), stoi(n));
    return (N < 0)? gen_0: gel(x,N+2);
  }
  if (varncmp(w,v) > 0) return N? gen_0: x;
  /* w < v */
  z = cgetg(lx, t_SER); z[1] = x[1];
  for (i = 2; i < lx; i++) gel(z,i) = polcoef_i(gel(x,i), n, v);
  return normalizeser(z);
}

/* assume x a t_RFRAC(n) */
static GEN
_rfraccoef(GEN x, long n, long v)
{
  GEN p = gel(x,1), q = gel(x,2), z;
  long vp = gvar(p), vq = gvar(q), vz;
  if (v < 0) v = varncmp(vp, vq) < 0? vp: vq;
  vz = v;
  if (varncmp(vp, v) < 0 || varncmp(vq, v) < 0) vz = fetch_var_higher();
  if (vp != v) p = swap_vars(p, v, vz);
  if (vq != v) q = swap_vars(q, v, vz);
  n += degpol(q);
  z = gdiv(_polcoef(p, n, vz), leading_coeff(q));
  if (vz != v) (void)delete_var();
  if (!RgX_is_monomial(q)) pari_err_TYPE("polcoef", x);
  return z;
}

GEN
polcoef_i(GEN x, long n, long v)
{
  long tx = typ(x);
  switch(tx)
  {
    case t_POL: return _polcoef(x,n,v);
    case t_SER: return _sercoef(x,n,v);
    case t_RFRAC: return _rfraccoef(x,n,v);
  }
  if (!is_scalar_t(tx)) pari_err_TYPE("polcoef", x);
  return n? gen_0: x;
}

/* with respect to the main variable if v<0, with respect to the variable v
 * otherwise. v ignored if x is not a polynomial/series. */
GEN
polcoef(GEN x, long n, long v)
{
  pari_sp av = avma;
  x = polcoef_i(x,n,v);
  if (x == gen_0) return x;
  return (avma == av)? gcopy(x): gc_GEN(av, x);
}

static GEN
vecdenom(GEN v, long imin, long imax)
{
  long i = imin;
  GEN s;
  if (imin > imax) return gen_1;
  s = denom_i(gel(v,i));
  for (i++; i<=imax; i++)
  {
    GEN t = denom_i(gel(v,i));
    if (t != gen_1) s = glcm(s,t);
  }
  return s;
}
static GEN denompol(GEN x, long v);
static GEN
vecdenompol(GEN v, long imin, long imax, long vx)
{
  long i = imin;
  GEN s;
  if (imin > imax) return gen_1;
  s = denompol(gel(v,i), vx);
  for (i++; i<=imax; i++)
  {
    GEN t = denompol(gel(v,i), vx);
    if (t != gen_1) s = glcm(s,t);
  }
  return s;
}
GEN
denom_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT:
    case t_REAL:
    case t_INTMOD:
    case t_FFELT:
    case t_PADIC:
    case t_SER:
    case t_VECSMALL: return gen_1;
    case t_FRAC: return gel(x,2);
    case t_COMPLEX: return vecdenom(x,1,2);
    case t_QUAD: return vecdenom(x,2,3);
    case t_POLMOD: return denom_i(gel(x,2));
    case t_RFRAC: return gel(x,2);
    case t_POL: return pol_1(varn(x));
    case t_VEC: case t_COL: case t_MAT: return vecdenom(x, 1, lg(x)-1);
  }
  pari_err_TYPE("denom",x);
  return NULL; /* LCOV_EXCL_LINE */
}
/* v has lower (or equal) priority as x's main variable */
static GEN
denompol(GEN x, long v)
{
  long vx, tx = typ(x);
  if (is_scalar_t(tx)) return gen_1;
  switch(typ(x))
  {
    case t_SER:
      if (varn(x) != v) return x;
      vx = valser(x); return vx < 0? pol_xn(-vx, v): pol_1(v);
    case t_RFRAC: x = gel(x,2); return varn(x) == v? x: pol_1(v);
    case t_POL: return pol_1(v);
    case t_VEC: case t_COL: case t_MAT: return vecdenompol(x, 1, lg(x)-1, v);
  }
  pari_err_TYPE("denom",x);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
denom(GEN x) { pari_sp av = avma; return gc_GEN(av, denom_i(x)); }

static GEN
denominator_v(GEN x, long v)
{
  long v0 = gvar(x);
  GEN d;
  if (v0 == NO_VARIABLE || varncmp(v0,v) > 0) return pol_1(v);
  if (v0 != v) { v0 = fetch_var_higher(); x = gsubst(x, v, pol_x(v0)); }
  d = denompol(x, v0);
  if (v0 != v) { d = gsubst(d, v0, pol_x(v)); (void)delete_var(); }
  return d;
}
GEN
denominator(GEN x, GEN D)
{
  pari_sp av = avma;
  GEN d;
  if (!D) return denom(x);
  if (isint1(D))
  {
    d = Q_denom_safe(x);
    if (!d) { set_avma(av); return gen_1; }
    return gc_GEN(av, d);
  }
  if (!gequalX(D)) pari_err_TYPE("denominator", D);
  return gc_upto(av, denominator_v(x, varn(D)));
}
GEN
numerator(GEN x, GEN D)
{
  pari_sp av = avma;
  long v;
  if (!D) return numer(x);
  if (isint1(D)) return Q_remove_denom(x,NULL);
  if (!gequalX(D)) pari_err_TYPE("numerator", D);
  v = varn(D); /* optimization */
  if (typ(x) == t_RFRAC && varn(gel(x,2)) == v) return gcopy(gel(x,1));
  return gc_upto(av, gmul(x, denominator_v(x,v)));
}
GEN
content0(GEN x, GEN D)
{
  pari_sp av = avma;
  long v, v0;
  GEN d;
  if (!D) return content(x);
  if (isint1(D))
  {
    d = Q_content_safe(x);
    return d? d: gen_1;
  }
  if (!gequalX(D)) pari_err_TYPE("content", D);
  v = varn(D);
  v0 = gvar(x); if (v0 == NO_VARIABLE) return gen_1;
  if (varncmp(v0,v) > 0)
  {
    v0 = gvar2(x);
    return v0 == NO_VARIABLE? gen_1: pol_1(v0);
  }
  if (v0 != v) { v0 = fetch_var_higher(); x = gsubst(x, v, pol_x(v0)); }
  d = content(x);
  /* gsubst is needed because of content([x]) = x */
  if (v0 != v) { d = gsubst(d, v0, pol_x(v)); (void)delete_var(); }
  return gc_upto(av, d);
}

GEN
numer_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT:
    case t_REAL:
    case t_INTMOD:
    case t_FFELT:
    case t_PADIC:
    case t_SER:
    case t_VECSMALL:
    case t_POL: return x;
    case t_POLMOD: return mkpolmod(numer_i(gel(x,2)), gel(x,1));
    case t_FRAC:
    case t_RFRAC: return gel(x,1);
    case t_COMPLEX:
    case t_QUAD:
    case t_VEC:
    case t_COL:
    case t_MAT: return gmul(denom_i(x),x);
  }
  pari_err_TYPE("numer",x);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
numer(GEN x) { pari_sp av = avma; return gc_GEN(av, numer_i(x)); }

/* Lift only intmods if v does not occur in x, lift with respect to main
 * variable of x if v < 0, with respect to variable v otherwise */
GEN
lift0(GEN x, long v)
{
  GEN y;

  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_INTMOD: return v < 0? icopy(gel(x,2)): gcopy(x);
    case t_POLMOD:
      if (v < 0 || v == varn(gel(x,1))) return gcopy(gel(x,2));
      y = cgetg(3, t_POLMOD);
      gel(y,1) = lift0(gel(x,1),v);
      gel(y,2) = lift0(gel(x,2),v); return y;
    case t_PADIC: return v < 0? padic_to_Q(x): gcopy(x);
    case t_POL:
      pari_APPLY_pol(lift0(gel(x,i), v));
    case t_SER:
      if (ser_isexactzero(x))
      {
        if (lg(x) == 2) return gcopy(x);
        y = scalarser(lift0(gel(x,2),v), varn(x), 1);
        setvalser(y, valser(x)); return y;
      }
      pari_APPLY_ser(lift0(gel(x,i), v));
    case t_COMPLEX: case t_QUAD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(lift0(gel(x,i), v));
    default: return gcopy(x);
  }
}
/* same as lift, shallow */
GEN
lift_shallow(GEN x)
{
  GEN y;
  switch(typ(x))
  {
    case t_INTMOD: case t_POLMOD: return gel(x,2);
    case t_PADIC: return padic_to_Q(x);
    case t_SER:
      if (ser_isexactzero(x))
      {
        if (lg(x) == 2) return x;
        y = scalarser(lift_shallow(gel(x,2)), varn(x), 1);
        setvalser(y, valser(x)); return y;
      }
      pari_APPLY_ser(lift_shallow(gel(x,i)));
    case t_POL:
      pari_APPLY_pol(lift_shallow(gel(x,i)));
    case t_COMPLEX: case t_QUAD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(lift_shallow(gel(x,i)));
    default: return x;
  }
}
GEN
lift(GEN x) { return lift0(x,-1); }

GEN
liftall_shallow(GEN x)
{
  GEN y;
  switch(typ(x))
  {
    case t_INTMOD: return gel(x,2);
    case t_POLMOD:
      return liftall_shallow(gel(x,2));
    case t_PADIC: return padic_to_Q(x);
    case t_POL:
      pari_APPLY_pol(liftall_shallow(gel(x,i)));
    case t_SER:
      if (ser_isexactzero(x))
      {
        if (lg(x) == 2) return x;
        y = scalarser(liftall_shallow(gel(x,2)), varn(x), 1);
        setvalser(y, valser(x)); return y;
      }
      pari_APPLY_ser(liftall_shallow(gel(x,i)));
    case t_COMPLEX: case t_QUAD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(liftall_shallow(gel(x,i)));
    default: return x;
  }
}
GEN
liftall(GEN x)
{ pari_sp av = avma; return gc_GEN(av, liftall_shallow(x)); }

GEN
liftint_shallow(GEN x)
{
  GEN y;
  switch(typ(x))
  {
    case t_INTMOD: return gel(x,2);
    case t_PADIC: return padic_to_Q(x);
    case t_POL:
      pari_APPLY_pol(liftint_shallow(gel(x,i)));
    case t_SER:
      if (ser_isexactzero(x))
      {
        if (lg(x) == 2) return x;
        y = scalarser(liftint_shallow(gel(x,2)), varn(x), 1);
        setvalser(y, valser(x)); return y;
      }
      pari_APPLY_ser(liftint_shallow(gel(x,i)));
    case t_POLMOD: case t_COMPLEX: case t_QUAD: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(liftint_shallow(gel(x,i)));
    default: return x;
  }
}
GEN
liftint(GEN x)
{ pari_sp av = avma; return gc_GEN(av, liftint_shallow(x)); }

GEN
liftpol_shallow(GEN x)
{
  GEN y;
  switch(typ(x))
  {
    case t_POLMOD:
      return liftpol_shallow(gel(x,2));
    case t_POL:
      pari_APPLY_pol(liftpol_shallow(gel(x,i)));
    case t_SER:
      if (ser_isexactzero(x))
      {
        if (lg(x) == 2) return x;
        y = scalarser(liftpol(gel(x,2)), varn(x), 1);
        setvalser(y, valser(x)); return y;
      }
      pari_APPLY_ser(liftpol_shallow(gel(x,i)));
    case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(liftpol_shallow(gel(x,i)));
    default: return x;
  }
}
GEN
liftpol(GEN x)
{ pari_sp av = avma; return gc_GEN(av, liftpol_shallow(x)); }

static GEN
centerliftii(GEN x, GEN y)
{
  pari_sp av = avma;
  long i = cmpii(shifti(x,1), y);
  set_avma(av); return (i > 0)? subii(x,y): icopy(x);
}

/* see lift0 */
GEN
centerlift0(GEN x, long v)
{ return v < 0? centerlift(x): lift0(x,v); }
GEN
centerlift(GEN x)
{
  GEN u, p, pd;
  long v;
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_INTMOD: return centerliftii(gel(x,2), gel(x,1));
    case t_POLMOD: return gcopy(gel(x,2));
    case t_POL:
      pari_APPLY_pol(centerlift(gel(x,i)));
   case t_SER:
      if (ser_isexactzero(x)) return lift(x);
      pari_APPLY_ser(centerlift(gel(x,i)));
   case t_COMPLEX: case t_QUAD: case t_RFRAC:
   case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(centerlift(gel(x,i)));
    case t_PADIC:
      if (!signe(padic_u(x))) return gen_0;
      v = valp(x); u = padic_u(x); p = padic_p(x); pd = padic_pd(x);
      if (v >= 0)
      { /* here p^v is an integer */
        pari_sp av = avma;
        GEN z = centerliftii(u, pd);
        return v? gc_INT(av, mulii(powiu(p,v), z)): z;
      }
      retmkfrac(centerliftii(u, pd), powiu(p,-v));
    default: return gcopy(x);
  }
}

/*******************************************************************/
/*                                                                 */
/*                      REAL & IMAGINARY PARTS                     */
/*                                                                 */
/*******************************************************************/

static GEN
op_ReIm(GEN f(GEN), GEN x)
{
  switch(typ(x))
  {
    case t_POL: pari_APPLY_pol(f(gel(x,i)));
    case t_SER: pari_APPLY_ser(f(gel(x,i)));
    case t_RFRAC: {
      pari_sp av = avma;
      GEN n, d, dxb = conj_i(gel(x,2));
      n = gmul(gel(x,1), dxb);
      d = gmul(gel(x,2), dxb);
      return gc_upto(av, gdiv(f(n), d));
    }
    case t_VEC: case t_COL: case t_MAT: pari_APPLY_same(f(gel(x, i)));
  }
  pari_err_TYPE("greal/gimag",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
real_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return x;
    case t_COMPLEX:
      return gel(x,1);
    case t_QUAD:
      return gel(x,2);
  }
  return op_ReIm(real_i,x);
}
GEN
imag_i(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gen_0;
    case t_COMPLEX:
      return gel(x,2);
    case t_QUAD:
      return gel(x,3);
  }
  return op_ReIm(imag_i,x);
}
GEN
greal(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return mpcopy(x);

    case t_FRAC:
      return gcopy(x);

    case t_COMPLEX:
      return gcopy(gel(x,1));

    case t_QUAD:
      return gcopy(gel(x,2));
  }
  return op_ReIm(greal,x);
}
GEN
gimag(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gen_0;

    case t_COMPLEX:
      return gcopy(gel(x,2));

    case t_QUAD:
      return gcopy(gel(x,3));
  }
  return op_ReIm(gimag,x);
}

/* return Re(x * y), x and y scalars */
GEN
mulreal(GEN x, GEN y)
{
  if (typ(x) == t_COMPLEX)
  {
    if (typ(y) == t_COMPLEX)
    {
      pari_sp av = avma;
      GEN a = gmul(gel(x,1), gel(y,1));
      GEN b = gmul(gel(x,2), gel(y,2));
      return gc_upto(av, gsub(a, b));
    }
    x = gel(x,1);
  }
  else
    if (typ(y) == t_COMPLEX) y = gel(y,1);
  return gmul(x,y);
}
/* Compute Re(x * y), x and y matrices of compatible dimensions
 * assume scalar entries */
GEN
RgM_mulreal(GEN x, GEN y)
{
  long i, j, k, l, lx = lg(x), ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  l = (lx == 1)? 1: lgcols(x);
  for (j=1; j<ly; j++)
  {
    GEN zj = cgetg(l,t_COL), yj = gel(y,j);
    gel(z,j) = zj;
    for (i=1; i<l; i++)
    {
      pari_sp av = avma;
      GEN c = mulreal(gcoeff(x,i,1),gel(yj,1));
      for (k=2; k<lx; k++) c = gadd(c, mulreal(gcoeff(x,i,k),gel(yj,k)));
      gel(zj, i) = gc_upto(av, c);
    }
  }
  return z;
}

/* Compute Re(x * y), symmetric result, x and y vectors of compatible
 * dimensions; assume scalar entries */
GEN
RgC_RgV_mulrealsym(GEN x, GEN y)
{
  long i, j, l = lg(x);
  GEN q = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    gel(q,j) = cgetg(l,t_COL);
    for (i = 1; i <= j; i++)
      gcoeff(q,i,j) = gcoeff(q,j,i) = mulreal(gel(x,i), gel(y,j));
  }
  return q;
}

/*******************************************************************/
/*                                                                 */
/*                     LOGICAL OPERATIONS                          */
/*                                                                 */
/*******************************************************************/
static long
_egal_i(GEN x, GEN y)
{
  x = simplify_shallow(x);
  y = simplify_shallow(y);
  if (typ(y) == t_INT)
  {
    if (equali1(y)) return gequal1(x);
    if (equalim1(y)) return gequalm1(x);
  }
  else if (typ(x) == t_INT)
  {
    if (equali1(x)) return gequal1(y);
    if (equalim1(x)) return gequalm1(y);
  }
  return gequal(x, y);
}
static long
_egal(GEN x, GEN y)
{ pari_sp av = avma; return gc_long(av, _egal_i(x, y)); }

GEN
glt(GEN x, GEN y) { return gcmp(x,y)<0? gen_1: gen_0; }

GEN
gle(GEN x, GEN y) { return gcmp(x,y)<=0? gen_1: gen_0; }

GEN
gge(GEN x, GEN y) { return gcmp(x,y)>=0? gen_1: gen_0; }

GEN
ggt(GEN x, GEN y) { return gcmp(x,y)>0? gen_1: gen_0; }

GEN
geq(GEN x, GEN y) { return _egal(x,y)? gen_1: gen_0; }

GEN
gne(GEN x, GEN y) { return _egal(x,y)? gen_0: gen_1; }

GEN
gnot(GEN x) { return gequal0(x)? gen_1: gen_0; }

/*******************************************************************/
/*                                                                 */
/*                      FORMAL SIMPLIFICATIONS                     */
/*                                                                 */
/*******************************************************************/

GEN
geval_gp(GEN x, GEN t)
{
  long lx, i, tx = typ(x);
  pari_sp av;
  GEN y, z;

  if (is_const_t(tx) || tx==t_VECSMALL) return gcopy(x);
  switch(tx)
  {
    case t_STR:
      return localvars_read_str(GSTR(x),t);

    case t_POLMOD:
      av = avma;
      return gc_upto(av, gmodulo(geval_gp(gel(x,2),t),
                                      geval_gp(gel(x,1),t)));

    case t_POL:
      lx=lg(x); if (lx==2) return gen_0;
      z = fetch_var_value(varn(x),t);
      if (!z) return RgX_copy(x);
      av = avma; y = geval_gp(gel(x,lx-1),t);
      for (i=lx-2; i>1; i--)
        y = gadd(geval_gp(gel(x,i),t), gmul(z,y));
      return gc_upto(av, y);

    case t_SER:
      pari_err_IMPL( "evaluation of a power series");

    case t_RFRAC:
      av = avma;
      return gc_upto(av, gdiv(geval_gp(gel(x,1),t), geval_gp(gel(x,2),t)));

    case t_QFB: case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(geval_gp(gel(x,i),t));

    case t_CLOSURE:
      if (closure_arity(x) || closure_is_variadic(x))
        pari_err_IMPL("eval on functions with parameters");
      return closure_evalres(x);
  }
  pari_err_TYPE("geval",x);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
geval(GEN x) { return geval_gp(x,NULL); }

GEN
simplify_shallow(GEN x)
{
  long v, lx;
  GEN y, z;
  if (!x) pari_err_BUG("simplify, NULL input");

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_PADIC: case t_QFB: case t_LIST: case t_STR: case t_VECSMALL:
    case t_CLOSURE: case t_ERROR: case t_INFINITY:
      return x;
    case t_COMPLEX: return isintzero(gel(x,2))? gel(x,1): x;
    case t_QUAD:    return isintzero(gel(x,3))? gel(x,2): x;

    case t_POLMOD: y = cgetg(3,t_POLMOD);
      z = gel(x,1); v = varn(z); z = simplify_shallow(z);
      if (typ(z) != t_POL || varn(z) != v) z = scalarpol_shallow(z, v);
      gel(y,1) = z;
      gel(y,2) = simplify_shallow(gel(x,2)); return y;

    case t_POL:
      lx = lg(x);
      if (lx==2) return gen_0;
      if (lx==3) return simplify_shallow(gel(x,2));
      pari_APPLY_pol(simplify_shallow(gel(x,i)));

    case t_SER:
      pari_APPLY_ser(simplify_shallow(gel(x,i)));

    case t_RFRAC: y = cgetg(3,t_RFRAC);
      gel(y,1) = simplify_shallow(gel(x,1));
      z = simplify_shallow(gel(x,2));
      if (typ(z) != t_POL) return gdiv(gel(y,1), z);
      gel(y,2) = z; return y;

    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(simplify_shallow(gel(x,i)));
  }
  pari_err_BUG("simplify_shallow, type unknown");
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
simplify(GEN x)
{
  pari_sp av = avma;
  GEN y = simplify_shallow(x);
  return av == avma ? gcopy(y): gc_GEN(av, y);
}

/*******************************************************************/
/*                                                                 */
/*                EVALUATION OF SOME SIMPLE OBJECTS                */
/*                                                                 */
/*******************************************************************/
/* q is a real symmetric matrix, x a RgV. Horner-type evaluation of q(x)
 * using (n^2+3n-2)/2 mul */
GEN
qfeval(GEN q, GEN x)
{
  pari_sp av = avma;
  long i, j, l = lg(q);
  GEN z;
  if (lg(x) != l) pari_err_DIM("qfeval");
  if (l==1) return gen_0;
  if (lgcols(q) != l) pari_err_DIM("qfeval");
  /* l = lg(x) = lg(q) > 1 */
  z = gmul(gcoeff(q,1,1), gsqr(gel(x,1)));
  for (i=2; i<l; i++)
  {
    GEN c = gel(q,i), s;
    if (isintzero(gel(x,i))) continue;
    s = gmul(gel(c,1), gel(x,1));
    for (j=2; j<i; j++) s = gadd(s, gmul(gel(c,j),gel(x,j)));
    s = gadd(gshift(s,1), gmul(gel(c,i),gel(x,i)));
    z = gadd(z, gmul(gel(x,i), s));
  }
  return gc_upto(av,z);
}

static GEN
qfbeval(GEN q, GEN z)
{
  GEN A, a = gel(q,1), b = gel(q,2), c = gel(q,3), x = gel(z,1), y = gel(z,2);
  pari_sp av = avma;
  A = gadd(gmul(x, gadd(gmul(a,x), gmul(b,y))), gmul(c, gsqr(y)));
  return gc_upto(av, A);
}
static GEN
qfbevalb(GEN q, GEN z, GEN z2)
{
  GEN A, a = gel(q,1), b = gel(q,2), c = gel(q,3);
  GEN x = gel(z,1), y = gel(z,2);
  GEN X = gel(z2,1), Y = gel(z2,2);
  GEN a2 = shifti(a,1), c2 = shifti(c,1);
  pari_sp av = avma;
  /* a2 x X + b (x Y + X y) + c2 y Y */
  A = gadd(gmul(x, gadd(gmul(a2,X), gmul(b,Y))),
           gmul(y, gadd(gmul(c2,Y), gmul(b,X))));
  return gc_upto(av, gmul2n(A, -1));
}
static GEN
qfb_ZM_apply_i(GEN q, GEN M)
{
  GEN a = gel(q,1), b = gel(q,2), c = gel(q,3), d = gel(q,4);
  GEN x = gcoeff(M,1,1), y = gcoeff(M,2,1);
  GEN z = gcoeff(M,1,2), t = gcoeff(M,2,2);
  GEN by = mulii(b,y), bt = mulii(b,t), bz  = mulii(b,z);
  GEN a2 = shifti(a,1), c2 = shifti(c,1);

  GEN A1 = mulii(x, addii(mulii(a,x), by));
  GEN A2 = mulii(c, sqri(y));
  GEN B1 = mulii(x, addii(mulii(a2,z), bt));
  GEN B2 = mulii(y, addii(mulii(c2,t), bz));
  GEN C1 = mulii(z, addii(mulii(a,z), bt));
  GEN C2 = mulii(c, sqri(t));
  GEN m = sqri(subii(mulii(x,t), mulii(y,z)));
  if (signe(m)==0) pari_err_INV("qfapply",M);
  retmkqfb(addii(A1,A2), addii(B1,B2), addii(C1, C2), mulii(d, m));
}

GEN
qfb_ZM_apply(GEN q, GEN M)
{
  pari_sp av = avma;
  return gc_upto(av, qfb_ZM_apply_i(q, M));
}

static GEN
qfnorm0(GEN q, GEN x)
{
  if (!q) switch(typ(x))
  {
    case t_VEC: case t_COL: return RgV_dotsquare(x);
    case t_MAT: return gram_matrix(x);
    default: pari_err_TYPE("qfeval",x);
  }
  switch(typ(q))
  {
    case t_MAT: break;
    case t_QFB:
      if (lg(x) == 3) switch(typ(x))
      {
        case t_VEC:
        case t_COL: return qfbeval(q,x);
        case t_MAT: if (RgM_is_ZM(x)) return qfb_ZM_apply(q,x);
        default: pari_err_TYPE("qfeval",x);
      }
    default: pari_err_TYPE("qfeval",q);
  }
  switch(typ(x))
  {
    case t_VEC: case t_COL: break;
    case t_MAT: return qf_RgM_apply(q, x);
    default: pari_err_TYPE("qfeval",x);
  }
  return qfeval(q,x);
}
/* obsolete, use qfeval0 */
GEN
qfnorm(GEN x, GEN q) { return qfnorm0(q,x); }

/* assume q is square, x~ * q * y using n^2+n mul */
GEN
qfevalb(GEN q, GEN x, GEN y)
{
  pari_sp av = avma;
  long l = lg(q);
  if (lg(x) != l || lg(y) != l) pari_err_DIM("qfevalb");
  return gc_upto(av, RgV_dotproduct(RgV_RgM_mul(x,q), y));
}

/* obsolete, use qfeval0 */
GEN
qfbil(GEN x, GEN y, GEN q)
{
  if (!is_vec_t(typ(x))) pari_err_TYPE("qfbil",x);
  if (!is_vec_t(typ(y))) pari_err_TYPE("qfbil",y);
  if (!q) {
    if (lg(x) != lg(y)) pari_err_DIM("qfbil");
    return RgV_dotproduct(x,y);
  }
  if (typ(q) != t_MAT) pari_err_TYPE("qfbil",q);
  return qfevalb(q,x,y);
}
GEN
qfeval0(GEN q, GEN x, GEN y)
{
  if (!y) return qfnorm0(q, x);
  if (!is_vec_t(typ(x))) pari_err_TYPE("qfeval",x);
  if (!is_vec_t(typ(y))) pari_err_TYPE("qfeval",y);
  if (!q) {
    if (lg(x) != lg(y)) pari_err_DIM("qfeval");
    return RgV_dotproduct(x,y);
  }
  switch(typ(q))
  {
    case t_MAT: break;
    case t_QFB:
      if (lg(x) == 3 && lg(y) == 3) return qfbevalb(q,x,y);
    default: pari_err_TYPE("qfeval",q);
  }
  return qfevalb(q,x,y);
}

/* q a hermitian complex matrix, x a RgV */
GEN
hqfeval(GEN q, GEN x)
{
  pari_sp av = avma;
  long i, j, l = lg(q);
  GEN z, xc;

  if (lg(x) != l) pari_err_DIM("hqfeval");
  if (l==1) return gen_0;
  if (lgcols(q) != l) pari_err_DIM("hqfeval");
  if (l == 2) return gc_upto(av, gmul(gcoeff(q,1,1), gnorm(gel(x,1))));
  /* l = lg(x) = lg(q) > 2 */
  xc = conj_i(x);
  z = mulreal(gcoeff(q,2,1), gmul(gel(x,2),gel(xc,1)));
  for (i=3;i<l;i++)
    for (j=1;j<i;j++)
      z = gadd(z, mulreal(gcoeff(q,i,j), gmul(gel(x,i),gel(xc,j))));
  z = gshift(z,1);
  for (i=1;i<l;i++) z = gadd(z, gmul(gcoeff(q,i,i), gnorm(gel(x,i))));
  return gc_upto(av,z);
}

static void
init_qf_apply(GEN q, GEN M, long *l)
{
  long k = lg(M);
  *l = lg(q);
  if (*l == 1) { if (k == 1) return; }
  else         { if (k != 1 && lgcols(M) == *l) return; }
  pari_err_DIM("qf_RgM_apply");
}
/* Return X = M'.q.M, assuming q is a symmetric matrix and M is a
 * matrix of compatible dimensions. X_ij are X_ji identical, not copies */
GEN
qf_RgM_apply(GEN q, GEN M)
{
  pari_sp av = avma;
  long l; init_qf_apply(q, M, &l); if (l == 1) return cgetg(1, t_MAT);
  return gc_upto(av, RgM_transmultosym(M, RgM_mul(q, M)));
}
GEN
qf_ZM_apply(GEN q, GEN M)
{
  pari_sp av = avma;
  long l; init_qf_apply(q, M, &l); if (l == 1) return cgetg(1, t_MAT);
  /* FIXME: ZM_transmultosym is asymptotically slow, so choose some random
   * threshold defaulting to default implementation: this is suboptimal but
   * has the right complexity in the dimension. Should implement M'*q*M as an
   * atomic operation with the right complexity, see ZM_mul_i. */
  if (l > 20)
    M = ZM_mul(shallowtrans(M), ZM_mul(q, M));
  else
    M = ZM_transmultosym(M, ZM_mul(q, M));
  return gc_upto(av, M);
}

GEN
poleval(GEN x, GEN y)
{
  long i, j, imin, M = 1, tx = typ(x);
  pari_sp av0 = avma, av;
  GEN t, t2, r, s;

  if (is_scalar_t(tx)) return gcopy(x);
  switch(tx)
  {
    case t_POL:
      if (typ(y) == t_POL && varn(x) == varn(y))
      {
        y = RgX_deflate_max(y, &M);
        if (degpol(y) == 1)
        {
          GEN a = gel(y,3), b = gel(y,2); /* y = a t + b */
          if (isint1(a))
          {
            y = RgX_Rg_translate(x, b);
            if (M == 1) return y;
          }
          else
            y = RgX_affine(x, a, b);
          if (M != 1) y = RgX_inflate(y, M);
          return gc_GEN(av0, y);
        }
      }

      i = lg(x)-1; imin = 2; break;

    case t_RFRAC:
      return gc_upto(av0, gdiv(poleval(gel(x,1),y),
                                    poleval(gel(x,2),y)));

    case t_VEC: case t_COL:
      i = lg(x)-1; imin = 1; break;
    default: pari_err_TYPE("poleval",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (i<=imin) return (i==imin)? gmul(gel(x,imin),Rg_get_1(y)): Rg_get_0(y);
  if (isintzero(y)) return gcopy(gel(x,imin));

  t = gel(x,i); i--;
  if (typ(y)!=t_COMPLEX)
  {
#if 0 /* standard Horner's rule */
    for ( ; i>=imin; i--)
      t = gadd(gmul(t,y),gel(x,i));
#endif
    /* specific attention to sparse polynomials */
    av = avma;
    for ( ; i>=imin; i=j-1)
    {
      for (j=i; isexactzero(gel(x,j)); j--)
        if (j==imin)
        {
          if (i!=j) y = gpowgs(y, i-j+1);
          y = gmul(t, y);
          if (M == 1) return gc_upto(av0, y);
          return gc_GEN(av0, RgX_inflate(y, M));
        }
      r = (i==j)? y: gpowgs(y, i-j+1);
      t = gadd(gmul(t,r), gel(x,j));
      if (gc_needed(av0,2))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"poleval: i = %ld",i);
        t = gc_upto(av, t);
      }
    }
    if (M == 1) return gc_upto(av0, t);
    return gc_GEN(av0, RgX_inflate(t, M));
  }

  t2 = gel(x,i); i--; r = gtrace(y); s = gneg_i(gnorm(y));
  av = avma;
  for ( ; i>=imin; i--)
  {
    GEN p = gadd(t2, gmul(r, t));
    t2 = gadd(gel(x,i), gmul(s, t)); t = p;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"poleval: i = %ld",i);
      (void)gc_all(av, 2, &t, &t2);
    }
  }
  return gc_upto(av0, gadd(t2, gmul(y, t)));
}

/* Evaluate a polynomial using Horner. Unstable!
 * If ui != NULL, ui = 1/u, evaluate P(1/u)*u^(deg P): useful for |u|>1 */
GEN
RgX_cxeval(GEN T, GEN u, GEN ui)
{
  pari_sp ltop = avma;
  GEN S;
  long n, lim = lg(T)-1;
  if (lim == 1) return gen_0;
  if (lim == 2) return gcopy(gel(T,2));
  if (!ui)
  {
    n = lim; S = gel(T,n);
    for (n--; n >= 2; n--) S = gadd(gmul(u,S), gel(T,n));
  }
  else
  {
    n = 2; S = gel(T,2);
    for (n++; n <= lim; n++) S = gadd(gmul(ui,S), gel(T,n));
    S = gmul(gpowgs(u, lim-2), S);
  }
  return gc_upto(ltop, S);
}

GEN
RgXY_cxevalx(GEN x, GEN u, GEN ui)
{
  pari_APPLY_pol(typ(gel(x,i))==t_POL? RgX_cxeval(gel(x,i), u, ui): gel(x,i));
}
