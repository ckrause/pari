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

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (second part)                             **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_pol

/* compute Newton sums S_1(P), ... , S_n(P). S_k(P) = sum a_j^k, a_j root of P
 * If N != NULL, assume p-adic roots and compute mod N [assume integer coeffs]
 * If T != NULL, compute mod (T,N) [assume integer coeffs if N != NULL]
 * If y0!= NULL, precomputed i-th powers, i=1..m, m = length(y0).
 * Not memory clean in the latter case */
GEN
polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N)
{
  long dP = degpol(P), i, k, m;
  GEN y, P_lead;

  if (n<0) pari_err_IMPL("polsym of a negative n");
  if (typ(P) != t_POL) pari_err_TYPE("polsym",P);
  if (!signe(P)) pari_err_ROOTS0("polsym");
  y = cgetg(n+2,t_COL);
  if (y0)
  {
    if (typ(y0) != t_COL) pari_err_TYPE("polsym_gen",y0);
    m = lg(y0)-1;
    for (i=1; i<=m; i++) gel(y,i) = gel(y0,i); /* not memory clean */
  }
  else
  {
    m = 1;
    gel(y,1) = stoi(dP);
  }
  P += 2; /* strip codewords */

  P_lead = gel(P,dP); if (gequal1(P_lead)) P_lead = NULL;
  if (P_lead)
  {
    if (N) P_lead = Fq_inv(P_lead,T,N);
    else if (T) P_lead = QXQ_inv(P_lead,T);
  }
  for (k=m; k<=n; k++)
  {
    pari_sp av1 = avma;
    GEN s = (dP>=k)? gmulsg(k,gel(P,dP-k)): gen_0;
    for (i=1; i<k && i<=dP; i++)
      s = gadd(s, gmul(gel(y,k-i+1),gel(P,dP-i)));
    if (N)
    {
      s = Fq_red(s, T, N);
      if (P_lead) s = Fq_mul(s, P_lead, T, N);
    }
    else if (T)
    {
      s = grem(s, T);
      if (P_lead) s = grem(gmul(s, P_lead), T);
    }
    else
      if (P_lead) s = gdiv(s, P_lead);
    gel(y,k+1) = gc_upto(av1, gneg(s));
  }
  return y;
}

GEN
polsym(GEN x, long n)
{
  return polsym_gen(x, NULL, n, NULL,NULL);
}

/* centered residue x mod p. po2 = shifti(p, -1) or NULL (euclidean residue) */
GEN
centermodii(GEN x, GEN p, GEN po2)
{
  GEN y = remii(x, p);
  switch(signe(y))
  {
    case 0: break;
    case 1: if (po2 && abscmpii(y,po2) > 0) y = subii(y, p);
      break;
    case -1: if (!po2 || abscmpii(y,po2) > 0) y = addii(y, p);
      break;
  }
  return y;
}

static long
s_centermod(long x, ulong pp, ulong pps2)
{
  long y = x % (long)pp;
  if (y < 0) y += pp;
  return Fl_center(y, pp,pps2);
}

/* for internal use */
GEN
centermod_i(GEN x, GEN p, GEN ps2)
{
  long i, lx;
  pari_sp av;
  GEN y;

  if (!ps2) ps2 = shifti(p,-1);
  switch(typ(x))
  {
    case t_INT: return centermodii(x,p,ps2);

    case t_POL: lx = lg(x);
      y = cgetg(lx,t_POL); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        av = avma;
        gel(y,i) = gc_INT(av, centermodii(gel(x,i),p,ps2));
      }
      return normalizepol_lg(y, lx);

    case t_COL: pari_APPLY_same(centermodii(gel(x,i),p,ps2));
    case t_MAT: pari_APPLY_same(centermod_i(gel(x,i),p,ps2));

    case t_VECSMALL: lx = lg(x);
    {
      ulong pp = itou(p), pps2 = itou(ps2);
      pari_APPLY_long(s_centermod(x[i], pp, pps2));
    }
  }
  return x;
}

GEN
centermod(GEN x, GEN p) { return centermod_i(x,p,NULL); }

static GEN
RgX_Frobenius_deflate(GEN S, ulong p)
{
  if (degpol(S)%p)
    return NULL;
  else
  {
    GEN F = RgX_deflate(S, p);
    long i, l = lg(F);
    for (i=2; i<l; i++)
    {
      GEN Fi = gel(F,i), R;
      if (typ(Fi)==t_POL)
      {
        if (signe(RgX_deriv(Fi))==0)
          gel(F,i) = RgX_Frobenius_deflate(gel(F, i), p);
        else return NULL;
      }
      else if (ispower(Fi, utoi(p), &R))
        gel(F,i) = R;
      else return NULL;
    }
    return F;
  }
}

static GEN
RgXY_squff(GEN f)
{
  long i, q, n = degpol(f);
  ulong p = itos_or_0(characteristic(f));
  GEN u = const_vec(n+1, pol_1(varn(f)));
  for(q = 1;;q *= p)
  {
    GEN t, v, tv, r = RgX_gcd(f, RgX_deriv(f));
    if (degpol(r) == 0) { gel(u, q) = f; break; }
    t = RgX_div(f, r);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = RgX_gcd(r, t);
        tv = RgX_div(t, v);
        if (degpol(tv) > 0) gel(u, j*q) = tv;
        if (degpol(v) <= 0) break;
        r = RgX_div(r, v);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    if (!p) break;
    f = RgX_Frobenius_deflate(r, p);
    if (!f) { gel(u, q) = r; break; }
  }
  for (i = n; i; i--)
    if (degpol(gel(u,i))) break;
  setlg(u,i+1); return u;
}

/* Lmod contains modular factors of *F (NULL codes an empty slot: used factor)
 * Lfac accumulates irreducible factors as they are found.
 * p is a product of modular factors in Lmod[1..i-1] (NULL for p = 1), not
 * a rational factor of *F
 * Find an irreducible factor of *F divisible by p (by including
 * exhaustively further factors from Lmod[i..]); return 0 on failure, else 1.
 * Update Lmod, Lfac and *F */
static int
RgX_cmbf(GEN p, long i, GEN BLOC, GEN Lmod, GEN Lfac, GEN *F)
{
  pari_sp av;
  GEN q;
  if (i == lg(Lmod)) return 0;
  if (RgX_cmbf(p, i+1, BLOC, Lmod, Lfac, F) && p) return 1;
  if (!gel(Lmod,i)) return 0;
  p = p? RgX_mul(p, gel(Lmod,i)): gel(Lmod,i);
  av = avma;
  q = RgV_to_RgX(RgX_digits(p, BLOC), varn(*F));
  if (degpol(q))
  {
    GEN R, Q = RgX_divrem(*F, q, &R);
    if (signe(R)==0) { vectrunc_append(Lfac, q); *F = Q; return 1; }
  }
  set_avma(av);
  if (RgX_cmbf(p, i+1, BLOC, Lmod, Lfac, F)) { gel(Lmod,i) = NULL; return 1; }
  return 0;
}

static GEN factor_domain(GEN x, GEN flag);

static GEN
ok_bloc(GEN f, GEN BLOC, ulong c)
{
  GEN F = poleval(f, BLOC);
  return issquarefree(c ? gmul(F,mkintmodu(1,c)): F)? F: NULL;
}
static GEN
random_FpX_monic(long n, long v, GEN p)
{
  long i, d = n + 2;
  GEN y = cgetg(d + 1, t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i = 2; i < d; i++) gel(y,i) = randomi(p);
  gel(y,i) = gen_1; return y;
}
static GEN
RgXY_factor_squarefree(GEN f, GEN dom)
{
  pari_sp av = avma;
  ulong i, c = itou_or_0(residual_characteristic(f));
  long vy = gvar2(f), val = RgX_valrem(f, &f), n = RgXY_degreex(f);
  GEN y, Lmod, F = NULL, BLOC = NULL, Lfac = coltrunc_init(degpol(f)+2);
  GEN gc = c? utoipos(c): NULL;
  if (val)
  {
    GEN x = pol_x(varn(f));
    if (dom)
    {
      GEN one = Rg_get_1(dom);
      if (typ(one) != t_INT) x = RgX_Rg_mul(x, one);
    }
    vectrunc_append(Lfac, x); if (!degpol(f)) return Lfac;
  }
  y = pol_x(vy);
  for(;;)
  {
    for (i = 0; !c || i < c; i++)
    {
      BLOC = gpowgs(gaddgs(y, i), n+1);
      if ((F = ok_bloc(f, BLOC, c))) break;
      if (c)
      {
        BLOC = random_FpX_monic(n, vy, gc);
        if ((F = ok_bloc(f, BLOC, c))) break;
      }
    }
    if (!c || i < c) break;
    n++;
  }
  if (DEBUGLEVEL >= 2)
    err_printf("bifactor: bloc:(x+%ld)^%ld, deg f=%ld\n",i,n,RgXY_degreex(f));
  Lmod = gel(factor_domain(F,dom),1);
  if (DEBUGLEVEL >= 2)
    err_printf("bifactor: %ld local factors\n",lg(Lmod)-1);
  (void)RgX_cmbf(NULL, 1, BLOC, Lmod, Lfac, &f);
  if (degpol(f)) vectrunc_append(Lfac, f);
  return gc_GEN(av, Lfac);
}

static GEN
FE_matconcat(GEN F, GEN E, long l)
{
  setlg(E,l); E = shallowconcat1(E);
  setlg(F,l); F = shallowconcat1(F); return mkmat2(F,E);
}

static int
gen_cmp_RgXY(void *data, GEN x, GEN y)
{
  long vx = varn(x), vy = varn(y);
  return (vx == vy)? gen_cmp_RgX(data, x, y): -varncmp(vx, vy);
}
static GEN
RgXY_factor(GEN f, GEN dom)
{
  pari_sp av = avma;
  GEN C, F, E, cf, V;
  long i, j, l;
  if (dom) { GEN c = Rg_get_1(dom); if (typ(c) != t_INT) f = RgX_Rg_mul(f,c); }
  cf = content(f);
  V = RgXY_squff(gdiv(f, cf)); l = lg(V);
  C = factor_domain(cf, dom);
  F = cgetg(l+1, t_VEC); gel(F,1) = gel(C,1);
  E = cgetg(l+1, t_VEC); gel(E,1) = gel(C,2);
  for (i=1, j=2; i < l; i++)
  {
    GEN v = gel(V,i);
    if (degpol(v))
    {
      gel(F,j) = v = RgXY_factor_squarefree(v, dom);
      gel(E,j) = const_col(lg(v)-1, utoipos(i));
      j++;
    }
  }
  f = FE_matconcat(F,E,j);
  (void)sort_factor(f,(void*)cmp_universal, &gen_cmp_RgXY);
  return gc_GEN(av, f);
}

/***********************************************************************/
/**                                                                   **/
/**                          FACTORIZATION                            **/
/**                                                                   **/
/***********************************************************************/
static long RgX_settype(GEN x, long *t, GEN *p, GEN *pol, long *pa, GEN *ff, long *t2, long *var);
#define assign_or_fail(x,y) { GEN __x = x;\
  if (!*y) *y=__x; else if (!gequal(__x,*y)) return 0;\
}
#define update_prec(x,y) { long __x = x; if (__x < *y) *y=__x; }

static const long RgX_type_shift = 6;
void
RgX_type_decode(long x, long *t1, long *t2)
{
  *t1 = x >> RgX_type_shift;
  *t2 = (x & ((1L<<RgX_type_shift)-1));
}
int
RgX_type_is_composite(long t) { return t >= RgX_type_shift; }

static int
settype(GEN c, long *t, GEN *p, GEN *pol, long *pa, GEN *ff, long *t2, long *var)
{
  long j;
  switch(typ(c))
  {
    case t_INT:
      break;
    case t_FRAC:
      t[1]=1; break;
      break;
    case t_REAL:
      update_prec(precision(c), pa);
      t[2]=1; break;
    case t_INTMOD:
      assign_or_fail(gel(c,1),p);
      t[3]=1; break;
    case t_FFELT:
      if (!*ff) *ff=c; else if (!FF_samefield(c,*ff)) return 0;
      assign_or_fail(FF_p_i(c),p);
      t[5]=1; break;
    case t_COMPLEX:
      for (j=1; j<=2; j++)
      {
        GEN d = gel(c,j);
        switch(typ(d))
        {
          case t_INT: case t_FRAC:
            if (!*t2) *t2 = t_COMPLEX;
            t[1]=1; break;
          case t_REAL:
            update_prec(precision(d), pa);
            if (!*t2) *t2 = t_COMPLEX;
            t[2]=1; break;
          case t_INTMOD:
            assign_or_fail(gel(d,1),p);
            if (!signe(*p) || mod4(*p) != 3) return 0;
            if (!*t2) *t2 = t_COMPLEX;
            t[3]=1; break;
          case t_PADIC:
            update_prec(precp(d)+valp(d), pa);
            assign_or_fail(padic_p(d), p);
            if (!*t2) *t2 = t_COMPLEX;
            t[7]=1; break;
          default: return 0;
        }
      }
      if (!t[2]) assign_or_fail(mkpoln(3, gen_1,gen_0,gen_1), pol); /*x^2+1*/
      break;
    case t_PADIC:
      update_prec(precp(c)+valp(c), pa);
      assign_or_fail(padic_p(c), p);
      t[7]=1; break;
    case t_QUAD:
      assign_or_fail(gel(c,1),pol);
      for (j=2; j<=3; j++)
      {
        GEN d = gel(c,j);
        switch(typ(d))
        {
          case t_INT: case t_FRAC:
            t[8]=1; break;
          case t_INTMOD:
            assign_or_fail(gel(d,1),p);
            if (*t2 != t_POLMOD) *t2 = t_QUAD;
            t[3]=1; break;
          case t_PADIC:
            update_prec(precp(d)+valp(d), pa);
            assign_or_fail(padic_p(d), p);
            if (*t2 != t_POLMOD) *t2 = t_QUAD;
            t[7]=1; break;
          default: return 0;
        }
      }
      break;
    case t_POLMOD:
      assign_or_fail(gel(c,1),pol);
      if (typ(gel(c,2))==t_POL && varn(gel(c,2))!=varn(gel(c,1))) return 0;
      for (j=1; j<=2; j++)
      {
        GEN pbis, polbis;
        long pabis;
        *t2 = t_POLMOD;
        switch(Rg_type(gel(c,j),&pbis,&polbis,&pabis))
        {
          case t_INT: break;
          case t_FRAC:   t[1]=1; break;
          case t_INTMOD: t[3]=1; break;
          case t_PADIC:  t[7]=1; update_prec(pabis,pa); break;
          default: return 0;
        }
        if (pbis) assign_or_fail(pbis,p);
        if (polbis) assign_or_fail(polbis,pol);
      }
      break;
    case t_RFRAC: t[11] = 1;
      if (!settype(gel(c,1),t,p,pol,pa,ff,t2,var)) return 0;
      c = gel(c,2); /* fall through */
    case t_POL: t[10] = 1;
      if (!RgX_settype(c,t,p,pol,pa,ff,t2,var)) return 0;
      if (*var == NO_VARIABLE) { *var = varn(c); break; }
      /* if more than one free var, ensure varn() == *var fails. FIXME: should
       * keep the list of all variables, later t_POLMOD may cancel them */
      if (*var != varn(c)) *var = MAXVARN+1;
      break;
    default: return 0;
  }
  return 1;
}
/* t[0] unused. Other values, if set, indicate a coefficient of type
 * t[1] : t_FRAC
 * t[2] : t_REAL
 * t[3] : t_INTMOD
 * t[4] : Unused
 * t[5] : t_FFELT
 * t[6] : Unused
 * t[7] : t_PADIC
 * t[8] : t_QUAD of rationals (t_INT/t_FRAC)
 * t[9]:  Unused
 * t[10]: t_POL (multivariate polynomials)
 * t[11]: t_RFRAC (recursive factorisation)  */
/* if t2 != 0: t_POLMOD/t_QUAD/t_COMPLEX of modular (t_INTMOD/t_PADIC,
 * given by t) */

static long
choosesubtype(long *t, long t2)
{
  if (t2 || t[11]) return 0;
  if (t[2] && (t[3]||t[7]||t[5])) return 0;
  if (t[8]) return t_QUAD;
  if (t[7]) return t_PADIC;
  if (t[5]) return t_FFELT;
  if (t[3]) return t_INTMOD;
  if (t[2]) return t_REAL;
  if (t[1]) return t_FRAC;
  return t_INT;
}

static long
choosetype(long *t, long t2, GEN ff, GEN *pol, long var)
{
  if (t[10] && (!*pol || var!=varn(*pol)))
  {
    long ts = choosesubtype(t, t2);
    if (ts==t_FFELT) *pol=ff;
    return ts == 0 ? t_POL: RgX_type_code(t_POL,ts);
  }
  if (t2) /* polmod/quad/complex of intmod/padic */
  {
    if (t[2] && (t[3]||t[7])) return 0;
    if (t[3]) return RgX_type_code(t2,t_INTMOD);
    if (t[7]) return RgX_type_code(t2,t_PADIC);
    if (t[2]) return t_COMPLEX;
    if (t[1]) return RgX_type_code(t2,t_FRAC);
    return RgX_type_code(t2,t_INT);
  }
  if (t[5]) /* ffelt */
  {
    if (t[2]||t[8]||t[9]) return 0;
    *pol=ff; return t_FFELT;
  }
  if (t[2]) /* inexact, real */
  {
    if (t[3]||t[7]||t[9]) return 0;
    return t_REAL;
  }
  if (t[10])
  {
    long ts = choosesubtype(t, t2);
    if (ts==t_FFELT) *pol=ff;
    return ts == 0 ? t_POL: RgX_type_code(t_POL,ts);
  }
  if (t[8]) return RgX_type_code(t_QUAD,t_INT);
  if (t[3]) return t_INTMOD;
  if (t[7]) return t_PADIC;
  if (t[1]) return t_FRAC;
  return t_INT;
}

static long
RgX_settype(GEN x, long *t, GEN *p, GEN *pol, long *pa, GEN *ff, long *t2, long *var)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
    if (!settype(gel(x,i),t,p,pol,pa,ff,t2,var)) return 0;
  return 1;
}

static long
RgC_settype(GEN x, long *t, GEN *p, GEN *pol, long *pa, GEN *ff, long *t2, long *var)
{
  long i, l = lg(x);
  for (i = 1; i<l; i++)
    if (!settype(gel(x,i),t,p,pol,pa,ff,t2,var)) return 0;
  return 1;
}

static long
RgM_settype(GEN x, long *t, GEN *p, GEN *pol, long *pa, GEN *ff, long *t2, long *var)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++)
    if (!RgC_settype(gel(x,i),t,p,pol,pa,ff,t2,var)) return 0;
  return 1;
}

long
Rg_type(GEN x, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_FFELT:
    case t_COMPLEX: case t_PADIC: case t_QUAD:
      if (!settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
      break;
    case t_POL: case t_SER:
      if (!RgX_settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
      break;
    case t_VEC: case t_COL:
      if(!RgC_settype(x, t, p, pol, pa, &ff, &t2, &var)) return 0;
      break;
    case t_MAT:
      if(!RgM_settype(x, t, p, pol, pa, &ff, &t2, &var)) return 0;
      break;
    default: return 0;
  }
  return choosetype(t,t2,ff,pol,var);
}

long
RgX_type(GEN x, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgX_settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgX_Rg_type(GEN x, GEN y, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgX_settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
  if (!settype(y,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgX_type2(GEN x, GEN y, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgX_settype(x,t,p,pol,pa,&ff,&t2,&var) ||
      !RgX_settype(y,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgX_type3(GEN x, GEN y, GEN z, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgX_settype(x,t,p,pol,pa,&ff,&t2,&var) ||
      !RgX_settype(y,t,p,pol,pa,&ff,&t2,&var) ||
      !RgX_settype(z,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgM_type(GEN x, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgM_settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgV_type(GEN x, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgC_settype(x,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgV_type2(GEN x, GEN y, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgC_settype(x,t,p,pol,pa,&ff,&t2,&var) ||
      !RgC_settype(y,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgM_RgC_type(GEN x, GEN y, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgM_settype(x,t,p,pol,pa,&ff,&t2,&var) ||
      !RgC_settype(y,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

long
RgM_type2(GEN x, GEN y, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0,0,0,0};
  long t2 = 0, var = NO_VARIABLE;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (!RgM_settype(x,t,p,pol,pa,&ff,&t2,&var) ||
      !RgM_settype(y,t,p,pol,pa,&ff,&t2,&var)) return 0;
  return choosetype(t,t2,ff,pol,var);
}

GEN
factor0(GEN x, GEN flag)
{
  ulong B;
  long tx = typ(x);
  if (!flag) return factor(x);
  if ((tx != t_INT && tx!=t_FRAC) || typ(flag) != t_INT)
    return factor_domain(x, flag);
  if (signe(flag) < 0) pari_err_FLAG("factor");
  switch(lgefint(flag))
  {
    case 2: B = 0; break;
    case 3: B = flag[2]; break;
    default: pari_err_OVERFLOW("factor [large prime bound]");
             return NULL; /*LCOV_EXCL_LINE*/
  }
  return boundfact(x, B);
}

GEN
deg1_from_roots(GEN L, long v)
{
  long i, l = lg(L);
  GEN z = cgetg(l,t_COL);
  for (i=1; i<l; i++)
    gel(z,i) = deg1pol_shallow(gen_1, gneg(gel(L,i)), v);
  return z;
}
GEN
roots_from_deg1(GEN x)
{
  long i,l = lg(x);
  GEN r = cgetg(l,t_VEC);
  for (i=1; i<l; i++) { GEN P = gel(x,i); gel(r,i) = gneg(gel(P,2)); }
  return r;
}

static GEN
Qi_factor_p(GEN p)
{
  GEN a, b; (void)cornacchia(gen_1, p, &a,&b);
  return mkcomplex(a, b);
}

static GEN
Qi_primpart(GEN x, GEN *c)
{
  GEN a = real_i(x), b = imag_i(x), n = gcdii(a, b);
  *c = n; if (n == gen_1) return x;
  retmkcomplex(diviiexact(a,n), diviiexact(b,n));
}

static GEN
Qi_primpart_try(GEN x, GEN c)
{
  GEN r, y;
  if (typ(x) == t_INT)
  {
    y = dvmdii(x, c, &r); if (r != gen_0) return NULL;
  }
  else
  {
    GEN a = gel(x,1), b = gel(x,2); y = cgetg(3, t_COMPLEX);
    gel(y,1) = dvmdii(a, c, &r); if (r != gen_0) return NULL;
    gel(y,2) = dvmdii(b, c, &r); if (r != gen_0) return NULL;
  }
  return y;
}

static int
Qi_cmp(GEN x, GEN y)
{
  int v;
  if (typ(x) != t_COMPLEX)
    return (typ(y) == t_COMPLEX)? -1: gcmp(x, y);
  if (typ(y) != t_COMPLEX) return 1;
  v = cmpii(gel(x,2), gel(y,2));
  if (v) return v;
  return gcmp(gel(x,1), gel(y,1));
}

/* 0 or canonical representative in Z[i]^* / <i> (impose imag(x) >= 0) */
static GEN
Qi_normal(GEN x)
{
  if (typ(x) != t_COMPLEX) return absi_shallow(x);
  if (signe(gel(x,1)) < 0) x = gneg(x);
  if (signe(gel(x,2)) < 0) x = mulcxI(x);
  return x;
}

static GEN
Qi_factor(GEN x)
{
  pari_sp av = avma;
  GEN a = real_i(x), b = imag_i(x), d = gen_1, n, y, fa, P, E, P2, E2;
  long t1 = typ(a);
  long t2 = typ(b), i, j, l, exp = 0;
  if (t1 == t_FRAC) d = gel(a,2);
  if (t2 == t_FRAC) d = lcmii(d, gel(b,2));
  if (d == gen_1) y = x;
  else
  {
    y = gmul(x, d);
    a = real_i(y); t1 = typ(a);
    b = imag_i(y); t2 = typ(b);
  }
  if (t1 != t_INT || t2 != t_INT) return NULL;
  y = Qi_primpart(y, &n);
  fa = factor(cxnorm(y));
  P = gel(fa,1);
  E = gel(fa,2); l = lg(P);
  P2 = cgetg(l, t_COL);
  E2 = cgetg(l, t_COL);
  for (j = 1, i = l-1; i > 0; i--) /* remove largest factors first */
  { /* either p = 2 (ramified) or those factors split in Q(i) */
    GEN p = gel(P,i), w, w2, t, we, pe;
    long v, e = itos(gel(E,i));
    int is2 = absequaliu(p, 2);
    w = is2? mkcomplex(gen_1,gen_1): Qi_factor_p(p);
    w2 = Qi_normal( conj_i(w) );
    /* w * w2 * I^3 = p, w2 = conj(w) * I */
    pe = powiu(p, e);
    we = gpowgs(w, e);
    t = Qi_primpart_try( gmul(y, conj_i(we)), pe );
    if (t) y = t; /* y /= w^e */
    else {
      /* y /= conj(w)^e, should be y /= w2^e */
      y = Qi_primpart_try( gmul(y, we), pe );
      swap(w, w2); exp -= e; /* += 3*e mod 4 */
    }
    gel(P,i) = w;
    v = Z_pvalrem(n, p, &n);
    if (v) {
      exp -= v; /* += 3*v mod 4 */
      if (is2) v <<= 1; /* 2 = w^2 I^3 */
      else {
        gel(P2,j) = w2;
        gel(E2,j) = utoipos(v); j++;
      }
      gel(E,i) = stoi(e + v);
    }
    v = Z_pvalrem(d, p, &d);
    if (v) {
      exp += v; /* -= 3*v mod 4 */
      if (is2) v <<= 1; /* 2 is ramified */
      else {
        gel(P2,j) = w2;
        gel(E2,j) = utoineg(v); j++;
      }
      gel(E,i) = stoi(e - v);
    }
    exp &= 3;
  }
  if (j > 1) {
    long k = 1;
    GEN P1 = cgetg(l, t_COL);
    GEN E1 = cgetg(l, t_COL);
    /* remove factors with exponent 0 */
    for (i = 1; i < l; i++)
      if (signe(gel(E,i)))
      {
        gel(P1,k) = gel(P,i);
        gel(E1,k) = gel(E,i);
        k++;
      }
    setlg(P1, k); setlg(E1, k);
    setlg(P2, j); setlg(E2, j);
    fa = famat_mul_shallow(mkmat2(P1,E1), mkmat2(P2,E2));
  }
  if (!equali1(n) || !equali1(d))
  {
    GEN Fa = factor(Qdivii(n, d));
    P = gel(Fa,1); l = lg(P);
    E = gel(Fa,2);
    for (i = 1; i < l; i++)
    {
      GEN w, p = gel(P,i);
      long e;
      int is2;
      switch(mod4(p))
      {
        case 3: continue;
        case 2: is2 = 1; break;
        default:is2 = 0; break;
      }
      e = itos(gel(E,i));
      w = is2? mkcomplex(gen_1,gen_1): Qi_factor_p(p);
      gel(P,i) = w;
      if (is2)
        gel(E,i) = stoi(2*e);
      else
      {
        P = vec_append(P, Qi_normal( conj_i(w) ));
        E = vec_append(E, gel(E,i));
      }
      exp -= e; /* += 3*e mod 4 */
      exp &= 3;
    }
    gel(Fa,1) = P;
    gel(Fa,2) = E;
    fa = famat_mul_shallow(fa, Fa);
  }
  fa = sort_factor(fa, (void*)&Qi_cmp, &cmp_nodata);

  y = gmul(y, powIs(exp));
  if (!gequal1(y)) {
    gel(fa,1) = vec_prepend(gel(fa,1), y);
    gel(fa,2) = vec_prepend(gel(fa,2), gen_1);
  }
  return gc_GEN(av, fa);
}

GEN
Q_factor_limit(GEN x, ulong lim)
{
  pari_sp av = avma;
  GEN a, b;
  if (typ(x) == t_INT) return Z_factor_limit(x, lim);
  a = Z_factor_limit(gel(x,1), lim);
  b = Z_factor_limit(gel(x,2), lim); gel(b,2) = ZC_neg(gel(b,2));
  return gc_GEN(av, ZM_merge_factor(a,b));
}
GEN
Q_factor(GEN x)
{
  pari_sp av = avma;
  GEN a, b;
  if (typ(x) == t_INT) return Z_factor(x);
  a = Z_factor(gel(x,1));
  b = Z_factor(gel(x,2)); gel(b,2) = ZC_neg(gel(b,2));
  return gc_GEN(av, ZM_merge_factor(a,b));
}

/* replace quadratic number over Fp or Q by t_POL in v */
static GEN
quadratic_to_RgX(GEN z, long v)
{
  GEN a, b;
  switch(typ(z))
  {
    case t_INT: case t_FRAC: case t_INTMOD: return z;
    case t_COMPLEX: a = gel(z,2); b = gel(z,1); break;
    case t_QUAD: a = gel(z,3); b = gel(z,2); break;
    default: pari_err_IMPL("factor for general polynomials"); /* paranoia */
             return NULL; /* LCOV_EXCL_LINE */
  }
  return deg1pol_shallow(a, b, v);
}
/* replace t_QUAD/t_COMPLEX [of rationals] coeffs by t_POL in v */
static GEN
RgX_fix_quadratic(GEN x, long v)
{ pari_APPLY_pol_normalized(quadratic_to_RgX(gel(x,i), v)); }
static GEN
RgXQ_factor_i(GEN x, GEN T, GEN p, long t1, long t2, long *pv)
{
  *pv = -1;
  if (t2 == t_PADIC) return NULL;
  if (t2 == t_INTMOD)
  {
    T = RgX_to_FpX(T,p);
    if (!FpX_is_irred(T,p)) return NULL;
  }
  if (t1 != t_POLMOD)
  { /* replace w in x by t_POL */
    if (t2 != t_INTMOD) T = leafcopy(T);
    *pv = fetch_var(); setvarn(T, *pv);
    x = RgX_fix_quadratic(x, *pv);
  }
  if (t2 == t_INTMOD) return factmod(x, mkvec2(p,T));
  return nffactor(T, x);
}
static GEN
RgXQ_factor(GEN x, GEN T, GEN p, long tx)
{
  pari_sp av = avma;
  long t1, t2, v;
  GEN w, y;
  RgX_type_decode(tx, &t1, &t2);
  y = RgXQ_factor_i(x, T, p, t1, t2, &v);
  if (!y) pari_err_IMPL("factor for general polynomials");
  if (v < 0) return gc_upto(av, y);
  /* substitute back w */
  w = (t1 == t_COMPLEX)? gen_I(): mkquad(T,gen_0,gen_1);
  gel(y,1) = gsubst(liftpol_shallow(gel(y,1)), v, w);
  (void)delete_var(); return gc_GEN(av, y);
}

static GEN
RX_factor(GEN x, long prec)
{
  GEN y = cgetg(3,t_MAT), R, P;
  pari_sp av = avma;
  long v = varn(x), i, l, r1;

  R = cleanroots(x, prec); l = lg(R);
  for (r1 = 1; r1 < l; r1++)
    if (typ(gel(R,r1)) == t_COMPLEX) break;
  l = (r1+l)>>1; P = cgetg(l,t_COL);
  for (i = 1; i < r1; i++)
    gel(P,i) = deg1pol_shallow(gen_1, negr(gel(R,i)), v);
  for (   ; i < l; i++)
  {
    GEN a = gel(R,2*i-r1), t;
    t = gmul2n(gel(a,1), 1); togglesign(t);
    gel(P,i) = deg2pol_shallow(gen_1, t, gnorm(a), v);
  }
  gel(y,1) = gc_upto(av, P);
  gel(y,2) = const_col(l-1, gen_1); return y;
}
static GEN
CX_factor(GEN x, long prec)
{
  GEN y = cgetg(3,t_MAT), R;
  pari_sp av = avma;
  long v = varn(x);

  R = roots(x, prec);
  gel(y,1) = gc_upto(av, deg1_from_roots(R, v));
  gel(y,2) = const_col(degpol(x), gen_1); return y;
}

static GEN
RgX_factor(GEN x, GEN dom)
{
  GEN  p, T;
  long pa, tx = dom ? RgX_Rg_type(x,dom,&p,&T,&pa): RgX_type(x,&p,&T,&pa);
  if (tx>>RgX_type_shift==t_POL) tx = t_POL;
  switch(tx)
  {
    case 0: pari_err_IMPL("factor for general polynomials");
    case t_POL: return RgXY_factor(x, dom);
    case t_INT: return ZX_factor(x);
    case t_FRAC: return QX_factor(x);
    case t_INTMOD: return factmod(x, p);
    case t_PADIC: return factorpadic(x, p, pa);
    case t_FFELT: return FFX_factor(x, T);
    case t_COMPLEX: return CX_factor(x, pa);
    case t_REAL: return RX_factor(x, pa);
  }
  return RgXQ_factor(x, T, p, tx);
}

static GEN
factor_domain(GEN x, GEN dom)
{
  long tx = typ(x), tdom = dom ? typ(dom): 0;
  pari_sp av;

  if (gequal0(x))
    switch(tx)
    {
      case t_INT:
      case t_COMPLEX:
      case t_POL:
      case t_RFRAC: return prime_fact(x);
      default: pari_err_TYPE("factor",x);
    }
  av = avma;
  switch(tx)
  {
    case t_POL: return RgX_factor(x, dom);
    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2);
      GEN y = famat_inv_shallow(RgX_factor(b, dom));
      if (typ(a)==t_POL) y = famat_mul_shallow(RgX_factor(a, dom), y);
      return gc_GEN(av, sort_factor_pol(y, cmp_universal));
    }
    case t_INT:  if (tdom==0 || tdom==t_INT) return Z_factor(x);
    case t_FRAC: if (tdom==0 || tdom==t_INT) return Q_factor(x);
    case t_COMPLEX: /* fall through */
      if (tdom==0 || tdom==t_COMPLEX)
      { GEN y = Qi_factor(x); if (y) return y; }
      /* fall through */
  }
  pari_err_TYPE("factor",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
factor(GEN x) { return factor_domain(x, NULL); }

/*******************************************************************/
/*                                                                 */
/*                     ROOTS --> MONIC POLYNOMIAL                  */
/*                                                                 */
/*******************************************************************/
static GEN
normalized_mul(void *E, GEN x, GEN y)
{
  long a = gel(x,1)[1], b = gel(y,1)[1];
  (void) E;
  return mkvec2(mkvecsmall(a + b),
                RgX_mul_normalized(gel(x,2),a, gel(y,2),b));
}
/* L = [Vecsmall([a]), A], with a > 0, A an RgX, deg(A) < a; return X^a + A */
static GEN
normalized_to_RgX(GEN L)
{
  long i, a = gel(L,1)[1];
  GEN A = gel(L,2);
  GEN z = cgetg(a + 3, t_POL);
  z[1] = evalsigne(1) | evalvarn(varn(A));
  for (i = 2; i < lg(A); i++) gel(z,i) = gcopy(gel(A,i));
  for (     ; i < a+2;   i++) gel(z,i) = gen_0;
  gel(z,i) = gen_1; return z;
}

static GEN
roots_to_pol_FpV(GEN x, long v, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flv_roots_to_pol(RgV_to_Flv(x, pp), pp, v<<VARNSHIFT));
  }
  else
    r = FpV_roots_to_pol(RgV_to_FpV(x, p), p, v);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
roots_to_pol_FqV(GEN x, long v, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("/", x, pol);
  r = FqV_roots_to_pol(RgC_to_FqC(x, T, p), T, p, v);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
roots_to_pol_fast(GEN x, long v)
{
  GEN p, pol;
  long pa;
  long t = RgV_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return roots_to_pol_FpV(x, v, p);
    case t_FFELT:  return FFV_roots_to_pol(x, pol, v);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return roots_to_pol_FqV(x, v, pol, p);
    default:       return NULL;
  }
}

/* compute prod (x - a[i]) */
GEN
roots_to_pol(GEN a, long v)
{
  pari_sp av = avma;
  long i, k, lx = lg(a);
  GEN L;
  if (lx == 1) return pol_1(v);
  L = roots_to_pol_fast(a, v);
  if (L) return L;
  L = cgetg(lx, t_VEC);
  for (k=1,i=1; i<lx-1; i+=2)
  {
    GEN s = gel(a,i), t = gel(a,i+1);
    GEN x0 = gmul(s,t);
    GEN x1 = gneg(gadd(s,t));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  if (i < lx) gel(L,k++) = mkvec2(mkvecsmall(1),
                                  scalarpol_shallow(gneg(gel(a,i)), v));
  setlg(L, k); L = gen_product(L, NULL, normalized_mul);
  return gc_upto(av, normalized_to_RgX(L));
}

/* prod_{i=1..r1} (x - a[i]) prod_{i=1..r2} (x - a[i])(x - conj(a[i]))*/
GEN
roots_to_pol_r1(GEN a, long v, long r1)
{
  pari_sp av = avma;
  long i, k, lx = lg(a);
  GEN L;
  if (lx == 1) return pol_1(v);
  L = cgetg(lx, t_VEC);
  for (k=1,i=1; i<r1; i+=2)
  {
    GEN s = gel(a,i), t = gel(a,i+1);
    GEN x0 = gmul(s,t);
    GEN x1 = gneg(gadd(s,t));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  if (i < r1+1) gel(L,k++) = mkvec2(mkvecsmall(1),
                                    scalarpol_shallow(gneg(gel(a,i)), v));
  for (i=r1+1; i<lx; i++)
  {
    GEN s = gel(a,i);
    GEN x0 = gnorm(s);
    GEN x1 = gneg(gtrace(s));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  setlg(L, k); L = gen_product(L, NULL, normalized_mul);
  return gc_upto(av, normalized_to_RgX(L));
}

GEN
polfromroots(GEN a, long v)
{
  if (!is_vec_t(typ(a)))
    pari_err_TYPE("polfromroots",a);
  if (v < 0) v = 0;
  if (varncmp(gvar(a), v) <= 0) pari_err_PRIORITY("polfromroots",a,"<=",v);
  return roots_to_pol(a, v);
}

/*******************************************************************/
/*                                                                 */
/*                          FACTORBACK                             */
/*                                                                 */
/*******************************************************************/
static GEN
mul(void *a, GEN x, GEN y) { (void)a; return gmul(x,y);}
static GEN
powi(void *a, GEN x, GEN y) { (void)a; return powgi(x,y);}
static GEN
Fpmul(void *a, GEN x, GEN y) { return Fp_mul(x,y,(GEN)a); }
static GEN
Fppow(void *a, GEN x, GEN n) { return Fp_pow(x,n,(GEN)a); }

/* [L,e] = [fa, NULL] or [elts, NULL] or [elts, exponents] */
GEN
gen_factorback(GEN L, GEN e, void *data, GEN (*_mul)(void*,GEN,GEN),
               GEN (*_pow)(void*,GEN,GEN), GEN (*_one)(void*))
{
  pari_sp av = avma;
  long k, l, lx;
  GEN p,x;

  if (e) /* supplied vector of exponents */
    p = L;
  else
  {
    switch(typ(L)) {
      case t_VEC:
      case t_COL: /* product of the L[i] */
        if (lg(L)==1) return _one? _one(data): gen_1;
        return gc_upto(av, gen_product(L, data, _mul));
      case t_MAT: /* genuine factorization */
        l = lg(L);
        if (l == 3) break;
        /*fall through*/
      default:
        pari_err_TYPE("factorback [not a factorization]", L);
    }
    p = gel(L,1);
    e = gel(L,2);
  }
  if (!is_vec_t(typ(p))) pari_err_TYPE("factorback [not a vector]", p);
  /* p = elts, e = expo */
  lx = lg(p);
  /* check whether e is an integral vector of correct length */
  switch(typ(e))
  {
    case t_VECSMALL:
      if (lx != lg(e))
        pari_err_TYPE("factorback [not an exponent vector]", e);
      if (lx == 1) return _one? _one(data): gen_1;
      x = cgetg(lx,t_VEC);
      for (l=1,k=1; k<lx; k++)
        if (e[k]) gel(x,l++) = _pow(data, gel(p,k), stoi(e[k]));
      break;
    case t_VEC: case t_COL:
      if (lx != lg(e) || !RgV_is_ZV(e))
        pari_err_TYPE("factorback [not an exponent vector]", e);
      if (lx == 1) return _one? _one(data): gen_1;
      x = cgetg(lx,t_VEC);
      for (l=1,k=1; k<lx; k++)
        if (signe(gel(e,k))) gel(x,l++) = _pow(data, gel(p,k), gel(e,k));
      break;
    default:
      pari_err_TYPE("factorback [not an exponent vector]", e);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  if (l==1) return gc_upto(av, _one? _one(data): gen_1);
  x[0] = evaltyp(t_VEC) | _evallg(l);
  return gc_upto(av, gen_product(x, data, _mul));
}

GEN
FpV_factorback(GEN L, GEN e, GEN p)
{ return gen_factorback(L, e, (void*)p, &Fpmul, &Fppow, NULL); }

ulong
Flv_factorback(GEN L, GEN e, ulong p)
{
  long i, l = lg(e);
  ulong r = 1UL, ri = 1UL;
  for (i = 1; i < l; i++)
  {
    long c = e[i];
    if (!c) continue;
    if (c < 0)
      ri = Fl_mul(ri, Fl_powu(L[i],-c,p), p);
    else
      r = Fl_mul(r, Fl_powu(L[i],c,p), p);
  }
  if (ri != 1UL) r = Fl_div(r, ri, p);
  return r;
}
GEN
FlxqV_factorback(GEN L, GEN e, GEN Tp, ulong p)
{
  pari_sp av = avma;
  GEN Hi = NULL, H = NULL;
  long i, l = lg(L), v = get_Flx_var(Tp);
  for (i = 1; i < l; i++)
  {
    GEN x, ei = gel(e,i);
    long s = signe(ei);
    if (!s) continue;
    x = Flxq_pow(gel(L,i), s > 0? ei: negi(ei), Tp, p);
    if (s > 0)
      H = H? Flxq_mul(H, x, Tp, p): x;
    else
      Hi = Hi? Flxq_mul(Hi, x, Tp, p): x;
  }
  if (!Hi)
  {
    if (!H) { set_avma(av); return mkvecsmall2(v,1); }
    return gc_leaf(av, H);
  }
  Hi = Flxq_inv(Hi, Tp, p);
  return gc_leaf(av, H? Flxq_mul(H,Hi,Tp,p): Hi);
}
GEN
FqV_factorback(GEN L, GEN e, GEN Tp, GEN p)
{
  pari_sp av = avma;
  GEN Hi = NULL, H = NULL;
  long i, l = lg(L), small = typ(e) == t_VECSMALL;
  for (i = 1; i < l; i++)
  {
    GEN x;
    long s;
    if (small)
    {
      s = e[i]; if (!s) continue;
      x = Fq_powu(gel(L,i), labs(s), Tp, p);
    }
    else
    {
      GEN ei = gel(e,i);
      s = signe(ei); if (!s) continue;
      x = Fq_pow(gel(L,i), s > 0? ei: negi(ei), Tp, p);
    }
    if (s > 0)
      H = H? Fq_mul(H, x, Tp, p): x;
    else
      Hi = Hi? Fq_mul(Hi, x, Tp, p): x;
  }
  if (Hi)
  {
    Hi = Fq_inv(Hi, Tp, p);
    H = H? Fq_mul(H,Hi,Tp,p): Hi;
  }
  else if (!H) return gc_const(av, gen_1);
  return gc_upto(av, H);
}

GEN
factorback2(GEN L, GEN e) { return gen_factorback(L, e, NULL, &mul, &powi, NULL); }
GEN
factorback(GEN fa) { return factorback2(fa, NULL); }

GEN
vecprod(GEN v)
{
  pari_sp av = avma;
  if (!is_vec_t(typ(v)))
    pari_err_TYPE("vecprod", v);
  if (lg(v) == 1) return gen_1;
  return gc_GEN(av, gen_product(v, NULL, mul));
}

static int
RgX_is_irred_i(GEN x)
{
  GEN y, p, pol;
  long l = lg(x), pa;

  if (!signe(x) || l <= 3) return 0;
  switch(RgX_type(x,&p,&pol,&pa))
  {
    case t_INTMOD: return FpX_is_irred(RgX_to_FpX(x,p), p);
    case t_COMPLEX: return l == 4;
    case t_REAL:
      if (l == 4) return 1;
      if (l > 5) return 0;
      return gsigne(RgX_disc(x)) > 0;
  }
  y = RgX_factor(x, NULL);
  return (lg(gcoeff(y,1,1))==l);
}
static int
RgX_is_irred(GEN x)
{ pari_sp av = avma; return gc_bool(av, RgX_is_irred_i(x)); }
long
polisirreducible(GEN x)
{
  long tx = typ(x);
  if (tx == t_POL) return RgX_is_irred(x);
  if (!is_scalar_t(tx)) pari_err_TYPE("polisirreducible",x);
  return 0;
}

/*******************************************************************/
/*                                                                 */
/*                         GENERIC GCD                             */
/*                                                                 */
/*******************************************************************/
static GEN
gcd3(GEN x, GEN y, GEN z) { return ggcd(ggcd(x, y), z); }

/* x is a COMPLEX or a QUAD */
static GEN
triv_cont_gcd(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a, b;
  if (typ(x)==t_COMPLEX)
  {
    a = gel(x,1); b = gel(x,2);
    if (typ(a) == t_REAL || typ(b) == t_REAL) return gen_1;
  }
  else
  {
    a = gel(x,2); b = gel(x,3);
  }
  return gc_upto(av, gcd3(a, b, y));
}

/* y is a PADIC, x a rational number or an INTMOD */
static GEN
padic_gcd(GEN x, GEN y)
{
  GEN p = padic_p(y);
  long v = gvaluation(x,p), w = valp(y);
  if (w < v) v = w;
  return powis(p, v);
}

static void
Zi_mul3(GEN xr, GEN xi, GEN yr, GEN yi, GEN *zr, GEN *zi)
{
  GEN p3 = addii(xr,xi);
  GEN p4 = addii(yr,yi);
  GEN p1 = mulii(xr,yr);
  GEN p2 = mulii(xi,yi);
  p3 = mulii(p3,p4);
  p4 = addii(p2,p1);
  *zr = subii(p1,p2); *zi = subii(p3,p4);
}

static GEN
Zi_rem(GEN x, GEN y)
{
  GEN xr = real_i(x), xi = imag_i(x);
  GEN yr = real_i(y), yi = imag_i(y);
  GEN n = addii(sqri(yr), sqri(yi));
  GEN ur, ui, zr, zi;
  Zi_mul3(xr, xi, yr, negi(yi), &ur, &ui);
  Zi_mul3(yr, yi, diviiround(ur, n), diviiround(ui, n), &zr, &zi);
  return mkcomplex(subii(xr,zr), subii(xi,zi));
}

static GEN
Qi_gcd(GEN x, GEN y)
{
  pari_sp av = avma, btop;
  GEN dx, dy;
  x = Q_remove_denom(x, &dx);
  y = Q_remove_denom(y, &dy);
  btop = avma;
  while (!gequal0(y))
  {
    GEN z = Zi_rem(x,y);
    x = y; y = z;
    if (gc_needed(btop,1)) {
      if(DEBUGMEM>1) pari_warn(warnmem,"Qi_gcd");
      (void)gc_all(btop,2, &x,&y);
    }
  }
  x = Qi_normal(x);
  if (typ(x) == t_COMPLEX)
  {
    if      (gequal0(gel(x,2))) x = gel(x,1);
    else if (gequal0(gel(x,1))) x = gel(x,2);
  }
  if (!dx && !dy) return gc_GEN(av, x);
  return gc_upto(av, gdiv(x, dx? (dy? lcmii(dx, dy): dx): dy));
}

static int
c_is_rational(GEN x)
{ return is_rational_t(typ(gel(x,1))) && is_rational_t(typ(gel(x,2))); }
static GEN
c_zero_gcd(GEN c)
{
  GEN x = gel(c,1), y = gel(c,2);
  long tx = typ(x), ty = typ(y);
  if (tx == t_REAL || ty == t_REAL) return gen_1;
  if (tx == t_PADIC || tx == t_INTMOD
   || ty == t_PADIC || ty == t_INTMOD) return ggcd(x, y);
  return Qi_gcd(c, gen_0);
}

/* gcd(x, 0) */
static GEN
zero_gcd(GEN x)
{
  pari_sp av;
  switch(typ(x))
  {
    case t_INT: return absi(x);
    case t_FRAC: return absfrac(x);
    case t_COMPLEX: return c_zero_gcd(x);
    case t_REAL: return gen_1;
    case t_PADIC: return powis(padic_p(x), valp(x));
    case t_SER: return pol_xnall(valser(x), varn(x));
    case t_POLMOD: {
      GEN d = gel(x,2);
      if (typ(d) == t_POL && varn(d) == varn(gel(x,1))) return content(d);
      return isinexact(d)? zero_gcd(d): gcopy(d);
    }
    case t_POL:
      if (!isinexact(x)) break;
      av = avma;
      return gc_upto(av, monomialcopy(content(x), RgX_val(x), varn(x)));

    case t_RFRAC:
      if (!isinexact(x)) break;
      av = avma;
      return gc_upto(av, gdiv(zero_gcd(gel(x,1)), gel(x,2)));
  }
  return gcopy(x);
}
/* z is an exact zero, t_INT, t_INTMOD or t_FFELT */
static GEN
zero_gcd2(GEN y, GEN z)
{
  pari_sp av;
  switch(typ(z))
  {
    case t_INT: return zero_gcd(y);
    case t_INTMOD:
      av = avma;
      return gc_upto(av, gmul(y, mkintmod(gen_1,gel(z,1))));
    case t_FFELT:
      av = avma;
      return gc_upto(av, gmul(y, FF_1(z)));
    default:
      pari_err_TYPE("zero_gcd", z);
      return NULL;/*LCOV_EXCL_LINE*/
  }
}
static GEN
cont_gcd_pol_i(GEN x, GEN y) { return scalarpol(ggcd(content(x),y), varn(x));}
/* tx = t_POL, y considered as constant */
static GEN
cont_gcd_pol(GEN x, GEN y)
{ pari_sp av = avma; return gc_upto(av, cont_gcd_pol_i(x,y)); }
/* tx = t_RFRAC, y considered as constant */
static GEN
cont_gcd_rfrac(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN cx; x = primitive_part(x, &cx);
  /* e.g. Mod(1,2) / (2*y+1) => primitive_part = Mod(1,2)*y^0 */
  if (typ(x) != t_RFRAC) x = cont_gcd_pol_i(x, y);
  else x = gred_rfrac_simple(ggcd(cx? cx: gen_1, y), gel(x,2));
  return gc_upto(av, x);
}
/* !is_const_t(tx), tx != t_POL,t_RFRAC, y considered as constant */
static GEN
cont_gcd_gen(GEN x, GEN y)
{
  pari_sp av = avma;
  return gc_upto(av, ggcd(content(x),y));
}
/* !is_const(tx), y considered as constant */
static GEN
cont_gcd(GEN x, long tx, GEN y)
{
  switch(tx)
  {
    case t_RFRAC: return cont_gcd_rfrac(x,y);
    case t_POL: return cont_gcd_pol(x,y);
    default: return cont_gcd_gen(x,y);
  }
}
static GEN
gcdiq(GEN x, GEN y)
{
  GEN z;
  if (!signe(x)) return Q_abs(y);
  z = cgetg(3,t_FRAC);
  gel(z,1) = gcdii(x,gel(y,1));
  gel(z,2) = icopy(gel(y,2));
  return z;
}
static GEN
gcdqq(GEN x, GEN y)
{
  GEN z = cgetg(3,t_FRAC);
  gel(z,1) = gcdii(gel(x,1), gel(y,1));
  gel(z,2) = lcmii(gel(x,2), gel(y,2));
  return z;
}
/* assume x,y t_INT or t_FRAC */
GEN
Q_gcd(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == t_INT)
  { return (ty == t_INT)? gcdii(x,y): gcdiq(x,y); }
  else
  { return (ty == t_INT)? gcdiq(y,x): gcdqq(x,y); }
}

/* t_QUADs */
static GEN
qgcd(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN q = gdiv(x,y), u, v;
  /* e.g. x = y with t_PADIC components */
  if (typ(q) != t_QUAD) { set_avma(av); return triv_cont_gcd(x,y); }
  u = gel(q,2); v = gel(q,3);
  if (gequal0(v))
  {
    if (typ(u)==t_INT) { set_avma(av); return gcopy(y); }
    if (typ(u)==t_FRAC) return gc_upto(av, gdiv(y, gel(u,2)));
    set_avma(av); return triv_cont_gcd(x,y);
  }
  if (typ(u)==t_INT && typ(v)==t_INT) { set_avma(av); return gcopy(y); }
  q = ginv(q); u = gel(q,2); v = gel(q,3); set_avma(av);
  if (typ(u)==t_INT && typ(v)==t_INT) return gcopy(x);
  return triv_cont_gcd(y,x);
}

GEN
ggcd(GEN x, GEN y)
{
  long vx, vy, tx = typ(x), ty = typ(y);
  pari_sp av;
  GEN p1,z;

  if (is_noncalc_t(tx) || is_matvec_t(tx) ||
      is_noncalc_t(ty) || is_matvec_t(ty)) pari_err_TYPE2("gcd",x,y);
  if (tx>ty) { swap(x,y); lswap(tx,ty); }
  /* tx <= ty */
  z = gisexactzero(x); if (z) return zero_gcd2(y,z);
  z = gisexactzero(y); if (z) return zero_gcd2(x,z);
  if (is_const_t(tx))
  {
    if (ty == tx) switch(tx)
    {
      case t_INT:
        return gcdii(x,y);

      case t_INTMOD: z=cgetg(3,t_INTMOD);
        if (equalii(gel(x,1),gel(y,1)))
          gel(z,1) = icopy(gel(x,1));
        else
          gel(z,1) = gcdii(gel(x,1),gel(y,1));
        if (gequal1(gel(z,1))) gel(z,2) = gen_0;
        else
        {
          av = avma; p1 = gcdii(gel(z,1),gel(x,2));
          if (!equali1(p1))
          {
            p1 = gcdii(p1,gel(y,2));
            if (equalii(p1, gel(z,1))) { cgiv(p1); p1 = gen_0; }
            else p1 = gc_INT(av, p1);
          }
          gel(z,2) = p1;
        }
        return z;

      case t_FRAC:
        return gcdqq(x,y);

      case t_FFELT:
        if (!FF_samefield(x,y)) pari_err_OP("gcd",x,y);
        return FF_equal0(x) && FF_equal0(y)? FF_zero(y): FF_1(y);

      case t_COMPLEX:
        if (c_is_rational(x) && c_is_rational(y)) return Qi_gcd(x,y);
        return triv_cont_gcd(y,x);

      case t_PADIC:
        if (!equalii(padic_p(x), padic_p(y))) return gen_1;
        return powis(padic_p(x), minss(valp(x), valp(y)));

      case t_QUAD: return qgcd(x, y);

      default: return gen_1; /* t_REAL */
    }
    if (is_const_t(ty)) switch(tx)
    {
      case t_INT:
        switch(ty)
        {
          case t_INTMOD: z = cgetg(3,t_INTMOD);
            gel(z,1) = icopy(gel(y,1)); av = avma;
            p1 = gcdii(gel(y,1),gel(y,2));
            if (!equali1(p1)) {
              p1 = gcdii(x,p1);
              if (equalii(p1, gel(z,1))) { cgiv(p1); p1 = gen_0; }
              else
                p1 = gc_INT(av, p1);
            }
            gel(z,2) = p1; return z;

          case t_REAL: return gen_1;

          case t_FRAC:
            return gcdiq(x,y);

          case t_COMPLEX:
            if (c_is_rational(y)) return Qi_gcd(x,y);
            return triv_cont_gcd(y,x);

          case t_FFELT:
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(x, gel(y,4))? FF_zero(y): FF_1(y);

          case t_PADIC:
            return padic_gcd(x,y);

          case t_QUAD:
            return triv_cont_gcd(y,x);
          default:
            pari_err_TYPE2("gcd",x,y);
        }

      case t_REAL:
        switch(ty)
        {
          case t_INTMOD:
          case t_FFELT:
          case t_PADIC: pari_err_TYPE2("gcd",x,y);
          default: return gen_1;
        }

      case t_INTMOD:
        switch(ty)
        {
          case t_FRAC:
            av = avma;
            if (!equali1(gcdii(gel(x,1),gel(y,2)))) pari_err_OP("gcd",x,y);
            set_avma(av); return ggcd(gel(y,1), x);

          case t_FFELT:
          {
            GEN p = gel(y,4);
            if (!dvdii(gel(x,1), p)) pari_err_OP("gcd",x,y);
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(gel(x,2),p)? FF_zero(y): FF_1(y);
          }

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);

          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_FRAC:
        switch(ty)
        {
          case t_COMPLEX:
            if (c_is_rational(y)) return Qi_gcd(x,y);
          case t_QUAD:
            return triv_cont_gcd(y,x);
          case t_FFELT:
          {
            GEN p = gel(y,4);
            if (dvdii(gel(x,2), p)) pari_err_OP("gcd",x,y);
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(gel(x,1),p)? FF_zero(y): FF_1(y);
          }

          case t_PADIC:
            return padic_gcd(x,y);

          default: pari_err_TYPE2("gcd",x,y);
        }
      case t_FFELT:
        switch(ty)
        {
          case t_PADIC:
          {
            GEN p = padic_p(y);
            long v = valp(y);
            if (!equalii(p, gel(x,4)) || v < 0) pari_err_OP("gcd",x,y);
            return (v && FF_equal0(x))? FF_zero(x): FF_1(x);
          }
          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_COMPLEX:
        switch(ty)
        {
          case t_PADIC:
          case t_QUAD: return triv_cont_gcd(x,y);
          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_PADIC:
        switch(ty)
        {
          case t_QUAD: return triv_cont_gcd(y,x);
          default: pari_err_TYPE2("gcd",x,y);
        }

      default: return gen_1; /* tx = t_REAL */
    }
    return cont_gcd(y,ty, x);
  }

  if (tx == t_POLMOD)
  {
    if (ty == t_POLMOD)
    {
      GEN T = gel(x,1), Ty = gel(y,1);
      vx = varn(T); vy = varn(Ty);
      z = cgetg(3,t_POLMOD);
      if (vx == vy)
        T = RgX_equal(T,Ty)? RgX_copy(T): RgX_gcd(T, Ty);
      else
        T = RgX_copy(varncmp(vx,vy) < 0? T: Ty);
      gel(z,1) = T;
      if (degpol(T) <= 0) gel(z,2) = gen_0;
      else
      {
        GEN X = gel(x,2), Y = gel(y,2), d;
        av = avma; d = ggcd(content(X), content(Y));
        if (!gequal1(d)) { X = gdiv(X,d); Y = gdiv(Y,d); }
        gel(z,2) = gc_upto(av, gmul(d, gcd3(T, X, Y)));
      }
      return z;
    }
    vx = varn(gel(x,1));
    switch(ty)
    {
      case t_POL:
        vy = varn(y);
        if (varncmp(vy,vx) < 0) return cont_gcd_pol(y, x);
        z = cgetg(3,t_POLMOD);
        gel(z,1) = RgX_copy(gel(x,1)); av = avma;
        gel(z,2) = gc_upto(av, gcd3(gel(x,1), gel(x,2), y));
        return z;

      case t_RFRAC:
        vy = varn(gel(y,2));
        if (varncmp(vy,vx) < 0) return cont_gcd_rfrac(y, x);
        av = avma;
        if (degpol(ggcd(gel(x,1),gel(y,2)))) pari_err_OP("gcd",x,y);
        set_avma(av); return gdiv(ggcd(gel(y,1),x), content(gel(y,2)));
    }
  }

  vx = gvar(x);
  vy = gvar(y);
  if (varncmp(vy, vx) < 0) return cont_gcd(y,ty, x);
  if (varncmp(vy, vx) > 0) return cont_gcd(x,tx, y);

  /* vx = vy: same main variable */
  switch(tx)
  {
    case t_POL:
      switch(ty)
      {
        GEN cz, cx, cy;
        case t_POL: return RgX_gcd(x,y);
        case t_SER:
          z = ggcd(content(x), content(y));
          return monomialcopy(z, minss(valser(y),gval(x,vx)), vx);
        case t_RFRAC:
          av = avma;
          x = primitive_part(x, &cx);
          y = primitive_part(y, &cy);
          z = gred_rfrac_simple(ggcd(gel(y,1), x), gel(y,2));
          if (cx) cz = cy? ggcd(cx, cy): cx; else cz = cy? cy: NULL;
          if (cz) z = gmul(z, cz);
          return gc_upto(av, z);
      }
      break;

    case t_SER:
      z = ggcd(content(x), content(y));
      switch(ty)
      {
        case t_SER:   return monomialcopy(z, minss(valser(x),valser(y)), vx);
        case t_RFRAC: return monomialcopy(z, minss(valser(x),gval(y,vx)), vx);
      }
      break;

    case t_RFRAC:
    {
      GEN xd = gel(x,2), yd = gel(y,2);
      if (ty != t_RFRAC) pari_err_TYPE2("gcd",x,y);
      z = cgetg(3,t_RFRAC); av = avma;
      gel(z,2) = gc_upto(av, RgX_mul(xd, RgX_div(yd, RgX_gcd(xd, yd))));
      gel(z,1) = ggcd(gel(x,1), gel(y,1)); return z;
    }
  }
  pari_err_TYPE2("gcd",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
ggcd0(GEN x, GEN y) { return y? ggcd(x,y): content(x); }

static GEN
fix_lcm(GEN x)
{
  GEN t;
  switch(typ(x))
  {
    case t_INT:
      x = absi_shallow(x); break;
    case t_POL:
      if (lg(x) <= 2) break;
      t = leading_coeff(x);
      if (typ(t) == t_INT && signe(t) < 0) x = gneg(x);
  }
  return x;
}
GEN
glcm0(GEN x, GEN y)
{
  if (!y) return fix_lcm(gassoc_proto(glcm,x,y));
  return glcm(x,y);
}
GEN
ZV_lcm(GEN x) { return fix_lcm(gassoc_proto(lcmii,x,NULL)); }
GEN
glcm(GEN x, GEN y)
{
  pari_sp av;
  GEN z;
  if (typ(x)==t_INT && typ(y)==t_INT) return lcmii(x,y);
  av = avma; z = ggcd(x,y);
  if (!gequal1(z))
  {
    if (gequal0(z)) { set_avma(av); return gmul(x,y); }
    y = gdiv(y,z);
  }
  return gc_upto(av, fix_lcm(gmul(x,y)));
}

/* x + r ~ x ? Assume x,r are t_POL, deg(r) <= deg(x) */
static int
pol_approx0(GEN r, GEN x, int exact)
{
  long i, l;
  if (exact) return !signe(r);
  l = minss(lg(x), lg(r));
  for (i = 2; i < l; i++)
    if (!cx_approx0(gel(r,i), gel(x,i))) return 0;
  return 1;
}

GEN
RgX_gcd_simple(GEN x, GEN y)
{
  pari_sp av1, av = avma;
  GEN r, yorig = y;
  int exact = !(isinexactreal(x) || isinexactreal(y));

  for(;;)
  {
    av1 = avma; r = RgX_rem(x,y);
    if (pol_approx0(r, x, exact))
    {
      set_avma(av1);
      if (y == yorig) return RgX_copy(y);
      y = normalizepol_approx(y, lg(y));
      if (lg(y) == 3) { set_avma(av); return pol_1(varn(x)); }
      return gc_upto(av,y);
    }
    x = y; y = r;
    if (gc_needed(av,1)) {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_gcd_simple");
      (void)gc_all(av,2, &x,&y);
    }
  }
}
GEN
RgX_extgcd_simple(GEN a, GEN b, GEN *pu, GEN *pv)
{
  pari_sp av = avma;
  GEN q, r, d, d1, u, v, v1;
  int exact = !(isinexactreal(a) || isinexactreal(b));

  d = a; d1 = b; v = gen_0; v1 = gen_1;
  for(;;)
  {
    if (pol_approx0(d1, a, exact)) break;
    q = poldivrem(d,d1, &r);
    v = gsub(v, gmul(q,v1));
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
  }
  u = gsub(d, gmul(b,v));
  u = RgX_div(u,a);

  (void)gc_all(av, 3, &u,&v,&d);
  *pu = u;
  *pv = v; return d;
}

GEN
ghalfgcd(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx==t_INT && ty==t_INT) return halfgcdii(x, y);
  if (tx==t_POL && ty==t_POL && varn(x)==varn(y))
  {
    pari_sp av = avma;
    GEN a, b, M = RgX_halfgcd_all(x, y, &a, &b);
    return gc_GEN(av, mkvec2(M, mkcol2(a,b)));
  }
  pari_err_OP("halfgcd", x, y);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                    CONTENT / PRIMITIVE PART                     */
/*                                                                 */
/*******************************************************************/

GEN
content(GEN x)
{
  long lx, i, t, tx = typ(x);
  pari_sp av = avma;
  GEN c;

  if (is_scalar_t(tx)) return zero_gcd(x);
  switch(tx)
  {
    case t_RFRAC:
    {
      GEN n = gel(x,1), d = gel(x,2);
      /* -- varncmp(vn, vd) < 0 can't happen
       * -- if n is POLMOD, its main variable (in the sense of gvar2)
       *    has lower priority than denominator */
      if (typ(n) == t_POLMOD || varncmp(gvar(n), varn(d)) > 0)
        n = isinexact(n)? zero_gcd(n): gcopy(n);
      else
        n = content(n);
      return gc_upto(av, gdiv(n, content(d)));
    }

    case t_VEC: case t_COL:
      lx = lg(x); if (lx==1) return gen_0;
      break;

    case t_MAT:
    {
      long hx, j;
      lx = lg(x);
      if (lx == 1) return gen_0;
      hx = lgcols(x);
      if (hx == 1) return gen_0;
      if (lx == 2) { x = gel(x,1); lx = lg(x); break; }
      if (hx == 2) { x = row_i(x, 1, 1, lx-1); break; }
      c = content(gel(x,1));
      for (j=2; j<lx; j++)
        for (i=1; i<hx; i++) c = ggcd(c,gcoeff(x,i,j));
      if (typ(c) == t_INTMOD || isinexact(c)) return gc_const(av, gen_1);
      return gc_upto(av,c);
    }

    case t_POL: case t_SER:
      lx = lg(x); if (lx == 2) return gen_0;
      break;
    case t_VECSMALL: return utoi(zv_content(x));
    case t_QFB:
      lx = 4; break;

    default: pari_err_TYPE("content",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  for (i=lontyp[tx]; i<lx; i++)
    if (typ(gel(x,i)) != t_INT) break;
  lx--; c = gel(x,lx);
  t = typ(c); if (is_matvec_t(t)) c = content(c);
  if (i > lx)
  { /* integer coeffs */
    while (lx-- > lontyp[tx])
    {
      c = gcdii(c, gel(x,lx));
      if (equali1(c)) return gc_const(av, gen_1);
    }
  }
  else
  {
    if (isinexact(c)) c = zero_gcd(c);
    while (lx-- > lontyp[tx])
    {
      GEN d = gel(x,lx);
      t = typ(d); if (is_matvec_t(t)) d = content(d);
      c = ggcd(c, d);
    }
    if (isinexact(c)) return gc_const(av, gen_1);
  }
  switch(typ(c))
  {
    case t_INT:
      c = absi_shallow(c); break;
    case t_VEC: case t_COL: case t_MAT:
      pari_err_TYPE("content",x);
  }

  return av==avma? gcopy(c): gc_upto(av,c);
}

GEN
primitive_part(GEN x, GEN *ptc)
{
  pari_sp av = avma;
  GEN c = content(x);
  if (gequal1(c)) { set_avma(av); c = NULL; }
  else if (!gequal0(c)) x = gdiv(x,c);
  if (ptc) *ptc = c;
  return x;
}
GEN
primpart(GEN x) { return primitive_part(x, NULL); }

static GEN
Q_content_v(GEN x, long imin, long l)
{
  pari_sp av = avma;
  long i = l-1;
  GEN d = Q_content_safe(gel(x,i));
  if (!d) return NULL;
  for (i--; i >= imin; i--)
  {
    GEN c = Q_content_safe(gel(x,i));
    if (!c) return NULL;
    d = Q_gcd(d, c);
    if (gc_needed(av,1)) d = gc_upto(av, d);
  }
  return gc_upto(av, d);
}
/* As content(), but over Q. Treats polynomial as elts of Q[x1,...xn], instead
 * of Q(x2,...,xn)[x1] */
GEN
Q_content_safe(GEN x)
{
  long l;
  switch(typ(x))
  {
    case t_INT:  return absi(x);
    case t_FRAC: return absfrac(x);
    case t_COMPLEX: case t_VEC: case t_COL: case t_MAT:
      l = lg(x); return l==1? gen_1: Q_content_v(x, 1, l);
    case t_POL:
      l = lg(x); return l==2? gen_0: Q_content_v(x, 2, l);
    case t_POLMOD: return Q_content_safe(gel(x,2));
    case t_RFRAC:
    {
      GEN a, b;
      a = Q_content_safe(gel(x,1)); if (!a) return NULL;
      b = Q_content_safe(gel(x,2)); if (!b) return NULL;
      return gdiv(a, b);
    }
  }
  return NULL;
}
GEN
Q_content(GEN x)
{
  GEN c = Q_content_safe(x);
  if (!c) pari_err_TYPE("Q_content",x);
  return c;
}

GEN
ZX_content(GEN x)
{
  long i, l = lg(x);
  GEN d;
  pari_sp av;

  if (l == 2) return gen_0;
  d = gel(x,2);
  if (l == 3) return absi(d);
  av = avma;
  for (i=3; !is_pm1(d) && i<l; i++) d = gcdii(d, gel(x,i));
  if (signe(d) < 0) d = negi(d);
  return gc_INT(av, d);
}

static GEN
Z_content_v(GEN x, long i, long l)
{
  pari_sp av = avma;
  GEN d = Z_content(gel(x,i));
  if (!d) return NULL;
  for (i++; i<l; i++)
  {
    GEN c = Z_content(gel(x,i));
    if (!c) return NULL;
    d = gcdii(d, c); if (equali1(d)) return NULL;
    if ((i & 255) == 0) d = gc_INT(av, d);
  }
  return gc_INT(av, d);
}
/* return NULL for 1 */
GEN
Z_content(GEN x)
{
  long l;
  switch(typ(x))
  {
    case t_INT:
      if (is_pm1(x)) return NULL;
      return absi(x);
    case t_COMPLEX: case t_VEC: case t_COL: case t_MAT:
      l = lg(x); return l==1? NULL: Z_content_v(x, 1, l);
    case t_POL:
      l = lg(x); return l==2? gen_0: Z_content_v(x, 2, l);
    case t_POLMOD: return Z_content(gel(x,2));
  }
  pari_err_TYPE("Z_content", x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
Q_denom_v(GEN x, long i, long l)
{
  pari_sp av = avma;
  GEN d = Q_denom_safe(gel(x,i));
  if (!d) return NULL;
  for (i++; i<l; i++)
  {
    GEN D = Q_denom_safe(gel(x,i));
    if (!D) return NULL;
    if (D != gen_1) d = lcmii(d, D);
    if ((i & 255) == 0) d = gc_INT(av, d);
  }
  return gc_INT(av, d);
}
/* NOT MEMORY CLEAN (because of t_FRAC).
 * As denom(), but over Q. Treats polynomial as elts of Q[x1,...xn], instead
 * of Q(x2,...,xn)[x1] */
GEN
Q_denom_safe(GEN x)
{
  long l;
  switch(typ(x))
  {
    case t_INT: return gen_1;
    case t_PADIC: l = valp(x); return l < 0? powiu(padic_p(x), -l): gen_1;
    case t_FRAC: return gel(x,2);
    case t_QUAD: return Q_denom_v(x, 2, 4);
    case t_COMPLEX: case t_VEC: case t_COL: case t_MAT:
      l = lg(x); return l==1? gen_1: Q_denom_v(x, 1, l);
    case t_POL: case t_SER:
      l = lg(x); return l==2? gen_1: Q_denom_v(x, 2, l);
    case t_POLMOD: return Q_denom(gel(x,2));
    case t_RFRAC:
    {
      GEN a, b;
      a = Q_content(gel(x,1)); if (!a) return NULL;
      b = Q_content(gel(x,2)); if (!b) return NULL;
      return Q_denom(gdiv(a, b));
    }
  }
  return NULL;
}
GEN
Q_denom(GEN x)
{
  GEN d = Q_denom_safe(x);
  if (!d) pari_err_TYPE("Q_denom",x);
  return d;
}

GEN
Q_remove_denom(GEN x, GEN *ptd)
{
  GEN d = Q_denom_safe(x);
  if (d) { if (d == gen_1) d = NULL; else x = Q_muli_to_int(x,d); }
  if (ptd) *ptd = d;
  return x;
}

/* return y = x * d, assuming x rational, and d,y integral */
GEN
Q_muli_to_int(GEN x, GEN d)
{
  GEN y, xn, xd;
  pari_sp av;

  if (typ(d) != t_INT) pari_err_TYPE("Q_muli_to_int",d);
  switch (typ(x))
  {
    case t_INT:
      return mulii(x,d);

    case t_FRAC:
      xn = gel(x,1);
      xd = gel(x,2); av = avma;
      y = mulii(xn, diviiexact(d, xd));
      return gc_INT(av, y);
    case t_COMPLEX:
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = Q_muli_to_int(gel(x,1),d);
      gel(y,2) = Q_muli_to_int(gel(x,2),d);
      return y;
    case t_PADIC:
      y = gcopy(x); if (!isint1(d)) setvalp(y, 0);
      return y;
    case t_QUAD:
      y = cgetg(4,t_QUAD);
      gel(y,1) = ZX_copy(gel(x,1));
      gel(y,2) = Q_muli_to_int(gel(x,2),d);
      gel(y,3) = Q_muli_to_int(gel(x,3),d); return y;

    case t_VEC:
    case t_COL:
    case t_MAT: pari_APPLY_same(Q_muli_to_int(gel(x,i), d));
    case t_POL: pari_APPLY_pol_normalized(Q_muli_to_int(gel(x,i), d));
    case t_SER: pari_APPLY_ser_normalized(Q_muli_to_int(gel(x,i), d));

    case t_POLMOD:
      retmkpolmod(Q_muli_to_int(gel(x,2), d), RgX_copy(gel(x,1)));
    case t_RFRAC:
      return gmul(x, d);
  }
  pari_err_TYPE("Q_muli_to_int",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static void
rescale_init(GEN c, int *exact, long *emin, GEN *D)
{
  long e, i;
  switch(typ(c))
  {
    case t_REAL:
      *exact = 0;
      if (!signe(c)) return;
      e = expo(c) + 1 - bit_prec(c);
      for (i = lg(c)-1; i > 2; i--, e += BITS_IN_LONG)
        if (c[i]) break;
      e += vals(c[i]); break; /* e[2] != 0 */
    case t_INT:
      if (!signe(c)) return;
      e = expi(c);
      break;
    case t_FRAC:
      e = expi(gel(c,1)) - expi(gel(c,2));
      if (*exact) *D = lcmii(*D, gel(c,2));
      break;
    default:
      pari_err_TYPE("rescale_to_int",c);
      return; /* LCOV_EXCL_LINE */
  }
  if (e < *emin) *emin = e;
}
GEN
RgM_rescale_to_int(GEN x)
{
  long lx = lg(x), i,j, hx, emin;
  GEN D;
  int exact;

  if (lx == 1) return cgetg(1,t_MAT);
  hx = lgcols(x);
  exact = 1;
  emin = HIGHEXPOBIT;
  D = gen_1;
  for (j = 1; j < lx; j++)
    for (i = 1; i < hx; i++) rescale_init(gcoeff(x,i,j), &exact, &emin, &D);
  if (exact) return D == gen_1 ? x: Q_muli_to_int(x, D);
  return grndtoi(gmul2n(x, -emin), NULL);
}
GEN
RgX_rescale_to_int(GEN x)
{
  long lx = lg(x), i, emin;
  GEN D;
  int exact;
  if (lx == 2) return gcopy(x); /* rare */
  exact = 1;
  emin = HIGHEXPOBIT;
  D = gen_1;
  for (i = 2; i < lx; i++) rescale_init(gel(x,i), &exact, &emin, &D);
  if (exact) return D == gen_1 ? x: Q_muli_to_int(x, D);
  return grndtoi(gmul2n(x, -emin), NULL);
}

/* return x * n/d. x: rational; d,n,result: integral; d,n coprime */
static GEN
Q_divmuli_to_int(GEN x, GEN d, GEN n)
{
  GEN y, xn, xd;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT:
      av = avma; y = diviiexact(x,d);
      return gc_INT(av, mulii(y,n));

    case t_FRAC:
      xn = gel(x,1);
      xd = gel(x,2); av = avma;
      y = mulii(diviiexact(xn, d), diviiexact(n, xd));
      return gc_INT(av, y);

    case t_VEC:
    case t_COL:
    case t_MAT: pari_APPLY_same(Q_divmuli_to_int(gel(x,i), d,n));
    case t_POL: pari_APPLY_pol_normalized(Q_divmuli_to_int(gel(x,i), d,n));

    case t_RFRAC:
      av = avma;
      return gc_upto(av, gmul(x,mkfrac(n,d)));

    case t_POLMOD:
      retmkpolmod(Q_divmuli_to_int(gel(x,2), d,n), RgX_copy(gel(x,1)));
  }
  pari_err_TYPE("Q_divmuli_to_int",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* return x / d. x: rational; d,result: integral. */
static GEN
Q_divi_to_int(GEN x, GEN d)
{
  switch(typ(x))
  {
    case t_INT:
      return diviiexact(x,d);

    case t_VEC:
    case t_COL:
    case t_MAT: pari_APPLY_same(Q_divi_to_int(gel(x,i), d));
    case t_POL: pari_APPLY_pol_normalized(Q_divi_to_int(gel(x,i), d));

    case t_RFRAC:
      return gdiv(x,d);

    case t_POLMOD:
      retmkpolmod(Q_divi_to_int(gel(x,2), d), RgX_copy(gel(x,1)));
  }
  pari_err_TYPE("Q_divi_to_int",x);
  return NULL; /* LCOV_EXCL_LINE */
}
/* c t_FRAC */
static GEN
Q_divq_to_int(GEN x, GEN c)
{
  GEN n = gel(c,1), d = gel(c,2);
  if (is_pm1(n)) {
    GEN y = Q_muli_to_int(x,d);
    if (signe(n) < 0) y = gneg(y);
    return y;
  }
  return Q_divmuli_to_int(x, n,d);
}

/* return y = x / c, assuming x,c rational, and y integral */
GEN
Q_div_to_int(GEN x, GEN c)
{
  switch(typ(c))
  {
    case t_INT:  return Q_divi_to_int(x, c);
    case t_FRAC: return Q_divq_to_int(x, c);
  }
  pari_err_TYPE("Q_div_to_int",c);
  return NULL; /* LCOV_EXCL_LINE */
}
/* return y = x * c, assuming x,c rational, and y integral */
GEN
Q_mul_to_int(GEN x, GEN c)
{
  GEN d, n;
  switch(typ(c))
  {
    case t_INT: return Q_muli_to_int(x, c);
    case t_FRAC:
      n = gel(c,1);
      d = gel(c,2);
      return Q_divmuli_to_int(x, d,n);
  }
  pari_err_TYPE("Q_mul_to_int",c);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
Q_primitive_part(GEN x, GEN *ptc)
{
  pari_sp av = avma;
  GEN c = Q_content_safe(x);
  if (c)
  {
    if (typ(c) == t_INT)
    {
      if (equali1(c)) { set_avma(av); c = NULL; }
      else if (signe(c)) x = Q_divi_to_int(x, c);
    }
    else x = Q_divq_to_int(x, c);
  }
  if (ptc) *ptc = c;
  return x;
}
GEN
Q_primpart(GEN x) { return Q_primitive_part(x, NULL); }
GEN
vec_Q_primpart(GEN x)
{ pari_APPLY_same(Q_primpart(gel(x,i))) }
GEN
row_Q_primpart(GEN M)
{ return shallowtrans(vec_Q_primpart(shallowtrans(M))); }

/*******************************************************************/
/*                                                                 */
/*                           SUBRESULTANT                          */
/*                                                                 */
/*******************************************************************/
/* for internal use */
GEN
gdivexact(GEN x, GEN y)
{
  long i,lx;
  GEN z;
  if (gequal1(y)) return x;
  if (typ(y) == t_POLMOD) return gmul(x, ginv(y));
  switch(typ(x))
  {
    case t_INT:
      if (typ(y)==t_INT) return diviiexact(x,y);
      if (!signe(x)) return gen_0;
      break;
    case t_INTMOD:
    case t_FFELT:
    case t_POLMOD: return gmul(x,ginv(y));
    case t_POL:
      switch(typ(y))
      {
        case t_INTMOD:
        case t_FFELT:
        case t_POLMOD: return gmul(x,ginv(y));
        case t_POL: { /* not stack-clean */
          long v;
          if (varn(x)!=varn(y)) break;
          v = RgX_valrem(y,&y);
          if (v) x = RgX_shift_shallow(x,-v);
          if (!degpol(y)) { y = gel(y,2); break; }
          return RgX_div(x,y);
        }
        case t_RFRAC:
          if (varn(gel(y,2)) != varn(x)) break;
          return gdiv(x, y);
      }
      return RgX_Rg_divexact(x, y);
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = new_chunk(lx);
      for (i=1; i<lx; i++) gel(z,i) = gdivexact(gel(x,i),y);
      z[0] = x[0]; return z;
  }
  if (DEBUGLEVEL) pari_warn(warner,"missing case in gdivexact");
  return gdiv(x,y);
}

static GEN
init_resultant(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), vx, vy;
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (gequal0(x) || gequal0(y)) return gmul(x,y); /* keep type info */
    if (tx==t_POL) return gpowgs(y, degpol(x));
    if (ty==t_POL) return gpowgs(x, degpol(y));
    return gen_1;
  }
  if (tx!=t_POL) pari_err_TYPE("resultant",x);
  if (ty!=t_POL) pari_err_TYPE("resultant",y);
  if (!signe(x) || !signe(y)) return gmul(Rg_get_0(x),Rg_get_0(y)); /*type*/
  vx = varn(x);
  vy = varn(y); if (vx == vy) return NULL;
  return (varncmp(vx,vy) < 0)? gpowgs(y,degpol(x)): gpowgs(x,degpol(y));
}

/* x an RgX, y a scalar */
static GEN
scalar_res(GEN x, GEN y, GEN *U, GEN *V)
{
  *V = gpowgs(y,degpol(x)-1);
  *U = gen_0; return gmul(y, *V);
}

/* return 0 if the subresultant chain can be interrupted.
 * Set u = NULL if the resultant is 0. */
static int
subres_step(GEN *u, GEN *v, GEN *g, GEN *h, GEN *uze, GEN *um1, long *signh)
{
  GEN u0, c, r, q = RgX_pseudodivrem(*u,*v, &r);
  long du, dv, dr, degq;

  if (gequal0(leading_coeff(r))) r = RgX_renormalize(r);
  dr = lg(r); if (!signe(r)) { *u = NULL; return 0; }
  du = degpol(*u);
  dv = degpol(*v);
  degq = du - dv;
  if (*um1 == gen_1)
    u0 = gpowgs(gel(*v,dv+2),degq+1);
  else if (*um1 == gen_0)
    u0 = gen_0;
  else /* except in those 2 cases, um1 is an RgX */
    u0 = RgX_Rg_mul(*um1, gpowgs(gel(*v,dv+2),degq+1));

  if (*uze == gen_0) /* except in that case, uze is an RgX */
    u0 = scalarpol(u0, varn(*u)); /* now an RgX */
  else
    u0 = gsub(u0, gmul(q,*uze));

  *um1 = *uze;
  *uze = u0; /* uze <- lead(v)^(degq + 1) * um1 - q * uze */

  *u = *v; c = *g; *g  = leading_coeff(*u);
  switch(degq)
  {
    case 0: break;
    case 1:
      c = gmul(*h,c); *h = *g; break;
    default:
      c = gmul(gpowgs(*h,degq), c);
      *h = gdivexact(gpowgs(*g,degq), gpowgs(*h,degq-1));
  }
  if (typ(c) == t_POLMOD)
  {
    c = ginv(c);
    *v = RgX_Rg_mul(r,c);
    *uze = RgX_Rg_mul(*uze,c);
  }
  else
  {
    *v  = RgX_Rg_divexact(r,c);
    *uze= RgX_Rg_divexact(*uze,c);
  }
  if (both_odd(du, dv)) *signh = -*signh;
  return (dr > 3);
}

/* compute U, V s.t Ux + Vy = resultant(x,y) */
static GEN
subresext_i(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av, av2;
  long dx, dy, du, signh, tx = typ(x), ty = typ(y);
  GEN r, z, g, h, p1, cu, cv, u, v, um1, uze, vze;

  if (!is_extscalar_t(tx)) pari_err_TYPE("subresext",x);
  if (!is_extscalar_t(ty)) pari_err_TYPE("subresext",y);
  if (gequal0(x) || gequal0(y)) { *U = *V = gen_0; return gen_0; }
  if (tx != t_POL) {
    if (ty != t_POL) { *U = ginv(x); *V = gen_0; return gen_1; }
    return scalar_res(y,x,V,U);
  }
  if (ty != t_POL) return scalar_res(x,y,U,V);
  if (varn(x) != varn(y))
    return varncmp(varn(x), varn(y)) < 0? scalar_res(x,y,U,V)
                                        : scalar_res(y,x,V,U);
  if (gequal0(leading_coeff(x))) x = RgX_renormalize(x);
  if (gequal0(leading_coeff(y))) y = RgX_renormalize(y);
  dx = degpol(x);
  dy = degpol(y);
  signh = 1;
  if (dx < dy)
  {
    pswap(U,V); lswap(dx,dy); swap(x,y);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy == 0)
  {
    *V = gpowgs(gel(y,2),dx-1);
    *U = gen_0; return gmul(*V,gel(y,2));
  }
  av = avma;
  u = x = primitive_part(x, &cu);
  v = y = primitive_part(y, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    if (!subres_step(&u, &v, &g, &h, &uze, &um1, &signh)) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"subresext, dr = %ld", degpol(v));
      (void)gc_all(av2,6, &u,&v,&g,&h,&uze,&um1);
    }
  }
  /* uze an RgX */
  if (!u) { *U = *V = gen_0; return gc_const(av, gen_0); }
  z = gel(v,2); du = degpol(u);
  if (du > 1)
  { /* z = gdivexact(gpowgs(z,du), gpowgs(h,du-1)); */
    p1 = gpowgs(gdiv(z,h),du-1);
    z = gmul(z,p1);
    uze = RgX_Rg_mul(uze, p1);
  }
  if (signh < 0) { z = gneg_i(z); uze = RgX_neg(uze); }

  vze = RgX_divrem(Rg_RgX_sub(z, RgX_mul(uze,x)), y, &r);
  if (signe(r)) pari_warn(warner,"inexact computation in subresext");
  /* uze ppart(x) + vze ppart(y) = z = resultant(ppart(x), ppart(y)), */
  p1 = gen_1;
  if (cu) p1 = gmul(p1, gpowgs(cu,dy));
  if (cv) p1 = gmul(p1, gpowgs(cv,dx));
  cu = cu? gdiv(p1,cu): p1;
  cv = cv? gdiv(p1,cv): p1;
  z = gmul(z,p1);
  *U = RgX_Rg_mul(uze,cu);
  *V = RgX_Rg_mul(vze,cv);
  return z;
}
GEN
subresext(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av = avma;
  GEN z = subresext_i(x, y, U, V);
  return gc_all(av, 3, &z, U, V);
}

static GEN
zero_extgcd(GEN y, GEN *U, GEN *V, long vx)
{
  GEN x=content(y);
  *U=pol_0(vx); *V = scalarpol(ginv(x), vx); return gmul(y,*V);
}

static int
must_negate(GEN x)
{
  GEN t = leading_coeff(x);
  switch(typ(t))
  {
    case t_INT: case t_REAL:
      return (signe(t) < 0);
    case t_FRAC:
      return (signe(gel(t,1)) < 0);
  }
  return 0;
}

static GEN
gc_gcdext(pari_sp av, GEN r, GEN *u, GEN *v)
{
  if (!u && !v) return gc_upto(av, r);
  if (u  &&  v) return gc_all(av, 3, &r, u, v);
  return gc_all(av, 2, &r, u ? u: v);
}

static GEN
RgX_extgcd_FpX(GEN x, GEN y, GEN p, GEN *u, GEN *v)
{
  pari_sp av = avma;
  GEN r = FpX_extgcd(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p, u, v);
  if (u) *u = FpX_to_mod(*u, p);
  if (v) *v = FpX_to_mod(*v, p);
  return gc_gcdext(av, FpX_to_mod(r, p), u, v);
}

static GEN
RgX_extgcd_FpXQX(GEN x, GEN y, GEN pol, GEN p, GEN *U, GEN *V)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  r = FpXQX_extgcd(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p), T, p, U, V);
  return gc_gcdext(av, FpXQX_to_mod(r, T, p), U, V);
}

static GEN
RgX_extgcd_fast(GEN x, GEN y, GEN *U, GEN *V)
{
  GEN p, pol;
  long pa;
  long t = RgX_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_FFELT:  return FFX_extgcd(x, y, pol, U, V);
    case t_INTMOD: return RgX_extgcd_FpX(x, y, p, U, V);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgX_extgcd_FpXQX(x, y, pol, p, U, V);
    default:       return NULL;
  }
}

/* compute U, V s.t Ux + Vy = GCD(x,y) using subresultant */
GEN
RgX_extgcd(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av, av2, tetpil;
  long signh; /* junk */
  long dx, dy, vx, tx = typ(x), ty = typ(y);
  GEN r, z, g, h, p1, cu, cv, u, v, um1, uze, vze;

  if (tx!=t_POL) pari_err_TYPE("RgX_extgcd",x);
  if (ty!=t_POL) pari_err_TYPE("RgX_extgcd",y);
  if ( varncmp(varn(x),varn(y))) pari_err_VAR("RgX_extgcd",x,y);
  vx=varn(x);
  if (!signe(x))
  {
    if (signe(y)) return zero_extgcd(y,U,V,vx);
    *U = pol_0(vx); *V = pol_0(vx);
    return pol_0(vx);
  }
  if (!signe(y)) return zero_extgcd(x,V,U,vx);
  r = RgX_extgcd_fast(x, y, U, V);
  if (r) return r;
  dx = degpol(x); dy = degpol(y);
  if (dx < dy) { pswap(U,V); lswap(dx,dy); swap(x,y); }
  if (dy==0) { *U=pol_0(vx); *V=ginv(y); return pol_1(vx); }

  av = avma;
  u = x = primitive_part(x, &cu);
  v = y = primitive_part(y, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    if (!subres_step(&u, &v, &g, &h, &uze, &um1, &signh)) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_extgcd, dr = %ld",degpol(v));
      (void)gc_all(av2,6,&u,&v,&g,&h,&uze,&um1);
    }
  }
  if (uze != gen_0) {
    GEN r;
    vze = RgX_divrem(RgX_sub(v, RgX_mul(uze,x)), y, &r);
    if (signe(r)) pari_warn(warner,"inexact computation in RgX_extgcd");
    if (cu) uze = RgX_Rg_div(uze,cu);
    if (cv) vze = RgX_Rg_div(vze,cv);
    p1 = ginv(content(v));
  }
  else /* y | x */
  {
    vze = cv ? RgX_Rg_div(pol_1(vx),cv): pol_1(vx);
    uze = pol_0(vx);
    p1 = gen_1;
  }
  if (must_negate(v)) p1 = gneg(p1);
  tetpil = avma;
  z = RgX_Rg_mul(v,p1);
  *U = RgX_Rg_mul(uze,p1);
  *V = RgX_Rg_mul(vze,p1);
  return gc_all_unsafe(av,tetpil, 3, &z, U, V);
}

static GEN
RgX_halfgcd_all_i(GEN a, GEN b, GEN *pa, GEN *pb)
{
  pari_sp av=avma;
  long m = degpol(a), va = varn(a);
  GEN R, u,u1,v,v1;
  u1 = v = pol_0(va);
  u = v1 = pol_1(va);
  if (degpol(a)<degpol(b))
  {
    swap(a,b);
    swap(u,v); swap(u1,v1);
  }
  while (2*degpol(b) >= m)
  {
    GEN r, q = RgX_pseudodivrem(a,b,&r);
    GEN l = gpowgs(leading_coeff(b), degpol(a)-degpol(b)+1);
    GEN g = ggcd(l, content(r));
    q = RgX_Rg_div(q, g);
    r = RgX_Rg_div(r, g);
    l = gdiv(l, g);
    a = b; b = r; swap(u,v); swap(u1,v1);
    v  = RgX_sub(gmul(l,v),  RgX_mul(u, q));
    v1 = RgX_sub(gmul(l,v1), RgX_mul(u1, q));
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"halfgcd (d = %ld)",degpol(b));
      (void)gc_all(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  if (pa) *pa = a;
  if (pb) *pb = b;
  R = mkmat22(u,u1,v,v1);
  return !pa && pb ? gc_all(av, 2, &R, pb): gc_all(av, 1+!!pa+!!pb, &R, pa, pb);
}

static GEN
RgX_halfgcd_all_FpX(GEN x, GEN y, GEN p, GEN *a, GEN *b)
{
  pari_sp av = avma;
  GEN M;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    GEN xp = RgX_to_Flx(x, pp), yp = RgX_to_Flx(y, pp);
    M = Flx_halfgcd_all(xp, yp, pp, a, b);
    M = FlxM_to_ZXM(M); *a = Flx_to_ZX(*a); *b = Flx_to_ZX(*b);
  }
  else
  {
    x = RgX_to_FpX(x, p); y = RgX_to_FpX(y, p);
    M = FpX_halfgcd_all(x, y, p, a, b);
  }
  return !a && b ? gc_all(av, 2, &M, b): gc_all(av, 1+!!a+!!b, &M, a, b);
}

static GEN
RgX_halfgcd_all_FpXQX(GEN x, GEN y, GEN pol, GEN p, GEN *a, GEN *b)
{
  pari_sp av = avma;
  GEN M, T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("halfgcd", x, y);
  x = RgX_to_FpXQX(x, T, p); y = RgX_to_FpXQX(y, T, p);
  M = FpXQX_halfgcd_all(x, y, T, p, a, b);
  if (a) *a = FqX_to_mod(*a, T, p);
  if (b) *b = FqX_to_mod(*b, T, p);
  M = FqXM_to_mod(M, T, p);
  return !a && b ? gc_all(av, 2, &M, b): gc_all(av, 1+!!a+!!b, &M, a, b);
}

static GEN
RgX_halfgcd_all_fast(GEN x, GEN y, GEN *a, GEN *b)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_FFELT:  return FFX_halfgcd_all(x, y, pol, a, b);
    case t_INTMOD: return RgX_halfgcd_all_FpX(x, y, p, a, b);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgX_halfgcd_all_FpXQX(x, y, pol, p, a, b);
    default:       return NULL;
  }
}

GEN
RgX_halfgcd_all(GEN x, GEN y, GEN *a, GEN *b)
{
  GEN z = RgX_halfgcd_all_fast(x, y, a, b);
  if (z) return z;
  return RgX_halfgcd_all_i(x, y, a, b);
}

GEN
RgX_halfgcd(GEN x, GEN y)
{ return  RgX_halfgcd_all(x, y, NULL, NULL); }

int
RgXQ_ratlift(GEN x, GEN T, long amax, long bmax, GEN *P, GEN *Q)
{
  pari_sp av = avma, av2, tetpil;
  long signh; /* junk */
  long vx;
  GEN g, h, p1, cu, cv, u, v, um1, uze;

  if (typ(x)!=t_POL) pari_err_TYPE("RgXQ_ratlift",x);
  if (typ(T)!=t_POL) pari_err_TYPE("RgXQ_ratlift",T);
  if ( varncmp(varn(x),varn(T)) ) pari_err_VAR("RgXQ_ratlift",x,T);
  if (bmax < 0) pari_err_DOMAIN("ratlift", "bmax", "<", gen_0, stoi(bmax));
  if (!signe(T)) {
    if (degpol(x) <= amax) {
      *P = RgX_copy(x);
      *Q = pol_1(varn(x));
      return 1;
    }
    return 0;
  }
  if (amax+bmax >= degpol(T))
    pari_err_DOMAIN("ratlift", "amax+bmax", ">=", stoi(degpol(T)),
                    mkvec3(stoi(amax), stoi(bmax), T));
  vx = varn(T);
  u = x = primitive_part(x, &cu);
  v = T = primitive_part(T, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    (void) subres_step(&u, &v, &g, &h, &uze, &um1, &signh);
    if (!u || (typ(uze)==t_POL && degpol(uze)>bmax)) return gc_bool(av,0);
    if (typ(v)!=t_POL || degpol(v)<=amax) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXQ_ratlift, dr = %ld", degpol(v));
      (void)gc_all(av2,6,&u,&v,&g,&h,&uze,&um1);
    }
  }
  if (uze == gen_0)
  {
    set_avma(av); *P = pol_0(vx); *Q = pol_1(vx);
    return 1;
  }
  if (cu) uze = RgX_Rg_div(uze,cu);
  p1 = ginv(content(v));
  if (must_negate(v)) p1 = gneg(p1);
  tetpil = avma;
  *P = RgX_Rg_mul(v,p1);
  *Q = RgX_Rg_mul(uze,p1);
  (void)gc_all_unsafe(av,tetpil,2,P,Q); return 1;
}

GEN
RgX_chinese_coprime(GEN x, GEN y, GEN Tx, GEN Ty, GEN Tz)
{
  pari_sp av = avma;
  GEN ax = RgX_mul(RgXQ_inv(Tx,Ty), Tx);
  GEN p1 = RgX_mul(ax, RgX_sub(y,x));
  p1 = RgX_add(x,p1);
  if (!Tz) Tz = RgX_mul(Tx,Ty);
  p1 = RgX_rem(p1, Tz);
  return gc_upto(av,p1);
}

/*******************************************************************/
/*                                                                 */
/*                RESULTANT USING DUCOS VARIANT                    */
/*                                                                 */
/*******************************************************************/
/* x^n / y^(n-1), assume n > 0 */
static GEN
Lazard(GEN x, GEN y, long n)
{
  long a;
  GEN c;

  if (n == 1) return x;
  a = 1 << expu(n); /* a = 2^k <= n < 2^(k+1) */
  c=x; n-=a;
  while (a>1)
  {
    a>>=1; c=gdivexact(gsqr(c),y);
    if (n>=a) { c=gdivexact(gmul(c,x),y); n -= a; }
  }
  return c;
}

/* F (x/y)^(n-1), assume n >= 1 */
static GEN
Lazard2(GEN F, GEN x, GEN y, long n)
{
  if (n == 1) return F;
  return RgX_Rg_divexact(RgX_Rg_mul(F, Lazard(x,y,n-1)), y);
}

static GEN
RgX_neg_i(GEN x, long lx)
{
  long i;
  GEN y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
static GEN
RgX_Rg_mul_i(GEN y, GEN x, long ly)
{
  long i;
  GEN z;
  if (isrationalzero(x)) return pol_0(varn(y));
  z = cgetg(ly,t_POL); z[1] = y[1];
  for (i = 2; i < ly; i++) gel(z,i) = gmul(x,gel(y,i));
  return z;
}
static long
reductum_lg(GEN x, long lx)
{
  long i = lx-2;
  while (i > 1 && gequal0(gel(x,i))) i--;
  return i+1;
}

#define addshift(x,y) RgX_addmulXn_shallow((x),(y),1)
/* delta = deg(P) - deg(Q) > 0, deg(Q) > 0, P,Q,Z t_POL in the same variable,
 * s "scalar". Return prem(P, -Q) / s^delta lc(P) */
static GEN
nextSousResultant(GEN P, GEN Q, GEN Z, GEN s)
{
  GEN p0, q0, h0, TMP, H, A, z0 = leading_coeff(Z);
  long p, q, j, lP, lQ;
  pari_sp av;

  p = degpol(P); p0 = gel(P,p+2); lP = reductum_lg(P,lg(P));
  q = degpol(Q); q0 = gel(Q,q+2); lQ = reductum_lg(Q,lg(Q));
  /* p > q. Very often p - 1 = q */
  av = avma;
  /* H = RgX_neg(reductum(Z)) optimized, using Q ~ Z */
  H = RgX_neg_i(Z, lQ); /* deg H < q */

  A = (q+2 < lP)? RgX_Rg_mul_i(H, gel(P,q+2), lQ): NULL;
  for (j = q+1; j < p; j++)
  {
    if (degpol(H) == q-1)
    { /* h0 = coeff of degree q-1 = leading coeff */
      h0 = gel(H,q+1); (void)normalizepol_lg(H, q+1);
      H = addshift(H, RgX_Rg_divexact(RgX_Rg_mul_i(Q, gneg(h0), lQ), q0));
    }
    else
      H = RgX_shift_shallow(H, 1);
    if (j+2 < lP)
    {
      TMP = RgX_Rg_mul(H, gel(P,j+2));
      A = A? RgX_add(A, TMP): TMP;
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"nextSousResultant j = %ld/%ld",j,p);
      (void)gc_all(av,A?2:1,&H,&A);
    }
  }
  if (q+2 < lP) lP = reductum_lg(P, q+3);
  TMP = RgX_Rg_mul_i(P, z0, lP);
  A = A? RgX_add(A, TMP): TMP;
  A = RgX_Rg_divexact(A, p0);
  if (degpol(H) == q-1)
  {
    h0 = gel(H,q+1); (void)normalizepol_lg(H, q+1); /* destroy old H */
    A = RgX_add(RgX_Rg_mul(addshift(H,A),q0), RgX_Rg_mul_i(Q, gneg(h0), lQ));
  }
  else
    A = RgX_Rg_mul(addshift(H,A), q0);
  return RgX_Rg_divexact(A, s);
}
#undef addshift

static GEN
RgX_pseudodenom(GEN x)
{
  GEN m = NULL;
  long l = lg(x), i;
  for (i = 2; i < l; i++)
  {
    GEN xi = gel(x, i);
    if (typ(xi) == t_RFRAC)
    {
      GEN d = denom_i(xi);
      if (!m || signe(RgX_pseudorem(m, d)))
        m = m ? gmul(m, d): d;
    }
  }
  return m;
}

/* Ducos's subresultant */
GEN
RgX_resultant_all(GEN P, GEN Q, GEN *sol)
{
  pari_sp av, av2;
  long dP, dQ, delta, sig = 1;
  GEN DP, DQ, cP, cQ, Z, s;

  dP = degpol(P);
  dQ = degpol(Q); delta = dP - dQ;
  if (delta < 0)
  {
    if (both_odd(dP, dQ)) sig = -1;
    swap(P,Q); lswap(dP, dQ); delta = -delta;
  }
  if (sol) *sol = gen_0;
  av = avma;
  if (dQ <= 0)
  {
    if (dQ < 0) return Rg_get_0(P);
    s = gpowgs(gel(Q,2), dP);
    if (sig == -1) s = gc_upto(av, gneg(s));
    return s;
  }
  if (dQ == 1)
  {
    if (sol) *sol = Q;
    s = RgX_homogenous_evalpow(P, gel(Q,2), gpowers(gneg(gel(Q,3)), dP));
    if (sig==-1) s = gneg(s);
    return gc_all(av, sol ? 2: 1, &s, sol);
  }
  /* primitive_part is also possible here, but possibly very costly,
   * and hardly ever worth it */

  DP = RgX_pseudodenom(P); if (DP) P = gmul(P,DP);
  DQ = RgX_pseudodenom(Q); if (DQ) Q = gmul(Q,DQ);
  P = Q_primitive_part(P, &cP);
  Q = Q_primitive_part(Q, &cQ);
  av2 = avma;
  s = gpowgs(leading_coeff(Q),delta);
  if (both_odd(dP, dQ)) sig = -sig;
  Z = Q;
  Q = RgX_pseudorem(P, Q);
  P = Z;
  while(degpol(Q) > 0)
  {
    delta = degpol(P) - degpol(Q); /* > 0 */
    Z = Lazard2(Q, leading_coeff(Q), s, delta);
    if (both_odd(degpol(P), degpol(Q))) sig = -sig;
    Q = nextSousResultant(P, Q, Z, s);
    P = Z;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"resultant_all, degpol Q = %ld",degpol(Q));
      (void)gc_all(av2,2,&P,&Q);
    }
    s = leading_coeff(P);
  }
  if (!signe(Q)) { set_avma(av); return Rg_get_0(Q); }
  s = Lazard(leading_coeff(Q), s, degpol(P));
  if (sig == -1) s = gneg(s);
  if (DP) s = gdiv(s, gpowgs(DP,dQ));
  if (DQ) s = gdiv(s, gpowgs(DQ,dP));
  if (cP) s = gmul(s, gpowgs(cP,dQ));
  if (cQ) s = gmul(s, gpowgs(cQ,dP));
  if (!sol) return gc_GEN(av, s);
  *sol = P; return gc_all(av, 2, &s, sol);
}

static GEN
RgX_resultant_FpX(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = utoi(Flx_resultant(RgX_to_Flx(x, pp), RgX_to_Flx(y, pp), pp));
  }
  else
    r = FpX_resultant(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p);
  return gc_upto(av, Fp_to_mod(r, p));
}

static GEN
RgX_resultant_FpXQX(GEN x, GEN y, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  r = FpXQX_resultant(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p), T, p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
resultant_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa, t;
  p = init_resultant(x,y);
  if (p) return p;
  t = RgX_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZX_resultant(x,y);
    case t_FRAC:   return QX_resultant(x,y);
    case t_FFELT:  return FFX_resultant(x,y,pol);
    case t_INTMOD: return RgX_resultant_FpX(x, y, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgX_resultant_FpXQX(x, y, pol, p);
    case RgX_type_code(t_POL, t_INT):
    {
      long v = -1;
      if (varn(x)==varn(y) && RgX_is_ZXX(x, &v) && RgX_is_ZXX(y, &v) && v>=0)
                   return ZXX_resultant(x,y,v);
    } /* FALL THROUGH */
    default:       return NULL;
  }
}

static GEN
RgX_resultant_sylvester(GEN x, GEN y)
{
  pari_sp av = avma;
  return gc_upto(av, det(RgX_sylvestermatrix(x,y)));
}

/* Return resultant(P,Q).
 * Uses Sylvester's matrix if P or Q inexact, a modular algorithm if they
 * are in Q[X], and Ducos/Lazard optimization of the subresultant algorithm
 * in the "generic" case. */
GEN
resultant(GEN P, GEN Q)
{
  GEN z = resultant_fast(P,Q);
  if (z) return z;
  if (isinexact(P) || isinexact(Q)) return RgX_resultant_sylvester(P,Q);
  return RgX_resultant_all(P, Q, NULL);
}

/*******************************************************************/
/*                                                                 */
/*               RESULTANT USING SYLVESTER MATRIX                  */
/*                                                                 */
/*******************************************************************/
static GEN
syl_RgC(GEN x, long j, long d, long D, long cp)
{
  GEN c = cgetg(d+1,t_COL);
  long i;
  for (i=1; i< j; i++) gel(c,i) = gen_0;
  for (   ; i<=D; i++) { GEN t = gel(x,D-i+2); gel(c,i) = cp? gcopy(t): t; }
  for (   ; i<=d; i++) gel(c,i) = gen_0;
  return c;
}
static GEN
syl_RgM(GEN x, GEN y, long cp)
{
  long j, d, dx = degpol(x), dy = degpol(y);
  GEN M;
  if (dx < 0) return dy < 0? cgetg(1,t_MAT): zeromat(dy,dy);
  if (dy < 0) return zeromat(dx,dx);
  d = dx+dy; M = cgetg(d+1,t_MAT);
  for (j=1; j<=dy; j++) gel(M,j)    = syl_RgC(x,j,d,j+dx, cp);
  for (j=1; j<=dx; j++) gel(M,j+dy) = syl_RgC(y,j,d,j+dy, cp);
  return M;
}
GEN
RgX_sylvestermatrix(GEN x, GEN y) { return syl_RgM(x,y,0); }
GEN
sylvestermatrix(GEN x, GEN y)
{
  if (typ(x)!=t_POL) pari_err_TYPE("sylvestermatrix",x);
  if (typ(y)!=t_POL) pari_err_TYPE("sylvestermatrix",y);
  if (varn(x) != varn(y)) pari_err_VAR("sylvestermatrix",x,y);
  return syl_RgM(x,y,1);
}

GEN
resultant2(GEN x, GEN y)
{
  GEN r = init_resultant(x,y);
  return r? r: RgX_resultant_sylvester(x,y);
}

/* let vx = main variable of x, v0 a variable of highest priority;
 * return a t_POL in variable v0:
 * if vx <= v, return subst(x, v, pol_x(v0))
 * if vx >  v, return scalarpol(x, v0) */
static GEN
fix_pol(GEN x, long v, long v0)
{
  long vx, tx = typ(x);
  if (tx != t_POL)
    vx = gvar(x);
  else
  { /* shortcut: almost nothing to do */
    vx = varn(x);
    if (v == vx)
    {
      if (v0 != v) { x = leafcopy(x); setvarn(x, v0); }
      return x;
    }
  }
  if (varncmp(v, vx) > 0)
  {
    x = gsubst(x, v, pol_x(v0));
    if (typ(x) != t_POL) vx = gvar(x);
    else
    {
      vx = varn(x);
      if (vx == v0) return x;
    }
  }
  if (varncmp(vx, v0) <= 0) pari_err_TYPE("polresultant", x);
  return scalarpol_shallow(x, v0);
}

/* resultant of x and y with respect to variable v, or with respect to their
 * main variable if v < 0. */
GEN
polresultant0(GEN x, GEN y, long v, long flag)
{
  pari_sp av = avma;

  if (v >= 0)
  {
    long v0 = fetch_var_higher();
    x = fix_pol(x,v, v0);
    y = fix_pol(y,v, v0);
  }
  switch(flag)
  {
    case 0: x=resultant(x,y); break;
    case 1: x=resultant2(x,y); break;
    case 2: x=RgX_resultant_all(x,y,NULL); break;
    default: pari_err_FLAG("polresultant");
  }
  if (v >= 0) (void)delete_var();
  return gc_upto(av,x);
}

static GEN
RgX_extresultant_FpX(GEN x, GEN y, GEN p, GEN *u, GEN *v)
{
  pari_sp av = avma;
  GEN r = FpX_extresultant(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p, u, v);
  if (signe(r) == 0) { *u = gen_0; *v = gen_0; return gc_const(av, gen_0); }
  if (u) *u = FpX_to_mod(*u, p);
  if (v) *v = FpX_to_mod(*v, p);
  return gc_gcdext(av, Fp_to_mod(r, p), u, v);
}

static GEN
RgX_extresultant_fast(GEN x, GEN y, GEN *U, GEN *V)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x, y, &p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return RgX_extresultant_FpX(x, y, p, U, V);
    default:       return NULL;
  }
}

GEN
polresultantext0(GEN x, GEN y, long v)
{
  GEN R = NULL, U, V;
  pari_sp av = avma;

  if (v >= 0)
  {
    long v0 = fetch_var_higher();
    x = fix_pol(x,v, v0);
    y = fix_pol(y,v, v0);
  }
  if (typ(x)==t_POL && typ(y)==t_POL)
    R = RgX_extresultant_fast(x, y, &U, &V);
  if (!R)
    R = subresext_i(x,y, &U,&V);
  if (v >= 0)
  {
    (void)delete_var();
    if (typ(U) == t_POL && varn(U) != v) U = poleval(U, pol_x(v));
    if (typ(V) == t_POL && varn(V) != v) V = poleval(V, pol_x(v));
  }
  return gc_GEN(av, mkvec3(U,V,R));
}
GEN
polresultantext(GEN x, GEN y) { return polresultantext0(x,y,-1); }

/*******************************************************************/
/*                                                                 */
/*             CHARACTERISTIC POLYNOMIAL USING RESULTANT           */
/*                                                                 */
/*******************************************************************/

static GEN
RgXQ_charpoly_FpXQ(GEN x, GEN T, GEN p, long v)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    r = Flx_to_ZX(Flxq_charpoly(RgX_to_Flx(x, pp), RgX_to_Flx(T, pp), pp));
  }
  else
    r = FpXQ_charpoly(RgX_to_FpX(x, p), RgX_to_FpX(T, p), p);
  r = FpX_to_mod(r, p); setvarn(r, v);
  return gc_upto(av, r);
}

static GEN
RgXQ_charpoly_fast(GEN x, GEN T, long v)
{
  GEN p, pol;
  long pa, t = RgX_type2(x,T, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZXQ_charpoly(x, T, v);
    case t_FRAC:
    {
      pari_sp av = avma;
      GEN cT;
      T = Q_primitive_part(T, &cT);
      T = QXQ_charpoly(x, T, v);
      if (cT) T = gc_upto(av, T); /* silly rare case */
      return T;
    }
    case t_INTMOD: return RgXQ_charpoly_FpXQ(x, T, p, v);
    default:       return NULL;
  }
}

/* (v - x)^d */
static GEN
caract_const(pari_sp av, GEN x, long v, long d)
{ return gc_upto(av, gpowgs(deg1pol_shallow(gen_1, gneg_i(x), v), d)); }

GEN
RgXQ_charpoly_i(GEN x, GEN T, long v)
{
  pari_sp av = avma;
  long d = degpol(T), dx = degpol(x), v0;
  GEN ch, L;
  if (dx >= degpol(T)) { x = RgX_rem(x, T); dx = degpol(x); }
  if (dx <= 0) return dx? pol_xn(d, v): caract_const(av, gel(x,2), v, d);

  v0 = fetch_var_higher();
  x = RgX_neg(x);
  gel(x,2) = gadd(gel(x,2), pol_x(v));
  setvarn(x, v0);
  T = leafcopy(T); setvarn(T, v0);
  ch = resultant(T, x);
  (void)delete_var();
  /* test for silly input: x mod (deg 0 polynomial) */
  if (typ(ch) != t_POL)
    pari_err_PRIORITY("RgXQ_charpoly", pol_x(v), "<", gvar(ch));
  L = leading_coeff(ch);
  if (!gequal1(L)) ch = RgX_Rg_div(ch, L);
  return gc_upto(av, ch);
}

/* return caract(Mod(x,T)) in variable v */
GEN
RgXQ_charpoly(GEN x, GEN T, long v)
{
  GEN ch = RgXQ_charpoly_fast(x, T, v);
  if (ch) return ch;
  return RgXQ_charpoly_i(x, T, v);
}

/* characteristic polynomial (in v) of x over nf, where x is an element of the
 * algebra nf[t]/(Q(t)) */
GEN
rnfcharpoly(GEN nf, GEN Q, GEN x, long v)
{
  const char *f = "rnfcharpoly";
  long dQ = degpol(Q);
  pari_sp av = avma;
  GEN T;

  if (v < 0) v = 0;
  nf = checknf(nf); T = nf_get_pol(nf);
  Q = RgX_nffix(f, T,Q,0);
  switch(typ(x))
  {
    case t_INT:
    case t_FRAC: return caract_const(av, x, v, dQ);
    case t_POLMOD:
      x = polmod_nffix2(f,T,Q, x,0);
      break;
    case t_POL:
      x = varn(x) == varn(T)? Rg_nffix(f,T,x,0): RgX_nffix(f, T,x,0);
      break;
    default: pari_err_TYPE(f,x);
  }
  if (typ(x) != t_POL) return caract_const(av, x, v, dQ);
  /* x a t_POL in variable vQ */
  if (degpol(x) >= dQ) x = RgX_rem(x, Q);
  if (dQ <= 1) return caract_const(av, constant_coeff(x), v, 1);
  return gc_GEN(av, lift_if_rational( RgXQ_charpoly(x, Q, v) ));
}

/*******************************************************************/
/*                                                                 */
/*                  GCD USING SUBRESULTANT                         */
/*                                                                 */
/*******************************************************************/
static int inexact(GEN x, int *simple);
static int
isinexactall(GEN x, int *simple)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
    if (inexact(gel(x,i), simple)) return 1;
  return 0;
}
/* return 1 if coeff explosion is not possible */
static int
inexact(GEN x, int *simple)
{
  int junk = 0;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: return 0;

    case t_REAL: case t_PADIC: case t_SER: return 1;

    case t_INTMOD:
    case t_FFELT:
      if (!*simple) *simple = 1;
      return 0;

    case t_COMPLEX:
      return inexact(gel(x,1), simple)
          || inexact(gel(x,2), simple);
    case t_QUAD:
      *simple = 0;
      return inexact(gel(x,2), &junk)
          || inexact(gel(x,3), &junk);

    case t_POLMOD:
      return isinexactall(gel(x,1), simple);
    case t_POL:
      *simple = -1;
      return isinexactall(x, &junk);
    case t_RFRAC:
      *simple = -1;
      return inexact(gel(x,1), &junk)
          || inexact(gel(x,2), &junk);
  }
  *simple = -1; return 0;
}

/* x monomial, y t_POL in the same variable */
static GEN
gcdmonome(GEN x, GEN y)
{
  pari_sp av = avma;
  long dx = degpol(x), e = RgX_valrem(y, &y);
  long i, l = lg(y);
  GEN t, v = cgetg(l, t_VEC);
  gel(v,1) = gel(x,dx+2);
  for (i = 2; i < l; i++) gel(v,i) = gel(y,i);
  t = content(v); /* gcd(lc(x), cont(y)) */
  t = simplify_shallow(t);
  if (dx < e) e = dx;
  return gc_upto(av, monomialcopy(t, e, varn(x)));
}

static GEN
RgX_gcd_FpX(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flx_gcd(RgX_to_Flx(x, pp),
                                  RgX_to_Flx(y, pp), pp));
  }
  else
    r = FpX_gcd(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgX_gcd_FpXQX(GEN x, GEN y, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("gcd", x, y);
  r = FpXQX_gcd(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p), T, p);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
RgX_gcd_FpXk(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r = FpXk_gcd(Rg_to_FpXk(x, p), Rg_to_FpXk(y, p), p);
  return gc_upto(av, gmul(r, gmodulsg(1,p)));
}

static GEN
RgX_liftred(GEN x, GEN T)
{ return RgXQX_red(liftpol_shallow(x), T); }

static GEN
RgX_gcd_ZXQX(GEN x, GEN y, GEN T)
{
  pari_sp av = avma;
  GEN r = ZXQX_gcd(RgX_liftred(x, T), RgX_liftred(y, T), T);
  return gc_GEN(av, QXQX_to_mod_shallow(r, T));
}

static GEN
RgX_gcd_QXQX(GEN x, GEN y, GEN T)
{
  pari_sp av = avma;
  GEN r = QXQX_gcd(RgX_liftred(x, T), RgX_liftred(y, T), T);
  return gc_GEN(av, QXQX_to_mod_shallow(r, T));
}

static GEN
RgX_gcd_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZX_gcd(x, y);
    case t_FRAC:   return QX_gcd(x, y);
    case t_FFELT:  return FFX_gcd(x, y, pol);
    case t_INTMOD: return RgX_gcd_FpX(x, y, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgX_gcd_FpXQX(x, y, pol, p);
    case RgX_type_code(t_POLMOD, t_INT):
                   return ZX_is_monic(pol)? RgX_gcd_ZXQX(x,y,pol): NULL;
    case RgX_type_code(t_POLMOD, t_FRAC):
                   return RgX_is_ZX(pol) && ZX_is_monic(pol) ?
                                            RgX_gcd_QXQX(x,y,pol): NULL;
    case  RgX_type_code(t_POL, t_INT):
                   return ZXk_gcd(x,y);
    case  RgX_type_code(t_POL, t_FRAC):
                   return QXk_gcd(x,y);
    case  RgX_type_code(t_POL, t_INTMOD):
                   return RgX_gcd_FpXk(x,y,p);
    default:       return NULL;
  }
}

/* x, y are t_POL in the same variable */
GEN
RgX_gcd(GEN x, GEN y)
{
  long dx, dy;
  pari_sp av, av1;
  GEN d, g, h, p1, p2, u, v;
  int simple = 0;
  GEN z = RgX_gcd_fast(x, y);
  if (z) return z;
  if (isexactzero(y)) return RgX_copy(x);
  if (isexactzero(x)) return RgX_copy(y);
  if (RgX_is_monomial(x)) return gcdmonome(x,y);
  if (RgX_is_monomial(y)) return gcdmonome(y,x);
  if (isinexactall(x,&simple) || isinexactall(y,&simple))
  {
    av = avma; u = ggcd(content(x), content(y));
    return gc_upto(av, scalarpol(u, varn(x)));
  }

  av = avma;
  if (simple > 0) x = RgX_gcd_simple(x,y);
  else
  {
    dx = lg(x); dy = lg(y);
    if (dx < dy) { swap(x,y); lswap(dx,dy); }
    if (dy==3)
    {
      d = ggcd(gel(y,2), content(x));
      return gc_upto(av, scalarpol(d, varn(x)));
    }
    u = primitive_part(x, &p1); if (!p1) p1 = gen_1;
    v = primitive_part(y, &p2); if (!p2) p2 = gen_1;
    d = ggcd(p1,p2);
    av1 = avma;
    g = h = gen_1;
    for(;;)
    {
      GEN r = RgX_pseudorem(u,v);
      long degq, du, dv, dr = lg(r);

      if (!signe(r)) break;
      if (dr <= 3)
      {
        set_avma(av1);
        return gc_upto(av, scalarpol(d, varn(x)));
      }
      du = lg(u); dv = lg(v); degq = du-dv;
      u = v; p1 = g; g = leading_coeff(u);
      switch(degq)
      {
        case 0: break;
        case 1:
          p1 = gmul(h,p1); h = g; break;
        default:
          p1 = gmul(gpowgs(h,degq), p1);
          h = gdiv(gpowgs(g,degq), gpowgs(h,degq-1));
      }
      v = RgX_Rg_div(r,p1);
      if (gc_needed(av1,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"RgX_gcd, dr = %ld", degpol(r));
        (void)gc_all(av1,4, &u,&v,&g,&h);
      }
    }
    x = RgX_Rg_mul(primpart(v), d);
  }
  if (must_negate(x)) x = RgX_neg(x);
  return gc_upto(av,x);
}

/* disc P = (-1)^(n(n-1)/2) lc(P)^(n - deg P' - 2) Res(P,P'), n = deg P */
static GEN
RgX_disc_i(GEN P)
{
  long n = degpol(P), dd;
  GEN N, D, L, y;
  if (!signe(P) || !n) return Rg_get_0(P);
  if (n == 1) return Rg_get_1(P);
  if (n == 2) {
    GEN a = gel(P,4), b = gel(P,3), c = gel(P,2);
    return gsub(gsqr(b), gmul2n(gmul(a,c),2));
  }
  y = RgX_deriv(P);
  N = characteristic(P);
  if (signe(N)) y = gmul(y, mkintmod(gen_1,N));
  if (!signe(y)) return Rg_get_0(y);
  dd = n - 2 - degpol(y);
  if (isinexact(P))
    D = resultant2(P,y);
  else
  {
    D = RgX_resultant_all(P, y, NULL);
    if (D == gen_0) return Rg_get_0(y);
  }
  L = leading_coeff(P);
  if (dd && !gequal1(L)) D = (dd == -1)? gdiv(D, L): gmul(D, gpowgs(L, dd));
  if (n & 2) D = gneg(D);
  return D;
}

static GEN
RgX_disc_FpX(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN r = FpX_disc(RgX_to_FpX(x, p), p);
  return gc_upto(av, Fp_to_mod(r, p));
}

static GEN
RgX_disc_FpXQX(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  r = FpXQX_disc(RgX_to_FpXQX(x, T, p), T, p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgX_disc_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgX_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZX_disc(x);
    case t_FRAC:   return QX_disc(x);
    case t_FFELT:  return FFX_disc(x, pol);
    case t_INTMOD: return RgX_disc_FpX(x, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgX_disc_FpXQX(x, pol, p);
    default:       return NULL;
  }
}

GEN
RgX_disc(GEN x)
{
  pari_sp av;
  GEN z = RgX_disc_fast(x);
  if (z) return z;
  av = avma;
  return gc_upto(av, RgX_disc_i(x));
}

GEN
poldisc0(GEN x, long v)
{
  long v0, tx = typ(x);
  pari_sp av;
  GEN D;
  if (tx == t_POL && (v < 0 || v == varn(x))) return RgX_disc(x);
  switch(tx)
  {
    case t_QUAD:
      return quad_disc(x);
    case t_POLMOD:
      if (v >= 0 && varn(gel(x,1)) != v) break;
      return RgX_disc(gel(x,1));
    case t_QFB:
      return icopy(qfb_disc(x));
    case t_VEC: case t_COL: case t_MAT:
      pari_APPLY_same(poldisc0(gel(x,i), v));
  }
  if (v < 0) pari_err_TYPE("poldisc",x);
  av = avma; v0 = fetch_var_higher();
  x = fix_pol(x,v, v0);
  D = RgX_disc(x); (void)delete_var();
  return gc_upto(av, D);
}

GEN
reduceddiscsmith(GEN x)
{
  long j, n = degpol(x);
  pari_sp av = avma;
  GEN xp, M;

  if (typ(x) != t_POL) pari_err_TYPE("poldiscreduced",x);
  if (n<=0) pari_err_CONSTPOL("poldiscreduced");
  RgX_check_ZX(x,"poldiscreduced");
  if (!gequal1(gel(x,n+2)))
    pari_err_IMPL("nonmonic polynomial in poldiscreduced");
  M = cgetg(n+1,t_MAT);
  xp = ZX_deriv(x);
  for (j=1; j<=n; j++)
  {
    gel(M,j) = RgX_to_RgC(xp, n);
    if (j<n) xp = RgX_rem(RgX_shift_shallow(xp, 1), x);
  }
  return gc_upto(av, ZM_snf(M));
}

/***********************************************************************/
/**                                                                   **/
/**                       STURM ALGORITHM                             **/
/**              (number of real roots of x in [a,b])                 **/
/**                                                                   **/
/***********************************************************************/
static GEN
R_to_Q_up(GEN x)
{
  long e;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_INFINITY: return x;
    case t_REAL:
      x = mantissa_real(x,&e);
      return gmul2n(addiu(x,1), -e);
    default: pari_err_TYPE("R_to_Q_up", x);
      return NULL; /* LCOV_EXCL_LINE */
  }
}
static GEN
R_to_Q_down(GEN x)
{
  long e;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_INFINITY: return x;
    case t_REAL:
      x = mantissa_real(x,&e);
      return gmul2n(subiu(x,1), -e);
    default: pari_err_TYPE("R_to_Q_down", x);
      return NULL; /* LCOV_EXCL_LINE */
  }
}

static long
sturmpart_i(GEN x, GEN ab)
{
  long tx = typ(x);
  if (gequal0(x)) pari_err_ROOTS0("sturm");
  if (tx != t_POL)
  {
    if (is_real_t(tx)) return 0;
    pari_err_TYPE("sturm",x);
  }
  if (lg(x) == 3) return 0;
  if (!RgX_is_ZX(x)) x = RgX_rescale_to_int(x);
  (void)ZX_gcd_all(x, ZX_deriv(x), &x);
  if (ab)
  {
    GEN A, B;
    if (typ(ab) != t_VEC || lg(ab) != 3) pari_err_TYPE("RgX_sturmpart", ab);
    A = R_to_Q_down(gel(ab,1));
    B = R_to_Q_up(gel(ab,2));
    ab = mkvec2(A, B);
  }
  return ZX_sturmpart(x, ab);
}
/* Deprecated: RgX_sturmpart() should be preferred  */
long
sturmpart(GEN x, GEN a, GEN b)
{
  pari_sp av = avma;
  if (!b && a && typ(a) == t_VEC) return RgX_sturmpart(x, a);
  if (!a) a = mkmoo();
  if (!b) b = mkoo();
  return gc_long(av, sturmpart_i(x, mkvec2(a,b)));
}
long
RgX_sturmpart(GEN x, GEN ab)
{ pari_sp av = avma; return gc_long(av, sturmpart_i(x, ab)); }

/***********************************************************************/
/**                                                                   **/
/**                        GENERIC EXTENDED GCD                       **/
/**                                                                   **/
/***********************************************************************/
/* assume typ(x) = typ(y) = t_POL */
static GEN
RgXQ_inv_i(GEN x, GEN y)
{
  long vx=varn(x), vy=varn(y);
  pari_sp av;
  GEN u, v, d;

  while (vx != vy)
  {
    if (varncmp(vx,vy) > 0)
    {
      d = (vx == NO_VARIABLE)? ginv(x): gred_rfrac_simple(gen_1, x);
      return scalarpol(d, vy);
    }
    if (lg(x)!=3) pari_err_INV("RgXQ_inv",mkpolmod(x,y));
    x = gel(x,2); vx = gvar(x);
  }
  av = avma; d = subresext_i(x,y,&u,&v/*junk*/);
  if (gequal0(d)) pari_err_INV("RgXQ_inv",mkpolmod(x,y));
  d = gdiv(u,d);
  if (typ(d) != t_POL || varn(d) != vy) d = scalarpol(d, vy);
  return gc_upto(av, d);
}

/*Assume x is a polynomial and y is not */
static GEN
scalar_bezout(GEN x, GEN y, GEN *U, GEN *V)
{
  long vx = varn(x);
  int xis0 = signe(x)==0, yis0 = gequal0(y);
  if (xis0 && yis0) { *U = *V = pol_0(vx); return pol_0(vx); }
  if (yis0) { *U=pol_1(vx); *V = pol_0(vx); return RgX_copy(x);}
  *U=pol_0(vx); *V= ginv(y); return pol_1(vx);
}
/* Assume x==0, y!=0 */
static GEN
zero_bezout(GEN y, GEN *U, GEN *V)
{
  *U=gen_0; *V = ginv(y); return gen_1;
}

GEN
gbezout(GEN x, GEN y, GEN *u, GEN *v)
{
  long tx=typ(x), ty=typ(y), vx;
  if (tx == t_INT && ty == t_INT) return bezout(x,y,u,v);
  if (tx != t_POL)
  {
    if (ty == t_POL)
      return scalar_bezout(y,x,v,u);
    else
    {
      int xis0 = gequal0(x), yis0 = gequal0(y);
      if (xis0 && yis0) { *u = *v = gen_0; return gen_0; }
      if (xis0) return zero_bezout(y,u,v);
      else return zero_bezout(x,v,u);
    }
  }
  else if (ty != t_POL) return scalar_bezout(x,y,u,v);
  vx = varn(x);
  if (vx != varn(y))
    return varncmp(vx, varn(y)) < 0? scalar_bezout(x,y,u,v)
                                   : scalar_bezout(y,x,v,u);
  return RgX_extgcd(x,y,u,v);
}

GEN
gcdext0(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  gel(z,3) = gbezout(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                    GENERIC (modular) INVERSE                    */
/*                                                                 */
/*******************************************************************/

GEN
ginvmod(GEN x, GEN y)
{
  long tx=typ(x);

  switch(typ(y))
  {
    case t_POL:
      if (tx==t_POL) return RgXQ_inv(x,y);
      if (is_scalar_t(tx)) return ginv(x);
      break;
    case t_INT:
      if (tx==t_INT) return Fp_inv(x,y);
      if (tx==t_POL) return gen_0;
  }
  pari_err_TYPE2("ginvmod",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/***********************************************************************/
/**                                                                   **/
/**                         NEWTON POLYGON                            **/
/**                                                                   **/
/***********************************************************************/

/* assume leading coeff of x is nonzero */
GEN
newtonpoly(GEN x, GEN p)
{
  pari_sp av = avma;
  long n, ind, a, b;
  GEN y, vval;

  if (typ(x) != t_POL) pari_err_TYPE("newtonpoly",x);
  n = degpol(x); if (n<=0) return cgetg(1,t_VEC);
  vval = new_chunk(n+1);
  y = cgetg(n+1,t_VEC); x += 2; /* now x[i] = term of degree i */
  for (a = 0; a <= n; a++) vval[a] = gvaluation(gel(x,a),p);
  for (a = 0, ind = 1; a < n; a++)
  {
    if (vval[a] != LONG_MAX) break;
    gel(y,ind++) = mkoo();
  }
  for (b = a+1; b <= n; a = b, b = a+1)
  {
    long u1, u2, c;
    while (vval[b] == LONG_MAX) b++;
    u1 = vval[a] - vval[b];
    u2 = b - a;
    for (c = b+1; c <= n; c++)
    {
      long r1, r2;
      if (vval[c] == LONG_MAX) continue;
      r1 = vval[a] - vval[c];
      r2 = c - a;
      if (u1*r2 <= u2*r1) { u1 = r1; u2 = r2; b = c; }
    }
    while (ind <= b) gel(y,ind++) = sstoQ(u1,u2);
  }
  stackdummy((pari_sp)vval, av); return y;
}

static GEN
RgXQ_mul_FpXQ(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flxq_mul(RgX_to_Flx(x, pp),
                RgX_to_Flx(y, pp), RgX_to_Flx(T, pp), pp));
  }
  else
    r = FpXQ_mul(RgX_to_FpX(x, p), RgX_to_FpX(y, p), RgX_to_FpX(T, p), p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgXQ_sqr_FpXQ(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flxq_sqr(RgX_to_Flx(x, pp),
                                   RgX_to_Flx(y, pp), pp));
  }
  else
    r = FpXQ_sqr(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgXQ_inv_FpXQ(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flx_to_ZX_inplace(Flxq_inv(RgX_to_Flx(x, pp),
                                   RgX_to_Flx(y, pp), pp));
  }
  else
    r = FpXQ_inv(RgX_to_FpX(x, p), RgX_to_FpX(y, p), p);
  return gc_upto(av, FpX_to_mod(r, p));
}

static GEN
RgXQ_mul_FpXQXQ(GEN x, GEN y, GEN S, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r;
  GEN T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("*",x,y);
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    GEN Tp = ZX_to_Flx(T, pp);
    r = FlxX_to_ZXX(FlxqXQ_mul(RgX_to_FlxqX(x, Tp, pp),
                               RgX_to_FlxqX(y, Tp, pp),
                               RgX_to_FlxqX(S, Tp, pp), Tp, pp));
  }
  else
    r = FpXQXQ_mul(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p),
                   RgX_to_FpXQX(S, T, p), T, p);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
RgXQ_sqr_FpXQXQ(GEN x, GEN y, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r;
  GEN T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("*",x,x);
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    GEN Tp = ZX_to_Flx(T, pp);
    r = FlxX_to_ZXX(FlxqXQ_sqr(RgX_to_FlxqX(x, Tp, pp),
                               RgX_to_FlxqX(y, Tp, pp), Tp, pp));
  }
  else
    r = FpXQXQ_sqr(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p), T, p);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
RgXQ_inv_FpXQXQ(GEN x, GEN y, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r;
  GEN T = RgX_to_FpX(pol, p);
  if (signe(T)==0) pari_err_OP("^",x,gen_m1);
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    GEN Tp = ZX_to_Flx(T, pp);
    r = FlxX_to_ZXX(FlxqXQ_inv(RgX_to_FlxqX(x, Tp, pp),
                               RgX_to_FlxqX(y, Tp, pp), Tp, pp));
  }
  else
    r = FpXQXQ_inv(RgX_to_FpXQX(x, T, p), RgX_to_FpXQX(y, T, p), T, p);
  return gc_upto(av, FpXQX_to_mod(r, T, p));
}

static GEN
RgXQ_mul_fast(GEN x, GEN y, GEN T)
{
  GEN p, pol;
  long pa;
  long t = RgX_type3(x,y,T, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZX_is_monic(T) ? ZXQ_mul(x,y,T): NULL;
    case t_FRAC:   return RgX_is_ZX(T) && ZX_is_monic(T) ? QXQ_mul(x,y,T): NULL;
    case t_FFELT:  return FFXQ_mul(x, y, T, pol);
    case t_INTMOD: return RgXQ_mul_FpXQ(x, y, T, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgXQ_mul_FpXQXQ(x, y, T, pol, p);
    default:       return NULL;
  }
}

GEN
RgXQ_mul(GEN x, GEN y, GEN T)
{
  GEN z = RgXQ_mul_fast(x, y, T);
  if (!z) z = RgX_rem(RgX_mul(x, y), T);
  return z;
}

static GEN
RgXQ_sqr_fast(GEN x, GEN T)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x, T, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZX_is_monic(T) ? ZXQ_sqr(x,T): NULL;
    case t_FRAC:   return RgX_is_ZX(T) && ZX_is_monic(T) ? QXQ_sqr(x,T): NULL;
    case t_FFELT:  return FFXQ_sqr(x, T, pol);
    case t_INTMOD: return RgXQ_sqr_FpXQ(x, T, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgXQ_sqr_FpXQXQ(x, T, pol, p);
    default:       return NULL;
  }
}

GEN
RgXQ_sqr(GEN x, GEN T)
{
  GEN z = RgXQ_sqr_fast(x, T);
  if (!z) z = RgX_rem(RgX_sqr(x), T);
  return z;
}

static GEN
RgXQ_inv_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgX_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return QXQ_inv(x,y);
    case t_FRAC:   return RgX_is_ZX(y)? QXQ_inv(x,y): NULL;
    case t_FFELT:  return FFXQ_inv(x, y, pol);
    case t_INTMOD: return RgXQ_inv_FpXQ(x, y, p);
    case RgX_type_code(t_POLMOD, t_INTMOD):
                   return RgXQ_inv_FpXQXQ(x, y, pol, p);
    default:       return NULL;
  }
}

GEN
RgXQ_inv(GEN x, GEN y)
{
  GEN z = RgXQ_inv_fast(x, y);
  if (!z) z = RgXQ_inv_i(x, y);
  return z;
}
