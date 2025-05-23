/* Copyright (C) 2012  The PARI group.

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

/* Not so fast arithmetic with polynomials over FpX */

/*******************************************************************/
/*                                                                 */
/*                             FpXX                                */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/

static GEN
to_ZX(GEN a, long v) { return typ(a)==t_INT? scalarpol_shallow(a,v): a; }

static ulong
to_FlxqX(GEN P, GEN Q, GEN T, GEN p, GEN *pt_P, GEN *pt_Q, GEN *pt_T)
{
  ulong pp = uel(p,2);
  long v = get_FpX_var(T);
  *pt_P = ZXX_to_FlxX(P, pp, v);
  if (pt_Q) *pt_Q = ZXX_to_FlxX(Q, pp, v);
  *pt_T = ZXT_to_FlxT(T, pp);
  return pp;
}

static GEN
ZXX_copy(GEN a) { return gcopy(a); }

GEN
FpXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i), c;
    if (typ(zi)==t_INT)
      c = modii(zi,p);
    else
    {
      pari_sp av = avma;
      c = FpX_red(zi,p);
      switch(lg(c)) {
        case 2: set_avma(av); c = gen_0; break;
        case 3: c = gc_GEN(av, gel(c,2)); break;
      }
    }
    gel(res,i) = c;
  }
  return FpXX_renormalize(res,lg(res));
}
GEN
FpXX_add(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fq_add(gel(x,i), gel(y,i), NULL, p);
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  return FpXX_renormalize(z, lz);
}
GEN
FpXX_sub(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ly; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<lx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ly; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z, lz);
}

static GEN
FpXX_subspec(GEN x, GEN y, GEN p, long nx, long ny)
{
  long i,lz;
  GEN z;
  if (ny <= nx)
  {
    lz = nx+2; z = cgetg(lz, t_POL);
    for (i=0; i<ny; i++) gel(z,i+2) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<nx; i++) gel(z,i+2) = gcopy(gel(x,i));
  }
  else
  {
    lz = ny+2; z = cgetg(lz, t_POL);
    for (i=0; i<nx; i++) gel(z,i+2) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ny; i++) gel(z,i+2) = Fq_neg(gel(y,i), NULL, p);
  }
  z[1] = 0; return FpXX_renormalize(z, lz);
}

GEN
FpXX_neg(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fq_neg(gel(x,i), NULL, p);
  return FpXX_renormalize(y, lx);
}

GEN
FpXX_Fp_mul(GEN P, GEN u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,u,p): FpX_Fp_mul(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_mulu(GEN P, ulong u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,u,p): FpX_mulu(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_halve(GEN P, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_halve(x,p): FpX_halve(x,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_deriv(GEN P, GEN p)
{
  long i, l = lg(P)-1;
  GEN res;

  if (l < 3) return pol_0(varn(P));
  res = cgetg(l, t_POL);
  res[1] = P[1];
  for (i=2; i<l ; i++)
  {
    GEN x = gel(P,i+1);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,i-1,p): FpX_mulu(x,i-1,p);
  }
  return FpXX_renormalize(res, l);
}

GEN
FpXX_integ(GEN P, GEN p)
{
  long i, l = lg(P);
  GEN res;

  if (l == 2) return pol_0(varn(P));
  res = cgetg(l+1, t_POL);
  res[1] = P[1];
  gel(res,2) = gen_0;
  for (i=3; i<=l ; i++)
  {
    GEN x = gel(P,i-1);
    if (signe(x))
    {
      GEN i1 = Fp_inv(utoi(i-2), p);
      gel(res,i) = typ(x)==t_INT? Fp_mul(x,i1,p): FpX_Fp_mul(x,i1,p);
    } else
      gel(res,i) = gen_0;
  }
  return FpXX_renormalize(res, l+1);
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/

static GEN
get_FpXQX_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

GEN
random_FpXQX(long d1, long v, GEN T, GEN p)
{
  long dT = get_FpX_degree(T), vT = get_FpX_var(T);
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_FpX(dT, vT, p);
  return FpXQX_renormalize(y,d);
}

/*Not stack clean*/
GEN
Kronecker_to_FpXQX(GEN Z, GEN T, GEN p)
{
  long i,j,lx,l, N = (get_FpX_degree(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL), z = FpX_red(Z, p);
  t[1] = evalvarn(get_FpX_var(T));
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  return FpXQX_renormalize(x, i+1);
}

GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    if (typ(gel(z,i)) == t_INT)
      gel(res,i) = modii(gel(z,i),p);
    else
      gel(res,i) = FpXQ_red(gel(z,i),T,p);
  return FpXQX_renormalize(res,l);
}

GEN
FpXQXV_red(GEN x, GEN T, GEN p)
{ pari_APPLY_type(t_VEC, FpXQX_red(gel(x,i), T, p)) }

GEN
FpXQXT_red(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_POL)
    return FpXQX_red(x, T, p);
  else
    pari_APPLY_type(t_VEC, FpXQXT_red(gel(x,i), T, p))
}

static GEN
to_intmod(GEN x, GEN p) { retmkintmod(modii(x, p), p); }

GEN
FpXQX_to_mod(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN x;
  if (l == 2)
  {
    x = cgetg(3, t_POL); x[1] = z[1];
    p = icopy(p); T = FpX_to_mod_raw(T, p);
    gel(x,2) = mkpolmod(mkintmod(gen_0, p), T);
    return x;
  }
  x = cgetg(l, t_POL); x[1] = z[1];
  p = icopy(p); T = FpX_to_mod_raw(T, p);
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i);
    gel(x,i) = typ(zi) == t_POL? mkpolmod(FpX_to_mod_raw(zi, p), T)
                               : to_intmod(zi, p);
  }
  return normalizepol_lg(x,l);
}

static GEN
FpXQX_to_mod_raw(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN x;

  if (l == 2)
  {
    x = cgetg(3, t_POL); x[1] = z[1];
    p = icopy(p);
    gel(x,2) = mkpolmod(mkintmod(gen_0, p), T);
    return x;
  }
  x = cgetg(l, t_POL); x[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i);
    gel(x,i) = typ(zi) == t_POL? mkpolmod(FpX_to_mod_raw(zi, p), T)
                               : to_intmod(zi, p);
  }
  return normalizepol_lg(x,l);
}

INLINE GEN
FqX_to_mod_raw(GEN f, GEN T, GEN p)
{ return T?FpXQX_to_mod_raw(f, T, p): FpX_to_mod_raw(f, p); }

static GEN
FqXC_to_mod_raw(GEN x, GEN T, GEN p)
{ pari_APPLY_type(t_COL, FqX_to_mod_raw(gel(x,i), T, p)) }

GEN
FqXC_to_mod(GEN z, GEN T, GEN p)
{
  GEN x;
  long i,l = lg(z);
  if (!T) return FpXC_to_mod(z, p);
  x = cgetg(l, t_COL);
  if (l == 1) return x;
  p = icopy(p);
  T = FpX_to_mod_raw(T, p);
  for (i=1; i<l; i++)
    gel(x,i) = FqX_to_mod_raw(gel(z, i), T, p);
  return x;
}

GEN
FqXM_to_mod(GEN z, GEN T, GEN p)
{
  GEN x;
  long i,l = lg(z);
  if (!T) return FpXM_to_mod(z, p);
  x = cgetg(l, t_MAT);
  if (l == 1) return x;
  p = icopy(p);
  T = FpX_to_mod_raw(T, p);
  for (i=1; i<l; i++)
    gel(x,i) = FqXC_to_mod_raw(gel(z, i), T, p);
  return x;
}

static int
ZXX_is_ZX_spec(GEN a,long na)
{
  long i;
  for(i=0;i<na;i++)
    if(typ(gel(a,i))!=t_INT) return 0;
  return 1;
}

static int
ZXX_is_ZX(GEN a) { return ZXX_is_ZX_spec(a+2,lgpol(a)); }

static GEN
FpXX_FpX_mulspec(GEN P, GEN U, GEN p, long v, long lU)
{
  long i, lP =lg(P);
  GEN res;
  res = cgetg(lP, t_POL); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN Pi = gel(P,i);
    gel(res,i) = typ(Pi)==t_INT? FpX_Fp_mulspec(U, Pi, p, lU):
                                 FpX_mulspec(U, Pi+2, p, lU, lgpol(Pi));
    setvarn(gel(res,i),v);
  }
  return FpXQX_renormalize(res,lP);
}

GEN
FpXX_FpX_mul(GEN P, GEN U, GEN p)
{ return FpXX_FpX_mulspec(P,U+2,p,varn(U),lgpol(U)); }

static GEN
FpXY_FpY_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  long v = get_FpX_var(T);
  GEN z = RgXY_swapspec(x,get_FpX_degree(T)-1,v,lx);
  z = FpXX_FpX_mulspec(z,y,p,v,ly);
  z = RgXY_swapspec(z+2,lx+ly+3,v,lgpol(z));
  return gc_GEN(av,z);
}

static GEN
FpXQX_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long n;
  if (ZXX_is_ZX_spec(y,ly))
  {
    if (ZXX_is_ZX_spec(x,lx))
      return FpX_mulspec(x,y,p,lx,ly);
    else
      return FpXY_FpY_mulspec(x,y,T,p,lx,ly);
  } else if (ZXX_is_ZX_spec(x,lx))
      return FpXY_FpY_mulspec(y,x,T,p,ly,lx);
  n = get_FpX_degree(T);
  kx = RgXX_to_Kronecker_spec(x, lx, n);
  ky = RgXX_to_Kronecker_spec(y, ly, n);
  z = Kronecker_to_FpXQX(ZX_mul(ky,kx), T, p);
  return gc_upto(av, z);
}

GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  GEN z = FpXQX_mulspec(x+2,y+2,T,p,lgpol(x),lgpol(y));
  setvarn(z,varn(x)); return z;
}

GEN
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  if (ZXX_is_ZX(x)) return ZX_sqr(x);
  kx= RgXX_to_Kronecker(x, get_FpX_degree(T));
  z = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return gc_upto(av, z);
}

GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res;
  res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? FpX_Fp_mul(U, gel(P,i), p):
                                       FpXQ_mul(U, gel(P,i), T,p);
  return FpXQX_renormalize(res,lP);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
static GEN
FpXQX_divrem_basecase(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx = varn(x), dx = degpol(x), dy = degpol(y), dy1, dz, i, j, sx, lr;
  pari_sp av0, av;
  GEN z, p1, rem, lead;

  if (!signe(y)) pari_err_INV("FpX_divrem",y);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { set_avma(av0); return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_coeff(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (gequal1(lead)) return FpXQX_red(x,T,p);
    av0 = avma; x = FqX_Fq_mul(x, Fq_inv(lead, T,p), T,p);
    return gc_upto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  lead = gequal1(lead)? NULL: gclone(Fq_inv(lead,T,p));
  set_avma(av0);
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;
  for (dy1=dy-1; dy1>=0 && !signe(gel(y, dy1)); dy1--);

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gc_upto(av, Fq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy1; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    if (lead) p1 = Fq_mul(p1, lead, NULL,p);
    gel(z,i-dy) = gc_upto(av, Fq_red(p1,T,p));
  }
  if (!pr) { guncloneNULL(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=maxss(0,i-dy1); j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    p1 = Fq_red(p1, T, p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    set_avma(av);
  }
  if (pr == ONLY_DIVIDES)
  {
    guncloneNULL(lead);
    if (sx) return gc_NULL(av0);
    return gc_const((pari_sp)rem, z-2);
  }
  lr=i+3; rem -= lr; av = (pari_sp)rem;
  rem[0] = evaltyp(t_POL) | _evallg(lr);
  rem[1] = z[-1];
  rem += 2; gel(rem,i) = gc_upto(av, p1);
  for (i--; i>=0; i--)
  {
    av = avma; p1 = gel(x,i);
    for (j=maxss(0,i-dy1); j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j), NULL,p), NULL,p);
    gel(rem,i) = gc_upto(av, Fq_red(p1, T, p));
  }
  rem -= 2;
  guncloneNULL(lead);
  if (!sx) (void)FpXQX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gc_upto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
FpXQX_addmulmul(GEN u, GEN v, GEN x, GEN y, GEN T, GEN p)
{
  return FpXX_add(FpXQX_mul(u, x, T, p),FpXQX_mul(v, y, T, p), p);
}

static GEN
FpXQXM_FpXQX_mul2(GEN M, GEN x, GEN y, GEN T, GEN p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = FpXQX_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, T, p);
  gel(res, 2) = FpXQX_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, T, p);
  return res;
}

static GEN
FpXQXM_mul2(GEN A, GEN B, GEN T, GEN p)
{
  GEN A11=gcoeff(A,1,1),A12=gcoeff(A,1,2), B11=gcoeff(B,1,1),B12=gcoeff(B,1,2);
  GEN A21=gcoeff(A,2,1),A22=gcoeff(A,2,2), B21=gcoeff(B,2,1),B22=gcoeff(B,2,2);
  GEN M1 = FpXQX_mul(FpXX_add(A11,A22, p), FpXX_add(B11,B22, p), T, p);
  GEN M2 = FpXQX_mul(FpXX_add(A21,A22, p), B11, T, p);
  GEN M3 = FpXQX_mul(A11, FpXX_sub(B12,B22, p), T, p);
  GEN M4 = FpXQX_mul(A22, FpXX_sub(B21,B11, p), T, p);
  GEN M5 = FpXQX_mul(FpXX_add(A11,A12, p), B22, T, p);
  GEN M6 = FpXQX_mul(FpXX_sub(A21,A11, p), FpXX_add(B11,B12, p), T, p);
  GEN M7 = FpXQX_mul(FpXX_sub(A12,A22, p), FpXX_add(B21,B22, p), T, p);
  GEN T1 = FpXX_add(M1,M4, p), T2 = FpXX_sub(M7,M5, p);
  GEN T3 = FpXX_sub(M1,M2, p), T4 = FpXX_add(M3,M6, p);
  retmkmat22(FpXX_add(T1,T2, p), FpXX_add(M3,M5, p),
             FpXX_add(M2,M4, p), FpXX_add(T3,T4, p));
}
/* Return [0,1;1,-q]*M */
static GEN
FpXQX_FpXQXM_qmul(GEN q, GEN M, GEN T, GEN p)
{
  GEN u = FpXQX_mul(gcoeff(M,2,1), q, T, p);
  GEN v = FpXQX_mul(gcoeff(M,2,2), q, T, p);
  retmkmat22(gcoeff(M,2,1), gcoeff(M,2,2),
    FpXX_sub(gcoeff(M,1,1), u, p), FpXX_sub(gcoeff(M,1,2), v, p));
}

static GEN
matid2_FpXQXM(long v)
{ retmkmat22(pol_1(v),pol_0(v),pol_0(v),pol_1(v)); }

static GEN
matJ2_FpXQXM(long v)
{ retmkmat22(pol_0(v),pol_1(v),pol_1(v),pol_0(v)); }

static GEN
FpXX_shift(GEN a, long n) { return RgX_shift_shallow(a, n); }

INLINE GEN
FpXXn_red(GEN a, long n) { return RgXn_red_shallow(a, n); }

/* Fast resultant formula from William Hart in Flint <http://flintlib.org/> */

struct FpXQX_res
{
   GEN res, lc;
   long deg0, deg1, off;
};

INLINE void
FpXQX_halfres_update(long da, long db, long dr, GEN T, GEN p, struct FpXQX_res *res)
{
  if (dr >= 0)
  {
    if (!ZX_equal1(res->lc))
    {
      res->lc  = FpXQ_powu(res->lc, da - dr, T, p);
      res->res = FpXQ_mul(res->res, res->lc, T, p);
    }
    if (both_odd(da + res->off, db + res->off))
      res->res = FpX_neg(res->res, p);
  } else
  {
    if (db == 0)
    {
      if (!ZX_equal1(res->lc))
      {
          res->lc  = FpXQ_powu(res->lc, da, T, p);
          res->res = FpXQ_mul(res->res, res->lc, T, p);
      }
    } else
      res->res = pol_0(get_FpX_var(T));
  }
}

static GEN
FpXQX_halfres_basecase(GEN a, GEN b, GEN T, GEN p, GEN *pa, GEN *pb, struct FpXQX_res *res)
{
  pari_sp av=avma;
  GEN u,u1,v,v1, M;
  long vx = varn(a), vT = get_FpX_var(T), n = lgpol(a)>>1;
  u1 = v = pol_0(vx);
  u = v1 = pol_1(vx);
  while (lgpol(b)>n)
  {
    GEN r, q;
    q = FpXQX_divrem(a,b, T, p, &r);
    if (res)
    {
      long da = degpol(a), db=degpol(b), dr = degpol(r);
      res->lc = to_ZX(gel(b,db+2),vT);
      if (dr >= n)
        FpXQX_halfres_update(da, db, dr, T, p, res);
      else
      {
        res->deg0 = da;
        res->deg1 = db;
      }
    }
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = FpXX_sub(u1, FpXQX_mul(u, q, T, p), p);
    v1 = FpXX_sub(v1, FpXQX_mul(v, q, T, p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_halfgcd (d = %ld)",degpol(b));
      if (res)
        (void)gc_all(av, 8, &a,&b,&u1,&v1,&u,&v,&res->res,&res->lc);
      else
        (void)gc_all(av, 6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  M = mkmat22(u,v,u1,v1); *pa = a; *pb = b;
  return res ? gc_all(av, 5, &M, pa, pb, &res->res, &res->lc)
             : gc_all(av, 3, &M, pa, pb);
}

static GEN FpXQX_halfres_i(GEN x, GEN y, GEN T, GEN p, GEN *a, GEN *b, struct FpXQX_res *res);

static GEN
FpXQX_halfres_split(GEN x, GEN y, GEN T, GEN p, GEN *a, GEN *b, struct FpXQX_res *res)
{
  pari_sp av = avma;
  GEN Q, R, S, V1, V2;
  GEN x1, y1, r, q;
  long l = lgpol(x), n = l>>1, k, vT = get_FpX_var(T);
  if (lgpol(y) <= n)
    { *a = RgX_copy(x); *b = RgX_copy(y); return matid2_FpXQXM(varn(x)); }
  if (res)
  {
     res->lc = to_ZX(leading_coeff(y), vT);
     res->deg0 -= n;
     res->deg1 -= n;
     res->off += n;
  }
  R = FpXQX_halfres_i(FpXX_shift(x,-n),FpXX_shift(y,-n), T, p, a, b, res);
  if (res)
  {
    res->off -= n;
    res->deg0 += n;
    res->deg1 += n;
  }
  V1 = FpXQXM_FpXQX_mul2(R, Flxn_red(x,n), Flxn_red(y,n), T, p);
  x1 = FpXX_add(FpXX_shift(*a,n), gel(V1,1), p);
  y1 = FpXX_add(FpXX_shift(*b,n), gel(V1,2), p);
  if (lgpol(y1) <= n)
  {
    *a = x1; *b = y1;
    return res ? gc_all(av, 5, &R, a, b, &res->res, &res->lc)
               : gc_all(av, 3, &R, a, b);
  }
  k = 2*n-degpol(y1);
  q = FpXQX_divrem(x1, y1, T, p, &r);
  if (res)
  {
    long dx1 = degpol(x1), dy1 = degpol(y1), dr = degpol(r);
    if (dy1 < degpol(y))
      FpXQX_halfres_update(res->deg0, res->deg1, dy1, T, p, res);
    res->lc = to_ZX(leading_coeff(y1), vT);
    res->deg0 = dx1;
    res->deg1 = dy1;
    if (dr >= n)
    {
      FpXQX_halfres_update(dx1, dy1, dr, T, p, res);
      res->deg0 = dy1;
      res->deg1 = dr;
    }
    res->deg0 -= k;
    res->deg1 -= k;
    res->off += k;
  }
  S = FpXQX_halfres_i(FpXX_shift(y1,-k), FpXX_shift(r,-k), T, p, a, b, res);
  if (res)
  {
    res->deg0 += k;
    res->deg1 += k;
    res->off -= k;
  }
  Q = FpXQXM_mul2(S,FpXQX_FpXQXM_qmul(q, R, T, p), T, p);
  V2 = FpXQXM_FpXQX_mul2(S, FpXXn_red(y1,k), FpXXn_red(r,k), T, p);
  *a = FpXX_add(FpXX_shift(*a,k), gel(V2,1), p);
  *b = FpXX_add(FpXX_shift(*b,k), gel(V2,2), p);
  return res ? gc_all(av, 5, &Q, a, b, &res->res, &res->lc)
             : gc_all(av, 3, &Q, a, b);
}

static GEN
FpXQX_halfres_i(GEN x, GEN y, GEN T, GEN p, GEN *a, GEN *b, struct FpXQX_res *res)
{
  if (lgpol(x) < FpXQX_HALFGCD_LIMIT)
    return FpXQX_halfres_basecase(x, y, T, p, a, b, res);
  return FpXQX_halfres_split(x, y, T, p, a, b, res);
}

static GEN
FpXQX_halfgcd_all_i(GEN x, GEN y, GEN T, GEN p, GEN *pa, GEN *pb)
{
  GEN a, b;
  GEN R = FpXQX_halfres_i(x, y, T, p, &a, &b, NULL);
  if (pa) *pa = a;
  if (pb) *pb = b;
  return R;
}

/* Return M in GL_2(Fp[X]/(T)[Y]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

GEN
FpXQX_halfgcd_all(GEN x, GEN y, GEN T, GEN p, GEN *a, GEN *b)
{
  pari_sp av = avma;
  GEN R,q,r;
  if (lgefint(p)==3)
  {
    ulong pp = to_FlxqX(x, y, T, p, &x, &y, &T);
    R = FlxXM_to_ZXXM(FlxqX_halfgcd(x, y, T, pp));
    if (a) *a = Flx_to_ZX(*a);
    if (b) *b = Flx_to_ZX(*b);
    return !a && b ? gc_all(av, 2, &R, b): gc_all(av, 1+!!a+!!b, &R, a, b);
  }
  if (!signe(x))
  {
    if (a) *a = RgX_copy(y);
    if (b) *b = RgX_copy(x);
    return matJ2_FpXQXM(varn(x));
  }
  if (degpol(y)<degpol(x)) return FpXQX_halfgcd_all_i(x, y, T, p, a, b);
  q = FpXQX_divrem(y, x, T, p, &r);
  R = FpXQX_halfgcd_all_i(x, r, T, p, a, b);
  gcoeff(R,1,1) = FpXX_sub(gcoeff(R,1,1),
                           FpXQX_mul(q, gcoeff(R,1,2), T, p), p);
  gcoeff(R,2,1) = FpXX_sub(gcoeff(R,2,1),
                           FpXQX_mul(q, gcoeff(R,2,2), T, p), p);
  return !a && b ? gc_all(av, 2, &R, b): gc_all(av, 1+!!a+!!b, &R, a, b);
}

GEN
FpXQX_halfgcd(GEN x, GEN y, GEN T, GEN p)
{ return FpXQX_halfgcd_all(x, y, T, p, NULL, NULL); }

static GEN
FpXQX_gcd_basecase(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma, av0=avma;
  while (signe(b))
  {
    GEN c;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_gcd (d = %ld)",degpol(b));
      (void)gc_all(av0,2, &a,&b);
    }
    av = avma; c = FpXQX_rem(a, b, T, p); a=b; b=c;
  }
  return gc_const(av, a);
}

GEN
FpXQX_gcd(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, U;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    U  = FlxqX_gcd(Pl, Ql, Tl, pp);
    return gc_upto(av, FlxX_to_ZXX(U));
  }
  x = FpXQX_red(x, T, p);
  y = FpXQX_red(y, T, p);
  if (!signe(x)) return gc_upto(av, y);
  while (lgpol(y)>=FpXQX_GCD_LIMIT)
  {
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FpXQX_rem(x, y, T, p);
      x = y; y = r;
    }
    (void) FpXQX_halfgcd_all(x,y, T, p, &x, &y);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_gcd (y = %ld)",degpol(y));
      (void)gc_all(av,2,&x,&y);
    }
  }
  return gc_upto(av, FpXQX_gcd_basecase(x, y, T, p));
}

static GEN
FpXQX_extgcd_basecase(GEN a, GEN b, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol_1(vx);
  while (signe(d1))
  {
    GEN r, q = FpXQX_divrem(d, d1, T, p, &r);
    v = FpXX_sub(v,FpXQX_mul(q,v1,T, p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_extgcd (d = %ld)",degpol(d));
      (void)gc_all(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = FpXQX_div(FpXX_sub(d,FpXQX_mul(b,v, T, p), p), a, T, p);
  *ptv = v; return d;
}

static GEN
FpXQX_extgcd_halfgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN u,v;
  GEN V = cgetg(expu(lgpol(y))+2,t_VEC);
  long i, n = 0, vs = varn(x);
  while (lgpol(y) >= FpXQX_EXTGCD_LIMIT)
  {
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = FpXQX_divrem(x, y, T, p, &r);
      x = y; y = r;
      gel(V,++n) = mkmat22(pol_0(vs),pol_1(vs),pol_1(vs),FpXX_neg(q,p));
    } else
      gel(V,++n) = FpXQX_halfgcd_all(x, y, T, p, &x, &y);
  }
  y = FpXQX_extgcd_basecase(x,y, T, p, &u,&v);
  for (i = n; i>1; i--)
  {
    GEN R = gel(V,i);
    GEN u1 = FpXQX_addmulmul(u, v, gcoeff(R,1,1), gcoeff(R,2,1), T, p);
    GEN v1 = FpXQX_addmulmul(u, v, gcoeff(R,1,2), gcoeff(R,2,2), T, p);
    u = u1; v = v1;
  }
  {
    GEN R = gel(V,1);
    if (ptu)
      *ptu = FpXQX_addmulmul(u, v, gcoeff(R,1,1), gcoeff(R,2,1), T, p);
    *ptv   = FpXQX_addmulmul(u, v, gcoeff(R,1,2), gcoeff(R,2,2), T, p);
  }
  return y;
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av = avma;
  GEN d;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, Dl;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    Dl = FlxqX_extgcd(Pl, Ql, Tl, pp, ptu, ptv);
    if (ptu) *ptu = FlxX_to_ZXX(*ptu);
    *ptv = FlxX_to_ZXX(*ptv);
    d = FlxX_to_ZXX(Dl);
  }
  else
  {
    x = FpXQX_red(x, T, p);
    y = FpXQX_red(y, T, p);
    if (lgpol(y)>=FpXQX_EXTGCD_LIMIT)
      d = FpXQX_extgcd_halfgcd(x, y, T, p, ptu, ptv);
    else
      d = FpXQX_extgcd_basecase(x, y, T, p, ptu, ptv);
  }
  return gc_all(av, ptu?3:2, &d, ptv, ptu);
}

static GEN
FpXQX_halfres(GEN x, GEN y, GEN T, GEN p, GEN *a, GEN *b, GEN *r)
{
  struct FpXQX_res res;
  GEN V;
  long dB, vT = get_FpX_var(T);

  res.res  = *r;
  res.lc   = to_ZX(leading_coeff(y),vT);
  res.deg0 = degpol(x);
  res.deg1 = degpol(y);
  res.off = 0;
  V = FpXQX_halfres_i(x, y, T, p, a, b, &res);
  dB = degpol(*b);
  if (dB < degpol(y))
    FpXQX_halfres_update(res.deg0, res.deg1, dB, T, p, &res);
  *r = res.res;
  return V;
}

/* Res(A,B) = Res(B,R) * lc(B)^(a-r) * (-1)^(ab), with R=A%B, a=deg(A) ...*/
static GEN
FpXQX_resultant_basecase(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma;
  long vT = get_FpX_var(T), da,db,dc;
  GEN c,lb, res = pol_1(vT);

  if (!signe(a) || !signe(b)) return pol_0(vT);

  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = FpX_neg(res, p);
  }
  if (!da) return pol_1(vT); /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  while (db)
  {
    lb = to_ZX(gel(b,db+2),vT);
    c = FpXQX_rem(a,b, T,p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { set_avma(av); return pol_0(vT); }

    if (both_odd(da,db)) res = FpX_neg(res, p);
    if (!ZX_equal1(lb)) res = FpXQ_mul(res, FpXQ_powu(lb, da - dc, T, p), T, p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_resultant (da = %ld)",da);
      (void)gc_all(av,3, &a,&b,&res);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  res = FpXQ_mul(res, FpXQ_powu(gel(b,2), da, T, p), T, p);
  return gc_upto(av, res);
}

GEN
FpXQX_resultant(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  long dx, dy, vT = get_FpX_var(T);
  GEN res = pol_1(vT);
  if (!signe(x) || !signe(y)) return pol_0(vT);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    GEN Pl, Ql, Tl, R;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    R = FlxqX_resultant(Pl, Ql, Tl, pp);
    return gc_upto(av, Flx_to_ZX(R));
  }

  dx = degpol(x); dy = degpol(y);
  if (dx < dy)
  {
    swap(x,y);
    if (both_odd(dx, dy))
      res = Fp_neg(res, p);
  }
  while (lgpol(y) >= FpXQX_GCD_LIMIT)
  {
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FpXQX_rem(x, y, T, p);
      long dx = degpol(x), dy = degpol(y), dr = degpol(r);
      GEN ly = FpX_red(gel(y,dy+2),p);
      if (!ZX_equal1(ly)) res = FpXQ_mul(res, FpXQ_powu(ly, dx - dr, T, p), T, p);
      if (both_odd(dx, dy))
        res = Fp_neg(res, p);
      x = y; y = r;
    }
    (void) FpXQX_halfres(x, y, T, p, &x, &y, &res);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_resultant (y = %ld)",degpol(y));
      (void)gc_all(av,3,&x,&y,&res);
    }
  }
  return gc_upto(av, FpXQ_mul(res, FpXQX_resultant_basecase(x, y, T, p), T, p));
}

/* disc P = (-1)^(n(n-1)/2) lc(P)^(n - deg P' - 2) Res(P,P'), n = deg P */
GEN
FpXQX_disc(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN L, dP = FpXX_deriv(P, p), D = FpXQX_resultant(P, dP, T, p);
  long dd;
  if (!signe(D)) return pol_0(get_FpX_var(T));
  dd = degpol(P) - 2 - degpol(dP); /* >= -1; > -1 iff p | deg(P) */
  L = leading_coeff(P);
  if (dd && !gequal1(L))
    D = (dd == -1)? FpXQ_div(D,L,T,p): FpXQ_mul(D, FpXQ_powu(L, dd, T, p), T, p);
  if (degpol(P) & 2) D = FpX_neg(D, p);
  return gc_upto(av, D);
}

GEN
FpXQX_dotproduct(GEN x, GEN y, GEN T, GEN p)
{
  long i, l = minss(lg(x), lg(y));
  pari_sp av;
  GEN c;
  if (l == 2) return gen_0;
  av = avma; c = gmul(gel(x,2),gel(y,2));
  for (i=3; i<l; i++) c = gadd(c, gmul(gel(x,i),gel(y,i)));
  return gc_upto(av, Fq_red(c,T,p));
}

/***********************************************************************/
/**                                                                   **/
/**                       Barrett reduction                           **/
/**                                                                   **/
/***********************************************************************/

/* Return new lgpol */
static long
ZXX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (signe(gel(x,i))) break;
  return i+1;
}

static GEN
FpXQX_invBarrett_basecase(GEN S, GEN T, GEN p)
{
  long i, l=lg(S)-1, lr = l-1, k;
  GEN r=cgetg(lr, t_POL); r[1]=S[1];
  gel(r,2) = gen_1;
  for (i=3; i<lr; i++)
  {
    pari_sp av = avma;
    GEN u = gel(S,l-i+2);
    for (k=3; k<i; k++)
      u = Fq_add(u, Fq_mul(gel(S,l-i+k), gel(r,k), NULL, p), NULL, p);
    gel(r,i) = gc_upto(av, Fq_red(Fq_neg(u, NULL, p), T, p));
  }
  return FpXQX_renormalize(r,lr);
}

INLINE GEN
FpXX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpXQX_invBarrett_Newton(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(S), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = gen_0;
  q = RgX_recipspec_shallow(S+2,l+1,l+1); lQ = lgpol(q); q+=2;
  /* We work on _spec_ FpX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Fq_inv(gel(q,0), T, p);
  if (lQ>1) gel(q,1) = Fq_red(gel(q,1), T, p);
  if (lQ>1 && signe(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!gequal1(gel(x,0))) u = Fq_mul(u, Fq_sqr(gel(x,0), T, p), T, p);
    gel(x,1) = Fq_neg(u, T, p); lx = 2;
  }
  else
    lx = 1;
  nold = 1;
  for (; mask > 1; )
  { /* set x -= x(x*q - 1) + O(t^(nnew + 1)), knowing x*q = 1 + O(t^(nold+1)) */
    long i, lnew, nnew = nold << 1;

    if (mask & 1) nnew--;
    mask >>= 1;

    lnew = nnew + 1;
    lq = ZXX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FpXQX_mulspec(x, q, T, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (signe(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = ZXX_lgrenormalizespec (z+i, lz-i);
    z = FpXQX_mulspec(x, z+i, T, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = ZXX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Fq_neg(gel(z,i), T, p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = S[1];
  return gc_GEN(av, x);
}

GEN
FpXQX_invBarrett(GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long l = lg(S);
  GEN r;
  if (l<5) return pol_0(varn(S));
  if (l<=FpXQX_INVBARRETT_LIMIT)
  {
    GEN c = gel(S,l-1), ci=gen_1;
    if (!gequal1(c))
    {
      ci = Fq_inv(c, T, p);
      S = FqX_Fq_mul(S, ci, T, p);
      r = FpXQX_invBarrett_basecase(S, T, p);
      r = FqX_Fq_mul(r, ci, T, p);
    } else
      r = FpXQX_invBarrett_basecase(S, T, p);
  }
  else
    r = FpXQX_invBarrett_Newton(S, T, p);
  return gc_upto(ltop, r);
}

GEN
FpXQX_get_red(GEN S, GEN T, GEN p)
{
  if (typ(S)==t_POL && lg(S)>FpXQX_BARRETT_LIMIT)
    retmkvec2(FpXQX_invBarrett(S,T,p),S);
  return S;
}

/* Compute x mod S where 2 <= degpol(S) <= l+1 <= 2*(degpol(S)-1)
 * and mg is the Barrett inverse of S. */
static GEN
FpXQX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(S); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = ZXX_lgrenormalizespec(S+2,lt);
  lmg = ZXX_lgrenormalizespec(mg+2,lm);
  q = FpXX_recipspec(x+lt,ld,ld);                 /* q = rec(x)     lq<=ld*/
  q = FpXQX_mulspec(q+2,mg+2,T,p,lgpol(q),lmg);    /* q = rec(x) * mg lq<=ld+lm*/
  q = FpXX_recipspec(q+2,minss(ld,lgpol(q)),ld);  /* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = FpXQX_mulspec(q+2,S+2,T,p,lgpol(q),lT);      /* r = q*pol        lr<=ld+lt*/
  r = FpXX_subspec(x,r+2,p,lt,minss(lt,lgpol(r))); /* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
FpXQX_divrem_Barrett(GEN x, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN q = NULL, r = FpXQX_red(x, T, p);
  long l = lgpol(r), lt = degpol(S), lm = 2*lt-1, v = varn(S);
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return r;
    if (pr == ONLY_DIVIDES) return signe(r)? NULL: pol_0(v);
    if (pr) *pr = r;
    return pol_0(v);
  }
  if (lt <= 1)
    return FpXQX_divrem_basecase(r,S,T,p,pr);
  if (pr != ONLY_REM && l>lm)
  {
    q = cgetg(l-lt+2, t_POL); q[1] = S[1];
    for (i=0;i<l-lt;i++) gel(q+2,i) = gen_0;
  }
  while (l>lm)
  {
    GEN zr, zq = FpXQX_divrem_Barrettspec(r+2+l-lm,lm,mg,S,T,p,&zr);
    long lz = lgpol(zr);
    if (pr != ONLY_REM)
    {
      long lq = lgpol(zq);
      for(i=0; i<lq; i++) gel(q+2+l-lm,i) = gel(zq,2+i);
    }
    for(i=0; i<lz; i++) gel(r+2+l-lm,i) = gel(zr,2+i);
    l = l-lm+lz;
  }
  if (pr == ONLY_REM)
  {
    if (l > lt)
      r = FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,ONLY_REM);
    else
      r = FpXQX_renormalize(r, l+2);
    setvarn(r, v); return r;
  }
  if (l > lt)
  {
    GEN zq = FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,pr ? &r: NULL);
    if (!q) q = zq;
    else
    {
      long lq = lgpol(zq);
      for(i=0; i<lq; i++) gel(q+2,i) = gel(zq,2+i);
    }
  }
  else if (pr)
    r = FpX_renormalize(r, l+2);
  setvarn(q, v); q = FpXQX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) { setvarn(r, v); *pr = r; }
  return q;
}

GEN
FpXQX_divrem(GEN x, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN B, y;
  long dy, dx, d;
  if (pr == ONLY_REM) return FpXQX_rem(x, S, T, p);
  y = get_FpXQX_red(S, &B);
  dy = degpol(y); dx = degpol(x); d = dx-dy;
  if (lgefint(p) == 3)
  {
    GEN a, b, t, z;
    pari_sp av = avma, tetpil;
    ulong pp = to_FlxqX(x, y, T, p, &a, &b, &t);
    z = FlxqX_divrem(a, b, t, pp, pr);
    if (!z) return gc_NULL(av);
    if (!pr || pr == ONLY_DIVIDES) return gc_upto(av, FlxX_to_ZXX(z));
    tetpil = avma;
    z = FlxX_to_ZXX(z);
    *pr = FlxX_to_ZXX(*pr);
    return gc_all_unsafe(av,tetpil,2, &z, pr);
  }
  if (!B && d+3 < FpXQX_DIVREM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y,T,p,pr);
  else
  {
    pari_sp av = avma;
    GEN mg = B? B: FpXQX_invBarrett(y, T, p);
    GEN q = FpXQX_divrem_Barrett(x,mg,y,T,p,pr);
    if (!q) return gc_NULL(av);
    if (!pr || pr == ONLY_DIVIDES) return gc_GEN(av, q);
    return gc_all(av, 2, &q, pr);
  }
}

GEN
FpXQX_rem(GEN x, GEN S, GEN T, GEN p)
{
  GEN B, y = get_FpXQX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FpXQX_red(x, T, p);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    GEN a, b, t, z;
    ulong pp = to_FlxqX(x, y, T, p, &a, &b, &t);
    z = FlxqX_rem(a, b, t, pp);
    return gc_upto(av, FlxX_to_ZXX(z));
  }
  if (!B && d+3 < FpXQX_REM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y, T, p, ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: FpXQX_invBarrett(y, T, p);
    GEN r = FpXQX_divrem_Barrett(x, mg, y, T, p, ONLY_REM);
    return gc_upto(av, r);
  }
}

/* x + y*z mod p */
INLINE GEN
Fq_addmul(GEN x, GEN y, GEN z, GEN T, GEN p)
{
  pari_sp av;
  if (!signe(y) || !signe(z)) return Fq_red(x, T, p);
  if (!signe(x)) return Fq_mul(z,y, T, p);
  av = avma;
  return gc_upto(av, Fq_add(x, Fq_mul(y, z, T, p), T, p));
}

GEN
FpXQX_div_by_X_x(GEN a, GEN x, GEN T, GEN p, GEN *r)
{
  long l = lg(a), i;
  GEN z;
  if (lgefint(p)==3)
  {
    pari_sp av = avma;
    GEN ap, xp, t, z;
    ulong pp = to_FlxqX(a, NULL, T, p, &ap, NULL, &t);
    xp = ZX_to_Flx(to_ZX(x, get_FpX_var(T)), pp);
    z = FlxX_to_ZXX(FlxqX_div_by_X_x(ap, xp, t, pp, r));
    if (!r) return gc_upto(av, z);
    *r = Flx_to_ZX(*r);
    return gc_all(av, 2, &z, r);
  }
  if (l <= 3)
  {
    if (r) *r = l == 2? gen_0: gcopy(gel(a,2));
    return pol_0(varn(a));
  }
  l--; z = cgetg(l, t_POL); z[1] = a[1];
  gel(z, l-1) = gel(a,l);
  for (i=l-2; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
    gel(z, i) = Fq_addmul(gel(a,i+1), x, gel(z,i+1), T, p);
  if (r) *r = Fq_addmul(gel(a,2), x, gel(z,2), T, p);
  return z;
}

struct _FpXQXQ {
  GEN T, S;
  GEN p;
};

static GEN _FpXQX_mul(void *data, GEN a,GEN b)
{
  struct _FpXQXQ *d=(struct _FpXQXQ*)data;
  return FpXQX_mul(a,b,d->T,d->p);
}

static GEN _FpXQX_sqr(void *data, GEN a)
{
  struct _FpXQXQ *d=(struct _FpXQXQ*)data;
  return FpXQX_sqr(a, d->T, d->p);
}

GEN
FpXQX_powu(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQXQ D;
  if (n==0) return pol_1(varn(x));
  D.T = T; D.p = p;
  return gen_powu(x, n, (void *)&D, _FpXQX_sqr, _FpXQX_mul);
}

GEN
FpXQXV_prod(GEN V, GEN T, GEN p)
{
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN Tl = ZXT_to_FlxT(T, pp);
    GEN Vl = ZXXV_to_FlxXV(V, pp, get_FpX_var(T));
    Tl = FlxqXV_prod(Vl, Tl, pp);
    return gc_upto(av, FlxX_to_ZXX(Tl));
  }
  else
  {
    struct _FpXQXQ d;
    d.T=T; d.p=p;
    return gen_product(V, (void*)&d, &_FpXQX_mul);
  }
}

static GEN
_FpXQX_divrem(void * E, GEN x, GEN y, GEN *r)
{
  struct _FpXQXQ *d = (struct _FpXQXQ *) E;
  return FpXQX_divrem(x, y, d->T, d->p, r);
}

static GEN
_FpXQX_add(void * E, GEN x, GEN y)
{
  struct _FpXQXQ *d = (struct _FpXQXQ *) E;
  return FpXX_add(x, y, d->p);
}

static GEN
_FpXQX_sub(void * E, GEN x, GEN y) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) E;
  return FpXX_sub(x,y, d->p);
}

static struct bb_ring FpXQX_ring = { _FpXQX_add, _FpXQX_mul, _FpXQX_sqr };

GEN
FpXQX_digits(GEN x, GEN B, GEN T, GEN p)
{
  long d = degpol(B), n = (lgpol(x)+d-1)/d;
  struct _FpXQXQ D;
  D.T = T; D.p = p;
  return gen_digits(x, B, n, (void *)&D, &FpXQX_ring, _FpXQX_divrem);
}

GEN
FpXQXV_FpXQX_fromdigits(GEN x, GEN B, GEN T, GEN p)
{
  struct _FpXQXQ D;
  D.T = T; D.p = p;
  return gen_fromdigits(x,B,(void *)&D, &FpXQX_ring);
}

/* Q an FpXY (t_POL with FpX coeffs), evaluate at X = x */
GEN
FpXY_evalx(GEN Q, GEN x, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FpX_eval(q, x, p);
  }
  return FpX_renormalize(z, lb);
}
/* Q an FpXY, evaluate at Y = y */
GEN
FpXY_evaly(GEN Q, GEN y, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (!signe(Q)) return pol_0(vx);
  if (lb == 3 || !signe(y)) {
    z = gel(Q, 2);
    return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);
  }
  z = gel(Q, lb-1);
  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--) z = Fq_add(gel(Q,i), FpX_Fp_mul(z, y, p), NULL, p);
  return gc_upto(av, z);
}
/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FpXY_eval(GEN Q, GEN y, GEN x, GEN p)
{
  pari_sp av = avma;
  return gc_INT(av, FpX_eval(FpXY_evalx(Q, x, p), y, p));
}

GEN
FpXY_FpXQV_evalx(GEN P, GEN x, GEN T, GEN p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? icopy(gel(P,i)):
                                       FpX_FpXQV_eval(gel(P,i), x, T, p);
  return FlxX_renormalize(res, lP);
}

GEN
FpXY_FpXQ_evalx(GEN P, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(P),1);
  GEN xp = FpXQ_powers(x, n, T, p);
  return gc_upto(av, FpXY_FpXQV_evalx(P, xp, T, p));
}

/*******************************************************************/
/*                                                                 */
/*                       (Fp[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T, p;
} FpXYQQ_muldata;

/* reduce x in Fp[X, Y] in the algebra Fp[X,Y]/ (S(X),T(Y)) */
static GEN
FpXYQQ_redswap(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long n = get_FpX_degree(S);
  long m = get_FpX_degree(T);
  long v = get_FpX_var(T);
  GEN V = RgXY_swap(x,m,v);
  V = FpXQX_red(V,S,p);
  V = RgXY_swap(V,n,v);
  return gc_GEN(ltop,V);
}
static GEN
FpXYQQ_sqr(void *data, GEN x)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_sqr(x, D->T, D->p),D->S,D->T,D->p);

}
static GEN
FpXYQQ_mul(void *data, GEN x, GEN y)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_mul(x,y, D->T, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FpXYQQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  FpXYQQ_muldata D;
  GEN y;
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, NULL, T, p, &x, NULL, &T);
    S = ZX_to_Flx(S, pp);
    y = FlxX_to_ZXX( FlxYqq_pow(x, n, S, T, pp) );
    y = gc_upto(av, y);
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    y = gen_pow(x, n, (void*)&D, &FpXYQQ_sqr, &FpXYQQ_mul);
  }
  return y;
}

GEN
FpXQXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_mul(x, y, T, p), S, T, p);
}

GEN
FpXQXQ_sqr(GEN x, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_sqr(x, T, p), S, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQXQ_invsafe(GEN x, GEN S, GEN T, GEN p)
{
  GEN V, z = FpXQX_extgcd(get_FpXQX_mod(S), x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = gel(z,2);
  z = typ(z)==t_INT ? Fp_invsafe(z,p) : FpXQ_invsafe(z,T,p);
  if (!z) return NULL;
  return typ(z)==t_INT ? FpXX_Fp_mul(V, z, p): FpXQX_FpXQ_mul(V, z, T, p);
}

GEN
FpXQXQ_inv(GEN x, GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQXQ_invsafe(x, S, T, p);
  if (!U) pari_err_INV("FpXQXQ_inv",x);
  return gc_upto(av, U);
}

GEN
FpXQXQ_div(GEN x,GEN y,GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  return gc_upto(av, FpXQXQ_mul(x, FpXQXQ_inv(y,S,T,p),S,T,p));
}

static GEN
_FpXQXQ_cmul(void *data, GEN P, long a, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  GEN y = gel(P,a+2);
  return typ(y)==t_INT ? FpXX_Fp_mul(x,y, d->p):
                         FpXX_FpX_mul(x,y,d->p);
}
static GEN
_FpXQXQ_red(void *data, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQX_red(x, d->T, d->p);
}
static GEN
_FpXQXQ_mul(void *data, GEN x, GEN y) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQXQ_mul(x,y, d->S,d->T, d->p);
}
static GEN
_FpXQXQ_sqr(void *data, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQXQ_sqr(x, d->S,d->T, d->p);
}

static GEN
_FpXQXQ_one(void *data) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return pol_1(get_FpXQX_var(d->S));
}

static GEN
_FpXQXQ_zero(void *data) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return pol_0(get_FpXQX_var(d->S));
}

static struct bb_algebra FpXQXQ_algebra = { _FpXQXQ_red, _FpXQX_add,
       _FpXQX_sub, _FpXQXQ_mul, _FpXQXQ_sqr, _FpXQXQ_one, _FpXQXQ_zero };

const struct bb_algebra *
get_FpXQXQ_algebra(void **E, GEN S, GEN T, GEN p)
{
  GEN z = new_chunk(sizeof(struct _FpXQXQ));
  struct _FpXQXQ *e = (struct _FpXQXQ *) z;
  e->T = FpX_get_red(T, p);
  e->S = FpXQX_get_red(S, e->T, p);
  e->p  = p; *E = (void*)e;
  return &FpXQXQ_algebra;
}

static struct bb_algebra FpXQX_algebra = { _FpXQXQ_red, _FpXQX_add,
       _FpXQX_sub, _FpXQX_mul, _FpXQX_sqr, _FpXQXQ_one, _FpXQXQ_zero };

const struct bb_algebra *
get_FpXQX_algebra(void **E, GEN T, GEN p, long v)
{
  GEN z = new_chunk(sizeof(struct _FpXQXQ));
  struct _FpXQXQ *e = (struct _FpXQXQ *) z;
  e->T = FpX_get_red(T, p);
  e->S = pol_x(v);
  e->p  = p; *E = (void*)e;
  return &FpXQX_algebra;
}

/* x over Fq, return lift(x^n) mod S */
GEN
FpXQXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN y;
  struct _FpXQXQ D;
  long s = signe(n);
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQXQ_inv(x,S,T,p): ZXX_copy(x);
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, S, T, p, &x, &S, &T);
    GEN z = FlxqXQ_pow(x, n, S, T, pp);
    y = FlxX_to_ZXX(z);
    return gc_upto(ltop, y);
  }
  else
  {
    T = FpX_get_red(T, p);
    S = FpXQX_get_red(S, T, p);
    D.S = S; D.T = T; D.p = p;
    if (s < 0) x = FpXQXQ_inv(x,S,T,p);
    y = gen_pow_i(x, n, (void*)&D,&_FpXQXQ_sqr,&_FpXQXQ_mul);
    return gc_GEN(ltop, y);
  }
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQXQ_powers(GEN x, long l, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  int use_sqr = 2*degpol(x) >= get_FpXQX_degree(S);
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S = S; D.T = T; D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FpXQXQ_sqr, &_FpXQXQ_mul,&_FpXQXQ_one);
}

/* Let v a linear form, return the linear form z->v(tau*z)
   that is, v*(M_tau) */

INLINE GEN
FpXQX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpXQXQ_transmul_init(GEN tau, GEN S, GEN T, GEN p)
{
  GEN bht;
  GEN h, Sp = get_FpXQX_red(S, &h);
  long n = degpol(Sp), vT = varn(Sp);
  GEN ft = FpXQX_recipspec(Sp+2, n+1, n+1);
  GEN bt = FpXQX_recipspec(tau+2, lgpol(tau), n);
  setvarn(ft, vT); setvarn(bt, vT);
  if (h)
    bht = FpXQXn_mul(bt, h, n-1, T, p);
  else
  {
    GEN bh = FpXQX_div(FpXX_shift(tau, n-1), S, T, p);
    bht = FpXQX_recipspec(bh+2, lgpol(bh), n-1);
    setvarn(bht, vT);
  }
  return mkvec3(bt, bht, ft);
}

static GEN
FpXQXQ_transmul(GEN tau, GEN a, long n, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN t1, t2, t3, vec;
  GEN bt = gel(tau, 1), bht = gel(tau, 2), ft = gel(tau, 3);
  if (signe(a)==0) return pol_0(varn(a));
  t2 = FpXX_shift(FpXQX_mul(bt, a, T, p),1-n);
  if (signe(bht)==0) return gc_GEN(ltop, t2);
  t1 = FpXX_shift(FpXQX_mul(ft, a, T, p),-n);
  t3 = FpXQXn_mul(t1, bht, n-1, T, p);
  vec = FpXX_sub(t2, FpXX_shift(t3, 1), p);
  return gc_upto(ltop, vec);
}

static GEN
polxn_FpXX(long n, long v, long vT)
{
  long i, a = n+2;
  GEN p = cgetg(a+1, t_POL);
  p[1] = evalsigne(1)|evalvarn(v);
  for (i = 2; i < a; i++) gel(p,i) = pol_0(vT);
  gel(p,a) = pol_1(vT); return p;
}

GEN
FpXQXQ_minpoly(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long vS, vT, n;
  GEN v_x, g, tau;
  vS = get_FpXQX_var(S);
  vT = get_FpX_var(T);
  n = get_FpXQX_degree(S);
  g = pol_1(vS);
  tau = pol_1(vS);
  S = FpXQX_get_red(S, T, p);
  v_x = FpXQXQ_powers(x, usqrt(2*n), S, T, p);
  while(signe(tau) != 0)
  {
    long i, j, m, k1;
    GEN M, v, tr;
    GEN g_prime, c;
    if (degpol(g) == n) { tau = pol_1(vS); g = pol_1(vS); }
    v = random_FpXQX(n, vS, T, p);
    tr = FpXQXQ_transmul_init(tau, S, T, p);
    v = FpXQXQ_transmul(tr, v, n, T, p);
    m = 2*(n-degpol(g));
    k1 = usqrt(m);
    tr = FpXQXQ_transmul_init(gel(v_x,k1+1), S, T, p);
    c = cgetg(m+2,t_POL);
    c[1] = evalsigne(1)|evalvarn(vS);
    for (i=0; i<m; i+=k1)
    {
      long mj = minss(m-i, k1);
      for (j=0; j<mj; j++)
        gel(c,m+1-(i+j)) = FpXQX_dotproduct(v, gel(v_x,j+1), T, p);
      v = FpXQXQ_transmul(tr, v, n, T, p);
    }
    c = FpXX_renormalize(c, m+2);
    /* now c contains <v,x^i> , i = 0..m-1  */
    M = FpXQX_halfgcd(polxn_FpXX(m, vS, vT), c, T, p);
    g_prime = gmael(M, 2, 2);
    if (degpol(g_prime) < 1) continue;
    g = FpXQX_mul(g, g_prime, T, p);
    tau = FpXQXQ_mul(tau, FpXQX_FpXQXQV_eval(g_prime, v_x, S, T, p), S, T, p);
  }
  g = FpXQX_normalize(g,T, p);
  return gc_GEN(ltop,g);
}

GEN
FpXQXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, GEN p)
{
  return RgXV_to_RgM(FpXQXQ_powers(y,m-1,S,T,p),n);
}

GEN
FpXQX_FpXQXQV_eval(GEN P, GEN V, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval_powers(P, degpol(P), V, (void*)&D, &FpXQXQ_algebra,
                                                   _FpXQXQ_cmul);
}

GEN
FpXQX_FpXQXQ_eval(GEN Q, GEN x, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  int use_sqr = 2*degpol(x) >= get_FpXQX_degree(S);
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval(Q, degpol(Q), x, use_sqr, (void*)&D, &FpXQXQ_algebra,
      _FpXQXQ_cmul);
}

static GEN
FpXQXQ_autpow_sqr(void * E, GEN x)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi = gel(x,1), S1 = gel(x,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(S1)+1,1);
  GEN V = FpXQ_powers(phi, n, T, p);
  GEN phi2 = FpX_FpXQV_eval(phi, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V, T, p);
  GEN S2 = FpXQX_FpXQXQ_eval(Sphi, S1, S, T, p);
  return mkvec2(phi2, S2);
}

static GEN
FpXQXQ_autpow_mul(void * E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2);
  GEN phi2 = gel(y,1), S2 = gel(y,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+1, 1);
  GEN V = FpXQ_powers(phi2, n, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V, T, p);
  GEN S3 = FpXQX_FpXQXQ_eval(Sphi, S2, S, T, p);
  return mkvec2(phi3, S3);
}

GEN
FpXQXQ_autpow(GEN aut, long n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  aut = gen_powu_i(aut,n,&D,FpXQXQ_autpow_sqr,FpXQXQ_autpow_mul);
  return gc_GEN(av, aut);
}

static GEN
FpXQXQ_auttrace_mul(void *E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T;
  GEN p = D->p;
  GEN S1 = gel(x,1), a1 = gel(x,2);
  GEN S2 = gel(y,1), a2 = gel(y,2);
  long n = brent_kung_optpow(maxss(degpol(S1),degpol(a1)),2,1);
  GEN V = FpXQXQ_powers(S2, n, S, T, p);
  GEN S3 = FpXQX_FpXQXQV_eval(S1, V, S, T, p);
  GEN aS = FpXQX_FpXQXQV_eval(a1, V, S, T, p);
  GEN a3 = FpXX_add(aS, a2, p);
  return mkvec2(S3, a3);
}

static GEN
FpXQXQ_auttrace_sqr(void *E, GEN x)
{ return FpXQXQ_auttrace_mul(E, x, x); }

GEN
FpXQXQ_auttrace(GEN aut, long n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  aut = gen_powu_i(aut,n,&D,FpXQXQ_auttrace_sqr,FpXQXQ_auttrace_mul);
  return gc_GEN(av, aut);
}

static GEN
FpXQXQ_autsum_mul(void *E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *) E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2), a1 = gel(x,3);
  GEN phi2 = gel(y,1), S2 = gel(y,2), a2 = gel(y,3);
  long n2 = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+lgpol(a1)+1, 1);
  GEN V2 = FpXQ_powers(phi2, n2, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V2, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V2, T, p);
  GEN aphi = FpXY_FpXQV_evalx(a1, V2, T, p);
  long n = brent_kung_optpow(maxss(degpol(Sphi),degpol(aphi)),2,1);
  GEN V = FpXQXQ_powers(S2, n, S, T, p);
  GEN S3 = FpXQX_FpXQXQV_eval(Sphi, V, S, T, p);
  GEN aS = FpXQX_FpXQXQV_eval(aphi, V, S, T, p);
  GEN a3 = FpXQXQ_mul(aS, a2, S, T, p);
  return mkvec3(phi3, S3, a3);
}

static GEN
FpXQXQ_autsum_sqr(void * T, GEN x)
{ return FpXQXQ_autsum_mul(T,x,x); }

GEN
FpXQXQ_autsum(GEN aut, long n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  aut = gen_powu_i(aut,n,&D,FpXQXQ_autsum_sqr,FpXQXQ_autsum_mul);
  return gc_GEN(av, aut);
}

GEN
FpXQXn_mul(GEN x, GEN y, long n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long d;
  if (ZXX_is_ZX(y) && ZXX_is_ZX(x))
    return FpXn_mul(x,y,n,p);
  d = get_FpX_degree(T);
  kx = RgXX_to_Kronecker(x, d);
  ky = RgXX_to_Kronecker(y, d);
  z = Kronecker_to_FpXQX(ZXn_mul(ky,kx,(2*d-1)*n), T, p);
  return gc_upto(av, z);
}

GEN
FpXQXn_sqr(GEN x, long n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  long d;
  if (ZXX_is_ZX(x)) return ZXn_sqr(x, n);
  d = get_FpX_degree(T);
  kx= RgXX_to_Kronecker(x, d);
  z = Kronecker_to_FpXQX(ZXn_sqr(kx, (2*d-1)*n), T, p);
  return gc_upto(av, z);
}

/* (f*g) \/ x^n */
static GEN
FpXQX_mulhigh_i(GEN f, GEN g, long n, GEN T, GEN p)
{
  return FpXX_shift(FpXQX_mul(f,g,T, p),-n);
}

static GEN
FpXQXn_mulhigh(GEN f, GEN g, long n2, long n, GEN T, GEN p)
{
  GEN F = RgX_blocks(f, n2, 2), fl = gel(F,1), fh = gel(F,2);
  return FpXX_add(FpXQX_mulhigh_i(fl, g, n2, T, p), FpXQXn_mul(fh, g, n - n2, T, p), p);
}

/* Compute intformal(x^n*S)/x^(n+1) */
static GEN
FpXX_integXn(GEN x, long n, GEN p)
{
  long i, lx = lg(x);
  GEN y;
  if (lx == 2) return ZXX_copy(x);
  y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++)
  {
    ulong j = n+i-1;
    GEN xi = gel(x,i);
    if (!signe(xi))
      gel(y,i) = gen_0;
    else
      gel(y,i) = typ(xi)==t_INT ? Fp_divu(xi, j, p)
                                : FpX_divu(xi, j, p);
  }
  return ZXX_renormalize(y, lx);;
}

/* Compute intformal(x^n*S)/x^(n+1) */
static GEN
ZlXX_integXn(GEN x, long n, GEN p, ulong pp)
{
  long i, lx = lg(x);
  GEN y;
  if (lx == 2) return ZXX_copy(x);
  if (!pp) return FpXX_integXn(x, n, p);
  y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++)
  {
    GEN xi = gel(x,i);
    if (!signe(xi))
      gel(y,i) = gen_0;
    else
    {
      ulong j;
      long v = u_lvalrem(n+i-1, pp, &j);
      if (typ(xi)==t_INT)
      {
        if (v==0)
          gel(y,i) = Fp_divu(xi, j, p);
        else
          gel(y,i) = Fp_divu(diviuexact(xi, upowuu(pp, v)), j, p);
      } else
      {
        if (v==0)
          gel(y,i) = FpX_divu(xi, j, p);
        else
          gel(y,i) = FpX_divu(ZX_divuexact(xi, upowuu(pp, v)), j, p);
      }
    }
  }
  return ZXX_renormalize(y, lx);;
}

GEN
ZlXQXn_expint(GEN h, long e, GEN T, GEN p, ulong pp)
{
  pari_sp av = avma, av2;
  long v = varn(h), n=1;
  GEN f = pol_1(v), g = pol_1(v);
  ulong mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, w;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    u = FpXQXn_mul(g, FpXQX_mulhigh_i(f, FpXXn_red(h, n2-1), n2-1, T, p), n-n2, T, p);
    u = FpXX_add(u, FpXX_shift(FpXXn_red(h, n-1), 1-n2), p);
    w = FpXQXn_mul(f, ZlXX_integXn(u, n2-1, p, pp), n-n2, T, p);
    f = FpXX_add(f, FpXX_shift(w, n2), p);
    if (mask<=1) break;
    u = FpXQXn_mul(g, FpXQXn_mulhigh(f, g, n2, n, T, p), n-n2, T, p);
    g = FpXX_sub(g, FpXX_shift(u, n2), p);
    if (gc_needed(av2,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQXn_exp, e = %ld", n);
      (void)gc_all(av2, 2, &f, &g);
    }
  }
  return gc_upto(av, f);
}

GEN
FpXQXn_expint(GEN h, long e, GEN T, GEN p)
{ return ZlXQXn_expint(h, e, T, p, 0); }

GEN
FpXQXn_exp(GEN h, long e, GEN T, GEN p)
{
  if (signe(h)==0 || degpol(h)<1 || !gequal0(gel(h,2)))
    pari_err_DOMAIN("FpXQXn_exp","valuation", "<", gen_1, h);
  return FpXQXn_expint(FpXX_deriv(h, p), e, T, p);
}

GEN
FpXQXn_div(GEN g, GEN f, long e, GEN T, GEN p)
{
  pari_sp av = avma, av2;
  ulong mask;
  GEN W, a;
  long v = varn(f), n = 1;

  if (!signe(f)) pari_err_INV("FpXXn_inv",f);
  a = Fq_inv(gel(f,2), T, p);
  if (e == 1 && !g) return scalarpol(a, v);
  else if (e == 2 && !g)
  {
    GEN b;
    if (degpol(f) <= 0) return scalarpol(a, v);
    b = Fq_neg(gel(f,3),T,p);
    if (signe(b)==0) return scalarpol(a, v);
    if (!is_pm1(a)) b = Fq_mul(b, Fq_sqr(a, T, p), T, p);
    W = deg1pol_shallow(b, a, v);
    return gc_GEN(av, W);
  }
  W = scalarpol_shallow(Fq_inv(gel(f,2), T, p),v);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, fr;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    fr = FpXXn_red(f, n);
    if (mask>1 || !g)
    {
      u = FpXQXn_mul(W, FpXQXn_mulhigh(fr, W, n2, n, T, p), n-n2, T, p);
      W = FpXX_sub(W, FpXX_shift(u, n2), p);
    }
    else
    {
      GEN y = FpXQXn_mul(g, W, n, T, p), yt =  FpXXn_red(y, n-n2);
      u = FpXQXn_mul(yt, FpXQXn_mulhigh(fr,  W, n2, n, T, p), n-n2, T, p);
      W = FpXX_sub(y, FpXX_shift(u, n2), p);
    }
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpXQXn_inv, e = %ld", n);
      W = gc_upto(av2, W);
    }
  }
  return gc_upto(av, W);
}

GEN
FpXQXn_inv(GEN f, long e, GEN T, GEN p)
{ return FpXQXn_div(NULL, f, e, T, p); }
