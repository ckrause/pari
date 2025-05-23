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
/**             GENERIC ALGORITHMS ON BLACKBOX GROUP                  **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"
#undef pow /* AIX: pow(a,b) is a macro, wrongly expanded on grp->pow(a,b,c) */

#define DEBUGLEVEL DEBUGLEVEL_bb_group

/***********************************************************************/
/**                                                                   **/
/**                    POWERING                                       **/
/**                                                                   **/
/***********************************************************************/

/* return (n>>(i+1-l)) & ((1<<l)-1) */
static ulong
int_block(GEN n, long i, long l)
{
  long q = divsBIL(i), r = remsBIL(i)+1, lr;
  GEN nw = int_W(n, q);
  ulong w = (ulong) *nw, w2;
  if (r>=l) return (w>>(r-l))&((1UL<<l)-1);
  w &= (1UL<<r)-1; lr = l-r;
  w2 = (ulong) *int_precW(nw); w2 >>= (BITS_IN_LONG-lr);
  return (w<<lr)|w2;
}

/* assume n != 0, t_INT. Compute x^|n| using sliding window powering */
static GEN
sliding_window_powu(GEN x, ulong n, long e, void *E, GEN (*sqr)(void*,GEN),
                                                     GEN (*mul)(void*,GEN,GEN))
{
  long i, l = expu(n), u = (1UL<<(e-1));
  GEN tab = cgetg(1+u, t_VEC), x2 = sqr(E, x), z = NULL;

  gel(tab, 1) = x;
  for (i = 2; i <= u; i++) gel(tab,i) = mul(E, gel(tab,i-1), x2);
  while (l >= 0)
  {
    long w, v;
    GEN tw;
    if (e > l+1) e = l+1;
    w = (n>>(l+1-e)) & ((1UL<<e)-1); v = vals(w); l-=e;
    tw = gel(tab, 1 + (w>>(v+1)));
    if (!z) z = tw;
    else
    {
      for (i = 1; i <= e-v; i++) z = sqr(E, z);
      z = mul(E, z, tw);
    }
    for (i = 1; i <= v; i++) z = sqr(E, z);
    while (l >= 0)
    {
      if (n&(1UL<<l)) break;
      z = sqr(E, z); l--;
    }
  }
  return z;
}

/* assume n != 0, t_INT. Compute x^|n| using sliding window powering */
static GEN
sliding_window_pow(GEN x, GEN n, long e, void *E, GEN (*sqr)(void*,GEN),
                                                  GEN (*mul)(void*,GEN,GEN))
{
  pari_sp av;
  long i, l = expi(n), u = (1UL<<(e-1));
  GEN tab = cgetg(1+u, t_VEC);
  GEN x2 = sqr(E, x), z = NULL;

  gel(tab, 1) = x;
  for (i=2; i<=u; i++) gel(tab,i) = mul(E, gel(tab,i-1), x2);
  av = avma;
  while (l >= 0)
  {
    long w, v;
    GEN tw;
    if (e > l+1) e = l+1;
    w = int_block(n,l,e); v = vals(w); l-=e;
    tw = gel(tab, 1+(w>>(v+1)));
    if (!z) z = tw;
    else
    {
      for (i = 1; i <= e-v; i++) z = sqr(E, z);
      z = mul(E, z, tw);
    }
    for (i = 1; i <= v; i++) z = sqr(E, z);
    while (l >= 0)
    {
      if (gc_needed(av,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"sliding_window_pow (%ld)", l);
        z = gc_GEN(av, z);
      }
      if (int_bit(n,l)) break;
      z = sqr(E, z); l--;
    }
  }
  return z;
}

/* assume n != 0, t_INT. Compute x^|n| using leftright binary powering */
static GEN
leftright_binary_powu(GEN x, ulong n, void *E, GEN (*sqr)(void*,GEN),
                                               GEN (*mul)(void*,GEN,GEN))
{
  pari_sp av = avma;
  GEN  y;
  int j;

  if (n == 1) return x;
  y = x; j = 1+bfffo(n);
  /* normalize, i.e set highest bit to 1 (we know n != 0) */
  n<<=j; j = BITS_IN_LONG-j;
  /* first bit is now implicit */
  for (; j; n<<=1,j--)
  {
    y = sqr(E,y);
    if (n & HIGHBIT) y = mul(E,y,x); /* first bit set: multiply by base */
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"leftright_powu (%d)", j);
      y = gc_GEN(av, y);
    }
  }
  return y;
}

GEN
gen_powu_i(GEN x, ulong n, void *E, GEN (*sqr)(void*,GEN),
                                    GEN (*mul)(void*,GEN,GEN))
{
  if (n == 1) return x;
  if (n < 512)
    return leftright_binary_powu(x, n, E, sqr, mul);
  else
    return sliding_window_powu(x, n, n < (1UL<<25)? 2: 3, E, sqr, mul);
}

GEN
gen_powu(GEN x, ulong n, void *E, GEN (*sqr)(void*,GEN),
                                  GEN (*mul)(void*,GEN,GEN))
{
  pari_sp av = avma;
  if (n == 1) return gcopy(x);
  return gc_GEN(av, gen_powu_i(x,n,E,sqr,mul));
}

GEN
gen_pow_i(GEN x, GEN n, void *E, GEN (*sqr)(void*,GEN),
                                 GEN (*mul)(void*,GEN,GEN))
{
  long l, e;
  if (lgefint(n)==3) return gen_powu_i(x, uel(n,2), E, sqr, mul);
  l = expi(n);
  if      (l<=64)  e = 3;
  else if (l<=160) e = 4;
  else if (l<=384) e = 5;
  else if (l<=896) e = 6;
  else             e = 7;
  return sliding_window_pow(x, n, e, E, sqr, mul);
}

GEN
gen_pow(GEN x, GEN n, void *E, GEN (*sqr)(void*,GEN),
                               GEN (*mul)(void*,GEN,GEN))
{
  pari_sp av = avma;
  return gc_GEN(av, gen_pow_i(x,n,E,sqr,mul));
}

/* assume n > 0. Compute x^n using left-right binary powering */
GEN
gen_powu_fold_i(GEN x, ulong n, void *E, GEN  (*sqr)(void*,GEN),
                                         GEN (*msqr)(void*,GEN))
{
  pari_sp av = avma;
  GEN y;
  int j;

  if (n == 1) return x;
  y = x; j = 1+bfffo(n);
  /* normalize, i.e set highest bit to 1 (we know n != 0) */
  n<<=j; j = BITS_IN_LONG-j;
  /* first bit is now implicit */
  for (; j; n<<=1,j--)
  {
    if (n & HIGHBIT) y = msqr(E,y); /* first bit set: multiply by base */
    else y = sqr(E,y);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gen_powu_fold (%d)", j);
      y = gc_GEN(av, y);
    }
  }
  return y;
}
GEN
gen_powu_fold(GEN x, ulong n, void *E, GEN (*sqr)(void*,GEN),
                                       GEN (*msqr)(void*,GEN))
{
  pari_sp av = avma;
  if (n == 1) return gcopy(x);
  return gc_GEN(av, gen_powu_fold_i(x,n,E,sqr,msqr));
}

/* assume N != 0, t_INT. Compute x^|N| using left-right binary powering */
GEN
gen_pow_fold_i(GEN x, GEN N, void *E, GEN (*sqr)(void*,GEN),
                                      GEN (*msqr)(void*,GEN))
{
  long ln = lgefint(N);
  if (ln == 3) return gen_powu_fold_i(x, N[2], E, sqr, msqr);
  else
  {
    GEN nd = int_MSW(N), y = x;
    ulong n = *nd;
    long i;
    int j;
    pari_sp av = avma;

    if (n == 1)
      j = 0;
    else
    {
      j = 1+bfffo(n); /* < BIL */
      /* normalize, i.e set highest bit to 1 (we know n != 0) */
      n <<= j; j = BITS_IN_LONG - j;
    }
    /* first bit is now implicit */
    for (i=ln-2;;)
    {
      for (; j; n<<=1,j--)
      {
        if (n & HIGHBIT) y = msqr(E,y); /* first bit set: multiply by base */
        else y = sqr(E,y);
        if (gc_needed(av,1))
        {
          if (DEBUGMEM>1) pari_warn(warnmem,"gen_pow_fold (%ld,%d)", i,j);
          y = gc_GEN(av, y);
        }
      }
      if (--i == 0) return y;
      nd = int_precW(nd);
      n = *nd; j = BITS_IN_LONG;
    }
  }
}
GEN
gen_pow_fold(GEN x, GEN n, void *E, GEN (*sqr)(void*,GEN),
                                    GEN (*msqr)(void*,GEN))
{
  pari_sp av = avma;
  return gc_GEN(av, gen_pow_fold_i(x,n,E,sqr,msqr));
}

GEN
gen_pow_init(GEN x, GEN n, long k, void *E, GEN (*sqr)(void*,GEN), GEN (*mul)(void*,GEN,GEN))
{
  long i, j, l = expi(n);
  long m = 1UL<<(k-1);
  GEN x2 = sqr(E, x), y = gcopy(x);
  GEN R = cgetg(m+1, t_VEC);
  for(i = 1; i <= m; i++)
  {
    GEN C = cgetg(l+1, t_VEC);
    gel(C,1) = y;
    for(j = 2; j <= l; j++)
      gel(C,j) = sqr(E, gel(C,j-1));
    gel(R,i) = C;
    y = mul(E, y, x2);
  }
  return R;
}

GEN
gen_pow_table(GEN R, GEN n, void *E, GEN (*one)(void*), GEN (*mul)(void*,GEN,GEN))
{
  long e = expu(lg(R)-1) + 1;
  long l = expi(n);
  long i, w;
  GEN z = one(E), tw;
  for(i=0; i<=l; )
  {
    if (int_bit(n, i)==0) { i++; continue; }
    if (i+e-1>l) e = l+1-i;
    w = int_block(n,i+e-1,e);
    tw = gmael(R, 1+(w>>1), i+1);
    z = mul(E, z, tw);
    i += e;
  }
  return z;
}

GEN
gen_powers(GEN x, long l, int use_sqr, void *E, GEN (*sqr)(void*,GEN),
                                      GEN (*mul)(void*,GEN,GEN), GEN (*one)(void*))
{
  long i;
  GEN V = cgetg(l+2,t_VEC);
  gel(V,1) = one(E); if (l==0) return V;
  gel(V,2) = gcopy(x); if (l==1) return V;
  gel(V,3) = sqr(E,x);
  if (use_sqr)
    for(i = 4; i < l+2; i++)
      gel(V,i) = (i&1)? sqr(E,gel(V, (i+1)>>1))
                      : mul(E,gel(V, i-1),x);
  else
    for(i = 4; i < l+2; i++)
      gel(V,i) = mul(E,gel(V,i-1),x);
  return V;
}

GEN
producttree_scheme(long n)
{
  GEN v, w;
  long i, j, k, u, l;
  if (n<=2) return mkvecsmall(n);
  u = expu(n-1);
  v = cgetg(n+1,t_VECSMALL);
  w = cgetg(n+1,t_VECSMALL);
  v[1] = n; l = 1;
  for (i=1; i<=u; i++)
  {
    for(j=1, k=1; j<=l; j++, k+=2)
    {
      long vj = v[j], v2 = vj>>1;
      w[k]    = vj-v2;
      w[k+1]  = v2;
    }
    swap(v,w); l<<=1;
  }
  fixlg(v, l+1); set_avma((pari_sp)v); return v;
}

GEN
gen_product(GEN x, void *E, GEN (*mul)(void *,GEN,GEN))
{
  pari_sp av;
  long i, k, l = lg(x);
  pari_timer ti;
  GEN y, v;

  if (l <= 2) return l == 1? gen_1: gcopy(gel(x,1));
  y = cgetg(l, t_VEC); av = avma;
  v = producttree_scheme(l-1);
  l = lg(v);
  if (DEBUGLEVEL>7) timer_start(&ti);
  for (k = i = 1; k < l; i += v[k++])
    gel(y,k) = v[k]==1? gel(x,i): mul(E, gel(x,i), gel(x,i+1));
  while (k > 2)
  {
    long n = k - 1;
    if (DEBUGLEVEL>7) timer_printf(&ti,"gen_product: remaining objects %ld",n);
    for (k = i = 1; i < n; i += 2) gel(y,k++) = mul(E, gel(y,i), gel(y,i+1));
    if (gc_needed(av,1)) gc_slice(av, y+1, k-1);
  }
  return gel(y,1);
}

/***********************************************************************/
/**                                                                   **/
/**                    DISCRETE LOGARITHM                             **/
/**                                                                   **/
/***********************************************************************/
static GEN
iter_rho(GEN x, GEN g, GEN q, GEN A, ulong h, void *E, const struct bb_group *grp)
{
  GEN a = gel(A,1), b = gel(A,2), c = gel(A,3);
  switch((h | grp->hash(a)) % 3UL)
  {
    case 0: return mkvec3(grp->pow(E,a,gen_2), Fp_mulu(b,2,q), Fp_mulu(c,2,q));
    case 1: return mkvec3(grp->mul(E,a,x), addiu(b,1), c);
    case 2: return mkvec3(grp->mul(E,a,g), b, addiu(c,1));
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/*Generic Pollard rho discrete log algorithm*/
static GEN
gen_Pollard_log(GEN x, GEN g, GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av=avma;
  GEN A, B, l, sqrt4q = sqrti(shifti(q,4));
  ulong i, h = 0, imax = itou_or_0(sqrt4q);
  if (!imax) imax = ULONG_MAX;
  do {
 rho_restart:
    A = B = mkvec3(x,gen_1,gen_0);
    i=0;
    do {
      if (i>imax)
      {
        h++;
        if (DEBUGLEVEL)
          pari_warn(warner,"changing Pollard rho hash seed to %ld",h);
        goto rho_restart;
      }
      A = iter_rho(x, g, q, A, h, E, grp);
      B = iter_rho(x, g, q, B, h, E, grp);
      B = iter_rho(x, g, q, B, h, E, grp);
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gen_Pollard_log");
        (void)gc_all(av, 2, &A, &B);
      }
      i++;
    } while (!grp->equal(gel(A,1), gel(B,1)));
    gel(A,2) = modii(gel(A,2), q);
    gel(B,2) = modii(gel(B,2), q);
    h++;
  } while (equalii(gel(A,2), gel(B,2)));
  l = Fp_div(Fp_sub(gel(B,3), gel(A,3),q),Fp_sub(gel(A,2), gel(B,2), q), q);
  return gc_INT(av, l);
}

/* compute a hash of g^(i-1), 1<=i<=n. Return [sorted hash, perm, g^-n] */
GEN
gen_Shanks_init(GEN g, long n, void *E, const struct bb_group *grp)
{
  GEN p1 = g, G, perm, table = cgetg(n+1,t_VECSMALL);
  pari_sp av=avma;
  long i;
  table[1] = grp->hash(grp->pow(E,g,gen_0));
  for (i=2; i<=n; i++)
  {
    table[i] = grp->hash(p1);
    p1 = grp->mul(E,p1,g);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_log, baby = %ld", i);
      p1 = gc_upto(av, p1);
    }
  }
  G = gc_upto(av, grp->pow(E,p1,gen_m1)); /* g^-n */
  perm = vecsmall_indexsort(table);
  table = vecsmallpermute(table,perm);
  return mkvec4(table,perm,g,G);
}
/* T from gen_Shanks_init(g,n). Return v < n*N such that x = g^v or NULL */
GEN
gen_Shanks(GEN T, GEN x, ulong N, void *E, const struct bb_group *grp)
{
  pari_sp av=avma;
  GEN table = gel(T,1), perm = gel(T,2), g = gel(T,3), G = gel(T,4);
  GEN p1 = x;
  long n = lg(table)-1;
  ulong k;
  for (k=0; k<N; k++)
  { /* p1 = x G^k, G = g^-n */
    long h = grp->hash(p1), i = zv_search(table, h);
    if (i)
    {
      do i--; while (i && table[i] == h);
      for (i++; i <= n && table[i] == h; i++)
      {
        GEN v = addiu(muluu(n,k), perm[i]-1);
        if (grp->equal(grp->pow(E,g,v),x)) return gc_INT(av,v);
        if (DEBUGLEVEL)
          err_printf("gen_Shanks_log: false positive %lu, %lu\n", k,h);
      }
    }
    p1 = grp->mul(E,p1,G);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_log, k = %lu", k);
      p1 = gc_upto(av, p1);
    }
  }
  return NULL;
}
/* Generic Shanks baby-step/giant-step algorithm. Return log_g(x), ord g = q.
 * One-shot: use gen_Shanks_init/log if many logs are desired; early abort
 * if log < sqrt(q) */
static GEN
gen_Shanks_log(GEN x, GEN g, GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av=avma, av1;
  long lbaby, i, k;
  GEN p1, table, giant, perm, ginv;
  p1 = sqrti(q);
  if (abscmpiu(p1,LGBITS) >= 0)
    pari_err_OVERFLOW("gen_Shanks_log [order too large]");
  lbaby = itos(p1)+1; table = cgetg(lbaby+1,t_VECSMALL);
  ginv = grp->pow(E,g,gen_m1);
  av1 = avma;
  for (p1=x, i=1;;i++)
  {
    if (grp->equal1(p1)) return gc_stoi(av, i-1);
    table[i] = grp->hash(p1); if (i==lbaby) break;
    p1 = grp->mul(E,p1,ginv);
    if (gc_needed(av1,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_log, baby = %ld", i);
      p1 = gc_upto(av1, p1);
    }
  }
  p1 = giant = gc_upto(av1, grp->mul(E,x,grp->pow(E, p1, gen_m1)));
  perm = vecsmall_indexsort(table);
  table = vecsmallpermute(table,perm);
  av1 = avma;
  for (k=1; k<= lbaby; k++)
  {
    long h = grp->hash(p1), i = zv_search(table, h);
    if (i)
    {
      while (table[i] == h && i) i--;
      for (i++; i <= lbaby && table[i] == h; i++)
      {
        GEN v = addiu(mulss(lbaby-1,k),perm[i]-1);
        if (grp->equal(grp->pow(E,g,v),x)) return gc_INT(av,v);
        if (DEBUGLEVEL)
          err_printf("gen_Shanks_log: false positive %ld, %lu\n", k,h);
      }
    }
    p1 = grp->mul(E,p1,giant);
    if (gc_needed(av1,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_log, k = %ld", k);
      p1 = gc_upto(av1, p1);
    }
  }
  retgc_const(av, cgetg(1, t_VEC)); /* no solution */
}

/*Generic discrete logarithme in a group of prime order p*/
GEN
gen_plog(GEN x, GEN g, GEN p, void *E, const struct bb_group *grp)
{
  if (grp->easylog)
  {
    GEN e = grp->easylog(E, x, g, p);
    if (e) return e;
  }
  if (grp->equal1(x)) return gen_0;
  if (grp->equal(x,g)) return gen_1;
  if (expi(p)<32) return gen_Shanks_log(x,g,p,E,grp);
  return gen_Pollard_log(x, g, p, E, grp);
}

GEN
get_arith_ZZM(GEN o)
{
  if (!o) return NULL;
  switch(typ(o))
  {
    case t_INT:
      if (signe(o) > 0) return mkvec2(o, Z_factor(o));
      break;
    case t_MAT:
      if (is_Z_factorpos(o)) return mkvec2(factorback(o), o);
      break;
    case t_VEC:
      if (lg(o) == 3 && signe(gel(o,1)) > 0 && is_Z_factorpos(gel(o,2))) return o;
      break;
  }
  pari_err_TYPE("generic discrete logarithm (order factorization)",o);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
get_arith_Z(GEN o)
{
  if (!o) return NULL;
  switch(typ(o))
  {
    case t_INT:
      if (signe(o) > 0) return o;
      break;
    case t_MAT:
      o = factorback(o);
      if (typ(o) == t_INT && signe(o) > 0) return o;
      break;
    case t_VEC:
      if (lg(o) != 3) break;
      o = gel(o,1);
      if (typ(o) == t_INT && signe(o) > 0) return o;
      break;
  }
  pari_err_TYPE("generic discrete logarithm (order factorization)",o);
  return NULL; /* LCOV_EXCL_LINE */
}

/* Generic Pohlig-Hellman discrete logarithm: smallest integer n >= 0 such that
 * g^n=a. Assume ord(g) | ord; grp->easylog() is an optional trapdoor
 * function that catches easy logarithms */
GEN
gen_PH_log(GEN a, GEN g, GEN ord, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  GEN v, ginv, fa, ex;
  long i, j, l;

  if (grp->equal(g, a)) /* frequent special case */
    return grp->equal1(g)? gen_0: gen_1;
  if (grp->easylog)
  {
    GEN e = grp->easylog(E, a, g, ord);
    if (e) return e;
  }
  v = get_arith_ZZM(ord);
  ord= gel(v,1);
  fa = gel(v,2);
  ex = gel(fa,2);
  fa = gel(fa,1); l = lg(fa);
  ginv = grp->pow(E,g,gen_m1);
  v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN q = gel(fa,i), qj, gq, nq, ginv0, a0, t0;
    long e = itos(gel(ex,i));
    if (DEBUGLEVEL>5)
      err_printf("Pohlig-Hellman: DL mod %Ps^%ld\n",q,e);
    qj = new_chunk(e+1);
    gel(qj,0) = gen_1;
    gel(qj,1) = q;
    for (j = 2; j <= e; j++) gel(qj,j) = mulii(gel(qj,j-1), q);
    t0 = diviiexact(ord, gel(qj,e));
    a0 = grp->pow(E, a, t0);
    ginv0 = grp->pow(E, ginv, t0); /* ord(ginv0) | q^e */
    if (grp->equal1(ginv0)) { gel(v,i) = mkintmod(gen_0, gen_1); continue; }
    do gq = grp->pow(E,g, mulii(t0, gel(qj,--e))); while (grp->equal1(gq));
    /* ord(gq) = q */
    nq = gen_0;
    for (j = 0;; j++)
    { /* nq = sum_{i<j} b_i q^i */
      GEN b = grp->pow(E,a0, gel(qj,e-j));
      /* cheap early abort: wrong local order */
      if (j == 0 && !grp->equal1(grp->pow(E,b,q))) {
        retgc_const(av, cgetg(1, t_VEC));
      }
      b = gen_plog(b, gq, q, E, grp);
      if (typ(b) != t_INT) retgc_const(av, cgetg(1, t_VEC));
      nq = addii(nq, mulii(b, gel(qj,j)));
      if (j == e) break;

      a0 = grp->mul(E,a0, grp->pow(E,ginv0, b));
      ginv0 = grp->pow(E,ginv0, q);
    }
    gel(v,i) = mkintmod(nq, gel(qj,e+1));
  }
  return gc_INT(av, lift(chinese1_coprime_Z(v)));
}

/***********************************************************************/
/**                                                                   **/
/**                    ORDER OF AN ELEMENT                            **/
/**                                                                   **/
/***********************************************************************/

static GEN
rec_order(GEN a, GEN o, GEN m,
          void *E, const struct bb_group *grp, long x, long y)
{
  pari_sp av = avma;
  if(grp->equal1(a)) return gen_1;
  if(x == y)
  {
    GEN b = a, p = gcoeff(m, x, 1);
    long i, e = itos(gcoeff(m,x,2));
    for (i = 0; i < e; i++)
    {
      if (grp->equal1(b)) return gc_GEN(av, powiu(p, i));
      b = grp->pow(E, b, p);
    }
    return gc_GEN(av, powiu(p, e));
  }
  else
  {
    GEN b, o1, o2, cof = gen_1;
    long i, z = (x+y)/2;
    for (i = x; i <= z; i++)
      cof = mulii(cof, powii(gcoeff(m, i, 1), gcoeff(m, i, 2)));
    b = grp->pow(E, a, cof);
    o1 = rec_order(b, diviiexact(o, cof), m, E, grp, z+1, y);
    b = grp->pow(E, a, o1);
    o2 = rec_order(b, diviiexact(o, o1), m, E, grp, x, z);
    return gc_GEN(av, mulii(o1, o2));
  }
}

/*Find the exact order of a assuming a^o==1*/
GEN
gen_order(GEN a, GEN o, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  long l;
  GEN m;

  m = get_arith_ZZM(o);
  if (!m) pari_err_TYPE("gen_order [missing order]",a);
  o = gel(m,1);
  if (is_pm1(o)) return gen_1;
  m = gel(m,2); l = lgcols(m);
  return gc_GEN(av, rec_order(a, o, m, E, grp, 1, l-1));
}

/*Find the exact order of a assuming a^o==1, return [order,factor(order)] */
GEN
gen_factored_order(GEN a, GEN o, void *E, const struct bb_group *grp)
{
  pari_sp av = avma;
  long i, l, ind;
  GEN m, F, P;

  m = get_arith_ZZM(o);
  if (!m) pari_err_TYPE("gen_factored_order [missing order]",a);
  o = gel(m,1);
  m = gel(m,2); l = lgcols(m);
  P = cgetg(l, t_COL); ind = 1;
  F = cgetg(l, t_COL);
  for (i = l-1; i; i--)
  {
    GEN t, y, p = gcoeff(m,i,1);
    long j, e = itos(gcoeff(m,i,2));
    if (l == 2) {
      t = gen_1;
      y = a;
    } else {
      t = diviiexact(o, powiu(p,e));
      y = grp->pow(E, a, t);
    }
    if (grp->equal1(y)) o = t;
    else {
      for (j = 1; j < e; j++)
      {
        y = grp->pow(E, y, p);
        if (grp->equal1(y)) break;
      }
      gel(P,ind) = p;
      gel(F,ind) = utoipos(j);
      if (j < e) {
        if (j > 1) p = powiu(p, j);
        o = mulii(t, p);
      }
      ind++;
    }
  }
  setlg(P, ind); P = vecreverse(P);
  setlg(F, ind); F = vecreverse(F);
  return gc_GEN(av, mkvec2(o, mkmat2(P,F)));
}

/* E has order o[1], ..., or o[#o], draw random points until all solutions
 * but one are eliminated */
GEN
gen_select_order(GEN o, void *E, const struct bb_group *grp)
{
  pari_sp ltop = avma, btop;
  GEN lastgood, so, vo;
  long lo = lg(o), nbo=lo-1;
  if (nbo == 1) return icopy(gel(o,1));
  so = ZV_indexsort(o); /* minimize max( o[i+1] - o[i] ) */
  vo = zero_zv(lo);
  lastgood = gel(o, so[nbo]);
  btop = avma;
  for(;;)
  {
    GEN lasto = gen_0;
    GEN P = grp->rand(E), t = mkvec(gen_0);
    long i;
    for (i = 1; i < lo; i++)
    {
      GEN newo = gel(o, so[i]);
      if (vo[i]) continue;
      t = grp->mul(E,t, grp->pow(E, P, subii(newo,lasto)));/*P^o[i]*/
      lasto = newo;
      if (!grp->equal1(t))
      {
        if (--nbo == 1) { set_avma(ltop); return icopy(lastgood); }
        vo[i] = 1;
      }
      else
        lastgood = lasto;
    }
    set_avma(btop);
  }
}

/*******************************************************************/
/*                                                                 */
/*                          n-th ROOT                              */
/*                                                                 */
/*******************************************************************/
/* Assume l is prime. Return a generator of the l-th Sylow and set *zeta to an element
 * of order l.
 *
 * q = l^e*r, e>=1, (r,l)=1
 * UNCLEAN */
static GEN
gen_lgener(GEN l, long e, GEN r,GEN *zeta, void *E, const struct bb_group *grp)
{
  const pari_sp av1 = avma;
  GEN m, m1;
  long i;
  for (;; set_avma(av1))
  {
    m1 = m = grp->pow(E, grp->rand(E), r);
    if (grp->equal1(m)) continue;
    for (i=1; i<e; i++)
    {
      m = grp->pow(E,m,l);
      if (grp->equal1(m)) break;
    }
    if (i==e) break;
  }
  *zeta = m; return m1;
}

/* Let G be a cyclic group of order o>1. Returns a (random) generator */

GEN
gen_gener(GEN o, void *E, const struct bb_group *grp)
{
  pari_sp ltop = avma, av;
  long i, lpr;
  GEN F, N, pr, z=NULL;
  F = get_arith_ZZM(o);
  N = gel(F,1); pr = gel(F,2); lpr = lgcols(pr);
  av = avma;

  for (i = 1; i < lpr; i++)
  {
    GEN l = gcoeff(pr,i,1);
    long e = itos(gcoeff(pr,i,2));
    GEN r = diviiexact(N,powis(l,e));
    GEN zetan, zl = gen_lgener(l,e,r,&zetan,E,grp);
    z = i==1 ? zl: grp->mul(E,z,zl);
    if (gc_needed(av,2))
    { /* n can have lots of prime factors*/
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_gener");
      z = gc_upto(av, z);
    }
  }
  return gc_upto(ltop, z);
}

/* solve x^l = a , l prime in G of order q.
 *
 * q =  (l^e)*r, e >= 1, (r,l) = 1
 * y is not an l-th power, hence generates the l-Sylow of G
 * m = y^(q/l) != 1 */
static GEN
gen_Shanks_sqrtl(GEN a, GEN l, long e, GEN r, GEN y, GEN m,void *E,
                 const struct bb_group *grp)
{
  pari_sp av = avma;
  long k;
  GEN p1, u1, u2, v, w, z, dl;

  (void)bezout(r,l,&u1,&u2);
  v = grp->pow(E,a,u2);
  w = grp->pow(E,v,l);
  w = grp->mul(E,w,grp->pow(E,a,gen_m1));
  while (!grp->equal1(w))
  {
    k = 0;
    p1 = w;
    do
    {
      z = p1; p1 = grp->pow(E,p1,l);
      k++;
    } while(!grp->equal1(p1));
    if (k==e) return gc_NULL(av);
    dl = gen_plog(z,m,l,E,grp);
    if (typ(dl) != t_INT) return gc_NULL(av);
    dl = negi(dl);
    p1 = grp->pow(E, grp->pow(E,y, dl), powiu(l,e-k-1));
    m = grp->pow(E,m,dl);
    e = k;
    v = grp->mul(E,p1,v);
    y = grp->pow(E,p1,l);
    w = grp->mul(E,y,w);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_sqrtl");
      (void)gc_all(av,4, &y,&v,&w,&m);
    }
  }
  return gc_GEN(av, v);
}
/* Return one solution of x^n = a in a cyclic group of order q
 *
 * 1) If there is no solution, return NULL.
 *
 * 2) If there is a solution, there are exactly m of them [m = gcd(q-1,n)].
 * If zetan!=NULL, *zetan is set to a primitive m-th root of unity so that
 * the set of solutions is { x*zetan^k; k=0..m-1 }
 */
GEN
gen_Shanks_sqrtn(GEN a, GEN n, GEN q, GEN *zetan, void *E, const struct bb_group *grp)
{
  pari_sp ltop = avma;
  GEN m, u1, u2, z;
  int is_1;

  if (is_pm1(n))
  {
    if (zetan) *zetan = grp->pow(E,a,gen_0);
    return signe(n) < 0? grp->pow(E,a,gen_m1): gcopy(a);
  }
  is_1 = grp->equal1(a);
  if (is_1 && !zetan) return gcopy(a);

  m = bezout(n,q,&u1,&u2);
  z = grp->pow(E,a,gen_0);
  if (!is_pm1(m))
  {
    GEN F = Z_factor(m);
    long i, j, e;
    GEN r, zeta, y, l;
    pari_sp av1 = avma;
    for (i = nbrows(F); i; i--)
    {
      l = gcoeff(F,i,1);
      j = itos(gcoeff(F,i,2));
      e = Z_pvalrem(q,l,&r);
      y = gen_lgener(l,e,r,&zeta,E,grp);
      if (zetan) z = grp->mul(E,z, grp->pow(E,y,powiu(l,e-j)));
      if (!is_1) {
        do
        {
          a = gen_Shanks_sqrtl(a,l,e,r,y,zeta,E,grp);
          if (!a) return gc_NULL(ltop);
        } while (--j);
      }
      if (gc_needed(ltop,1))
      { /* n can have lots of prime factors*/
        if(DEBUGMEM>1) pari_warn(warnmem,"gen_Shanks_sqrtn");
        (void)gc_all(av1, zetan? 2: 1, &a, &z);
      }
    }
  }
  if (!equalii(m, n))
    a = grp->pow(E,a,modii(u1,q));
  if (zetan)
  {
    *zetan = z;
    (void)gc_all(ltop,2,&a,zetan);
  }
  else /* is_1 is 0: a was modified above -> gc_upto valid */
    a = gc_upto(ltop, a);
  return a;
}

/*******************************************************************/
/*                                                                 */
/*               structure of groups with pairing                  */
/*                                                                 */
/*******************************************************************/
/* return c = \prod_{p^2 | (N,d^2)} p^{v_p(N)} and factor(c); multiple of d2 */
static GEN
d2_multiple(GEN N, GEN d)
{
  GEN P, E, Q = gel(Z_factor(gcdii(N,d)), 1);
  long i, j, l = lg(Q);
  P = cgetg(l, t_COL);
  E = cgetg(l, t_COL);
  for (i = 1, j = 1; i < l; i++)
  {
    long v = Z_pval(N, gel(Q,i));
    if (v <= 1) continue;
    gel(P, j) = gel(Q,i);
    gel(E, j) = utoipos(v); j++;
  }
  if (j == 1) return NULL;
  setlg(P,j); setlg(E,j);
  return mkvec2(factorback2(P, E), mkmat2(P, E));
}

/* Return elementary divisors [d1, d2], d2 | d1, for group of order N.
 * We have d2 | d */
GEN
gen_ellgroup(GEN N, GEN d, GEN *pm, void *E, const struct bb_group *grp,
             GEN pairorder(void *E, GEN P, GEN Q, GEN m, GEN F))
{
  pari_sp av = avma;
  GEN N0, N1, F, fa0, L0, E0, g1 = gen_1, g2 = gen_1;
  long n = 0, n0, j;

  if (pm) *pm = gen_1;
  if (is_pm1(N)) return cgetg(1,t_VEC);
  F = d2_multiple(N, d); if (!F) { set_avma(av); return mkveccopy(N); }
  N0 = gel(F,1); fa0 = gel(F,2); /* N0 a multiple of d2, fa0 = factor(N0) */
  N1 = diviiexact(N, N0); /* N1 | d1 */
  L0 = gel(fa0, 1); n0 = lg(L0)-1; /* primes dividing N0 */
  E0 = ZV_to_nv(gel(fa0, 2)); /* ... and their exponents */
  while (1)
  { /* g1 | (d1/N1), g2 | d2 */
    pari_sp av2 = avma;
    GEN P, Q, s, t, m, mo;

    P = grp->pow(E,grp->rand(E), N1);
    s = gen_order(P, F, E, grp); /* s | N0 */
    if (equalii(s, N0)) { set_avma(av); return mkveccopy(N); }

    Q = grp->pow(E,grp->rand(E), N1);
    t = gen_order(Q, F, E, grp); /* t | N0 */
    if (equalii(t, N0)) { set_avma(av); return mkveccopy(N); }

    m = lcmii(s, t); /* m | N0 */
    mo = mulii(m, pairorder(E, P, Q, m, F));

    /* For each prime l dividing N0, check whether P and Q
     * generate all rational points of order a power of l */
    for (j = 1; j <= n0; j++)
    {
      GEN l;
      ulong e = uel(E0, j);
      if (e == 0) continue;
      l = gel(L0, j);
      if ((ulong)Z_pval(mo, l) == e)
      {
        long vm = Z_pval(m, l);
        g1 = mulii(g1, powiu(l, vm));
        g2 = mulii(g2, powiu(l, e - vm));
        if (++n == n0)
        { /* done with all primes l */
          GEN g;
          if (equali1(g2)) { set_avma(av); return mkveccopy(N); }
          if (pm) *pm = g1;
          g = mkvec2(mulii(g1, N1), g2);
          if (!pm) return gc_GEN(av, g);
          *pm = m; return gc_all(av, 2, &g, pm);
        }
        uel(E0, j) = 0; /* done with this prime l */
      }
    }
    (void)gc_all(av2, 2, &g1, &g2);
  }
}

GEN
gen_ellgens(GEN D1, GEN d2, GEN m, void *E, const struct bb_group *grp,
             GEN pairorder(void *E, GEN P, GEN Q, GEN m, GEN F))
{
  pari_sp ltop = avma, av;
  GEN F, d1, dm;
  GEN P, Q, d, s;
  F = get_arith_ZZM(D1);
  d1 = gel(F, 1), dm =  diviiexact(d1,m);
  av = avma;
  do
  {
    set_avma(av);
    P = grp->rand(E);
    s = gen_order(P, F, E, grp);
  } while (!equalii(s, d1));
  av = avma;
  do
  {
    set_avma(av);
    Q = grp->rand(E);
    d = pairorder(E, grp->pow(E, P, dm), grp->pow(E, Q, dm), m, F);
  } while (!equalii(d, d2));
  return gc_GEN(ltop, mkvec2(P,Q));
}
