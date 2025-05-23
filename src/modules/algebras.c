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
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_alg

#define dbg_printf(lvl) if (DEBUGLEVEL >= (lvl) + 3) err_printf

/********************************************************************/
/**                                                                **/
/**           ASSOCIATIVE ALGEBRAS, CENTRAL SIMPLE ALGEBRAS        **/
/**                 contributed by Aurel Page (2014)               **/
/**                                                                **/
/********************************************************************/
static GEN alg_subalg(GEN al, GEN basis);
static GEN alg_maximal_primes(GEN al, GEN P);
static GEN algnatmultable(GEN al, long D);
static GEN _tablemul_ej(GEN mt, GEN x, long j);
static GEN _tablemul_ej_Fp(GEN mt, GEN x, long j, GEN p);
static GEN _tablemul_ej_Fl(GEN mt, GEN x, long j, ulong p);
static ulong algtracei(GEN mt, ulong p, ulong expo, ulong modu);
static GEN alg_pmaximal(GEN al, GEN p);
static GEN alg_maximal(GEN al);
static GEN algtracematrix(GEN al);
static GEN algtableinit_i(GEN mt0, GEN p);
static GEN algbasisrightmultable(GEN al, GEN x);
static GEN algbasismul(GEN al, GEN x, GEN y);
static GEN algbasismultable(GEN al, GEN x);
static GEN algbasismultable_Flm(GEN mt, GEN x, ulong m);
static GEN algeltfromnf_i(GEN al, GEN x);
static void computesplitting(GEN al, long d, long v, long flag);
static GEN alg_change_overorder_shallow(GEN al, GEN ord);

static GEN H_inv(GEN x);
static GEN H_norm(GEN x, long abs);
static GEN H_trace(GEN x, long abs);

static int
checkalg_i(GEN al)
{
  GEN mt, rnf;
  long t;
  if (typ(al) != t_VEC || lg(al) != 12) return 0;
  mt = alg_get_multable(al);
  if (typ(mt) != t_VEC || lg(mt) == 1 || typ(gel(mt,1)) != t_MAT) return 0;
  rnf = alg_get_splittingfield(al);
  if (isintzero(rnf) || !gequal0(alg_get_char(al)))
    return 1;
  if (typ(gel(al,2)) != t_VEC || lg(gel(al,2)) == 1) return 0;
  /* not checkrnf_i: beware placeholder from alg_csa_table */
  t = typ(rnf);
  return t==t_COMPLEX || t==t_REAL || (t==t_VEC && lg(rnf)==13);
}
void
checkalg(GEN al)
{
  if (al && !checkalg_i(al))
    pari_err_TYPE("checkalg [please apply alginit()]",al);
}

static int
checklat_i(GEN al, GEN lat)
{
  long N,i,j;
  GEN m,t,c;
  if (typ(lat)!=t_VEC || lg(lat) != 3) return 0;
  t = gel(lat,2);
  if (typ(t) != t_INT && typ(t) != t_FRAC) return 0;
  if (gsigne(t)<=0) return 0;
  m = gel(lat,1);
  if (typ(m) != t_MAT) return 0;
  N = alg_get_absdim(al);
  if (lg(m)-1 != N || lg(gel(m,1))-1 != N) return 0;
  for (i=1; i<=N; i++)
    for (j=1; j<=N; j++) {
      c = gcoeff(m,i,j);
      if (typ(c) != t_INT) return 0;
      if (j<i && signe(gcoeff(m,i,j))) return 0;
      if (i==j && !signe(gcoeff(m,i,j))) return 0;
    }
  return 1;
}
void checklat(GEN al, GEN lat)
{ if (!checklat_i(al,lat)) pari_err_TYPE("checklat [please apply alglathnf()]", lat); }

/**  ACCESSORS  **/
long
alg_type(GEN al)
{
  long t;
  if (!al) return al_REAL;
  t = typ(alg_get_splittingfield(al));
  if (t==t_REAL || t==t_COMPLEX) return al_REAL;
  if (isintzero(alg_get_splittingfield(al)) || !gequal0(alg_get_char(al))) return al_TABLE;
  switch(typ(gmael(al,2,1))) {
    case t_MAT: return al_CSA;
    case t_INT:
    case t_FRAC:
    case t_POL:
    case t_POLMOD: return al_CYCLIC;
    default: return al_NULL;
  }
  return -1; /*LCOV_EXCL_LINE*/
}
long
algtype(GEN al)
{ return checkalg_i(al)? alg_type(al): al_NULL; }

static long /* is a square special case? */
alg_is_asq(GEN al) { return typ(gmael(al,6,1)) == t_VEC; }

/* absdim == dim for al_TABLE. */
static long
algreal_dim(GEN al)
{
  switch(lg(alg_get_multable(al))) {
    case 2: case 3: return 1;
    case 5: return 4;
    default: pari_err_TYPE("algreal_dim", al);
  }
  return -1; /*LCOV_EXCL_LINE*/
}
long
alg_get_dim(GEN al)
{
  long d;
  if (!al) return 4;
  switch(alg_type(al)) {
    case al_TABLE: return lg(alg_get_multable(al))-1;
    case al_CSA: return lg(alg_get_relmultable(al))-1;
    case al_CYCLIC: d = alg_get_degree(al); return d*d;
    case al_REAL: return algreal_dim(al);
    default: pari_err_TYPE("alg_get_dim", al);
  }
  return -1; /*LCOV_EXCL_LINE*/
}

long
alg_get_absdim(GEN al)
{
  if (!al) return 4;
  switch(alg_type(al)) {
    case al_TABLE: case al_REAL: return lg(alg_get_multable(al))-1;
    case al_CSA: return alg_get_dim(al)*nf_get_degree(alg_get_center(al));
    case al_CYCLIC:
      return rnf_get_absdegree(alg_get_splittingfield(al))*alg_get_degree(al);
    default: pari_err_TYPE("alg_get_absdim", al);
  }
  return -1;/*LCOV_EXCL_LINE*/
}

long
algdim(GEN al, long abs)
{
  checkalg(al);
  if (abs) return alg_get_absdim(al);
  return alg_get_dim(al);
}

/* only cyclic */
GEN
alg_get_auts(GEN al)
{
  long ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_REAL)
    pari_err_TYPE("alg_get_auts [noncyclic algebra]", al);
  return gel(al,2);
}
GEN
alg_get_aut(GEN al)
{
  long ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_REAL)
    pari_err_TYPE("alg_get_aut [noncyclic algebra]", al);
  return gel(alg_get_auts(al),1);
}
GEN
algaut(GEN al) { checkalg(al); return alg_get_aut(al); }
GEN
alg_get_b(GEN al)
{
  long ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_REAL)
    pari_err_TYPE("alg_get_b [noncyclic algebra]", al);
  return gel(al,3);
}
GEN
algb(GEN al) { checkalg(al); return alg_get_b(al); }

/* only CSA */
GEN
alg_get_relmultable(GEN al)
{
  if (alg_type(al) != al_CSA)
    pari_err_TYPE("alg_get_relmultable [algebra not given via mult. table]", al);
  return gel(al,2);
}
GEN
algrelmultable(GEN al) { checkalg(al); return alg_get_relmultable(al); }
GEN
alg_get_splittingdata(GEN al)
{
  if (alg_type(al) != al_CSA)
    pari_err_TYPE("alg_get_splittingdata [algebra not given via mult. table]",al);
  return gel(al,3);
}
GEN
algsplittingdata(GEN al) { checkalg(al); return alg_get_splittingdata(al); }
GEN
alg_get_splittingbasis(GEN al)
{
  if (alg_type(al) != al_CSA)
    pari_err_TYPE("alg_get_splittingbasis [algebra not given via mult. table]",al);
  return gmael(al,3,2);
}
GEN
alg_get_splittingbasisinv(GEN al)
{
  if (alg_type(al) != al_CSA)
    pari_err_TYPE("alg_get_splittingbasisinv [algebra not given via mult. table]",al);
  return gmael(al,3,3);
}

/* only cyclic and CSA */
GEN
alg_get_splittingfield(GEN al) { return gel(al,1); }
GEN
algsplittingfield(GEN al)
{
  long ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_CSA && ta != al_REAL)
    pari_err_TYPE("alg_get_splittingfield [use alginit]",al);
  return alg_get_splittingfield(al);
}
long
alg_get_degree(GEN al)
{
  long ta;
  ta = alg_type(al);
  if (ta == al_REAL) return algreal_dim(al)==1? 1 : 2;
  if (ta != al_CYCLIC && ta != al_CSA)
    pari_err_TYPE("alg_get_degree [use alginit]",al);
  return rnf_get_degree(alg_get_splittingfield(al));
}
long
algdegree(GEN al)
{
  checkalg(al);
  return alg_get_degree(al);
}

GEN
alg_get_center(GEN al)
{
  long ta;
  ta = alg_type(al);
  if (ta == al_REAL)
  {
    if (algreal_dim(al) != 4) return alg_get_splittingfield(al);
    return stor(1, LOWDEFAULTPREC);
  }
  if (ta != al_CSA && ta != al_CYCLIC)
    pari_err_TYPE("alg_get_center [use alginit]",al);
  return rnf_get_nf(alg_get_splittingfield(al));
}
GEN
alg_get_splitpol(GEN al)
{
  long ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_CSA)
    pari_err_TYPE("alg_get_splitpol [use alginit]",al);
  return rnf_get_pol(alg_get_splittingfield(al));
}
GEN
alg_get_abssplitting(GEN al)
{
  long ta = alg_type(al), prec;
  if (ta != al_CYCLIC && ta != al_CSA)
    pari_err_TYPE("alg_get_abssplitting [use alginit]",al);
  prec = nf_get_prec(alg_get_center(al));
  return rnf_build_nfabs(alg_get_splittingfield(al), prec);
}
GEN
alg_get_hasse_i(GEN al)
{
  long ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_CSA && ta != al_REAL)
    pari_err_TYPE("alg_get_hasse_i [use alginit]",al);
  if (ta == al_CSA && !alg_is_asq(al))
    pari_err_IMPL("computation of Hasse invariants over table CSA");
  return gel(al,4);
}
GEN
alghassei(GEN al) { checkalg(al); return alg_get_hasse_i(al); }
GEN
alg_get_hasse_f(GEN al)
{
  long ta = alg_type(al);
  GEN hf;
  if (ta != al_CYCLIC && ta != al_CSA)
    pari_err_TYPE("alg_get_hasse_f [use alginit]",al);
  if (ta == al_CSA && !alg_is_asq(al))
    pari_err_IMPL("computation of Hasse invariants over table CSA");
  hf = gel(al,5);
  if (typ(hf) == t_INT) /* could be computed on the fly */
    pari_err(e_MISC, "Hasse invariants were not computed for this algebra");
  return hf;
}
GEN
alghassef(GEN al) { checkalg(al); return alg_get_hasse_f(al); }

/* all types */
GEN
alg_get_basis(GEN al) { return gel(al,7); }
GEN
algbasis(GEN al) { checkalg(al); return alg_get_basis(al); }
GEN
alg_get_invbasis(GEN al) { return gel(al,8); }
GEN
alginvbasis(GEN al) { checkalg(al); return alg_get_invbasis(al); }
GEN
alg_get_multable(GEN al) { return gel(al,9); }
GEN
algmultable(GEN al) { checkalg(al); return alg_get_multable(al); }
GEN
alg_get_char(GEN al) { if (!al) return gen_0; return gel(al,10); }
GEN
algchar(GEN al) { checkalg(al); return alg_get_char(al); }
GEN
alg_get_tracebasis(GEN al) { return gel(al,11); }
GEN
alg_get_invol(GEN al) { return gmael(al,6,2); }

/* lattices */
GEN
alglat_get_primbasis(GEN lat) { return gel(lat,1); }
GEN
alglat_get_scalar(GEN lat) { return gel(lat,2); }

/* algmodpr */
GEN
algmodpr_get_pr(GEN data) { return gel(data,1); }
long
algmodpr_get_k(GEN data) { return gel(data,2)[1]; } /* target M_k(F_p^m) */
long
algmodpr_get_m(GEN data) { return gel(data,2)[2]; } /* target M_k(F_p^m) */
GEN
algmodpr_get_ff(GEN data) { return gel(data,3); }
GEN
algmodpr_get_proj(GEN data) { return gel(data,4); }
GEN
algmodpr_get_lift(GEN data) { return gel(data,5); }
GEN
algmodpr_get_tau(GEN data) { return gel(data,6); }
GEN
algmodpr_get_p(GEN data) { return pr_get_p(algmodpr_get_pr(data)); }
GEN
algmodpr_get_T(GEN data) { return gel(data,2)[2]==1 ? NULL : gel(data,7); }

/** ADDITIONAL **/

/* is N=smooth*prime? */
static int Z_easyfactor(GEN N, ulong lim)
{
  GEN fa;
  if (lgefint(N) <= 3) return 1;
  fa = absZ_factor_limit(N, lim);
  return BPSW_psp(veclast(gel(fa,1)));
}

/* no garbage collection */
static GEN
backtrackfacto(GEN y0, long n, GEN red, GEN pl, GEN nf, GEN data, int (*test)(GEN,GEN), GEN* fa, GEN N, GEN I)
{
  long b, i;
  ulong lim = 1UL << 17;
  long *v = new_chunk(n+1);
  pari_sp av = avma;
  for (b = 0;; b += (2*b)/(3*n) + 1)
  {
    GEN ny, y1, y2;
    set_avma(av);
    for (i = 1; i <= n; i++) v[i] = -b;
    v[n]--;
    for(;;)
    {
      i = n;
      while (i > 0)
      { if (v[i] == b) v[i--] = -b; else { v[i]++; break; } }
      if (i==0) break;

      y1 = y0;
      for (i = 1; i <= n; i++) y1 = nfadd(nf, y1, ZC_z_mul(gel(red,i), v[i]));
      if (!nfchecksigns(nf, y1, pl)) continue;

      ny = absi_shallow(nfnorm(nf, y1));
      if (!signe(ny)) continue;
      ny = diviiexact(ny, gcdii(ny, N));
      if (!Z_easyfactor(ny, lim)) continue;

      y2 = idealdivexact(nf, y1, idealadd(nf,y1,I));
      *fa = idealfactor(nf, y2);
      if (!data || test(data,*fa)) return y1;
    }
  }
}

/* if data == NULL, the test is skipped */
/* in the test, the factorization does not contain the known factors */
static GEN
factoredextchinesetest(GEN nf, GEN x, GEN y, GEN pl, GEN* fa, GEN data, int (*test)(GEN,GEN))
{
  pari_sp av = avma;
  long n,i;
  GEN x1, y0, y1, red, N, I, P = gel(x,1), E = gel(x,2);
  n = nf_get_degree(nf);
  x = idealchineseinit(nf, mkvec2(x,pl));
  x1 = gel(x,1);
  red = lg(x1) == 1? matid(n): gmael(x1,1,1);
  y0 = idealchinese(nf, x, y);

  E = shallowcopy(E);
  if (!gequal0(y0))
    for (i=1; i<lg(E); i++)
    {
      long v = nfval(nf,y0,gel(P,i));
      if (cmpsi(v, gel(E,i)) < 0) gel(E,i) = stoi(v);
    }
  /* N and I : known factors */
  I = factorbackprime(nf, P, E);
  N = idealnorm(nf,I);

  y1 = backtrackfacto(y0, n, red, pl, nf, data, test, fa, N, I);

  /* restore known factors */
  for (i=1; i<lg(E); i++) gel(E,i) = stoi(nfval(nf,y1,gel(P,i)));
  *fa = famat_reduce(famat_mul_shallow(*fa, mkmat2(P, E)));
  return gc_all(av, 2, &y1, fa);
}

static GEN
factoredextchinese(GEN nf, GEN x, GEN y, GEN pl, GEN* fa)
{ return factoredextchinesetest(nf,x,y,pl,fa,NULL,NULL); }

/** OPERATIONS ON ASSOCIATIVE ALGEBRAS algebras.c **/

/*
Convention:
(K/F,sigma,b) = sum_{i=0..n-1} u^i*K
t*u = u*sigma(t)

Natural basis:
1<=i<=d*n^2
b_i = u^((i-1)/(dn))*ZKabs.((i-1)%(dn)+1)

Integral basis:
Basis of some order.

al structure:
1- rnf of the cyclic splitting field of degree n over the center nf of degree d
2- VEC of aut^i 1<=i<=n if n>1, or i=0 if n=1
3- b in nf
4- infinite hasse invariants (mod n) : VECSMALL of size r1, values only 0 or n/2 (if integral)
5- finite hasse invariants (mod n) : VEC[sorted VEC of primes, VECSMALL of hasse inv mod n]
6- VEC
  6.1- 0, or [a,b,sa] where sa^2=a if al is quaternion algebra (a,b)
  6.2- dn^2*dn^2 matrix of stored involution
7* dn^2*dn^2 matrix expressing the integral basis in terms of the natural basis
8* dn^2*dn^2 matrix expressing the natural basis in terms of the integral basis
9* VEC of dn^2 matrices giving the dn^2*dn^2 left multiplication tables of the integral basis
10* characteristic of the base field (used only for algebras given by a multiplication table)
11* trace of basis elements

If al is given by a multiplication table (al_TABLE), only the * fields are present.
The other ones are filled with gen_0 placeholders.
*/

/* assumes same center and same variable */
/* currently only works for coprime degrees */
GEN
algtensor(GEN al1, GEN al2, long flag) {
  pari_sp av = avma;
  long v, k, d1, d2;
  GEN nf, P1, P2, aut1, aut2, b1, b2, C, rnf, aut, b, x1, x2, al, rnfpol;

  checkalg(al1);
  checkalg(al2);
  if (alg_type(al1) != al_CYCLIC  || alg_type(al2) != al_CYCLIC)
    pari_err_IMPL("tensor of noncyclic algebras"); /* TODO: do it. */

  nf = alg_get_center(al1);
  if (!gequal(alg_get_center(al2),nf))
    pari_err_OP("tensor product [not the same center]", al1, al2);

  P1=alg_get_splitpol(al1); aut1=alg_get_aut(al1); b1=alg_get_b(al1);
  P2=alg_get_splitpol(al2); aut2=alg_get_aut(al2); b2=alg_get_b(al2);
  v=varn(P1);

  d1=alg_get_degree(al1);
  d2=alg_get_degree(al2);
  if (ugcd(d1,d2) != 1)
    pari_err_IMPL("tensor of cyclic algebras of noncoprime degrees"); /* TODO */

  if (d1==1) return gcopy(al2);
  if (d2==1) return gcopy(al1);

  C = nfcompositum(nf, P1, P2, 3);
  rnfpol = gel(C,1);
  if (!(flag & al_FACTOR)) rnfpol = mkvec2(rnfpol, stoi(1<<20));
  rnf = rnfinit(nf, rnfpol);
  /* TODO use integral basis of P1 and P2 to get that of C */
  x1 = gel(C,2);
  x2 = gel(C,3);
  k = itos(gel(C,4));
  aut = gadd(gsubst(aut2,v,x2),gmulsg(k,gsubst(aut1,v,x1)));
  b = nfmul(nf,nfpow_u(nf,b1,d2),nfpow_u(nf,b2,d1));
  al = alg_cyclic(rnf, aut, b, flag);
  return gc_GEN(av,al);
}

/* M an n x d Flm of rank d, n >= d. Initialize Mx = y solver */
static GEN
Flm_invimage_init(GEN M, ulong p)
{
  GEN v = Flm_indexrank(M, p), perm = gel(v,1);
  GEN MM = rowpermute(M, perm); /* square invertible */
  return mkvec2(Flm_inv(MM,p), perm);
}
/* assume Mx = y has a solution, v = Flm_invimage_init(M,p); return x */
static GEN
Flm_invimage_pre(GEN v, GEN y, ulong p)
{
  GEN inv = gel(v,1), perm = gel(v,2);
  return Flm_Flc_mul(inv, vecsmallpermute(y, perm), p);
}

GEN
algradical(GEN al)
{
  pari_sp av = avma;
  GEN I, x, traces, K, MT, P, mt;
  long l,i,ni, n;
  ulong modu, expo, p;
  checkalg(al);
  if (alg_type(al) != al_TABLE) return gen_0;
  P = alg_get_char(al);
  mt = alg_get_multable(al);
  n = alg_get_absdim(al);
  dbg_printf(1)("algradical: char=%Ps, dim=%d\n", P, n);
  traces = algtracematrix(al);
  if (!signe(P))
  {
    dbg_printf(2)(" char 0, computing kernel...\n");
    K = ker(traces);
    dbg_printf(2)(" ...done.\n");
    ni = lg(K)-1; if (!ni) return gc_const(av, gen_0);
    return gc_upto(av, K);
  }
  dbg_printf(2)(" char>0, computing kernel...\n");
  K = FpM_ker(traces, P);
  dbg_printf(2)(" ...done.\n");
  ni = lg(K)-1; if (!ni) return gc_const(av, gen_0);
  if (abscmpiu(P,n)>0) return gc_upto(av, K);

  /* tough case, p <= n. Ronyai's algorithm */
  p = P[2]; l = 1;
  expo = p; modu = p*p;
  dbg_printf(2)(" char>0, hard case.\n");
  while (modu<=(ulong)n) { l++; modu *= p; }
  MT = ZMV_to_FlmV(mt, modu);
  I = ZM_to_Flm(K,p); /* I_0 */
  for (i=1; i<=l; i++) {/*compute I_i, expo = p^i, modu = p^(l+1) > n*/
    long j, lig,col;
    GEN v = cgetg(ni+1, t_VECSMALL);
    GEN invI = Flm_invimage_init(I, p);
    dbg_printf(2)(" computing I_%d:\n", i);
    traces = cgetg(ni+1,t_MAT);
    for (j = 1; j <= ni; j++)
    {
      GEN M = algbasismultable_Flm(MT, gel(I,j), modu);
      uel(v,j) = algtracei(M, p,expo,modu);
    }
    for (col=1; col<=ni; col++)
    {
      GEN t = cgetg(n+1,t_VECSMALL); gel(traces,col) = t;
      x = gel(I, col); /*col-th basis vector of I_{i-1}*/
      for (lig=1; lig<=n; lig++)
      {
        GEN y = _tablemul_ej_Fl(MT,x,lig,p);
        GEN z = Flm_invimage_pre(invI, y, p);
        uel(t,lig) = Flv_dotproduct(v, z, p);
      }
    }
    dbg_printf(2)(" computing kernel...\n");
    K = Flm_ker(traces, p);
    dbg_printf(2)(" ...done.\n");
    ni = lg(K)-1; if (!ni) return gc_const(av, gen_0);
    I = Flm_mul(I,K,p);
    expo *= p;
  }
  return Flm_to_ZM(I);
}

/* compute the multiplication table of the element x, where mt is a
 * multiplication table in an arbitrary ring */
static GEN
Rgmultable(GEN mt, GEN x)
{
  long i, l = lg(x);
  GEN z = NULL;
  for (i = 1; i < l; i++)
  {
    GEN c = gel(x,i);
    if (!gequal0(c))
    {
      GEN M = RgM_Rg_mul(gel(mt,i),c);
      z = z? RgM_add(z, M): M;
    }
  }
  return z;
}

static GEN
change_Rgmultable(GEN mt, GEN P, GEN Pi)
{
  GEN mt2;
  long lmt = lg(mt), i;
  mt2 = cgetg(lmt,t_VEC);
  for (i=1;i<lmt;i++) {
    GEN mti = Rgmultable(mt,gel(P,i));
    gel(mt2,i) = RgM_mul(Pi, RgM_mul(mti,P));
  }
  return mt2;
}

/* S: lift (basis of quotient) ; Si: proj */
static GEN
alg_quotient0(GEN al, GEN S, GEN Si, long nq, GEN p, long maps)
{
  GEN mt = cgetg(nq+1,t_VEC), P, Pi, d;
  long i;
  dbg_printf(3)("  alg_quotient0: char=%Ps, dim=%d, dim I=%d\n", p, alg_get_absdim(al), lg(S)-1);
  for (i=1; i<=nq; i++) {
    GEN mti = algbasismultable(al,gel(S,i));
    if (signe(p)) gel(mt,i) = FpM_mul(Si, FpM_mul(mti,S,p), p);
    else          gel(mt,i) = RgM_mul(Si, RgM_mul(mti,S));
  }
  if (!signe(p) && !isint1(Q_denom(mt))) {
    dbg_printf(3)("  bad case: denominator=%Ps\n", Q_denom(mt));
    P = Q_remove_denom(Si,&d);
    P = ZM_hnf(P);
    P = RgM_Rg_div(P,d); /* P: new basis (Z-basis of image of order in al) */
    Pi = RgM_inv(P);
    mt = change_Rgmultable(mt,P,Pi);
    Si = RgM_mul(Pi,Si);
    S = RgM_mul(S,P);
  }
  al = algtableinit_i(mt,p);
  if (maps) al = mkvec3(al,Si,S); /* algebra, proj, lift */
  return al;
}

/* quotient of an algebra by a nontrivial two-sided ideal */
GEN
alg_quotient(GEN al, GEN I, long maps)
{
  pari_sp av = avma;
  GEN p, IS, ISi, S, Si;
  long n, ni;

  checkalg(al);
  if (alg_type(al) != al_TABLE) pari_err_TYPE("alg_quotient [not a table algebra]", al);
  p = alg_get_char(al);
  n = alg_get_absdim(al);
  ni = lg(I)-1;

  /* force first vector of complement to be the identity */
  IS = shallowconcat(I, gcoeff(alg_get_multable(al),1,1));
  if (signe(p)) {
    IS = FpM_suppl(IS,p);
    ISi = FpM_inv(IS,p);
  }
  else {
    IS = suppl(IS);
    ISi = RgM_inv(IS);
  }
  S = vecslice(IS, ni+1, n);
  Si = rowslice(ISi, ni+1, n);
  return gc_GEN(av, alg_quotient0(al, S, Si, n-ni, p, maps));
}

static GEN
image_keep_first(GEN m, GEN p) /* assume first column is nonzero or m==0, no GC */
{
  GEN ir, icol, irow, M, c, x;
  long i;
  if (gequal0(gel(m,1))) return zeromat(nbrows(m),0);

  if (signe(p)) ir = FpM_indexrank(m,p);
  else          ir = indexrank(m);

  icol = gel(ir,2);
  if (icol[1]==1) return extract0(m,icol,NULL);

  irow = gel(ir,1);
  M = extract0(m, irow, icol);
  c = extract0(gel(m,1), irow, NULL);
  if (signe(p)) x = FpM_FpC_invimage(M,c,p);
  else          x = inverseimage(M,c); /* TODO modulo a small prime */

  for (i=1; i<lg(x); i++)
  {
    if (!gequal0(gel(x,i)))
    {
      icol[i] = 1;
      vecsmall_sort(icol);
      return extract0(m,icol,NULL);
    }
  }

  return NULL; /* LCOV_EXCL_LINE */
}

/* z[1],...z[nz] central elements such that z[1]A + z[2]A + ... + z[nz]A = A
 * is a direct sum. idempotents ==> first basis element is identity */
GEN
alg_centralproj(GEN al, GEN z, long maps)
{
  pari_sp av = avma;
  GEN S, U, Ui, alq, p;
  long i, iu, lz = lg(z), ta;

  checkalg(al);
  ta = alg_type(al);
  if (ta != al_TABLE) pari_err_TYPE("algcentralproj [not a table algebra]", al);
  if (typ(z) != t_VEC) pari_err_TYPE("alcentralproj",z);
  p = alg_get_char(al);
  dbg_printf(3)("  alg_centralproj: char=%Ps, dim=%d, #z=%d\n", p, alg_get_absdim(al), lz-1);
  S = cgetg(lz,t_VEC); /* S[i] = Im(z_i) */
  for (i=1; i<lz; i++)
  {
    GEN mti = algbasismultable(al, gel(z,i));
    gel(S,i) = image_keep_first(mti,p);
  }
  U = shallowconcat1(S); /* U = [Im(z_1)|Im(z_2)|...|Im(z_nz)], n x n */
  if (lg(U)-1 < alg_get_absdim(al)) pari_err_TYPE("alcentralproj [z[i]'s not surjective]",z);
  if (signe(p)) Ui = FpM_inv(U,p);
  else          Ui = RgM_inv(U);
  if (!Ui) pari_err_BUG("alcentralproj"); /*LCOV_EXCL_LINE*/

  alq = cgetg(lz,t_VEC);
  for (iu=0,i=1; i<lz; i++)
  {
    long nq = lg(gel(S,i))-1, ju = iu + nq;
    GEN Si = rowslice(Ui, iu+1, ju);
    gel(alq, i) = alg_quotient0(al,gel(S,i),Si,nq,p,maps);
    iu = ju;
  }
  return gc_GEN(av, alq);
}

/* al is an al_TABLE */
static GEN
algtablecenter(GEN al)
{
  pari_sp av = avma;
  long n, i, j, k, ic;
  GEN C, cij, mt, p;

  n = alg_get_absdim(al);
  mt = alg_get_multable(al);
  p = alg_get_char(al);
  C = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(C,j) = cgetg(n*n-n+1,t_COL);
    ic = 1;
    for (i=2; i<=n; i++) {
      if (signe(p)) cij = FpC_sub(gmael(mt,i,j),gmael(mt,j,i),p);
      else          cij = RgC_sub(gmael(mt,i,j),gmael(mt,j,i));
      for (k=1; k<=n; k++, ic++) gcoeff(C,ic,j) = gel(cij, k);
    }
  }
  if (signe(p)) return gc_upto(av, FpM_ker(C,p));
  else          return gc_upto(av, ker(C));
}

GEN
algcenter(GEN al)
{
  checkalg(al);
  if (alg_type(al)==al_TABLE) return algtablecenter(al);
  return alg_get_center(al);
}

/* Only in positive characteristic. Assumes that al is semisimple. */
GEN
algprimesubalg(GEN al)
{
  pari_sp av = avma;
  GEN p, Z, F, K;
  long nz, i;
  checkalg(al);
  p = alg_get_char(al);
  if (!signe(p)) pari_err_DOMAIN("algprimesubalg","characteristic","=",gen_0,p);

  Z = algtablecenter(al);
  nz = lg(Z)-1;
  if (nz==1) return Z;

  F = cgetg(nz+1, t_MAT);
  for (i=1; i<=nz; i++) {
    GEN zi = gel(Z,i);
    gel(F,i) = FpC_sub(algpow(al,zi,p),zi,p);
  }
  K = FpM_ker(F,p);
  return gc_upto(av, FpM_mul(Z,K,p));
}

static GEN
out_decompose(GEN t, GEN Z, GEN P, GEN p)
{
  GEN ali = gel(t,1), projm = gel(t,2), liftm = gel(t,3), pZ;
  if (signe(p)) pZ = FpM_image(FpM_mul(projm,Z,p),p);
  else          pZ = image(RgM_mul(projm,Z));
  return mkvec5(ali, projm, liftm, pZ, P);
}
/* fa factorization of charpol(x) */
static GEN
alg_decompose_from_facto(GEN al, GEN x, GEN fa, GEN Z, long mini)
{
  long k = lgcols(fa)-1, k2 = mini? 1: k/2;
  GEN v1 = rowslice(fa,1,k2);
  GEN v2 = rowslice(fa,k2+1,k);
  GEN alq, P, Q, p = alg_get_char(al);
  dbg_printf(3)("  alg_decompose_from_facto\n");
  if (signe(p)) {
    P = FpXV_factorback(gel(v1,1), gel(v1,2), p, 0);
    Q = FpXV_factorback(gel(v2,1), gel(v2,2), p, 0);
    P = FpX_mul(P, FpXQ_inv(P,Q,p), p);
  }
  else {
    P = factorback(v1);
    Q = factorback(v2);
    P = RgX_mul(P, RgXQ_inv(P,Q));
  }
  P = algpoleval(al, P, x);
  if (signe(p)) Q = FpC_sub(col_ei(lg(P)-1,1), P, p);
  else          Q = gsub(gen_1, P);
  if (gequal0(P) || gequal0(Q)) return NULL;
  alq = alg_centralproj(al, mkvec2(P,Q), 1);

  P = out_decompose(gel(alq,1), Z, P, p); if (mini) return P;
  Q = out_decompose(gel(alq,2), Z, Q, p);
  return mkvec2(P,Q);
}

static GEN
random_pm1(long n)
{
  GEN z = cgetg(n+1,t_VECSMALL);
  long i;
  for (i = 1; i <= n; i++) z[i] = random_bits(5)%3 - 1;
  return z;
}

static GEN alg_decompose(GEN al, GEN Z, long mini, GEN* pt_primelt);
/* Try to split al using x's charpoly. Return gen_0 if simple, NULL if failure.
 * And a splitting otherwise
 * If pt_primelt!=NULL, compute a primitive element of the center when simple */
static GEN
try_fact(GEN al, GEN x, GEN zx, GEN Z, GEN Zal, long mini, GEN* pt_primelt)
{
  GEN z, dec0, dec1, cp = algcharpoly(Zal,zx,0,1), fa, p = alg_get_char(al);
  long nfa, e;
  dbg_printf(3)("  try_fact: zx=%Ps\n", zx);
  if (signe(p)) fa = FpX_factor(cp,p);
  else          fa = factor(cp);
  dbg_printf(3)("  charpoly=%Ps\n", fa);
  nfa = nbrows(fa);
  if (nfa == 1) {
    if (signe(p)) e = gel(fa,2)[1];
    else          e = itos(gcoeff(fa,1,2));
    if (e == 1) {
      if (pt_primelt != NULL) *pt_primelt = mkvec2(x, cp);
      return gen_0;
    }
    else return NULL;
  }
  dec0 = alg_decompose_from_facto(al, x, fa, Z, mini);
  if (!dec0) return NULL;
  if (!mini) return dec0;
  dec1 = alg_decompose(gel(dec0,1), gel(dec0,4), 1, pt_primelt);
  z = gel(dec0,5);
  if (!isintzero(dec1)) {
    if (signe(p)) z = FpM_FpC_mul(gel(dec0,3),dec1,p);
    else          z = RgM_RgC_mul(gel(dec0,3),dec1);
  }
  return z;
}
static GEN
randcol(long n, GEN b)
{
  GEN N = addiu(shifti(b,1), 1);
  long i;
  GEN res =  cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    pari_sp av = avma;
    gel(res,i) = gc_INT(av, subii(randomi(N),b));
  }
  return res;
}
/* Return gen_0 if already simple. mini: only returns a central idempotent
 * corresponding to one simple factor
 * if pt_primelt!=NULL, sets it to a primitive element of the center when simple */
static GEN
alg_decompose(GEN al, GEN Z, long mini, GEN* pt_primelt)
{
  pari_sp av;
  GEN Zal, x, zx, rand, dec0, B, p;
  long i, nz = lg(Z)-1;

  if (nz == 1) {
    if (pt_primelt != 0) *pt_primelt = mkvec2(zerocol(alg_get_dim(al)), pol_x(0));
    return gen_0;
  }
  p = alg_get_char(al);
  dbg_printf(2)(" alg_decompose: char=%Ps, dim=%d, dim Z=%d\n", p, alg_get_absdim(al), nz);
  Zal = alg_subalg(al,Z);
  Z = gel(Zal,2);
  Zal = gel(Zal,1);
  av = avma;

  rand = random_pm1(nz);
  zx = zc_to_ZC(rand);
  if (signe(p)) {
    zx = FpC_red(zx,p);
    x = ZM_zc_mul(Z,rand);
    x = FpC_red(x,p);
  }
  else x = RgM_zc_mul(Z,rand);
  dec0 = try_fact(al,x,zx,Z,Zal,mini,pt_primelt);
  if (dec0) return dec0;
  set_avma(av);

  for (i=2; i<=nz; i++)
  {
    dec0 = try_fact(al,gel(Z,i),col_ei(nz,i),Z,Zal,mini,pt_primelt);
    if (dec0) return dec0;
    set_avma(av);
  }
  B = int2n(10);
  for (;;)
  {
    GEN x = randcol(nz,B), zx = ZM_ZC_mul(Z,x);
    dec0 = try_fact(al,x,zx,Z,Zal,mini,pt_primelt);
    if (dec0) return dec0;
    set_avma(av);
  }
}

static GEN
alg_decompose_total(GEN al, GEN Z, long maps)
{
  GEN dec, sc, p;
  long i;

  dec = alg_decompose(al, Z, 0, NULL);
  if (isintzero(dec))
  {
    if (maps) {
      long n = alg_get_absdim(al);
      al = mkvec3(al, matid(n), matid(n));
    }
    return mkvec(al);
  }
  p = alg_get_char(al); if (!signe(p)) p = NULL;
  sc = cgetg(lg(dec), t_VEC);
  for (i=1; i<lg(sc); i++) {
    GEN D = gel(dec,i), a = gel(D,1), Za = gel(D,4);
    GEN S = alg_decompose_total(a, Za, maps);
    gel(sc,i) = S;
    if (maps)
    {
      GEN projm = gel(D,2), liftm = gel(D,3);
      long j, lS = lg(S);
      for (j=1; j<lS; j++)
      {
        GEN Sj = gel(S,j), p2 = gel(Sj,2), l2 = gel(Sj,3);
        if (p) p2 = FpM_mul(p2, projm, p);
        else   p2 = RgM_mul(p2, projm);
        if (p) l2 = FpM_mul(liftm, l2, p);
        else   l2 = RgM_mul(liftm, l2);
        gel(Sj,2) = p2;
        gel(Sj,3) = l2;
      }
    }
  }
  return shallowconcat1(sc);
}

static GEN
alg_subalg(GEN al, GEN basis)
{
  GEN invbasis, mt, p = alg_get_char(al);
  long i, j, n;

  if (!signe(p)) p = NULL;
  basis = shallowmatconcat(mkvec2(col_ei(alg_get_absdim(al),1), basis));
  if (p)
  {
    basis = image_keep_first(basis,p);
    invbasis = FpM_inv(basis,p);
  }
  else
  { /* FIXME use an integral variant of image_keep_first */
    basis = QM_ImQ_hnf(basis);
    invbasis = RgM_inv(basis);
  }
  n = lg(basis)-1;
  mt = cgetg(n+1,t_VEC);
  gel(mt,1) = matid(n);
  for (i = 2; i <= n; i++)
  {
    GEN mtx = cgetg(n+1,t_MAT), x = gel(basis,i);
    gel(mtx,1) = col_ei(n,i);
    for (j = 2; j <= n; j++)
    {
      GEN xy = algmul(al, x, gel(basis,j));
      if (p) gel(mtx,j) = FpM_FpC_mul(invbasis, xy, p);
      else   gel(mtx,j) = RgM_RgC_mul(invbasis, xy);
    }
    gel(mt,i) = mtx;
  }
  return mkvec2(algtableinit_i(mt,p), basis);
}

GEN
algsubalg(GEN al, GEN basis)
{
  pari_sp av = avma;
  GEN p;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("algsubalg [real algebra]", al);
  if (typ(basis) != t_MAT) pari_err_TYPE("algsubalg",basis);
  p = alg_get_char(al);
  if (signe(p)) basis = RgM_to_FpM(basis,p);
  return gc_GEN(av, alg_subalg(al,basis));
}

static int
cmp_algebra(GEN x, GEN y)
{
  long d;
  d = gel(x,1)[1] - gel(y,1)[1]; if (d) return d < 0? -1: 1;
  d = gel(x,1)[2] - gel(y,1)[2]; if (d) return d < 0? -1: 1;
  return cmp_universal(gel(x,2), gel(y,2));
}

GEN
algsimpledec_ss(GEN al, long maps)
{
  pari_sp av = avma;
  GEN Z, p, r, res, perm;
  long i, l, n;
  checkalg(al);
  p = alg_get_char(al);
  dbg_printf(1)("algsimpledec_ss: char=%Ps, dim=%d\n", p, alg_get_absdim(al));
  if (signe(p))                     Z = algprimesubalg(al);
  else if (alg_type(al)!=al_TABLE)  Z = gen_0;
  else                              Z = algtablecenter(al);

  if (lg(Z) == 2) {/* dim Z = 1 */
    n = alg_get_absdim(al);
    set_avma(av);
    if (!maps) return mkveccopy(al);
    retmkvec(mkvec3(gcopy(al), matid(n), matid(n)));
  }
  res = alg_decompose_total(al, Z, maps);
  l = lg(res); r = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN A = maps? gmael(res,i,1): gel(res,i);
    gel(r,i) = mkvec2(mkvecsmall2(alg_get_dim(A), lg(algtablecenter(A))),
                      alg_get_multable(A));
  }
  perm = gen_indexsort(r, (void*)cmp_algebra, &cmp_nodata);
  return gc_GEN(av, vecpermute(res, perm));
}

GEN
algsimpledec(GEN al, long maps)
{
  pari_sp av = avma;
  int ss;
  GEN rad, dec, res, proj=NULL, lift=NULL;
  rad = algradical(al);
  ss = gequal0(rad);
  if (!ss)
  {
    al = alg_quotient(al, rad, maps);
    if (maps) {
      proj = gel(al,2);
      lift = gel(al,3);
      al = gel(al,1);
    }
  }
  dec = algsimpledec_ss(al, maps);
  if (!ss && maps) /* update maps */
  {
    GEN p = alg_get_char(al);
    long i;
    for (i=1; i<lg(dec); i++)
    {
      if (signe(p))
      {
        gmael(dec,i,2) = FpM_mul(gmael(dec,i,2), proj, p);
        gmael(dec,i,3) = FpM_mul(lift, gmael(dec,i,3), p);
      }
      else
      {
        gmael(dec,i,2) = RgM_mul(gmael(dec,i,2), proj);
        gmael(dec,i,3) = RgM_mul(lift, gmael(dec,i,3));
      }
    }
  }
  res = mkvec2(rad, dec);
  return gc_GEN(av,res);
}

static GEN alg_idempotent(GEN al, long n, long d);
static GEN
try_split(GEN al, GEN x, long n, long d)
{
  GEN cp, p = alg_get_char(al), fa, e, pol, exp, P, Q, U, u, mx, mte, ire;
  long nfa, i, smalldim = alg_get_absdim(al)+1, dim, smalli = 0;
  cp = algcharpoly(al,x,0,1);
  fa = FpX_factor(cp,p);
  nfa = nbrows(fa);
  if (nfa == 1) return NULL;
  pol = gel(fa,1);
  exp = gel(fa,2);

  /* charpoly is always a d-th power */
  for (i=1; i<lg(exp); i++) {
    if (exp[i]%d) pari_err(e_MISC, "the algebra must be simple (try_split 1)");
    exp[i] /= d;
  }
  cp = FpXV_factorback(gel(fa,1), gel(fa,2), p, 0);

  /* find smallest Fp-dimension of a characteristic space */
  for (i=1; i<lg(pol); i++) {
    dim = degree(gel(pol,i))*exp[i];
    if (dim < smalldim) {
      smalldim = dim;
      smalli = i;
    }
  }
  i = smalli;
  if (smalldim != n) return NULL;
  /* We could also compute e*al*e and try again with this smaller algebra */
  /* Fq-rank 1 = Fp-rank n idempotent: success */

  /* construct idempotent */
  mx = algbasismultable(al,x);
  P = gel(pol,i);
  P = FpX_powu(P, exp[i], p);
  Q = FpX_div(cp, P, p);
  e = algpoleval(al, Q, mkvec2(x,mx));
  U = FpXQ_inv(Q, P, p);
  u = algpoleval(al, U, mkvec2(x,mx));
  e = algbasismul(al, e, u);
  mte = algbasisrightmultable(al,e);
  ire = FpM_indexrank(mte,p);
  if (lg(gel(ire,1))-1 != smalldim*d) pari_err(e_MISC, "the algebra must be simple (try_split 2)");

  return mkvec3(e,mte,ire);
}

/*
 * Given a simple algebra al of dimension d^2 over its center of degree n,
 * find an idempotent e in al with rank n (which is minimal).
*/
static GEN
alg_idempotent(GEN al, long n, long d)
{
  pari_sp av = avma;
  long i, N = alg_get_absdim(al);
  GEN e, p = alg_get_char(al), x;
  for(i=2; i<=N; i++) {
    x = col_ei(N,i);
    e = try_split(al, x, n, d);
    if (e) return e;
    set_avma(av);
  }
  for(;;) {
    x = random_FpC(N,p);
    e = try_split(al, x, n, d);
    if (e) return e;
    set_avma(av);
  }
}

static GEN
try_descend(GEN M, GEN B, GEN p, long m, long n, long d)
{
  GEN B2 = cgetg(m+1,t_MAT), b;
  long i, j, k=0;
  for (i=1; i<=d; i++)
  {
    k++;
    b = gel(B,i);
    gel(B2,k) = b;
    for (j=1; j<n; j++)
    {
      k++;
      b = FpM_FpC_mul(M,b,p);
      gel(B2,k) = b;
    }
  }
  if (!signe(FpM_det(B2,p))) return NULL;
  return FpM_inv(B2,p);
}

/* Given an m*m matrix M with irreducible charpoly over F of degree n,
 * let K = F(M), which is a field, and write m=d*n.
 * Compute the d-dimensional K-vector space structure on V=F^m induced by M.
 * Return [B,C] where:
 *  - B is m*d matrix over F giving a K-basis b_1,...,b_d of V
 *  - C is d*m matrix over F[x] expressing the canonical F-basis of V on the b_i
 * Currently F = Fp TODO extend this. */
static GEN
descend_i(GEN M, long n, GEN p)
{
  GEN B, C;
  long m,d,i;
  pari_sp av;
  m = lg(M)-1;
  d = m/n;
  B = cgetg(d+1,t_MAT);
  av = avma;

  /* try a subset of the canonical basis */
  for (i=1; i<=d; i++)
    gel(B,i) = col_ei(m,n*(i-1)+1);
  C = try_descend(M,B,p,m,n,d);
  if (C) return mkvec2(B,C);
  set_avma(av);

  /* try smallish elements */
  for (i=1; i<=d; i++)
    gel(B,i) = FpC_red(zc_to_ZC(random_pm1(m)),p);
  C = try_descend(M,B,p,m,n,d);
  if (C) return mkvec2(B,C);
  set_avma(av);

  /* try random elements */
  for (;;)
  {
    for (i=1; i<=d; i++)
      gel(B,i) = random_FpC(m,p);
    C = try_descend(M,B,p,m,n,d);
    if (C) return mkvec2(B,C);
    set_avma(av);
  }
}
static GEN
RgC_contract(GEN C, long n, long v) /* n>1 */
{
  GEN C2, P;
  long m, d, i, j;
  m = lg(C)-1;
  d = m/n;
  C2 = cgetg(d+1,t_COL);
  for (i=1; i<=d; i++)
  {
    P = pol_xn(n-1,v);
    for (j=1; j<=n; j++)
      gel(P,j+1) = gel(C,n*(i-1)+j);
    P = normalizepol(P);
    gel(C2,i) = P;
  }
  return C2;
}
static GEN
RgM_contract(GEN A, long n, long v) /* n>1 */
{
  GEN A2 = cgetg(lg(A),t_MAT);
  long i;
  for (i=1; i<lg(A2); i++)
    gel(A2,i) = RgC_contract(gel(A,i),n,v);
  return A2;
}
static GEN
descend(GEN M, long n, GEN p, long v)
{
  GEN res = descend_i(M,n,p);
  gel(res,2) = RgM_contract(gel(res,2),n,v);
  return res;
}

/* isomorphism of Fp-vector spaces M_d(F_p^n) -> (F_p)^(d^2*n) */
static GEN
RgM_mat2col(GEN M, long d, long n)
{
  long nd = d*n,  N = d*nd, i, j, ni, nj;
  GEN C = cgetg(N+1, t_COL);
  for (i=1, ni = 0; i<=d; i++, ni += nd)
    for (j=1, nj = 0; j<=d; j++, nj += n)
    {
      GEN P = gcoeff(M,i,j);
      long k, e = ni + nj + 1;
      if (typ(P)==t_POL)
      {
        long dP = degpol(P);
        for (k = 0; k <= dP; k++)
          gel(C,e+k) = gel(P,k+2);
      } else
      {
        gel(C,e) = P;
        k = 1;
      }
      for (  ; k < n; k++)
        gel(C,e+k) = gen_0;
    }
  return C;
}
/* inverse isomorphism */
static GEN
RgC_col2mat(GEN C, long d, long n, long v)
{
  long i, j, start;
  GEN M = cgetg(d+1, t_MAT), cM;
  for (j=1; j<=d; j++)
  {
    cM = cgetg(d+1, t_COL);
    for (i=1; i<=d; i++)
    {
      start = n*(d*(i-1)+j-1)+1;
      if (n==1) gel(cM,i) = gel(C, start);
      else gel(cM,i) = RgV_to_RgX(vecslice(C, start, start+n-1), v);
    }
    gel(M,j) = cM;
  }
  return M;
}

static GEN
alg_finite_csa_split(GEN al, long v)
{
  GEN Z, e, mte, ire, primelt, b, T, M, proje, lifte, extre, p, B, C, mt, mx, map, mapi, T2, ro;
  long n, d, N = alg_get_absdim(al), i;
  p = alg_get_char(al);
  /* compute the center */
  Z = algcenter(al);
  /* TODO option to give the center as input instead of computing it */
  n = lg(Z)-1;

  /* compute a minimal rank idempotent e */
  if (n==N) {
    d = 1;
    e = col_ei(N,1);
    mte = matid(N);
    ire = mkvec2(identity_perm(n),identity_perm(n));
  }
  else {
    d = usqrt(N/n);
    if (d*d*n != N) pari_err(e_MISC, "the algebra must be simple (alg_finite_csa_split 1)");
    e = alg_idempotent(al,n,d);
    mte = gel(e,2);
    ire = gel(e,3);
    e = gel(e,1);
  }

  /* identify the center */
  if (n==1)
  {
    T = pol_x(v);
    primelt = gen_0;
  }
  else
  {
    b = alg_decompose(al, Z, 1, &primelt);
    if (!gequal0(b)) pari_err(e_MISC, "the algebra must be simple (alg_finite_csa_split 2)");
    T = gel(primelt,2);
    primelt = gel(primelt,1);
    setvarn(T,v);
  }

  /* use the ffinit polynomial */
  if (n>1)
  {
    T2 = init_Fq(p,n,v);
    setvarn(T,fetch_var_higher());
    ro = FpXQX_roots(T2,T,p);
    ro = gel(ro,1);
    primelt = algpoleval(al,ro,primelt);
    T = T2;
    delete_var();
  }

  /* descend al*e to a vector space over the center */
  /* lifte: al*e -> al ; proje: al*e -> al */
  lifte = shallowextract(mte,gel(ire,2));
  extre = shallowmatextract(mte,gel(ire,1),gel(ire,2));
  extre = FpM_inv(extre,p);
  proje = rowpermute(mte,gel(ire,1));
  proje = FpM_mul(extre,proje,p);
  if (n==1)
  {
    B = lifte;
    C = proje;
  }
  else
  {
    M = algbasismultable(al,primelt);
    M = FpM_mul(M,lifte,p);
    M = FpM_mul(proje,M,p);
    B = descend(M,n,p,v);
    C = gel(B,2);
    B = gel(B,1);
    B = FpM_mul(lifte,B,p);
    C = FqM_mul(C,proje,T,p);
  }

  /* compute the isomorphism */
  mt = alg_get_multable(al);
  map = cgetg(N+1,t_VEC);
  M = cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++)
  {
    mx = gel(mt,i);
    mx = FpM_mul(mx,B,p);
    mx = FqM_mul(C,mx,T,p);
    gel(map,i) = mx;
    gel(M,i) = RgM_mat2col(mx,d,n);
  }
  mapi = FpM_inv(M,p);
  if (!mapi) pari_err(e_MISC, "the algebra must be simple (alg_finite_csa_split 3)");
  return mkvec4(T,map,mapi,M);
}

GEN
algsplit(GEN al, long v)
{
  pari_sp av = avma;
  GEN res, T, map, mapi, ff, p;
  long i,j,k,li,lj;
  checkalg(al);
  p = alg_get_char(al);
  if (gequal0(p))
    pari_err_IMPL("splitting a characteristic 0 algebra over its center");
  res = alg_finite_csa_split(al, v);
  T = gel(res,1);
  map = gel(res,2);
  mapi = gel(res,3);
  ff = Tp_to_FF(T,p);
  for (i=1; i<lg(map); i++)
  {
    li = lg(gel(map,i));
    for (j=1; j<li; j++)
    {
      lj = lg(gmael(map,i,j));
      for (k=1; k<lj; k++)
        gmael3(map,i,j,k) = Fq_to_FF(gmael3(map,i,j,k),ff);
    }
  }

  return gc_GEN(av, mkvec2(map,mapi));
}

/* multiplication table sanity checks */
static GEN
check_mt_noid(GEN mt, GEN p)
{
  long i, l;
  GEN MT = cgetg_copy(mt, &l);
  if (typ(MT) != t_VEC || l == 1) return NULL;
  for (i = 1; i < l; i++)
  {
    GEN M = gel(mt,i);
    if (typ(M) != t_MAT || lg(M) != l || lgcols(M) != l) return NULL;
    if (p) M = RgM_to_FpM(M,p);
    gel(MT,i) = M;
  }
  return MT;
}
static GEN
check_mt(GEN mt, GEN p)
{
  long i;
  GEN MT;
  MT = check_mt_noid(mt, p);
  if (!MT || !ZM_isidentity(gel(MT,1))) return NULL;
  for (i=2; i<lg(MT); i++)
    if (ZC_is_ei(gmael(MT,i,1)) != i) return NULL;
  return MT;
}

static GEN
check_relmt(GEN nf, GEN mt)
{
  long i, l = lg(mt), j, k;
  GEN MT = gcopy(mt), a, b, d;
  if (typ(MT) != t_VEC || l == 1) return NULL;
  for (i = 1; i < l; i++)
  {
    GEN M = gel(MT,i);
    if (typ(M) != t_MAT || lg(M) != l || lgcols(M) != l) return NULL;
    for (k = 1; k < l; k++)
      for (j = 1; j < l; j++)
      {
        a = gcoeff(M,j,k);
        if (typ(a)==t_INT) continue;
        b = algtobasis(nf,a);
        d = Q_denom(b);
        if (!isint1(d))
          pari_err_DOMAIN("alg_csa_table", "denominator(mt)", "!=", gen_1, mt);
        gcoeff(M,j,k) = lift(basistoalg(nf,b));
      }
    if (i > 1 && RgC_is_ei(gel(M,1)) != i) return NULL; /* i = 1 checked at end */
    gel(MT,i) = M;
  }
  if (!RgM_isidentity(gel(MT,1))) return NULL;
  return MT;
}

int
algisassociative(GEN mt0, GEN p)
{
  pari_sp av = avma;
  long i, j, k, n;
  GEN M, mt;

  if (checkalg_i(mt0)) { p = alg_get_char(mt0); mt0 = alg_get_multable(mt0); }
  if (!p) p = gen_0;
  if (typ(p) != t_INT) pari_err_TYPE("algisassociative",p);
  mt = check_mt_noid(mt0, isintzero(p)? NULL: p);
  if (!mt) pari_err_TYPE("algisassociative (mult. table)", mt0);
  if (!ZM_isidentity(gel(mt,1))) return gc_bool(av,0);
  n = lg(mt)-1;
  M = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(M,j) = cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    GEN mi = gel(mt,i);
    for (j=1; j<=n; j++) gcoeff(M,i,j) = gel(mi,j); /* ei.ej */
  }
  for (i=2; i<=n; i++) {
    GEN mi = gel(mt,i);
    for (j=2; j<=n; j++) {
      for (k=2; k<=n; k++) {
        GEN x, y;
        if (signe(p)) {
          x = _tablemul_ej_Fp(mt,gcoeff(M,i,j),k,p);
          y = FpM_FpC_mul(mi,gcoeff(M,j,k),p);
        }
        else {
          x = _tablemul_ej(mt,gcoeff(M,i,j),k);
          y = RgM_RgC_mul(mi,gcoeff(M,j,k));
        }
        /* not cmp_universal: must not fail on 0 == Mod(0,2) for instance */
        if (!gequal(x,y)) return gc_bool(av,0);
      }
    }
  }
  return gc_bool(av,1);
}

int
algiscommutative(GEN al) /* assumes e_1 = 1 */
{
  long i,j,k,N,sp;
  GEN mt,a,b,p;
  checkalg(al);
  if (alg_type(al) != al_TABLE) return alg_get_degree(al)==1;
  N = alg_get_absdim(al);
  mt = alg_get_multable(al);
  p = alg_get_char(al);
  sp = signe(p);
  for (i=2; i<=N; i++)
    for (j=2; j<=N; j++)
      for (k=1; k<=N; k++) {
        a = gcoeff(gel(mt,i),k,j);
        b = gcoeff(gel(mt,j),k,i);
        if (sp) {
          if (cmpii(Fp_red(a,p), Fp_red(b,p))) return 0;
        }
        else if (gcmp(a,b)) return 0;
      }
  return 1;
}

int
algissemisimple(GEN al)
{
  pari_sp av = avma;
  GEN rad;
  checkalg(al);
  if (alg_type(al) != al_TABLE) return 1;
  rad = algradical(al);
  set_avma(av);
  return gequal0(rad);
}

/* ss : known to be semisimple */
int
algissimple(GEN al, long ss)
{
  pari_sp av = avma;
  GEN Z, dec, p;
  checkalg(al);
  if (alg_type(al) != al_TABLE) return 1;
  if (!ss && !algissemisimple(al)) return 0;

  p = alg_get_char(al);
  if (signe(p)) Z = algprimesubalg(al);
  else          Z = algtablecenter(al);

  if (lg(Z) == 2) {/* dim Z = 1 */
    set_avma(av);
    return 1;
  }
  dec = alg_decompose(al, Z, 1, NULL);
  set_avma(av);
  return gequal0(dec);
}

static long
is_place_emb(GEN nf, GEN pl)
{
  long r, r1, r2;
  if (typ(pl) != t_INT) pari_err_TYPE("is_place_emb", pl);
  if (signe(pl)<=0) pari_err_DOMAIN("is_place_emb", "pl", "<=", gen_0, pl);
  nf_get_sign(nf,&r1,&r2); r = r1+r2;
  if (cmpiu(pl,r)>0) pari_err_DOMAIN("is_place_emb", "pl", ">", utoi(r), pl);
  return itou(pl);
}

static long
alghasse_emb(GEN al, long emb)
{
  GEN nf = alg_get_center(al);
  long r1 = nf_get_r1(nf);
  return (emb <= r1)? alg_get_hasse_i(al)[emb]: 0;
}

static long
alghasse_pr(GEN al, GEN pr)
{
  GEN hf = alg_get_hasse_f(al);
  long i = tablesearch(gel(hf,1), pr, &cmp_prime_ideal);
  return i? gel(hf,2)[i]: 0;
}

static long
alghasse_0(GEN al, GEN pl)
{
  long ta;
  GEN pr, nf;
  ta = alg_type(al);
  if (ta == al_REAL) return algreal_dim(al)!=1;
  if (!pl)
    pari_err(e_MISC, "must provide a place pl");
  if (ta == al_CSA && !alg_is_asq(al))
    pari_err_IMPL("computation of Hasse invariants over table CSA");
  if ((pr = get_prid(pl))) return alghasse_pr(al, pr);
  nf = alg_get_center(al);
  return alghasse_emb(al, is_place_emb(nf, pl));
}
GEN
alghasse(GEN al, GEN pl)
{
  long h;
  checkalg(al);
  if (alg_type(al) == al_TABLE) pari_err_TYPE("alghasse [use alginit]",al);
  h = alghasse_0(al,pl);
  return sstoQ(h, alg_get_degree(al));
}

/* h >= 0, d >= 0 */
static long
indexfromhasse(long h, long d) { return d/ugcd(h,d); }

long
algindex(GEN al, GEN pl)
{
  long d, res, i, l, ta;
  GEN hi, hf;

  checkalg(al);
  ta = alg_type(al);
  if (ta == al_TABLE) pari_err_TYPE("algindex [use alginit]",al);
  if (ta == al_REAL) return algreal_dim(al)==1 ? 1 : 2;
  d = alg_get_degree(al);
  if (pl) return indexfromhasse(alghasse_0(al,pl), d);

  /* else : global index */
  res = 1;
  hi = alg_get_hasse_i(al); l = lg(hi);
  for (i=1; i<l && res!=d; i++) res = ulcm(res, indexfromhasse(hi[i],d));
  hf = gel(alg_get_hasse_f(al), 2); l = lg(hf);
  for (i=1; i<l && res!=d; i++) res = ulcm(res, indexfromhasse(hf[i],d));
  return res;
}

int
algisdivision(GEN al, GEN pl)
{
  checkalg(al);
  if (alg_type(al) == al_TABLE) {
    if (!algissimple(al,0)) return 0;
    if (algiscommutative(al)) return 1;
    pari_err_IMPL("algisdivision for table algebras");
  }
  return algindex(al,pl) == alg_get_degree(al);
}

int
algissplit(GEN al, GEN pl)
{
  checkalg(al);
  if (alg_type(al) == al_TABLE) pari_err_TYPE("algissplit [use alginit]", al);
  return algindex(al,pl) == 1;
}

int
algisramified(GEN al, GEN pl) { return !algissplit(al,pl); }

/* sorted; infinite places first */
GEN
algramifiedplaces(GEN al)
{
  pari_sp av = avma;
  GEN ram, hf, hi, Lpr;
  long r1, count, i, ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta != al_CSA && ta != al_CYCLIC)
    pari_err_TYPE("algramifiedplaces [not a central simple algebra"
        " over a number field]", al);
  r1 = nf_get_r1(alg_get_center(al));
  hi = alg_get_hasse_i(al);
  hf = alg_get_hasse_f(al);
  Lpr = gel(hf,1);
  hf = gel(hf,2);
  ram = cgetg(r1+lg(Lpr), t_VEC);
  count = 0;
  for (i=1; i<=r1; i++)
    if (hi[i]) {
      count++;
      gel(ram,count) = stoi(i);
    }
  for (i=1; i<lg(Lpr); i++)
    if (hf[i]) {
      count++;
      gel(ram,count) = gel(Lpr,i);
    }
  setlg(ram, count+1);
  return gc_GEN(av, ram);
}

/* assume same degree and al_CYCLIC or al_CSA */
static int
algissimilar_i(GEN al, GEN al2, GEN pl)
{
  GEN ram, ram2;
  long i, h;
  if (pl)
  {
    h = alghasse_0(al2,pl);
    return alghasse_0(al,pl) == h;
  }
  ram = algramifiedplaces(al);
  ram2 = algramifiedplaces(al2);
  if (!gequal(ram, ram2)) return 0;
  for (i = 1; i < lg(ram); i++)
  {
    h = alghasse_0(al2,gel(ram,i));
    if (alghasse_0(al,gel(ram,i)) != h) return 0;
  }
  return 1;
}

int
algisisom(GEN al, GEN al2, GEN pl)
{
  pari_sp av = avma;
  long t, d;
  checkalg(al);
  checkalg(al2);
  t = alg_type(al);
  if (t != al_CYCLIC && t != al_CSA)
    pari_err_TYPE("algisisom [al: apply alginit()]", al);
  t = alg_type(al2);
  if (t != al_CYCLIC && t != al_CSA)
    pari_err_TYPE("algisisom [al2: apply alginit()]", al2);
  if (!gequal(nf_get_pol(alg_get_center(al)), nf_get_pol(alg_get_center(al2))))
    pari_err(e_MISC, "base fields must be identical in algisisom");
  d = alg_get_degree(al);
  if (d != alg_get_degree(al2)) return gc_int(av, 0);
  if (d == 1) return gc_int(av, 1);
  return gc_int(av, algissimilar_i(al,al2,pl));
}

GEN
algnewprec_shallow(GEN al, long prec)
{
  GEN al2;
  long t = algtype(al);
  if (t != al_CYCLIC && t != al_CSA) return al;
  al2 = shallowcopy(al);
  gel(al2,1) = rnfnewprec_shallow(gel(al2,1), prec);
  return al2;
};

GEN
algnewprec(GEN al, long prec)
{
  pari_sp av = avma;
  GEN al2 = algnewprec_shallow(al, prec);
  return gc_GEN(av, al2);
}

/** OPERATIONS ON ELEMENTS operations.c **/

static long
alg_model0(GEN al, GEN x)
{
  long t, N = alg_get_absdim(al), lx = lg(x), d, n, D, i;
  if (typ(x) == t_MAT) return al_MATRIX;
  if (typ(x) != t_COL) return al_INVALID;
  if (N == 1) {
    if (lx != 2) return al_INVALID;
    switch(typ(gel(x,1)))
    {
      case t_INT: case t_FRAC: return al_TRIVIAL; /* cannot distinguish basis and alg from size */
      case t_POL: case t_POLMOD: return al_ALGEBRAIC;
      default: return al_INVALID;
    }
  }

  switch(alg_type(al)) {
    case al_TABLE:
      if (lx != N+1) return al_INVALID;
      return al_BASIS;
    case al_CYCLIC:
      d = alg_get_degree(al);
      if (lx == N+1) return al_BASIS;
      if (lx == d+1) return al_ALGEBRAIC;
      return al_INVALID;
    case al_CSA:
      D = alg_get_dim(al);
      n = nf_get_degree(alg_get_center(al));
      if (n == 1) {
        if (lx != D+1) return al_INVALID;
        for (i=1; i<=D; i++) {
          t = typ(gel(x,i));
          if (t == t_POL || t == t_POLMOD)  return al_ALGEBRAIC;
            /* TODO t_COL for coefficients in basis form ? */
        }
        return al_BASIS;
      }
      else {
        if (lx == N+1) return al_BASIS;
        if (lx == D+1) return al_ALGEBRAIC;
        return al_INVALID;
      }
  }
  return al_INVALID; /* LCOV_EXCL_LINE */
}

static void
checkalgx(GEN x, long model)
{
  long t, i;
  switch(model) {
    case al_BASIS:
      for (i=1; i<lg(x); i++) {
        t = typ(gel(x,i));
        if (t != t_INT && t != t_FRAC)
          pari_err_TYPE("checkalgx", gel(x,i));
      }
      return;
    case al_TRIVIAL:
    case al_ALGEBRAIC:
      for (i=1; i<lg(x); i++) {
        t = typ(gel(x,i));
        if (t != t_INT && t != t_FRAC && t != t_POL && t != t_POLMOD)
          /* TODO t_COL ? */
          pari_err_TYPE("checkalgx", gel(x,i));
      }
      return;
  }
}

long
alg_model(GEN al, GEN x)
{
  long res = alg_model0(al, x);
  if (res == al_INVALID) pari_err_TYPE("alg_model", x);
  checkalgx(x, res); return res;
}

static long
H_model0(GEN x)
{
  long i;
  switch(typ(x))
  {
    case t_INT:
    case t_FRAC:
    case t_REAL:
    case t_COMPLEX:
      return H_SCALAR;
    case t_MAT:
      return H_MATRIX;
    case t_COL:
      if (lg(x)!=5) return H_INVALID;
      for (i=1; i<=4; i++) if (!is_real_t(typ(gel(x,i)))) return H_INVALID;
      return H_QUATERNION;
    default:
      return al_INVALID;
  }
}

static long
H_model(GEN x)
{
  long res = H_model0(x);
  if (res == H_INVALID) pari_err_TYPE("H_model", x);
  return res;
}

static GEN
alC_add_i(GEN al, GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = algadd(al, gel(x,i), gel(y,i));
  return A;
}
static GEN
alM_add(GEN al, GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lg(y) != lx) pari_err_DIM("alM_add (rows)");
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  if (lgcols(y) != l) pari_err_DIM("alM_add (columns)");
  for (j = 1; j < lx; j++) gel(z,j) = alC_add_i(al, gel(x,j), gel(y,j), l);
  return z;
}
static GEN
H_add(GEN x, GEN y)
{
  long tx = H_model(x), ty = H_model(y);
  if ((tx==H_MATRIX) ^ (ty==H_MATRIX)) pari_err_TYPE2("H_add", x, y);
  if (tx>ty) { swap(x,y); lswap(tx,ty); }
  switch (tx)
  {
    case H_MATRIX: /* both H_MATRIX */ return alM_add(NULL, x, y);
    case H_QUATERNION: /* both H_QUATERNION */ return gadd(x,y);
    case H_SCALAR:
      if (ty == H_SCALAR) return gadd(x,y);
      else /* ty == H_QUATERNION */
      {
        pari_sp av = avma;
        GEN res = gcopy(y), im;
        gel(res,1) = gadd(gel(res,1), real_i(x));
        im = imag_i(x);
        if (im != gen_0) gel(res,2) = gadd(gel(res,2), im);
        return gc_upto(av, res);
      }
  }
  return NULL; /*LCOV_EXCL_LINE*/
}
GEN
algadd(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long tx, ty;
  GEN p;
  checkalg(al);
  if (alg_type(al)==al_REAL) return H_add(x,y);
  tx = alg_model(al,x);
  ty = alg_model(al,y);
  p = alg_get_char(al);
  if (signe(p)) return FpC_add(x,y,p);
  if (tx==ty) {
    if (tx!=al_MATRIX) return gadd(x,y);
    return gc_GEN(av, alM_add(al,x,y));
  }
  if (tx==al_ALGEBRAIC) x = algalgtobasis(al,x);
  if (ty==al_ALGEBRAIC) y = algalgtobasis(al,y);
  return gc_upto(av, gadd(x,y));
}

static GEN
H_neg(GEN x)
{
  (void)H_model(x);
  return gneg(x);
}

GEN
algneg(GEN al, GEN x)
{
  checkalg(al);
  if (alg_type(al)==al_REAL) return H_neg(x);
  (void)alg_model(al,x);
  return gneg(x);
}

static GEN
alC_sub_i(GEN al, GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = algsub(al, gel(x,i), gel(y,i));
  return A;
}
static GEN
alM_sub(GEN al, GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lg(y) != lx) pari_err_DIM("alM_sub (rows)");
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  if (lgcols(y) != l) pari_err_DIM("alM_sub (columns)");
  for (j = 1; j < lx; j++) gel(z,j) = alC_sub_i(al, gel(x,j), gel(y,j), l);
  return z;
}
GEN
algsub(GEN al, GEN x, GEN y)
{
  long tx, ty;
  pari_sp av = avma;
  GEN p;
  checkalg(al);
  if (alg_type(al)==al_REAL) return gc_upto(av, algadd(NULL,x,gneg(y)));
  tx = alg_model(al,x);
  ty = alg_model(al,y);
  p = alg_get_char(al);
  if (signe(p)) return FpC_sub(x,y,p);
  if (tx==ty) {
    if (tx != al_MATRIX) return gsub(x,y);
    return gc_GEN(av, alM_sub(al,x,y));
  }
  if (tx==al_ALGEBRAIC) x = algalgtobasis(al,x);
  if (ty==al_ALGEBRAIC) y = algalgtobasis(al,y);
  return gc_upto(av, gsub(x,y));
}

static GEN
algalgmul_cyc(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long n = alg_get_degree(al), i, k;
  GEN xalg, yalg, res, rnf, auts, sum, b, prod, autx;
  rnf = alg_get_splittingfield(al);
  auts = alg_get_auts(al);
  b = alg_get_b(al);

  xalg = cgetg(n+1, t_COL);
  for (i=0; i<n; i++)
    gel(xalg,i+1) = lift_shallow(rnfbasistoalg(rnf,gel(x,i+1)));

  yalg = cgetg(n+1, t_COL);
  for (i=0; i<n; i++) gel(yalg,i+1) = rnfbasistoalg(rnf,gel(y,i+1));

  res = cgetg(n+1,t_COL);
  for (k=0; k<n; k++) {
    gel(res,k+1) = gmul(gel(xalg,k+1),gel(yalg,1));
    for (i=1; i<=k; i++) {
      autx = poleval(gel(xalg,k-i+1),gel(auts,i));
      prod = gmul(autx,gel(yalg,i+1));
      gel(res,k+1) = gadd(gel(res,k+1), prod);
    }

    sum = gen_0;
    for (; i<n; i++) {
      autx = poleval(gel(xalg,k+n-i+1),gel(auts,i));
      prod = gmul(autx,gel(yalg,i+1));
      sum = gadd(sum,prod);
    }
    sum = gmul(b,sum);

    gel(res,k+1) = gadd(gel(res,k+1),sum);
  }

  return gc_GEN(av, res);
}

static GEN
_tablemul(GEN mt, GEN x, GEN y)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = RgM_RgC_mul(gel(mt,i),y);
      GEN t = RgC_Rg_mul(My,c);
      res = res? RgC_add(res,t): t;
    }
  }
  if (!res) { set_avma(av); return zerocol(D); }
  return gc_upto(av, res);
}

static GEN
_tablemul_Fp(GEN mt, GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (signe(c)) {
      GEN My = FpM_FpC_mul(gel(mt,i),y,p);
      GEN t = FpC_Fp_mul(My,c,p);
      res = res? FpC_add(res,t,p): t;
    }
  }
  if (!res) { set_avma(av); return zerocol(D); }
  return gc_upto(av, res);
}

/* x*ej */
static GEN
_tablemul_ej(GEN mt, GEN x, long j)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = gel(gel(mt,i),j);
      GEN t = RgC_Rg_mul(My,c);
      res = res? RgC_add(res,t): t;
    }
  }
  if (!res) { set_avma(av); return zerocol(D); }
  return gc_upto(av, res);
}
static GEN
_tablemul_ej_Fp(GEN mt, GEN x, long j, GEN p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    GEN c = gel(x,i);
    if (!gequal0(c)) {
      GEN My = gel(gel(mt,i),j);
      GEN t = FpC_Fp_mul(My,c,p);
      res = res? FpC_add(res,t,p): t;
    }
  }
  if (!res) { set_avma(av); return zerocol(D); }
  return gc_upto(av, res);
}

static GEN
_tablemul_ej_Fl(GEN mt, GEN x, long j, ulong p)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN res = NULL;
  for (i=1; i<=D; i++) {
    ulong c = x[i];
    if (c) {
      GEN My = gel(gel(mt,i),j);
      GEN t = Flv_Fl_mul(My,c, p);
      res = res? Flv_add(res,t, p): t;
    }
  }
  if (!res) { set_avma(av); return zero_Flv(D); }
  return gc_upto(av, res);
}

static GEN
algalgmul_csa(GEN al, GEN x, GEN y)
{
  GEN z, nf = alg_get_center(al);
  long i;
  z = _tablemul(alg_get_relmultable(al), x, y);
  for (i=1; i<lg(z); i++)
    gel(z,i) = basistoalg(nf,gel(z,i));
  return z;
}

/* assumes x and y in algebraic form */
static GEN
algalgmul(GEN al, GEN x, GEN y)
{
  switch(alg_type(al))
  {
    case al_CYCLIC: return algalgmul_cyc(al, x, y);
    case al_CSA: return algalgmul_csa(al, x, y);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
algbasismul(GEN al, GEN x, GEN y)
{
  GEN mt = alg_get_multable(al), p = alg_get_char(al);
  if (signe(p)) return _tablemul_Fp(mt, x, y, p);
  return _tablemul(mt, x, y);
}

/* x[i,]*y. Assume lg(x) > 1 and 0 < i < lgcols(x) */
static GEN
alMrow_alC_mul_i(GEN al, GEN x, GEN y, long i, long lx)
{
  pari_sp av = avma;
  GEN c = algmul(al,gcoeff(x,i,1),gel(y,1)), ZERO;
  long k;
  ZERO = zerocol(alg_get_absdim(al));
  for (k = 2; k < lx; k++)
  {
    GEN t = algmul(al, gcoeff(x,i,k), gel(y,k));
    if (!gequal(t,ZERO)) c = algadd(al, c, t);
  }
  return gc_GEN(av, c);
}
/* return x * y, 1 < lx = lg(x), l = lgcols(x) */
static GEN
alM_alC_mul_i(GEN al, GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i=1; i<l; i++) gel(z,i) = alMrow_alC_mul_i(al,x,y,i,lx);
  return z;
}
static GEN
alM_mul(GEN al, GEN x, GEN y)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  if (lx != lgcols(y)) pari_err_DIM("alM_mul");
  if (lx==1) return zeromat(0, ly-1);
  l = lgcols(x); z = cgetg(ly,t_MAT);
  for (j=1; j<ly; j++) gel(z,j) = alM_alC_mul_i(al,x,gel(y,j),lx,l);
  return z;
}

static void
H_compo(GEN x, GEN* a, GEN* b, GEN* c, GEN* d)
{
  switch(H_model(x))
  {
    case H_SCALAR:
      *a = real_i(x);
      *b = imag_i(x);
      *c = gen_0;
      *d = gen_0;
      return;
    case H_QUATERNION:
      *a = gel(x,1);
      *b = gel(x,2);
      *c = gel(x,3);
      *d = gel(x,4);
      return;
    default: *a = *b = *c = *d = NULL; return; /*LCOV_EXCL_LINE*/
  }
}
static GEN
H_mul(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a,b,c,d,u,v,w,z;
  long tx = H_model(x), ty = H_model(y);
  if ((tx==H_MATRIX) ^ (ty==H_MATRIX)) pari_err_TYPE2("H_mul", x, y);
  if (tx == H_MATRIX) /* both H_MATRIX */ return alM_mul(NULL, x, y);
  if (tx == H_SCALAR && ty == H_SCALAR) return gmul(x,y);
  H_compo(x,&a,&b,&c,&d);
  H_compo(y,&u,&v,&w,&z);
  return gc_GEN(av,mkcol4(
        gsub(gmul(a,u), gadd(gadd(gmul(b,v),gmul(c,w)),gmul(d,z))),
        gsub(gadd(gmul(a,v),gadd(gmul(b,u),gmul(c,z))), gmul(d,w)),
        gsub(gadd(gmul(a,w),gadd(gmul(c,u),gmul(d,v))), gmul(b,z)),
        gsub(gadd(gmul(a,z),gadd(gmul(b,w),gmul(d,u))), gmul(c,v))
        ));
}

GEN
algmul(GEN al, GEN x, GEN y)
{
  pari_sp av = avma;
  long tx, ty;
  checkalg(al);
  if (alg_type(al)==al_REAL) return H_mul(x,y);
  tx = alg_model(al,x);
  ty = alg_model(al,y);
  if (tx==al_MATRIX) {
    if (ty==al_MATRIX) return alM_mul(al,x,y);
    pari_err_TYPE("algmul", y);
  }
  if (signe(alg_get_char(al))) return algbasismul(al,x,y);
  if (tx==al_TRIVIAL) retmkcol(gmul(gel(x,1),gel(y,1)));
  if (tx==al_ALGEBRAIC && ty==al_ALGEBRAIC) return algalgmul(al,x,y);
  if (tx==al_ALGEBRAIC) x = algalgtobasis(al,x);
  if (ty==al_ALGEBRAIC) y = algalgtobasis(al,y);
  return gc_upto(av,algbasismul(al,x,y));
}

static GEN
H_sqr(GEN x)
{
  pari_sp av = avma;
  long tx = H_model(x);
  GEN a,b,c,d;
  if (tx == H_SCALAR) return gsqr(x);
  if (tx == H_MATRIX) return H_mul(x,x);
  H_compo(x,&a,&b,&c,&d);
  return gc_GEN(av, mkcol4(
        gsub(gsqr(a), gadd(gsqr(b),gadd(gsqr(c),gsqr(d)))),
        gshift(gmul(a,b),1),
        gshift(gmul(a,c),1),
        gshift(gmul(a,d),1)
        ));
}

GEN
algsqr(GEN al, GEN x)
{
  pari_sp av = avma;
  long tx;
  checkalg(al);
  if (alg_type(al)==al_REAL) return H_sqr(x);
  tx = alg_model(al,x);
  if (tx==al_MATRIX) return gc_GEN(av,alM_mul(al,x,x));
  if (signe(alg_get_char(al))) return algbasismul(al,x,x);
  if (tx==al_TRIVIAL) retmkcol(gsqr(gel(x,1)));
  if (tx==al_ALGEBRAIC) return algalgmul(al,x,x);
  return gc_upto(av,algbasismul(al,x,x));
}

static GEN
algmtK2Z_cyc(GEN al, GEN m)
{
  pari_sp av = avma;
  GEN nf = alg_get_abssplitting(al), res, mt, rnf = alg_get_splittingfield(al), c, dc;
  long n = alg_get_degree(al), N = nf_get_degree(nf), Nn, i, j, i1, j1;
  Nn = N*n;
  res = zeromatcopy(Nn,Nn);
  for (i=0; i<n; i++)
  for (j=0; j<n; j++) {
    c = gcoeff(m,i+1,j+1);
    if (!gequal0(c)) {
      c = rnfeltreltoabs(rnf,c);
      c = algtobasis(nf,c);
      c = Q_remove_denom(c,&dc);
      mt = zk_multable(nf,c);
      if (dc) mt = ZM_Z_div(mt,dc);
      for (i1=1; i1<=N; i1++)
      for (j1=1; j1<=N; j1++)
        gcoeff(res,i*N+i1,j*N+j1) = gcoeff(mt,i1,j1);
    }
  }
  return gc_GEN(av,res);
}

static GEN
algmtK2Z_csa(GEN al, GEN m)
{
  pari_sp av = avma;
  GEN nf = alg_get_center(al), res, mt, c, dc;
  long d2 = alg_get_dim(al), n = nf_get_degree(nf), D, i, j, i1, j1;
  D = d2*n;
  res = zeromatcopy(D,D);
  for (i=0; i<d2; i++)
  for (j=0; j<d2; j++) {
    c = gcoeff(m,i+1,j+1);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      c = Q_remove_denom(c,&dc);
      mt = zk_multable(nf,c);
      if (dc) mt = ZM_Z_div(mt,dc);
      for (i1=1; i1<=n; i1++)
      for (j1=1; j1<=n; j1++)
        gcoeff(res,i*n+i1,j*n+j1) = gcoeff(mt,i1,j1);
    }
  }
  return gc_GEN(av,res);
}

/* assumes al is a CSA or CYCLIC */
static GEN
algmtK2Z(GEN al, GEN m)
{
  switch(alg_type(al))
  {
    case al_CYCLIC: return algmtK2Z_cyc(al, m);
    case al_CSA: return algmtK2Z_csa(al, m);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/* left multiplication table, as a vector space of dimension n over the splitting field (by right multiplication) */
static GEN
algalgmultable_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  long n = alg_get_degree(al), i, j;
  GEN res, rnf, auts, b, pol;
  rnf = alg_get_splittingfield(al);
  auts = alg_get_auts(al);
  b = alg_get_b(al);
  pol = rnf_get_pol(rnf);

  res = zeromatcopy(n,n);
  for (i=0; i<n; i++)
    gcoeff(res,i+1,1) = lift_shallow(rnfbasistoalg(rnf,gel(x,i+1)));

  for (i=0; i<n; i++) {
    for (j=1; j<=i; j++)
      gcoeff(res,i+1,j+1) = gmodulo(poleval(gcoeff(res,i-j+1,1),gel(auts,j)),pol);
    for (; j<n; j++)
      gcoeff(res,i+1,j+1) = gmodulo(gmul(b,poleval(gcoeff(res,n+i-j+1,1),gel(auts,j))), pol);
  }

  for (i=0; i<n; i++)
    gcoeff(res,i+1,1) = gmodulo(gcoeff(res,i+1,1),pol);

  return gc_GEN(av, res);
}

static GEN
elementmultable(GEN mt, GEN x)
{
  pari_sp av = avma;
  long D = lg(mt)-1, i;
  GEN z = NULL;
  for (i=1; i<=D; i++)
  {
    GEN c = gel(x,i);
    if (!gequal0(c))
    {
      GEN M = RgM_Rg_mul(gel(mt,i),c);
      z = z? RgM_add(z, M): M;
    }
  }
  if (!z) { set_avma(av); return zeromatcopy(D,D); }
  return gc_upto(av, z);
}
/* mt a t_VEC of Flm modulo m */
static GEN
algbasismultable_Flm(GEN mt, GEN x, ulong m)
{
  pari_sp av = avma;
  long D = lg(gel(mt,1))-1, i;
  GEN z = NULL;
  for (i=1; i<=D; i++)
  {
    ulong c = x[i];
    if (c)
    {
      GEN M = Flm_Fl_mul(gel(mt,i),c, m);
      z = z? Flm_add(z, M, m): M;
    }
  }
  if (!z) { set_avma(av); return zero_Flm(D,D); }
  return gc_upto(av, z);
}
static GEN
elementabsmultable_Z(GEN mt, GEN x)
{
  long i, l = lg(x);
  GEN z = NULL;
  for (i = 1; i < l; i++)
  {
    GEN c = gel(x,i);
    if (signe(c))
    {
      GEN M = ZM_Z_mul(gel(mt,i),c);
      z = z? ZM_add(z, M): M;
    }
  }
  return z;
}
static GEN
elementabsmultable(GEN mt, GEN x)
{
  GEN d, z = elementabsmultable_Z(mt, Q_remove_denom(x,&d));
  return (z && d)? ZM_Z_div(z, d): z;
}
static GEN
elementabsmultable_Fp(GEN mt, GEN x, GEN p)
{
  GEN z = elementabsmultable_Z(mt, x);
  return z? FpM_red(z, p): z;
}
static GEN
algbasismultable(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN z, p = alg_get_char(al), mt = alg_get_multable(al);
  z = signe(p)? elementabsmultable_Fp(mt, x, p): elementabsmultable(mt, x);
  if (!z)
  {
    long D = lg(mt)-1;
    set_avma(av); return zeromat(D,D);
  }
  return gc_upto(av, z);
}

static GEN
algalgmultable_csa(GEN al, GEN x)
{
  GEN nf = alg_get_center(al), m;
  long i,j;
  m = elementmultable(alg_get_relmultable(al), x);
  for (i=1; i<lg(m); i++)
    for(j=1; j<lg(m); j++)
      gcoeff(m,i,j) = basistoalg(nf,gcoeff(m,i,j));
  return m;
}

/* assumes x in algebraic form */
static GEN
algalgmultable(GEN al, GEN x)
{
  switch(alg_type(al))
  {
    case al_CYCLIC: return algalgmultable_cyc(al, x);
    case al_CSA: return algalgmultable_csa(al, x);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/* on the natural basis */
/* assumes x in algebraic form */
static GEN
algZmultable(GEN al, GEN x) {
  pari_sp av = avma;
  return gc_upto(av, algmtK2Z(al,algalgmultable(al,x)));
}

/* x integral */
static GEN
algbasisrightmultable(GEN al, GEN x)
{
  long N = alg_get_absdim(al), i,j,k;
  GEN res = zeromatcopy(N,N), c, mt = alg_get_multable(al), p = alg_get_char(al);
  if (gequal0(p)) p = NULL;
  for (i=1; i<=N; i++) {
    c = gel(x,i);
    if (!gequal0(c)) {
      for (j=1; j<=N; j++)
      for(k=1; k<=N; k++) {
        if (p) gcoeff(res,k,j) = Fp_add(gcoeff(res,k,j), Fp_mul(c, gcoeff(gel(mt,j),k,i), p), p);
        else gcoeff(res,k,j) = addii(gcoeff(res,k,j), mulii(c, gcoeff(gel(mt,j),k,i)));
      }
    }
  }
  return res;
}

/* central simple algebra al from alginit */
/* right multiplication table on integral basis; no checks no GC */
static GEN
algrightmultable(GEN al, GEN x)
{
  GEN d, M;
  x = algalgtobasis(al, x);
  x = Q_remove_denom(x, &d);
  M = algbasisrightmultable(al,x);
  return d ? ZM_Z_div(M,d) : M;
}

/* basis for matrices : 1, E_{i,j} for (i,j)!=(1,1) */
/* index : ijk = ((i-1)*N+j-1)*n + k */
/* square matrices only, coefficients in basis form, shallow function */
static GEN
algmat2basis(GEN al, GEN M)
{
  long n = alg_get_absdim(al), N = lg(M)-1, i, j, k, ij, ijk;
  GEN res, x;
  res = zerocol(N*N*n);
  for (i=1; i<=N; i++) {
    for (j=1, ij=(i-1)*N+1; j<=N; j++, ij++) {
      x = gcoeff(M,i,j);
      for (k=1, ijk=(ij-1)*n+1; k<=n; k++, ijk++) {
        gel(res, ijk) = gel(x, k);
        if (i>1 && i==j) gel(res, ijk) = gsub(gel(res,ijk), gel(res,k));
      }
    }
  }

  return res;
}

static GEN
algbasis2mat(GEN al, GEN M, long N)
{
  long n = alg_get_absdim(al), i, j, k, ij, ijk;
  GEN res, x;
  res = zeromatcopy(N,N);
  for (i=1; i<=N; i++)
  for (j=1; j<=N; j++)
    gcoeff(res,i,j) = zerocol(n);

  for (i=1; i<=N; i++) {
    for (j=1, ij=(i-1)*N+1; j<=N; j++, ij++) {
      x = gcoeff(res,i,j);
      for (k=1, ijk=(ij-1)*n+1; k<=n; k++, ijk++) {
        gel(x,k) = gel(M,ijk);
        if (i>1 && i==j) gel(x,k) = gadd(gel(x,k), gel(M,k));
      }
    }
  }

  return res;
}

static GEN
algmatbasis_ei(GEN al, long ijk, long N)
{
  long n = alg_get_absdim(al), i, j, k, ij;
  GEN res;

  res = zeromatcopy(N,N);
  for (i=1; i<=N; i++)
  for (j=1; j<=N; j++)
    gcoeff(res,i,j) = zerocol(n);

  k = ijk%n;
  if (k==0) k=n;
  ij = (ijk-k)/n+1;

  if (ij==1) {
    for (i=1; i<=N; i++)
      gcoeff(res,i,i) = col_ei(n,k);
    return res;
  }

  j = ij%N;
  if (j==0) j=N;
  i = (ij-j)/N+1;

  gcoeff(res,i,j) = col_ei(n,k);
  return res;
}

/* FIXME lazy implementation! */
static GEN
algleftmultable_mat(GEN al, GEN M)
{
  long N = lg(M)-1, n = alg_get_absdim(al), D = N*N*n, j;
  GEN res, x, Mx;
  if (N == 0) return cgetg(1, t_MAT);
  if (N != nbrows(M)) pari_err_DIM("algleftmultable_mat (nonsquare)");
  res = cgetg(D+1, t_MAT);
  for (j=1; j<=D; j++) {
    x = algmatbasis_ei(al, j, N);
    Mx = algmul(al, M, x);
    gel(res, j) = algmat2basis(al, Mx);
  }
  return res;
}

/* left multiplication table on integral basis */
static GEN
algleftmultable(GEN al, GEN x)
{
  pari_sp av = avma;
  long tx;
  GEN res;

  checkalg(al);
  tx = alg_model(al,x);
  switch(tx) {
    case al_TRIVIAL : res = mkmatcopy(mkcol(gel(x,1))); break;
    case al_ALGEBRAIC : x = algalgtobasis(al,x);
    case al_BASIS : res = algbasismultable(al,x); break;
    case al_MATRIX : res = algleftmultable_mat(al,x); break;
    default : return NULL; /* LCOV_EXCL_LINE */
  }
  return gc_upto(av,res);
}

static GEN
algbasissplittingmatrix_csa(GEN al, GEN x)
{
  long d = alg_get_degree(al), i, j;
  GEN rnf = alg_get_splittingfield(al), splba = alg_get_splittingbasis(al), splbainv = alg_get_splittingbasisinv(al), M;
  M = algbasismultable(al,x);
  M = RgM_mul(M, splba); /* TODO best order ? big matrix /Q vs small matrix /nf */
  M = RgM_mul(splbainv, M);
  for (i=1; i<=d; i++)
  for (j=1; j<=d; j++)
    gcoeff(M,i,j) = rnfeltabstorel(rnf, gcoeff(M,i,j));
  return M;
}

static GEN
algmat_tomatrix(GEN al, GEN x) /* abs = 0 */
{
  GEN res;
  long i,j;
  if (lg(x) == 1) return cgetg(1, t_MAT);
  res = zeromatcopy(nbrows(x),lg(x)-1);
  for (j=1; j<lg(x); j++)
  for (i=1; i<lgcols(x); i++)
    gcoeff(res,i,j) = algtomatrix(al,gcoeff(x,i,j),0);
  return shallowmatconcat(res);
}

static GEN
R_tomatrix(GEN x)
{
  long t = H_model(x);
  if (t == H_QUATERNION) pari_err_TYPE("R_tomatrix", x);
  if (t == H_MATRIX) return x;
  return mkmat(mkcol(x));
}
static GEN
C_tomatrix(GEN z, long abs)
{
  GEN x,y;
  long t = H_model(z), nrows, ncols;
  if (t == H_QUATERNION) pari_err_TYPE("C_tomatrix", z);
  if (!abs)
  {
    if (t == H_MATRIX) return z;
    return mkmat(mkcol(z));
  }
  if (t == H_MATRIX)
  {
    /* Warning: this is not the same choice of basis as for other algebras */
    GEN res, a, b;
    long i,j;
    RgM_dimensions(z,&nrows,&ncols);
    res = zeromatcopy(2*nrows,2*ncols);
    for (i=1; i<=nrows; i++)
      for (j=1; j<=ncols; j++)
      {
        a = real_i(gcoeff(z,i,j));
        b = imag_i(gcoeff(z,i,j));
        gcoeff(res,2*i-1,2*j-1) = a;
        gcoeff(res,2*i,2*j) = a;
        gcoeff(res,2*i-1,2*j) = gneg(b);
        gcoeff(res,2*i,2*j-1) = b;
      }
    return res;
  }
  x = real_i(z);
  y = imag_i(z);
  return mkmat22(x,gneg(y),y,x);
}
static GEN
H_tomatrix(GEN x, long abs)
{
  long tx = H_model(x);
  GEN a = NULL, b =NULL, c = NULL, d = NULL, md = NULL, M = NULL;
  if (abs) {
    if (tx == H_MATRIX) return algleftmultable_mat(NULL,x);
    switch(tx)
    {
      case H_SCALAR:
        a = real_i(x);
        b = imag_i(x);
        c = gen_0;
        d = gen_0;
        break;
      case H_QUATERNION:
        a = gel(x,1);
        b = gel(x,2);
        c = gel(x,3);
        d = gel(x,4);
        break;
    }
    M = scalarmat(a,4);
    gcoeff(M,2,1) = gcoeff(M,4,3) = b;
    gcoeff(M,1,2) = gcoeff(M,3,4) = gneg(b);
    gcoeff(M,3,1) = gcoeff(M,2,4) = c;
    gcoeff(M,4,2) = gcoeff(M,1,3) = gneg(c);
    gcoeff(M,4,1) = gcoeff(M,3,2) = d;
    gcoeff(M,2,3) = gcoeff(M,1,4) = gneg(d);
  }
  else /* abs == 0 */
  {
    if (tx == H_MATRIX) return algmat_tomatrix(NULL,x);
    switch(tx)
    {
      case H_SCALAR:
        M = mkmat22(
            x,      gen_0,
            gen_0,  conj_i(x)
            );
        break;
      case H_QUATERNION:
        a = gel(x,1);
        b = gel(x,2);
        c = gel(x,3);
        md = gneg(gel(x,4));
        M = mkmat22(
            mkcomplex(a,b),     mkcomplex(gneg(c),md),
            mkcomplex(c,md),    mkcomplex(a,gneg(b))
            );
    }
  }
  return M;
}

GEN
algtomatrix(GEN al, GEN x, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  long ta, tx;
  checkalg(al);
  ta = alg_type(al);
  if (ta==al_REAL)
  {
    switch(alg_get_absdim(al)) {
      case 1: res = R_tomatrix(x); break;
      case 2: res = C_tomatrix(x,abs); break;
      case 4: res = H_tomatrix(x,abs); break;
      default: pari_err_TYPE("algtomatrix [apply alginit]", al);
    }
    return gc_GEN(av, res);
  }
  if (abs || ta==al_TABLE) return algleftmultable(al,x);
  tx = alg_model(al,x);
  if (tx == al_MATRIX) res = algmat_tomatrix(al,x);
  else switch (alg_type(al))
  {
    case al_CYCLIC:
      if (tx==al_BASIS) x = algbasistoalg(al,x);
      res = algalgmultable(al,x);
      break;
    case al_CSA:
      if (tx==al_ALGEBRAIC) x = algalgtobasis(al,x);
      res = algbasissplittingmatrix_csa(al,x);
      break;
    default: return NULL; /*LCOV_EXCL_LINE*/
  }
  return gc_GEN(av,res);
}

/*  x^(-1)*y, NULL if no solution */
static GEN
C_divl_i(GEN x, GEN y)
{
  long tx = H_model(x), ty = H_model(y);
  if (tx != ty) pari_err_TYPE2("C_divl", x, y);
  switch (tx) {
    case H_SCALAR:
      if (gequal0(x)) return gequal0(y) ? gen_0 : NULL;
      else return gdiv(y,x);
    case H_MATRIX:
      if ((lg(x)>1 && lg(x) != lgcols(x)) || (lg(y)>1 && lg(y) != lgcols(y)))
        pari_err_DIM("C_divl (nonsquare)");
      if (lg(x) != lg(y)) pari_err_DIM("C_divl");
      if (lg(y) == 1) return cgetg(1, t_MAT);
      return RgM_invimage(x, y);
    default: pari_err_TYPE("C_divl", x); return NULL;
  }
}
/* H^k -> C^2k */
static GEN
HC_to_CC(GEN v)
{
  long l = lg(v), i;
  GEN w = cgetg(2*l-1, t_COL), a, b, c, d;
  for (i=1; i<l; i++)
  {
    H_compo(gel(v,i),&a,&b,&c,&d);
    gel(w,2*i-1) = mkcomplex(a,b);
    gel(w,2*i) = mkcomplex(c,gneg(d));
  }
  return w;
}
/* C^2k -> H^k */
static GEN
CC_to_HC(GEN w)
{
  long l = lg(w), i, lv = (l+1)/2;
  GEN v = cgetg(lv, t_COL), ab, cd;
  for (i=1; i<lv; i++)
  {
    ab = gel(w,2*i-1);
    cd = gel(w,2*i);
    gel(v,i) = mkcol4(real_i(ab),imag_i(ab),real_i(cd),gneg(imag_i(cd)));
  }
  return v;
}
/* M_{k,n}(H) -> M_{2k,n}(C) */
static GEN
HM_to_CM(GEN x) pari_APPLY_same(HC_to_CC(gel(x,i)));
/* M_{2k,n}(C) -> M_{k,n}(H) */
static GEN
CM_to_HM(GEN x) pari_APPLY_same(CC_to_HC(gel(x,i)));
/*  x^(-1)*y, NULL if no solution */
static GEN
H_divl_i(GEN x, GEN y)
{
  pari_sp av = avma;
  long tx = H_model(x), ty = H_model(y);
  if ((tx==H_MATRIX) ^ (ty==H_MATRIX)) pari_err_TYPE2("H_divl", x, y);
  if (tx==H_MATRIX)
  {
    GEN mx, my, mxdivy;
    if ((lg(x)>1 && lg(x) != lgcols(x)) || (lg(y)>1 && lg(y) != lgcols(y)))
      pari_err_DIM("H_divl (nonsquare)");
    if (lg(x) != lg(y)) pari_err_DIM("H_divl");
    if (lg(y) == 1) return cgetg(1, t_MAT);
    mx = H_tomatrix(x,0);
    my = HM_to_CM(y);
    mxdivy = RgM_invimage(mx, my);
    if (!mxdivy) return gc_NULL(av);
    return gc_GEN(av,CM_to_HM(mxdivy));
  }
  if (gequal0(y)) return gen_0;
  if (gequal0(x)) return NULL;
  return gc_GEN(av,H_mul(H_inv(x),y));
}
/*  x^(-1)*y, NULL if no solution */
static GEN
algdivl_i(GEN al, GEN x, GEN y, long tx, long ty) {
  pari_sp av = avma;
  GEN res, p = alg_get_char(al), mtx;
  if (tx != ty) {
    if (tx==al_ALGEBRAIC) { x = algalgtobasis(al,x); tx=al_BASIS; }
    if (ty==al_ALGEBRAIC) { y = algalgtobasis(al,y); ty=al_BASIS; }
  }
  if (ty == al_MATRIX)
  {
    if (alg_type(al) != al_TABLE) y = algalgtobasis(al,y);
    y = algmat2basis(al,y);
  }
  if (signe(p)) res = FpM_FpC_invimage(algbasismultable(al,x),y,p);
  else
  {
    if (ty==al_ALGEBRAIC)   mtx = algalgmultable(al,x);
    else                    mtx = algleftmultable(al,x);
    res = inverseimage(mtx,y);
  }
  if (!res || lg(res)==1) return gc_NULL(av);
  if (tx == al_MATRIX) {
    res = algbasis2mat(al, res, lg(x)-1);
    return gc_GEN(av,res);
  }
  return gc_upto(av,res);
}
static GEN
algdivl_i2(GEN al, GEN x, GEN y)
{
  long tx, ty;
  checkalg(al);
  if (alg_type(al)==al_REAL) switch(alg_get_absdim(al)) {
    case 1: case 2: return C_divl_i(x,y);
    case 4: return H_divl_i(x,y);
  }
  tx = alg_model(al,x);
  ty = alg_model(al,y);
  if (tx == al_MATRIX) {
    if (ty != al_MATRIX) pari_err_TYPE2("\\", x, y);
    if ((lg(x)>1 && lg(x) != lgcols(x)) || (lg(y)>1 && lg(y) != lgcols(y)))
      pari_err_DIM("algdivl (nonsquare)");
    if (lg(x) != lg(y)) pari_err_DIM("algdivl");
    if (lg(y) == 1) return cgetg(1, t_MAT);
  }
  return algdivl_i(al,x,y,tx,ty);
}

GEN algdivl(GEN al, GEN x, GEN y)
{
  GEN z;
  z = algdivl_i2(al,x,y);
  if (!z) pari_err_INV("algdivl", x);
  return z;
}

int
algisdivl(GEN al, GEN x, GEN y, GEN* ptz)
{
  pari_sp av = avma;
  GEN z = algdivl_i2(al,x,y);
  if (!z) return gc_bool(av,0);
  if (ptz != NULL) *ptz = z;
  return 1;
}

static GEN
C_inv(GEN x)
{
  switch (H_model(x))
  {
    case H_SCALAR: return gequal0(x) ? NULL : ginv(x);
    case H_MATRIX: return RgM_inv(x);
    default: pari_err_TYPE("alginv_i", x);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}
static GEN
H_inv(GEN x)
{
  pari_sp av = avma;
  GEN nm, xi;
  long i;
  switch (H_model(x))
  {
    case H_SCALAR:
      if (gequal0(x)) return NULL;
      return ginv(x);
    case H_QUATERNION:
      if (gequal0(x)) return NULL;
      nm = H_norm(x, 0);
      xi = gdiv(x,nm);
      for(i=2; i<=4; i++) gel(xi,i) = gneg(gel(xi,i));
      return gc_GEN(av,xi);
    case H_MATRIX:
      if (lg(x)==1) return cgetg(1,t_MAT);
      return H_divl_i(x, matid(lg(x)-1));
  }
  return NULL; /*LCOV_EXCL_LINE*/
}
static GEN
alginv_i(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL, p = alg_get_char(al);
  long tx, n, ta;
  ta = alg_type(al);
  if (ta==al_REAL) switch(alg_get_absdim(al)) {
    case 1: case 2: return C_inv(x);
    case 4: return H_inv(x);
    default: pari_err_TYPE("alginv_i [apply alginit]", al);
  }
  tx = alg_model(al,x);
  switch(tx) {
    case al_TRIVIAL :
      if (signe(p)) { res = mkcol(Fp_inv(gel(x,1),p)); break; }
      else          { res = mkcol(ginv(gel(x,1))); break; }
    case al_ALGEBRAIC :
      switch(ta) {
        case al_CYCLIC: n = alg_get_degree(al); break;
        case al_CSA: n = alg_get_dim(al); break;
        default: return NULL; /* LCOV_EXCL_LINE */
      }
      res = algdivl_i(al, x, col_ei(n,1), tx, al_ALGEBRAIC); break;
    case al_BASIS : res = algdivl_i(al, x, col_ei(alg_get_absdim(al),1), tx,
                                                            al_BASIS); break;
    case al_MATRIX :
      n = lg(x)-1;
      if (n==0) return cgetg(1, t_MAT);
      if (n != nbrows(x)) pari_err_DIM("alginv_i (nonsquare)");
      res = algdivl_i(al, x, col_ei(n*n*alg_get_absdim(al),1), tx, al_BASIS);
        /* cheat on type because wrong dimension */
  }
  if (!res) return gc_NULL(av);
  return gc_GEN(av,res);
}
GEN
alginv(GEN al, GEN x)
{
  GEN z;
  checkalg(al);
  z = alginv_i(al,x);
  if (!z) pari_err_INV("alginv", x);
  return z;
}

int
algisinv(GEN al, GEN x, GEN* ptix)
{
  pari_sp av = avma;
  GEN ix;
  if (al) checkalg(al);
  ix = alginv_i(al,x);
  if (!ix) return gc_bool(av,0);
  if (ptix != NULL) *ptix = ix;
  return 1;
}

/*  x*y^(-1)  */
GEN
algdivr(GEN al, GEN x, GEN y) { return algmul(al, x, alginv(al, y)); }

static GEN _mul(void* data, GEN x, GEN y) { return algmul((GEN)data,x,y); }
static GEN _sqr(void* data, GEN x) { return algsqr((GEN)data,x); }

static GEN
algmatid(GEN al, long N)
{
  long n = alg_get_absdim(al), i, j;
  GEN res, one, zero;

  res = zeromatcopy(N,N);
  one = col_ei(n,1);
  zero = zerocol(n);
  for (i=1; i<=N; i++)
  for (j=1; j<=N; j++)
    gcoeff(res,i,j) = i==j ? one : zero;
  return res;
}

GEN
algpow(GEN al, GEN x, GEN n)
{
  pari_sp av = avma;
  GEN res;
  long s = signe(n);
  checkalg(al);
  if (!s && alg_type(al)==al_REAL)
  {
    if (H_model(x) == H_MATRIX) return matid(lg(x)-1);
    else                        return gen_1;
  }
  switch (s) {
    case 0:
      if (alg_model(al,x) == al_MATRIX)
        res = algmatid(al,lg(x)-1);
      else
        res = col_ei(alg_get_absdim(al),1);
      return res;
    case 1:
      res = gen_pow_i(x, n, (void*)al, _sqr, _mul); break;
    default: /* -1 */
      res = gen_pow_i(alginv(al,x), gneg(n), (void*)al, _sqr, _mul);
  }
  return gc_GEN(av,res);
}

static GEN
algredcharpoly_i(GEN al, GEN x, long v)
{
  GEN rnf = alg_get_splittingfield(al);
  GEN cp = charpoly(algtomatrix(al,x,0),v);
  long i, m = lg(cp);
  for (i=2; i<m; i++) gel(cp,i) = rnfeltdown(rnf, gel(cp,i));
  return cp;
}

/* assumes al is CSA or CYCLIC */
static GEN
algredcharpoly(GEN al, GEN x, long v)
{
  pari_sp av = avma;
  long w = gvar(rnf_get_pol(alg_get_center(al)));
  if (varncmp(v,w)>=0) pari_err_PRIORITY("algredcharpoly",pol_x(v),">=",w);
  switch(alg_type(al))
  {
    case al_CYCLIC:
    case al_CSA:
      return gc_upto(av, algredcharpoly_i(al, x, v));
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
algbasischarpoly(GEN al, GEN x, long v)
{
  pari_sp av = avma;
  GEN p = alg_get_char(al), mx;
  if (alg_model(al,x) == al_MATRIX) mx = algleftmultable_mat(al,x);
  else                              mx = algbasismultable(al,x);
  if (signe(p)) {
    GEN res = FpM_charpoly(mx,p);
    setvarn(res,v);
    return gc_upto(av, res);
  }
  return gc_upto(av, charpoly(mx,v));
}

static GEN
R_charpoly(GEN x, long v, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR: res = mkpoln(2, gen_1, gneg(x)); break;
    case H_MATRIX:
      res = charpoly(x,v);
      if (abs) res = gpowgs(res,nbrows(x));
      break;
    default: pari_err_TYPE("R_charpoly", x);
  }
  if (v) setvarn(res, v);
  return gc_GEN(av, res);
}
static GEN
C_charpoly(GEN x, long v, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR:
      if (abs)  res = mkpoln(3, gen_1, gneg(gshift(real_i(x),1)), cxnorm(x));
      else      res = mkpoln(2, gen_1, gneg(x));
      break;
    case H_MATRIX:
      res = charpoly(x,v);
      if (abs) res = gpowgs(real_i(gmul(res,gconj(res))),nbrows(x));
      break;
    default: pari_err_TYPE("C_charpoly", x);
  }
  if (v) setvarn(res, v);
  return gc_GEN(av, res);
}
static GEN
H_charpoly(GEN x, long v, long abs)
{
  pari_sp av = avma;
  GEN res;
  if (H_model(x) == H_MATRIX) return greal(charpoly(H_tomatrix(x,abs),v));
  res = mkpoln(3, gen_1, gneg(H_trace(x,0)), H_norm(x,0));
  if (v) setvarn(res, v);
  if (abs) res = gsqr(res);
  return gc_GEN(av, res);
}

GEN
algcharpoly(GEN al, GEN x, long v, long abs)
{
  long ta;
  if (v<0) v=0;
  checkalg(al);
  ta = alg_type(al);
  if (ta == al_REAL) switch (alg_get_absdim(al)) {
    case 1: return R_charpoly(x, v, abs);
    case 2: return C_charpoly(x, v, abs);
    case 4: return H_charpoly(x, v, abs);
    default: pari_err_TYPE("algcharpoly [apply alginit]", al);
  }

  /* gneg(x[1]) left on stack */
  if (alg_model(al,x) == al_TRIVIAL) {
    GEN p = alg_get_char(al);
    if (signe(p)) return deg1pol(gen_1,Fp_neg(gel(x,1),p),v);
    return deg1pol(gen_1,gneg(gel(x,1)),v);
  }

  switch(ta) {
    case al_CYCLIC: case al_CSA:
      if (abs)
      {
        if (alg_model(al,x)==al_ALGEBRAIC) x = algalgtobasis(al,x);
      }
      else return algredcharpoly(al,x,v);
    case al_TABLE: return algbasischarpoly(al,x,v);
    default : return NULL; /* LCOV_EXCL_LINE */
  }
}

/* assumes x in basis form */
static GEN
algabstrace(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL, p = alg_get_char(al);
  if (signe(p)) return FpV_dotproduct(x, alg_get_tracebasis(al), p);
  switch(alg_model(al,x)) {
    case al_TRIVIAL: return gcopy(gel(x,1)); break;
    case al_BASIS: res = RgV_dotproduct(x, alg_get_tracebasis(al)); break;
  }
  return gc_upto(av,res);
}

static GEN
algredtrace(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch(alg_model(al,x)) {
    case al_TRIVIAL: return gcopy(gel(x,1)); break;
    case al_BASIS: return algredtrace(al, algbasistoalg(al,x));
                   /* TODO precompute too? */
    case al_ALGEBRAIC:
      switch(alg_type(al))
      {
        case al_CYCLIC:
          res = rnfelttrace(alg_get_splittingfield(al),gel(x,1));
          break;
        case al_CSA:
          res = gtrace(algalgmultable_csa(al,x));
          res = gdiv(res, stoi(alg_get_degree(al)));
          break;
        default: return NULL; /* LCOV_EXCL_LINE */
      }
  }
  return gc_upto(av,res);
}

static GEN
algtrace_mat(GEN al, GEN M, long abs) {
  pari_sp av = avma;
  long N = lg(M)-1, i;
  GEN res, p = alg_get_char(al);
  if (N == 0) return gen_0;
  if (N != nbrows(M)) pari_err_DIM("algtrace_mat (nonsquare)");

  if (!signe(p)) p = NULL;
  if (alg_type(al) == al_TABLE) abs = 1;
  res = algtrace(al, gcoeff(M,1,1), abs);
  for (i=2; i<=N; i++) {
    if (p)  res = Fp_add(res, algtrace(al,gcoeff(M,i,i),abs), p);
    else    res = gadd(res, algtrace(al,gcoeff(M,i,i),abs));
  }
  if (abs) res = gmulgu(res, N); /* absolute trace */
  return gc_upto(av, res);
}

static GEN
R_trace(GEN x, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR: res = gcopy(x); break;
    case H_MATRIX: res = abs? mulrs(gtrace(x),nbrows(x)) : gtrace(x); break;
    default: pari_err_TYPE("R_trace", x);
  }
  return gc_GEN(av, res);
}
static GEN
C_trace(GEN x, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR: res = abs ? gshift(real_i(x),1) : x; break;
    case H_MATRIX:
      res = abs ? mulrs(real_i(gtrace(x)),2*nbrows(x)) : gtrace(x); break;
    default: pari_err_TYPE("C_trace", x);
  }
  return gc_GEN(av, res);
}
static GEN
H_trace(GEN x, long abs)
{
  long s = abs? 2 : 1;
  switch (H_model(x))
  {
    case H_SCALAR: return gshift(real_i(x),s);
    case H_QUATERNION: return gshift(gel(x,1),s);
    case H_MATRIX:
      return algtrace_mat(NULL, x, abs);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

GEN
algtrace(GEN al, GEN x, long abs)
{
  long ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta==al_REAL) switch (alg_get_absdim(al)) {
    case 1: return R_trace(x,abs);
    case 2: return C_trace(x,abs);
    case 4: return H_trace(x,abs);
    default: pari_err_TYPE("algtrace [apply alginit]", al);
  }
  if (alg_model(al,x) == al_MATRIX) return algtrace_mat(al,x,abs);
  switch(ta) {
    case al_CYCLIC: case al_CSA:
      if (!abs) return algredtrace(al,x);
      if (alg_model(al,x)==al_ALGEBRAIC) x = algalgtobasis(al,x);
    case al_TABLE: return algabstrace(al,x);
    default : return NULL; /* LCOV_EXCL_LINE */
  }
}

static GEN
algtracebasis(GEN al)
{
  pari_sp av = avma;
  GEN mt = alg_get_multable(al), p = alg_get_char(al);
  long i, l = lg(mt);
  GEN v = cgetg(l, t_VEC);
  if (signe(p)) for (i=1; i < l; i++) gel(v,i) = FpM_trace(gel(mt,i), p);
  else          for (i=1; i < l; i++) gel(v,i) = ZM_trace(gel(mt,i));
  return gc_upto(av,v);
}

/* Assume: i > 0, expo := p^i <= absdim, x contained in I_{i-1} given by mult
 * table modulo modu=p^(i+1). Return Tr(x^(p^i)) mod modu */
static ulong
algtracei(GEN mt, ulong p, ulong expo, ulong modu)
{
  pari_sp av = avma;
  long j, l = lg(mt);
  ulong tr = 0;
  mt = Flm_powu(mt,expo,modu);
  for (j=1; j<l; j++) tr += ucoeff(mt,j,j);
  return gc_ulong(av, (tr/expo) % p);
}

static GEN
R_norm(GEN x, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR: res = gcopy(x); break;
    case H_MATRIX: res = abs ? powrs(det(x),nbrows(x)) : det(x); break;
    default: pari_err_TYPE("R_norm", x);
  }
  return gc_GEN(av,res);
}
static GEN
C_norm(GEN x, long abs)
{
  pari_sp av = avma;
  GEN res = NULL;
  switch (H_model(x))
  {
    case H_SCALAR: res = abs ? cxnorm(x) : x; break;
    case H_MATRIX: res = abs ? powrs(cxnorm(det(x)),nbrows(x)) : det(x); break;
    default: pari_err_TYPE("C_norm", x);
  }
  return gc_GEN(av,res);
}
static GEN
H_norm(GEN x, long abs)
{
  pari_sp av = avma;
  switch (H_model(x))
  {
    case H_SCALAR:
      if (abs)  return gc_GEN(av,gsqr(gnorm(x)));
      else      return gnorm(x);
    case H_QUATERNION:
      if (abs)  return gc_GEN(av,gsqr(gnorml2(x)));
      else      return gnorml2(x);
    case H_MATRIX:
      return gc_GEN(av,real_i(det(H_tomatrix(x,abs))));
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

GEN
algnorm(GEN al, GEN x, long abs)
{
  pari_sp av = avma;
  long tx, ta;
  GEN p, rnf, res, mx;
  checkalg(al);
  ta = alg_type(al);
  if (ta==al_REAL) switch (alg_get_absdim(al)) {
    case 1: return R_norm(x,abs);
    case 2: return C_norm(x,abs);
    case 4: return H_norm(x,abs);
    default: pari_err_TYPE("algnorm [apply alginit]", al);
  }
  p = alg_get_char(al);
  tx = alg_model(al,x);
  if (signe(p)) {
    if (tx == al_MATRIX)    mx = algleftmultable_mat(al,x);
    else                    mx = algbasismultable(al,x);
    return gc_upto(av, FpM_det(mx,p));
  }
  if (tx == al_TRIVIAL) return gcopy(gel(x,1));

  switch(ta) {
    case al_CYCLIC: case al_CSA:
      if (abs)
      {
        if (alg_model(al,x)==al_ALGEBRAIC) x = algalgtobasis(al,x);
      }
      else
      {
        rnf = alg_get_splittingfield(al);
        res = rnfeltdown(rnf, det(algtomatrix(al,x,0)));
        break;
      }
    case al_TABLE:
      if (tx == al_MATRIX)  mx = algleftmultable_mat(al,x);
      else                  mx = algbasismultable(al,x);
      res = det(mx);
      break;
    default: return NULL; /* LCOV_EXCL_LINE */
  }
  return gc_upto(av, res);
}

static GEN
algalgtonat_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = alg_get_abssplitting(al), rnf = alg_get_splittingfield(al), res, c;
  long n = alg_get_degree(al), N = nf_get_degree(nf), i, i1;
  res = zerocol(N*n);
  for (i=0; i<n; i++) {
    c = gel(x,i+1);
    c = rnfeltreltoabs(rnf,c);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      for (i1=1; i1<=N; i1++) gel(res,i*N+i1) = gel(c,i1);
    }
  }
  return gc_GEN(av, res);
}

static GEN
algalgtonat_csa(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = alg_get_center(al), res, c;
  long d2 = alg_get_dim(al), n = nf_get_degree(nf), i, i1;
  res = zerocol(d2*n);
  for (i=0; i<d2; i++) {
    c = gel(x,i+1);
    if (!gequal0(c)) {
      c = algtobasis(nf,c);
      for (i1=1; i1<=n; i1++) gel(res,i*n+i1) = gel(c,i1);
    }
  }
  return gc_GEN(av, res);
}

/* assumes al CSA or CYCLIC */
static GEN
algalgtonat(GEN al, GEN x)
{
  switch(alg_type(al))
  {
    case al_CYCLIC: return algalgtonat_cyc(al, x);
    case al_CSA: return algalgtonat_csa(al, x);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
algnattoalg_cyc(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = alg_get_abssplitting(al), rnf = alg_get_splittingfield(al), res, c;
  long n = alg_get_degree(al), N = nf_get_degree(nf), i, i1;
  res = zerocol(n);
  c = zerocol(N);
  for (i=0; i<n; i++) {
    for (i1=1; i1<=N; i1++) gel(c,i1) = gel(x,i*N+i1);
    gel(res,i+1) = rnfeltabstorel(rnf,basistoalg(nf,c));
  }
  return gc_GEN(av, res);
}

static GEN
algnattoalg_csa(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN nf = alg_get_center(al), res, c;
  long d2 = alg_get_dim(al), n = nf_get_degree(nf), i, i1;
  res = zerocol(d2);
  c = zerocol(n);
  for (i=0; i<d2; i++) {
    for (i1=1; i1<=n; i1++) gel(c,i1) = gel(x,i*n+i1);
    gel(res,i+1) = basistoalg(nf,c);
  }
  return gc_GEN(av, res);
}

/* assumes al CSA or CYCLIC */
static GEN
algnattoalg(GEN al, GEN x)
{
  switch(alg_type(al))
  {
    case al_CYCLIC: return algnattoalg_cyc(al, x);
    case al_CSA: return algnattoalg_csa(al, x);
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
algalgtobasis_mat(GEN al, GEN x) /* componentwise */
{
  pari_sp av = avma;
  long lx, lxj, i, j;
  GEN res;
  lx = lg(x);
  res = cgetg(lx, t_MAT);
  for (j=1; j<lx; j++) {
    lxj = lg(gel(x,j));
    gel(res,j) = cgetg(lxj, t_COL);
    for (i=1; i<lxj; i++)
      gcoeff(res,i,j) = algalgtobasis(al,gcoeff(x,i,j));
  }
  return gc_GEN(av,res);
}
GEN
algalgtobasis(GEN al, GEN x)
{
  pari_sp av;
  long tx, ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_CSA) pari_err_TYPE("algalgtobasis [use alginit]", al);
  tx = alg_model(al,x);
  if (tx==al_BASIS) return gcopy(x);
  if (tx==al_MATRIX) return algalgtobasis_mat(al,x);
  av = avma;
  x = algalgtonat(al,x);
  x = RgM_RgC_mul(alg_get_invbasis(al),x);
  return gc_upto(av, x);
}

/*
 Quaternion algebras special case:
 al = (L/F, sigma, b) with L quadratic
 > v^2-a: i = v
 > v^2+A*v+B: i = 2*v+A: i^2 = a = A^2-4*B
 al ~ (a,b)_F
*/
/* We could improve efficiency, but these functions are just for convenience. */
GEN
algquattobasis(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN L1, L2, pol, A, x2, nf;
  long v, i, ta;
  checkalg(al);
  if (alg_is_asq(al))
  {
    x = algalgtonat(al,x);
    x = RgM_RgC_mul(alg_get_invbasis(al),x);
    return gc_upto(av,x);
  }
  ta = alg_type(al);
  if (ta != al_CYCLIC || alg_get_degree(al)!=2)
    pari_err_TYPE("algquattobasis [not a quaternion algebra]", al);
  if (typ(x)!=t_COL && typ(x)!=t_VEC) pari_err_TYPE("algquattobasis", x);
  if (lg(x)!=5) pari_err_DIM("algquattobasis [quaternions have 4 components]");
  nf = alg_get_center(al);
  x2 = cgetg(5, t_COL);
  for (i=1; i<=4; i++) gel(x2,i) = basistoalg(nf, gel(x,i));
  gel(x2,4) = gneg(gel(x2,4));
  pol = alg_get_splitpol(al);
  v = varn(pol);
  A = gel(pol,3); /* coeff of v^1 */
  if (gequal0(A))
  {
    /* i = v */
    L1 = deg1pol_shallow(gel(x2,2), gel(x2,1), v);
    L2 = deg1pol_shallow(gel(x2,4), gel(x2,3), v);
  }
  else
  {
    /* i = 2*v+A */
    L1 = deg1pol_shallow(gshift(gel(x2,2),1),
        gadd(gel(x2,1),gmul(A,gel(x2,2))), v);
    L2 = deg1pol_shallow(gshift(gel(x2,4),1),
        gadd(gel(x2,3),gmul(A,gel(x2,4))), v);
  }
  return gc_upto(av, algalgtobasis(al,mkcol2(L1,L2)));
}
GEN
algbasistoquat(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN pol, A, x2, q;
  long v, ta;
  checkalg(al);
  if (alg_is_asq(al))
  {
    x = RgM_RgC_mul(alg_get_basis(al),x);
    x = algnattoalg(al,x);
    return gc_upto(av, x);
  }
  ta = alg_type(al);
  if (ta != al_CYCLIC || alg_get_degree(al)!=2)
    pari_err_TYPE("algbasistoquat [not a quaternion algebra]", al);
  pol = alg_get_splitpol(al);
  v = varn(pol);
  A = gel(pol,3); /* coeff of v^1 */
  x2 = algbasistoalg(al, x);
  x2 = lift0(x2, v);
  q = cgetg(5, t_COL);
  if (gequal0(A))
  {
    /* v = i */
    gel(q,1) = polcoef_i(gel(x2,1),0,v);
    gel(q,2) = polcoef_i(gel(x2,1),1,v);
    gel(q,3) = polcoef_i(gel(x2,2),0,v);
    gel(q,4) = polcoef_i(gel(x2,2),1,v);
    gel(q,4) = gneg(gel(q,4));
  }
  else
  {
    /* v = (i-A)/2 */
    gel(q,2) = gshift(polcoef_i(gel(x2,1),1,v),-1);
    gel(q,1) = gsub(polcoef_i(gel(x2,1),0,v), gmul(A,gel(q,2)));
    gel(q,4) = gneg(gshift(polcoef_i(gel(x2,2),1,v),-1));
    gel(q,3) = gadd(polcoef_i(gel(x2,2),0,v),gmul(A,gel(q,4)));
  }
  return gc_GEN(av, q);
}
GEN
algisquatalg(GEN al)
{
  pari_sp av = avma;
  GEN pol, a;
  long ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta == al_REAL && algreal_dim(al)==4)
    return gc_GEN(av, mkvec2(gen_m1,gen_m1));
  if (alg_is_asq(al))
    return gc_GEN(av, mkvec2(gmael3(al,6,1,1),gmael3(al,6,1,2)));
  if (ta != al_CYCLIC || alg_get_degree(al)!=2) return gc_const(av, gen_0);
  pol = alg_get_splitpol(al);
  if (gequal0(gel(pol,3))) a = gneg(gel(pol,2)); /* coeffs of v^1 and v^0 */
  else a = RgX_disc(pol);
  return gc_GEN(av, mkvec2(a,lift_shallow(alg_get_b(al))));
}

static GEN
algbasistoalg_mat(GEN al, GEN x) /* componentwise */
{
  long j, lx = lg(x);
  GEN res = cgetg(lx, t_MAT);
  for (j=1; j<lx; j++) {
    long i, lxj = lg(gel(x,j));
    gel(res,j) = cgetg(lxj, t_COL);
    for (i=1; i<lxj; i++) gcoeff(res,i,j) = algbasistoalg(al,gcoeff(x,i,j));
  }
  return res;
}
GEN
algbasistoalg(GEN al, GEN x)
{
  pari_sp av;
  long tx, ta;
  checkalg(al);
  ta = alg_type(al);
  if (ta != al_CYCLIC && ta != al_CSA) pari_err_TYPE("algbasistoalg [use alginit]", al);
  tx = alg_model(al,x);
  if (tx==al_ALGEBRAIC) return gcopy(x);
  if (tx==al_MATRIX) return algbasistoalg_mat(al,x);
  av = avma;
  x = RgM_RgC_mul(alg_get_basis(al),x);
  x = algnattoalg(al,x);
  return gc_upto(av, x);
}

static GEN
R_random(GEN b)
{
  pari_sp av = avma;
  long prec = realprec(b);
  GEN z = randomr(prec); shiftr_inplace(z, 1);
  return gc_leaf(av, mulrr(b,addsr(-1, z)));
}
static GEN
C_random(GEN b)
{
  retmkcomplex(R_random(b), R_random(b));
}
static GEN
H_random(GEN b)
{
  GEN res = cgetg(5, t_COL);
  long i;
  for (i=1; i<=4; i++) gel(res,i) = R_random(b);
  return res;
}
GEN
algrandom(GEN al, GEN b)
{
  GEN res = NULL, p, N;
  long i, n;
  checkalg(al);
  if (alg_type(al)==al_REAL)
  {
    if (typ(b) != t_REAL) pari_err_TYPE("algrandom",b);
    if (signe(b) < 0) pari_err_DOMAIN("algrandom", "b", "<", gen_0, b);
    switch(alg_get_absdim(al))
    {
      case 1: res = R_random(b); break;
      case 2: res = C_random(b); break;
      case 4: res = H_random(b); break;
      default: pari_err_TYPE("algrandom [apply alginit]", al);
    }
    return res;
  }
  if (typ(b) != t_INT) pari_err_TYPE("algrandom",b);
  if (signe(b) < 0) pari_err_DOMAIN("algrandom", "b", "<", gen_0, b);
  n = alg_get_absdim(al);
  N = addiu(shifti(b,1), 1); /* left on stack */
  p = alg_get_char(al); if (!signe(p)) p = NULL;
  res = cgetg(n+1,t_COL);
  for (i = 1; i <= n; i++)
  {
    pari_sp av = avma;
    GEN t = subii(randomi(N),b);
    if (p) t = modii(t, p);
    gel(res,i) = gc_INT(av, t);
  }
  return res;
}

static GEN
H_poleval(GEN pol, GEN x)
{
  pari_sp av = avma;
  GEN res;
  long i;
  switch (H_model(x))
  {
    case H_SCALAR: return RgX_cxeval(pol, x, NULL);
    case H_QUATERNION: break;
    default: pari_err_TYPE("H_poleval", x);
  }

  res = zerocol(4);
  for (i=lg(pol)-1; i>1; i--)
  {
    gel(res,1) = gadd(gel(res,1), gel(pol,i));
    if (i>2) res = H_mul(x, res);
  }

  return gc_GEN(av,res);
}

/* Assumes pol has coefficients in the same ring as the COL x; x either
 * in basis or algebraic form or [x,mx] where mx is the mult. table of x.
 TODO more general version: pol with coeffs in center and x in basis form */
GEN
algpoleval(GEN al, GEN pol, GEN x)
{
  pari_sp av = avma;
  GEN p, mx = NULL, res, c;
  long i, xalg = 0;
  if (typ(pol) != t_POL) pari_err_TYPE("algpoleval", pol);
  checkalg(al);
  if (alg_type(al)==al_REAL) return H_poleval(pol,x);
  p = alg_get_char(al);
  if (typ(x) == t_VEC)
  {
    if (lg(x) != 3) pari_err_TYPE("algpoleval [vector must be of length 2]", x);
    mx = gel(x,2);
    x = gel(x,1);
    if (typ(mx)!=t_MAT || !gequal(x,gel(mx,1)))
      pari_err_TYPE("algpoleval [mx must be the multiplication table of x]", mx);
  }
  else
  {
    switch(alg_model(al,x))
    {
      case al_ALGEBRAIC: mx = algalgmultable(al,x); xalg=1; break;
      case al_BASIS:
      case al_TRIVIAL: mx = algbasismultable(al,x); break;
      default: pari_err_TYPE("algpoleval", x);
    }
  }
  res = zerocol(lg(mx)-1);
  if (signe(p)) {
    for (i=lg(pol)-1; i>1; i--)
    {
      gel(res,1) = Fp_add(gel(res,1), gel(pol,i), p);
      if (i>2) res = FpM_FpC_mul(mx, res, p);
    }
  }
  else {
    for (i=lg(pol)-1; i>1; i--)
    {
      c = gel(pol,i);
      if (xalg || is_rational_t(typ(c))) gel(res,1) = gadd(gel(res,1), c);
      else res = RgC_add(res, algeltfromnf_i(al,c));
      if (i>2) res = RgM_RgC_mul(mx, res);
    }
  }
  return gc_upto(av, res);
}

static GEN
H_invol(GEN x)
{
  pari_sp av = avma;
  long tx;
  GEN cx;
  if (!x) return gc_upto(av,diagonal(mkvec4(gen_1,gen_m1,gen_m1,gen_m1)));
  tx = H_model(x);
  if (tx == H_SCALAR) return gconj(x);
  cx = gneg(x);
  gel(cx,1) = gcopy(gel(x,1));
  return gc_upto(av, cx);
}

GEN
alginvol(GEN al, GEN x)
{
  pari_sp av = avma;
  GEN invol;
  checkalg(al);
  if (!x && al) return gc_upto(av, alg_get_invol(al));
  if (alg_type(al)==al_REAL) return H_invol(x);
  x = algalgtobasis(al, x);
  invol = alg_get_invol(al);
  if (typ(invol)!=t_MAT)
    pari_err_DOMAIN("alginvol [al does not contain an involution]", "invol", "=", gen_0, invol);
  return gc_upto(av, RgM_RgC_mul(invol,x));
}

GEN
algskolemnoether(GEN al, GEN a, GEN fa)
{
  pari_sp av = avma;
  long c = 0, i, ta;
  GEN M, K, b;
  checkalg(al);
  ta = alg_type(al);
  if (ta!=al_CYCLIC && ta!=al_CSA) pari_err_TYPE("algskolemnoether"
      " [al: apply alginit()]", al);
  if (typ(a) != t_VEC) a = mkvec(a);
  if (typ(fa) != t_VEC) fa = mkvec(fa);
  if (lg(a) != lg(fa)) pari_err_DIM("algskolemnoether [lg(a) != lg(fa)]");
  if (lg(a) == 1) return gc_upto(av, col_ei(alg_get_absdim(al),1));

  /* compute space K of b s.t. b*a_i == fa_i*b for all i */
  M = cgetg(lg(a),t_COL);
  for (i=1; i<lg(a); i++) gel(M,i) = RgM_sub(algrightmultable(al,gel(a,i)),
                                      algleftmultable(al,gel(fa,i)));
  M = shallowmatconcat(M);
  K = QM_ker(M);

  /* find invertible element in K */
  if (lg(K)==1) pari_err(e_MISC, "no solution in algskolemnoether"
      " [check simplicity and homomorphism assumptions]");
  b = gel(K,1);
  while (!algisinv(al, b, NULL))
  {
    b = gadd(b, gel(K,1+random_Fl(lg(K)-1)));
    c++;
    if (c > 200) pari_err(e_MISC, "probable infinite loop in algskolemnoether"
        " (the subalgebra is probably not simple)");
  }
  return gc_upto(av, b);
}

/** GRUNWALD-WANG **/
/*
Song Wang's PhD thesis (pdf pages)
p.25 definition of chi_b. K^Ker(chi_b) = K(b^(1/m))
p.26 bound on the conductor (also Cohen adv. GTM 193 p.166)
p.21 & p.34 description special case, also on wikipedia:
http://en.wikipedia.org/wiki/Grunwald%E2%80%93Wang_theorem#Special_fields
p.77 Kummer case
*/

/* n > 0. Is n = 2^k ? */
static int
uispow2(ulong n) { return !(n &(n-1)); }

static GEN
get_phi0(GEN bnr, GEN Lpr, GEN Ld, GEN pl, long *pr, long *pn)
{
  const long NTRY = 10; /* FIXME: magic constant */
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  GEN S = bnr_get_cyc(bnr);
  GEN Sst, G, globGmod, loc, X, Rglob, Rloc, H, U, Lconj;
  long i, j, r, nbfrob, nbloc, nz, t;

  *pn = n;
  *pr = r = lg(S)-1;
  if (!r) return NULL;
  Sst = cgetg(r+1, t_VECSMALL); /* Z/n-dual */
  for (i=1; i<=r; i++) Sst[i] = ugcdiu(gel(S,i), n);
  if (Sst[1] != n) return NULL;
  Lconj = NULL;
  nbloc = nbfrob = lg(Lpr)-1;
  if (uispow2(n))
  {
    long l = lg(pl), k = 0;
    GEN real = cgetg(l, t_VECSMALL);
    for (i = 1; i < l; i++)
      if (pl[i] == -1) real[++k] = i;
    if (k)
    {
      GEN nf = bnr_get_nf(bnr), I = bid_get_fact(bnr_get_bid(bnr));
      GEN v, y, C = idealchineseinit(bnr, I);
      long r1 = nf_get_r1(nf), n = nbrows(I);
      nbloc += k;
      Lconj = cgetg(k+1, t_VEC);
      v = const_vecsmall(r1, 1);
      y = const_vec(n, gen_1);
      for (i = 1; i <= k; i++)
      {
        v[real[i]] = -1; gel(Lconj,i) = idealchinese(nf, mkvec2(C,v), y);
        v[real[i]] = 1;
      }
    }
  }
  globGmod = cgetg(r+1,t_MAT);
  G = cgetg(r+1,t_VECSMALL);
  for (i = 1; i <= r; i++)
  {
    G[i] = n / Sst[i]; /* pairing between S and Sst */
    gel(globGmod,i) = cgetg(nbloc+1,t_VECSMALL);
  }

  /* compute images of Frobenius elements (and complex conjugation) */
  loc = cgetg(nbloc+1,t_VECSMALL);
  for (i = 1; i <= nbloc; i++)
  {
    long L;
    if (i <= nbfrob)
    {
      X = gel(Lpr, i);
      L = Ld[i];
    }
    else
    { /* X = 1 (mod f), sigma_i(x) < 0, positive at all other real places */
      X = gel(Lconj, i-nbfrob);
      L = 2;
    }
    X = ZV_to_Flv(isprincipalray(bnr,X), n);
    for (nz=0,j=1; j<=r; j++)
    {
      ulong c = (X[j] * G[j]) % L;
      ucoeff(globGmod,i,j) = c;
      if (c) nz = 1;
    }
    if (!nz) return NULL;
    loc[i] = L;
  }

  /* try some random elements in the dual */
  Rglob = cgetg(r+1,t_VECSMALL);
  for (t=0; t<NTRY; t++) {
    for (j = 1; j <= r; j++) Rglob[j] = random_Fl(Sst[j]);
    Rloc = zm_zc_mul(globGmod,Rglob);
    for (i = 1; i <= nbloc; i++)
      if (Rloc[i] % loc[i] == 0) break;
    if (i > nbloc) return zv_to_ZV(Rglob);
  }

  /* try to realize some random elements of the product of the local duals */
  H = ZM_hnfall_i(shallowconcat(zm_to_ZM(globGmod),
                                diagonal_shallow(zv_to_ZV(loc))), &U, 2);
  /* H,U nbloc x nbloc */
  Rloc = cgetg(nbloc+1,t_COL);
  for (t = 0; t < NTRY; t++)
  { /* nonzero random coordinate */ /* TODO add special case ? */
    for (i = 1; i <= nbloc; i++) gel(Rloc,i) = stoi(1 + random_Fl(loc[i]-1));
    Rglob = hnf_invimage(H, Rloc);
    if (Rglob)
    {
      Rglob = ZM_ZC_mul(U,Rglob);
      return vecslice(Rglob,1,r);
    }
  }
  return NULL;
}

static GEN
bnrgwsearch(GEN bnr, GEN Lpr, GEN Ld, GEN pl)
{
  pari_sp av = avma;
  long n, r;
  GEN phi0 = get_phi0(bnr,Lpr,Ld,pl, &r,&n), gn, v, H,U;
  if (!phi0) return gc_const(av, gen_0);
  gn = stoi(n);
  /* compute kernel of phi0 */
  v = ZV_extgcd(vec_append(phi0, gn));
  U = vecslice(gel(v,2), 1,r);
  H = ZM_hnfmodid(rowslice(U, 1,r), gn);
  return gc_upto(av, H);
}

GEN
bnfgwgeneric(GEN bnf, GEN Lpr, GEN Ld, GEN pl, long var)
{
  pari_sp av = avma;
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  forprime_t S;
  GEN bnr = NULL, ideal = gen_1, nf, dec, H = gen_0, finf, pol;
  ulong ell, p;
  long deg, i, degell;
  (void)uisprimepower(n, &ell);
  nf = bnf_get_nf(bnf);
  deg = nf_get_degree(nf);
  degell = ugcd(deg,ell-1);
  finf = cgetg(lg(pl),t_VEC);
  for (i=1; i<lg(pl); i++) gel(finf,i) = pl[i]==-1 ? gen_1 : gen_0;

  u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S))) {
    if (Fl_powu(p % ell, degell, ell) != 1) continue; /* ell | p^deg-1 ? */
    dec = idealprimedec(nf, utoipos(p));
    for (i=1; i<lg(dec); i++) {
      GEN pp = gel(dec,i);
      if (RgV_isin(Lpr,pp)) continue;
        /* TODO also accept the prime ideals at which there is a condition
         * (use local Artin)? */
      if (smodis(idealnorm(nf,pp),ell) != 1) continue; /* ell | N(pp)-1 ? */
      ideal = idealmul(bnf,ideal,pp);
      /* TODO: give factorization ? */
      bnr = Buchray(bnf, mkvec2(ideal,finf), nf_INIT);
      H = bnrgwsearch(bnr,Lpr,Ld,pl);
      if (H != gen_0)
      {
        pol = rnfkummer(bnr,H,nf_get_prec(nf));
        setvarn(pol, var);
        return gc_upto(av,pol);
      }
    }
  }
  pari_err_BUG("bnfgwgeneric (no suitable p)"); /*LCOV_EXCL_LINE*/
  return NULL;/*LCOV_EXCL_LINE*/
}

/* pr.p != ell */
static GEN
localextdeg(GEN nf, GEN pr, long d, ulong ell, long n)
{
  GEN modpr, T, p, gen, k;
  if (d == 1) return gen_1;
  k = powuu(ell, Z_lval(subiu(pr_norm(pr),1), ell));
  k = divis(k, n / d);
  modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  (void)Fq_sqrtn(gen_1, k, T, p, &gen);
  return Fq_to_nf(gen, modpr);
}
/* pr.p = ell */
static GEN
localextdegell(GEN nf, GEN pr, GEN E, long d, long n)
{
  GEN x;
  if (d == 1) return gen_1;
  x = nfadd(nf, gen_1, pr_get_gen(pr));
  return nfpowmodideal(nf, x, stoi(n / d), idealpow(nf, pr, E));
}

/* Ld[i] must be nontrivial powers of the same prime ell */
/* pl : -1 at real places at which the extension must ramify, 0 elsewhere */
GEN
nfgwkummer(GEN nf, GEN Lpr, GEN Ld, GEN pl, long var)
{
  const long n = (lg(Ld)==1)? 2: vecsmall_max(Ld);
  ulong ell;
  long i, l = lg(Lpr), v = uisprimepower(n, &ell);
  GEN E = cgetg(l, t_COL), y = cgetg(l, t_VEC), fa;

  for (i = 1; i < l; i++)
  {
    GEN pr = gel(Lpr,i), p = pr_get_p(pr);
    if (!absequalui(ell, p))
    {
      gel(E, i) = gen_1;
      gel(y, i) = localextdeg(nf, pr, Ld[i], ell, n);
    }
    else
    {
      long e = pr_get_e(pr);
      gel(E, i) = addui(1 + v*e, divsi(e, subiu(p,1)));
      gel(y, i) = localextdegell(nf, pr, gel(E,i), Ld[i], n);
    }
  }
  y = factoredextchinese(nf, mkmat2(shallowtrans(Lpr),E), y, pl, &fa);
  return gsub(gpowgs(pol_x(var),n), basistoalg(nf, y));
}

static GEN
get_vecsmall(GEN v)
{
  switch(typ(v))
  {
    case t_VECSMALL: return v;
    case t_VEC: if (RgV_is_ZV(v)) return ZV_to_zv(v);
  }
  pari_err_TYPE("nfgrunwaldwang",v);
  return NULL;/*LCOV_EXCL_LINE*/
}
GEN
nfgrunwaldwang(GEN nf0, GEN Lpr, GEN Ld, GEN pl, long var)
{
  ulong n, ell, ell2;
  pari_sp av = avma;
  GEN nf, bnf;
  long t, w, i, vnf;

  if (var < 0) var = 0;
  nf = get_nf(nf0,&t);
  if (!nf) pari_err_TYPE("nfgrunwaldwang",nf0);
  vnf = nf_get_varn(nf);
  if (varncmp(var, vnf) >= 0)
    pari_err_PRIORITY("nfgrunwaldwang", pol_x(var), ">=", vnf);
  if (typ(Lpr) != t_VEC) pari_err_TYPE("nfgrunwaldwang",Lpr);
  if (lg(Lpr) != lg(Ld)) pari_err_DIM("nfgrunwaldwang [#Lpr != #Ld]");
  if (nf_get_degree(nf)==1) Lpr = shallowcopy(Lpr);
  for (i=1; i<lg(Lpr); i++) {
    GEN pr = gel(Lpr,i);
    if (nf_get_degree(nf)==1 && typ(pr)==t_INT)
      gel(Lpr,i) = gel(idealprimedec(nf,pr), 1);
    else checkprid(pr);
  }
  if (lg(pl)-1 != nf_get_r1(nf))
    pari_err_DOMAIN("nfgrunwaldwang [pl should have r1 components]", "#pl",
        "!=", stoi(nf_get_r1(nf)), stoi(lg(pl)-1));

  Ld = get_vecsmall(Ld);
  pl = get_vecsmall(pl);
  bnf = get_bnf(nf0,&t);
  n = (lg(Ld)==1)? 2: vecsmall_max(Ld);

  if (!uisprimepower(n, &ell))
    pari_err_IMPL("nfgrunwaldwang for non prime-power local degrees (a)");
  for (i=1; i<lg(Ld); i++)
    if (Ld[i]!=1 && (!uisprimepower(Ld[i],&ell2) || ell2!=ell))
      pari_err_IMPL("nfgrunwaldwang for non prime-power local degrees (b)");
  for (i=1; i<lg(pl); i++)
    if (pl[i]==-1 && ell%2)
      pari_err_IMPL("nfgrunwaldwang for non prime-power local degrees (c)");

  w = bnf? bnf_get_tuN(bnf): itos(gel(nfrootsof1(nf),1));

  /* TODO choice between kummer and generic ? Let user choose between speed
   * and size */
  if (w%n==0 && lg(Ld)>1)
    return gc_upto(av, nfgwkummer(nf,Lpr,Ld,pl,var));
  if (ell==n)
  {
    if (!bnf) bnf = Buchall(nf, nf_FORCE, 0);
    return gc_upto(av, bnfgwgeneric(bnf,Lpr,Ld,pl,var));
  }
  pari_err_IMPL("nfgrunwaldwang for nonprime degree");
  return NULL; /*LCOV_EXCL_LINE*/
}

/** HASSE INVARIANTS **/

/* TODO long -> ulong + uel */
static GEN
hasseconvert(GEN H, long n)
{
  GEN h, c;
  long i, l;
  switch(typ(H)) {
    case t_VEC:
      l = lg(H); h = cgetg(l,t_VECSMALL);
      if (l == 1) return h;
      c = gel(H,1);
      if (typ(c) == t_VEC && l == 3)
        return mkvec2(gel(H,1),hasseconvert(gel(H,2),n));
      for (i=1; i<l; i++)
      {
        c = gel(H,i);
        switch(typ(c)) {
          case t_INT:  break;
          case t_INTMOD:
            c = gel(c,2); break;
          case t_FRAC :
            c = gmulgs(c,n);
            if (typ(c) == t_INT) break;
            pari_err_DOMAIN("hasseconvert [degree should be a denominator of the invariant]", "denom(h)", "ndiv", stoi(n), Q_denom(gel(H,i)));
          default : pari_err_TYPE("Hasse invariant", c);
        }
        h[i] = smodis(c,n);
      }
      return h;
    case t_VECSMALL: return H;
  }
  pari_err_TYPE("Hasse invariant", H);
  return NULL;/*LCOV_EXCL_LINE*/
}

/* assume f >= 2 */
static long
cyclicrelfrob0(GEN nf, GEN aut, GEN pr, GEN q, long f, long g)
{
  GEN T, p, a, b, modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  long s;

  a = pol_x(nf_get_varn(nf));
  b = galoisapply(nf, aut, modpr_genFq(modpr));
  b = nf_to_Fq(nf, b, modpr);
  for (s = 0; !ZX_equal(a, b); s++) a = Fq_pow(a, q, T, p);
  return g * Fl_inv(s, f); /* < n */
}

static long
cyclicrelfrob(GEN rnf, GEN auts, GEN pr)
{
  pari_sp av = avma;
  long f,g,frob, n = rnf_get_degree(rnf);
  GEN P = rnfidealprimedec(rnf, pr);

  if (pr_get_e(gel(P,1)) > pr_get_e(pr))
    pari_err_DOMAIN("cyclicrelfrob","e(PR/pr)",">",gen_1,pr);
  g = lg(P) - 1;
  f = n / g;

  if (f <= 2) frob = g % n;
  else {
    GEN nf2, PR = gel(P,1);
    GEN autabs = rnfeltreltoabs(rnf,gel(auts,g));
    nf2 = obj_check(rnf,rnf_NFABS);
    autabs = nfadd(nf2, autabs, gmul(rnf_get_k(rnf), rnf_get_alpha(rnf)));
    frob = cyclicrelfrob0(nf2, autabs, PR, pr_norm(pr), f, g);
  }
  return gc_long(av, frob);
}

static long
localhasse(GEN rnf, GEN cnd, GEN pl, GEN auts, GEN b, long k)
{
  pari_sp av = avma;
  long v, m, h, lfa, frob, n, i;
  GEN previous, y, pr, nf, q, fa;
  nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  pr = gcoeff(cnd,k,1);
  v = nfval(nf, b, pr);
  m = lg(cnd)>1 ? nbrows(cnd) : 0;

  /* add the valuation of b to the conductor... */
  previous = gcoeff(cnd,k,2);
  gcoeff(cnd,k,2) = addis(previous, v);

  y = const_vec(m, gen_1);
  gel(y,k) = b;
  /* find a factored element y congruent to b mod pr^(vpr(b)+vpr(cnd)) and to 1 mod the conductor. */
  y = factoredextchinese(nf, cnd, y, pl, &fa);
  h = 0;
  lfa = nbrows(fa);
  /* sum of all Hasse invariants of (rnf/nf,aut,y) is 0, Hasse invariants at q!=pr are easy, Hasse invariant at pr is the same as for al=(rnf/nf,aut,b). */
  for (i=1; i<=lfa; i++) {
    q = gcoeff(fa,i,1);
    if (cmp_prime_ideal(pr,q)) {
      frob = cyclicrelfrob(rnf, auts, q);
      frob = Fl_mul(frob,umodiu(gcoeff(fa,i,2),n),n);
      h = Fl_add(h,frob,n);
    }
  }
  /* ...then restore it. */
  gcoeff(cnd,k,2) = previous;
  return gc_long(av, Fl_neg(h,n));
}

static GEN
allauts(GEN rnf, GEN aut)
{
  long n = rnf_get_degree(rnf), i;
  GEN pol = rnf_get_pol(rnf), vaut;
  if (n==1) n=2;
  vaut = cgetg(n,t_VEC);
  aut = lift_shallow(rnfbasistoalg(rnf,aut));
  if (typ(aut) != t_POL || varn(pol) != varn(aut))
    pari_err_TYPE("alg_cyclic", aut);
  gel(vaut,1) = aut;
  for (i=1; i<n-1; i++)
    gel(vaut,i+1) = RgX_rem(poleval(gel(vaut,i), aut), pol);
  return vaut;
}

static GEN
clean_factor(GEN fa)
{
  GEN P2,E2, P = gel(fa,1), E = gel(fa,2);
  long l = lg(P), i, j = 1;
  P2 = cgetg(l, t_COL);
  E2 = cgetg(l, t_COL);
  for (i = 1;i < l; i++)
    if (signe(gel(E,i))) {
      gel(P2,j) = gel(P,i);
      gel(E2,j) = gel(E,i); j++;
    }
  setlg(P2,j);
  setlg(E2,j); return mkmat2(P2,E2);
}

/* shallow concat x[1],...x[nx],y[1], ... y[ny], returning a t_COL. To be
 * used when we do not know whether x,y are t_VEC or t_COL */
static GEN
colconcat(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z=cgetg(lx+ly-1, t_COL);
  for (i=1; i<lx; i++) z[i]     = x[i];
  for (i=1; i<ly; i++) z[lx+i-1]= y[i];
  return z;
}

/* return v(x) at all primes in listpr, replace x by cofactor */
static GEN
nfmakecoprime(GEN nf, GEN *px, GEN listpr)
{
  long j, l = lg(listpr);
  GEN x1, x = *px, L = cgetg(l, t_COL);

  if (typ(x) != t_MAT)
  { /* scalar, divide at the end (fast valuation) */
    x1 = NULL;
    for (j=1; j<l; j++)
    {
      GEN pr = gel(listpr,j), e;
      long v = nfval(nf, x, pr);
      e = stoi(v); gel(L,j) = e;
      if (v) x1 = x1? idealmulpowprime(nf, x1, pr, e)
                    : idealpow(nf, pr, e);
    }
    if (x1) x = idealdivexact(nf, idealhnf(nf,x), x1);
  }
  else
  { /* HNF, divide as we proceed (reduce size) */
    for (j=1; j<l; j++)
    {
      GEN pr = gel(listpr,j);
      long v = idealval(nf, x, pr);
      gel(L,j) = stoi(v);
      if (v) x = idealmulpowprime(nf, x, pr, stoi(-v));
    }
  }
  *px = x; return L;
}

/* Caveat: factorizations are not sorted wrt cmp_prime_ideal: Lpr comes first */
static GEN
computecnd(GEN rnf, GEN Lpr)
{
  GEN id, nf, fa, Le, P,E;
  long n = rnf_get_degree(rnf);

  nf = rnf_get_nf(rnf);
  id = rnf_get_idealdisc(rnf);
  Le = nfmakecoprime(nf, &id, Lpr);
  fa = idealfactor(nf, id); /* part of D_{L/K} coprime with Lpr */
  P =  colconcat(Lpr,gel(fa,1));
  E =  colconcat(Le, gel(fa,2));
  fa = mkmat2(P, gdiventgs(E, eulerphiu(n)));
  return mkvec2(fa, clean_factor(fa));
}

/* h >= 0 */
static void
nextgen(GEN gene, long h, GEN* gens, GEN* hgens, long* ngens, long* curgcd) {
  long nextgcd = ugcd(h,*curgcd);
  if (nextgcd == *curgcd) return;
  (*ngens)++;
  gel(*gens,*ngens) = gene;
  gel(*hgens,*ngens) = utoi(h);
  *curgcd = nextgcd;
  return;
}

static int
dividesmod(long d, long h, long n) { return !(h%cgcd(d,n)); }

/* ramified prime with nontrivial Hasse invariant */
static GEN
localcomplete(GEN rnf, GEN pl, GEN cnd, GEN auts, long j, long n, long h, long* v)
{
  GEN nf, gens, hgens, pr, modpr, T, p, sol, U, b, gene, randg, pu;
  long ngens, i, d, np, d1, d2, hg, dnf, vcnd, curgcd;
  nf = rnf_get_nf(rnf);
  pr = gcoeff(cnd,j,1);
  np = umodiu(pr_norm(pr), n);
  dnf = nf_get_degree(nf);
  vcnd = itos(gcoeff(cnd,j,2));
  ngens = 13+dnf;
  gens = zerovec(ngens);
  hgens = zerovec(ngens);
  *v = 0;
  curgcd = 0;
  ngens = 0;

  if (!uisprime(n)) {
    gene =  pr_get_gen(pr);
    hg = localhasse(rnf, cnd, pl, auts, gene, j);
    nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
  }

  if (ugcd(np,n) != 1) { /* GCD(Np,n) != 1 */
    pu = idealprincipalunits(nf,pr,vcnd);
    pu = abgrp_get_gen(pu);
    for (i=1; i<lg(pu) && !dividesmod(curgcd,h,n); i++) {
      gene = gel(pu,i);
      hg = localhasse(rnf, cnd, pl, auts, gene, j);
      nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
    }
  }

  d = ugcd(np-1,n);
  if (d != 1) { /* GCD(Np-1,n) != 1 */
    modpr = nf_to_Fq_init(nf, &pr, &T, &p);
    while (!dividesmod(curgcd,h,n)) { /* TODO gener_FpXQ_local */
      if (T==NULL) randg = randomi(p);
      else randg = random_FpX(degpol(T), varn(T),p);

      if (!gequal0(randg) && !gequal1(randg)) {
        gene = Fq_to_nf(randg, modpr);
        hg = localhasse(rnf, cnd, pl, auts, gene, j);
        nextgen(gene, hg, &gens, &hgens, &ngens, &curgcd);
      }
    }
  }

  setlg(gens,ngens+1);
  setlg(hgens,ngens+1);

  sol = ZV_extgcd(hgens);
  U = ZV_to_Flv(gmael(sol,2,ngens), n);
  d = itou(gel(sol,1));
  d1 = ugcd(d, n);
  d2 = d / d1;
  d = Fl_mul(h / d1, Fl_inv(d2,n), n);
  if (d != 1) U = Flv_Fl_mul(U, d, n);
  for (i = 1, b = gen_1; i <= ngens; i++)
    if (U[i]) b = nfmul(nf, b, nfpow_u(nf, gel(gens,i), U[i]));
  *v = U[1]; return b;
}

static int
testsplits(GEN data, GEN fa)
{
  GEN rnf = gel(data,1), forbid = gel(data,2), P = gel(fa,1), E = gel(fa,2);
  long i, n, l = lg(P);

  for (i = 1; i < l; i++)
  {
    GEN pr = gel(P,i);
    if (tablesearch(forbid, pr, &cmp_prime_ideal)) return 0;
  }
  n = rnf_get_degree(rnf);
  for (i = 1; i < l; i++)
  {
    long e = itos(gel(E,i)) % n;
    if (e)
    {
      GEN L = rnfidealprimedec(rnf, gel(P,i));
      long g = lg(L) - 1;
      if ((e * g) % n) return 0;
    }
  }
  return 1;
}

/* remove entries with Hasse invariant 0 */
static GEN
hassereduce(GEN hf)
{
  GEN pr,h, PR = gel(hf,1), H = gel(hf,2);
  long i, j, l = lg(PR);

  pr= cgetg(l, t_VEC);
  h = cgetg(l, t_VECSMALL);
  for (i = j = 1; i < l; i++)
    if (H[i]) {
      gel(pr,j) = gel(PR,i);
      h[j] = H[i]; j++;
    }
  setlg(pr,j);
  setlg(h,j); return mkvec2(pr,h);
}

static void
alg_insert_quatconj(GEN al)
{
  GEN aut, nf, rnf, nfabs, gene, absaut;
  long d;
  aut = alg_get_aut(al);
  d = alg_get_absdim(al) / 4;
  nf = alg_get_center(al);
  rnf = alg_get_splittingfield(al);
  nfabs = rnf_build_nfabs(rnf, nf_get_prec(nf));
  gene = lift_shallow(rnfeltabstorel(rnf,pol_x(nf_get_varn(nfabs))));
  absaut = rnfeltreltoabs(rnf,poleval(gene,aut));
  gmael(al,6,2) = shallowmatconcat(mkmat22(
    nfgaloismatrix(nfabs,absaut),
    gen_0,
    gen_0,
    gneg(matid(2*d))
    ));
}

/* rnf complete */
static GEN
alg_complete0(GEN rnf, GEN aut, GEN hf, GEN hi, long flag)
{
  pari_sp av = avma;
  GEN nf, pl, pl2, cnd, prcnd, cnds, y, Lpr, auts, b, fa, data, hfe;
  GEN forbid, al, ind, perm;
  long D, n, d, i, j, l;
  nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  d = nf_get_degree(nf);
  D = d*n*n;
  checkhasse(nf,hf,hi,n);
  hf = hassereduce(hf);
  Lpr = gel(hf,1);
  hfe = gel(hf,2);

  auts = allauts(rnf,aut);

  pl = leafcopy(hi); /* conditions on the final b */
  pl2 = leafcopy(hi); /* conditions for computing local Hasse invariants */
  l = lg(pl); ind = cgetg(l, t_VECSMALL);
  for (i = j = 1; i < l; i++)
    if (hi[i]) { pl[i] = -1; pl2[i] = 1; } else ind[j++] = i;
  setlg(ind, j);
  y = nfpolsturm(nf, rnf_get_pol(rnf), ind);
  for (i = 1; i < j; i++)
    if (!signe(gel(y,i))) { pl[ind[i]] = 1; pl2[ind[i]] = 1; }

  cnds = computecnd(rnf,Lpr);
  prcnd = gel(cnds,1);
  cnd = gel(cnds,2);
  y = cgetg(lgcols(prcnd),t_VEC);
  forbid = vectrunc_init(lg(Lpr));
  for (i=j=1; i<lg(Lpr); i++)
  {
    GEN pr = gcoeff(prcnd,i,1), yi;
    long v, e = itou( gcoeff(prcnd,i,2) );
    if (!e) {
      long frob = cyclicrelfrob(rnf,auts,pr), f1 = ugcd(frob,n);
      vectrunc_append(forbid, pr);
      yi = gen_0;
      v = ((hfe[i]/f1) * Fl_inv(frob/f1,n)) % n;
    }
    else
      yi = localcomplete(rnf, pl2, cnd, auts, j++, n, hfe[i], &v);
    gel(y,i) = yi;
    gcoeff(prcnd,i,2) = stoi(e + v);
  }
  for (; i<lgcols(prcnd); i++) gel(y,i) = gen_1;
  gen_sort_inplace(forbid, (void*)&cmp_prime_ideal, &cmp_nodata, NULL);
  data = mkvec2(rnf,forbid);
  b = factoredextchinesetest(nf,prcnd,y,pl,&fa,data,testsplits);

  al = cgetg(12, t_VEC);
  gel(al,10)= gen_0; /* must be set first */
  gel(al,1) = rnf;
  gel(al,2) = auts;
  gel(al,3) = basistoalg(nf,b);
  gel(al,4) = hi;
  /* add primes | disc or b with trivial Hasse invariant to hf */
  Lpr = gel(prcnd,1); y = b;
  (void)nfmakecoprime(nf, &y, Lpr);
  Lpr = shallowconcat(Lpr, gel(idealfactor(nf,y), 1));
  settyp(Lpr,t_VEC);
  hf = shallowconcat(hfe, const_vecsmall(lg(Lpr)-lg(hfe), 0));
  perm = gen_indexsort(Lpr, (void*)&cmp_prime_ideal, &cmp_nodata);
  gel(al,5) = mkvec2(vecpermute(Lpr,perm), vecsmallpermute(hf,perm));
  gel(al,6) = mkvec2(gen_0,gen_0);
  gel(al,7) = matid(D);
  gel(al,8) = matid(D); /* TODO modify 7, 8 et 9 once LLL added */
  gel(al,9) = algnatmultable(al,D);
  gel(al,11)= algtracebasis(al);

  if (n==2) alg_insert_quatconj(al);
  if (flag & al_MAXORD) al = alg_maximal_primes(al, prV_primes(Lpr));
  return gc_GEN(av, al);
}

GEN
alg_complete(GEN rnf, GEN aut, GEN hf, GEN hi, long flag)
{
  long n = rnf_get_degree(rnf);
  rnfcomplete(rnf);
  return alg_complete0(rnf, aut, hasseconvert(hf,n), hasseconvert(hi,n), flag);
}

void
checkhasse(GEN nf, GEN hf, GEN hi, long n)
{
  GEN Lpr, Lh;
  long i, sum;
  if (typ(hf) != t_VEC || lg(hf) != 3) pari_err_TYPE("checkhasse [hf]", hf);
  Lpr = gel(hf,1);
  Lh = gel(hf,2);
  if (typ(Lpr) != t_VEC) pari_err_TYPE("checkhasse [Lpr]", Lpr);
  if (typ(Lh) != t_VECSMALL) pari_err_TYPE("checkhasse [Lh]", Lh);
  if (typ(hi) != t_VECSMALL) pari_err_TYPE("checkhasse [hi]", hi);
  if ((nf && lg(hi) != nf_get_r1(nf)+1))
    pari_err_DOMAIN("checkhasse [hi should have r1 components]","#hi","!=",stoi(nf_get_r1(nf)),stoi(lg(hi)-1));
  if (lg(Lpr) != lg(Lh))
    pari_err_DIM("checkhasse [Lpr and Lh should have same length]");
  for (i=1; i<lg(Lpr); i++) checkprid(gel(Lpr,i));
  if (lg(gen_sort_uniq(Lpr, (void*)cmp_prime_ideal, cmp_nodata)) < lg(Lpr))
    pari_err(e_MISC, "error in checkhasse [duplicate prime ideal]");
  sum = 0;
  for (i=1; i<lg(Lh); i++) sum = (sum+Lh[i])%n;
  for (i=1; i<lg(hi); i++) {
      if (hi[i] && 2*hi[i] != n) pari_err_DOMAIN("checkhasse", "Hasse invariant at real place [must be 0 or 1/2]", "!=", n%2? gen_0 : stoi(n/2), stoi(hi[i]));
      sum = (sum+hi[i])%n;
  }
  if (sum<0) sum = n+sum;
  if (sum != 0)
    pari_err_DOMAIN("checkhasse","sum(Hasse invariants)","!=",gen_0,Lh);
}

static GEN
hassecoprime(GEN hf, GEN hi, long n)
{
  pari_sp av = avma;
  long l, i, j, lk, inv;
  GEN fa, P,E, res, hil, hfl;
  hi = hasseconvert(hi, n);
  hf = hasseconvert(hf, n);
  checkhasse(NULL,hf,hi,n);
  fa = factoru(n);
  P = gel(fa,1); l = lg(P);
  E = gel(fa,2);
  res = cgetg(l,t_VEC);
  for (i=1; i<l; i++) {
    lk = upowuu(P[i],E[i]);
    inv = Fl_invsafe((n/lk)%lk, lk);
    hil = gcopy(hi);
    hfl = gcopy(hf);

    if (P[i] == 2)
      for (j=1; j<lg(hil); j++) hil[j] = hi[j]==0 ? 0 : lk/2;
    else
      for (j=1; j<lg(hil); j++) hil[j] = 0;
    for (j=1; j<lgcols(hfl); j++) gel(hfl,2)[j] = (gel(hf,2)[j]*inv)%lk;
    hfl = hassereduce(hfl);
    gel(res,i) = mkvec3(hfl,hil,utoi(lk));
  }

  return gc_GEN(av, res);
}

/* no garbage collection */
static GEN
genefrob(GEN nf, GEN gal, GEN r)
{
  long i;
  GEN g = identity_perm(nf_get_degree(nf)), fa = Z_factor(r), p, pr, frob;
  for (i=1; i<lgcols(fa); i++) {
    p = gcoeff(fa,i,1);
    pr = idealprimedec(nf, p);
    pr = gel(pr,1);
    frob = idealfrobenius(nf, gal, pr);
    g = perm_mul(g, perm_pow(frob, gcoeff(fa,i,2)));
  }
  return g;
}

static GEN
rnfcycaut(GEN rnf)
{
  GEN nf2 = obj_check(rnf, rnf_NFABS);
  GEN L, alpha, pol, salpha, s, sj, polabs, k, X, pol0, nf;
  long i, d, j;
  d = rnf_get_degree(rnf);
  L = galoisconj(nf2,NULL);
  alpha = lift_shallow(rnf_get_alpha(rnf));
  pol = rnf_get_pol(rnf);
  k = rnf_get_k(rnf);
  polabs = rnf_get_polabs(rnf);
  nf = rnf_get_nf(rnf);
  pol0 = nf_get_pol(nf);
  X = RgX_rem(pol_x(varn(pol0)), pol0);

  /* TODO check mod prime of degree 1 */
  for (i=1; i<lg(L); i++) {
    s = gel(L,i);
    salpha = RgX_RgXQ_eval(alpha,s,polabs);
    if (!gequal(alpha,salpha)) continue;

    s = lift_shallow(rnfeltabstorel(rnf,s));
    sj = s = gsub(s, gmul(k,X));
    for (j=1; !gequal0(gsub(sj,pol_x(varn(s)))); j++)
      sj = RgX_RgXQ_eval(sj,s,pol);
    if (j<d) continue;
    return s;
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/* returns the smallest prime not in P */
static GEN
extraprime(GEN P)
{
  forprime_t T;
  GEN p;
  forprime_init(&T, gen_2, NULL);
  while ((p = forprime_next(&T))) if (!ZV_search(P, p)) break;
  return p;
}

/* true nf */
GEN
alg_hasse(GEN nf, long n, GEN hf, GEN hi, long var, long flag)
{
  pari_sp av = avma;
  GEN primary, al = gen_0, al2, rnf, hil, hfl, Ld, pl, pol, Lpr, aut, Lpr2, Ld2;
  long i, lk, j, maxdeg;
  dbg_printf(1)("alg_hasse\n");
  if (n<=1) pari_err_DOMAIN("alg_hasse", "degree", "<=", gen_1, stoi(n));
  primary = hassecoprime(hf, hi, n);
  for (i=1; i<lg(primary); i++) {
    lk = itos(gmael(primary,i,3));
    hfl = gmael(primary,i,1);
    hil = gmael(primary,i,2);
    checkhasse(nf, hfl, hil, lk);
    dbg_printf(1)("alg_hasse: i=%d hf=%Ps hi=%Ps lk=%d\n", i, hfl, hil, lk);

    if (lg(gel(hfl,1))>1 || lk%2==0) {
      maxdeg = 1;
      Lpr = gel(hfl,1);
      Ld = gcopy(gel(hfl,2));
      for (j=1; j<lg(Ld); j++)
      {
        Ld[j] = lk/ugcd(lk,Ld[j]);
        maxdeg = maxss(Ld[j],maxdeg);
      }
      pl = leafcopy(hil);
      for (j=1; j<lg(pl); j++) if(pl[j])
      {
        pl[j] = -1;
        maxdeg = maxss(maxdeg,2);
      }

      Lpr2 = Lpr;
      Ld2 = Ld;
      if (maxdeg<lk)
      {
        if (maxdeg==1 && lk==2 && lg(pl)>1) pl[1] = -1;
        else
        {
          GEN p = extraprime(prV_primes(Lpr));
          Lpr2 = vec_append(Lpr2, idealprimedec_galois(nf, p));
          Ld2 = vecsmall_append(Ld2, lk);
        }
      }

      dbg_printf(2)("alg_hasse: calling nfgrunwaldwang Lpr=%Ps Pd=%Ps pl=%Ps\n",
          Lpr, Ld, pl);
      pol = nfgrunwaldwang(nf, Lpr2, Ld2, pl, var);
      dbg_printf(2)("alg_hasse: calling rnfinit(%Ps)\n", pol);
      rnf = rnfinit0(nf,pol,1);
      dbg_printf(2)("alg_hasse: computing automorphism\n");
      aut = rnfcycaut(rnf);
      dbg_printf(2)("alg_hasse: calling alg_complete\n");
      al2 = alg_complete0(rnf, aut, hfl, hil, flag);
    }
    else al2 = alg_matrix(nf, lk, var, flag);

    if (i==1) al = al2;
    else      al = algtensor(al,al2,flag);
  }
  return gc_GEN(av,al);
}

/** CYCLIC ALGEBRA WITH GIVEN HASSE INVARIANTS **/

/* no garbage collection */
static GEN
subcycloindep(GEN nf, long n, long v, GEN *pr)
{
  pari_sp av;
  forprime_t S;
  ulong p;
  u_forprime_arith_init(&S, 1, ULONG_MAX, 1, n);
  av = avma;
  while ((p = u_forprime_next(&S)))
  {
    ulong r = pgener_Fl(p);
    GEN pol = galoissubcyclo(utoipos(p), utoipos(Fl_powu(r,n,p)), 0, v);
    GEN fa = nffactor(nf, pol);
    if (lgcols(fa) == 2) { *pr = utoipos(r); return pol; }
    set_avma(av);
  }
  pari_err_BUG("subcycloindep (no suitable prime = 1(mod n))"); /*LCOV_EXCL_LINE*/
  *pr = NULL; return NULL; /*LCOV_EXCL_LINE*/
}

GEN
alg_matrix(GEN nf, long n, long v, long flag)
{
  pari_sp av = avma;
  GEN pol, gal, rnf, cyclo, g, r, aut;
  dbg_printf(1)("alg_matrix\n");
  if (n<=0) pari_err_DOMAIN("alg_matrix", "n", "<=", gen_0, stoi(n));
  pol = subcycloindep(nf, n, v, &r);
  rnf = rnfinit(nf, pol);
  cyclo = nfinit(pol, nf_get_prec(nf));
  gal = galoisinit(cyclo, NULL);
  g = genefrob(cyclo,gal,r);
  aut = galoispermtopol(gal,g);
  return gc_upto(av, alg_cyclic(rnf, aut, gen_1, flag));
}

static GEN
alg_hilbert_asquare(GEN nf, GEN a, GEN sa, GEN b, long v, long flag)
{
  GEN mt, al, ord, z1, z2, den, invol;
  long d = nf_get_degree(nf), i;
  mt = mkvec4(
      matid(4),
      mkmat4(
        mkcol4(gen_0,gen_1,gen_0,gen_0),
        mkcol4(a,gen_0,gen_0,gen_0),
        mkcol4(gen_0,gen_0,gen_0,gen_1),
        mkcol4(gen_0,gen_0,a,gen_0)
      ),
      mkmat4(
        mkcol4(gen_0,gen_0,gen_1,gen_0),
        mkcol4(gen_0,gen_0,gen_0,gen_m1),
        mkcol4(b,gen_0,gen_0,gen_0),
        mkcol4(gen_0,gneg(b),gen_0,gen_0)
      ),
      mkmat4(
        mkcol4(gen_0,gen_0,gen_0,gen_1),
        mkcol4(gen_0,gen_0,gneg(a),gen_0),
        mkcol4(gen_0,b,gen_0,gen_0),
        mkcol4(gneg(gmul(a,b)),gen_0,gen_0,gen_0)
      )
  );
  al = alg_csa_table(nf, mt, v, al_NOSPLITTING);

  /* set trivial Hasse invariants */
  gel(al,4) = zero_zv(nf_get_r1(nf));
  gel(al,5) = mkvec2(cgetg(1,t_VEC),cgetg(1,t_VECSMALL));

  /* remember special case */
  sa = basistoalg(nf,sa);
  gmael(al,6,1) = mkvec3(a,b,sa);
  invol = matid(4*d);
  for (i=d+1; i<lg(invol); i++) gcoeff(invol,i,i) = gen_m1;
  gmael(al,6,2) = invol;

  if (flag & al_MAXORD)
  {
    ord = cgetg(4,t_VEC);

    z1 = mkfracss(1,2); /* 1/2 */
    z2 = gmul2n(ginv(sa),-1); /* 1/(2*sa) */
    /* (1+i/sa)/2 */
    gel(ord,1) = algleftmultable(al,mkcol4(z1,z2,gen_0,gen_0));
    /* (j-ij/sa)/2 */
    gel(ord,2) = algleftmultable(al,mkcol4(gen_0,gen_0,z1,gneg(z2)));
    z1 = basistoalg(nf,nfdiv(nf,z1,b));
    z2 = basistoalg(nf,nfdiv(nf,z2,b));
    /* (j/b + ij/(b*sa))/2 */
    gel(ord,3) = algleftmultable(al,mkcol4(gen_0,gen_0,z1,z2));

    /* multiply by nf.zk == d first vectors of natural basis */
    for (i=1; i<=3; i++) gel(ord,i) = vecslice(gel(ord,i),1,d);

    ord = shallowmatconcat(ord);
    ord = Q_remove_denom(ord, &den);
    ord = hnfmodid(ord, den);
    ord = ZM_Z_div(ord, den);
    al = alg_change_overorder_shallow(al, ord);
  }
  /* could take splitting field == nf */
  computesplitting(al, 2, v, flag);
  return al;
}

GEN
alg_hilbert(GEN nf, GEN a, GEN b, long v, long flag)
{
  pari_sp av = avma;
  GEN rnf, aut, rnfpol, sa;
  dbg_printf(1)("alg_hilbert\n");
  if (gequal0(a)) pari_err_DOMAIN("alg_hilbert", "a", "=", gen_0, a);
  if (gequal0(b)) pari_err_DOMAIN("alg_hilbert", "b", "=", gen_0, b);
  if (!isint1(Q_denom(algtobasis(nf,a))))
    pari_err_DOMAIN("alg_hilbert", "denominator(a)", "!=", gen_1,a);
  if (!isint1(Q_denom(algtobasis(nf,b))))
    pari_err_DOMAIN("alg_hilbert", "denominator(b)", "!=", gen_1,b);
  if (nfissquare(nf,a,&sa))
    return gc_GEN(av, alg_hilbert_asquare(nf,a,sa,b,v,flag));

  if (v < 0) v = 0;
  rnfpol = deg2pol_shallow(gen_1, gen_0, gneg(basistoalg(nf,a)), v);
  if (!(flag & al_FACTOR)) rnfpol = mkvec2(rnfpol, stoi(1<<20));
  rnf = rnfinit(nf, rnfpol);
  aut = gneg(pol_x(v));
  return gc_upto(av, alg_cyclic(rnf, aut, b, flag));
}

/* shortcut for alg_hasse in quaternion case */
static GEN
alg_quatramif(GEN nf, GEN Lpr, GEN hi, long var, long flag)
{
  pari_sp av = avma;
  GEN hf = mkvec2(Lpr, const_vecsmall(lg(Lpr)-1,1));
  return gc_upto(av, alg_hasse(nf, 2, hf, hi, var, flag));
}

/* return a structure representing the algebra of real numbers */
static GEN
mk_R()
{
  pari_sp av = avma;
  GEN al;
  al = zerovec(11);
  gel(al,1) = stor(1, LOWDEFAULTPREC);
  gel(al,2) = mkvec(gel(al,1));
  gel(al,3) = gen_1;
  gel(al,4) = mkvecsmall(0);
  gel(al,6) = mkvec2(gen_0,matid(1));
  gel(al,8) = gel(al,7) = matid(1);
  gel(al,9) = mkvec(matid(1));
  return gc_GEN(av,al);
}
/* return a structure representing the algebra of complex numbers */
static GEN
mk_C()
{
  pari_sp av = avma;
  GEN al, I;
  al = zerovec(11);
  I = gen_I();
  gel(al,1) = I;
  gel(al,2) = mkvec(I);
  gel(al,3) = gen_1;
  gel(al,4) = cgetg(1,t_VECSMALL);
  gel(al,6) = mkvec2(gen_0,mkmat22(gen_1,gen_0,gen_0,gen_m1));
  gel(al,8) = gel(al,7) = matid(2);
  gel(al,9) = mkvec2(
    matid(2),
    mkmat22(gen_0,gen_m1,gen_1,gen_0)
  );
  return gc_GEN(av,al);
}
/* return a structure representing the Hamilton quaternion algebra */
static GEN
mk_H()
{
  pari_sp av = avma;
  GEN al, I;
  al = zerovec(11);
  I = gen_I();
  gel(al,1) = I;
  gel(al,2) = mkvec(gconj(I));
  gel(al,3) = gen_m1;
  gel(al,4) = mkvecsmall(1);
  gel(al,6) = mkvec2(gen_0, H_invol(NULL));
  gel(al,8) = gel(al,7) = matid(4);
  gel(al,9) = mkvec4(
    matid(4),
    H_tomatrix(I,1),
    H_tomatrix(mkcol4(gen_0,gen_0,gen_1,gen_0),1),
    H_tomatrix(mkcol4(gen_0,gen_0,gen_0,gen_1),1)
  );
  return gc_GEN(av,al);
}

GEN
alginit(GEN A, GEN B, long v, long flag)
{
  long w;
  if (typ(A) == t_COMPLEX) return mk_C();
  if (typ(A) == t_REAL)
  {
    if (is_scalar_t(typ(B)) && gequal0(B)) return mk_R();
    if (typ(B) == t_FRAC && gequal(B, mkfrac(gen_1,gen_2))) return mk_H();
    pari_err_DOMAIN("alginit", "real Hasse invariant [must be 0 or 1/2]", "", NULL, B);
  }
  switch(nftyp(A))
  {
    case typ_NF:
      if (v<0) v=0;
      w = gvar(nf_get_pol(A));
      if (varncmp(v,w)>=0) pari_err_PRIORITY("alginit", pol_x(v), ">=", w);
      switch(typ(B))
      {
        long nB;
        case t_INT: return alg_matrix(A, itos(B), v, flag);
        case t_VEC:
          nB = lg(B)-1;
          if (nB && typ(gel(B,1)) == t_MAT) return alg_csa_table(A,B,v,flag);
          switch(nB)
          {
            case 2:
              if (typ(gel(B,1)) == t_VEC)
                return alg_quatramif(A, gel(B,1), gel(B,2), v, flag);
              return alg_hilbert(A, gel(B,1), gel(B,2), v, flag);
            case 3:
              if (typ(gel(B,1))!=t_INT)
                  pari_err_TYPE("alginit [degree should be an integer]", gel(B,1));
              return alg_hasse(A, itos(gel(B,1)), gel(B,2), gel(B,3), v,
                                                                      flag);
          }
      }
      pari_err_TYPE("alginit", B); break;

    case typ_RNF:
      if (typ(B) != t_VEC || lg(B) != 3) pari_err_TYPE("alginit", B);
      return alg_cyclic(A, gel(B,1), gel(B,2), flag);
  }
  pari_err_TYPE("alginit", A);
  return NULL;/*LCOV_EXCL_LINE*/
}

/* assumes al CSA or CYCLIC */
static GEN
algnatmultable(GEN al, long D)
{
  GEN res, x;
  long i;
  res = cgetg(D+1,t_VEC);
  for (i=1; i<=D; i++) {
    x = algnattoalg(al,col_ei(D,i));
    gel(res,i) = algZmultable(al,x);
  }
  return res;
}

static int normfact_is_partial(GEN nf, GEN x, GEN fax)
{
  long i;
  GEN nfx;
  nfx = RgM_shallowcopy(fax);
  for (i=1; i<lg(gel(nfx,1)); i++)
    gcoeff(nfx,i,1) = idealnorm(nf, gcoeff(nfx,i,1));
  nfx = factorback(nfx);
  return !gequal(idealnorm(nf, x), nfx);
}
/* no garbage collection */
static void
algcomputehasse(GEN al, long flag)
{
  int partialfact;
  long r1, k, n, m, m1, m2, m3, i, m23, m123;
  GEN rnf, nf, b, fab, disc2, cnd, fad, auts, pr, pl, perm, y, hi, PH, H, L;

  rnf = alg_get_splittingfield(al);
  n = rnf_get_degree(rnf);
  nf = rnf_get_nf(rnf);
  b = alg_get_b(al);
  r1 = nf_get_r1(nf);
  auts = alg_get_auts(al);
  (void)alg_get_abssplitting(al);

  y = nfpolsturm(nf, rnf_get_pol(rnf), NULL);
  pl = cgetg(r1+1, t_VECSMALL);
  /* real places where rnf/nf ramifies */
  for (k = 1; k <= r1; k++) pl[k] = !signe(gel(y,k));

  /* infinite Hasse invariants */
  if (odd(n)) hi = const_vecsmall(r1, 0);
  else
  {
    GEN s = nfsign(nf, b);
    hi = cgetg(r1+1, t_VECSMALL);
    for (k = 1; k<=r1; k++) hi[k] = (s[k] && pl[k]) ? (n/2) : 0;
  }
  gel(al,4) = hi;

  partialfact = 0;
  if (flag & al_FACTOR)
    fab = idealfactor(nf, b);
  else {
    fab = idealfactor_limit(nf, b, 1<<20);
    /* does not report whether factorisation was partial; check it */
    partialfact = normfact_is_partial(nf, b, fab);
  }

  disc2 = rnf_get_idealdisc(rnf);
  L = nfmakecoprime(nf, &disc2, gel(fab,1));
  m = lg(L)-1;
  /* m1 = #{pr|b: pr \nmid disc}, m3 = #{pr|b: pr | disc} */
  perm = cgetg(m+1, t_VECSMALL);
  for (i=1, m1=m, k=1; k<=m; k++)
    if (signe(gel(L,k))) perm[m1--] = k; else perm[i++] = k;
  m3 = m - m1;

  /* disc2 : factor of disc coprime to b */
  if (flag & al_FACTOR)
    fad = idealfactor(nf, disc2);
  else {
    fad = idealfactor_limit(nf, disc2, 1<<20);
    partialfact = partialfact || normfact_is_partial(nf, disc2, fad);
  }

  /* if factorisation is partial, do not compute Hasse invariants */
  /* we could compute their sum at composite factors */
  if (partialfact)
  {
    if (!(flag & al_MAXORD))
    {
      gel(al,5) = gen_0;
      return;
    }
    /* but transmit list of factors found for computation of maximal order */
    PH = prV_primes(shallowconcat(gel(fab,1), gel(fad,1)));
    gel(al,5) = mkvec2(PH, gen_0);;
    return;
  }

  /* m2 : number of prime factors of disc not dividing b */
  m2 = nbrows(fad);
  m23 = m2+m3;
  m123 = m1+m2+m3;

  /* initialize the possibly ramified primes (hasse) and the factored conductor of rnf/nf (cnd) */
  cnd = zeromatcopy(m23,2);
  PH = cgetg(m123+1, t_VEC); /* ramified primes */
  H = cgetg(m123+1, t_VECSMALL); /* Hasse invariant */
  /* compute Hasse invariant at primes that are unramified in rnf/nf */
  for (k=1; k<=m1; k++) {/* pr | b, pr \nmid disc */
    long frob, e, j = perm[k];
    pr = gcoeff(fab,j,1);
    e = itos(gcoeff(fab,j,2));
    frob = cyclicrelfrob(rnf, auts, pr);
    gel(PH,k) = pr;
    H[k] = Fl_mul(frob, e, n);
  }
  /* compute Hasse invariant at primes that are ramified in rnf/nf */
  for (k=1; k<=m2; k++) {/* pr \nmid b, pr | disc */
    pr = gcoeff(fad,k,1);
    gel(PH,k+m1) = pr;
    gcoeff(cnd,k,1) = pr;
    gcoeff(cnd,k,2) = gcoeff(fad,k,2);
  }
  for (k=1; k<=m3; k++) { /* pr | (b, disc) */
    long j = perm[k+m1];
    pr = gcoeff(fab,j,1);
    gel(PH,k+m1+m2) = pr;
    gcoeff(cnd,k+m2,1) = pr;
    gcoeff(cnd,k+m2,2) = gel(L,j);
  }
  gel(cnd,2) = gdiventgs(gel(cnd,2), eulerphiu(n));
  for (k=1; k<=m23; k++) H[k+m1] = localhasse(rnf, cnd, pl, auts, b, k);
  perm = gen_indexsort(PH, (void*)&cmp_prime_ideal, &cmp_nodata);
  gel(al,5) = mkvec2(vecpermute(PH,perm),vecsmallpermute(H,perm));
  checkhasse(nf, alg_get_hasse_f(al), alg_get_hasse_i(al), n);
}

static GEN
alg_maximal_primes(GEN al, GEN P)
{
  pari_sp av = avma;
  long l = lg(P), i;
  for (i=1; i<l; i++)
  {
    if (i != 1) al = gc_GEN(av, al);
    al = alg_pmaximal(al,gel(P,i));
  }
  return al;
}

GEN
alg_cyclic(GEN rnf, GEN aut, GEN b, long flag)
{
  pari_sp av = avma;
  GEN al, nf;
  long D, n, d;
  dbg_printf(1)("alg_cyclic\n");
  checkrnf(rnf); nf = rnf_get_nf(rnf);
  b = nf_to_scalar_or_basis(nf, b);
  if (typ(b) == t_FRAC || (typ(b) == t_COL && !RgV_is_ZV(b)))
    pari_err_DOMAIN("alg_cyclic", "denominator(b)", "!=", gen_1,b);

  n = rnf_get_degree(rnf);
  d = nf_get_degree(nf);
  D = d*n*n;

  al = cgetg(12,t_VEC);
  gel(al,10)= gen_0; /* must be set first */
  gel(al,1) = rnf;
  gel(al,2) = allauts(rnf, aut);
  gel(al,3) = basistoalg(nf,b);
  rnf_build_nfabs(rnf, nf_get_prec(nf));
  gel(al,6) = mkvec2(gen_0,gen_0);
  gel(al,7) = matid(D);
  gel(al,8) = matid(D); /* TODO modify 7, 8 et 9 once LLL added */
  gel(al,9) = algnatmultable(al,D);
  gel(al,11)= algtracebasis(al);

  if (n==2) alg_insert_quatconj(al);

  algcomputehasse(al, flag);

  if (flag & al_MAXORD) {
    GEN hf = alg_get_hasse_f(al), pr = gel(hf,1);
    if (typ(gel(hf,2)) == t_INT) /* factorisation was partial */
      gel(al,5) = gen_0;
    else pr = prV_primes(pr);
    al = alg_maximal_primes(al, pr);
  }
  return gc_GEN(av, al);
}

static int
ismaximalsubfield(GEN al, GEN x, GEN d, long v, GEN *pt_minpol)
{
  GEN cp = algbasischarpoly(al, x, v), lead;
  if (!ispower(cp, d, pt_minpol)) return 0;
  lead = leading_coeff(*pt_minpol);
  if (isintm1(lead)) *pt_minpol = gneg(*pt_minpol);
  return ZX_is_irred(*pt_minpol);
}

static GEN
findmaximalsubfield(GEN al, GEN d, long v)
{
  long count, nb=2, i, N = alg_get_absdim(al), n = nf_get_degree(alg_get_center(al));
  GEN x, minpol, maxc = gen_1;

  for (i=n+1; i<=N; i+=n) {
    for (count=0; count<2 && i+count<=N; count++) {
      x = col_ei(N,i+count);
      if (ismaximalsubfield(al, x, d, v, &minpol)) return mkvec2(x,minpol);
    }
  }

  while(1) {
    x = zerocol(N);
    for (count=0; count<nb; count++)
    {
      i = random_Fl(N)+1;
      gel(x,i) = addiu(randomi(maxc),1);
      if (random_bits(1)) gel(x,i) = negi(gel(x,i));
    }
    if (ismaximalsubfield(al, x, d, v, &minpol)) return mkvec2(x,minpol);
    if (!random_bits(3)) maxc = addiu(maxc,1);
    if (nb<N) nb++;
  }

  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
frobeniusform(GEN al, GEN x)
{
  GEN M, FP, P, Pi;

  /* /!\ has to be the *right* multiplication table */
  M = algbasisrightmultable(al, x);

  FP = matfrobenius(M,2,0); /* M = P^(-1)*F*P */
  P = gel(FP,2);
  Pi = RgM_inv(P);
  return mkvec2(P, Pi);
}

static void
computesplitting(GEN al, long d, long v, long flag)
{
  GEN subf, x, pol, polabs, basis, P, Pi, nf = alg_get_center(al), rnf, Lbasis, Lbasisinv, Q, pows;
  long i, n = nf_get_degree(nf), nd = n*d, N = alg_get_absdim(al), j, j2;

  subf = findmaximalsubfield(al, utoipos(d), v);
  x = gel(subf, 1);
  polabs = gel(subf, 2);

  /* Frobenius form to obtain L-vector space structure */
  basis = frobeniusform(al, x);
  P = gel(basis, 1);
  Pi = gel(basis, 2);

  /* construct rnf of splitting field */
  pol = gel(nffactor(nf,polabs),1);
  for (i=1; i<lg(pol); i++)
    /* select relative factor that vanishes on x */
    if (gequal0(algpoleval(al, gel(pol,i), x)))
    {
      pol = gel(pol,i);
      break;
    }
  if (typ(pol) != t_POL) pari_err_BUG("computesplitting (no valid factor)");
  if (!(flag & al_FACTOR)) pol = mkvec2(pol, stoi(1<<20));
  gel(al,1) = rnf = rnfinit(nf, pol);
  /* since pol is irreducible over Q, we have k=0 in rnf. */
  if (!gequal0(rnf_get_k(rnf)))
    pari_err_BUG("computesplitting (k!=0)"); /*LCOV_EXCL_LINE*/
  rnf_build_nfabs(rnf, nf_get_prec(nf));

  /* construct splitting data */
  Lbasis = cgetg(d+1, t_MAT);
  for (j=j2=1; j<=d; j++, j2+=nd)
    gel(Lbasis,j) = gel(Pi,j2);

  Q = zeromatcopy(d,N);
  pows = pol_x_powers(nd,v);
  for (i=j=1; j<=N; j+=nd, i++)
  for (j2=0; j2<nd; j2++)
    gcoeff(Q,i,j+j2) = mkpolmod(gel(pows,j2+1),polabs);
  Lbasisinv = RgM_mul(Q,P);

  gel(al,3) = mkvec3(x,Lbasis,Lbasisinv);
}

/* assumes that mt defines a central simple algebra over nf */
GEN
alg_csa_table(GEN nf, GEN mt0, long v, long flag)
{
  pari_sp av = avma;
  GEN al, mt;
  long n, D, d2 = lg(mt0)-1, d = usqrt(d2);
  dbg_printf(1)("alg_csa_table\n");

  mt = check_relmt(nf,mt0);
  if (!mt) pari_err_TYPE("alg_csa_table", mt0);
  n = nf_get_degree(nf);
  D = n*d2;
  if (d*d != d2)
    pari_err_DOMAIN("alg_csa_table","(nonsquare) dimension","!=",stoi(d*d),mt);

  al = cgetg(12, t_VEC);
  gel(al,10) = gen_0; /* must be set first */
  gel(al,1) = zerovec(12); gmael(al,1,10) = nf;
  gmael(al,1,1) = gpowgs(pol_x(0), d); /* placeholder before splitting field */
  gel(al,2) = mt;
  gel(al,3) = gen_0; /* placeholder */
  gel(al,4) = gel(al,5) = gen_0; /* TODO Hasse invariants if flag&al_FACTOR */
  gel(al,6) = mkvec2(gen_0,gen_0);
  gel(al,7) = matid(D);
  gel(al,8) = matid(D);
  gel(al,9) = algnatmultable(al,D);
  gel(al,11)= algtracebasis(al);
  if (flag & al_MAXORD) al = alg_maximal(al);
  if (!(flag & al_NOSPLITTING)) computesplitting(al, d, v, flag);
  return gc_GEN(av, al);
}

static GEN
algtableinit_i(GEN mt0, GEN p)
{
  GEN al, mt;
  long i, n;

  if (p && !signe(p)) p = NULL;
  mt = check_mt(mt0,p);
  if (!mt) pari_err_TYPE("algtableinit", mt0);
  if (!p && !isint1(Q_denom(mt0)))
    pari_err_DOMAIN("algtableinit", "denominator(mt)", "!=", gen_1, mt0);
  n = lg(mt)-1;
  al = cgetg(12, t_VEC);
  for (i=1; i<=5; i++) gel(al,i) = gen_0;
  gel(al,6) = mkvec2(gen_0, gen_0);
  gel(al,7) = matid(n);
  gel(al,8) = matid(n);
  gel(al,9) = mt;
  gel(al,10) = p? p: gen_0;
  gel(al,11) = algtracebasis(al);
  return al;
}
GEN
algtableinit(GEN mt0, GEN p)
{
  pari_sp av = avma;
  if (p)
  {
    if (typ(p) != t_INT) pari_err_TYPE("algtableinit",p);
    if (signe(p) && !BPSW_psp(p)) pari_err_PRIME("algtableinit",p);
  }
  return gc_GEN(av, algtableinit_i(mt0, p));
}

/** REPRESENTATIONS OF GROUPS **/

static GEN
list_to_regular_rep(GEN elts, long n)
{
  GEN reg, elts2, g;
  long i,j;
  elts = shallowcopy(elts);
  gen_sort_inplace(elts, (void*)&vecsmall_lexcmp, &cmp_nodata, NULL);
  reg = cgetg(n+1, t_VEC);
  gel(reg,1) = identity_perm(n);
  for (i=2; i<=n; i++) {
    g = perm_inv(gel(elts,i));
    elts2 = cgetg(n+1, t_VEC);
    for (j=1; j<=n; j++) gel(elts2,j) = perm_mul(g,gel(elts,j));
    gen_sort_inplace(elts2, (void*)&vecsmall_lexcmp, &cmp_nodata, &gel(reg,i));
  }
  return reg;
}

static GEN
matrix_perm(GEN perm, long n)
{
  GEN m;
  long j;
  m = cgetg(n+1, t_MAT);
  for (j=1; j<=n; j++) {
    gel(m,j) = col_ei(n,perm[j]);
  }
  return m;
}

GEN
conjclasses_algcenter(GEN cc, GEN p)
{
  GEN mt, elts = gel(cc,1), conjclass = gel(cc,2), rep = gel(cc,3), card;
  long i, nbcl = lg(rep)-1, n = lg(elts)-1;
  pari_sp av;

  card = zero_Flv(nbcl);
  for (i=1; i<=n; i++) card[conjclass[i]]++;

  /* multiplication table of the center of Z[G] (class functions) */
  mt = cgetg(nbcl+1,t_VEC);
  for (i=1;i<=nbcl;i++) gel(mt,i) = zero_Flm_copy(nbcl,nbcl);
  av = avma;
  for (i=1;i<=nbcl;i++)
  {
    GEN xi = gel(elts,rep[i]), mi = gel(mt,i);
    long j,k;
    for (j=1;j<=n;j++)
    {
      GEN xj = gel(elts,j);
      k = vecsearch(elts, perm_mul(xi,xj), NULL);
      ucoeff(mi, conjclass[k], conjclass[j])++;
    }
    for (k=1; k<=nbcl; k++)
      for (j=1; j<=nbcl; j++)
      {
        ucoeff(mi,k,j) *= card[i];
        ucoeff(mi,k,j) /= card[k];
      }
    set_avma(av);
  }
  for (i=1;i<=nbcl;i++) gel(mt,i) = Flm_to_ZM(gel(mt,i));
  return algtableinit_i(mt,p);
}

GEN
alggroupcenter(GEN G, GEN p, GEN *pcc)
{
  pari_sp av = avma;
  GEN cc = group_to_cc(G), al = conjclasses_algcenter(cc, p);
  if (!pcc) return gc_GEN(av,al);
  *pcc = cc; return gc_all(av, 2, &al, pcc);
}

static GEN
groupelts_algebra(GEN elts, GEN p)
{
  pari_sp av = avma;
  GEN mt;
  long i, n = lg(elts)-1;
  elts = list_to_regular_rep(elts,n);
  mt = cgetg(n+1, t_VEC);
  for (i=1; i<=n; i++) gel(mt,i) = matrix_perm(gel(elts,i),n);
  return gc_GEN(av, algtableinit_i(mt,p));
}

GEN
alggroup(GEN gal, GEN p)
{
  GEN elts = checkgroupelts(gal);
  return groupelts_algebra(elts, p);
}

/** MAXIMAL ORDER **/

static GEN
mattocol(GEN M, long n)
{
  GEN C = cgetg(n*n+1, t_COL);
  long i,j,ic;
  ic = 1;
  for (i=1; i<=n; i++)
  for (j=1; j<=n; j++, ic++) gel(C,ic) = gcoeff(M,i,j);
  return C;
}

/* Ip is a lift of a left O/pO-ideal where O is the integral basis of al */
static GEN
algleftordermodp(GEN al, GEN Ip, GEN p)
{
  pari_sp av = avma;
  GEN I, Ii, M, mt, K, imi, p2;
  long n, i;
  n = alg_get_absdim(al);
  mt = alg_get_multable(al);
  p2 = sqri(p);

  I = ZM_hnfmodid(Ip, p);
  Ii = ZM_inv(I,NULL);

  M = cgetg(n+1, t_MAT);
  for (i=1; i<=n; i++) {
    imi = FpM_mul(Ii, FpM_mul(gel(mt,i), I, p2), p2);
    imi = ZM_Z_divexact(imi, p);
    gel(M,i) = mattocol(imi, n);
  }
  K = FpM_ker(M, p);
  if (lg(K)==1) { set_avma(av); return matid(n); }
  K = ZM_hnfmodid(K,p);

  return gc_upto(av, ZM_Z_div(K,p));
}

static GEN
alg_ordermodp(GEN al, GEN p)
{
  GEN alp;
  long i, N = alg_get_absdim(al);
  alp = cgetg(12, t_VEC);
  for (i=1; i<=8; i++) gel(alp,i) = gen_0;
  gel(alp,9) = cgetg(N+1, t_VEC);
  for (i=1; i<=N; i++) gmael(alp,9,i) = FpM_red(gmael(al,9,i), p);
  gel(alp,10) = p;
  gel(alp,11) = cgetg(N+1, t_VEC);
  for (i=1; i<=N; i++) gmael(alp,11,i) = Fp_red(gmael(al,11,i), p);

  return alp;
}

static GEN
algpradical_i(GEN al, GEN p, GEN zprad, GEN projs)
{
  pari_sp av = avma;
  GEN alp = alg_ordermodp(al, p), liftrad, projrad, alq, alrad, res, Lalp, radq;
  long i;
  if (lg(zprad)==1) {
    liftrad = NULL;
    projrad = NULL;
  }
  else {
    alq = alg_quotient(alp, zprad, 1);
    alp = gel(alq,1);
    projrad = gel(alq,2);
    liftrad = gel(alq,3);
  }

  if (projs) {
    if (projrad) {
      projs = gcopy(projs);
      for (i=1; i<lg(projs); i++)
        gel(projs,i) = FpM_FpC_mul(projrad, gel(projs,i), p);
    }
    Lalp = alg_centralproj(alp, projs, 1);

    alrad = cgetg(lg(Lalp),t_VEC);
    for (i=1; i<lg(Lalp); i++) {
      alq = gel(Lalp,i);
      radq = algradical(gel(alq,1));
      if (gequal0(radq))
        gel(alrad,i) = cgetg(1,t_MAT);
      else {
        radq = FpM_mul(gel(alq,3),radq,p);
        gel(alrad,i) = radq;
      }
    }
    alrad = shallowmatconcat(alrad);
    alrad = FpM_image(alrad,p);
  }
  else alrad = algradical(alp);

  if (!gequal0(alrad)) {
    if (liftrad) alrad = FpM_mul(liftrad, alrad, p);
    res = shallowmatconcat(mkvec2(alrad, zprad));
    res = FpM_image(res,p);
  }
  else res = lg(zprad)==1 ? gen_0 : zprad;
  return gc_GEN(av, res);
}

static GEN
algpdecompose0(GEN al, GEN prad, GEN p, GEN projs)
{
  pari_sp av = avma;
  GEN alp, quo, ss, liftm = NULL, projm = NULL, dec, res, I, Lss, deci;
  long i, j;

  alp = alg_ordermodp(al, p);
  if (!gequal0(prad)) {
    quo = alg_quotient(alp, prad, 1);
    ss = gel(quo,1);
    projm = gel(quo,2);
    liftm = gel(quo,3);
  }
  else ss = alp;

  if (projs) {
    if (projm) {
      for (i=1; i<lg(projs); i++)
        gel(projs,i) = FpM_FpC_mul(projm, gel(projs,i), p);
    }
    Lss = alg_centralproj(ss, projs, 1);

    dec = cgetg(lg(Lss),t_VEC);
    for (i=1; i<lg(Lss); i++) {
      gel(dec,i) = algsimpledec_ss(gmael(Lss,i,1), 1);
      deci = gel(dec,i);
      for (j=1; j<lg(deci); j++)
       gmael(deci,j,3) = FpM_mul(gmael(Lss,i,3), gmael(deci,j,3), p);
    }
    dec = shallowconcat1(dec);
  }
  else dec = algsimpledec_ss(ss,1);

  res = cgetg(lg(dec),t_VEC);
  for (i=1; i<lg(dec); i++) {
    I = gmael(dec,i,3);
    if (liftm) I = FpM_mul(liftm,I,p);
    I = shallowmatconcat(mkvec2(I,prad));
    gel(res,i) = I;
  }

  return gc_GEN(av, res);
}

/* finds a nontrivial ideal of O/prad or gen_0 if there is none. */
static GEN
algpdecompose_i(GEN al, GEN p, GEN zprad, GEN projs)
{
  pari_sp av = avma;
  GEN prad = algpradical_i(al,p,zprad,projs);
  return gc_upto(av, algpdecompose0(al, prad, p, projs));
}

/* ord is assumed to be in hnf wrt the integral basis of al. */
/* assumes that alg_get_invbasis(al) is integral. */
static GEN
alg_change_overorder_shallow(GEN al, GEN ord)
{
  GEN al2, mt, iord, mtx, den, den2, div, invol;
  long i, n;
  n = alg_get_absdim(al);

  iord = QM_inv(ord);
  al2 = shallowcopy(al);

  invol = alg_get_invol(al);
  if (typ(invol) == t_MAT) gmael(al2,6,2) = QM_mul(iord, QM_mul(invol,ord));

  ord = Q_remove_denom(ord,&den);

  gel(al2,7) = Q_remove_denom(gel(al,7), &den2);
  if (den2) div = mulii(den,den2);
  else      div = den;
  gel(al2,7) = ZM_Z_div(ZM_mul(gel(al2,7), ord), div);

  gel(al2,8) = ZM_mul(iord, gel(al,8));

  mt = cgetg(n+1,t_VEC);
  gel(mt,1) = matid(n);
  div = sqri(den);
  for (i=2; i<=n; i++) {
    mtx = algbasismultable(al,gel(ord,i));
    gel(mt,i) = ZM_mul(iord, ZM_mul(mtx, ord));
    gel(mt,i) = ZM_Z_divexact(gel(mt,i), div);
  }
  gel(al2,9) = mt;

  gel(al2,11) = algtracebasis(al2);

  return al2;
}

static GEN
algeltfromnf_i(GEN al, GEN x)
{
  GEN nf = alg_get_center(al);
  long n;
  switch(alg_type(al)) {
    case al_CYCLIC:
      n = alg_get_degree(al);
      break;
    case al_CSA:
      n = alg_get_dim(al);
      break;
    default: return NULL; /*LCOV_EXCL_LINE*/
  }
  return algalgtobasis(al, scalarcol(basistoalg(nf, x), n));
}

GEN
algeltfromnf(GEN al, GEN x)
{
  pari_sp av = avma;
  checkalg(al);
  return gc_upto(av, algeltfromnf_i(al,x));
}

/* x is an ideal of the center in hnf form */
static GEN
algeltfromnf_hnf(GEN al, GEN x)
{
  GEN res;
  long i;
  res = cgetg(lg(x), t_MAT);
  for (i=1; i<lg(x); i++) gel(res,i) = algeltfromnf_i(al, gel(x,i));
  return res;
}

/* assumes al is CSA or CYCLIC */
static GEN
algcenter_precompute(GEN al, GEN p)
{
  GEN fa, pdec, nfprad, projs, nf = alg_get_center(al);
  long i, np;

  pdec = idealprimedec(nf, p);
  settyp(pdec, t_COL);
  np = lg(pdec)-1;
  fa = mkmat2(pdec, const_col(np, gen_1));
  if (dvdii(nf_get_disc(nf), p))
    nfprad = idealprodprime(nf, pdec);
  else
    nfprad = scalarmat_shallow(p, nf_get_degree(nf));
  fa = idealchineseinit(nf, fa);
  projs = cgetg(np+1, t_VEC);
  for (i=1; i<=np; i++) gel(projs, i) = idealchinese(nf, fa, vec_ei(np,i));
  return mkvec2(nfprad, projs);
}

static GEN
algcenter_prad(GEN al, GEN p, GEN pre)
{
  GEN nfprad, zprad, mtprad;
  long i;
  nfprad = gel(pre,1);
  zprad = algeltfromnf_hnf(al, nfprad);
  zprad = FpM_image(zprad, p);
  mtprad = cgetg(lg(zprad), t_VEC);
  for (i=1; i<lg(zprad); i++) gel(mtprad, i) = algbasismultable(al, gel(zprad,i));
  mtprad = shallowmatconcat(mtprad);
  zprad = FpM_image(mtprad, p);
  return zprad;
}

static GEN
algcenter_p_projs(GEN al, GEN p, GEN pre)
{
  GEN projs, zprojs;
  long i;
  projs = gel(pre,2);
  zprojs = cgetg(lg(projs), t_VEC);
  for (i=1; i<lg(projs); i++) gel(zprojs,i) = FpC_red(algeltfromnf_i(al, gel(projs,i)),p);
  return zprojs;
}

/* al is assumed to be simple */
static GEN
alg_pmaximal(GEN al, GEN p)
{
  pari_sp av;
  long n = alg_get_absdim(al);
  GEN id = matid(n), al2 = al, prad, lord = gen_0, dec, zprad, projs, pre;

  dbg_printf(0)("Round 2 (noncommutative) at p=%Ps, dim=%d\n", p, n);
  pre = algcenter_precompute(al,p); av = avma;
  while (1) {
    zprad = algcenter_prad(al2, p, pre);
    projs = algcenter_p_projs(al2, p, pre);
    if (lg(projs) == 2) projs = NULL;
    prad = algpradical_i(al2,p,zprad,projs);
    if (typ(prad) == t_INT) break;
    lord = algleftordermodp(al2,prad,p);
    if (!cmp_universal(lord,id)) break;
    al2 = gc_GEN(av, alg_change_overorder_shallow(al2,lord));
  }

  dec = algpdecompose0(al2,prad,p,projs); av = avma;
  while (lg(dec) > 2) {
    long i;
    for (i = 1; i < lg(dec); i++) {
      GEN I = gel(dec,i);
      lord = algleftordermodp(al2,I,p);
      if (cmp_universal(lord,id)) break;
    }
    if (i==lg(dec)) break;
    al2 = gc_GEN(av, alg_change_overorder_shallow(al2,lord));
    zprad = algcenter_prad(al2, p, pre);
    projs = algcenter_p_projs(al2, p, pre);
    if (lg(projs) == 2) projs = NULL;
    dec = algpdecompose_i(al2,p,zprad,projs);
  }
  return al2;
}

static GEN
algtracematrix(GEN al)
{
  GEN M, mt;
  long n, i, j;
  n = alg_get_absdim(al);
  mt = alg_get_multable(al);
  M = cgetg(n+1, t_MAT);
  for (i=1; i<=n; i++)
  {
    gel(M,i) = cgetg(n+1,t_MAT);
    for (j=1; j<=i; j++)
      gcoeff(M,j,i) = gcoeff(M,i,j) = algabstrace(al,gmael(mt,i,j));
  }
  return M;
}
static GEN
algdisc_i(GEN al) { return ZM_det(algtracematrix(al)); }
GEN
algdisc(GEN al)
{
  pari_sp av = avma;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("algdisc [real algebra]", al);
  return gc_INT(av, algdisc_i(al));
}
static GEN
alg_maximal(GEN al)
{
  GEN fa = absZ_factor(algdisc_i(al));
  return alg_maximal_primes(al, gel(fa,1));
}

/** LATTICES **/

/*
 Convention: lattice = [I,t] representing t*I, where
 - I integral nonsingular upper-triangular matrix representing a lattice over
   the integral basis of the algebra, and
 - t>0 either an integer or a rational number.

 Recommended and returned by the functions below:
 - I HNF and primitive
*/

/* TODO use hnfmodid whenever possible using a*O <= I <= O
 * for instance a = ZM_det_triangular(I) */

static GEN
primlat(GEN lat)
{
  GEN m, t, c;
  m = alglat_get_primbasis(lat);
  t = alglat_get_scalar(lat);
  m = Q_primitive_part(m,&c);
  if (c) return mkvec2(m,gmul(t,c));
  return lat;
}

/* assumes the lattice contains d * integral basis, d=0 allowed */
GEN
alglathnf(GEN al, GEN m, GEN d)
{
  pari_sp av = avma;
  long N,i,j;
  GEN m2, c;
  if (!d) d = gen_0;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("alglathnf [real algebra]", al);
  N = alg_get_absdim(al);
  if (!d) d = gen_0;
  if (typ(m) == t_VEC) m = matconcat(m);
  if (typ(m) == t_COL) m = algleftmultable(al,m);
  if (typ(m) != t_MAT) pari_err_TYPE("alglathnf",m);
  if (typ(d) != t_FRAC && typ(d) != t_INT) pari_err_TYPE("alglathnf",d);
  if (lg(m)-1 < N || lg(gel(m,1))-1 != N) pari_err_DIM("alglathnf");
  for (i=1; i<=N; i++)
    for (j=1; j<lg(m); j++)
      if (typ(gcoeff(m,i,j)) != t_FRAC && typ(gcoeff(m,i,j)) != t_INT)
        pari_err_TYPE("alglathnf", gcoeff(m,i,j));
  m2 = Q_primitive_part(m,&c);
  if (!c) c = gen_1;
  if (!signe(d)) d = detint(m2);
  else           d = gdiv(d,c); /* should be an integer */
  if (!signe(d)) pari_err_INV("alglathnf [m does not have full rank]", m2);
  m2 = ZM_hnfmodid(m2,d);
  return gc_GEN(av, mkvec2(m2,c));
}

static GEN
prepare_multipliers(GEN *a, GEN *b)
{
  GEN na, nb, da, db, d;
  na = numer_i(*a); da = denom_i(*a);
  nb = numer_i(*b); db = denom_i(*b);
  na = mulii(na,db);
  nb = mulii(nb,da);
  d = gcdii(na,nb);
  *a = diviiexact(na,d);
  *b = diviiexact(nb,d);
  return gdiv(d, mulii(da,db));
}

static GEN
prepare_lat(GEN m1, GEN t1, GEN m2, GEN t2)
{
  GEN d = prepare_multipliers(&t1, &t2);
  m1 = ZM_Z_mul(m1,t1);
  m2 = ZM_Z_mul(m2,t2);
  return mkvec3(m1,m2,d);
}

static GEN
alglataddinter(GEN al, GEN lat1, GEN lat2, GEN *sum, GEN *inter)
{
  GEN d, m1, m2, t1, t2, M, prep, d1, d2, ds, di, K;
  checkalg(al);
  if (alg_type(al) == al_REAL)
    pari_err_TYPE("alglataddinter [real algebra]", al);
  checklat(al,lat1);
  checklat(al,lat2);

  m1 = alglat_get_primbasis(lat1);
  t1 = alglat_get_scalar(lat1);
  m2 = alglat_get_primbasis(lat2);
  t2 = alglat_get_scalar(lat2);
  prep = prepare_lat(m1, t1, m2, t2);
  m1 = gel(prep,1);
  m2 = gel(prep,2);
  d = gel(prep,3);
  M = matconcat(mkvec2(m1,m2));
  d1 = ZM_det_triangular(m1);
  d2 = ZM_det_triangular(m2);
  ds = gcdii(d1,d2);
  if (inter)
  {
    di = diviiexact(mulii(d1,d2),ds);
    if (equali1(di))
    {
      *inter = matid(lg(m1)-1);
      if (sum) *sum = matid(lg(m1)-1);
    }
    else
    {
      K = matkermod(M,di,sum);
      K = rowslice(K,1,lg(m1));
      *inter = hnfmodid(FpM_mul(m1,K,di),di);
      if (sum) *sum = hnfmodid(*sum,ds);
    }
  }
  else *sum = hnfmodid(M,ds);
  return d;
}

GEN
alglatinter(GEN al, GEN lat1, GEN lat2, GEN* psum)
{
  pari_sp av = avma;
  GEN inter, d;
  d = alglataddinter(al, lat1, lat2, psum, &inter);
  inter = primlat(mkvec2(inter, d));
  if (!psum) return gc_GEN(av, inter);
  *psum = primlat(mkvec2(*psum,d));
  return gc_all(av, 2, &inter, psum);
}

GEN
alglatadd(GEN al, GEN lat1, GEN lat2, GEN* pinter)
{
  pari_sp av = avma;
  GEN sum, d;
  d = alglataddinter(al, lat1, lat2, &sum, pinter);
  sum = primlat(mkvec2(sum, d));
  if (!pinter) return gc_GEN(av, sum);
  *pinter = primlat(mkvec2(*pinter,d));
  return gc_all(av, 2, &sum, pinter);
}

/* TODO version that returns the quotient as abelian group? */
/* return matrices to convert coordinates from one to other? */
int
alglatsubset(GEN al, GEN lat1, GEN lat2, GEN* pindex)
{
  pari_sp av = avma;
  int res;
  GEN m1, m2, m2i, m, t;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("alglatsubset [real algebra]", al);
  checklat(al,lat1);
  checklat(al,lat2);
  m1 = alglat_get_primbasis(lat1);
  m2 = alglat_get_primbasis(lat2);
  m2i = RgM_inv_upper(m2);
  t = gdiv(alglat_get_scalar(lat1), alglat_get_scalar(lat2));
  m = RgM_Rg_mul(RgM_mul(m2i,m1), t);
  res = RgM_is_ZM(m);
  if (!res || !pindex) return gc_int(av, res);
  *pindex = gc_INT(av, mpabs(ZM_det_triangular(m)));
  return 1;
}

GEN
alglatindex(GEN al, GEN lat1, GEN lat2)
{
  pari_sp av = avma;
  long N;
  GEN res;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("alglatindex [real algebra]", al);
  checklat(al,lat1);
  checklat(al,lat2);
  N = alg_get_absdim(al);
  res = alglat_get_scalar(lat1);
  res = gdiv(res, alglat_get_scalar(lat2));
  res = gpowgs(res, N);
  res = gmul(res,RgM_det_triangular(alglat_get_primbasis(lat1)));
  res = gdiv(res, RgM_det_triangular(alglat_get_primbasis(lat2)));
  res = gabs(res,0);
  return gc_GEN(av, res);
}

GEN
alglatmul(GEN al, GEN lat1, GEN lat2)
{
  pari_sp av = avma;
  long N,i;
  GEN m1, m2, m, V, lat, t, d, dp;
  checkalg(al);
  if (alg_type(al) == al_REAL) pari_err_TYPE("alglatmul [real algebra]", al);
  if (typ(lat1)==t_COL)
  {
    if (typ(lat2)==t_COL)
      pari_err_TYPE("alglatmul [one of lat1, lat2 has to be a lattice]", lat2);
    checklat(al,lat2);
    lat1 = Q_remove_denom(lat1,&d);
    m = algbasismultable(al,lat1);
    m2 = alglat_get_primbasis(lat2);
    dp = mulii(detint(m),ZM_det_triangular(m2));
    m = ZM_mul(m,m2);
    t = alglat_get_scalar(lat2);
    if (d) t = gdiv(t,d);
  }
  else /* typ(lat1)!=t_COL */
  {
    checklat(al,lat1);
    if (typ(lat2)==t_COL)
    {
      lat2 = Q_remove_denom(lat2,&d);
      m = algbasisrightmultable(al,lat2);
      m1 = alglat_get_primbasis(lat1);
      dp = mulii(detint(m),ZM_det_triangular(m1));
      m = ZM_mul(m,m1);
      t = alglat_get_scalar(lat1);
      if (d) t = gdiv(t,d);
    }
    else /* typ(lat2)!=t_COL */
    {
      checklat(al,lat2);
      N = alg_get_absdim(al);
      m1 = alglat_get_primbasis(lat1);
      m2 = alglat_get_primbasis(lat2);
      dp = mulii(ZM_det_triangular(m1), ZM_det_triangular(m2));
      V = cgetg(N+1,t_VEC);
      for (i=1; i<=N; i++) {
        gel(V,i) = algbasismultable(al,gel(m1,i));
        gel(V,i) = ZM_mul(gel(V,i),m2);
      }
      m = matconcat(V);
      t = gmul(alglat_get_scalar(lat1), alglat_get_scalar(lat2));
    }
  }

  lat = alglathnf(al,m,dp);
  gel(lat,2) = gmul(alglat_get_scalar(lat), t);
  lat = primlat(lat);
  return gc_GEN(av, lat);
}

int
alglatcontains(GEN al, GEN lat, GEN x, GEN *ptc)
{
  pari_sp av = avma;
  GEN m, t, sol;
  checkalg(al);
  if (alg_type(al) == al_REAL)
    pari_err_TYPE("alglatcontains [real algebra]", al);
  checklat(al,lat);
  m = alglat_get_primbasis(lat);
  t = alglat_get_scalar(lat);
  x = RgC_Rg_div(x,t);
  if (!RgV_is_ZV(x)) return gc_bool(av,0);
  sol = hnf_solve(m,x);
  if (!sol) return gc_bool(av,0);
  if (!ptc) return gc_bool(av,1);
  *ptc = gc_GEN(av, sol); return 1;
}

GEN
alglatelement(GEN al, GEN lat, GEN c)
{
  pari_sp av = avma;
  GEN res;
  checkalg(al);
  if (alg_type(al) == al_REAL)
    pari_err_TYPE("alglatelement [real algebra]", al);
  checklat(al,lat);
  if (typ(c)!=t_COL) pari_err_TYPE("alglatelement", c);
  res = ZM_ZC_mul(alglat_get_primbasis(lat),c);
  res = RgC_Rg_mul(res, alglat_get_scalar(lat));
  return gc_GEN(av,res);
}

/* idem QM_invimZ, knowing result is contained in 1/c*Z^n */
static GEN
QM_invimZ_mod(GEN m, GEN c)
{
  GEN d, m0, K;
  m0 = Q_remove_denom(m, &d);
  if (d)    d = mulii(d,c);
  else      d = c;
  K = matkermod(m0, d, NULL);
  if (lg(K)==1) K = scalarmat(d, lg(m)-1);
  else          K = hnfmodid(K, d);
  return RgM_Rg_div(K,c);
}

/* If m is injective, computes a Z-basis of the submodule of elements whose
 * image under m is integral */
static GEN
QM_invimZ(GEN m)
{
  return RgM_invimage(m, QM_ImQ_hnf(m));
}

/* An isomorphism of R-modules M_{m,n}(R) -> R^{m*n} */
static GEN
mat2col(GEN M, long m, long n)
{
  long i,j,k,p;
  GEN C;
  p = m*n;
  C = cgetg(p+1,t_COL);
  for (i=1,k=1;i<=m;i++)
    for (j=1;j<=n;j++,k++)
      gel(C,k) = gcoeff(M,i,j);
  return C;
}

static GEN
alglattransporter_i(GEN al, GEN lat1, GEN lat2, long right)
{
  GEN m1, m2, m2i, M, MT, mt, t1, t2, T, c;
  long N, i;
  N = alg_get_absdim(al);
  m1 = alglat_get_primbasis(lat1);
  m2 = alglat_get_primbasis(lat2);
  m2i = RgM_inv_upper(m2);
  c = detint(m1);
  t1 = alglat_get_scalar(lat1);
  m1 = RgM_Rg_mul(m1,t1);
  t2 = alglat_get_scalar(lat2);
  m2i = RgM_Rg_div(m2i,t2);

  MT = right? NULL: alg_get_multable(al);
  M = cgetg(N+1, t_MAT);
  for (i=1; i<=N; i++) {
    if (right) mt = algbasisrightmultable(al, vec_ei(N,i));
    else       mt = gel(MT,i);
    mt = RgM_mul(m2i,mt);
    mt = RgM_mul(mt,m1);
    gel(M,i) = mat2col(mt, N, N);
  }

  c = gdiv(t2,gmul(c,t1));
  c = denom_i(c);
  T = QM_invimZ_mod(M,c);
  return primlat(mkvec2(T,gen_1));
}

/*
   { x in al | x*lat1 subset lat2}
*/
GEN
alglatlefttransporter(GEN al, GEN lat1, GEN lat2)
{
  pari_sp av = avma;
  checkalg(al);
  if (alg_type(al) == al_REAL)
    pari_err_TYPE("alglatlefttransporter [real algebra]", al);
  checklat(al,lat1);
  checklat(al,lat2);
  return gc_GEN(av, alglattransporter_i(al,lat1,lat2,0));
}

/*
   { x in al | lat1*x subset lat2}
*/
GEN
alglatrighttransporter(GEN al, GEN lat1, GEN lat2)
{
  pari_sp av = avma;
  checkalg(al);
  if (alg_type(al) == al_REAL)
    pari_err_TYPE("alglatrighttransporter [real algebra]", al);
  checklat(al,lat1);
  checklat(al,lat2);
  return gc_GEN(av, alglattransporter_i(al,lat1,lat2,1));
}

GEN
algmakeintegral(GEN mt0, long maps)
{
  pari_sp av = avma;
  long n,i;
  GEN m,P,Pi,mt2,mt;
  n = lg(mt0)-1;
  mt = check_mt(mt0,NULL);
  if (!mt) pari_err_TYPE("algmakeintegral", mt0);
  if (isint1(Q_denom(mt0))) {
    if (maps) mt = mkvec3(mt,matid(n),matid(n));
    return gc_GEN(av,mt);
  }
  dbg_printf(2)(" algmakeintegral: dim=%d, denom=%Ps\n", n, Q_denom(mt0));
  m = cgetg(n+1,t_MAT);
  for (i=1;i<=n;i++)
    gel(m,i) = mat2col(gel(mt,i),n,n);
  dbg_printf(2)(" computing order, dims m = %d x %d...\n", nbrows(m), lg(m)-1);
  P = QM_invimZ(m);
  dbg_printf(2)(" ...done.\n");
  P = shallowmatconcat(mkvec2(col_ei(n,1),P));
  P = hnf(P);
  Pi = RgM_inv(P);
  mt2 = change_Rgmultable(mt,P,Pi);
  if (maps) mt2 = mkvec3(mt2,Pi,P); /* mt2, mt->mt2, mt2->mt */
  return gc_GEN(av,mt2);
}

/** ORDERS **/

/*
 * algmodpr data:
 * 1. pr
 * 2. Vecsmall([k,m]) s.t. target is M_k(F_p^m). /!\ m can differ from pr.f
 * 3. t_FFELT 1 representing the finite field F_q
 * 4. proj: O -> M_k(F_q)
 * 5. lift: M_k(F_q) -> O
 * 6. tau: anti uniformizer (left multiplication matrix)
 * 7. T s.t. F_q = F_p[x]/T
 */
GEN
algmodprinit(GEN al, GEN pr, long v)
{
  pari_sp av = avma;
  GEN p, alp, g, Q, pro, lif, map, mapi, alpr, spl, data, nf, T, J, tau;
  long tal, k, m;
  checkalg(al); checkprid(pr);
  tal = alg_type(al);
  if (tal!=al_CYCLIC && tal!=al_CSA)
    pari_err_TYPE("algmodprinit [use alginit]", al);
  nf = alg_get_center(al);
  p = pr_get_p(pr);
  alp = alg_ordermodp(al, p);
  g = algeltfromnf_i(al, pr_get_gen(pr));
  g = algbasismultable(alp, g);
  g = FpM_image(g, p);
  alpr = alg_quotient(alp, g, 1);
  Q = gel(alpr, 1);
  pro = gel(alpr, 2);
  lif = gel(alpr, 3);
  J = algradical(Q); /* could skip if we knew the order is maximal at unramified pr */
  if (!gequal0(J))
  {
    Q = alg_quotient(Q, J, 1);
    pro = ZM_mul(gel(Q,2), pro);
    lif = ZM_mul(lif, gel(Q,3));
    Q = gel(Q,1);
  }
  spl = alg_finite_csa_split(Q, v);
  T = gel(spl, 1); /* t_POL, possibly of degree 1 */
  mapi = gel(spl, 3);
  map = gel(spl, 4);
  tau = pr_anti_uniformizer(nf, pr);
  m = degpol(T);
  k = lg(gmael(spl,2,1)) - 1;
  if (typ(tau) != t_INT) tau = algbasismultable(al,algeltfromnf_i(al,tau));
  data = mkvecn(7,
    pr,
    mkvecsmall2(k, m),
    Tp_to_FF(T,p),
    FpM_mul(map, pro, p),
    FpM_mul(lif, mapi, p),
    tau,
    T
  );
  return gc_GEN(av, data);
}

static int
checkalgmodpr_i(GEN data)
{
  GEN compo;
  if (typ(data)!=t_VEC || lg(data)!=8) return 0;
  checkprid(gel(data,1));
  compo = gel(data,2);
  if (typ(compo)!=t_VECSMALL || lg(compo)!=3) return 0;
  if (typ(gel(data,3))!=t_FFELT) return 0;
  if (typ(gel(data,4))!=t_MAT) return 0;
  if (typ(gel(data,5))!=t_MAT) return 0;
  compo = gel(data,6);
  if (typ(compo)!=t_MAT && (typ(compo)!=t_INT || !equali1(compo))) return 0;
  if (typ(gel(data,7))!=t_POL) return 0;
  return 1;
}
static void
checkalgmodpr(GEN data)
{
  if(!checkalgmodpr_i(data))
    pari_err_TYPE("checkalgmodpr [use algmodprinit()]", data);
}

/* x belongs to the stored order of al, no GC */
static GEN
algmodpr_integral(GEN x, GEN data, long reduce)
{
  GEN res, T, p;
  long k, m, v = -1;
  T = algmodpr_get_T(data);
  if (T) v = varn(T);
  p = algmodpr_get_p(data);
  k = algmodpr_get_k(data);
  m = algmodpr_get_m(data);
  res = ZM_ZC_mul(algmodpr_get_proj(data), x);
  res = RgC_col2mat(res, k, m, v);
  return reduce? FqM_red(res, T, p) : res;
}

/* x in basis form */
static GEN
algmodpr_i(GEN x, GEN data)
{
  GEN T, p, res, den, tau;
  long v, i, j;
  x = Q_remove_denom(x, &den);
  T = algmodpr_get_T(data);
  p = algmodpr_get_p(data);
  tau = algmodpr_get_tau(data);
  if (den)
  {
    v = Z_pvalrem(den, p, &den);
    if (v && typ(tau)!=t_INT)
    {
      /* TODO not always better to exponentiate the matrix */
      x = ZM_ZC_mul(ZM_powu(tau, v), x);
      v -= ZV_pvalrem(x, p, &x);
    }
    if (v>0) pari_err_INV("algmodpr", mkintmod(gen_0,p));
    if (v<0)
    {
      long k = algmodpr_get_k(data);
      return zeromatcopy(k,k);
    }
    if (equali1(den)) den = NULL;
  }
  res = algmodpr_integral(x, data, 0);
  if (den)
  {
    GEN d = Fp_inv(den, p);
    for (j=1; j<lg(res); j++)
      for (i=1; i<lg(res); i++)
        gcoeff(res,i,j) = Fq_Fp_mul(gcoeff(res,i,j), d, T, p);
  }
  else res = FqM_red(res, T, p);
  return res;
}

static GEN
algmodpr_mat(GEN al, GEN x, GEN data)
{
  GEN res, cx, c;
  long i, j;
  res = cgetg(lg(x),t_MAT);
  for (j=1; j<lg(x); j++)
  {
    cx = gel(x,j);
    c = cgetg(lg(cx), t_COL);
    for (i=1; i<lg(cx); i++) gel(c,i) = algmodpr(al, gel(cx,i), data);
    gel(res, j) = c;
  }
  return shallowmatconcat(res);
}

GEN
algmodpr(GEN al, GEN x, GEN data)
{
  pari_sp av = avma;
  GEN res, ff;
  checkalgmodpr(data);
  if (typ(x) == t_MAT) return gc_GEN(av, algmodpr_mat(al,x,data));
  x = algalgtobasis(al, x);
  res = algmodpr_i(x, data);
  ff = algmodpr_get_ff(data);
  return gc_GEN(av, FqM_to_FFM(res,ff));
}

static GEN
algmodprlift_i(GEN x, GEN data)
{
  GEN lift, C, p, c, T = NULL;
  long i, j, k, m;
  lift = algmodpr_get_lift(data);
  p = algmodpr_get_p(data);
  k = algmodpr_get_k(data);
  m = algmodpr_get_m(data); /* M_k(F_p^m) */
  if (m > 1) T = algmodpr_get_T(data);
  x = gcopy(x);
  for (i=1; i<=k; i++)
    for (j=1; j<=k; j++)
    {
      c = gcoeff(x,i,j);
      if (typ(c) == t_FFELT)    gcoeff(x,i,j) = FF_to_FpXQ(c);
      else if (m == 1)          gcoeff(x,i,j) = scalarpol(Rg_to_Fp(c,p), -1);
      else                      gcoeff(x,i,j) = Rg_to_FpXQ(c, T, p);
    }
  C = RgM_mat2col(x, k, m);
  return FpM_FpC_mul(lift, C, p);
}

GEN
algmodprlift(GEN al, GEN x, GEN data)
{
  pari_sp av = avma;
  GEN res, blk;
  long k, nc, nr, i, j;
  checkalg(al);
  checkalgmodpr(data);
  k = algmodpr_get_k(data); /* M_k(F_p^m) */
  if (typ(x) != t_MAT) pari_err_TYPE("algmodprlift [matrix x]",x);
  if ((lg(x)-1)%k) pari_err_DIM("algmodprlift [matrix x, nb cols]");
  nc = (lg(x)-1)/k;
  if (!nc) return gc_upto(av, zeromat(0,0));
  if ((lgcols(x)-1)%k) pari_err_DIM("algmodprlift [matrix x, nb rows]");
  nr = nbrows(x)/k;
  if (nr==1 && nc==1) res = algmodprlift_i(x, data);
  else
  {
    res = zeromatcopy(nr, nc);
    for (i=1; i<=nr; i++)
      for(j=1; j<=nc; j++)
      {
        blk = matslice(x, (i-1)*k+1, i*k, (j-1)*k+1, j*k);
        gcoeff(res,i,j) = algmodprlift_i(blk, data);
      }
  }
  return gc_GEN(av, res);
}

/* e in al such that e mod pr is a non-invertible idempotent of maximal rank */
static GEN
eichleridempotent(GEN al, GEN pr)
{
  long i, k, n, nk, j;
  GEN data, mapi, e;
  data = algmodprinit(al, pr, -1);
  mapi = algmodpr_get_lift(data);
  k = algmodpr_get_k(data);
  n = pr_get_f(pr);
  nk = n*(k+1);
  if (k==1) return zerocol(alg_get_absdim(al));
  e = gel(mapi,1+nk);
  for (i = 2, j = 1+2*nk; i < k; i++, j += nk) e = ZC_add(e,gel(mapi,j));
  return e;
}

static GEN
mat_algeltfromnf(GEN al, GEN x)
{
  pari_APPLY_type(t_MAT, algeltfromnf_i(al, gel(x,i)));
}
static GEN
eichlerprimepower_i(GEN al, GEN pr, long m, GEN prm)
{
  GEN p, e, polidem, Me, Mzk, nf, Mprm;
  long ep, i;
  ulong mask;
  polidem = mkpoln(4, gen_m2, utoi(3), gen_0, gen_0);
  p = pr_get_p(pr); ep = pr_get_e(pr);
  e = eichleridempotent(al, pr); /* ZC */
  mask = quadratic_prec_mask(m);
  i = 1;
  while (mask > 1)
  {
    i *=2;
    if (mask & 1UL) i--;
    mask >>= 1;
    e = algpoleval(al, polidem, e);
    e = FpC_red(e, powiu(p,(i+ep-1)/ep));
  }
  Me = algbasisrightmultable(al, e);
  nf = algcenter(al);
  Mzk = mat_algeltfromnf(al, nf_get_zk(nf));
  prm = idealtwoelt(nf, prm);
  Mprm = algbasismultable(al, algeltfromnf_i(al,gel(prm,2)));
  return hnfmodid(shallowmatconcat(mkvec3(Me,Mzk,Mprm)), gel(prm,1));
}
static GEN
eichlerprimepower(GEN al, GEN pr, long m, GEN prm)
{
  pari_sp av = avma;
  return gc_upto(av, eichlerprimepower_i(al, pr, m, prm));
}

GEN
algeichlerbasis(GEN al, GEN N)
{
  pari_sp av = avma;
  GEN nf, faN, LH = NULL, Cpr = NULL, Cm = NULL, Lpp, M, H, pp, LH2;
  long k, n, ih, lh, np;

  checkalg(al);
  nf = alg_get_center(al);
  if (checkprid_i(N)) return eichlerprimepower(al,N,1,N);
  if (is_nf_factor(N))
  {
    faN = sort_factor(shallowcopy(N), (void*)&cmp_prime_ideal, &cmp_nodata);
    N = factorbackprime(nf, gel(faN,1), gel(faN,2));
  }
  else faN = idealfactor(nf, N);
  n = nbrows(faN);
  if (!n) { set_avma(av); return matid(alg_get_absdim(al)); }
  if (n==1)
  {
    GEN pr = gcoeff(faN,1,1), mZ = gcoeff(faN,1,2);
    long m = itos(mZ);
    return gc_upto(av, eichlerprimepower_i(al, pr, m, N));
  }

  /* collect prime power Eichler orders */
  Lpp = cgetg(n+1,t_VEC);
  LH2 = cgetg(n+1, t_VEC);
  np = 0;
  ih = 1;
  lh = 1;
  for (k = 1; k <= n; k++)
  {
    GEN pr = gcoeff(faN,k,1), mZ = gcoeff(faN,k,2), prm;
    long m = itos(mZ);

    if (ih == lh) /* done with previous p, prepare next */
    {
      GEN p = pr_get_p(pr);
      long k2 = k + 1;
      np++;
      gel(Lpp,np) = gen_0;
      lh = 2;
      /* count the pr|p in faN */
      while (k2<=n && equalii(p,pr_get_p(gcoeff(faN,k2,1)))) { lh++; k2++; }
      LH = cgetg(lh, t_VEC);
      Cpr = cgetg(lh, t_VEC);
      Cm = cgetg(lh, t_VEC);
      ih = 1;
    }
    prm = idealpow(nf, pr, mZ);
    H = eichlerprimepower(al, pr, m, prm);
    pp = gcoeff(prm,1,1);
    if (cmpii(pp,gel(Lpp,np)) > 0) gel(Lpp,np) = pp;
    gel(LH,ih) = H;
    gel(Cpr,ih) = pr;
    gel(Cm,ih) = mZ;
    ih++;

    if (ih == lh) /* done with this p */
    {
      if (lh == 2) gel(LH2,np) = gel(LH,1);
      else
      { /* put together the pr|p */
        GEN U = gmael(idealchineseinit(nf, mkmat2(Cpr,Cm)),1,2);
        long i;
        for (i = 1; i < lh; i++)
        {
          GEN e = algeltfromnf_i(al, gel(U,i));
          e = algbasismultable(al, e);
          gel(LH,i) = ZM_mul(e, gel(LH,i));
        }
        gel(LH2,np) = hnfmodid(shallowmatconcat(LH), gel(Lpp,np));
      }
    }
  }
  if (np == 1) return gc_GEN(av, gel(LH2,1));
  /* put together all p */
  setlg(Lpp,np+1);
  setlg(LH2,np+1);
  H = nmV_chinese_center(LH2, Lpp, &M);
  return gc_upto(av, hnfmodid(H, M));
}

/** IDEALS **/
