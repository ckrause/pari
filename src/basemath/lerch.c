/* Copyright (C) 2022  The PARI group.

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

#define DEBUGLEVEL DEBUGLEVEL_trans

/********************************************************/
/*                   Hurwitz zeta function              */
/********************************************************/
/* s1 = s-1 or NULL (if s=1) */
static GEN
hurwitzp_i(GEN cache, GEN s1, GEN x, GEN p, long prec)
{
  long j, J = lg(cache) - 2;
  GEN S, x2, x2j;

  x = ginv(gadd(x, zeropadic_shallow(p, prec)));
  S = s1? gmul2n(gmul(s1, x), -1): gadd(Qp_log(x), gmul2n(x, -1));
  x2j = x2 = gsqr(x); S = gaddgs(S,1);
  for (j = 1;; j++)
  {
    S = gadd(S, gmul(gel(cache, j+1), x2j));
    if (j == J) break;
    x2j = gmul(x2, x2j);
  }
  if (s1) S = gmul(gdiv(S, s1), Qp_exp(gmul(s1, Qp_log(x))));
  return S;
}

static GEN
init_cache(long prec, long p, GEN s)
{
  long j, fls = !gequal1(s), J = (((p==2)? (prec >> 1): prec) + 2) >> 1;
  GEN C = gen_1, cache = bernvec(J);
  for (j = 1; j <= J; j++)
  { /* B_{2j} * binomial(1-s, 2j) */
    GEN t = (j > 1 || fls) ? gmul(gaddgs(s, 2*j-3), gaddgs(s, 2*j-2)) : s;
    C = gdiv(gmul(C, t), mulss(2*j, 2*j-1));
    gel(cache, j+1) = gmul(gel(cache, j+1), C);
  }
  return cache;
}

static GEN
zetap_i(GEN s, long D)
{
  pari_sp av = avma;
  GEN cache, S, s1, gm, va, gp = gel(s,2);
  ulong a, p = itou(gp), m;
  long prec = valp(s) + precp(s);

  if (D <= 0) pari_err_DOMAIN("p-adic L-function", "D", "<=", gen_0, stoi(D));
  if (!uposisfundamental(D))
    pari_err_TYPE("p-adic L-function [D not fundamental]", stoi(D));
  if (D == 1 && gequal1(s))
    pari_err_DOMAIN("p-adic zeta", "argument", "=", gen_1, s);
  if (prec <= 0) prec = 1;
  cache = init_cache(prec, p, s);
  m = ulcm(D, p == 2? 4: p);
  gm = stoi(m);
  va = coprimes_zv(m);
  S = gen_0; s1 = gsubgs(s,1); if (gequal0(s1)) s1 = NULL;
  for (a = 1; a <= (m >> 1); a++)
    if (va[a])
    {
      GEN z = hurwitzp_i(cache, s1, gdivsg(a,gm), gp, prec);
      S = gadd(S, gmulsg(kross(D,a), z));
    }
  S = gdiv(gmul2n(S, 1), gm);
  if (D > 1)
  {
    gm = gadd(gm, zeropadic_shallow(gp, prec));
    S = gmul(S, Qp_exp(gmul(gsubsg(1, s), Qp_log(gm))));
  }
  return gerepileupto(av, S);
}
GEN
Qp_zeta(GEN s) { return zetap_i(s, 1); }

static GEN
hurwitzp(GEN s, GEN x)
{
  GEN s1, T = (typ(s) == t_PADIC)? s: x, gp = gel(T,2);
  long p = itou(gp), vqp = (p==2)? 2: 1, prec = maxss(1, valp(T) + precp(T));

  if (s == T) x = gadd(x, zeropadic_shallow(gp, prec));
  else        s = gadd(s, zeropadic_shallow(gp, prec));
  /* now both s and x are t_PADIC */
  if (valp(x) > -vqp)
  {
    GEN S = gen_0;
    long j, M = (p==2)? 4: p;
    for (j = 0; j < M; j++)
    {
      GEN y = gaddsg(j, x);
      if (valp(y) <= 0) S = gadd(S, hurwitzp(s, gdivgu(y, M)));
    }
    return gdivgu(S, M);
  }
  if (valp(s) <= 1/(p-1) - vqp)
    pari_err_DOMAIN("hurwitzp", "v(s)", "<=", stoi(1/(p-1)-vqp), s);
  s1 = gsubgs(s,1); if (gequal0(s1)) s1 = NULL;
  return hurwitzp_i(init_cache(prec,p,s), s1, x, gp, prec);
}

static void
binsplit(GEN *pP, GEN *pR, GEN aN2, GEN isqaN, GEN s, long j, long k, long prec)
{
  if (j + 1 == k)
  {
    long j2 = j << 1;
    GEN P;
    if (!j) P = gdiv(s, aN2);
    else
    {
      P = gmul(gaddgs(s, j2-1), gaddgs(s, j2));
      P = gdivgunextu(gmul(P, isqaN), j2+1);
    }
    if (pP) *pP = P;
    if (pR) *pR = gmul(bernreal(j2+2, prec), P);
  }
  else
  {
    GEN P1, R1, P2, R2;
    binsplit(&P1,pR? &R1: NULL, aN2, isqaN, s, j, (j+k) >> 1, prec);
    binsplit(pP? &P2: NULL, pR? &R2: NULL, aN2, isqaN, s, (j+k) >> 1, k, prec);
    if (pP) *pP = gmul(P1,P2);
    if (pR) *pR = gadd(R1, gmul(P1, R2));
  }
}

/* a0 +  a1 x + O(x^e), e >= 0 */
static GEN
deg1ser_shallow(GEN a1, GEN a0, long v, long e)
{ return RgX_to_ser(deg1pol_shallow(a1, a0, v), e+2); }

/* New zetahurwitz, from Fredrik Johansson. */
GEN
zetahurwitz(GEN s, GEN x, long der, long bitprec)
{
  pari_sp av = avma, av2;
  GEN a, ra, ra0, Nx, S1, S2, S3, N2, rx, sch = NULL, s0 = s, x0 = x, y;
  long j, k, m, N, prec0 = nbits2prec(bitprec), prec = prec0, fli = 0;
  pari_timer T;

  if (der < 0) pari_err_DOMAIN("zetahurwitz", "der", "<", gen_0, stoi(der));
  if (der)
  {
    GEN z;
    if (!is_scalar_t(typ(s)))
    {
      z = deriv(zetahurwitz(s, x, der - 1, bitprec), -1);
      z = gdiv(z, deriv(s, -1));
    }
    else
    {
      if (gequal1(s)) pari_err_DOMAIN("zetahurwitz", "s", "=", gen_1, s0);
      s = deg1ser_shallow(gen_1, s, 0, der+2);
      z = zetahurwitz(s, x, 0, bitprec + der * log2(der));
      z = gmul(mpfact(der), polcoef_i(z, der, -1));
    }
    return gerepileupto(av,z);
  }
  if (typ(x) == t_PADIC || typ(s) == t_PADIC)
    return gerepilecopy(av, hurwitzp(s, x));
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: break;
    default:
      if (!(y = toser_i(x))) pari_err_TYPE("zetahurwitz", x);
      x = y; x0 = polcoef_i(x, 0, -1); break;
  }
  rx = grndtoi(real_i(x0), &j);
  if (typ(rx) != t_INT) pari_err_TYPE("zetahurwitz", x);
  if (x0 == x && signe(rx) <= 0 && gexpo(gsub(x, rx)) < 17 - bitprec)
    pari_err_DOMAIN("zetahurwitz", "x", "<=", gen_0, x);
  switch (typ(s))
  {
    long v, pr;
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: break;
    default:
      if (!(y = toser_i(s))) pari_err_TYPE("zetahurwitz", s);
      if (valp(y) < 0) pari_err_DOMAIN("zetahurwitz", "val(s)", "<", gen_0, s);
      s0 = polcoef_i(y, 0, -1);
      switch(typ(s0))
      {
        case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: break;
        case t_PADIC: pari_err_IMPL("zetahurwitz(t_SER of t_PADIC)");
        default: pari_err_TYPE("zetahurwitz", s0);
      }
      sch = gequal0(s0)? y: serchop0(y);
      v = valp(sch);
      pr = (lg(y) + v + 1) / v;
      if (gequal1(s0)) pr += v;
      s = deg1ser_shallow(gen_1, s0, 0, pr);
    }
  a = gneg(s0); ra = real_i(a); ra0 = ground(ra);
  if (gequal1(s0) && (!sch || gequal0(sch)))
    pari_err_DOMAIN("zetahurwitz", "s", "=", gen_1, s0);
  fli = (gsigne(ra0) >= 0 && gexpo(gsub(a, ra0)) < 17 - bitprec);
  if (!sch && fli)
  { /* a ~ non negative integer */
    k = itos(gceil(ra)) + 1;
    if (odd(k)) k++;
    N = 1;
  }
  else
  {
    GEN C, ix = imag_i(x0);
    double c = (typ(s) == t_INT)? 1: 20 * log((double)bitprec);
    double rs = gtodouble(ra) + 1;
    long k0;
    if (fli) a = gadd(a, ghalf); /* hack */
    if (rs > 0)
    {
      bitprec += (long)ceil(rs * expu(bitprec));
      prec = nbits2prec(bitprec);
      x = gprec_w(x, prec);
      s = gprec_w(s, prec);
      if (sch) sch = gprec_w(sch, prec);
    }
    k = bitprec * M_LN2 / (1 + dbllambertW0(M_PI / c));
    k0 = itos(gceil(gadd(ra, ghalf))) + 1;
    k = maxss(k0, k);
    if (odd(k)) k++;
    /* R_k < 2 |binom(a,k+1) B_{k+2}/(k+2)| */
    C = binomial(a, k+1); C = polcoef_i(C, 0, -1);
    C = gmul(C, gdivgu(bernfrac(k+2), k+2));
    C = gmul2n(gabs(C,LOWDEFAULTPREC), bitprec + 1);
    C = gpow(C, ginv(gsubsg(k+1, ra)), LOWDEFAULTPREC);
    /* need |N + x - 1|^2 > C^2 */
    if (!gequal0(ix)) C = gsqrt(gsub(gsqr(C), gsqr(ix)), LOWDEFAULTPREC);
    /* need |N + re(x) - 1| > C */
    C = gceil(gadd(C, gsubsg(1, rx)));
    if (typ(C) != t_INT) pari_err_TYPE("zetahurwitz",s);
    N = signe(C) > 0? itos(C) : 1;
    if (N == 1 && signe(a) > 0)
    { /* May reduce k if 2Pix > a */
      /* Need 2 |x^(-K) (B_K/K) binom(a, K-1)| < 2^-bit |x|^-rs |zeta(s,x)|
       * with K = k+2; N = 1; |zeta(s,x)| ~ |x|^(rs-1);
       * if a > 0, (B_K/K) binom(a, K-1) < 2 |a / 2Pi|^K */
      double dx = dbllog2(x0), d = 1 + dx + log2(M_PI) - dbllog2(s0);
      if (d > 0)
      { /* d ~ log2 |2Pi x / a| */
        long K = (long)ceil((bitprec + 1 + dx) / d);
        K = maxss(k0, K);
        if (odd(K)) K++;
        if (K < k) k = K;
      }
    }
  }
  if (gsigne(rx) < 0) N = maxss(N, 1 - itos(rx));
  a = gneg(s);
  if (DEBUGLEVEL>2) timer_start(&T);
  incrprec(prec);
  Nx = gmul(real_1(prec), gaddsg(N - 1, x));
  S1 = S3 = gpow(Nx, a, prec);
  av2 = avma;
  if (gequal1(x)) S1 = dirpowerssum(N, a, prec);
  else
    for (m = N - 2; m >= 0; m--)
    {
      S1 = gadd(S1, gpow(gaddsg(m,x), a, prec));
      if ((m & 0xff) == 0) S1 = gerepileupto(av2, S1);
    }
  if (DEBUGLEVEL>2) timer_printf(&T,"sum from 0 to N - 1");
  constbern(k >> 1);
  N2 = ginv(gsqr(Nx));
  if (typ(s0) == t_INT)
  {
    S2 = divru(bernreal(k, prec), k);
    for (j = k - 2; j >= 2; j -= 2)
    {
      GEN t = gsubgs(a, j), u = gmul(t, gaddgs(t, 1));
      u = gmul(gdivgunextu(u, j), gmul(S2, N2));
      S2 = gadd(divru(bernreal(j, prec), j), u);
    }
    S2 = gmul(S2, gdiv(a, Nx));
  }
  else
  {
    binsplit(NULL,&S2, gmul2n(Nx,1), N2, s, 0, k >> 1, prec);
    S2 = gneg(S2);
  }
  S2 = gadd(ghalf, S2);
  if (DEBUGLEVEL>2) timer_printf(&T,"Bernoulli sum");
  S2 = gmul(S3, gadd(gdiv(Nx, gaddsg(1, a)), S2));
  S1 = gprec_wtrunc(gsub(S1, S2), prec0);
  if (sch) return gerepileupto(av, gsubst(S1, 0, sch));
  return gerepilecopy(av, S1);
}

/* New Lerch, inspired by Fredrik Johansson. */

GEN
lerch_worker(GEN t, GEN E)
{
  GEN n, d, T, s = gel(E,1), a = gmul(gel(E,2), t), z = gel(E,3);
  long p = itos(gel(E,4)), prec = labs(p);
  d = gadd(gexp(t, prec), z);
  T = p > 0? t: gneg(t);
  if (typ(s) == t_INT)
    n = gmul(gpow(T, s, prec), gexp(a, prec));
  else /* save one exp */
    n = gexp(gadd(gmul(s, glog(T, prec)), a), prec);
  return gdiv(n, d);
}

/* tab already computed with N = #tab[1] even */
static GEN
parintnumgauss(GEN f, GEN a, GEN b, GEN tab, long prec)
{
  GEN R = gel(tab, 1), W = gel(tab, 2), bma, bpa, S = gen_0, VP, VM, V;
  long n = lg(R) - 1, i, prec2 = prec + EXTRAPREC64;
  a = gprec_wensure(a, prec2);
  b = gprec_wensure(b, prec2);
  VP = cgetg(n + 1, t_VEC); bma = gmul2n(gsub(b, a), -1);
  VM = cgetg(n + 1, t_VEC); bpa = gadd(bma, a);
  for (i = 1; i <= n; i++)
  {
    GEN h = gmul(bma, gel(R, i));
    gel(VP, i) = gadd(bpa, h);
    gel(VM, i) = gsub(bpa, h);
  }
  V = gadd(parapply(f, VP), parapply(f, VM));
  for (i = 1; i <= n; i++)
  {
    S = gadd(S, gmul(gel(W, i), gel(V, i)));
    S = gprec_wensure(S, prec2);
  }
  return gprec_wtrunc(gmul(bma, S), prec);
}

/* Assume tab computed and a >= 0 */
static GEN
parintnum(GEN f, GEN a, GEN tab)
{
  pari_sp av;
  GEN tabx0 = gel(tab, 2), tabw0 = gel(tab, 3), tabxm = gel(tab, 6);
  GEN tabxp = gel(tab, 4), tabwp = gel(tab, 5), tabwm = gel(tab, 7);
  GEN VP = tabxp, VM = tabxm, x0 = tabx0, S;
  long prec = gprecision(tabw0), L = lg(tabxp), i, fla = 0;
  if (!gequal0(a))
  {
    if (gexpo(a) <= 0)
    {
      x0 = gadd(a, x0);
      for (i = 1; i < L; i++)
      {
        gel(VP, i) = gadd(a, gel(VP, i));
        gel(VM, i) = gadd(a, gel(VM, i));
      }
    }
    else
    {
      x0 = gmul(a, gaddsg(1, x0)); fla = 1;
      for (i = 1; i < L; i++)
      {
        gel(VP, i) = gmul(a, gaddsg(1, gel(VP, i)));
        gel(VM, i) = gmul(a, gaddsg(1, gel(VM, i)));
      }
    }
  }
  VP = parapply(f, VP);
  VM = parapply(f, VM); av = avma;
  S = gmul(tabw0, closure_callgen1(f, x0));
  for (i = 1; i < L; i++)
  {
    S = gadd(S, gadd(gmul(gel(tabwp, i), gel(VP, i)),
                     gmul(gel(tabwm, i), gel(VM, i))));
    if ((i & 0x7f) == 1) S = gerepileupto(av, S);
    S = gprec_wensure(S, prec);
  }
  if (fla) S = gmul(S, a);
  return gmul(S, gel(tab, 1));
}

static GEN
refine(GEN A)
{
  long n = lg(A) - 1, i;
  GEN B = cgetg(2 * n, t_VEC);
  for (i = 1; i < n; i++)
  {
    gel(B, 2 * i - 1) = gel(A, i);
    gel(B, 2 * i) = gmul2n(gadd(gel(A, i), gel(A, i + 1)), -1);
  }
  gel(B, 2 * n - 1) = gel(A, n); return B;
}

/* Here L = [a1, a2, a3,...] integration vertices. Refine by splitting
 * intervals. */
static GEN
parintnumgaussadapt(GEN f, GEN L, GEN tab, long bit)
{
  GEN Rold = gen_0, Rnew;
  long i, ct = 0, prec = nbits2prec(bit);
  while (ct <= 5)
  {
    Rnew = gen_0;
    for (i = 1; i < lg(L) - 1; i++)
      Rnew = gadd(Rnew, parintnumgauss(f, gel(L, i), gel(L, i + 1), tab, prec));
    if (ct && gexpo(gsub(Rnew, Rold)) - gexpo(Rnew) < 10 - bit) return Rnew;
    ct++; Rold = Rnew; L = refine(L);
  }
  if (DEBUGLEVEL) err_printf("intnumgaussadapt: possible accuracy loss");
  return Rnew; /* Possible accuracy loss */
}

/* Here b = [oo, r], so refine by increasing integration step m */
static GEN
parintnumadapt(GEN f, GEN a, GEN b, GEN tab, long bit)
{
  GEN Rold = gen_0, Rnew;
  long m = 0, prec = nbits2prec(bit);
  if (!tab) tab = intnuminit(gen_0, b, 0, prec);
  while (m <= 5)
  {
    Rnew = parintnum(f, a, tab);
    if (m && gexpo(gsub(Rnew, Rold)) - gexpo(Rnew) < 10 - bit) return Rnew;
    m++; Rold = Rnew; tab = intnuminit(gen_0, b, m, prec);
  }
  if (DEBUGLEVEL) err_printf("intnumadapt: possible accuracy loss");
  return Rnew; /* Possible accuracy loss */
}

static int
iscplx(GEN z) { long t = typ(z); return is_real_t(t) || t == t_COMPLEX; }

static GEN
lerch_easy(GEN z, GEN s, GEN a, long B)
{
  long n, prec = nbits2prec(B + 32);
  GEN zn, ms = gneg(s), S = gpow(a, ms, prec);
  zn = z = gtofp(z, prec);
  for (n = 1;; n++, zn = gmul(zn, z))
  {
    S = gadd(S, gmul(zn, gpow(gaddgs(a, n), ms, prec)));
    if (gexpo(zn) <= - B - 5) return S;
  }
}

static GEN
_lerchphi(GEN z, GEN s, GEN a, long prec)
{
  GEN res = NULL, L, LT, J, rs, mleft, left, right, top, w, Linf, tabg;
  GEN E, f, fm;
  long B = prec2nbits(prec), MB = 3 - B, NB, prec2;
  entree *ep;

  if (!iscplx(z)) pari_err_TYPE("lerchphi", z);
  if (!iscplx(s)) pari_err_TYPE("lerchphi", s);
  if (!iscplx(a)) pari_err_TYPE("lerchphi", a);
  if (gexpo(z) < MB) return gpow(a, gneg(s), prec);
  if (gexpo(gsubgs(z, 1)) < MB) return zetahurwitz(s, a, 0, B); /* z ~ 1 */
  if (gexpo(gaddgs(z, 1)) < MB) /* z ~ -1 */
  {
    GEN tmp = gsub(zetahurwitz(s, gmul2n(a, -1), 0, B),
                   zetahurwitz(s, gmul2n(gaddgs(a, 1), -1), 0, B));
    return gmul(gpow(gen_2, gneg(s), prec), tmp);
  }
  if (gcmpgs(gmulsg(10, gabs(z, prec)), 9) <= 0) /* |z| <= 9/10 */
    return lerch_easy(z, s, a, B);
  if (gcmpgs(real_i(a), 2) < 0)
    return gadd(gpow(a, gneg(s), prec),
                gmul(z, lerchphi(z, s, gaddgs(a, 1), prec)));
  NB = (long)ceil(B + M_PI * fabs(gtodouble(imag_i(s))));
  prec2 = nbits2prec(NB);
  z = gprec_w(z, prec2);
  s = gprec_w(s, prec2);
  a = gprec_w(a, prec2);
  rs = ground(real_i(s)); L = glog(z, prec2);
  ep = is_entry("_lerch_worker");
  E = mkvec4(gsubgs(s, 1), gsubsg(1, a), gneg(z), stoi(prec2));
  f = snm_closure(ep, mkvec(E));
  E = shallowcopy(E); gel(E,4) = stoi(-prec2);
  fm = snm_closure(ep, mkvec(E));
  Linf = mkvec2(mkoo(), real_i(a));
  if (gexpo(gsub(s, rs)) < MB && gcmpgs(rs, 1) >= 0)
  { /* real(s) ~ positive integer */
    if (gcmp(gabs(imag_i(L), prec2), sstoQ(1, 4)) < 0 && gsigne(real_i(L)) >= 0)
    { /* real(L) >= 0, |imag(L)| < 1/4 */
      GEN t = gsigne(imag_i(z)) > 0 ? gen_m1: gen_1;
      GEN LT1 = gaddgs(gabs(L, prec2), 1);
      LT = mkvec4(gen_0, mkcomplex(gen_0, t), mkcomplex(LT1, t), LT1);
      tabg = intnumgaussinit(2*(NB >> 2) + 60, prec2);
      J = parintnumgaussadapt(f, LT, tabg, NB);
      J = gadd(J, parintnumadapt(f, LT1, Linf, NULL, NB));
    }
    else J = parintnumadapt(f, gen_0, Linf, NULL, NB);
    return gdiv(J, ggamma(s, prec2));
  }
  tabg = intnumgaussinit(2*(NB >> 2) + 60, prec2);
  if (gcmp(real_i(L), gneg(ghalf)) < 0) /* real(L) < -1/2 */
    left = right = top = gmin(gmul2n(gabs(real_i(L), prec2), -1), gen_1);
  else if (gcmp(gabs(imag_i(L), prec2), ghalf) > 0) /* |imag(L)| > 1/2 */
    left = right = top = gmin(gmul2n(gabs(imag_i(L), prec2), -1), gen_1);
  else
  {
    res = gdiv(gpow(gneg(L), s, prec2), gmul(L, gpow(z, a, prec2)));
    left = gaddgs(gmax(gen_0, gneg(real_i(L))), 1);
    top = gaddgs(gabs(imag_i(L), prec2), 1);
    right = gaddgs(gabs(L, prec2), 1);
  }
  w = expIPiC(gsubgs(s, 1), prec2);
  mleft = gneg(left);
  if (gexpo(imag_i(z)) < MB && gexpo(imag_i(a)) < MB && gexpo(imag_i(s)) < MB
      && gcmpgs(real_i(z), 1) < 0 && gsigne(real_i(a)) > 0)
  {
    /* z, s, a real, 0 < a, z < 1 */
    LT = mkvec3(right, mkcomplex(right, top), mkcomplex(mleft, top));
    J = imag_i(gdiv(parintnumgaussadapt(f, LT, tabg, NB), w));
    LT = mkvec2(mkcomplex(mleft, top), mleft);
    J = gmul2n(gadd(J, imag_i(parintnumgaussadapt(fm, LT, tabg, NB))), 1);
    J = mulcxI(J);
  }
  else
  {
    GEN mtop = gneg(top);
    LT = mkvec3(right, mkcomplex(right, top), mkcomplex(mleft, top));
    J = gdiv(parintnumgaussadapt(f, LT, tabg, NB), w);
    LT = mkvec2(mkcomplex(mleft, top), mkcomplex(mleft, mtop));
    J = gadd(J, parintnumgaussadapt(fm, LT, tabg, NB));
    LT = mkvec3(mkcomplex(mleft, mtop), mkcomplex(right, mtop), right);
    J = gadd(J, gmul(parintnumgaussadapt(f, LT, tabg, NB), w));
  }
  J = gadd(J, gmul(gsub(w, ginv(w)), parintnumadapt(f, right, Linf, NULL, NB)));
  J = gdiv(J, PiI2(prec2)); if (res) J = gadd(J, res);
  return gneg(gmul(ggamma(gsubsg(1, s), prec2), J));
}
/* lerchphi(z,-k,a)=
 *  -1/(z-1)*sum(q=0,k,(z/(z-1))^q*sum(j=0,q,(-1)^j*(j+a)^k*binomial(q,j)))
 * zetahurwitz(-k,a)=-B(k+1,a)/(k+1) */
GEN
lerchphi(GEN z, GEN s, GEN a, long prec)
{
  pari_sp av = avma;
  return gerepileupto(av, _lerchphi(z, s, a, prec));
}

GEN
lerchzeta(GEN s, GEN a, GEN lam, long prec)
{
  pari_sp av = avma;
  GEN z = gexp(gmul(PiI2(prec), lam), prec);
  return gerepileupto(av, _lerchphi(z, s, a, prec));
}