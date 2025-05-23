#line 2 "../src/kernel/none/ratlift.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*==========================================================
 * Fp_ratlift(GEN x, GEN m, GEN *a, GEN *b, GEN amax, GEN bmax)
 *==========================================================
 * Reconstruct rational number from its residue x mod m
 *    Given t_INT x, m, amax>=0, bmax>0 such that
 *         0 <= x < m;  2*amax*bmax < m
 *    attempts to find t_INT a, b such that
 *         (1) a = b*x (mod m)
 *         (2) |a| <= amax, 0 < b <= bmax
 *         (3) gcd(m, b) = gcd(a, b)
 *    If unsuccessful, it will return 0 and leave a,b unchanged  (and
 *    caller may deduce no such a,b exist).  If successful, sets a,b
 *    and returns 1.  If there exist a,b satisfying (1), (2), and
 *         (3') gcd(m, b) = 1
 *    then they are uniquely determined subject to (1),(2) and
 *         (3'') gcd(a, b) = 1,
 *    and will be returned by the routine.  (The caller may wish to
 *    check gcd(a,b)==1, either directly or based on known prime
 *    divisors of m, depending on the application.)
 * Reference:
 @article {MR97c:11116,
     AUTHOR = {Collins, George E. and Encarnaci{\'o}n, Mark J.},
      TITLE = {Efficient rational number reconstruction},
    JOURNAL = {J. Symbolic Comput.},
     VOLUME = {20},
       YEAR = {1995},
     NUMBER = {3},
      PAGES = {287--297},
 }
 * Preprint available from:
 * ftp://ftp.risc.uni-linz.ac.at/pub/techreports/1994/94-64.ps.gz */
static ulong
get_vmax(GEN r, long lb, long lbb)
{
  long lr = lb - lgefint(r);
  ulong vmax;
  if (lr > 1)        /* still more than a word's worth to go */
    vmax = ULONG_MAX;        /* (cannot in fact happen) */
  else
  { /* take difference of bit lengths */
    long lbr = bfffo(*int_MSW(r));
    lr = lr*BITS_IN_LONG - lbb + lbr;
    if ((ulong)lr > BITS_IN_LONG)
      vmax = ULONG_MAX;
    else if (lr == 0)
      vmax = 1UL;
    else
      vmax = 1UL << (lr-1); /* pessimistic but faster than a division */
  }
  return vmax;
}

/* assume bmax <= sqrt(m), fast if amax <=sqrt(m) */
static int
Fp_ratlift_hgcd(GEN n, GEN m, GEN amax, GEN bmax, GEN *pa, GEN *pb)
{
  pari_sp av = avma;
  GEN x, y, a, b;
  GEN H = halfgcdii(n, m), M = gel(H,1), V = gel(H,2);
  x = gel(V,1); a = gel(V,2); y = gcoeff(M,1,1); b = gcoeff(M,2,1);
  while(abscmpii(b, bmax)<=0)
  {
    GEN q, r, u;
    if (abscmpii(a, amax)<=0)
    {
      if (signe(b)<0)  { a = negi(a); b = negi(b); }
      *pa =a; *pb = b;
      (void)gc_all(av, 2, pb, pa); return 1;
    }
    q = dvmdii(x, a, &r); x = a; a = r;
    u = subii(y, mulii(b, q));
    y = b; b = u;
  }
  return gc_bool(av, 0);
}

/* Assume x,m,amax >= 0,bmax > 0 are t_INTs, 0 <= x < m, 2 amax * bmax < m */
int
Fp_ratlift(GEN x, GEN m, GEN amax, GEN bmax, GEN *a, GEN *b)
{
  GEN d, d1, v, v1, q, r;
  pari_sp av = avma, av1;
  long lb, lbb, s, s0;
  ulong vmax;
  ulong xu, xu1, xv, xv1; /* Lehmer stage recurrence matrix */
  int lhmres;             /* Lehmer stage return value */

  /* special cases x=0 and/or amax=0 */
  if (!signe(x)) { *a = gen_0; *b = gen_1; return 1; }
  if (!signe(amax)) return 0;
  /* assert: m > x > 0, amax > 0 */

  /* check whether a=x, b=1 is a solution */
  if (cmpii(x,amax) <= 0) { *a = icopy(x); *b = gen_1; return 1; }

  if (amax == bmax || equalii(amax, bmax))
    return Fp_ratlift_hgcd(x, m, amax, bmax, a, b);

  /* There is no special case for single-word numbers since this is
   * mainly meant to be used with large moduli. */
  (void)new_chunk(lgefint(bmax) + lgefint(amax)); /* room for a,b */
  d = m; d1 = x;
  v = gen_0; v1 = gen_1;
  /* assert d1 > amax, v1 <= bmax here */
  lb = lgefint(bmax);
  lbb = bfffo(*int_MSW(bmax));
  s = 1;
  av1 = avma;

  /* General case: Euclidean division chain starting with m div x, and
   * with bounds on the sequence of convergents' denoms v_j.
   * Just to be different from what invmod and bezout are doing, we work
   * here with the all-nonnegative matrices [u,u1;v,v1]=prod_j([0,1;1,q_j]).
   * Loop invariants:
   * (a) (sign)*[-v,v1]*x = [d,d1] (mod m)  (componentwise)
   * (sign initially +1, changes with each Euclidean step)
   * so [a,b] will be obtained in the form [-+d,v] or [+-d1,v1];
   * this congruence is a consequence of
   *
   * (b) [x,m]~ = [u,u1;v,v1]*[d1,d]~,
   * where u,u1 is the usual numerator sequence starting with 1,0
   * instead of 0,1  (just multiply the eqn on the left by the inverse
   * matrix, which is det*[v1,-u1;-v,u], where "det" is the same as the
   * "(sign)" in (a)).  From m = v*d1 + v1*d and
   *
   * (c) d > d1 >= 0, 0 <= v < v1,
   * we have d >= m/(2*v1), so while v1 remains smaller than m/(2*amax),
   * the pair [-(sign)*d,v] satisfies (1) but violates (2) (d > amax).
   * Conversely, v1 > bmax indicates that no further solutions will be
   * forthcoming;  [-(sign)*d,v] will be the last, and first, candidate.
   * Thus there's at most one point in the chain division where a solution
   * can live:  v < bmax, v1 >= m/(2*amax) > bmax,  and this is acceptable
   * iff in fact d <= amax  (e.g. m=221, x=34 or 35, amax=bmax=10 fail on
   * this count while x=32,33,36,37 succeed).  However, a division may leave
   * a zero residue before we ever reach this point  (consider m=210, x=35,
   * amax=bmax=10),  and our caller may find that gcd(d,v) > 1  (Examples:
   * keep m=210 and consider any of x=29,31,32,33,34,36,37,38,39,40,41).
   * Furthermore, at the start of the loop body we have in fact
   *
   * (c') 0 <= v < v1 <= bmax, d > d1 > amax >= 0,
   * (and are never done already).
   *
   * Main loop is similar to those of invmod() and bezout(), except for
   * having to determine appropriate vmax bounds, and checking termination
   * conditions.  The signe(d1) condition is only for paranoia */
  while (lgefint(d) > 3 && signe(d1))
  {
    /* determine vmax for lgcdii so as to ensure v won't overshoot.
     * If v+v1 > bmax, the next step would take v1 beyond the limit, so
     * since [+-d1,v1] is not a solution, we give up.  Otherwise if v+v1
     * is way shorter than bmax, use vmax=ULONG_MAX.  Otherwise, set vmax
     * to a crude lower approximation of bmax/(v+v1), or to 1, which will
     * allow the inner loop to do one step */
    r = addii(v,v1);
    if (cmpii(r,bmax) > 0) return gc_long(av, 0); /* done, not found */
    vmax = get_vmax(r, lb, lbb);
    /* do a Lehmer-Jebelean round */
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, vmax);
    if (lhmres) /* check progress */
    { /* apply matrix */
      if (lhmres == 1 || lhmres == -1)
      {
        s = -s;
        if (xv1 == 1)
        { /* re-use v+v1 computed above */
          v = v1; v1 = r;
          r = subii(d,d1); d = d1; d1 = r;
        }
        else
        {
          r = subii(d, mului(xv1,d1)); d = d1; d1 = r;
          r = addii(v, mului(xv1,v1)); v = v1; v1 = r;
        }
      }
      else
      {
        r  = subii(muliu(d,xu),  muliu(d1,xv));
        d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
        r  = addii(muliu(v,xu),  muliu(v1,xv));
        v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
        if (lhmres&1) { togglesign(d); s = -s; } else togglesign(d1);
      }
      /* check whether we're done.  Assert v <= bmax here.  Examine v1:
       * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
       * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise proceed*/
      if (cmpii(v1,bmax) > 0)
      {
        set_avma(av);
        if (cmpii(d,amax) > 0) return 0; /* done, not found */
        /* done, found */
        *a = icopy(d); setsigne(*a,-s);
        *b = icopy(v); return 1;
      }
      if (cmpii(d1,amax) <= 0)
      { /* done, found */
        set_avma(av);
        if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
        *b = icopy(v1); return 1;
      }
    } /* lhmres != 0 */

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
      d = d1; d1 = r;
      r = addii(v, mulii(q,v1));
      v = v1; v1 = r;
      s = -s;
      /* check whether we are done now.  Since we weren't before the div, it
       * suffices to examine v1 and d1 -- the new d (former d1) cannot cut it */
      if (cmpii(v1,bmax) > 0) return gc_long(av, 0); /* done, not found */
      if (cmpii(d1,amax) <= 0) /* done, found */
      {
        set_avma(av);
        if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
        *b = icopy(v1); return 1;
      }
    }

    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ratlift");
      (void)gc_all(av1, 4, &d, &d1, &v, &v1);
    }
  } /* end while */

  /* Postprocessing - final sprint.  Since we usually underestimate vmax,
   * this function needs a loop here instead of a simple conditional.
   * Note we can only get here when amax fits into one word  (which will
   * typically not be the case!).  The condition is bogus -- d1 is never
   * zero at the start of the loop.  There will be at most a few iterations,
   * so we don't bother collecting garbage */
  while (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3.
     * Moreover, we aren't done already, or we would have returned by now.
     * Recompute vmax */
    r = addii(v,v1);
    if (cmpii(r,bmax) > 0) return gc_long(av, 0); /* done, not found */
    vmax = get_vmax(r, lb, lbb);
    /* single-word "Lehmer", discarding the gcd or whatever it returns */
    (void)rgcduu((ulong)*int_MSW(d), (ulong)*int_MSW(d1), vmax, &xu, &xu1, &xv, &xv1, &s0);
    if (xv1 == 1) /* avoid multiplications */
    { /* re-use r = v+v1 computed above */
      v = v1; v1 = r;
      r = subii(d,d1); d = d1; d1 = r;
      s = -s;
    }
    else if (xu == 0) /* and xv==1, xu1==1, xv1 > 1 */
    {
      r = subii(d, mului(xv1,d1)); d = d1; d1 = r;
      r = addii(v, mului(xv1,v1)); v = v1; v1 = r;
      s = -s;
    }
    else
    {
      r  = subii(muliu(d,xu),  muliu(d1,xv));
      d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
      r  = addii(muliu(v,xu),  muliu(v1,xv));
      v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
      if (s0 < 0) { togglesign(d); s = -s; } else togglesign(d1);
    }
    /* check whether we're done, as above.  Assert v <= bmax.
     * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
     * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise proceed.
     */
    if (cmpii(v1,bmax) > 0)
    {
      set_avma(av);
      if (cmpii(d,amax) > 0) return 0; /* done, not found */
      /* done, found */
      *a = icopy(d); setsigne(*a,-s);
      *b = icopy(v); return 1;
    }
    if (cmpii(d1,amax) <= 0)
    { /* done, found */
      set_avma(av);
      if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
      *b = icopy(v1); return 1;
    }
  } /* while */

  /* We have run into d1 == 0 before returning. This cannot happen */
  pari_err_BUG("ratlift failed to catch d1 == 0");
  return 0; /* LCOV_EXCL_LINE */
}
