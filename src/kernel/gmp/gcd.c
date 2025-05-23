#line 2 "../src/kernel/gmp/gcd.c"
/* Copyright (C) 2000-2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* assume y > x > 0. return y mod x */
static ulong
resiu(GEN y, ulong x)
{
  return mpn_mod_1(LIMBS(y), NLIMBS(y), x);
}

GEN
gcdii(GEN a, GEN b)
{
  long v, w;
  pari_sp av;
  GEN t;

  switch (abscmpii(a,b))
  {
    case 0: return absi(a);
    case -1: swap(a,b);
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return igcduu((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return igcduu((ulong)b[2], u);
  }
  /* larger than gcd: GC using set_avma(av) (erasing t) is valid */
  av = avma; (void)new_chunk(lgefint(b)+1); /* HACK */
  t = remii(a,b);
  if (!signe(t)) { set_avma(av); return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setabssign(a);
  w = vali(b); b = shifti(b,-w); setabssign(b);
  if (w < v) v = w;
  switch(abscmpii(a,b))
  {
    case  0: set_avma(av); a=shifti(a,v); return a;
    case -1: swap(a,b);
  }
  if (is_pm1(b)) { set_avma(av); return int2n(v); }
 {
  /* Serves two purposes: 1) mpn_gcd destroys its input and needs an extra limb
   * 2) allows us to use icopy for GC. */
  GEN res= cgeti(lgefint(a)+1);
  GEN ca = icopy_ef(a,lgefint(a)+1);
  GEN cb = icopy_ef(b,lgefint(b)+1);
  long l = mpn_gcd(LIMBS(res), LIMBS(ca), NLIMBS(ca), LIMBS(cb), NLIMBS(cb));
  res[1] = evalsigne(1)|evallgefint(l+2);
  set_avma(av); return shifti(res,v);
  }
}
