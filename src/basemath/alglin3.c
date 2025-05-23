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

/********************************************************************/
/**                                                                **/
/**                         LINEAR ALGEBRA                         **/
/**                          (third part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define DEBUGLEVEL DEBUGLEVEL_mat

/*******************************************************************/
/*                                                                 */
/*                               SUM                               */
/*                                                                 */
/*******************************************************************/

GEN
vecsum(GEN v)
{
  pari_sp av = avma;
  long i, l;
  GEN p;
  if (!is_vec_t(typ(v)))
    pari_err_TYPE("vecsum", v);
  l = lg(v);
  if (l == 1) return gen_0;
  p = gel(v,1);
  if (l == 2) return gcopy(p);
  for (i=2; i<l; i++)
  {
    p = gadd(p, gel(v,i));
    if (gc_needed(av, 2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sum");
      p = gc_upto(av, p);
    }
  }
  return gc_upto(av, p);
}

/*******************************************************************/
/*                                                                 */
/*                         TRANSPOSE                               */
/*                                                                 */
/*******************************************************************/
/* A[x0,]~ */
static GEN
row_transpose(GEN A, long x0)
{
  long i, lB = lg(A);
  GEN B  = cgetg(lB, t_COL);
  for (i=1; i<lB; i++) gel(B, i) = gcoeff(A, x0, i);
  return B;
}
static GEN
row_transposecopy(GEN A, long x0)
{
  long i, lB = lg(A);
  GEN B  = cgetg(lB, t_COL);
  for (i=1; i<lB; i++) gel(B, i) = gcopy(gcoeff(A, x0, i));
  return B;
}

/* No copy*/
GEN
shallowtrans(GEN x)
{
  long i, dx, lx;
  GEN y;
  switch(typ(x))
  {
    case t_VEC: y = leafcopy(x); settyp(y,t_COL); break;
    case t_COL: y = leafcopy(x); settyp(y,t_VEC); break;
    case t_MAT:
      lx = lg(x); if (lx==1) return cgetg(1,t_MAT);
      dx = lgcols(x); y = cgetg(dx,t_MAT);
      for (i = 1; i < dx; i++) gel(y,i) = row_transpose(x,i);
      break;
    default: pari_err_TYPE("shallowtrans",x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  return y;
}

GEN
gtrans(GEN x)
{
  long i, dx, lx;
  GEN y;
  switch(typ(x))
  {
    case t_VEC: y = gcopy(x); settyp(y,t_COL); break;
    case t_COL: y = gcopy(x); settyp(y,t_VEC); break;
    case t_MAT:
      lx = lg(x); if (lx==1) return cgetg(1,t_MAT);
      dx = lgcols(x); y = cgetg(dx,t_MAT);
      for (i = 1; i < dx; i++) gel(y,i) = row_transposecopy(x,i);
      break;
    default: pari_err_TYPE("gtrans",x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                           EXTRACTION                            */
/*                                                                 */
/*******************************************************************/

static long
str_to_long(char *s, char **pt)
{
  long a = atol(s);
  while (isspace((unsigned char)*s)) s++;
  if (*s == '-' || *s == '+') s++;
  while (isdigit((unsigned char)*s) || isspace((unsigned char)*s)) s++;
  *pt = s; return a;
}

static int
get_range(char *s, long *a, long *b, long *cmpl, long lx)
{
  long max = lx - 1;

  *a = 1; *b = max;
  if (*s == '^') { *cmpl = 1; s++; } else *cmpl = 0;
  if (!*s) return 0;
  if (*s != '.')
  {
    *a = str_to_long(s, &s);
    if (*a < 0) *a += lx;
    if (*a<1 || *a>max) return 0;
  }
  if (*s == '.')
  {
    s++; if (*s != '.') return 0;
    do s++; while (isspace((unsigned char)*s));
    if (*s)
    {
      *b = str_to_long(s, &s);
      if (*b < 0) *b += lx;
      if (*b<1 || *b>max || *s) return 0;
    }
    return 1;
  }
  if (*s) return 0;
  *b = *a; return 1;
}

static int
extract_selector_ok(long lx, GEN L)
{
  long i, l;
  switch (typ(L))
  {
    case t_INT: {
      long maxj;
      if (!signe(L)) return 1;
      l = lgefint(L)-1;
      maxj = BITS_IN_LONG - bfffo(*int_MSW(L));
      return ((l-2) * BITS_IN_LONG + maxj < lx);
    }
    case t_STR: {
      long first, last, cmpl;
      return get_range(GSTR(L), &first, &last, &cmpl, lx);
    }
    case t_VEC: case t_COL:
      l = lg(L);
      for (i=1; i<l; i++)
      {
        long j = itos(gel(L,i));
        if (j>=lx || j<=0) return 0;
      }
      return 1;
    case t_VECSMALL:
      l = lg(L);
      for (i=1; i<l; i++)
      {
        long j = L[i];
        if (j>=lx || j<=0) return 0;
      }
      return 1;
  }
  return 0;
}

GEN
shallowmatextract(GEN x, GEN l1, GEN l2)
{
  long i, j, n1 = lg(l1), n2 = lg(l2);
  GEN M = cgetg(n2, t_MAT);
  for(i=1; i < n2; i++)
  {
    long ii = l2[i];
    GEN C = cgetg(n1, t_COL);
    for (j=1; j < n1; j++)
    {
      long jj = l1[j];
      gel(C, j) = gmael(x, ii, jj);
    }
    gel(M, i) = C;
  }
  return M;
}

GEN
shallowextract(GEN x, GEN L)
{
  long i,j, tl = typ(L), tx = typ(x), lx = lg(x);
  GEN y;

  switch(tx)
  {
    case t_VEC:
    case t_COL:
    case t_MAT:
    case t_VECSMALL: break;
    default: pari_err_TYPE("extract",x);

  }
  if (tl==t_INT)
  { /* extract components of x as per the bits of mask L */
    long k, l, ix, iy, maxj;
    GEN Ld;
    if (!signe(L)) return cgetg(1,tx);
    y = new_chunk(lx);
    l = lgefint(L)-1; ix = iy = 1;
    maxj = BITS_IN_LONG - bfffo(*int_MSW(L));
    if ((l-2) * BITS_IN_LONG + maxj >= lx)
      pari_err_TYPE("vecextract [mask too large]", L);
    for (k = 2, Ld = int_LSW(L); k < l; k++, Ld = int_nextW(Ld))
    {
      ulong B = *Ld;
      for (j = 0; j < BITS_IN_LONG; j++, B >>= 1, ix++)
        if (B & 1) y[iy++] = x[ix];
    }
    { /* k = l */
      ulong B = *Ld;
      for (j = 0; j < maxj; j++, B >>= 1, ix++)
        if (B & 1) y[iy++] = x[ix];
    }
    y[0] = evaltyp(tx) | evallg(iy);
    return y;
  }
  if (tl==t_STR)
  {
    char *s = GSTR(L);
    long first, last, cmpl, d;
    if (! get_range(s, &first, &last, &cmpl, lx))
      pari_err_TYPE("vecextract [incorrect range]", L);
    if (lx == 1) return cgetg(1,tx);
    d = last - first;
    if (cmpl)
    {
      if (d >= 0)
      {
        y = cgetg(lx - (1+d),tx);
        for (j=1; j<first; j++) gel(y,j) = gel(x,j);
        for (i=last+1; i<lx; i++,j++) gel(y,j) = gel(x,i);
      }
      else
      {
        y = cgetg(lx - (1-d),tx);
        for (j=1,i=lx-1; i>first; i--,j++) gel(y,j) = gel(x,i);
        for (i=last-1; i>0; i--,j++) gel(y,j) = gel(x,i);
      }
    }
    else
    {
      if (d >= 0)
      {
        y = cgetg(d+2,tx);
        for (i=first,j=1; i<=last; i++,j++) gel(y,j) = gel(x,i);
      }
      else
      {
        y = cgetg(2-d,tx);
        for (i=first,j=1; i>=last; i--,j++) gel(y,j) = gel(x,i);
      }
    }
    return y;
  }

  if (is_vec_t(tl))
  {
    long ll=lg(L); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = itos(gel(L,i));
      if (j<=0) pari_err_COMPONENT("vecextract","<=",gen_0,stoi(j));
      if (j>=lx) pari_err_COMPONENT("vecextract",">=",stoi(lx),stoi(j));
      gel(y,i) = gel(x,j);
    }
    return y;
  }
  if (tl == t_VECSMALL)
  {
    long ll=lg(L); y=cgetg(ll,tx);
    for (i=1; i<ll; i++)
    {
      j = L[i];
      if (j<=0) pari_err_COMPONENT("vecextract","<=",gen_0,stoi(j));
      if (j>=lx) pari_err_COMPONENT("vecextract",">=",stoi(lx),stoi(j));
      gel(y,i) = gel(x,j);
    }
    return y;
  }
  pari_err_TYPE("vecextract [mask]", L);
  return NULL; /* LCOV_EXCL_LINE */
}

/* does the component selector l select 0 component ? */
static int
select_0(GEN l)
{
  switch(typ(l))
  {
    case t_INT:
      return (!signe(l));
    case t_VEC: case t_COL: case t_VECSMALL:
      return (lg(l) == 1);
  }
  return 0;
}

GEN
extract0(GEN x, GEN l1, GEN l2)
{
  pari_sp av = avma, av2;
  GEN y;
  if (! l2)
  {
    y = shallowextract(x, l1);
    if (lg(y) == 1 || typ(y) == t_VECSMALL) return y;
    av2 = avma;
    y = gcopy(y);
  }
  else
  {
    if (typ(x) != t_MAT) pari_err_TYPE("extract",x);
    y = shallowextract(x,l2);
    if (select_0(l1)) { set_avma(av); return zeromat(0, lg(y)-1); }
    if (lg(y) == 1 && lg(x) > 1)
    {
      if (!extract_selector_ok(lgcols(x), l1))
        pari_err_TYPE("vecextract [incorrect mask]", l1);
      retgc_const(av, cgetg(1, t_MAT));
    }
    y = shallowextract(shallowtrans(y), l1);
    av2 = avma;
    y = gtrans(y);
  }
  stackdummy(av, av2);
  return y;
}

static long
vecslice_parse_arg(long lA, long *y1, long *y2, long *skip)
{
  *skip=0;
  if (*y1==LONG_MAX)
  {
    if (*y2!=LONG_MAX)
    {
      if (*y2<0) *y2 += lA;
      if (*y2<0 || *y2==LONG_MAX || *y2>=lA)
        pari_err_DIM("_[..]");
      *skip=*y2;
    }
    *y1 = 1; *y2 = lA-1;
  }
  else if (*y2==LONG_MAX) *y2 = *y1;
  if (*y1<=0) *y1 += lA;
  if (*y2<0) *y2 += lA;
  if (*y1<=0 || *y1>*y2+1 || *y2>=lA) pari_err_DIM("_[..]");
  return *y2 - *y1 + 2 - !!*skip;
}

static GEN
vecslice_i(GEN A, long t, long lB, long y1, long skip)
{
  GEN B = cgetg(lB, t);
  long i;
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) { i--; continue; }
    gel(B,i) = gcopy(gel(A,y1));
  }
  return B;
}

static GEN
rowslice_i(GEN A, long lB, long x1, long y1, long skip)
{
  GEN B = cgetg(lB, t_VEC);
  long i;
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) { i--; continue; }
    gel(B,i) = gcopy(gcoeff(A,x1,y1));
  }
  return B;
}

static GEN
rowsmallslice_i(GEN A, long lB, long x1, long y1, long skip)
{
  GEN B = cgetg(lB, t_VECSMALL);
  long i;
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) { i--; continue; }
    B[i] = coeff(A,x1,y1);
  }
  return B;
}

static GEN
vecsmallslice_i(GEN A, long t, long lB, long y1, long skip)
{
  GEN B = cgetg(lB, t);
  long i;
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) { i--; continue; }
    B[i] = A[y1];
  }
  return B;
}
GEN
vecslice0(GEN A, long y1, long y2)
{
  long skip, lB, t = typ(A);
  switch(t)
  {
    case t_VEC: case t_COL:
      lB = vecslice_parse_arg(lg(A), &y1, &y2, &skip);
      return vecslice_i(A, t,lB,y1,skip);
    case t_VECSMALL:
      lB = vecslice_parse_arg(lg(A), &y1, &y2, &skip);
      return vecsmallslice_i(A, t,lB,y1,skip);
    case t_LIST:
      if (list_typ(A) == t_LIST_RAW)
      {
        GEN y, z = list_data(A);
        long l = z? lg(z): 1;
        lB = vecslice_parse_arg(l, &y1, &y2, &skip);
        y = mklist(); if (!z) return y;
        list_data(y) = vecslice_i(z, t_VEC,lB,y1,skip);
        return y;
      }
    default:
      pari_err_TYPE("_[_.._]",A);
      return NULL;/*LCOV_EXCL_LINE*/
  }
}

GEN
matslice0(GEN A, long x1, long x2, long y1, long y2)
{
  GEN B;
  long i, lB, lA = lg(A), rA, t, skip, rskip, rlB;
  long is_col = y1!=LONG_MAX && y2==LONG_MAX;
  long is_row = x1!=LONG_MAX && x2==LONG_MAX;
  GEN (*slice)(GEN A, long t, long lB, long y1, long skip);
  if (typ(A)!=t_MAT) pari_err_TYPE("_[_.._,_.._]",A);
  lB = vecslice_parse_arg(lA, &y1, &y2, &skip);
  if (is_col) return vecslice0(gel(A, y1), x1, x2);
  rA = lg(A)==1 ? 1: lgcols(A);
  rlB = vecslice_parse_arg(rA, &x1, &x2, &rskip);
  t = lg(A)==1 ? t_COL: typ(gel(A,1));
  if (is_row) return t == t_COL ? rowslice_i(A, lB, x1, y1, skip):
                                  rowsmallslice_i(A, lB, x1, y1, skip);
  slice = t == t_COL? &vecslice_i: &vecsmallslice_i;

  B = cgetg(lB, t_MAT);
  for (i=1; i<lB; i++, y1++)
  {
    if (y1 == skip) { i--; continue; }
    gel(B,i) = slice(gel(A,y1),t,rlB, x1, rskip);
  }
  return B;
}

GEN
vecrange(GEN a, GEN b)
{
  GEN y;
  long i, l;
  if (typ(a)!=t_INT) pari_err_TYPE("[_.._]",a);
  if (typ(b)!=t_INT) pari_err_TYPE("[_.._]",b);
  if (cmpii(a,b)>0) return cgetg(1,t_VEC);
  l = itos(subii(b,a))+1;
  a = setloop(a);
  y = cgetg(l+1, t_VEC);
  for (i=1; i<=l; a = incloop(a), i++) gel(y,i) = icopy(a);
  return y;
}

GEN
vecrangess(long a, long b)
{
  GEN y;
  long i, l;
  if (a>b) return cgetg(1,t_VEC);
  l = b-a+1;
  y = cgetg(l+1, t_VEC);
  for (i=1; i<=l; a++, i++) gel(y,i) = stoi(a);
  return y;
}

GEN
genindexselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  long l, i, lv;
  GEN v, z;
  pari_sp av;
  switch(typ(A))
  {
    case t_LIST:
      z = list_data(A);
      l = z? lg(z): 1;
      if (list_typ(A)==t_LIST_MAP)
      {
        av = avma;
        return gc_GEN(av, mapselect_shallow(E, f, A));
      }
      break;
    case t_VEC: case t_COL: case t_MAT:
      l = lg(A);
      z = A;
      break;
    default:
      pari_err_TYPE("select",A);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  v = cgetg(l, t_VECSMALL);
  av = avma;
  clone_lock(A);
  for (i = lv = 1; i < l; i++) {
    if (f(E, gel(z,i))) v[lv++] = i;
    set_avma(av);
  }
  clone_unlock_deep(A); fixlg(v, lv); return v;
}
static GEN
extract_copy(GEN A, GEN v)
{
  long i, l = lg(v);
  GEN B = cgetg(l, typ(A));
  for (i = 1; i < l; i++) gel(B,i) = gcopy(gel(A,v[i]));
  return B;
}
/* as genselect, but treat A [ t_VEC,t_COL, or t_MAT] as a t_VEC */
GEN
vecselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  GEN v;
  clone_lock(A);
  v = genindexselect(E, f, A);
  A = extract_copy(A, v); settyp(A, t_VEC);
  clone_unlock_deep(A); return A;
}
GEN
genselect(void *E, long (*f)(void* E, GEN x), GEN A)
{
  pari_sp av  = avma;
  GEN y, z, v;/* v left on stack for efficiency */
  clone_lock(A);
  switch(typ(A))
  {
    case t_LIST:
      z = list_data(A);
      if (!z) y = mklist();
      else
      {
        if (list_typ(A)==t_LIST_MAP)
        {
          long i, l = z? lg(z): 1, lv=1;
          GEN v1 = cgetg(l, t_COL);
          GEN v2 = cgetg(l, t_COL);
          for (i = lv = 1; i < l; i++) {
            if (f(E, gmael3(z,i,1,2)))
           {
             gel(v1,lv) = gmael3(z,i,1,1);
             gel(v2,lv) = gmael3(z,i,1,2);
             lv++;
           }
          }
          fixlg(v1, lv); fixlg(v2, lv); y = gtomap(mkmat2(v1,v2));
        }
        else
        {
          GEN B;
          y = cgetg(3, t_LIST);
          v = genindexselect(E, f, z);
          B = extract_copy(z, v);
          y[1] = lg(B)-1;
          list_data(y) = B;
        }
      }
      break;
    case t_VEC: case t_COL: case t_MAT:
      v = genindexselect(E, f, A);
      y = extract_copy(A, v);
      break;
    default:
      pari_err_TYPE("select",A);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  clone_unlock_deep(A); return gc_upto(av, y);
}

static void
check_callgen1(GEN f, const char *s)
{
  if (typ(f) != t_CLOSURE || closure_is_variadic(f)  || closure_arity(f) < 1)
    pari_err_TYPE(s, f);
}

GEN
select0(GEN f, GEN x, long flag)
{
  check_callgen1(f, "select");
  switch(flag)
  {
    case 0: return genselect((void *) f, gp_callbool, x);
    case 1: return genindexselect((void *) f, gp_callbool, x);
    default: pari_err_FLAG("select");
             return NULL;/*LCOV_EXCL_LINE*/
  }
}

GEN
parselect(GEN C, GEN D, long flag)
{
  pari_sp av, av2;
  long lv, l = lg(D), i, pending = 0, workid;
  GEN V, done;
  struct pari_mt pt;
  check_callgen1(C, "parselect");
  if (!is_vec_t(typ(D))) pari_err_TYPE("parselect",D);
  V = cgetg(l, t_VECSMALL); av = avma;
  mt_queue_start_lim(&pt, C, l-1);
  av2 = avma;
  for (i=1; i<l || pending; i++)
  {
    mt_queue_submit(&pt, i, i<l? mkvec(gel(D,i)): NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done) V[workid] = !gequal0(done);
    set_avma(av2);
  }
  mt_queue_end(&pt);
  set_avma(av);
  for (lv=1, i=1; i<l; i++)
    if (V[i]) V[lv++]=i;
  fixlg(V, lv);
  return flag? V: extract_copy(D, V);
}

GEN
veccatapply(void *E, GEN (*f)(void*, GEN), GEN x)
{
  pari_sp av = avma;
  GEN v = vecapply(E, f, x);
  return lg(v) == 1? v: gc_GEN(av, shallowconcat1(v));
}

static GEN
ser_apply(void *E, GEN (*f)(void*, GEN), GEN x)
{ pari_APPLY_ser(f(E, gel(x,i))); }
static GEN
RgX_apply(void *E, GEN (*f)(void*, GEN), GEN x)
{ pari_APPLY_pol(f(E, gel(x,i))); }
static GEN
RgV_apply(void *E, GEN (*f)(void*, GEN), GEN x)
{ pari_APPLY_same( f(E, gel(x,i)) ); }
static GEN
RgM_apply(void *E, GEN (*f)(void*, GEN), GEN x)
{ pari_APPLY_same( RgV_apply(E,f,gel(x,i)) ); }

static GEN
map_apply_i(void *E, GEN (*f)(void*, GEN), GEN x)
{ retmkvec2(mkvec2(gcopy(gmael(x,1,1)), f(E, gmael(x,1,2))),
            gcopy(gel(x, 2))); }
static GEN
map_apply(void *E, GEN (*f)(void* E, GEN x), GEN x)
{ pari_APPLY_same(map_apply_i(E, f, gel(x,i))); }

/* as genapply, but treat A [ t_VEC,t_COL, or t_MAT] as a t_VEC */
GEN
vecapply(void *E, GEN (*f)(void* E, GEN x), GEN x)
{
  GEN y;
  clone_lock(x); y = RgV_apply(E,f,x);
  clone_unlock_deep(x); settyp(y, t_VEC); return y;
}
GEN
genapply(void *E, GEN (*f)(void* E, GEN x), GEN x)
{
  long tx = typ(x);
  GEN y, z;

  if (is_scalar_t(tx)) return f(E, x);
  clone_lock(x);
  switch(tx) {
    case t_POL: y = RgX_apply(E,f,x); break;
    case t_SER:
      y = ser_isexactzero(x)? gcopy(x): ser_apply(E,f,x);
      break;
    case t_LIST:
      {
        long t = list_typ(x);
        z = list_data(x);
        if (!z)
          y = mklist_typ(t);
        else
        {
          y = cgetg(3, t_LIST);
          y[1] = evaltyp(t)|_evallg(lg(z)-1);
          switch(t)
          {
            case t_LIST_RAW: list_data(y) = RgV_apply(E,f,z); break;
            case t_LIST_MAP: list_data(y) = map_apply(E,f,z); break;
          }
        }
      }
      break;
    case t_MAT: y = RgM_apply(E, f, x); break;
    case t_VEC: case t_COL: y = RgV_apply(E,f,x); break;
    default:
      pari_err_TYPE("apply",x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  clone_unlock_deep(x); return y;
}

GEN
apply0(GEN f, GEN x)
{
  check_callgen1(f, "apply");
  return genapply((void *) f, gp_call, x);
}

GEN
vecselapply(void *Epred, long (*pred)(void* E, GEN x), void *Efun,
                         GEN (*fun)(void* E, GEN x), GEN A)
{
  GEN y;
  long i, l = lg(A), nb=1;
  clone_lock(A); y = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
    if (pred(Epred, gel(A,i))) gel(y,nb++) = fun(Efun, gel(A,i));
  fixlg(y,nb); clone_unlock_deep(A); return y;
}

GEN
veccatselapply(void *Epred, long (*pred)(void* E, GEN x), void *Efun,
                            GEN (*fun)(void* E, GEN x), GEN A)
{
  pari_sp av = avma;
  GEN v = vecselapply(Epred, pred, Efun, fun, A);
  return lg(v) == 1? v: gc_GEN(av, shallowconcat1(v));
}

/* suitable for gc_upto */
GEN
parapply_slice_worker(GEN x, GEN worker)
{ pari_APPLY_same(closure_callgen1(worker, gel(x,i))); }

/* B <- {A[i] : i = r (mod m)}, 1 <= r <= m */
static void
arithprogset(GEN B, GEN A, long r, long m)
{
  long i, k, l = lg(A);
  for (k = 1, i = r; i < l; i += m, k++) gel(B, k) = gel(A, i);
  setlg(B, k);
}
GEN
gen_parapply_slice(GEN worker, GEN D, long mmin)
{
  long l, r, n = lg(D)-1, m = minss(mmin, n), pending = 0;
  GEN L = cgetg(n / m + 2, t_VEC), va = mkvec(L), V = cgetg_copy(D, &l);
  struct pari_mt pt;
  mt_queue_start_lim(&pt, worker, m);
  for (r = 1; r <= m || pending; r++)
  {
    long workid;
    GEN done;
    if (r <= m) arithprogset(L, D, r, m);
    mt_queue_submit(&pt, r, r <= m? va: NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done)
    {
      long j, k, J = lg(done)-1;
      for (j = 1, k = workid; j <= J; j++, k +=m) gel(V, k) = gel(done, j);
    }
  }
  mt_queue_end(&pt); return V;
}

GEN
gen_parapply_percent(GEN worker, GEN D, long percent)
{
  long l = lg(D), i, pending = 0, cnt = 0, lper = -1, lcnt = 0;
  GEN W, V;
  struct pari_mt pt;

  if (l == 1) return cgetg(1, typ(D));
  W = cgetg(2, t_VEC);
  V = cgetg(l, typ(D));
  mt_queue_start_lim(&pt, worker, l-1);
  for (i = 1; i < l || pending; i++)
  {
    long workid;
    GEN done;
    if (i < l) gel(W,1) = gel(D,i);
    mt_queue_submit(&pt, i, i<l? W: NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done)
    {
      gel(V,workid) = done;
      if (percent && (++cnt)-lcnt>=percent)
      {
        long per = (long)(cnt*100./(l-1));
        lcnt = cnt;
        if (per > lper) { err_printf("%ld%% ",per); lper = per; }
      }
    }
  }
  mt_queue_end(&pt); return V;
}

GEN
gen_parapply(GEN worker, GEN D)
{ return gen_parapply_percent(worker, D, 0); }

GEN
parapply(GEN C, GEN D)
{
  pari_sp av = avma;
  check_callgen1(C, "parapply");
  if (!is_vec_t(typ(D))) pari_err_TYPE("parapply",D);
  return gc_upto(av, gen_parapply(C, D));
}

GEN
genfold(void *E, GEN (*f)(void* E, GEN x, GEN y), GEN x)
{
  pari_sp av = avma;
  GEN z;
  long i, l = lg(x);
  if (!is_vec_t(typ(x))|| l==1  ) pari_err_TYPE("fold",x);
  clone_lock(x);
  z = gel(x,1);
  for (i=2; i<l; i++)
  {
    z = f(E,z,gel(x,i));
    if (gc_needed(av, 2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"fold");
      z = gc_GEN(av, z);
    }
  }
  clone_unlock_deep(x);
  return gc_GEN(av, z);
}

GEN
fold0(GEN f, GEN x)
{
  if (typ(f) != t_CLOSURE || closure_arity(f) < 2) pari_err_TYPE("fold",f);
  return genfold((void *) f, gp_call2, x);
}
/*******************************************************************/
/*                                                                 */
/*                     SCALAR-MATRIX OPERATIONS                    */
/*                                                                 */
/*******************************************************************/
GEN
gtomat(GEN x)
{
  long lx, i;
  GEN y;

  if (!x) return cgetg(1, t_MAT);
  switch(typ(x))
  {
    case t_LIST:
      if (list_typ(x)==t_LIST_MAP)
        return maptomat(x);
      x = list_data(x);
      if (!x) return cgetg(1, t_MAT);
      /* fall through */
    case t_VEC: {
      lx=lg(x); y=cgetg(lx,t_MAT);
      if (lx == 1) break;
      if (typ(gel(x,1)) == t_COL) {
        long h = lgcols(x);
        for (i=2; i<lx; i++) {
          if (typ(gel(x,i)) != t_COL || lg(gel(x,i)) != h) break;
        }
        if (i == lx) { /* matrix with h-1 rows */
          y = cgetg(lx, t_MAT);
          for (i=1 ; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
          return y;
        }
      }
      for (i=1; i<lx; i++) gel(y,i) = mkcolcopy(gel(x,i));
      break;
    }
    case t_COL:
      lx = lg(x);
      if (lx == 1) return cgetg(1, t_MAT);
      if (typ(gel(x,1)) == t_VEC) {
        long j, h = lg(gel(x,1));
        for (i=2; i<lx; i++) {
          if (typ(gel(x,i)) != t_VEC || lg(gel(x,i)) != h) break;
        }
        if (i == lx) { /* matrix with h cols */
          y = cgetg(h, t_MAT);
          for (j=1 ; j<h; j++) {
            gel(y,j) = cgetg(lx, t_COL);
            for (i=1; i<lx; i++) gcoeff(y,i,j) = gcopy(gmael(x,i,j));
          }
          return y;
        }
      }
      y = mkmatcopy(x); break;
    case t_MAT:
      y = gcopy(x); break;
    case t_QFB: {
      GEN b;
      y = cgetg(3,t_MAT); b = gmul2n(gel(x,2),-1);
      gel(y,1) = mkcol2(icopy(gel(x,1)), b);
      gel(y,2) = mkcol2(b, icopy(gel(x,3)));
      break;
    }
    default:
      y = cgetg(2,t_MAT); gel(y,1) = mkcolcopy(x);
      break;
  }
  return y;
}

/* create the diagonal matrix, whose diagonal is given by x */
GEN
diagonal(GEN x)
{
  long j, lx, tx = typ(x);
  GEN y;

  if (! is_matvec_t(tx)) return scalarmat(x,1);
  if (tx==t_MAT)
  {
    if (RgM_isdiagonal(x)) return gcopy(x);
    pari_err_TYPE("diagonal",x);
  }
  lx=lg(x); y=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    gel(y,j) = zerocol(lx-1);
    gcoeff(y,j,j) = gcopy(gel(x,j));
  }
  return y;
}
/* same, assuming x is a t_VEC/t_COL. Not memory clean. */
GEN
diagonal_shallow(GEN x)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx,t_MAT);

  for (j=1; j<lx; j++)
  {
    gel(y,j) = zerocol(lx-1);
    gcoeff(y,j,j) = gel(x,j);
  }
  return y;
}

GEN
zv_diagonal(GEN x)
{
  long j, l = lg(x), n = l-1;
  GEN y = cgetg(l,t_MAT);

  for (j = 1; j < l; j++)
  {
    gel(y,j) = zero_Flv(n);
    ucoeff(y,j,j) = uel(x,j);
  }
  return y;
}

/* compute x*diagonal(d) */
GEN
matmuldiagonal(GEN x, GEN d)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("matmuldiagonal",x);
  if (! is_vec_t(typ(d))) pari_err_TYPE("matmuldiagonal",d);
  if (lg(d) != lg(x)) pari_err_OP("operation 'matmuldiagonal'", x,d);
  pari_APPLY_same(RgC_Rg_mul(gel(x,i), gel(d,i)));
}

/* compute A*B assuming the result is a diagonal matrix */
GEN
matmultodiagonal(GEN A, GEN B)
{
  long i, j, hA, hB, lA = lg(A), lB = lg(B);
  GEN y = matid(lB-1);

  if (typ(A) != t_MAT) pari_err_TYPE("matmultodiagonal",A);
  if (typ(B) != t_MAT) pari_err_TYPE("matmultodiagonal",B);
  hA = (lA == 1)? lB: lgcols(A);
  hB = (lB == 1)? lA: lgcols(B);
  if (lA != hB || lB != hA) pari_err_OP("operation 'matmultodiagonal'", A,B);
  for (i=1; i<lB; i++)
  {
    GEN z = gen_0;
    for (j=1; j<lA; j++) z = gadd(z, gmul(gcoeff(A,i,j),gcoeff(B,j,i)));
    gcoeff(y,i,i) = z;
  }
  return y;
}

/* [m[1,1], ..., m[l,l]], internal */
GEN
RgM_diagonal_shallow(GEN m)
{
  long i, lx = lg(m);
  GEN y = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) gel(y, i) = gcoeff(m,i,i);
  return y;
}

/* same, public function */
GEN
RgM_diagonal(GEN m)
{
  long i, lx = lg(m);
  GEN y = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) gel(y,i) = gcopy(gcoeff(m,i,i));
  return y;
}
