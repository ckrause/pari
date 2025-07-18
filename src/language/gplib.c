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

/*******************************************************************/
/**                                                               **/
/**            LIBRARY ROUTINES FOR PARI CALCULATOR               **/
/**                                                               **/
/*******************************************************************/
#ifdef _WIN32
#  include "../systems/mingw/pwinver.h"
#  include <windows.h>
#  include "../systems/mingw/mingw.h"
#  include <process.h>
#endif

#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                            STRINGS                             **/
/**                                                                **/
/********************************************************************/

void
pari_skip_space(char **s) {
  char *t = *s;
  while (isspace((unsigned char)*t)) t++;
  *s = t;
}
void
pari_skip_alpha(char **s) {
  char *t = *s;
  while (isalpha((unsigned char)*t)) t++;
  *s = t;
}

/*******************************************************************/
/**                                                               **/
/**                          BUFFERS                              **/
/**                                                               **/
/*******************************************************************/
static Buffer **bufstack;
static pari_stack s_bufstack;
void
pari_init_buffers(void)
{ pari_stack_init(&s_bufstack, sizeof(Buffer*), (void**)&bufstack); }

void
pop_buffer(void)
{
  if (s_bufstack.n)
    delete_buffer( bufstack[ --s_bufstack.n ] );
}

/* kill all buffers until B is met or nothing is left */
void
kill_buffers_upto(Buffer *B)
{
  while (s_bufstack.n) {
    if (bufstack[ s_bufstack.n-1 ] == B) break;
    pop_buffer();
  }
}
void
kill_buffers_upto_including(Buffer *B)
{
  while (s_bufstack.n) {
    if (bufstack[ s_bufstack.n-1 ] == B) { pop_buffer(); break; }
    pop_buffer();
  }
}

static int disable_exception_handler = 0;
#define BLOCK_EH_START                \
{                                     \
  int block=disable_exception_handler;\
  disable_exception_handler = 1;

#define BLOCK_EH_END                \
  disable_exception_handler = block;\
}
/* numerr < 0: from SIGINT */
int
gp_handle_exception(long numerr)
{
  if (disable_exception_handler)
    disable_exception_handler = 0;
  else if (GP_DATA->breakloop && cb_pari_break_loop
                              && cb_pari_break_loop(numerr))
    return 1;
  return 0;
}

/********************************************************************/
/**                                                                **/
/**                             HELP                               **/
/**                                                                **/
/********************************************************************/
void
pari_hit_return(void)
{
  int c;
  if (GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS)) return;
  BLOCK_EH_START
  pari_puts("/*-- (type RETURN to continue) --*/");
  pari_flush();
  /* if called from a readline callback, may be in a funny TTY mode */
  do c = fgetc(stdin); while (c >= 0 && c != '\n' && c != '\r');
  pari_putc('\n');
  BLOCK_EH_END
}

static int
has_ext_help(void) { return (GP_DATA->help && *GP_DATA->help); }

static int
compare_str(const void *s1, const void*s2)
{ return strcmp(*(char**)s1, *(char**)s2); }

/* Print all elements of list in columns, pausing every nbli lines
 * if nbli is nonzero. list is a NULL terminated list of function names */
void
print_fun_list(char **list, long nbli)
{
  long i=0, j=0, maxlen=0, nbcol,len, w = term_width();
  char **l;

  while (list[i]) i++;
  qsort (list, i, sizeof(char *), compare_str);

  for (l=list; *l; l++)
  {
    len = strlen(*l);
    if (len > maxlen) maxlen=len;
  }
  maxlen++; nbcol= w / maxlen;
  if (nbcol * maxlen == w) nbcol--;
  if (!nbcol) nbcol = 1;

  pari_putc('\n'); i=0;
  for (l=list; *l; l++)
  {
    pari_puts(*l); i++;
    if (i >= nbcol)
    {
      i=0; pari_putc('\n');
      if (nbli && j++ > nbli) { j = 0; pari_hit_return(); }
      continue;
    }
    len = maxlen - strlen(*l);
    while (len--) pari_putc(' ');
  }
  if (i) pari_putc('\n');
}

static const char *help_sections[] = {
  "user-defined functions (aliases, installed and user functions)",
  "PROGRAMMING under GP",
  "Standard monadic or dyadic OPERATORS",
  "CONVERSIONS and similar elementary functions",
  "functions related to COMBINATORICS",
  "basic NUMBER THEORY",
  "POLYNOMIALS and power series",
  "Vectors, matrices, LINEAR ALGEBRA and sets",
  "TRANSCENDENTAL functions",
  "SUMS, products, integrals and similar functions",
  "General NUMBER FIELDS",
  "Associative and central simple ALGEBRAS",
  "ELLIPTIC and HYPERELLIPTIC curves",
  "L-FUNCTIONS",
  "HYPERGEOMETRIC MOTIVES",
  "MODULAR FORMS",
  "MODULAR SYMBOLS",
  "GRAPHIC functions"
};

static const long MAX_SECTION = numberof(help_sections) - 1;

static void
commands(long n)
{
  long i;
  entree *ep;
  char **t_L;
  pari_stack s_L;

  pari_stack_init(&s_L, sizeof(*t_L), (void**)&t_L);
  for (i = 0; i < functions_tblsz; i++)
    for (ep = functions_hash[i]; ep; ep = ep->next)
    {
      long m;
      switch (EpVALENCE(ep))
      {
        case EpVAR:
          if (typ((GEN)ep->value) == t_CLOSURE) break;
          /* fall through */
        case EpNEW: continue;
      }
      m = ep->menu;
      if (m == n || (n < 0 && m && m <= MAX_SECTION))
        pari_stack_pushp(&s_L, (void*)ep->name);
    }
  pari_stack_pushp(&s_L, NULL);
  print_fun_list(t_L, term_height()-4);
  pari_stack_delete(&s_L);
}

void
pari_center(const char *s)
{
  pari_sp av = avma;
  long i, l = strlen(s), pad = term_width() - l;
  char *buf, *u;

  if (pad<0) pad=0; else pad >>= 1;
  u = buf = stack_malloc(l + pad + 2);
  for (i=0; i<pad; i++) *u++ = ' ';
  while (*s) *u++ = *s++;
  *u++ = '\n'; *u = 0;
  pari_puts(buf); set_avma(av);
}

static void
community(void)
{
  const char *pari_docdir;
#if defined(_WIN32)
  /* for some reason, the documentation on windows is not in datadir */
  if (paricfg_datadir[0]=='@' && paricfg_datadir[1]==0)
    pari_docdir = win32_basedir();
  else
#endif
    pari_docdir = pari_datadir;

  print_text("The PARI/GP distribution includes a reference manual, a \
tutorial, a reference card and quite a few examples. They have been installed \
in the directory ");
  pari_puts("  ");
  pari_puts(pari_docdir);
  pari_puts("\nYou can also download them from http://pari.math.u-bordeaux.fr/.\
\n\nThree mailing lists are devoted to PARI:\n\
  - pari-announce (moderated) to announce major version changes.\n\
  - pari-dev for everything related to the development of PARI, including\n\
    suggestions, technical questions, bug reports and patch submissions.\n\
  - pari-users for everything else!\n\
To subscribe, send an empty message to\n\
  <pari_list_name>-request@pari.math.u-bordeaux.fr\n\
with a Subject: field containing the word 'subscribe'.\n\n");
  print_text("An archive is kept at the WWW site mentioned above. You can also \
reach the authors at pari@math.u-bordeaux.fr (answer not guaranteed)."); }

static void
gentypes(void)
{
  pari_puts("List of the PARI types:\n\
  t_INT    : long integers     [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_REAL   : long real numbers [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_INTMOD : integermods       [ code ] [ mod  ] [ integer ]\n\
  t_FRAC   : irred. rationals  [ code ] [ num. ] [ den. ]\n\
  t_FFELT  : finite field elt. [ code ] [ cod2 ] [ elt ] [ mod ] [ p ]\n\
  t_COMPLEX: complex numbers   [ code ] [ real ] [ imag ]\n\
  t_PADIC  : p-adic numbers    [ cod1 ] [ cod2 ] [ p ] [ p^r ] [ int ]\n\
  t_QUAD   : quadratic numbers [ cod1 ] [ mod  ] [ real ] [ imag ]\n\
  t_POLMOD : poly mod          [ code ] [ mod  ] [ polynomial ]\n\
  -------------------------------------------------------------\n\
  t_POL    : polynomials       [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_SER    : power series      [ cod1 ] [ cod2 ] [ man_1 ] ... [ man_k ]\n\
  t_RFRAC  : irred. rat. func. [ code ] [ num. ] [ den. ]\n\
  t_QFB    : qfb               [ code ] [ a ] [ b ] [ c ] [ disc ]\n\
  t_VEC    : row vector        [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_COL    : column vector     [ code ] [  x_1  ] ... [  x_k  ]\n\
  t_MAT    : matrix            [ code ] [ col_1 ] ... [ col_k ]\n\
  t_LIST   : list              [ cod1 ] [ cod2 ] [ vec ]\n\
  t_STR    : string            [ code ] [ man_1 ] ... [ man_k ]\n\
  t_VECSMALL: vec. small ints  [ code ] [ x_1 ] ... [ x_k ]\n\
  t_CLOSURE: functions         [ code ] [ arity ] [ proto ] [ operand ] ... \n\
  t_ERROR  : error context     [ code ] [ errnum ] [ dat_1 ] ... [ dat_k ]\n\
  t_INFINITY: a*infinity       [ code ] [ a ]\n\
\n");
}

static void
menu_commands(void)
{
  ulong i;
  pari_puts("Help topics: for a list of relevant subtopics, type ?n for n in\n");
  for (i = 0; i <= MAX_SECTION; i++)
    pari_printf("  %2lu: %s\n", i, help_sections[i]);
  pari_printf("  %2lu: The PARI community\n", i);
  pari_puts("Also:\n\
  ? functionname (short on-line help)\n\
  ?\\             (keyboard shortcuts)\n\
  ?.             (member functions)\n");
  if (has_ext_help()) pari_puts("\
Extended help (if available):\n\
  ??             (opens the full user's manual in a dvi previewer)\n\
  ??  tutorial / refcard / libpari (tutorial/reference card/libpari manual)\n\
  ??  refcard-ell (or -lfun/-mf/-nf: specialized reference card)\n\
  ??  keyword    (long help text about \"keyword\" from the user's manual)\n\
  ??? keyword    (a propos: list of related functions).");
}

static void
slash_commands(void)
{
  pari_puts("#       : enable/disable timer\n\
##      : print time for last result\n\
\\\\      : comment up to end of line\n\
\\a {n}  : print result in raw format (readable by PARI)\n\
\\B {n}  : print result in beautified format\n\
\\c      : list all commands (same effect as ?*)\n\
\\d      : print all defaults\n\
\\e {n}  : enable/disable echo (set echo=n)\n\
\\g {n}  : set debugging level\n\
\\gf{n}  : set file debugging level\n\
\\gm{n}  : set memory debugging level\n\
\\h {m-n}: hashtable information\n\
\\l {f}  : enable/disable logfile (set logfile=f)\n\
\\m {n}  : print result in prettymatrix format\n\
\\o {n}  : set output method (0=raw, 1=prettymatrix, 2=prettyprint, 3=2-dim)\n\
\\p {n}  : change real precision\n\
\\pb{n}  : change real bit precision\n\
\\ps{n}  : change series precision\n\
\\q      : quit completely this GP session\n\
\\r {f}  : read in a file\n\
\\s      : print stack information\n\
\\t      : print the list of PARI types\n\
\\u      : print the list of user-defined functions\n\
\\um     : print the list of user-defined member functions\n\
\\uv     : print the list of user-defined variables, excluding closures\n\
\\v      : print current version of GP\n\
\\w {nf} : write to a file\n\
\\x {n}  : print complete inner structure of result\n\
\\y {n}  : disable/enable automatic simplification (set simplify=n)\n\
\\z {n}  : disable/enable doctest mode\n\
\n\
{f}=optional filename. {n}=optional integer\n");
}

static void
member_commands(void)
{
  pari_puts("\
Member functions, followed by relevant objects\n\n\
a1-a6, b2-b8, c4-c6 : coeff. of the curve.         ell\n\
area : area                                        ell\n\
bid  : big ideal                     bid,                     bnr\n\
bnf  : big number field                                   bnf,bnr\n\
clgp : class group              quad,bid,                 bnf,bnr\n\
cyc  : cyclic decomposition     quad,bid,     clgp,ell,   bnf,bnr\n\
diff, codiff: different and codifferent                nf,bnf,bnr\n\
disc : discriminant                                ell,nf,bnf,bnr,rnf\n\
e, f : inertia/residue  degree           prid\n\
fu   : fundamental units                                  bnf\n\
gen  : generators                    bid,prid,clgp,ell,   bnf,bnr,    gal\n\
group: group                                       ell,               gal\n\
index: index                                           nf,bnf,bnr\n\
j    : j-invariant                                 ell\n");
/* split: some compilers can't handle long constant strings */
  pari_puts("\
mod  : modulus                       bid,                     bnr,    gal\n\
nf   : number field                                    nf,bnf,bnr,rnf\n\
no   : number of elements       quad,bid,     clgp,ell,   bnf,bnr\n\
normfu:                         quad\n\
omega, eta: [w1,w2] and [eta1, eta2]               ell\n\
orders: relative orders of generators                                 gal\n\
p    : rational prime                    prid,     ell,nf,bnf,bnr,rnf,gal\n\
pol  : defining polynomial                             nf,bnf,bnr,    gal\n\
polabs: defining polynomial over Q                                rnf\n\
reg  : regulator                quad,                     bnf\n\
roots: roots                                       ell,nf,bnf,bnr,    gal\n\
sign,r1,r2 : signature                                 nf,bnf,bnr\n\
t2   : t2 matrix                                       nf,bnf,bnr\n\
tate : Tate's [u^2, u, q, [a,b], L, Ei]            ell\n\
tu   : torsion unit and its order                         bnf\n\
zk   : integral basis                                  nf,bnf,bnr,rnf\n\
zkst : structure of (Z_K/m)*         bid,                     bnr\n");
}

#define QUOTE "_QUOTE"
#define DOUBQUOTE "_DOUBQUOTE"
#define BACKQUOTE "_BACKQUOTE"

static char *
_cat(char *s, const char *t)
{
  *s = 0; strcat(s,t); return s + strlen(t);
}

static char *
filter_quotes(const char *s)
{
  int i, l = strlen(s);
  int quote = 0;
  int backquote = 0;
  int doubquote = 0;
  char *str, *t;

  for (i=0; i < l; i++)
    switch(s[i])
    {
      case '\'': quote++; break;
      case '`' : backquote++; break;
      case '"' : doubquote++;
    }
  str = (char*)pari_malloc(l + quote * (strlen(QUOTE)-1)
                          + doubquote * (strlen(DOUBQUOTE)-1)
                          + backquote * (strlen(BACKQUOTE)-1) + 1);
  t = str;
  for (i=0; i < l; i++)
    switch(s[i])
    {
      case '\'': t = _cat(t, QUOTE); break;
      case '`' : t = _cat(t, BACKQUOTE); break;
      case '"' : t = _cat(t, DOUBQUOTE); break;
      default: *t++ = s[i];
    }
  *t = 0; return str;
}

static int
nl_read(char *s) { size_t l = strlen(s); return s[l-1] == '\n'; }

/* query external help program for s. num < 0 [keyword] or chapter number */
static void
external_help(const char *s, long num)
{
  long nbli = term_height()-3, li = 0;
  char buf[256], *str;
  const char *opt = "", *ar = "";
  char *t, *help = GP_DATA->help;
  pariFILE *z;
  FILE *f;
  if (cb_pari_long_help) { cb_pari_long_help(s, num); return; }

  if (!has_ext_help()) pari_err(e_MISC,"no external help program");
  t = filter_quotes(s);
  if (num < 0)
    opt = "-k";
  else if (t[strlen(t)-1] != '@')
    ar = stack_sprintf("@%d",num);
#ifdef _WIN32
  if (*help == '@')
  {
    const char *basedir = win32_basedir();
    help = stack_sprintf("%c:& cd %s & %s", *basedir, basedir, help+1);
  }
#endif
  str = stack_sprintf("%s -fromgp %s %c%s%s%c",
                      help, opt, SHELL_Q, t, ar, SHELL_Q);
  z = try_pipe(str,0); f = z->file;
  pari_free(t);
  while (fgets(buf, numberof(buf), f))
  {
    if (!strncmp("ugly_kludge_done",buf,16)) break;
    pari_puts(buf);
    if (nl_read(buf) && ++li > nbli) { pari_hit_return(); li = 0; }
  }
  pari_fclose(z);
}

const char **
gphelp_keyword_list(void)
{
  static const char *L[]={
  "operator",
  "libpari",
  "member",
  "integer",
  "real",
  "readline",
  "refcard",
  "refcard-nf",
  "refcard-ell",
  "refcard-mf",
  "refcard-lfun",
  "tutorial",
  "tutorial-mf",
  "mf",
  "nf",
  "bnf",
  "bnr",
  "ell",
  "rnf",
  "hgm",
  "HGM",
  "ideal",
  "idele",
  "CFT",
  "bid",
  "modulus",
  "prototype",
  "Lmath",
  "Ldata",
  "Linit",
  "character",
  "sums",
  "products",
  "integrals",
  "gchar",
  "grossencharacter",
  "Grossencharacter",
  NULL};
  return L;
}

static int
ok_external_help(char **s)
{
  const char **L;
  long n;
  if (!**s) return 1;
  if (!isalpha((unsigned char)**s)) return 3; /* operator or section number */
  if (!strncmp(*s,"t_",2)) { *s += 2; return 2; } /* type name */

  L = gphelp_keyword_list();
  for (n=0; L[n]; n++)
    if (!strcmp(*s,L[n])) return 3;
  return 0;
}

static void
cut_trailing_garbage(char *s)
{
  char c;
  while ( (c = *s++) )
  {
    if (c == '\\' && ! *s++) return; /* gobble next char, return if none. */
    if (!is_keyword_char(c) && c != '@') { s[-1] = 0; return; }
  }
}

static void
digit_help(char *s, long flag)
{
  long n = atoi(s);
  if (n < 0 || n > MAX_SECTION+4)
    pari_err(e_SYNTAX,"no such section in help: ?",s,s);
  if (n == MAX_SECTION+1)
    community();
  else if (flag & h_LONG)
    external_help(s,3);
  else
    commands(n);
  return;
}

long
pari_community(void)
{
  return MAX_SECTION+1;
}

static void
simple_help(const char *s1, const char *s2) { pari_printf("%s: %s\n", s1, s2); }

static void
default_help(char *s, long flag)
{
  if (flag & h_LONG)
    external_help(stack_strcat("se:def,",s),3);
  else
    simple_help(s,"default");
}

static void
help(const char *s0, int flag)
{
  const long long_help = flag & h_LONG;
  long n;
  entree *ep;
  char *s = get_sep(s0);

  if (isdigit((unsigned char)*s)) { digit_help(s,flag); return; }
  if (flag & h_APROPOS) { external_help(s,-1); return; }
  /* Get meaningful answer on '\ps 5' (e.g. from <F1>) */
  if (*s == '\\' && isalpha((unsigned char)*(s+1)))
  { char *t = s+1; pari_skip_alpha(&t); *t = '\0'; }
  if (isalpha((unsigned char)*s))
  {
    char *t = s;
    if (!strncmp(s, "default", 7))
    { /* special-case ?default(dft_name), e.g. default(log) */
      t += 7; pari_skip_space(&t);
      if (*t == '(')
      {
        t++; pari_skip_space(&t);
        cut_trailing_garbage(t);
        if (pari_is_default(t)) { default_help(t,flag); return; }
      }
    }
    if (!strncmp(s, "refcard-", 8)) t += 8;
    else if (!strncmp(s, "tutorial-", 9)) t += 9;
    if (strncmp(s, "se:", 3)) cut_trailing_garbage(t);
  }

  if (long_help && (n = ok_external_help(&s))) { external_help(s,n); return; }
  switch (*s)
  {
    case '*' : commands(-1); return;
    case '\0': menu_commands(); return;
    case '\\': slash_commands(); return;
    case '.' : member_commands(); return;
  }
  ep = is_entry(s);
  if (!ep)
  {
    if (pari_is_default(s))
      default_help(s,flag);
    else if (long_help)
      external_help(s,3);
    else if (!cb_pari_whatnow || !cb_pari_whatnow(pariOut, s,1))
      simple_help(s,"unknown identifier");
    return;
  }

  if (EpVALENCE(ep) == EpALIAS)
  {
    pari_printf("%s is aliased to:\n\n",s);
    ep = do_alias(ep);
  }
  switch(EpVALENCE(ep))
  {
    case EpVAR:
      if (!ep->help)
      {
        if (typ((GEN)ep->value)!=t_CLOSURE)
          simple_help(s, "user defined variable");
        else
        {
          GEN str = closure_get_text((GEN)ep->value);
          if (typ(str) == t_VEC)
            pari_printf("%s =\n  %Ps\n", ep->name, ep->value);
        }
        return;
      }
      break;

    case EpINSTALL:
      if (!ep->help) { simple_help(s, "installed function"); return; }
      break;

    case EpNEW:
      if (!ep->help) { simple_help(s, "new identifier"); return; };
      break;

    default: /* built-in function */
      if (!ep->help) pari_err_BUG("gp_help (no help found)"); /*paranoia*/
      if (long_help) { external_help(ep->name,3); return; }
  }
  print_text(ep->help);
}

void
gp_help(const char *s, long flag)
{
  pari_sp av = avma;
  if ((flag & h_RL) == 0)
  {
    if (*s == '?') { flag |= h_LONG; s++; }
    if (*s == '?') { flag |= h_APROPOS; s++; }
  }
  term_color(c_HELP); help(s,flag); term_color(c_NONE);
  if ((flag & h_RL) == 0) pari_putc('\n');
  set_avma(av);
}

/********************************************************************/
/**                                                                **/
/**                         GP HEADER                              **/
/**                                                                **/
/********************************************************************/
static char *
what_readline(void)
{
#ifdef READLINE
  const char *v = READLINE;
  char *s = stack_malloc(3 + strlen(v) + 8);
  (void)sprintf(s, "v%s %s", v, GP_DATA->use_readline? "enabled": "disabled");
  return s;
#else
  return (char*)"not compiled in";
#endif
}

static char *
what_cc(void)
{
  char *s;
#ifdef GCC_VERSION
#  ifdef __cplusplus
  s = stack_malloc(6 + strlen(GCC_VERSION) + 1);
  (void)sprintf(s, "(C++) %s", GCC_VERSION);
#  else
  s = stack_strdup(GCC_VERSION);
#  endif
#else
#  ifdef _MSC_VER
  s = stack_malloc(32);
  (void)sprintf(s, "MSVC-%i", _MSC_VER);
#  else
  s = NULL;
#  endif
#endif
  return s;
}

static char *
convert_time(char *s, long delay)
{
  /* Do not do month and year: ambiguous definition and overflows 32 bits. */
  if (delay >= 86400000)
  {
    sprintf(s, "%ldd, ", delay / 86400000); s+=strlen(s);
    delay %= 86400000;
  }
  if (delay >= 3600000)
  {
    sprintf(s, "%ldh, ", delay / 3600000); s+=strlen(s);
    delay %= 3600000;
  }
  if (delay >= 60000)
  {
    sprintf(s, "%ldmin, ", delay / 60000); s+=strlen(s);
    delay %= 60000;
  }
  if (delay >= 1000)
  {
    sprintf(s, "%ld,", delay / 1000); s+=strlen(s);
    delay %= 1000;
    if (delay < 100)
    {
      sprintf(s, "%s", (delay<10)? "00": "0");
      s+=strlen(s);
    }
  }
  sprintf(s, "%ld ms", delay); s+=strlen(s);
  return s;
}

/* Format a time of 'delay' ms */
const char *
gp_format_time(long delay)
{
  char *buf = stack_malloc(64), *s = buf;
  term_get_color(s, c_TIME);
  s = convert_time(s + strlen(s), delay);
  term_get_color(s, c_NONE); return buf;
}

GEN
strtime(long delay)
{
  long n = nchar2nlong(64);
  GEN x = cgetg(n+1, t_STR);
  char *buf = GSTR(x), *t = buf + 64, *s = convert_time(buf, delay);
  s++; while (s < t) *s++ = 0; /* pacify valgrind */
  return x;
}

/********************************************************************/
/*                                                                  */
/*                              GPRC                                */
/*                                                                  */
/********************************************************************/
/* LOCATE GPRC */
static void
err_gprc(const char *s, char *t, char *u)
{
  err_printf("\n");
  pari_err(e_SYNTAX,s,t,u);
}

/* return $HOME or the closest we can find */
static const char *
get_home(int *free_it)
{
  char *drv, *pth = os_getenv("HOME");
  if (pth) return pth;
  if ((drv = os_getenv("HOMEDRIVE"))
   && (pth = os_getenv("HOMEPATH")))
  { /* looks like WinNT */
    char *buf = (char*)pari_malloc(strlen(pth) + strlen(drv) + 1);
    sprintf(buf, "%s%s",drv,pth);
    *free_it = 1; return buf;
  }
  pth = pari_get_homedir("");
  return pth? pth: ".";
}

static FILE *
gprc_chk(const char *s)
{
  FILE *f = fopen(s, "r");
  if (f && !(GP_DATA->flags & gpd_QUIET)) err_printf("Reading GPRC: %s\n", s);
  return f;
}

/* Look for [._]gprc: $GPRC, then in $HOME, ., /etc, pari_datadir */
static FILE *
gprc_get(void)
{
  FILE *f = NULL;
  const char *gprc = os_getenv("GPRC");
  if (gprc) f = gprc_chk(gprc);
  if (!f)
  {
    int free_it = 0;
    const char *home = get_home(&free_it);
    char *str, *s, c;
    long l;
    l = strlen(home); c = home[l-1];
    /* + "/gprc.txt" + \0*/
    str = strcpy((char*)pari_malloc(l+10), home);
    if (free_it) pari_free((void*)home);
    s = str + l;
    if (c != '/' && c != '\\') *s++ = '/';
#ifndef _WIN32
    strcpy(s, ".gprc");
#else
    strcpy(s, "gprc.txt");
#endif
    f = gprc_chk(str); /* in $HOME */
    if (!f) f = gprc_chk(s); /* in . */
#ifndef _WIN32
    if (!f) f = gprc_chk("/etc/gprc");
#else
    if (!f)  /* in basedir */
    {
      const char *basedir = win32_basedir();
      char *t = (char *) pari_malloc(strlen(basedir)+strlen(s)+2);
      sprintf(t, "%s/%s", basedir, s);
      f = gprc_chk(t); free(t);
    }
#endif
    pari_free(str);
  }
  return f;
}

/* PREPROCESSOR */

static ulong
read_uint(char **s)
{
  long v = atol(*s);
  if (!isdigit((unsigned char)**s)) err_gprc("not an integer", *s, *s);
  while (isdigit((unsigned char)**s)) (*s)++;
  return v;
}
static ulong
read_dot_uint(char **s)
{
  if (**s != '.') return 0;
  (*s)++; return read_uint(s);
}
/* read a.b.c */
static long
read_version(char **s)
{
  long a, b, c;
  a = read_uint(s);
  b = read_dot_uint(s);
  c = read_dot_uint(s);
  return PARI_VERSION(a,b,c);
}

static int
get_preproc_value(char **s)
{
  if (!strncmp(*s,"EMACS",5)) {
    *s += 5;
    return GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS);
  }
  if (!strncmp(*s,"READL",5)) {
    *s += 5;
    return GP_DATA->use_readline;
  }
  if (!strncmp(*s,"VERSION",7)) {
    int less = 0, orequal = 0;
    long d;
    *s += 7;
    switch(**s)
    {
      case '<': (*s)++; less = 1; break;
      case '>': (*s)++; less = 0; break;
      default: return -1;
    }
    if (**s == '=') { (*s)++; orequal = 1; }
    d = paricfg_version_code - read_version(s);
    if (!d) return orequal;
    return less? (d < 0): (d > 0);
  }
  if (!strncmp(*s,"BITS_IN_LONG",12)) {
    *s += 12;
    if ((*s)[0] == '=' && (*s)[1] == '=')
    {
      *s += 2;
      return BITS_IN_LONG == read_uint(s);
    }
  }
  return -1;
}

/* PARSE GPRC */

/* 1) replace next separator by '\0' (t must be writable)
 * 2) return the next expression ("" if none)
 * see get_sep() */
static char *
next_expr(char *t)
{
  int outer = 1;
  char *s = t;

  for(;;)
  {
    char c;
    switch ((c = *s++))
    {
      case '"':
        if (outer || (s >= t+2 && s[-2] != '\\')) outer = !outer;
        break;
      case '\0':
        return (char*)"";
      default:
        if (outer && c == ';') { s[-1] = 0; return s; }
    }
  }
}

Buffer *
filtered_buffer(filtre_t *F)
{
  Buffer *b = new_buffer();
  init_filtre(F, b);
  pari_stack_pushp(&s_bufstack, (void*)b);
  return b;
}

/* parse src of the form s=t (or s="t"), set *ps to s, and *pt to t.
 * modifies src (replaces = by \0) */
void
parse_key_val(char *src, char **ps, char **pt)
{
  char *s_end, *t;
  t = src; while (*t && *t != '=') t++;
  if (*t != '=') err_gprc("missing '='",t,src);
  s_end = t;
  t++;
  if (*t == '"') (void)pari_translate_string(t, t, src);
  *s_end = 0; *ps = src; *pt = t;
}
/* parse src of the form (s,t) (or "s", or "t"), set *ps to s, and *pt to t. */
static void
parse_key_val_paren(char *src, char **ps, char **pt)
{
  char *s, *t, *s_end, *t_end;
  s = t = src + 1; while (*t && *t != ',') t++;
  if (*t != ',') err_gprc("missing ','",t,src);
  s_end = t;
  t++; while (*t && *t != ')') t++;
  if (*t != ')') err_gprc("missing ')'",t,src);
  if (t[1])  err_gprc("unexpected character",t+1,src);
  t_end = t; t = s_end + 1;
  if (*t == '"') (void)pari_translate_string(t, t, src);
  if (*s == '"') (void)pari_translate_string(s, s, src);
  *s_end = 0; *t_end = 0; *ps = s; *pt = t;
}

void
gp_initrc(pari_stack *p_A)
{
  FILE *file = gprc_get();
  Buffer *b;
  filtre_t F;
  VOLATILE long c = 0;
  jmp_buf *env;
  pari_stack s_env;

  if (!file) return;
  b = filtered_buffer(&F);
  pari_stack_init(&s_env, sizeof(*env), (void**)&env);
  (void)pari_stack_new(&s_env);
  for(;;)
  {
    char *nexts, *s, *t;
    if (setjmp(env[s_env.n-1])) err_printf("...skipping line %ld.\n", c);
    c++;
    if (!get_line_from_file(NULL,&F,file)) break;
    s = b->buf;
    if (*s == '#')
    { /* preprocessor directive */
      int z, NOT = 0;
      s++;
      if (strncmp(s,"if",2)) err_gprc("unknown directive",s,b->buf);
      s += 2;
      if (!strncmp(s,"not",3)) { NOT = !NOT; s += 3; }
      if (*s == '!')           { NOT = !NOT; s++; }
      t = s;
      z = get_preproc_value(&s);
      if (z < 0) err_gprc("unknown preprocessor variable",t,b->buf);
      if (NOT) z = !z;
      if (!*s)
      { /* make sure at least an expr follows the directive */
        if (!get_line_from_file(NULL,&F,file)) break;
        s = b->buf;
      }
      if (!z) continue; /* dump current line */
    }
    /* parse line */
    for ( ; *s; s = nexts)
    {
      nexts = next_expr(s);
      if (!strncmp(s,"read",4) && (s[4] == ' ' || s[4] == '\t' || s[4] == '"'))
      { /* read file */
        s += 4;
        t = (char*)pari_malloc(strlen(s) + 1);
        if (*s == '"') (void)pari_translate_string(s, t, s-4); else strcpy(t,s);
        pari_stack_pushp(p_A,t);
      }
      else if (!strncmp(s, "default(", 8))
      {
        s += 7; parse_key_val_paren(s, &s,&t);
        (void)setdefault(s,t,d_INITRC);
      }
      else if (!strncmp(s, "setdebug(", 9))
      {
        s += 8; parse_key_val_paren(s, &s,&t);
        setdebug(s, atol(t));
      }
      else
      { /* set default */
        parse_key_val(s, &s,&t);
        (void)setdefault(s,t,d_INITRC);
      }
    }
  }
  pari_stack_delete(&s_env);
  pop_buffer();
  if (!(GP_DATA->flags & gpd_QUIET)) err_printf("GPRC Done.\n\n");
  fclose(file);
}

void
gp_load_gprc(void)
{
  pari_stack sA;
  char **A;
  long i;
  pari_stack_init(&sA,sizeof(*A),(void**)&A);
  gp_initrc(&sA);
  for (i = 0; i < sA.n; pari_free(A[i]),i++)
  {
    pari_CATCH(CATCH_ALL) { err_printf("... skipping file '%s'\n", A[i]); }
    pari_TRY { gp_read_file(A[i]); } pari_ENDCATCH;
  }
  pari_stack_delete(&sA);
}

/********************************************************************/
/*                                                                  */
/*                             PROMPTS                              */
/*                                                                  */
/********************************************************************/
/* if prompt is coloured, tell readline to ignore the ANSI escape sequences */
/* s must be able to store 14 chars (including final \0) */
#ifdef READLINE
static void
readline_prompt_color(char *s, int c)
{
#ifdef _WIN32
  (void)s; (void)c;
#else
  *s++ = '\001'; /*RL_PROMPT_START_IGNORE*/
  term_get_color(s, c);
  s += strlen(s);
  *s++ = '\002'; /*RL_PROMPT_END_IGNORE*/
  *s = 0;
#endif
}
#endif
/* s must be able to store 14 chars (including final \0) */
static void
brace_color(char *s, int c, int force)
{
  if (disable_color || (gp_colors[c] == c_NONE && !force)) return;
#ifdef READLINE
  if (GP_DATA->use_readline)
    readline_prompt_color(s, c);
  else
#endif
    term_get_color(s, c);
}

/* strlen(prompt) + 28 chars */
static const char *
color_prompt(const char *prompt)
{
  long n = strlen(prompt);
  char *t = stack_malloc(n + 28), *s = t;
  *s = 0;
  /* escape sequences bug readline, so use special bracing (if available) */
  brace_color(s, c_PROMPT, 0);
  s += strlen(s); memcpy(s, prompt, n);
  s += n; *s = 0;
  brace_color(s, c_INPUT, 1);
  return t;
}

const char *
gp_format_prompt(const char *prompt)
{
  if (GP_DATA->flags & gpd_TEST)
    return prompt;
  else
  {
    char b[256]; /* longer is truncated */
    strftime_expand(prompt, b, sizeof(b));
    return color_prompt(b);
  }
}

/********************************************************************/
/*                                                                  */
/*                           GP MAIN LOOP                           */
/*                                                                  */
/********************************************************************/
static int
is_interactive(void)
{ return cb_pari_is_interactive? cb_pari_is_interactive(): 0; }

static char *
strip_prompt(const char *s)
{
  long l = strlen(s);
  char *t, *t0 = stack_malloc(l+1);
  t = t0;
  for (; *s; s++)
  {
    /* RL_PROMPT_START_IGNORE / RL_PROMPT_END_IGNORE */
    if (*s == 1 || *s == 2) continue;
    if (*s == '\x1b') /* skip ANSI color escape sequence */
    {
      while (*++s != 'm')
        if (!*s) goto end;
      continue;
    }
    *t = *s; t++;
  }
end:
  *t = 0; return t0;
}
static void
update_logfile(const char *prompt, const char *s)
{
  pari_sp av;
  const char *p;
  if (!pari_logfile) return;
  av = avma;
  p = strip_prompt(prompt); /* raw prompt */

  switch (pari_logstyle) {
    case logstyle_TeX:
      fprintf(pari_logfile,
              "\\PARIpromptSTART|%s\\PARIpromptEND|%s\\PARIinputEND|%%\n",
              p, s);
    break;
    case logstyle_plain:
      fprintf(pari_logfile,"%s%s\n",p, s);
    break;
    case logstyle_color:
      fprintf(pari_logfile,"%s%s%s%s%s\n",term_get_color(NULL,c_PROMPT), p,
                                          term_get_color(NULL,c_INPUT), s,
                                          term_get_color(NULL,c_NONE));
      break;
  }
  set_avma(av);
}

void
gp_echo_and_log(const char *prompt, const char *s)
{
  if (!is_interactive())
  {
    if (!GP_DATA->echo) return;
    /* not pari_puts(): would duplicate in logfile */
    fputs(prompt, pari_outfile);
    fputs(s,      pari_outfile);
    fputc('\n',   pari_outfile);
    pari_set_last_newline(1);
  }
  update_logfile(prompt, s);
  pari_flush();
}

/* prompt = NULL --> from gprc. Return 1 if new input, and 0 if EOF */
int
get_line_from_file(const char *prompt, filtre_t *F, FILE *file)
{
  char *s;
  input_method IM;

  IM.file = (void*)file;
  if (file==stdin && cb_pari_fgets_interactive)
    IM.myfgets = (fgets_t)cb_pari_fgets_interactive;
  else
    IM.myfgets = (fgets_t)&fgets;
  IM.getline = &file_input;
  IM.free = 0;
  if (! input_loop(F,&IM))
  {
    if (file==stdin && cb_pari_start_output) cb_pari_start_output();
    return 0;
  }
  s = F->buf->buf;
  /* don't log if from gprc or empty input */
  if (*s && prompt && GP_DATA->echo != 2) gp_echo_and_log(prompt, s);
  return 1;
}

/* return 0 if no line could be read (EOF). If PROMPT = NULL, expand and
 * color default prompt; otherwise, use PROMPT as-is. */
int
gp_read_line(filtre_t *F, const char *PROMPT)
{
  static const char *DFT_PROMPT = "? ";
  Buffer *b = (Buffer*)F->buf;
  const char *p;
  int res, interactive;
  if (b->len > 100000) fix_buffer(b, 100000);
  interactive = is_interactive();
  if (interactive || pari_logfile || GP_DATA->echo)
  {
    p = PROMPT;
    if (!p) {
      p = F->in_comment? GP_DATA->prompt_comment: GP_DATA->prompt;
      p = gp_format_prompt(p);
    }
  }
  else
    p = DFT_PROMPT;

  if (interactive)
  {
    BLOCK_EH_START
    if (!pari_last_was_newline()) pari_putc('\n');
    if (cb_pari_get_line_interactive)
      res = cb_pari_get_line_interactive(p, GP_DATA->prompt_cont, F);
    else {
      pari_puts(p); pari_flush();
      res = get_line_from_file(p, F, pari_infile);
    }
    BLOCK_EH_END
  }
  else
  { /* in case UI fakes noninteractivity, e.g. TeXmacs */
    if (cb_pari_start_output && cb_pari_get_line_interactive)
      res = cb_pari_get_line_interactive(p, GP_DATA->prompt_cont, F);
    else
      res = get_line_from_file(p, F, pari_infile);
  }
  if (!strcmp(b->buf,"\\qf")) return 0;
  if (!disable_color && p != DFT_PROMPT &&
      (gp_colors[c_PROMPT] != c_NONE || gp_colors[c_INPUT] != c_NONE))
  {
    term_color(c_NONE); pari_flush();
  }
  return res;
}

/********************************************************************/
/*                                                                  */
/*                      EXCEPTION HANDLER                           */
/*                                                                  */
/********************************************************************/
static THREAD pari_timer ti_alarm;

#if defined(_WIN32) || defined(SIGALRM)
static void
gp_alarm_fun(void) {
  char buf[64];
  if (cb_pari_start_output) cb_pari_start_output();
  convert_time(buf, timer_get(&ti_alarm));
  pari_err(e_ALARM, buf);
}
#endif /* SIGALRM */

void
gp_sigint_fun(void) {
  char buf[150];
#if defined(_WIN32)
  if (win32alrm) { win32alrm = 0; gp_alarm_fun(); return;}
#endif
  if (cb_pari_start_output) cb_pari_start_output();
  convert_time(buf, timer_get(GP_DATA->T));
  if (pari_mt_nbthreads > 1)
  {
    sprintf(buf + strlen(buf), " cpu time, ");
    convert_time(buf + strlen(buf), walltimer_get(GP_DATA->Tw));
    sprintf(buf + strlen(buf), " real time");
  }
  pari_sigint(buf);
}

#ifdef SIGALRM
void
gp_alarm_handler(int sig)
{
#ifndef HAS_SIGACTION
  /*SYSV reset the signal handler in the handler*/
  (void)os_signal(sig,gp_alarm_handler);
#endif
  if (PARI_SIGINT_block) PARI_SIGINT_pending=sig;
  else gp_alarm_fun();
  return;
}
#endif /* SIGALRM */

/********************************************************************/
/*                                                                  */
/*                      GP-SPECIFIC ROUTINES                        */
/*                                                                  */
/********************************************************************/
void
gp_allocatemem(GEN z)
{
  ulong newsize;
  if (!z) newsize = 0;
  else {
    if (typ(z) != t_INT) pari_err_TYPE("allocatemem",z);
    newsize = itou(z);
    if (signe(z) < 0) pari_err_DOMAIN("allocatemem","size","<",gen_0,z);
  }
  if (pari_mainstack->vsize)
    paristack_resize(newsize);
  else
    paristack_newrsize(newsize);
}

GEN
gp_input(void)
{
  filtre_t F;
  Buffer *b = filtered_buffer(&F);
  GEN x;

  while (! get_line_from_file("",&F,pari_infile))
    if (popinfile()) { err_printf("no input ???"); cb_pari_quit(1); }
  x = readseq(b->buf);
  pop_buffer(); return x;
}

static GEN
closure_alarmer(GEN C, long s)
{
  struct pari_evalstate state;
  VOLATILE GEN x;
  if (!s) { pari_alarm(0); return closure_evalgen(C); }
  evalstate_save(&state);
#if !defined(HAS_ALARM) && !defined(_WIN32)
  pari_err(e_ARCH,"alarm");
#endif
  pari_CATCH(CATCH_ALL) /* We need to stop the timer after any error */
  {
    GEN E = pari_err_last();
    if (err_get_num(E) != e_ALARM) { pari_alarm(0); pari_err(0, E); }
    x = evalstate_restore_err(&state);
  }
  pari_TRY { pari_alarm(s); x = closure_evalgen(C); pari_alarm(0); } pari_ENDCATCH;
  return x;
}

void
pari_alarm(long s)
{
  if (s < 0) pari_err_DOMAIN("alarm","delay","<",gen_0,stoi(s));
  if (s) timer_start(&ti_alarm);
#ifdef _WIN32
  win32_alarm(s);
#elif defined(HAS_ALARM)
  alarm(s);
#else
  if (s) pari_err(e_ARCH,"alarm");
#endif
}

GEN
gp_alarm(long s, GEN code)
{
  if (!code) { pari_alarm(s); return gnil; }
  return closure_alarmer(code,s);
}

/*******************************************************************/
/**                                                               **/
/**                    EXTERNAL PRETTYPRINTER                     **/
/**                                                               **/
/*******************************************************************/
/* Wait for prettinprinter to finish, to prevent new prompt from overwriting
 * the output.  Fill the output buffer, wait until it is read.
 * Better than sleep(2): give possibility to print */
static void
prettyp_wait(FILE *out)
{
  const char *s = "                                                     \n";
  long i = 2000;

  fputs("\n\n", out); fflush(out); /* start translation */
  while (--i) fputs(s, out);
  fputs("\n", out); fflush(out);
}

/* initialise external prettyprinter (tex2mail) */
static int
prettyp_init(void)
{
  gp_pp *pp = GP_DATA->pp;
  if (!pp->cmd) return 0;
  if (pp->file || (pp->file = try_pipe(pp->cmd, mf_OUT))) return 1;

  pari_warn(warner,"broken prettyprinter: '%s'",pp->cmd);
  pari_free(pp->cmd); pp->cmd = NULL;
  sd_output("1", d_SILENT);
  return 0;
}
/* assume prettyp_init() was called */
static void
prettyp_GEN(GEN z)
{
  FILE *log = pari_logfile, *out = GP_DATA->pp->file->file;
  pariout_t T = *(GP_DATA->fmt); /* copy */
  /* output */
  T.prettyp = f_TEX;
  fputGEN_pariout(z, &T, out);
  /* flush and restore, output to logfile */
  prettyp_wait(out);
  if (log) {
    if (pari_logstyle == logstyle_TeX) {
      T.TeXstyle |= TEXSTYLE_BREAK;
      fputGEN_pariout(z, &T, log);
      fputc('%', log);
    } else {
      T.prettyp = f_RAW;
      fputGEN_pariout(z, &T, log);
    }
    fputc('\n', log); fflush(log);
  }
}
/* assume prettyp_init() was called. */
static void
prettyp_output(long n)
{
  FILE *log = pari_logfile, *out = GP_DATA->pp->file->file;
  pari_sp av = avma;
  const char *c_hist = term_get_color(NULL, c_HIST);
  const char *c_out = term_get_color(NULL, c_OUTPUT);
  GEN z = pari_get_hist(n);
  /* Emit first: there may be lines before the prompt */
  term_color(c_OUTPUT); pari_flush();
  /* history number */
  if (!(GP_DATA->flags & gpd_QUIET))
  {
    if (*c_hist || *c_out)
      fprintf(out, "\\LITERALnoLENGTH{%s}\\%%%ld =\\LITERALnoLENGTH{%s} ",
                   c_hist, n, c_out);
    else
      fprintf(out, "\\%%%ld = ", n);
  }
  if (log) switch (pari_logstyle)
  {
    case logstyle_plain:
      fprintf(log, "%%%ld = ", n);
      break;
    case logstyle_color:
      fprintf(log, "%s%%%ld = %s", c_hist, n, c_out);
      break;
    case logstyle_TeX:
      fprintf(log, "\\PARIout{%ld}", n);
      break;
  }
  set_avma(av); prettyp_GEN(z);
  term_color(c_NONE); pari_flush();
}

/*******************************************************************/
/**                                                               **/
/**                   FORMAT GP OUTPUT                            **/
/**                                                               **/
/*******************************************************************/

#define COLOR_LEN 16

static void
str_lim_lines(pari_str *S, char *s, long n, long max_lin)
{
  long lin, col, width;
  char COL[COLOR_LEN];
  char c;
  if (!*s) return;
  width = term_width();
  lin = 1;
  col = n;

  if (lin > max_lin) return;
  while ( (c = *s++) )
  {
    if (lin >= max_lin)
      if (c == '\n' || col >= width-5)
      {
        pari_sp av = avma;
        str_puts(S, term_get_color(COL, c_ERR)); set_avma(av);
        str_puts(S,"[+++]"); return;
      }
    if (c == '\n')         { col = -1; lin++; }
    else if (col == width) { col =  0; lin++; }
    pari_set_last_newline(c=='\n');
    col++; str_putc(S, c);
  }
}
void
str_display_hist(pari_str *S, long n)
{
  long l = 0;
  char col[COLOR_LEN];
  char *s;
  /* history number */
  if (n)
  {
    char buf[64];
    if (!(GP_DATA->flags & gpd_QUIET))
    {
      str_puts(S, term_get_color(col, c_HIST));
      sprintf(buf, "%%%ld = ", n);
      str_puts(S, buf);
      l = strlen(buf);
    }
  }
  /* output */
  str_puts(S, term_get_color(col, c_OUTPUT));
  s = GENtostr(pari_get_hist(n));
  if (GP_DATA->lim_lines)
    str_lim_lines(S, s, l, GP_DATA->lim_lines);
  else
    str_puts(S, s);
  pari_free(s);
  str_puts(S,term_get_color(col, c_NONE));
}

static void
gp_classic_output(long n)
{
  pari_sp av = avma;
  pari_str S;
  str_init(&S, 1);
  str_display_hist(&S, n);
  str_putc(&S, 0);
  pari_puts(S.string);
  pari_putc('\n'); pari_flush();
  set_avma(av);
}

void
gp_display_hist(long n)
{
  if (cb_pari_display_hist)
    cb_pari_display_hist(n);
  else if (GP_DATA->fmt->prettyp == f_PRETTY && prettyp_init())
    prettyp_output(n);
  else
    gp_classic_output(n);
}

/*******************************************************************/
/**                                                               **/
/**                     GP-SPECIFIC DEFAULTS                      **/
/**                                                               **/
/*******************************************************************/

static long
atocolor(const char *s)
{
  long l = atol(s);
  if (l & ~0xff) pari_err(e_MISC, "invalid 8bit RGB code: %ld", l);
  return l;
}

GEN
sd_graphcolormap(const char *v, long flag)
{
  char *p, *q;
  long i, j, l, a, s, *lp;

  if (v)
  {
    pari_sp av = avma;
    char *t = gp_filter(v);
    if (*t != '[' || t[strlen(t)-1] != ']')
      pari_err(e_SYNTAX, "incorrect value for graphcolormap", t, t);
    for (s = 0, p = t+1, l = 2, a=0; *p; p++)
      if (*p == '[')
      {
        a++;
        while (*++p != ']')
          if (!*p || *p == '[')
            pari_err(e_SYNTAX, "incorrect value for graphcolormap", p, t);
      }
      else if (*p == '"')
      {
        s += sizeof(long)+1;
        while (*p && *++p != '"') s++;
        if (!*p) pari_err(e_SYNTAX, "incorrect value for graphcolormap", p, t);
        s = (s+sizeof(long)-1) & ~(sizeof(long)-1);
      }
      else if (*p == ',')
        l++;
    if (l < 4)
      pari_err(e_MISC, "too few colors (< 4) in graphcolormap");
    if (GP_DATA->colormap) pari_free(GP_DATA->colormap);
    GP_DATA->colormap = (GEN)pari_malloc((l+4*a)*sizeof(long) + s);
    GP_DATA->colormap[0] = evaltyp(t_VEC)|evallg(l);
    for (p = t+1, i = 1, lp = GP_DATA->colormap+l; i < l; p++)
      switch(*p)
      {
      case '"':
        gel(GP_DATA->colormap, i) = lp;
        q = ++p; while (*q != '"') q++;
        *q = 0;
        j = 1 + nchar2nlong(q-p+1);
        lp[0] = evaltyp(t_STR)|evallg(j);
        strncpy(GSTR(lp), p, q-p+1);
        lp += j; p = q;
        break;
      case '[': {
        const char *ap[3];
        gel(GP_DATA->colormap, i) = lp;
        lp[0] = evaltyp(t_VECSMALL)|_evallg(4);
        for (ap[0] = ++p, j=0; *p && *p != ']'; p++)
          if (*p == ',' && j<2) { *p++ = 0; ap[++j] = p; }
        while (j<2) ap[++j] = "0";
        if (j>2 || *p != ']')
        {
          char buf[100];
          sprintf(buf, "incorrect value for graphcolormap[%ld]: ", i);
          pari_err(e_SYNTAX, buf, p, t);
        }
        *p = '\0';
        lp[1] = atocolor(ap[0]);
        lp[2] = atocolor(ap[1]);
        lp[3] = atocolor(ap[2]);
        lp += 4;
        break;
      }
      case ',':
      case ']':
        i++;
        break;
      default:
        pari_err(e_SYNTAX, "incorrect value for graphcolormap", p, t);
      }
    set_avma(av);
  }
  if (flag == d_RETURN || flag == d_ACKNOWLEDGE)
  {
    GEN C = cgetg(lg(GP_DATA->colormap), t_VEC);
    long i, l = lg(C);
    for (i = 1; i < l; i++)
    {
      GEN c = gel(GP_DATA->colormap, i);
      gel(C, i) = (typ(c) == t_STR)? gcopy(c): zv_to_ZV(c);
    }
    if (flag == d_RETURN) return C;
    pari_printf("   graphcolormap = %Ps\n", C);
  }
  return gnil;
}

GEN
sd_graphcolors(const char *v, long flag)
{ return sd_intarray(v, flag, &(GP_DATA->graphcolors), "graphcolors"); }
GEN
sd_plothsizes(const char *v, long flag)
{ return sd_intarray(v, flag, &(GP_DATA->plothsizes), "plothsizes"); }

GEN
sd_help(const char *v, long flag)
{
  const char *str;
  if (v)
  {
    if (GP_DATA->secure)
      pari_err(e_MISC,"[secure mode]: can't modify 'help' default (to %s)",v);
    if (GP_DATA->help) pari_free((void*)GP_DATA->help);
#ifndef _WIN32
    GP_DATA->help = path_expand(v);
#else
    GP_DATA->help = pari_strdup(v);
#endif
  }
  str = GP_DATA->help? GP_DATA->help: "none";
  if (flag == d_RETURN) return strtoGENstr(str);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   help = \"%s\"\n", str);
  return gnil;
}

static GEN
sd_prompt_set(const char *v, long flag, const char *how, char **p)
{
  if (v) {
    if (*p) free(*p);
    *p = pari_strdup(v);
  }
  if (flag == d_RETURN) return strtoGENstr(*p);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   prompt%s = \"%s\"\n", how, *p);
  return gnil;
}
GEN
sd_prompt(const char *v, long flag)
{ return sd_prompt_set(v, flag, "", &(GP_DATA->prompt)); }
GEN
sd_prompt_cont(const char *v, long flag)
{ return sd_prompt_set(v, flag, "_cont", &(GP_DATA->prompt_cont)); }

GEN
sd_breakloop(const char *v, long flag)
{ return sd_toggle(v,flag,"breakloop", &(GP_DATA->breakloop)); }
GEN
sd_doctest(const char *v, long flag)
{ return sd_ulong(v,flag,"doctest",&(GP_DATA->doctest), 0,1,NULL); }
GEN
sd_echo(const char *v, long flag)
{ return sd_ulong(v,flag,"echo", &(GP_DATA->echo), 0,2,NULL); }
GEN
sd_timer(const char *v, long flag)
{ return sd_toggle(v,flag,"timer", &(GP_DATA->chrono)); }
GEN
sd_recover(const char *v, long flag)
{ return sd_toggle(v,flag,"recover", &(GP_DATA->recover)); }

GEN
sd_psfile(const char *v, long flag)
{ return sd_string(v, flag, "psfile", &current_psfile); }

GEN
sd_lines(const char *v, long flag)
{ return sd_ulong(v,flag,"lines",&(GP_DATA->lim_lines), 0,LONG_MAX,NULL); }
GEN
sd_linewrap(const char *v, long flag)
{
  ulong old = GP_DATA->linewrap, n = GP_DATA->linewrap;
  GEN z = sd_ulong(v,flag,"linewrap",&n, 0,LONG_MAX,NULL);
  if (old)
  { if (!n) resetout(1); }
  else
  { if (n) init_linewrap(n); }
  GP_DATA->linewrap = n; return z;
}

/* readline-specific defaults */
GEN
sd_readline(const char *v, long flag)
{
  const char *msg[] = {
    "(bits 0x2/0x4 control matched-insert/arg-complete)", NULL};
  ulong state = GP_DATA->readline_state;
  GEN res = sd_ulong(v,flag,"readline", &GP_DATA->readline_state, 0, 7, msg);

  if (state != GP_DATA->readline_state)
    (void)sd_toggle(GP_DATA->readline_state? "1": "0", d_SILENT, "readline", &(GP_DATA->use_readline));
  return res;
}
GEN
sd_histfile(const char *v, long flag)
{
  char *old = GP_DATA->histfile;
  GEN r = sd_string(v, flag, "histfile", &GP_DATA->histfile);
  if (v && !*v)
  {
    free(GP_DATA->histfile);
    GP_DATA->histfile = NULL;
  }
  else if (GP_DATA->histfile != old && (!old || strcmp(old,GP_DATA->histfile)))
  {
    if (cb_pari_init_histfile) cb_pari_init_histfile();
  }
  return r;
}

/********************************************************************/
/**                                                                **/
/**                         METACOMMANDS                           **/
/**                                                                **/
/********************************************************************/
void
pari_print_version(void)
{
  pari_sp av = avma;
  char *buf, *ver = what_cc();
  const char *kver = pari_kernel_version();
  const char *date = paricfg_compiledate, *mt = paricfg_mt_engine;
  ulong t = pari_mt_nbthreads;

  pari_center(paricfg_version);
  buf = stack_malloc(strlen(paricfg_buildinfo) + 2 + strlen(kver));
  (void)sprintf(buf, paricfg_buildinfo, kver);
  pari_center(buf);
  buf = stack_malloc(128 + strlen(date) + (ver? strlen(ver): 0));
  if (ver) (void)sprintf(buf, "compiled: %s, %s", date, ver);
  else     (void)sprintf(buf, "compiled: %s", date);
  pari_center(buf);
  if (t > 1) sprintf(buf, "threading engine: %s, nbthreads = %lu",mt,t);
  else       sprintf(buf, "threading engine: %s",mt);
  pari_center(buf);
  ver = what_readline();
  buf = stack_malloc(strlen(ver) + 64);
  (void)sprintf(buf, "(readline %s, extended help%s enabled)", ver,
                has_ext_help()? "": " not");
  pari_center(buf); set_avma(av);
}

static int
cmp_epname(void *E, GEN e, GEN f)
{
  (void)E;
  return strcmp(((entree*)e)->name, ((entree*)f)->name);
}
/* if fun is set print only closures, else only non-closures
 * if member is set print only member functions, else only non-members */
static void
print_all_user_obj(int fun, int member)
{
  pari_sp av = avma;
  long i, iL = 0, lL = 1024;
  GEN L = cgetg(lL+1, t_VECSMALL);
  entree *ep;
  for (i = 0; i < functions_tblsz; i++)
    for (ep = functions_hash[i]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpVAR && fun == (typ((GEN)ep->value) == t_CLOSURE))
      {
        const char *f = ep->name;
        if (member == (f[0] == '_' && f[1] == '.'))
        {
          if (iL >= lL) { lL *= 2; L = vecsmall_lengthen(L, lL); }
          L[++iL] = (long)ep;
        }
      }
  if (iL)
  {
    setlg(L, iL+1);
    gen_sort_inplace(L, NULL, &cmp_epname, NULL);
    for (i = 1; i <= iL; i++)
    {
      ep = (entree*)L[i];
      pari_printf("%s =\n  %Ps\n\n", ep->name, ep->value);
    }
  }
  set_avma(av);
}

/* get_sep, removing enclosing quotes */
static char *
get_name(const char *s)
{
  char *t = get_sep(s);
  if (*t == '"')
  {
    long n = strlen(t)-1;
    if (t[n] == '"') { t[n] = 0; t++; }
  }
  return t;
}
static void
ack_debug(const char *s, long d) {pari_printf("   debug(\"%s\") = %ld\n",s,d);}
static void
ack_setdebug(const char *s, long d) {setdebug(s, d); ack_debug(s, d);}

static void
escape(const char *tch, int ismain)
{
  const char *s = tch;
  long d;
  char c;
  GEN x;
  switch ((c = *s++))
  {
    case 'w': case 'x': case 'a': case 'b': case 'B': case 'm':
    { /* history things */
      if (c != 'w' && c != 'x') d = get_int(s,0);
      else
      {
        d = atol(s); if (*s == '-') s++;
        while (isdigit((unsigned char)*s)) s++;
      }
      x = pari_get_hist(d);
      switch (c)
      {
        case 'B': /* prettyprinter */
          if (prettyp_init())
          {
            pari_flush(); prettyp_GEN(x);
            pari_flush(); break;
          }
        case 'b': /* fall through */
        case 'm': matbrute(x, GP_DATA->fmt->format, -1); break;
        case 'a': brute(x, GP_DATA->fmt->format, -1); break;
        case 'x': dbgGEN(x, get_int(s, -1)); break;
        case 'w':
          s = get_name(s); if (!*s) s = current_logfile;
          write0(s, mkvec(x)); return;
      }
      pari_putc('\n'); return;
    }

    case 'c': commands(-1); break;
    case 'd': (void)setdefault(NULL,NULL,d_SILENT); break;
    case 'e':
      s = get_sep(s);
      if (!*s) s = (GP_DATA->echo)? "0": "1";
      (void)sd_echo(s,d_ACKNOWLEDGE); break;
    case 'g':
        if (isdigit((unsigned char)*s))
        {
          const char *t = s + 1;
          if (isdigit((unsigned char)*t)) t++; /* atol(s) < 99 */
          t = get_name(t);
          if (*t) { d = atol(s); ack_setdebug(t, d); break; }
        }
        else if (*s == '"' || isalpha((unsigned char)*s))
        {
          char *t = get_name(s);
          if (t[1] && !isdigit((unsigned char)t[1]))
          {
            char *T = t + strlen(t) - 1;
            if (isdigit((unsigned char)*T))
            {
              if (isdigit((unsigned char)T[-1])) T--; /* < 99 */
              d = atol(T); *T = 0;
              ack_setdebug(get_name(t), d); /* get_name in case of ".." */
            }
            else
            {
              x = setdebug(t, -1); ack_debug(t, itos(x));
            }
          }
          else switch (*t)
          {
            case 'm':
              s++; (void)sd_debugmem(*s? s: NULL,d_ACKNOWLEDGE); break;
            case 'f':
              s++; (void)sd_debugfiles(*s? s: NULL,d_ACKNOWLEDGE); break;
          }
          break;
        }
        (void)sd_debug(*s? s: NULL,d_ACKNOWLEDGE); break;
      break;
    case 'h': print_functions_hash(s); break;
    case 'l':
      s = get_name(s);
      if (*s)
      {
        if (pari_logfile) { (void)sd_logfile(s,d_ACKNOWLEDGE);break; }
        (void)sd_logfile(s,d_SILENT);
      }
      (void)sd_log(pari_logfile?"0":"1",d_ACKNOWLEDGE);
      break;
    case 'o': (void)sd_output(*s? s: NULL,d_ACKNOWLEDGE); break;
    case 'p':
      switch (*s)
      {
        case 's': s++;
          (void)sd_seriesprecision(*s? s: NULL,d_ACKNOWLEDGE); break;
        case 'b' : s++;
          (void)sd_realbitprecision(*s? s: NULL,d_ACKNOWLEDGE); break;
        default :
          (void)sd_realprecision(*s? s: NULL,d_ACKNOWLEDGE); break;
      }
      break;
    case 'q': cb_pari_quit(0); break;
    case 'r':
      s = get_name(s);
      if (!ismain) { (void)gp_read_file(s); break; }
      switchin(s);
      if (file_is_binary(pari_infile))
      {
        pari_sp av = avma;
        int vector;
        GEN x = readbin(s,pari_infile, &vector);
        popinfile();
        if (!x) pari_err_FILE("input file",s);
        if (vector) /* many BIN_GEN */
        {
          long i, l = lg(x);
          pari_warn(warner,"setting %ld history entries", l-1);
          for (i=1; i<l; i++) pari_add_hist(gel(x,i), 0, 0);
        }
        set_avma(av);
      }
      break;
    case 's': dbg_pari_heap(); break;
    case 't': gentypes(); break;
    case 'u':
      switch(*s)
      {
        case 'v':
          if (*++s) break;
          print_all_user_obj(0, 0); return;
        case 'm':
          if (*++s) break;
          print_all_user_obj(1, 1); return;
        case '\0':
          print_all_user_obj(1, 0); return;
      }
      pari_err(e_SYNTAX,"unexpected character", s,tch-1); break;
    case 'v':
      if (*s) pari_err(e_SYNTAX,"unexpected character", s,tch-1);
      pari_print_version(); break;
    case 'y':
      s = get_sep(s);
      if (!*s) s = (GP_DATA->simplify)? "0": "1";
      (void)sd_simplify(s,d_ACKNOWLEDGE); break;
    case 'z':
      s = get_sep(s);
      if (!*s) s = (GP_DATA->doctest)? "0": "1";
      (void)sd_doctest(s,d_ACKNOWLEDGE); break;
    default: pari_err(e_SYNTAX,"unexpected character", tch,tch-1);
  }
}

static int
chron(const char *s)
{
  if (*s)
  { /* if "#" or "##" timer metacommand. Otherwise let the parser get it */
    const char *t;
    if (*s == '#') s++;
    if (*s) return 0;
    if (pari_nb_hist()==0)
      pari_printf("  ***   no last result.\n");
    else
    {
      t = gp_format_time(pari_get_histtime(0));
      if (pari_mt_nbthreads==1)
        pari_printf("  ***   last result computed in %s.\n", t);
      else
      {
        const char *r = gp_format_time(pari_get_histrtime(0));
        pari_printf("  ***   last result: cpu time %s, real time %s.\n", t,r);
      }
    }
  }
  else { GP_DATA->chrono ^= 1; (void)sd_timer(NULL,d_ACKNOWLEDGE); }
  return 1;
}

/* return 0: can't interpret *buf as a metacommand
 *        1: did interpret *buf as a metacommand or empty command */
int
gp_meta(const char *buf, int ismain)
{
  switch(*buf++)
  {
    case '?': gp_help(buf, h_REGULAR); break;
    case '#': return chron(buf);
    case '\\': escape(buf, ismain); break;
    case '\0': break;
    default: return 0;
  }
  return 1;
}

void
pari_breakpoint(void)
{
  if (!pari_last_was_newline()) pari_putc('\n');
  closure_err(0);
  if (cb_pari_break_loop && cb_pari_break_loop(-1)) return;
  cb_pari_err_recover(e_MISC);
}
