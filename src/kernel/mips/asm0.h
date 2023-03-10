#line 2 "../src/kernel/mips/asm0.h"
/* Copyright (C) 2013  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
/*
ASM mulll
NOASM addll bfffo divll
*/
#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  ulong hiremainder
#define LOCAL_OVERFLOW     ulong overflow

#if defined(__mips_isa_rev) && __mips_isa_rev >= 6
#define mulll(a, b)                                         \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("muhu %0,%2,%3\n\tmulu %1,%2,%3"                  \
   : "=&r" (__value), "=&r" (hiremainder)                   \
   : "r" (__arg1), "r" (__arg2)                             \
   : );                                                     \
 __value;                                                   \
})

#define addmul(a, b)                                                    \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value, __tmp;                     \
  __asm__ ("muhu %0,%3,%4\n\tmulu %2,%3,%4\n\t"                      \
           "addu %1,%2,%5\n\tsltu %2,%1,%5\n\taddu %0,%0,%2"            \
           : "=&r" (hiremainder), "=&r" (__value), "=&r" (__tmp)        \
           : "r" (__arg1), "r" (__arg2), "r" (hiremainder)              \
           : "hi", "lo");                                               \
  __value;                                                              \
})
#else
#define mulll(a, b)                                         \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("multu %2,%3\n\tmfhi %1"                          \
   : "=&l" (__value), "=&r" (hiremainder)                   \
   : "r" (__arg1), "r" (__arg2)                             \
   : "hi");                                                 \
 __value;                                                   \
})

#define addmul(a, b)                                                    \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value, __tmp;                     \
  __asm__ ("multu %3,%4\n\tmfhi %0\n\tmflo %2\n\t"                      \
           "addu %1,%2,%5\n\tsltu %2,%1,%5\n\taddu %0,%0,%2"            \
           : "=&r" (hiremainder), "=&r" (__value), "=&r" (__tmp)        \
           : "r" (__arg1), "r" (__arg2), "r" (hiremainder)              \
           : "hi", "lo");                                               \
  __value;                                                              \
})
#endif

#endif
