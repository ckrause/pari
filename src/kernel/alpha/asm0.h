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

/*
ASM addll mulll
NOASM bfffo divll
*/
#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  ulong hiremainder
#define LOCAL_OVERFLOW     ulong overflow

#define addll(a, b)\
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
  __asm__ ("addq %2,%3,%0\n\tcmpult %4,%2,%1" \
   : "=&r" (__value), "=r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0)); \
  __value; \
})

#define addllx(a, b)\
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ ("addq %3,%4,%0\n\tcmpult %5,%3,%2\n\taddq %5,%6,%0\n\tcmpult %5,%6,%1\n\taddq %6,%7,%1\n\t" \
   : "=&r" (__value), "=r" (overflow), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0), "1" (overflow), "2" ((ulong) 0)); \
__value; \
})

#define subll(a, b)\
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
  __asm__ ("subq %2,%3,%0\n\tcmpult %2,%4,%1" \
   : "=&r" (__value), "=r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong)0)); \
  __value; \
})

#define subllx(a, b)\
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp1, __temp2; \
__asm__ ("subq %4,%5,%2\n\tcmpult %4,%8,%3\n\tsubq %8,%7,%0\n\tcmpult %8,%6,%1\n\taddq %7,%9,%1\n\t" \
   : "=r" (__value), "=r" (overflow), "=&r" (__temp1), "=r" (__temp2)  \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong)0), "1" (overflow), "2" ((ulong)0), "3" ((ulong)0)); \
 __value; \
})

#define mulll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("umulh %2,%3,%1\n\tmulq %2,%3,%0\n\t" \
   : "=r" (__value), "=&r" (hiremainder) \
   : "r" (__arg1), "r" (__arg2)); \
 __value; \
})

#define addmul(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ ("mulq %3,%4,%0\n\tumulh %3,%4,%2\n\taddq %5,%6,%0\n\tcmpult %5,%6,%1\n\taddq %7,%6,%1\n\t" \
   : "=&r" (__value), "=r" (hiremainder), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0), "1" (hiremainder), "2" ((ulong) 0)); \
 __value; \
})
#endif
