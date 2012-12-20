/* hwfeatures.c - Detect hardware features.
 * Copyright (C) 2007, 2011  Free Software Foundation, Inc.
 *
 * This file is part of Libgcrypt.
 *
 * Libgcrypt is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * Libgcrypt is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>

#include "g10lib.h"

/* A bit vector describing the hardware features currently
   available. */
static unsigned int hw_features;


/* Return a bit vector describing the available hardware features.
   The HWF_ constants are used to test for them. */
unsigned int
_gcry_get_hw_features (void)
{
  return hw_features;
}


#undef HAS_X86_CPUID

#if defined (__i386__) && SIZEOF_UNSIGNED_LONG == 4 && defined (__GNUC__)
#define HAS_X86_CPUID 1

static int
is_cpuid_available(void)
{
  int has_cpuid = 0;

  /* Detect the CPUID feature by testing some undefined behaviour (16
     vs 32 bit pushf/popf). */
  asm volatile
    ("pushf\n\t"                 /* Copy flags to EAX.  */
     "popl %%eax\n\t"
     "movl %%eax, %%ecx\n\t"     /* Save flags into ECX.  */
     "xorl $0x200000, %%eax\n\t" /* Toggle ID bit and copy it to the flags.  */
     "pushl %%eax\n\t"
     "popf\n\t"
     "pushf\n\t"                 /* Copy changed flags again to EAX.  */
     "popl %%eax\n\t"
     "pushl %%ecx\n\t"           /* Restore flags from ECX.  */
     "popf\n\t"
     "xorl %%eax, %%ecx\n\t"     /* Compare flags against saved flags.  */
     "jz .Lno_cpuid%=\n\t"       /* Toggling did not work, thus no CPUID.  */
     "movl $1, %0\n"             /* Worked. true -> HAS_CPUID.  */
     ".Lno_cpuid%=:\n\t"
     : "+r" (has_cpuid)
     :
     : "%eax", "%ecx", "cc"
     );

  return has_cpuid;
}

static void
get_cpuid(unsigned int in, unsigned int *eax, unsigned int *ebx,
          unsigned int *ecx, unsigned int *edx)
{
  unsigned int regs[4];

  asm volatile
    ("pushl %%ebx\n\t"           /* Save GOT register.  */
     "cpuid\n\t"
     "movl %%ebx, %1\n\t"
     "popl %%ebx\n\t"            /* Restore GOT register. */
     : "=a" (regs[0]), "=r" (regs[1]), "=c" (regs[2]), "=d" (regs[3])
     : "0" (in)
     : "cc"
     );

  if (eax)
    *eax = regs[0];
  if (ebx)
    *ebx = regs[1];
  if (ecx)
    *ecx = regs[2];
  if (edx)
    *edx = regs[3];
}
#endif /* i386 && GNUC */


#if defined (__x86_64__) && defined (__GNUC__)
#define HAS_X86_CPUID 1

static int
is_cpuid_available(void)
{
  return 1;
}

static void
get_cpuid(unsigned int in, unsigned int *eax, unsigned int *ebx,
          unsigned int *ecx, unsigned int *edx)
{
  unsigned int regs[4];

  asm volatile
    ("cpuid\n\t"
     : "=a" (regs[0]), "=b" (regs[1]), "=c" (regs[2]), "=d" (regs[3])
     : "0" (in)
     : "cc"
     );

  if (eax)
    *eax = regs[0];
  if (ebx)
    *ebx = regs[1];
  if (ecx)
    *ecx = regs[2];
  if (edx)
    *edx = regs[3];
}
#endif /* x86-64 && GNUC */


#ifdef HAS_X86_CPUID
static void
detect_x86_gnuc (void)
{
  char vendor_id[12+1];
  unsigned int features;

  if (!is_cpuid_available())
    return;

  get_cpuid(0, NULL,
            (unsigned int *)&vendor_id[0],
            (unsigned int *)&vendor_id[8],
            (unsigned int *)&vendor_id[4]);
  vendor_id[12] = 0;

  if (0)
    ; /* Just to make "else if" and ifdef macros look pretty.  */
#ifdef ENABLE_PADLOCK_SUPPORT
  else if (!strcmp (vendor_id, "CentaurHauls"))
    {
      /* This is a VIA CPU.  Check what PadLock features we have.  */

      /* Check for extended centaur (EAX).  */
      get_cpuid(0xC0000000, &features, NULL, NULL, NULL);

      /* Has extended centaur features? */
      if (features > 0xC0000000)
        {
           /* Ask for the extended feature flags (EDX). */
           get_cpuid(0xC0000001, NULL, NULL, NULL, &features);

           /* Test bits 2 and 3 to see whether the RNG exists and is enabled. */
           if ((features & 0x0C) == 0x0C)
             hw_features |= HWF_PADLOCK_RNG;

           /* Test bits 6 and 7 to see whether the ACE exists and is enabled. */
           if ((features & 0xC0) == 0xC0)
             hw_features |= HWF_PADLOCK_AES;

           /* Test bits 10 and 11 to see whether the PHE exists and is
              enabled.  */
           if ((features & 0xC00) == 0xC00)
             hw_features |= HWF_PADLOCK_SHA;

           /* Test bits 12 and 13 to see whether the MONTMUL exists and is
              enabled.  */
           if ((features & 0x3000) == 0x3000)
             hw_features |= HWF_PADLOCK_MMUL;
        }
    }
#endif /*ENABLE_PADLOCK_SUPPORT*/
  else if (!strcmp (vendor_id, "GenuineIntel"))
    {
      /* This is an Intel CPU.  */
    }
  else if (!strcmp (vendor_id, "AuthenticAMD"))
    {
      /* This is an AMD CPU.  */
    }

  /* Detect Intel features, that might also be supported by other
     vendors.  */

  /* Get CPU info and Intel feature flags (ECX).  */
  get_cpuid(1, NULL, NULL, &features, NULL);

#ifdef ENABLE_AESNI_SUPPORT
  /* Test bit 25 for AES-NI.  */
  if (features & 0x02000000)
     hw_features |= HWF_INTEL_AESNI;
#endif /*ENABLE_AESNI_SUPPORT*/
#ifdef ENABLE_DRNG_SUPPORT
  /* Test bit 30 for RDRAND.  */
  if (features & 0x40000000)
     hw_features |= HWF_INTEL_RDRAND;
#endif /*ENABLE_DRNG_SUPPORT*/

}
#endif /* HAS_X86_CPUID */


/* Detect the available hardware features.  This function is called
   once right at startup and we assume that no other threads are
   running.  */
void
_gcry_detect_hw_features (unsigned int disabled_features)
{
  hw_features = 0;

  if (fips_mode ())
    return; /* Hardware support is not to be evaluated.  */

#if HAS_X86_CPUID
  {
    detect_x86_gnuc ();
  }
#endif /* HAS_X86_CPUID */

  hw_features &= ~disabled_features;
}
