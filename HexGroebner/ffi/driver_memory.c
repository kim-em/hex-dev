/* Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Kim Morrison */
/* Process memory policy for the standalone F4 driver executables only.

   The Lean runtime's allocator reserves its arena with MADV_HUGEPAGE. Under
   the common `transparent_hugepage/defrag=madvise` kernel setting, a first
   touch in such a region may synchronously compact memory and zero a whole
   2 MiB page. On a busy host this dominated short runs and added tens of
   percent to medium ones. Disabling transparent huge pages for this process
   gives ordinary 4 KiB faults, the same treatment glibc-malloc comparators
   receive under the `madvise` policy.

   The constructor runs before Lean module initialization, so no runtime
   allocation precedes it. `HEX_GROEBNER_THP=1` keeps the inherited policy for
   comparisons. Library code never changes process state; only the driver
   executables link this object. Other platforms are unaffected. */
#if defined(__linux__)
#include <stdlib.h>
#include <sys/prctl.h>

__attribute__((constructor)) static void hex_groebner_driver_memory(void) {
    const char *keep = getenv("HEX_GROEBNER_THP");
    if (keep && keep[0] == '1' && keep[1] == 0) return;
    (void)prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0);
}
#endif

typedef int hex_groebner_driver_memory_unit;
