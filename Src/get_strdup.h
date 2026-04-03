/* ask for strdup & getline - see https://en.cppreference.com/w/c/experimental/dynamic/getline & https://en.cppreference.com/w/c/experimental/dynamic/strdup */
#ifdef __STDC_ALLOC_LIB__
 #define __STDC_WANT_LIB_EXT2__ 1
#else
 #define _POSIX_C_SOURCE 200809L
#endif

#include <string.h>
#include <stdio.h>
