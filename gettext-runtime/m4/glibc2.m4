# glibc2.m4 serial 1
dnl Copyright (C) 2000-2002, 2004 Free Software Foundation, Inc.
dnl This file is free software, distributed under the terms of the GNU
dnl General Public License.  As a special exception to the GNU General
dnl Public License, this file may be distributed as part of a program
dnl that contains a configuration script generated by Autoconf, under
dnl the same distribution terms as the rest of that program.

# Test for the GNU C Library, version 2.0 or newer.
# From Bruno Haible.

AC_DEFUN([gt_GLIBC2],
  [
    AC_CACHE_CHECK(whether we are using the GNU C Library 2 or newer,
      ac_cv_gnu_library_2,
      [AC_EGREP_CPP([Lucky GNU user],
	[
#include <features.h>
#ifdef __GNU_LIBRARY__
 #if (__GLIBC__ >= 2)
  Lucky GNU user
 #endif
#endif
	],
	ac_cv_gnu_library_2=yes,
	ac_cv_gnu_library_2=no)
      ]
    )
    AC_SUBST(GLIBC2)
    GLIBC2="$ac_cv_gnu_library_2"
  ]
)