#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.61])
AC_INIT([lfsc-checker], [1.0], [cvc-bugs@cs.nyu.edu])
AC_CONFIG_SRCDIR([libwriter.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([config])
AC_CONFIG_HEADERS([config.h])

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE([1.11 foreign no-define tar-pax])
LT_INIT



m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

# on by default
AM_MAINTAINER_MODE([enable])


# If macosx, than check for macports or fink default installation.
default_macports_path=/opt/local
default_fink_path=/sw
case $host_os in
     darwin*) 
              # Perhaps this will be useful some time.
     	      #dnl nested function support
     	      #AC_MSG_NOTICE([Adding -fnested-functions to CFLAGS])
	      #CFLAGS="-fnested-functions"

	      dnl fink or macports installation
     	      AC_MSG_CHECKING([for a fink or macports installation at $default_fink_path and $default_macports_path])
     	      if test -d $default_fink_path; then 
	      	 AC_MSG_RESULT([found fink!])
		 AC_MSG_NOTICE([Adding -I$default_fink_path/include to CPPFLAGS])
	      	 CPPFLAGS="-I$default_fink_path/include $CPPFLAGS"
		 AC_MSG_NOTICE([Adding -L$default_fink_path/lib to LDFLAGS])
		 LDFLAGS="-L$default_fink_path/lib $LDFLAGS"
              elif test -d $default_macports_path; then
		 AC_MSG_RESULT([found macports!])
		 AC_MSG_NOTICE([Adding -I$default_macports_path/include to CPPFLAGS])
	      	 CPPFLAGS="-I$default_macports_path/include $CPPFLAGS"
		 AC_MSG_NOTICE([Adding -L$default_macports_path/lib to LDFLAGS])
		 LDFLAGS="-L$default_macports_path/lib $LDFLAGS"
	      else
		AC_MSG_RESULT(none)
		AC_MSG_NOTICE([You may need to add set CPPFLAGS and LDFLAGS for gmp, etc.])
	      fi
	      ;;
esac


# turn off static lib building by default
AC_ENABLE_SHARED
AC_DISABLE_STATIC

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC

# Checks for libraries.
# FIXME: Replace `main' with a function in `-lgmp':
AC_CHECK_LIB([gmp], [__gmpz_init])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h string.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([strdup])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
