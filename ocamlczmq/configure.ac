# These lines are required
AC_PREREQ(2.59)
AC_INIT([ocamlczmq], [0.9], [christoph-sticksel@uiowa.edu])

# This just checks if some source file is present
AC_CONFIG_SRCDIR([src/ZMQ.ml])

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

AC_CONFIG_MACRO_DIR([config])

# Check for libtool
# LT_INIT([disable-shared])
# AC_PROG_LIBTOOL

# Checks for libraries for ZeroMQ
AC_CHECK_LIB([pthread], [pthread_create])
AC_CHECK_LIB([rt], [clock_gettime])

# Check for OCaml  
AC_PROG_OCAML

if test "x$OCAMLOPT" = "xno"; then
  AC_MSG_ERROR([You must install the OCaml native-code compiler])
fi

# TODO: Check for OCaml 4
# if [[["x$OCAMLVERSION" =~ "x4"]]]; then
#   AC_MSG_ERROR([OCaml 4 is required])
# fi

# Check for Camlp4
AC_PROG_CAMLP4
if test "x$CAMLP4" = "xno"; then
  AC_MSG_ERROR([You must install the Camlp4 preprocessor])
fi

# Check for OCaml findlib
AC_PROG_FINDLIB
if test "x$OCAMLFIND" = "xno"; then
   AC_MSG_WARN([You must install the OCaml findlib (the ocamlfind command)])
fi

# Check for C compiler
AC_PROG_CC

if test "x$CC" = "xno"; then
  AC_MSG_ERROR([You need a C compiler])
fi

AC_CONFIG_FILES([Makefile src/Makefile])

AC_OUTPUT
echo "Configure succeed. Now run make and make install."

