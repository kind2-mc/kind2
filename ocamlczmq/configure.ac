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
# if test "x$OCAMLVERSION" =~ "x5"; then
#   AC_MSG_ERROR([OCaml 4 is required])
# fi

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


AC_ARG_WITH(
    [zmq],
    [AS_HELP_STRING([--with-zmq], [Configure ZeroMQ <:@default: false@:>@])],
    [with_zmq=yes],
    [with_zmq=no])

if test "x$with_zmq" = "xyes"; then
   AC_CONFIG_SUBDIRS([libzmq])
fi

AC_ARG_WITH(
    [czmq],
    [AS_HELP_STRING([--with-czmq], [Configure CZMQ <:@default: false@:>@])],
    [with_czmq=yes],
    [with_czmq=no])

if test "x$with_czmq" = "xyes"; then
   AC_CONFIG_SUBDIRS([czmq])
fi

AC_OUTPUT
echo "Configure succeed. Now run make and make install."

