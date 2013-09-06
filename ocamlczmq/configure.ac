# These lines are required
AC_PREREQ(2.59)
AC_INIT([ocamlczmq], [0.9], [christoph-sticksel@uiowa.edu])

# This just checks if some source file is present
AC_CONFIG_SRCDIR([src/ZMQ.ml])

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

AC_CONFIG_MACRO_DIR([m4])

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

# Check for zmq library 
AC_ARG_WITH([libzmq],
            [AS_HELP_STRING([--with-libzmq],
                            [Specify libzmq prefix])],
            [search_libzmq="yes"],
            [])

if test "x$search_libzmq" = "xyes"; then
    if test -r "${with_libzmq}/include/zmq.h"; then
        CFLAGS="-I${with_libzmq}/include ${CFLAGS}"
        LDFLAGS="-L${with_libzmq}/lib ${LDFLAGS}"
        OCAMLCZMQ_LFLAGS="-L${with_libzmq}/lib ${OCAMLCZMQ_LFLAGS}"
        OCAMLCZMQ_CCOPTFLAGS="-ccopt -L${with_libzmq}/lib ${OCAMLCZMQ_CCOPTFLAGS}"
        CZMQ_CONFFLAGS="--with-libzmq=${with_libzmq}"
    else
        AC_MSG_ERROR([${with_libzmq}/include/zmq.h not found. Please check libzmq prefix])
    fi
fi

AC_CHECK_LIB(zmq, zmq_init, ,[AC_MSG_ERROR([cannot link with -lzmq, install libzmq.])])

AC_SUBST(CZMQ_CONFFLAGS)
AC_SUBST(OCAMLCZMQ_LFLAGS)
AC_SUBST(OCAMLCZMQ_CCOPTFLAGS)

AC_CONFIG_FILES([Makefile src/Makefile])

AC_OUTPUT
echo "Configure succeed. Now run make and make install."

