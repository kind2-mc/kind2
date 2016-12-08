# These lines are required
AC_PREREQ(2.59)
AC_INIT([kind2], [v1.0.1], [christoph-sticksel@uiowa.edu])

# This just checks if some source file is present
AC_CONFIG_SRCDIR([src/kind2.ml])

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

# Check for OCaml  
AC_PROG_OCAML      

if test "x$OCAMLOPT" = "xno"; then
  AC_MSG_ERROR([You must install the OCaml native-code compiler])
fi

# Check for OCaml 4.03 
if expr "$OCAMLVERSION" '<' '4.03' > /dev/null ; then
  AC_MSG_ERROR([OCaml version 4.03 or later required])
fi

# Check for OCaml findlib
AC_PROG_FINDLIB
if test "x$OCAMLFIND" = "xno"; then
   AC_MSG_WARN([You must install the OCaml findlib (the ocamlfind command)])
fi

# Check for menhir
AC_PROG_MENHIR
if test "x$MENHIR" = "xno"; then
   AC_MSG_ERROR([You must install the Menhir parser])
fi

# Check for C compiler
AC_PROG_CC

if test "x$CC" = "xno"; then
  AC_MSG_ERROR([You need a C compiler])
fi

# ######################################################################
# git version suffix      
# ######################################################################

AC_ARG_WITH(
    [version-suffix],
    AS_HELP_STRING([--with-version-suffix@<:@=VER@:>@], [Append version suffix to binary @<:@default: no, --with-version-suffix adds the git hash, --with-version-suffix=VER adds the suffix VER@:>@]),
    [],
    [with_version_suffix=no])

if test "x$with_version_suffix" = "xyes"; then
   bin_suffix='-`git rev-parse --short HEAD`'

elif test "x$with_version_suffix" = "xno"; then
   bin_suffix=''
     
else
   bin_suffix=$with_version_suffix
fi

AC_SUBST(bin_suffix)

dnl ######################################################################
dnl Debug builds            
dnl ######################################################################

dnl AC_ARG_ENABLE(
dnl     [debug],
dnl     AS_HELP_STRING([--enable-debug@<:@=TAGS@:>@], [Enable debug output, optionally give tags to enable @<:@default: no, --enable-debug enables all tags@:>@]),
dnl     [],
dnl     [enable_debug=no])

dnl if test "x$enable_debug" = "xyes"; then
dnl    static_camlp4_debug='*'

dnl elif test "x$enable_debug" = "xno"; then
dnl    static_camlp4_debug=''
     
dnl else
dnl    static_camlp4_debug=$enable_debug
dnl fi

dnl AC_SUBST(static_camlp4_debug)

dnl # ######################################################################
dnl # Check for SMT solvers 
dnl # ######################################################################

dnl # Check for Z3 

dnl # yes if --with-z3, no if --without-z3, or <arg> if --with-z3=<arg>
dnl AC_ARG_WITH(
dnl     [z3],
dnl     [AS_HELP_STRING([--with-z3@<:@=ARG@:>@], [Enable Z3 and use executable ARG @<:@default: search for Z3 in path@:>@])],
dnl     [],
dnl     [with_z3=yes])

dnl # Z3 disabled 
dnl if test "x$with_z3" = "xno"; then
dnl     have_z3=no

dnl # Z3 enabled, search in path
dnl elif test "x$with_z3" = "xyes"; then

dnl     # Check for z3 in path     
dnl     AC_PATH_PROG([with_z3],[z3],[no])

dnl     # Z3 found in path? 
dnl     if test "x$with_z3" != "xno"; then

dnl         # Enable Z3 and use found executable
dnl         have_z3=yes
dnl         Z3_BIN=$with_z3

dnl     else

dnl         # Disable Z3
dnl         have_z3=no

dnl     fi

dnl else

dnl     # Enable Z3 and use given executable
dnl     have_z3=yes
dnl     Z3_BIN=$with_z3

dnl fi

dnl # Check for CVC4

dnl # yes if --with-cvc4, no if --without-cvc4, or <arg> if --with-cvc4=<arg>
dnl AC_ARG_WITH(
dnl     [cvc4],
dnl     [AS_HELP_STRING([--with-cvc4@<:@=ARG@:>@], [Enable CVC4 and use executable ARG @<:@default: search for CVC4 in path@:>@])],
dnl     [],
dnl     [with_cvc4=yes])

dnl # CVC4 disabled 
dnl if test "x$with_cvc4" = "xno"; then
dnl     have_cvc4=no

dnl # CVC4 enabled, search in path
dnl elif test "x$with_cvc4" = "xyes"; then

dnl     # Check for CVC4 in path     
dnl     AC_PATH_PROG([with_cvc4],[cvc4],[no])

dnl     # CVC4 found in path? 
dnl     if test "x$with_cvc4" != "xno"; then

dnl         # Enable CVC4 and use found executable
dnl         have_cvc4=yes
dnl         CVC4_BIN=$with_cvc4

dnl     else

dnl         # Disable CVC4
dnl         have_cvc4=no

dnl     fi

dnl else

dnl     # Enable CVC4 and use given executable
dnl     have_cvc4=yes
dnl     CVC4_BIN=$with_cvc4

dnl fi


dnl # Check for MathSAT5

dnl # yes if --with-mathsat5, no if --without-mathsat5, or <arg> if --with-mathsat5=<arg>
dnl AC_ARG_WITH(
dnl     [mathsat5],
dnl     [AS_HELP_STRING([--with-mathsat5@<:@=ARG@:>@], [Enable MathSAT5 and use executable ARG @<:@default: search for MathSAT5 in path@:>@])],
dnl     [],
dnl     [with_mathsat5=yes])

dnl # MATHSAT5 disabled 
dnl if test "x$with_mathsat5" = "xno"; then
dnl     have_mathsat5=no

dnl # MATHSAT5 enabled, search in path
dnl elif test "x$with_mathsat5" = "xyes"; then

dnl     # Check for MATHSAT5 in path     
dnl     AC_PATH_PROG([with_mathsat5],[mathsat],[no])

dnl     # MATHSAT5 found in path? 
dnl     if test "x$with_mathsat5" != "xno"; then

dnl         # Enable MATHSAT5 and use found executable
dnl         have_mathsat5=yes
dnl         MATHSAT5_BIN=$with_mathsat5

dnl     else

dnl         # Disable MATHSAT5
dnl         have_mathsat5=no

dnl     fi

dnl else

dnl     # Enable MATHSAT5 and use given executable
dnl     have_mathsat5=yes
dnl     MATHSAT5_BIN=$with_mathsat5

dnl fi


dnl # Default SMT solver
dnl AC_ARG_WITH(
dnl     [default_smtsolver],
dnl     [AS_HELP_STRING([--with-default-smtsolver@<:@=ARG@:>@], [Default SMT solver @<:@default: Z3 if available, otherwise CVC4 if available, else MathSAT5@:>@])],
dnl     [],
dnl     [with_default_smtsolver=yes])


dnl # Z3 is set as default but not available
dnl if test "x$with_default_smtsolver" = "xz3" -a "x$have_z3" = "xno"; then

dnl     AC_MSG_ERROR([You selected Z3 as the default solver, but is not available. Remove the option --with-default-smtsolver or choose a different solver.])

dnl # Z3 is available and set as default
dnl elif test "x$with_default_smtsolver" = "xz3"; then
     
dnl     AC_MSG_NOTICE([Z3 is the default solver])
dnl     SMTSOLVER=SMTLIBSolver
dnl     SMTLIBSOLVER_CONFIG=smtlibsolver_config_z3

dnl # CVC4 is set as default but not available
dnl elif test "x$with_default_smtsolver" = "xcvc4" -a "x$have_cvc4" = "xno"; then

dnl     AC_MSG_ERROR([You selected CVC4 as the default solver, but is not available. Remove the option --with-default-smtsolver or choose a different solver.])

dnl # CVC4 is available and set as default
dnl elif test "x$with_default_smtsolver" = "xcvc4"; then
     
dnl     AC_MSG_NOTICE([CVC4 is the default solver])
dnl     SMTSOLVER=SMTLIBSolver
dnl     SMTLIBSOLVER_CONFIG=smtlibsolver_config_cvc4

dnl # MathSAT5 is set as default but not available
dnl elif test "x$with_default_smtsolver" = "xmathsat5" -a "x$have_mathsat5" = "xno"; then

dnl     AC_MSG_ERROR([You selected MathSAT5 as the default solver, but is not available. Remove the option --with-default-smtsolver or choose a different solver.])

dnl # MathSAT5 is available and set as default
dnl elif test "x$with_default_smtsolver" = "xmathsat5"; then  
     
dnl     AC_MSG_NOTICE([MathSAT5 is the default solver])
dnl     SMTSOLVER=SMTLIBSolver
dnl     SMTLIBSOLVER_CONFIG=smtlibsolver_config_mathsat5

dnl # No default chosen 
dnl elif test "x$with_default_smtsolver" = "xyes"; then  

dnl     # Z3 is not available
dnl     if test "x$have_z3" = "xno"; then
     
dnl         # CVC4 is not available
dnl         if test "x$have_cvc4" = "xno"; then
     
dnl             # MathSAT5 is not available
dnl             if test "x$have_mathsat5" = "xno"; then
     
dnl                 AC_MSG_ERROR([Must have at least one SMT solver, use --with-z3, --with-cvc4 or --with-mathsat5])
   
dnl             # MathSAT5 is available 
dnl             else

dnl                 AC_MSG_NOTICE([MathSAT5 is the default solver])
dnl                 SMTSOLVER=SMTLIBSolver
dnl                 SMTLIBSOLVER_CONFIG=smtlibsolver_config_mathsat5

dnl             fi

dnl         # CVC4 is available 
dnl         else

dnl             AC_MSG_NOTICE([CVC4 is the default solver])
dnl             SMTSOLVER=SMTLIBSolver
dnl             SMTLIBSOLVER_CONFIG=smtlibsolver_config_cvc4

dnl         fi

dnl     # Z3 is available 
dnl     else

dnl         AC_MSG_NOTICE([Z3 is the default solver])
dnl         SMTSOLVER=SMTLIBSolver
dnl         SMTLIBSOLVER_CONFIG=smtlibsolver_config_z3

dnl     fi

dnl fi


dnl # Substitute for SMT solver
dnl AC_SUBST(SMTSOLVER)

dnl # Substitute for Z3 binary
dnl AC_SUBST(Z3_BIN)

dnl # Substitute for CVC4 binary
dnl AC_SUBST(CVC4_BIN)

dnl # Substitute for CVC4 binary
dnl AC_SUBST(MATHSAT5_BIN)



# ######################################################################
# Check for interpolating SMT solvers 
# ######################################################################

# Check for iZ3 

# yes if --with-iz3, no if --without-iz3, or <arg> if --with-iz3=<arg>
AC_ARG_WITH(
    [iz3],
    [AS_HELP_STRING([--with-iz3@<:@=ARG@:>@], [Enable iZ3 and use executable ARG @<:@default: search for iz3 in path@:>@])],
    [],
    [with_iz3=yes])

# iZ3 disabled 
if test "x$with_iz3" = "xno"; then
    have_iz3=no

# iZ3 enabled, search in path
elif test "x$with_iz3" = "xyes"; then

    # Check for iz3 in path     
    AC_PATH_PROG([with_iz3],[iz3],[no])

    # iZ3 found in path? 
    if test "x$with_iz3" != "xno"; then

        # Enable iZ3 and use found executable
        have_iz3=yes
        IZ3_BIN=$with_iz3

    else

        # Disable iZ3
        have_iz3=no

    fi

else

    # Enable iZ3 and use given executable
    have_iz3=yes
    IZ3_BIN=$with_iz3

fi

# Substitute for iZ3 binary
AC_SUBST(IZ3_BIN)

AC_CONFIG_SUBDIRS([ocamlczmq])

# Configuration files
AC_CONFIG_FILES([Makefile src/Makefile src/myocamlbuild.ml src/kind2Config.ml server/Makefile server/myocamlbuild.ml])

# Write configuration files
AC_OUTPUT
