# These lines are required
AC_PREREQ(2.59)
AC_INIT([kind2], [0.1], [christoph-sticksel@uiowa.edu])

# This just checks if some source file is present
AC_CONFIG_SRCDIR([src/kind2.ml])

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

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

# ######################################################################
# Debug builds            
# ######################################################################

AC_ARG_ENABLE(
    [debug],
    AS_HELP_STRING([--enable-debug@<:@=TAGS@:>@], [Enable debug output, optionally give tags to enable @<:@default: no, --enable-debug enables all tags@:>@]),
    [],
    [enable_debug=no])

if test "x$enable_debug" = "xyes"; then
   static_camlp4_debug='*'

elif test "x$enable_debug" = "xno"; then
   static_camlp4_debug=''
     
else
   static_camlp4_debug=$enable_debug
fi

AC_SUBST(static_camlp4_debug)

# ######################################################################
# Check for SMT solvers 
# ######################################################################

# Check for Z3 

# yes if --with-z3, no if --without-z3, or <arg> if --with-z3=<arg>
AC_ARG_WITH(
    [z3],
    [AS_HELP_STRING([--with-z3@<:@=ARG@:>@], [Enable Z3 and use executable ARG @<:@default: search for Z3 in path@:>@])],
    [],
    [with_z3=yes])

# Z3 disabled 
if test "x$with_z3" = "xno"; then
    have_z3=no

# Z3 enabled, search in path
elif test "x$with_z3" = "xyes"; then

    # Check for z3 in path     
    AC_PATH_PROG([with_z3],[z3],[no])

    # Z3 found in path? 
    if test "x$with_z3" != "xno"; then

        # Enable Z3 and use found executable
        have_z3=yes
        Z3_BIN=$with_z3

    else

        # Disable Z3
        have_z3=no

    fi

else

    # Enable Z3 and use given executable
    have_z3=yes
    Z3_BIN=$with_z3

fi

# Check for CVC4

# yes if --with-cvc4, no if --without-cvc4, or <arg> if --with-cvc4=<arg>
AC_ARG_WITH(
    [cvc4],
    [AS_HELP_STRING([--with-cvc4@<:@=ARG@:>@], [Enable CVC4 and use executable ARG @<:@default: search for CVC4 in path@:>@])],
    [],
    [with_cvc4=yes])

# CVC4 disabled 
if test "x$with_cvc4" = "xno"; then
    have_cvc4=no

# CVC4 enabled, search in path
elif test "x$with_cvc4" = "xyes"; then

    # Check for CVC4 in path     
    AC_PATH_PROG([with_cvc4],[cvc4],[no])

    # CVC4 found in path? 
    if test "x$with_cvc4" != "xno"; then

        # Enable CVC4 and use found executable
        have_cvc4=yes
        CVC4_BIN=$with_cvc4

    else

        # Disable CVC4
        have_cvc4=no

    fi

else

    # Enable CVC4 and use given executable
    have_cvc4=yes
    CVC4_BIN=$with_cvc4

fi


# Check for MathSAT5

# yes if --with-mathsat5, no if --without-mathsat5, or <arg> if --with-mathsat5=<arg>
AC_ARG_WITH(
    [mathsat5],
    [AS_HELP_STRING([--with-mathsat5@<:@=ARG@:>@], [Enable MathSAT5 and use executable ARG @<:@default: search for MathSAT5 in path@:>@])],
    [],
    [with_mathsat5=yes])

# MATHSAT5 disabled 
if test "x$with_mathsat5" = "xno"; then
    have_mathsat5=no

# MATHSAT5 enabled, search in path
elif test "x$with_mathsat5" = "xyes"; then

    # Check for MATHSAT5 in path     
    AC_PATH_PROG([with_mathsat5],[mathsat],[no])

    # MATHSAT5 found in path? 
    if test "x$with_mathsat5" != "xno"; then

        # Enable MATHSAT5 and use found executable
        have_mathsat5=yes
        MATHSAT5_BIN=$with_mathsat5

    else

        # Disable MATHSAT5
        have_mathsat5=no

    fi

else

    # Enable MATHSAT5 and use given executable
    have_mathsat5=yes
    MATHSAT5_BIN=$with_mathsat5

fi


# Default SMT solver
AC_ARG_WITH(
    [default_smtsolver],
    [AS_HELP_STRING([--with-default-smtsolver@<:@=ARG@:>@], [Default SMT solver @<:@default: Z3 if possible, otherwise CVC4@:>@])],
    [],
    [with_default_smtsolver=z3])


# Check if Z3 available
if test "x$have_z3" = "xno"; then

   # Check if CVC4 available
   if test "x$have_cvc4" = "xno"; then

      AC_MSG_ERROR([Must have at least one SMT solver, use --with-z3 or --with-cvc4])
   
   else

       # Only CVC4 available
       AC_MSG_NOTICE([CVC4 is the default solver])
       SMTSOLVER=SMTLIBSolver
       SMTLIBSOLVER_CONFIG=smtlibsolver_config_cvc4
           
   fi     

else

   # Check if CVC4 available
   if test "x$have_cvc4" = "xno"; then
   
      # Only Z3 available
      AC_MSG_NOTICE([Z3 is the default solver])
      SMTSOLVER=SMTLIBSolver
      SMTLIBSOLVER_CONFIG=smtlibsolver_config_z3

   else

      # Both CVC4 and Z3 available, check for default
      if test "x$with_default_smtsolver" = "xz3"; then

         AC_MSG_NOTICE([Z3 is the default solver])
         SMTSOLVER=SMTLIBSolver
         SMTLIBSOLVER_CONFIG=smtlibsolver_config_z3
   
      elif test "x$with_default_smtsolver" = "xcvc4"; then

         AC_MSG_NOTICE([CVC4 is the default solver])
         SMTSOLVER=SMTLIBSolver
         SMTLIBSOLVER_CONFIG=smtlibsolver_config_cvc4

      else

        AC_MSG_ERROR([Unknown default SMT solver])

      fi

   fi 

fi



# Substitute for SMT solver
AC_SUBST(SMTSOLVER)

# Substitute for Z3 binary
AC_SUBST(Z3_BIN)

# Substitute for CVC4 binary
AC_SUBST(CVC4_BIN)



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
AC_CONFIG_FILES([Makefile src/Makefile src/myocamlbuild.ml src/config.ml src/flags.ml src/kind1/solvers_path.ml server/Makefile server/myocamlbuild.ml])

# Write configuration files
AC_OUTPUT
