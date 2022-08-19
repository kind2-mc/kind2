#!/bin/bash

cat ${@:2} | grep WARNING
CHECK=$(cat ${@:2} | grep check)
[ -z "$CHECK" ] && echo "; WARNING: Empty proof!!!"

SIG_DIR=lfsc/signatures
SIGS="$SIG_DIR/cvc5/core_defs.plf \
    $SIG_DIR/cvc5/util_defs.plf \
    $SIG_DIR/cvc5/theory_def.plf \
    $SIG_DIR/cvc5/nary_programs.plf \
    $SIG_DIR/cvc5/boolean_programs.plf \
    $SIG_DIR/cvc5/boolean_rules.plf \
    $SIG_DIR/cvc5/cnf_rules.plf \
    $SIG_DIR/cvc5/equality_rules.plf \
    $SIG_DIR/cvc5/arith_programs.plf \
    $SIG_DIR/cvc5/arith_rules.plf \
    $SIG_DIR/cvc5/strings_programs.plf \
    $SIG_DIR/cvc5/strings_rules.plf \
    $SIG_DIR/cvc5/quantifiers_rules.plf \
    $SIG_DIR/kind2/kind2.plf"
$1 $SIGS ${@:2} >& lfsc.out

# recover macros for applications of arity 1,2,3, and simplify builtin syntax for constants
#sed -i.orig 's/(f_ite [^ \)]*)/f_ite/g' lfsc.out
sed -i.orig 's/(\ [^ ]* (\ [^ ]* (\ [^ ]* (apply (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*) [^ ]*))))/\1/g; s/(\ [^ ]* (\ [^ ]* (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*)))/\1/g; s/(\ [^ ]* (apply f_\([^ ]*\) [^ ]*))/\1/g; s/(var \([^ ]*\) [^ \)]*)/var_\1/g; s/(int \([^ \)]*\))/\1/g; s/emptystr/""/g; s/int\.//g' lfsc.out

cat lfsc.out
rm lfsc.out
