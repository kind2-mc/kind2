#ifndef SCC_CODE_H
#define SCC_CODE_H

#include "check.h"

void init_compiled_scc();

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args );

inline Expr* f_append( Expr* c1, Expr* c2 );

inline Expr* f_simplify_clause( Expr* c );

inline Expr* f_unroll_from( Expr* T, Expr* I, Expr* k );

inline Expr* f_base_k( Expr* I, Expr* T, Expr* P, Expr* k );

inline Expr* f_base( Expr* I, Expr* T, Expr* P, Expr* k );

inline Expr* f_unroll_with( Expr* T, Expr* P, Expr* k );

inline Expr* f_step( Expr* T, Expr* P, Expr* k );

#endif

