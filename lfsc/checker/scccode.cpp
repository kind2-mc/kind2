#include "scccode.h"

Expr* e_cln;
Expr* e_clc;
Expr* e_concat_cl;
Expr* e_clr;
Expr* e_pos;
Expr* e_neg;
Expr* e_tt;
Expr* e_ff;
Expr* e_and;
Expr* e_not;
Expr* e_or;
Expr* e_append;
Expr* e_simplify_clause;
Expr* e_unroll_from;
Expr* e_base_k;
Expr* e_base;
Expr* e_unroll_with;
Expr* e_step;

void init_compiled_scc(){
   e_cln = symbols->get("cln").first;
   e_clc = symbols->get("clc").first;
   e_concat_cl = symbols->get("concat_cl").first;
   e_clr = symbols->get("clr").first;
   e_pos = symbols->get("pos").first;
   e_neg = symbols->get("neg").first;
   e_tt = symbols->get("tt").first;
   e_ff = symbols->get("ff").first;
   e_and = symbols->get("and").first;
   e_not = symbols->get("not").first;
   e_or = symbols->get("or").first;
   e_append = progs["append"];
   e_simplify_clause = progs["simplify_clause"];
   e_unroll_from = progs["unroll_from"];
   e_base_k = progs["base_k"];
   e_base = progs["base"];
   e_unroll_with = progs["unroll_with"];
   e_step = progs["step"];
}

Expr* run_compiled_scc( Expr* p, std::vector< Expr* >& args ){
   if( p==e_append ){
      return f_append( args[0], args[1] );
   }else if( p==e_simplify_clause ){
      return f_simplify_clause( args[0] );
   }else if( p==e_unroll_from ){
      return f_unroll_from( args[0], args[1], args[2] );
   }else if( p==e_base_k ){
      return f_base_k( args[0], args[1], args[2], args[3] );
   }else if( p==e_base ){
      return f_base( args[0], args[1], args[2], args[3] );
   }else if( p==e_unroll_with ){
      return f_unroll_with( args[0], args[1], args[2] );
   }else if( p==e_step ){
      return f_step( args[0], args[1], args[2] );
   }else{
      return NULL;
   }
}

Expr* f_append( Expr* c1, Expr* c2 ){
   Expr* e0;
   c1->inc();
   Expr* e1 = c1->followDefs()->get_head();
   Expr* e2;
   e2 = e_cln;
   e2->inc();
   Expr* e3;
   e3 = e_clc;
   e3->inc();
   if( e1==e2 ){
      e0 = c2;
      e0->inc();
   }else if( e1==e3 ){
      Expr* l = ((CExpr*)c1->followDefs())->kids[1];
      Expr* c1h = ((CExpr*)c1->followDefs())->kids[2];
      l->inc();
      Expr* e4;
      c1h->inc();
      c2->inc();
      e4 = f_append( c1h, c2 );
      c1h->dec();
      c2->dec();
      static Expr* e5;
      e5 = e_clc;
      e5->inc();
      e0 = new CExpr( APP, e5, l, e4 );
   }else{
      std::cout << "Could not find match for expression in function f_append ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   c1->dec();
   e2->dec();
   e3->dec();
   return e0;
}

Expr* f_simplify_clause( Expr* c ){
   Expr* e0;
   c->inc();
   Expr* e1 = c->followDefs()->get_head();
   Expr* e2;
   e2 = e_cln;
   e2->inc();
   Expr* e3;
   e3 = e_clc;
   e3->inc();
   Expr* e4;
   e4 = e_concat_cl;
   e4->inc();
   Expr* e5;
   e5 = e_clr;
   e5->inc();
   if( e1==e2 ){
      e0 = e_cln;
      e0->inc();
   }else if( e1==e3 ){
      Expr* l = ((CExpr*)c->followDefs())->kids[1];
      Expr* c1 = ((CExpr*)c->followDefs())->kids[2];
      l->inc();
      Expr* e6 = l->followDefs()->get_head();
      Expr* e7;
      e7 = e_pos;
      e7->inc();
      Expr* e8;
      e8 = e_neg;
      e8->inc();
      if( e6==e7 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e9;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e9 = v;
            e9->inc();
            v->dec();
            e9->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         m->inc();
         Expr* e10 = m->followDefs()->get_head();
         Expr* e11;
         e11 = e_tt;
         e11->inc();
         Expr* e12;
         e12 = e_ff;
         e12->inc();
         if( e10==e11 ){
            Expr* e13;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2)){
               e13 = v;
               e13->inc();
            }else{
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e13 = v;
               e13->inc();
               v->dec();
            }
            v->dec();
            e13->dec();
            e0 = ch;
            e0->inc();
         }else if( e10==e12 ){
            Expr* e14;
            Expr* e15;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2)){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e15 = v;
               e15->inc();
               v->dec();
            }else{
               e15 = v;
               e15->inc();
            }
            v->dec();
            e15->dec();
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e14 = v;
            e14->inc();
            v->dec();
            e14->dec();
            l->inc();
            ch->inc();
            static Expr* e16;
            e16 = e_clc;
            e16->inc();
            e0 = new CExpr( APP, e16, l, ch );
         }else{
            std::cout << "Could not find match for expression in function f_simplify_clause ";
            e10->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         m->dec();
         e11->dec();
         e12->dec();
         ch->dec();
         m->dec();
      }else if( e6==e8 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(1)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e17;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e17 = v;
            e17->inc();
            v->dec();
            e17->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         m->inc();
         Expr* e18 = m->followDefs()->get_head();
         Expr* e19;
         e19 = e_tt;
         e19->inc();
         Expr* e20;
         e20 = e_ff;
         e20->inc();
         if( e18==e19 ){
            Expr* e21;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3)){
               e21 = v;
               e21->inc();
            }else{
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e21 = v;
               e21->inc();
               v->dec();
            }
            v->dec();
            e21->dec();
            e0 = ch;
            e0->inc();
         }else if( e18==e20 ){
            Expr* e22;
            Expr* e23;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3)){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e23 = v;
               e23->inc();
               v->dec();
            }else{
               e23 = v;
               e23->inc();
            }
            v->dec();
            e23->dec();
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e22 = v;
            e22->inc();
            v->dec();
            e22->dec();
            l->inc();
            ch->inc();
            static Expr* e24;
            e24 = e_clc;
            e24->inc();
            e0 = new CExpr( APP, e24, l, ch );
         }else{
            std::cout << "Could not find match for expression in function f_simplify_clause ";
            e18->print( std::cout );
            std::cout << std::endl;
            exit( 1 );
         }
         m->dec();
         e19->dec();
         e20->dec();
         ch->dec();
         m->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause ";
         e6->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      l->dec();
      e7->dec();
      e8->dec();
   }else if( e1==e4 ){
      Expr* c1 = ((CExpr*)c->followDefs())->kids[1];
      Expr* c2 = ((CExpr*)c->followDefs())->kids[2];
      Expr* e25;
      c1->inc();
      e25 = f_simplify_clause( c1 );
      c1->dec();
      Expr* e26;
      c2->inc();
      e26 = f_simplify_clause( c2 );
      c2->dec();
      e0 = f_append( e25, e26 );
      e25->dec();
      e26->dec();
   }else if( e1==e5 ){
      Expr* l = ((CExpr*)c->followDefs())->kids[1];
      Expr* c1 = ((CExpr*)c->followDefs())->kids[2];
      l->inc();
      Expr* e27 = l->followDefs()->get_head();
      Expr* e28;
      e28 = e_pos;
      e28->inc();
      Expr* e29;
      e29 = e_neg;
      e29->inc();
      if( e27==e28 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(0)){
            m = e_tt;
            m->inc();
         }else{
            Expr* e30;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(0))
               ((SymExpr*)v->followDefs())->clearmark(0);
            else
               ((SymExpr*)v->followDefs())->setmark(0);
            e30 = v;
            e30->inc();
            v->dec();
            e30->dec();
            m = e_ff;
            m->inc();
         }
         v->dec();
         Expr* m3;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(2)){
            Expr* e31;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(2))
               ((SymExpr*)v->followDefs())->clearmark(2);
            else
               ((SymExpr*)v->followDefs())->setmark(2);
            e31 = v;
            e31->inc();
            v->dec();
            e31->dec();
            m3 = e_tt;
            m3->inc();
         }else{
            m3 = e_ff;
            m3->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(2)){
            Expr* e32;
            Expr* e33;
            m3->inc();
            Expr* e34 = m3->followDefs()->get_head();
            Expr* e35;
            e35 = e_tt;
            e35->inc();
            Expr* e36;
            e36 = e_ff;
            e36->inc();
            if( e34==e35 ){
               e33 = v;
               e33->inc();
            }else if( e34==e36 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(2))
                  ((SymExpr*)v->followDefs())->clearmark(2);
               else
                  ((SymExpr*)v->followDefs())->setmark(2);
               e33 = v;
               e33->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e34->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m3->dec();
            e35->dec();
            e36->dec();
            e33->dec();
            m->inc();
            Expr* e37 = m->followDefs()->get_head();
            Expr* e38;
            e38 = e_tt;
            e38->inc();
            Expr* e39;
            e39 = e_ff;
            e39->inc();
            if( e37==e38 ){
               e32 = v;
               e32->inc();
            }else if( e37==e39 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(0))
                  ((SymExpr*)v->followDefs())->clearmark(0);
               else
                  ((SymExpr*)v->followDefs())->setmark(0);
               e32 = v;
               e32->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e37->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m->dec();
            e38->dec();
            e39->dec();
            e32->dec();
            e0 = ch;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         ch->dec();
         m3->dec();
         m->dec();
      }else if( e27==e29 ){
         Expr* v = ((CExpr*)l->followDefs())->kids[1];
         Expr* m2;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(1)){
            m2 = e_tt;
            m2->inc();
         }else{
            Expr* e40;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(1))
               ((SymExpr*)v->followDefs())->clearmark(1);
            else
               ((SymExpr*)v->followDefs())->setmark(1);
            e40 = v;
            e40->inc();
            v->dec();
            e40->dec();
            m2 = e_ff;
            m2->inc();
         }
         v->dec();
         Expr* m4;
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(3)){
            Expr* e41;
            v->inc();
            if ( ((SymExpr*)v->followDefs())->getmark(3))
               ((SymExpr*)v->followDefs())->clearmark(3);
            else
               ((SymExpr*)v->followDefs())->setmark(3);
            e41 = v;
            e41->inc();
            v->dec();
            e41->dec();
            m4 = e_tt;
            m4->inc();
         }else{
            m4 = e_ff;
            m4->inc();
         }
         v->dec();
         Expr* ch;
         c1->inc();
         ch = f_simplify_clause( c1 );
         c1->dec();
         v->inc();
         if ( ((SymExpr*)v->followDefs())->getmark(3)){
            Expr* e42;
            Expr* e43;
            m4->inc();
            Expr* e44 = m4->followDefs()->get_head();
            Expr* e45;
            e45 = e_tt;
            e45->inc();
            Expr* e46;
            e46 = e_ff;
            e46->inc();
            if( e44==e45 ){
               e43 = v;
               e43->inc();
            }else if( e44==e46 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(3))
                  ((SymExpr*)v->followDefs())->clearmark(3);
               else
                  ((SymExpr*)v->followDefs())->setmark(3);
               e43 = v;
               e43->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e44->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m4->dec();
            e45->dec();
            e46->dec();
            e43->dec();
            m2->inc();
            Expr* e47 = m2->followDefs()->get_head();
            Expr* e48;
            e48 = e_tt;
            e48->inc();
            Expr* e49;
            e49 = e_ff;
            e49->inc();
            if( e47==e48 ){
               e42 = v;
               e42->inc();
            }else if( e47==e49 ){
               v->inc();
               if ( ((SymExpr*)v->followDefs())->getmark(1))
                  ((SymExpr*)v->followDefs())->clearmark(1);
               else
                  ((SymExpr*)v->followDefs())->setmark(1);
               e42 = v;
               e42->inc();
               v->dec();
            }else{
               std::cout << "Could not find match for expression in function f_simplify_clause ";
               e47->print( std::cout );
               std::cout << std::endl;
               exit( 1 );
            }
            m2->dec();
            e48->dec();
            e49->dec();
            e42->dec();
            e0 = ch;
            e0->inc();
         }else{
            e0 = NULL;
         }
         v->dec();
         ch->dec();
         m4->dec();
         m2->dec();
      }else{
         std::cout << "Could not find match for expression in function f_simplify_clause ";
         e27->print( std::cout );
         std::cout << std::endl;
         exit( 1 );
      }
      l->dec();
      e28->dec();
      e29->dec();
   }else{
      std::cout << "Could not find match for expression in function f_simplify_clause ";
      e1->print( std::cout );
      std::cout << std::endl;
      exit( 1 );
   }
   c->dec();
   e2->dec();
   e3->dec();
   e4->dec();
   e5->dec();
   return e0;
}

Expr* f_unroll_from( Expr* T, Expr* I, Expr* k ){
   Expr* e0;
   k->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e1;
               e1 = new IntExpr( (signed long int)0 );
               e1->inc();
               I->inc();
               e0 = new CExpr( APP, I, e1 );
            }else{
               Expr* j;
               k->inc();
               Expr* e2;
               e2 = new IntExpr( (signed long int)-1 );
               e2->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum0;
                  mpz_init(rnum0);
                  mpz_add( rnum0, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e2->followDefs())->n);
                  j = new IntExpr(rnum0);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum0;
                  mpq_init(rnum0);
                  mpq_add( rnum0, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e2->followDefs())->n);
                  j = new RatExpr(rnum0);
               }
               k->dec();
               e2->dec();
               Expr* e3;
               T->inc();
               I->inc();
               j->inc();
               e3 = f_unroll_from( T, I, j );
               T->dec();
               I->dec();
               j->dec();
               Expr* e4;
               j->inc();
               k->inc();
               T->inc();
               e4 = new CExpr( APP, T, j, k );
               static Expr* e5;
               e5 = e_and;
               e5->inc();
               e0 = new CExpr( APP, e5, e3, e4 );
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e6;
               e6 = new IntExpr( (signed long int)0 );
               e6->inc();
               I->inc();
               e0 = new CExpr( APP, I, e6 );
            }else{
               Expr* j;
               k->inc();
               Expr* e7;
               e7 = new IntExpr( (signed long int)-1 );
               e7->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum1;
                  mpz_init(rnum1);
                  mpz_add( rnum1, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e7->followDefs())->n);
                  j = new IntExpr(rnum1);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum1;
                  mpq_init(rnum1);
                  mpq_add( rnum1, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e7->followDefs())->n);
                  j = new RatExpr(rnum1);
               }
               k->dec();
               e7->dec();
               Expr* e8;
               T->inc();
               I->inc();
               j->inc();
               e8 = f_unroll_from( T, I, j );
               T->dec();
               I->dec();
               j->dec();
               Expr* e9;
               j->inc();
               k->inc();
               T->inc();
               e9 = new CExpr( APP, T, j, k );
               static Expr* e10;
               e10 = e_and;
               e10->inc();
               e0 = new CExpr( APP, e10, e8, e9 );
               j->dec();
            }
         }
         k->dec();
      }
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e11;
               e11 = new IntExpr( (signed long int)0 );
               e11->inc();
               I->inc();
               e0 = new CExpr( APP, I, e11 );
            }else{
               Expr* j;
               k->inc();
               Expr* e12;
               e12 = new IntExpr( (signed long int)-1 );
               e12->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum2;
                  mpz_init(rnum2);
                  mpz_add( rnum2, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e12->followDefs())->n);
                  j = new IntExpr(rnum2);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum2;
                  mpq_init(rnum2);
                  mpq_add( rnum2, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e12->followDefs())->n);
                  j = new RatExpr(rnum2);
               }
               k->dec();
               e12->dec();
               Expr* e13;
               T->inc();
               I->inc();
               j->inc();
               e13 = f_unroll_from( T, I, j );
               T->dec();
               I->dec();
               j->dec();
               Expr* e14;
               j->inc();
               k->inc();
               T->inc();
               e14 = new CExpr( APP, T, j, k );
               static Expr* e15;
               e15 = e_and;
               e15->inc();
               e0 = new CExpr( APP, e15, e13, e14 );
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e16;
               e16 = new IntExpr( (signed long int)0 );
               e16->inc();
               I->inc();
               e0 = new CExpr( APP, I, e16 );
            }else{
               Expr* j;
               k->inc();
               Expr* e17;
               e17 = new IntExpr( (signed long int)-1 );
               e17->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum3;
                  mpz_init(rnum3);
                  mpz_add( rnum3, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e17->followDefs())->n);
                  j = new IntExpr(rnum3);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum3;
                  mpq_init(rnum3);
                  mpq_add( rnum3, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e17->followDefs())->n);
                  j = new RatExpr(rnum3);
               }
               k->dec();
               e17->dec();
               Expr* e18;
               T->inc();
               I->inc();
               j->inc();
               e18 = f_unroll_from( T, I, j );
               T->dec();
               I->dec();
               j->dec();
               Expr* e19;
               j->inc();
               k->inc();
               T->inc();
               e19 = new CExpr( APP, T, j, k );
               static Expr* e20;
               e20 = e_and;
               e20->inc();
               e0 = new CExpr( APP, e20, e18, e19 );
               j->dec();
            }
         }
         k->dec();
      }
   }
   k->dec();
   return e0;
}

Expr* f_base_k( Expr* I, Expr* T, Expr* P, Expr* k ){
   Expr* e0;
   k->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e1;
               T->inc();
               I->inc();
               Expr* e2;
               e2 = new IntExpr( (signed long int)0 );
               e2->inc();
               e1 = f_unroll_from( T, I, e2 );
               T->dec();
               I->dec();
               e2->dec();
               Expr* e3;
               Expr* e4;
               Expr* e5;
               e5 = new IntExpr( (signed long int)0 );
               e5->inc();
               P->inc();
               e4 = new CExpr( APP, P, e5 );
               static Expr* e6;
               e6 = e_not;
               e6->inc();
               e3 = new CExpr( APP, e6, e4 );
               static Expr* e7;
               e7 = e_and;
               e7->inc();
               e0 = new CExpr( APP, e7, e1, e3 );
            }else{
               Expr* j;
               k->inc();
               Expr* e8;
               e8 = new IntExpr( (signed long int)-1 );
               e8->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum0;
                  mpz_init(rnum0);
                  mpz_add( rnum0, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e8->followDefs())->n);
                  j = new IntExpr(rnum0);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum0;
                  mpq_init(rnum0);
                  mpq_add( rnum0, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e8->followDefs())->n);
                  j = new RatExpr(rnum0);
               }
               k->dec();
               e8->dec();
               Expr* e9;
               I->inc();
               T->inc();
               P->inc();
               j->inc();
               e9 = f_base_k( I, T, P, j );
               I->dec();
               T->dec();
               P->dec();
               j->dec();
               Expr* e10;
               Expr* e11;
               T->inc();
               I->inc();
               k->inc();
               e11 = f_unroll_from( T, I, k );
               T->dec();
               I->dec();
               k->dec();
               Expr* e12;
               Expr* e13;
               k->inc();
               P->inc();
               e13 = new CExpr( APP, P, k );
               static Expr* e14;
               e14 = e_not;
               e14->inc();
               e12 = new CExpr( APP, e14, e13 );
               static Expr* e15;
               e15 = e_and;
               e15->inc();
               e10 = new CExpr( APP, e15, e11, e12 );
               static Expr* e16;
               e16 = e_or;
               e16->inc();
               e0 = new CExpr( APP, e16, e9, e10 );
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e17;
               T->inc();
               I->inc();
               Expr* e18;
               e18 = new IntExpr( (signed long int)0 );
               e18->inc();
               e17 = f_unroll_from( T, I, e18 );
               T->dec();
               I->dec();
               e18->dec();
               Expr* e19;
               Expr* e20;
               Expr* e21;
               e21 = new IntExpr( (signed long int)0 );
               e21->inc();
               P->inc();
               e20 = new CExpr( APP, P, e21 );
               static Expr* e22;
               e22 = e_not;
               e22->inc();
               e19 = new CExpr( APP, e22, e20 );
               static Expr* e23;
               e23 = e_and;
               e23->inc();
               e0 = new CExpr( APP, e23, e17, e19 );
            }else{
               Expr* j;
               k->inc();
               Expr* e24;
               e24 = new IntExpr( (signed long int)-1 );
               e24->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum1;
                  mpz_init(rnum1);
                  mpz_add( rnum1, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e24->followDefs())->n);
                  j = new IntExpr(rnum1);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum1;
                  mpq_init(rnum1);
                  mpq_add( rnum1, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e24->followDefs())->n);
                  j = new RatExpr(rnum1);
               }
               k->dec();
               e24->dec();
               Expr* e25;
               I->inc();
               T->inc();
               P->inc();
               j->inc();
               e25 = f_base_k( I, T, P, j );
               I->dec();
               T->dec();
               P->dec();
               j->dec();
               Expr* e26;
               Expr* e27;
               T->inc();
               I->inc();
               k->inc();
               e27 = f_unroll_from( T, I, k );
               T->dec();
               I->dec();
               k->dec();
               Expr* e28;
               Expr* e29;
               k->inc();
               P->inc();
               e29 = new CExpr( APP, P, k );
               static Expr* e30;
               e30 = e_not;
               e30->inc();
               e28 = new CExpr( APP, e30, e29 );
               static Expr* e31;
               e31 = e_and;
               e31->inc();
               e26 = new CExpr( APP, e31, e27, e28 );
               static Expr* e32;
               e32 = e_or;
               e32->inc();
               e0 = new CExpr( APP, e32, e25, e26 );
               j->dec();
            }
         }
         k->dec();
      }
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e33;
               T->inc();
               I->inc();
               Expr* e34;
               e34 = new IntExpr( (signed long int)0 );
               e34->inc();
               e33 = f_unroll_from( T, I, e34 );
               T->dec();
               I->dec();
               e34->dec();
               Expr* e35;
               Expr* e36;
               Expr* e37;
               e37 = new IntExpr( (signed long int)0 );
               e37->inc();
               P->inc();
               e36 = new CExpr( APP, P, e37 );
               static Expr* e38;
               e38 = e_not;
               e38->inc();
               e35 = new CExpr( APP, e38, e36 );
               static Expr* e39;
               e39 = e_and;
               e39->inc();
               e0 = new CExpr( APP, e39, e33, e35 );
            }else{
               Expr* j;
               k->inc();
               Expr* e40;
               e40 = new IntExpr( (signed long int)-1 );
               e40->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum2;
                  mpz_init(rnum2);
                  mpz_add( rnum2, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e40->followDefs())->n);
                  j = new IntExpr(rnum2);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum2;
                  mpq_init(rnum2);
                  mpq_add( rnum2, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e40->followDefs())->n);
                  j = new RatExpr(rnum2);
               }
               k->dec();
               e40->dec();
               Expr* e41;
               I->inc();
               T->inc();
               P->inc();
               j->inc();
               e41 = f_base_k( I, T, P, j );
               I->dec();
               T->dec();
               P->dec();
               j->dec();
               Expr* e42;
               Expr* e43;
               T->inc();
               I->inc();
               k->inc();
               e43 = f_unroll_from( T, I, k );
               T->dec();
               I->dec();
               k->dec();
               Expr* e44;
               Expr* e45;
               k->inc();
               P->inc();
               e45 = new CExpr( APP, P, k );
               static Expr* e46;
               e46 = e_not;
               e46->inc();
               e44 = new CExpr( APP, e46, e45 );
               static Expr* e47;
               e47 = e_and;
               e47->inc();
               e42 = new CExpr( APP, e47, e43, e44 );
               static Expr* e48;
               e48 = e_or;
               e48->inc();
               e0 = new CExpr( APP, e48, e41, e42 );
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e49;
               T->inc();
               I->inc();
               Expr* e50;
               e50 = new IntExpr( (signed long int)0 );
               e50->inc();
               e49 = f_unroll_from( T, I, e50 );
               T->dec();
               I->dec();
               e50->dec();
               Expr* e51;
               Expr* e52;
               Expr* e53;
               e53 = new IntExpr( (signed long int)0 );
               e53->inc();
               P->inc();
               e52 = new CExpr( APP, P, e53 );
               static Expr* e54;
               e54 = e_not;
               e54->inc();
               e51 = new CExpr( APP, e54, e52 );
               static Expr* e55;
               e55 = e_and;
               e55->inc();
               e0 = new CExpr( APP, e55, e49, e51 );
            }else{
               Expr* j;
               k->inc();
               Expr* e56;
               e56 = new IntExpr( (signed long int)-1 );
               e56->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum3;
                  mpz_init(rnum3);
                  mpz_add( rnum3, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e56->followDefs())->n);
                  j = new IntExpr(rnum3);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum3;
                  mpq_init(rnum3);
                  mpq_add( rnum3, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e56->followDefs())->n);
                  j = new RatExpr(rnum3);
               }
               k->dec();
               e56->dec();
               Expr* e57;
               I->inc();
               T->inc();
               P->inc();
               j->inc();
               e57 = f_base_k( I, T, P, j );
               I->dec();
               T->dec();
               P->dec();
               j->dec();
               Expr* e58;
               Expr* e59;
               T->inc();
               I->inc();
               k->inc();
               e59 = f_unroll_from( T, I, k );
               T->dec();
               I->dec();
               k->dec();
               Expr* e60;
               Expr* e61;
               k->inc();
               P->inc();
               e61 = new CExpr( APP, P, k );
               static Expr* e62;
               e62 = e_not;
               e62->inc();
               e60 = new CExpr( APP, e62, e61 );
               static Expr* e63;
               e63 = e_and;
               e63->inc();
               e58 = new CExpr( APP, e63, e59, e60 );
               static Expr* e64;
               e64 = e_or;
               e64->inc();
               e0 = new CExpr( APP, e64, e57, e58 );
               j->dec();
            }
         }
         k->dec();
      }
   }
   k->dec();
   return e0;
}

Expr* f_base( Expr* I, Expr* T, Expr* P, Expr* k ){
   Expr* e0;
   I->inc();
   T->inc();
   P->inc();
   Expr* e1;
   k->inc();
   Expr* e2;
   e2 = new IntExpr( (signed long int)-1 );
   e2->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      mpz_t rnum0;
      mpz_init(rnum0);
      mpz_add( rnum0, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e2->followDefs())->n);
      e1 = new IntExpr(rnum0);
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      mpq_t rnum0;
      mpq_init(rnum0);
      mpq_add( rnum0, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e2->followDefs())->n);
      e1 = new RatExpr(rnum0);
   }
   k->dec();
   e2->dec();
   e0 = f_base_k( I, T, P, e1 );
   I->dec();
   T->dec();
   P->dec();
   e1->dec();
   return e0;
}

Expr* f_unroll_with( Expr* T, Expr* P, Expr* k ){
   Expr* e0;
   k->inc();
   if( k->followDefs()->getclass()==INT_EXPR ){
      if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e1;
               e1 = new IntExpr( (signed long int)0 );
               e1->inc();
               P->inc();
               e0 = new CExpr( APP, P, e1 );
            }else{
               Expr* j;
               k->inc();
               Expr* e2;
               e2 = new IntExpr( (signed long int)-1 );
               e2->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum0;
                  mpz_init(rnum0);
                  mpz_add( rnum0, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e2->followDefs())->n);
                  j = new IntExpr(rnum0);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum0;
                  mpq_init(rnum0);
                  mpq_add( rnum0, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e2->followDefs())->n);
                  j = new RatExpr(rnum0);
               }
               k->dec();
               e2->dec();
               j->inc();
               if( j->followDefs()->getclass()==INT_EXPR ){
                  if( mpz_sgn( ((IntExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e3;
                     Expr* e4;
                     e4 = new IntExpr( (signed long int)0 );
                     e4->inc();
                     P->inc();
                     e3 = new CExpr( APP, P, e4 );
                     Expr* e5;
                     Expr* e6;
                     e6 = new IntExpr( (signed long int)0 );
                     e6->inc();
                     Expr* e7;
                     e7 = new IntExpr( (signed long int)1 );
                     e7->inc();
                     T->inc();
                     e5 = new CExpr( APP, T, e6, e7 );
                     static Expr* e8;
                     e8 = e_and;
                     e8->inc();
                     e0 = new CExpr( APP, e8, e3, e5 );
                  }else{
                     Expr* e9;
                     T->inc();
                     P->inc();
                     j->inc();
                     e9 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e10;
                     Expr* e11;
                     j->inc();
                     P->inc();
                     e11 = new CExpr( APP, P, j );
                     Expr* e12;
                     j->inc();
                     k->inc();
                     T->inc();
                     e12 = new CExpr( APP, T, j, k );
                     static Expr* e13;
                     e13 = e_and;
                     e13->inc();
                     e10 = new CExpr( APP, e13, e11, e12 );
                     static Expr* e14;
                     e14 = e_and;
                     e14->inc();
                     e0 = new CExpr( APP, e14, e9, e10 );
                  }
               }else if( j->followDefs()->getclass()==RAT_EXPR ){
                  if( mpq_sgn( ((RatExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e15;
                     Expr* e16;
                     e16 = new IntExpr( (signed long int)0 );
                     e16->inc();
                     P->inc();
                     e15 = new CExpr( APP, P, e16 );
                     Expr* e17;
                     Expr* e18;
                     e18 = new IntExpr( (signed long int)0 );
                     e18->inc();
                     Expr* e19;
                     e19 = new IntExpr( (signed long int)1 );
                     e19->inc();
                     T->inc();
                     e17 = new CExpr( APP, T, e18, e19 );
                     static Expr* e20;
                     e20 = e_and;
                     e20->inc();
                     e0 = new CExpr( APP, e20, e15, e17 );
                  }else{
                     Expr* e21;
                     T->inc();
                     P->inc();
                     j->inc();
                     e21 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e22;
                     Expr* e23;
                     j->inc();
                     P->inc();
                     e23 = new CExpr( APP, P, j );
                     Expr* e24;
                     j->inc();
                     k->inc();
                     T->inc();
                     e24 = new CExpr( APP, T, j, k );
                     static Expr* e25;
                     e25 = e_and;
                     e25->inc();
                     e22 = new CExpr( APP, e25, e23, e24 );
                     static Expr* e26;
                     e26 = e_and;
                     e26->inc();
                     e0 = new CExpr( APP, e26, e21, e22 );
                  }
               }
               j->dec();
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e27;
               e27 = new IntExpr( (signed long int)0 );
               e27->inc();
               P->inc();
               e0 = new CExpr( APP, P, e27 );
            }else{
               Expr* j;
               k->inc();
               Expr* e28;
               e28 = new IntExpr( (signed long int)-1 );
               e28->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum1;
                  mpz_init(rnum1);
                  mpz_add( rnum1, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e28->followDefs())->n);
                  j = new IntExpr(rnum1);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum1;
                  mpq_init(rnum1);
                  mpq_add( rnum1, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e28->followDefs())->n);
                  j = new RatExpr(rnum1);
               }
               k->dec();
               e28->dec();
               j->inc();
               if( j->followDefs()->getclass()==INT_EXPR ){
                  if( mpz_sgn( ((IntExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e29;
                     Expr* e30;
                     e30 = new IntExpr( (signed long int)0 );
                     e30->inc();
                     P->inc();
                     e29 = new CExpr( APP, P, e30 );
                     Expr* e31;
                     Expr* e32;
                     e32 = new IntExpr( (signed long int)0 );
                     e32->inc();
                     Expr* e33;
                     e33 = new IntExpr( (signed long int)1 );
                     e33->inc();
                     T->inc();
                     e31 = new CExpr( APP, T, e32, e33 );
                     static Expr* e34;
                     e34 = e_and;
                     e34->inc();
                     e0 = new CExpr( APP, e34, e29, e31 );
                  }else{
                     Expr* e35;
                     T->inc();
                     P->inc();
                     j->inc();
                     e35 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e36;
                     Expr* e37;
                     j->inc();
                     P->inc();
                     e37 = new CExpr( APP, P, j );
                     Expr* e38;
                     j->inc();
                     k->inc();
                     T->inc();
                     e38 = new CExpr( APP, T, j, k );
                     static Expr* e39;
                     e39 = e_and;
                     e39->inc();
                     e36 = new CExpr( APP, e39, e37, e38 );
                     static Expr* e40;
                     e40 = e_and;
                     e40->inc();
                     e0 = new CExpr( APP, e40, e35, e36 );
                  }
               }else if( j->followDefs()->getclass()==RAT_EXPR ){
                  if( mpq_sgn( ((RatExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e41;
                     Expr* e42;
                     e42 = new IntExpr( (signed long int)0 );
                     e42->inc();
                     P->inc();
                     e41 = new CExpr( APP, P, e42 );
                     Expr* e43;
                     Expr* e44;
                     e44 = new IntExpr( (signed long int)0 );
                     e44->inc();
                     Expr* e45;
                     e45 = new IntExpr( (signed long int)1 );
                     e45->inc();
                     T->inc();
                     e43 = new CExpr( APP, T, e44, e45 );
                     static Expr* e46;
                     e46 = e_and;
                     e46->inc();
                     e0 = new CExpr( APP, e46, e41, e43 );
                  }else{
                     Expr* e47;
                     T->inc();
                     P->inc();
                     j->inc();
                     e47 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e48;
                     Expr* e49;
                     j->inc();
                     P->inc();
                     e49 = new CExpr( APP, P, j );
                     Expr* e50;
                     j->inc();
                     k->inc();
                     T->inc();
                     e50 = new CExpr( APP, T, j, k );
                     static Expr* e51;
                     e51 = e_and;
                     e51->inc();
                     e48 = new CExpr( APP, e51, e49, e50 );
                     static Expr* e52;
                     e52 = e_and;
                     e52->inc();
                     e0 = new CExpr( APP, e52, e47, e48 );
                  }
               }
               j->dec();
               j->dec();
            }
         }
         k->dec();
      }
   }else if( k->followDefs()->getclass()==RAT_EXPR ){
      if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) < 0 ){
         e0 = NULL;
      }else{
         k->inc();
         if( k->followDefs()->getclass()==INT_EXPR ){
            if( mpz_sgn( ((IntExpr *)k->followDefs())->n ) == 0 ){
               Expr* e53;
               e53 = new IntExpr( (signed long int)0 );
               e53->inc();
               P->inc();
               e0 = new CExpr( APP, P, e53 );
            }else{
               Expr* j;
               k->inc();
               Expr* e54;
               e54 = new IntExpr( (signed long int)-1 );
               e54->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum2;
                  mpz_init(rnum2);
                  mpz_add( rnum2, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e54->followDefs())->n);
                  j = new IntExpr(rnum2);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum2;
                  mpq_init(rnum2);
                  mpq_add( rnum2, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e54->followDefs())->n);
                  j = new RatExpr(rnum2);
               }
               k->dec();
               e54->dec();
               j->inc();
               if( j->followDefs()->getclass()==INT_EXPR ){
                  if( mpz_sgn( ((IntExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e55;
                     Expr* e56;
                     e56 = new IntExpr( (signed long int)0 );
                     e56->inc();
                     P->inc();
                     e55 = new CExpr( APP, P, e56 );
                     Expr* e57;
                     Expr* e58;
                     e58 = new IntExpr( (signed long int)0 );
                     e58->inc();
                     Expr* e59;
                     e59 = new IntExpr( (signed long int)1 );
                     e59->inc();
                     T->inc();
                     e57 = new CExpr( APP, T, e58, e59 );
                     static Expr* e60;
                     e60 = e_and;
                     e60->inc();
                     e0 = new CExpr( APP, e60, e55, e57 );
                  }else{
                     Expr* e61;
                     T->inc();
                     P->inc();
                     j->inc();
                     e61 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e62;
                     Expr* e63;
                     j->inc();
                     P->inc();
                     e63 = new CExpr( APP, P, j );
                     Expr* e64;
                     j->inc();
                     k->inc();
                     T->inc();
                     e64 = new CExpr( APP, T, j, k );
                     static Expr* e65;
                     e65 = e_and;
                     e65->inc();
                     e62 = new CExpr( APP, e65, e63, e64 );
                     static Expr* e66;
                     e66 = e_and;
                     e66->inc();
                     e0 = new CExpr( APP, e66, e61, e62 );
                  }
               }else if( j->followDefs()->getclass()==RAT_EXPR ){
                  if( mpq_sgn( ((RatExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e67;
                     Expr* e68;
                     e68 = new IntExpr( (signed long int)0 );
                     e68->inc();
                     P->inc();
                     e67 = new CExpr( APP, P, e68 );
                     Expr* e69;
                     Expr* e70;
                     e70 = new IntExpr( (signed long int)0 );
                     e70->inc();
                     Expr* e71;
                     e71 = new IntExpr( (signed long int)1 );
                     e71->inc();
                     T->inc();
                     e69 = new CExpr( APP, T, e70, e71 );
                     static Expr* e72;
                     e72 = e_and;
                     e72->inc();
                     e0 = new CExpr( APP, e72, e67, e69 );
                  }else{
                     Expr* e73;
                     T->inc();
                     P->inc();
                     j->inc();
                     e73 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e74;
                     Expr* e75;
                     j->inc();
                     P->inc();
                     e75 = new CExpr( APP, P, j );
                     Expr* e76;
                     j->inc();
                     k->inc();
                     T->inc();
                     e76 = new CExpr( APP, T, j, k );
                     static Expr* e77;
                     e77 = e_and;
                     e77->inc();
                     e74 = new CExpr( APP, e77, e75, e76 );
                     static Expr* e78;
                     e78 = e_and;
                     e78->inc();
                     e0 = new CExpr( APP, e78, e73, e74 );
                  }
               }
               j->dec();
               j->dec();
            }
         }else if( k->followDefs()->getclass()==RAT_EXPR ){
            if( mpq_sgn( ((RatExpr *)k->followDefs())->n ) == 0 ){
               Expr* e79;
               e79 = new IntExpr( (signed long int)0 );
               e79->inc();
               P->inc();
               e0 = new CExpr( APP, P, e79 );
            }else{
               Expr* j;
               k->inc();
               Expr* e80;
               e80 = new IntExpr( (signed long int)-1 );
               e80->inc();
               if( k->followDefs()->getclass()==INT_EXPR ){
                  mpz_t rnum3;
                  mpz_init(rnum3);
                  mpz_add( rnum3, ((IntExpr*)k->followDefs())->n, ((IntExpr*)e80->followDefs())->n);
                  j = new IntExpr(rnum3);
               }else if( k->followDefs()->getclass()==RAT_EXPR ){
                  mpq_t rnum3;
                  mpq_init(rnum3);
                  mpq_add( rnum3, ((RatExpr*)k->followDefs())->n, ((RatExpr*)e80->followDefs())->n);
                  j = new RatExpr(rnum3);
               }
               k->dec();
               e80->dec();
               j->inc();
               if( j->followDefs()->getclass()==INT_EXPR ){
                  if( mpz_sgn( ((IntExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e81;
                     Expr* e82;
                     e82 = new IntExpr( (signed long int)0 );
                     e82->inc();
                     P->inc();
                     e81 = new CExpr( APP, P, e82 );
                     Expr* e83;
                     Expr* e84;
                     e84 = new IntExpr( (signed long int)0 );
                     e84->inc();
                     Expr* e85;
                     e85 = new IntExpr( (signed long int)1 );
                     e85->inc();
                     T->inc();
                     e83 = new CExpr( APP, T, e84, e85 );
                     static Expr* e86;
                     e86 = e_and;
                     e86->inc();
                     e0 = new CExpr( APP, e86, e81, e83 );
                  }else{
                     Expr* e87;
                     T->inc();
                     P->inc();
                     j->inc();
                     e87 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e88;
                     Expr* e89;
                     j->inc();
                     P->inc();
                     e89 = new CExpr( APP, P, j );
                     Expr* e90;
                     j->inc();
                     k->inc();
                     T->inc();
                     e90 = new CExpr( APP, T, j, k );
                     static Expr* e91;
                     e91 = e_and;
                     e91->inc();
                     e88 = new CExpr( APP, e91, e89, e90 );
                     static Expr* e92;
                     e92 = e_and;
                     e92->inc();
                     e0 = new CExpr( APP, e92, e87, e88 );
                  }
               }else if( j->followDefs()->getclass()==RAT_EXPR ){
                  if( mpq_sgn( ((RatExpr *)j->followDefs())->n ) == 0 ){
                     Expr* e93;
                     Expr* e94;
                     e94 = new IntExpr( (signed long int)0 );
                     e94->inc();
                     P->inc();
                     e93 = new CExpr( APP, P, e94 );
                     Expr* e95;
                     Expr* e96;
                     e96 = new IntExpr( (signed long int)0 );
                     e96->inc();
                     Expr* e97;
                     e97 = new IntExpr( (signed long int)1 );
                     e97->inc();
                     T->inc();
                     e95 = new CExpr( APP, T, e96, e97 );
                     static Expr* e98;
                     e98 = e_and;
                     e98->inc();
                     e0 = new CExpr( APP, e98, e93, e95 );
                  }else{
                     Expr* e99;
                     T->inc();
                     P->inc();
                     j->inc();
                     e99 = f_unroll_with( T, P, j );
                     T->dec();
                     P->dec();
                     j->dec();
                     Expr* e100;
                     Expr* e101;
                     j->inc();
                     P->inc();
                     e101 = new CExpr( APP, P, j );
                     Expr* e102;
                     j->inc();
                     k->inc();
                     T->inc();
                     e102 = new CExpr( APP, T, j, k );
                     static Expr* e103;
                     e103 = e_and;
                     e103->inc();
                     e100 = new CExpr( APP, e103, e101, e102 );
                     static Expr* e104;
                     e104 = e_and;
                     e104->inc();
                     e0 = new CExpr( APP, e104, e99, e100 );
                  }
               }
               j->dec();
               j->dec();
            }
         }
         k->dec();
      }
   }
   k->dec();
   return e0;
}

Expr* f_step( Expr* T, Expr* P, Expr* k ){
   Expr* e0;
   Expr* e1;
   T->inc();
   P->inc();
   k->inc();
   e1 = f_unroll_with( T, P, k );
   T->dec();
   P->dec();
   k->dec();
   Expr* e2;
   Expr* e3;
   k->inc();
   P->inc();
   e3 = new CExpr( APP, P, k );
   static Expr* e4;
   e4 = e_not;
   e4->inc();
   e2 = new CExpr( APP, e4, e3 );
   static Expr* e5;
   e5 = e_and;
   e5->inc();
   e0 = new CExpr( APP, e5, e1, e2 );
   return e0;
}

