/* A new implementation of dependent types via Dosen's substructural categorial programming: example of the Yoneda lemma for fibrations

Applications: datatypes or 1+2=3 via 3 methods: natural numbers category via types, natural numbers object via adjunctions and category of finite sets/numbers via colimits
https://github.com/1337777/cartier/blob/master/cartierSolution14.lp

Cut-elimination in the double category of fibred profunctors with inner cut-eliminated adjunctions: 
https://github.com/1337777/cartier/blob/master/cartierSolution13.lp

The goal of this section is to demo that it is possible to do a roundtrip between the concrete data structures and the abstract prover grammar; this is very subtle. The concrete application of these datatypes is the computation with the addition function of two variables that 1+2=3 via 3 different methods: the natural numbers category via intrinsic types, the natural numbers object via adjunctions/product/exponential, and the category of finite sets/numbers via limits/colimits/coproducts.

the AlgebraicJulia library package is an attempt to add “functional language” features to the Julia scientific computing language, via category theory. This applied category theory on concrete data structures allows to achieve some amount of compositionality (function-based) features onto ordinary scientific computing. The AlgebraicJulia implementation essentially hacks and reimplements some pseudo-dependent-types domain-specific-language embedded within Julia. The present text claims that there is a better approach via the LambdaPi logical framework and Kosta Dosen's substructural categorial programming. This new approach allows, not only to compute with concrete data, but also to do so via a grammatical interface which is more strongly-typed and which enables the theorem proving/programming of the correctness-by-construction of the algorithms.

An updated file, https://github.com/1337777/cartier/blob/master/cartierSolution14.lp, now contains the correct-by-construction concrete computation of the data of limits and colimits in the concrete category of sets and its functor categories. The goal is to demo that it is possible to do a roundtrip between the concrete data structures and the abstract prover grammar; this is very subtle. But this demo now successfully works generically, including on this silly example: the limit/equalizer of a (inductive) diagram when the (inductive-hypothesis) product cone [12;11]×[22;21]×[33;32;31] now is given an extra constant arrow [22;21] → [33;32;31] onto 31, besides its old discrete base diagram. The output is the limit cone apex object and side arrows (and its universality): 
compute obj_category_Obj ((category_Obj_obj One) ∘>o (sigma_Fst (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram)));
(0,13,21,31) :: (0,13,22,31) :: (0,12,21,31) :: (0,12,22,31) :: (0,11,21,31) :: (0,11,22,31) :: nil

Also the other methods output concrete data; first via intrinsic types, then via adjunctions:

compute ((Product_pair_func (Succ_inj_nat_func (Succ_inj_nat_func Zero_inj_nat_func)) (Succ_inj_nat_func Zero_inj_nat_func)) ∘> add_nat_func);
// Succ_inj_nat_func (Succ_inj_nat_func (Succ_inj_nat_func Zero_inj_nat_func))

compute λ C : cat, (iprod_pair_hom (Product_pair_func (itermin_func C) (itermin_func C)) 
                      (Func_cov_hom (itermin_func C) Id_func) (Func_cov_hom (itermin_func C) Id_func)) '∘ (_)_'∘> 
((Id_hom _) ∘>'_(_) ∘' 
    ((Product_pair_cov_hom (Product_pair_func _ _) 
          (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func
          (Succ_inj_inat_hom C (Zero_inj_inat_hom C)) (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C))))
      '∘ (_)_'∘> (add_inat_hom C))); 
// λ C, Succ_inj_inat_hom C (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C)))

 */

// require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.FOL Blanqui.Lib.Eq Blanqui.Lib.Bool Blanqui.Lib.Nat Blanqui.Lib.List;
require open modos.cartierSolution13;

/* OUTLINE:
--- SECTION 1 : Natural numbers category via DATATYPES CATS/OPERATORS IN THE OUTER DOUBLECAT PROF
--- SECTION 2 : Natural numbers object, via DATATYPES OBJECTS/FUNCTORS IN ANY INNER PARTICULAR CAT AND INTERNAL ADJUNCTIONS/PRODUCTS/EXPONENTIALS
--- SECTION 2.1 : Alternative addition function via (encoded/non-intrinsic) multi-variable/parameter adjunction
--- SECTION 2.2 : TODO: Addition function via intrinsic/structural multi-variable adjunction and multivariable functors/profunctors...
--- SECTION 3 : Category of finite sets/numbers, and colimits/limits and addition/coproduct
 */


/* ---------------------------
SECTION 1 : Natural numbers category via DATATYPES CATS/OPERATORS IN THE OUTER DOUBLECAT PROF
 */

//REVIEW nomenclature: projection/copairing, pairing/univ, injection/cocase, case/couniv,... instead of intro , elim 
constant symbol FuncCat_cat : Π (A B : cat), cat ;
constant symbol FuncCat_proj_func : Π (A B : cat) , //no lack for accumulator because align assoc
 func (Product_cat A (FuncCat_cat A B)) B;
injective symbol FuncCat_pair_func : Π  [A B D : cat]
(F : func (Product_cat A D) B), func D (FuncCat_cat A B);
//TODO hom arrows for FuncCat

//naturality
rule $K ∘> (FuncCat_pair_func $F ) ↪ (FuncCat_pair_func ((Product_pairproj_right_func _ $K) ∘> $F));
//beta
rule (Product_pairproj_right_func $A (FuncCat_pair_func $F )) ∘> (FuncCat_proj_func $A $B ) ↪ $F ;
rule Product_pair_func $K (FuncCat_pair_func $F) ∘> (FuncCat_proj_func $A $B ) ↪ Product_pair_func $K Id_func ∘> $F;
//eta
rule (FuncCat_pair_func (FuncCat_proj_func $A $B ))  ↪ Id_func; 

constant symbol nat_cat : cat;
constant symbol Zero_inj_nat_func  : func Terminal_cat nat_cat;
constant symbol Succ_inj_nat_func :  Π [I], func I nat_cat →  func I nat_cat;
symbol case_nat_func [L0 : cat]
  (L0_zero : func Terminal_cat L0)
  (L0_succ : func L0 L0 ) :  func nat_cat L0;

// accumulation
rule $m ∘> (Succ_inj_nat_func $n) ↪ (Succ_inj_nat_func ($m ∘> $n));
// beta
rule (Zero_inj_nat_func) ∘> (case_nat_func $L0_zero $L0_succ) ↪ $L0_zero;
rule (Succ_inj_nat_func $n) ∘> (case_nat_func $L0_zero $L0_succ)
 ↪ ($n ∘> (case_nat_func $L0_zero $L0_succ)) ∘> $L0_succ;

symbol add_nat_func : func (Product_cat nat_cat nat_cat) nat_cat ≔
begin
have add' : func nat_cat (FuncCat_cat nat_cat nat_cat)
{ refine (case_nat_func _ _ ) 
  { refine FuncCat_pair_func _;
    refine (Product_proj_left_func _ _);
  }
  { refine FuncCat_pair_func _;
    refine Succ_inj_nat_func _;
    refine (FuncCat_proj_func _ _);
  };
};
refine ((Product_pairproj_right_func nat_cat add' ) ∘> (FuncCat_proj_func nat_cat nat_cat)) 
end;

compute ((Product_pair_func (Succ_inj_nat_func (Succ_inj_nat_func Zero_inj_nat_func)) (Succ_inj_nat_func Zero_inj_nat_func)) ∘> add_nat_func);
// Succ_inj_nat_func (Succ_inj_nat_func (Succ_inj_nat_func Zero_inj_nat_func))

/* ---------------------------
SECTION 2 : Natural numbers object, via DATATYPES OBJECTS/FUNCTORS IN ANY INNER PARTICULAR CAT AND INTERNAL ADJUNCTIONS/PRODUCTS/EXPONENTIALS
 */

constant symbol itermin_func (C : cat) : func (Terminal_cat) C;
constant symbol itermin_adj (C : cat) : adj (Terminal_func C) (itermin_func C);
symbol itermin_pair_hom [C : cat] [I] (L0 : func I C) 
:  hom L0 (Unit_mod Id_func (itermin_func C)) (Terminal_func I)
≔ (Adj_con_hom (itermin_adj C) Id_func L0);

symbol idiag_func (C : cat) : func C (Product_cat C C) 
≔ Product_pair_func [C] [C] [C] Id_func Id_func;
constant symbol iprod_func (C : cat) : func (Product_cat C C) C;
constant symbol idiag_iprod_adj (C : cat) : adj (idiag_func C) (iprod_func C);

symbol iprod_proj_left_hom [C : cat] [I] (N : func I (Product_cat C C)) [J] (Z : func J I) :
  hom ((Z ∘> N) ∘> (iprod_func C)) (Unit_mod Id_func ((Product_proj_left_func C C) <∘ N)) Z
  ≔ Func_cov_hom (Product_proj_left_func C C) _ ∘>'_(_) ∘' (Adj_cov_hom (idiag_iprod_adj C) N Z) ;
symbol iprod_proj_right_hom [C : cat] [I] (N : func I (Product_cat C C)) [J] (Z : func J I) :
  hom ((Z ∘> N) ∘> (iprod_func C)) (Unit_mod Id_func ((Product_proj_right_func C C) <∘ N)) Z
  ≔ Func_cov_hom (Product_proj_right_func C C) _ ∘>'_(_) ∘' (Adj_cov_hom (idiag_iprod_adj C) N Z) ;

constant symbol iprod_ladj_proj_left_hom [C : cat] [I] [I'] (N : func I I') (N' : func I' (Product_cat C C)) [J] (Z : func J I) :
  hom (Z ∘> N) (Unit_mod (N' /* TODO N' is Product */ ∘> (iprod_func C)) ((Product_proj_left_func C C) <∘ (N' <∘ N))) Z;

rule (Id_hom _) ∘>'_(_) ∘' (iprod_ladj_proj_left_hom $N $N' $Z) ↪ (iprod_proj_left_hom ($N ∘> $N') $Z);

rule (Product_pair_cov_hom (Product_pair_func _ _ ) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] $Y $f $g) '∘ ((_)_'∘> (iprod_ladj_proj_left_hom (Product_pair_func $F' $G') Id_func  Id_func)) 
↪ (iprod_ladj_proj_left_hom _  Id_func Id_func '∘ ((_)_'∘> $f)); 

symbol iprod_pair_hom [C : cat] [I] (N : func I (Product_cat C C)) [C'] [K0 : func C' C] [J] [L0 : func J C'] [M : func J I]
 (L0_fst : hom L0 (Unit_mod (/*Z ∘>*/ K0) ((Product_proj_left_func C C) <∘ N)) M)
 (L0_snd : hom L0 (Unit_mod (/*Z ∘>*/ K0) ((Product_proj_right_func C C) <∘ N)) M) :
 hom (L0 /*∘> Z*/) (Unit_mod K0 ((iprod_func C) <∘ N)) M ≔ 
 (Adj_con_hom (idiag_iprod_adj C) K0 Id_func) ∘>'_(_) ∘'  (Product_pair_cov_hom L0 Id_func Id_func M L0_fst L0_snd);

symbol const_func [C : cat] I (X : func Terminal_cat C) : func I C ≔ Terminal_func I ∘> X;

constant symbol iexp_func (C : cat) : func (Product_cat (Op_cat C) C) C;
constant symbol iprod_iexp_adj (C : cat) (X : func Terminal_cat C) : 
adj (Product_pair_func (const_func C X) Id_func ∘> (iprod_func C))
    ((Product_pair_func (const_func C (Op_func X)) Id_func) ∘> (iexp_func C));

constant symbol inat_func (C : cat) : func (Terminal_cat) C;
constant symbol Zero_inj_inat_hom (C : cat) : hom (itermin_func C) (Unit_mod Id_func (inat_func C)) Id_func;
constant symbol Succ_inj_inat_hom (C : cat) : Π [C0] [X0 : func C0 C] [I] [X: func I C0] [Y : func I _], 
 hom X (Unit_mod X0 (inat_func C)) Y → hom X (Unit_mod X0 (inat_func C)) Y;
symbol case_inat_hom [C : cat] [J] (Y : func Terminal_cat J) [L0 : func J C]  
 (L0_zero : hom (itermin_func C) (Unit_mod Id_func L0) Y)
 (L0_succ : /* Π (Y : func Terminal_cat J) , */  hom L0 (Unit_mod Id_func L0) Id_func):  //TODO... hmm nope, L0_succ already in context of Y
 hom (inat_func C) (Unit_mod Id_func L0) Y;

//natural
rule ($m '∘ (_)_'∘> (Succ_inj_inat_hom $C $n)) ↪ (Succ_inj_inat_hom $C ($m '∘ (_)_'∘> $n));
rule (Id_hom _) ∘>'_ (_) ∘' (Succ_inj_inat_hom $C $n) 
  ↪ (Succ_inj_inat_hom $C ((Id_hom _) ∘>'_ (_) ∘' $n));
// rule (Func_con_hom $F $G) ∘>'_ (_) ∘' (Succ_inj_inat_hom $C $n)   //not used?
//   ↪ (Succ_inj_inat_hom $C ((Func_con_hom $F $G) ∘>'_ (_) ∘' $n));
rule  Id_hom _ ∘>'_ (_) ∘' ($n '∘ (_)_'∘> (Zero_inj_inat_hom $C))  //TODO redo as accumulator for succ
↪ (Id_hom _ ∘>'_ (_) ∘' $n) '∘ (_)_'∘> (Zero_inj_inat_hom $C);

//beta
rule (Zero_inj_inat_hom $C) '∘ (_)_'∘> (case_inat_hom $Y $L0_zero $L0_succ)
  ↪ $L0_zero;
rule (Succ_inj_inat_hom $C $n) '∘ (_)_'∘> (case_inat_hom $Y $L0_zero $L0_succ)
  ↪ ($n '∘ (_)_'∘> (case_inat_hom $Y $L0_zero $L0_succ)) '∘ (_)_'∘> $L0_succ;

symbol addParam_inat_hom C : hom (inat_func C) (Unit_mod (Product_pair_func (const_func C (inat_func C)) Id_func ∘> (iprod_func C)) (inat_func C)) Id_func ≔
begin
assume C;
have add' : hom (inat_func C) (Unit_mod Id_func ((Product_pair_func (const_func C (Op_func (inat_func C))) Id_func ∘> (iexp_func C)) <∘ (inat_func C))) Id_func
{ refine (case_inat_hom _ _ _ ) 
  { refine ((Adj_con_hom (iprod_iexp_adj C (inat_func C))  Id_func Id_func) ∘>'_((inat_func C)) ∘' _ );
    refine iprod_ladj_proj_left_hom _ (Product_pair_func (const_func C (inat_func C)) Id_func) _;
  }
  { refine ((Adj_con_hom (iprod_iexp_adj C (inat_func C))  Id_func Id_func) ∘>'_((inat_func C)) ∘' _ );
    refine (Succ_inj_inat_hom C _);
    refine ( (Adj_cov_hom (iprod_iexp_adj C (inat_func C)) (inat_func C) Id_func) );
  };
};
refine (add' '∘ (_)_'∘> (Adj_cov_hom (iprod_iexp_adj C (inat_func C)) (inat_func C) Id_func));
end;

compute λ C : cat, ((Adj_con_hom (idiag_iprod_adj C) Id_func Id_func) ∘>'_(_) ∘' 
                    (Product_pair_cov_hom _ (Id_func) [Id_func] (Id_func) [Id_func] Id_func
                          (Succ_inj_inat_hom C (Zero_inj_inat_hom C))
                          (Func_cov_hom (itermin_func C) Id_func))) 
    '∘ (_)_'∘> ((Id_hom _) ∘>'_(_) ∘'  
                          ((Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C)))
                                  '∘ (_)_'∘> (addParam_inat_hom C)));
// λ C, Succ_inj_inat_hom C (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C)))

// TODO REVIEW obviously stuck computation, ?should be able to connect the two because action of adjoint functor is definabe from unit operationss, together with functoriality...
// compute λ C : cat, ((Adj_con_hom (idiag_iprod_adj C) Id_func Id_func) ∘>'_(_) ∘' 
//                     (Product_pair_cov_hom _ (Id_func) [Id_func] (Id_func) [Id_func] Id_func
//                           (Succ_inj_inat_hom C (Zero_inj_inat_hom C))
//                           (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C))))) 
//     '∘ (_)_'∘> ((Id_hom _) ∘>'_(_) ∘' (addParam_inat_hom C));
// compute λ C : cat, Product_pair_cov_hom (Product_pair_func _ _) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func
// (Succ_inj_inat_hom C (Zero_inj_inat_hom C))
// (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C)))
// '∘ (_)_'∘> ((Func_con_hom (iprod_func C) (Product_pair_func (const_func C (inat_func C)) Id_func)) ∘>'_(_) ∘' addParam_inat_hom C);

/* --- SECTION 2.1 : Alternative dddition function via (encoded/non-intrinsic) multi-variable/parameter adjunction
 */

constant symbol exp2_func (C : cat) : func (Product_cat (Op_cat C) C) C;
injective symbol adjProdExp2_lambda_hom [C : cat] : let I ≔ Terminal_cat in Π [X : func I C] [J] (P : func J C) [Z : func I J] [J'] (Q : func J' C) [Y : func I J'],
 hom ((Product_pair_func X Y)) (Unit_mod (Product_pairproj_right_func _ Q ∘> (iprod_func C)) P) Z
→ hom Y (Unit_mod Q (Product_pairproj_right_func _ P ∘> (exp2_func C))) (Product_pair_func (Op_func X) Z);
symbol adjProdExp2_eval_hom [C : cat] : let I ≔ Terminal_cat in Π [X : func I C] [J] (P : func J C) [Z : func I J] [J'] (Q : func J' C) [Y : func I J'],
hom Y (Unit_mod Q (Product_pairproj_right_func (Op_cat C) P ∘> (exp2_func C))) (Product_pair_func (Op_func X) Z)
→ hom ((Product_pair_func X Y)) (Unit_mod (Product_pairproj_right_func C Q ∘> (iprod_func C)) P) Z;

//beta
rule (adjProdExp2_eval_hom $P $Q (adjProdExp2_lambda_hom $P $Q $h)) ↪ $h;
//eta, 
//TODO: REVIEW slow, warning unjoinable with beta rule, note the loop with beta rule
// rule (adjProdExp2_lambda_hom $P $Q (adjProdExp2_eval_hom $P $Q  $h)) ↪ $h;

//TODO: REVIEW WHY: NOTE THAT MUST ASSOCIATE ON LEFT IN THE RESULT .. NOTE THAT THIS ASSOCIATIVITY IS NON-COMPUTATIONAL BUT ONLY PROPOSITIONAL
rule  (Product_pair_cov_hom (Product_pair_func _ _) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func $f $g) '∘ (_)_'∘> (adjProdExp2_eval_hom $P $Q  $h)
↪  (adjProdExp2_eval_hom $P $Q  (($g '∘ (_)_'∘> $h) ∘>'_(_) ∘' (Product_pair_con_hom (Product_pair_func _ _) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func (Op_hom $f) (Func_con_hom _ _) )  ));

rule adjProdExp2_lambda_hom $P $Q $h '∘ ((_)_'∘> ((Func_cov_hom (exp2_func $C) _ ∘>'_(_)) ∘' Product_pairproj_right_cov_hom [_] [_] [_] [$P] [$P'] $p))
↪ adjProdExp2_lambda_hom $P' $Q ($h '∘ ((_)_'∘> $p)) ;

rule  (adjProdExp2_lambda_hom $P $Q $h ∘>'_(_)) ∘' (Product_pair_con_hom (Product_pair_func _ _) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func $x $z)
↪ adjProdExp2_lambda_hom $P $Q ((Product_pair_cov_hom (Product_pair_func _ _) (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func (Op_hom $x) (Func_cov_hom _ Id_func)) '∘ (_)_'∘>
              ($h  ∘>'_(_) ∘' $z));

symbol add_inat_hom C : hom (Product_pair_func (inat_func C) (inat_func C)) (Unit_mod (iprod_func C) (inat_func C)) Id_func ≔
begin
assume C; refine adjProdExp2_eval_hom _ Id_func _;
refine  case_inat_hom _  _ _ 
{ refine adjProdExp2_lambda_hom [_] [inat_func C] (inat_func C) _ _ ;
  refine iprod_ladj_proj_left_hom _ Id_func _;
}
{ refine (Func_cov_hom (exp2_func C) _ ∘>'_(_) ∘' (Product_pairproj_right_cov_hom (Succ_inj_inat_hom C (Func_cov_hom _ Id_func))));
}
end;

//NOTE: this uses the naturality conversion ($x''x'_ '∘ ((Id_func)_'∘> ( ($s ∘>'_(_)) ∘' $y'y_ )))
// ↪ ($s ∘>'_(_)) ∘' ($x''x'_ '∘ ((Id_func)_'∘> ( $y'y_ ))) 
// to move out (Func_cov_hom (Product_proj_left_func C C) (Product_pair_func Id_func Id_func) ∘>'_(_) ∘'
compute λ C : cat, (iprod_pair_hom (Product_pair_func (itermin_func C) (itermin_func C)) 
                      (Func_cov_hom (itermin_func C) Id_func) (Func_cov_hom (itermin_func C) Id_func)) '∘ (_)_'∘> 
((Id_hom _) ∘>'_(_) ∘' 
    ((Product_pair_cov_hom (Product_pair_func _ _) 
          (Product_proj_left_func _ _) [Id_func] (Product_proj_right_func _ _) [Id_func] Id_func
          (Succ_inj_inat_hom C (Zero_inj_inat_hom C)) (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C))))
      '∘ (_)_'∘> (add_inat_hom C))); 
// λ C, Succ_inj_inat_hom C (Succ_inj_inat_hom C (Succ_inj_inat_hom C (Zero_inj_inat_hom C)))

// MEMO: REVERSE DEBUGGED: λ C, (((          ((Adj_con_hom (idiag_iprod_adj C) Id_func Id_func ∘>'_ Product_pair_func (itermin_func C) (itermin_func C)) ∘' Product_pair_cov_hom (itermin_func C) Id_func Id_func Id_func (Func_cov_hom (itermin_func C) Id_func) (Func_cov_hom (itermin_func C) Id_func) )           '∘ (Id_func _'∘> (  (Func_cov_hom (Product_proj_left_func C C) (Product_pair_func Id_func Id_func) ∘>'_ Product_pair_func (itermin_func C) (itermin_func C)) ∘' Adj_cov_hom (idiag_iprod_adj C) (Product_pair_func (itermin_func C) (itermin_func C)) Id_func)) )         '∘ (Id_func _'∘> Zero_inj_inat_hom C)) '∘ (Id_func _'∘> Succ_inj_inat_hom C)) '∘ (Id_func _'∘> Succ_inj_inat_hom C)

/* ---------------------------
SECTION 2.2 : TODO: Addition function via intrinsic/structural multi-variable adjunction and multivariable functors/profunctors...
 */

 ///// TODO:


/* ---------------------------
 SECTION 3 : Category of finite sets/numbers, and colimits/limits and addition/coproduct
 */
 
inductive one : TYPE ≔ One : one;
constant symbol one_Set : Set;
rule τ one_Set ↪ one;
  
constant symbol obj : Π C : cat, TYPE;
constant symbol obj_Set : Π C : cat, Set;
rule τ (obj_Set $C) ↪ obj $C;

symbol ∘>o: Π [Y Z : cat], obj Y → func Y Z → obj Z;
notation ∘>o infix left 90;

rule $X ∘>o ($G ∘> $H) ↪ ($X ∘>o $G) ∘>o $H
with $F ∘>o Id_func ↪ $F;

///TODO also dependent versions of One elim, and dependent One
//Terminal_cat ahas dual status as also datatype: 
//intro rule
constant symbol Terminal_obj : obj Terminal_cat; 
//elim rule, rename Terminal_elim_func ?
injective symbol Obj_func : Π [Y : cat], obj Y → func Terminal_cat Y ;

//computation rule, obj
//  rule (Terminal_obj) ∘>o (Obj_func $F) ↪  $F;
rule $M ∘>o (Obj_func $F) ↪  $F;

//TODO reverse also Terminal_elim_funcd... same as ordinarry cut-elim with functors
rule (Obj_func $F) ∘> $H ↪ (Obj_func ($F ∘>o $H));

injective symbol Op_obj : Π [ Y : cat] , obj Y → obj (Op_cat Y);
rule Op_obj ($F ∘>o $G) ↪ (Op_obj $F) ∘>o (Op_func $G); //or reverse?
rule Obj_func (Terminal_obj) ↪ Id_func; //as usual this causes non-constant symbol

constant symbol arr: Π [A B : cat], obj A → mod A B → obj B →  TYPE ;
constant symbol arr_Set: Π [A B : cat], obj A → mod A B → obj B → Set ;
rule τ (@arr_Set $A $B $F $R $G) ↪ (@arr $A $B $F $R $G);

//todo erase Id condition?
symbol '∘a : Π [A B' B : cat] [S : mod A B'] [T : mod A B]
[X : obj A] [Y : obj B']  [G : func B' B], //SHOULD X be Terminal_obj ?
arr X S Y → transf S Id_func T G → arr X T (Y ∘>o G);
notation '∘a infix right 80;
symbol ∘a' [A' B A : cat] [S : mod A' B] [T : mod A B]
[X : obj A'] [Y : obj B] [F : func A' A] : //SHOULD Y be Terminal_obj ?
transf S F T Id_func → arr X S Y → arr (X ∘>o F) T Y;
notation ∘a' infix left 80;

//todo both cov ad con of ''∘ (nahhh erase: only operator arrgument has Id frame)?
rule ($r '∘a $rs) '∘a $st
↪  $r '∘a ($rs ''∘ $st);
rule $r '∘a (Id_transf _) ↪ $r;
rule $st ∘a' ($rs ∘a' $r)
↪  ($st ∘'' $rs) ∘a' $r;
rule (Id_transf _) ∘a' $r ↪ $r;

/// aka terminalunitprofunctor_elim_hom, which, for one, contains also terminal_elim_cov_hom
//TODO redo
//  injective symbol Arr_hom: Π [A B : cat] [F : obj A] [R : mod A B] [G : obj B],  arr F R G → hom (Obj_func F) R (Obj_func G);
injective symbol Arr_hom /* terminalunitprofunctor_elim_hom */: 
Π [A B: cat] [R : mod A B]  (F : func Terminal_cat A) (G : func Terminal_cat B) 
(t_arr : arr (Terminal_obj ∘>o F) R (Terminal_obj ∘>o G)),
hom F R G;

symbol DEFINABLE_Arr_hom_instance_terminal_elim_cov_hom  [E  : cat] (F : func Terminal_cat E)  (G : func Terminal_cat E)
(t_arr : arr (Terminal_obj ∘>o F) (Unit_mod Id_func (G )) Terminal_obj) : //TODO  o<∘
  hom F (Unit_mod Id_func G) Id_func ≔ Arr_hom _ _ t_arr ;

//computation rule for Arr_hom
//reversed to tradeoff with more usual rule for datatype elimination... nope reversed back because elim now uses arr input
rule (Arr_hom _ _ $r) '∘ $t  ↪ (Arr_hom _ _ ($r '∘a $t));
rule  $t ∘' (Arr_hom _ _ $r)  ↪ (Arr_hom _ _ ($t ∘a' $r));

//TODO? Id_arr ?
// constant symbol Id_arr [A : cat] (F : obj A)  : arr F (Unit_mod Id_func Id_func) F;
// rule (Id_arr Terminal_obj) '∘a ( (_) _'∘> (Arr_hom $r)) ↪  $r;
// rule Arr_hom (Id_arr $F) ↪ Id_hom (Obj_func $F);

//TODO rename Func_cov_hom to Id_cov_hom because of this explanation: ?
//TODO redo Id_cov_arr for more general thant Id_func ?
constant symbol Id_cov_arr [A : cat] (F : obj A)  : arr F (Unit_mod Id_func (Obj_func F)) Terminal_obj;
//computation rule for Arr_hom
rule (Id_cov_arr $F) '∘a ( (_) _'∘> (Arr_hom _ _ $r)) ↪  $r;
rule Arr_hom (Obj_func _) Id_func (Id_cov_arr $F) ↪ Func_cov_hom _ _ ;

constant symbol Id_con_arr [A : cat] (F : obj A)  : arr Terminal_obj (Unit_mod (Obj_func F) Id_func ) F;
rule ( (Arr_hom _ _ $r) ∘>'_ (_)) ∘a' (Id_con_arr $F)   ↪  $r;
rule Arr_hom Id_func (Obj_func _) (Id_con_arr $F) ↪ Func_con_hom _ _ ;
constant symbol Id_con_arr0 [A A0 : cat] (K : func A A0) (F : obj A)  : arr Terminal_obj (Unit_mod (Obj_func (F ∘>o K)) K ) F;
rule ( (Arr_hom _ _ $r) ∘>'_ (_)) ∘a' (Id_con_arr0 Id_func $F)   ↪  $r;
rule Arr_hom Id_func (Obj_func _) (Id_con_arr0 Id_func $F) ↪ Func_con_hom _ _ ;

//computation rule for Obj_func, arr
rule (Func_cov_hom ( Obj_func $E_obj) _) ∘>'_(_) ∘a' (Id_cov_arr $M)
  ↪ (Id_cov_arr $E_obj);

//TODO REVIEW ∘↓o and Func_con_arr not necessary  ?
// TODO  ∘↓o ?  vs (Func_cov_arr $F) '∘a  (_) _'∘>
symbol ∘↓o : Π [I A B : cat] [R : mod A B] [F : func I A] 
[G : func I B], hom F R G → Π (X : obj I), arr (X ∘>o F) R (X ∘>o G);
notation ∘↓o infix left 120;

//TODO ?
rule (Arr_hom _ _ $r) ∘↓o Terminal_obj  ↪  $r;

//reverse direction?
rule ($r ∘↓ $H) ∘↓o $K ↪ $r ∘↓o ($K ∘>o $H  );

// TODO redo Func_cov_arr to more general than Id_func similar as Id_cov_arr or category_Arr_cov_arr ?
///TODO ?
constant symbol Func_con_arr : Π [I J] (Z: func I J ) (M: obj I),
  arr M (Unit_mod Z Id_func) (M ∘>o Z);
  type λ [A : cat] (F : obj A), Func_con_arr (Obj_func F) Terminal_obj;
constant symbol Func_cov_arr : Π [I J] (Z: func I J ) (M: obj I),
  arr (M ∘>o Z) (Unit_mod Id_func Z) M;
rule  (Func_con_hom $Z $F) ∘↓o $H  ↪ Func_con_arr $Z ($H ∘>o $F)
with (Func_cov_hom $Z $F) ∘↓o $H  ↪ Func_cov_arr $Z ($H ∘>o $F); 

//TODO MEMO LATER... get complex
constant symbol presh : Π C : cat, TYPE;
constant symbol presh_Set : Π C : cat, Set;
rule τ (presh_Set $C) ↪ presh $C;
constant symbol copresh : Π C : cat, TYPE;
constant symbol copresh_Set : Π C : cat, Set;
rule τ (copresh_Set $C) ↪ copresh $C;
constant symbol ⊗o : Π [A B : cat], mod A B → presh B → presh A ; //Tensor_mod;
notation ⊗o infix left 70;
constant symbol o⊗ : Π [A B: cat], copresh A → mod A B →  copresh B ; //Tensor_mod;
notation o⊗ infix left 70;
constant symbol Unit_presh : Π [X A  : cat], func A X → obj X →  presh A ;
symbol o<<∘ : Π [A X : cat], mod A X → obj X → presh A;
symbol ∘>>o : Π [B X: cat], obj X → mod X B → copresh B;
notation o<<∘ infix left 80; notation ∘>>o infix right 80;
rule  (Unit_mod $F $G) o<<∘ $K ↪ Unit_presh $F ($K ∘>o $G) 
with ($R ⊗ $S) o<<∘ $G ↪ $R ⊗o ($S o<<∘ $G);
injective symbol Presh_mod : Π [Y : cat], presh Y → mod Y Terminal_cat ;
rule (Presh_mod $F) o<<∘ $M ↪ $F;


 ////-----------

inductive category : TYPE ≔ | Struct_category : Π 
(category_Obj : Set) 
(category_Arr : τ category_Obj → τ category_Obj → Set)
(category_Comp : Π [M N L : τ category_Obj] (f : τ (category_Arr M N)) (g : τ (category_Arr N L)), τ (category_Arr M L)) 
(category_Iden : Π (M: τ category_Obj), τ (category_Arr M M)), category;

injective symbol category_Obj_Set (C : category) : Set;
rule category_Obj_Set (Struct_category $category_Obj $category_Arr $category_Comp $category_Iden) ↪ $category_Obj;
injective symbol category_Obj (C : category) : TYPE ≔ τ (category_Obj_Set C);
injective symbol category_Arr_Set [C : category]  : (category_Obj C) → (category_Obj C) → Set;
rule @category_Arr_Set (Struct_category $category_Obj $category_Arr $category_Comp $category_Iden) ↪ $category_Arr;
injective symbol category_Arr [C : category]  : (category_Obj C) → (category_Obj C) → TYPE ≔ λ M N, τ (category_Arr_Set M N);
symbol category_Comp [C : category] : Π [M N L : (category_Obj C)] (f : category_Arr M N) (g : (category_Arr N L)), (category_Arr M L);
rule @category_Comp (Struct_category $category_Obj $category_Arr $category_Comp $category_Iden) ↪ $category_Comp;
symbol category_Iden [C : category] : Π (M:  (category_Obj C)), (category_Arr M M);
rule @category_Iden (Struct_category $category_Obj $category_Arr $category_Comp $category_Iden) ↪ $category_Iden;

(C D : category) inductive functor : TYPE ≔ | Struct_functor : Π 
(functor_Obj : category_Obj C → category_Obj D) 
(functor_Arr : Π [M N : category_Obj C], category_Arr M N → category_Arr (functor_Obj M) (functor_Obj N)), functor C D;

symbol functor_Obj [C D : category] (F : functor C D) :  category_Obj C → category_Obj D;
rule functor_Obj (Struct_functor $functor_Obj $functor_Arr) ↪ $functor_Obj;
symbol functor_Arr [C D : category] (F : functor C D) :  Π [M N : category_Obj C], category_Arr M N → category_Arr (functor_Obj F M) (functor_Obj F N);
rule @functor_Arr _ _ (Struct_functor $functor_Obj $functor_Arr) ↪ $functor_Arr;

symbol comp_functor [C D E : category] (F : functor C D) (G : functor D E) : functor C E
 ≔ Struct_functor (λ M : category_Obj C, functor_Obj G (functor_Obj F M)) (λ (M N : category_Obj C) a, (functor_Arr G (functor_Arr F a)));
symbol iden_functor (C : category) : functor C C
 ≔ Struct_functor (λ M : category_Obj C, M) (λ (M N : category_Obj C) a, a);

symbol constant_functor (C : category) [D : category] (M : category_Obj D) : functor C D
≔ Struct_functor (λ _, M) (λ _ _ _, category_Iden M);


[C D : category] inductive transformation (F G: functor C D) : TYPE ≔ | Struct_transformation [F G: functor C D] : Π 
(transformation_Arr : Π (M : category_Obj C), category_Arr (functor_Obj F M) (functor_Obj G M)), transformation F G;

symbol transformation_Arr [C D : category] [F G: functor C D]  (h : transformation F G) : Π (M : category_Obj C), category_Arr (functor_Obj F M) (functor_Obj G M);
rule transformation_Arr (Struct_transformation $transformation_Arr) ↪ $transformation_Arr;

symbol iden_transformation [C D : category] (F : functor C D) : transformation F F 
 ≔ Struct_transformation (λ M : category_Obj C, category_Iden (functor_Obj F M));
symbol comp_transformation [C D : category] [F G H: functor C D] (h : transformation F G) (t : transformation G H) : transformation F H 
 ≔ Struct_transformation (λ M : category_Obj C, category_Comp (transformation_Arr h M) (transformation_Arr t M));
symbol tensor_cov_transformation [C D E : category] [F G : functor C D] (h : transformation F G) (K : functor D E) : transformation (comp_functor F K) (comp_functor G K)
 ≔ Struct_transformation (λ M : category_Obj C, functor_Arr K (transformation_Arr h M));
 symbol tensor_con_transformation [C D B : category] [F G : functor C D] (K : functor B C) (h : transformation F G)  : transformation (comp_functor K F) (comp_functor K G)
 ≔ Struct_transformation (λ M : category_Obj B, (transformation_Arr h (functor_Obj K M)));

 symbol constant_transformation [C D : category] [M N : category_Obj D] (a : category_Arr M N): transformation (constant_functor C M) (constant_functor C N) 
 ≔ Struct_transformation (λ M : category_Obj C, a);


symbol terminal_category : category ≔ Struct_category one_Set (λ F G, one_Set) (λ F G H f g, One) (λ F, One);
symbol terminal_intro_functor (C : category) : functor C terminal_category ≔ constant_functor C One;

injective symbol category_Obj_functor [C : category] (M : category_Obj C) : functor terminal_category C
≔ Struct_functor (λ _, M) (λ _ _ _, category_Iden M);
injective symbol category_Arr_transformation [C : category] [M N : category_Obj C] (a : category_Arr M N) : transformation (category_Obj_functor M) (category_Obj_functor N)
≔ Struct_transformation (λ _, a);

inductive natUniv  : TYPE ≔ 
| Base_natUniv : ℕ → natUniv 
| Pair_natUniv : natUniv → natUniv → natUniv
// | InLeft_natUniv : natUniv →  natUniv
// | InRight_natUniv : natUniv →  natUniv
| Undefined_natUniv : natUniv;
symbol natUniv_Set : Set; rule τ natUniv_Set ↪ natUniv;
symbol natUniv_eq : natUniv → natUniv → 𝔹;
rule  natUniv_eq (Base_natUniv $x) (Base_natUniv $y) ↪ eqn $x $y 
with natUniv_eq (Base_natUniv $x) (Pair_natUniv $y1 $y2) ↪ false
with natUniv_eq (Base_natUniv $x) (Undefined_natUniv) ↪ false
with natUniv_eq (Pair_natUniv $y1 $y2) (Base_natUniv $x)  ↪ false
with natUniv_eq (Pair_natUniv $y1 $y2) (Undefined_natUniv)  ↪ false
with natUniv_eq (Pair_natUniv $x1 $x2) (Pair_natUniv $y1 $y2) ↪  (natUniv_eq $x1 $y1) and (natUniv_eq $x2 $y2)
with natUniv_eq (Undefined_natUniv) (Undefined_natUniv) ↪ true
with natUniv_eq (Undefined_natUniv) (Pair_natUniv $y1 $y2)   ↪ false
with natUniv_eq (Undefined_natUniv) (Base_natUniv $x)  ↪ false;
// with natUniv_eq (InLeft_natUniv $x) (InLeft_natUniv $y) ↪ natUniv_eq $x $y
// with natUniv_eq (InLeft_natUniv $x) (InRight_natUniv $y) ↪ false 

symbol natUniv_fst : natUniv → natUniv;
symbol natUniv_snd : natUniv → natUniv;
rule natUniv_fst (Pair_natUniv $1 $2) ↪ $1;
rule natUniv_snd (Pair_natUniv $1 $2) ↪ $2;

injective symbol listsub  (l : 𝕃 natUniv_Set) ≔  (`sub_ x : natUniv, istrue(∈ natUniv_eq x l));

injective symbol liset_Arr_Set  (M : 𝕃 natUniv_Set) (N : 𝕃 natUniv_Set) : Set
≔ natUniv_Set →_ natUniv_Set;
injective symbol liset_Arr  (M : 𝕃 natUniv_Set) (N : 𝕃 natUniv_Set) ≔ τ (liset_Arr_Set M N);

symbol liset_Comp  [M N L : 𝕃 natUniv_Set]  (f :  (liset_Arr M N)) (g : (liset_Arr N L)) : (liset_Arr M L)
≔ λ x, (g (f x));

injective symbol liset_Iden  M : (liset_Arr M M) ≔ λ x, x;

symbol liset ≔ Struct_category (list natUniv_Set)  (liset_Arr_Set) (@liset_Comp) (liset_Iden);

/// _______________

inductive empty : TYPE ≔ ;
constant symbol empty_Set : Set;
rule τ (empty_Set) ↪ empty;
symbol rect_empty : Π [p0: (empty → Set)], Π x: empty, τ (p0 x);

(p : Set) inductive option : TYPE ≔
| Some : τ p → option p
| None : option p;
constant symbol option_Set : Set → Set;
rule τ (option_Set $p) ↪ option $p;
symbol rect_option : Π [a0 : Set], Π [p0: (option a0 → Set)], (Π x1: τ a0, τ (p0 (Some x1))) → (τ (p0 (None ))) →  Π x: option a0, τ (p0 x);
rule rect_option $1 $2 (Some $x) ↪ $1 $x;
rule rect_option $1 $2 (None) ↪ $2;

inductive graph : TYPE ≔ | Struct_graph : Π 
(graph_Obj : Set) 
(graph_Arr : τ graph_Obj → τ graph_Obj → Set), graph;

injective symbol graph_Obj_Set (C : graph) : Set;
rule graph_Obj_Set (Struct_graph $graph_Obj $graph_Arr) ↪ $graph_Obj;
/* injective */ symbol graph_Obj (C : graph) : TYPE ≔ τ (graph_Obj_Set C);
injective symbol graph_Arr_Set [C : graph]  : (graph_Obj C) → (graph_Obj C) → Set;
rule @graph_Arr_Set (Struct_graph $graph_Obj $graph_Arr) ↪ $graph_Arr;
symbol graph_Arr [C : graph]  : (graph_Obj C) → (graph_Obj C) → TYPE ≔ λ M N, τ (graph_Arr_Set M N);


//TODO quotient by assoc iden... this quotient is harrder to explain than expected because no way to remember that it is now a free category
// hmm in fact whole "concrete freely_category" is a bad idea, should directly do abstract (freely-)cat datatype on graph...
// injective symbol freely_category (C : graph) : category ≔ Struct_category (graph_Obj_Set C) (@freely_category_Arr_Set C) (@freely_category_Comp C) (@freely_category_Iden C);

(C : graph) inductive diagram (D : category) : TYPE ≔ | Struct_diagram [D] : Π 
(diagram_Obj : graph_Obj C → category_Obj D) 
(diagram_Arr : Π [M N : graph_Obj C], graph_Arr M N → category_Arr (diagram_Obj M) (diagram_Obj N)), diagram C D;

symbol diagram_Obj [C : graph] [D : category] (F : diagram C D) :  graph_Obj C → category_Obj D;
rule diagram_Obj (Struct_diagram $diagram_Obj $diagram_Arr) ↪ $diagram_Obj;
symbol diagram_Arr [C : graph] [D : category] (F : diagram C D) :  Π [M N : graph_Obj C], graph_Arr M N → category_Arr (diagram_Obj F M) (diagram_Obj F N);
rule @diagram_Arr _ _ (Struct_diagram $diagram_Obj $diagram_Arr) ↪ $diagram_Arr;

(C D : graph) inductive graphMorph  : TYPE ≔ | Struct_graphMorph : Π 
(graphMorph_Obj : graph_Obj C → graph_Obj D) 
(graphMorph_Arr : Π [M N : graph_Obj C], graph_Arr M N → graph_Arr (graphMorph_Obj M) (graphMorph_Obj N)), graphMorph C D;

symbol graphMorph_Obj [C : graph] [D : graph] (F : graphMorph C D) :  graph_Obj C → graph_Obj D;
rule graphMorph_Obj (Struct_graphMorph $graphMorph_Obj $graphMorph_Arr) ↪ $graphMorph_Obj;
symbol graphMorph_Arr [C : graph] [D : graph] (F : graphMorph C D) :  Π [M N : graph_Obj C], graph_Arr M N → graph_Arr (graphMorph_Obj F M) (graphMorph_Obj F N);
rule @graphMorph_Arr _ _ (Struct_graphMorph $graphMorph_Obj $graphMorph_Arr) ↪ $graphMorph_Arr;

symbol comp_graphMorph_diagram [C' : graph] [C : graph] (F : graphMorph C' C) [D : category] (G : diagram C D) : diagram C' D
≔ Struct_diagram (λ M : graph_Obj C', diagram_Obj G (graphMorph_Obj F M)) (λ (M N : graph_Obj C') a, (diagram_Arr G (graphMorph_Arr F a)));

/* injective */ symbol joinGraph_Obj [C : graph] (X Y : graph_Obj C) : Set ≔ (graph_Obj_Set C) ;
injective symbol joinGraph_Arr [C : graph] (X Y : graph_Obj C) : Π (M N : τ (joinGraph_Obj X Y)), Set;
constant symbol joinGraph_Arr_introOld [C : graph] (X Y : graph_Obj C) : Π [M N : graph_Obj C], graph_Arr M N → τ (joinGraph_Arr X Y M N);
constant symbol joinGraph_Arr_introNew [C : graph] (X Y : graph_Obj C) : τ (joinGraph_Arr X Y X Y);
symbol joinGraph_Arr_elim [C : graph] [X Y : graph_Obj C] : Π [E : τ (joinGraph_Obj X Y) → τ (joinGraph_Obj X Y) → Set]
 (first : Π [M N : graph_Obj C], graph_Arr M N → τ (E M N)) (second: τ (E X Y)),
  Π (M N : graph_Obj C), τ (joinGraph_Arr X Y M N) → τ (E M N);
rule (@joinGraph_Arr_elim $C $X $Y $E $oldarr $newarr _ _ (@joinGraph_Arr_introOld $C $X $Y _ _ $a)) ↪ ($oldarr _ _ $a);
rule (@joinGraph_Arr_elim $C $X $Y $E $oldarr $newarr _ _ (@joinGraph_Arr_introNew $C $X $Y)) ↪ ($newarr);
///todo review this eta necessarry?
rule (@joinGraph_Arr_elim _ $X $Y _ (@joinGraph_Arr_introOld _ $X $Y) (@joinGraph_Arr_introNew _ $X $Y)) ↪ λ M N a, a;

injective symbol joinGraph [C : graph] (X Y : graph_Obj C): graph ≔ Struct_graph (joinGraph_Obj X Y) (joinGraph_Arr X Y);

symbol joinGraph_graphMorph_Obj [C : graph] (X Y : graph_Obj C) : graph_Obj C → graph_Obj (joinGraph X Y) ≔ λ x, x;
symbol joinGraph_graphMorph [C : graph] (X Y : graph_Obj C) : graphMorph C (joinGraph X Y) 
≔ @Struct_graphMorph C (joinGraph X Y) (joinGraph_graphMorph_Obj X Y) (@joinGraph_Arr_introOld _ X Y);

/////////////----------

inductive  cone [C : graph] [D : category] (M : category_Obj D) (F : diagram C D) : TYPE ≔ | Struct_cone [C D M F] : Π
(cone_Arr : Π (N : graph_Obj C), category_Arr M (diagram_Obj F N)), @cone C D M F ;

injective symbol cone_Arr [C D M F] (c : @cone C D M F) : Π (N : graph_Obj C), category_Arr M (diagram_Obj F N);
rule cone_Arr (Struct_cone $1) ↪ $1;

symbol tensor_cone [C B : graph] [D : category] (K: graphMorph B C) [M : category_Obj D] [F : diagram C D] (h : cone M F)
 : cone M (comp_graphMorph_diagram K F)
 ≔ Struct_cone (λ N : graph_Obj B, (cone_Arr h (graphMorph_Obj K N)));

symbol comp_con_cone  [D : category] [M' M : category_Obj D] (m : category_Arr M' M) [C : graph] [F : diagram C D] (t : cone M F) : cone M' F
 ≔ Struct_cone (λ N : graph_Obj C, category_Comp m (cone_Arr t N));


inductive limit' [C : graph] [D : category] (F : diagram C D) : TYPE ≔ | Struct_limit' [C D F]: 
Π (limit'_Obj : category_Obj D) 
(limit'_Cone : cone limit'_Obj F)
(limit'_Univ : Π [M : category_Obj D] (t : cone M F), category_Arr M limit'_Obj), @limit' C D F;

injective symbol limit'_Obj [C D F] (lim_F : @limit' C D F) : category_Obj D;
rule limit'_Obj (Struct_limit' $1 $2 $3) ↪ $1;
injective symbol limit'_Cone [C D F] (lim_F : @limit' C D F) : cone (limit'_Obj lim_F) F;
rule limit'_Cone (Struct_limit' $1 $2 $3) ↪ $2;
injective symbol limit'_Univ [C D F] (lim_F : @limit' C D F) : Π [M : category_Obj D] (t : cone M F), category_Arr M (limit'_Obj lim_F);
rule @limit'_Univ _ _ _ (Struct_limit' $1 $2 $3) ↪ $3;

inductive equalizing [C : graph] [X Y : graph_Obj C] [D : category] [M : category_Obj D] (F : diagram (joinGraph X Y) D)
(t : cone M (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F)): TYPE ≔ | Struct_equalizing [C X Y D M F t] :
Π (equalizing_Obj : category_Obj D) 
(equalizing_Arr : category_Arr (equalizing_Obj) M)
(equalizing_Cone : cone (equalizing_Obj) F), @equalizing C X Y D M F t;

constant symbol equalizing_Set [C : graph] [X Y : graph_Obj C] [D : category] [M : category_Obj D] (F : diagram (joinGraph X Y) D)
(t : cone M (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F)): Set;
rule τ (@equalizing_Set $C $X $Y $D $M $F $t) ↪ @equalizing $C $X $Y $D $M $F $t;
injective symbol equalizing_Obj [C X Y D M F t] (L : @equalizing C X Y D M F t): category_Obj D;
rule equalizing_Obj (Struct_equalizing $1 $2 $3) ↪ $1;
injective symbol equalizing_Arr [C X Y D M F t] (L : @equalizing C X Y D M F t): category_Arr (@equalizing_Obj C X Y D M F t L) M;
rule equalizing_Arr (Struct_equalizing $1 $2 $3) ↪ $2;
injective symbol equalizing_Cone [C X Y D M F t] (L : @equalizing C X Y D M F t): cone (@equalizing_Obj C X Y D M F t L) F;
rule equalizing_Cone (Struct_equalizing $1 $2 $3) ↪ $3;

inductive equalizer [C : graph] [X Y : graph_Obj C] [D : category] [M : category_Obj D] (F : diagram (joinGraph X Y) D)
(t : cone M (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F)): TYPE ≔ | Struct_equalizer [C X Y D M F t] : 
Π (equalizer_Equalizing : @equalizing C X Y D M F t) 
(equalizer_Univ : Π L : @equalizing C X Y D M F t, category_Arr (equalizing_Obj L) (equalizing_Obj equalizer_Equalizing)), @equalizer C X Y D M F t;

//TODO equalizer_Set
injective symbol equalizer_Equalizing [C X Y D M F t] (L : @equalizer C X Y D M F t): @equalizing C X Y D M F t;
rule equalizer_Equalizing (Struct_equalizer $1 $2) ↪ $1;
injective symbol equalizer_Univ [C X Y D M F t] (L : @equalizer C X Y D M F t): Π L0 : @equalizing C X Y D M F t, category_Arr (@equalizing_Obj C X Y D M F t L0) (@equalizing_Obj C X Y D M F t (@equalizer_Equalizing C X Y D M F t L));
rule equalizer_Univ (Struct_equalizer $1 $2) ↪ $2;

///---
symbol emptyGraph  : graph ≔ Struct_graph (empty_Set ) (λ _ _, empty_Set);

///---

/* injective */ symbol optionGraph_Obj (C : graph) : Set ≔  option_Set (graph_Obj_Set C);
injective symbol optionGraph_Arr (C : graph) : Π (M N : τ (optionGraph_Obj C)), Set;
constant symbol optionGraph_Arr_intro (C : graph) : Π [M N : graph_Obj C], graph_Arr M N → τ (optionGraph_Arr C (Some M) (Some N));
symbol optionGraph_Arr_elim (C : graph) : Π [E : τ (optionGraph_Obj C) → τ (optionGraph_Obj C) → Set]
 (E_left : Π [M N : graph_Obj C], graph_Arr M N → τ (E (Some M) (Some N)))  ,
  Π (M N : τ (optionGraph_Obj C)), τ (optionGraph_Arr C M N) → τ (E M N);
rule (@optionGraph_Arr_elim $C $E $E_left  _ _ (@optionGraph_Arr_intro $C _ _ $a)) ↪ ($E_left _ _ $a);
///todo review this eta necessarry?
rule (@optionGraph_Arr_elim $C (optionGraph_Arr $C) (@optionGraph_Arr_intro $C)) ↪ λ M N a, a;

injective symbol optionGraph (C : graph) : graph ≔ Struct_graph (optionGraph_Obj C) (optionGraph_Arr C);

symbol optionGraph_graphMorph (C : graph) : graphMorph C (optionGraph C) 
≔ @Struct_graphMorph C (optionGraph C) (Some) (@optionGraph_Arr_intro C);

///---

inductive terminal (D : category) : TYPE ≔ | Struct_terminal [D] : 
Π (terminal_Obj : category_Obj D) 
(terminal_Univ : Π L0 : category_Obj D, category_Arr L0 (terminal_Obj)), @terminal D;

injective symbol terminal_Obj [D] (L : @terminal D): @category_Obj D;
rule terminal_Obj (Struct_terminal $1 $2) ↪ $1;
injective symbol terminal_Univ [D] (L : @terminal D): Π L0 : @category_Obj D, category_Arr L0 (@terminal_Obj D L);
rule terminal_Univ (Struct_terminal $1 $2) ↪ $2;


///---

inductive producing [C : graph]  [D : category] [M : category_Obj D] (F : diagram (optionGraph C) D)
(t : cone M (comp_graphMorph_diagram (optionGraph_graphMorph C) F)): TYPE ≔ | Struct_producing [C D M F t] :
Π (producing_Obj : category_Obj D) 
(producing_Arr : category_Arr (producing_Obj) M)
(producing_Cone : cone (producing_Obj) F), @producing C D M F t;

constant symbol producing_Set [C : graph]  [D : category] [M : category_Obj D] (F : diagram (optionGraph C) D)
(t : cone M (comp_graphMorph_diagram (optionGraph_graphMorph C) F)): Set;
rule τ (@producing_Set $C $D $M $F $t) ↪ @producing $C $D $M $F $t;
injective symbol producing_Obj [C D M F t] (L : @producing C D M F t): category_Obj D;
rule producing_Obj (Struct_producing $1 $2 $3) ↪ $1;
injective symbol producing_Arr [C D M F t] (L : @producing C D M F t): category_Arr (@producing_Obj C D M F t L) M;
rule producing_Arr (Struct_producing $1 $2 $3) ↪ $2;
injective symbol producing_Cone [C D M F t] (L : @producing C D M F t): cone (@producing_Obj C D M F t L) F;
rule producing_Cone (Struct_producing $1 $2 $3) ↪ $3;

inductive product [C : graph]  [D : category] [M : category_Obj D] (F : diagram (optionGraph C) D)
(t : cone M (comp_graphMorph_diagram (optionGraph_graphMorph C) F)): TYPE ≔ | Struct_product [C D M F t] : 
Π (product_Producing : @producing C D M F t) 
(product_Univ : Π L : @producing C D M F t, category_Arr (producing_Obj L) (producing_Obj product_Producing)), @product C D M F t;

//TODO product_Set
injective symbol product_Producing [C D M F t] (L : @product C D M F t): @producing C D M F t;
rule product_Producing (Struct_product $1 $2) ↪ $1;
injective symbol product_Univ [C D M F t] (L : @product C D M F t): Π L0 : @producing C D M F t, category_Arr (@producing_Obj C D M F t L0) (@producing_Obj C D M F t (@product_Producing C D M F t L));
rule product_Univ (Struct_product $1 $2) ↪ $2;

///-----

inductive isFiniteGraph : graph → TYPE ≔
| EmptyGraph_isFiniteGraph : isFiniteGraph emptyGraph 
| OptionGraph_isFiniteGraph [C : graph] : isFiniteGraph C → isFiniteGraph (optionGraph C)
| JoinGraph_isFiniteGraph [C : graph]: isFiniteGraph C → Π (X Y : graph_Obj C), isFiniteGraph (joinGraph X Y) ;

symbol rect_isFiniteGraph : Π p0: (Π x0: graph, isFiniteGraph x0 → Set), 
τ (p0 emptyGraph EmptyGraph_isFiniteGraph) → 
(Π C: graph, Π x1: isFiniteGraph C, τ (p0 C x1) → τ (p0 (optionGraph C) (OptionGraph_isFiniteGraph x1))) → 
(Π C: graph, Π x3: isFiniteGraph C, Π X: graph_Obj C, Π Y: graph_Obj C, τ (p0 C x3) → τ (p0 (joinGraph X Y) (JoinGraph_isFiniteGraph x3 X Y ))) → 
Π x0: graph, Π x: isFiniteGraph x0, τ (p0 x0 x);
rule @rect_isFiniteGraph $1 $2 $3 $4 $5 (@EmptyGraph_isFiniteGraph) ↪
  $2 ;
rule @rect_isFiniteGraph $1 $2 $3 $4 $5 (@OptionGraph_isFiniteGraph $6 $7) ↪
  $3 $6 $7 (@rect_isFiniteGraph $1 $2 $3 $4 $6 $7);
rule @rect_isFiniteGraph $1 $2 $3 $4 $5 (@JoinGraph_isFiniteGraph $6 $7 $8 $9) ↪
  $4 $6 $7 $8 $9 (@rect_isFiniteGraph $1 $2 $3 $4 $6 $7);


symbol lemma_ind_hypothesis_equalizer_limit : Π D, (Π [C X Y M F t], @equalizer C X Y D M F t) → 
Π [C : graph] [X Y : graph_Obj C] (C_isf : isFiniteGraph C), 
(Π (F' : diagram C D), @limit' C D F') →
Π (F : diagram (joinGraph X Y) D), @limit' (joinGraph X Y) D F ≔ 
begin
assume D eqs C X Y C_ist IH F; 

have IH_F : limit' (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F) 
{ refine (IH (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F)) };

have Eq_IH_F : equalizer F (limit'_Cone IH_F) 
{ refine (eqs _ _ _ _ F (limit'_Cone IH_F)) };  

apply @Struct_limit' 
{ refine (equalizing_Obj (equalizer_Equalizing Eq_IH_F)) } 

{ refine (equalizing_Cone (equalizer_Equalizing Eq_IH_F)) }

{ assume M c_;

    have Eq_side : category_Arr M (limit'_Obj IH_F) 
    { refine (limit'_Univ IH_F) (tensor_cone (joinGraph_graphMorph X Y) c_) }; 

    refine (equalizer_Univ Eq_IH_F (Struct_equalizing M Eq_side c_ )) ; };
end;

// ---------

symbol liset_terminal_natUniv : natUniv ≔ Base_natUniv 0; 
symbol liset_terminal : 
  terminal liset ≔
begin
refine Struct_terminal _ _ 
{  refine (liset_terminal_natUniv ⸬ □)  
}
{ refine λ M x, liset_terminal_natUniv
};
end;

symbol foldl [b] [a] (f : τ b → τ a →  τ b) (i : τ b) : 𝕃 a → τ b;

rule foldl $f $i □  ↪ $i
with foldl $f $i ($x ⸬ $l) ↪ $f (foldl $f $i $l) $x ;
compute foldl (⋅) □ ((1 ⸬ 2 ⸬ □) ⸬ (5 ⸬ 6 ⸬ □) ⸬ □);
symbol flatten [a] : 𝕃 (list a) → 𝕃 a ≔ foldl (⋅) □; //rev

symbol liset_product : 
Π [A: graph], Π [K: category_Obj liset], 
  Π F: diagram (optionGraph A) liset, 
  Π t: cone K (comp_graphMorph_diagram (optionGraph_graphMorph A) F), 
  product F t ≔
begin
assume A K F t;
refine Struct_product _ _ 
{  refine Struct_producing _ _ _ 
  { refine (flatten (map (λ xs, map (Pair_natUniv xs) (diagram_Obj F None)) K));
  }
  { refine natUniv_fst;    
  }
  { refine (Struct_cone _);
  simplify;
  refine rect_option _ _
    { assume M; refine (λ x, (cone_Arr t M) (natUniv_fst x));
    }
    { refine natUniv_snd
    };
  }
}
{ assume L0; simplify producing_Obj;
  refine (λ i, Pair_natUniv ((producing_Arr L0) i) (cone_Arr (producing_Cone L0) None i));
};
end;


symbol liset_equalizer : 
Π [A: graph], Π [X: graph_Obj A], Π [Y: graph_Obj A], Π [K: category_Obj liset], 
  Π F: diagram (joinGraph X Y) liset, 
  Π t: cone K (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F), 
  equalizer F t ≔
begin
assume A X Y K F t;
refine Struct_equalizer _ _ 
{  refine Struct_equalizing _ _ _ 
  { refine (let f ≔ (category_Comp (cone_Arr t X) (diagram_Arr F (joinGraph_Arr_introNew X Y))) in 
      let g ≔ (cone_Arr t Y) in 
      filter (λ x, natUniv_eq (f x) (g x)) K) ;
  }
  { refine (λ x : natUniv, x);    
  }
  { refine (Struct_cone _);
    refine (λ M,  category_Comp (λ x : natUniv, x) ((cone_Arr t M)));
  }
}
{ assume L0;
  refine (λ i, (equalizing_Arr L0) i);
};
end;

//data for the main example
symbol example_graph : graph ≔ begin
refine (@joinGraph _ _ _ ) 
{ refine (optionGraph (optionGraph (optionGraph emptyGraph) ) )
}
{ refine (Some None)
}
{ refine (None)
}
end;

symbol example_graph_isf : isFiniteGraph example_graph ≔ 
begin
refine (@JoinGraph_isFiniteGraph _ _ _ _ ) ;
refine (@OptionGraph_isFiniteGraph _ _) ;
refine (@OptionGraph_isFiniteGraph _ _) ;
refine (@OptionGraph_isFiniteGraph _ _) ;
refine (@EmptyGraph_isFiniteGraph ) ;
end;

symbol example_diagram : diagram example_graph liset
≔ begin
refine Struct_diagram _ _ 
{ 
  refine rect_option _ _ 
  { 
    refine rect_option _ _ 
    { 
      refine rect_option _ _  
      { 
        refine rect_empty
      }
      {
        refine ((Base_natUniv 13) ⸬ (Base_natUniv 12) ⸬ (Base_natUniv 11) ⸬ □)
      }
    }
    {
      refine ((Base_natUniv 22) ⸬ (Base_natUniv 21) ⸬ □)
    }
  }
  {
    refine ((Base_natUniv 32) ⸬ (Base_natUniv 31) ⸬ □)
  }  
}
{  
  refine (joinGraph_Arr_elim _ _ )
  { 
    refine (optionGraph_Arr_elim _ _ );
    refine (optionGraph_Arr_elim _ _ );
    refine (optionGraph_Arr_elim _ _ );
    assume M N; 
    refine rect_empty
  }
  { 
    refine (λ x, Base_natUniv 31)
  }
}
end;


// ---------

//universality is in extensional formulation, as compared to intensional intrinsic formulation for limit_cov projection limit_cov_transf
// injective symbol limit_cov_univ' : Π  [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B] (isl : limit_cov F W F_⇐_W), 
// Π [I : cat] [M : func I B],
// transf (((Unit_mod M F)) ⇐  W) Id_func (Unit_mod M F_⇐_W) Id_func;
injective symbol ilimit_cov_univ : Π  [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B] (isl : limit_cov F W F_⇐_W), 
Π [I : cat] [M : func I B]  [X : func J' I] ,
hom X (((Unit_mod M F)) ⇐ W) Id_func → hom X (Unit_mod M F_⇐_W) Id_func;

//narrurality of limit intro
//WARRNING: this rule is necessarry because no such more general rule as: rule ($M)_'∘> ($g '∘ $t) ↪ (($M)_'∘> $g) ''∘ $t;
// which fails because $M is not id
// rule ($Z)_'∘> ($f '∘  (limit_cov_univ' $isl)) 
// ↪  ( (_)_'∘> $f ) ''∘ (limit_cov_univ' $isl );
rule @'∘ _ _ _ _ _ _ _ Id_func _ $f  (($Z)_'∘> (ilimit_cov_univ $isl $c)) 
↪  ilimit_cov_univ $isl ($f '∘ ($Z)_'∘> $c);
type @transf;
//TODO: review slow? 5 minutes
rule (@∘>'_ _ _ _ _ _ (Unit_mod _ Id_func) _  $f _) ∘' (ilimit_cov_univ $isl $c)  
↪  ilimit_cov_univ $isl ((comp_Imply_cov_mod $f) ∘' $c);

injective symbol ilimit_cov_cone : Π  [B J J' : cat]  [W : mod J' J] [F : func J B] [F_⇐_W : func J' B] (isl : limit_cov F W F_⇐_W),
hom F_⇐_W (((Unit_mod Id_func F)) ⇐ W) Id_func;

//beta
// rule (limit_cov_univ' $isl) ''∘ ((_)_'∘> (ilimit_cov_cone $isl)) ↪ Id_transf _;
rule (ilimit_cov_univ $isl $c) '∘ (_)_'∘> (ilimit_cov_cone $isl) ↪ $c;

//eta
// rule  ((_)_'∘> (ilimit_cov_cone $isl)) ''∘  (limit_cov_univ' $isl) ↪ Id_transf _;
rule (ilimit_cov_univ $isl (ilimit_cov_cone $isl))   ↪ Func_cov_hom _ _;

//universality is in extensional formulation, as compared to intensional intrinsic formulation for limit_cov projection limit_cov_transf
injective symbol ilimit_Set [J' B : cat]  [J : cat] (F : func J B) (W : mod J' J) : Set ≔
`Σ_ (F_⇐_W : func J' B),
        (hom_Set F_⇐_W (((Unit_mod Id_func F)) ⇐ W) Id_func)
    ×    (`Π_ [I : cat], `Π_ [M : func I B], `Π_ [S : func J' I],   /* TODO: T should Id_func ? */
    hom_Set S (((Unit_mod M F)) ⇐ W) Id_func →_ hom_Set S (Unit_mod M F_⇐_W) Id_func);
injective symbol ilimit [J' B : cat]  [J : cat] (F : func J B) (W : mod J' J) : TYPE ≔ τ (ilimit_Set F W);

injective symbol ilimit_limit_cov [J' B J F W] (F_⇐_W : @ilimit J' B J F W) :
  limit_cov F W (sigma_Fst F_⇐_W);

rule @ilimit_cov_univ _ _ _ _ _ _  (@ilimit_limit_cov $J' $B $J $F $W $F_⇐_W)
 ↪ (sigma_Snd $F_⇐_W)₂;
 rule @ilimit_cov_cone _ _ _ _ _ _  (@ilimit_limit_cov $J' $B $J $F $W $F_⇐_W)
 ↪ (sigma_Snd $F_⇐_W)₁;
 rule @∘' _ _ _ _ _ _ _ Id_func _ (@limit_cov_univ_transf _ _ _ _ _ _ (@ilimit_limit_cov $J' $B $J $F $W $F_⇐_W) _ _)  $c
 ↪ (sigma_Snd $F_⇐_W)₂ _ _ _ $c ;

////-----------

constant symbol graph_cat : Π C : graph, cat;
constant symbol graph_Obj_obj [C : graph] (M : graph_Obj C) : obj (graph_cat C); 
//TODO normalization operations define recursively by cases
symbol obj_graph_Obj [C : graph] (M : obj (graph_cat C)) : graph_Obj C;
rule (obj_graph_Obj (graph_Obj_obj $o)) ↪ $o; 


//TODO: also generalize this from Id_func ? similar as for category
constant symbol graph_Arr_cov_arr [C : graph] (M N : obj (graph_cat C)) (a : graph_Arr (obj_graph_Obj M) (obj_graph_Obj N)) : 
arr M (Unit_mod Id_func (Obj_func N)) Terminal_obj;
constant symbol graph_Arr_con_arr [C : graph] (M N : obj (graph_cat C)) (a : graph_Arr (obj_graph_Obj M) (obj_graph_Obj N)) : 
arr Terminal_obj (Unit_mod (Obj_func M) Id_func) N;
//TODO: finish: graph viewed as unit profunctor
constant symbol graphunitprofunctor_Arr_arr [C : graph] (M N : obj (graph_cat C)) (a : graph_Arr (obj_graph_Obj M) (obj_graph_Obj N)) : 
arr M (Unit_mod Id_func Id_func) N;

//have both cov elim and con elim?, and separrated from (neutral) categoryunitprofunctor elim?
injective symbol graph_elim_cov_func [C : graph] : Π [E : cat]
(E_obj : Π (M : graph_Obj C), obj E)
(E_cov_arr : Π [M N : graph_Obj C] (a : graph_Arr M N), 
  arr (E_obj M) (Unit_mod Id_func (Obj_func (E_obj N))) Terminal_obj),
  func (graph_cat C) E;

//TODO later as accumulator? for redirecting associativity
rule  $M ∘>o (graph_elim_cov_func $E_obj $E_cov_arr)
  ↪ $E_obj (obj_graph_Obj $M);
rule (Func_cov_hom (graph_elim_cov_func $E_obj $E_cov_arr) _) ∘>'_(_) ∘a' (graph_Arr_cov_arr $M $N $a)
  ↪ ($E_cov_arr (obj_graph_Obj $M) (obj_graph_Obj $N) $a);

//eta  review this
symbol graph_elim_cov_func_Obj (C : graph) [E : cat]
(F : func (graph_cat C) E):
Π (M : graph_Obj C), obj E;
// ≔ λ M, (graph_Obj_obj M) ∘>o F;
rule @graph_elim_cov_func_Obj $C $E $F $M ↪ (graph_Obj_obj $M) ∘>o $F;

symbol graph_elim_cov_func_Arr (C : graph) [E : cat]
(F : func (graph_cat C) E):
Π [M N : graph_Obj C] (a : graph_Arr M N), 
  arr (graph_elim_cov_func_Obj _ F M) (Unit_mod Id_func (Obj_func (graph_elim_cov_func_Obj _ F N))) Terminal_obj;
// ≔ λ M N a, (Func_cov_hom F _) ∘>'_(_) ∘a' (graph_Arr_cov_arr a);
rule (@graph_elim_cov_func_Arr $C $E $F $M $N $a) ↪ (Func_cov_hom $F _) ∘>'_(_) ∘a' (graph_Arr_cov_arr (graph_Obj_obj $M) (graph_Obj_obj $N) $a);
//eta
rule (graph_elim_cov_func (graph_elim_cov_func_Obj _ $F) (@graph_elim_cov_func_Arr _ _ $F))
  ↪ $F;

//TODO REVIEW THIS
// rule obj_graph_Obj ((graph_Obj_obj $X) ∘>o $F) ↪ obj_graph_Obj (graph_elim_cov_func_Obj _ $F $X);

//this says that the correspondence in the freely-category adjunction is  not only bijection but is also isomorphism/equivalence of categories
symbol graph_elim_cov_hom [C : graph] : Π [E  : cat] [G : func (graph_cat C) E] [F : func (graph_cat C) E] 
  (t_arr : Π (M : graph_Obj C), 
    arr ( (graph_Obj_obj M) ∘>o F) (Unit_mod Id_func (G <∘ (Obj_func (graph_Obj_obj M)))) Terminal_obj)
//   (t_nat : Π [M N : graph_Obj C] (a : graph_Arr M N), 
//  π(((Func_cov_hom F _) ∘>'_(_) ∘a' (graph_Arr_cov_arr (graph_Obj_obj M) (graph_Obj_obj N) a)) '∘a (( _ ) _'∘>  (Arr_hom (t_arr N)))
//  =  (t_arr M) '∘a (_)_'∘> (Arr_hom ((Func_cov_hom G _) ∘>'_(_) ∘a' (graph_Arr_cov_arr (graph_Obj_obj M) (graph_Obj_obj N) a)))))
  ,  hom F (Unit_mod Id_func G) Id_func;

// rule (graph_elim_cov_hom $x) '∘ (( _ ) _'∘>  (graph_elim_cov_hom $h))
//     ↪ graph_elim_cov_hom (λ M,  ($x M) '∘a (( _ ) _'∘>  (Arr_hom ($h M)))) ;
rule (graph_elim_cov_hom $x) '∘ (( _ ) _'∘>  (graph_elim_cov_hom $h))
    ↪ graph_elim_cov_hom (λ M,  ($x M) '∘a (( _ ) _'∘>  (Arr_hom (Obj_func _) (Obj_func _) ($h M)))) ;

rule ((graph_elim_cov_hom $t_arr) ∘>'_ ( _ )) ∘a' (Id_cov_arr (graph_Obj_obj $M))
    ↪ $t_arr $M ;

//TODO define category_elim_cov_hom from graphunitprofunctor_elim_hom ? or keep both because of rule below for interaction?
symbol  graphunitprofunctor_elim_hom [C : graph] : Π [A B: cat]  (F : func (graph_cat C) A) [R : mod A B] (G : func (graph_cat C) B) 
(t_arr : Π [M : graph_Obj C] [N : graph_Obj C] (r : graph_Arr M N),
              arr ((graph_Obj_obj M) ∘>o F) R ((graph_Obj_obj N) ∘>o G))

, hom F R G;

rule ((Func_cov_hom $F _) ∘>'_(_) ∘a' ((graph_Arr_con_arr (graph_Obj_obj $M') (graph_Obj_obj $M) $a))) '∘a (_)_'∘> (graphunitprofunctor_elim_hom $F $G $t_arr)
↪ ($t_arr $M' $M $a);
// rule ((Func_cov_hom $F _) ∘>'_(_) ∘' (Arr_hom (graph_Arr_con_arr $a))) '∘ (_)_'∘> (graphunitprofunctor_elim_hom $F $G $t_arr)
// ↪ ($t_arr _ _ $a);

rule (graph_elim_cov_hom $x) '∘ (_)_'∘> (graphunitprofunctor_elim_hom $F $G $t_arr)
↪ (graphunitprofunctor_elim_hom _ $G  (λ M N r, ($x M) '∘a (_)_'∘> (Arr_hom _ (Obj_func _) ($t_arr _ _ r))));

// rule (graph_elim_cov_hom $x) '∘ (_)_'∘> (graphunitprofunctor_elim_hom $F $G $t_arr)
// ↪ (graphunitprofunctor_elim_hom _ $G  (λ M N r, ($x M) '∘ (_)_'∘> ($t_arr _ _ r)));

//TODO redo this with presheaves grammatical entry...
//QUESTIONABLE, USED in old alternative abstract lemma_ind_base_iterminal_ilimit  but not in the new more relevant
symbol graph_elim_cov_transf [C : graph] : 
Π [A' A : cat] [F : func A' A]
[W : mod A' (graph_cat C)] [R : mod A (graph_cat C)] 
(t_arr : Π [N : graph_Obj C] ,
    transf (W  <<∘ (Obj_func (graph_Obj_obj N))) 
          F (R  <<∘ (Obj_func (graph_Obj_obj N))) Id_func )

, transf W F R Id_func;

rule (graph_elim_cov_transf $t_arr) <<∘1 (Obj_func (graph_Obj_obj $N)) ↪ ($t_arr $N);

constant symbol graphMorph_func [C : graph] [E : graph] (F : graphMorph C E):
func (graph_cat C) (graph_cat E);
rule  $M ∘>o (graphMorph_func $F) ↪ graph_Obj_obj (graphMorph_Obj $F (obj_graph_Obj $M));
rule (Func_cov_hom (graphMorph_func $F) _) ∘>'_(_) ∘a' (graph_Arr_cov_arr $M $N $a)
↪ (graph_Arr_cov_arr _ _ (graphMorph_Arr $F $a));

////-----------

constant symbol category_cat : Π C : category, cat;

constant symbol category_Obj_obj [C : category] (M : category_Obj C) : obj (category_cat C); //TODO later as accumulator? for redirecting associativity
//TODO normalization operations define recursively by cases
symbol obj_category_Obj [C : category] (M : obj (category_cat C)) : category_Obj C;
rule (obj_category_Obj (category_Obj_obj $o)) ↪ $o; 

//TODO similar as some elim
//replace (Obj_func N) by any (func Terminal_cat _)
constant symbol category_Arr_cov_arr0 [C : category] [I : cat] (H : func I (category_cat C)) (M  : obj I) (N : obj (category_cat C)) 
(a : category_Arr (obj_category_Obj (M ∘>o H)) (obj_category_Obj N)) :
 arr M (Unit_mod H (Obj_func N)) Terminal_obj;
// constant symbol category_Arr_cov_arr [C : category] (M N : obj (category_cat C)) 
// (a : category_Arr (obj_category_Obj M) (obj_category_Obj N)) :
//  arr M (Unit_mod Id_func (Obj_func N)) Terminal_obj;
 constant symbol category_Arr_cov_arr' [C : category] [I : cat] (H : func I (category_cat C)) (M  : obj I) (N : func Terminal_cat (category_cat C)) 
 (a : category_Arr (obj_category_Obj (M ∘>o H)) (obj_category_Obj (Terminal_obj ∘>o N))) :
  arr M (Unit_mod H N) Terminal_obj;
  //not really cov anymore...
// constant symbol category_Arr_cov_arr'' [C : category] (M : obj (category_cat C)) [C' : cat] (N : func C' (category_cat C)) (Y : obj C')
// (a : category_Arr (obj_category_Obj M /* ∘>o Id_func */ ) (obj_category_Obj (Y ∘>o N))) :
//   arr M (Unit_mod Id_func N) Y;

constant symbol category_Arr_con_arr [C : category] (M N : obj (category_cat C)) 
(a : category_Arr (obj_category_Obj M) (obj_category_Obj N)) :
arr Terminal_obj (Unit_mod (Obj_func M) Id_func) N;
//TODO: finish: category viewed as unit profunctor
constant symbol categoryunitprofunctor_Arr_arr [C : category] (M N : obj (category_cat C)) 
(a : category_Arr (obj_category_Obj M) (obj_category_Obj N)) :
arr M (Unit_mod Id_func Id_func) N;

rule (Arr_hom _ (Obj_func _) (category_Arr_cov_arr0 _ _ _ $x)) '∘ (( _ ) _'∘>  (Arr_hom _ _ (category_Arr_cov_arr0 Id_func _ _ $h)))
    ↪ Arr_hom _ _ (category_Arr_cov_arr0 _ _ _ (category_Comp $x $h)) ;
rule (Arr_hom _ (Obj_func _) (category_Arr_cov_arr0 Id_func _ _  $x)) '∘ (( _ ) _'∘>  (Arr_hom _ _ (categoryunitprofunctor_Arr_arr _ _ $h)))
    ↪ Arr_hom _ _ (categoryunitprofunctor_Arr_arr _ _ (category_Comp $x $h)) ;

rule (Arr_hom _ (Obj_func _) (category_Arr_cov_arr' $H' _ _ $x)) '∘ (( _ ) _'∘>  (Arr_hom _ _ (category_Arr_cov_arr' Id_func _ _ $h)))
    ↪ Arr_hom _ _ (category_Arr_cov_arr' _ _ _ (category_Comp $x $h)) ;
rule (Arr_hom _ (Obj_func _) (category_Arr_cov_arr' Id_func _ _  $x)) '∘ (( _ ) _'∘>  (Arr_hom _ _(categoryunitprofunctor_Arr_arr _ _ $h))) /* memo: redo when categoryunitprofunctor_Arr_arr is generalized */
    ↪ Arr_hom _ _ (categoryunitprofunctor_Arr_arr _ _ (category_Comp $x $h)) ;

//TODO normalization operations define recursively by cases
symbol arr_category_Arr [C : category] [I : cat] [F: func I (category_cat C)] [J : cat] [G: func J (category_cat C)] [M : obj I] [N : obj J] 
  (a : arr M (Unit_mod F G) N) :
 category_Arr (obj_category_Obj (M ∘>o F)) (obj_category_Obj (N ∘>o G)) ;

rule (arr_category_Arr (category_Arr_cov_arr0 _ _ _ $a)) ↪ $a;
rule (arr_category_Arr (category_Arr_cov_arr' _ _ _ $a)) ↪ $a;

//have both cov elim and con elim?, and separrated from (neutral) categoryunitprofunctor elim?
injective symbol  category_elim_cov_func [C : category] : Π [E : cat]
(E_obj : Π (M : category_Obj C), obj E)
(E_cov_arr : Π [M N : category_Obj C] (a : category_Arr M N), 
  arr (E_obj M) (Unit_mod Id_func (Obj_func (E_obj N))) Terminal_obj)
// (E_cov_hom_nat : Π [M N : category_Obj C] (a : category_Arr M N) [M'] (b : category_Arr M' M), 
//   π ((E_cov_arr M' M b) '∘a (( _ ) _'∘>  (Arr_hom (E_cov_arr M N a))) = E_cov_arr M' N (category_Comp b a)))
,  func (category_cat C) E;

//TODO later as accumulator? for redirecting associativity
// rule $M ∘>o ( category_elim_cov_func $E_obj $E_cov_arr)
//   ↪ $E_obj (obj_category_Obj $M);
rule $M ∘>o ( category_elim_cov_func $E_obj $E_cov_arr)
  ↪ $E_obj (obj_category_Obj $M);

// rule (Func_cov_hom ( category_elim_cov_func $E_obj $E_cov_arr) _) ∘>'_(_) ∘a' (category_Arr_cov_arr $M $N $a)
//   ↪ $E_cov_arr $M $N $a;
//TODO redo this for general arrow on left and use its normalization on right
rule (Func_cov_hom ( category_elim_cov_func $E_obj $E_cov_arr) _) ∘>'_(_) ∘a' (category_Arr_cov_arr0 _ $M $N $a)
  ↪ $E_cov_arr _ (obj_category_Obj $N) $a;

//TODO retry
// rule (Func_cov_hom ( category_elim_cov_func $E_obj $E_cov_arr) Id_func) ∘>'_(_) ∘a' $a
//   ↪ $E_cov_arr _ _ (category_cov_arr_Arr $a);

// rule (Func_cov_hom ( category_elim_cov_func $E_obj $E_cov_arr) _) ∘>'_(_) ∘' (Arr_hom (category_Arr_cov_arr $a))
//   ↪ $E_cov_arr _ _ $a;

//TEST  ERASE?
injective symbol  cat_elim_cov_func [C : cat] : Π [E : cat]
(E_obj : Π (M : obj C), obj E)
(E_cov_arr : Π [M N : obj C] (a : arr M (Unit_mod Id_func (Obj_func N)) Terminal_obj), 
  arr (E_obj M) (Unit_mod Id_func (Obj_func (E_obj N))) Terminal_obj)
// (E_cov_hom_nat : Π [M N : obj C] (a : arr M (Unit_mod Id_func (Obj_func N)) Terminal_obj) 
//   [M'] (b : arr M' (Unit_mod Id_func (Obj_func M)) Terminal_obj), 
//   π ((E_cov_arr M' M b) '∘a (( _ ) _'∘>  (Arr_hom _ _ (E_cov_arr M N a))) 
//       = E_cov_arr M' N (b '∘a ((_) _'∘> (Arr_hom _ _ a)))))
,  func C E;
rule $M ∘>o ( cat_elim_cov_func $E_obj $E_cov_arr)
  ↪ $E_obj $M;
// rule @∘a' _ _ _ _ _ _ Terminal_obj _ ((Func_cov_hom ( cat_elim_cov_func $E_obj $E_cov_arr) _) ∘>'_(_))  $a
//   ↪ $E_cov_arr _ _  $a;

//eta  review this

symbol category_elim_cov_func_Obj [C : category] [E : cat]
(F : func (category_cat C) E):
Π (M : category_Obj C), obj E;
// ≔ λ M, (category_Obj_obj M) ∘>o F;
rule @category_elim_cov_func_Obj $C $E $F $M ↪  (category_Obj_obj $M) ∘>o $F;

symbol category_elim_cov_func_Arr [C : category] [E : cat]
(F : func (category_cat C) E):
Π [M N : category_Obj C] (a : category_Arr M N), 
  arr (category_elim_cov_func_Obj F M) (Unit_mod Id_func (Obj_func (category_elim_cov_func_Obj F N))) Terminal_obj;
// ≔ λ M N a, (Func_cov_hom F _) ∘>'_(_) ∘a' (category_Arr_cov_arr a);
rule (@category_elim_cov_func_Arr $C $E $F $M $N $a) ↪ (Func_cov_hom $F _) ∘>'_(_) ∘a' (category_Arr_cov_arr0 Id_func (category_Obj_obj $M) (category_Obj_obj $N) $a);


//eta
rule (category_elim_cov_func (category_elim_cov_func_Obj $F) (@category_elim_cov_func_Arr _ _ $F))
  ↪ $F;

//TODO REVIEW THIS
// rule obj_category_Obj ((category_Obj_obj $X) ∘>o $F) ↪ obj_category_Obj (category_elim_cov_func_Obj $F $X);
// rule obj_category_Obj ((graph_Obj_obj $X) ∘>o $F) ↪ obj_category_Obj (graph_elim_cov_func_Obj _ $F $X);

// rule arr_category_Arr ((Func_cov_hom $F _) ∘>'_(_) ∘a' (category_Arr_cov_arr $a))
//    ↪ arr_category_Arr (category_elim_cov_func_Arr $F $a);


//(obj_category_Obj (graph_Obj_obj X ∘>o F))  (category_elim_cov_func_Obj $F (obj_category_Obj (graph_Obj_obj X)))
//this says that the correspondence in the freely-category adjunction is  not only bijection but is also isomorphism/equivalence of categories
symbol category_elim_cov_hom [C : category] : Π [E  : cat] [G : func (category_cat C) E] [F : func (category_cat C) E] 
  (t_arr : Π (M : category_Obj C), 
  arr ((category_Obj_obj M) ∘>o F) (Unit_mod Id_func (G <∘ (Obj_func (category_Obj_obj M)))) Terminal_obj) //TODO  o<∘
//   (t_nat : Π [M N : category_Obj C] (a : category_Arr M N), 
//  π(((Func_cov_hom F _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)) '∘a (( _ ) _'∘>  (Arr_hom _ _ (t_arr N)))
//  =   (t_arr M) '∘a (_)_'∘> (Arr_hom _ _ ((Func_cov_hom G _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)))))
  ,  hom F (Unit_mod Id_func G) Id_func;

rule (category_elim_cov_hom $x) '∘ (( _ ) _'∘>  (category_elim_cov_hom $h))
    ↪ category_elim_cov_hom (λ M,  ($x M) '∘a (( _ ) _'∘>  (Arr_hom _ (Obj_func _) ($h M)))) ;

// rule (category_elim_cov_hom $x) '∘ (( _ ) _'∘>  (category_elim_cov_hom $h))
//     ↪ category_elim_cov_hom (λ M,  ($x M) '∘ (( _ ) _'∘>  ($h M))) ;
rule  (category_elim_cov_hom $t_arr) ∘>'_(_) ∘a' (Id_cov_arr (category_Obj_obj $M))
↪ ($t_arr  $M );

symbol category_elim_cov_hom0 [C : category] : Π [E  : cat] [G : func (category_cat C) E] [E'] [F : func (category_cat C) E'] [H : func E' E] 
  (t_arr : Π (M : category_Obj C), 
  arr ((category_Obj_obj M) ∘>o F) (Unit_mod H (G <∘ (Obj_func (category_Obj_obj M)))) Terminal_obj) //TODO  o<∘
//   (t_nat : Π [M N : category_Obj C] (a : category_Arr M N), 
//  π(((Func_cov_hom F _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)) '∘a (( _ ) _'∘>  (Arr_hom _ _ (t_arr N)))
//  =   (t_arr M) '∘a (_)_'∘> (Arr_hom _ _ ((Func_cov_hom G _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)))))
  ,  hom F (Unit_mod H G) Id_func;

rule (category_elim_cov_hom0 $x) '∘ (( _ ) _'∘>  (category_elim_cov_hom0 $h))
    ↪ category_elim_cov_hom0 (λ M,  ($x M) '∘a (( _ ) _'∘>  (Arr_hom _ (Obj_func _) ($h M)))) ;

// rule (category_elim_cov_hom0 $x) '∘ (( _ ) _'∘>  (category_elim_cov_hom0 $h))
//     ↪ category_elim_cov_hom0 (λ M,  ($x M) '∘ (( _ ) _'∘>  ($h M))) ;
rule  (category_elim_cov_hom0 $t_arr) ∘>'_(_) ∘a' (Id_cov_arr (category_Obj_obj $M))
↪ ($t_arr  $M );

symbol category_elim_cov_hom' [C : category] : Π [E  : cat] [G : func (category_cat C) E] [F : func (category_cat C) E] 
  (t_arr : Π (M : obj (category_cat C)), 
  arr (M ∘>o F) (Unit_mod Id_func ((Obj_func M) ∘> G)) Terminal_obj) 
  ,  hom F (Unit_mod Id_func G) Id_func ≔
begin
  assume C E G F t_arr;
  refine category_elim_cov_hom _;
  assume M; refine (t_arr (category_Obj_obj M));
end;

symbol cat_elim_cov_hom [C : cat] : Π [E  : cat] [G : func C E] [E'] [F : func C E']  [H : func E' E]
  (t_arr : Π (M : obj C), 
  arr (M ∘>o F) (Unit_mod H ((Obj_func M) ∘> G)) Terminal_obj) //TODO  o<∘
  // (t_nat : Π [M N : obj C] (a : arr M (Unit_mod Id_func (Obj_func N)) Terminal_obj), 
  //       π(  ((Func_cov_hom F _) ∘>'_(_) ∘a' a) '∘a (( _ ) _'∘>  (Arr_hom _ _ (t_arr N)))
  //            =   (t_arr M) '∘a (_)_'∘> (Arr_hom _ _ ((Func_cov_hom G _) ∘>'_(_) ∘a' a))  ))
  ,  hom F (Unit_mod H G) Id_func;
rule  (cat_elim_cov_hom $t_arr) ∘>'_(_) ∘a' (Id_cov_arr $M) ↪ ($t_arr  $M );
rule (cat_elim_cov_hom $x) '∘ (( _ ) _'∘>  (cat_elim_cov_hom $h))
    ↪ cat_elim_cov_hom (λ M,  ($x M) '∘a (( _ ) _'∘>  (Arr_hom _ (Obj_func _) ($h M)))) ;


    // symbol category_elim_cov_hom'' [C : category] : Π [E  : cat] [G : func (category_cat C) E] [F : func (category_cat C) E] 
//   (t_arr : Π (M : category_Obj C), 
//   arr ((category_Obj_obj M) ∘>o F) (Unit_mod Id_func (G <∘ (Obj_func (category_Obj_obj M)))) Terminal_obj) //TODO  o<∘
// //   (t_nat : Π [M N : category_Obj C] (a : category_Arr M N), 
// //  π(((Func_cov_hom F _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)) '∘a (( _ ) _'∘>  (Arr_hom (t_arr N)))
// //  =   (t_arr M) '∘a (_)_'∘> (Arr_hom ((Func_cov_hom G _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M) (category_Obj_obj N) a)))))
//   ,  hom F (Unit_mod Id_func G) Id_func ≔
//   begin
//     assume C E G F t_arr;
//     refine cat_elim_cov_hom _;
//     assume M; refine (t_arr (obj_category_Obj M));

//   abort;

//TODO define category_elim_cov_hom from categoryunitprofunctor_elim_hom ? or keep both because of rule below for interaction?
symbol  categoryunitprofunctor_elim_hom [C : category] : Π [A B: cat]  (F : func (category_cat C) A) [R : mod A B] (G : func (category_cat C) B) 
(t_arr : Π [M : category_Obj C] [N : category_Obj C] (r : category_Arr M N),
        arr ((category_Obj_obj M) ∘>o F) R ((category_Obj_obj N) ∘>o G))
//  (t_hom_nat : Π [M : category_Obj C] [N : category_Obj C] (r : category_Arr  M N),
//           Π [M' : category_Obj C] (a : category_Arr M' M),
//         π (((Func_cov_hom F _) ∘>'_(_) ∘a' (category_Arr_cov_arr (category_Obj_obj M') (category_Obj_obj M) a)) '∘a (_)_'∘> (Arr_hom (t_arr _ _ r))
//         = t_arr _ _ (category_Comp a r)))
, hom F R G;

rule ((Func_cov_hom $F _) ∘>'_(_) ∘a' (category_Arr_con_arr (category_Obj_obj $M') (category_Obj_obj $M) $a)) '∘a (_)_'∘> (categoryunitprofunctor_elim_hom $F $G $t_arr)
↪ ($t_arr $M' $M $a);
// rule ((Func_cov_hom $F _) ∘>'_(_) ∘' (Arr_hom (category_Arr_con_arr $a))) '∘ (_)_'∘> (categoryunitprofunctor_elim_hom $F $G $t_arr)
// ↪ ($t_arr _ _ $a);

rule (category_elim_cov_hom $x) '∘ (_)_'∘> (categoryunitprofunctor_elim_hom $F $G $t_arr)
↪ (categoryunitprofunctor_elim_hom _ $G  (λ M N r, ($x M) '∘a (_)_'∘> (Arr_hom _ (Obj_func _) ($t_arr _ _ r))));
rule (category_elim_cov_hom0 $x) '∘ (_)_'∘> (categoryunitprofunctor_elim_hom $F $G $t_arr)
↪ (categoryunitprofunctor_elim_hom _ $G  (λ M N r, ($x M) '∘a (_)_'∘> (Arr_hom _ (Obj_func _) ($t_arr _ _ r))));

// rule (category_elim_cov_hom $x) '∘ (_)_'∘> (categoryunitprofunctor_elim_hom $F $G $t_arr)
// ↪ (categoryunitprofunctor_elim_hom _ $G  (λ M N r, ($x M) '∘ (_)_'∘> ($t_arr _ _ r)));

//TODO redo this with presheaves grammatical entry...
symbol category_elim_cov_transf [C : category] : 
Π [A' A : cat] [F : func A' A]
[W : mod A' (category_cat C)] [R : mod A (category_cat C)] 
(t_arr : Π [N : category_Obj C] ,
    transf (W  <<∘ (Obj_func (category_Obj_obj N))) 
          F (R  <<∘ (Obj_func (category_Obj_obj N))) Id_func )

, transf W F R Id_func;

rule (category_elim_cov_transf $t_arr) <<∘1 (Obj_func (category_Obj_obj $N)) ↪ ($t_arr $N);


constant symbol diagram_func [C : graph] [E : category] (F : diagram C E):
func (graph_cat C) (category_cat E) ;
rule $M ∘>o (diagram_func $F) ↪ category_Obj_obj (diagram_Obj $F (obj_graph_Obj $M));
rule (Func_cov_hom (diagram_func $F) _) ∘>'_(_) ∘a' (graph_Arr_cov_arr $M $N $a)
↪ category_Arr_cov_arr0 _ _ _ (diagram_Arr $F $a);

//extra rules for extra special constants
rule graphMorph_func $H ∘> diagram_func $F ↪ diagram_func (comp_graphMorph_diagram $H $F);

constant symbol functor_func [C E : category] (F : functor C E):
func (category_cat C) (category_cat E) ;
rule $M ∘>o (functor_func $F) ↪ category_Obj_obj (functor_Obj $F (obj_category_Obj $M));
rule (Func_cov_hom (functor_func $F) _) ∘>'_(_) ∘a' (category_Arr_cov_arr0 _ $M $N $a)
↪ category_Arr_cov_arr0 _ _ _ (functor_Arr $F $a);

constant symbol transformation_con_hom : Π [C D : category] [F G : functor C D] (h : transformation F G), 
hom Id_func (Unit_mod (functor_func F) Id_func) (functor_func G);
constant symbol transformation_cov_hom : Π [C D : category] [F G : functor C D] (h : transformation F G),
hom (functor_func F) (Unit_mod Id_func (functor_func G)) Id_func;

rule  (@transformation_cov_hom _ _ $F $G $h) ∘>'_(_) ∘a' (Id_cov_arr (category_Obj_obj $M))
↪ (category_Arr_cov_arr0 _ (category_Obj_obj $M ∘>o functor_func $F) (category_Obj_obj (functor_Obj $G (obj_category_Obj (category_Obj_obj $M)))) (transformation_Arr $h $M) );

rule (transformation_cov_hom $x) '∘ (( _ ) _'∘>  (transformation_cov_hom $h))
    ↪ transformation_cov_hom (comp_transformation $x $h) ;

///these extra conversion rules for transformation_cov_hom and functor_func are necessary? the equations versions should be derivable by deduction or metatheorem
rule (functor_func $F) ∘> (functor_func $G)
    ↪ functor_func (comp_functor $F $G) ;

rule  ((@transformation_cov_hom $C $D $F $G $h) ∘>'_ ( _ )) ∘' (@transformation_cov_hom $C' $D' $F' $G' $y)
    ↪ transformation_cov_hom (comp_transformation (tensor_con_transformation $F' $h) (tensor_cov_transformation $y $G)) ;
// : hom (functor_func F' ∘> functor_func F) (Unit_mod Id_func (functor_func G) <<∘ functor_func G') (Id_func <∘ Id_func)

rule ((Func_cov_hom (functor_func $K) Id_func) ∘>'_ ( _ )) ∘' (transformation_cov_hom $h) 
    ↪ (transformation_cov_hom (tensor_cov_transformation $h $K)) ;

rule (@transformation_cov_hom $C $D $F $G $h) '∘ (( _ ) _'∘>  (Func_con_hom (functor_func $K) (functor_func $G)) )
    ↪ ((Func_con_hom (functor_func $K) (functor_func $F)) ∘>'_ ( _ ) /* cast */) ∘' (transformation_con_hom (tensor_cov_transformation $h $K)) ;
  
/////////////------------

//TODO ELIMINATION FOR FIBRATIONS
// symbol  category_elim_cov_funcs [C : category] : Π [E : catd (category_cat C)] //(E_isf : isFibration_con E)
// (E_obj : Π (M : category_Obj C), funcs (Obj_func (category_Obj_obj M)) E)
// (E_cov_arr : Π [M N : category_Obj C] (a : category_Arr M N), 
//    homs (Arr_hom _ _ (category_Arr_cov_arr _ _ a))  (E_obj M) (Unit_modd Id_funcd (Funcs_funcd (E_obj N))) (Func_funcs Id_func))
// // (E_nat : Π [M N : category_Obj C] (a : category_Arr M N), 
// //         π (Fibration_con_funcd E_isf (E_obj N) (Arr_hom (category_Arr_con_arr a))
// //                     = Fibre_intro_funcd _ _ Id_func (E_obj M) ))
// ,  funcs Id_func E;

//COMMMENT
//TODO redo with objd (is funcs from terminal_cat) and arrd (is homds from terminal_cat besides terminal_catd)
symbol  category_elim_cov_funcd' :  //maybe quantify over abstract obj
Π [C: category], Π [E: catd (category_cat C)], // Π E_isf: isFibration_con E, //for E_nat

Π E_obj: (Π M: category_Obj C, funcd (Terminal_catd Terminal_cat) (Obj_func (category_Obj_obj M)) E), 

Π (E_cov_arr : Π M: category_Obj C, Π N: category_Obj C, Π a: category_Arr M N, 
      homd (Arr_hom (Obj_func (category_Obj_obj M)) Id_func 
                (category_Arr_cov_arr0 Id_func (category_Obj_obj M) (category_Obj_obj N) a)) 
          (E_obj M) (Unit_modd Id_funcd (E_obj N)) Id_funcd),

// Π (E_nat : Π M: category_Obj C, Π N: category_Obj C, Π a: category_Arr M N, 
//       π (Fibration_con_funcd E_isf (E_obj N) 
//               (Arr_hom Id_func (Obj_func (category_Obj_obj N)) 
//                   (category_Arr_con_arr (category_Obj_obj M) (category_Obj_obj N) a)) 
//         = Fibre_intro_funcd E (Obj_func (category_Obj_obj M)) Id_func (E_obj M))),

funcd (Terminal_catd (category_cat C)) Id_func E;


//////////////----------

//TODO: in adition to weightprof
(C D : category) inductive profunctor : TYPE ≔ | Struct_profunctor : Π 
(profunctor_Arr : category_Obj C → category_Obj D → Set)
(profunctor_cov_Comp : Π [M : category_Obj C] [K L : category_Obj D], category_Arr K L → τ (profunctor_Arr M K →_ profunctor_Arr M L))
(profunctor_con_Comp : Π [M N : category_Obj C] [K : category_Obj D], category_Arr M N →  τ (profunctor_Arr N K →_ profunctor_Arr M K)), profunctor C D;
injective symbol profunctor_Arr [C D : category] (R : profunctor C D) : category_Obj C → category_Obj D → TYPE;
rule profunctor_Arr (Struct_profunctor $1 $2 $3) ↪ λ M N, τ ($1 M N);
injective symbol profunctor_cov_Comp [C D : category] [R : profunctor C D] : Π [M : category_Obj C] [K L : category_Obj D], category_Arr K L →  profunctor_Arr R M K → profunctor_Arr R M L;
rule @profunctor_cov_Comp _ _ (Struct_profunctor $1 $2 $3) ↪ $2;
injective symbol profunctor_con_Comp [C D : category] [R : profunctor C D] : Π [M N : category_Obj C] [K : category_Obj D], category_Arr M N →  profunctor_Arr R N K → profunctor_Arr R M K;
rule @profunctor_con_Comp _ _ (Struct_profunctor $1 $2 $3) ↪ $3;

constant symbol profunctor_mod : Π [C D : category] (R : profunctor C D), mod (category_cat C) (category_cat D);
constant symbol profunctor_Arr_arr : Π [C D : category] [R : profunctor C D] (M : obj (category_cat C)) (N : obj (category_cat D)) (r : profunctor_Arr R (obj_category_Obj M) (obj_category_Obj N)),
 arr M (profunctor_mod R) N;


//////////------------

inductive iterminal (J' : cat) (B : cat)  : TYPE ≔ 
| Struct_iterminal [J' B] : 
Π (iterminal_Func : func J' B) 
  (iterminal_Univ :  Π (I : cat) (L0 : func I B), Π (S : func J' I) ,  
                   hom S (Unit_mod L0 iterminal_Func) Id_func), 
   @iterminal J' B;

injective symbol iterminal_Func [J' B] (L : @iterminal J' B): func J' B;
rule iterminal_Func (Struct_iterminal $1 $2) ↪ $1;
injective symbol iterminal_Univ [J' B] (L : @iterminal J' B): Π  (I : cat) (L0 : func I B), Π (S : func J' I), 
hom S (Unit_mod L0 (@iterminal_Func J' B L)) Id_func ;
rule iterminal_Univ (Struct_iterminal $1 $2) ↪ $2;


////---------


inductive iproducing [J' : cat] [B : cat]  [A : graph]  
(F : func (graph_cat (optionGraph A)) B) (W : mod J' (graph_cat (optionGraph A)) )
[L : func J' B] 
(l : hom L (((Unit_mod Id_func 
    (F <∘ (graphMorph_func (optionGraph_graphMorph A)))) ) ⇐
    (W <<∘ (graphMorph_func (optionGraph_graphMorph A)) )) Id_func) : TYPE ≔ 
| Struct_iproducing [J' B A F W L l]  : Π
(I : cat) (S : func J' I) 
(iproducing_Func : func I B) 
(iproducing_Imply : hom S (((Unit_mod iproducing_Func F)) ⇐ W) Id_func)
(iproducing_Hom : hom S (Unit_mod iproducing_Func L) Id_func), @iproducing J' B A F W L l;

//TODO iproducing_Set
injective symbol iproducing_I [J' B A F W L l] (e : @iproducing J' B A F W L l): cat;
rule iproducing_I (Struct_iproducing $I $S $1 $2 $3) ↪ $I;
injective symbol iproducing_S [J' B A F W L l] (e : @iproducing J' B A F W L l): func J' (iproducing_I e);
rule iproducing_S (Struct_iproducing $I $S $1 $2 $3) ↪ $S;

injective symbol iproducing_Func [J' B A F W L l] (e : @iproducing J' B A F W L l): func (iproducing_I e) B;
rule iproducing_Func (Struct_iproducing $I $S $1 $2 $3) ↪ $1;
injective symbol iproducing_Imply [J' B A F W L l] (e : @iproducing J' B A F W L l): hom (iproducing_S e) (((Unit_mod (@iproducing_Func J' B A F W L l e) F)) ⇐ W) Id_func  ;
rule iproducing_Imply (Struct_iproducing $I $S $1 $2 $3) ↪ $2;
injective symbol iproducing_Hom [J' B A F W L l] (e : @iproducing J' B A F W L l): hom (iproducing_S e) (Unit_mod (@iproducing_Func J' B A F W L l e) L) Id_func;
rule iproducing_Hom (Struct_iproducing $I $S $1 $2 $3) ↪ $3;

inductive iproduct [J' : cat] [B : cat]  [A : graph]  
(F : func (graph_cat (optionGraph A)) B) (W : mod J' (graph_cat (optionGraph A)) )
[L : func J' B] 
(l : hom L (((Unit_mod Id_func  
    (F <∘ (graphMorph_func (optionGraph_graphMorph A)))) ) ⇐ 
    (W <<∘ (graphMorph_func (optionGraph_graphMorph A)) )) Id_func) : TYPE ≔ 
| Struct_iproduct [J' B A F W L l] : 
Π (iproduct_Func : func J' B) 
(iproduct_Hom : hom iproduct_Func (Unit_mod Id_func L) Id_func)
(iproduct_Imply : hom iproduct_Func (((Unit_mod Id_func F)) ⇐ W) Id_func)
(iproduct_Univ : Π e : @iproducing J' B A F W L l, 
   hom (iproducing_S e) (Unit_mod (iproducing_Func e)  iproduct_Func) Id_func ), 
   @iproduct J' B A F W L l;

//TODO iproduct_Set
injective symbol iproduct_Func [J' B A F W L l] (e : @iproduct J' B A F W L l): func J' B;
rule iproduct_Func (Struct_iproduct $1 $2 $3 $4) ↪ $1;
injective symbol iproduct_Hom [J' B A F W L l] (e : @iproduct J' B A F W L l): hom (@iproduct_Func J' B A F W L l e) (Unit_mod Id_func L) Id_func;
rule iproduct_Hom (Struct_iproduct $1 $2 $3 $4) ↪ $2;
injective symbol iproduct_Imply [J' B A F W L l] (e : @iproduct J' B A F W L l): hom (@iproduct_Func J' B A F W L l e) (((Unit_mod Id_func F)) ⇐ W) Id_func;
rule iproduct_Imply (Struct_iproduct $1 $2 $3 $4) ↪ $3;
injective symbol iproduct_Univ [J' B A F W L l] (e : @iproduct J' B A F W L l): Π e' : @iproducing J' B A F W L l, hom (iproducing_S e') (Unit_mod (iproducing_Func e') (@iproduct_Func J' B A F W L l e) ) Id_func ;
rule iproduct_Univ (Struct_iproduct $1 $2 $3 $4) ↪ $4;

/////////------------

inductive iqualizing [J' : cat] [B : cat]  [A : graph] [X : graph_Obj A] [Y : graph_Obj A] 
(F : func (graph_cat (joinGraph X Y)) B) (W : mod J' (graph_cat (joinGraph X Y)) )
[L : func J' B] 
(l : hom L (((Unit_mod Id_func 
    (F <∘ (graphMorph_func (joinGraph_graphMorph X Y)))) ) ⇐ 
    (W <<∘ (graphMorph_func (joinGraph_graphMorph X Y)) )) Id_func) : TYPE ≔ 
| Struct_iqualizing [J' B A X Y F W L l]  : Π
(I : cat) (S : func J' I) 
(iqualizing_Func : func I B) 
(iqualizing_Imply : hom S (((Unit_mod iqualizing_Func F)) ⇐ W) Id_func)
(iqualizing_Hom : hom S (Unit_mod iqualizing_Func L) Id_func), @iqualizing J' B A X Y F W L l;

//TODO iqualizing_Set
injective symbol iqualizing_I [J' B A X Y F W L l] (e : @iqualizing J' B A X Y F W L l): cat;
rule iqualizing_I (Struct_iqualizing $I $S $1 $2 $3) ↪ $I;
injective symbol iqualizing_S [J' B A X Y F W L l] (e : @iqualizing J' B A X Y F W L l): func J' (iqualizing_I e);
rule iqualizing_S (Struct_iqualizing $I $S $1 $2 $3) ↪ $S;

injective symbol iqualizing_Func [J' B A X Y F W L l] (e : @iqualizing J' B A X Y F W L l): func (iqualizing_I e) B;
rule iqualizing_Func (Struct_iqualizing $I $S $1 $2 $3) ↪ $1;
injective symbol iqualizing_Imply [J' B A X Y F W L l] (e : @iqualizing J' B A X Y F W L l): hom (iqualizing_S e) (((Unit_mod (@iqualizing_Func J' B A X Y F W L l e) F)) ⇐ W) Id_func  ;
rule iqualizing_Imply (Struct_iqualizing $I $S $1 $2 $3) ↪ $2;
injective symbol iqualizing_Hom [J' B A X Y F W L l] (e : @iqualizing J' B A X Y F W L l): hom (iqualizing_S e) (Unit_mod (@iqualizing_Func J' B A X Y F W L l e) L) Id_func;
rule iqualizing_Hom (Struct_iqualizing $I $S $1 $2 $3) ↪ $3;

inductive iqualizer [J' : cat] [B : cat]  [A : graph] [X : graph_Obj A] [Y : graph_Obj A] 
(F : func (graph_cat (joinGraph X Y)) B) (W : mod J' (graph_cat (joinGraph X Y)) )
[L : func J' B] 
(l : hom L (((Unit_mod Id_func  
    (F <∘ (graphMorph_func (joinGraph_graphMorph X Y)))) ) ⇐ 
    (W <<∘ (graphMorph_func (joinGraph_graphMorph X Y)) )) Id_func) : TYPE ≔ 
| Struct_iqualizer [J' B A X Y F W L l] : 
Π (iqualizer_Func : func J' B) 
(iqualizer_Hom : hom iqualizer_Func (Unit_mod Id_func L) Id_func)
(iqualizer_Imply : hom iqualizer_Func (((Unit_mod Id_func F)) ⇐ W) Id_func)
(iqualizer_Univ : Π e : @iqualizing J' B A X Y F W L l, 
   hom (iqualizing_S e) (Unit_mod (iqualizing_Func e)  iqualizer_Func) Id_func ), 
   @iqualizer J' B A X Y F W L l;

//TODO iqualizer_Set
injective symbol iqualizer_Func [J' B A X Y F W L l] (e : @iqualizer J' B A X Y F W L l): func J' B;
rule iqualizer_Func (Struct_iqualizer $1 $2 $3 $4) ↪ $1;
injective symbol iqualizer_Hom [J' B A X Y F W L l] (e : @iqualizer J' B A X Y F W L l): hom (@iqualizer_Func J' B A X Y F W L l e) (Unit_mod Id_func L) Id_func;
rule iqualizer_Hom (Struct_iqualizer $1 $2 $3 $4) ↪ $2;
injective symbol iqualizer_Imply [J' B A X Y F W L l] (e : @iqualizer J' B A X Y F W L l): hom (@iqualizer_Func J' B A X Y F W L l e) (((Unit_mod Id_func F)) ⇐ W) Id_func;
rule iqualizer_Imply (Struct_iqualizer $1 $2 $3 $4) ↪ $3;
injective symbol iqualizer_Univ [J' B A X Y F W L l] (e : @iqualizer J' B A X Y F W L l): Π e' : @iqualizing J' B A X Y F W L l, hom (iqualizing_S e') (Unit_mod (iqualizing_Func e') (@iqualizer_Func J' B A X Y F W L l e) ) Id_func ;
rule iqualizer_Univ (Struct_iqualizer $1 $2 $3 $4) ↪ $4;


(C : category) inductive weightprof (D : graph) : TYPE ≔ | Struct_weightprof [D] : Π 
(weightprof_Arr : category_Obj C → graph_Obj D → Set)
(weightprof_cov_Comp : Π [M : category_Obj C] [K L : graph_Obj D], 
  graph_Arr K L → 
    τ (weightprof_Arr M K →_ weightprof_Arr M L)) 
(weightprof_con_Comp : Π [N : category_Obj C] [K : graph_Obj D] [M : category_Obj C],
    category_Arr M N → 
   τ (weightprof_Arr N K →_ weightprof_Arr M K))
, weightprof C D;

constant symbol weightprof_Set (C : category) (D : graph) : Set;
rule τ (weightprof_Set $C $D) ↪ weightprof $C $D;
injective symbol weightprof_Arr_Set [C : category] [D : graph] (R : weightprof C D) : category_Obj C → graph_Obj D → Set;
rule @weightprof_Arr_Set _ _ (Struct_weightprof $1 $2 $3) ↪ $1 ;
/* injective */ symbol weightprof_Arr [C : category] [D : graph] (R : weightprof C D) : category_Obj C → graph_Obj D  → TYPE ≔ λ M N, τ (weightprof_Arr_Set R  M N);
injective symbol weightprof_cov_Comp [C : category] [D : graph] [R : weightprof C D] : Π [M : category_Obj C] [K L : graph_Obj D], 
graph_Arr K L →
  τ (weightprof_Arr_Set R M K →_ weightprof_Arr_Set R M L);
rule @weightprof_cov_Comp _ _ (Struct_weightprof $1 $2 $3) ↪ $2;
injective symbol weightprof_con_Comp [C : category] [D : graph] [R : weightprof C D] : Π [N : category_Obj C] [K : graph_Obj D] [M : category_Obj C],
category_Arr M N → 
 τ (weightprof_Arr_Set R N K →_ weightprof_Arr_Set R M K);
rule @weightprof_con_Comp _ _ (Struct_weightprof $1 $2 $3) ↪ $3;


constant symbol weightprof_mod : Π [C : category] [D : graph] (R : weightprof C D), mod (category_cat C) (graph_cat D);

constant symbol weightprof_Arr_arr : Π [C : category] [D : graph] [R : weightprof C D] (M : obj (category_cat C)) (N : obj (graph_cat D)) (r : weightprof_Arr R (obj_category_Obj M) (obj_graph_Obj N)),
arr M (weightprof_mod R) N;
// TODO: todo generalize Id_func
rule ((category_Arr_cov_arr0 Id_func $M $N $h)) '∘a (_)_'∘> (Arr_hom _ _ (weightprof_Arr_arr $N $L $r))
   ↪ (weightprof_Arr_arr $M $L (weightprof_con_Comp $h $r));


   // rule ((category_Arr_cov_arr $h)) '∘a (_)_'∘> (Arr_hom (weightprof_Arr_arr $r))
//    ↪ (weightprof_Arr_arr (weightprof_con_Comp (category_Arr_cov_arr $h) $r));
// rule (Arr_hom (category_Arr_cov_arr $h)) '∘ (_)_'∘> (Arr_hom (weightprof_Arr_arr $r))
//    ↪ Arr_hom (weightprof_Arr_arr (weightprof_con_Comp (category_Arr_cov_arr $h) $r));
// //todo generalize Id_func
// rule $h '∘ (Id_func)_'∘> weightprof_Arr_arr $r
//    ↪ weightprof_Arr_arr (weightprof_con_Comp $h $r);

rule (Arr_hom _ _ (weightprof_Arr_arr _ $N $r)) ∘>'_ (_) ∘a' (graph_Arr_con_arr $N $L $a)
   ↪ (weightprof_Arr_arr _ $L (weightprof_cov_Comp $a $r));

symbol arr_weightprof_Arr [C : category] [D : graph] [R : weightprof C D] [M : obj (category_cat C)] [N : obj (graph_cat D)]  
(a : arr M (weightprof_mod R) N)
: weightprof_Arr R (obj_category_Obj M) (obj_graph_Obj N) ;
rule (arr_weightprof_Arr (weightprof_Arr_arr _ _ $a)) ↪ $a;

   //TODO both separrate cov and con? outer fixed M: transf (M o>> (weightprof_mod R')) (M o> F) R G;
 symbol  weightprof_elim_transf [A' : category] [B' : graph] /* TODO: R' implicit? */ [R' : weightprof A' B'] : Π [A B: cat]  (F : func (category_cat A') A) [R : mod A B] (G : func (graph_cat B') B) 
 (t_arr : Π  [M : category_Obj A'] [N : graph_Obj B'] (r : weightprof_Arr R' M N),
             arr ( (category_Obj_obj M) ∘>o F) R ((graph_Obj_obj N) ∘>o G))
//  (t_hom_con_nat : Π [M : category_Obj A'] [N : category_Obj B'] (r : weightprof_Arr R' M N),
//           Π [M' : category_Obj A'] (a : category_Arr M' M),
//         π (((Func_cov_hom F _) ∘>'_(_) ∘' (category_Arr_cov_arr a)) '∘ (_)_'∘> t_arr _ _ r
//         = t_arr _ _ (weightprof_con_Comp a r)))
// t_hom_cov_nat
, transf (weightprof_mod R') F R G;
rule ( (weightprof_Arr_arr (category_Obj_obj $M) (graph_Obj_obj $N) $r)) '∘a (weightprof_elim_transf $F $G $t_arr)
↪ ($t_arr _ _ $r);
rule (weightprof_elim_transf $F $G $t_arr) ∘a' ( (weightprof_Arr_arr (category_Obj_obj $M) (graph_Obj_obj $N) $r)) 
↪ ($t_arr _ _ $r);
// rule (Arr_hom (weightprof_Arr_arr $r)) '∘ (weightprof_elim_transf $F $G $t_arr)
// ↪ ($t_arr _ _ $r);

/* //TODO review this alt
symbol  mod_elim_transf [A' : cat] [B' : graph] [R' : mod A' (graph_cat B')] : Π [A B: cat]  (F : func A' A) [R : mod A B] (G : func (graph_cat B') B) 
(t_arr : Π  [M : obj A'] [N : graph_Obj B'] (r : arr M R' (graph_Obj_obj N)),
            arr ( M ∘>o F) R ((graph_Obj_obj N) ∘>o G))
//  (t_hom_con_nat : Π [M : category_Obj A'] [N : category_Obj B'] (r : weightprof_Arr R' M N),
//           Π [M' : category_Obj A'] (a : category_Arr M' M),
//         π (((Func_cov_hom F _) ∘>'_(_) ∘' (category_Arr_cov_arr a)) '∘ (_)_'∘> t_arr _ _ r
//         = t_arr _ _ (weightprof_con_Comp a r)))
// t_hom_cov_nat
, transf R' F R G;
rule ( (weightprof_Arr_arr (graph_Obj_obj $M) $r)) '∘a (mod_elim_transf $F $G $t_arr)
↪ ($t_arr _ _ ( (weightprof_Arr_arr (graph_Obj_obj $M) $r)));
rule (mod_elim_transf $F $G $t_arr) ∘a' ( (weightprof_Arr_arr (graph_Obj_obj $M) $r)) 
↪ ($t_arr _ _ (weightprof_Arr_arr (graph_Obj_obj $M) $r));
 */
symbol weightprof_elim_transf_con_Arr [A' : category] [B' : graph] [R' : weightprof A' B'] [ B: cat]  [R : mod (category_cat A') B] [G : func (graph_cat B') B]
(t: transf (weightprof_mod R') Id_func R G) : 
 Π  (M : category_Obj A') (N : graph_Obj B') (r : weightprof_Arr R' M N),
 arr ( (category_Obj_obj M) ) R ((graph_Obj_obj N) ∘>o G);
// ≔ λ M N r, ((weightprof_Arr_arr (graph_Obj_obj _)  r)) '∘a t;
rule weightprof_elim_transf_con_Arr $t $M $N $r ↪ ((weightprof_Arr_arr  (category_Obj_obj $M) (graph_Obj_obj $N)  $r)) '∘a $t;
//instance eta for F=Id_func
rule (weightprof_elim_transf Id_func $G (@weightprof_elim_transf_con_Arr _ _ _ _ _ $G $t)) ↪ $t;

/* symbol mod_elim_transf_con_Arr [A' : cat] [B' : graph] [R' : mod A' (graph_cat B')] [ B: cat]  [R : mod A' B] [G : func (graph_cat B') B]
(t: transf R' Id_func R G) : 
 Π  (M : obj A') (N : graph_Obj B') (r : arr M R' (graph_Obj_obj N)),
 arr ( M ) R ((graph_Obj_obj N) ∘>o G);
 rule mod_elim_transf_con_Arr $t $M $N $r ↪ $r '∘a $t;
 rule (mod_elim_transf Id_func $G (@mod_elim_transf_con_Arr _ _ _ _ _ $G $t)) ↪ $t;
  */

symbol weightprof_elim_transf_cov_Arr [A' : category] (B' : graph) [R' : weightprof A' B'] [ A : cat] [F : func (category_cat A') A]  [R : mod A (graph_cat B')] 
(t: transf (weightprof_mod R') F R Id_func) : 
 Π  (M : category_Obj A') (N : graph_Obj B') (r : weightprof_Arr R' M N),
 arr ( (category_Obj_obj M) ∘>o F) R ((graph_Obj_obj N));
//≔ λ M N r, t ∘a' ( (weightprof_Arr_arr (graph_Obj_obj _) r));
rule weightprof_elim_transf_cov_Arr _ $t $M $N $r ↪ $t ∘a' ( (weightprof_Arr_arr (category_Obj_obj $M) (graph_Obj_obj $N) $r));
//instance eta for F=Id_func
rule (weightprof_elim_transf $F Id_func (@weightprof_elim_transf_cov_Arr _ _ _ _ $F _ $t))
↪ $t;

/* symbol mod_elim_transf_cov_Arr [A' : cat] [B' : graph] [R' : mod A' (graph_cat B')] [ A : cat] [F : func A' A]  [R : mod A (graph_cat B')] 
(t: transf R' F R Id_func) : 
 Π  (M : obj A') (N : graph_Obj B') (r : arr M R' (graph_Obj_obj N)),
 arr ( M ∘>o F) R ((graph_Obj_obj N));
//≔ λ M N r, t ∘a' ( (weightprof_Arr_arr (graph_Obj_obj _) r));
rule mod_elim_transf_cov_Arr $t $M $N $r ↪ $t ∘a' $r;
rule (mod_elim_transf $F Id_func (@mod_elim_transf_cov_Arr _ _ _ _ $F _ $t)) ↪ $t;
 */

symbol subst_cov_weightprof [C D] (R : weightprof C D) [E] (F : graphMorph E D) : weightprof C E ≔
begin 
  assume C D R E F;
  refine (Struct_weightprof (λ M N, weightprof_Arr_Set R M (graphMorph_Obj F N)) _ _)
  { assume M K L a h;
  refine (weightprof_cov_Comp (graphMorph_Arr F a) h);
}
{ assume N K M a h;
  simplify;
  refine (weightprof_con_Comp a h);
};
end;

rule (weightprof_mod $R) <<∘ (graphMorph_func $F)
↪ (weightprof_mod (subst_cov_weightprof $R $F));

symbol subst_con_weightprof [C D] (R : weightprof C D) [C'] (F : functor C' C) : weightprof C' D ≔
begin 
assume C D R C' F;
refine (Struct_weightprof (λ M N, weightprof_Arr_Set R (functor_Obj F M ) N) _ _) 
{ assume M K L a h;
  refine (weightprof_cov_Comp a h);
}
{ assume N K M a h;
  simplify;
  refine (weightprof_con_Comp (functor_Arr F a ) h);
};
end;
rule (functor_func $F) ∘>> (weightprof_mod $R) 
↪ (weightprof_mod (subst_con_weightprof $R $F));


symbol terminal_weightprof (C : category) (D : graph) : weightprof C D ≔ 
  Struct_weightprof (λ M N, one_Set) (λ M K L a r, One) (λ N K M a r, One);
  
//could use Terminal_mod instead? but datatype is required, or add datatype properties on top of Terminal_mod
assert (C : category) (D : graph) (E : graph) (F : graphMorph E D) ⊢ 
(weightprof_mod (terminal_weightprof C D )) <<∘ (graphMorph_func F) ≡ (weightprof_mod (terminal_weightprof C E ));


/////////-------------

/// note that concrete data cone produces abstract grammatical transf, not grammatical hom; but concrete data transformation do produces abstract grammatical hom
constant symbol cone_transf [C : graph] [D : category] [L : category_Obj D] [F : diagram C D] (h : cone L F) : 
transf (weightprof_mod (terminal_weightprof terminal_category C)) 
  (functor_func (category_Obj_functor L)) 
  (Unit_mod Id_func (diagram_func F)) Id_func;
// ≔ begin
//   assume C D L F h; refine weightprof_elim_transf _ _ _ ;
//   assume _ N; simplify; 
//   assume _;
//   refine ( (category_Arr_cov_arr _  _ (cone_Arr h N))
//     '∘a ((Id_func)_'∘> Func_cov_hom (diagram_func F) (Obj_func (graph_Obj_obj N))) );
// abort;
//λ C D L F h, weightprof_elim_transf (functor_func (category_Obj_functor L)) Id_func (λ _ N _, category_Arr_cov_arr (category_Obj_obj L) (category_Obj_obj (diagram_Obj F (obj_graph_Obj (graph_Obj_obj N)))) (cone_Arr h N) '∘a (Id_func _'∘> Func_cov_hom (diagram_func F) (Obj_func (graph_Obj_obj N))))
rule (@cone_transf $C $D $L $F $h) ∘a' ( (weightprof_Arr_arr (category_Obj_obj $M) (graph_Obj_obj $N) $r)) 
↪ category_Arr_cov_arr0 _ (category_Obj_obj $L) (category_Obj_obj (diagram_Obj $F (obj_graph_Obj (graph_Obj_obj $N)))) (cone_Arr $h $N) '∘a (Id_func _'∘> Func_cov_hom (diagram_func $F) (Obj_func (graph_Obj_obj $N)));
//TODO review necessity of both rules
rule @weightprof_elim_transf_cov_Arr _ _ _ _ _ _ (@cone_transf $C $D $L $F $h) $M $N $r
↪ category_Arr_cov_arr0 _ (category_Obj_obj $L) (category_Obj_obj (diagram_Obj $F (obj_graph_Obj (graph_Obj_obj $N)))) (cone_Arr $h $N) '∘a (Id_func _'∘> Func_cov_hom (diagram_func $F) (Obj_func (graph_Obj_obj $N)));

//////---------

symbol lemma_ind_base_iterminal_ilimit' : Π (J': category), Π (B: cat), 
( iterminal (category_cat J') B ) → 
Π F: func (graph_cat emptyGraph) B, 
Π W: weightprof J' emptyGraph, 
   ilimit F (weightprof_mod W)  ≔ 
begin
assume J' B Hterminal F W;
apply Struct_sigma
{ refine (iterminal_Func Hterminal); 
}
{ refine (_ & _)
  { refine (Lambda_cov_transf_hom _);
    refine (weightprof_elim_transf _ _ _);
    assume M; simplify;
    refine rect_empty;

    // // ALT with questionable graph_elim_cov_transf
    // refine (graph_elim_cov_transf _);
    // simplify;
    // refine rect_empty;
  }
  { simplify;
    assume I M S  _;
    refine (iterminal_Univ Hterminal I M S);
  }
}
end;

  ////-----

symbol lemma_ind_hypothesis_iproduct_ilimit' : Π (J': category), Π (B: cat), 
(Π [A : graph] , 
  Π F: func (graph_cat (optionGraph A)) B, 
  Π W: weightprof J' (optionGraph A), 
  Π L: func (category_cat J') B, 
  Π l: hom L ((Unit_mod Id_func 
      (F <∘ (graphMorph_func (optionGraph_graphMorph A)))) ⇐ 
      ((weightprof_mod W) <<∘ (graphMorph_func (optionGraph_graphMorph A)))) Id_func, 
  iproduct F (weightprof_mod W) l) → 
Π (A : graph) , isFiniteGraph A → 
(Π F1: func (graph_cat A) B, 
 Π W1: weightprof J' A, 
    ilimit F1 (weightprof_mod W1)) → 
Π F: func (graph_cat (optionGraph A)) B, 
Π W: weightprof J' (optionGraph A), 
   ilimit F (weightprof_mod W)  ≔ 
begin
assume J' B Hprod A A_isf IH F W; 
 
have lim_F_comp : ilimit (F <∘ (graphMorph_func (optionGraph_graphMorph A))) 
                    ((weightprof_mod W) <<∘ (graphMorph_func (optionGraph_graphMorph A))) 
{ refine (IH (F <∘ (graphMorph_func (optionGraph_graphMorph A))) 
              (subst_cov_weightprof  W (optionGraph_graphMorph A))) 
};

have Prod_F_lim_F_comp : iproduct F (weightprof_mod W) ((sigma_Snd lim_F_comp)₁)
{ refine (Hprod _ F W _ ((sigma_Snd lim_F_comp)₁)) 
};  

apply Struct_sigma
{ refine (iproduct_Func Prod_F_lim_F_comp); 
}
{ refine (_ & _)
  { refine (iproduct_Imply Prod_F_lim_F_comp) 
  }
  { assume I M S  c_F;
    have c_F_side : τ (hom_Set S (Unit_mod M (sigma_Fst lim_F_comp)) Id_func)
    { refine ((sigma_Snd lim_F_comp)₂ _ _ _
      (c_F '∘ (subst_Imply_cov_mod (graphMorph_func (optionGraph_graphMorph A))))) 
    };

    have c_F_iproducing : iproducing F (weightprof_mod W) ((sigma_Snd lim_F_comp)₁)
    { refine (@Struct_iproducing _  _ _ _ _ _ 
          ((sigma_Snd lim_F_comp)₁) _ _ M c_F c_F_side) 
    };
    
    refine (iproduct_Univ Prod_F_lim_F_comp 
              (@Struct_iproducing _ _ _ _ _ _ ((sigma_Snd lim_F_comp)₁) _ _ M c_F c_F_side)) ;
  }
}
end;

symbol lemma_ind_hypothesis_iqualizer_ilimit' : Π (J': category), Π (B: cat), 
(Π [A : graph] [X : graph_Obj A] [Y : graph_Obj A], 
  Π F: func (graph_cat (joinGraph X Y)) B, 
  Π W: weightprof J' (joinGraph X Y), 
  Π L: func (category_cat J') B, 
  Π l: hom L ((Unit_mod Id_func 
      (F <∘ (graphMorph_func (joinGraph_graphMorph X Y)))) ⇐ 
      ((weightprof_mod W) <<∘ (graphMorph_func (joinGraph_graphMorph X Y)))) Id_func, 
  iqualizer F (weightprof_mod W) l) → 
Π (A : graph), isFiniteGraph A → Π [X : graph_Obj A] [Y : graph_Obj A], 
(Π F1: func (graph_cat A) B, 
 Π W1: weightprof J' A, 
    ilimit F1 (weightprof_mod W1)) → 
Π F: func (graph_cat (joinGraph X Y)) B, 
Π W: weightprof J'  (joinGraph X Y), 
   ilimit F (weightprof_mod W)  ≔ 
begin
assume J' B Hequa A A_isf X Y IH F W; 
 
have lim_F_comp : ilimit (F <∘ (graphMorph_func (joinGraph_graphMorph X Y))) ((weightprof_mod W) <<∘ (graphMorph_func (joinGraph_graphMorph X Y))) 
{ refine (IH (F <∘ (graphMorph_func (joinGraph_graphMorph X Y))) (subst_cov_weightprof  W (joinGraph_graphMorph X Y))) };

have Eq_F_lim_F_comp : iqualizer F (weightprof_mod W)  ((sigma_Snd lim_F_comp)₁)
{ refine (Hequa _ _ _ F W _ ((sigma_Snd lim_F_comp)₁)) };  

apply Struct_sigma
{ refine (iqualizer_Func Eq_F_lim_F_comp); }
{ refine (_ & _)
  {  refine (iqualizer_Imply Eq_F_lim_F_comp) }
  { assume I M S c_F;
    have c_F_side : τ (hom_Set S (Unit_mod M (sigma_Fst lim_F_comp)) Id_func)
    { refine ((sigma_Snd lim_F_comp)₂ _ _ _ (c_F '∘ (subst_Imply_cov_mod (graphMorph_func (joinGraph_graphMorph X Y))))) };

    have c_F_iqualizing : iqualizing F (weightprof_mod W)  ((sigma_Snd lim_F_comp)₁)
    { refine (@Struct_iqualizing _  _ _ _ _ _ _ _ ((sigma_Snd lim_F_comp)₁) _ _  M c_F c_F_side) };
    
    refine (iqualizer_Univ Eq_F_lim_F_comp (@Struct_iqualizing _ _ _ _ _ _ _ _ ((sigma_Snd lim_F_comp)₁) _ _ M c_F c_F_side)) ;
  }
}
end;

symbol lemma_data_terminal_iterminal : Π [J' B : category ], 
( terminal  B) →
 iterminal (category_cat J') (category_cat B)   ≔
begin
  assume J' B Hterminal;
  refine Struct_iterminal _ _ 
  { refine category_elim_cov_func _ _
    { assume M;
      refine (category_Obj_obj (terminal_Obj Hterminal));
    }
    { assume M N a; refine DEBUG_ADMIT
    };
  }
  { assume I L0 S;
    refine cat_elim_cov_hom _;
    simplify; assume M;
    // refine (category_Arr_cov_arr' L0 (M ∘>o S) (Obj_func (category_Obj_obj (terminal_Obj Hterminal))) 
    //       (terminal_Univ Hterminal (obj_category_Obj ((M ∘>o S) ∘>o L0))));
    refine (category_Arr_cov_arr0 L0 (M ∘>o S) (category_Obj_obj (terminal_Obj Hterminal)) 
            (terminal_Univ Hterminal (obj_category_Obj ((M ∘>o S) ∘>o L0))));
    // refine category_Arr_cov_arr0 _ _ _ ((terminal_Univ Hterminal) _);
  }
end;

symbol lemma_data_product_iproduct : Π [J' B : category ], 
(Π A: graph, Π L: category_Obj B, 
  Π F: diagram (optionGraph A) B, 
  Π t: cone L (comp_graphMorph_diagram (optionGraph_graphMorph A) F), 
  product F t) →
(Π [A : graph],
   Π F: func (graph_cat (optionGraph A)) (category_cat B), 
  Π W: weightprof J'  (optionGraph A) ,
  Π [L: func (category_cat J') (category_cat B)], 
  Π l: hom L ((Unit_mod Id_func 
       (F <∘ (graphMorph_func (optionGraph_graphMorph A)))) ⇐ 
        ((weightprof_mod W) <<∘ (graphMorph_func (optionGraph_graphMorph A)))) Id_func,
@iproduct (category_cat J') (category_cat B) A F (weightprof_mod W) L l )   ≔
begin
  assume J' B Hprod A F W L l;

  have F_dia : diagram (optionGraph A) B
  { refine @Struct_diagram (optionGraph A) _ (λ I: graph_Obj (optionGraph A), (obj_category_Obj (@graph_elim_cov_func_Obj (optionGraph A) _ F I))) 
      /* l' */ (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (optionGraph A) _ F M1 N1 a1)) ;        
  };

  have l_cone : Π M, cone (obj_category_Obj ((category_Obj_obj M) ∘>o L))
      (comp_graphMorph_diagram (optionGraph_graphMorph A) 
      /* F_dia */ (@Struct_diagram (optionGraph A) _ (λ I : graph_Obj (optionGraph A), (obj_category_Obj (@graph_elim_cov_func_Obj (optionGraph A) _ F I))) 
              (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (optionGraph A) _ F M1 N1 a1))) )
  { refine λ M, Struct_cone (λ N, (λ M N a, arr_category_Arr (weightprof_elim_transf_cov_Arr  _ (Eval_cov_hom_transf  l) M N a)) M N _); 
    refine DEBUG_ADMIT /* weight TEST */
  };
  have l_Hprod : Π M, product /* F_dia */ (@Struct_diagram (optionGraph A) _ (λ I : graph_Obj (optionGraph A), (obj_category_Obj (@graph_elim_cov_func_Obj (optionGraph A) _ F I))) 
  (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (optionGraph A) _ F M1 N1 a1)))
    (l_cone M)
  { refine (λ M, Hprod A (obj_category_Obj ((category_Obj_obj M) ∘>o L))
    /* F_dia */ (@Struct_diagram (optionGraph A) _ (λ I : graph_Obj (optionGraph A), (obj_category_Obj (@graph_elim_cov_func_Obj (optionGraph A) _ F I))) 
        (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (optionGraph A) _ F M1 N1 a1)))
    (l_cone M))
  }; 
  refine Struct_iproduct _ _ _ _
  { refine category_elim_cov_func _ _
    { assume M;
      refine (category_Obj_obj (producing_Obj (product_Producing (l_Hprod M))));
    }
    { assume M N a; refine DEBUG_ADMIT
    };
  }
  { refine category_elim_cov_hom _ ;
  assume M; simplify;
  apply (category_Arr_cov_arr0 _ (category_Obj_obj (producing_Obj (product_Producing (l_Hprod M)))) (category_Obj_obj M ∘>o L) (producing_Arr (product_Producing (l_Hprod M))));
  //category_Arr (producing_Obj (product_Producing (l_Hprod M))) (obj_category_Obj (category_Obj_obj M ∘>o L))
  }
  { refine (Lambda_cov_transf_hom (weightprof_elim_transf _ _ _));
    assume M N _ /* TEST */ ;
    simplify;
    type (category_Arr_cov_arr0 Id_func (category_Obj_obj (producing_Obj (product_Producing (l_Hprod M))))  ((graph_Obj_obj N) ∘>o F) (@cone_Arr (optionGraph A) _ _ _ (producing_Cone (product_Producing (l_Hprod M))) N));
    //category_Arr (producing_Obj (product_Producing (l_Hprod (obj_category_Obj M)))) (diagram_Obj (Struct_diagram (λ I, obj_category_Obj (graph_elim_cov_func_Obj _ F I)) (λ M1 N1 a1, arr_category_Arr (graph_elim_cov_func_Arr _ F a1))) N)
    refine ( (category_Arr_cov_arr0 _ _  _ (@cone_Arr (optionGraph A) _ _ _ (producing_Cone (product_Producing (l_Hprod M))) N))
    '∘a ((Id_func)_'∘> Func_cov_hom F (Obj_func (graph_Obj_obj N))) );
  }
  { assume L0;
    refine category_elim_cov_hom0 _;
    simplify; assume M;
    refine (category_Arr_cov_arr0 _ _ _ _); simplify obj_category_Obj;

    have L0_producing : producing /* F_dia  */(@Struct_diagram (optionGraph A) _ (λ I: graph_Obj (optionGraph A), (obj_category_Obj (@graph_elim_cov_func_Obj (optionGraph A) _ F I))) /* l' */ (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (optionGraph A) _ F M1 N1 a1))) (l_cone M)
    { refine (DEBUG_TAG1 (Struct_producing _ _ _ ))
      { refine ((obj_category_Obj (((category_Obj_obj M) ∘>o iproducing_S L0) ∘>o iproducing_Func L0)))
      }
      { simplify;
        //TODO review this and its computation  or use  ∘o↓  ?
        refine arr_category_Arr (((iproducing_Hom L0) ∘>'_ (_)) ∘a' (Id_cov_arr  (category_Obj_obj M) ));
      }
      { refine (Struct_cone _); assume N; simplify;
        refine (arr_category_Arr (@weightprof_elim_transf_cov_Arr _ _ _ _ _ _ (Eval_cov_hom_transf  (iproducing_Imply L0)) M N _)) ;
        refine DEBUG_ADMIT; /* TEST weight */
      }
    };  proofterm;

    refine (let L0_producing ≔ (Struct_producing (obj_category_Obj ((category_Obj_obj M ∘>o iproducing_S L0) ∘>o iproducing_Func L0)) (arr_category_Arr ((iproducing_Hom L0 ∘>'_ Obj_func (category_Obj_obj M)) ∘a' Id_cov_arr (category_Obj_obj M))) (Struct_cone (λ N, arr_category_Arr (weightprof_elim_transf_cov_Arr (optionGraph A) (Eval_cov_hom_transf (iproducing_Imply L0)) M N DEBUG_ADMIT)))) in 
    (product_Univ  (l_Hprod M) L0_producing));
  };
end; //abort;

/////////////////------------

symbol lemma_data_equalizer_iqualizer : Π [J' B : category ], 
(Π A: graph, Π X: graph_Obj A, Π Y: graph_Obj A, Π L: category_Obj B, 
  Π F: diagram (joinGraph X Y) B, 
  Π t: cone L (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F), 
  equalizer F t) →
(Π [A : graph] [X : graph_Obj A] [Y : graph_Obj A],
   Π F: func (graph_cat (joinGraph X Y)) (category_cat B), 
  Π W: weightprof J'  (joinGraph X Y), //≔ (terminal_weightprof _ _) in 
  Π [L: func (category_cat J') (category_cat B)], 
  Π l: hom L ((Unit_mod Id_func 
       (F <∘ (graphMorph_func (joinGraph_graphMorph X Y)))) ⇐ 
        ((weightprof_mod W) <<∘ (graphMorph_func (joinGraph_graphMorph X Y)))) Id_func,
@iqualizer (category_cat J') (category_cat B) A X Y F (weightprof_mod W) L l )   ≔
begin
  assume J' B Hequa A X Y F W L l;

  have extra_arr : (category_Arr (obj_category_Obj (graph_Obj_obj X ∘>o F)) (obj_category_Obj (graph_Obj_obj Y ∘>o F)))
  { refine (arr_category_Arr (graph_elim_cov_func_Arr _ F (joinGraph_Arr_introNew X Y)));
  };

  have F_dia : diagram (joinGraph X Y) B
  { refine @Struct_diagram (joinGraph X Y) _ (λ I: graph_Obj (joinGraph X Y), (obj_category_Obj (@graph_elim_cov_func_Obj (joinGraph X Y) _ F I))) 
      (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (joinGraph X Y) _ F M1 N1 a1)) ;        
  };

  have l_cone : Π M, cone (obj_category_Obj ((category_Obj_obj M) ∘>o L))
      (comp_graphMorph_diagram (joinGraph_graphMorph X Y) 
      /* F_dia */ (@Struct_diagram (joinGraph X Y) _ (λ I : graph_Obj (joinGraph X Y), (obj_category_Obj (@graph_elim_cov_func_Obj (joinGraph X Y) _ F I))) 
              (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (joinGraph X Y) _ F M1 N1 a1))) )
  { refine λ M, Struct_cone (λ N, /* l' */ (λ M N a, arr_category_Arr (weightprof_elim_transf_cov_Arr _ (Eval_cov_hom_transf  l) M N a)) M N _); 
    refine DEBUG_ADMIT /* weight TEST */
  };

  have l_Hequa : Π M, equalizer /* F_dia */ (@Struct_diagram (joinGraph X Y) _ (λ I : graph_Obj (joinGraph X Y), (obj_category_Obj (@graph_elim_cov_func_Obj (joinGraph X Y) _ F I))) 
  (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (joinGraph X Y) _ F M1 N1 a1)))
    (l_cone M)
  { refine (λ M, Hequa A X Y (obj_category_Obj ((category_Obj_obj M) ∘>o L))
    /* F_dia */ (@Struct_diagram (joinGraph X Y) _ (λ I : graph_Obj (joinGraph X Y), (obj_category_Obj (@graph_elim_cov_func_Obj (joinGraph X Y) _ F I))) 
        (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (joinGraph X Y) _ F M1 N1 a1)))
    (l_cone M))
  }; 

  refine Struct_iqualizer _ _ _ _
  { refine category_elim_cov_func _ _
    { assume M;
      refine (category_Obj_obj (equalizing_Obj (equalizer_Equalizing (l_Hequa M))));
    }
    { assume M N a; refine DEBUG_ADMIT;
    };
  }
  { refine category_elim_cov_hom _ ;
    assume M; simplify;
    refine (category_Arr_cov_arr0 _ (category_Obj_obj (equalizing_Obj (equalizer_Equalizing (l_Hequa M)))) (category_Obj_obj M ∘>o L) (equalizing_Arr (equalizer_Equalizing (l_Hequa M))));
  }
  { refine (Lambda_cov_transf_hom (weightprof_elim_transf _ _ _));
    assume M N _ /* TEST */;
    simplify;
    refine ( (category_Arr_cov_arr0 _ _  _ (@cone_Arr (joinGraph X Y) _ _ _ (equalizing_Cone (equalizer_Equalizing (l_Hequa M))) N))
                   '∘a ((Id_func)_'∘> Func_cov_hom F (Obj_func (graph_Obj_obj N))) );
  }
  { assume L0;
    refine category_elim_cov_hom0 _;
    simplify; assume M;
    refine (category_Arr_cov_arr0 _ _ _ _); simplify obj_category_Obj;

    have L0_equalizing : equalizing /* F_dia  */(Struct_diagram (λ I: graph_Obj (joinGraph X Y), (obj_category_Obj (@graph_elim_cov_func_Obj (joinGraph X Y) _ F I))) (λ M1 N1 a1, arr_category_Arr (@graph_elim_cov_func_Arr (joinGraph X Y) _ F M1 N1 a1))) (l_cone M)
    { refine (DEBUG_TAG1 (Struct_equalizing _ _ _ ))
      { refine ((obj_category_Obj (((category_Obj_obj M) ∘>o iqualizing_S L0) ∘>o iqualizing_Func L0)))
      }
      { simplify;
        //TODO review this and its computation  or use  ∘o↓  ?
        refine arr_category_Arr (((iqualizing_Hom L0) ∘>'_ (_)) ∘a' (Id_cov_arr  (category_Obj_obj M) ));
      }
      { refine (Struct_cone _); assume N; simplify;
        refine (arr_category_Arr (@weightprof_elim_transf_cov_Arr _ (joinGraph X Y) _ _ _ _ (Eval_cov_hom_transf  (iqualizing_Imply L0)) M N _)) ;
        refine DEBUG_ADMIT; /* TEST weight */
      }
    }; // proofterm;

    refine (let L0_equalizing ≔ (Struct_equalizing (obj_category_Obj ((category_Obj_obj M ∘>o iqualizing_S L0) ∘>o iqualizing_Func L0)) (arr_category_Arr ((iqualizing_Hom L0 ∘>'_ Obj_func (category_Obj_obj M)) ∘a' Id_cov_arr (category_Obj_obj M))) (Struct_cone (λ N, arr_category_Arr (weightprof_elim_transf_cov_Arr (joinGraph X Y) (Eval_cov_hom_transf (iqualizing_Imply L0)) M N DEBUG_ADMIT)))) in 
    (equalizer_Univ  (l_Hequa M) L0_equalizing));
  };
end;

///////-------

symbol construct_inductively_limit : Π [J': category], Π [B: cat], 
(iterminal (category_cat J') B) → 
(Π A: graph, 
Π F: func (graph_cat (optionGraph A)) B, 
Π W: weightprof J' (optionGraph A), 
Π L: func (category_cat J') B, 
Π l: hom L ((Unit_mod Id_func (F <∘ graphMorph_func (optionGraph_graphMorph A))) ⇐ 
  ((weightprof_mod W) <<∘ graphMorph_func (optionGraph_graphMorph A))) Id_func, iproduct F (weightprof_mod W) l) → 
(Π A: graph, Π X: graph_Obj A, Π Y: graph_Obj A, 
Π F: func (graph_cat (joinGraph X Y)) B, 
Π W: weightprof J' (joinGraph X Y), 
Π L: func (category_cat J') B, 
Π l: hom L ((Unit_mod Id_func (F <∘ graphMorph_func (joinGraph_graphMorph X Y))) ⇐ 
  ((weightprof_mod W) <<∘ graphMorph_func (joinGraph_graphMorph X Y))) Id_func, iqualizer F (weightprof_mod W) l) → 
Π A: graph, isFiniteGraph A → 
τ `Π_ F: func (graph_cat A) B, 
`Π_ W: weightprof J' A, 
ilimit_Set F (weightprof_mod W) ≔ 
begin
assume J' B Hterminal Hprod Hequa;
refine (rect_isFiniteGraph _ _ _ _ )
{ refine (@lemma_ind_base_iterminal_ilimit' J' B Hterminal)
}
{ refine (@lemma_ind_hypothesis_iproduct_ilimit' J' B Hprod)
}
{ refine (@lemma_ind_hypothesis_iqualizer_ilimit' J' B Hequa)
};
end;

// //MEMO: this possible general alternative is provable, but it cannot be simply linked to the concrete data lemmas
// symbol construct_inductively_limit : Π [J': cat], Π [B: cat], 
// (iterminal J' B) → 
// (Π A: graph, 
// Π F: func (graph_cat (optionGraph A)) B, 
// Π W: mod J' (graph_cat (optionGraph A)), 
// Π L: func J' B, 
// Π l: hom L ((Unit_mod Id_func (F <∘ graphMorph_func (optionGraph_graphMorph A))) ⇐ 
//   (W <<∘ graphMorph_func (optionGraph_graphMorph A))) Id_func, iproduct F W l) → 
// (Π A: graph, Π X: graph_Obj A, Π Y: graph_Obj A, 
// Π F: func (graph_cat (joinGraph X Y)) B, 
// Π W: mod J' (graph_cat (joinGraph X Y)), 
// Π L: func J' B, 
// Π l: hom L ((Unit_mod Id_func (F <∘ graphMorph_func (joinGraph_graphMorph X Y))) ⇐ 
//   (W <<∘ graphMorph_func (joinGraph_graphMorph X Y))) Id_func, iqualizer F W l) → 
// Π A: graph, isFiniteGraph A → 
// τ `Π_ F: func (graph_cat A) B, 
// `Π_ W: mod J' (graph_cat A), 
// ilimit_Set F W ≔ 
// begin
// assume J' B Hterminal Hprod Hequa;
// refine (rect_isFiniteGraph _ _ _ _ )
// { refine (@lemma_ind_base_iterminal_ilimit J' B Hterminal)
// }
// { refine (@lemma_ind_hypothesis_iproduct_ilimit J' B Hprod)
// }
// { refine (@lemma_ind_hypothesis_iqualizer_ilimit J' B Hequa)
// };
// end;

symbol construct_inductively_limit_instance : Π [J' B : category ], 
(terminal B) →
(Π A: graph, Π L: category_Obj B, 
  Π F: diagram (optionGraph A) B, 
  Π t: cone L (comp_graphMorph_diagram (optionGraph_graphMorph A) F), 
  product F t) →
(Π A: graph, Π X: graph_Obj A, Π Y: graph_Obj A, Π L: category_Obj B, 
  Π F: diagram (joinGraph X Y) B, 
  Π t: cone L (comp_graphMorph_diagram (joinGraph_graphMorph X Y) F), 
  equalizer F t) →
Π A: graph, isFiniteGraph A → 
τ `Π_ F: func (graph_cat A) (category_cat B), 
`Π_ W: weightprof J' A, 
ilimit_Set F (weightprof_mod W) ≔ 
begin 
assume J' B Hterminal Hprod Hequa;
refine @construct_inductively_limit J' (category_cat B)
(@lemma_data_terminal_iterminal J' B Hterminal)
(@lemma_data_product_iproduct J' B Hprod)
 (@lemma_data_equalizer_iqualizer J' B Hequa);
end;

symbol construct_inductively_limit_instance_liset (A: graph) (A_isf : isFiniteGraph A) (F: diagram A liset) ≔ @construct_inductively_limit_instance (terminal_category) _ @liset_terminal @liset_product @liset_equalizer A A_isf (diagram_func F) (terminal_weightprof terminal_category A);

//forgot this rule, had to reverse engineer from the stuck computation to discover it
rule arr_category_Arr ($a '∘a ( (_) _'∘> Func_cov_hom $F $Z)) ↪ arr_category_Arr $a;

// limit cone apex object
compute obj_category_Obj ((category_Obj_obj One) ∘>o (sigma_Fst (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram)));

//Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 13)) (Base_natUniv 21)) (Base_natUniv 31) ⸬ (Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 13)) (Base_natUniv 22)) (Base_natUniv 31) ⸬ (Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 12)) (Base_natUniv 21)) (Base_natUniv 31) ⸬ (Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 12)) (Base_natUniv 22)) (Base_natUniv 31) ⸬ (Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 11)) (Base_natUniv 21)) (Base_natUniv 31) ⸬ (Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 11)) (Base_natUniv 22)) (Base_natUniv 31) ⸬ □)))))

//EARLIER OUTPUT reverse engineered
/* category_Obj_obj (if (natUniv_eq (Base_natUniv 1) 
(arr_category_Arr ( category_Arr_cov_arr 
(category_Obj_obj (Pair_natUniv (Base_natUniv 2) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 2) (Base_natUniv 1) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 1) ⸬ □)))))
(category_Obj_obj (Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □)))
 natUniv_snd 
 '∘a (Id_func _'∘> Func_cov_hom 
 (diagram_func (Struct_diagram (λ _, Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □)) (λ _ _ a, rect_empty a))) 
 (Obj_func (graph_Obj_obj (Struct_sub (Base_natUniv 2) top)))))
 (Pair_natUniv (Base_natUniv 2) (Base_natUniv 2)))) 
(Pair_natUniv (Base_natUniv 2) (Base_natUniv 2) ⸬ if (natUniv_eq (Base_natUniv 1) (arr_category_Arr (category_Arr_cov_arr (category_Obj_obj (Pair_natUniv (Base_natUniv 2) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 2) (Base_natUniv 1) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 1) ⸬ □))))) (category_Obj_obj (Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □))) natUniv_snd '∘a (Id_func _'∘> Func_cov_hom (diagram_func (Struct_diagram (λ _, Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □)) (λ _ _ a, rect_empty a))) (Obj_func (graph_Obj_obj (Struct_sub (Base_natUniv 2) top))))) (Pair_natUniv (Base_natUniv 2) (Base_natUniv 1)))) (Pair_natUniv (Base_natUniv 2) (Base_natUniv 1) ⸬ if (natUniv_eq (Base_natUniv 1) (arr_category_Arr (category_Arr_cov_arr (category_Obj_obj (Pair_natUniv (Base_natUniv 2) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 2) (Base_natUniv 1) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 2) ⸬ (Pair_natUniv (Base_natUniv 1) (Base_natUniv 1) ⸬ □))))) (category_Obj_obj (Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □))) natUniv_snd '∘a (Id_func _'∘> Func_cov_hom (diagram_func (Struct_diagram (λ _, Base_natUniv 2 ⸬ (Base_natUniv 1 ⸬ □)) (λ _ _ a, rect_empty a))) ...
 */

//limit cone sides arrows
compute arr_category_Arr ((Eval_cov_hom_transf ((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₁ ))  ∘a' ( (@weightprof_Arr_arr _ _ _ (category_Obj_obj One) (graph_Obj_obj None) One))  );
// λ x, natUniv_snd x
compute arr_category_Arr ((Eval_cov_hom_transf ((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₁ ))  ∘a' ( (@weightprof_Arr_arr _ _ _ (category_Obj_obj One) (graph_Obj_obj (Some (Some None))) One))  );
// λ x, natUniv_snd (natUniv_fst (natUniv_fst x))

assert ⊢ arr_category_Arr ((Eval_cov_hom_transf ((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₁ ))  ∘a' ( (@weightprof_Arr_arr _ _ _ (category_Obj_obj One) (graph_Obj_obj (Some (Some None))) One))  )
≡ λ x, natUniv_snd (natUniv_fst (natUniv_fst x)) ;

//limit cone universality
type ((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₂ );

symbol example_cone : hom (functor_func (category_Obj_functor (terminal_Obj liset_terminal))) ((Unit_mod Id_func (diagram_func example_diagram)) ⇐ (weightprof_mod (terminal_weightprof terminal_category example_graph))) Id_func ≔
begin
  refine (Lambda_cov_transf_hom _);
  refine (weightprof_elim_transf _ _ _);
  assume M N  _ /* weight TEST */ ; 
  //arr (category_Obj_obj (producing_Obj (product_Producing (l_Hprod M)))) (Unit_mod Id_func F) (graph_Obj_obj N)
  
  //arr (category_Obj_obj (Base_natUniv 0 ⸬ □)) (Unit_mod Id_func (diagram_func example_diagram)) (graph_Obj_obj N)
  refine ( _ '∘a ((Id_func)_'∘> Func_cov_hom (diagram_func example_diagram) (Obj_func (graph_Obj_obj N))) )
  { refine Terminal_obj
  }
  { refine (category_Arr_cov_arr0 _ _ _ _ );
    simplify;
    refine (@rect_option _ (λ _, natUniv_Set →_ natUniv_Set  ) _ _ N)
    {
      refine rect_option _ _ 
      { 
        refine rect_option _ _  
        { 
          refine rect_empty
        }
        {
          refine (λ _, (Base_natUniv 12) )
        }
      }
      {
        refine (λ _, (Base_natUniv 22) )
      }
    }
    {
      refine (λ _, (Base_natUniv 31) )
    }
  };
end;

type arr_category_Arr (((((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₂ ) _ _ _ example_cone) ∘>'_ ( _ ) ) ∘a' (Id_cov_arr (category_Obj_obj One))) liset_terminal_natUniv;

//first attempt, reverse engineer it
compute arr_category_Arr (((((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₂ ) _ _ _ example_cone) ∘>'_ ( _ ) ) ∘a' (Id_cov_arr (category_Obj_obj One))) liset_terminal_natUniv;

//EARLIER OUTPUT reverse engineered
/* type Pair_natUniv (Pair_natUniv (Pair_natUniv _
 (arr_category_Arr 
   (Eval_cov_hom_transf 
      (  ( (Lambda_cov_transf_hom 
                (weightprof_elim_transf (functor_func _) Id_func 
                        (λ _ N _, category_Arr_cov_arr0 Id_func (category_Obj_obj _) (category_Obj_obj _) _ 
                                        '∘a (Id_func _'∘> Func_cov_hom (diagram_func _) (Obj_func (graph_Obj_obj N))))) 
           '∘ Lambda_cov_transf (Eval_cov_transf (Id_transf _) <<∘1 graphMorph_func _) ) 
          '∘ Lambda_cov_transf (Eval_cov_transf (Id_transf _) <<∘1 graphMorph_func _)) 
       '∘ Lambda_cov_transf (Eval_cov_transf (Id_transf _) <<∘1 graphMorph_func _) ) 
   ∘a' weightprof_Arr_arr (category_Obj_obj One) (graph_Obj_obj None) DEBUG_ADMIT) 
 _ )) 
  (arr_category_Arr _ _)) 
  (arr_category_Arr _ _) */

type λ [A  X A'  : cat] [Q : mod A X] 
[O : mod A' X]  [F : func A A'] ,
λ (t : transf Q  F O                     Id_func), λ [Y] (K : func Y X),
(Lambda_cov_transf_hom t) '∘  (Lambda_cov_transf ((Eval_cov_transf (Id_transf _)) <<∘1 K)) 
 = (Lambda_cov_transf_hom (t <<∘1 K));

rule (Lambda_cov_transf_hom $t) '∘  (Lambda_cov_transf ((Eval_cov_transf (Id_transf _)) <<∘1 $K)) 
↪ (Lambda_cov_transf_hom ($t <<∘1 $K));

type λ [A' : category] (B' : graph) [R' : weightprof A' B'] [ A : cat] [F : func (category_cat A') A]  [R : mod A (graph_cat B')] 
(t_arr : Π  (M : category_Obj A') (N : graph_Obj B') (r : weightprof_Arr R' M N),
arr ( (category_Obj_obj M) ∘>o F) R ((graph_Obj_obj N))) [D : graph] (K : graphMorph D B'),
λ (t_K_arr : Π  (M : category_Obj A') (N : graph_Obj D) (r : weightprof_Arr (subst_cov_weightprof R' K) M N),
arr ( (category_Obj_obj M) ∘>o F) (R <<∘ (graphMorph_func K)) ((graph_Obj_obj N))), 
(weightprof_elim_transf F Id_func t_arr) <<∘1 graphMorph_func K
= (@weightprof_elim_transf _ _ ((subst_cov_weightprof R' K)) _ _ F _ Id_func 
    (λ M N r, (((Arr_hom (Obj_func ( (category_Obj_obj M) ∘>o F)) _ (t_arr M (graphMorph_Obj K N) r )) ∘>'_ (_) ) ∘a' (Id_con_arr0 (graphMorph_func K) (graph_Obj_obj N)))) )  ;
symbol tmp [A' : category] (B' : graph) [R' : weightprof A' B'] [ A : cat] [F : func (category_cat A') A]  [R : mod A (graph_cat B')] 
(t_arr : Π  (M : category_Obj A') (N : graph_Obj B') (r : weightprof_Arr R' M N),
arr ( (category_Obj_obj M) ∘>o F) R ((graph_Obj_obj N)))
 [D : graph] (K : graphMorph D B') :
 Π  (M : category_Obj A') (N : graph_Obj D) (r : weightprof_Arr (subst_cov_weightprof R' K) M N),
arr ( (category_Obj_obj M) ∘>o F) (R <<∘ (graphMorph_func K)) ((graph_Obj_obj N)) ≔ 
begin
 assume A' B' R' A F R t_arr D K M N r;
  type (t_arr M (graphMorph_Obj K N) r );
  refine (((Arr_hom (Obj_func ( (category_Obj_obj M) ∘>o F)) _ (t_arr M (graphMorph_Obj K N) r )) ∘>'_ (_) ) ∘a' (Id_con_arr0 (graphMorph_func K) (graph_Obj_obj N)));
abort;
rule (@weightprof_elim_transf $A' $B' $R' $A _ $F $R Id_func $t_arr) <<∘1 @graphMorph_func _ $B' $K
↪ (@weightprof_elim_transf _ _ ((subst_cov_weightprof $R' $K)) _ _ $F _ Id_func 
(λ M N r, (((Arr_hom (Obj_func ( (category_Obj_obj M) ∘>o $F)) _ ($t_arr M (graphMorph_Obj $K N) r )) ∘>'_ (_) ) ∘a' (Id_con_arr0 (graphMorph_func $K) (graph_Obj_obj N)))) ) ;

//TODO review this rule, is there simpler rules? 
rule arr_category_Arr ( ( (@Arr_hom _ _ (Unit_mod _ _) _ (Obj_func _) $r) ∘>'_ (_)) ∘a' (Id_con_arr0 _ $F) ) ↪  arr_category_Arr $r;

//second attempt, third attempt  YES
compute arr_category_Arr (((((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₂ ) _ _ _ example_cone) ∘>'_ ( _ ) ) ∘a' (Id_cov_arr (category_Obj_obj One))) liset_terminal_natUniv;

assert ⊢ arr_category_Arr (((((sigma_Snd (construct_inductively_limit_instance_liset _ example_graph_isf example_diagram))₂ ) _ _ _ example_cone) ∘>'_ ( _ ) ) ∘a' (Id_cov_arr (category_Obj_obj One))) liset_terminal_natUniv
≡ Pair_natUniv (Pair_natUniv (Pair_natUniv (Base_natUniv 0) (Base_natUniv 12)) (Base_natUniv 22)) (Base_natUniv 31);

//EARLIER SECOND OUTPUT reverse engineered
/*  arr_category_Arr ( (Arr_hom _ _ ( (Arr_hom _ _ ( 
   (Arr_hom _ _  (category_Arr_cov_arr0  _ ) ∘>'_ graphMorph_func _) ∘a' Id_con_arr0 _ _)  ∘>'_ graphMorph_func _ )   ∘a' Id_con_arr0 (graphMorph_func _) (graph_Obj_obj (Some None))) ∘>'_ graphMorph_func _) ∘a' Id_con_arr0 (graphMorph_func _) (graph_Obj_obj None)) 
 */


 /* Voila! */
