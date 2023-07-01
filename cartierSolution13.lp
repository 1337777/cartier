/* A new implementation of dependent types via Dosen's substructural categorial programming: example of the Yoneda lemma for fibrations

This closes the open problem of implementing a dependent-types computer for category theory, where types are categories and dependent types are fibrations of categories. The basis for this implementation are the ideas and techniques from Kosta Dosen's book « Cut-elimination in categories » (1999), which essentially is about the substructural logic of category theory, in particular about how some good substructural formulation of the Yoneda lemma allows for computation and automatic-decidability of categorial equations.

The core of dependent types/fibrations in category theory is the Comma/slice construction and the corresponding Yoneda lemma for fibrations (https://stacks.math.columbia.edu/tag/0GWH), thereby its implementation essentially closes this open problem also investigated by Cisinski's directed types or Garner's 2-dimensional types. Even what constitutes a solution is subtle and is often misunderstood/misframed, but at the end of the day, the thesis here is that Dosen's substructural techniques cannot be bypassed.

In summary, this text implements an (outer) cut-elimination in the double category of fibred profunctors with (inner) cut-eliminated adjunctions. The outer cut-elimination essentially is a new functorial lambda calculus via dinaturality, without need for multicategories because (outer) contexts are expressed via dependent types.  This text also implements Sigma-categories/types and categories-of-functors and more generally Pi-categories-of-functors, but a complete better formulation using spans or polynomial functors will be investigated. This text also implements a dualizing Op operations, and it can computationally-prove that left-adjoint functors preserve profunctor-weighted colimits from the proof that right-adjoint functors preserve profunctor-weighted limits. This text also implements a grammatical (univalent) universe and the univeral fibration classifying fibrations, together with the dual universal opfibration. Finally, there is an experimental implementation of covering (co)sieves towards grammatical sheaf cohomology and a description of algebraic geometry’s schemes in their formulation as locally affine ringed sites (structured topos), instead of via their formulation as underlying topological space...

https://github.com/1337777/cartier/blob/master/cartierSolution13.lp */

constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
builtin "T" ≔ τ;

constant symbol Prop : TYPE;
injective symbol π : Prop → TYPE;
builtin "Prop" ≔ Prop; builtin "P" ≔ π;

constant symbol = [a] : τ a → τ a → Prop; notation = infix 10;
constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x); 
builtin "eq" ≔ = ; builtin "refl"  ≔ eq_refl; builtin "eqind" ≔ ind_eq;
 
 /* (A) INTERFACE ========================== */

 constant symbol cat : TYPE ;
 
 constant symbol func : Π (A B : cat), TYPE ;
 
 constant symbol mod : Π (A B : cat), TYPE ;

 constant symbol hom_c : Π [I A B : cat], func I A → mod A B → func I B → Set ;
 injective symbol hom [I A B : cat] (F : func I A) (R : mod A B) (G : func I B): TYPE 
  ≔ τ (@hom_c I A B F R G );
 
 //TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR DEPENDENT MORPHISM OF FIBRATIONS
 // AND FOR COMPOSIITON OF SPANS USE ALGEBRAIC PULLBACKS NOT UNIVERSAL VERSION
 constant symbol transf_Set: Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → Set  ;
 injective symbol transf [A' B' A B: cat] (R' : mod A' B') (F : func A' A) (R : mod A B) (G : func B' B) : TYPE  
  ≔ τ (@transf_Set A' B' A B R' F R G);
 
 constant symbol adj : Π [R L : cat], func R L → func L R → TYPE  ;
 
 constant symbol limit_cov : Π [B J0 J J' : cat] (K : func J J0) (F : func J0 B) (W : mod J' J) (F_⇐_W : func J' B), TYPE  ;
 
 constant symbol limit_con: Π [B J0 J J' : cat] (K : func J J0) (F : func J0 B) (W : mod J J') (W_⇒_F : func J' B), TYPE  ;
 
 constant symbol catd: Π (X : cat), TYPE ; 
 constant symbol isFibration_con: Π [X : cat] (XX : catd X), TYPE; 
 constant symbol isFibration_cov: Π [X : cat] (XX : catd X), TYPE; 

 constant symbol funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE ;
 
//TODO: erase, instead declare the Total_func $FF $u as isFuncEquiv
 constant symbol isEquiv : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → TYPE ;
 
 constant symbol modd : Π [X Y : cat], catd X → mod X Y → catd Y → TYPE ;

 constant symbol homd_Set : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
Π [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), Set ; 
injective symbol homd [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] (r : hom F R G) 
 [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B) : TYPE
≔ τ (@homd_Set X Y I F R G r A B II FF RR GG); 

 constant symbol transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
 transf R xx' R' yy' → modd A R B → funcd A xx' A' → modd A' R' B' → funcd B yy' B' → TYPE  ;
   
 constant symbol Id_func : Π [A : cat], func A A;
 constant symbol Triv_catd : Π (A : cat), catd A;
 
 constant symbol moddu : Π [I : cat], catd I → catd I → TYPE ;
 
 constant symbol homdu: Π [I: cat] [A : catd I] [B : catd I] [II : catd I]
(FF : funcd II Id_func A) (RR : moddu A B) (GG : funcd II Id_func B), TYPE ;
 
 constant symbol transfduu: Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I], 
 moddu A B → funcd A Id_func A' → moddu A' B' → funcd B Id_func B' → TYPE ; 

 ///experimental grammatical topology covering (co)sieves, for sheaf cohomology
 constant symbol coveringu : Π [I : cat] [A : catd I] [B : catd I]
 (RR : moddu A B), funcd (Triv_catd I) Id_func B → TYPE ;
 
 constant symbol covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [y : func I Y], funcd (Triv_catd I) y B → TYPE  ;
 
 
 // reduction-conversion relation
 constant symbol ==> : Π [I A B: cat] [F : func I A] [T : mod A B] [G :func I B],
 hom F T G → hom F T G → TYPE;
 notation ==> infix 20;

 constant symbol ==>> : Π [A' B' A B: cat] [S : mod A' B'] [F : func A' A] [T : mod A B] [G :func B' B],
 transf S F T G → transf S F T G → TYPE;
 notation ==>> infix 20;
 
 constant symbol ==>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G] 
 [A : catd X] [B : catd Y] [II : catd I] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
 homd r FF RR GG → homd r FF RR GG → TYPE;
notation ==>d infix 20;


/* (B) cat ========================== */

injective symbol Op_cat : cat → cat;

symbol Pullback_cat : Π [U X Y : cat] (F : func X U) (G : func Y U), cat;

constant symbol Terminal_cat : cat;
//not as datatype; and both pullback and product required...
symbol Product_cat : Π (U : cat) (A : cat), cat; 

constant symbol Sigma_cat : Π [X : cat], catd X → cat;
constant symbol Pi_cat : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), cat;


rule Op_cat (Op_cat $A) ↪ $A
with Op_cat (Terminal_cat) ↪ Terminal_cat ;

rule Product_cat $A Terminal_cat ↪  $A
with Product_cat Terminal_cat $A  ↪  $A
with Product_cat (Product_cat $A $B ) $C  ↪  Product_cat $A (Product_cat $B $C ) ;

/* (C) func ========================== */


//Subst_func
symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix right 90;
symbol <∘ [A B C: cat] : func B C → func A B → func A C ≔ λ G F, F ∘> G;
notation <∘ infix left 90;

rule ($F ∘> $G) ∘> $H ↪ $F ∘> ($G ∘> $H)
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

injective symbol Op_func : Π [A B: cat], func A B → func (Op_cat A) (Op_cat B);

rule Op_func (Op_func $F) ↪ $F
with Op_func Id_func ↪ Id_func
with Op_func ($F ∘> $G) ↪  ((Op_func $F) ∘> (Op_func $G));

symbol Pullback_fst_func : Π [U X Y : cat] (F : func X U) (G : func Y U), func (Pullback_cat F G) X;
symbol Pullback_snd_func : Π [U X Y : cat] (F : func X U) (G : func Y U), func (Pullback_cat F G) Y;

constant symbol Terminal_func :  Π (A : cat), func A Terminal_cat;

constant symbol Product_intro_func : Π [T X I : cat] (F : func I T) (G : func I X),
  func I (Product_cat T X);
constant symbol Product_fst_func : Π [T : cat] (X : cat) [T' : cat],
func T T' → func (Product_cat T X) T' ; 
constant symbol Product_snd_func : Π (T : cat) [X X': cat],
func X X' → func (Product_cat T X) X' ; 


rule (Product_fst_func $T $F) ∘> $H ↪ (Product_fst_func $T ($F ∘> $H))
with (Product_snd_func $T $F) ∘> $H ↪ (Product_snd_func $T ($F ∘> $H))
with $H ∘> (Product_intro_func $F $G) ↪ (Product_intro_func ($H ∘> $F) ($H ∘> $G));

rule (@Product_intro_func $T $X $I $F $G) ∘> (@Product_fst_func $T $X _ $H) ↪ $F ∘> $H 
with (@Product_intro_func $T $X $I $F $G) ∘> (@Product_snd_func $T $X _ $H) ↪ $G ∘> $H ;
//todo add extensionality? requires definable func symbols
 
//TODO: REVIEW THIS, NOT USED? ?ok semantic rule?
rule (Pullback_fst_func $F $G) ∘> $F ↪ (Pullback_snd_func $F $G) ∘> $G ;
symbol Pullback_func  [U X Y : cat] (F : func X U) (G : func Y U):
  func (Pullback_cat F G) U ≔ (Pullback_snd_func F G) ∘> G;


// this reversal of rewrite direction and symmetric versions of rewrites are required later at Total_func of @∘>d
// this rewrite direction will use associativity of ∘>
rule Pullback_cat (Pullback_snd_func $F $G) $H  ↪ Pullback_cat $F ($H ∘> $G)
with Pullback_cat $H (Pullback_fst_func $F $G) ↪  Pullback_cat ($H ∘> $F) $G ;
//symmetry
rule Pullback_cat $H (Pullback_snd_func $F $G)   ↪ Pullback_cat $F ($H ∘> $G)
with Pullback_cat (Pullback_fst_func $F $G) $H ↪  Pullback_cat ($H ∘> $F) $G ;

//TODO: REVIEW THIS associativity to right ?  NOT USED? 
// rule Pullback_cat (Pullback_snd_func $F $G) $H ↪ Pullback_cat $H (Pullback_snd_func $F $G)
//  with Pullback_cat $H (Pullback_fst_func $F $G)  ↪ Pullback_cat (Pullback_fst_func $F $G) $H ;

//reverse direction?
rule (Pullback_fst_func (Pullback_snd_func $F $G) $H) ∘> (Pullback_fst_func $F $G) ↪ Pullback_fst_func $F ($H ∘> $G) ;
rule (Pullback_snd_func $H (Pullback_fst_func $F $G)) ∘> (Pullback_snd_func $F $G) ↪ Pullback_snd_func ($H ∘> $F) $G;

rule @Pullback_cat $U $X $Y $F Id_func ↪ $X
with @Pullback_cat $U $X $Y Id_func $G ↪ $Y;
rule Pullback_fst_func $F Id_func ↪ Id_func;
rule Pullback_snd_func Id_func $G ↪ Id_func;

rule Pullback_fst_func ($H ∘> $F) $G ↪ (Pullback_fst_func $H (Pullback_fst_func $F $G));
rule Pullback_snd_func $F ($H ∘> $G) ↪ (Pullback_snd_func (Pullback_snd_func $F $G) $H);

rule Pullback_fst_func Id_func $F ↪ $F;
rule Pullback_snd_func $G Id_func ↪ $G;

//get only algebraic functor instead of universality
symbol Pullback_functor_func [U X Y : cat] (F : func X U) (G : func Y U) [Y'] (G' : func Y' Y)
 : func (Pullback_cat F (G' ∘> G)) (Pullback_cat F G)
   ≔  (Pullback_fst_func (Pullback_snd_func F G) G') ;

// naturality/functoriality is automatically derivable by computation
type λ F G H G', Pullback_functor_func F G (H ∘> G');  
//func (Pullback_cat F ((H ∘> G') ∘> G)) (Pullback_cat F G)
type λ F G H G', Pullback_functor_func F (G' ∘> G) H ∘> Pullback_functor_func F G G'; 
//func (Pullback_cat F (H ∘> (G' ∘> G))) (Pullback_cat F G)
assert  F G H G' ⊢ Pullback_functor_func F G (H ∘> G') ≡ 
        Pullback_functor_func F (G' ∘> G) H ∘> Pullback_functor_func F G G';
 
 rule Op_func (Terminal_func $A) ↪ (Terminal_func (Op_cat $A));
 
rule (@∘> $A $B $C $F (Terminal_func $B)) ↪ (Terminal_func $A) ; 

/* (D) mod ========================== */

injective symbol Op_mod : Π [A B : cat], mod A B → mod (Op_cat B) (Op_cat A); //Tensor_mod;
 
constant symbol Unit_mod : Π [X A B : cat], func A X → func B X → mod A B;
 
 //TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR PULLBACK-PRODUCT OF FIBRATIONS
 constant symbol ⊗ : Π [A B X : cat], mod A B → mod B X → mod A X; //Tensor_mod;
 notation ⊗ infix left 70;
 
 constant symbol Imply_cov_mod : Π [A B C X : cat], mod A B → func C B → mod X C → mod A X;
 
 constant symbol Imply_con_mod : Π [A B C X : cat], mod C X → func C A → mod A B → mod X B;
 
 constant symbol Terminal_mod : Π (A B : cat), mod A B;

 rule Op_mod (Op_mod $A) ↪ $A
with Op_mod (Unit_mod $F $G) ↪   (Unit_mod (Op_func $G) (Op_func $F)) 
with Op_mod ( $R ⊗ $S ) ↪   (Op_mod $S) ⊗ (Op_mod $R)  
 with Op_mod ( Imply_cov_mod $R  $F $S ) ↪   Imply_con_mod (Op_mod $S) (Op_func $F) (Op_mod $R) 
 with Op_mod ( Imply_con_mod $R  $F $S ) ↪   Imply_cov_mod (Op_mod $S) (Op_func $F) (Op_mod $R)   ;

 //Subst_cov_mod
 symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;
 //Subst_con_mod
 symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
 notation <<∘ infix left 80; notation ∘>> infix right 80;
 
 rule  (Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K) 
 with ($R ⊗ $S) <<∘ $G ↪ $R ⊗ ($S <<∘ $G)
 with (Imply_cov_mod $R $H $S) <<∘ $G ↪ Imply_cov_mod $R $H ($G ∘>> $S)
 with (Imply_con_mod $R $H $S) <<∘ $G ↪ Imply_con_mod $R $H ($S <<∘ $G);
 
 rule  $K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G 
 with  $G ∘>> ($R ⊗ $S) ↪ ($G ∘>> $R) ⊗ $S
 with $G ∘>> (Imply_con_mod $R $H $S) ↪ Imply_con_mod ($R <<∘ $G) $H $S
 with $G ∘>> (Imply_cov_mod $R $H $S) ↪ Imply_cov_mod ($G ∘>> $R) $H $S;
 
 rule $R <<∘ Id_func ↪ $R 
// with $R <<∘ ($K ∘> $H  ) ↪ ($R <<∘ $H) <<∘ $K; 
  with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K); 
 
 rule Id_func ∘>> $R ↪ $R 
// with ($K ∘> $H) ∘>> $R  ↪  $K ∘>> ($H ∘>> $R); 
 with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R; 
 
 rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));

rule Op_mod ($F ∘>> $R)  ↪ ((Op_mod $R) <<∘ (Op_func $F))
with Op_mod ($R <<∘ $G)  ↪ ((Op_func $G) ∘>> (Op_mod $R));

 
 
/* (E) hom ========================== */

injective symbol Op_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] (r : hom F R G), hom (Op_func G) (Op_mod R) (Op_func F); 

constant symbol Id_hom : Π [A B : cat] (F : func B A),
hom F (Unit_mod Id_func Id_func ) F;

symbol Func_con_hom'' : Π [A B A' : cat] (Z : func A A') (F : func B A) ,
 hom F (Unit_mod Z Id_func) (Z <∘ F);
symbol Func_cov_hom'' : Π [A B A' : cat] (Z : func A A') (F : func B A) ,
 hom (F ∘> Z) (Unit_mod Id_func Z) F;

 //TODO: replace with correct accumulation version Func_cov_hom'' above, 
 // seems important to accumulate, especialy when the tests become actual rewrite rules
 constant symbol Func_con_hom : Π [A B : cat] (F : func B A),
 hom Id_func (Unit_mod F Id_func ) F;
 constant symbol Func_cov_hom : Π [A B : cat] (F : func B A),
 hom F (Unit_mod Id_func F) Id_func;
 

 rule Op_hom (Op_hom $A) ↪ $A
 with Op_hom (Id_hom $F) ↪ (Id_hom (Op_func $F))
 with Op_hom (Func_con_hom'' $Z $F) ↪ Func_cov_hom'' (Op_func $Z) (Op_func $F)
 with Op_hom (Func_cov_hom'' $Z $F) ↪ Func_con_hom'' (Op_func $Z) (Op_func $F);

 rule Func_con_hom'' Id_func $F ↪ (Id_hom $F)
 with Func_cov_hom'' Id_func $F ↪ (Id_hom $F);

 //todo reduce Terminal_mod Terminal_cat Terminal_cat to Unit_mod ?
 constant symbol Terminal_hom : Π [A B I : cat] (F : func I A) (G : func I B),  hom F (Terminal_mod A B) G;
 
 constant symbol Tensor_hom_hom  : Π [A  X I : cat] [P : mod A I] [Q : mod I X]
 [F : func I A] [G : func I X],
 hom F P Id_func → hom Id_func Q G → hom F ((⊗) P  Q) G;
 
 rule (Op_hom (Tensor_hom_hom $p $q)) ↪ Tensor_hom_hom (Op_hom $q) (Op_hom $p); 

 constant symbol Lambda_cov_transf_hom : Π [A  X A' X' : cat] [Q : mod A X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf Q  F O                     L  →
 hom                       F (Imply_cov_mod O L Q) Id_func;
 
  //Comp_func_hom
 symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
 [G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
 notation ∘↓ infix left 120;
 
 rule $r ∘↓ Id_func ↪ $r
 //reverse direction?
 //with $r ∘↓ ($H <∘ $K) ↪ ($r ∘↓ $H) ∘↓ $K
 //with $r ∘↓ ($K ∘> $H  ) ↪ ($r ∘↓ $H) ∘↓ $K
 with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($K ∘> $H  )
 with (Id_hom $F) ∘↓ $H  ↪ Id_hom ($F <∘ $H)
 with (Func_con_hom'' $Z $F) ∘↓ $H  ↪ Func_con_hom'' $Z ($F <∘ $H)
 with (Func_cov_hom'' $Z $F) ∘↓ $H  ↪ Func_cov_hom'' $Z ($F <∘ $H); 
 
rule Op_hom ($r ∘↓ $H) ↪ (Op_hom $r) ∘↓ (Op_func $H); 
 
/* (F) transf ========================== */

injective symbol Op_transf :Π [X Y X' Y': cat]  [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
 transf R xx' R' yy'  → transf (Op_mod R) (Op_func yy') (Op_mod R') (Op_func xx');

 constant symbol Id_transf : Π [A X : cat] (R : mod A X) ,
 transf R Id_func R Id_func;

 rule Op_transf (Op_transf $A) ↪ $A
 with Op_transf (Id_transf $R) ↪ (Id_transf (Op_mod $R)); 
 
constant symbol Terminal_transf : Π [A B : cat] (R : mod A B), transf R (Terminal_func A) (Unit_mod Id_func Id_func) (Terminal_func B);
 
constant symbol Unit_Tensor_cov_transf : Π [A B A' X : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] ,
transf P F P' Id_func → 
transf ((⊗) P (Unit_mod Id_func Id_func)) F P' Id_func;

 //todo eval-lambda with unit, so between hom and transf 
 //todo eval-lambda dependent over —/Γ context? or prefixed under Γ⊗— context?
 constant symbol  Eval_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ((⊗) P Q)  F O                     L;
 
//TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR DEPENDENT MORPHISM OF FIBRATIONS
// THEREFORE TENSOR ABSORB THE SPAN WHICH WOULD REPLACE Id_func AND SOLVES EARLIER PROBLEMS
constant symbol Lambda_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ((⊗) P Q)  F O                     L;
 
 constant symbol Eval_cov_hom_transf : Π [A  X A' X' : cat] [Q : mod A X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 hom                       F (Imply_cov_mod O L Q) Id_func →
 transf Q  F O                     L;
 
 constant symbol Tensor_cov_transf : Π [A' I X' A X: cat] [P' : mod A' I] [Q' : mod I X'] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func X' X],
 transf P' F P Id_func → transf Q' Id_func Q G →
 transf ((⊗) P' Q') F ((⊗) P Q) G;

rule Op_transf (Tensor_cov_transf $rr $ss) ↪ (Tensor_cov_transf (Op_transf $ss) (Op_transf $rr)); 
 
 constant symbol Tensor_cov_hom_transf : Π [A' I A X: cat] [P' : mod A' I] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func I X],
 transf P' F P Id_func → hom Id_func Q G →
 transf P' F ((⊗) P Q) G;
 
 constant symbol Imply_cov_transf : Π [A B A' B' C D D' : cat] [O : mod A B] [O' : mod A' B']
  [Q : mod C D] [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func D D'],
 transf O F O' G → Π (K : func D' B), transf Q Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) Id_func;
 
 constant symbol Imply_cov_hom_transf : Π [A B A' B' C  D' : cat] [O : mod A B] [O' : mod A' B']
   [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func C D'],
 transf O F O' G → Π (K : func D' B), hom Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (O' <<∘ ((G <∘ K) <∘ L)) Id_func;
 
 
 // "J-rule" , admissible/eliminated until accumulation onto basic constructors
 //Unit_cov_transf
 injective symbol ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func;
 //Unit_con_transf
 injective symbol _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G;
 
 notation _'∘> infix right 80; notation ∘>'_ infix left 80;
 
rule Op_transf (($M)_'∘> $r) ↪ (Op_hom $r) ∘>'_ (Op_func $M);
rule Op_transf ($r ∘>'_ ($M)) ↪ (Op_func $M) _'∘> (Op_hom $r);

 // (substitution) admissible/eliminated until accumulation onto basic constructors
 //Comp_hom
 symbol '∘ : Π [A' B' A B I : cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func B' B],
 hom X S Y → transf S F T G → hom (X ∘> F) T (G <∘ Y);
 notation '∘ infix right 80;
 
 symbol ∘' [A' B' A B I : cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func B' B] :
 transf S F T G → hom X S Y → hom (X ∘> F) T (G <∘ Y)
  ≔ λ st s, s '∘ st;
 notation ∘' infix left 80;

rule Op_hom ($s '∘ $st) ↪ (Op_hom $s) '∘ (Op_transf $st);

 rule ($a '∘  $t) ∘↓ $Z ↪ (($a ∘↓ $Z) '∘  $t) ; //check SIMILAR RULE below possibly in reverse and re-correct
 
 //TODO: REVIEW no lack for Comp_transfd because it is always applied to Total_transf ? so no separate cut case analysis
 //Comp_transf
 symbol ''∘ : Π [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B],
 transf R X S Y → transf S F T G → transf R (X ∘> F) T (G <∘ Y);
 notation ''∘ infix right 80;
 
 symbol ∘'' [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B] :
 transf S F T G → transf R X S Y → transf R (X ∘> F) T (G <∘ Y)
   ≔ λ st rs, rs ''∘ st;
 notation ∘'' infix left 80;
 
 rule Op_transf ($rs ''∘ $st) ↪ (Op_transf $rs) ''∘ (Op_transf $st);

// it is a metatheorem by cases induction that the associativity propositional-equation is derivable,
// and it must not be assumed as rewrite/conversion rule
 constant symbol associativity_con_metatheorem : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
 Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
 Π  (s : hom x R y), 
 Π   [K0] [F' : func K0 A] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x) Id_func) , 
 π (( (( x''x'_ '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' y'y_  ) 
   =  (x''x'_ '∘ ((F')_'∘> ( (s ∘>'_(G)) ∘' y'y_ ))));
 
/* (G) limit_cov ========================== */

 // inductive transf
 injective symbol Op_limit_con : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
 (isl : limit_cov K F W F_⇐_W), limit_con (Op_func K) (Op_func F) (Op_mod W) (Op_func F_⇐_W); 
 injective symbol Op_limit_cov : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J J'] [F : func J0 B] [W_⇒_F : func J' B]
 (isl : limit_con K F W W_⇒_F), limit_cov (Op_func K) (Op_func F) (Op_mod W) (Op_func W_⇒_F);

 rule Op_limit_con (Op_limit_cov $isl) ↪ $isl
 with Op_limit_cov (Op_limit_con $isl) ↪ $isl ;
 
 constant symbol limit_cov_transf : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
 (isl : limit_cov K F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (Imply_cov_mod ((Unit_mod M F)) K W) Id_func (Unit_mod M F_⇐_W) Id_func;

constant symbol limit_con_transf : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J J'] [F : func J0 B] [W_⇒_F : func J' B]
 (isl : limit_con K F W W_⇒_F), Π [I : cat] (M : func I B),
 transf (Imply_con_mod W K ((Unit_mod F M ))) Id_func (Unit_mod W_⇒_F M) Id_func;

rule Op_transf (Op_transf $A) ↪ $A
with (Op_transf (limit_cov_transf $isl $M) ) ↪ limit_con_transf (Op_limit_con $isl) (Op_func $M);
 
//  /* (1) ========================== */
 
 // naturality and dinaturality of evaluation
 
 type λ [A B X A' X' : cat] [P : mod A B] [Q : mod B X] 
 (O : mod A' X')  [F : func A A'] (L : func X X')
 (pq_o : transf P                       F (Imply_cov_mod O L Q) Id_func)
 A0  X0 (M: func A0 A)  (Z : func X0 X) 
 (P': mod A0 B) (Q' : mod B X0) 
 (p'p : transf P' M P Id_func) (q'q : transf Q' Id_func Q Z),
 (Eval_cov_transf  pq_o)  ∘'' (Tensor_cov_transf p'p q'q)
 ==>> Eval_cov_transf  ((pq_o ∘'' p'p) ''∘ (Imply_cov_transf (Id_transf O) L q'q)); 
 
 type λ [A X A' X' : cat] [Q : mod A X] 
 (O : mod A' X')  [F : func A A'] (L : func X X')
 (pq_o : hom                       F (Imply_cov_mod O L Q) Id_func)
  X0  (Z : func X0 X) 
  (Q' : mod A X0) 
  (q'q : transf Q' Id_func Q Z),
 (Eval_cov_hom_transf  pq_o)  ∘'' q'q
 ==>> Eval_cov_hom_transf  (pq_o '∘ (Imply_cov_transf (Id_transf O) L q'q)); 
 
 // evaluation of coyoneda at identity hom
 
 type λ [A B A' : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] 
 (pp : transf P F P' Id_func),
 (Unit_Tensor_cov_transf pp)  ∘'' (Tensor_cov_hom_transf (Id_transf P) (Func_cov_hom Id_func))
  ==>> pp;
 // transf P (Id_func ∘> F) P' (Id_func <∘ Id_func)
 
 
 // functos and adjunctions 
 
 constant symbol Adj_cov_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I L),
 hom (Z ∘> RAdj_func) (Unit_mod LAdj_func Z) Id_func;
 
 constant symbol Adj_con_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I R),
 hom Id_func (Unit_mod Z RAdj_func) (Z ∘> LAdj_func);
 
 injective symbol Op_adj : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), adj (Op_func RAdj_func) (Op_func LAdj_func);
 
 rule Op_adj (Op_adj $aj) ↪ $aj;
 
 rule Op_hom (Adj_cov_hom $aj $Z) ↪ Adj_con_hom (Op_adj $aj) (Op_func $Z);



 /* (6) misc ========================== */
 
 //voila
 
 // idtransf ''∘  transf = transf
 
 type λ [A' B' A B: cat] [R' : mod A' B'] [F : func A' A] [R : mod A B] [G : func B' B]
 (r'r : transf R' F R G),
 (Id_transf _) ''∘ r'r ==>> r'r;
 type λ [A' B' A B: cat] [R' : mod A' B'] [F : func A' A] [R : mod A B] [G : func B' B]
 (r'r : transf R' F R G),
 r'r ''∘ (Id_transf _) ==>> r'r;
 
 // idhom ''∘ funchom = idhom
 type λ [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ,
 ((M)_'∘> ((Func_con_hom F) ∘↓ Z) ) ''∘ ((M ∘> F)_'∘> (Func_con_hom F')) 
 ==>> ((M)_'∘> ((Func_con_hom (F ∘> F')) ∘↓ Z)) ; 
 // : ransf (Unit_mod M (Z ∘> Id_func)) (Id_func ∘> Id_func) ((M ∘> F) ∘>> Unit_mod F' Id_func) (F' <∘ (F <∘ Z))
 
 // j-rule then apply hom then restrict
 //todo more general, no need for case of  jrule
 //TODO REVIEW THIS . ANOTHER RULE ABOVE MAY GO IN REVERSE DIRECTION
 type λ [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B]
 (M : func J A) (r : hom F R G ) K (M' : func K J ) N'  (a : hom M' (Unit_mod M F) N')
 K' (Z : func K' K), 
  ((a '∘ ((M)_'∘> r)) ∘↓ Z )
 ==> ((a ∘↓ Z) '∘ ((M)_'∘> r)) ;
 // : hom (M' ∘> Id_func) (M ∘>> R) (G <∘ N')
 
 // assoc comp_transf then comp_hom
rule  $r '∘ ($rs ''∘ $st)
 ↪ ($r '∘ $rs) '∘ $st;
assert [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
[X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B]
(rs : transf R X S Y) (st : transf S F T G) K (M' : func K A'') N'  (r : hom M' R N') ⊢ eq_refl _ : π (
  r '∘ (rs ''∘ st)
   = (r '∘ rs) '∘ st  );

 //todo: derivable restr ?
 // type λ [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ,
 // ((M)_'∘> ((Func_con_hom F) ∘↓ Z) ) ;
 
 // id_cov_hom on id_func is id_transf
 type λ [B : cat] I (M : func I B)  ,
 ((M)_'∘> (Func_con_hom Id_func) )
 ==>> (Id_transf _)  ;
 
 // j-rule then applied to id_hom, both cov and con
 // note for confluence that already exists another rewrite that jrule of restr 
 type λ [I A B : cat] [F : func I A] [R : mod A B] [G : func I B]
 (r : hom F R G ) J (Z : func J _ ) , 
   (((Func_cov_hom F) ∘↓ Z) '∘ ((Id_func)_'∘> r)) 
 ==> r ∘↓ Z;
 
 /* (2) ========================== */
 
 // naturality
 
//naturality1_con_con
 // t∘1(g) ∘X0 -  =  t∘1(g ∘X0 -) 
 rule ($M)_'∘> ($g '∘ (($X0)_'∘> $t))
 ↪ (($M)_'∘> $g) ''∘ (($M ∘> $X0)_'∘> $t);

 assert [L R J I I' I1 : cat] [T : mod R L]
 [Y0 : func I1 R] [Y: func I' I1] [Z : func I1 L]
 (M : func J I) [X: func I' I] (X0: func I R) 
 (t : hom Y0 T Z)
 (g : hom X (Unit_mod X0 Y0) Y) ⊢ eq_refl _ : π (
 (M)_'∘> (g '∘ ((X0)_'∘> t))
 = ((M)_'∘> g) ''∘ ((M ∘> X0)_'∘> t)    );

 symbol naturality1_con_con : Π [L R J I I' I1 : cat] [T : mod R L]
 [Y0 : func I1 R] [Y: func I' I1] [Z : func I1 L]
 (M : func J I) [X: func I' I] (X0: func I R) 
 (t : hom Y0 T Z)
 (g : hom X (Unit_mod X0 Y0) Y),
 (M)_'∘> (g '∘ ((X0)_'∘> t))
 ==>> ((M)_'∘> g) ''∘ ((M ∘> X0)_'∘> t);
 // : transf (M ∘>> _1<∘ (X ∘> Id_func)) Id_func (M ∘>> (X0 ∘>> T)) (Z <∘ Y)
 
 symbol naturality1_con_con_Adj_con [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) [I] (Z : func I R)
  [J I1 I2 : cat] (X: func J I1) (X0: func I1 I) (Y: func J I2) (Y0 : func I2 I) 
  (g : hom X (Unit_mod X0 Y0) Y) J' (M: func J' I1): 
 (M)_'∘>  (g '∘ ((X0)_'∘> ((Adj_con_hom aj Z) ∘↓ Y0)))
  ==>>  ((M)_'∘>  g) ''∘ ((M ∘> X0)_'∘> ((Adj_con_hom aj Z) ∘↓ Y0))
 ≔ naturality1_con_con M X0 (Adj_con_hom aj Z ∘↓ Y0) g;
 
 //?solution to use of Id_hom : Z0 is identity in practice instances; or both versions are present
 // (1∘Z0-)∘t∘(g)  =  1∘t∘(- Y0<∘ g)
 // todo erase, N not general enough, use instead naturality2_con_cov
 type λ [L R I I0 I1 J : cat] 
 (X: func I I0) (X0: func I0 R)
 (Y0 : func I1 R) (Y: func I I1) (Z0 : func I1 L) (N : func J I1)
 (T : mod R L) (t : hom Y0 T Z0)
 (g : hom X (Unit_mod X0 Y0) Y),
 ((g '∘ ((X0)_'∘> t)) ∘>'_(Id_func)) // : transf ((Y ∘> Z0) ∘>1_) X (X0 ∘>> T) Id_func
    ∘'' (( (Y)_'∘> (Func_con_hom Z0) ∘↓ N))
 ==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> (t ∘↓ N)))  ;
 // transf (Y ∘>> _1<∘ (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) 
 //        ((X0 ∘>> T) <<∘ Id_func) (Id_func <∘ (Z0 <∘ N))
 

 symbol naturality2_con_cov : Π [L I : cat] [Z_LAdj_func : func I L] [Unit_mod_Z_RAdj_func : mod I L]
 (Adj_con_hom_Z : hom Id_func Unit_mod_Z_RAdj_func Z_LAdj_func)
  [J I1 I2 : cat] [X: func J I1] (X0: func I1 I) [Y: func J I2] (Y0 : func I2 I) 
  (g : hom X (Unit_mod X0 Y0) Y) [J' : cat] (N : func J' I), /* N is more general */
 
  (g '∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ Y0))) ∘>'_(Id_func)
     ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func)) ∘↓ N))
  ==>> ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ N)) ;

//TODO: this is the correct version, replace everywhere above
constant symbol Adj_con_hom' : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func), Π [I] (Z : func I R) [J] (N : func J I),
hom N (Unit_mod Z RAdj_func) (N ∘> (Z ∘> LAdj_func));

type λ [L I : cat] [Z_LAdj_func : func I L] [Unit_mod_Z_RAdj_func : mod I L]
(Adj_con_hom_Z : hom Id_func Unit_mod_Z_RAdj_func Z_LAdj_func)
 [J I1 I2 : cat] [X: func J I1] (X0: func I1 I) [Y: func J I2] (Y0 : func I2 I) 
 (g : hom X (Unit_mod X0 Y0) Y) [J' : cat] (N : func J' I), /* N is more general */

 (@∘>'_ _ _ _ _ _ _ (Y ∘> Y0) (g '∘ ((X0)_'∘> (Id_hom Y0))) (N))
 ''∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ N));

 rule   (( ($Y ∘> $Y0)_'∘> (Func_con_hom'' ($Z ∘> $LAdj_func) $N))) ''∘
(@'∘ _ _ _ _ _ _ _ _ $Y _ _ $g  (($X0)_'∘> ((@Adj_con_hom' _ _ $LAdj_func _ $aj _ $Z _ $Y0)))) ∘>'_(Id_func)
↪   (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_ ($N))
 ''∘ (($X0)_'∘> ((Adj_con_hom' $aj $Z $N) ));

 symbol naturality2_con_cov_Adj_con [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 [aj : adj LAdj_func RAdj_func] [I] [Z : func I R]
  [J I1 I2 : cat] [X: func J I1] [X0: func I1 I] [Y: func J I2] [Y0 : func I2 I] 
  [g : hom X (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I]: /* N is more general */
 
  (g '∘ ((X0)_'∘> ((Adj_con_hom aj Z) ∘↓ Y0))) ∘>'_(Id_func)
     ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z ∘> LAdj_func)) ∘↓ N))
  ==>> ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Adj_con_hom aj Z) ∘↓ N))
 ≔ naturality2_con_cov (Adj_con_hom aj Z) X0 Y0 g N;
 
 symbol naturality2_con_cov_Func_con  [L I : cat] [Z_LAdj_func : func I L]
  [J I1 I2 : cat] [X: func J I1] [X0: func I1 I] [Y: func J I2] [Y0 : func I2 I] 
  [g : hom X (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I]: 
 
  (g '∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func) ∘↓ Y0))) ∘>'_(Id_func)
     ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func)) ∘↓ N))
  ==>> ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func) ∘↓ N))
 ≔ naturality2_con_cov (Func_con_hom Z_LAdj_func) X0 Y0 g N;
 
 
 
 //TODO: erase? see more general naturality2_con_cov
 //solution to use of Id_hom : Z0 is identity in practice instances; or both versions are present
 // (1∘1-)∘t∘(g)  =  1∘t∘(- Y0<∘ g)
 type λ [R I I0 I1 J : cat] 
 (X: func I I0) (X0: func I0 R)
 (Y0 : func I1 R) (Y: func I I1) (N : func J I1)
 (T : mod R I1) (t : hom Y0 T Id_func)
 (g : hom X (Unit_mod X0 Y0) Y),
 ((g '∘ ((X0)_'∘> t)) ∘>'_(Id_func)) // : transf (Y ∘>1_) X (X0 ∘>> T) Id_func
    ∘'' (( (Y)_'∘> (Id_hom N)))
 ==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> (t ∘↓ N)))  ;
 // : transf (Unit_mod Y (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) ((X0 ∘>> T) <<∘ Id_func) (Id_func <∘ (Id_func <∘ N))
 

//  /* (3) ========================== */
 
 // adjunction inverses
 
 // “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
 type λ [L R I J I0 J0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I0 R) (M : func I I0)  (N : func J J0) (W: func J0 L),
  (((Adj_con_hom aj Z) ∘↓ M) ∘>'_(N ∘> W)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj W) ∘↓ N))
  ==>>  (((Func_con_hom (Z ∘> LAdj_func)) ∘↓ M) ∘>'_(N ∘> W) ) ''∘ ((Z ∘> LAdj_func)_'∘> ((Func_cov_hom W) ∘↓ N));
  // : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) (N ∘> W)) M (Unit_mod (Z ∘> LAdj_func) W) N
  
 // “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   
 type λ [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) Z (N : func I R) (M : func J R),
 ( (M)_'∘> ((Adj_con_hom aj Z) ∘↓ N) )   ''∘ ( (M ∘> Z )_'∘> (Adj_cov_hom aj Id_func) )
 ==>>  ( (M)_'∘> ((Func_con_hom (Z ∘> LAdj_func)) ∘↓ N) ); 
 // : transf (Unit_mod M N) Id_func (Unit_mod (M ∘> (Z ∘> LAdj_func)) Id_func) ((Z ∘> LAdj_func) <∘ N)
 
 
//  /* (4) ========================== */
 
//  // right adjoint preserves weighted limit_covs
 

  symbol righ_adjoint_preserves_limit_cov  [B J0 J J' A : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
  (isl : limit_cov K F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) :
  transf (Imply_cov_mod (Unit_mod M (F ∘> R)) K W) Id_func (Unit_mod M R <<∘ F_⇐_W) Id_func
  ≔ ((Imply_cov_transf ((M)_'∘> Adj_cov_hom isa F) K (Id_transf W)) ''∘ (limit_cov_transf isl (M ∘> L)))
  ''∘ ((Adj_con_hom isa M) ∘>'_(F_⇐_W));

// assert [B J0 J J' A : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
// (isl : limit_cov K F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
// Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
// transf (Imply_con_mod (Op_mod W) (Op_func K) ((Op_func F ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M))) 
//          Id_func ((Op_func F_⇐_W ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M)) Id_func;
assert [B J0 J J' A : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
(isl : limit_cov K F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
transf (Imply_con_mod (Op_mod W) (Op_func K) ( (Unit_mod (Op_func F ∘> Op_func R) (Op_func M)))) 
         Id_func ((Unit_mod (Op_func F_⇐_W ∘> Op_func R) (Op_func M))) Id_func;

assert [B J0 J J' A : cat] [K : func J J0] [W : mod J J'] [F : func J0 B] [W_⇒_F : func J' B]
(isl : limit_con K F W W_⇒_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M)) :
transf (Op_mod (Imply_cov_mod (Unit_mod (Op_func M) (Op_func F ∘> Op_func L)) (Op_func K) (Op_mod W)))
   (Op_func Id_func) (Op_mod (Unit_mod (Op_func M) (Op_func L) <<∘ Op_func W_⇒_F)) (Op_func Id_func) ;

symbol left_adjoint_preserves_limit_con [B J0 J J' A : cat] [K : func J J0] [W : mod J J'] [F : func J0 B] [W_⇒_F : func J' B]
(isl : limit_con K F W W_⇒_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) :
  transf (Imply_con_mod W K (Unit_mod (F ∘> L) M)) Id_func (W_⇒_F ∘>> Unit_mod L M) Id_func
  ≔ Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M));

//  /* (5) ========================== */
 
//  // concrete example and inductive data type
 
//OK ONR
symbol join_cat : Π (A B : cat), cat;
symbol join_First_func : Π (A B : cat), func A (join_cat A B);
symbol join_Second_func : Π (A B : cat), func B (join_cat A B);
symbol join_hom :  Π (A B : cat) [I : cat] (a : func I A) (b : func I B), hom a (Unit_mod (join_First_func A B) (join_Second_func A B)) b ;

rule @'∘ _ _ _ _ _ _ _ $a' Id_func _ _ $r (( Id_func ) _'∘> (join_hom $A $B $a $b)) ↪ (join_hom $A $B $a' $b);
assert (A B : cat) [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) ⊢ 
        eq_refl _  : π (r  '∘ (( _ ) _'∘> (join_hom A B a b)) = (join_hom A B a' b));

symbol join_elim_con_func : Π (A B : cat) [E : cat] (first_func : func A E)  (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b)) //note extensionality second_func outside
(natural_eq : Π [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) , 
      π (r  '∘ (( _ ) _'∘> (one_hom I a b)) = (one_hom I a' b))), 
  func (join_cat A B) E;
rule  join_First_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F0
with  join_Second_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F1;

type λ (A B : cat) [E : cat] (first_func : func A E) (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b))
[I : cat] (a : func I A) (b : func I B),
((join_hom A B a b) '∘ ((join_First_func A B) _'∘> (Func_con_hom'' (join_elim_con_func A B first_func second_func one_hom _) 
                            (join_Second_func A B)))) ==> one_hom _ a b ;

rule ((join_hom $A $B $a $b) '∘ ((join_First_func $A $B) _'∘> (Func_con_hom'' (join_elim_con_func $A $B $first_func $second_func $one_hom _) 
              (join_Second_func $A $B)))) ↪ $one_hom _ $a $b ;




 /* PART 2 Fibrations and dependency */

/* (ad) catd ========================== */

 injective symbol Op_catd : Π [X : cat] (A : catd X), catd (Op_cat X);
 injective symbol Op_isFibration_cov : Π [X : cat] [A : catd X], isFibration_con A → isFibration_cov (Op_catd A);
 injective symbol Op_isFibration_con : Π [X : cat] [A : catd X], isFibration_cov A → isFibration_con (Op_catd A);

 rule Op_catd (Op_catd $A) ↪ $A;
 rule Op_isFibration_cov (Op_isFibration_con $A_isf) ↪ $A_isf
 with Op_isFibration_con (Op_isFibration_cov $A_isf) ↪ $A_isf;

 //| Fibre_cat : Π [X I : cat] (A : catd X) (x : func I X), cat //not lacked;
 

 constant symbol Comma_cat : Π [A B : cat] (R : mod A B), cat;
 
 constant symbol Universe_con_cat : cat; 
 constant symbol Universe_cov_cat : cat;
 constant symbol Universe_con_catd : catd Universe_con_cat;
 constant symbol Universe_cov_catd : catd Universe_cov_cat;
 constant symbol Universe_con_isFibration_con : isFibration_con Universe_con_catd;
constant symbol Universe_cov_isFibration_cov : isFibration_cov Universe_cov_catd;

 rule Op_cat (Universe_cov_cat) ↪ Universe_con_cat
// this inverse necessary? yes for confluence and for the rule for Op_catd below
 with Op_cat (Universe_con_cat) ↪ Universe_cov_cat;

 rule Op_catd (Universe_cov_catd) ↪ Universe_con_catd
 with Op_catd (Universe_con_catd) ↪ Universe_cov_catd;

 rule Op_isFibration_cov (Universe_con_isFibration_con) ↪ Universe_cov_isFibration_cov
 with Op_isFibration_con (Universe_cov_isFibration_cov) ↪ Universe_con_isFibration_con;

 // todo both cov catd and con catd
 
 symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;
 constant symbol Fibre_isFibration_con : Π [X I : cat] (A : catd X) (A_isf : isFibration_con A) (x : func I X),
    isFibration_con (Fibre_catd A x);
 constant symbol Fibre_isFibration_cov : Π [X I : cat] (A : catd X) (A_isf : isFibration_cov A) (x : func I X),
     isFibration_cov (Fibre_catd A x);

//TODO: use Productdt_ instead of Cast_ ?  or add each and all the intermediate versions ?
 constant symbol Cast_catd : Π (A : cat) , catd Terminal_cat;
 constant symbol Productdt_catd : Π [U : cat] (UU : catd U) (A : cat), catd U;

constant symbol Productd'_catd : Π [U : cat] (X : catd U) (Y : catd U), catd U;

 constant symbol Sigma_catd : Π [Y X : cat] (Z : catd Y) (F : func Y X), catd X;

constant symbol Pid_catd : Π [X' X Y : cat] (K : func X X') (A : catd X) (F : func X Y) (B : catd Y), catd X';

 
 constant symbol Comma_con_catd : Π [A B : cat] (R : mod A B), catd A;
 constant symbol Comma_con_catd' : Π [A B : cat] (R : mod A B) (BB : catd B) , catd A;
 
 constant symbol Comma_cov_catd : Π [A B : cat] (R : mod A B), catd B;
 constant symbol Comma_cov_catd' : Π [A B : cat] (AA : catd A) (R : mod A B), catd B;
 
rule Op_catd (Fibre_catd $A $x) ↪ (Fibre_catd (Op_catd $A) (Op_func $x))
with Op_catd (Productdt_catd $T $A) ↪ (Productdt_catd (Op_catd $T) (Op_cat $A))
with Op_catd (Productd'_catd $X $Y) ↪ (Productd'_catd (Op_catd $Y) (Op_catd $X))
with Op_catd (Triv_catd $X)  ↪ Triv_catd (Op_cat $X)
with Op_catd (Comma_con_catd' $R $BB) ↪ (Comma_cov_catd'  (Op_catd $BB) (Op_mod $R))
with Op_catd (Comma_cov_catd $R) ↪ (Comma_con_catd (Op_mod $R));
 
 rule Fibre_catd $A Id_func ↪ $A
 with Fibre_catd $A ($x ∘> $y)  ↪ Fibre_catd (Fibre_catd $A $y) $x
 // reverse direction ?
// with  Fibre_catd (Fibre_catd $A $y) $x ↪ Fibre_catd $A ($x ∘> $y)  
with Fibre_catd (Triv_catd _) _ ↪ (Triv_catd _)
 with Fibre_catd (Comma_con_catd $R) $F ↪ (Comma_con_catd ($F ∘>> $R))  //todo review this?
 with Fibre_catd (Comma_cov_catd $R) $G ↪ (Comma_cov_catd ($R <<∘ $G)) ;

// NOTE: contrast Sigma_cat vs Total_cat: Total_cat is defined by rules, 
// Sigma_cat is constant constructor adjoint to Cast_catd
symbol Total_cat : Π [X : cat], catd X → Π [X'] (x : func X' X), cat;
symbol Total_proj_func : Π [X : cat] (A : catd X), Π [X'] (x : func X' X) , func (Total_cat A x) X';

//this direction to collect associativity
rule Pullback_cat (Total_proj_func $A $F) $G
↪ Total_cat $A ($G ∘> $F);
rule Pullback_snd_func (Total_proj_func $A $F) $G
↪ Total_proj_func $A ($G ∘> $F);


rule Total_cat (Fibre_catd $A $F) $G  ↪ Total_cat $A ($G ∘> $F) // = Pullback_cat (Total_proj_func $A $F) $G
with @Total_cat _ (Triv_catd $A) $B $F ↪ $B
with @Total_cat _ (Cast_catd $A) $U' $F  ↪  (Product_cat $U' $A) 
 with Total_cat (Productdt_catd $UU $A) $F  ↪  (Product_cat (Total_cat $UU $F) $A)  
with Total_cat (Productd'_catd $X $Y) $H ↪  
(Pullback_cat (Total_proj_func $X $H) (Total_proj_func $Y $H)) 
// these are instances of fibre rule above
with Total_cat (Comma_con_catd ($F ∘>> $R)) $F' ↪ Total_cat (Comma_con_catd $R) ($F' ∘> $F)
with Total_cat (Comma_cov_catd ($R <<∘ $G)) $G' ↪ Total_cat (Comma_cov_catd $R) ($G' ∘> $G)
;



rule Total_proj_func (Fibre_catd $A $F) $G ↪ Total_proj_func $A ($G ∘> $F) // = Pullback_snd_func (Total_proj_func $A $F) $G
with Total_proj_func (Triv_catd $A) $F ↪ Id_func
with @Total_proj_func _ (Cast_catd $A) $U' $F ↪ @Product_fst_func $U' $A _ Id_func 
 with Total_proj_func (Productdt_catd $UU $A) $F  ↪  (Product_fst_func $A (Total_proj_func $UU $F))
with Total_proj_func (Productd'_catd $X $Y) $H  ↪  
(Pullback_func (Total_proj_func $X $H) (Total_proj_func $Y $H)) 
;


/* (bd) funcd ========================== */

constant symbol  Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A;

symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
notation ∘>d infix right 90;
symbol d<∘ [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z] : funcd B G C → funcd A F B → funcd A (F ∘> G) C ≔ λ G F, F ∘>d G;
notation d<∘ infix left 90;

rule ($F ∘>d $G) ∘>d $H ↪ $F ∘>d ($G ∘>d $H)
with $F ∘>d Id_funcd ↪ $F
with Id_funcd ∘>d $F ↪ $F; 

injective symbol Op_funcd : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → funcd (Op_catd A) (Op_func F) (Op_catd B);

rule Op_funcd (Op_funcd $F) ↪ $F
with Op_funcd (Id_funcd) ↪ (Id_funcd)
with Op_funcd ($F ∘>d $G) ↪ ((Op_funcd $F) ∘>d (Op_funcd $G)) ;

//TODO: use Productdt_ instead of Cast_ ?
constant symbol Cast_intro_funcd : Π [U A : cat] (I : catd U) [U'] (u : func U' U) (G : func (Total_cat I u) A), 
funcd (Fibre_catd I u) (Terminal_func U') (Cast_catd A);

//TODO: will be clearly motivated when spans are used instead
constant symbol Productdt_intro_funcd' : Π [U : cat] [UU : catd U] [A : cat] [U'] [u : func U' U] 
[U''] [u' : func U' U''] [I : catd U''] (F : funcd (Fibre_catd I u') u UU)  
(G : func (Total_cat I u') A) , 
funcd (Fibre_catd I u') u (Productdt_catd UU A);

//TODO erase Cast_ use instead Productdt_
constant symbol Cast_funcd : Π  [A B : cat] (F : func A B), funcd (Cast_catd A) Id_func (Cast_catd B); 

constant symbol Productdt_funcd : Π [U : cat] (UU : catd U) [A B : cat] (F : func A B), funcd (Productdt_catd UU A) Id_func (Productdt_catd UU B); 
constant symbol Productdt_base_funcd : Π [U V : cat] [F : func U V] [UU : catd U] [VV : catd V] (FF : funcd UU F VV) (A : cat) , funcd (Productdt_catd UU A) F (Productdt_catd VV A); // ?used?

 symbol  Triv_funcd :  Π [X Y : cat] (xy : func X Y), funcd (Triv_catd X) xy (Triv_catd Y);
 
symbol Fibre_intro_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A  → funcd J i (Fibre_catd A x);
 //TODO: REVIEW both are required in different grammatical/syntactical entries (implementation datatype), 
 ///together with cancelation against the same elim
 constant symbol Fibre_intro_funcd' : Π [X I : cat] (A : catd X) (x : func I X) [J : catd I]  ,
 funcd J x A  → funcd J Id_func (Fibre_catd A x);

 
 symbol Fibre_elim_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;
 
 
rule Op_funcd (Triv_funcd $xy) ↪ (Triv_funcd (Op_func $xy))
 with Op_funcd (Fibre_intro_funcd $A $x $i $FF) ↪ (Fibre_intro_funcd (Op_catd $A) (Op_func $x) (Op_func $i) (Op_funcd $FF))
 with Op_funcd (Fibre_elim_funcd $A $x) ↪ (Fibre_elim_funcd (Op_catd $A) (Op_func $x));


constant symbol Comma_con_intro_funcd' : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd BB y) x (Comma_con_catd' R BB);
constant symbol Comma_cov_intro_funcd' : Π [A B I : cat] (AA : catd A) [R : mod A B]  [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd AA x) y (Comma_cov_catd' AA R);
 
 
constant symbol Comma_con_comp_funcd' : Π [A B I : cat] (R : mod A B) (BB : catd B) (F : func I A),
funcd (Comma_con_catd' (F ∘>> R) BB) F (Comma_con_catd' R BB);
constant symbol Comma_cov_comp_funcd' : Π [A B I : cat] (AA : catd A) (R : mod A B) (G : func I B),
funcd (Comma_cov_catd' AA (R <<∘ G )) G (Comma_cov_catd' AA R);

rule (Comma_con_comp_funcd' _ _ $F') ∘>d (Comma_con_comp_funcd' $R $BB $F)
↪ (Comma_con_comp_funcd' $R $BB ($F' ∘> $F));

//SIGNIFICANT: note no use of explicit Op_cat contravariance or of extra notion of contravariant functor, 
// here the contravariance is intrinsic baked into the contravariant universe, 
// and each independent development of the two universes need not interact via Op_ ,
// better: each don't even need the existance of Op_
symbol Universe_con_func : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), func  X Universe_con_cat; 
symbol Universe_cov_func : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), func X Universe_cov_cat;

symbol Universe_con_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), funcd A (Universe_con_func A A_isf) Universe_con_catd;
symbol Universe_cov_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), funcd A (Universe_cov_func A A_isf) Universe_cov_catd;

rule Op_func (Universe_cov_func $A $A_isf) ↪ (Universe_con_func (Op_catd $A) (Op_isFibration_con $A_isf))
with Op_func (Universe_con_func $A $A_isf) ↪ Universe_cov_func (Op_catd $A) (Op_isFibration_cov $A_isf);

rule Op_funcd (Universe_cov_funcd $A $A_isf) ↪ Universe_con_funcd (Op_catd $A) (Op_isFibration_con $A_isf)
with Op_funcd (Universe_con_funcd $A $A_isf) ↪ Universe_cov_funcd (Op_catd $A) (Op_isFibration_cov $A_isf);
 
//todo review  necessary
// constant symbol Catd_funcd : Π [X : cat] (A : catd X), funcd A Id_func (Triv_catd X); //as funchd ?;
 
 constant symbol SigmaIntro_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X), funcd Z F (Sigma_catd Z F);
 
 
 constant symbol SigmaElim_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X),
 Π [X' : cat] [C : catd X'] (G : func X X'),
   funcd Z (F ∘> G) C → funcd (Sigma_catd Z F) G C;
 
// naturality
rule (SigmaElim_funcd $Z $F $G $GG) ∘>d $HH ↪ (SigmaElim_funcd $Z $F _ ($GG ∘>d $HH));
// beta
rule (SigmaIntro_funcd $Z $F) ∘>d (SigmaElim_funcd $Z $F $G $GG) ↪ $GG;



rule Op_funcd (Productdt_funcd $UU $F) ↪ (Productdt_funcd (Op_catd $UU) (Op_func $F))
with Op_funcd (Productdt_base_funcd $FF $A) ↪ (Productdt_base_funcd (Op_funcd $FF) (Op_cat $A));

rule (Cast_funcd $F) ∘>d (Cast_funcd $G) ↪ Cast_funcd ($F ∘> $G);


//TODO: ADD THIS FUNCTOR AS INTERMEDIATE LOGICAL SYMBOL WITH OWN RULES, WITH ITS OLDER DEFINITION CONTENT WHICH REWRITE TO THIS SYMBOL
symbol Fibre_functor_funcd  [X Y Z] [B: catd Y] [C: catd Z] [G: func Y Z] (GG : funcd B G C) (F: func X Y) :
 funcd (Fibre_catd B F) Id_func (Fibre_catd C (F ∘> G)) ≔ // todo over Id intro
  Fibre_intro_funcd C (F ∘> G) Id_func (@∘>d _ _ _ _ B C F G (Fibre_elim_funcd B F) GG ) ;
//this comes from naturality, less prime
symbol Fibre_functor_funcd'  [X Y Z] [B: catd Y] [C: catd Z]  [G: func Y Z] (GG : funcd B G C) (F: func X Y):
funcd (Fibre_catd B F) F (Fibre_catd C G) ≔ 
 Fibre_intro_funcd C G F (@∘>d _ _ _ _ B C F G (Fibre_elim_funcd B F) GG ) ;


constant symbol Productd'_intro_funcd : Π [U] [T X : catd U] [V] [I : catd V]
[u : func V U] (FF : funcd I u T)  (GG : funcd I u X),
 funcd I u (Productd'_catd T X);
constant symbol Productd'_fst_funcd : Π [U] (T X : catd U) ,
funcd (Productd'_catd T X) Id_func T ; 
constant symbol Productd'_snd_funcd : Π [U] (T X : catd U),
funcd (Productd'_catd T X) Id_func X ; 

//TODO: ADD THIS FUNCTOR AS INTERMEDIATE LOGICAL SYMBOL WITH OWN RULES, WITH ITS OLDER DEFINITION CONTENT WHICH REWRITE TO THIS SYMBOL
symbol Productd'_functor_snd_funcd [U] T [X X' : catd U] (GG : funcd X Id_func X'):
funcd (Productd'_catd T X) Id_func (Productd'_catd T X') 
≔ Productd'_intro_funcd (Productd'_fst_funcd T X) ((Productd'_snd_funcd T X) ∘>d GG) ; 

 constant symbol Pi_intro_func : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y] (D : cat) 
(FF : funcd (Productdt_catd A D) F B), func D (Pi_cat A F B);
constant symbol Pi_elim_funcd : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y] (D : cat) ,
 funcd (Productdt_catd A (Pi_cat A F B)) F B;

constant symbol Pid_intro_funcd : Π [X' X Y : cat] 
(K : func X X') [A : catd X]  [F : func X Y] [B : catd Y] (D : catd X') 
(FF : funcd (Productd'_catd A (Fibre_catd D K)) F B), funcd D Id_func (Pid_catd K A F B);

constant symbol Pid_intro_funcd' : Π [X' X Y : cat] 
(K : func X X') (A : catd X)  (F : func X Y) (B : catd Y) [X''] (D : catd X'') (L : func X'' X') 
(FF : funcd (Productd'_catd (Fibre_catd A (Pullback_snd_func L K)) (Fibre_catd D (Pullback_fst_func L K)))
  ((Pullback_snd_func L K) ∘> F) B), 
funcd D L (Pid_catd K A F B);

constant symbol Pid_elim_funcd : Π [X' X Y : cat] 
(K : func X X') (A : catd X)  (F : func X Y) (B : catd Y),
funcd (Productd'_catd A (Fibre_catd (Pid_catd K A F B) K)) F B;

// rule (Productd'_functor_snd_funcd $A (Fibre_functor_funcd (@Pid_intro_funcd _ _ _ $K $A $F $B $D $FF) $K)) ∘>d (Pid_elim_funcd $K $A $F $B) 
// ↪ $FF;


//TODO FIbre_intro and FIbre_elim  over comp and id
type λ [X' X Y : cat] 
[K : func X X'] [A : catd X]  [F : func X Y] [B : catd Y] (D : catd X') 
(FF : funcd (Productd'_catd A (Fibre_catd D K)) F B), 
(Productd'_functor_snd_funcd A (Fibre_functor_funcd (Pid_intro_funcd K D FF) K)) ∘>d (Pid_elim_funcd K A  F B ) ;

rule (Fibre_catd (Pid_catd $K $A $F $B) $L) ↪ 
(Pid_catd (Pullback_fst_func $L $K) (Fibre_catd $A (Pullback_snd_func $L $K)) 
   ((Pullback_snd_func $L $K) ∘> $F) $B);

// this require the above rewrite on fibre of pid
type λ [X' X Y : cat] 
(K : func X X') [A : catd X]  [F : func X Y] [B : catd Y] [X''] (D : catd X'') (L : func X'' X') 
(FF : funcd (Productd'_catd (Fibre_catd A (Pullback_snd_func L K)) (Fibre_catd D (Pullback_fst_func L K)))
  ((Pullback_snd_func L K) ∘> F) B), 
(Productd'_functor_snd_funcd (Fibre_catd  A (Pullback_snd_func  L  K)) (Fibre_functor_funcd (Pid_intro_funcd' K A F B D L FF) (Pullback_fst_func  L  K)))  ∘>d 
(Pid_elim_funcd (Pullback_fst_func  L  K) (Fibre_catd  A (Pullback_snd_func  L  K)) ((Pullback_snd_func L K) ∘> F) B ) ;


rule Fibre_elim_funcd $A Id_func ↪ Id_funcd
// reverse direction?
//with (Fibre_elim_funcd (Fibre_catd $A $y) $x) ∘>d Fibre_elim_funcd $A $y  ↪ Fibre_elim_funcd $A ($x ∘> $y)
with Fibre_elim_funcd $A ($x ∘> $y) ↪ (Fibre_elim_funcd (Fibre_catd $A $y) $x) ∘>d Fibre_elim_funcd $A $y 
with Fibre_elim_funcd (Triv_catd _) _ ↪ (Triv_funcd _);

rule Fibre_intro_funcd $A Id_func $i $FF ↪ $FF
// reverse direction?
// with (Fibre_intro_funcd (Fibre_catd $A $y) $x $i (Fibre_intro_funcd $A $y ($i ∘> $x) $FF)) 
// ↪  (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
with (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
↪ (Fibre_intro_funcd (Fibre_catd $A $y) $x $i (Fibre_intro_funcd $A $y ($i ∘> $x) $FF));

rule $H ∘>d (Productd'_intro_funcd $F $G) ↪ (Productd'_intro_funcd ($H ∘>d $F) ($H ∘>d $G));
rule (@Productd'_intro_funcd _ $T $X _ _ _ $F $G) ∘>d (Productd'_fst_funcd $T $X) ↪ $F  
with (@Productd'_intro_funcd _ $T $X _ _ _ $F $G) ∘>d (Productd'_snd_funcd $T $X) ↪ $G  ;



//HERE ERASE? SLOW
//rule @Fibre_intro_funcd $X $X _ $A (@Id_func $X) _ $F $MM ↪ $MM;

 // naturality
 rule (Fibre_elim_funcd (Fibre_catd $BB $y) $zz) ∘>d (@Comma_con_intro_funcd' _ _ _ _ $BB _ $y $r) 
   ↪ (Comma_con_intro_funcd' $BB ($r ∘↓ $zz));
 rule (Fibre_elim_funcd (Fibre_catd $AA $x) $zz) ∘>d (@Comma_cov_intro_funcd' _ _ _ $AA _  $x _ $r) 
  ↪ (Comma_cov_intro_funcd' $AA ($r ∘↓ $zz));
 
 //TODO: REVIEW, or reverse, conversion on non-constant Triv_funcd instead?
 rule Triv_funcd ($F ∘> $G) ↪ (Triv_funcd $F) ∘>d (Triv_funcd $G)  //TODO accumulator version of Triv_funcd?
 with  (Triv_funcd Id_func) ↪ Id_funcd; //note in fact the left is section so both lacked, and no need for convertibility
  
 rule (Fibre_intro_funcd $A $x _ $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF ;
 rule $HH ∘>d (Fibre_intro_funcd $A $x _ $FF) ↪ (Fibre_intro_funcd $A $x _ ($HH ∘>d $FF)) ;
 
//  rule (Fibre_intro_funcd' $A $x $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF ;
//FAILS INDEED: rule $HH ∘>d (Fibre_intro_funcd' $A $x $FF) ↪ (Fibre_intro_funcd' $A $x ($HH ∘>d $FF)) ;

//TODO: REVIEW SLOW
//rule (@Fibre_intro_funcd $X $I $I $A $x (Fibre_catd $A $x) (@Id_func $I) (Fibre_elim_funcd $A $x))  ↪ @Id_funcd _ (Fibre_catd $A $x) ;

 rule $F ∘> (Universe_con_func $A $A_isf)  ↪ (Universe_con_func (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));
 rule (Fibre_elim_funcd $A $F) ∘>d (Universe_con_funcd $A $A_isf)  ↪ (Universe_con_funcd (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));

 rule (Universe_con_func (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F))  ↪ $F;
 rule (Universe_con_funcd (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F))  ↪ Fibre_elim_funcd Universe_con_catd $F;
 
 //strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
 rule (Fibre_catd Universe_con_catd (Universe_con_func $A _))  ↪ $A;
 rule (Fibre_elim_funcd Universe_con_catd (Universe_con_func $A $A_isf))  ↪ (Universe_con_funcd $A $A_isf);

 //note: these below are copy-paste replace _con_ by _cov_
 rule $F ∘> (Universe_cov_func $A $A_isf)  ↪ (Universe_cov_func (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));
 rule (Fibre_elim_funcd $A $F) ∘>d (Universe_cov_funcd $A $A_isf)  ↪ (Universe_cov_funcd (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));

 rule (Universe_cov_func (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F))  ↪ $F;
 rule (Universe_cov_funcd (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F))  ↪ Fibre_elim_funcd Universe_cov_catd $F;
 
 //strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
 rule (Fibre_catd Universe_cov_catd (Universe_cov_func $A _))  ↪ $A;
 rule (Fibre_elim_funcd Universe_cov_catd (Universe_cov_func $A $A_isf))  ↪ (Universe_cov_funcd $A $A_isf);


symbol Total_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
funcd A xy B → Π [X'] (x : func X' X), func (Total_cat A x) (Total_cat B (x ∘> xy));

rule (@Total_func _ _ $A $B $F $FF $X' $x) ∘> (@Total_proj_func _ $B $X' $x ) ↪ (Total_proj_func $A $x) ;

rule Total_func (Id_funcd) _  ↪ Id_func
with Total_func (Fibre_elim_funcd $A $F) _ ↪ Id_func

//this  Total_func of @∘>d requires above earlier Pullback_cat reversal of rewrite direction and symmetric versions of rewrites
with Total_func ( @∘>d _ _ _ $A $B $C $F $G $FF $GG) $x ↪ 
   (Total_func $FF $x) ∘> (Total_func $GG ($x ∘> $F))
 
with Total_func (Triv_funcd $F) _ ↪ Id_func
//todo problem with @Total_func _ _ _ _ _ (Product_funcd $A $F) $A' $x ↪ Total_func (Product_funcd $A' $F) Id_func
//nope more general 
//with Total_func (SigmaIntro_funcd $Z $F) ↪ (Id_func)
;

//this should use the intro over Id so that the _ is inferred otherwise inconsistent...
// rule Total_func ( Fibre_intro_funcd $C _ Id_func (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
// ↪ (Pullback_functor_func ($K ∘> $F) (Total_proj_func (Fibre_catd $C $G)) (Total_func $GG))  ;
rule Total_func ( Fibre_intro_funcd $C _ Id_func (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
↪ (Total_func $GG ($K ∘> $F))  ;
rule Total_func ( Fibre_intro_funcd $C $G $F (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
↪ (Total_func $GG ($K ∘> $F))  ;

 
 //TODO: erase, instead declare their Total_func $FF $u as isFuncEquiv
 constant symbol  Id_funcd_isEquiv : Π [X : cat] [A : catd X], isEquiv (@Id_funcd _ A);
 constant symbol Sigma_isEquiv : Π [Y X : cat] (Z : catd Y) (F : func Y X), isEquiv (SigmaIntro_funcd Z F);
 
 
 /* (d) modd moddu ========================== */

 injective symbol Op_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B), modd (Op_catd B) (Op_mod R) (Op_catd A);
 
 injective symbol Op_moddu : Π [I : cat] [A : catd I] [B : catd I]
 (RR : moddu A B), moddu (Op_catd B) (Op_catd A);

constant symbol Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] 
[XX : catd X] [YY : catd Y] [II : catd I] (F : funcd XX xi II)  (G : funcd YY yi II), 
modd XX (Unit_mod xi yi) YY;

 constant symbol Unit_moddu : Π [I : cat] [XX : catd I] [YY : catd I] [II : catd I]
 (F : funcd XX Id_func II) (G : funcd YY Id_func II), 
 moddu XX YY;
 
 constant symbol Triv_modd : Π [X Y : cat] (R : mod X Y) ,
 modd (Triv_catd X) R (Triv_catd Y);
 
 constant symbol Triv_moddu : Π (X : cat), moddu (Triv_catd X) (Triv_catd X);
 
 //example of fibred profunctor: squares fibred by their diagonal
 constant symbol Comma_modd' : Π [A B : cat] (AA : catd A) (R : mod A B) (BB : catd B),
    modd (Comma_con_catd' R BB) R (Comma_cov_catd' AA R);
 
 
 symbol Fibre_func_moddu : Π [I: cat] [A : catd I] [B : catd I] (RR : moddu A B),
  Π [J: cat] (i : func J I), moddu (Fibre_catd A i) (Fibre_catd B i);
 
 rule Fibre_func_moddu $A Id_func ↪ $A
 with Fibre_func_moddu $A ($x ∘> $y)  ↪ Fibre_func_moddu (Fibre_func_moddu $A $y) $x
with Fibre_func_moddu (Unit_moddu $FF $GG) $F ↪ Unit_moddu (Fibre_functor_funcd $FF $F) (Fibre_functor_funcd $GG $F)
with Fibre_func_moddu (Triv_moddu _) $F ↪ Triv_moddu _;
 
 //TODO: REVIEW this, use instead Fibre_functor_funcd ? yep
 // symbol Fibre_homdu : Π [I: cat] [A : catd I] [B : catd I] [II: catd I] 
 // [FF : funchd II A] [RR : moddu A B] [GG : funchd II B],
 // homdu FF RR GG →  Π [J: cat] (i : func J I),
 // homdu (Fibre_funchd FF i)  (Fibre_func_moddu RR i) (Fibre_funchd GG i) ;
 
 symbol Fibre_transf_modd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [S : mod X' Y'] [x : func X' X] [y : func Y' Y], transf S x R y → 
  modd (Fibre_catd A x) S (Fibre_catd B y);
 
 rule Fibre_transf_modd $A (Id_transf _) ↪ $A
 with Fibre_transf_modd $A ($x ''∘ $y)  ↪ Fibre_transf_modd (Fibre_transf_modd $A $y) $x
 with Fibre_transf_modd (Triv_modd _) $F ↪ Triv_modd _ ;
 
 
 symbol Fibre_hom_moddu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [x : func I X] [y : func I Y], hom x R y → 
  moddu (Fibre_catd A x) (Fibre_catd B y);
 
rule  Fibre_hom_moddu (Unit_modd $FF $GG) (Id_hom $F) ↪ Unit_moddu (Fibre_functor_funcd $FF $F) (Fibre_functor_funcd $GG $F)
with Fibre_hom_moddu $A ($r ∘↓ $F)  ↪ Fibre_func_moddu (Fibre_hom_moddu $A $r) $F
 with Fibre_hom_moddu (Triv_modd _) $r ↪ Triv_moddu _ ;

  
 constant symbol Sheaf_con_mod : Π [A B : cat], mod A B → mod A B;
 

constant symbol Productdt_moddu : Π [T : cat] (TT : catd T) [X Y : cat] (R : mod X Y), moddu (Productdt_catd TT X) (Productdt_catd TT Y);
  
constant symbol  Productdt_modd : Π [A B : cat] [T : mod A B] [AA : catd A] [BB : catd B] (TT : modd AA T BB) [X Y : cat] (R : mod X Y), modd (Productdt_catd AA X) T (Productdt_catd BB Y);
 
 
 constant symbol ⊗d : Π [A B X : cat] [AA : catd A][BB : catd B][XX : catd X]
  [R :mod A B] [S :mod B X], modd AA R BB → modd BB S XX →
  modd AA ((⊗) R S) XX;  //Tensor_modd;
 notation ⊗d infix left 70;
 
 
 constant symbol Sheaf_con_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → modd A R B;
 
 //Subst_cov_modd
 symbol d<<∘ : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], modd AA R BB → Π [B' : cat] [b : func B' B] [BB' : catd B'], funcd BB' b BB → modd AA (R <<∘ b) BB';
 //Subst_con_modd
 symbol ∘>>d : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], Π [A' : cat] [a : func A' A] [AA' : catd A'], funcd AA' a AA →  modd AA R BB →  modd AA' (a ∘>> R) BB;
 //Subst_cov_moddu
 symbol du<<∘ : Π [I : cat] [AA : catd I] [BB : catd I], moddu AA BB → Π [BB' : catd I], funcd BB' Id_func BB → moddu AA BB';
 //Subst_con_moddu
 symbol ∘>>du : Π [I : cat] [AA : catd I] [BB : catd I], Π [AA' : catd I], funcd AA' Id_func AA →  moddu AA BB →  moddu AA' BB;
 notation d<<∘ infix left 80; notation ∘>>d infix right 80;
 notation du<<∘ infix left 80; notation ∘>>du infix right 80;
 
  
 rule $R d<<∘ Id_funcd ↪ $R 
// with $R d<<∘ ($H d<∘ $K)  ↪ ($R d<<∘ $H) d<<∘ $K;
  with ($R d<<∘ $H) d<<∘ $K ↪ $R d<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>d $R ↪ $R 
// with ($K ∘>d $H) ∘>>d $R ↪ $K ∘>>d ($H ∘>>d $R);  
  with $K ∘>>d ($H ∘>>d $R) ↪ ($K ∘>d $H) ∘>>d $R; 
 
 rule ($F ∘>>d $R) d<<∘ $G ↪ ($F ∘>>d ($R d<<∘ $G));

rule  (Unit_modd $F $G) d<<∘ $K ↪ Unit_modd $F ($G d<∘ $K) 
with $K ∘>>d (Unit_modd $F $G) ↪ Unit_modd ($K ∘>d $F) $G ;

 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));

 rule $R du<<∘ Id_funcd ↪ $R 
// with $R du<<∘ ($K ∘>d $H ) ↪ ($R du<<∘ $H) du<<∘ $K; // error ∘>d is not manifestly over Id_func
  with ($R du<<∘ $H) du<<∘ $K ↪ $R du<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>du $R ↪ $R 
// with ($K ∘>d $H) ∘>>du $R ↪ $K ∘>>du ($H ∘>>du $R); // error ∘>d is not manifestly over Id_func
  with $K ∘>>du ($H ∘>>du $R) ↪ ($K ∘>d $H) ∘>>du $R; 
 
 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));
 
 rule  (Unit_moddu $F $G) du<<∘ $K ↪ Unit_moddu $F ($G d<∘ $K) 
 with $K ∘>>du (Unit_moddu $F $G) ↪ Unit_moddu ($K ∘>d $F) $G ;
  
 
 rule Op_modd (Op_modd $RR) ↪ $RR
with Op_modd (Unit_modd $FF $GG) ↪   (Unit_modd (Op_funcd $GG) (Op_funcd $FF)) 
with Op_modd ( Triv_modd $R ) ↪   Triv_modd (Op_mod $R)
 with Op_modd ( Fibre_transf_modd $RR $sr ) ↪   Fibre_transf_modd (Op_modd $RR) (Op_transf $sr) 
 with Op_modd ( Productdt_modd $T  $R ) ↪   Productdt_modd (Op_modd $T)  (Op_mod $R) 
 with Op_modd ( $RR ⊗d $SS ) ↪   (Op_modd $SS) ⊗d (Op_modd $RR)   ;

rule Op_modd ($F ∘>>d $R)  ↪ ((Op_modd $R) d<<∘ (Op_funcd $F))
with Op_modd ($R d<<∘ $G)  ↪ ((Op_funcd $G) ∘>>d (Op_modd $R));

rule Op_moddu (Op_moddu $RR) ↪ $RR
// with Op_moddu (Unit_moddu0 $A) ↪   (Unit_moddu0 (Op_catd $A)) 
with Op_moddu (Unit_moddu $FF $GG) ↪   (Unit_moddu (Op_funcd $GG) (Op_funcd $FF)) 
with Op_moddu ( Triv_moddu $I ) ↪   Triv_moddu (Op_cat $I)
with Op_moddu ( Fibre_func_moddu $RR $i ) ↪   Fibre_func_moddu (Op_moddu $RR) (Op_func $i) 
with Op_moddu ( Fibre_hom_moddu $RR $r ) ↪   Fibre_hom_moddu (Op_modd $RR) (Op_hom $r) 
with Op_moddu ( Productdt_moddu $T  $R ) ↪   Productdt_moddu (Op_catd $T)  (Op_mod $R)  
;

rule Op_moddu ($F ∘>>du $R)  ↪ ((Op_moddu $R) du<<∘ (Op_funcd $F))
with Op_moddu ($R du<<∘ $G)  ↪ ((Op_funcd $G) ∘>>du (Op_moddu $R));

/* (e) homdd homddu ========================== */
 
injective symbol Op_homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
   [A : catd X] [B : catd Y] [II : catd I]  [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
   homd r FF RR GG →  homd (Op_hom r) (Op_funcd GG) (Op_modd RR) (Op_funcd FF); 

constant symbol Id_homd : Π [I X : cat] [xi : func X I]  [II : catd I] [XX] (F : funcd XX xi II) ,
homd  (Id_hom xi) F (Unit_modd Id_funcd Id_funcd) F;

 constant symbol Id_homdu : Π [I : cat] [A : catd I] [II] (F : funcd II Id_func A),
 homdu F (Unit_moddu Id_funcd Id_funcd) F;
 
 constant symbol Func_con_homd'' : Π [I X : cat] [F : func X I]  [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX F II),
homd  (Func_con_hom'' Z F)   FF (Unit_modd ZZ Id_funcd) (FF ∘>d ZZ) ;

constant symbol Func_cov_homd'' : Π [I X : cat] [xi : func X I]  [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX xi II),
homd  (Func_cov_hom'' Z xi)  (FF ∘>d ZZ) (Unit_modd Id_funcd ZZ) FF ;

 //Comp_funcd_homd
 symbol ∘↓d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
  homd r FF RR GG → Π [I'] [Z : func I' I] [I'I'] (ZZ : funcd I'I' Z II) ,
  homd (r ∘↓ Z) (ZZ ∘>d FF) RR (ZZ ∘>d GG);
 notation ∘↓d infix left 120;
 
 rule $r ∘↓d Id_funcd ↪ $r
 // with $r ∘↓d ($K ∘> $H  )  ↪ ($r ∘↓d $H) ∘↓d $K
 with ($r ∘↓d $H) ∘↓d $K  ↪ $r ∘↓d ($K ∘>d $H  )
 with (Id_homd $F) ∘↓d $H  ↪ Id_homd ($F d<∘ $H)
 with (Func_con_homd'' $Z $F) ∘↓d $H  ↪ Func_con_homd'' $Z ($F d<∘ $H)
 with (Func_cov_homd'' $Z $F) ∘↓d $H  ↪ Func_cov_homd'' $Z ($F d<∘ $H);
 
 rule Op_homd (Op_homd $F) ↪ $F
 with Op_homd (Id_homd $F) ↪ (Id_homd (Op_funcd $F))
 with Op_homd (Func_con_homd'' $Z $F) ↪ Func_cov_homd'' (Op_funcd $Z) (Op_funcd $F)
 with Op_homd (Func_cov_homd'' $Z $F) ↪ Func_con_homd'' (Op_funcd $Z) (Op_funcd $F); 
rule Op_homd ($r ∘↓d $H) ↪ (Op_homd $r) ∘↓d (Op_funcd $H); 

// /* (f) transfd transfdu ========================== */

 injective symbol Op_transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 [r : transf R xx' R' yy'] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
  transfd r RR FF RR' GG →  transfd (Op_transf r) (Op_modd RR) (Op_funcd GG) (Op_modd RR') (Op_funcd FF);
 
constant symbol Id_transfd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y] (RR : modd A R B),
 transfd (Id_transf R) RR Id_funcd RR Id_funcd;
  
constant symbol Triv_transfduu : Π (I : cat), transfduu (Triv_moddu I) Id_funcd (Triv_moddu I) Id_funcd; // is Id ?
 
 constant symbol Triv_transfd : Π [A' B' A B: cat] [R' : mod A' B'] [F : func A' A] [R : mod A B] [G : func B' B]
 (r'r : transf R' F R G),  transfd r'r (Triv_modd R') (Triv_funcd F) (Triv_modd R) (Triv_funcd G)    ;
 
 
  //Unit_con_transfd
 constant symbol _'∘>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
  Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), 
 homd r FF RR GG → transfd ((M)_'∘> r) (Unit_modd MM FF) Id_funcd (MM ∘>>d RR) GG; 
 notation _'∘>d infix right 80; 

 constant symbol ∘>d'_ : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
 homd r FF RR GG → Π [J: cat] [M : func J Y] [JJ : catd J] (MM : funcd JJ M B), 
 transfd ( r ∘>'_(M) ) (Unit_modd GG MM) FF (RR d<<∘ MM ) Id_funcd;                
 notation ∘>d'_ infix left 80;
 
 rule Op_transfd (Op_transfd $rr) ↪ $rr
 with Op_transfd (Id_transfd $RR) ↪ (Id_transfd (Op_modd $RR))
 with Op_transfd (($MM)_'∘>d $rr) ↪ (Op_homd $rr) ∘>d'_ (Op_funcd $MM);
 rule Op_transfd ($rr ∘>d'_ ($MM)) ↪ (Op_funcd $MM) _'∘>d (Op_homd $rr);
 
 
 //Unit_con_transfdu
 constant symbol _'∘>du : Π [I: cat] [A : catd I] [B : catd I] [II]
 [FF : funcd II Id_func A] [RR : moddu A B] [GG : funcd II Id_func B], 
 Π [JJ : catd I] (MM : funcd JJ Id_func A),
 homdu FF RR GG → transfduu (Unit_moddu MM FF) Id_funcd (MM ∘>>du RR) GG;
 notation _'∘>du infix right 80; 
 
 
 //Comp_homd_transfd
 symbol '∘d : Π [A'' A' B' A B : cat] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func A'' B'] [F : func A' A] [G : func B' B],
 Π [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB'] [TT : modd AA T BB] [t : transf S F T G]
 [A''A''] [XX : funcd A''A'' X AA'] [YY : funcd A''A'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB]  [s : hom X S Y],
 homd s XX SS YY → transfd t SS FF TT GG → homd (s '∘ t) (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘d infix right 80;

 symbol ∘d' [A'' A' B' A B : cat] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func A'' B'] [F : func A' A] [G : func B' B]
 [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB'] [TT : modd AA T BB] [t : transf S F T G]
 [A''A''] [XX : funcd A''A'' X AA'] [YY : funcd A''A'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB]  [s : hom X S Y]:
transfd t SS FF TT GG →  homd s XX SS YY →  homd (s '∘ t) (XX ∘>d FF) TT (YY ∘>d GG)
≔ λ st s, s '∘d st;
 notation ∘d' infix left 80;


rule Op_homd ($s '∘d $st) ↪ (Op_homd $s) '∘d (Op_transfd $st);

//TODO: REVIEW //SEE RULE somewhere in reverse
rule ($a '∘d  $t) ∘↓d $Z ↪ (($a ∘↓d $Z) '∘d  $t) ; 

 //Comp_homdu_transfduu
 symbol '∘duduu : Π [A : cat] ,
 Π [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [SS : moddu AA' BB'] [TT : moddu AA BB] 
 [AA0] [XX : funcd AA0 Id_func AA'] [YY : funcd AA0 Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
 homdu XX SS YY → transfduu SS FF TT GG → homdu (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘duduu infix right 80;
 
 
 //Comp_transfduu_transfduu
 symbol ''∘duuduu : Π [ A : cat]
 [AA'' : catd A] [BB'' : catd A] [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [RR : moddu AA'' BB''] [SS : moddu AA' BB'] [TT : moddu AA BB] 
 [XX : funcd AA'' Id_func AA'] [YY : funcd BB'' Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
 transfduu RR XX SS YY → transfduu SS FF TT GG → transfduu RR (XX ∘>d FF) TT (YY ∘>d GG);
 notation ''∘duuduu infix right 80;
 
//Comp_transfd
symbol ''∘d : Π [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
[X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B],
Π [AA'' : catd A''] [BB'' : catd B''] [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B]  [s : transf R X S Y] [RR : modd AA'' R BB''] [t : transf S F T G] [SS : modd AA' S BB'] [TT : modd AA T BB] 
[XX : funcd AA'' X AA'] [YY : funcd BB'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB],
transfd s RR XX SS YY → transfd t SS FF TT GG → transfd (s ''∘ t) RR (XX ∘>d FF) TT (YY ∘>d GG);
notation ''∘d infix right 80;

rule Op_transfd ($rs ''∘d $st) ↪ (Op_transfd $rs) ''∘d (Op_transfd $st);

 

 
//  /* (7) fibrations: semantics ========================== */
 

// next adjust

//  //lacked? could use Total_func
//  //todo: del
//  // symbol Total_funchd_func : Π [X : cat] [A : catd X] [B : catd X],
//  //  funchd A B → func (Total_cat A) (Total_cat B);
 
//  symbol Total_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
//   modd A R B → Π [X'] [x : func X' X] [Y'] [y : func Y' Y] [S : mod X' Y'] (r : transf S x R y), mod (Total_cat A x) (Total_cat B y);
 
//  symbol Total_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
//   (RR : modd A R B), Π [X'] [x : func X' X] [Y'] [y : func Y' Y] [S : mod X' Y'] (r : transf S x R y), transf (Total_mod RR r) (Total_proj_func A x Id_func) S (Total_proj_func B y Id_func);
 
//  symbol Total_hom_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
//  modd A R B → Π [I] [I'] (i : func I' I) [x : func I X]  [y : func I Y] (r : hom x R y), 
//  mod (Total_cat A (i ∘> x)) (Total_cat B (i ∘> y));
//  //TODO Total_hom_modd_proj_transf  ??
 
//  rule Total_hom_mod $648696 ($648732 ∘> $648728) $648712 ↪ Total_hom_mod $648696 $648732 ($648712 ∘↓ $648728);

//  symbol Total_hom_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
//  (RR : modd A R B), Π [I] [I'] (i : func I' I) [x : func I X]  [y : func I Y] (r : hom x R y), 
//  transf (Total_hom_mod RR i r) (Total_proj_func A (i ∘> x) (i ∘> x)) R (Total_proj_func B (i ∘> y) (i ∘> y));
 
//  symbol Total_moddu_mod : Π [I : cat] [A : catd I] [B : catd I],
//   moddu A B → Π [I'] (i : func I' I) , mod (Total_cat A i) (Total_cat B i);
 
 
//  //lacked? could use Total_modd_proj_transf
// //  symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
// //  (RR : moddu A B), Π [I'] (i : func I' I), transf (Total_moddu_mod RR i) (Total_proj_func A i Id_func) (Unit_mod0 I') (Total_proj_func B i Id_func);
// symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
// (RR : moddu A B), Π [I'] (i : func I' I), 
// transf (Total_moddu_mod RR i) (Total_proj_func A i Id_func) (Unit_mod Id_func Id_func) (Total_proj_func B i Id_func);

// //  symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
// //   [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B],
// //  homd r FF RR GG  → Π [I'] (i : func I' I), hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);
//  symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
//   [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
//  homd r FF RR GG  → //Π [I'] [i : func I' I][I'I'] (ii : funcd I'I' i II), 
//  Π [I'] (i : func I' I), 
//  hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);
// //  symbol Total_hom' : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
// //   [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
// //  homd r FF RR GG  → Π [I'] [i : func I' I][I'I'] (ii : funcd I'I' i II), 
// //  hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);
 
// //  symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
// //  [FF : funcd (Triv_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Triv_catd I) Id_func B], homdu FF RR GG → Π [I'] (i : func I' I), 
// //  hom (Total_func FF i) (Total_moddu_mod RR i) (Total_func GG i);
//  symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
//  [II] [FF : funcd II Id_func A] [RR : moddu A B] [GG : funcd II Id_func B], homdu FF RR GG → Π [I'] (i : func I' I), 
//  hom (Total_func FF i) (Total_moddu_mod RR i) (Total_func GG i);
 
// //  symbol Total_transf: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
// //  [t : transf R xx' R' yy' ] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'] ,
// //  transfd t RR FF RR' GG → transf (Total_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);
 
// //  // symbol Total_transfdu_transf : Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [xx' : func I X'] [yy' : func I Y'] [R' : mod X' Y']
// //  // [r : hom xx' R' yy' ] [RR : moddu A B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B' ],
// //  // transfdu r RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);
 
// //  //com
// // //  symbol Total_transfduu_transf : Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I]
// // //  [RR : moddu A B] [FF : funcd A Id_func A'] [RR' : moddu A' B'] [GG : funcd B Id_func B'],
// // //  transfduu RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_moddu_mod RR') (Total_func GG);
 
 
// //  // symbol FibreProj_func : Π [X I : cat] (A : catd X) (x : func I X), func (Total_cat (Fibre_catd A x)) (Total_cat A);
// //  // rule (Total_func (Fibre_elim_funcd $A $x))  ↪ Id_func 
// //  // with (Total_func (Fibre_intro_funcd' $A $x $FF))  ↪ (Total_func $FF) ;
 
 

 

 
// //  rule Total_moddu_mod (Triv_moddu $I) $i ↪ (Unit_mod0 _)
// rule Total_moddu_mod (Triv_moddu $I) $i ↪ (Unit_mod Id_func Id_func)
// //TODO with Total_moddu_mod (Productdt_moddu $R) Id_func ↪ $R
//  //with Total_moddu_mod (Unit_moddu $F $G) ↪ (Unit_mod (Total_func $F) (Total_func $G));
// //  with Total_moddu_mod (Unit_moddu0 $AA) $i ↪ (Unit_mod0 (Total_cat $AA $i))
// with Total_moddu_mod (Unit_moddu0 $AA) $i ↪ (Unit_mod (@Id_func (Total_cat $AA $i)) Id_func)
// with  Total_moddu_mod ($FF ∘>>du $RR) $i ↪ (Total_func $FF $i) ∘>> (Total_moddu_mod $RR $i)
//  with  Total_moddu_mod ($RR du<<∘ $GG ) $i ↪ (Total_moddu_mod $RR $i) <<∘ (Total_func $GG $i);
 
// //  rule Total_moddu_proj_transf (Triv_moddu $X) $i ↪ (Id_transf (Unit_mod0 _))
// rule Total_moddu_proj_transf (Triv_moddu $X) $i ↪ (Id_transf (Unit_mod Id_func Id_func))
// //TODO with Total_moddu_proj_transf (Productdt_moddu $R) Id_func ↪ (Terminal_transf $R)
//  ;
 
//  rule @Total_mod _ _ _ _ _ (Triv_modd $R) _ _ _ _ $S $r ↪ $S
//  //with Total_mod (Unit_modd $FF $GG) ↪ (Unit_mod (Total_func $FF) (Total_func $GG))
//  //with Total_mod (Unit_modd0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
//  //with Total_mod (Comma_modd $R) ↪ (Comma_mod $R)
//  with Total_mod ($R ⊗d $S) (Tensor_cov_transf  $p $q) ↪ (Total_mod $R $p) ⊗ (Total_mod $S $q)
//  //with  Total_mod ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR)
//  //with  Total_mod ($RR d<<∘ $GG ) ↪ (Total_mod $RR) <<∘ (Total_func $GG)
//  ;
 
//  rule Total_modd_proj_transf (Triv_modd $R) $r ↪ (Id_transf _)
//  //with Total_modd_proj_transf (Comma_modd $R) ↪ (Comma_transf $R)
//  //.?with  Total_mod_proj ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR);
//  ;
 
 
// //  rule Total_hom_mod (Unit_modd0 $AA)  $i (Id_hom $F) ↪ (Unit_mod0 (Total_cat $AA ($i ∘> $F)));
// // rule Total_hom_mod (Unit_modd0 $AA)  $i (Id_hom $F) ↪ (Unit_mod  (@Id_func (Total_cat $AA ($i ∘> $F))) Id_func );
// rule Total_hom_mod (Unit_modd (@Id_funcd _ $AA) Id_funcd)  $i (Id_hom $F) 
//    ↪ (Unit_mod  (@Id_func (Total_cat $AA ($i ∘> $F))) Id_func );

//  //k====kjkkdd=====kjd
 
// //  type λ [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
// //  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B]
// //  (rr :homd r FF RR GG)  [I'] (i : func I' I), (@Total_hom _ _ _ _ _ _ r _ _ _ RR _  rr _ i) '∘ (Total_hom_modd_proj_transf RR (r ∘↓ i));
//  //dkd=====kddddkd

// //   rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr _ $i) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
// //   ($r ∘↓ $i);
// rule (@Total_hom _ _ _ _ _ _ $r _ _ $II _ $RR _ $rr _ $i ) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
// ($r ∘↓ (Total_proj_func $II $i $i  ));
// // rule (@Total_hom' _ _ _ _ _ _ $r _ _ $II _ $RR _ $rr _ $i $I'I' $ii ) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
// // ($r ∘↓ (Total_proj_func $I'I' Id_func $i  ));

//  //rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr) '∘ (Total_modd_proj_transf $RR) ↪  $r;==
 
// //  rule //Total_hom (Comma_homd $r) ↪ Comma_hom $r
// //   Total_hom ($rr ∘↓d $Z) $i ↪ (Total_hom $rr ($i ∘> $Z)) ;
// rule //Total_hom (Comma_homd $r) ↪ Comma_hom $r
// Total_hom ($rr ∘↓d (Triv_funcd $Z)) $i ↪ (Total_hom $rr ($i ∘> $Z)) ;

//  rule Total_hom (Id_homd $F) $i ↪ Id_hom (Total_func $F $i);
 
//  //rule (@Total_homdu_hom $I _ _ _ $RR _ $rr _  $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Id_hom Id_func;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?
 
// //  rule (@Total_homdu_hom $I _ _ _ _$RR _ $rr _ $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Id_hom Id_func;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?
//   rule (@Total_homdu_hom $I _ _ $II _ $RR _ $rr _ $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Id_hom (Total_proj_func $II $i Id_func);//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?

//  rule Total_homdu_hom (Id_homdu $F)$i ↪ Id_hom (Total_func $F $i);
 
 
 
 
 
 
 
// //  ///---
 
 
 
// //  rule (@Total_transf _ _ _ _ _ _ _ _ _ _ _ _ $rr' $RR _ $RR' _ $rrr'r') ''∘ (Total_modd_proj_transf $RR') ↪ (Total_modd_proj_transf $RR) ''∘ $rr';
 
// //  //Unit_mod Id_func (Total_func $59302320) ≡ Total_mod (Unit_modd Id_funcd $59302320)
// //  rule Total_transf ( ($MM)_'∘>d $rr) ↪ (Total_func $MM)_'∘> (Total_hom $rr);
// //  rule Total_transf ($rs ''∘d $st) ↪ (Total_transf $rs) ''∘ (Total_transf $st);
// //  rule Total_transfduu_transf ($rs ''∘duuduu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfduu_transf $st);
// //  // rule Total_transfdu_transf ($rs ''∘duudu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfdu_transf $st);
// //  // rule Total_transfdu_transf ($rs ''∘dud $st) ↪ (Total_transfdu_transf $rs) ''∘ (Total_transf $st);
 
// //  // todo: Total_hom of homdu applied/Comp_homd onto transfdu
// //  // todo: postpone Total_transf of  Comp_transfd or act_transfd 
 
// //  // symbol Fibre_transfd_transfdu : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
// //  //  [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
// //  // transfd RR FF RR' GG → 
// //  // Π [I : cat] [G : func I Y] [F : func I X] (r : hom F R G), 
// //  // transfdu (Fibre_hom_moddu RR r) (Fibre_elim_funcd F FF) RR' (Fibre_elim_funcd G GG);
 
 
// //  //todo review this or add Proj_transfduu ?
// //  // symbol Proj_transfdu : Π [X Y : cat] [A : catd X] [B: catd Y] [R : mod X Y]
// //  // [RR : modd A R B], Π [I : cat] [G : func I Y] [F : func I X] (r : hom F R G), 
// //  // transfdu r (Fibre_hom_moddu RR r) (Fibre_elim_funcd  _ F) RR (Fibre_elim_funcd _ G);
 
// //  // symbol Fibre_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
// //  //  [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
// //  // transfd RR FF RR' GG → 
// //  // Π [X0 Y0 : cat] [S : mod X0 Y0] [G : func Y0 Y] [F : func X0 X] (t : transf S F R G), 
// //  // transfd (Fibre_transf_modd RR t) (Fibre_elim_funcd F FF) RR' (Fibre_elim_funcd G GG);
 
// //  symbol Proj_transfd : Π [X Y : cat] [A : catd X] [B: catd Y] [R : mod X Y]
// //  [RR : modd A R B], Π [X0 Y0 : cat] [S : mod X0 Y0] [G : func Y0 Y] [F : func X0 X] (t : transf S F R G), 
// //  transfd t (Fibre_transf_modd RR t) (Fibre_elim_funcd _ F) RR (Fibre_elim_funcd _ G); 
 
 
 
 
// //  constant symbol Unit_transf : Π [I X Y : cat] [xi $yi: func X I] [yi : func Y I] [II : catd I]
// //    (F : funcd (Triv_catd X) xi II) (G : funcd (Triv_catd Y) yi II), 
// //   transf (Unit_mod (Total_func F) (Total_func G)) Id_func (Unit_mod xi yi) Id_func;




/// OLD TOTAL


// /* (7) fibrations: semantics ========================== */

// // other defined operations via induction-recursion

// symbol Total_cat : Π [X : cat], catd X → cat;

// //todo: allow explicit accumulator argument?
// symbol Total_proj_func : Π [X : cat] (A : catd X), func (Total_cat A) X;

// // symbol Total_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
// //  funcd A xy B → func (Total_cat A) (Total_cat B);

// symbol Total_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
// funcd A xy B → func (Total_cat A) (Total_cat (Fibre_catd B xy));

// //lacked? could use Total_func
// //todo: del
// // symbol Total_funchd_func : Π [X : cat] [A : catd X] [B : catd X],
// //  funchd A B → func (Total_cat A) (Total_cat B);

// symbol Total_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
//  modd A R B → mod (Total_cat A) (Total_cat B);

// symbol Total_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
//  (RR : modd A R B), transf (Total_mod RR) (Total_proj_func A) R (Total_proj_func B);

// symbol Total_moddu_mod : Π [I : cat] [A : catd I] [B : catd I],
//  moddu A B → mod (Total_cat A) (Total_cat B);

// //lacked? could use Total_modd_proj_transf
// symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
// (RR : moddu A B), transf (Total_moddu_mod RR) (Total_proj_func A) (Unit_mod0 _) (Total_proj_func B);

// symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
//  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B],
// homd r FF RR GG  → hom (Total_func FF) (Total_mod RR) (Total_func GG);

// symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
// [FF : funcd (Triv_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Triv_catd I) Id_func B], homdu FF RR GG →
// hom (Total_func FF) (Total_moddu_mod RR) (Total_func GG);

// symbol Total_transf: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
// [t : transf R xx' R' yy' ] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'] ,
// transfd t RR FF RR' GG → transf (Total_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);

// // symbol Total_transfdu_transf : Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [xx' : func I X'] [yy' : func I Y'] [R' : mod X' Y']
// // [r : hom xx' R' yy' ] [RR : moddu A B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B' ],
// // transfdu r RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);

// symbol Total_transfduu_transf : Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I]
// [RR : moddu A B] [FF : funcd A Id_func A'] [RR' : moddu A' B'] [GG : funcd B Id_func B'],
// transfduu RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_moddu_mod RR') (Total_func GG);


// symbol FibreProj_func : Π [X I : cat] (A : catd X) (x : func I X), func (Total_cat (Fibre_catd A x)) (Total_cat A);
// rule (Total_func (FibreProj_funcd $A $x))  ↪ Id_func 
// with (Total_func (FibrePairing_funcd' $A $x $FF))  ↪ (Total_func $FF) ;


// rule Total_cat (Triv_catd $A) ↪ $A
// with Total_cat (Cast_catd $A) ↪ $A
// //with Total_cat (Fibre_catd $A $F) ↪ Fibre_cat $A $F  //should depend on particular catd
// // with Total_cat (Comma_con_catd $R) ↪ (Comma_cat $R)
// // with Total_cat (Comma_cov_catd $R) ↪ (Comma_cat $R)
// //nope more general 
// //with Total_cat (Sigma_catd $Z $F) ↪ (Total_cat $Z)
// ;

// rule Total_proj_func (Triv_catd $A) ↪ Id_func
// with Total_proj_func (Cast_catd $A) ↪ Terminal_func $A
// // with Total_proj_func (Comma_con_catd $R) ↪ (Comma_con_func $R)
// // with Total_proj_func (Comma_cov_catd $R) ↪ (Comma_cov_func $R)
// //nope more general 
// //with Total_proj_func (Sigma_catd $Z $F) ↪ (Total_proj_func $Z) ∘> $F
// ;

// //rule (@Total_func _ _ $A $B $F $FF) ∘> (Total_proj_func $B) ↪ (Total_proj_func $A) ∘> $F;
// rule (@Total_func _ _ $A $B $F $FF) ∘> (Total_proj_func (Fibre_catd $B $F)) ↪ (Total_proj_func $A);

// rule  Total_func ( @∘>d _ _ _ $A $B $C $F $G $FF $GG) ↪ (Total_func $FF) ∘> ((FibreProj_func $B $F) ∘> (Total_func $GG))
// ;

// rule Total_func (Id_funcd) ↪ Id_func
// // todo: postpone Total_func of  Comp_funcd or act_funcd 
// with Total_func ($FF ∘>d $GG) ↪ Total_func $FF ∘> ((Total_func (FibreProj_funcd _ _)) ∘> (Total_func $GG))
// with Total_func (Triv_funcd $F) ↪ $F
// with Total_func (Cast_funcd $F) ↪ $F
// with Total_func (Comma_con_funcd $r) ↪ (Comma_func $r)
// with Total_func (Comma_cov_funcd $r) ↪ (Comma_func $r)
// //nope more general 
// //with Total_func (SigmaIntro_funcd $Z $F) ↪ (Id_func)
// ;
// // todo Total_funchd_func  on inclusion

// //todo: del
// // rule Total_funchd_func (Id_funchd) ↪ Id_func;

// rule Total_moddu_mod (Triv_moddu $X) ↪ (Unit_mod Id_func Id_func)
// with Total_moddu_mod (Cast_moddu $R) ↪ $R
// //with Total_moddu_mod (Unit_moddu $F $G) ↪ (Unit_mod (Total_func $F) (Total_func $G));
// with Total_moddu_mod (Unit_moddu0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
// with  Total_moddu_mod ($FF ∘>>du $RR) ↪ (Total_func $FF) ∘>> (Total_moddu_mod $RR)
// with  Total_moddu_mod ($RR du<<∘ $GG ) ↪ (Total_moddu_mod $RR) <<∘ (Total_func $GG);

// rule Total_moddu_proj_transf (Triv_moddu $X) ↪ (Id_transf (Unit_mod Id_func Id_func))
// with Total_moddu_proj_transf (Cast_moddu $R) ↪ (Terminal_transf $R);

// rule Total_mod (Triv_modd $R) ↪ $R
// //with Total_mod (Unit_modd $FF $GG) ↪ (Unit_mod (Total_func $FF) (Total_func $GG))
// with Total_mod (Unit_modd0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
// with Total_mod (Comma_modd $R) ↪ (Comma_mod $R)
// with Total_mod ($R ⊗d $S) ↪ (Total_mod $R) ⊗ (Total_mod $S)
// with  Total_mod ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR)
// with  Total_mod ($RR d<<∘ $GG ) ↪ (Total_mod $RR) <<∘ (Total_func $GG);

// rule Total_modd_proj_transf (Triv_modd $R) ↪ (Id_transf $R)
// with Total_modd_proj_transf (Comma_modd $R) ↪ (Comma_transf $R)
// //.?with  Total_mod_proj ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR);
// ;

// rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr) '∘ (Total_modd_proj_transf $RR) ↪  $r;

// rule Total_hom (Comma_homd $r) ↪ Comma_hom $r
// with Total_hom ($rr ∘↓d $Z) ↪ (Total_hom $rr) ∘↓ $Z ;

// rule Total_hom (Id_homd $F) ↪ Id_hom (Total_func $F);

// rule (@Total_homdu_hom $I _ _ _ $RR _ $rr) '∘ (Total_moddu_proj_transf $RR) ↪  Id_hom Id_func;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?

// rule Total_homdu_hom (Id_homdu $F) ↪ Id_hom (Total_func $F);







// ///---



// rule (@Total_transf _ _ _ _ _ _ _ _ _ _ _ _ $rr' $RR _ $RR' _ $rrr'r') ''∘ (Total_modd_proj_transf $RR') ↪ (Total_modd_proj_transf $RR) ''∘ $rr';

// //Unit_mod Id_func (Total_func $59302320) ≡ Total_mod (Unit_modd Id_funcd $59302320)
// rule Total_transf ( ($MM)_'∘>d $rr) ↪ (Total_func $MM)_'∘> (Total_hom $rr);
// rule Total_transf ($rs ''∘d $st) ↪ (Total_transf $rs) ''∘ (Total_transf $st);
// rule Total_transfduu_transf ($rs ''∘duuduu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfduu_transf $st);
// // rule Total_transfdu_transf ($rs ''∘duudu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfdu_transf $st);
// // rule Total_transfdu_transf ($rs ''∘dud $st) ↪ (Total_transfdu_transf $rs) ''∘ (Total_transf $st);

// // todo: Total_hom of homdu applied/Comp_homd onto transfdu
// // todo: postpone Total_transf of  Comp_transfd or act_transfd 


 
// //  /* (8) fibrations: cartesian transport / fibred yoneda ========================== */

constant symbol Comma_con_homd' : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
Π [J] [x' : func J I]  [J0] [F : func J0 A] [x'x : func J J0] (x'x_ : hom x'x (Unit_mod F x) x') , 
homd ( x'x_ ) (Comma_con_intro_funcd' BB ( x'x_ '∘  ((F)_'∘> r) )) (Unit_modd (Comma_con_comp_funcd' R BB F) (Comma_con_intro_funcd' BB r)) (Fibre_elim_funcd (Fibre_catd BB y) x');
constant symbol Comma_cov_homd' : Π [A B I : cat] (AA : catd A) [R : mod A B]  [x : func I A] [y : func I B] (r : hom x R y),
Π [K] [y' : func K I]  [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y' (Unit_mod y G) y'y) ,
homd ( y'y_ ) (Fibre_elim_funcd (Fibre_catd AA x) y') (Unit_modd (Comma_cov_intro_funcd' AA r) (Comma_cov_comp_funcd' AA R G) ) (Comma_cov_intro_funcd' AA ( (r ∘>'_(G)) ∘' y'y_ ));

type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I]  [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J]  [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
  (((Comma_con_homd' BB (x'x_ '∘  ((F)_'∘> r)) x''x'_) ) '∘d  (( _ ) _'∘>d  (Comma_con_homd' BB r x'x_)))
       = ((Comma_con_homd' BB r (x''x'_ '∘  ((F')_'∘> x'x_ ))) ); 


//TODO: REVIEW NOPE, too general ?
//  .constant symbol Comma_homd' : Π [A B I : cat] (AA : catd A) [R : mod A B] (BB : catd B) 
// [x : func I A] [y : func I B],
// Π   [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
// Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
// Π  (s : hom x'x (F ∘>> R) y) (t : hom x (R <<∘ G) y'y) (r : hom x'x (F ∘>> (R <<∘ G)) y'y), 
// homd r (Comma_con_intro_funcd' BB s) 
// ((Comma_con_comp_funcd' R BB F) ∘>>d ((Comma_modd' AA R BB) d<<∘ (Comma_cov_comp_funcd' AA R G))) 
//  (Comma_cov_intro_funcd' AA t); //redo

 //example of fibred profunctor: squares fibred by their diagonal
constant symbol Comma_homd' : Π [A B I : cat] (R : mod A B) [x : func I A] [y : func I B],
Π   [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
Π  (s : hom x'x (F ∘>> R) y) (t : hom x (R <<∘ G) y'y) (r : hom x'x (F ∘>> (R <<∘ G)) y'y), 
π (( x'x_ '∘  ((F)_'∘> t) ) = r) → π (( (s ∘>'_(G)) ∘' y'y_ ) = r) → 
homd r (Comma_con_intro_funcd' (Triv_catd B) s) 
((Comma_con_comp_funcd' R (Triv_catd B) F) ∘>>d ((Comma_modd' (Triv_catd A) R (Triv_catd B)) d<<∘ (Comma_cov_comp_funcd' (Triv_catd A) R G))) 
 (Comma_cov_intro_funcd' (Triv_catd A) t); //redo

opaque symbol Comma_homd'_lemma1 : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
Π   [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
Π   (t : hom x R y) (r : hom x'x (F ∘>> R) y), 
Π   [K0] [F' : func K0 J0] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x'x) Id_func) , 
π (( x'x_ '∘  ((F)_'∘> t) ) = r) →  π (( ( x''x'_ '∘ ( (F')_'∘> x'x_)  ) '∘  ((_)_'∘> t) ) = (x''x'_ '∘ ((F')_'∘> r))) ≔
begin 
  assume _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; assume prf;
  rewrite left prf; reflexivity;
end;

opaque symbol Comma_homd'_lemma2 : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
Π  (s : hom x R y)  (r : hom x (R <<∘ G) y'y), 
Π   [K0] [F' : func K0 A] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x) Id_func) , 
π (( (s ∘>'_(G)) ∘' y'y_ ) = r) →  
π (( (( x''x'_ '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' y'y_  ) =  (x''x'_ '∘ ((F')_'∘> r))) ≔
begin 
  assume A B I R x y J1 G y'y y'y_ s r K0 F' x''x' x''x'_; assume prf;
  rewrite left prf; apply (associativity_con_metatheorem y'y_ s x''x'_);
end;

symbol todo_rule_Comma_homd'_Comma_con_homd' ≔ λ [A B I : cat]  (R : mod A B)  [x : func I A] [y : func I B],
λ   [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
λ   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
λ  (s : hom x'x (F ∘>> R) y) (t : hom x (R <<∘ G) y'y) (r : hom x'x (F ∘>> (R <<∘ G)) y'y), 
λ   [K0] [F' : func K0 J0] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x'x) Id_func) , 
λ (prf : π (( x'x_ '∘  ((F)_'∘> t) ) = r) ) (prf2 : π (( (s ∘>'_(G)) ∘' y'y_ ) = r)),
 (Comma_con_homd' (Triv_catd B) s x''x'_ )  '∘d 
   (( _ ) _'∘>d (Comma_homd' R x'x_ y'y_ s t r ) prf prf2)
= (Comma_homd' R ( x''x'_ '∘ ( (F')_'∘> x'x_)  ) y'y_ (x''x'_ '∘ ((F')_'∘> s)) t (x''x'_ '∘ ((F')_'∘> r)) 
     (Comma_homd'_lemma1 x'x_ t r x''x'_ prf) 
     (Comma_homd'_lemma2 y'y_ s  r x''x'_ prf2) );

 
constant symbol Comma_con_elim_funcd' : Π [I X : cat] (xi : func X I)  [II : catd I] (II_isf : isFibration_con II) [KK : catd I] /* KK is non cart */
(FF : funcd KK Id_func II), //OK
funcd (Comma_con_catd' (Unit_mod xi Id_func) KK) xi II;

constant symbol Comma_con_elim_homd' : Π [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
[KK : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd KK Id_func II) (f : hom x'x (Unit_mod xi Id_func) F),
homd f (Comma_con_intro_funcd' KK f) (Unit_modd (Comma_con_elim_funcd' xi II_isf FF) Id_funcd) ((Fibre_elim_funcd KK F) ∘>d FF);

rule (Comma_con_comp_funcd' _ _ $H) ∘>d (Comma_con_elim_funcd' $xi $II_isf $FF) 
   ↪  (Comma_con_elim_funcd' ($H ∘> $xi) $II_isf $FF);


type λ [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
[KK : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd KK Id_func II) (f : hom x'x (Unit_mod xi Id_func) F)
[X'0] (x'0x : func X'0 X) [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 

 ((Comma_con_homd' KK f x'0x' ) '∘d
 (( _ ) _'∘>d (Comma_con_elim_homd' xi II_isf FF f))) ==>d
 (Comma_con_elim_homd' (x'0x ∘> xi) II_isf FF (x'0x' '∘ ( (_ ) _'∘> f)));

symbol Fibration_con_funcd'' : Π [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
  [KK : catd X'] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II) /* II Cart */
(FF : funcd KK F II) (f : hom x'x (Unit_mod xi Id_func) F), 
funcd KK x'x  (Fibre_catd II xi); // aka f*FF
symbol Fibration_cov_funcd : Π [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
[KK : catd X'] [F : func X' I]  [II : catd I] /* II coCart */
(FF : funcd KK F II) (f : hom F (Unit_mod Id_func xi) x'x ), 
funcd KK x'x  (Fibre_catd II xi); // aka f!FF

constant symbol Fibration_con_elim_homd'' :  Π [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
 [KK : catd X'] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
 (FF : funcd KK F II) (f : hom x'x (Unit_mod xi Id_func) F),
  homd f (Fibration_con_funcd'' xi II_isf FF f) (Unit_modd (Fibre_elim_funcd II xi)  Id_funcd) FF;
 
constant symbol Fibration_con_intro_homd'' : Π [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
[KK : catd X'] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd KK F II) (f : hom x'x (Unit_mod xi Id_func) F)
[X'0] [x'0x : func X'0 X] [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x') [JJ : catd X'0] (MM : funcd JJ x'0x (Fibre_catd II xi))
[H : funcd (Fibre_catd KK x''x') x''x'0 JJ],
homd ((x'0x' '∘ ((x'0x)_'∘> f))) H (Unit_modd (MM ∘>d (Fibre_elim_funcd II xi)) Id_funcd) ((Fibre_elim_funcd KK (x''x')) ∘>d FF) →  //TODO move FF outside
homd x'0x' H (Unit_modd MM (Fibration_con_funcd'' xi II_isf FF f)) (Fibre_elim_funcd KK (x''x')) ;


// naturality
rule @∘>d _ _ _ _ _ _ $Z _ $ZZ  (Fibration_con_funcd'' $xi $II_isf $FF $f)  ↪ (Fibration_con_funcd'' $xi $II_isf ($ZZ ∘>d $FF) ($f ∘↓ $Z)) ;
rule (Fibration_con_intro_homd'' $xi $II_isf $FF $f  $x'0x' $MM $ii) ∘↓d (Fibre_elim_funcd _ $zz) 
  ↪ (Fibration_con_intro_homd'' $xi $II_isf $FF  $f  ($x'0x' ∘↓ $zz) $MM ($ii ∘↓d (Fibre_elim_funcd _ $zz))) ;

// rule (@∘↓d _ _ _ _ _ _ _ _ _ _ _ _ _ (Fibration_con_intro_homd $xi $FF $f $x'0x $x'0x' $MM $ii) _ $z _ $zz) 
//    ↪ (Fibration_con_intro_homd $xi $FF  $f $x'0x ($x'0x' ∘↓ $z) $MM ($ii ∘↓d $zz)) ;

// ??TODO outer naturality of fibred yoneda: Fibration_con_intro_homd''' applied to Fibration_con_intro_homd''' (xyz ∘> $f) to relate Fibration_con_funcd''' (xyz ∘> $f)  to Fibration_con_funcd''' $f
// so that so that composing with it is the corresponding action, which is then obviously natural (that is, the component-wise-specified output transf as univhoms is then natural)

// universality/deformation
rule (Fibration_con_intro_homd'' $xi $II_isf $FF $f  $x'0x' $MM $ii) '∘d (($MM)_'∘>d (Fibration_con_elim_homd'' $xi $II_isf $FF $f)) ↪ $ii;

//TODO: normality, lift id to id




//TODO: REVIEW SLOW
//-NOPE-->-FAILS ONLY BECAUSE LACKING THIS WHICH IS SLOW , FAILS ALSO BECAUSE NO BETA RULE
// rule (@Fibration_con_funcd _ _ _ _ $x'x $xi $FF ((Func_con_hom'' $xi $x'0x ∘>'_ $F) ∘' $f) )
//  ↪ (Fibration_con_funcd $xi $FF $f ) ;
// rule (@Fibration_con_funcd _ _ _ _ ($x'x ∘> $x'0x)  $xi $x'y $F $II $FF (@∘' _ _ _ _ _ (Unit_mod ($x'0x ∘> $xi) $F) _ $x'x $x'y _ _ (Func_con_hom'' $xi $x'0x ∘>'_ $F)  $f) )
//  ↪ (@Fibration_con_funcd _ _ _ _ $x'x ($x'0x ∘> $xi) $x'y $F $II $FF $f ) ;

rule (Comma_con_intro_funcd' $KK $f) ∘>d (Comma_con_elim_funcd' $xi $II_isf $FF)
↪ (Fibration_con_funcd'' $xi $II_isf ((Fibre_elim_funcd $KK _) ∘>d $FF) $f) ∘>d (Fibre_elim_funcd _ $xi) ;


//NOTE this says that the universal comparaison morphism for the algebraic Comma_con_elim_homd,
// which would use some absent universal intro rule similar as Fibration_con_intro_homd, is still definable
type λ [I X X'  : cat] [x'x : func X' X] (xi : func X I) //OK
[KK : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd KK Id_func II) (f : hom x'x (Unit_mod xi Id_func) F)
[X'0] [x'0x : func X'0 X] [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 
((Comma_con_homd' KK f x'0x' ) '∘d
((_) _'∘>d (Func_con_homd'' (Comma_con_elim_funcd' xi II_isf FF) (Comma_con_intro_funcd' KK f))))  ==>d
((Fibration_con_intro_homd'' xi II_isf ((Fibre_elim_funcd KK F) ∘>d FF) f x'0x' (Fibre_intro_funcd _ xi x'0x (Comma_con_elim_funcd' (x'0x ∘> xi) II_isf FF))
                  (Comma_con_elim_homd' (x'0x ∘> xi) II_isf FF (x'0x' '∘ (x'0x _'∘> f))))
     '∘d (( _ ) _'∘>d 
               (Func_con_homd'' (Fibre_elim_funcd II xi) (Fibration_con_funcd'' xi II_isf ((Fibre_elim_funcd KK F) ∘>d FF) f))));


//rewrite rule to make concrete how is the derived transport for the pullback of fibration,
// definable from the transport for the original fibration
symbol Pullback_Fibration_con_funcd [I X X'  : cat] [x'x : func X' X] (xi : func X I) 
[KK : catd X'] [F : func X' I] [I0] (i0 : func I I0) (II0 : catd I0) (II0_isf : isFibration_con II0)
(FF : funcd KK F (Fibre_catd II0 i0)) (f : hom x'x (Unit_mod xi Id_func) F):
funcd KK x'x  (Fibre_catd (Fibre_catd II0 i0) xi)
≔ Fibration_con_funcd'' (xi ∘> i0) II0_isf (FF ∘>d (Fibre_elim_funcd II0 i0))
      (f '∘ ( ( xi ) _'∘> (Func_con_hom'' i0 Id_func) ) );

rule @Fibration_con_funcd'' _ _ _ _ $xi _ _ (Fibre_catd $II0 $i0) (Fibre_isFibration_con $II0 $II0_isf $i0) $FF $f
 ↪  Pullback_Fibration_con_funcd $xi $i0 $II0 $II0_isf $FF $f;

// grammatical (univalent) universe by declaring an inverse to the transport for the universe fibration
injective symbol Universe_Fibration_con_funcd_inv : Π [X Y: cat] (F : func X Universe_con_cat) (G : func Y Universe_con_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) 
→ hom xy (Unit_mod G Id_func) F;

injective symbol Universe_Fibration_cov_funcd_inv : Π [X Y: cat] (F : func X Universe_cov_cat) (G : func Y Universe_cov_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_cov_catd F) xy (Fibre_catd Universe_cov_catd G) 
→ hom F (Unit_mod Id_func G) xy;

injective symbol Universe_Fibration_con_funcd  [X Y: cat] [F : func X Universe_con_cat] [G : func Y Universe_con_cat] 
[xy : func X Y] (h : hom xy (Unit_mod G Id_func) F) :
funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) ≔ 
 Fibration_con_funcd'' G  Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd F) h;

rule Fibration_con_funcd'' $G Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) (Universe_Fibration_con_funcd_inv $F $G $HH) ↪ $HH;
rule (Universe_Fibration_con_funcd_inv $F $G (Fibration_con_funcd'' $G Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) $h)) ↪ $h;


// //  /* (10) fibrations: topology ========================== */
 
 
 constant symbol Triv_covering : Π [X Y I : cat] [R : mod X Y] [G : func I Y] , 
 covering (Triv_modd R) (Triv_funcd G);
 
 constant symbol Triv_coveringu : Π (I : cat), 
 coveringu (Triv_moddu I) (Triv_funcd Id_func);
 
 constant symbol Fibre_coveringu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 [RR : modd A R B]  [G : func I Y] [H : funcd (Triv_catd I) G B],
  covering RR H →  Π [F : func I X] (r : hom F R G),
  coveringu (Fibre_hom_moddu RR r)  (Fibre_intro_funcd _ G Id_func H );
 
   constant symbol Total_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 [RR : modd A R B]  [G : func I Y] [H : funcd (Triv_catd I) G B],
 (Π [F : func I X] (r : hom F R G), coveringu (Fibre_hom_moddu RR r)  (Fibre_intro_funcd _ G Id_func H )) → 
  covering RR H ;

constant symbol Glue_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
[rr' : transf R xx' R' yy'] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
Π [I : cat] [G : func I Y] [H : funcd (Triv_catd I) G B] , covering RR H →
(Π [F : func I X] (r : hom F R G), transfduu  (Fibre_hom_moddu RR r) (Fibre_intro_funcd _ (F ∘> xx') Id_func (Fibre_elim_funcd A F ∘>d FF))  
   (Fibre_hom_moddu (Sheaf_con_modd  RR') (r '∘ rr')) (Fibre_intro_funcd _ (G ∘> yy') Id_func (Fibre_elim_funcd B G ∘>d GG))) → 
transfd rr' RR FF (Sheaf_con_modd RR') GG;
