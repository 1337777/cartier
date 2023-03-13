(* GOTO THIS FILE DEDUKTI LAMBDAPI>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

https://github.com/1337777/cartier/blob/master/cartierSolution12.lp

 <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<INSTEAD GOTO THIS FILE DEDUKTI LAMBDAPI

*)

(* 
/* TODO: these are unfinished prototypes for demo that it does work

https://github.com/1337777/cartier/blob/master/cartierSolution12.v (head version; experiment file)
https://github.com/1337777/cartier/blob/master/cartierSolution12.lp (lagging version; future primary file; must use LambdaPi for modulo structural coherence)

In one line: the problem of contextual composition (cut elimination) and monoidal units (J-rule elimination) is solved by alternative formulations of adjunctions.

Context: There is now sufficient evidence (ref [6], [7]) that Kosta Dosen's ideas and techniques (ref [1], [2], [3], [4], [5]) could be implemented for proof-assistants, sheaves and applications; in particular cut-elimination, rewriting and confluence for various enriched, internal, indexed or double categories with adjunctions, monads, negation, quantifiers or additive biproducts; quantitative/quantum linear algebra semantics; presheaf/profunctor semantics; inductive-sheafification and sheaf semantics; sheaf cohomology and duality...

[1] Dosen-Petric: Cut Elimination in Categories 1999;
[2] Proof-Theoretical Coherence 2004;
[3] Proof-Net Categories 2005;
[4] Coherence in Linear Predicate Logic 2007;
[5] Coherence for closed categories with biproducts 2022

Proposal for prospective implementation:

The problem of “formulations of adjunction”, the problem of “unit objects” and also the problem of “contextual composition/cut” can be understood as the same problem. The question arises when one attempts to write precisely the counit/eval transformation ϵ_X ∶ catA(F G X, X) where F : catB → catA is the left-adjoint. One could instead write ϵ_X ∶ catA(F ,1)(G X, X) where the profunctor object/datatype catA(F ,1) is used in lieu of the unit hom-profunctor catA; in other words: F is now some implicit context, and the contextual composition/cut (in contravariant action) of some g:catB(Y, G X) in the unit profunctor against ϵ_X should produce an element of the same datatype: ϵ_X∘g : catA(F,1)(Y,X)... Ultimately Dosen-Petric (ref [5]) would be extended in this setting where some dagger compact closed double category, of left-adjoint profunctors across Cauchy-complete categories, is both inner and outer dagger compact closed where the dagger operation on profunctors (as 1-cells) coincides with the negation operation on profunctors (as 0-cells), optionally with sheaf semantics and cohomology. The earlier Coq prototypes (ref [6] for example) show that the core difficulty is in the industrial labor and tooling, which requires a coordinated workshop of workers (not celebrities, lol).

Recall that closed monoidal categories (with conjunction bifunctor ∧ with right adjoint implication functor →) are similar as programming with linear logic and types. Now to be able to express duality, finitely-dimensional/traced/compact closed categories are often used to require the function space (implication →) to be expressible in basis form. But along this attempt to express duality, two (equivalent) pathways of the world of substructural proof theory open up: one route is via Barr’s star-autonomous categories and another route is via Seely’s linearly distributive categories with negation.

For star-autonomous categories, one adds a “dualizing unit” object ⊥ which forces the evaluation arrow A ⊢ (A → ⊥) → ⊥ into an isomorphism. For linearly distributive categories with negation, one adds a “monoidal unit” object ⊥ for another disjunction bifunctor ∨ whose negation A'∨- is right-adjoint to the conjunction A∧- where this adjunction is expressed via the help of some new associativity rule A∧(B∨C) ⊢ (A∧B)∨C called “dissociativity” or “linear distributivity” (used to commute the context A∧ - and the negated context -∨C); and it is this route chosen by Dosen-Petric to prove most of their Gentzen-formulations and cut-elimination lemmas (ref §4.2 of [3] for linear, ref §11.5 of [2] for cartesian, and ref §7.7 of [2] for an introductory example). In summary, those are two routes into some problem of “unit objects” in non-cartesian linear logic.

Some oversight about the problem of “unit objects” is the belief that it should have any definitive once-for-all solution. Instead, this appears to be a collection of substructural problems for each domain-specific language. Really, even the initial key insight of Dosen-Petric, about the cut-elimination formulation in the domain-specific language of categorial adjunctions, can be understood as a problem of “unit profunctor” in the double category of profunctors and the (inner) cut elimination lemma becomes synonymous with elimination of the “J-rule”; and recall that such equality/path-induction J-rule would remain stuck in (non-domain-specific) directed (homotopy) type theory.

Now the many “formulation of adjunctions” are for different purposes. Indeed the outer framework (closed monoidal category) hosting such inner domain-specific language (unit-counit formulation) could itself be in another new formulation of adjunctions (bijection of hom-sets) where the implication bifunctor  → is accumulated during computation via dinaturality (in contrast to the traditional Kelly-MacLane formulation).

Finally the problem of “contextual composition/cut” also arises from the problem of the structural coherence of associativity or dissociativity or commutativity, which now enables gluing the codomain/domain of compositions such as A∧f ∶ A∧X → A∧(B∨C) then g∨C ∶ (A∧B)∨C → Y∨C, or such as η_A ∶ I → A'∧A then ϵ_A∘f∧A' ∶ A∧A' → I, and which would force the outer framework to explicitly handle compositions under contexts/polycategories modulo associativity (“Gentzen cuts”) or to handle trace functions on arrows loops modulo cyclicity (for compact closed categories)... In other words, the meta framework (such as Blanqui’s LambdaPi and surprisingly not Coq’s CoqMT at present) of the framework should ideally implement those strictification lemmas (ref §3.1 of [2]) to be able to compute modulo structural coherence.

[6] Cut-elimination in the double category of profunctors with J-rule-eliminated adjunctions: https://github.com/1337777/cartier/blob/master/cartierSolution12.v ( /cartierSolution12.lp ; /maclaneSolution2.v MacLane’s pentagon is some recursive square! )

[7] Pierre Cartier
 */

symbol Prop : TYPE;
injective symbol Prf : Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;


inductive cat : TYPE ≔ 

with func : Π (A B : cat), TYPE ≔
| Id_func : Π [A : cat], func A A

with mod : Π (A B : cat), TYPE ≔
| Unit_mod : Π [X A B : cat], func A X → func B X → mod A B
| Tensor_cov_mod : Π [A B C X : cat], mod A B → func B C → mod C X → mod A X
| Tensor_con_mod : Π [A B C X : cat], mod X C → func A C → mod A B → mod X B
| Imply_cov_mod : Π [A B C X : cat], mod A B → func C B → mod X C → mod A X
| Imply_con_mod : Π [A B C X : cat], mod C X → func C A → mod A B → mod X B

with modd : Π [A X Y B : cat], func A X → mod X Y → func B Y → TYPE ≔
// fibred

with adj : Π [R L : cat], func R L → func L R → TYPE ≔

with hom: Π [I A B : cat], func I A → mod A B → func I B → TYPE ≔

| Id_cov_hom : Π [A B I : cat] (F : func B A),
hom Id_func (Unit_mod F Id_func ) F

| Id_con_hom : Π [A B I : cat] (F : func B A),
hom F (Unit_mod Id_func F) Id_func

| Adj_cov_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func),
hom RAdj_func (Unit_mod LAdj_func Id_func) Id_func

| Adj_con_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func),
hom Id_func (Unit_mod Id_func RAdj_func) LAdj_func;

//Subst_func
symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix right 80;

symbol <∘ : Π [A B C: cat], func B C → func A B → func A C 
  ≔ λ _ _ _ G F, F ∘> G;
notation <∘ infix left 80;

//Subst_cov_mod
symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;
notation <<∘ infix left 80;

//Subst_con_mod
symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
notation ∘>> infix right 80;

// Subst_hom
symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
[G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
notation ∘↓ infix left 120;

rule ($F ∘> $G) ∘> $H ↪ $F ∘> ($G ∘> $H)
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

rule (Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K)
with (Tensor_cov_mod $R $H $S) <<∘ $G ↪ Tensor_cov_mod $R $H ($S <<∘ $G)
with (Tensor_con_mod $R $H $S) <<∘ $G ↪ Tensor_con_mod $R $H ($S <<∘ $G)
with (Imply_cov_mod $R $H $S) <<∘ $G ↪ Imply_cov_mod $R $H ($G ∘>> $S)
with (Imply_con_mod $R $H $S) <<∘ $G ↪ Imply_con_mod $R $H ($S <<∘ $G);

rule $K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G
with $G ∘>> (Tensor_con_mod $R $H $S) ↪ Tensor_con_mod ($G ∘>> $R) $H $S
with $G ∘>> (Tensor_cov_mod $R $H $S) ↪ Tensor_cov_mod ($G ∘>> $R) $H $S
with $G ∘>> (Imply_con_mod $R $H $S) ↪ Imply_con_mod ($R <<∘ $G) $H $S
with $G ∘>> (Imply_cov_mod $R $H $S) ↪ Imply_cov_mod ($G ∘>> $R) $H $S;

// provable  (careful ?? this indirely unify stuff?)
rule $R <<∘ Id_func ↪ $R 
with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K); 

rule Id_func ∘>> $R ↪ $R 
with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R; 

rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));

rule $r ∘↓ Id_func ↪ $r
with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($H <∘ $K); 

/* =========================== */

inductive transf: Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → TYPE ≔

| Id_transf : Π [A X : cat] (R : mod A X) ,
transf R Id_func R Id_func

//Unit_cov_trans
| ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func

//Unit_con_trans
| _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G

| Unit_Tensor_cov_transf : Π [A B A' X : cat] [P : mod A B] [P' : mod A' X] [F : func A A'] [K : func B X],
transf P F P' K → 
transf (Tensor_cov_mod P K ( Unit_mod Id_func Id_func )) F P' Id_func

| Eval_cov_transf : Π [A B C X A' X' : cat] [P : mod A B] [Q : mod C X] 
[O : mod A' X'] [K : func B C] [F : func A A'] [L : func X X'],
transf P                       F (Imply_cov_mod O L Q) K →
transf (Tensor_cov_mod P K Q)  F O                     L

| Lambda_cov_transf : Π [A B C X A' X' : cat] [P : mod A B] [Q : mod C X] 
[O : mod A' X'] [K : func B C] [F : func A A'] [L : func X X'],
transf (Tensor_cov_mod P K Q) F O L →
transf P F (Imply_cov_mod O L Q) K 

| Tensor_cov_transf : Π [A' B' X' A B C X C': cat] [P' : mod A' B'] [Q' : mod C' X'] 
[P : mod A B] [Q : mod C X] [K' : func B' B] [F : func A' A] [K : func C' C] [G : func X' X],
transf P' F P K' → transf Q' K Q G → Π  (K0 : func B C'),
transf (Tensor_cov_mod P' (K' ∘> K0) Q') F (Tensor_cov_mod P K0 (K ∘>> Q)) G

| Tensor_hom_cov_transf : Π [A' I' I X' A C X I0 : cat] [P' : mod A' I']
[P : mod A I0] [Q : mod C X] [F : func A' A] [H : func I' I0] [K : func I C] [G : func I X],
transf P' F P H → hom K Q G → Π (H0 : func I0 I),
transf P' F (Tensor_cov_mod P H0 (K ∘>> Q)) (G <∘ (H0 <∘ H))

| Imply_cov_transf : Π [A B A' B' C D C' D' : cat] [O : mod A B] [O' : mod A' B']
 [Q : mod C D] [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func D D'],
transf O F O' G → Π (K : func D' B), transf Q H Q' L → 
transf   (Imply_cov_mod O K (H ∘>> Q'))
       F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) Id_func

| Imply_hom_cov_transf : Π [A B A' B' C C' D' : cat] [O : mod A B] [O' : mod A' B']
  [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func C D'],
transf O F O' G → Π (K : func D' B), hom H Q' L → 
transf   (Imply_cov_mod O K (H ∘>> Q'))
       F (O' <<∘ ((G <∘ K) <∘ L)) Id_func ;

notation _'∘> infix right 80;
notation ∘>'_ infix left 80;

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

//TODO  THESE ARE ADMISSIBLE Id_cov_transf ,  Id_con_transf  then can derive structural operations, Subst_cov_transf, UnSubst_cov_transf
symbol Id_cov_transf : Π [A X A' : cat] (R : mod A X) (F : func A' A),
transf (F ∘>> R) F R Id_func;

symbol Id_con_transf : Π [X B B' : cat] (R : mod X B) (G : func B' B),
transf (R <<∘ G) Id_func R G;

injective symbol ==> : Π [I A B: cat] [F : func I A] [T : mod A B] [G :func I B],
hom F T G → hom F T G → TYPE;
notation ==> infix 20;

injective symbol ==>> : Π [A' B' A B: cat] [S : mod A' B'] [F : func A' A] [T : mod A B] [G :func B' B],
transf S F T G → transf S F T G → TYPE;
notation ==>> infix 20;



/* ========================== */

// naturality

// t∘1(g) ∘X0 -  =  t∘1(g ∘X0 -) 
type λ [L R J I I' I1 : cat] (T : mod R L)
 (Y0 : func I1 R) (Y: func I' I1) (Z : func I1 L)
 (M : func J I) (X: func I' I) (X0: func I R) 
(t : hom Y0 T Z)
(g : hom X (Unit_mod X0 Y0) Y),
(M)_'∘> (g '∘ ((X0)_'∘> t))
==>> ((M)_'∘> g) ''∘ ((M ∘> X0)_'∘> t);
// : transf (M ∘>> _1<∘ (X ∘> Id_func)) Id_func (M ∘>> (X0 ∘>> T)) (Z <∘ Y)

// (1∘Z0-)∘t∘(g)  =  1∘t∘(- Y0<∘ g)
type λ [L R I I0 I1 J : cat] 
(X: func I I0) (X0: func I0 R)
(Y0 : func I1 R) (Y: func I I1) (Z0 : func I1 L) (N : func J I1)
(T : mod R L) (t : hom Y0 T Z0)
(g : hom X (Unit_mod X0 Y0) Y),
((g '∘ ((X0)_'∘> t)) ∘>'_(Id_func)) // : transf ((Y ∘> Z0) ∘>1_) X (X0 ∘>> T) Id_func
   ∘'' (( (Y)_'∘> (Id_cov_hom Z0) ∘↓ N))
==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> (t ∘↓ N)))  ;
// transf (Y ∘>> _1<∘ (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) 
//        ((X0 ∘>> T) <<∘ Id_func) (Id_func <∘ (Z0 <∘ N))

/* ========================== */

// adjunct inverses

// “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
type λ [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) (Z : func I R) (N : func J L),
 (((Adj_con_hom aj) ∘↓ Z) ∘>'_(N)) ''∘ ((Id_func)_'∘> ((Adj_cov_hom aj) ∘↓ N))
 ==>> (((Id_cov_hom LAdj_func) ∘↓ Z) ∘>'_(N) ) ''∘ (  (LAdj_func)_'∘> ((Id_con_hom Id_func) ∘↓ N) );
// : transf (((LAdj_func <∘ Z) ∘>1_) <<∘ N) ((Z ∘> Id_func) ∘> Id_func) (Id_func ∘>> Unit_mod LAdj_func Id_func) ((Id_func <∘ N) <∘ Id_func)


// “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   
type λ [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) (Z : func I R) V (M : func J R),
( (M)_'∘> ((Adj_con_hom aj) ∘↓ Z) ) ''∘ ( (M)_'∘> ((Adj_cov_hom aj) ) )
==>> ( (M)_'∘> ((Id_cov_hom LAdj_func) ∘↓ Z) );
// : transf (M ∘>> _1<∘ (Z ∘> Id_func)) (Id_func ∘> Id_func) (M ∘>> Unit_mod LAdj_func Id_func) (Id_func <∘ (LAdj_func <∘ Z))


/* ========================== */

// naturality and dinaturality of evaluation
type λ  [A B C X A' X' A0 C0 : cat] [P : mod A B] [Q : mod C X] 
[O : mod A' X'] [K0 : func B C0] [F : func A A'] [L : func X X'] (M: func A0 A)  (K : func C0 C)
(pq_o : transf P F (Imply_cov_mod O L (K ∘>> Q)) K0)
B0 (N : func B0 B) D (Z : func D X) 
(P': mod A0 B0) (p'p : transf P' M P N)  (Q' : mod C0 D) (q'q : transf Q' K Q Z),
(Eval_cov_transf pq_o) ∘'' (Tensor_cov_transf p'p q'q K0)  
==>> Eval_cov_transf ((pq_o ∘'' p'p) ''∘  (Imply_cov_transf (Id_transf O) L q'q));
//transf (Tensor_cov_mod P' (N ∘> K0) Q') (M ∘> F) O (L <∘ Z)


// pp (- o> 1)  ==>>  pp    coyoneda 
type λ [A B A' X : cat] [P : mod A B] [P' : mod A' X] [F : func A A'] [K : func B X]
(pp : transf P F P' K),
(Unit_Tensor_cov_transf pp)  ∘'' (Tensor_hom_cov_transf (Id_transf P) (Id_con_hom Id_func) K)
 ==>> pp;
//transf P (Id_func ∘> F) P' (Id_func <∘ (Id_func <∘ (K <∘ Id_func)))


/* ========================== */

//voila

 *)