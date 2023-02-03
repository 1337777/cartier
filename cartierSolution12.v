(** # #
#+TITLE: cartierSolution12.v

TODO: these are unfinished prototypes for demo that it does work

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

-----

#+BEGIN_SRC coq :exports both :results silent # # **)

Module Example.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path fintype tuple finfun bigop ssralg. 

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.

Parameter Cat : Set.

Inductive functor: forall (C D : Cat), Type :=
| Subst_functor : forall [C D E: Cat], functor C D -> functor D E ->   functor C E
| Id_functor : forall C : Cat, functor C C

with rel: forall (C D : Cat), Type :=
| Tensor_antec_rel' : forall [A B C B' : Cat], rel C B -> functor B B' -> rel B' A -> rel C A
| Id_rel :  forall [C C' D' : Cat], functor C' C -> functor D' C -> rel C' D'
| Imply_antec_rel' : forall  [A C B C' : Cat], rel A C -> rel B C' -> functor C C' -> rel B A
| Subst_rel : forall [C D C' D': Cat], rel C D -> functor C' C -> functor D' D ->  rel C' D' .

Inductive adjunc : forall [C D: Cat], functor C D -> functor D C -> Type := 

with transf:  forall [C A B: Cat], rel A B -> functor C A -> functor C B -> Type :=

| Restr_transf (* admissible *): forall C A B: Cat, forall (R : rel A B) (F : functor C A) (G : functor C B),
  forall D (X : functor D C), transf R F G -> transf R (Subst_functor X F) (Subst_functor X G)

| Id_antec_transf : forall E C: Cat, forall (F : functor C E), forall D (X : functor D C),
       transf  (Id_rel F (Id_functor _) ) X  (Subst_functor X F)
| Id_conse_transf : forall E C: Cat, forall (F : functor C E),  forall D (X : functor D C),
      transf (Id_rel (Id_functor _) F)   (Subst_functor X F) X

| UnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A C), 
    transf   (Id_rel (Id_functor _) (RightAdjunc_functor) ) X  (Subst_functor X (LeftAdjunc_functor))

| CoUnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A D), 
    transf  (Id_rel (LeftAdjunc_functor) (Id_functor D)) (Subst_functor X (RightAdjunc_functor)) X

| App_transf : forall [C D C' D' A: Cat], forall [R : rel C D] [F : functor C C'] [S : rel C' D'] [G : functor D D'] [M : functor A C] [N : functor A D], 
    transf R M  N -> funcTransf R S F G -> transf S (Subst_functor M F) (Subst_functor N G)

with funcTransf: forall [C D C' D': Cat], rel C D -> rel C' D' -> functor C C' -> functor D D' -> Type :=  
   

| Subst_funcTransf (* admissible *) : forall [C D C' D' C'' D'': Cat], forall [R : rel C D] [S : rel C' D'] [F : functor C C'] [G : functor D D']
  [T : rel C'' D''] [F' : functor C C''] [G' : functor D D''],
  funcTransf R S F G -> funcTransf (Subst_rel S F G) T F' G' -> funcTransf R T F' G'

| Id_funcTransf : forall C D: Cat, forall R : rel C D, 
  forall (C' D': Cat) (F : functor C' C) (G : functor D' D), 
    funcTransf (Subst_rel R F G) R F G

| Restr_funcTransf (* admissible *): forall C D: Cat,  forall  C' D' (F : functor C C'), forall S : rel C' D', forall (G : functor D D'),
  forall  C'' D'' (F' : functor C' C''), forall T : rel C'' D'', forall (G' : functor D' D''),
   funcTransf S T F' G' -> funcTransf (Subst_rel S F G) T (Subst_functor F F') (Subst_functor G G')

| Comp_antec_funcTransf' : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> forall B' (K: functor B' B), funcTransf (Id_rel G K) R F K

| Comp_conse_funcTransf' : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> forall A' (K: functor A' A), funcTransf (Id_rel K F) R K G

| CoYoneda_antec_funcTransf'' : forall (C D D' : Cat) (H : functor D D') (R : rel C D) 
    (C' : Cat) (F : functor C C') (T : rel C' D'),
    funcTransf R T F H ->
    forall (D0 : Cat) (K : functor D0 D'),
    funcTransf (Tensor_antec_rel' R H (Id_rel (Id_functor D') K)) T F K

| CoYoneda_antec_appId_funcTransf'' (* OK version to derive ?? *): 
forall C D: Cat, forall D0 (H : functor D  D0), forall R : rel C D,
forall  C' (F : functor C C') D' (G : functor D D') (T : rel C' D'), 
    funcTransf (Tensor_antec_rel' R H (Id_rel (Id_functor _) H)) T F G -> 
    funcTransf R T F G

| Imply_antec_app_funcTransf'' : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' (D'D : functor D' D) (R : rel E D'),
    funcTransf P (Imply_antec_rel' R S D'D) F E'E ->
    funcTransf (Tensor_antec_rel' P E'E R) S F D'D

| Imply_antec_lambda_funcTransf' (* OK version for skew bif *) : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' (D'D : functor D' D) (R : rel E D'),
    funcTransf (Tensor_antec_rel' P E'E R) S F D'D ->
    funcTransf P (Imply_antec_rel' R S D'D) F E'E


| Tensor_antec_funcTransf'' (* OK version for skew bif *) : forall (D A  : Cat)  (S : rel D A) C' (H : functor C' D) C (F : functor C A) (S' : rel C' C)
E E' (R : rel E E') (G : functor A E)  A' (K : functor A' E')  (R' : rel A A')  ,
 funcTransf S' S H F -> funcTransf R' R G K ->
  funcTransf (Tensor_antec_rel' S' F R') (Tensor_antec_rel' S G R) H K

| Imply_antec_funcTransf''_bif'  (* NOPE because contravariance ? *):  forall  [A A0 C0 B C' : Cat] (R' : rel A0 C0) (S : rel B C') (K : functor C0 C')
B' (F : functor B B')  C'' (G : functor C' C'')  (S' : rel B' C'')
C (H : functor C C0) (R : rel A C),
funcTransf S S' F G (* must G be id ? *) -> forall (L : functor A A0),  funcTransf R R' L(* ?? must be id? more general lambda too; note this is contra now; or assume it is id only for cast*) H ->
forall  A1 (M : functor A1 A),  
funcTransf (Imply_antec_rel' (Subst_rel R' (Subst_functor M L) (Id_functor _)) S K) (Imply_antec_rel' R S' (Subst_functor H (Subst_functor K G))) F M(* must be id; or restrict R'? yeo, input M to restrict rr *)

(* from sol *)

| Id_antec_Comp_antec_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),  forall A' (Y : functor A' _),
  funcTransf (Id_rel (Subst_functor X F) Y) (Id_rel F (Id_functor _) ) X  Y

| Id_antec_Comp_conse_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _), forall A' (Y : functor A' _),
  funcTransf (Id_rel Y X) (Id_rel F (Id_functor _) ) Y (Subst_functor X F)

| Id_conse_Comp_conse_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),  forall A' (Y : functor A' _),
  funcTransf (Id_rel Y (Subst_functor X F)) (Id_rel (Id_functor _) F)  Y X

| UnitAdjunc_Comp_antec_funcTransf'' (* bad  *): forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A C), forall B (Y : functor B D), 
      funcTransf (Id_rel (Subst_functor X (LeftAdjunc_functor)) Y) (Id_rel (Id_functor _) (RightAdjunc_functor) ) X  Y

| CoUnitAdjunc_Comp_antec_funcTransf'' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ),
forall A (X : functor A _),   forall B (Y : functor B _), 
  funcTransf (Id_rel X Y ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Subst_functor X (RightAdjunc_functor)) Y

| CoUnitAdjunc_Comp_conse_funcTransf'' (* bad *) : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
forall A (X : functor A C), forall B (Y : functor B D), 
  funcTransf (Id_rel X (Subst_functor Y (RightAdjunc_functor)) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) X Y .


(* eval/app dinaturality ; redex *)
Check fun  (C E D : Cat)  
(C' : Cat)   (F : functor C C') (S : rel C' D)
E' (E'E : functor E' E) (P : rel C E')
D' (D'D : functor D' D) (R : rel E D') C0 (C0C : functor C0 C) D0 (D0D' : functor D0 D')
(ff : funcTransf (Subst_rel P C0C (Id_functor _)) (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F) E'E ) 
E0 (E0E' : functor E0 E') 
P' (pp : funcTransf P' P C0C E0E') R' (rr : funcTransf R' R E'E D0D')  =>
( Tensor_antec_funcTransf'' pp rr (* todo in develop form, so one at a time *),
  (Imply_antec_app_funcTransf'' ff)  )
: funcTransf (Tensor_antec_rel' P' E0E' R') (Tensor_antec_rel' P E'E R) C0C D0D' *
funcTransf (Tensor_antec_rel' (Subst_rel P C0C (Id_functor E')) E'E
                (Subst_rel R (Id_functor E) D0D')) S (Subst_functor C0C F) (Subst_functor D0D' D'D) .

(* eval/app dinaturality ; contractum *)
Check fun  (C E D : Cat)  
(C' : Cat)   (F : functor C C') (S : rel C' D)
E' (E'E : functor E' E) (P : rel C E')
D' (D'D : functor D' D) (R : rel E D') C0 (C0C : functor C0 C) D0 (D0D' : functor D0 D')
(ff : funcTransf (Subst_rel P C0C (Id_functor _)) (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F ) E'E ) 
E0 (E0E' : functor E0 E') 
P' (pp : funcTransf P' P C0C E0E') R' (rr : funcTransf R' (Subst_rel R (Id_functor _) D0D') E'E (Id_functor _))  =>
fun (ff_restr (* becaus input is dependent pair (E0E', pp) ; this is first application of E0E' *)
 : funcTransf (Subst_rel P C0C E0E') (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F ) (Subst_functor E0E' E'E)) 
(tmp_compo_result_type:  funcTransf P'  (Imply_antec_rel' R' S
                          (Subst_functor (Id_functor D0)
                              (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))))   (Subst_functor C0C F) E0E') =>
( (Subst_funcTransf pp ff_restr (* input E0E' to restrict ff *) ),
 (Imply_antec_funcTransf''_bif' (Subst_functor D0D' D'D) (Id_funcTransf S  (Subst_functor C0C F ) (Id_functor _)) rr E0E' (* input E0E' to restrict rr *) (L:=E'E) ),
 Imply_antec_app_funcTransf'' tmp_compo_result_type )
: funcTransf P'
(Imply_antec_rel' (Subst_rel R (Id_functor E) D0D') S
   (Subst_functor D0D' D'D)) (Subst_functor C0C F)
(Subst_functor E0E' E'E) *
funcTransf (Imply_antec_rel'
   (Subst_rel (Subst_rel R (Id_functor E) D0D')
      (Subst_functor E0E' E'E) (Id_functor D0))
   (Subst_rel S (Subst_functor C0C F) (Id_functor D))
   (Subst_functor D0D' D'D))
(Imply_antec_rel' R' S
   (Subst_functor (Id_functor D0)
      (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))))
(Subst_functor C0C F) E0E' *
funcTransf (Tensor_antec_rel' P' E0E' R') S 
(Subst_functor C0C F)
(Subst_functor (Id_functor D0)
   (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))).



(*** “1∘FX(h)” <∘ “1∘F(g)”  =                     “1∘F(h X<∘ g)”       *) (* OK *)
(*** “1∘F(h)” <∘ “1∘F(g)”  =                     “1∘F(h <∘ “1∘I(g)”)”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y X) M N)  P (K: functor P A) =>
( Id_antec_Comp_conse_funcTransf''  (Subst_functor X F) K N  (* 1∘FX *),
Id_antec_Comp_conse_funcTransf'' F (Subst_functor K X) (Subst_functor N X)   ,
Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' F X Y)) (Subst_functor K (Subst_functor X F)) )
:  funcTransf (Id_rel N K) (Id_rel (Subst_functor X F) (Id_functor E)) N (Subst_functor K (Subst_functor X F)) *
funcTransf (Id_rel (Subst_functor N X) (Subst_functor K X)) (Id_rel F (Id_functor E)) (Subst_functor N X) (Subst_functor (Subst_functor K X) F) *
funcTransf (Id_rel (Subst_functor N (Subst_functor X F)) (Subst_functor K (Subst_functor X F))) 
(Id_rel F (Id_functor E)) (Subst_functor M Y) (Subst_functor K (Subst_functor X F)).

(*** “1∘FX(h)” <∘ “1∘F(g)”                       = “1∘F(h X<∘ g)”       *) (* OK *)
(*** “1∘F(h)” <∘ “1∘F(g)”                       = “1∘F(h <∘ “1∘I(g)”)”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y (Subst_functor X (Id_functor _))) M N) P (K: functor P A) =>
( Comp_antec_funcTransf' g K  (* X<∘ *),
  Comp_antec_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) X Y)) (Subst_functor K X),
  Id_antec_Comp_conse_funcTransf'' F (Subst_functor K X) (Subst_functor M Y)  )
: funcTransf (Id_rel N K) (Id_rel Y (Subst_functor X (Id_functor C))) M K *
 funcTransf (Id_rel (Subst_functor N X) (Subst_functor K X))
(Id_rel (Id_functor C) (Id_functor C)) (Subst_functor M Y) (Subst_functor K X) *
funcTransf (Id_rel (Subst_functor M Y) (Subst_functor K X))
(Id_rel F (Id_functor E)) (Subst_functor M Y) (Subst_functor (Subst_functor K X) F).


(***   “1∘F(g)” ∘>F h =                     “1∘F”( “I∘1(g)” ∘> h )  *) (* OK *)
 Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y X) M N) P (K: functor P C) =>
Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' F X Y)) K
:  funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel F (Id_functor E)) K (Subst_functor N (Subst_functor X F)).

(*   “1∘F(g)” ∘>F h                    = “1∘F”( “I∘1(g)” ∘> h )  *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y (Subst_functor X (Id_functor _))) M N) P (K: functor P C) =>
( Comp_conse_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) X Y)) K,
  Id_antec_Comp_conse_funcTransf'' F (Subst_functor N X) K)
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel (Id_functor C) (Id_functor C)) K  (Subst_functor N X) *
funcTransf (Id_rel K (Subst_functor N X)) (Id_rel F (Id_functor E)) K (Subst_functor (Subst_functor N X) F).



(* todo: try  “1(g)∘G”  =  id(g)   then   “1(g)∘G” ∘>G “1∘F(h)” =   g ∘>GFY  ?  *)

(***   “1(g)∘G” ∘>G “1∘F(h)” =                    “1(“1(g)∘GF” ∘>GF h)∘G”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) E' (G : functor E E') A (X : functor A E')
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel  (Subst_functor (Subst_functor Y F) G) X) M N) P (K: functor P _) =>
(  Id_antec_Comp_conse_funcTransf'' F (Subst_functor M Y) K ,
Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' G (Subst_functor Y F) X)) (Subst_functor K F) )
: funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel F (Id_functor E)) K (Subst_functor (Subst_functor M Y) F) *
funcTransf (Id_rel (Subst_functor K F) (Subst_functor M (Subst_functor Y F)))
(Id_rel G (Id_functor E')) (Subst_functor K F)  (Subst_functor N X).

(***   “1(g)∘G” ∘>G “1∘F(h)”                      = “1(“1(g)∘GF” ∘>GF h)∘G”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) E' (G : functor E E') A (X : functor A E')
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel  (Subst_functor Y (Subst_functor F G)) X) M N) P (K: functor P _) =>
( Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' (Subst_functor F G) Y X)) K ,
 Id_antec_Comp_antec_funcTransf'' G (Subst_functor K F) (Subst_functor N X) )
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel (Subst_functor F G) (Id_functor E')) K  (Subst_functor N X) *
funcTransf (Id_rel (Subst_functor (Subst_functor K F) G) (Subst_functor N X))
(Id_rel G (Id_functor E')) (Subst_functor K F)  (Subst_functor N X).



(*** “ϕ∘F(g)” ∘>F h =                “ϕ∘F(“I∘1(g)” ∘> h)” *)  (* OK *) (* instance included: “(“ϕ∘F”g)∘FY”h =                   “ϕ∘F”(“g∘Y”h) *)  
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A (X : functor A D)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N)  P (K: functor P C) =>
Comp_conse_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj Y X)) K
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel LeftAdjunc_functor (Id_functor D)) K  (Subst_functor N X).

(* “ϕ∘F(g)” ∘>F h                 = “ϕ∘F(“I∘1(g)” ∘> h)” *)  (* OK *) 
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A (X : functor A D)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y (Subst_functor (Subst_functor X RightAdjunc_functor) (Id_functor _) )) M N)  P (K: functor P C) =>
( Comp_conse_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) (Subst_functor X RightAdjunc_functor) Y)) K ,
CoUnitAdjunc_Comp_conse_funcTransf'' adj K (Subst_functor N X) )
: funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel (Id_functor C) (Id_functor C)) K (Subst_functor N (Subst_functor X RightAdjunc_functor)) *
funcTransf (Id_rel K (Subst_functor (Subst_functor N X) RightAdjunc_functor)) (Id_rel LeftAdjunc_functor (Id_functor D)) K (Subst_functor N X).


(*** alt: “ϕ∘F(g)” <∘ “1∘F(h)” =                “ϕ∘F( g <∘ “I∘1(h)” )” *)  (* OK *)
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A A' (X : functor A' C) (Y : functor A C)
 B (M : functor B A') (N : functor B A) 
 (h: transf (Id_rel X Y) M N  )  P (K: functor P D) =>
 ( CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor N Y) K ,
 Comp_antec_funcTransf' (App_transf h (Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor Y X)) K )
: funcTransf (Id_rel (Subst_functor N Y) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor N Y) K *
funcTransf (Id_rel (Subst_functor N (Subst_functor Y LeftAdjunc_functor)) K)
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M X) K .

(* alt: “ϕ∘F(g)” <∘ “1∘F(h)”                   = “ϕ∘F( g <∘ “I∘1(h)” )” *)  (* OK *)
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A A' (X : functor A' C) (Y : functor A C)
 B (M : functor B A') (N : functor B A) 
 (h: transf (Id_rel X (Subst_functor Y (Id_functor _))) M N  )  P (K: functor P D) =>
 ( Comp_antec_funcTransf' (App_transf h (Id_conse_Comp_conse_funcTransf'' (Id_functor _ ) Y X)) (Subst_functor K RightAdjunc_functor),
 CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor M X) K  )
: funcTransf (Id_rel (Subst_functor N Y) (Subst_functor K RightAdjunc_functor))
(Id_rel (Id_functor C) (Id_functor C)) (Subst_functor M X) (Subst_functor K RightAdjunc_functor) *
funcTransf (Id_rel (Subst_functor M X) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M X) K.



(*** h <∘ “ϕ∘F(g)” =                “ϕ∘F( h G<∘ “G∘1(g)” )” *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' C) A''  (M : functor A'' A') (N : functor A'' A)
(g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N) P (K: functor P D)  =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj Y X )) K
: funcTransf (Id_rel (Subst_functor N X) K)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor M Y) K.

                                     (*? old? todo: here subst exact matching only on cotravariant and conversion of subst on covariant*)
(* h <∘ “ϕ∘F(g)”                  = “ϕ∘F( h G<∘ “G∘1(g)” )” *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' C) A''  (M : functor A'' A') (N : functor A'' A)
(g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N) P (K: functor P D)  =>
( Comp_antec_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' RightAdjunc_functor X Y)) K ,
CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor M Y) K )
: funcTransf (Id_rel (Subst_functor N X) K)
(Id_rel (Id_functor C) RightAdjunc_functor)  (Subst_functor M Y) K *
funcTransf (Id_rel (Subst_functor M Y) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M Y) K .



(*** “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   *) (* OK *)
Check fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C) B (Y : functor B C) =>
(Comp_conse_funcTransf' (UnitAdjunc_transf adj X) Y,
CoUnitAdjunc_Comp_conse_funcTransf'' adj Y (Subst_functor X LeftAdjunc_functor)  )
: funcTransf (Id_rel Y X) (Id_rel (Id_functor C) RightAdjunc_functor) Y (Subst_functor X LeftAdjunc_functor) *
funcTransf (Id_rel Y (Subst_functor (Subst_functor X LeftAdjunc_functor) RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D)) Y (Subst_functor X LeftAdjunc_functor) .

(* “ϕ∘F(“γ∘(g)”)”             = “1∘F(g)”  *) (* OK *)
Check fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C) B (Y : functor B C) =>
Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor  X Y
: funcTransf (Id_rel Y X) (Id_rel LeftAdjunc_functor (Id_functor D)) Y (Subst_functor X LeftAdjunc_functor).


(*** “(f)∘ϕ” <∘ “1∘F(g)” =         f <∘ “ϕ∘F(g)” *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A D)
 A' (K : functor A' C) A'' (M : functor A'' A') (N : functor A'' A) 
 (g : transf (Id_rel K (Subst_functor X (RightAdjunc_functor))) M N ) B (Y : functor B D) =>
( CoUnitAdjunc_Comp_antec_funcTransf'' adj (Subst_functor N X) Y,
 Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor (Subst_functor X RightAdjunc_functor) K)) Y )
: funcTransf (Id_rel (Subst_functor N X) Y)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor (Subst_functor N X) RightAdjunc_functor) Y *
funcTransf (Id_rel (Subst_functor N (Subst_functor (Subst_functor X RightAdjunc_functor) LeftAdjunc_functor)) Y)
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M K) Y .

(* “(f)∘ϕ” <∘ “1∘F(g)”             =  f <∘ “ϕ∘F(g)” *) (* OK *) 
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A D)
A' (K : functor A' C) A'' (M : functor A'' A') (N : functor A'' A) 
(g : transf (Id_rel K (Subst_functor X (RightAdjunc_functor))) M N ) B (Y : functor B D) =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj K X)) Y.


(*** “ϕ∘F(“G(f)∘γ”)”  =            id(f) *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D) (* A'' (M : functor A'' A') (N : functor A'' A) 
 (f : transf (Id_rel (Subst_functor X (LeftAdjunc_functor)) K) N M ) *) =>
( UnitAdjunc_Comp_antec_funcTransf'' adj X K,
 CoUnitAdjunc_Comp_conse_funcTransf'' adj X K )
:  funcTransf (Id_rel (Subst_functor X LeftAdjunc_functor) K)
(Id_rel (Id_functor C) RightAdjunc_functor) X K *
funcTransf (Id_rel X (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D)) X K .

(* “ϕ∘F(“G(f)∘γ”)”             =  id(f) *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D)  =>
Id_funcTransf (Id_rel LeftAdjunc_functor (Id_functor D)) X K
: funcTransf (Subst_rel (Id_rel LeftAdjunc_functor (Id_functor D)) X K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K.


(*** h <∘ “(g)∘ϕ” =                   “(h <∘ g)∘ϕ”    *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' D) A''  (M : functor A'' A) (N : functor A'' A')
(g : transf (Id_rel X Y) M N) B (Z: functor B D)  =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_antec_funcTransf'' adj X Y)) Z
: funcTransf (Id_rel (Subst_functor N Y) Z)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor M (Subst_functor X RightAdjunc_functor)) Z.

(* h <∘ “(g)∘ϕ”                      =  “(h <∘ “1(g)∘I”)∘ϕ”    *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' D) A''  (M : functor A'' A) (N : functor A'' A')
(g : transf (Id_rel (Subst_functor X (Id_functor _)) Y) M N) B (Z: functor B D)  =>
( Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' (Id_functor _) X Y)) Z ,
 CoUnitAdjunc_Comp_antec_funcTransf'' adj (Subst_functor M X) Z ).


(* todo: “I∘1(f)” = id(f)   ;  “1(f)∘I” = id(f)* ;  “1(f)∘F” = id(f)(? := ?) *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D)  =>
 ( Id_antec_Comp_antec_funcTransf'' LeftAdjunc_functor X K,
 Id_funcTransf (Id_rel LeftAdjunc_functor (Id_functor D)) X K   )
:  funcTransf (Id_rel (Subst_functor X LeftAdjunc_functor) K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K *
funcTransf (Subst_rel (Id_rel LeftAdjunc_functor (Id_functor D)) X K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K .


End Example.