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
 */

symbol Prop : TYPE;
injective symbol Prf : Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

constant symbol Cat : TYPE;
constant symbol Functor : Cat → Cat → TYPE;
constant symbol Object : Cat → TYPE;
constant symbol Rel : Cat → Cat → TYPE;
constant symbol Transf : Π  [C A B: Cat], Rel A B →  Functor C A →  Functor C B → TYPE;
constant symbol Adjunc : Π [C], Π [ D: Cat], Functor C D → Functor D C → TYPE;

inductive object: Π (C : Cat), TYPE ≔
| Gen_object : Π [C : Cat], Object C → object C
| App_object : Π [C D: Cat], object C → functor C D →  object D

with functor: Π (C D : Cat), TYPE ≔
| Gen_functor : Π [C D : Cat], Functor C D → functor C D
| Id_functor : Π C : Cat, functor C C
| App_functor : Π [C D E: Cat], Functor C D → functor D E →   functor C E 

with rel: Π (C D : Cat), TYPE ≔
| Gen_rel : Π [C D : Cat], Rel C D → rel C D
| Tensor_rel : Π [A B C : Cat], rel C B → rel B A → rel C A
| Id_rel :  Π [C C' D' : Cat], functor C' C → functor D' C → rel C' D'
| Imply_antec_rel : Π  [A C B], rel A C → rel B C → rel B A
| Imply_conse_rel : Π  [C A B], rel C A → rel C B → rel A B;

symbol Subst_functor : Π [C D E: Cat], functor C D → functor D E →   functor C E;
symbol Subst_rel : Π [C D C' D': Cat], rel C D → functor C' C → functor D' D →  rel C' D' ;

inductive adjunc : Π [C D: Cat], functor C D → functor D C → TYPE ≔ 

| Gen_adjunc : Π [C D: Cat] (LeftAdjunc_functor : Functor C D) (RightAdjunc_functor : Functor D C), 
  adjunc (Gen_functor LeftAdjunc_functor) (Gen_functor RightAdjunc_functor)

with arrow: Π [A B: Cat], rel A B → object A → object B → TYPE ≔

| App_arrow : Π [C A B: Cat], Π (R : rel A B) (F : functor C A) (G : functor C B),
  Π (X : object C), transf R F G → arrow R (App_object X F) (App_object X G)

with transf:  Π [C A B: Cat], rel A B → functor C A → functor C B → TYPE ≔

| Id_antec_transf' :  Π [E C: Cat] (F : functor C E),  transf  (Id_rel F (Id_functor _) ) (Id_functor _)  F

| Id_conse_transf' : Π [E C: Cat] (F : functor C E),  transf (Id_rel (Id_functor _) F)  F (Id_functor _)

| App_transf : Π [C D C' D' A: Cat], Π [R : rel C D] [F : functor C C'] [S : rel C' D'] [G : functor D D'] [M : functor A C] [N : functor A D], 
    transf R M  N → funcTransf R S F G → transf S (Subst_functor M F) (Subst_functor N G)

| App_conse_transf : Π [C D D' A: Cat], Π [R : rel C D] [S : rel C D'] [G : functor A D'] [M : functor A C] [N : functor A D], 
    transf R M  N → funcTransf (Subst_rel R (Id_functor _) N) S (Id_functor C) G → transf S M G

| App_conse_transf' : Π [C D C' D' A: Cat], Π [R : rel C D] [S : rel C' D'] [K : functor C C'] [G : functor A D'] [M : functor A C] [N : functor A D], 
    transf R M  N → funcTransf (Subst_rel R (Id_functor _) N) S K G → transf S (Subst_functor M K) G

with funcTransf: Π [C D C' D': Cat], rel C D → rel C' D' → functor C C' → functor D D' → TYPE ≔  

| Subst_funcTransf : Π [C D C' D' C'' D'': Cat], Π [R : rel C D] [S : rel C' D'] [F : functor C C'] [G : functor D D']
  [T : rel C'' D''] [F' : functor C C''] [G' : functor D D''],
  funcTransf R S F G → funcTransf (Subst_rel S F G) T F' G' →  funcTransf R T F' G'

  | Comp_antec_funcTransf : Π [C A B: Cat], Π [R: rel A B] [F : functor C A] [G: functor C B],
  transf R F G → funcTransf (Id_rel G (Id_functor B)) R F (Id_functor B)

| Comp_conse_funcTransf : Π [C A B: Cat], Π [R: rel A B] [F : functor C A] [G: functor C B],
  transf R F G → funcTransf (Id_rel (Id_functor A) F) R (Id_functor A) G

  | Id_antec_Comp_antec_funcTransf' : Π [E C: Cat] (F : functor C E), 
  funcTransf (Id_rel F (Id_functor _)) (Id_rel F (Id_functor _) ) (Id_functor _)  (Id_functor _)

| Id_antec_Comp_conse_funcTransf' : Π [E C: Cat] (F : functor C E),
  funcTransf (Id_rel (Id_functor _) (Id_functor _)) (Id_rel F (Id_functor _) ) (Id_functor _)  F

  | Id_antec_Comp_conse_funcTransf'' : Π [E C A:  Cat] (F : functor C E) (K : functor A C),
  funcTransf (Id_rel K (Id_functor _)) (Id_rel F (Id_functor _) ) K  F

| Id_conse_Comp_antec_funcTransf' : Π [E C: Cat] (F : functor C E),
  funcTransf (Id_rel (Id_functor _) (Id_functor _)) (Id_rel (Id_functor _) F)  F (Id_functor _) 

| Id_conse_Comp_conse_funcTransf' : Π [E C: Cat] (F : functor C E),
  funcTransf (Id_rel (Id_functor _) F) (Id_rel (Id_functor _) F)  (Id_functor E) (Id_functor _) ;

rule  Subst_functor $F (Subst_functor $G $H)  ↪ Subst_functor (Subst_functor $F $G) $H  
with  Subst_functor $F (Id_functor _) ↪ $F
with  Subst_functor  (Id_functor _) $F ↪ $F;

rule Subst_rel (Id_rel $F $G) $H $K ↪  Id_rel (Subst_functor $H $F) (Subst_functor $K $G);

type λ [E C: Cat] [F : functor C E]    (M : functor C C)  (g : transf (Id_rel (Id_functor C) (Id_functor C)) M (Id_functor C)),
   ( App_conse_transf  g (Id_antec_Comp_conse_funcTransf' F ))   ;

type λ [E C: Cat] [F : functor C E]   (X : functor C C)   (g : transf (Id_rel X (Id_functor C)) (Id_functor _) X),
  ( App_transf  g (Id_antec_Comp_conse_funcTransf'' F X ))   ;

