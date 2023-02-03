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

