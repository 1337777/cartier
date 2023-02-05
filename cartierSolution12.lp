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
 
 inductive func: Π (C D : Cat), TYPE ≔
 | Id_func : Π C : Cat, func C C
 
 with hom: Π (C D : Cat), TYPE ≔
 | Unit_hom : Π [C C' D' : Cat], func C' C → func D' C → hom C' D'
 | Tensor_cov_hom : Π [A B C B' : Cat], hom C B → func B B' → hom B' A → hom C A
 | Imply_cov_hom : Π [A C B C' : Cat], hom B C → func C' C → hom A C' → hom B A;
 
 symbol Subst_func : Π [C D E: Cat], func C D → func D E → func C E;
 symbol Subst_hom /* admissible */ : Π [C D C' D': Cat], hom C D → func C' C → func D' D → hom C' D' ;
 
 rule  Subst_func $F (Subst_func $G $H)  ↪ Subst_func (Subst_func $F $G) $H  
 with  Subst_func $F (Id_func _) ↪ $F
 with  Subst_func  (Id_func _) $F ↪ $F;
 
 rule Subst_hom (Unit_hom $F $G) $H $K ↪  Unit_hom (Subst_func $H $F) (Subst_func $K $G)
 with Subst_hom (Tensor_cov_hom $R $H $S) $F $G ↪ Tensor_cov_hom (Subst_hom $R $F (Id_func _) ) $H (Subst_hom $S (Id_func _) $G) 
 with Subst_hom (Imply_cov_hom $R $H $S) $F $G ↪  Imply_cov_hom (Subst_hom $R  $F (Id_func _)) $H (Subst_hom $S $G (Id_func _));
 
 inductive adj : Π [C D: Cat], func C D → func D C → TYPE ≔
 
 with transf: Π [C A B: Cat], hom A B → func C A → func C B → TYPE ≔
 
 | Comp_transf /* admissible */ : Π [C D C' D' A : Cat] [R : hom C D] [F : func C C']
 [S : hom C' D'] [G : func D D'] [M : func A C] [N : func A D],
 transf R M N → morph R S F G → transf S (Subst_func M F) (Subst_func N G)
 
 | Subst_transf /* admissible */ : Π [C A B D : Cat] [R : hom A B] [F : func C A] 
 [G : func C B] (X : func D C),
 transf R F G → transf R (Subst_func X F) (Subst_func X G)
 
 | Id_transf : Π [E C D: Cat] (F : func C E) (X : func D C),
 transf (Unit_hom (Id_func E) F) (Subst_func X F) X
 
 | CoId_transf : Π [E C D : Cat] (F : func C E) (X : func D C),
 transf (Unit_hom F (Id_func E)) X (Subst_func X F)
 
 | UnitAdj_transf : Π [C D A : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
 adj LAdj_func RAdj_func → Π X : func A C,
 transf (Unit_hom (Id_func C) RAdj_func) X (Subst_func X LAdj_func)
 
 | CoUnitAdj_transf : Π [C D A : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
 adj LAdj_func RAdj_func → Π X : func A D,
 transf (Unit_hom LAdj_func (Id_func D)) (Subst_func X RAdj_func) X
 
 with morph: Π [C D C' D': Cat], hom C D → hom C' D' → func C C' → func D D' → TYPE ≔
 
 | Comp_morph /* admissible */ : Π [C D C' D' C'' D'': Cat], Π [R : hom C D] [S : hom C' D'] [F : func C C'] [G : func D D']
  [T : hom C'' D''] [F' : func C C''] [G' : func D D''],
  morph R S F G → morph (Subst_hom S F G) T F' G' → morph R T F' G'
 
 | Subst_morph /* admissible */ : Π [C D C' D' C'' D'' : Cat] [S : hom C' D'] [F' : func C' C'']
 [T : hom C'' D''] [G' : func D' D''] (X : func C C') (Y : func D D'),
 morph S T F' G' →
 morph (Subst_hom S X Y) T (Subst_func X F') (Subst_func Y G')
 
 | Id_morph : Π [C D C' D' : Cat] (R : hom C D) (F : func C' C) (G : func D' D),
 morph (Subst_hom R F G) R F G
 
 | UnitHom_cov_morph : Π [C A B B' : Cat] [F : func C A] [R : hom A B] [G : func C B],
 transf R F G → Π K : func B' B, morph (Unit_hom G K) R F K
 
 | UnitHom_con_morph : Π [C A B A' : Cat] [F : func C A] [R : hom A B] [G : func C B],
 transf R F G → Π K : func A' A, morph (Unit_hom K F) R K G
 
 | UnitHom_eval_cov_morph : Π [C D D' D0 C' : Cat] [H : func D D'] [R : hom C D] 
 [F : func C C'] [T : hom C' D'],
 morph R T F H → Π K : func D0 D',
 morph (Tensor_cov_hom R H (Unit_hom (Id_func D') K)) T F K
 
 | UnitHom_lam_cov_morph : Π [C D D0 C' D' : Cat] [H : func D D0] [R : hom C D] 
 [T : hom C' D'] [F : func C C'] [G : func D D'],
 morph (Tensor_cov_hom R H (Unit_hom (Id_func D0) H)) T F G →
 morph R T F G
 
 | Imply_eval_cov_morph : Π [C E D C' E' D' : Cat] [P : hom C E'] [R : hom E D'] 
 [S : hom C' D] [E'E : func E' E] [F : func C C'] [D'D : func D' D],
 morph P (Imply_cov_hom S D'D R) F E'E →
 morph (Tensor_cov_hom P E'E R) S F D'D
 
 | Imply_lam_cov_morph : Π [C E D C' E' D' : Cat] [P : hom C E'] [R : hom E D'] 
 [S : hom C' D] [E'E : func E' E] [F : func C C'] [D'D : func D' D],
 morph (Tensor_cov_hom P E'E R) S F D'D →
 morph P (Imply_cov_hom S D'D R) F E'E
 
 | Tensor_cov_morph : Π [D A C' C E E' A' : Cat] [S' : hom C' C] [R' : hom A A'] 
 [S : hom D A] [R : hom E E'] [F : func C A] [G : func A E] [H : func C' D] [K : func A' E'],
 morph S' S H F → morph R' R G K →
 morph (Tensor_cov_hom S' F R') (Tensor_cov_hom S G R) H K
 
 | Imply_cov_morph : Π [A A0 C0 B C' B' C'' C A1 : Cat] [S : hom B C'] 
 [R' : hom A0 C0] [S' : hom B' C''] [R : hom A C] 
 [L : func A A0] [H : func C C0] [G : func C' C''] [F : func B B'],
 morph S S' F G → morph R R' L H →
 Π (K : func C0 C') (M : func A1 A),
 morph (Imply_cov_hom S K (Subst_hom R' (Subst_func M L) (Id_func C0)))
  (Imply_cov_hom S' (Subst_func H (Subst_func K G)) R) F M
 
 /* from sol */
 
 | CoId_UnitHom_cov_morph : Π [E C A A' : Cat] (F : func C E) (X : func A C) (Y : func A' E),
 morph (Unit_hom (Subst_func X F) Y) (Unit_hom F (Id_func E)) X Y
 
 | CoId_UnitHom_con_morph : Π [E C A A' : Cat] (F : func C E) (Y : func A' C) (X : func A C),
 morph (Unit_hom Y X) (Unit_hom F (Id_func E)) Y (Subst_func X F)
 
 | Id_UnitHom_con_morph : Π [E C A A' : Cat] (F : func C E) (Y : func A' E) (X : func A C),
 morph (Unit_hom Y (Subst_func X F)) (Unit_hom (Id_func E) F) Y X
 
 | UnitAdj_UnitHom_cov_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
 adj LAdj_func RAdj_func → Π (X : func A C) (Y : func B D),
 morph (Unit_hom (Subst_func X LAdj_func) Y) (Unit_hom (Id_func C) RAdj_func) X Y
 
 | CoUnitAdj_UnitHom_cov_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
 adj LAdj_func RAdj_func → Π (X : func A D) (Y : func B D),
 morph (Unit_hom X Y) (Unit_hom LAdj_func (Id_func D)) (Subst_func X RAdj_func) Y
 
 | CoUnitAdj_UnitHom_con_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
 adj LAdj_func RAdj_func → Π (X : func A C) (Y : func B D),
 morph (Unit_hom X (Subst_func Y RAdj_func)) (Unit_hom LAdj_func (Id_func D)) X Y;
 
 symbol ==  [C D C' D': Cat] [R : hom C D] [S : hom C' D'] [F F' : func C C'] [G G' : func D D'] : morph R S F G  → morph R S F' G'  → TYPE;
 notation == infix 20;
 
 /* eval/app dinaturality ; redex  */
 type λ  (C E D : Cat)
 (C' : Cat)   (F : func C C') (S : hom C' D)
 E' (E'E : func E' E) (P : hom C E')
 D' (D'D : func D' D) (R : hom E D') C0 (C0C : func C0 C) D0 (D0D' : func D0 D')
 (ff : morph (Subst_hom P C0C (Id_func _)) (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F) E'E )
 E0 (E0E' : func E0 E')
 P' (pp : morph P' P C0C E0E') R' (rr : morph R' R E'E D0D') ,
 Comp_morph (Tensor_cov_morph pp rr ) (Imply_eval_cov_morph ff);
 /* : morph (Tensor_cov_hom P' E0E' R') S (Subst_func C0C F) (Subst_func D0D' D'D)  */
 
 /* eval/app dinaturality ; contractum */ /* todo:  first do the rules for the subst on morphisms */
 type λ  (C E D : Cat)
 (C' : Cat)   (F : func C C') (S : hom C' D)
 E' (E'E : func E' E) (P : hom C E')
 D' (D'D : func D' D) (R : hom E D') C0 (C0C : func C0 C) D0 (D0D' : func D0 D')
 (ff : morph (Subst_hom P C0C (Id_func _)) (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F ) E'E )
 E0 (E0E' : func E0 E')
 P' (pp : morph P' P C0C E0E') R' (rr : morph R' (Subst_hom R (Id_func _) D0D') E'E (Id_func _))
 /* todo: first do the rules for the subst on morphisms */
 (ff_restr : morph (Subst_hom P C0C E0E') (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F ) (Subst_func E0E' E'E)),
 Imply_eval_cov_morph
 (Comp_morph (Comp_morph pp ff_restr ) 
     (Imply_cov_morph  (Id_morph S  (Subst_func C0C F ) (Id_func _)) rr (Subst_func D0D' D'D) E0E' )) ;
 
 /*  : morph (Tensor_cov_hom P' E0E' R') S (Subst_func C0C F) (Subst_func (Id_func D0) (Subst_func (Subst_func D0D' D'D) (Id_func D))) */
 
 /*** “1∘FX(h)” <∘ “1∘F(g)”  =                     “1∘F(h X<∘ g)”       */
 type λ  (E C: Cat) (F : func C E) A (X : func A C)
 A' A''  (M : func A' A'') (N : func A' A) (Y : func A'' C)
 (g : transf (Unit_hom Y X) M N)  P (K: func P A),
 Comp_morph ( CoId_UnitHom_con_morph  (Subst_func X F)  N  K /* 1∘FX */)
 (UnitHom_cov_morph (Comp_transf g (CoId_UnitHom_con_morph F Y X)) (Subst_func K (Subst_func X F)) )
 == Comp_morph (UnitHom_cov_morph g K /* X<∘ */ ) 
 (CoId_UnitHom_con_morph F (Subst_func M Y) (Subst_func K X))  ;
 
 /*** “1∘F(h)” <∘ “1∘F(g)”  =                     “1∘F(h <∘ “1∘I(g)”)”        */
 type λ  (E C: Cat) (F : func C E) A (X : func A C)
 A' A''  (M : func A' A'') (N : func A' A) (Y : func A'' C)
 (g : transf (Unit_hom Y X) M N)  P (K: func P A),
 Comp_morph (CoId_UnitHom_con_morph F (Subst_func N X) (Subst_func K X))
 (UnitHom_cov_morph (Comp_transf g (CoId_UnitHom_con_morph F Y X)) (Subst_func K (Subst_func X F)) )
 == Comp_morph (UnitHom_cov_morph (Comp_transf g (Id_UnitHom_con_morph (Id_func _) Y X)) (Subst_func K X) ) 
 (CoId_UnitHom_con_morph F (Subst_func M Y) (Subst_func K X))  ;
 
 
 /***   “1∘F(g)” ∘>F h =                     “1∘F”( “I∘1(g)” ∘> h )  */ /* OK */
  type λ (E C: Cat) (F : func C E) A (X : func A C)
  A' A''  (M : func A' A'') (N : func A' A) (Y : func A'' C)
  (g : transf (Unit_hom Y X) M N) P (K: func P C)  ,
 UnitHom_con_morph (Comp_transf g (CoId_UnitHom_con_morph F Y X)) K ==
 Comp_morph ( UnitHom_con_morph (Comp_transf g (Id_UnitHom_con_morph (Id_func _) Y X)) K)
   (CoId_UnitHom_con_morph F K (Subst_func N X) );
 
 /* todo: try  “1(g)∘G”  =  id(g)   then   “1(g)∘G” ∘>G “1∘F(h)” =   g ∘>GFY  ?  */
 
 /***   “1(g)∘G” ∘>G “1∘F(h)” =                    “1(“1(g)∘GF” ∘>GF h)∘G”   */ /* OK */
 type λ (E C: Cat) (F : func C E) E' (G : func E E') A (X : func A E')
 A' A''  (M : func A' A'') (N : func A' A) (Y : func A'' C)
 (g : transf (Unit_hom  (Subst_func (Subst_func Y F) G) X) M N) P (K: func P _)  ,
 Comp_morph  (  CoId_UnitHom_con_morph F K (Subst_func M Y) )
 (UnitHom_con_morph (Comp_transf g (CoId_UnitHom_cov_morph G (Subst_func Y F) X)) (Subst_func K F) )
 == Comp_morph ( UnitHom_con_morph (Comp_transf g (CoId_UnitHom_cov_morph (Subst_func F G) Y X)) K )
 (CoId_UnitHom_cov_morph G (Subst_func K F) (Subst_func N X) );
 
 
 /*** “ϕ∘F(g)” ∘>F h =                “ϕ∘F(“I∘1(g)” ∘> h)” */  /* OK */ /* instance included: “(“ϕ∘F”g)∘FY”h =                   “ϕ∘F”(“g∘Y”h) */
 type λ  (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C) (adj: adj LAdj_func RAdj_func )
  A (X : func A D)
  A' A''  (M : func A' A'') (N : func A' A) (Y : func A'' C)
  (g : transf (Unit_hom Y (Subst_func X RAdj_func)) M N)  P (K: func P C)  ,
 UnitHom_con_morph (Comp_transf g (CoUnitAdj_UnitHom_con_morph adj Y X)) K
 == Comp_morph ( UnitHom_con_morph (Comp_transf g (Id_UnitHom_con_morph (Id_func _) Y (Subst_func X RAdj_func))) K )
 (CoUnitAdj_UnitHom_con_morph adj K (Subst_func N X) );
 
 
 /*** alt: “ϕ∘F(g)” <∘ “1∘F(h)” =                “ϕ∘F( g <∘ “I∘1(h)” )” */  /* OK */
 type λ  (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C) (adj: adj LAdj_func RAdj_func )
  A A' (X : func A' C) (Y : func A C)
  B (M : func B A') (N : func B A)
  (h: transf (Unit_hom X Y) M N  )  P (K: func P D)  ,
  Comp_morph  ( CoUnitAdj_UnitHom_con_morph adj (Subst_func N Y) K )
  (UnitHom_cov_morph (Comp_transf h (CoId_UnitHom_con_morph LAdj_func X Y )) K )
  ==  Comp_morph ( UnitHom_cov_morph (Comp_transf h (Id_UnitHom_con_morph (Id_func _ ) X Y)) (Subst_func K RAdj_func))
  (CoUnitAdj_UnitHom_con_morph adj (Subst_func M X) K  );
 
 
 /*** h <∘ “ϕ∘F(g)” =                “ϕ∘F( h G<∘ “G∘1(g)” )” */  /* OK */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C) (adj: adj LAdj_func RAdj_func )
 A (X : func A D) A' (Y : func A' C) A''  (M : func A'' A') (N : func A'' A)
 (g : transf (Unit_hom Y (Subst_func X RAdj_func)) M N) P (K: func P D)   ,
 UnitHom_cov_morph (Comp_transf g (CoUnitAdj_UnitHom_con_morph adj Y X )) K
 == Comp_morph ( UnitHom_cov_morph (Comp_transf g (Id_UnitHom_con_morph RAdj_func Y X)) K )
 (CoUnitAdj_UnitHom_con_morph adj (Subst_func M Y) K );
 
 
 /*** “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   */ /* OK */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C)
 (adj: adj LAdj_func RAdj_func ) A (X : func A C) B (Y : func B C)  ,
 Comp_morph (UnitHom_con_morph (UnitAdj_transf adj X) Y)
 (CoUnitAdj_UnitHom_con_morph adj Y (Subst_func X LAdj_func)  )
 == CoId_UnitHom_con_morph LAdj_func  Y  X;
 
 
 /*** “(f)∘ϕ” <∘ “1∘F(g)” =         f <∘ “ϕ∘F(g)” */ /* OK */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C)
 (adj: adj LAdj_func RAdj_func ) A (X : func A D)
  A' (K : func A' C) A'' (M : func A'' A') (N : func A'' A)
  (g : transf (Unit_hom K (Subst_func X (RAdj_func))) M N ) B (Y : func B D)  ,
 Comp_morph ( CoUnitAdj_UnitHom_cov_morph adj (Subst_func N X) Y)
 ( UnitHom_cov_morph (Comp_transf g (CoId_UnitHom_con_morph LAdj_func K (Subst_func X RAdj_func))) Y )
 == UnitHom_cov_morph (Comp_transf g (CoUnitAdj_UnitHom_con_morph adj K X)) Y;
 
 
 /*** “ϕ∘F(“G(f)∘γ”)”  =            id(f) */ /* OK */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C)
 (adj: adj LAdj_func RAdj_func ) A (X : func A C)
  A' (K : func A' D) /* A'' (M : func A'' A') (N : func A'' A)
  (f : transf (Unit_hom (Subst_func X (LAdj_func)) K) N M ) */  ,
 Comp_morph ( UnitAdj_UnitHom_cov_morph adj X K)
 (CoUnitAdj_UnitHom_con_morph adj X K )
 == Id_morph (Unit_hom LAdj_func (Id_func D)) X K;
 
 
 /*** h <∘ “(g)∘ϕ” =                   “(h <∘ g)∘ϕ”    */  /* OK */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C) (adj: adj LAdj_func RAdj_func )
 A (X : func A D) A' (Y : func A' D) A''  (M : func A'' A) (N : func A'' A')
 (g : transf (Unit_hom X Y) M N) B (Z: func B D)   ,
 UnitHom_cov_morph (Comp_transf g (CoUnitAdj_UnitHom_cov_morph adj X Y)) Z
 == Comp_morph ( UnitHom_cov_morph (Comp_transf g (CoId_UnitHom_cov_morph (Id_func _) X Y)) Z )
  (CoUnitAdj_UnitHom_cov_morph adj (Subst_func M X) Z );
 
 
 /* todo: “I∘1(f)” = id(f)   ;  “1(f)∘I” = id(f)* ;  “1(f)∘F” = id(f)(? := ?) */
 type λ (C D: Cat) (LAdj_func : func C D) (RAdj_func : func D C)
 (adj: adj LAdj_func RAdj_func ) A (X : func A C)
  A' (K : func A' D)   ,
   CoId_UnitHom_cov_morph LAdj_func X K
  == Id_morph (Unit_hom LAdj_func (Id_func D)) X K  ;
 
 