/* TODO: these are unfinished prototypes for demo that it does work

https://github.com/1337777/cartier/blob/master/cartierSolution12.v (laggin version; experiment file)
https://github.com/1337777/cartier/blob/master/cartierSolution12.lp (head version; future primary file; must use LambdaPi for modulo structural coherence)

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
 
 inductive func: Π (A B : Cat), TYPE ≔
 | Id_func : Π [A : Cat], func A A
 
 with mod: Π (A B : Cat), TYPE ≔
 | Unit_mod : Π [X A B : Cat], func A X → func B X → mod A B
 | Tensor_cov_mod : Π [A B C X : Cat], mod A B → func B C → mod C X → mod A X
 | Tensor_con_mod : Π [A B C X : Cat], mod X C → func A C → mod A B → mod X B
 | Imply_cov_mod : Π [A B C X : Cat], mod A B → func C B → mod X C → mod A X
 | Imply_con_mod : Π [A B C X : Cat], mod C X → func C A → mod A B → mod X B;
 
 /* injective */ symbol Subst_func : Π [A B C: Cat], func A B → func B C → func A C;
 symbol Subst_cov_mod : Π [A X C: Cat], mod A X → func C X → mod A C;
 symbol Subst_con_mod : Π [X B C: Cat], func C X → mod X B → mod C B;
 
 symbol _1<∘ : Π [X B : Cat], func B X → mod X B ≔ λ _ _ F, Unit_mod Id_func F;
 notation _1<∘ prefix 100;
 
 symbol ∘>1_ : Π [X A : Cat], func A X → mod A X ≔ λ _ _ F, Unit_mod F Id_func;
 notation ∘>1_ postfix 100;
 
 symbol ∘> : Π [A B C: Cat], func A B → func B C → func A C ≔ @Subst_func;
 notation ∘> infix right 80;
 symbol <∘ : Π [A B C: Cat], func B C → func A B → func A C 
   ≔ λ _ _ _ G F, Subst_func F G;
 notation <∘ infix left 80;
 
 symbol ∘>> : Π [X B C: Cat], func C X → mod X B → mod C B ≔ @Subst_con_mod;
 notation ∘>> infix right 80;
 symbol <<∘ : Π [A X C: Cat], mod A X → func C X → mod A C ≔ @Subst_cov_mod;
 notation <<∘ infix left 80;
 
 rule Subst_func (Subst_func $F $G) $H ↪ Subst_func $F (Subst_func $G $H)
 with Subst_func $F Id_func ↪ $F
 with Subst_func Id_func $F ↪ $F;
 
 
 rule Subst_cov_mod (Unit_mod $F $G) $K ↪ Unit_mod $F ($G <∘ $K)
 with Subst_cov_mod (Tensor_cov_mod $R $H $S) $G ↪ Tensor_cov_mod $R $H (Subst_cov_mod $S $G)
 with Subst_cov_mod (Tensor_con_mod $R $H $S) $G ↪ Tensor_con_mod $R $H (Subst_cov_mod $S $G)
 with Subst_cov_mod (Imply_cov_mod $R $H $S) $G ↪ Imply_cov_mod $R $H (Subst_con_mod $G $S)
 with Subst_cov_mod (Imply_con_mod $R $H $S) $G ↪ Imply_con_mod $R $H (Subst_cov_mod $S $G);
 
 rule Subst_con_mod $K (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G
 with Subst_con_mod $G (Tensor_con_mod $R $H $S) ↪ Tensor_con_mod (Subst_con_mod $G $R) $H $S
 with Subst_con_mod $G (Tensor_cov_mod $R $H $S) ↪ Tensor_cov_mod (Subst_con_mod $G $R) $H $S
 with Subst_con_mod $G (Imply_con_mod $R $H $S) ↪ Imply_con_mod (Subst_cov_mod $R $G) $H $S
 with Subst_con_mod $G (Imply_cov_mod $R $H $S) ↪ Imply_cov_mod (Subst_con_mod $G $R) $H $S;
 
 /* provable */
 rule Subst_cov_mod $R Id_func ↪ $R  // ?? careful, this indirely unify stuff?
 with Subst_cov_mod (Subst_cov_mod $R $H) $K ↪ Subst_cov_mod $R ($H <∘ $K); 
 
 rule Subst_con_mod Id_func $R ↪ $R  // ?? careful, this indirely unify stuff?
 with Subst_con_mod $K (Subst_con_mod $H $R) ↪ Subst_con_mod ($K ∘> $H) $R; 
 
 rule Subst_cov_mod (Subst_con_mod $F $R) $G ↪ (Subst_con_mod $F (Subst_cov_mod $R $G));
 
 /* =========================== */
 
 inductive adj : Π [R L : Cat], func R L → func L R → TYPE ≔
 
 with hom: Π [I A B : Cat], func I A → mod A B → func I B → TYPE ≔
 
 | Id_cov_hom : Π [A B I : Cat] (F : func B A) (Z : func I B),
 hom Z (F ∘>1_ ) (F <∘ Z)
 
 | Id_con_hom : Π [A B I : Cat] (F : func B A) (Z : func I B),
 hom (Z ∘> F) ( _1<∘ F) Z
 
 | UnitAdj_cov_hom : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I L),
 hom (Z ∘> RAdj_func) (LAdj_func ∘>1_ ) Z
 
 | UnitAdj_con_hom : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I R),
 hom Z ( _1<∘ RAdj_func) (LAdj_func <∘ Z)
 
 with transf: Π [A' B' A B: Cat], mod A' B' → func A' A → mod A B → func B' B → TYPE ≔
 
 //TODO ERASE Id_cov_transf ,  Id_con_transf  because too semantic and can derive structural operations
 | Id_cov_transf : Π [A X A' : Cat] (R : mod A X) (F : func A' A),
 transf (F ∘>> R) F R Id_func
 
 | Id_con_transf : Π [X B B' : Cat] (R : mod X B) (G : func B' B),
 transf (R <<∘ G) Id_func R G
 
 | UnitMod_cov_transf : Π [I A B : Cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → transf (G ∘>1_ ) F R Id_func
 
 | UnitMod_cov_trans_test1 : Π [I A B J : Cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → Π (N: func J B), transf (G ∘>1_ <<∘ N ) F R N
 
 | UnitMod_con_transf : Π [I A B : Cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → transf ( _1<∘ F) Id_func R G
 
 | UnitMod_con_trans_test1 : Π [I A B J : Cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( M ∘>> _1<∘ F) M R G
 
 | UnitMod_Tensor_cov_transf : Π [A B A' X : Cat] [P : mod A B] [P' : mod A' X] [F : func A A'] [K : func B X],
 transf P F P' K → 
 transf (Tensor_cov_mod P K ( _1<∘ Id_func)) F P' Id_func
 
 | Eval_cov_transf : Π [A B C X A' X' : Cat] [P : mod A B] [Q : mod C X] 
 [O : mod A' X'] [K : func B C] [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) K →
 transf (Tensor_cov_mod P K Q)  F O                     L
 
 | Lambda_cov_transf : Π [A B C X A' X' : Cat] [P : mod A B] [Q : mod C X] 
 [O : mod A' X'] [K : func B C] [F : func A A'] [L : func X X'],
 transf (Tensor_cov_mod P K Q) F O L →
 transf P F (Imply_cov_mod O L Q) K 
 
 | Tensor_cov_transf : Π [A' B' X' A B C X : Cat] [P' : mod A' B'] [Q' : mod B X'] 
 [P : mod A B] [Q : mod C X] [K' : func B' B] [F : func A' A] [K : func B C] [G : func X' X],
 transf P' F P K' → transf Q' K Q G →
 transf (Tensor_cov_mod P' K' Q') F (Tensor_cov_mod P K Q) G
 
 | Tensor_hom_cov_transf : Π [A' I X' A C X : Cat] [P' : mod A' I]
 [P : mod A I] [Q : mod C X] [F : func A' A] [K : func I C] [G : func I X],
 transf P' F P Id_func → hom K Q G →
 transf P' F (Tensor_cov_mod P K Q) G
 
 | Imply_cov_transf : Π [A B A' B' C D C' D' C0 : Cat] [O : mod A B] [O' : mod A' B']
  [Q : mod C D] [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func D D'],
 transf O F O' G → Π (K : func D' B), transf Q H Q' L → Π (N: func C0 C),
 transf   (Imply_cov_mod O K (N ∘>> (H ∘>> Q')))
        F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) N
 
 // | Imply_cov_transf : Π [A B A' B' C D C' D' : Cat] [O : mod A B] [O' : mod A' B']
 //  [Q : mod C D] [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func D D'],
 // transf O F O' G → Π (K : func D' B), transf Q H Q' L → 
 // transf   (Imply_cov_mod O K (H ∘>> Q'))
 //        F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) Id_func
 
 | Imply_hom_cov_transf : Π [A B A' B' C C' D' C0 : Cat] [O : mod A B] [O' : mod A' B']
   [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func C D'],
 transf O F O' G → Π (K : func D' B), hom H Q' L → Π (N: func C0 C),
 transf   (Imply_cov_mod O K (N ∘>> (H ∘>> Q')))
        F (O' <<∘ ((G <∘ K) <∘ L)) N
 
 // | Imply_hom_cov_transf : Π [A B A' B' C C' D' : Cat] [O : mod A B] [O' : mod A' B']
 //   [Q' : mod C' D'] [F : func A A'] [G : func B B'] [H : func C C'] [L : func C D'],
 // transf O F O' G → Π (K : func D' B), hom H Q' L →
 // transf   (Imply_cov_mod O K (H ∘>> Q'))
 //        F (O' <<∘ ((G <∘ K) <∘ L)) Id_func
 
 /* from sol */
 | Id_cov_UnitMod_cov_transf : Π [A B I : Cat] (F : func B A) (Z : func I B),
 transf ((Z ∘> F) ∘>1_ ) Z (F ∘>1_ ) Id_func
 
 | Id_cov_UnitMod_con_transf : Π [A B I : Cat] (F : func B A) (Z : func I B),
 transf ( _1<∘ Z) Id_func (F ∘>1_ ) (F <∘ Z)
 
 | Id_con_UnitMod_cov_transf : Π [A B I : Cat] (F : func B A) (Z : func I B),
 transf (Z ∘>1_ ) (Z ∘> F) ( _1<∘ F) Id_func
 
 | Id_con_UnitMod_con_transf : Π [A B I : Cat] (F : func B A) (Z : func I B),
 transf ( _1<∘ (F <∘ Z)) Id_func ( _1<∘ F) Z
 
 | Id_con_UnitMod_con_trans_test2 : Π [A B I J : Cat] (F : func B A) (M : func J _) (Z : func I B) ,
 transf ( M ∘>> _1<∘ (F <∘ Z)) Id_func ( M ∘>> _1<∘ F) Z
 
 | UnitAdj_cov_UnitMod_cov_transf : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I L),
 transf (Z ∘>1_ ) (Z ∘> RAdj_func) (LAdj_func ∘>1_ ) Id_func
 
 | UnitAdj_cov_UnitMod_cov_trans_test1: Π [L R I J : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I L) (M : func J L),
 transf (Z ∘>1_ <<∘ M ) (Z ∘> RAdj_func) (LAdj_func ∘>1_ ) M
 
 | UnitAdj_cov_UnitMod_con_transf : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I L),
 transf ( _1<∘ (RAdj_func <∘ Z)) Id_func (LAdj_func ∘>1_ ) Z
 
 
 | UnitAdj_cov_UnitMod_con_trans_test1 : Π [L R I J : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (M : func J R) (Z : func I L),
 transf ( M ∘>> _1<∘ (RAdj_func <∘ Z)) M (LAdj_func ∘>1_ ) Z
 
 | UnitAdj_cov_UnitMod_con_trans_test2 : Π [L R I J : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (M : func J R) (Z : func I L),
 transf ( M ∘>> _1<∘ (RAdj_func <∘ Z)) Id_func ( M ∘>> LAdj_func ∘>1_ ) Z
 
 
 | UnitAdj_con_UnitMod_cov_transf : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I R),
 transf ((Z ∘> LAdj_func) ∘>1_ ) Z ( _1<∘ RAdj_func) Id_func
 
 | UnitAdj_con_UnitMod_con_transf : Π [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 adj LAdj_func RAdj_func → Π (Z : func I R),
 transf ( _1<∘ Z) Id_func ( _1<∘ RAdj_func) (LAdj_func <∘ Z)
 ;
 
 symbol Comp_cov_hom : Π [A' B' A B I : Cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func I A] [G : func B' B],
 hom X S Y → transf (X ∘>> S) F T G → hom F T (Y ∘> G);
 
 symbol Comp_con_hom : Π [A' B' A B I : Cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func I B],
 hom X S Y → transf (S <<∘ Y) F T G → hom (X ∘> F) T G;
 
 // TODO: admissible
 symbol Subst_hom : Π [I A B I' : Cat] [R : mod A B] [F : func I A] 
 [G : func I B] (X : func I' I),
 hom F R G → hom (X ∘> F) R (G <∘ X);
 
 symbol ∘>' [A' B' A B I : Cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func I A] [G : func B' B]:
 transf (X ∘>> S) F T G → hom X S Y → hom F T (Y ∘> G)
  ≔ λ st s, Comp_cov_hom s st;
 notation ∘>' infix right 80;
 
 symbol '∘> : Π [A' B' A B I : Cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func I B],
 hom X S Y → transf (S <<∘ Y) F T G → hom (X ∘> F) T G
   ≔ @Comp_con_hom ;
 notation '∘> infix left 80;
 
 
 symbol Comp_cov_transf : Π [A'' B'' A' B' A B : Cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A'' A] [G : func B' B],
 transf R X S Y → transf (X ∘>> S) F T G → transf R F T (G <∘ Y);
 
 symbol Comp_con_transf : Π [A'' B'' A' B' A B : Cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B'' B],
 transf R X S Y → transf (S <<∘ Y) F T G → transf R (X ∘> F) T G;
 
 /* admissible until accumulated into the basic transf */
 symbol Subst_cov_transf : Π [A' B' A B B'' : Cat] [S : mod A' B'] [T : mod A B] 
  [F : func A' A] [G : func B' B],
  transf S F T G → Π (Y : func B'' B'), transf (S <<∘ Y) F T (G <∘ Y);
 
 symbol Subst_con_transf : Π [A' B' A B A'' : Cat] [S : mod A' B'] [T : mod A B] 
  [F : func A' A] [G : func B' B], 
  Π (X : func A'' A'), transf S F T G → transf (X ∘>> S) (X ∘> F) T G;
 
 symbol ∘>>' [A'' B'' A' B' A B : Cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A'' A] [G : func B' B] :
  transf (X ∘>> S) F T G → transf R X S Y → transf R F T (G <∘ Y) 
  ≔ λ st rs, Comp_cov_transf rs st;
 notation ∘>>' infix right 80;
 
 symbol ∘>>'' [B'' A' B' A B : Cat] [R : mod A' B''] [S : mod A' B'] [T : mod A B] 
  [Y : func B'' B'] [F : func A' A] [G : func B' B] :
  transf S F T G → transf R Id_func S Y → transf R F T (G <∘ Y) 
  ≔ λ st rs, Comp_cov_transf rs st;
 notation ∘>>'' infix right 80;
 
 symbol '∘>> : Π [A'' B'' A' B' A B : Cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B'' B],
 transf R X S Y → transf (S <<∘ Y) F T G → transf R (X ∘> F) T G
   ≔ @Comp_con_transf ;
 notation '∘>> infix left 80;
 
 symbol ''∘>> [A'' A' B' A B : Cat] [R : mod A'' B'] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [F : func A' A] [G : func B' B] :
 transf R X S Id_func → transf S F T G → transf R (X ∘> F) T G
   ≔ λ rs st, Comp_con_transf rs st;
 notation ''∘>> infix left 80;
 
 
 symbol _'∘> : Π [I A B J : Cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( M ∘>> _1<∘ F) M R G
 ≔ @UnitMod_con_trans_test1 ;
 notation _'∘> infix left 80;
 
 // symbol _'∘>adjCov^ : Π [L R I J : Cat] [LAdj_func : func R L] [RAdj_func : func L R],
 // adj LAdj_func RAdj_func → Π (M : func J R) (Z : func I L),
 // transf ( M ∘>> _1<∘ (RAdj_func <∘ Z)) M (LAdj_func ∘>1_ ) Z
 // ≔ @UnitAdj_cov_UnitMod_con_trans_test1;
 
 /* ========================== */
 
 /* derivable operations */
 symbol Id_transf [A B A' B' : Cat] (R : mod A B) (F : func A' A) (G : func B' B) :
   transf (F ∘>> (R <<∘ G)) F R G ≔ 
 (Id_cov_transf R F) ∘>>' (Id_con_transf (F ∘>> R) G);
 
 /*todo: old erase
  symbol UnSubst_cov_hom [I A B B' : Cat] (R : mod A B) [F : func I A] 
  [G' : func I B'] (G : func B' B) (r : hom F (R <<∘ G) G') : 
   hom F R (G <∘ G') ≔ 
 (Id_transf R F G) ∘>' r;
  */
 symbol UnSubst_cov_hom [I A B B' : Cat] (R : mod A B) [F : func I A] 
  [G' : func I B'] (G : func B' B) (r : hom F (R <<∘ G) G') : 
   hom F R (G <∘ G') ≔ 
  r '∘> (Id_con_transf R (G <∘ G'));
 
 
 /*todo: old erase
   symbol UnSubst_cov_transf [A' B'' A B B' : Cat] [S : mod A' B''] (R : mod A B) [F : func A' A] 
 [G' : func B'' B'] (G : func B' B) (r : transf S F (R <<∘ G) G') :
   transf S F R (G' ∘> G) ≔ 
 Id_transf R F G ∘>>' r; */
 
 /* compare _ ∘>>' _ there in restriction vs  _ '∘>> _ here */
 symbol UnSubst_cov_transf [A' B'' A B B' : Cat] [S : mod A' B''] (T : mod A B) [F : func A' A] 
 [G' : func B'' B'] (G : func B' B) (st : transf S F (T <<∘ G) G') :
   transf S F T (G' ∘> G) ≔ 
 st '∘>> (Id_con_transf T (G <∘ G'));
 
 /* TODO: relate UnSubst_cov_transf with UnSubst_cov_hom  and UnitMod*/
 
 /* unif_rule Subst_func $G' $G ≡ Subst_func $F' $F ↪ [ $G' ≡ $F'; $G ≡ $F ];
 unif_rule Subst_func $F $G ≡ $F' ↪ [ $F' ≡ Subst_func $F Id_func ];
 
 symbol UnSubst_cov_transf' [A' B'' A B B' : Cat] [S : mod A' B''] [R : mod A B] [F : func A' A] 
 [G : func B' B] (G' : func B'' B') (r : transf S F (R <<∘ G) G') :
   transf S F R (G' ∘> G) ≔ 
 begin
   assume A' B'' A B B' S R F G G' r ;
   refine (r '∘>> _) { apply Id_func; } {} ;   apply Id_con_transf; proofterm;
 end;
 */
 
 symbol UnSubst_con_hom [I A B A' : Cat] (R : mod A B) [F' : func I A'] 
  [G : func I B] (F : func A' A) (r : hom F' (F ∘>> R) G) : 
   hom (F' ∘> F) R G ≔ 
   (Id_cov_transf R (F' ∘> F)) ∘>' r;
 
 /* compare _ ∘>>' _ there in restriction vs  _ '∘>> _ here */
 symbol UnSubst_con_transf [A'' B' A B A' : Cat] [S : mod A'' B'] (T : mod A B) [F' : func A'' A'] 
 [G : func B' B] (F : func A' A) (st : transf S F' (F ∘>> T) G) :
   transf S (F' ∘> F) T G ≔ 
 (Id_cov_transf T (F' ∘> F)) ∘>>' st;
 
 
 /* =================================== */
 
 /* conversions */
 // TODO: check for remaining Id_func in g : hom Id_func R N
 
 symbol ==> : Π [A' B' A B: Cat] [S : mod A' B'] [F : func A' A] [T : mod A B] [G :func B' B],
 transf S F T G → transf S F T G → TYPE;
 notation ==> infix 20;
 
 //BEGIN TEST +++++++++++++++++
 //TODO compositions with Subst_cov_transf ? Subst_cov_transf only as accumulated form?
 //HERE
 // transf (M ∘>> _1<∘ (X ∘> X0)) M (∘>1_ LAdj_func) Y
 //R1 test
 /*** “ϕ∘F(g)” ∘>F h =                “ϕ∘F(“I∘1(g)” ∘> h)” */  /* OK */ /* instance included: “(“ϕ∘F”g)∘FY”h =                   “ϕ∘F”(“g∘Y”h) */
 type λ [L R I J I' : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (M : func J I') (X: func I I') (X0: func I' R)(Y: func I L)
 (g : hom X ( X0 ∘>> _1<∘ RAdj_func) Y) , 
 (M)_'∘> (g '∘> (UnitAdj_cov_UnitMod_con_trans_test2 aj X0 Y))
 ==> ((M)_'∘> g) '∘>> (UnitAdj_cov_UnitMod_con_trans_test2 aj X0 Y);
 
 // (M)_'∘> (g '∘> (UnitAdj_cov_UnitMod_con_trans_test2 aj X0 Y));
 // transf (M ∘>> _1<∘ (X ∘> Id_func)) M (X0 ∘>> LAdj_func ∘>1_ ) Y
 // transf (M ∘>> _1<∘ X) (M ∘> Id_func) (X0 ∘>> LAdj_func ∘>1_ ) Y
 // test
 type λ [L R I J : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (M : func J R) (X: func I R) (X0: func R R)(Y: func I L)
 (g : hom X ( X0 ∘>> _1<∘ RAdj_func) Y) ,
  (M)_'∘> (g '∘> (UnitAdj_cov_UnitMod_con_trans_test1 aj X0 Y))
 ==> ((M)_'∘> (UnSubst_con_hom ( _1<∘ RAdj_func) X0 g)) '∘>> (UnitAdj_cov_UnitMod_con_trans_test1 aj Id_func Y);
 // : transf ( _1<∘ X) Id_func (LAdj_func ∘>1_ ) Y
 // : transf (M ∘>> _1<∘ (X ∘> Id_func)) M (∘>1_ LAdj_func) Y
 
 //transf (M ∘>> _1<∘ (X ∘> X0)) M (∘>1_ LAdj_func) Y
 //transf (M ∘>> _1<∘ X) (M ∘> X0) (∘>1_ LAdj_func) Y
 //END TEST +++++++++++++++++
 
 //B1
 /*** “ϕ∘F(g)” ∘>F h =                “ϕ∘F(“I∘1(g)” ∘> h)” */  /* OK */ /* instance included: “(“ϕ∘F”g)∘FY”h =                   “ϕ∘F”(“g∘Y”h) */
 /* “ϕ∘F(g)” ∘ - =                “ϕ∘F(g ∘ -)” */
 /*** note: alt input order would not be expressible: “ϕ∘F( G∘1( 1(-)∘XN )  )” <∘ “1∘F(h)” =  ...
     because requires both cov and con fixed, in other words that con is both fixed and free ... ??? OR NOT */ 
 type λ [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (X: func I R) (Y: func I L)
 (g : hom X ( _1<∘ RAdj_func) Y),
 UnitMod_con_transf (g '∘> (UnitAdj_cov_UnitMod_con_transf aj Y))
 ==> (UnitMod_con_transf g) '∘>> (UnitAdj_cov_UnitMod_con_transf aj Y);
 // : transf ( _1<∘ X) Id_func (LAdj_func ∘>1_ ) Y
 //todo: erase old generality not necessary type λ [L R I I' : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 // (aj : adj LAdj_func RAdj_func) (Z : func I L) (X: func I' R) (Y: func I' I)
 // (g : hom X ( _1<∘ (RAdj_func <∘ Z)) Y),
 // UnitMod_con_transf (g '∘> (UnitAdj_cov_UnitMod_con_transf aj (Z <∘ Y)))
 // ==> (UnitMod_con_transf g) '∘>> (UnitAdj_cov_UnitMod_con_transf aj (Z <∘ Y));
 
 //B2 ????
 /*** alt input order: 1(“ϕ∘F( - )”)∘XN <∘ “1∘F(h)” =                “ϕ∘F( G∘1(- <∘ I∘1(h)) )” */  /* OK */
 type λ  [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (X: func I R) (Y: func I L)
 (g : hom X ( _1<∘ RAdj_func) Y) (N: func R I)
 (h: hom Id_func ( _1<∘ X) N),
  (UnitMod_cov_transf (h '∘> (Id_cov_UnitMod_con_transf LAdj_func (X <∘ N)))) ∘>>'
    (Subst_con_transf (N ∘> X) (UnitAdj_cov_UnitMod_con_transf aj Y ))
 ==> (Subst_cov_transf (UnitMod_cov_transf (UnSubst_cov_hom ( _1<∘ Id_func) X h)) (RAdj_func <∘ Y)) '∘>> (UnitAdj_cov_UnitMod_con_transf aj Y ) ;
 // note Unit_mod convergence is used to unify these two domains
 // : transf ((N ∘> X) ∘>> _1<∘ (RAdj_func <∘ Y)) Id_func (LAdj_func ∘>1_ ) (Id_func <∘ Y)
 // : transf ( (X <∘ N) ∘>1_ <<∘ (RAdj_func <∘ Y)) Id_func (LAdj_func ∘>1_ ) Y
 
 //BEGIN TEST +++++++++++++++++
 //test
 type λ [L R I I' : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I L) (Y : func I' I) (X: func I' R) X0
 (g : hom X ( X0 ∘>> _1<∘ (RAdj_func <∘ Z)) Y),
 UnitMod_cov_transf (g '∘> (UnitAdj_cov_UnitMod_con_trans_test2 aj X0 (Z <∘ Y))) ==>
 (UnitMod_cov_transf (g '∘> (Id_con_UnitMod_con_trans_test2 RAdj_func X0 (Z <∘ Y))))
      '∘>> (UnitAdj_cov_UnitMod_con_trans_test2 aj X0 Id_func);
 //END TEST +++++++++++++++++
 
 // B3
 /*** h <∘ “ϕ∘F(g)” =                “ϕ∘F( h G<∘ “G∘1(g)” )” */  /* OK */
 type λ [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I L) (Y : func R I)
 (g : hom Id_func ( _1<∘ (RAdj_func <∘ Z)) Y),
 UnitMod_cov_transf (g '∘> (UnitAdj_cov_UnitMod_con_transf aj (Z <∘ Y))) ==>
 (UnitMod_cov_transf (g '∘> (Id_con_UnitMod_con_transf RAdj_func (Z <∘ Y))))
      '∘>> (UnitAdj_cov_UnitMod_con_transf aj Id_func);
 // transf ((Z <∘ Y) ∘>1_ ) (Id_func ∘> Id_func) (LAdj_func ∘>1_ ) Id_func
 
 // B4
 /*** “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   */ /* OK */
 // HERE argument Z is properly needed, (LAdj_func <∘ Z) cannot be Id_func
 type λ [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I R),
 (UnitAdj_con_UnitMod_con_transf aj Z) '∘>> (UnitAdj_cov_UnitMod_con_transf aj (LAdj_func <∘ Z)) ==>
 Id_cov_UnitMod_con_transf LAdj_func Z ;
 // : transf ( _1<∘ Z) (Id_func ∘> Id_func) (LAdj_func ∘>1_ ) (LAdj_func <∘ Z)
 
 
 // B5
 /*** “(-)∘ϕ” <∘ “1∘F(g)” =         - <∘ “ϕ∘F(g)” */ /* OK */
 type λ [L R : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Y : func R L)
 (g : hom Id_func ( _1<∘ RAdj_func) Y) ,
 (UnitMod_cov_transf (g '∘> (Id_cov_UnitMod_con_transf LAdj_func (RAdj_func <∘ Y))))
   ∘>>' (UnitAdj_cov_UnitMod_cov_transf aj Y)
 ==> UnitMod_cov_transf (g '∘> (UnitAdj_cov_UnitMod_con_transf aj Y));
         // : transf (Y ∘>1_ ) Id_func (LAdj_func ∘>1_ ) Id_func
 
 // use UnSubst_cov_hom to get for general (g : hom Id_func ( _1<∘ (RAdj_func <∘ Z)) Y)
 // type λ [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 // (aj : adj LAdj_func RAdj_func) (Z : func I L) (Y : func R I)
 // (g : hom Id_func ( _1<∘ (RAdj_func <∘ Z)) Y) ,
 // (UnitMod_cov_transf (g '∘> (Id_cov_UnitMod_con_transf LAdj_func ((RAdj_func <∘ Z) <∘ Y))))
 //   ∘>>' (UnitAdj_cov_UnitMod_cov_transf aj (Z <∘ Y))
 // ==> UnitMod_cov_transf (g '∘> (UnitAdj_cov_UnitMod_con_transf aj (Z <∘ Y)));
 
 
 // B6
 /*** “ϕ∘F(“G(f)∘γ”)”  =            id(f) */ /* OK */
 type λ [L R I : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I R),
 (UnitAdj_con_UnitMod_cov_transf aj Z) 
  '∘>> (UnitAdj_cov_UnitMod_con_transf aj Id_func)
 ==> Id_cov_transf (LAdj_func ∘>1_ ) Z;
 // : transf ((Z ∘> LAdj_func) ∘>1_ ) Z (LAdj_func ∘>1_ ) Id_func
 
 //B7
 /*** h <∘ “(g)∘ϕ” =                   “(h <∘ 1(g)∘I)∘ϕ”    */  /* OK */
 type λ [L R I I' : Cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I L) (X : func I' I) (Y : func I' L)
 (g : hom X (Z ∘>1_ ) Y),
 UnitMod_cov_transf ((UnitAdj_cov_UnitMod_cov_transf aj (X ∘> Z)) ∘>' g)
 ==> (UnitAdj_cov_UnitMod_cov_transf aj (X ∘> Z)) ∘>>' (UnitMod_cov_transf g);
 
 
 
 
 /* ============================================== */
 
 
 
 
 /* 00 */
 /* id ∘ f   = f */
 type λ [A'' A' B' A B : Cat] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [F : func A'' A] [G : func B' B] (st : transf (X ∘>> S) F T G),
 st ∘>>' (Id_cov_transf S X)
 ==> st;
 
 /* id_con ∘ f  = restriction of f ,  compare _ ∘>>' _ here in restriction vs  _ '∘>> _ there in UnSubst_cov_transf */
 type λ [B'' A' B' A B : Cat] [S : mod A' B'] [T : mod A B] 
  [Y : func B'' B'] [F : func A' A] [G : func B' B] (st : transf S F T G),
 st ∘>>' (Id_con_transf S Y)
 ==> (Subst_cov_transf st Y) ;
 // : transf (S <<∘ Y) F T (G <∘ Y)
 
 /*    pp (- o> 1)  ==>  pp  */ /* coyoneda */
 type λ [A B A' X : Cat] [P : mod A B] [P' : mod A' X] [F : func A A'] [K : func B X]
 (pp : transf P F P' K),
 (UnitMod_Tensor_cov_transf pp) ∘>>' (Tensor_hom_cov_transf (Id_cov_transf P Id_func) (Id_con_hom Id_func K))
   ==> pp;
 
 //A1
 type λ  [A B C X A' X' A0 : Cat] [P : mod A B] [Q : mod C X] 
 [O : mod A' X'] [K : func B C] [F : func A0 A'] [L : func X X'] (M: func A0 A)
 (pq_o : transf (M ∘>> P) F (Imply_cov_mod O L Q) K)
 B0 (N : func B0 B) X0 (X0X : func X0 X) 
 (P': mod A0 B0) (pp : transf P' M P N) (Q' : mod B X0) (qq : transf Q' K Q X0X ),
 (Eval_cov_transf pq_o) ∘>>' (Tensor_cov_transf pp qq)
 ==> Eval_cov_transf ((pq_o ∘>>' pp) '∘>>  (Imply_cov_transf (Id_cov_transf O Id_func) L qq N));
 // : transf (Tensor_cov_mod P' N Q') F O (L <∘ X0X)
 
 
 
 
 /* ============================================== */
 
 
 
 /*  “1(f)∘F” = id(f)  */
 type λ  [A B I : Cat] (F : func B A) (Z : func I B),
 (Id_cov_UnitMod_cov_transf F Z)
 ==> (Id_cov_transf (F ∘>1_ ) Z) ;
 
 /*  “1∘I(f)” = id(f)  ????????? */
 // error: [Id_func ∘>1_ ] and [ _1<∘ Id_func] are not unifiable.
 // or via [ _1<∘ Z] and [
 //  Tensor_cov_mod (Id_func ∘>1_ ) Id_func ( _1<∘ Z)
 // ] are not unifiable
 type λ  [A I : Cat]  (Z : func I A),
 (Id_cov_UnitMod_con_transf (@Id_func A) Z)
 ==> (Id_con_transf (Id_func ∘>1_ ) Z) ;
 //in : transf ( _1<∘ Z) Id_func (Id_func ∘>1_ ) (Id_func <∘ Z)
 //out1 : transf ( _1<∘ Id_func <<∘ Z) Id_func ( _1<∘ Id_func) Z
 //out2 : transf (Id_func ∘>1_ <<∘ Z) Id_func (Id_func ∘>1_ ) Z
 
 
 /***   “1∘F(g)” ∘>F - =                     “1∘F”( g ∘> - )  */ /* OK */
 type λ [A B I I' : Cat] (F : func B A) (Z : func I B) (M: func I' B) (N: func I' I)
  (g : hom M ( _1<∘ Z) N),
 UnitMod_con_transf (g '∘> (Id_cov_UnitMod_con_transf F (Z <∘ N)))
 ==> (UnitMod_con_transf g) '∘>> (Id_cov_UnitMod_con_transf F (Z <∘ N));
 // : transf ( _1<∘ M) Id_func (F ∘>1_ ) (F <∘ (Z <∘ N))
 
 //A2 // note this is alt input order of above “1∘F(g)” ∘>F - 
 // TODO: check for remaining Id_func in g : hom Id_func R N
 /*** “1∘FZ(-)” <∘ “1∘F(g)”  =                     “1∘F( - Z<∘ g)”     TODO: N is only restriction not applied functor, that is factor (N -) and (- N) */
 type λ [A B I : Cat] (F : func B A) (Z : func I B) I' (N: func I' I) (M: func I' B)
 (g : hom M ( _1<∘ Z) N) I'' (K: func I'' I), 
 (UnitMod_cov_transf (g '∘> (Id_cov_UnitMod_con_transf F (Z <∘ N)))) ∘>>' (Subst_con_transf N (Id_cov_UnitMod_con_transf (F <∘ Z) K))
 ==> (Subst_cov_transf (UnitMod_cov_transf g) K) '∘>> (Id_cov_UnitMod_con_transf F (Z <∘ K));
 // : transf (N ∘>> _1<∘ K) M ( F ∘>1_ ) ((F <∘ Z) <∘ K)
 // todo? erase this derivable general K 
 // also: derivable  “1∘FZN(-)” <∘ “1∘F(g)”  =                     “1∘F((- N∘1) Z<∘ g)”     from N is only restriction not applied functor, that is factor (N -) and (- N) 
 // type λ [A B I : Cat] (F : func B A) (Z : func I B) I' (N: func I' I) (M: func I' B)
 // (g : hom M ( _1<∘ Z) N) I'' (K: func I'' I'), 
 // (UnitMod_cov_transf (g '∘> (Id_cov_UnitMod_con_transf F (Z <∘ N)))) ∘>>' (Id_cov_UnitMod_con_transf ((F <∘ Z) <∘ N) K)
 // ==> ((UnitMod_cov_transf g) ∘>>' (Id_cov_UnitMod_con_transf N K)) '∘>> (Id_cov_UnitMod_con_transf F ((Z <∘ N) <∘ K));
 // : transf ( _1<∘ K) M (F ∘>1_ ) (((F <∘ Z) <∘ N) <∘ K)
 
 /* “1∘G(“-F∘1”)”   =              “1∘GF(-)”  or reverse direction ? */
 type λ [A B C : Cat] (F : func A B) (G : func B C)  /* genralize? I (K: func I A) L */, 
  (Id_con_UnitMod_cov_transf F Id_func) '∘>>  (Id_cov_UnitMod_con_transf G F) 
 ==> (UnSubst_con_transf ( G ∘>1_ ) F (Id_cov_UnitMod_con_transf (G <∘ F) Id_func));
 // == (Id_cov_transf G F) ∘>>' (Id_cov_UnitMod_con_transf (G <∘ F) Id_func)
 // : transf (∘>1_ Id_func) ((Id_func ∘> F) ∘> Id_func) (G ∘>1_ ) (G <∘ F)
 
 
 
 
 
 
 /* ============================================== */
 
 