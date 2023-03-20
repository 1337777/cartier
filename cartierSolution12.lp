/* TITLE: Cut-elimination in the double category of profunctors with J-rule-eliminated adjunctions
TODO: these are unfinished prototypes for demo that it does work

https://github.com/1337777/cartier/blob/master/cartierSolution12.lp (head version; future primary file; must use LambdaPi proof-assistant for modulo structural coherence)
https://github.com/1337777/cartier/blob/master/cartierSolution12.v (lagging version; unable proof-assistant)

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
 
 | One_cat : cat
 
 | Fibre_cat : Π [X I : cat] (A : catd X) (x : func I X), cat
 
 | Mod_cat : Π [A B : cat] (R : mod A B), cat
 
 with catd: Π (X : cat), TYPE ≔ 
 
 | Triv_catd : Π (A : cat), catd A
 
 | Cast_catd : Π (A : cat), catd One_cat
 
 | Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd  I
 
 | Mod_con_catd : Π [A B : cat] (R : mod A B), catd A
 
 | Mod_cov_catd : Π [A B : cat] (R : mod A B), catd  B
 
 with func : Π (A B : cat), TYPE ≔
 
 | Id_func : Π [A : cat], func A A
 
 //Subst_func'  constructor
 | '∘> : Π [A B C: cat], func A B → func B C → func A C
 
 | One_func :  Π (A : cat), func A One_cat
 
 | Mod_func : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
  func I (Mod_cat R) 
 
 with funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE ≔
 
 | Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A
 
 | '∘>d: Π [X Y Z : cat] (A : catd X) (B : catd Y) (C : catd Z) (F : func X Y)
    (G : func Y Z), funcd A F B → funcd B G C → funcd A (('∘>) F G) C
 
 | Triv_funcd :  Π [X Y : cat] (xy : func X Y), funcd (Triv_catd X) xy (Triv_catd Y)
 
 | Proj_funcd : Π [X Y I : cat] [A : catd X] (x : func I X) [B : catd Y] [F : func X Y],
 funcd A F B →  funcd (Fibre_catd A x) (('∘>) x  F ) B
 
 | Univ_funcd : Π [X I : cat] [A : catd X] [x : func I X] [J : catd I]  ,
   funcd J x A  → funcd J Id_func (Fibre_catd A x)
 
 | Mod_con_funcd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
  funcd (Triv_catd I) x (Mod_con_catd R)
 
 | Mod_cov_funcd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 funcd (Triv_catd I) y (Mod_cov_catd R)
 
 with  mod : Π (A B : cat), TYPE ≔
 
 | Unit_mod : Π [X A B : cat], func A X → func B X → mod A B
 
 | ⊗ : Π [A B X : cat], mod A B → mod B X → mod A X //Tensor_mod
 
 | Imply_cov_mod : Π [A B C X : cat], mod A B → func C B → mod X C → mod A X
 
 | Imply_con_mod : Π [A B C X : cat], mod C X → func C A → mod A B → mod X B
 
 | One_mod : Π (A B : cat), mod A B
 
 | Mod_mod : Π [A B : cat] (R : mod A B), mod (Mod_cat R) (Mod_cat R)
 
 | Sheaf_con_mod : Π [A B : cat], mod A B → mod A B
 
 with modd : Π [X Y : cat], catd X → mod X Y → catd Y → TYPE ≔ 
 
 | ⊗d : Π [A B X : cat] [AA : catd A][BB : catd B][XX : catd X]
  [R :mod A B] [S :mod B X], modd AA R BB →  modd BB S XX →
  modd AA ( (⊗) R S) XX  //Tensor_modd
 
 | Triv_modd : Π [X Y : cat] (R : mod X Y) ,
 modd (Triv_catd X) R (Triv_catd Y)
 
 | Fibre_modd : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [x : func I X] [y : func I Y], hom x R y → 
  modd (Fibre_catd A x) (Unit_mod Id_func Id_func) (Fibre_catd B y)
 
 | Mod_modd : Π [A B : cat] (R : mod A B), modd (Mod_con_catd R) R (Mod_cov_catd R)
 
 | Sheaf_con_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → modd A R B
 
 with hom: Π [I A B : cat], func I A → mod A B → func I B → TYPE ≔
 
 | Id_cov_hom : Π [A B I : cat] (F : func B A),
 hom Id_func (Unit_mod F Id_func ) F
 
 | Id_con_hom : Π [A B I : cat] (F : func B A),
 hom F (Unit_mod Id_func F) Id_func
 
 | Adj_cov_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I _),
 hom ( ('∘>) Z  RAdj_func) (Unit_mod ( ('∘>) Id_func  LAdj_func) Z) Id_func
 
 | Adj_con_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I _),
 hom Id_func (Unit_mod Z ( ('∘>) Id_func  RAdj_func)) ( ('∘>) Z  LAdj_func)
 
 | One_hom : Π [A B I : cat] (F : func I A) (G : func I B),  hom F (One_mod A B) G
 
 | Mod_hom : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 hom (Mod_func r) (Mod_mod R) (Mod_func r)
 
 | Tensor_hom_hom  : Π [A  X I : cat] [P : mod A I] [Q : mod I X]
 [F : func I A] [G : func I X],
 hom F P Id_func → hom Id_func Q G → hom F ((⊗) P  Q) G
 
 with homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
   Π [A : catd X] [B : catd Y] [II: catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), TYPE ≔
 
 | Mod_homd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 homd r (Mod_con_funcd r) (Mod_modd R) (Mod_cov_funcd r)
 
 with adj : Π [R L : cat], func R L → func L R → TYPE ≔
 
 with covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [J : catd I][y : func I Y],  funcd J y B → TYPE ≔
 
 | Triv_covering : Π [X Y I : cat] [R : mod X Y] [G : func I Y], 
 covering (Triv_modd R) (Triv_funcd G)
 
 | Fibre_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
  (RR : modd A R B) [J : catd I] [G : func I Y]  (H : funcd J G B), Π [F : func I X]  (r : hom F R G),
   covering RR H → 
   covering (Fibre_modd RR r)  (Univ_funcd H)
 
 | Sigma_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [G : func I Y], Π [J : catd I] [H : funcd J G B],
 (Π [F : func I X] (r : hom F R G), covering (Fibre_modd RR r)  (Univ_funcd H)) → 
  covering RR H ;
 
 notation '∘> infix right 90; notation ⊗ infix left 70; notation ⊗d infix left 70;
 
 symbol Sigma_cat : Π [X : cat], catd X → cat;
 
 symbol Sigma_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
  funcd A xy B → func (Sigma_cat A) (Sigma_cat B);
 
 symbol Sigma_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → mod (Sigma_cat A) (Sigma_cat B);
 
 symbol Sigma_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II: catd I] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
 homd r FF RR GG  → hom (Sigma_func FF) (Sigma_mod RR) (Sigma_func GG);
 
 rule Sigma_cat (Triv_catd $A) ↪ $A
 with Sigma_cat (Cast_catd $A) ↪ $A
 with Sigma_cat (Fibre_catd $A $F) ↪ Fibre_cat $A $F
 with Sigma_cat (Mod_con_catd $R) ↪ (Mod_cat $R)
 with Sigma_cat (Mod_cov_catd $R) ↪ (Mod_cat $R);
 
 rule Sigma_func (Id_funcd) ↪ Id_func
 with Sigma_func (Triv_funcd $F) ↪ $F
 with Sigma_func (Mod_con_funcd $r) ↪ (Mod_func $r)
 with Sigma_func (Mod_cov_funcd $r) ↪ (Mod_func $r);
 
 rule Sigma_mod (Triv_modd $R) ↪ $R
 with Sigma_mod (Mod_modd $R) ↪ (Mod_mod $R)
 with Sigma_mod ($R ⊗d $S) ↪ (Sigma_mod $R) ⊗ (Sigma_mod $S);
 
 rule Sigma_hom (Mod_homd $r) ↪ Mod_hom $r;
 
 //Subst_func
 symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
 notation ∘> infix right 90;
 symbol <∘ [A B C: cat] : func B C → func A B → func A C ≔ λ G F, F ∘> G;
 notation <∘ infix left 90;
 
 rule ($F ∘> $G) ∘> $H ↪ $F ∘> ($G ∘> $H)
 with $F ∘> Id_func ↪ $F
 with Id_func ∘> $F ↪ $F
 with ($F ∘> ($G '∘> $H)) ↪ (($F ∘> $G) '∘> $H)
 with (($F '∘> $G) ∘> $H) ↪ ($F '∘> ($G ∘> $H));
 
 // Subst_hom 
 symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
 [G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
 notation ∘↓ infix left 120;
 
 rule $r ∘↓ Id_func ↪ $r
 with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($H <∘ $K); 
 
 //Subst_cov_mod
 symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;
 notation <<∘ infix left 80;
 
 //Subst_con_mod
 symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
 notation ∘>> infix right 80;
 
 rule (Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K)
 with ($R ⊗ $S) <<∘ $G ↪ $R ⊗ ($S <<∘ $G)
 with (Imply_cov_mod $R $H $S) <<∘ $G ↪ Imply_cov_mod $R $H ($G ∘>> $S)
 with (Imply_con_mod $R $H $S) <<∘ $G ↪ Imply_con_mod $R $H ($S <<∘ $G);
 
 rule $K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G
 with $G ∘>> ($R ⊗ $S) ↪ ($G ∘>> $R) ⊗ $S
 with $G ∘>> (Imply_con_mod $R $H $S) ↪ Imply_con_mod ($R <<∘ $G) $H $S
 with $G ∘>> (Imply_cov_mod $R $H $S) ↪ Imply_cov_mod ($G ∘>> $R) $H $S;
 
 // provable  (careful ?? this indirely unify stuff?)
 rule $R <<∘ Id_func ↪ $R 
 with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K); 
 
 rule Id_func ∘>> $R ↪ $R 
 with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R; 
 
 rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));
 
 inductive transf: Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → TYPE ≔
 
 | Id_transf : Π [A X : cat] (R : mod A X) ,
 transf R Id_func R Id_func
 
 | Unit_Tensor_cov_transff : Π [A B A' X : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] ,
 transf P F P' Id_func → 
 transf (P ⊗ ( Unit_mod Id_func Id_func )) F P' Id_func
 
 | Eval_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ( P ⊗ Q)  F O                     L
 
 | Lambda_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ( P ⊗ Q)  F O                     L
 
 | Tensor_cov_transff : Π [A' I X' A X: cat] [P' : mod A' I] [Q' : mod I X'] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func X' X],
 transf P' F P Id_func → transf Q' Id_func Q G →
 transf (P' ⊗ Q') F (P ⊗ Q) G
 
 | Tensor_cov_hom_transf : Π [A' I A X: cat] [P' : mod A' I] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func I X],
 transf P' F P Id_func → hom Id_func Q G →
 transf P' F (P ⊗ Q) G
 
 | Tensor_cov_transf : Π [A B A' B' C D D' : cat] [O : mod A B] [O' : mod A' B']
  [Q : mod C D] [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func D D'],
 transf O F O' G → Π (K : func D' B), transf Q Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) Id_func
 
 | Imply_cov_hom_transf : Π [A B A' B' C  D' : cat] [O : mod A B] [O' : mod A' B']
   [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func C D'],
 transf O F O' G → Π (K : func D' B), hom Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (O' <<∘ ((G <∘ K) <∘ L)) Id_func 
 
 | Glue_transf : Π [X Y A' B': cat] [A : catd X]  [B: catd Y] [R : mod X Y]
 (RR : modd A R B) (FF : funcd A (One_func X) (Cast_catd A')) (RR' : mod A'  B') (GG : funcd B (One_func Y)  (Cast_catd B')),
 Π I [G : func I Y], Π [J : catd I] [H : funcd J G B], covering RR H →
 (Π [F : func I X] (r : hom F R G), transf (Sigma_mod (Fibre_modd  RR r)) (Sigma_func (Proj_funcd F FF )) (Sheaf_con_mod RR') (Sigma_func (Proj_funcd  G GG))) →
   transf (Sigma_mod RR) (Sigma_func FF) (Sheaf_con_mod RR') (Sigma_func GG )
 
 with transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
   modd A R B → funcd A xx' A' → modd A' R' B' → funcd B yy' B' → TYPE ≔
 
 | Glue_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 (RR : modd A R B) (FF : funcd A xx' A') (RR' : modd A' R' B') (GG : funcd B yy' B'),
 Π I [G : func I Y], Π [J : catd I] [H : funcd J G B], covering RR H →
 (Π [F : func I X] (r : hom F R G), transfd (Fibre_modd  RR r) (Proj_funcd F FF ) (Sheaf_con_modd RR') (Proj_funcd  G GG)) →
   transfd RR FF (Sheaf_con_modd RR') GG ;
 
 // "J-rule" , admissible/eliminated until accumulation onto basic constructors
 //Unit_cov_trans
 symbol  ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func;
 
 //Unit_con_trans
 symbol  _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G;
 
 notation _'∘> infix right 80;
 notation ∘>'_ infix left 80;
 
 
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
 
 injective symbol ==> : Π [I A B: cat] [F : func I A] [T : mod A B] [G :func I B],
 hom F T G → hom F T G → TYPE;
 notation ==> infix 20;
 
 injective symbol ==>> : Π [A' B' A B: cat] [S : mod A' B'] [F : func A' A] [T : mod A B] [G :func B' B],
 transf S F T G → transf S F T G → TYPE;
 notation ==>> infix 20;
 
 
 /* ========================== */
 
 // inductive data type
 
 symbol OneArrow_cat : cat;
 symbol OneArrow_First_func : Π [A : cat], func A One_cat → func A OneArrow_cat;
 symbol OneArrow_Second_func : Π [A : cat], func A One_cat → func A OneArrow_cat;
 symbol OneArrow_hom : Π [A : cat] (F : func A One_cat), hom (OneArrow_First_func F) (Unit_mod Id_func Id_func) (OneArrow_Second_func F);
 symbol OneArrow_elim : Π (E : cat) (first_func : func One_cat E) 
 (second_func : func One_cat E) (one_hom : hom first_func (Unit_mod Id_func Id_func) second_func), func OneArrow_cat E;
 
 /* ========================== */
 
 // weighted covariant limit (with reindexing)
 
 injective symbol limit : Π [B J0 J J' : cat] (K : func J J0) (F : func J0 B) (W : mod J' J) (F_⇐_W : func J' B), TYPE;
 
 symbol limit_transf : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
 (isl : limit K F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (Imply_cov_mod ((Unit_mod M F)) K W) Id_func (Unit_mod M F_⇐_W) Id_func;
 
 type λ  [B J0 J J' A : cat] (K : func J J0) (W : mod J' J) (F : func J0 B) (F_⇐_W : func J' B)
 (isl : limit K F W F_⇐_W) (R : func B A) (L : func A B) (isa : adj L R) I (M : func I A), 
  ((Tensor_cov_transf ((M)_'∘> Adj_cov_hom isa F) K (Id_transf W)) ''∘ (limit_transf isl (M '∘> L)))
  ''∘ ((Adj_con_hom isa M) ∘>'_(F_⇐_W)) ;
  // : transf (Imply_cov_mod (Unit_mod M (F '∘> R)) K W) 
  // ((Id_func ∘> Id_func) ∘> Id_func) (Unit_mod M (Id_func '∘> R) <<∘ F_⇐_W) (Id_func <∘ (Id_func <∘ Id_func))
 
 
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
 
 // adjunction inverses
 
 // “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
 type λ [L R I J I0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I0 R) (M : func I I0)  (N : func J L),
  (((Adj_con_hom aj Z) ∘↓ M) ∘>'_(N)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj Id_func) ∘↓ N))
 ==>>  (((Id_cov_hom (Z '∘> LAdj_func)) ∘↓ M) ∘>'_(N) ) ''∘ (  (Z '∘> LAdj_func)_'∘> ((Id_con_hom Id_func) ∘↓ N) );
 // : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) N) M (Unit_mod (Z ∘> LAdj_func) Id_func) N
 
 
 // “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   
 type λ [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) Z (N : func I R) (M : func J R),
 ( (M)_'∘> ((Adj_con_hom aj Z) ∘↓ N) )   ''∘ ( (M ∘> Z )_'∘> (Adj_cov_hom aj Id_func) )
 ==>>  ( (M)_'∘> ((Id_cov_hom (Z '∘> LAdj_func)) ∘↓ N) ); 
 // : transf (Unit_mod M N) Id_func (Unit_mod (M ∘> (Z ∘> LAdj_func)) Id_func) ((Z ∘> LAdj_func) <∘ N)
 
 /* ========================== */
 
 // naturality and dinaturality of evaluation
 
 type λ [A B B X A' X' : cat] [P : mod A B] [Q : mod B X] 
 (O : mod A' X')  [F : func A A'] (L : func X X')
 (pq_o : transf P                       F (Imply_cov_mod O L Q) Id_func)
 A0  X0 (M: func A0 A)  (Z : func X0 X) 
 (P': mod A0 B) (Q' : mod B X0) 
 (p'p : transf P' M P Id_func) (q'q : transf Q' Id_func Q Z),
 (Eval_cov_transf  pq_o)  ∘'' (Tensor_cov_transff p'p q'q)
 ==>> Eval_cov_transf  ((pq_o ∘'' p'p) ''∘ (Tensor_cov_transf (Id_transf O) L q'q)); 
 
 // evaluation of coyoneda at identity hom
 
 type λ [A B A' : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] 
 (pp : transf P F P' Id_func),
 (Unit_Tensor_cov_transff pp)  ∘'' (Tensor_cov_hom_transf (Id_transf P) (Id_con_hom Id_func))
  ==>> pp;
 // transf P (Id_func ∘> F) P' (Id_func <∘ Id_func)
 
 /* ========================== */
 
 //voila
 
 