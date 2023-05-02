/* TODO: these are unfinished prototypes for demo that it does work

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
 builtin "Prop" ≔ Prop; builtin "P" ≔ Prf;
 
 
 //TODO: uncomment
 // symbol Fibre_homdu : Π [I: cat] [A : catd I] [B : catd I] [II: catd I] 
 //todo fibre Unit_mod is Unit_mod Fibre
 //todo blend fibre with CartFib_homdu
 
 //
 //
 //todo eval-lambda with unit, so between hom and transf 
 //todo eval-lambda dependent over —/Γ context? or prefixed under Γ⊗— context?
 //
 //todo composition of substitutions
 //todo whiskering version of Tensor_cov_transf
 // j-rule then apply hom then restrict  //also j-rule for funcid
 // j-rule then funcid (..same as con-con naturality of funcid?)
 //todo j-rule of restrict of hom
 //todo j-rule then applied to funcid (id of hom)
 // add ordinary functor application in Unit F F ? (and its reduction when restricted)
 // restriction after application of hom on transf // in particular on transf which is jruled-funcid?
 // application of hom on composition of transf //in particular on composition of j-ruled-funcid ? on compose of funcid?
 // j-rule then applied to id_hom, both cov and con
 //
 // fibre of fibre
 // restriction dep hom Subst_homd
 // funcid in homd FuncId_con_homd
 // repeat restrict of ordinary funcid
 // repeat restrict after  (jrule then apply hom)
 //  repeat jrule on (funcid for ident functor)
 // 
 // add rew for commute from total of funcd
 // add total of homd
 // add total of id_funcd, total of triv_catd
 // add total of comp funcd
 // total of dep jrule is base jrule of totals
 // total of dep comp transf , in particular of postcomp by jruled idfunc
 // total of dep restr
 //
 //  fibre of funcd
 //  fibre of modd along both base hom gives moddu and base transf gives modd
 //  grammar entry for both homd above id_transf and transfd above id_transf ? and adjunct-indirect functorial fibre? or functorial by univ?
 //  fibre of homdu  along func gives homdu
 //  fibre of id_funcd ? adjunct-indirectly
 //  fibre of comp_funcd ? not necessary if adjunct-indirectly 
 //  fibre of idfunc_homd,  or of idfunc_homdu?
 //  fibre of dep jrule
 //  fibre of dep restriction
 //  fibre of dep comp transf , in particular of postcomp by jruled idfunc
 //
 // fibre of catd along id_func, along comp_func
 // fibre of funchd along id_func
 // todo homdu, fibre of homdu along func, fibre of transfdu along transf
 // fibre of homdu along id_func
 //
 // fibre of catd along comp_func
 // fibre of funchd along comp_func
 // fibre of homdu along comp_func
 //
 // fibre of modd along both hom and transf
 //
 // fibre of moddu along func, case analysis of moddu
 // fibre of modd along transf,  along hom
 // fibre of modd along id_transf
 // fibre of modd along jrule transf is jrulehd of (fibre of modd along hom which gives transfdu)
 // fibre of modd along comp of transf
 // fibre of modd along restr of hom
 // 
 //
 // // todo: Total_hom of homdu applied/Comp_homd onto transfdu
 //
 //todo Fibre_homdu of homdu along functor
 //todo Fibre_transfuu of transfduu along functor
 //
 //
 //
 inductive cat : TYPE ≔ 
 
 | Terminal_cat : cat
 
 //| Fibre_cat : Π [X I : cat] (A : catd X) (x : func I X), cat //not lacked
 
 | Comma_cat : Π [A B : cat] (R : mod A B), cat
 
 // todo both cov catd and con catd
 with catd: Π (X : cat), TYPE ≔ 
 
 | Triv_catd : Π (A : cat), catd A
 
 | Cast_catd : Π (A : cat), catd Terminal_cat
 
 | Sigma_catd : Π [Y X : cat] (Z : catd Y) (F : func Y X), catd X
 
 | Comma_con_catd : Π [A B : cat] (R : mod A B), catd A
 
 | Comma_cov_catd : Π [A B : cat] (R : mod A B), catd  B
 
 with func : Π (A B : cat), TYPE ≔
 
 | Id_func : Π [A : cat], func A A
 
 //Subst_func'  constructor
 | '∘> : Π [A B C: cat], func A B → func B C → func A C
 
 | Terminal_func :  Π (A : cat), func A Terminal_cat
 
 // necessary?
 | Comma_con_func : Π [A B : cat] (R : mod A B), func (Comma_cat R) A
 | Comma_cov_func : Π [A B : cat] (R : mod A B), func (Comma_cat R) B
 
 | Comma_func : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
  func I (Comma_cat R) 
 
 //todo: funchd would allow to pack all inductives into one single declaration instead of waiting for Id_func
 // with funchd : Π [X : cat] (A : catd X) (B : catd X), TYPE ≔
 
 // | Id_funchd : Π [X : cat] [A : catd X], funchd A A
 
 //todo: funchd = funcd over Id_func ?
 with funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE ≔
 
 //todo: delete?
 | Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A
 
 // necessary?
 | '∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
    [G : func Y Z], funcd A F B → funcd B G C → funcd A (('∘>) F G) C
 
 | Triv_funcd :  Π [X Y : cat] (xy : func X Y), funcd (Triv_catd X) xy (Triv_catd Y)
 
 | Cast_funcd : Π [Y X : cat] (F : func Y X), funcd (Cast_catd Y) Id_func (Cast_catd X) //as funchd ?
 
 | Catd_funcd : Π [X : cat] (A : catd X), funcd A Id_func (Triv_catd X) //as funchd ?
 
 | SigmaIntro_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X), funcd Z F (Sigma_catd Z F)
 
 | Comma_con_funcd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
  funcd (Triv_catd I) x (Comma_con_catd R)
 
 | Comma_cov_funcd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 funcd (Triv_catd I) y (Comma_cov_catd R)
 
 with isEquiv : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → TYPE ≔
 //todo comp_funcd id_funcd is equiv
 | Id_funcd_isEquiv : Π [X : cat] [A : catd X], isEquiv (@Id_funcd _ A)
 
 | Sigma_isEquiv : Π [Y X : cat] (Z : catd Y) (F : func Y X), isEquiv (SigmaIntro_funcd Z F)
 
 with  mod : Π (A B : cat), TYPE ≔
 
 | Unit_mod0 : Π (A: cat), mod A A
 
 | ⊗ : Π [A B X : cat], mod A B → mod B X → mod A X //Tensor_mod
 
 | Imply_cov_mod : Π [A B C X : cat], mod A B → func C B → mod X C → mod A X
 
 | Imply_con_mod : Π [A B C X : cat], mod C X → func C A → mod A B → mod X B
 
 | Terminal_mod : Π (A B : cat), mod A B
 
 | Comma_mod : Π [A B : cat] (R : mod A B), mod (Comma_cat R) (Comma_cat R)
 
 | Sheaf_con_mod : Π [A B : cat], mod A B → mod A B
 
 with moddu : Π [I : cat], catd I → catd I → TYPE ≔ 
 
 | Triv_moddu : Π (X : cat), moddu (Triv_catd X) (Triv_catd X)
 
 | Cast_moddu : Π [X Y : cat] (R : mod X Y), moddu (Cast_catd X) (Cast_catd Y)
 
 // necessary ?
 | Unit_moddu0 : Π [I : cat] (II : catd I), moddu II II
 
 with modd : Π [X Y : cat], catd X → mod X Y → catd Y → TYPE ≔ 
 
 //todo: erase, instead Cast_moddu
 //| Cast_modd : Π [X Y : cat] (R : mod X Y), modd (Cast_catd X) (Terminal_mod Terminal_cat Terminal_cat) (Cast_catd Y)
 
 | Triv_modd : Π [X Y : cat] (R : mod X Y) ,
 modd (Triv_catd X) R (Triv_catd Y)
 
 //todo delete
 // | Fibre_hom_modd : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 // (RR : modd A R B) [x : func I X] [y : func I Y], hom x R y → 
 //  modd (Fibre_catd A x) (Unit_mod Id_func Id_func) (Fibre_catd B y)
 
 // | Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] [II : catd I]
 //   (F : funcd (Triv_catd X) xi II) (G : funcd (Triv_catd Y) yi II), 
 //  modd (Triv_catd X) (Unit_mod xi yi) (Triv_catd Y)
 
 | Unit_modd0 : Π [I] (II : catd I),
  modd II (Unit_mod0 I) II
 
 | ⊗d : Π [A B X : cat] [AA : catd A][BB : catd B][XX : catd X]
  [R :mod A B] [S :mod B X], modd AA R BB → modd BB S XX →
  modd AA ((⊗) R S) XX  //Tensor_modd
 
 | Comma_modd : Π [A B : cat] (R : mod A B), modd (Comma_con_catd R) R (Comma_cov_catd R)
 
 | Sheaf_con_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → modd A R B
 
 // adjoints
 with adj : Π [R L : cat], func R L → func L R → TYPE ≔
 
 // weighted covariant limit (with reindexing)
 with limit : Π [B J0 J J' : cat] (K : func J J0) (F : func J0 B) (W : mod J' J) (F_⇐_W : func J' B), TYPE ≔
 
 with hom: Π [I A B : cat], func I A → mod A B → func I B → TYPE ≔
 
 // old ajd here
 
 | Lambda_cov_transf_hom : Π [A  X A' X' : cat] [Q : mod A X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf Q  F O                     L  →
 hom                       F (Imply_cov_mod O L Q) Id_func
 
 
 //todo reduce Terminal_mod Terminal_cat Terminal_cat to Unit_mod ?
 | Terminal_hom : Π [A B I : cat] (F : func I A) (G : func I B),  hom F (Terminal_mod A B) G
 
 | Comma_hom : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 hom (Comma_func r) (Comma_mod R) (Comma_func r)
 
 | Tensor_hom_hom  : Π [A  X I : cat] [P : mod A I] [Q : mod I X]
 [F : func I A] [G : func I X],
 hom F P Id_func → hom Id_func Q G → hom F ((⊗) P  Q) G
 
 
 
 with covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [J : catd I][y : func I Y], funcd J y B → TYPE ≔
 
 | Triv_covering : Π [X Y I : cat] [R : mod X Y] [G : func I Y] , 
 covering (Triv_modd R) (Triv_funcd G)
 
 // | Triv_covering : Π [X Y I : cat] [R : mod X Y] [J : catd I] [G : func I Y] (GG : funcd J G (Triv_catd Y)) , 
 // covering (Triv_modd R) GG
 
 //todo delete
 // | Fibre_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 //  (RR : modd A R B) [J : catd I] [G : func I Y]  (H : funcd J G B), Π [F : func I X]  (r : hom F R G),
 //   covering RR H → 
 //   covering (Fibre_hom_modd RR r)  (FibreUniv_funcd H)
 //todo delete
 // | Total_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 // (RR : modd A R B) [G : func I Y], Π [J : catd I] [H : funcd J G B],
 // (Π [F : func I X] (r : hom F R G), covering (Fibre_hom_modd RR r)  (FibreUniv_funcd H)) → 
 //  covering RR H
 
 //todo transf with codomain Unit_mod? similar as domain Unit_mod for hom ?
 with transf: Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → TYPE ≔
 
 | Id_transf : Π [A X : cat] (R : mod A X) ,
 transf R Id_func R Id_func
 
 | Unit_Tensor_cov_transf : Π [A B A' X : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] ,
 transf P F P' Id_func → 
 transf ((⊗) P (Unit_mod0 _)) F P' Id_func
 
 //todo eval-lambda with unit, so between hom and transf 
 //todo eval-lambda dependent over —/Γ context? or prefixed under Γ⊗— context?
 | Eval_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ((⊗) P Q)  F O                     L
 
 | Lambda_cov_transf : Π [A B  X A' X' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 transf P                       F (Imply_cov_mod O L Q) Id_func →
 transf ((⊗) P Q)  F O                     L
 
 | Eval_cov_hom_transf : Π [A  X A' X' : cat] [Q : mod A X] 
 [O : mod A' X']  [F : func A A'] [L : func X X'],
 hom                       F (Imply_cov_mod O L Q) Id_func →
 transf Q  F O                     L
 
 | Tensor_cov_transf : Π [A' I X' A X: cat] [P' : mod A' I] [Q' : mod I X'] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func X' X],
 transf P' F P Id_func → transf Q' Id_func Q G →
 transf ((⊗) P' Q') F ((⊗) P Q) G
 
 | Tensor_cov_hom_transf : Π [A' I A X: cat] [P' : mod A' I] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func I X],
 transf P' F P Id_func → hom Id_func Q G →
 transf P' F ((⊗) P Q) G
 
 
 | Comma_transf : Π [A B : cat] (R : mod A B), transf (Comma_mod R) (Comma_con_func R) R (Comma_cov_func R)
 
 | Terminal_transf : Π [A B : cat] (R : mod A B), transf R (Terminal_func A) (Unit_mod0 _) (Terminal_func B)
 
 // with transfduu: Π [I J: cat] [A' : catd J] [A : catd I] [B' : catd J] [B: catd I] [j : func I J] , 
 // moddu A B → funcd A j A' → moddu A' B' → funcd B j B' → TYPE ≔
 
 //todo:  transfhhd where both base mod are Unit with Id_transf?
 with transfdu: Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [ix' : func I X'] [iy' : func I Y'] [R' : mod X' Y'], 
   hom ix' R' iy' → moddu A B → funcd A ix' A' → modd A' R' B' → funcd B iy' B' → TYPE ≔
 
 | Triv_transfdu : Π [I A B: cat] [F : func I A] [R : mod A B] [G : func I B]
 (r : hom F R G),  transfdu r (Triv_moddu I) (Triv_funcd F) (Triv_modd R) (Triv_funcd G)
 
 with transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
   transf R xx' R' yy' → modd A R B → funcd A xx' A' → modd A' R' B' → funcd B yy' B' → TYPE ≔
 // todo: both transfd over transf and transfd over hom ?
 
 // | Glue_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 // (RR : modd A R B) (FF : funcd A xx' A') (RR' : modd A' R' B') (GG : funcd B yy' B'),
 // Π I [G : func I Y], Π [J : catd I] [H : funcd J G B], covering RR H →
 // (Π [F : func I X] (r : hom F R G), transfd (Fibre_hom_modd  RR r) (FibreProj_funcd F FF ) (Sheaf_con_modd RR') (FibreProj_funcd  G GG)) →
 //   transfd RR FF (Sheaf_con_modd RR') GG 
 | Triv_transfd : Π [A' B' A B: cat] [R' : mod A' B'] [F : func A' A] [R : mod A B] [G : func B' B]
 (r'r : transf R' F R G),  transfd r'r (Triv_modd R') (Triv_funcd F) (Triv_modd R) (Triv_funcd G)
   ;
 
 notation '∘> infix right 90; notation '∘>d infix right 90;
 notation ⊗ infix left 70; notation ⊗d infix left 70;
 
 // other defined operations via induction-recursion
 
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
 
 // general  ∘>d necessary? instead of just action by funchd
 symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
 [G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
 notation ∘>d infix right 90;
 symbol d<∘ [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
 [G : func Y Z] : funcd B G C → funcd A F B → funcd A (F ∘> G) C ≔ λ G F, F ∘>d G;
 notation d<∘ infix left 90;
 
 rule ($F ∘>d $G) ∘>d $H ↪ $F ∘>d ($G ∘>d $H)
 with $F ∘>d Id_funcd ↪ $F
 with Id_funcd ∘>d $F ↪ $F
 with ($F ∘>d ($G '∘>d $H)) ↪ (($F ∘>d $G) '∘>d $H) //'∘>d necessary?
 with (($F '∘>d $G) ∘>d $H) ↪ ($F '∘>d ($G ∘>d $H)); 
 
 //TOOO: move this rule
 //TODO: Triv_transfd of comp
 rule (Triv_funcd $F) ∘>d (Triv_funcd $G) ↪ Triv_funcd ($F ∘> $G);
 
 // symbol ∘>hd: Π [X : cat] [A : catd X] [B : catd X] [C : catd X] 
 // , funchd A  B → funchd B  C → funchd A  C;
 // notation ∘>hd infix right 90;
 
 // rule ($F ∘>hd $G) ∘>hd $H ↪ $F ∘>hd ($G ∘>hd $H)
 // with $F ∘>hd Id_funchd ↪ $F
 // with Id_funchd ∘>hd $F ↪ $F; 
 
 // other defined operations via induction-recursion
 
 
 //Subst_cov_mod
 symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;
 //Subst_con_mod
 symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
 
 notation <<∘ infix left 80; notation ∘>> infix right 80;
 
 rule 
 //(Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K) with 
 ($R ⊗ $S) <<∘ $G ↪ $R ⊗ ($S <<∘ $G)
 with (Imply_cov_mod $R $H $S) <<∘ $G ↪ Imply_cov_mod $R $H ($G ∘>> $S)
 with (Imply_con_mod $R $H $S) <<∘ $G ↪ Imply_con_mod $R $H ($S <<∘ $G);
 
 rule 
 //$K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G with 
 $G ∘>> ($R ⊗ $S) ↪ ($G ∘>> $R) ⊗ $S
 with $G ∘>> (Imply_con_mod $R $H $S) ↪ Imply_con_mod ($R <<∘ $G) $H $S
 with $G ∘>> (Imply_cov_mod $R $H $S) ↪ Imply_cov_mod ($G ∘>> $R) $H $S;
 
 // provable  (careful ?? this indirely unify stuff?)
 rule $R <<∘ Id_func ↪ $R 
 with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K); 
 
 rule Id_func ∘>> $R ↪ $R 
 with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R; 
 
 rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));
 
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
 
 
 //todo review this ... reviewed
 //rule (Unit_modd $F $G) d<<∘ (Triv_funcd $K) ↪ Unit_modd $F ($G d<∘ (Triv_funcd $K));
 //rule (Triv_funcd $K) ∘>>d (Unit_modd $F $G) ↪ Unit_modd ((Triv_funcd $K) ∘>d $F) $G;
 
 // provable  (careful ?? this indirely unify stuff?)
 rule $R d<<∘ Id_funcd ↪ $R 
 with ($R d<<∘ $H) d<<∘ $K ↪ $R d<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>d $R ↪ $R 
 with $K ∘>>d ($H ∘>>d $R) ↪ ($K ∘>d $H) ∘>>d $R; 
 
 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));
 
 rule $R du<<∘ Id_funcd ↪ $R 
 with ($R du<<∘ $H) du<<∘ $K ↪ $R du<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>du $R ↪ $R 
 with $K ∘>>du ($H ∘>>du $R) ↪ ($K ∘>d $H) ∘>>du $R; 
 
 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));
 
 
 //todo: Unit_mod F G as defined as restr of another more basic (@Unit_mod)
 symbol Unit_mod : Π [X A B : cat], func A X → func B X → mod A B ≔ λ X _ _ F G, F ∘>> ((Unit_mod0 X) <<∘ G);
 
 // symbol Unit_moddu : Π [I : cat] [II : catd I]
 // (F : funcd (Triv_catd I) Id_func II) (G : funcd (Triv_catd I) Id_func II), 
 // moddu (Triv_catd I) (Triv_catd I) ≔ λ _ II F G, F ∘>>du ((Unit_moddu0 II) du<<∘ G);
 symbol Unit_moddu : Π [I : cat] [XX : catd I] [YY : catd I] [II : catd I]
 (F : funcd XX Id_func II) (G : funcd YY Id_func II), 
 moddu XX YY ≔ λ _ _ _ II F G, F ∘>>du ((Unit_moddu0 II) du<<∘ G);
 
 // symbol Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] [II : catd I]
 // (F : funcd (Triv_catd X) xi II) (G : funcd (Triv_catd Y) yi II), 
 // modd (Triv_catd X) (Unit_mod xi yi) (Triv_catd Y) ≔ λ _ _ _ _ _ II F G, F ∘>>d ((Unit_modd0 II) d<<∘ G);
 symbol Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] 
 [XX : catd X] [YY : catd Y] [II : catd I] (F : funcd XX xi II)  (G : funcd YY yi II), 
 modd XX (Unit_mod xi yi) YY ≔ λ _ _ _ _ _ _ _ II F G, F ∘>>d ((Unit_modd0 II) d<<∘ G);
 // inductive hom
 
 //todo also have Id_hom : hom Id_func (Unit_mod Id_func Id_func) Id_func ? with reductions to it?
 //this above seems resolved by FuncId_hom, but what implications for adjunctions?
 injective symbol FuncId_hom : Π [A B : cat] (F : func B A),
 hom Id_func (Unit_mod F F ) Id_func;
 
 injective symbol FuncId_cov_hom : Π [A B : cat] (F : func B A),
 hom Id_func (Unit_mod F Id_func ) F;
 
 injective symbol FuncId_con_hom : Π [A B : cat] (F : func B A),
 hom F (Unit_mod Id_func F) Id_func;
 
 injective symbol Adj_cov_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I _),
 hom ( ('∘>) Z  RAdj_func) (Unit_mod ( ('∘>) Id_func  LAdj_func) Z) Id_func;
 
 injective symbol Adj_con_hom : Π [L R I : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I _),
 hom Id_func (Unit_mod Z ( ('∘>) Id_func  RAdj_func)) ( ('∘>) Z  LAdj_func);
 
 // inductive transf
 injective symbol limit_transf : Π  [B J0 J J' : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
 (isl : limit K F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (Imply_cov_mod ((Unit_mod M F)) K W) Id_func (Unit_mod M F_⇐_W) Id_func;
 
 
 // todo homdu for non-rec constants, while homd for rec operations such as tensor, with cast from homdu
 injective symbol homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
   Π [A : catd X] [B : catd Y] (FF : funcd (Triv_catd I) F A) (RR : modd A R B) (GG : funcd (Triv_catd I) G B), TYPE;
 
 injective symbol FuncId_homd : Π [I X : cat] [xi : func X I]  [II : catd I]
   (F : funcd (Triv_catd X) xi II) ,
 homd  (FuncId_hom xi) Id_funcd (Unit_modd F F ) Id_funcd;
 
 
 
 // todo FuncId_con_homd
 injective symbol Comma_homd : Π [A B I : cat] [R : mod A B] [x : func I A] [y : func I B] (r : hom x R y),
 homd r (Comma_con_funcd r) (Comma_modd R) (Comma_cov_funcd r);
 
 injective symbol homdu: Π [I: cat] [A : catd I] [B : catd I]
 (FF : funcd (Triv_catd I) Id_func A) (RR : moddu A B) (GG : funcd (Triv_catd I) Id_func B), TYPE;
 
 injective symbol FuncId_homdu : Π [I : cat] [A : catd I] (F : funcd (Triv_catd I) Id_func A),
 homdu Id_funcd (Unit_moddu F F) Id_funcd;
 
 injective symbol coveringdu : Π [X : cat] [A : catd X] [B : catd X]
 (RR : moddu A B) [I : cat] [II : catd I] [x : func I X], funcd II x B → TYPE;
 
 // injective symbol Triv_coveringdu : Π [X : cat] [I : catd X] (GG : funcd I Id_func (Triv_catd X)), 
 // coveringdu (Triv_moddu X) GG;
 
 injective symbol Triv_coveringdu : Π [X I : cat] (G : func I X), 
 coveringdu (Triv_moddu X) (Triv_funcd G);
 
 injective symbol transfduu: Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I], 
 moddu A B → funcd A Id_func A' → moddu A' B' → funcd B Id_func B' → TYPE;
 
 
 // other injective constructors via induction-recursion
 
 
 // Subst_hom todo Subst_homd
 //Comp_func_hom
 symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
 [G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
 notation ∘↓ infix left 120;
 
 rule $r ∘↓ Id_func ↪ $r
 with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($H <∘ $K); 
 
 //Comp_funcd_homd
 symbol ∘↓d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B], 
  homd r FF RR GG → Π [I'] (Z : func I' I) ,
  homd (r ∘↓ Z) ((Triv_funcd Z) ∘>d FF) RR ((Triv_funcd Z) ∘>d GG);
 notation ∘↓d infix left 120;
 //todo rules for ∘↓d
 
 // "J-rule" , admissible/eliminated until accumulation onto basic constructors
 //Unit_cov_transf
 injective symbol ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func;
 //Unit_con_transf
 injective symbol _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G;
 
 notation _'∘> infix right 80; notation ∘>'_ infix left 80;
 
 // todo jrulehd Unit_con_transfdu where only base is empty, this is transfdu
 //Unit_con_transfd
 //todo generalize
 // "dependent J-rule dependent-over-path"
 // injective symbol _'∘>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
 //  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B], 
 //  Π [J: cat] [M : func J X] (MM : funcd (Triv_catd J) M A), homd r FF RR GG → transfd ((M)_'∘> r) (Unit_modd MM FF) Id_funcd (MM ∘>>d RR) GG;
 injective symbol _'∘>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B], 
  Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), homd r FF RR GG → transfd ((M)_'∘> r) (Unit_modd MM FF) Id_funcd (MM ∘>>d RR) GG;
 //MM ∘>>d (Unit_modd0 _) d<<∘ FF
 
 notation _'∘>d infix right 80; //notation ∘>'_ infix left 80;
 
 
 //Unit_con_transfdu
 //"dependent J-rule non-dependent-over-path"
 // injective symbol _'∘>du : Π [I: cat] [A : catd I] [B : catd I]
 // [FF : funcd (Triv_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Triv_catd I) Id_func B], 
 // Π  (MM : funcd (Triv_catd I) Id_func A),
 // homdu FF RR GG → transfduu (Unit_moddu MM FF) Id_funcd (MM ∘>>du RR) GG;
 injective symbol _'∘>du : Π [I: cat] [A : catd I] [B : catd I]
 [FF : funcd (Triv_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Triv_catd I) Id_func B], 
 Π   [II : catd I] (MM : funcd II Id_func A),
 homdu FF RR GG → transfduu (Unit_moddu MM FF) Id_funcd (MM ∘>>du RR) GG;
 //(MM ∘>>du (Unit_moddu0 _) du<<∘ FF)
 notation _'∘>du infix right 80; //notation ∘>'_ infix left 80;
 
 // (substitution) admissible/eliminated until accumulation onto basic constructors
 //Comp_hom
 //todo Comp_homd '∘d
 injective symbol '∘ : Π [A' B' A B I : cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func B' B],
 hom X S Y → transf S F T G → hom (X ∘> F) T (G <∘ Y);
 notation '∘ infix right 80;
 
 injective symbol ∘' [A' B' A B I : cat] [S : mod A' B'] [T : mod A B]
 [X : func I A'] [Y : func I B'] [F : func A' A] [G : func B' B] :
 transf S F T G → hom X S Y → hom (X ∘> F) T (G <∘ Y)
  ≔ λ st s, s '∘ st;
 notation ∘' infix left 80;
 
 // no lack for Comp_transfd because it is always applied to Total_transf ? so no separate cut case analysis
 //Comp_transf
 injective symbol ''∘ : Π [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B],
 transf R X S Y → transf S F T G → transf R (X ∘> F) T (G <∘ Y);
 notation ''∘ infix right 80;
 
 injective symbol ∘'' [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B] :
 transf S F T G → transf R X S Y → transf R (X ∘> F) T (G <∘ Y)
   ≔ λ st rs, rs ''∘ st;
 notation ∘'' infix left 80;
 
 //Comp_hom
 //Comp_homd_transfd
 injective symbol '∘d : Π [A'' A' B' A B : cat] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func A'' B'] [F : func A' A] [G : func B' B],
 Π [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB'] [TT : modd AA T BB] [t : transf S F T G]
 [XX : funcd (Triv_catd A'') X AA'] [YY : funcd (Triv_catd A'') Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB]  [s : hom X S Y],
 homd s XX SS YY → transfd t SS FF TT GG → homd (s '∘ t) (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘d infix right 80;
 
 //Comp_homdu_transfdu
 injective symbol '∘dudu : Π [A' A B : cat]  [T : mod A B] 
  [F : func A' A] [G : func A' B],
 Π [AA' : catd A'] [BB' : catd A'] [AA : catd A] [BB : catd B] [SS : moddu AA' BB'] [TT : modd AA T BB] [t : hom F T G]
 [XX : funcd (Triv_catd A') Id_func AA'] [YY : funcd (Triv_catd A') Id_func BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB],
 homdu XX SS YY → transfdu t SS FF TT GG → homd t (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘dudu infix right 80;
 
 //Comp_homdu_transfduu
 injective symbol '∘duduu : Π [A : cat] ,
 Π [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [SS : moddu AA' BB'] [TT : moddu AA BB] 
 [XX : funcd (Triv_catd A) Id_func AA'] [YY : funcd (Triv_catd A) Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
 homdu XX SS YY → transfduu SS FF TT GG → homdu (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘duduu infix right 80;
 
 // other defined operations via induction-recursion
 
 symbol Total_cat : Π [X : cat], catd X → cat;
 
 //todo: allow explicit accumulator argument?
 symbol Total_proj_func : Π [X : cat] (A : catd X), func (Total_cat A) X;
 
 symbol Total_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
  funcd A xy B → func (Total_cat A) (Total_cat B);
 
 //lacked? could use Total_func
 //todo: del
 // symbol Total_funchd_func : Π [X : cat] [A : catd X] [B : catd X],
 //  funchd A B → func (Total_cat A) (Total_cat B);
 
 symbol Total_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → mod (Total_cat A) (Total_cat B);
 
 symbol Total_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
  (RR : modd A R B), transf (Total_mod RR) (Total_proj_func A) R (Total_proj_func B);
 
 symbol Total_moddu_mod : Π [I : cat] [A : catd I] [B : catd I],
  moddu A B → mod (Total_cat A) (Total_cat B);
 
 //lacked? could use Total_modd_proj_transf
 symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
 (RR : moddu A B), transf (Total_moddu_mod RR) (Total_proj_func A) (Unit_mod Id_func Id_func) (Total_proj_func B);
 
 symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [FF : funcd (Triv_catd I) F A] [RR : modd A R B] [GG : funcd (Triv_catd I) G B],
 homd r FF RR GG  → hom (Total_func FF) (Total_mod RR) (Total_func GG);
 
 symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
 [FF : funcd (Triv_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Triv_catd I) Id_func B], homdu FF RR GG →
 hom (Total_func FF) (Total_moddu_mod RR) (Total_func GG);
 
 symbol Total_transf: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 [t : transf R xx' R' yy' ] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'] ,
 transfd t RR FF RR' GG → transf (Total_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);
 
 symbol Total_transfdu_transf : Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [xx' : func I X'] [yy' : func I Y'] [R' : mod X' Y']
 [r : hom xx' R' yy' ] [RR : moddu A B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B' ],
 transfdu r RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);
 
 symbol Total_transfduu_transf : Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I]
 [RR : moddu A B] [FF : funcd A Id_func A'] [RR' : moddu A' B'] [GG : funcd B Id_func B'],
 transfduu RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_moddu_mod RR') (Total_func GG);
 
 rule Total_cat (Triv_catd $A) ↪ $A
 with Total_cat (Cast_catd $A) ↪ $A
 //with Total_cat (Fibre_catd $A $F) ↪ Fibre_cat $A $F  //should depend on particular catd
 with Total_cat (Comma_con_catd $R) ↪ (Comma_cat $R)
 with Total_cat (Comma_cov_catd $R) ↪ (Comma_cat $R)
 //nope more general 
 //with Total_cat (Sigma_catd $Z $F) ↪ (Total_cat $Z)
 ;
 
 rule Total_proj_func (Triv_catd $A) ↪ Id_func
 with Total_proj_func (Cast_catd $A) ↪ Terminal_func $A
 with Total_proj_func (Comma_con_catd $R) ↪ (Comma_con_func $R)
 with Total_proj_func (Comma_cov_catd $R) ↪ (Comma_cov_func $R)
 //nope more general 
 //with Total_proj_func (Sigma_catd $Z $F) ↪ (Total_proj_func $Z) ∘> $F
 ;
 
 rule (@Total_func _ _ $A $B $F $FF) ∘> (Total_proj_func $B) ↪ (Total_proj_func $A) ∘> $F;
 
 rule Total_func (Id_funcd) ↪ Id_func
 // todo: postpone Total_func of  Comp_funcd or act_funcd 
 with Total_func ($FF ∘>d $GG) ↪ Total_func $FF ∘> Total_func $GG
 with Total_func (Triv_funcd $F) ↪ $F
 with Total_func (Cast_funcd $F) ↪ $F
 with Total_func (Comma_con_funcd $r) ↪ (Comma_func $r)
 with Total_func (Comma_cov_funcd $r) ↪ (Comma_func $r)
 //nope more general 
 //with Total_func (SigmaIntro_funcd $Z $F) ↪ (Id_func)
 ;
 // todo Total_funchd_func  on inclusion
 
 //todo: del
 // rule Total_funchd_func (Id_funchd) ↪ Id_func;
 
 rule Total_moddu_mod (Triv_moddu $X) ↪ (Unit_mod Id_func Id_func)
 with Total_moddu_mod (Cast_moddu $R) ↪ $R
 //with Total_moddu_mod (Unit_moddu $F $G) ↪ (Unit_mod (Total_func $F) (Total_func $G));
 with Total_moddu_mod (Unit_moddu0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
 with  Total_moddu_mod ($FF ∘>>du $RR) ↪ (Total_func $FF) ∘>> (Total_moddu_mod $RR)
 with  Total_moddu_mod ($RR du<<∘ $GG ) ↪ (Total_moddu_mod $RR) <<∘ (Total_func $GG);
 
 rule Total_moddu_proj_transf (Triv_moddu $X) ↪ (Id_transf (Unit_mod Id_func Id_func))
 with Total_moddu_proj_transf (Cast_moddu $R) ↪ (Terminal_transf $R);
 
 rule Total_mod (Triv_modd $R) ↪ $R
 //with Total_mod (Unit_modd $FF $GG) ↪ (Unit_mod (Total_func $FF) (Total_func $GG))
 with Total_mod (Unit_modd0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
 with Total_mod (Comma_modd $R) ↪ (Comma_mod $R)
 with Total_mod ($R ⊗d $S) ↪ (Total_mod $R) ⊗ (Total_mod $S)
 with  Total_mod ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR)
 with  Total_mod ($RR d<<∘ $GG ) ↪ (Total_mod $RR) <<∘ (Total_func $GG);
 
 rule Total_modd_proj_transf (Triv_modd $R) ↪ (Id_transf $R)
 with Total_modd_proj_transf (Comma_modd $R) ↪ (Comma_transf $R)
 //.?with  Total_mod_proj ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR);
 ;
 
 rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr) '∘ (Total_modd_proj_transf $RR) ↪  $r;
 
 rule Total_hom (Comma_homd $r) ↪ Comma_hom $r
 with Total_hom ($rr ∘↓d $Z) ↪ (Total_hom $rr) ∘↓ $Z ;
 
 rule Total_hom (FuncId_homd $F) ↪ FuncId_hom (Total_func $F);
 
 rule (@Total_homdu_hom $I _ _ _ $RR _ $rr) '∘ (Total_moddu_proj_transf $RR) ↪  FuncId_hom Id_func;//TODO: INSTEAD Id_hom or FuncId_cov_hom or FuncId_hom ?
 
 rule Total_homdu_hom (FuncId_homdu $F) ↪ FuncId_hom (Total_func $F);
 
 
 symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;
 
 symbol FibreUniv_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A  → funcd J i (Fibre_catd A x);
 
 // symbol FibreUniv_funcd' : Π [X I : cat] (A : catd X) (x : func I X) [J : catd I]  ,
 // funcd J x A  → funcd J Id_func (Fibre_catd A x);
 
 symbol FibreProj_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;
 
 // symbol FibreProj_funcd : Π [X Y I : cat] [A : catd X] (x : func I X) [B : catd Y] [F : func X Y],
 // funcd A F B → funcd (Fibre_catd A x) (x ∘> F) B;
 
 
 // symbol Fibre_funchd : Π [X I : cat] [A B : catd X] (FF : funchd A B) (x : func I X), 
 // funchd (Fibre_catd A x) (Fibre_catd B x);
 
 rule Fibre_catd $A Id_func ↪ $A
 with Fibre_catd $A ($x ∘> $y)  ↪ Fibre_catd (Fibre_catd $A $y) $x;
 
 // Π X: cat, Π I: cat, Π I': cat, Π A: catd X, Π x: func I X, Π J: catd I', Π i: func I' I, funcd J (i ∘> x) A → Π Y: cat, Π F: func X Y, Π B: catd Y, funcd A F B → funcd J (i ∘> (x ∘> F)) B
 
 //rule (FibreUniv_funcd $A $x $i $FF) ∘>d (FibreProj_funcd $A $x $GG) ↪ $FF ∘>d $GG ;
 rule (FibreUniv_funcd $A $x _ $FF) ∘>d (FibreProj_funcd $A $x) ↪ $FF ;
 rule $HH ∘>d (FibreUniv_funcd $A $x _ $FF) ↪ (FibreUniv_funcd $A $x _ ($HH ∘>d $FF)) ;
 //rule (FibreUniv_funcd' $A $x $FF) ∘>d (FibreProj_funcd $A $x) ↪ $FF;
 
 //todo redo with Id_func
 // rule Fibre_funchd Id_funchd $x ↪ Id_funchd
 // with Fibre_funchd ($F ∘>hd $G) $x ↪ (Fibre_funchd $F $x) ∘>hd (Fibre_funchd $G $x);
 
 symbol Fibre_moddu : Π [I: cat] [A : catd I] [B : catd I] (RR : moddu A B),
  Π [J: cat] (i : func J I), moddu (Fibre_catd A i) (Fibre_catd B i);
 
 rule Fibre_moddu (Unit_moddu0 $II) $F ↪ Unit_moddu0 (Fibre_catd $II $F);
 
 //TODO: uncomment
 // symbol Fibre_homdu : Π [I: cat] [A : catd I] [B : catd I] [II: catd I] 
 // [FF : funchd II A] [RR : moddu A B] [GG : funchd II B],
 // homdu FF RR GG →  Π [J: cat] (i : func J I),
 // homdu (Fibre_funchd FF i)  (Fibre_moddu RR i) (Fibre_funchd GG i) ;
 
 symbol Fibre_modd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [S : mod X' Y'] [x : func X' X] [y : func Y' Y], transf S x R y → 
  modd (Fibre_catd A x) S (Fibre_catd B y);
 
 symbol Fibre_modd_moddu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [x : func I X] [y : func I Y], hom x R y → 
  moddu (Fibre_catd A x) (Fibre_catd B y);
 
 
 //todo Fibre_homdu of homdu along functor; ok do this
 //todo Fibre_transfuu of transfduu along functor;  ok do this
 
 //todo del
 // symbol Fibre_homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
 // Π [A : catd X] [B : catd Y] [II: catd I] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
 // homd FF RR GG →  Π [J: cat] (i : func J I),
 // homd (FibreProj_funcd i FF) RR (FibreProj_funcd i GG);
 
 // symbol Fibre_transfdu: Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [xx' : func I X'] [yy' : func I Y'] [R' : mod X' Y']
 // [RR : moddu A B] [FF : funcd A xx' A'] [R'R' : modd A' R' B'] [GG : funcd B yy' B'],
 // transfdu RR FF R'R' GG  → Π [J: cat] (i : func J I),
 //  transfdu (Fibre_moddu RR i) (FibreProj_funcd i FF) R'R' (FibreProj_funcd i GG);
 
 // symbol Proj_transfduu: Π [I : cat]  [A : catd I]  [B: catd I] 
 // [RR : moddu A B] , Π [J: cat] (i : func J I),
 // transfduu (Fibre_moddu RR i) (FibreProj_funcd i Id_funcd) RR (FibreProj_funcd i Id_funcd);
 
 
 ////----------
 
 // injective symbol  CartFib_funcdu : Π [I : cat] [II : catd I]
 // (r : hom Id_func (Unit_mod0 I) Id_func) (G : funcd (Triv_catd I) Id_func II), 
 // funcd (Triv_catd I) Id_func II;
 
 // injective symbol CartFib_homdu : Π [I : cat] [II : catd I]
 // (r : hom Id_func (Unit_mod0 I) Id_func) (G : funcd (Triv_catd I) Id_func II),
 // homdu (CartFib_funcdu r G) (Unit_moddu0 II) G;
 
 injective symbol CartFib_funcdu : Π [I I' : cat] (ii : func I' I) [II : catd I]
 (r : hom ii (Unit_mod0 I) ii) (G : funcd (Triv_catd I') ii II), 
 funcd (Triv_catd I') Id_func (Fibre_catd II ii);
 
 //todo: another grammar homu for hom Id_func _ Id_func ?
 ///todo : blend this with fibre
 injective symbol CartFib_homdu : Π [I I' : cat] (ii : func I' I) [II : catd I]
 (r : hom ii (Unit_mod0 I) ii) (G : funcd (Triv_catd I') ii II), 
 homdu (CartFib_funcdu ii r G) 
 ((Unit_moddu0 (Fibre_catd II ii)) du<<∘ (FibreUniv_funcd II ii Id_func G)) Id_funcd;
 
 // injective symbol FIbration_homdu : Π [I : cat] [II : catd I]
 // (r : hom Id_func (Unit_mod (@Id_func I) Id_func) Id_func) (G : funcd (Triv_catd I) Id_func II), 
 // homdu Id_funcd (Unit_moddu (CartFib_funcd r G) G) Id_funcd;
 
 
 //TODO: solve non-general problem by erasing accumulators from Unit_mod_
 //TODO del
 // injective symbol CartFibd_funcd : Π [I X : cat] [xi : func X I] [yi : func X I]  [II : catd I]
 // ( r : hom xi (Unit_mod0 I) yi) (G : funcd (Triv_catd X) yi II) ,
 // funcd (Triv_catd X) xi II;
 // injective symbol CartFibd_homd : Π [I X : cat] [xi : func X I] [yi : func X I]  [II : catd I]
 // ( r : hom xi (Unit_mod0 I) yi) (G : funcd (Triv_catd X) yi II) , // xx: X' -> X
 // homd r (CartFibd_funcd r G /*xx*/ ) (Unit_modd0 II) G  /*xx*/ ;
 
 injective symbol CartFibd_funcd : Π [I X X' : cat] (xx : func X' X) (xi : func X I) [yi : func X I]  [II : catd I]
 (r : hom (xx ∘> xi) ((Unit_mod0 I) <<∘ yi) xx) (G : funcd (Triv_catd X) yi II) ,
 funcd (Triv_catd X') (xx ∘> xi) II;
 injective symbol CartFibd_homd :  Π [I X X' : cat] (xx : func X' X) (xi : func X I) [yi : func X I]  [II : catd I]
 (r : hom (xx ∘> xi) ((Unit_mod0 I) <<∘ yi) xx) (G : funcd (Triv_catd X) yi II) ,
 homd r ((CartFibd_funcd xx xi r G)) ((Unit_modd0 II) d<<∘ G) (Triv_funcd xx);
 
 rule (Triv_funcd $zz) ∘>d (CartFibd_funcd $xx $xi $r $G) ↪ (CartFibd_funcd ($zz ∘> $xx) $xi ($r ∘↓ $zz) $G) ;
 rule  (CartFibd_homd $xx $xi $r $G) ∘↓d $zz ↪ (CartFibd_homd ($zz ∘> $xx) $xi ($r ∘↓ $zz) $G) ;
 
 
 ///-----------
 
 injective symbol Unit_transf : Π [I X Y : cat] [xi : func X I] [yi : func Y I] [II : catd I]
   (F : funcd (Triv_catd X) xi II) (G : funcd (Triv_catd Y) yi II), 
  transf (Unit_mod (Total_func F) (Total_func G)) Id_func (Unit_mod xi yi) Id_func;
 
 //Comp_transfduu_transfduu
 injective symbol ''∘duuduu : Π [ A : cat]
 [AA'' : catd A] [BB'' : catd A] [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [RR : moddu AA'' BB''] [SS : moddu AA' BB'] [TT : moddu AA BB] 
 [XX : funcd AA'' Id_func AA'] [YY : funcd BB'' Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
 transfduu RR XX SS YY → transfduu SS FF TT GG → transfduu RR (XX ∘>d FF) TT (YY ∘>d GG);
 notation ''∘duuduu infix right 80;
 
 //Comp_transfduu_transfdu
 injective symbol ''∘duudu : Π [ A' A B : cat]  [T : mod A B] 
  [F : func A' A] [G : func A' B],
 Π [AA'' : catd A'] [BB'' : catd A'] [AA' : catd A'] [BB' : catd A'] [AA : catd A] [BB : catd B] [RR : moddu AA'' BB''] [r : hom F T G] [SS : moddu AA' BB'] [TT : modd AA T BB] 
 [XX : funcd AA'' Id_func AA'] [YY : funcd BB'' Id_func BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB],
 transfduu RR XX SS YY → transfdu r SS FF TT GG → transfdu r RR (XX ∘>d FF) TT (YY ∘>d GG);
 notation ''∘duudu infix right 80;
 
 //Comp_transfdu_transfd
 injective symbol ''∘dud : Π [A'' A' B' A B : cat] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func A'' B'] [F : func A' A] [G : func B' B],
 Π [AA'' : catd A''] [BB'' : catd A''] [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B] [s : hom X S Y] [RR : moddu AA'' BB''] [t : transf S F T G] [SS : modd AA' S BB'] [TT : modd AA T BB] 
 [XX : funcd AA'' X AA'] [YY : funcd BB'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB],
 transfdu s RR XX SS YY → transfd t SS FF TT GG → transfdu (s '∘ t) RR (XX ∘>d FF) TT (YY ∘>d GG);
 notation ''∘dud infix right 80;
 
 //Comp_transfd
 injective symbol ''∘d : Π [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B],
 Π [AA'' : catd A''] [BB'' : catd B''] [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B]  [s : transf R X S Y] [RR : modd AA'' R BB''] [t : transf S F T G] [SS : modd AA' S BB'] [TT : modd AA T BB] 
 [XX : funcd AA'' X AA'] [YY : funcd BB'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB],
 transfd s RR XX SS YY → transfd t SS FF TT GG → transfd (s ''∘ t) RR (XX ∘>d FF) TT (YY ∘>d GG);
 notation ''∘d infix right 80;
 
 rule (@Total_transf _ _ _ _ _ _ _ _ _ _ _ _ $rr' $RR _ $RR' _ $rrr'r') ''∘ (Total_modd_proj_transf $RR') ↪ (Total_modd_proj_transf $RR) ''∘ $rr';
 
 //Unit_mod Id_func (Total_func $59302320) ≡ Total_mod (Unit_modd Id_funcd $59302320)
 rule Total_transf ( ($MM)_'∘>d $rr) ↪ (Total_func $MM)_'∘> (Total_hom $rr);
 rule Total_transf ($rs ''∘d $st) ↪ (Total_transf $rs) ''∘ (Total_transf $st);
 rule Total_transfduu_transf ($rs ''∘duuduu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfduu_transf $st);
 rule Total_transfdu_transf ($rs ''∘duudu $st) ↪ (Total_transfduu_transf $rs) ''∘ (Total_transfdu_transf $st);
 rule Total_transfdu_transf ($rs ''∘dud $st) ↪ (Total_transfdu_transf $rs) ''∘ (Total_transf $st);
 // todo: Total_hom of homdu applied/Comp_homd onto transfdu
 // todo: postpone Total_transf of  Comp_transfd or act_transfd 
 
 // symbol Fibre_transfd_transfdu : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 //  [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
 // transfd RR FF RR' GG → 
 // Π [I : cat] [G : func I Y] [F : func I X] (r : hom F R G), 
 // transfdu (Fibre_modd_moddu RR r) (FibreProj_funcd F FF) RR' (FibreProj_funcd G GG);
 
 symbol Proj_transfdu : Π [X Y : cat] [A : catd X] [B: catd Y] [R : mod X Y]
 [RR : modd A R B], Π [I : cat] [G : func I Y] [F : func I X] (r : hom F R G), 
 transfdu r (Fibre_modd_moddu RR r) (FibreProj_funcd  _ F) RR (FibreProj_funcd _ G);
 
 // symbol Fibre_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 //  [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
 // transfd RR FF RR' GG → 
 // Π [X0 Y0 : cat] [S : mod X0 Y0] [G : func Y0 Y] [F : func X0 X] (t : transf S F R G), 
 // transfd (Fibre_modd RR t) (FibreProj_funcd F FF) RR' (FibreProj_funcd G GG);
 
 symbol Proj_transfd : Π [X Y : cat] [A : catd X] [B: catd Y] [R : mod X Y]
 [RR : modd A R B], Π [X0 Y0 : cat] [S : mod X0 Y0] [G : func Y0 Y] [F : func X0 X] (t : transf S F R G), 
 transfd t (Fibre_modd RR t) (FibreProj_funcd _ F) RR (FibreProj_funcd _ G); 
 
 
 // symbol Fibre_transfd
 // symbol Fibre_transfhhd
 
 symbol Sum_catd : Π [X: cat] (A : catd X) (B: catd (Total_cat A)), catd X;
 
 rule Sum_catd (Triv_catd _) $B  ↪ $B
 with Sum_catd $A (Triv_catd _)  ↪ $A;
 
 symbol Pair_Sum_catd : Π [X: cat] (A : catd X) (B: catd (Total_cat A)) [Y'] [y'y : func Y' (Total_cat A)] [B' : catd Y'], 
   funcd B' y'y B → funcd B' y'y (Fibre_catd (Sum_catd A B) (Total_func (Catd_funcd A)));
 symbol Proj_Sum_catd : Π [X: cat] (A : catd X) (C: catd X) [X'] [xx' : func X X'] [C' : catd X'], 
   funcd C xx' C' → funcd (Sum_catd A (Fibre_catd C (Total_func (Catd_funcd A)))) xx' C';
 symbol Bij_Sum_catd : Π [X: cat] (A : catd X) (B: catd (Total_cat A)) (C: catd X),
   funcd B Id_func (Fibre_catd C (Total_func (Catd_funcd A))) → funcd (Sum_catd A B) Id_func C;  //todo funchd ?
 
 
 //TODO
 //symbol Pi_catd : Π [X: cat] (A : catd X) (B: catd (Total_cat A)), catd X;
 
 
 // other injective constructors via induction-recursion
 
 injective symbol SigmaElim_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X),
 Π [X' : cat] [C : catd X'] (G : func X X'),
   funcd Z (F ∘> G) C → funcd (Sigma_catd Z F) G C;
 
 // naturality
 rule (SigmaElim_funcd $Z $F $G $GG) ∘>d $HH ↪ (SigmaElim_funcd $Z $F _ ($GG ∘>d $HH));
 // beta
 rule (SigmaIntro_funcd $Z $F) ∘>d (SigmaElim_funcd $Z $F $G $GG) ↪ $GG;
 
 injective symbol FibreSigmaProj_funcd : Π [X Y : cat] (A : catd X) [F : func X Y] (B : catd Y)
 (FF : funcd A F B) (BB : catd (Total_cat B)),
 funcd (Sigma_catd (Fibre_catd BB (Total_func FF)) (Total_proj_func A))
       F  (Sigma_catd BB (Total_proj_func B));
 injective symbol FibreSigmaProj_isEquiv : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y]
 [FF : funcd A F B] (FF_ise : isEquiv FF) (BB : catd (Total_cat B)),
 isEquiv (FibreSigmaProj_funcd A B FF BB);
 
 rule (SigmaIntro_funcd (Fibre_catd $BB _) _) ∘>d (FibreSigmaProj_funcd $A $B $FF $BB) 
 ↪ (FibreProj_funcd $BB (Total_func $FF)) ∘>d (SigmaIntro_funcd $BB (Total_proj_func $B))  ;
 
 // rule (SigmaIntro_funcd (Fibre_catd $BB (Total_func $FF)) (Total_proj_func $A)) ∘>d (FibreSigmaProj_funcd $A $B $FF $FFe $BB) 
 // ↪ (FibreProj_funcd $BB (Total_func $FF)) ∘>d (SigmaIntro_funcd $BB (Total_proj_func $B))  ;
 
 // rule  (SigmaIntro_funcd (Fibre_catd $BB (Total_func $FF)) _) ∘>d (FibreSigmaProj_funcd $FF $FFe $BB) 
 // ↪ (SigmaIntro_funcd (Fibre_catd $BB (Total_func $FF)) _) ∘>d (FibreSigmaProj_funcd $FF $FFe $BB) ;
 
 // Π [Y X : cat] (Z : catd Y) (F : func Y X) (A : catd (Total_cat Z)),
 // catd (Total_cat (Sigma_catd Z F));
 
 
 // other injective constructors via induction-recursion
 
 injective symbol Fibre_coveringdu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
  [RR : modd A R B] [I' : cat] [J : catd I'] [G' : func I' I] [G : func I Y] [H : funcd J (G' ∘> G) B],
   covering RR H →  Π [F : func I X] (r : hom F R G),
   coveringdu (Fibre_modd_moddu RR r)  (FibreUniv_funcd _ G G' H );
 
 // injective symbol Fibre_coveringdu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 //  [RR : modd A R B] [J : catd I] [G : func I Y] [H : funcd J G B],
 //   covering RR H →  Π [F : func I X] (r : hom F R G),
 //   coveringdu (Fibre_modd_moddu RR r)  (FibreUniv_funcd H);
 
 injective symbol Total_covering' : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [I' : cat] [J : catd I'] [G' : func I' I] [G : func I Y] [H : funcd J (G' ∘> G) B],
 (Π [F : func I X] (r : hom F R G), coveringdu (Fibre_modd_moddu RR r)  (FibreUniv_funcd _ G G' H )) → 
  covering RR H;
 
 // injective symbol Total_covering' : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 // (RR : modd A R B) [J : catd I] [G : func I Y] [H : funcd J G B],
 // (Π [F : func I X] (r : hom F R G), coveringdu (Fibre_modd_moddu RR r)  (FibreUniv_funcd H)) → 
 //  covering RR H;
 
 injective symbol Imply_cov_transf : Π [A B A' B' C D D' : cat] [O : mod A B] [O' : mod A' B']
  [Q : mod C D] [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func D D'],
 transf O F O' G → Π (K : func D' B), transf Q Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (Imply_cov_mod O' ((G <∘ K) <∘ L) Q) Id_func;
 
 injective symbol Imply_cov_hom_transf : Π [A B A' B' C  D' : cat] [O : mod A B] [O' : mod A' B']
   [Q' : mod C D'] [F : func A A'] [G : func B B']  [L : func C D'],
 transf O F O' G → Π (K : func D' B), hom Id_func Q' L → 
 transf   (Imply_cov_mod O K Q')
        F (O' <<∘ ((G <∘ K) <∘ L)) Id_func;
 
 // injective symbol Glue_transf : Π [X Y A' B': cat] [A : catd X]  [B: catd Y] [R : mod X Y]
 // (RR : modd A R B) (FF : funcd A (Terminal_func X) (Cast_catd A')) (RR' : mod A'  B') (GG : funcd B (Terminal_func Y)  (Cast_catd B')),
 // Π I [G : func I Y], Π [J : catd I] [H : funcd J G B], covering RR H →
 // (Π [F : func I X] (r : hom F R G), transf (Total_mod (Fibre_hom_modd  RR r)) (Total_func (FibreProj_funcd F FF )) (Sheaf_con_mod RR') (Total_func (FibreProj_funcd  G GG))) →
 //   transf (Total_mod RR) (Total_func FF) (Sheaf_con_mod RR') (Total_func GG );
 
 injective symbol Glue_transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 [rr' : transf R xx' R' yy'] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
 Π [I : cat] [G : func I Y] [J : catd I] [H : funcd J G B], covering RR H →
 (Π [F : func I X] (r : hom F R G), transfdu (r '∘ rr') (Fibre_modd_moddu RR r) (FibreProj_funcd _ F ∘>d FF) (Sheaf_con_modd RR') (FibreProj_funcd _ G ∘>d GG)) →
   transfd rr' RR FF (Sheaf_con_modd RR') GG;
 
 
 
 
 // reduction-conversion relation
 injective symbol ==> : Π [I A B: cat] [F : func I A] [T : mod A B] [G :func I B],
 hom F T G → hom F T G → TYPE;
 notation ==> infix 20;
 
 injective symbol ==>> : Π [A' B' A B: cat] [S : mod A' B'] [F : func A' A] [T : mod A B] [G :func B' B],
 transf S F T G → transf S F T G → TYPE;
 notation ==>> infix 20;
 
 
 /* (1) ========================== */
 
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
 (Unit_Tensor_cov_transf pp)  ∘'' (Tensor_cov_hom_transf (Id_transf P) (FuncId_con_hom Id_func))
  ==>> pp;
 // transf P (Id_func ∘> F) P' (Id_func <∘ Id_func)
 
 /* (2) ========================== */
 
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
 
 //?solution to use of FuncId_hom : Z0 is identity in practice instances; or both versions are present
 // (1∘Z0-)∘t∘(g)  =  1∘t∘(- Y0<∘ g)
 type λ [L R I I0 I1 J : cat] 
 (X: func I I0) (X0: func I0 R)
 (Y0 : func I1 R) (Y: func I I1) (Z0 : func I1 L) (N : func J I1)
 (T : mod R L) (t : hom Y0 T Z0)
 (g : hom X (Unit_mod X0 Y0) Y),
 ((g '∘ ((X0)_'∘> t)) ∘>'_(Id_func)) // : transf ((Y ∘> Z0) ∘>1_) X (X0 ∘>> T) Id_func
    ∘'' (( (Y)_'∘> (FuncId_cov_hom Z0) ∘↓ N))
 ==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> (t ∘↓ N)))  ;
 // transf (Y ∘>> _1<∘ (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) 
 //        ((X0 ∘>> T) <<∘ Id_func) (Id_func <∘ (Z0 <∘ N))
 
 //TMPtmpsol
 //solution to use of FuncId_hom : Z0 is identity in practice instances; or both versions are present
 // (1∘1-)∘t∘(g)  =  1∘t∘(- Y0<∘ g)
 type λ [R I I0 I1 J : cat] 
 (X: func I I0) (X0: func I0 R)
 (Y0 : func I1 R) (Y: func I I1) (N : func J I1)
 (T : mod R I1) (t : hom Y0 T Id_func)
 (g : hom X (Unit_mod X0 Y0) Y),
 ((g '∘ ((X0)_'∘> t)) ∘>'_(Id_func)) // : transf (Y ∘>1_) X (X0 ∘>> T) Id_func
    ∘'' (( (Y)_'∘> (FuncId_hom Id_func) ∘↓ N))
 ==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> (t ∘↓ N)))  ;
 // : transf (Unit_mod Y (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) ((X0 ∘>> T) <<∘ Id_func) (Id_func <∘ (Id_func <∘ N))
 
 //tmp2 nope
 // type λ [L R I I0 I1 J : cat] 
 // (X: func I I0) (X0: func I0 R)
 // (Y0 : func I1 R) (Y: func I I1) (Z0 : func I1 L) (N : func J I1)
 // (T : mod R L) (t : Π [L'] (Z0' : func I1 L') (Z0'' : func L' L), hom Y0 (T <<∘ Z0'') Z0')
 // (g : hom X (Unit_mod X0 Y0) Y) K,
 // ((g '∘ ((X0)_'∘> (t _ Z0 K))) ∘>'_(Z0)) // : transf (Unit_mod (Z0 <∘ Y) Z0) (X ∘> Id_func) ((X0 ∘>> T) <<∘ Z0) Id_func
 //    ∘'' (( (Y)_'∘> (FuncId_hom Z0) ∘↓ N))
 //    ==>>  ((g ∘>'_(N)) ''∘ ((X0)_'∘> ((t _ Id_func (Z0 ∘> K)) ∘↓ N)))  ;
 //transf (Unit_mod Y (N ∘> Id_func)) (Id_func ∘> (X ∘> Id_func)) ((X0 ∘>> T) <<∘ Z0) (Id_func <∘ (Id_func <∘ N))
 
 /* (3) ========================== */
 
 // adjunction inverses
 
 // “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
 type λ [L R I J I0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) (Z : func I0 R) (M : func I I0)  (N : func J L),
  (((Adj_con_hom aj Z) ∘↓ M) ∘>'_(N)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj Id_func) ∘↓ N))
 ==>>  (((FuncId_cov_hom (Z '∘> LAdj_func)) ∘↓ M) ∘>'_(N) ) ''∘ (  (Z '∘> LAdj_func)_'∘> ((FuncId_con_hom Id_func) ∘↓ N) );
 // : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) N) M (Unit_mod (Z ∘> LAdj_func) Id_func) N
 
 
 // “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   
 type λ [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) Z (N : func I R) (M : func J R),
 ( (M)_'∘> ((Adj_con_hom aj Z) ∘↓ N) )   ''∘ ( (M ∘> Z )_'∘> (Adj_cov_hom aj Id_func) )
 ==>>  ( (M)_'∘> ((FuncId_cov_hom (Z '∘> LAdj_func)) ∘↓ N) ); 
 // : transf (Unit_mod M N) Id_func (Unit_mod (M ∘> (Z ∘> LAdj_func)) Id_func) ((Z ∘> LAdj_func) <∘ N)
 
 /* (4) ========================== */
 
 // right adjoint preserves weighted limits
 
 type λ  [B J0 J J' A : cat] (K : func J J0) (W : mod J' J) (F : func J0 B) (F_⇐_W : func J' B)
 (isl : limit K F W F_⇐_W) (R : func B A) (L : func A B) (isa : adj L R) I (M : func I A), 
  ((Imply_cov_transf ((M)_'∘> Adj_cov_hom isa F) K (Id_transf W)) ''∘ (limit_transf isl (M '∘> L)))
  ''∘ ((Adj_con_hom isa M) ∘>'_(F_⇐_W)) ;
  // : transf (Imply_cov_mod (Unit_mod M (F '∘> R)) K W) 
  // ((Id_func ∘> Id_func) ∘> Id_func) (Unit_mod M (Id_func '∘> R) <<∘ F_⇐_W) (Id_func <∘ (Id_func <∘ Id_func))
 
 /* (5) ========================== */
 
 // inductive data type
 
 symbol TerminalDatatype_cat : cat;
 symbol TerminalDatatype_First_func : Π [A : cat], func A Terminal_cat → func A TerminalDatatype_cat;
 symbol TerminalDatatype_Second_func : Π [A : cat], func A Terminal_cat → func A TerminalDatatype_cat;
 symbol TerminalDatatype_hom : Π [A : cat] (F : func A Terminal_cat), hom (TerminalDatatype_First_func F) (Unit_mod Id_func Id_func) (TerminalDatatype_Second_func F);
 symbol TerminalDatatype_elim : Π (E : cat) (first_func : func Terminal_cat E) 
 (second_func : func Terminal_cat E) (one_hom : hom first_func (Unit_mod Id_func Id_func) second_func), func TerminalDatatype_cat E;
 
 
 /* ========================== */
 
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
 ((M)_'∘> ((FuncId_cov_hom F) ∘↓ Z) ) ''∘ ((M ∘> F)_'∘> (FuncId_cov_hom F')) 
 ==>> ((M)_'∘> ((FuncId_cov_hom (F ∘> F')) ∘↓ Z)) ; 
 // : ransf (Unit_mod M (Z ∘> Id_func)) (Id_func ∘> Id_func) ((M ∘> F) ∘>> Unit_mod F' Id_func) (F' <∘ (F <∘ Z))
 
 // j-rule then apply hom then restrict
 type λ [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B]
 (M : func J A) (r : hom F R G ) K (M' : func K J ) N'  (a : hom M' (Unit_mod M F) N')
 K' (Z : func K' K), 
  ((a ∘↓ Z) '∘ ((M)_'∘> r)) 
 ==> (a '∘ ((M)_'∘> r)) ∘↓ Z ;
 // : hom (M' ∘> Id_func) (M ∘>> R) (G <∘ N')
 
 // assoc comp_transf then comp_hom
 type λ [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
 [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B]
 (rs : transf R X S Y) (st : transf S F T G) K (M' : func K A'') N'  (r : hom M' R N'),
 r '∘ (rs ''∘ st)
  ==> (r '∘ rs) '∘ st;
 
 //todo: derivable restr ?
 // type λ [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ,
 // ((M)_'∘> ((FuncId_cov_hom F) ∘↓ Z) ) ;
 
 // id_cov_hom on id_func is id_transf
 type λ [B : cat] I (M : func I B)  ,
 ((M)_'∘> (FuncId_cov_hom Id_func) )
 ==>> (Id_transf _)  ;
 
 // j-rule then applied to id_hom, both cov and con
 // note for confluence that already exists another rewrite that jrule of restr 
 type λ [I A B : cat] [F : func I A] [R : mod A B] [G : func I B]
 (r : hom F R G ) J (Z : func J _ ) , 
   (((FuncId_con_hom F) ∘↓ Z) '∘ ((Id_func)_'∘> r)) 
 ==> r ∘↓ Z;
 
 
 