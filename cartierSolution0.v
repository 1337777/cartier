(** # #
#+TITLE: cartierSolution0.v

Proph

https://gitlab.com/1337777/cartier/blob/master/cartierSolution0.v

shows the general outline of the solutions to some question of CARTIER which is
 how to program the MODOS proof-assistant for
 « dependent constructive computational logic for algebraic-geometric dataobjects »
 (including homotopy types) ...

Appendix: What is the minimal example of sheaf cohomology? Grammatically
Short: Hold any Dosen-style cut-elimination confluence of arrow-terms (for some comonad, or pairing-product, or 2-category, or proof-net star-autonomous category,... ), and form the (petit) grammatical-globular site (double category) whose objects are the arrow-terms and where any (necessarily finite) covering family of morphisms is either any reduction-conversion linkage or all the (immediate proper, including unit-arrows in cuts) subterms of some redex arrow-term. Define any model (in Set) to be some grammatical sheaf (hence globular copresheaf) of (span of) sets over this site, where each covering family become limit cone (constructively, using compatible families). Now starting with some generative presheaf data, then sheafification-restricted-below-any-sieve of this presheaf can be inductively constructed by refinements of the sieves. Moreover, it may be assumed some generating cocontinuous adjunction of sites; the result is some dependent-constructive-computational-logic of geometric dataobjects (including homotopy-types): MODOS. Now globular homology of any copresheaf computes the composable occurrences of arrow-terms (cycles from 0 to 1). Also grammatical cohomology of the sheafification (graded by the nerve of its sieve argument) computes the global solutions of occurrences of all arrow-terms in the model which satisfy the confluence of reductions in the site. Contrast to the covariant sketch models of some coherent theory; but now any globular-covariant (contravariant finite-limit sketch) concrete model is some category with operations on arrows. The sense mimicks the usual Kripke-Joyal sense, as explicit definitions. The generic model contravariantly sends any object G to the covariant diagram of sets represented by the sheafified G over only the finitely-presentable (data) sheaf-models: G ↦ Hom(sheafified(Hom(–, G)), fpModelsSet(_)) … and further could be sliced over any (outer/fixed) dataobject.

(1.) Morphisms: the shape of the point is now “A” instead of singleton, context extension is polymorph…
for (B over Delta) and for variable (Theta), then
Span(Theta ~> (Delta;B))  :<=>  Hom( (x: Gamma; a: A( h(x) )) ~> B( f(x) ) ) with some (f: Gamma -> Delta) and (h: Gamma -> Theta) and (A over Theta)

ERRATA: (2.) Algebraic-geometric dataobjects: the elimination schema for the dataobjects gives the base of the construction for the sheafification; continued with the refinements/gluing schema below any sieve...

| Constructing : asConstructor F U f
______________________________________
Hom( Restrict U VV ~> Restrict F VV ))

| Destructing : (forall U (f : F U) (cons_f : asConstructor F U f), 
			Hom( Restrict U VV ~> E ))
___________________________________________________________________
Hom( Restrict F VV ~> Sheafified E VV )

| Refining : (forall W (v : Site( W ~> V | in sieve VV )), 
			Hom( Restrict F WW_v ~> Sheafified E WW_v ))
____________________________________________________________________
Hom( Restrict F WW_VV ~> Sheafified E WW_VV )

Lemma: cut-elimination holds. Corollary: grammatical sheaf cohomology exists.

Applications: with 2-category sites, get some constructive homotopy types; with proof-net star-autonomous categories sites, get some constructive alternative to Urs Schreiber's geometry of quantum-fields physics.

https://nicolasbourbaki365-demo.workschool365.com
( https://github.com/1337777/cartier/blob/master/cartierSolution0.v )


OUTLINE ::

* Generating site, its cut-elimination and confluence

* Generated modos, its cut-elimination and confluence

* Example

-----

* Generating site, its cut-elimination and confluence

#+BEGIN_SRC coq :exports both :results silent # # **)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Lia.

Module SHEAF.

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections.

Notation "'sval'" := (@proj1_sig _ _).

Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Module Type GENERATOR.

Parameter obGenerator : eqType.

Parameter morGenerator : obGenerator -> obGenerator -> Type.
Notation "''Generator' ( V ~> U )" := (@morGenerator V U)
(at level 0, format "''Generator' (  V  ~>  U  )") : poly_scope.

Parameter polyGenerator :
forall U V, 'Generator( V ~> U ) -> forall W, 'Generator( W ~> V ) -> 'Generator( W ~> U ).
Notation "wv o>Generator vu" := (@polyGenerator _ _ vu _ wv)
(at level 40, vu at next level) : poly_scope.

Parameter unitGenerator : forall {U : obGenerator}, 'Generator( U ~> U ).

Parameter polyGenerator_morphism :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
        (W : obGenerator) (wv : 'Generator( W ~> V )),
forall X (xw : 'Generator( X ~> W )),
  xw o>Generator ( wv o>Generator vu ) = ( xw o>Generator wv ) o>Generator vu.
Parameter polyGenerator_unitGenerator :
forall (U V : obGenerator) (vu : 'Generator( V ~> U )),
  vu = ((@unitGenerator V) o>Generator vu ).
Parameter unitGenerator_polyGenerator :
forall (U : obGenerator), forall (W : obGenerator) (wv : 'Generator( W ~> U )),
    wv = ( wv o>Generator (@unitGenerator U)).

(* CONSTRUCTIVE CONFLUENCE: 2 kinds of arrows.
  FIRST KIND OF ARROWS: these arrows below are required to be computational; 
    and in fact these arrows will appear by-definition
      during the inductive construction of the confluence *)
Parameter ConflVertex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )), obGenerator.
Parameter ConflProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  'Generator( ConflVertex projecter indexer ~> IndexerVertex ).
Parameter ConflIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  'Generator( ConflVertex projecter indexer ~> ProjecterVertex ).
Parameter ConflMorphismIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  'Generator( ConflVertex projecter (preIndexer o>Generator indexer) ~>
                          ConflVertex projecter indexer ).
Parameter ConflMorphismProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
  'Generator( ConflVertex (preProjecter o>Generator projecter) indexer ~>
                          ConflVertex projecter indexer ).
Parameter ConflComposProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
  'Generator( (ConflVertex preProjecter (ConflIndex projecter indexer))
                    ~> (ConflVertex (preProjecter o>Generator projecter) indexer )).
Parameter ConflDiagonal :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
  'Generator( (ConflVertex (projecter o>Generator diagonal) (indexer o>Generator diagonal) )
                        ~>  (ConflVertex projecter indexer) ).

Parameter ConflCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  ConflProject projecter indexer o>Generator indexer
  = ConflIndex projecter indexer o>Generator projecter.
Parameter ConflMorphismIndexCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
ConflProject projecter (preIndexer o>Generator indexer) o>Generator preIndexer
= ConflMorphismIndex projecter indexer preIndexer o>Generator ConflProject projecter indexer
/\  ConflIndex projecter (preIndexer o>Generator indexer)
    = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer.
Parameter ConflMorphismProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
ConflIndex (preProjecter o>Generator projecter) indexer o>Generator preProjecter
= ConflMorphismProject projecter indexer preProjecter o>Generator ConflIndex projecter indexer
/\  ConflProject (preProjecter o>Generator projecter) indexer
    = ConflMorphismProject projecter indexer preProjecter o>Generator ConflProject projecter indexer.
Parameter ConflMorphismIndexProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
ConflMorphismIndex (preProjecter o>Generator projecter) indexer preIndexer
o>Generator ConflMorphismProject projecter indexer preProjecter 
= ConflMorphismProject projecter (preIndexer o>Generator indexer) preProjecter
o>Generator ConflMorphismIndex projecter indexer preIndexer.
Parameter ConflComposProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
(ConflComposProject projecter indexer preProjecter) o>Generator (ConflIndex (preProjecter o>Generator projecter) indexer) 
  = (ConflIndex preProjecter (ConflIndex projecter indexer))
  /\  (ConflComposProject projecter indexer preProjecter) o>Generator (ConflMorphismProject projecter indexer preProjecter)
      = ConflProject preProjecter (ConflIndex projecter indexer) .
Parameter ConflDiagonalCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
(ConflDiagonal projecter indexer diagonal) o>Generator (ConflIndex projecter indexer)
= (ConflIndex (projecter o>Generator diagonal) (indexer o>Generator diagonal) )
  /\  (ConflDiagonal projecter indexer diagonal) o>Generator (ConflProject projecter indexer) 
      = (ConflProject (projecter o>Generator diagonal) (indexer o>Generator diagonal) ) .

(* CONFLUENCE PROPERTIES:
  SECOND KIND OF ARROWS: these arrows below are NOT required to be computational; 
    and these arrows are mere derivable logical properties of the confluence 
      which are proved after the definition of confluence *)
Parameter ConflProp_ComposIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex (ConflProject projecter indexer) preIndexer )) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter (preIndexer o>Generator indexer ))) |
  CommonConfl1 o>Generator (ConflProject (ConflProject projecter indexer) preIndexer )
  = CommonConfl2 o>Generator (ConflProject projecter (preIndexer o>Generator indexer ))
  /\  CommonConfl1 o>Generator ((ConflIndex (ConflProject projecter indexer) preIndexer ))
      = CommonConfl2 o>Generator (ConflMorphismIndex projecter indexer preIndexer )
} } }.

Parameter ConflProp_AssocIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PrePreIndexerVertex (prePreIndexer : 'Generator( PrePreIndexerVertex ~> PreIndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~>
 (ConflVertex projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~>
 (ConflVertex projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))) |
  CommonConfl1 o>Generator (ConflProject projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)))
  = CommonConfl2 o>Generator (ConflProject projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))
  /\  CommonConfl1 o>Generator ((ConflMorphismIndex projecter (preIndexer o>Generator indexer) prePreIndexer)
                                  o>Generator (ConflMorphismIndex projecter indexer preIndexer))
      = CommonConfl2 o>Generator (ConflMorphismIndex projecter indexer (prePreIndexer o>Generator preIndexer))
} } }.

Parameter ConflProp_MorphismIndexRelativeProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                            (ConflMorphismIndex projecter (indexer) preIndexer
                            o>Generator (ConflProject projecter (indexer) o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                                (ConflProject projecter (preIndexer o>Generator indexer)
                                o>Generator (preIndexer o>Generator indexer))) |
CommonConfl1 o>Generator ConflProject projecter (ConflMorphismIndex projecter (indexer) preIndexer
o>Generator (ConflProject projecter (indexer) o>Generator indexer))
= CommonConfl2 o>Generator ConflProject projecter
(ConflProject projecter (preIndexer o>Generator indexer) o>Generator (preIndexer o>Generator indexer))
/\  CommonConfl1 o>Generator (ConflMorphismIndex projecter (ConflProject projecter (indexer) o>Generator indexer)
(ConflMorphismIndex projecter (indexer) preIndexer)
  o>Generator ConflMorphismIndex projecter (indexer) (ConflProject projecter (indexer)))
= CommonConfl2 o>Generator (ConflMorphismIndex projecter (preIndexer o>Generator indexer)
                              (ConflProject projecter (preIndexer o>Generator indexer))
        o>Generator ConflMorphismIndex projecter (indexer) preIndexer)
} } }.

Parameter ConflProp_ComposRelativeIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
                         ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
                 (ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer)) |
CommonConfl1 o>Generator ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
= CommonConfl2 o>Generator ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer
                                                          o>Generator ConflIndex projecter indexer)
/\  CommonConfl1 o>Generator (ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
o>Generator ConflMorphismIndex projecter indexer preIndexer)
= CommonConfl2 o>Generator (ConflMorphismIndex preProjecter (ConflIndex projecter indexer)
  (ConflMorphismIndex projecter indexer preIndexer)
o>Generator ConflProject preProjecter (ConflIndex projecter indexer))
} } }.

Parameter ConflProp_MixIndexProject_1 :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ConflVertex projecter indexer )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~>
 ConflVertex (preProjecter o>Generator ConflProject projecter indexer) preIndexer ) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~>
 ConflVertex preProjecter (ConflMorphismIndex projecter indexer preIndexer)) |
  CommonConfl1 o>Generator ConflProject (preProjecter o>Generator ConflProject projecter indexer) preIndexer
  = CommonConfl2 o>Generator (ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer)
                                          o>Generator ConflProject projecter (preIndexer o>Generator indexer))
  /\  CommonConfl1 o>Generator (ConflIndex (preProjecter o>Generator ConflProject projecter indexer) preIndexer)
      = CommonConfl2 o>Generator (ConflIndex preProjecter (ConflMorphismIndex projecter indexer preIndexer))
} } }.

Parameter ConflProp_ComposRelativeIndex_ComposProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
                    ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
            (ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer)) |
CommonConfl1 o>Generator ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
= CommonConfl2 o>Generator ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer
                                                          o>Generator ConflIndex projecter indexer)
/\  (CommonConfl1 o>Generator ConflComposProject projecter (preIndexer o>Generator indexer) preProjecter)
    o>Generator ConflMorphismIndex (preProjecter o>Generator projecter) (indexer) preIndexer
= (CommonConfl2 o>Generator ConflMorphismIndex preProjecter (ConflIndex projecter (indexer))
              (ConflMorphismIndex projecter (indexer) preIndexer))
      o>Generator ConflComposProject projecter (indexer) preProjecter
} } }.

Parameter ConflProp_AssocIndex_Diagonal :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
ConflVertex (projecter o>Generator diagonal) (preIndexer o>Generator (indexer o>Generator diagonal))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> 
ConflVertex (projecter o>Generator diagonal) ((preIndexer o>Generator indexer) o>Generator diagonal)) |
CommonConfl1 o>Generator ConflProject (projecter o>Generator diagonal)
              (preIndexer o>Generator (indexer o>Generator diagonal)) =
CommonConfl2 o>Generator ConflProject (projecter o>Generator diagonal)
              ((preIndexer o>Generator indexer) o>Generator diagonal)
/\ (CommonConfl1 o>Generator ConflMorphismIndex (projecter o>Generator diagonal)
                (indexer o>Generator diagonal) preIndexer)
      o>Generator ConflDiagonal projecter (indexer) diagonal
 = (CommonConfl2 o>Generator ConflDiagonal projecter (preIndexer o>Generator indexer) diagonal)
        o>Generator ConflMorphismIndex projecter (indexer) preIndexer
} } }.

End GENERATOR.

Module Type COMOD (Generator : GENERATOR).
Import Generator.
(** # #
#+END_SRC

* Generated modos, its cut-elimination and confluence

#+BEGIN_SRC coq :exports both :results silent # # **)
Definition Sense01_action (Sense00 : obGenerator -> Type)
(Sense01 : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Sense00 G -> Sense00 G')
          G G' (g : 'Generator( G' ~> G)) (x : Sense00 G)
:= (Sense01 G G' g x).

Notation "g o>Generator_ [ Sense01 ] x" := (@Sense01_action _ Sense01 _ _ g x)
 (at level 40, x at next level) : poly_scope.
Notation "g o>Generator_ x" := (@Sense01_action _ _ _ _ g x)
(at level 40, x at next level) : poly_scope.

Definition Sense01_functor (Sense00 : obGenerator -> Type)
 (Sense01 : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Sense00 G -> Sense00 G') : Prop :=
( forall G G' (g : 'Generator( G' ~> G)) G'' (g' : 'Generator( G'' ~> G')) x,
    g' o>Generator_[Sense01] (g o>Generator_[Sense01] x)
    = (g' o>Generator g) o>Generator_[Sense01] x ) /\
( forall G x, x = (@unitGenerator G) o>Generator_[Sense01] x ).

Definition Sense01_def (Sense00 : obGenerator -> Type)
:= { Sense01 : ( forall G G' : obGenerator, 'Generator( G' ~> G ) -> Sense00 G -> Sense00 G' ) |
      Sense01_functor Sense01 }.

Definition Sense1_natural Sense00_F (Sense01_F : Sense01_def Sense00_F)
 Sense00_E (Sense01_E : Sense01_def Sense00_E) (Sense1 : forall G : obGenerator, Sense00_F G -> Sense00_E G) : Prop :=
forall G G' (g : 'Generator( G' ~> G )) (f : Sense00_F G),
  g o>Generator_[sval Sense01_E] (Sense1 G f)
  = Sense1 G' (g o>Generator_[sval Sense01_F] f).

Definition Sense1_def Sense00_F (Sense01_F : Sense01_def Sense00_F) Sense00_E (Sense01_E : Sense01_def Sense00_E)
:=  { Sense1 : ( forall G : obGenerator, Sense00_F G -> Sense00_E G ) |
      Sense1_natural Sense01_F Sense01_E Sense1 }.

Notation "''exists'  x  ..." := (exist _ x _) (at level 10, x at next level) : poly_scope.
Notation "[<  data  |  ...  >]" := (@existT _ (fun data => @sigT _ _) data _) (at level 0) : poly_scope.

Lemma Sense00_ViewOb : forall (G : obGenerator), (obGenerator -> Type).
Proof. intros G. refine (fun H => 'Generator( H ~> G )). Defined.

Lemma Sense01_ViewOb : forall (G : obGenerator), Sense01_def (Sense00_ViewOb G).
Proof.
intros. unshelve eexists.
- intros H H' h. refine (fun g => h o>Generator g).
- abstract (split; [intros; exact: polyGenerator_morphism
                    | intros; exact: polyGenerator_unitGenerator]).
Defined.

Record Sense00_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
      U V (vu : 'Generator( V ~> U )) (G: obGenerator) : Type :=
{ getIndexerOfViewing : 'Generator( G ~> U ) ;
  getDataOfViewing : Sense00_F (ConflVertex vu getIndexerOfViewing)
}.

Axiom Sense00_Viewing_quotient :
 forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
  U V (vu : 'Generator( V ~> U )),
forall G : obGenerator, forall (f1 f2 : Sense00_Viewing Sense01_F vu G),
forall (CommonConflVertex : obGenerator)
(CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex vu (getIndexerOfViewing f1))))
(CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex vu (getIndexerOfViewing f2)))),
CommonConfl1 o>Generator (ConflProject vu (getIndexerOfViewing f1))
= CommonConfl2 o>Generator (ConflProject vu (getIndexerOfViewing f2)) ->
CommonConfl1 o>Generator_[sval Sense01_F] (getDataOfViewing f1)
= CommonConfl2 o>Generator_[sval Sense01_F] (getDataOfViewing f2)
-> f1 = f2.

Definition Sense01_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
          U V (vu : 'Generator( V ~> U ))
: Sense01_def (Sense00_Viewing Sense01_F vu ).
Proof.
intros. unshelve eexists.
- intros G G' g f. exists ( g o>Generator (getIndexerOfViewing f)).
exact: ((ConflMorphismIndex vu (getIndexerOfViewing f) g) 
            o>Generator_[sval Sense01_F] (getDataOfViewing f)).
- abstract (split; simpl;
[ intros G G' g G'' g' f;
move: (ConflProp_AssocIndex vu (getIndexerOfViewing f) g g' ) =>
  [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
  unshelve eapply Sense00_Viewing_quotient; simpl;
  [ | exact CommonConfl1
  | exact CommonConfl2
  | assumption
  | ];
  do 2 rewrite [LHS](proj1 (proj2_sig Sense01_F));
      rewrite [RHS](proj1 (proj2_sig Sense01_F));
      congr( _ o>Generator_ _);
      rewrite -polyGenerator_morphism;
      assumption
| intros G f;
  unshelve eapply Sense00_Viewing_quotient; simpl;
  [ | exact (ConflMorphismIndex vu (getIndexerOfViewing f) unitGenerator)
  | exact unitGenerator
  | rewrite -(proj1 (ConflMorphismIndexCommuteProp vu (getIndexerOfViewing f) unitGenerator));
    rewrite -[RHS]polyGenerator_unitGenerator -[LHS]unitGenerator_polyGenerator; reflexivity
  | rewrite [RHS](proj1 (proj2_sig Sense01_F));
    congr( _ o>Generator_ _);
    rewrite -[RHS]polyGenerator_unitGenerator; reflexivity
]]).
Defined.

Record Sense00_ViewedOb Sense00_F (Sense01_F : Sense01_def Sense00_F)
      U V (vu : 'Generator( V ~> U )) (G: obGenerator) : Type :=
{ getProjectVertexOfViewed : obGenerator ;
  getProjectOfViewed : 'Generator( getProjectVertexOfViewed ~> G ) ;
  getDataOfViewed : (Sense00_Viewing Sense01_F vu) getProjectVertexOfViewed ;
}.

Axiom Sense00_ViewedOb_quotient :
forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
        U V (vu : 'Generator( V ~> U )) (G: obGenerator),
forall (f1 f2 : Sense00_ViewedOb Sense01_F vu G),
forall (CommonConflVertex : obGenerator)
    (CommonConfl1 : 'Generator( CommonConflVertex ~> getProjectVertexOfViewed f1 ))
    (CommonConfl2 : 'Generator( CommonConflVertex ~> getProjectVertexOfViewed f2 )),
  CommonConfl1 o>Generator (getProjectOfViewed f1)
  = CommonConfl2 o>Generator (getProjectOfViewed f2) ->
  CommonConfl1 o>Generator_[sval (Sense01_Viewing Sense01_F vu)] (getDataOfViewed f1)
  = CommonConfl2 o>Generator_[sval (Sense01_Viewing Sense01_F vu)] (getDataOfViewed f2)
  -> f1 = f2.

Definition Sense01_ViewedOb Sense00_F (Sense01_F : Sense01_def Sense00_F)
          U V (vu : 'Generator( V ~> U ))
: Sense01_def (Sense00_ViewedOb Sense01_F vu).
Proof.
intros. unshelve eexists.
- intros G G' g f. exact
{| getProjectVertexOfViewed :=(ConflVertex (getProjectOfViewed f) g) ;
  getProjectOfViewed := (ConflProject (getProjectOfViewed f) g) ;
  getDataOfViewed := ((ConflIndex (getProjectOfViewed f) g) 
                    o>Generator_[sval (Sense01_Viewing Sense01_F vu)] (getDataOfViewed f)) 
|}.
- abstract (split; simpl;
[ intros G G' g G'' g' f;
move: (ConflProp_ComposIndex (getProjectOfViewed f) g g' ) =>
[CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| assumption
| ];
do 2 rewrite [LHS](proj1 (proj2_sig (Sense01_Viewing Sense01_F vu)));
rewrite [RHS](proj1 (proj2_sig (Sense01_Viewing Sense01_F vu)));
congr( _ o>Generator_ _); rewrite HeqIndex; rewrite -polyGenerator_morphism;
rewrite -(proj2 (ConflMorphismIndexCommuteProp _ _ _ )); reflexivity
| intros G f;
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact (ConflIndex (getProjectOfViewed f) unitGenerator)
| exact unitGenerator
| rewrite -(ConflCommuteProp (getProjectOfViewed f) unitGenerator);
  rewrite -polyGenerator_unitGenerator -unitGenerator_polyGenerator; reflexivity
| rewrite [RHS](proj1 (proj2_sig (Sense01_Viewing Sense01_F vu)));
  congr( _ o>Generator_ _);
  rewrite -polyGenerator_unitGenerator; reflexivity
]]).
Defined.

Definition Sense1_Compos :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) 
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F') 
(Sense1_ff' : Sense1_def Sense01_F' Sense01_F)
(Sense00_F'' : obGenerator -> Type) (Sense01_F'' : Sense01_def Sense00_F'')
(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F'),
Sense1_def Sense01_F'' Sense01_F.
Proof.
intros. unshelve eexists.
- intros G dataIn.
apply: (sval Sense1_ff' G (sval Sense1_ff_ G dataIn)).
- abstract (move; simpl; intros; rewrite [LHS](proj2_sig Sense1_ff');
          rewrite (proj2_sig Sense1_ff_); reflexivity).
Defined.

Definition Sense1_Constructing_default :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F),
forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) (Sense01_Viewing Sense01_F vu).
Proof.
intros. unshelve eexists.
- intros H h. exact {|
  getIndexerOfViewing := getIndexerOfViewing h;
  getDataOfViewing := getDataOfViewing h o>Generator_[sval Sense01_F] form
|}.
- abstract (move; simpl; intros; unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| rewrite -(proj1 (proj2_sig Sense01_F)); reflexivity ]).
Defined.

Definition Sense1_ViewObMor :
forall (G : obGenerator) (H : obGenerator) (g : 'Generator( H ~> G )),
Sense1_def (Sense01_ViewOb H) (Sense01_ViewOb G).
Proof.
intros G H hg. unshelve eexists.
- intros G0 h. exact: (  h o>Generator hg ).
- abstract (move; simpl; intros ; rewrite /Sense01_action /= ; exact: polyGenerator_morphism).
Defined.

Definition Sense1_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
U V (vu : 'Generator( V ~> U ))
Sense00_E (Sense01_E : Sense01_def Sense00_E)
(Sense1_ff : Sense1_def Sense01_F Sense01_E) :
Sense1_def (Sense01_Viewing Sense01_F vu) (Sense01_Viewing Sense01_E vu).
Proof.
intros. unshelve eexists.
- intros G f. exact
{|
getIndexerOfViewing := getIndexerOfViewing f;
  getDataOfViewing :=
    sval Sense1_ff (ConflVertex vu (getIndexerOfViewing f))
        (getDataOfViewing f)
|}.
- abstract (move; intros; simpl;
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
  | exact unitGenerator
  | reflexivity
  | rewrite (proj2_sig Sense1_ff); reflexivity ] ).
Defined.

Definition Morphism_prop
U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
  Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E) :=
forall (G : obGenerator)  (form : Sense00_F G),
forall (G' : obGenerator) (g : 'Generator( G' ~> G )) ,
forall (H : obGenerator) (f0 : (Sense00_Viewing (Sense01_ViewOb G') vu) H) f,
(*  pb (g'o>g) V = V = pb (g) V *)
f =  (sval (Sense1_Viewing vu (Sense1_ViewObMor g)) H f0) ->
(sval (Sense1_ee__ G form) H f) =
(sval (Sense1_ee__ G' (g o>Generator_[sval Sense01_F] form)) H f0).

Lemma Morphism_Constructing
: forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
Morphism_prop Sense01_F (@Sense1_Constructing_default _ _ vu _ Sense01_F ).
Proof.
intros; move; intros; subst; unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| congr ( _ o>Generator_ _);
  rewrite (proj1 (projT2 Sense01_F)); reflexivity ].
Qed.

Definition Sense1_Destructing :
forall U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee : forall (G : obGenerator) (form : Sense00_F G),
  Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee),
Sense1_def (Sense01_Viewing Sense01_F vu ) (Sense01_ViewedOb Sense01_E vu).
Proof.
intros. unshelve eexists.
- intros G f. refine
{|
getProjectVertexOfViewed := ConflVertex vu (getIndexerOfViewing f);
getProjectOfViewed := ConflProject vu (getIndexerOfViewing f);
getDataOfViewed := {|
  getIndexerOfViewing :=
       (ConflProject vu (getIndexerOfViewing f)) o>Generator (getIndexerOfViewing f) ;
  getDataOfViewing := ( ConflProject vu 
              ((ConflProject vu (getIndexerOfViewing f)) o>Generator (getIndexerOfViewing f)) )
      o>Generator_[sval Sense01_E] 
        (sval (Sense1_ee (ConflVertex vu (getIndexerOfViewing f))
                      (getDataOfViewing f)) (ConflVertex vu (getIndexerOfViewing f))
            {|
              getIndexerOfViewing :=
                ConflProject vu (getIndexerOfViewing f)
                              o>Generator getIndexerOfViewing f;
              getDataOfViewing :=
                ConflMorphismIndex vu (getIndexerOfViewing f)
                                    (ConflProject vu (getIndexerOfViewing f))
            |})
  |}
|}.
- abstract (move; simpl; intros G G' g' f;
move: (ConflProp_ComposIndex vu (getIndexerOfViewing f) g' )
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| exact HeqProject
| ];
do 1 rewrite [LHS](proj1 (proj2_sig (Sense01_Viewing Sense01_E vu)));
rewrite HeqIndex;
do 1 rewrite -[LHS](proj1 (proj2_sig (Sense01_Viewing Sense01_E vu)));
congr (_ o>Generator_ _);
move: (ConflProp_MorphismIndexRelativeProject vu (getIndexerOfViewing f) g')
=> [CommonConflVertex' [CommonConfl1' [CommonConfl2' [HeqProject' HeqIndex']]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact CommonConfl1'
| exact CommonConfl2'
| exact HeqProject'
| ];
do 1 rewrite [in RHS](proj1 (proj2_sig Sense01_E));
rewrite -[in RHS]HeqProject';
do 1 rewrite -[in RHS](proj1 (proj2_sig Sense01_E));
congr (_ o>Generator_ _);
do 1 rewrite [in LHS](proj1 (proj2_sig Sense01_E));
rewrite -[in LHS](proj1 (ConflMorphismIndexCommuteProp _ _ _));
do 1 rewrite -[in LHS](proj1 (proj2_sig Sense01_E));
congr (_ o>Generator_ _);

do 1 rewrite [in LHS](proj2_sig (Sense1_ee _ _));
apply: Sense1_ee_morphism;
move: (ConflProp_MorphismIndexRelativeProject vu (getIndexerOfViewing f) g')
=> [CommonConflVertex'' [CommonConfl1'' [CommonConfl2'' [HeqProject'' HeqIndex'']]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact CommonConfl1''
| exact CommonConfl2''
| exact HeqProject''
| assumption ]).
Defined.

Definition Sense1_UnitViewing
U V (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F) (G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F) :
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) (Sense01_Viewing Sense01_F vu).
Proof.
intros; unshelve eexists.
- intros H h. exact
  {|  getIndexerOfViewing := (getIndexerOfViewing h) ;
      getDataOfViewing := (ConflProject vu (getIndexerOfViewing h))
                          o>Generator_[sval Sense01_F] (sval Sense1_ff H h)
  |}.
- abstract (move; simpl; intros H H' h' f;
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ];
congr ( _ o>Generator_ _ );
rewrite [in LHS](proj1 (proj2_sig Sense01_F));
rewrite -[in LHS](proj1 (ConflMorphismIndexCommuteProp _ _ _));
rewrite -[in LHS](proj1 (proj2_sig Sense01_F));
congr ( _ o>Generator_ _ );
rewrite [in LHS](proj2_sig Sense1_ff); reflexivity).
Defined.

Definition Sense1_UnitViewedOb
U V (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F) :
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) (Sense01_ViewedOb Sense01_F vu).
Proof.
intros. eapply Sense1_Compos; last exact (Sense1_UnitViewing Sense1_ff).
clear Sense1_ff. unshelve eexists.
- intros H h. exact
{|  getProjectVertexOfViewed := ConflVertex vu (getIndexerOfViewing h);
    getProjectOfViewed := ConflProject vu (getIndexerOfViewing h);
    getDataOfViewed :=  ConflProject vu (getIndexerOfViewing h)
                   o>Generator_[sval (Sense01_Viewing Sense01_F vu)] h
|}.
- abstract (move; simpl; intros H H' h' f;
move: (ConflProp_ComposIndex vu (getIndexerOfViewing f) h' ) =>
[CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| exact HeqProject
| ];
do 2 rewrite [in LHS](proj1 (proj2_sig (Sense01_Viewing Sense01_F vu)));
do 2 rewrite [in RHS](proj1 (proj2_sig (Sense01_Viewing Sense01_F vu)));
congr (_ o>Generator_ _);
rewrite -[in RHS]HeqProject;
rewrite -[in LHS]polyGenerator_morphism;
rewrite -[in RHS]polyGenerator_morphism;
congr (CommonConfl1 o>Generator _);
rewrite ConflCommuteProp; reflexivity).
Defined.

Definition lemma0_Sense1_Viewing_Refining :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall W (wv : 'Generator( W ~> V)),
Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_Viewing Sense01_F (wv o>Generator vu)).
Proof.
intros. unshelve eexists. 
- intros G f. exact
{|  getIndexerOfViewing := (getIndexerOfViewing f) o>Generator vu ;
    getDataOfViewing := (ConflDiagonal _ _ _)
                       o>Generator_[sval Sense01_F] (getDataOfViewing f) 
|}.
- abstract (move; simpl; intros G G' g f;
move: (ConflProp_AssocIndex_Diagonal wv (getIndexerOfViewing f) vu g ) =>
  [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| assumption
| ];
do 2 rewrite [in LHS](proj1 (proj2_sig Sense01_F));
do 2 rewrite [in RHS](proj1 (proj2_sig Sense01_F));
congr ( _ o>Generator_ _ ); exact HeqIndex).
Defined.

Definition lemma2_Viewing_Refining :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall W (wv : 'Generator( W ~> V)),
{ lem: forall G (g_f : (Sense00_Viewing Sense01_F (wv o>Generator vu)) G ),
        (Sense00_Viewing Sense01_F wv) (ConflVertex vu (getIndexerOfViewing g_f)) |
  forall G H (hg : 'Generator( H ~> G )) (g_f : (Sense00_Viewing Sense01_F (wv o>Generator vu)) G ),
  lem H (hg o>Generator_[sval (Sense01_Viewing Sense01_F (wv o>Generator vu))] g_f)
  = (ConflMorphismIndex vu (getIndexerOfViewing g_f) hg)
      o>Generator_[sval (Sense01_Viewing Sense01_F wv)] (lem G g_f) }.
Proof.
intros. unshelve eexists.
- intros. exact
{|  getIndexerOfViewing := ConflIndex vu (getIndexerOfViewing g_f);
    getDataOfViewing := (ConflComposProject _ _ _)
                        o>Generator_[sval Sense01_F] (getDataOfViewing g_f)
|}.
-  abstract (intros; simpl;
move: (ConflProp_ComposRelativeIndex_ComposProject vu wv (getIndexerOfViewing g_f) hg )
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| assumption
| ];
do 2 rewrite [in RHS](proj1 (proj2_sig ( Sense01_F)));
do 2 rewrite [in LHS](proj1 (proj2_sig ( Sense01_F)));
congr (_ o>Generator_ _); exact HeqIndex).
Defined.

Definition Sense1_Refining :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall W (wv : 'Generator( W ~> V(*nope, not pb*))),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
Sense1_def (Sense01_Viewing Sense01_F (wv o>Generator vu)) (Sense01_ViewedOb Sense01_E (wv o>Generator vu)).
Proof.
intros. unshelve eexists.
- intros G g_f.
pose lem1 : (Sense00_ViewedOb Sense01_E wv) (ConflVertex vu (getIndexerOfViewing g_f)) :=
(sval Sense1_ee (ConflVertex vu (getIndexerOfViewing g_f))
      (proj1_sig (lemma2_Viewing_Refining vu Sense01_F wv ) _ g_f)).
exact {|
  getProjectVertexOfViewed := getProjectVertexOfViewed lem1;
  getProjectOfViewed :=
    getProjectOfViewed lem1 o>Generator ConflProject vu (getIndexerOfViewing g_f);
  getDataOfViewed := (sval (lemma0_Sense1_Viewing_Refining vu _ wv ) _ (getDataOfViewed lem1))
|}.
- abstract (move; intros G H hg g_f;
rewrite [in RHS](proj2_sig (lemma2_Viewing_Refining _ _ _ ));
rewrite -[in RHS](proj2_sig Sense1_ee); simpl;
set getProjectOfViewed_ee := (getProjectOfViewed (sval Sense1_ee _ _));
move: @getProjectOfViewed_ee;
set getDataOfViewed_ee := (getDataOfViewed (sval Sense1_ee _ _));
move: @getDataOfViewed_ee;
set getProjectVertexOfViewed_ee := (getProjectVertexOfViewed (sval Sense1_ee _ _));
set getIndexerOfViewing_g_f := (getIndexerOfViewing g_f);
move =>  getDataOfViewed_ee getProjectOfViewed_ee;

move: (@ConflProp_MixIndexProject_1 _ _ vu _ getIndexerOfViewing_g_f _ hg _ getProjectOfViewed_ee)
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact CommonConfl1
| exact CommonConfl2
| exact HeqProject
| ];
do 1 rewrite [in LHS](proj1 (proj2_sig ( (Sense01_Viewing Sense01_E (wv o>Generator vu) )))) ;
rewrite HeqIndex;
do 1 rewrite -[in LHS](proj1 (proj2_sig ( (Sense01_Viewing Sense01_E (wv o>Generator vu) )))) ;
congr ( _ o>Generator_ _);

move: (ConflProp_AssocIndex_Diagonal wv 
(getIndexerOfViewing getDataOfViewed_ee) vu ((ConflIndex getProjectOfViewed_ee
(ConflMorphismIndex vu getIndexerOfViewing_g_f hg)))) =>
  [CommonConflVertex' [CommonConfl1' [CommonConfl2' [HeqProject' HeqIndex']]]];
    unshelve eapply Sense00_Viewing_quotient; simpl;
    [ | exact CommonConfl1'
    | exact CommonConfl2'
    | assumption
    | ];
do 2 rewrite [in LHS](proj1 (proj2_sig Sense01_E));
do 2 rewrite [in RHS](proj1 (proj2_sig Sense01_E));
congr ( _ o>Generator_ _ );
exact HeqIndex').
Defined.

Definition Sense1_ViewedMor :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F),
Sense1_def (Sense01_ViewedOb Sense01_E vu)
(Sense01_ViewedOb Sense01_F vu).
Proof.
intros. unshelve eexists.
- intros G e_. exact
{|
getProjectVertexOfViewed := getProjectVertexOfViewed e_;
getProjectOfViewed := getProjectOfViewed e_;
getDataOfViewed :=
sval (Sense1_Viewing vu Sense1_ff) (getProjectVertexOfViewed e_) (getDataOfViewed e_);
|}.
- abstract (move; intros; unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact: unitGenerator
| exact: unitGenerator
| reflexivity
| ];
congr (_ o>Generator_ _ );
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ]; 
rewrite (proj2_sig Sense1_ff); reflexivity).
Defined.

Definition Sense1_Unit:
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
Sense1_def Sense01_F Sense01_F.
Proof.
intros. exists (fun G => id).
abstract (intros; move; intros; reflexivity).
Defined.

Definition Morphism_Compos_morCode_Family :
forall U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
  Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D),
Morphism_prop Sense01_F (fun (G : obGenerator)  (form : Sense00_F G) =>
                            Sense1_Compos Sense1_dd (Sense1_ee__ G form)).
Proof.
intros. move; simpl; intros.
congr (sval Sense1_dd _ _ ). exact: Sense1_ee_morphism.
Qed.

Inductive morCode :
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E) ,
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
Sense1_def Sense01_E Sense01_F -> Type :=

| AtMember :
forall U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee : morCode_Family Sense1_ee_morphism),
forall (G : obGenerator)  (form : Sense00_F G),

morCode (Sense1_ee__ G form)

| Compos_morCode :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F')
(Sense1_ff' : Sense1_def Sense01_F' Sense01_F), morCode Sense1_ff' ->
forall (Sense00_F'' : obGenerator -> Type) (Sense01_F'' : Sense01_def Sense00_F'')
(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F' ),

morCode Sense1_ff_ -> morCode ( Sense1_Compos Sense1_ff' Sense1_ff_ )

| Unit_morCode :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),

morCode ( Sense1_Unit Sense01_F )

| Destructing_morCode :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__),
forall (Code_ee__ : morCode_Family Sense1_ee_morphism),

morCode (Sense1_Destructing Sense1_ee_morphism)

| Refining_morCode :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall W (wv : 'Generator( W ~> V )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee : morCode Sense1_ee),

morCode (Sense1_Refining vu Sense1_ee)

| UnitViewedOb_morCode :
forall U V (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Code_ff : morCode Sense1_ff),

morCode ( Sense1_UnitViewedOb Sense1_ff )

| ViewedMor_morCode :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),

morCode (Sense1_ViewedMor vu Sense1_ff )

with morCode_Family :
forall U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__), Type :=

| Constructing_morCode_Family :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),

morCode_Family (@Morphism_Constructing _ _ vu _ Sense01_F )

| Compos_morCode_Family :
forall U V (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd),
morCode_Family Sense1_ee_morphism ->

morCode_Family (Morphism_Compos_morCode_Family Sense1_ee_morphism Sense1_dd).

Inductive obCoMod : forall Sense00_F (Sense01_F : Sense01_def Sense00_F), Type :=

| Viewing :
forall Sense00_F Sense01_F (F: @obData Sense00_F Sense01_F)
U V (vu : 'Generator( V ~> U )),

@obCoMod (Sense00_Viewing Sense01_F vu) (Sense01_Viewing Sense01_F vu)

| ViewedOb :
forall Sense00_F (Sense01_F : Sense01_def Sense00_F) (F: @obCoMod Sense00_F Sense01_F)
U V (vu : 'Generator( V ~> U )),

@obCoMod (Sense00_ViewedOb Sense01_F vu) (Sense01_ViewedOb Sense01_F vu)

with obData : forall Sense00_F (Sense01_F : Sense01_def Sense00_F), Type :=

| ViewOb : forall G : obGenerator, @obData (Sense00_ViewOb G) (Sense01_ViewOb G).

Inductive elConstruct :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F), forall (G : obGenerator) (form : Sense00_F G), Type :=

| ViewOb_elConstruct : 
forall G : obGenerator, forall (G' : obGenerator) (g : 'Generator( G' ~> G )) ,

elConstruct (ViewOb G) g

(* with elConstruct_OneRecursiveArg _ : forall _, Type := *)

with elAlgebra :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F), forall (G : obGenerator) (form : Sense00_F G), Type :=

| ElConstruct_elAlgebra :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (G : obGenerator)  (form : Sense00_F G),
forall (cons_form : elConstruct F form),

elAlgebra F form

(* ELIMINATE, NOT in solution | Restrict_elAlgebra : *)
| Restrict_elAlgebra:
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form),
forall (G' : obGenerator) (g' : 'Generator( G' ~> G )),

elAlgebra F (g' o>Generator_[sval Sense01_F ] form )
(* | Zero : ... 
   | Plus : ... *)  .

Module Inversion_elConstruct_obDataViewOb.
Inductive elConstruct GFixed : forall (G : obGenerator)
(form: Sense00_ViewOb GFixed G)
(cons_form: elConstruct (ViewOb GFixed) form), Type :=
| ViewOb_elConstruct :
forall (G' : obGenerator) (g : 'Generator( G' ~> GFixed )) ,
elConstruct (ViewOb_elConstruct g).
End Inversion_elConstruct_obDataViewOb.

Lemma elConstruct_obDataViewObP (GFixed : obGenerator) : forall (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) ,
forall (G : obGenerator)  (form : Sense00_F G) (cons_form: elConstruct F form),
ltac:(destruct F as [ GF];
            [ destruct (eq_comparable GFixed GF);
              [ refine (Inversion_elConstruct_obDataViewOb.elConstruct cons_form)
              | refine True
              ]
            ]).
Proof.
intros. destruct cons_form.
- intros eq. destruct eq as [Heq |].
+ apply: Inversion_elConstruct_obDataViewOb.ViewOb_elConstruct.
+ apply I.
Defined.

Inductive Solution_elConstruct : Type :=
with Solution_elAlgebra : Type :=
(* ELIMINATE
| Restrict_elAlgebra : *).

Section ElCongr_def.

Variables (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F)
(G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form )
(form' : Sense00_F G) (cons_form' : elAlgebra F form' ).

Definition ElCongr_def : Type := form' = form.

End ElCongr_def.

Lemma ElCongr_Trans_convElAlgebra :
forall (Sense00_F : obGenerator -> Type) ,
forall (G : obGenerator) (form : Sense00_F G) ,
forall (form' : Sense00_F G),
ElCongr_def form form' ->
forall (form'' : Sense00_F G) ,
ElCongr_def form' form'' ->
ElCongr_def form form''.
Proof.
etransitivity; eassumption.
Qed.

Lemma ElCongr_Restrict_Restrict:
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(G : obGenerator) (form : Sense00_F G)
(G' : obGenerator) (g' : 'Generator( G' ~> G )) (G'0 : obGenerator)
(g'0 : 'Generator( G'0 ~> G' )),
ElCongr_def (g'0 o>Generator_[sval Sense01_F] (g' o>Generator_[sval Sense01_F] form))
((g'0 o>Generator g') o>Generator_[sval Sense01_F] form).
Proof.
intros. move. rewrite (proj1 (proj2_sig Sense01_F)). reflexivity.
Qed.

Lemma ElCongr_Restrict_ViewOb:
forall (G G' : obGenerator) (g : 'Generator( G' ~> G ))
(G'0 : obGenerator) (g'0 : 'Generator( G'0 ~> G' )),
ElCongr_def (g'0 o>Generator_[sval (Sense01_ViewOb G)] g) (g'0 o>Generator g).
Proof.
reflexivity.
Qed.

Reserved Notation "cons_f0  [ Congr_f_f0 ]<==  cons_f" (at level 10 ,  Congr_f_f0, cons_f at level 40).

Inductive convElAlgebra :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F) ,
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
forall (form' : Sense00_F G) (cons_form' : elAlgebra F form' ), ElCongr_def form form' -> Type :=

| Trans_convElAlgebra :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F) ,
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
forall (form' : Sense00_F G) (cons_form' : elAlgebra F form' ),
forall (Congr_form_form' : ElCongr_def form form' ),
cons_form'  [Congr_form_form' ]<== cons_form ->
forall (form'' : Sense00_F G) (cons_form'' : elAlgebra F form'' ),
forall (Congr_form'_form'' : ElCongr_def form' form'' ),
cons_form''  [Congr_form'_form'']<== cons_form' ->
cons_form''
[ElCongr_Trans_convElAlgebra Congr_form_form' Congr_form'_form'']<==
cons_form

| Restrict_Restrict:
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F) ,
forall (G : obGenerator)  (form : Sense00_F G),
forall (cons_form : elAlgebra F form),
forall (G' : obGenerator) (g' : 'Generator( G' ~> G )),
forall (G'0 : obGenerator) (g'0 : 'Generator( G'0 ~> G' )),

(Restrict_elAlgebra cons_form (g'0 o>Generator g'))
[ElCongr_Restrict_Restrict Sense01_F form g' g'0]<==
(Restrict_elAlgebra (Restrict_elAlgebra cons_form g') g'0)

| Restrict_ViewOb:
forall (G : obGenerator), forall (G' : obGenerator) (g : 'Generator( G' ~> G )),
forall (G'0 : obGenerator) (g'0 : 'Generator( G'0 ~> G' )),

(ElConstruct_elAlgebra (ViewOb_elConstruct (g'0 o>Generator g)))
[ElCongr_Restrict_ViewOb g g'0]<==
(Restrict_elAlgebra (ElConstruct_elAlgebra (ViewOb_elConstruct g)) g'0)

where "cons_f0  [ Congr_f_f0 ]<==  cons_f" := (@convElAlgebra _ _ _ _ _ cons_f _ cons_f0 Congr_f_f0 ).

Section Congr_def.
Variables (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff)
(Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff').

Definition Congr_def : Type :=
forall (G' : obGenerator), forall form'  form'0 ,
forall Heq : form'0 =  form',
(sval Sense1_ff' G' form'0) =  (sval Sense1_ff G' form').

End Congr_def.

Lemma Congr_Trans:
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Sense1_ff' : Sense1_def Sense01_E Sense01_F),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff' ),
forall (Sense1_ff'' : Sense1_def Sense01_E Sense01_F ),
forall (Congr_congr_ff' : Congr_def Sense1_ff' Sense1_ff''),
Congr_def Sense1_ff Sense1_ff''.
Proof.
intros. move; intros. subst.
etransitivity. apply: Congr_congr_ff'. reflexivity.
apply: Congr_congr_ff. reflexivity.
Qed.

Definition Congr_Constructing_comp_Destructing :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__),
forall (G : obGenerator) (form : Sense00_F G) ,
Congr_def (Sense1_Compos (Sense1_Destructing Sense1_ee_morphism)
(Sense1_Constructing_default vu Sense01_F form))
(Sense1_UnitViewedOb (Sense1_ee__ G form)).
Proof.
intros. move. intros H h h0 Heq; subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| subst; reflexivity
|
].
congr ( _ o>Generator_ _). subst.
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ].
congr ( _ o>Generator_ _).
do 1 rewrite [in LHS](proj1 (proj2_sig Sense01_E)).
rewrite -(proj1 (ConflMorphismIndexCommuteProp _ _ _)).
do 1 rewrite -[in LHS](proj1 (proj2_sig Sense01_E)).
congr ( _ o>Generator_ _).
etransitivity; first last.
apply Sense1_ee_morphism. reflexivity. simpl.
rewrite (proj2_sig (Sense1_ee__ _ _)). reflexivity.
Qed.

Definition Congr_UnitViewedOb_cong
U V (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Congr_ff: Congr_def Sense1_ff Sense1_ff0) :
Congr_def (Sense1_UnitViewedOb Sense1_ff) (Sense1_UnitViewedOb Sense1_ff0).
Proof.
intros. move. intros. subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| subst; reflexivity
|
].
congr(_ o>Generator_ _). congr(_ o>Generator_ _).
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ].
congr(_ o>Generator_ _). congr(_ o>Generator_ _). 
apply: Congr_ff. reflexivity.
Qed.

Definition Congr_Constructing_comp_Refining :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(W : obGenerator) (wv : 'Generator( W ~> V ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv)
(Sense01_ViewedOb Sense01_E wv))
(G : obGenerator) (form : Sense00_F G),
Congr_def (Sense1_Compos (Sense1_Refining vu Sense1_ee)
    (Sense1_Constructing_default (wv o>Generator vu) Sense01_F form))
(Sense1_Refining vu
  (Sense1_Compos Sense1_ee (Sense1_Constructing_default wv Sense01_F form))).
Proof.
intros. move. intros H h h0 Heq. subst. simpl.
rewrite (proj1 (proj2_sig Sense01_F)).
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| reflexivity
].
Qed.

Definition Congr_Refining_comp_ViewedMor:
forall (U V : obGenerator) (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E) (W : obGenerator)
(wv : 'Generator( W ~> V ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(Sense1_dd : Sense1_def Sense01_E Sense01_D),
Congr_def (Sense1_Compos (Sense1_ViewedMor (wv o>Generator vu) Sense1_dd) (Sense1_Refining vu Sense1_ee))
(Sense1_Refining vu (Sense1_Compos (Sense1_ViewedMor wv Sense1_dd) Sense1_ee)).
Proof.
intros. move. intros H h h0 Heq. subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ].
congr(_ o>Generator_ _).
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ].
congr(_ o>Generator_ _). rewrite (proj2_sig Sense1_dd). reflexivity.
Qed.

Lemma Congr_Constructing_cong:
forall (U V : obGenerator) (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (G : obGenerator)
(form : Sense00_F G)  (form' : Sense00_F G)
(ElCong_form_form' : ElCongr_def form form'),

Congr_def (Sense1_Constructing_default vu Sense01_F form)
(Sense1_Constructing_default vu Sense01_F form').
Proof.
intros. move; intros. subst. rewrite ElCong_form_form'.
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| reflexivity ].
Qed.

Lemma congr_Compos_cong :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F')
(Sense1_ff' : Sense1_def Sense01_F' Sense01_F) (Sense00_F'' : obGenerator -> Type)
(Sense01_F'' : Sense01_def Sense00_F'')
(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F')
(Sense1_ee' : Sense1_def Sense01_F' Sense01_F )
(Congr_congr_ff' : Congr_def Sense1_ff' Sense1_ee' ),
forall (Sense1_ee_ : Sense1_def Sense01_F'' Sense01_F' )
(Congr_congr_ff_ : Congr_def Sense1_ff_ Sense1_ee_ ),
Congr_def (Sense1_Compos Sense1_ff' Sense1_ff_) (Sense1_Compos Sense1_ee' Sense1_ee_).
Proof.
intros; move; intros; simpl.
apply: ( Congr_congr_ff').  apply: ( Congr_congr_ff_). assumption.
Qed.

Lemma Congr_Refl : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F),
Congr_def Sense1_ff Sense1_ff.
Proof.
intros. move; intros. subst; reflexivity.
Qed.

Definition Congr_AtMember_Compos_morCode_Family :
forall (U V: obGenerator)
(vu: 'Generator( V ~> U ))
(Sense00_F: obGenerator -> Type)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense00_D: obGenerator -> Type)
(Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D)
(G: obGenerator)
(form: Sense00_F G),
Congr_def (Sense1_Compos Sense1_dd (Sense1_ee__ G form))
(Sense1_Compos Sense1_dd (Sense1_ee__ G form)).
Proof.
intros. move; intros; subst; reflexivity.
Qed.

Definition Congr_Destructing_comp_ViewedMor :
forall (U V: obGenerator) (vu: 'Generator( V ~> U ))
(Sense00_F: obGenerator -> Type) (Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type) (Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
  Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Sense00_D: obGenerator -> Type) (Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D),
  Congr_def (Sense1_Compos (Sense1_ViewedMor vu Sense1_dd) (Sense1_Destructing Sense1_ee_morphism))
(Sense1_Destructing (Morphism_Compos_morCode_Family Sense1_ee_morphism Sense1_dd)).
Proof.
intros. move; simpl; intros; subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
|  exact unitGenerator
|  reflexivity
| ].
congr(_ o>Generator_ _).
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| ].
congr(_ o>Generator_ _). rewrite (proj2_sig Sense1_dd). reflexivity.
Qed.

Lemma Congr_Refining_cong :
forall (U V: obGenerator)
(vu: 'Generator( V ~> U ))
(Sense00_F: obGenerator -> Type)
(Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(W: obGenerator)
(wv: 'Generator( W ~> V ))
(Sense1_ee Sense1_dd: Sense1_def (Sense01_Viewing Sense01_F wv)
            (Sense01_ViewedOb Sense01_E wv))
(Congr_congr_eedd : Congr_def Sense1_ee Sense1_dd),
(Congr_def (Sense1_Refining vu Sense1_ee)
        (Sense1_Refining vu Sense1_dd)).
Proof.
intros. move. intros; subst; simpl.
set sval_Sense1_dd_ := (sval Sense1_dd _ _).
set sval_Sense1_ee_ := (sval Sense1_ee _ _).
have -> : sval_Sense1_dd_ = sval_Sense1_ee_ by
 apply: Congr_congr_eedd.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| reflexivity ].
Qed.

Lemma Congr_Rev : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff'),
Congr_def Sense1_ff' Sense1_ff.
Proof.
  intros; move; intros; subst;  symmetry;  apply: Congr_congr_ff; reflexivity.
Qed.

Definition Congr_Constructing_comp_Constructing :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
 (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
 (G : obGenerator) (form : Sense00_F G) (H : obGenerator) (h : Sense00_ViewOb G H),
Congr_def (Sense1_Compos (Sense1_Constructing_default vu Sense01_F form)
  (Sense1_Constructing_default vu (Sense01_ViewOb G) h))
(Sense1_Constructing_default vu Sense01_F (h o>Generator_[sval Sense01_F] form)).
Proof.
intros. move; intros;  subst;  simpl.
unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| rewrite -(proj1 (proj2_sig Sense01_F)); reflexivity ].
Qed.

Reserved Notation "''CoMod$' (  Code_ff  ~>  Code_ff'  @_ Congr_congr_ff  )" (at level 0).
Inductive congrMorCode : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff'),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff'), Type :=

| Trans_congrMorCode : 
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff'),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff')
(congr_ff : 'CoMod$( Code_ff ~> Code_ff' @_ Congr_congr_ff )),
forall (Sense1_ff'' : Sense1_def Sense01_E Sense01_F )
(Code_ff'' : morCode Sense1_ff''),
forall (Congr_congr_ff' : Congr_def Sense1_ff' Sense1_ff'' )
(congr_ff' : 'CoMod$( Code_ff' ~> Code_ff'' @_ Congr_congr_ff' )),

'CoMod$( Code_ff ~> Code_ff'' @_ Congr_Trans Congr_congr_ff Congr_congr_ff'  )

| Refl_congrMorCode : 
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),

'CoMod$( Code_ff ~> Code_ff @_ Congr_Refl Sense1_ff )

| Rev_congrMorCode : 
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff'),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff')
(congr_ff : 'CoMod$( Code_ff ~> Code_ff' @_ Congr_congr_ff )),

'CoMod$( Code_ff' ~> Code_ff @_ Congr_Rev Congr_congr_ff )

| Constructing_comp_Destructing_congrMorCode :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism),
forall (G : obGenerator) (form : Sense00_F G) ,

'CoMod$( Compos_morCode (Destructing_morCode Code_ee__)
    (AtMember (Constructing_morCode_Family vu Sense01_F)  form) ~>
  (UnitViewedOb_morCode (AtMember Code_ee__ form)) @_
    Congr_Constructing_comp_Destructing Sense1_ee_morphism form )

| UnitViewedOb_cong_congrMorCode :
forall U V (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Code_ff : morCode Sense1_ff)
(Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Code_ff0 : morCode Sense1_ff0)
(Congr_ff: Congr_def Sense1_ff Sense1_ff0)
(congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_ff )),

'CoMod$( UnitViewedOb_morCode Code_ff ~>
  UnitViewedOb_morCode Code_ff0 @_
  Congr_UnitViewedOb_cong Congr_ff )

| Constructing_comp_Refining_congrMorCode :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(W : obGenerator) (wv : 'Generator( W ~> V ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv)
                      (Sense01_ViewedOb Sense01_E wv))
(Code_ee : morCode Sense1_ee) (G : obGenerator) (form : Sense00_F G),

'CoMod$ (Compos_morCode (Refining_morCode vu Code_ee)
  (AtMember (Constructing_morCode_Family (wv o>Generator vu) Sense01_F) form) ~>
  Refining_morCode vu (Compos_morCode Code_ee
  (AtMember (Constructing_morCode_Family wv Sense01_F) form))
  @_ (Congr_Constructing_comp_Refining Sense1_ee form))

| Refining_comp_ViewedMor_congrMorCode:
forall (U V : obGenerator) (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E) (W : obGenerator) (wv : 'Generator( W ~> V ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv)
                  (Sense01_ViewedOb Sense01_E wv)) ,
forall (Code_ee : morCode Sense1_ee),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(Sense1_dd : Sense1_def Sense01_E Sense01_D) (Code_dd : morCode Sense1_dd),

'CoMod$( Compos_morCode (ViewedMor_morCode (wv o>Generator vu) Code_dd) (Refining_morCode vu Code_ee) ~>
  Refining_morCode vu (Compos_morCode (ViewedMor_morCode wv Code_dd) Code_ee)
  @_ Congr_Refining_comp_ViewedMor Sense1_ee Sense1_dd )

| Constructing_cong_congrMorCode :
forall (U V : obGenerator) (vu : 'Generator( V ~> U )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (G : obGenerator)
(form : Sense00_F G)  (form' : Sense00_F G)
(ElCong_form_form' : ElCongr_def form form'),

'CoMod$( AtMember (Constructing_morCode_Family vu Sense01_F) form ~>
      AtMember (Constructing_morCode_Family vu Sense01_F) form' @_
      (Congr_Constructing_cong Sense01_F ElCong_form_form' ))

| Compos_cong_congrMorCode :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F')
(Sense1_ff' : Sense1_def Sense01_F' Sense01_F) (Code_ff' : morCode Sense1_ff')
(Sense00_F'' : obGenerator -> Type) (Sense01_F'' : Sense01_def Sense00_F'')
(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F' ) (Code_ff_ : morCode Sense1_ff_)
(Sense1_ee' : Sense1_def Sense01_F' Sense01_F ) (Code_ee' : morCode Sense1_ee')
(Congr_congr_ff' : Congr_def Sense1_ff' Sense1_ee' ),
'CoMod$( Code_ff' ~> Code_ee' @_ Congr_congr_ff' ) ->
forall (Sense1_ee_ : Sense1_def Sense01_F'' Sense01_F' ) (Code_ee_ : morCode Sense1_ee_)
(Congr_congr_ff_ : Congr_def Sense1_ff_ Sense1_ee_ ),
'CoMod$( Code_ff_ ~> Code_ee_ @_ Congr_congr_ff_ ) ->

'CoMod$( Compos_morCode Code_ff' Code_ff_ ~> Compos_morCode Code_ee'  Code_ee_ @_
                  congr_Compos_cong Congr_congr_ff' Congr_congr_ff_ )

| AtMember_Compos_morCode_Family_congrMorCode :
forall (U V: obGenerator) (vu: 'Generator( V ~> U ))
(Sense00_F: obGenerator -> Type) (Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type) (Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
  Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__: morCode_Family Sense1_ee_morphism)
(Sense00_D: obGenerator -> Type) (Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D)
(Code_dd: morCode Sense1_dd) (G: obGenerator) (form: Sense00_F G),

'CoMod$( AtMember (Compos_morCode_Family Code_dd Code_ee__) form ~>
  Compos_morCode Code_dd (AtMember Code_ee__ form) @_
  (Congr_AtMember_Compos_morCode_Family Sense1_ee__ Sense1_dd form ))

| Destructing_comp_ViewedMor_congrMorCode :
forall (U V: obGenerator) (vu: 'Generator( V ~> U ))
(Sense00_F: obGenerator -> Type) (Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type) (Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
  Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__: morCode_Family Sense1_ee_morphism)
(Sense00_D: obGenerator -> Type) (Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D) (Code_dd: morCode Sense1_dd),

'CoMod$( Compos_morCode (ViewedMor_morCode vu Code_dd) (Destructing_morCode Code_ee__) ~>
  Destructing_morCode (Compos_morCode_Family Code_dd Code_ee__) @_
  Congr_Destructing_comp_ViewedMor Sense1_ee_morphism Sense1_dd )

| Refining_cong_congrMorCode :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E)
(W : obGenerator) (wv : 'Generator( W ~> V ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv)
        (Sense01_ViewedOb Sense01_E wv))
(Code_ee : morCode Sense1_ee)
(Sense1_dd : Sense1_def (Sense01_Viewing Sense01_F wv)
        (Sense01_ViewedOb Sense01_E wv))
(Code_dd : morCode Sense1_dd)
(Congr_congr_eedd : Congr_def Sense1_ee Sense1_dd)
(congr_eedd : 'CoMod$( Code_ee ~> Code_dd @_ Congr_congr_eedd )),

'CoMod$( Refining_morCode vu Code_ee ~>
Refining_morCode vu Code_dd @_ Congr_Refining_cong Congr_congr_eedd)

| Constructing_comp_Constructing_congrMorCode :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) (G : obGenerator) (form : Sense00_F G)
(cons_form : elAlgebra F form) (H : obGenerator)
(h : Sense00_ViewOb G H) (cons_h : elAlgebra (ViewOb G) h),

'CoMod$( Compos_morCode (AtMember (Constructing_morCode_Family vu Sense01_F) form)
    (AtMember (Constructing_morCode_Family vu (Sense01_ViewOb G)) h) ~>
 AtMember (Constructing_morCode_Family vu Sense01_F)
    (h o>Generator_ form) @_ Congr_Constructing_comp_Constructing Sense01_F form h  )

where "''CoMod$' (  Code_ff  ~>  Code_ff'  @_ Congr_congr_ff  )" :=
(@congrMorCode _ _ _ _ _ Code_ff _ Code_ff' Congr_congr_ff) : poly_scope.

Notation "congr_ff_ o>$ congr_ff'" := 
  (@Trans_congrMorCode _ _ _ _ _ _ _ _ _ congr_ff_ _ _ _ congr_ff')
  (at level 40 , congr_ff' at next level , left associativity) : poly_scope.
Arguments Refl_congrMorCode {_ _ _ _ _ _}.

Reserved Notation "''CoMod' (  E  ~>  F  @_ Code_ff  )" (at level 0).

Inductive morCoMod : 
forall Sense00_E Sense01_E (E : @obCoMod Sense00_E Sense01_E ),
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F ),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F) (Code_ff : morCode Sense1_ff ), Type :=

| Compos : 
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F ),
forall Sense00_F' Sense01_F' (F' : @obCoMod Sense00_F' Sense01_F' ) 
Sense1_ff' (Code_ff' : morCode Sense1_ff')
(ff' : 'CoMod( F' ~> F @_ Code_ff' )),
forall Sense00_F'' Sense01_F'' (F'' : @obCoMod Sense00_F'' Sense01_F''),
forall Sense1_ff_ (Code_ff_ : morCode Sense1_ff_) (ff_ : 'CoMod( F'' ~> F' @_ Code_ff_ )),

'CoMod( F'' ~> F @_ (Compos_morCode Code_ff'  Code_ff_))

| Unit :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : @obCoMod Sense00_F Sense01_F ),

'CoMod( F ~> F @_ (Unit_morCode Sense01_F))

| Constructing :
forall U V (vu : 'Generator( V ~> U )), forall (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),

'CoMod( Viewing (ViewOb G) vu ~> Viewing F vu
  @_ (AtMember (Constructing_morCode_Family vu Sense01_F) form))

| Destructing :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator)
          (form : Sense00_F G) (cons_form : elConstruct F form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Code_ee0__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form),
morCode (Sense1_ee0__ G form cons_form))
(ee__ : forall (G : obGenerator)
  (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod( Viewing (ViewOb G) vu ~> E @_ (Code_ee0__ G form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator)
              (form : Sense00_F G) (cons_form : elConstruct F form),
Congr_def ((Sense1_ee__ G form)) (Sense1_ee0__ G form cons_form))
(congr_ee__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod$( (AtMember Code_ee__ form) ~> (Code_ee0__ G form cons_form)
                          @_ Congr_congr_ee__ G form cons_form )),

'CoMod( Viewing F vu ~> ViewedOb E vu @_ (Destructing_morCode Code_ee__))

| Refining :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall W (wv : 'Generator( W ~> V )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) 
    (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F wv) 
    (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F wv ~> ViewedOb E wv @_ Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

'CoMod( Viewing F (wv o>Generator vu) ~> ViewedOb E (wv o>Generator vu) 
    @_ (Refining_morCode vu Code_ee))

| UnitViewedOb :
forall U V (vu : 'Generator( V ~> U )),
forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
(F: @obCoMod Sense00_F Sense01_F) (G : obGenerator)
(Sense1_ff : Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu)  Sense01_F)
(Code_ff : morCode Sense1_ff) (ff : 'CoMod(  Viewing (ViewOb G) vu ~> F @_ Code_ff )),

'CoMod( Viewing (ViewOb G) vu ~> ViewedOb F vu @_ UnitViewedOb_morCode Code_ff )

| ViewedMor :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obCoMod Sense00_F Sense01_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff) (ff : 'CoMod( E ~> F @_ Code_ff )),

'CoMod( ViewedOb E vu ~> ViewedOb F vu @_ ViewedMor_morCode vu Code_ff  )

where "''CoMod' ( E ~> F @_ Code_ff )" := (@morCoMod _ _ E _ _ F _ Code_ff) : poly_scope.

Notation "ff_ o>CoMod ff'" := (@Compos _ _ _ _ _ _ _ _ ff' _ _ _ _ _ ff_ )
(at level 40, left associativity) : poly_scope.

Reserved Notation "ff0  [  congr_ff  ]<~~  ff" (at level 10 ,  congr_ff , ff at level 40).

Inductive convCoMod :
forall Sense00_E Sense01_E (E : @obCoMod Sense00_E Sense01_E ),
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F ),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff ) (ff : 'CoMod( E ~> F @_ Code_ff )),
forall (Sense1_ff0 : Sense1_def Sense01_E Sense01_F)
(Code_ff0 : morCode Sense1_ff0 ) (ff0 : 'CoMod( E ~> F @_ Code_ff0 )),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff0)
(congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_congr_ff )), Prop :=

| Constructing_comp_Destructing :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Code_ee0__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
morCode (Sense1_ee0__ G form cons_form))
(ee__ : forall (G : obGenerator)
(form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod( Viewing (ViewOb G) vu ~> E @_ (Code_ee0__ G form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator)
            (form : Sense00_F G) (cons_form : elConstruct F form),
Congr_def ((Sense1_ee__ G form)) (Sense1_ee0__ G form cons_form))
(congr_ee__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod$( (AtMember Code_ee__ form) ~> (Code_ee0__ G form cons_form)
                          @_ Congr_congr_ee__ G form cons_form )),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),

(UnitViewedOb ( ee__ G form cons_form ))

  [ (Constructing_comp_Destructing_congrMorCode Code_ee__ form)
    o>$ (UnitViewedOb_cong_congrMorCode (congr_ee__ G form cons_form)) ]<~~

((Constructing vu (ElConstruct_elAlgebra cons_form))
  o>CoMod ( Destructing ee__ congr_ee__ ))

| Destructing_comp_ViewedMor :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator)
                (form : Sense00_F G) (cons_form : elConstruct F form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Code_ee0__ : forall (G : obGenerator)
              (form : Sense00_F G) (cons_form : elConstruct F form),
morCode (Sense1_ee0__ G form cons_form))
(ee__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod( Viewing (ViewOb G) vu ~> E @_ (Code_ee0__ G form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator)
          (form : Sense00_F G) (cons_form : elConstruct F form),
Congr_def ((Sense1_ee__ G form)) (Sense1_ee0__ G form cons_form))
(congr_ee__ : forall (G : obGenerator)
    (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod$( (AtMember Code_ee__ form) ~> (Code_ee0__ G form cons_form)
                        @_ Congr_congr_ee__ G form cons_form )),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(D: @obCoMod Sense00_D Sense01_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd)
(dd : 'CoMod( E ~> D @_ Code_dd )),

(Destructing (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form) =>
        ((ee__ G form cons_form) o>CoMod dd))
    (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form) =>
        (AtMember_Compos_morCode_Family_congrMorCode Code_ee__ Code_dd form) 
        o>$ Compos_cong_congrMorCode (Refl_congrMorCode) (congr_ee__ G form cons_form)))

  [ Destructing_comp_ViewedMor_congrMorCode Code_ee__ Code_dd ]<~~

(( Destructing ee__ congr_ee__ ) o>CoMod ( ViewedMor vu dd ))
(*MEMO: The type of this term is a product while it is expected to be (morCode_Family ?Sense1_ee_morphism). *)

| Constructing_comp_Refining :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
  (F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
  (E: @obCoMod Sense00_E Sense01_E),
forall W (wv : 'Generator( W ~> V )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F wv ~> ViewedOb E wv @_ Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),

(Refining vu ((Constructing wv cons_form) o>CoMod ee )
  (Compos_cong_congrMorCode congr_ee (Refl_congrMorCode)))

  [ Constructing_comp_Refining_congrMorCode vu Code_ee form ]<~~

(( Constructing (wv o>Generator vu) cons_form ) o>CoMod ( Refining vu ee congr_ee))

| Refining_comp_ViewedMor :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall W (wv : 'Generator( W ~> V )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F wv ~> ViewedOb E wv @_ Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(D: @obCoMod Sense00_D Sense01_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd)
(dd : 'CoMod( E ~> D @_ Code_dd )),

(Refining vu ( ee o>CoMod ( ViewedMor wv dd ))
(Compos_cong_congrMorCode (Refl_congrMorCode) congr_ee ))

[ Refining_comp_ViewedMor_congrMorCode vu Code_ee Code_dd ]<~~

(( Refining vu ee congr_ee ) o>CoMod ( ViewedMor (wv o>Generator vu) dd ))

| Constructing_comp_Constructing :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
forall (H : obGenerator) (h : (Sense00_ViewOb G) H) (cons_h : elAlgebra (ViewOb G) h),

(Constructing vu (Restrict_elAlgebra cons_form h))

  [ Constructing_comp_Constructing_congrMorCode vu cons_form cons_h ]<~~

(( Constructing vu cons_h ) o>CoMod ( Constructing vu cons_form ))

| Compos_cong : 
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F ),
forall Sense00_F' Sense01_F' (F' : @obCoMod Sense00_F' Sense01_F' ) Sense1_ff'
(Code_ff' : morCode Sense1_ff') (ff' : 'CoMod( F' ~> F @_ Code_ff' )),

forall Sense00_F'' Sense01_F'' (F'' : @obCoMod Sense00_F'' Sense01_F''),
forall Sense1_ff_ (Code_ff_ : morCode Sense1_ff_) (ff_ : 'CoMod( F'' ~> F' @_ Code_ff_ )),

forall Sense1_ee' (Code_ee' : morCode Sense1_ee') (ee' : 'CoMod( F' ~> F @_Code_ee' )),
forall Congr_congr_ff' (congr_ff' : 'CoMod$( Code_ff' ~> Code_ee' @_ Congr_congr_ff' )),
ee' [ congr_ff' ]<~~ ff' ->

forall Sense1_ee_ (Code_ee_ : morCode Sense1_ee_) (ee_ : 'CoMod( F'' ~> F' @_ Code_ee_ )),
forall Congr_congr_ff_ (congr_ff_ : 'CoMod$( Code_ff_ ~> Code_ee_ @_ Congr_congr_ff_ )),
ee_ [ congr_ff_ ]<~~ ff_ ->

( ee_ o>CoMod ee' )

  [ Compos_cong_congrMorCode congr_ff'  congr_ff_ ]<~~

( ff_ o>CoMod ff' )

| Constructing_cong :
forall U V (vu : 'Generator( V ~> U )), forall (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
forall (form' : Sense00_F G) (cons_form' : elAlgebra F form' )
(ElCong_form_form': ElCongr_def form form') ,
( cons_form'  [ ElCong_form_form' ]<==  cons_form )  ->

( Constructing vu cons_form' )

  [ Constructing_cong_congrMorCode vu Sense01_F ElCong_form_form' ]<~~

( Constructing vu cons_form )

| Destructing_cong :
(*SIMPLE CONGRUENCE, possible is congruence
with different Code_dd__ and manual coherence conversions in 'CoMod$ *)
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Code_ee0__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
morCode (Sense1_ee0__ G form cons_form))
(ee__ : forall (G : obGenerator)
(form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod( Viewing (ViewOb G) vu ~> E @_ (Code_ee0__ G form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator)
            (form : Sense00_F G) (cons_form : elConstruct F form),
Congr_def ((Sense1_ee__ G form)) (Sense1_ee0__ G form cons_form))
(congr_ee__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod$( (AtMember Code_ee__ form) ~> (Code_ee0__ G form cons_form)
                          @_ Congr_congr_ee__ G form cons_form )),
forall (Sense1_dd__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E
    := Sense1_ee__)
(Sense1_dd_morphism : Morphism_prop Sense01_F Sense1_dd__
    := Sense1_ee_morphism)
(Code_dd__ : morCode_Family Sense1_dd_morphism
    := Code_ee__)

(Sense1_dd0__ : forall (G : obGenerator)
        (form : Sense00_F G) (cons_form : elConstruct F form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_E)
(Code_dd0__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
morCode (Sense1_dd0__ G form cons_form))
(dd__ : forall (G : obGenerator)
(form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod( Viewing (ViewOb G) vu ~> E @_ (Code_dd0__ G form cons_form))),

forall (Congr_congr_dd__ : forall (G : obGenerator)
            (form : Sense00_F G) (cons_form : elConstruct F form),
Congr_def ((Sense1_dd__ G form)) (Sense1_dd0__ G form cons_form))
(congr_dd__ : forall (G : obGenerator)
      (form : Sense00_F G) (cons_form : elConstruct F form),
'CoMod$( (AtMember Code_dd__ form) ~> (Code_dd0__ G form cons_form)
                          @_ Congr_congr_dd__ G form cons_form )),

forall (Congr_congr_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
Congr_def (Sense1_ee0__ G form cons_form) (Sense1_dd0__ G form cons_form))
(congr_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
'CoMod$( (Code_ee0__ G form cons_form) ~> 
  (Code_dd0__ G form cons_form) @_ (Congr_congr_eedd0__ G form cons_form))),

forall (conv_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
  (dd__ G form cons_form) [ (congr_eedd0__ G form cons_form) ]<~~ (ee__ G form cons_form)),

( Destructing dd__ (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form )
                => (congr_ee__ G form cons_form) o>$ (congr_eedd0__ G form cons_form)))

[ Refl_congrMorCode (*SIMPLE CONGRUENCE *) ]<~~

 ( Destructing ee__ congr_ee__ )

| Refining_cong :
forall U V (vu : 'Generator( V ~> U )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall W (wv : 'Generator( W ~> V )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F wv ~> ViewedOb E wv @_ Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (Sense1_dd : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_dd : morCode Sense1_dd),
forall (Sense1_dd0 : Sense1_def (Sense01_Viewing Sense01_F wv) (Sense01_ViewedOb Sense01_E wv)),
forall (Code_dd0 : morCode Sense1_dd0),
forall (dd: 'CoMod( Viewing F wv ~> ViewedOb E wv @_ Code_dd0 )),
forall (Congr_congr_dd : Congr_def Sense1_dd Sense1_dd0)
(congr_dd : 'CoMod$( Code_dd ~> Code_dd0 @_ Congr_congr_dd )),

forall (Congr_congr_eedd0 : Congr_def Sense1_ee0 Sense1_dd0)
(congr_eedd0 : 'CoMod$( Code_ee0 ~> Code_dd0 @_ Congr_congr_eedd0 )),

forall (conv_eedd0 : dd [ congr_eedd0 ]<~~ ee),

( Refining vu dd congr_dd )

  [ Refining_cong_congrMorCode vu (congr_ee o>$ congr_eedd0 o>$ (Rev_congrMorCode congr_dd))  ]<~~

( Refining vu ee congr_ee )

| UnitViewedOb_cong :
forall U V (vu : 'Generator( V ~> U )),
forall Sense00_F (Sense01_F : Sense01_def Sense00_F) (F: @obCoMod Sense00_F Sense01_F) (G : obGenerator)
(Sense1_ff : Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu)  Sense01_F)
(Code_ff : morCode Sense1_ff) (ff : 'CoMod(  Viewing (ViewOb G) vu ~> F @_ Code_ff )),
forall (Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) vu) Sense01_F)
(Code_ff0 : morCode Sense1_ff0)
(ff0 : 'CoMod(  Viewing (ViewOb G) vu ~> F @_ Code_ff0 ))
(Congr_ff: Congr_def Sense1_ff Sense1_ff0)
(congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_ff )),
  ff0 [ congr_ff ]<~~ ff ->

(  UnitViewedOb ff0 )

  [ UnitViewedOb_cong_congrMorCode congr_ff ]<~~

( UnitViewedOb ff )

| convCoMod_Trans :
forall Sense00_E Sense01_E (E : @obCoMod Sense00_E Sense01_E),
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F),
forall Sense1_ff (Code_ff : morCode Sense1_ff) (ff : 'CoMod( E ~> F @_ Code_ff )),
forall Sense1_ff0 (Code_ff0 : morCode Sense1_ff0) (ff0 : 'CoMod( E ~> F @_ Code_ff0 )),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff0 )
(congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_congr_ff )),
ff0 [ congr_ff ]<~~ ff ->
forall Sense1_ff0' (Code_ff0' : morCode Sense1_ff0') (ff0' : 'CoMod( E ~> F @_ Code_ff0' )),
forall (Congr_congr_ff0 : Congr_def Sense1_ff0 Sense1_ff0')
(congr_ff0 : 'CoMod$( Code_ff0 ~> Code_ff0' @_ Congr_congr_ff0 )),
ff0' [ congr_ff0 ]<~~ ff0 ->

ff0' [ congr_ff o>$ congr_ff0 ]<~~ ff

| convCoMod_Refl : 
forall Sense00_E Sense01_E (E : @obCoMod Sense00_E Sense01_E),
forall Sense00_F Sense01_F (F : @obCoMod Sense00_F Sense01_F),
forall Sense1_ff (Code_ff : morCode Sense1_ff) (ff : 'CoMod( E ~> F @_ Code_ff )),

ff [ Refl_congrMorCode ]<~~ ff

where "ff0 [  congr_ff  ]<~~ ff" := (@convCoMod _ _ _ _ _ _ _ _ ff _ _ ff0 _ congr_ff).
(* forall (YKK2 : Congr_def _ _) (KK2 : 'CoMod$( _ ~> _ @_ YKK2 )),    *)

Global Hint Constructors convCoMod : core.

End COMOD.
(** # #
#+END_SRC

* Example

#+BEGIN_SRC coq :exports both :results silent # # **)
Module NatGenerator <: GENERATOR.

Definition obGenerator : eqType := nat_eqType.
Definition morGenerator : obGenerator -> obGenerator -> Type.
Proof.
  intros n m. exact (n <= m).
Defined.
Notation "''Generator' ( V ~> U )" := (@morGenerator V U)
(at level 0, format "''Generator' (  V  ~>  U  )") : poly_scope.
Definition polyGenerator :
forall U V, 'Generator( V ~> U ) -> forall W, 'Generator( W ~> V ) -> 'Generator( W ~> U ).
Proof.
  intros U V a W vu. eapply (leq_trans); eassumption.
Defined.

Notation "wv o>Generator vu" := (@polyGenerator _ _ vu _ wv)
(at level 40, vu at next level) : poly_scope.

Definition unitGenerator : forall {U : obGenerator}, 'Generator( U ~> U ) := leqnn.

Definition polyGenerator_morphism :
forall (U V : obGenerator) (vu : 'Generator( V ~> U ))
        (W : obGenerator) (wv : 'Generator( W ~> V )),
forall X (xw : 'Generator( X ~> W )),
  xw o>Generator ( wv o>Generator vu ) = ( xw o>Generator wv ) o>Generator vu.
Proof.
  intros. apply: bool_irrelevance.
Qed.

Parameter polyGenerator_unitGenerator :
forall (U V : obGenerator) (vu : 'Generator( V ~> U )),
  vu = ((@unitGenerator V) o>Generator vu ).
Parameter unitGenerator_polyGenerator :
forall (U : obGenerator), forall (W : obGenerator) (wv : 'Generator( W ~> U )),
    wv = ( wv o>Generator (@unitGenerator U)).

(* CONSTRUCTIVE CONFLUENCE: 2 kinds of arrows.
  FIRST KIND OF ARROWS: these arrows below are required to be computational; 
    and in fact these arrows will appear by-definition
      during the inductive construction of the confluence *)
Definition ConflVertex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )), obGenerator.
intros. exact (minn ProjecterVertex IndexerVertex).
Defined.
Definition ConflProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  'Generator( ConflVertex projecter indexer ~> IndexerVertex ).
intros. exact: geq_minr.
Defined.
Definition ConflIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  'Generator( ConflVertex projecter indexer ~> ProjecterVertex ).
intros. exact: geq_minl.
Defined.
Definition ConflCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  ConflProject projecter indexer o>Generator indexer
  = ConflIndex projecter indexer o>Generator projecter.
intros. apply: bool_irrelevance.
Qed.

Definition ConflMorphismIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  'Generator( ConflVertex projecter (preIndexer o>Generator indexer) ~>
                      ConflVertex projecter indexer ).
Proof.
unfold morGenerator. intros. rewrite leq_min. rewrite geq_minl.  simpl.
unfold ConflVertex. eapply leq_trans. exact: geq_minr. assumption.
Defined.
Parameter ConflMorphismProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
  'Generator( ConflVertex (preProjecter o>Generator projecter) indexer ~>
                          ConflVertex projecter indexer ).
Parameter ConflComposProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
  'Generator( (ConflVertex preProjecter (ConflIndex projecter indexer))
                    ~> (ConflVertex (preProjecter o>Generator projecter) indexer )).
Parameter ConflDiagonal :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
  'Generator( (ConflVertex (projecter o>Generator diagonal) (indexer o>Generator diagonal) )
                        ~>  (ConflVertex projecter indexer) ).

Parameter ConflMorphismIndexCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
ConflProject projecter (preIndexer o>Generator indexer) o>Generator preIndexer
= ConflMorphismIndex projecter indexer preIndexer o>Generator ConflProject projecter indexer
/\  ConflIndex projecter (preIndexer o>Generator indexer)
    = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer.
Parameter ConflMorphismProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
ConflIndex (preProjecter o>Generator projecter) indexer o>Generator preProjecter
= ConflMorphismProject projecter indexer preProjecter o>Generator ConflIndex projecter indexer
/\  ConflProject (preProjecter o>Generator projecter) indexer
    = ConflMorphismProject projecter indexer preProjecter o>Generator ConflProject projecter indexer.
Parameter ConflMorphismIndexProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
ConflMorphismIndex (preProjecter o>Generator projecter) indexer preIndexer
o>Generator ConflMorphismProject projecter indexer preProjecter 
= ConflMorphismProject projecter (preIndexer o>Generator indexer) preProjecter
o>Generator ConflMorphismIndex projecter indexer preIndexer.
Parameter ConflComposProjectCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
(ConflComposProject projecter indexer preProjecter) o>Generator (ConflIndex (preProjecter o>Generator projecter) indexer) 
  = (ConflIndex preProjecter (ConflIndex projecter indexer))
  /\  (ConflComposProject projecter indexer preProjecter) o>Generator (ConflMorphismProject projecter indexer preProjecter)
      = ConflProject preProjecter (ConflIndex projecter indexer) .
Parameter ConflDiagonalCommuteProp :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
(ConflDiagonal projecter indexer diagonal) o>Generator (ConflIndex projecter indexer)
= (ConflIndex (projecter o>Generator diagonal) (indexer o>Generator diagonal) )
  /\  (ConflDiagonal projecter indexer diagonal) o>Generator (ConflProject projecter indexer) 
      = (ConflProject (projecter o>Generator diagonal) (indexer o>Generator diagonal) ) .

(* CONFLUENCE PROPERTIES:
  SECOND KIND OF ARROWS: these arrows below are NOT required to be computational; 
    and these arrows are mere derivable logical properties of the confluence 
      which are proved after the definition of confluence *)
Parameter ConflProp_ComposIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex (ConflProject projecter indexer) preIndexer )) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter (preIndexer o>Generator indexer ))) |
  CommonConfl1 o>Generator (ConflProject (ConflProject projecter indexer) preIndexer )
  = CommonConfl2 o>Generator (ConflProject projecter (preIndexer o>Generator indexer ))
  /\  CommonConfl1 o>Generator ((ConflIndex (ConflProject projecter indexer) preIndexer ))
      = CommonConfl2 o>Generator (ConflMorphismIndex projecter indexer preIndexer )
} } }.

Parameter ConflProp_AssocIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PrePreIndexerVertex (prePreIndexer : 'Generator( PrePreIndexerVertex ~> PreIndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~>
 (ConflVertex projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~>
 (ConflVertex projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))) |
  CommonConfl1 o>Generator (ConflProject projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)))
  = CommonConfl2 o>Generator (ConflProject projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))
  /\  CommonConfl1 o>Generator ((ConflMorphismIndex projecter (preIndexer o>Generator indexer) prePreIndexer)
                                  o>Generator (ConflMorphismIndex projecter indexer preIndexer))
      = CommonConfl2 o>Generator (ConflMorphismIndex projecter indexer (prePreIndexer o>Generator preIndexer))
} } }.

Parameter ConflProp_MorphismIndexRelativeProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                            (ConflMorphismIndex projecter (indexer) preIndexer
                            o>Generator (ConflProject projecter (indexer)
                                          o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                                (ConflProject projecter (preIndexer o>Generator indexer)
                                o>Generator (preIndexer o>Generator indexer))) |
CommonConfl1 o>Generator ConflProject projecter (ConflMorphismIndex projecter (indexer) preIndexer
o>Generator (ConflProject projecter (indexer) o>Generator indexer))
= CommonConfl2 o>Generator ConflProject projecter
(ConflProject projecter (preIndexer o>Generator indexer) o>Generator (preIndexer o>Generator indexer))
/\  CommonConfl1 o>Generator (ConflMorphismIndex projecter (ConflProject projecter (indexer) o>Generator indexer)
(ConflMorphismIndex projecter (indexer) preIndexer)
  o>Generator ConflMorphismIndex projecter (indexer) (ConflProject projecter (indexer)))
= CommonConfl2 o>Generator (ConflMorphismIndex projecter (preIndexer o>Generator indexer)
                              (ConflProject projecter (preIndexer o>Generator indexer))
        o>Generator ConflMorphismIndex projecter (indexer) preIndexer)
} } }.

Parameter ConflProp_ComposRelativeIndex :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
                         ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
                 (ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer)) |
CommonConfl1 o>Generator ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
= CommonConfl2 o>Generator ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer
                                                          o>Generator ConflIndex projecter indexer)
/\  CommonConfl1 o>Generator (ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
o>Generator ConflMorphismIndex projecter indexer preIndexer)
= CommonConfl2 o>Generator (ConflMorphismIndex preProjecter (ConflIndex projecter indexer)
  (ConflMorphismIndex projecter indexer preIndexer)
o>Generator ConflProject preProjecter (ConflIndex projecter indexer))
} } }.

Parameter ConflProp_MixIndexProject_1 :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ConflVertex projecter indexer )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~>
 ConflVertex (preProjecter o>Generator ConflProject projecter indexer) preIndexer ) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~>
 ConflVertex preProjecter (ConflMorphismIndex projecter indexer preIndexer)) |
  CommonConfl1 o>Generator ConflProject (preProjecter o>Generator ConflProject projecter indexer) preIndexer
  = CommonConfl2 o>Generator (ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer)
                                          o>Generator ConflProject projecter (preIndexer o>Generator indexer))
  /\  CommonConfl1 o>Generator (ConflIndex (preProjecter o>Generator ConflProject projecter indexer) preIndexer)
      = CommonConfl2 o>Generator (ConflIndex preProjecter (ConflMorphismIndex projecter indexer preIndexer))
} } }.

Parameter ConflProp_ComposRelativeIndex_ComposProject :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall PreProjecterVertex (preProjecter : 'Generator( PreProjecterVertex ~> ProjecterVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
                    ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
            (ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer)) |
CommonConfl1 o>Generator ConflProject preProjecter (ConflIndex projecter (preIndexer o>Generator indexer))
= CommonConfl2 o>Generator ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer
                                                          o>Generator ConflIndex projecter indexer)
/\  (CommonConfl1 o>Generator ConflComposProject projecter (preIndexer o>Generator indexer) preProjecter)
    o>Generator ConflMorphismIndex (preProjecter o>Generator projecter) (indexer) preIndexer
= (CommonConfl2 o>Generator ConflMorphismIndex preProjecter (ConflIndex projecter (indexer))
              (ConflMorphismIndex projecter (indexer) preIndexer))
      o>Generator ConflComposProject projecter (indexer) preProjecter
} } }.

Parameter ConflProp_AssocIndex_Diagonal :
forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )),
forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
forall DiagonalVertex (diagonal : 'Generator( BaseVertex ~> DiagonalVertex )),
forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
{ CommonConflVertex : obGenerator &
{ CommonConfl1 : 'Generator( CommonConflVertex ~> 
ConflVertex (projecter o>Generator diagonal) (preIndexer o>Generator (indexer o>Generator diagonal))) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> 
ConflVertex (projecter o>Generator diagonal) ((preIndexer o>Generator indexer) o>Generator diagonal)) |
CommonConfl1 o>Generator ConflProject (projecter o>Generator diagonal)
              (preIndexer o>Generator (indexer o>Generator diagonal)) =
CommonConfl2 o>Generator ConflProject (projecter o>Generator diagonal)
              ((preIndexer o>Generator indexer) o>Generator diagonal)
/\ (CommonConfl1 o>Generator ConflMorphismIndex (projecter o>Generator diagonal)
                (indexer o>Generator diagonal) preIndexer)
      o>Generator ConflDiagonal projecter (indexer) diagonal
 = (CommonConfl2 o>Generator ConflDiagonal projecter (preIndexer o>Generator indexer) diagonal)
        o>Generator ConflMorphismIndex projecter (indexer) preIndexer
} } }.
End NatGenerator.

Import NatGenerator.
Declare Module Import CoMod : (COMOD NatGenerator).

Parameter (GFixed : obGenerator).

Record example_morphism_return : Type :=
{ ex_U : nat ;
  ex_Z : nat ;
  ex_zu : ex_Z <= ex_U ;
  ex_Sense1_ff : Sense1_def _ _ ;
  ex_Code_ff : morCode ex_Sense1_ff ;
  ex_morCoMod : 'CoMod( Viewing (ViewOb GFixed) ex_zu ~>
        ViewedOb (Viewing (ViewOb GFixed) (eq_refl _ : 0 <= 0)) ex_zu @_ ex_Code_ff ) }.

Definition example_morphism : example_morphism_return.
Proof.
repeat eexists.
eapply Refining with (vu := (eq_refl _ : 2 <= 3)) (2 := Refl_congrMorCode).
eapply Refining with (vu := (eq_refl _ : 1 <= 2)) (2 := Refl_congrMorCode).
eapply Refining with (vu := (eq_refl _ : 0 <= 1)) (2 := Refl_congrMorCode).
eapply Destructing with (vu := (eq_refl _ : 0 <= 0)).
intros. eapply Compos.
- apply Constructing, ElConstruct_elAlgebra, (ViewOb_elConstruct unitGenerator).
- move: (elConstruct_obDataViewObP GFixed cons_form).
elim (eq_comparable GFixed GFixed) => [ /=  ?  cons_form_P | // ].
destruct cons_form_P.
apply Constructing, ElConstruct_elAlgebra, (ViewOb_elConstruct g).

Unshelve. all: intros; try apply Congr_AtMember_Compos_morCode_Family;
try apply AtMember_Compos_morCode_Family_congrMorCode.
Defined.

Definition example_reduction:
{ Sense1_ff : Sense1_def _ _ &
{ Code_ff : morCode Sense1_ff &
{ ff : 'CoMod( _ ~> _ @_ Code_ff ) &
{ Congr_congr_ff : Congr_def _ _ &
{ congr_ff : 'CoMod$( _ ~> _ @_ Congr_congr_ff ) &
( ff )  [ congr_ff ]<~~
  ((Constructing (ex_zu example_morphism) (ElConstruct_elAlgebra (ViewOb_elConstruct unitGenerator)))
       o>CoMod (ex_morCoMod example_morphism)) }}}}}.
Proof.
repeat eexists. simpl.
eapply convCoMod_Trans.
eapply Constructing_comp_Refining.
eapply convCoMod_Trans.
eapply Refining_cong, Constructing_comp_Refining.
eapply convCoMod_Trans.
eapply Refining_cong, Refining_cong, Constructing_comp_Refining.
eapply convCoMod_Trans.
eapply Refining_cong, Refining_cong, Refining_cong, Constructing_comp_Destructing.
simpl. destruct (eq_comparable GFixed GFixed); last by []; simpl.
eapply convCoMod_Trans.
eapply Refining_cong, Refining_cong, Refining_cong, UnitViewedOb_cong, Constructing_comp_Constructing.
exact: convCoMod_Refl.
Unshelve. all: try apply Refl_congrMorCode.
Defined.
Eval simpl in (projT1 (projT2 (projT2 example_reduction))).
(*
= Refining (eqxx (2 - 3))
      (Refining (eqxx (1 - 2))
        (Refining (eqxx (0 - 1))
            (UnitViewedOb
              (Constructing (eqxx (0 - 0))
                  (Restrict_elAlgebra
                    (ElConstruct_elAlgebra
                        (ViewOb_elConstruct unitGenerator)) unitGenerator)))
            Refl_congrMorCode) Refl_congrMorCode) Refl_congrMorCode
  : 'CoMod ( Viewing (ViewOb GFixed) (ex_zu example_morphism) ~>
    ViewedOb (Viewing (ViewOb GFixed) (eqxx (0 - 0) : 0 <= 0))
      (ex_zu example_morphism) @_ projT1 (projT2 example_reduction) ) *)
End SHEAF.
(** # #
#+END_SRC

Voila.
# # **)