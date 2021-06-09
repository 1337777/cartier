(** # #
#+TITLE: cartierSolution0.v

Proph

https://gitlab.com/1337777/cartier/blob/master/cartierSolution0.v

shows the general outline of the solutions to some question of CARTIER which is how to program the MODOS proof-assistant for « dependent constructive computational logic for geometric dataobjects » (including homotopy types) ... 

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
Notation "''Generator' ( A' ~> A )" := (@morGenerator A' A)
  (at level 0, format "''Generator' (  A'  ~>  A  )") : poly_scope.

Parameter polyGenerator :
  forall A A', 'Generator( A' ~> A ) -> forall A'', 'Generator( A'' ~> A' ) -> 'Generator( A'' ~> A ).
Notation "a_ o>Generator a'" := (@polyGenerator _ _ a' _ a_)
  (at level 40, a' at next level) : poly_scope.

Parameter unitGenerator : forall {A : obGenerator}, 'Generator( A ~> A ).

Parameter polyGenerator_morphism :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )) 
          (A'' : obGenerator) (a_ : 'Generator( A'' ~> A' )),
  forall B (b : 'Generator( B ~> A'' )),
    b o>Generator ( a_ o>Generator a' ) = ( b o>Generator a_ ) o>Generator a'.
Parameter polyGenerator_unitGenerator :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )),
    a' = ( (@unitGenerator A') o>Generator a' ).
Parameter unitGenerator_polyGenerator :
  forall (A : obGenerator), forall (A'' : obGenerator) (a_ : 'Generator( A'' ~> A )),
      a_ = ( a_ o>Generator (@unitGenerator A) ).

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
Parameter ConflCommuteProp :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
    ConflProject projecter indexer o>Generator indexer
    = ConflIndex projecter indexer o>Generator projecter.

Parameter ConflMorphismIndex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
    'Generator( ConflVertex projecter (preIndexer o>Generator indexer) ~>
                            ConflVertex projecter indexer ).
Parameter ConflMorphismIndexCommuteProp :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  ConflProject projecter (preIndexer o>Generator indexer) o>Generator preIndexer
  = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflProject projecter indexer 
  /\  ConflIndex projecter (preIndexer o>Generator indexer)
      = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer.

Parameter ConflProp_ComposIndex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  { CommonConflVertex : obGenerator &
  { CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex (ConflProject projecter indexer) preIndexer ) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter (preIndexer o>Generator indexer ) )) |
    CommonConfl1 o>Generator (ConflProject (ConflProject projecter indexer) preIndexer ) 
    = CommonConfl2 o>Generator   (ConflProject projecter (preIndexer o>Generator indexer ))
    /\  CommonConfl1 o>Generator ((ConflIndex (ConflProject projecter indexer) preIndexer ) )
        = CommonConfl2 o>Generator   (ConflMorphismIndex projecter indexer preIndexer )
  } } }.

Parameter ConflProp_AssocIndex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  forall PrePreIndexerVertex (prePreIndexer : 'Generator( PrePreIndexerVertex ~> PreIndexerVertex )),
  { CommonConflVertex : obGenerator &
  { CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex projecter  (prePreIndexer o>Generator (preIndexer o>Generator indexer))) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer)) ) |
    CommonConfl1 o>Generator (ConflProject projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)) ) 
    = CommonConfl2 o>Generator   (ConflProject projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))
    /\  CommonConfl1 o>Generator ( (ConflMorphismIndex projecter (preIndexer o>Generator indexer) prePreIndexer)
                                    o>Generator (ConflMorphismIndex projecter indexer preIndexer) )
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
                                              o>Generator indexer)) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                                    (ConflProject projecter (preIndexer o>Generator indexer)
                                    o>Generator (preIndexer o>Generator indexer)) ) |
  CommonConfl1 o>Generator ConflProject projecter (ConflMorphismIndex projecter (indexer) preIndexer
    o>Generator (ConflProject projecter (indexer) o>Generator indexer))
  = CommonConfl2 o>Generator  ConflProject projecter
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
{ CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer)) ) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
                       (ConflMorphismIndex projecter indexer preIndexer
                        o>Generator ConflIndex projecter indexer) ) |
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
  { CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex (preProjecter o>Generator ConflProject projecter indexer) preIndexer  ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter (ConflMorphismIndex projecter indexer preIndexer)) |
    CommonConfl1 o>Generator ConflProject (preProjecter o>Generator ConflProject projecter indexer) preIndexer
    = CommonConfl2 o>Generator (ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer)
                                            o>Generator ConflProject projecter (preIndexer o>Generator indexer))
    /\  CommonConfl1 o>Generator (ConflIndex (preProjecter o>Generator ConflProject projecter indexer) preIndexer)
        = CommonConfl2 o>Generator (ConflIndex preProjecter (ConflMorphismIndex projecter indexer preIndexer) )
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
Proof. intros G. refine (fun H => 'Generator( H ~> G ) ). Defined.

Lemma Sense01_ViewOb : forall (G : obGenerator), Sense01_def (Sense00_ViewOb G).
Proof.
  intros. unshelve eexists.
  - intros H H' h. refine (fun g => h o>Generator g).
  - abstract (split; [intros; exact: polyGenerator_morphism
                      | intros; exact: polyGenerator_unitGenerator]).
Defined.

Record Sense00_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
        A A' (aa : 'Generator( A' ~> A )) (B: obGenerator) : Type :=
  { getIndexerOfViewing : 'Generator( B ~> A ) ;
    getDataOfViewing : Sense00_F (ConflVertex aa getIndexerOfViewing)
  }.

Axiom Sense00_Viewing_quotient :
 forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
    A A' (aa : 'Generator( A' ~> A )),
forall B : obGenerator, forall (f1 f2 : Sense00_Viewing Sense01_F aa B),
forall (CommonConflVertex : obGenerator)
(CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex aa (getIndexerOfViewing f1)) ))
(CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex aa (getIndexerOfViewing f2)) )), 
CommonConfl1 o>Generator (ConflProject aa (getIndexerOfViewing f1))
= CommonConfl2 o>Generator (ConflProject aa (getIndexerOfViewing f2)) -> 
CommonConfl1 o>Generator_[sval Sense01_F] (getDataOfViewing f1) 
= CommonConfl2 o>Generator_[sval Sense01_F] (getDataOfViewing f2)
-> f1 = f2.

Definition Sense01_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
            A A' (aa : 'Generator( A' ~> A ))
  :  Sense01_def (Sense00_Viewing Sense01_F aa ). 
Proof.
intros. unshelve eexists.
- intros G G' g f. exists ( g o>Generator (getIndexerOfViewing f)).
  exact: ( (ConflMorphismIndex aa (getIndexerOfViewing f) g)  o>Generator_[sval Sense01_F] (getDataOfViewing f)).
- abstract (split; simpl;
  [ intros G G' g G'' g' f;
  move: (ConflProp_AssocIndex aa (getIndexerOfViewing f) g g' ) =>
    [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]]; 
      unshelve eapply Sense00_Viewing_quotient; simpl;
      [
      | exact CommonConfl1
      | exact CommonConfl2
      | assumption
      |
      ]; 
      do 2 rewrite [LHS](proj1 (proj2_sig Sense01_F));
          rewrite [RHS](proj1 (proj2_sig Sense01_F));
          congr( _ o>Generator_ _);
          rewrite -polyGenerator_morphism;
          assumption
    | intros G f;
      unshelve eapply Sense00_Viewing_quotient; simpl;
      [
      | exact (ConflMorphismIndex aa (getIndexerOfViewing f) unitGenerator)
      | exact unitGenerator
      | rewrite -(proj1 (ConflMorphismIndexCommuteProp aa (getIndexerOfViewing f) unitGenerator));
        rewrite -[RHS]polyGenerator_unitGenerator -[LHS]unitGenerator_polyGenerator; reflexivity
      | rewrite [RHS](proj1 (proj2_sig Sense01_F));
        congr( _ o>Generator_ _);
        rewrite -[RHS]polyGenerator_unitGenerator; reflexivity
    ]]).
Defined.

Record Sense00_ViewedOb Sense00_F (Sense01_F : Sense01_def Sense00_F)
        A A' (aa : 'Generator( A' ~> A )) (B: obGenerator) : Type :=
  { getProjectVertexOfViewed : obGenerator ;
    getProjectOfViewed :  'Generator( getProjectVertexOfViewed ~> B ) ;
    getDataOfViewed : Sense00_F getProjectVertexOfViewed ;
    getConditionOfViewed : 'Generator( getProjectVertexOfViewed ~> A' ) 
  }.

Axiom Sense00_ViewedOb_quotient  : 
  forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
          A A' (aa : 'Generator( A' ~> A )) (B: obGenerator),
  forall (f1 f2 : Sense00_ViewedOb Sense01_F aa B),
  forall (CommonConflVertex : obGenerator)
          (CommonConfl1 : 'Generator( CommonConflVertex ~> getProjectVertexOfViewed f1 ))
          (CommonConfl2 : 'Generator( CommonConflVertex ~> getProjectVertexOfViewed f2 )), 
    CommonConfl1 o>Generator (getProjectOfViewed f1)
    = CommonConfl2 o>Generator (getProjectOfViewed f2) -> 
    CommonConfl1 o>Generator_[sval Sense01_F] (getDataOfViewed f1) 
    = CommonConfl2 o>Generator_[sval Sense01_F] (getDataOfViewed f2)
    -> f1 = f2.

Definition Sense01_ViewedOb Sense00_F (Sense01_F : Sense01_def Sense00_F)
            A  A' (aa : 'Generator( A' ~> A ))
  :  Sense01_def (Sense00_ViewedOb Sense01_F aa). 
Proof.
intros. unshelve eexists.
- intros G G' g f. exact
  {| getProjectVertexOfViewed :=(ConflVertex (getProjectOfViewed f) g) ;
    getProjectOfViewed := (ConflProject (getProjectOfViewed f) g) ;
    getDataOfViewed := ((ConflIndex (getProjectOfViewed f) g) o>Generator_[sval Sense01_F] (getDataOfViewed f)  ) ;
    getConditionOfViewed := ((ConflIndex (getProjectOfViewed f) g) o>Generator (getConditionOfViewed f)  ) 
  |}.
- abstract (split; simpl;
  [ intros G G' g G'' g' f;
  move: (ConflProp_ComposIndex (getProjectOfViewed f) g g' ) => 
  [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
  unshelve eapply Sense00_ViewedOb_quotient; simpl;
  [
  | exact CommonConfl1
  | exact CommonConfl2
  | assumption
  |
  ];
  do 2 rewrite [LHS](proj1 (proj2_sig Sense01_F));
  rewrite [RHS](proj1 (proj2_sig Sense01_F));
  congr( _ o>Generator_ _); rewrite HeqIndex; rewrite -polyGenerator_morphism;
  rewrite -(proj2 (ConflMorphismIndexCommuteProp _ _ _ )); reflexivity
  | intros G f;
    unshelve eapply Sense00_ViewedOb_quotient; simpl;
    [
    | exact (ConflIndex (getProjectOfViewed f) unitGenerator)
    | exact unitGenerator
    | rewrite -(ConflCommuteProp (getProjectOfViewed f) unitGenerator);
      rewrite -polyGenerator_unitGenerator -unitGenerator_polyGenerator; reflexivity
    | rewrite [RHS](proj1 (proj2_sig Sense01_F));
      congr( _ o>Generator_ _);
      rewrite -polyGenerator_unitGenerator; reflexivity
  ]]).
Defined.

Definition element_to_polyelement : forall Sense00_F (Sense01_F : Sense01_def Sense00_F) G,
    Sense00_F G -> Sense1_def  (Sense01_ViewOb G) Sense01_F.
Proof.
  intros ? ? G f. unshelve eexists. 
  apply: (fun G' g => g o>Generator_[sval Sense01_F] f). 
  abstract (move; simpl; intros G' G'' g' g;
            rewrite -(proj1 (proj2_sig Sense01_F)); reflexivity).
Defined.

Definition Sense1_Compos :
forall (Sense00_F : obGenerator -> Type)
  (Sense01_F : Sense01_def Sense00_F)
  (Sense00_F' : obGenerator -> Type)
  (Sense01_F' : Sense01_def Sense00_F')
  (Sense1_ff' : Sense1_def Sense01_F' Sense01_F)
  (Sense00_F'' : obGenerator -> Type)
  (Sense01_F'' : Sense01_def Sense00_F'')
  (Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F'),
  Sense1_def Sense01_F'' Sense01_F.
Proof.
intros. unshelve eexists.
- intros G dataIn. 
  apply:  (sval Sense1_ff' G  (sval Sense1_ff_ G dataIn)).
- abstract (move; simpl; intros; rewrite [LHS](proj2_sig Sense1_ff');
            rewrite (proj2_sig Sense1_ff_); reflexivity).
Defined.

Definition Sense1_Constructing_default : 
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F),

forall (G : obGenerator) (form : Sense00_F G), 
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) (Sense01_Viewing Sense01_F aa). 
Proof.
intros. unshelve eexists.
- intros H h. exact
  {|
getIndexerOfViewing := getIndexerOfViewing h;
    getDataOfViewing := getDataOfViewing h o>Generator_[sval Sense01_F] form
  |}.
- abstract (move; simpl; intros; unshelve eapply Sense00_Viewing_quotient; simpl;
  [
  | exact unitGenerator
  | exact unitGenerator
  | reflexivity
  | rewrite -(proj1 (proj2_sig  Sense01_F)); reflexivity 
  ]).
Defined.

Definition Sense1_ViewObMor :
forall (G : obGenerator) (H : obGenerator) (g : 'Generator( H ~> G )),
  Sense1_def (Sense01_ViewOb H) (Sense01_ViewOb G).
Proof.
intros G H hg. unshelve eexists.
- intros G0  h. exact: (  h o>Generator hg ).
- abstract (move; simpl; intros ; rewrite /Sense01_action /= ; exact: polyGenerator_morphism).
Defined.

Definition Sense1_Viewing Sense00_F (Sense01_F : Sense01_def Sense00_F)
  A A' (aa : 'Generator( A' ~> A ))
  Sense00_E (Sense01_E : Sense01_def Sense00_E)
  (Sense1_ff : Sense1_def Sense01_F Sense01_E)  :
Sense1_def (Sense01_Viewing Sense01_F aa) (Sense01_Viewing Sense01_E aa).
Proof.
intros. unshelve eexists.
- intros G f. exact
  {|
getIndexerOfViewing := getIndexerOfViewing f;
    getDataOfViewing :=
      sval Sense1_ff (ConflVertex aa (getIndexerOfViewing f))
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
A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
    Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E) :=
forall (G : obGenerator)  (form : Sense00_F G),
forall  (G' : obGenerator) (g : 'Generator( G' ~> G )) ,
forall (H : obGenerator) (f0 : (Sense00_Viewing (Sense01_ViewOb G') aa) H) f,
(*  pb (g'o>g) A' = A' = pb (g) A'  *)
f =  (sval (Sense1_Viewing aa (Sense1_ViewObMor g)) H f0) -> 
(sval (Sense1_ee__ G form) H f) =
(sval (Sense1_ee__ G' (g o>Generator_[sval Sense01_F] form)) H f0).

Lemma Morphism_Constructing
: forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
  Morphism_prop  Sense01_F (@Sense1_Constructing_default _ _ aa _ Sense01_F ).
Proof.         
intros; move; intros; subst; unshelve eapply Sense00_Viewing_quotient; simpl;
[ | exact unitGenerator 
  | exact unitGenerator 
  | reflexivity 
  | congr ( _ o>Generator_ _);
    rewrite (proj1 (projT2 Sense01_F)); reflexivity
].
Qed.

Definition Sense1_Destructing : 
forall A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee : forall (G : obGenerator) (form : Sense00_F G),
    Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee), 
Sense1_def (Sense01_Viewing Sense01_F aa ) (Sense01_ViewedOb Sense01_E aa).
Proof.
intros. unshelve eexists.
- intros G f. exact
{|
getProjectVertexOfViewed := ConflVertex aa (getIndexerOfViewing f);
getProjectOfViewed := ConflProject aa (getIndexerOfViewing f);
getDataOfViewed :=
  sval
    (Sense1_ee (ConflVertex aa (getIndexerOfViewing f))
                (getDataOfViewing f)) (ConflVertex aa (getIndexerOfViewing f))
    {|
      getIndexerOfViewing :=
        ConflProject aa (getIndexerOfViewing f)
                      o>Generator getIndexerOfViewing f;
      getDataOfViewing :=
        ConflMorphismIndex aa (getIndexerOfViewing f)
                            (ConflProject aa (getIndexerOfViewing f))
    |};
getConditionOfViewed := ConflIndex aa (getIndexerOfViewing f)
|}.
- abstract (move; simpl; intros G G' g' f;
move: (ConflProp_ComposIndex aa (getIndexerOfViewing f) g' ) 
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[
| exact CommonConfl1
| exact CommonConfl2
| assumption
|
];
do 1 rewrite [LHS](proj1 (proj2_sig Sense01_E));
rewrite HeqIndex;
do 1 rewrite -[LHS](proj1 (proj2_sig Sense01_E));
congr (_ o>Generator_ _);
do 1 rewrite [in LHS](proj2_sig (Sense1_ee _ _));
apply: Sense1_ee_morphism;
have Heq: (ConflMorphismIndex aa (getIndexerOfViewing f) g')
o>Generator (ConflProject aa (getIndexerOfViewing f))
= (ConflProject aa  (g' o>Generator getIndexerOfViewing f) o>Generator g');
first (by rewrite (proj1 (ConflMorphismIndexCommuteProp _ _ _ )); reflexivity);
move: (ConflProp_MorphismIndexRelativeProject aa (getIndexerOfViewing f) g') 
=> [CommonConflVertex' [CommonConfl1' [CommonConfl2' [HeqProject' HeqIndex']]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[
| exact CommonConfl1'
| exact CommonConfl2'
| assumption
| assumption
]).
Defined.

Definition Sense1_UnitViewedOb 
A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)
(* A' = pb aa G *)
(G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F) :
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) (Sense01_ViewedOb Sense01_F aa).
Proof.
intros; unshelve eexists.
- intros H h. exact
{|
getProjectVertexOfViewed := ConflVertex aa (getIndexerOfViewing h);
getProjectOfViewed := ConflProject aa (getIndexerOfViewing h);
getDataOfViewed :=
  ConflProject aa (getIndexerOfViewing h)
                o>Generator_[sval Sense01_F] sval Sense1_ff H h;
getConditionOfViewed := ConflIndex aa (getIndexerOfViewing h)
|}.
- abstract (move; simpl; intros H H' h' f;
move: (ConflProp_ComposIndex aa (getIndexerOfViewing f) h' ) => 
[CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[
| exact CommonConfl1
| exact CommonConfl2
| assumption
|
];
do 3 rewrite [in LHS](proj2_sig Sense1_ff);
do 2 rewrite [in RHS](proj2_sig Sense1_ff);
congr (sval Sense1_ff _ _);
do 2 rewrite [in RHS](proj1 (proj2_sig ( Sense01_Viewing (Sense01_ViewOb G) aa))) ;
do 2 rewrite [in LHS](proj1 (proj2_sig ( Sense01_Viewing (Sense01_ViewOb G) aa))) ;
congr ( _ o>Generator_ _);
rewrite -[in RHS]HeqProject;
rewrite -[in LHS]polyGenerator_morphism;
rewrite -[in RHS]polyGenerator_morphism;
congr (CommonConfl1 o>Generator _);
rewrite ConflCommuteProp; reflexivity).
Defined.

Definition lem_Viewing_Refinement :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall A'' (a''a' : 'Generator( A'' ~> A'(*nope, not pb*))),
{ lem:  forall G (g_f : (Sense00_Viewing Sense01_F a'a) G ),
(Sense00_Viewing Sense01_F a''a') (ConflVertex a'a  (getIndexerOfViewing g_f)) |
forall G H (hg : 'Generator( H ~> G )) (g_f : (Sense00_Viewing Sense01_F a'a) G ), 
lem H (hg o>Generator_[sval (Sense01_Viewing Sense01_F a'a)] g_f)  =
(ConflMorphismIndex a'a (getIndexerOfViewing g_f) hg) 
  o>Generator_[sval (Sense01_Viewing Sense01_F a''a')]
              lem G g_f }.
Proof.
intros. unshelve eexists. 
- intros.  exact
{|
  getIndexerOfViewing := ConflIndex a'a (getIndexerOfViewing g_f);
  getDataOfViewing :=
    ConflProject a''a'
                (ConflIndex a'a (getIndexerOfViewing g_f))
                o>Generator_[sval Sense01_F] getDataOfViewing g_f
|}.
- abstract (intros; simpl;
move: (ConflProp_ComposRelativeIndex a'a  a''a' (getIndexerOfViewing g_f) hg ) 
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_Viewing_quotient; simpl;
[
| exact CommonConfl1
| exact CommonConfl2
| assumption
|
];
do 2 rewrite [in RHS](proj1 (proj2_sig ( Sense01_F)));
do 2 rewrite [in LHS](proj1 (proj2_sig ( Sense01_F)));
congr (_ o>Generator_ _);
rewrite -[in LHS]polyGenerator_morphism;
rewrite -[in RHS]polyGenerator_morphism;
exact HeqIndex).
Defined.

Definition Sense1_Refinement :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall A'' (a''a' : 'Generator( A'' ~> A'(*nope, not pb*))),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
  Sense1_def (Sense01_Viewing Sense01_F a'a) (Sense01_ViewedOb Sense01_E a'a).
Proof. 
intros. unshelve eexists.
- intros G g_f. 
pose lem1 : (Sense00_ViewedOb Sense01_E a''a') (ConflVertex a'a (getIndexerOfViewing g_f)) :=
  (sval Sense1_ee (ConflVertex a'a (getIndexerOfViewing g_f))
        (proj1_sig (lem_Viewing_Refinement a'a Sense01_F a''a' ) _ g_f)).
exact {|
    getProjectVertexOfViewed := getProjectVertexOfViewed lem1;
    getProjectOfViewed :=
      getProjectOfViewed lem1
                          o>Generator ConflProject a'a (getIndexerOfViewing g_f);
    getDataOfViewed := getDataOfViewed lem1;
    getConditionOfViewed := getConditionOfViewed lem1 o>Generator a''a'
  |}.
- abstract (move; intros G H hg g_f;
rewrite [in RHS](proj2_sig (lem_Viewing_Refinement _ _ _  ));
rewrite -[in RHS](proj2_sig Sense1_ee);
simpl;
set getProjectOfViewed_ee := (getProjectOfViewed (sval Sense1_ee _ _));
move: @getProjectOfViewed_ee;
set getDataOfViewed_ee := (getDataOfViewed (sval Sense1_ee _ _));
move: @getDataOfViewed_ee;
set getConditionOfViewed_ee := (getConditionOfViewed (sval Sense1_ee _ _));
move: @getConditionOfViewed_ee;
set getProjectVertexOfViewed_ee := (getProjectVertexOfViewed (sval Sense1_ee _ _));
set getIndexerOfViewing_g_f := (getIndexerOfViewing g_f);
move => getConditionOfViewed_ee getDataOfViewed_ee getProjectOfViewed_ee;

move: (@ConflProp_MixIndexProject_1 _ _ a'a _ getIndexerOfViewing_g_f _ hg _ getProjectOfViewed_ee)
=> [CommonConflVertex [CommonConfl1 [CommonConfl2 [HeqProject HeqIndex]]]];
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[
| exact CommonConfl1
| exact CommonConfl2
| exact HeqProject
|
];
do 1 rewrite [in RHS](proj1 (proj2_sig ( Sense01_E))) ;
do 1 rewrite [in LHS](proj1 (proj2_sig ( Sense01_E))) ;
congr ( _ o>Generator_ _);
exact HeqIndex).
Defined.

Definition Sense1_ViewedMor :
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F),
Sense1_def (Sense01_ViewedOb Sense01_E a'a)
(Sense01_ViewedOb Sense01_F a'a).
Proof.
intros. unshelve eexists.
- intros G e_. exact 
{|
getProjectVertexOfViewed := getProjectVertexOfViewed e_;
getProjectOfViewed := getProjectOfViewed e_;
getDataOfViewed :=
sval Sense1_ff (getProjectVertexOfViewed e_) (getDataOfViewed e_);
getConditionOfViewed := getConditionOfViewed e_
|}. 
- abstract (move; intros; unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact: unitGenerator
| exact: unitGenerator
| reflexivity
|  ];
congr (_ o>Generator_ _ );
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
forall  A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
    Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D),

  Morphism_prop  Sense01_F (fun (G : obGenerator)  (form : Sense00_F G) =>
                              Sense1_Compos Sense1_dd (Sense1_ee__ G form) ).
Proof.
intros. move; simpl; intros. 
congr (sval Sense1_dd _ _  ). exact: Sense1_ee_morphism.
Qed.

Inductive morCode
: forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E) ,
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
Sense1_def Sense01_E Sense01_F -> Type :=

| AtMember :
forall  A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop Sense01_F Sense1_ee__)
(Code_ee : morCode_Family Sense1_ee_morphism),

forall (G : obGenerator)  (form : Sense00_F G),
morCode (Sense1_ee__ G form)

| Compos_morCode : 
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) 
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F') 
(Sense1_ff' : Sense1_def Sense01_F' Sense01_F),
morCode Sense1_ff' ->
forall (Sense00_F'' : obGenerator -> Type) (Sense01_F'' : Sense01_def Sense00_F'')
(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F' ),
morCode Sense1_ff_  -> morCode ( Sense1_Compos Sense1_ff' Sense1_ff_ )

| Unit_morCode : 
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
morCode ( Sense1_Unit Sense01_F )

| Destructing_morCode :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__),
forall (Code_ee__ : morCode_Family Sense1_ee_morphism),
morCode (Sense1_Destructing Sense1_ee_morphism)

| Refinement_morCode :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall A'' (a''a' : 'Generator( A'' ~> A' )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee : morCode Sense1_ee),
morCode (Sense1_Refinement a'a  Sense1_ee)

| UnitViewedOb_morCode : 
forall  A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)
(G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F)
(Code_ff : morCode Sense1_ff) ,
morCode ( Sense1_UnitViewedOb  Sense1_ff )

| ViewObMor_morCode : 
forall A A' (aa : 'Generator( A' ~> A )),
forall (G H : obGenerator) (g : 'Generator( G ~> H )),
morCode ( Sense1_Viewing aa (Sense1_ViewObMor g) )

| ViewedMor_morCode :
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
morCode (Sense1_ViewedMor a'a Sense1_ff )

with morCode_Family :
forall  A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__), Type :=

| Constructing_morCode_Family :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),

morCode_Family (@Morphism_Constructing _ _  aa _  Sense01_F   ) 

| Compos_morCode_Family :
forall  A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd),

morCode_Family Sense1_ee_morphism ->

morCode_Family  (Morphism_Compos_morCode_Family Sense1_ee_morphism Sense1_dd). 

Inductive obCoMod : forall Sense00_F (Sense01_F : Sense01_def Sense00_F), Type := 

| Viewing :
forall Sense00_F Sense01_F 
(F: @obData Sense00_F Sense01_F)
A A' (aa : 'Generator( A' ~> A )),
@obCoMod (Sense00_Viewing Sense01_F aa) (Sense01_Viewing Sense01_F aa)

| ViewedOb :
forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
(F: @obCoMod Sense00_F Sense01_F)
A A' (aa : 'Generator( A' ~> A )),
@obCoMod (Sense00_ViewedOb Sense01_F aa) (Sense01_ViewedOb Sense01_F aa)

with obData : forall Sense00_F (Sense01_F : Sense01_def Sense00_F), Type :=

(* | UnaryDataOb : obData Sense01_UnaryDataOb *)

| ViewOb : forall G : obGenerator, @obData (Sense00_ViewOb G) (Sense01_ViewOb G).

Inductive elConstruct  :
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) ,
forall (G : obGenerator)  (form : Sense00_F G), Type :=

| ViewOb_elConstruct : forall G : obGenerator, 
forall (G' : obGenerator) (g : 'Generator( G' ~> G )) ,
elConstruct (ViewOb G) g 

(* with elConstruct_OneRecursiveArg _ : forall _, Type := *)

with elAlgebra   :
forall (Sense00_F : obGenerator -> Type) 
  (Sense01_F : Sense01_def Sense00_F)
  (F : obData Sense01_F) ,
forall (G : obGenerator) (form : Sense00_F G), Type :=

| ElConstruct_elAlgebra :
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) ,

forall (G : obGenerator)  (form : Sense00_F G), 
forall (cons_form : elConstruct  F  form), 
elAlgebra  F  form

| Restrict_elAlgebra (*NOT in solution*):
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) ,

forall (G : obGenerator)  (form : Sense00_F G), 
forall (cons_form : elAlgebra  F form), 

forall (G' : obGenerator) (g' : 'Generator( G' ~> G )),
elAlgebra  F (g' o>Generator_[sval Sense01_F ] form )
(* | Zero : ... | Plus : ... *)  .

Module Inversion_elConstruct_obDataViewOb.
Inductive elConstruct GFixed : forall (G : obGenerator)
(form: Sense00_ViewOb GFixed G)
(cons_form: elConstruct (ViewOb GFixed) form), Type :=
| ViewOb_elConstruct :
forall (G' : obGenerator) (g : 'Generator( G' ~> GFixed )) ,
elConstruct (ViewOb_elConstruct g). 
End  Inversion_elConstruct_obDataViewOb.

Lemma elConstruct_obDataViewObP (GFixed : obGenerator) : forall  (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) ,
forall (G : obGenerator)  (form : Sense00_F G) (cons_form: elConstruct F form),
ltac:(destruct F as [ GF]; [
  destruct (eq_comparable GFixed GF); 
  [refine (Inversion_elConstruct_obDataViewOb.elConstruct cons_form)
| refine True]]).
Proof.
intros. destruct cons_form.
- intros eq. destruct eq as [Heq |].
  + apply:  Inversion_elConstruct_obDataViewOb.ViewOb_elConstruct.
  + apply I.
Defined.  

Inductive Solution_elConstruct : Type :=
with Solution_elAlgebra : Type :=
(* ELIMINATE
| Restrict_elAlgebra : *).

Section ElCongr_def.

Variables  (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F)
  (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F   form )
(form' : Sense00_F G) (cons_form' : elAlgebra F   form' ).

Definition ElCongr_def : Type := form' = form.

End ElCongr_def.

Lemma ElCongr_Trans_convElAlgebra :
forall (Sense00_F : obGenerator -> Type) ,
forall (G : obGenerator) (form : Sense00_F G) , 
forall  (form' : Sense00_F G),
ElCongr_def form form' ->
forall  (form'' : Sense00_F G) ,
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
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F   form ), 
forall  (form' : Sense00_F G) (cons_form' : elAlgebra F   form' ), ElCongr_def form form' -> Type :=

| Trans_convElAlgebra :
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F) ,
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F   form ), 
forall  (form' : Sense00_F G) (cons_form' : elAlgebra F   form' ),
forall (Congr_form_form' : ElCongr_def form form' ),
cons_form'  [Congr_form_form' ]<== cons_form ->
forall  (form'' : Sense00_F G) (cons_form'' : elAlgebra F   form'' ),
forall (Congr_form'_form'' : ElCongr_def form' form'' ),
cons_form''  [Congr_form'_form'']<== cons_form' ->
cons_form'' 
[ElCongr_Trans_convElAlgebra Congr_form_form' Congr_form'_form'']<== 
cons_form

| Restrict_Restrict (*NOT in solution*):
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) (F : obData Sense01_F) ,
forall (G : obGenerator)  (form : Sense00_F G), 
forall (cons_form : elAlgebra  F form), 
forall (G' : obGenerator) (g' : 'Generator( G' ~> G )),
forall (G'0 : obGenerator) (g'0 : 'Generator( G'0 ~> G' )),

(Restrict_elAlgebra cons_form (g'0 o>Generator g'))
[ElCongr_Restrict_Restrict Sense01_F form g' g'0]<==
(Restrict_elAlgebra (Restrict_elAlgebra cons_form g') g'0)

| Restrict_ViewOb (*NOT in solution*):
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
forall Heq :  form'0 =  form',
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

Definition  Congr_Constructing_comp_Destructing :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)

(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__),

forall (G : obGenerator) (form : Sense00_F G) ,

Congr_def (Sense1_Compos (Sense1_Destructing  Sense1_ee_morphism)
(Sense1_Constructing_default aa Sense01_F form))
(Sense1_UnitViewedOb  (Sense1_ee__ G form)).
Proof.
intros. move. intros H h h0 Heq; subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
  [ 
  | exact unitGenerator
  | exact unitGenerator
  | subst; reflexivity
  |
  ].
congr ( _ o>Generator_ _). subst.
etransitivity; first last.
apply  Sense1_ee_morphism. reflexivity. simpl.
rewrite (proj2_sig (Sense1_ee__ _ _)). reflexivity.
Qed.

Definition Congr_UnitViewedOb_cong
A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)
(G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F) 
(Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F)
(Congr_ff: Congr_def  Sense1_ff Sense1_ff0) :
Congr_def (Sense1_UnitViewedOb  Sense1_ff) (Sense1_UnitViewedOb  Sense1_ff0).
Proof.
intros. move. intros. subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ 
| exact unitGenerator
| exact unitGenerator
| subst; reflexivity
|
].
congr(_ o>Generator_ _). congr(_ o>Generator_ _). apply: Congr_ff. reflexivity.
Qed.

Definition Congr_Constructing_comp_Refinement :
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(A'' : obGenerator) (a''a' : 'Generator( A'' ~> A' ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a')
(Sense01_ViewedOb Sense01_E a''a')) 
(G : obGenerator) (form : Sense00_F G),
Congr_def
(Sense1_Compos (Sense1_Refinement a'a Sense1_ee)
(Sense1_Constructing_default a'a Sense01_F form))
(Sense1_Refinement a'a
(Sense1_Compos Sense1_ee
(Sense1_Constructing_default a''a' Sense01_F form))).
Proof.
intros. move. intros H h h0 Heq. subst. simpl.
rewrite (proj1 (proj2_sig Sense01_F)).
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ 
| exact unitGenerator
| exact unitGenerator
| reflexivity
| reflexivity
].
Qed.

Definition Congr_Refinement_comp_ViewedMor:
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E) (A'' : obGenerator)
(a''a' : 'Generator( A'' ~> A' ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a')
        (Sense01_ViewedOb Sense01_E a''a')),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(Sense1_dd : Sense1_def Sense01_E Sense01_D),
Congr_def (Sense1_Compos (Sense1_ViewedMor a'a Sense1_dd) (Sense1_Refinement a'a Sense1_ee))
(Sense1_Refinement a'a (Sense1_Compos (Sense1_ViewedMor a''a' Sense1_dd) Sense1_ee)).
Proof.
intros. move. intros H h h0 Heq. subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[ | exact unitGenerator
| exact unitGenerator
| reflexivity
| reflexivity].
Qed.

Lemma Congr_Constructing_cong:
forall (A A' : obGenerator) (aa : 'Generator( A' ~> A )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (G : obGenerator)
(form : Sense00_F G)  (form' : Sense00_F G)
(ElCong_form_form' : ElCongr_def form form'),

Congr_def (Sense1_Constructing_default aa Sense01_F form)
  (Sense1_Constructing_default aa Sense01_F form').
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
forall  (A A': obGenerator)
(aa: 'Generator( A' ~> A ))
(Sense00_F: obGenerator -> Type)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
  Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
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
forall (A A': obGenerator)
(aa: 'Generator( A' ~> A ))
(Sense00_F: obGenerator -> Type)
(Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
  Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Sense00_D: obGenerator -> Type)
(Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D),
Congr_def (Sense1_Compos (Sense1_ViewedMor aa Sense1_dd) (Sense1_Destructing Sense1_ee_morphism))
  (Sense1_Destructing (Morphism_Compos_morCode_Family Sense1_ee_morphism Sense1_dd)).
Proof.
intros. move; simpl; intros; subst.
unshelve eapply Sense00_ViewedOb_quotient; simpl;
[
| exact unitGenerator
|  exact unitGenerator
|  reflexivity
|  reflexivity
].
Qed.

Lemma Congr_Refinement_cong :
forall (A A': obGenerator)
(a'a: 'Generator( A' ~> A ))
(Sense00_F: obGenerator -> Type)
(Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(A'': obGenerator)
(a''a': 'Generator( A'' ~> A' ))
(Sense1_ee Sense1_dd: Sense1_def (Sense01_Viewing Sense01_F a''a')
              (Sense01_ViewedOb Sense01_E a''a'))
(Congr_congr_eedd : Congr_def Sense1_ee Sense1_dd),
(Congr_def (Sense1_Refinement a'a Sense1_ee)
          (Sense1_Refinement a'a Sense1_dd)).
intros. move. intros; subst; simpl.
set sval_Sense1_dd_ := (sval Sense1_dd _ _).
set sval_Sense1_ee_ := (sval Sense1_ee _ _).
have -> : sval_Sense1_dd_ = sval_Sense1_ee_ by 
 apply: Congr_congr_eedd.
 unshelve eapply Sense00_ViewedOb_quotient; simpl;
 [
 | exact unitGenerator
 |  exact unitGenerator
 |  reflexivity
 |  reflexivity
 ].
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
forall (A A' : obGenerator) (aa : 'Generator( A' ~> A ))
   (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
   (G : obGenerator) (form : Sense00_F G)
   (H : obGenerator) 
   (h : Sense00_ViewOb G H), 
Congr_def
(Sense1_Compos (Sense1_Constructing_default aa Sense01_F form)
  (Sense1_Constructing_default aa (Sense01_ViewOb G) h))
(Sense1_Constructing_default aa Sense01_F (h o>Generator_[sval Sense01_F] form)).
Proof.
intros. move; intros;  subst;  simpl.
unshelve eapply Sense00_Viewing_quotient; simpl;
[
| exact unitGenerator
| exact unitGenerator
| reflexivity
| rewrite -(proj1 (proj2_sig Sense01_F)); reflexivity 
].
Qed.

Reserved Notation "''CoMod$' (  Code_ff  ~>  Code_ff'  @_  Congr_congr_ff  )" (at level 0).
Inductive congrMorCode : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff'),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff'), Type :=

| Trans_congrMorCode : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
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

| Refl_congrMorCode : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
'CoMod$( Code_ff  ~> Code_ff @_ Congr_Refl Sense1_ff )

| Rev_congrMorCode : forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff),
forall (Sense1_ff' : Sense1_def Sense01_E Sense01_F)
(Code_ff' : morCode Sense1_ff'),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff')
(congr_ff : 'CoMod$( Code_ff ~> Code_ff' @_ Congr_congr_ff )),
'CoMod$( Code_ff' ~> Code_ff @_ Congr_Rev Congr_congr_ff  )

| Constructing_comp_Destructing_congrMorCode :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)

(Sense1_ee__ : forall (G : obGenerator) (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family Sense1_ee_morphism),

forall (G : obGenerator) (form : Sense00_F G) ,
'CoMod$ ( Compos_morCode (Destructing_morCode Code_ee__)
(AtMember (Constructing_morCode_Family aa Sense01_F)  form) ~>
(UnitViewedOb_morCode  (AtMember Code_ee__  form)) @_
Congr_Constructing_comp_Destructing Sense1_ee_morphism  form )

| UnitViewedOb_cong_congrMorCode
A A' (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)
(G : obGenerator)
(Sense1_ff: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F) 
(Code_ff : morCode Sense1_ff)
(Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F)
(Code_ff0 : morCode Sense1_ff0)
(Congr_ff: Congr_def  Sense1_ff Sense1_ff0)
(congr_ff : 'CoMod$ ( Code_ff ~> Code_ff0 @_ Congr_ff )) :
'CoMod$ ( UnitViewedOb_morCode  Code_ff ~>
    UnitViewedOb_morCode  Code_ff0 @_
    Congr_UnitViewedOb_cong  Congr_ff )

| Constructing_comp_Refinement_congrMorCode :
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(A'' : obGenerator) (a''a' : 'Generator( A'' ~> A' ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a')
                        (Sense01_ViewedOb Sense01_E a''a')) 
(Code_ee : morCode Sense1_ee)
(G : obGenerator) (form : Sense00_F G),
'CoMod$ (Compos_morCode  (Refinement_morCode a'a Code_ee)
  (AtMember     (Constructing_morCode_Family a'a     Sense01_F) form) ~>
  Refinement_morCode a'a  (Compos_morCode Code_ee
  (AtMember     (Constructing_morCode_Family a''a'     Sense01_F) form)) 
  @_ (Congr_Constructing_comp_Refinement Sense1_ee form) )

| Refinement_comp_ViewedMor_congrMorCode:
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E) (A'' : obGenerator)
(a''a' : 'Generator( A'' ~> A' ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a')
                    (Sense01_ViewedOb Sense01_E a''a')) ,
forall (Code_ee : morCode Sense1_ee),
forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
  (Sense1_dd : Sense1_def Sense01_E Sense01_D)
  (Code_dd : morCode Sense1_dd),
'CoMod$ ( Compos_morCode (ViewedMor_morCode a'a Code_dd) (Refinement_morCode a'a Code_ee) ~>
    Refinement_morCode a'a (Compos_morCode (ViewedMor_morCode a''a' Code_dd) Code_ee)
    @_ Congr_Refinement_comp_ViewedMor  Sense1_ee  Sense1_dd  )
        
| Constructing_cong_congrMorCode :
forall (A A' : obGenerator) (aa : 'Generator( A' ~> A )) (Sense00_F : obGenerator -> Type)
(Sense01_F : Sense01_def Sense00_F)  (G : obGenerator)
(form : Sense00_F G)  (form' : Sense00_F G)
(ElCong_form_form' : ElCongr_def form form'),
  
'CoMod$ ( AtMember (Constructing_morCode_Family aa Sense01_F) form ~>
        AtMember (Constructing_morCode_Family aa Sense01_F) form' @_
        (Congr_Constructing_cong Sense01_F ElCong_form_form' ) )

| Compos_cong_congrMorCode :  
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F) 
(Sense00_F' : obGenerator -> Type) (Sense01_F' : Sense01_def Sense00_F')

(Sense1_ff' : Sense1_def Sense01_F' Sense01_F) (Code_ff' : morCode Sense1_ff')
(Sense00_F'' : obGenerator -> Type) (Sense01_F'' : Sense01_def Sense00_F'') 

(Sense1_ff_ : Sense1_def Sense01_F'' Sense01_F' ) (Code_ff_ : morCode Sense1_ff_)
(Sense1_ee' : Sense1_def Sense01_F' Sense01_F ) (Code_ee' : morCode Sense1_ee')
(Congr_congr_ff' : Congr_def Sense1_ff' Sense1_ee' ),
'CoMod$ ( Code_ff' ~> Code_ee' @_ Congr_congr_ff' ) ->
forall (Sense1_ee_ : Sense1_def Sense01_F'' Sense01_F' ) (Code_ee_ : morCode Sense1_ee_)
(Congr_congr_ff_ : Congr_def Sense1_ff_ Sense1_ee_ ),
'CoMod$ ( Code_ff_ ~> Code_ee_ @_ Congr_congr_ff_ ) ->
'CoMod$ ( Compos_morCode Code_ff' Code_ff_ ~> Compos_morCode  Code_ee'  Code_ee_ @_
                    congr_Compos_cong Congr_congr_ff' Congr_congr_ff_ )

| AtMember_Compos_morCode_Family_congrMorCode :
forall
(A A': obGenerator)
(aa: 'Generator( A' ~> A ))
(Sense00_F: obGenerator -> Type)
(Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__: morCode_Family Sense1_ee_morphism)
(Sense00_D: obGenerator -> Type)
(Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D)
(Code_dd: morCode Sense1_dd)
(G: obGenerator)
(form: Sense00_F G),
'CoMod$ ( AtMember (Compos_morCode_Family Code_dd Code_ee__) form ~>
    Compos_morCode Code_dd (AtMember Code_ee__ form) @_
    (Congr_AtMember_Compos_morCode_Family Sense1_ee__ Sense1_dd form ))

| Destructing_comp_ViewedMor_congrMorCode :
forall (A A': obGenerator)
(aa: 'Generator( A' ~> A ))
(Sense00_F: obGenerator -> Type)
(Sense01_F: Sense01_def Sense00_F)
(Sense00_E: obGenerator -> Type)
(Sense01_E: Sense01_def Sense00_E)
(Sense1_ee__: forall G : obGenerator,
    Sense00_F G -> Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism: Morphism_prop Sense01_F Sense1_ee__)
(Code_ee__: morCode_Family Sense1_ee_morphism)
(Sense00_D: obGenerator -> Type)
(Sense01_D: Sense01_def Sense00_D)
(Sense1_dd: Sense1_def Sense01_E Sense01_D)
(Code_dd: morCode Sense1_dd),
'CoMod$ ( Compos_morCode (ViewedMor_morCode aa Code_dd) (Destructing_morCode Code_ee__) ~>
    Destructing_morCode (Compos_morCode_Family Code_dd Code_ee__) @_
    Congr_Destructing_comp_ViewedMor Sense1_ee_morphism Sense1_dd )

| Refinement_cong_congrMorCode :
forall (A A' : obGenerator) (a'a : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(Sense00_E : obGenerator -> Type)
(Sense01_E : Sense01_def Sense00_E)
(A'' : obGenerator) (a''a' : 'Generator( A'' ~> A' ))
(Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a')
          (Sense01_ViewedOb Sense01_E a''a'))
(Code_ee : morCode Sense1_ee)
(Sense1_dd : Sense1_def (Sense01_Viewing Sense01_F a''a')
          (Sense01_ViewedOb Sense01_E a''a'))
(Code_dd : morCode Sense1_dd)
(Congr_congr_eedd : Congr_def Sense1_ee Sense1_dd)
(congr_eedd : 'CoMod$ ( Code_ee ~> Code_dd @_ Congr_congr_eedd )),

'CoMod$ ( Refinement_morCode a'a Code_ee ~>
  Refinement_morCode a'a Code_dd @_ Congr_Refinement_cong Congr_congr_eedd)

| Constructing_comp_Constructing_congrMorCode  :
forall (A A' : obGenerator) (aa : 'Generator( A' ~> A ))
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F) (G : obGenerator) (form : Sense00_F G)
(cons_form : elAlgebra F form) (H : obGenerator) 
(h : Sense00_ViewOb G H) (cons_h : elAlgebra (ViewOb G) h),
'CoMod$ ( Compos_morCode
      (AtMember (Constructing_morCode_Family aa Sense01_F) form)
      (AtMember (Constructing_morCode_Family aa (Sense01_ViewOb G)) h)
  ~> AtMember (Constructing_morCode_Family aa Sense01_F)
      (h o>Generator_ form) @_ Congr_Constructing_comp_Constructing Sense01_F form h  )

where "''CoMod$' (  Code_ff  ~>  Code_ff'  @_  Congr_congr_ff  )" :=
(@congrMorCode _ _ _ _ _  Code_ff _ Code_ff' Congr_congr_ff) : poly_scope.

Notation "congr_ff_ o>$ congr_ff'" := (@Trans_congrMorCode _ _ _ _ _ _ _ _ _  congr_ff_ _ _ _ congr_ff')
    (at level 40 , congr_ff' at next level , left associativity) : poly_scope.
Arguments Refl_congrMorCode  {_ _ _ _ _ _}.

Reserved Notation "''CoMod' (  E  ~>  F  @_  Code_ff  )" (at level 0).

Inductive morCoMod : forall Sense00_E Sense01_E 
  (E : @obCoMod Sense00_E Sense01_E ),
forall Sense00_F Sense01_F 
(F : @obCoMod Sense00_F Sense01_F ),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff ), Type :=

| Compos : forall Sense00_F Sense01_F 
(F : @obCoMod Sense00_F Sense01_F ),
forall Sense00_F' Sense01_F'
(F' : @obCoMod Sense00_F' Sense01_F' ) Sense1_ff'
(Code_ff' : morCode Sense1_ff')
(ff' : 'CoMod( F' ~> F @_ Code_ff' )),

forall Sense00_F'' Sense01_F''
(F'' : @obCoMod Sense00_F'' Sense01_F''),
forall Sense1_ff_  (Code_ff_ : morCode Sense1_ff_)
(ff_ : 'CoMod( F'' ~> F' @_ Code_ff_ )),

'CoMod( F'' ~> F @_ (Compos_morCode  Code_ff'  Code_ff_) )

| Unit : 
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : @obCoMod Sense00_F Sense01_F ),
'CoMod( F ~> F @_ (Unit_morCode Sense01_F) )

| Constructing :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),

'CoMod( Viewing (ViewOb G) aa ~> Viewing F aa
    @_ (AtMember (Constructing_morCode_Family aa Sense01_F) form))

| Destructing :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family  Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator) 
            (form : Sense00_F G) (cons_form : elConstruct F  form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Code_ee0__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form),
morCode (Sense1_ee0__ G  form cons_form))
(ee__ : forall (G : obGenerator) 
    (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod( Viewing (ViewOb G) aa ~> E @_  (Code_ee0__ G  form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator) 
                (form : Sense00_F G) (cons_form : elConstruct F  form),
Congr_def ((Sense1_ee__ G  form)) (Sense1_ee0__ G  form cons_form) )
(congr_ee__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod$( (AtMember Code_ee__ form) ~> (Code_ee0__ G form cons_form) 
                            @_ Congr_congr_ee__ G  form cons_form ) ),

'CoMod( Viewing F aa ~> ViewedOb E aa  @_ (Destructing_morCode Code_ee__) )

| Refinement :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall A'' (a''a' : 'Generator( A'' ~> A' )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F a''a' ~> ViewedOb E a''a'  @_  Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

'CoMod( Viewing F a'a ~> ViewedOb E a'a  @_ (Refinement_morCode a'a  Code_ee) )

| UnitViewedOb :
forall A A' (aa : 'Generator( A' ~> A )),
forall Sense00_F (Sense01_F : Sense01_def Sense00_F)
(F: @obCoMod Sense00_F Sense01_F)
(G : obGenerator)
(Sense1_ff : Sense1_def  (Sense01_Viewing (Sense01_ViewOb G) aa)  Sense01_F)
(Code_ff : morCode Sense1_ff) (ff : 'CoMod (  Viewing (ViewOb G) aa ~> F @_ Code_ff )),
'CoMod ( Viewing (ViewOb G) aa ~> ViewedOb F aa @_ UnitViewedOb_morCode Code_ff  )

| ViewObMor : 
forall A A' (aa : 'Generator( A' ~> A )),
forall (G H : obGenerator) (g : 'Generator( G ~> H )),
'CoMod ( Viewing (ViewOb G) aa ~> Viewing (ViewOb H) aa @_ ViewObMor_morCode aa g  )

| ViewedMor :
forall (A A' : obGenerator) (aa : 'Generator( A' ~> A ))
(Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E)
(Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obCoMod Sense00_F Sense01_F),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
(Code_ff : morCode Sense1_ff)
(ff : 'CoMod( E ~> F @_ Code_ff )),
'CoMod ( ViewedOb E aa ~> ViewedOb F aa @_ ViewedMor_morCode aa Code_ff  )

where "''CoMod' ( E ~> F @_ Code_ff )" := (@morCoMod _ _ E _ _ F  _ Code_ff) : poly_scope.

Notation "ff_ o>CoMod ff'" := (@Compos _ _ _ _ _ _ _ _ ff' _ _ _ _ _ ff_ )
  (at level 40, left associativity) : poly_scope.

Reserved Notation "ff0  [  congr_ff  ]<~~  ff" (at level 10 ,  congr_ff , ff at level 40).

Inductive convCoMod : forall Sense00_E Sense01_E (E : @obCoMod Sense00_E Sense01_E ),
forall Sense00_F Sense01_F   (F : @obCoMod Sense00_F Sense01_F ),
forall (Sense1_ff : Sense1_def Sense01_E Sense01_F)
  (Code_ff : morCode Sense1_ff ) (ff : 'CoMod( E ~> F @_ Code_ff )),
forall (Sense1_ff0 : Sense1_def Sense01_E Sense01_F)
  (Code_ff0 : morCode Sense1_ff0 ) (ff0 : 'CoMod( E ~> F @_ Code_ff0 )),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff0)
  (congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_congr_ff  )), Prop :=

| Constructing_comp_Destructing :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family  Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Code_ee0__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
morCode (Sense1_ee0__ G  form cons_form))
(ee__ : forall (G : obGenerator) 
  (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod( Viewing (ViewOb G) aa ~> E @_  (Code_ee0__ G  form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator) 
              (form : Sense00_F G) (cons_form : elConstruct F  form),
Congr_def ((Sense1_ee__ G  form)) (Sense1_ee0__ G  form cons_form) )
(congr_ee__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod$( (AtMember Code_ee__   form) ~> (Code_ee0__ G  form cons_form) 
                            @_ Congr_congr_ee__ G  form cons_form ) ),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),

(UnitViewedOb  ( ee__ G form cons_form ))

[ (Constructing_comp_Destructing_congrMorCode Code_ee__ form)
  o>$ (UnitViewedOb_cong_congrMorCode  (congr_ee__ G form cons_form)) ]<~~

( ( Constructing aa (ElConstruct_elAlgebra cons_form) )
    o>CoMod ( Destructing ee__ congr_ee__ ) )

| Destructing_comp_ViewedMor :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family  Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator) 
                  (form : Sense00_F G) (cons_form : elConstruct F  form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Code_ee0__ : forall (G : obGenerator) 
                (form : Sense00_F G) (cons_form : elConstruct F  form),
morCode (Sense1_ee0__ G  form cons_form))
(ee__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod( Viewing (ViewOb G) aa ~> E @_  (Code_ee0__ G  form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator) 
            (form : Sense00_F G) (cons_form : elConstruct F  form),
Congr_def ((Sense1_ee__ G  form)) (Sense1_ee0__ G  form cons_form) )
(congr_ee__ : forall (G : obGenerator) 
      (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod$( (AtMember Code_ee__   form) ~> (Code_ee0__ G  form cons_form) 
                          @_ Congr_congr_ee__ G  form cons_form ) ),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(D: @obCoMod Sense00_D Sense01_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd)
(dd : 'CoMod( E ~> D @_ Code_dd )),

( Destructing (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form) => 
          ((ee__ G form cons_form) o>CoMod dd))
      (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form) => 
          (AtMember_Compos_morCode_Family_congrMorCode Code_ee__ Code_dd form) o>$ Compos_cong_congrMorCode (Refl_congrMorCode) (congr_ee__ G form cons_form) ) )

[ Destructing_comp_ViewedMor_congrMorCode  Code_ee__ Code_dd ]<~~

(  ( Destructing ee__ congr_ee__ ) o>CoMod ( ViewedMor aa dd ) ) 
(*MEMO: The type of this term is a product while it is expected to be (morCode_Family ?Sense1_ee_morphism). *)

| Constructing_comp_Refinement :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
    (F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
    (E: @obCoMod Sense00_E Sense01_E),
forall A'' (a''a' : 'Generator( A'' ~> A' )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F a''a' ~> ViewedOb E a''a'  @_  Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
(Refinement a'a ( (Constructing a''a' cons_form) o>CoMod ee )
    (Compos_cong_congrMorCode congr_ee (Refl_congrMorCode) ) )

[ Constructing_comp_Refinement_congrMorCode a'a  Code_ee form ]<~~

( ( Constructing a'a cons_form ) o>CoMod ( Refinement a'a ee congr_ee) )

| Refinement_comp_ViewedMor :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall A'' (a''a' : 'Generator( A'' ~> A' )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F a''a' ~> ViewedOb E a''a'  @_  Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (Sense00_D : obGenerator -> Type) (Sense01_D : Sense01_def Sense00_D)
(D: @obCoMod Sense00_D Sense01_D),
forall (Sense1_dd : Sense1_def Sense01_E Sense01_D)
(Code_dd : morCode Sense1_dd)
(dd : 'CoMod( E ~> D @_ Code_dd )),

( Refinement a'a ( ee o>CoMod ( ViewedMor a''a' dd ) )
  (Compos_cong_congrMorCode (Refl_congrMorCode) congr_ee ) )

[ Refinement_comp_ViewedMor_congrMorCode a'a Code_ee Code_dd ]<~~

( ( Refinement a'a ee congr_ee) o>CoMod ( ViewedMor a'a dd )  )

| Constructing_comp_Constructing :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),
forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),

forall (H : obGenerator) (h : (Sense00_ViewOb G) H) (cons_h : elAlgebra (ViewOb G) h),
( Constructing aa (Restrict_elAlgebra cons_form h) )

[ Constructing_comp_Constructing_congrMorCode aa cons_form cons_h ]<~~

( ( Constructing aa cons_h ) o>CoMod ( Constructing aa cons_form )  )

| Compos_cong : forall Sense00_F Sense01_F 
          (F : @obCoMod Sense00_F Sense01_F ),
forall Sense00_F' Sense01_F'
(F' : @obCoMod Sense00_F' Sense01_F' ) Sense1_ff'
(Code_ff' : morCode Sense1_ff')
(ff' : 'CoMod( F' ~> F @_ Code_ff' )),

forall Sense00_F'' Sense01_F''
(F'' : @obCoMod Sense00_F'' Sense01_F''),
forall Sense1_ff_  (Code_ff_ : morCode Sense1_ff_)
(ff_ : 'CoMod( F'' ~> F' @_ Code_ff_ )),

forall  Sense1_ee'
(Code_ee' : morCode Sense1_ee')
(ee' : 'CoMod( F' ~> F @_Code_ee' )),
forall Congr_congr_ff' (congr_ff' : 'CoMod$( Code_ff' ~> Code_ee' @_ Congr_congr_ff' ) ),
ee' [  congr_ff' ]<~~ ff' ->

forall Sense1_ee_ (Code_ee_ : morCode Sense1_ee_)
(ee_ : 'CoMod( F'' ~> F' @_ Code_ee_ )),
forall  Congr_congr_ff_ (congr_ff_ : 'CoMod$( Code_ff_ ~> Code_ee_ @_ Congr_congr_ff_ ) ),
ee_ [ congr_ff_ ]<~~ ff_ ->

( ee_ o>CoMod ee' )
[ Compos_cong_congrMorCode congr_ff'  congr_ff_ ]<~~
( ff_ o>CoMod ff' )

| Constructing_cong :
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) 
(Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (G : obGenerator) (form : Sense00_F G) (cons_form : elAlgebra F form ),
forall (form' : Sense00_F G) (cons_form' : elAlgebra F form' )
(ElCong_form_form': ElCongr_def form form') ,
( cons_form'  [ ElCong_form_form' ]<==  cons_form )  ->

( Constructing aa cons_form' )
  [ Constructing_cong_congrMorCode  aa Sense01_F ElCong_form_form' ]<~~
  ( Constructing aa cons_form  )

| Destructing_cong :
(*SIMPLE CONGRUENCE, possible is congruence
with different Code_dd__ and manual coherence conversions in 'CoMod$ *)
forall A A' (aa : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F : obData Sense01_F),

forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E : @obCoMod Sense00_E Sense01_E)

(Sense1_ee__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Sense1_ee_morphism : Morphism_prop  Sense01_F Sense1_ee__)
(Code_ee__ : morCode_Family  Sense1_ee_morphism)

(Sense1_ee0__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Code_ee0__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
morCode (Sense1_ee0__ G  form cons_form))
(ee__ : forall (G : obGenerator) 
  (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod( Viewing (ViewOb G) aa ~> E @_  (Code_ee0__ G  form cons_form))),

forall (Congr_congr_ee__ : forall (G : obGenerator) 
              (form : Sense00_F G) (cons_form : elConstruct F  form),
Congr_def ((Sense1_ee__ G  form)) (Sense1_ee0__ G  form cons_form) )
(congr_ee__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod$( (AtMember Code_ee__   form) ~> (Code_ee0__ G  form cons_form) 
                            @_ Congr_congr_ee__ G  form cons_form ) ),
forall (Sense1_dd__ : forall (G : obGenerator)  (form : Sense00_F G),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E
:= Sense1_ee__)
(Sense1_dd_morphism : Morphism_prop  Sense01_F Sense1_dd__
:= Sense1_ee_morphism)
(Code_dd__ : morCode_Family  Sense1_dd_morphism
:= Code_ee__)

(Sense1_dd0__ : forall (G : obGenerator) 
          (form : Sense00_F G) (cons_form : elConstruct F  form ),
Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_E)
(Code_dd0__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
morCode (Sense1_dd0__ G  form cons_form))
(dd__ : forall (G : obGenerator) 
  (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod( Viewing (ViewOb G) aa ~> E @_  (Code_dd0__ G  form cons_form))),

forall (Congr_congr_dd__ : forall (G : obGenerator) 
              (form : Sense00_F G) (cons_form : elConstruct F  form),
Congr_def ((Sense1_dd__ G  form)) (Sense1_dd0__ G  form cons_form) )
(congr_dd__ : forall (G : obGenerator) 
        (form : Sense00_F G) (cons_form : elConstruct F  form),
'CoMod$( (AtMember Code_dd__   form) ~> (Code_dd0__ G  form cons_form) 
                            @_ Congr_congr_dd__ G  form cons_form ) ),

forall (Congr_congr_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
Congr_def (Sense1_ee0__ G form cons_form) (Sense1_dd0__ G form cons_form))
  (congr_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
  'CoMod$( (Code_ee0__ G form cons_form) ~> (Code_dd0__ G form cons_form) @_ (Congr_congr_eedd0__ G form cons_form) )),

forall (conv_eedd0__ : forall (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form ),
    (dd__ G form cons_form) [ (congr_eedd0__ G form cons_form) ]<~~ (ee__ G form cons_form)),

( Destructing dd__ (fun (G : obGenerator) (form : Sense00_F G) (cons_form : elConstruct F form )
                  => (congr_ee__ G form cons_form) o>$ (congr_eedd0__  G form cons_form) ) ) 

[ Refl_congrMorCode (*SIMPLE CONGRUENCE *) ]<~~

 ( Destructing ee__ congr_ee__ ) 

| Refinement_cong :
forall A A' (a'a : 'Generator( A' ~> A )),
forall (Sense00_F : obGenerator -> Type) (Sense01_F : Sense01_def Sense00_F)
(F: @obData Sense00_F Sense01_F),
forall (Sense00_E : obGenerator -> Type) (Sense01_E : Sense01_def Sense00_E)
(E: @obCoMod Sense00_E Sense01_E),
forall A'' (a''a' : 'Generator( A'' ~> A' )),
forall (Sense1_ee : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee : morCode Sense1_ee),
forall (Sense1_ee0 : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_ee0 : morCode Sense1_ee0),
forall (ee: 'CoMod( Viewing F a''a' ~> ViewedOb E a''a'  @_  Code_ee0 )),
forall (Congr_congr_ee : Congr_def Sense1_ee Sense1_ee0)
(congr_ee : 'CoMod$( Code_ee ~> Code_ee0 @_ Congr_congr_ee )),

forall (Sense1_dd : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_dd : morCode Sense1_dd),
forall (Sense1_dd0 : Sense1_def (Sense01_Viewing Sense01_F a''a') (Sense01_ViewedOb Sense01_E a''a')),
forall (Code_dd0 : morCode Sense1_dd0),
forall (dd: 'CoMod( Viewing F a''a' ~> ViewedOb E a''a'  @_  Code_dd0 )),
forall (Congr_congr_dd : Congr_def Sense1_dd Sense1_dd0)
  (congr_dd : 'CoMod$( Code_dd ~> Code_dd0 @_ Congr_congr_dd )),

forall (Congr_congr_eedd0 : Congr_def Sense1_ee0 Sense1_dd0)
  (congr_eedd0 : 'CoMod$( Code_ee0 ~> Code_dd0 @_ Congr_congr_eedd0 )),

forall (conv_eedd0 : dd [ congr_eedd0 ]<~~ ee),

  ( Refinement a'a dd congr_dd )
  [ Refinement_cong_congrMorCode a'a (congr_ee o>$ congr_eedd0 o>$ (Rev_congrMorCode congr_dd))   ]<~~
  ( Refinement a'a ee congr_ee )

| UnitViewedOb_cong :
forall A A' (aa : 'Generator( A' ~> A )),
forall Sense00_F (Sense01_F : Sense01_def Sense00_F) (F: @obCoMod Sense00_F Sense01_F) (G : obGenerator)
(Sense1_ff : Sense1_def  (Sense01_Viewing (Sense01_ViewOb G) aa)  Sense01_F)
(Code_ff : morCode Sense1_ff) (ff : 'CoMod (  Viewing (ViewOb G) aa ~> F @_ Code_ff )),
forall (Sense1_ff0: Sense1_def (Sense01_Viewing (Sense01_ViewOb G) aa) Sense01_F)
(Code_ff0 : morCode Sense1_ff0)
(ff0 : 'CoMod (  Viewing (ViewOb G) aa ~> F @_ Code_ff0 ))
(Congr_ff: Congr_def  Sense1_ff Sense1_ff0)
(congr_ff : 'CoMod$ ( Code_ff ~> Code_ff0 @_ Congr_ff )),

    ff0 [ congr_ff ]<~~ ff ->
  (  UnitViewedOb  ff0 )
  [ UnitViewedOb_cong_congrMorCode  congr_ff  ]<~~
  ( UnitViewedOb  ff ) 

| convCoMod_Trans :  forall Sense00_E Sense01_E 
  (E : @obCoMod Sense00_E Sense01_E),
forall Sense00_F Sense01_F
(F : @obCoMod Sense00_F Sense01_F),
forall Sense1_ff (Code_ff : morCode Sense1_ff) (ff : 'CoMod( E ~> F @_ Code_ff )),
forall Sense1_ff0 (Code_ff0 : morCode Sense1_ff0) (ff0 : 'CoMod( E ~> F @_ Code_ff0 )),
forall (Congr_congr_ff : Congr_def Sense1_ff Sense1_ff0 )
(congr_ff : 'CoMod$( Code_ff ~> Code_ff0 @_ Congr_congr_ff  )),   
ff0 [ congr_ff ]<~~ ff ->
forall Sense1_ff0' (Code_ff0' : morCode Sense1_ff0') (ff0' : 'CoMod( E ~> F @_ Code_ff0' )),
forall (Congr_congr_ff0 : Congr_def Sense1_ff0 Sense1_ff0')
(congr_ff0 : 'CoMod$( Code_ff0 ~> Code_ff0' @_ Congr_congr_ff0  )),   

ff0' [ congr_ff0 ]<~~ ff0 ->
ff0' [  congr_ff o>$ congr_ff0 ]<~~ ff

| convCoMod_Refl :  forall Sense00_E Sense01_E 
(E : @obCoMod Sense00_E Sense01_E),
forall Sense00_F Sense01_F
(F : @obCoMod Sense00_F Sense01_F),
forall Sense1_ff (Code_ff : morCode Sense1_ff) (ff : 'CoMod( E ~> F @_ Code_ff )),

ff [  Refl_congrMorCode ]<~~ ff
    
where "ff0 [  congr_ff  ]<~~ ff" := (@convCoMod _ _ _ _ _ _ _ _ ff  _ _ ff0 _ congr_ff).
(* forall (YKK2 : Congr_def _  _) (KK2 : 'CoMod$( _ ~> _ @_ YKK2 )),    *)

Global Hint Constructors convCoMod : core.

End COMOD.
(** # #
#+END_SRC

* Example

#+BEGIN_SRC coq :exports both :results silent # # **)
Module NatGenerator <: GENERATOR.

Definition obGenerator : eqType := nat_eqType.
Definition morGenerator : obGenerator -> obGenerator -> Type.
  intros n m. exact (n <= m). 
Defined.
Notation "''Generator' ( A' ~> A )" := (@morGenerator A' A)
(at level 0, format "''Generator' (  A'  ~>  A  )") : poly_scope.
Definition polyGenerator :
  forall A A', 'Generator( A' ~> A ) -> forall A'', 'Generator( A'' ~> A' ) -> 'Generator( A'' ~> A ).
  intros A A' a A'' a'. eapply (leq_trans); eassumption.
Defined.

Notation "a_ o>Generator a'" := (@polyGenerator _ _ a' _ a_)
  (at level 40, a' at next level) : poly_scope.

Definition unitGenerator : forall {A : obGenerator}, 'Generator( A ~> A ) := leqnn.

Definition ConflVertex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )), obGenerator.
  intros. exact (minn ProjecterVertex  IndexerVertex).
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

Definition ConflMorphismIndexCommuteProp :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
    ConflProject projecter (preIndexer o>Generator indexer) o>Generator preIndexer
    = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflProject projecter indexer 
    /\  ConflIndex projecter (preIndexer o>Generator indexer)
        = ConflMorphismIndex projecter indexer preIndexer o>Generator ConflIndex projecter indexer.
  intros. split; apply: bool_irrelevance.
Qed.

Parameter polyGenerator_morphism :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )) 
          (A'' : obGenerator) (a_ : 'Generator( A'' ~> A' )),
  forall B (b : 'Generator( B ~> A'' )),
    b o>Generator ( a_ o>Generator a' ) = ( b o>Generator a_ ) o>Generator a'.
Parameter polyGenerator_unitGenerator :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )),
    a' = ( (@unitGenerator A') o>Generator a' ).
Parameter unitGenerator_polyGenerator :
  forall (A : obGenerator), forall (A'' : obGenerator) (a_ : 'Generator( A'' ~> A )),
      a_ = ( a_ o>Generator (@unitGenerator A) ).

Parameter ConflProp_ComposIndex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  { CommonConflVertex : obGenerator &
  { CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex (ConflProject projecter indexer) preIndexer ) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter (preIndexer o>Generator indexer ) )) |
    CommonConfl1 o>Generator (ConflProject (ConflProject projecter indexer) preIndexer ) 
    = CommonConfl2 o>Generator   (ConflProject projecter (preIndexer o>Generator indexer ))
    /\  CommonConfl1 o>Generator ((ConflIndex (ConflProject projecter indexer) preIndexer ) )
        = CommonConfl2 o>Generator   (ConflMorphismIndex projecter indexer preIndexer )
  } } }.

Parameter ConflProp_AssocIndex :
  forall BaseVertex ProjecterVertex (projecter : 'Generator( ProjecterVertex ~> BaseVertex )), 
  forall IndexerVertex (indexer : 'Generator( IndexerVertex ~> BaseVertex )),
  forall PreIndexerVertex (preIndexer : 'Generator( PreIndexerVertex ~> IndexerVertex )),
  forall PrePreIndexerVertex (prePreIndexer : 'Generator( PrePreIndexerVertex ~> PreIndexerVertex )),
  { CommonConflVertex : obGenerator &
  { CommonConfl1 : 'Generator( CommonConflVertex ~> (ConflVertex projecter  (prePreIndexer o>Generator (preIndexer o>Generator indexer))) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> (ConflVertex projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer)) ) |
    CommonConfl1 o>Generator (ConflProject projecter (prePreIndexer o>Generator (preIndexer o>Generator indexer)) ) 
    = CommonConfl2 o>Generator   (ConflProject projecter ((prePreIndexer o>Generator preIndexer) o>Generator indexer))
    /\  CommonConfl1 o>Generator ( (ConflMorphismIndex projecter (preIndexer o>Generator indexer) prePreIndexer)
                                    o>Generator (ConflMorphismIndex projecter indexer preIndexer) )
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
                                      o>Generator indexer)) ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex projecter
                  (ConflProject projecter (preIndexer o>Generator indexer)
                  o>Generator (preIndexer o>Generator indexer)) ) |
    CommonConfl1 o>Generator ConflProject projecter (ConflMorphismIndex projecter (indexer) preIndexer
    o>Generator (ConflProject projecter (indexer) o>Generator indexer))
  = CommonConfl2 o>Generator  ConflProject projecter
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
{ CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter (ConflIndex projecter (preIndexer o>Generator indexer)) ) &
{ CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter
                       (ConflMorphismIndex projecter indexer preIndexer
                        o>Generator ConflIndex projecter indexer) ) |
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
  { CommonConfl1 : 'Generator( CommonConflVertex ~> ConflVertex (preProjecter o>Generator ConflProject projecter indexer) preIndexer  ) &
  { CommonConfl2 : 'Generator( CommonConflVertex ~> ConflVertex preProjecter (ConflMorphismIndex projecter indexer preIndexer)) |
    CommonConfl1 o>Generator ConflProject (preProjecter o>Generator ConflProject projecter indexer) preIndexer
    = CommonConfl2 o>Generator (ConflProject preProjecter (ConflMorphismIndex projecter indexer preIndexer)
                                            o>Generator ConflProject projecter (preIndexer o>Generator indexer))
    /\  CommonConfl1 o>Generator (ConflIndex (preProjecter o>Generator ConflProject projecter indexer) preIndexer)
        = CommonConfl2 o>Generator (ConflIndex preProjecter (ConflMorphismIndex projecter indexer preIndexer) )
  } } }.
End NatGenerator.

Import NatGenerator.
Declare Module Import CoMod : (COMOD NatGenerator).

Parameter (GFixed : obGenerator). 

Definition example_morphism :   
{ Sense1_ff : Sense1_def _ _ &
{ Code_ff : morCode Sense1_ff &
  'CoMod( Viewing (ViewOb GFixed) (eq_refl _ : 2 <= 3) ~>
   ViewedOb (Viewing (ViewOb GFixed) (eq_refl _ : 0 <= 0)) (eq_refl _ : 2 <= 3) @_ Code_ff ) }}.
Proof.
repeat eexists.
eapply Refinement with (a'a := (eq_refl _ : 2 <= 3)) (2 := Refl_congrMorCode).
eapply Refinement with (a'a := (eq_refl _ : 1 <= 2)) (2 := Refl_congrMorCode).
eapply Refinement with (a'a := (eq_refl _ : 0 <= 1)) (2 := Refl_congrMorCode).
eapply Destructing with (aa := (eq_refl _ : 0 <= 0)).
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
{ ff : 'CoMod( _ ~> _  @_ Code_ff ) &
{ Congr_congr_ff : Congr_def _ _ &
{ congr_ff : 'CoMod$( _ ~> _ @_ Congr_congr_ff  ) &
( ff )  [ congr_ff ]<~~
 ( (Constructing (eq_refl _ : 2 <= 3) (ElConstruct_elAlgebra (ViewOb_elConstruct unitGenerator)))
     o>CoMod (projT2 (projT2 example_morphism)) ) 
}}}}}.
Proof.
repeat eexists.  simpl. 
eapply convCoMod_Trans.
eapply Constructing_comp_Refinement.
eapply convCoMod_Trans. 
eapply Refinement_cong, Constructing_comp_Refinement.
eapply convCoMod_Trans. 
eapply Refinement_cong, Refinement_cong, Constructing_comp_Refinement.
eapply convCoMod_Trans. 
eapply Refinement_cong, Refinement_cong, Refinement_cong, Constructing_comp_Destructing.
simpl. destruct (eq_comparable GFixed GFixed); last by []; simpl.
eapply convCoMod_Trans. 
eapply Refinement_cong, Refinement_cong, Refinement_cong, UnitViewedOb_cong, Constructing_comp_Constructing.
exact: convCoMod_Refl.
Unshelve. all: try apply Refl_congrMorCode.
Defined.
Eval simpl in (projT1 (projT2 (projT2 example_reduction))).
(*
= Refinement (eqxx (2 - 3))
      (Refinement (eqxx (1 - 2))
        (Refinement (eqxx (0 - 1))
            (UnitViewedOb
              (Constructing (eqxx (0 - 0))
                  (Restrict_elAlgebra
                    (ElConstruct_elAlgebra
                        (ViewOb_elConstruct unitGenerator)) unitGenerator)))
            Refl_congrMorCode) Refl_congrMorCode) Refl_congrMorCode
  : 'CoMod ( Viewing (ViewOb GFixed) (eqxx (2 - 3) : 1 < 3) ~>
    ViewedOb (Viewing (ViewOb GFixed) (eqxx (0 - 0) : 0 <= 0))
      (eqxx (2 - 3) : 1 < 3) @_ projT1 (projT2 example_reduction) ) *)
End SHEAF.
(** # #
#+END_SRC

Voila.
# # **)