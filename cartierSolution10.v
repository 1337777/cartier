(** # #
#+TITLE: cartierSolution10.v

Proph

https://gitlab.com/1337777/cartier/blob/master/cartierSolution10.v


#+BEGIN_SRC coq :exports both :results silent # # **)

(**COMMENTS: TODO: AtParam_ is not functor , then use only Local_ instead , 
so that fiber of elements is functor over View . 
 and also using Local_ in defining SumSubstFunctor will make SumSubstFunctor into more structured (?fibration?) ...

- WAIT NOT REALLY THIS : note that in Yoneda1_Form_ee G param form , form must be the old AtParam_ because there is no such
  outer action   (g : _ ) -> Local_ param -> Local_ (g o> Param) ;
  therefore while SumFunctor uses Local_, it is still sufficient for the transformation ee_ defined on it to use AtParam_
  by using the changes   AtParam_ >-> Local_   and   (h_form : Local_ param) -> AtParam ((projT1 h_form) o> param) 
  IN FACT : Yoneda1_Form_data , Yoneda1_Form_ee_morphism morphism would best use Local_ and require 
   ee_ param (g o> (form : Local_ param)) (localparam : Local_ (subst param)) (k : Local_ localparam)
   = ee_ param form localparam (g o> k)

- SHORT : therefore should instead attempt the Local_ everywhere because then some structural changes of parameters/fibers is internalized ( "fibration" , = possibility to work (still have structural operations) locally/within/internally of each (relaxed) fiber ;
         in other words : "fibration" = must enable "localization" (of structural-operations) )

- MEMO: in fact _Local_ est une formulationn de Intersec pour (element_to_polyelement param) whith nested quantification { actor : Generator( ) & { param2 : AtParam (actor o> param) | } } ;  TODO: use this _Local_ instead , and ee_morphism move the outside precomposition to the inside postcomposition on intersec and AtParam

-xxx TODO: erase the extra parameter of Param_AtParam_

- TODO: isFiniteness_FormParam_F over _proj and _subst ? and isFiniteness_Transf_subst0 for subst0 reparametrization only ? 

- TODO: Format and Formatting require the generating fibration GFib : Tot -> Base  to be full functor with "morphisms-functorial section" , which is simply some functor which is identity on objects and which is then some data  msec1_(-,#) :  Base( GFib - , GFib # ) -> Tot( - , # )  on morphisms .

-TODO: make convCoMod_sense use reparamMor_Form instead of explicit substitution in equation
-TODO: in PolyTransf , present the parameter Yoneda1_Param_subst in predicate/classified style , then define Yoneda00_Param_SubstF0 as sum/totality of this predicate 

-TODO: change Yoneda01_AtParam_transp to Yoneda00_AtParam_transp


-TODO: Yoneda1_Param_reparam_ in 'CoMod_$ (ReParam_EF ~> ReParamEF0 $ codereparam) shall also be carried by code , Heq_Form_ee in PolyTransf_default shall be carried by code itself carried by 'CoMod$(Form_ff ~> Form_ee @ codeHeq ) , and _morphism in PolyTransf_default shall be carried by code ; all of these code are mutual inductive and also carry isFiniteness codes .

-TODO: Yoneda1_Param_reparam_remember should be code as _morphism of PolyTransf , with SHARING both carried as code mutual with pseudoCode and carried as code in congrPseudoCode 

-TODO: add
user1@computer1:~$ coqc --version
The Coq Proof Assistant, version 8.12+alpha (March 2020)
compiled on Mar 13 2020 19:53:13 with OCaml 4.09.0

-xxxTODO: use transport lemma in Congr_Trans
-TODO: erase reparamMor_Form_Sym
-TODO: reparam_eedd__ and congr_eedd__ in | PolyTransf_default_cong should be each 4 instances only instead of whole family ... memo: therefore change lemma for sense also

-TODO: in Congr_PolyTransf_default_cong : 
HAHA AMBUSH ! SOLUTION : AS FOR _Local add the property that the projection value Yoneda1_Param_subsz0__  determines Yoneda00_Param_SubszF0__ (TODO: rename this),
     then apply the property and arrive at projT1 param'0 = projT1 param' which follows from Heqparam'

-TODO: document how record avoid nested projections : 3 nested projT2 require 56secs
Time have [:blurb] eeSol_transp :=
    (projT2 (projT2 (projT2
             (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee blurb)))).(* 56sec *)

-TODO: rename Yoneda01_Local_dep' as ( _ o>ParametrizatorAtLocal _ ) , contrast ( _  o>GeneratorAtParam _ ) because for example similarity in Yoneda1_Form_ee_morphism

-TODO: is  at least Refl_congrPseudoCode Trans_congrPseudoCode  Assoc_congrPseudoCode  uniform in use of codes ? maximumal use of codes or minimumal use of codes ... for now it is not uniform

-MEMO: in ViewedFunctor1_default_cong_congrPseudoCode and the code congr_conv_ff then the coded reparam_conv_ff is moreover used to moreover carry the codes ReParam_EF  ReParam_EF0

-TODO:  /!\ HAHA TACKLE /!\ [Form_ll] shall factorize through [Forget_pseudoCode ReParam_SubstF] , similar as when [ReParam_LF] factorizes through [ReParam_SubstF] 

-TODO: change to maximally inserted implicit  Forget_pseudoCode {Yoneda1_FormParam_F}

-TODO: /!\ TROLL /!\  REDO [REMEMBER] BY ASSUMING [FORM_LL] FASTOR AS [(FORM_LL' OVER REPARAM_LPISUBST) o>COMOD (FORM_LL'' OVER REPARAM_SUBSTF)]
   THEN THE OUTPUT IS JUST TO STRAIGHTEN THIS FACTORIZATION THROUGH [FORGET] ...

- TODO whether can replace  [is_Parameter0_P]  by general arrow  [Parameter0 G -> P] with pullbacks factorizing-through [Parameter1] ... , ref [View1_ReParam_comp_View1_ReParam] 

- TODO: change Heqis : is_Parameter_P = _  ; to  sval _ = sval _

-TODO: add Hint Resolve unitGenerator_reparamMorsymgenerator

-TODO: codes for all the morphisms-families (Param_morphism , Form_morphism , reparamMorSym_morphism) , add coherence of those codes in [PolyTransf_cong] with reflexivity hints , and add codes for the extensionality [PolyTransf(PolyElement)]
-TODO: rename _morphism to _family ?

-TODO: ERASE myadmit2 in Resolve tac_degrade

-TODO: add conv_param_ff_Sol_o_param_ff'Sol in  move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear; intros; in resolve of PolyTransf_morphism

-TODO: add clear solveCoMod solveCoMod_ReParam before every solution

-TODO: "proof assistants are too strict and not relaxed enough" ... well they can be relaxed , but NOT FOR FREE, there is a COST which is called "category/homotopy theory" ; luckily the routine coherence-bookkeeping relaxations can be automatic so that the cost is not too high, but there can still remain some manual hand-crafted relaxation ...

-TODO: headline :  $13.37 or Y73.31 DISCOUNTS INSIDE !

 *)
Require Import ssreflect ssrfun ssrbool.
Require Lia.
Module PARAMETRIZATION.

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections.

Notation "'sval'" := (@proj1_sig _ _).

Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Parameter obParametrizator : Type.
Parameter morParametrizator : obParametrizator -> obParametrizator -> Type.
Parameter polyParametrizator :
  forall A A', morParametrizator A' A -> forall A'', morParametrizator A'' A' -> morParametrizator A'' A .
Parameter unitParametrizator : forall {A : obParametrizator}, morParametrizator A A.
Notation "''Parametrizator' (  A'  ~>  A  )" := (@morParametrizator A' A) (at level 0) : poly_scope.
Notation "_@ A''  o>Parametrizator  a'" := (@polyParametrizator _ _ a' A'')
          (at level 40, A'' , a' at next level, left associativity) : poly_scope.
Notation "a_ o>Parametrizator a'" := (@polyParametrizator _ _ a' _ a_)
                                  (at level 40, a' at next level) : poly_scope.
Axiom polyParametrizator_morphism :
  forall (A A' : obParametrizator) (a' : 'Parametrizator( A' ~> A )) 
    (A'' : obParametrizator) (a_ : 'Parametrizator( A'' ~> A' )),
  forall B (b : 'Parametrizator( B ~> A'' )),
      b o>Parametrizator ( a_ o>Parametrizator a' ) = ( b o>Parametrizator a_ ) o>Parametrizator a' .
Axiom polyParametrizator_unitParametrizator :
  forall (A A' : obParametrizator) (a' : 'Parametrizator( A' ~> A )),
    a' = ( (@unitParametrizator A') o>Parametrizator a' ) .
Axiom unitParametrizator_polyParametrizator :
  forall (A : obParametrizator), forall (A'' : obParametrizator) (a_ : 'Parametrizator( A'' ~> A )),
    a_ = ( a_ o>Parametrizator (@unitParametrizator A) ) .
(** # #
#+END_SRC

** Generating parametrized-forms


#+BEGIN_SRC coq :exports both :results silent # # **)
Parameter obGenerator : Type.
Parameter morGenerator : obGenerator -> obGenerator -> Type.
Parameter polyGenerator :
  forall A A', morGenerator A' A -> forall A'', morGenerator A'' A' -> morGenerator A'' A .
Parameter unitGenerator : forall {A : obGenerator}, morGenerator A A.
Notation "''Generator' ( A' ~> A )" := (@morGenerator A' A)
                  (at level 0, format "''Generator' (  A'  ~>  A  )") : poly_scope.
Notation "_@ A''  o>Generator  a'" := (@polyGenerator _ _ a' A'')
          (at level 40, A'' , a' at next level, left associativity) : poly_scope.
Notation "a_ o>Generator a'" := (@polyGenerator _ _ a' _ a_)
                                  (at level 40, a' at next level) : poly_scope.
Axiom polyGenerator_morphism :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )) 
    (A'' : obGenerator) (a_ : 'Generator( A'' ~> A' )),
  forall B (b : 'Generator( B ~> A'' )),
      b o>Generator ( a_ o>Generator a' ) = ( b o>Generator a_ ) o>Generator a' .
Axiom polyGenerator_unitGenerator :
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )),
    a' = ( (@unitGenerator A') o>Generator a' ) .
Axiom unitGenerator_polyGenerator :
  forall (A : obGenerator), forall (A'' : obGenerator) (a_ : 'Generator( A'' ~> A )),
    a_ = ( a_ o>Generator (@unitGenerator A) ) .

Parameter Parameter0 : obGenerator -> obParametrizator.
Parameter Parameter1 : forall A A' : obGenerator,
    'Generator( A ~> A' ) -> 'Parametrizator( Parameter0 A ~> Parameter0 A') .
Axiom Parameter_morphism : 
  forall (A A' : obGenerator) (a' : 'Generator( A' ~> A )) 
    (A'' : obGenerator) (a_ : 'Generator( A'' ~> A' )),
    Parameter1 ( a_ o>Generator a' ) = ( Parameter1 a_ ) o>Parametrizator (Parameter1 a').
Axiom Parameter_unitGenerator :
  forall (A : obGenerator),
    (@unitParametrizator (Parameter0 A)) = ( Parameter1 (@unitGenerator A) ) .

(**TODO: make use of this NOOP head constant [Element_data] everywhere ;
  in particular , would be useful to match hypotheses such as
  [ param : Element_data Yoneda00_Param_F G ] in tactics such as [tac_param_all] **)
Definition Element_data (Yoneda00 : obGenerator -> Type) (G : obGenerator) : Type
  := (Yoneda00 G).

Definition Yoneda01_action (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : forall G G' : obGenerator,
               'Generator( G' ~> G ) -> Yoneda00 G -> Yoneda00 G')
           G G' (g : 'Generator( G' ~> G)) (x : Yoneda00 G)
  := (Yoneda01 G G' g x).

Notation "g o>Generator_ [ Yoneda01 ] x" := (@Yoneda01_action _ Yoneda01 _ _ g x)
                         (at level 40, x at next level) : poly_scope.
Notation "g o>Generator_ x" := (@Yoneda01_action _ _ _ _ g x)
                                 (at level 40, x at next level) : poly_scope.

Definition Yoneda01_functor (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : forall G G' : obGenerator,
               'Generator( G' ~> G ) -> Yoneda00 G -> Yoneda00 G') : Prop :=
  ( forall G G' (g : 'Generator( G' ~> G)) G'' (g' : 'Generator( G'' ~> G')) x,
        g' o>Generator_[Yoneda01] (g o>Generator_[Yoneda01] x)
        = (g' o>Generator g) o>Generator_[Yoneda01] x ) /\
  ( forall G x, x = (@unitGenerator G) o>Generator_[Yoneda01] x ) .

Definition Yoneda01_data (Yoneda00 : obGenerator -> Type)
  := { Yoneda01 : ( forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00 G -> Yoneda00 G' ) |
                              Yoneda01_functor Yoneda01 }.

Definition Yoneda1_natural
           Yoneda00_F (Yoneda01_F : Yoneda01_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_data Yoneda00_E)
           (Yoneda1 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G) : Prop :=
  forall G G' (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
    g o>Generator_[sval Yoneda01_E] (Yoneda1 G f)
    = Yoneda1 G' (g o>Generator_[sval Yoneda01_F] f) .

Definition Yoneda1_data
           Yoneda00_F (Yoneda01_F : Yoneda01_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_data Yoneda00_E)
  :=  { Yoneda1 : ( forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G ) |
      Yoneda1_natural Yoneda01_F Yoneda01_E Yoneda1 } .

Definition Yoneda01_Param_action (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : forall G G' : obGenerator,
               'Parametrizator( Parameter0 G' ~> Parameter0 G ) -> Yoneda00 G -> Yoneda00 G')
           G G' p x
  := (Yoneda01 G G' p x).

Notation "p o>Parametrizator_ [ Yoneda01 ] x" := (@Yoneda01_Param_action _ Yoneda01 _ _ p x)
                         (at level 40, x at next level) : poly_scope.
Notation "p o>Parametrizator_ x" := (@Yoneda01_Param_action _ _ _ _ p x)
                                 (at level 40, x at next level) : poly_scope.

Definition Yoneda01_Param_functor (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : forall G G' : obGenerator,
               'Parametrizator( Parameter0 G' ~> Parameter0 G ) -> Yoneda00 G -> Yoneda00 G') : Prop :=
  ( forall G G' (p : 'Parametrizator( Parameter0 G' ~> Parameter0 G )) G'' (p' : 'Parametrizator( Parameter0 G'' ~> Parameter0 G' )) x,
        p' o>Parametrizator_[Yoneda01] (p o>Parametrizator_[Yoneda01] x)
        = (p' o>Parametrizator p) o>Parametrizator_[Yoneda01] x ) /\
  ( forall G x, x = (@unitParametrizator (Parameter0 G)) o>Parametrizator_[Yoneda01] x ) .

Definition Yoneda01_Param_data (Yoneda00 : obGenerator -> Type)
  := { Yoneda01 : ( forall G G' : obGenerator,
               'Parametrizator( Parameter0 G' ~> Parameter0 G ) -> Yoneda00 G -> Yoneda00 G' ) |
                              Yoneda01_Param_functor Yoneda01 }.

Definition Yoneda1_Param_natural
           Yoneda00_F (Yoneda01_F : Yoneda01_Param_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_Param_data Yoneda00_E)
           (Yoneda1 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G) : Prop :=
  forall G G' (p : 'Parametrizator( Parameter0 G' ~> Parameter0 G )) (f : Yoneda00_F G),
    p o>Parametrizator_[sval Yoneda01_E] (Yoneda1 G f)
    = Yoneda1 G' (p o>Parametrizator_[sval Yoneda01_F] f) .

Definition Yoneda1_Param_data
           Yoneda00_F (Yoneda01_F : Yoneda01_Param_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_Param_data Yoneda00_E)
  :=  { Yoneda1 : ( forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G ) |
      Yoneda1_Param_natural Yoneda01_F Yoneda01_E Yoneda1 } .

Definition Yoneda01_data_of_Yoneda01_Param_data (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : Yoneda01_Param_data Yoneda00) : Yoneda01_data Yoneda00.
Proof.
  exists (fun G G' g => sval Yoneda01 G G' (Parameter1 g)).
  abstract(move; split; [ intros; simpl; rewrite /Yoneda01_action /= ; rewrite Parameter_morphism; exact: (proj1 (proj2_sig Yoneda01))
               | intros; simpl; rewrite /Yoneda01_action /= ; rewrite -Parameter_unitGenerator; exact: (proj2 (proj2_sig Yoneda01)) ]).
Defined.

Definition Yoneda1_data_of_Yoneda1_Param_data
           Yoneda00_F (Yoneda01_F : Yoneda01_Param_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_Param_data Yoneda00_E)
           (Yoneda1 : Yoneda1_Param_data Yoneda01_F Yoneda01_E) :
  Yoneda1_data (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_F) (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_E).
Proof. 
  exists (sval Yoneda1). 
  abstract(move; intros; simpl; rewrite /Yoneda01_action /= ; exact: (proj2_sig Yoneda1)).
Defined.

Definition Yoneda1_FormParam_data
           Yoneda00_F (Yoneda01_F : Yoneda01_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_Param_data Yoneda00_E)
  := Yoneda1_data Yoneda01_F (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_E).

Definition Yoneda1_FormParam_data_of_Yoneda1_Param_data
           Yoneda00_F (Yoneda01_F : Yoneda01_Param_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_Param_data Yoneda00_E)
           (Yoneda1 : Yoneda1_Param_data Yoneda01_F Yoneda01_E) :
  Yoneda1_FormParam_data (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_F) Yoneda01_E.
Proof. 
  intros. exact: (Yoneda1_data_of_Yoneda1_Param_data Yoneda1).
Defined.

(** # #
#+END_SRC

* Grammatical presentation of objects


** Sense-decodings of the objects

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Export Senses_obCoMod.
Notation "''exists'  x  ..." := (exist _ x _) (at level 10, x at next level) : poly_scope.
Notation "[<  data  |  ...  >]" := (exist (fun data : _ => sval _ _ data = _ ) data _) (at level 0) : poly_scope.

Lemma Yoneda00_View : forall (G : obGenerator), (obGenerator -> Type).
Proof. intros G. refine (fun H => 'Generator( H ~> G ) ). Defined.

Lemma Yoneda01_View : forall (G : obGenerator), Yoneda01_data (Yoneda00_View G) .
Proof.
  intros. unshelve eexists.
  - intros H H' h. refine (fun g => h o>Generator g).
  - abstract (split; [intros; exact: polyGenerator_morphism
                   | intros; exact: polyGenerator_unitGenerator]).
Defined.

Lemma Yoneda00_Param_View : forall (P : obParametrizator), (obGenerator -> Type).
Proof. intros P. refine (fun Q => 'Parametrizator( Parameter0 Q ~> P ) ). Defined.

Lemma Yoneda01_Param_View : forall (P : obParametrizator), Yoneda01_Param_data (Yoneda00_Param_View P) .
Proof.
  intros. unshelve eexists.
  - intros  G G' q. refine (fun p =>  q o>Parametrizator p).
  - abstract (split; [ intros; rewrite /Yoneda01_Param_action /= ; rewrite polyParametrizator_morphism; reflexivity
                     | intros; rewrite /Yoneda01_Param_action /= ; exact: polyParametrizator_unitParametrizator ]) .
Defined.

Lemma Yoneda1_FormParam_View : forall G : obGenerator , Yoneda1_FormParam_data (Yoneda01_View G) (Yoneda01_Param_View (Parameter0 G)).
Proof.
  intros G. unshelve eexists.
  - intros H. refine (@Parameter1 H G).
  - abstract(move; intros; symmetry; exact: Parameter_morphism).
Defined.

Definition Yoneda1_Param_View1 :
  forall (P : obParametrizator) (Q : obParametrizator) (p : 'Parametrizator( P ~> Q )),
    Yoneda1_Param_data (Yoneda01_Param_View P) (Yoneda01_Param_View Q).
Proof.
  intros. unshelve eexists.
  - intros G. refine (_@ (Parameter0  G) o>Parametrizator p ).
  - abstract (move; intros; rewrite /Yoneda01_action /= ; exact: polyParametrizator_morphism).
Defined.

Lemma Yoneda1_Param_Id :
  forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
    Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_F .
Proof.
  intros. exists (fun G => id).
  abstract (intros; move; intros; reflexivity).
Defined.

Definition Yoneda1_FormParam_Id :
  forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
    Yoneda1_FormParam_data (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_Param_F) Yoneda01_Param_F .
Proof.
  intros. exact: ( Yoneda1_data_of_Yoneda1_Param_data (Yoneda1_Param_Id _) ).
Defined.

Lemma Yoneda1_Param_PolyCoMod :
  forall Yoneda00_F1 (Yoneda01_F1 : Yoneda01_Param_data Yoneda00_F1) Yoneda00_F2 (Yoneda01_F2 : Yoneda01_Param_data Yoneda00_F2)
   (Yoneda1_ff_ : Yoneda1_Param_data Yoneda01_F1 Yoneda01_F2)
    Yoneda00_F2' (Yoneda01_F2' : Yoneda01_Param_data Yoneda00_F2')
    (Yoneda1_ff' : Yoneda1_Param_data Yoneda01_F2 Yoneda01_F2'),
    Yoneda1_Param_data Yoneda01_F1 Yoneda01_F2'.
Proof.
  intros. exists (fun A => (sval Yoneda1_ff') A \o (sval Yoneda1_ff_) A ).
  abstract (intros; move; intros; simpl; rewrite (proj2_sig Yoneda1_ff')
                                            (proj2_sig Yoneda1_ff_); reflexivity).
Defined.

Section Yoneda00_AtParam_.
Variables (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F).
Variables (Yoneda00_Param_F0' : obGenerator -> Type)
          (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0').
Variables (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_F0' Yoneda01_Param_F).

Definition Yoneda00_AtParam_
 (G : obGenerator) (param : Yoneda00_Param_F0' G)
  := {form : Yoneda00_Form_F G | sval Yoneda1_FormParam_F G form = sval Yoneda1_Param_project G param} .

Axiom Yoneda00_AtParam_quotientLogical :
  forall  (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G)
     (param param' : Yoneda00_AtParam_  paramlocal), sval param = sval param' -> param = param'.

Definition Yoneda01_AtParam_action
  (Yoneda01_AtParam : ( forall G (param : Yoneda00_Param_F0' G) (G' : obGenerator) (g : 'Generator( G' ~> G )),
                          Yoneda00_AtParam_ param -> Yoneda00_AtParam_ ((Parameter1 g ) o>Parametrizator_[sval Yoneda01_Param_F0'] param) ))
  G (param : Yoneda00_Param_F0' G) (G' : obGenerator) (g : 'Generator( G' ~> G ))(form : Yoneda00_AtParam_ param)
  := (Yoneda01_AtParam G param G' g form).

End Yoneda00_AtParam_.

Notation "''Generator' (  G'  ~>  G  @_  Yoneda1_Param_project  <|  param  )" :=
  (@Yoneda00_AtParam_ _ _ _ _ (Yoneda1_FormParam_View G) _ _ Yoneda1_Param_project G' param) (at level 0) : poly_scope.

Definition polyGenerator_AtParam : forall G (G' : obGenerator) (g' : 'Generator( G' ~> G )),
    forall (Yoneda00_Param_F0' : obGenerator -> Type) (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0')
      (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_F0' (Yoneda01_Param_View (Parameter0 G'))),
    forall (G'' : obGenerator) (param' : Yoneda00_Param_F0' G'') , 'Generator( G'' ~> G' @_ Yoneda1_Param_project <| param' ) ->
      'Generator( G'' ~> G  @_ (Yoneda1_Param_PolyCoMod Yoneda1_Param_project (Yoneda1_Param_View1 (Parameter1 g'))) <| param' ) .
Proof.
  intros G G' g' Yoneda00_Param_F0' Yoneda01_Param_F0' Yoneda1_Param_project G'' param' g_; unshelve eexists.  refine (sval g_ o>Generator g').
  - abstract (simpl; rewrite Parameter_morphism;
      rewrite [Parameter1 (sval g_)](proj2_sig g_); reflexivity).
Defined.

Definition unitGenerator_AtParam : forall {G : obGenerator} , 'Generator( G ~> G @_ (Yoneda1_Param_Id (Yoneda01_Param_View (Parameter0 G))) <| unitParametrizator ) .
Proof.
  intros. exists (@unitGenerator G).
  abstract (simpl; symmetry; exact: Parameter_unitGenerator).
Defined.

(*TODO: BAD NOTATION TODO: RENAME TO :  o>GeneratorAtParam_View *)
Notation "gp_ o>GeneratorAtParam g'" :=
  (@polyGenerator_AtParam _ _ g' _ _ _ _ _ gp_) (at level 40, g' at next level) : poly_scope.
Notation "g o>GeneratorAtParam_ [ Yoneda01_AtParam ] form" :=
  (@Yoneda01_AtParam_action _ _ _ _ _ _ _ _ Yoneda01_AtParam  _ _ _ g form)
    (at level 40, form at next level) : poly_scope.
Notation "g o>GeneratorAtParam_ form" :=
  (@Yoneda01_AtParam_action _ _ _ _ _ _ _ _ _  _ _ _ g form)
    (at level 40, form at next level) : poly_scope.

Section Yoneda01_AtParam_.
Variables (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F).
Variables (Yoneda00_Param_F0' : obGenerator -> Type)
          (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0').
Variables (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_F0' Yoneda01_Param_F).

Definition Yoneda01_AtParam_functor
  (Yoneda01_AtParam : forall G (param : Yoneda00_Param_F0' G) (G' : obGenerator) (g : 'Generator( G' ~> G )),
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param ->
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_F0'] param) ) : Prop :=
  ( forall G param G' (g : 'Generator( G' ~> G)) G'' (g' : 'Generator( G'' ~> G')) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param),
      sval (g' o>GeneratorAtParam_[Yoneda01_AtParam] (g o>GeneratorAtParam_[Yoneda01_AtParam] form)) =
      sval ((g' o>Generator g) o>GeneratorAtParam_[Yoneda01_AtParam] form )) /\
  ( forall G param (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param),
      sval form = sval ((@unitGenerator G) o>GeneratorAtParam_[Yoneda01_AtParam] form) ) .

Definition Yoneda01_AtParam_data
  := { Yoneda01_AtParam : ( forall G (param : Yoneda00_Param_F0' G) (G' : obGenerator) (g : 'Generator( G' ~> G )),
                              Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param -> Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_F0'] param) ) |
       Yoneda01_AtParam_functor Yoneda01_AtParam }.

Definition Yoneda01_AtParam_ : Yoneda01_AtParam_data.
Proof.
  unshelve eexists.
  - intros G param G' g form. exists (g o>Generator_[sval Yoneda01_Form_F] (sval form)).
    abstract(rewrite -[RHS](proj2_sig Yoneda1_Param_project);
             rewrite -[LHS](proj2_sig Yoneda1_FormParam_F); rewrite [in LHS](proj2_sig form); reflexivity).
  - abstract(split; move; simpl; intros; [ exact: (proj1 (proj2_sig Yoneda01_Form_F))
                                         | exact: (proj2 (proj2_sig Yoneda01_Form_F)) ]).
Defined.


(**  TODO: AtParam_ is not functor , instead use everywhere only Local_
 which is functor and is really pullback/fiber of element and is over functor View and over functor Param_F .
 and also using Local_ in defining SumSubstFunctor will make SumSubstFunctor into more structured (?fibration over Param_F?) ... 
 and does such directly defined SumSubstFunctor functor fibration over Param_F coincides with colimit of over all the fibers/pullpacks transformations in the topos  ? **)

Definition Yoneda01_AtParam_transp' :
 forall G (param param' : Yoneda00_Param_F0' G),  param =  param' -> 
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param ->
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param' .
Proof. 
  (** /!\ NO! intros until 1; subst; exact: id. Defined. /!\ **)
  intros ? ? ? Heq form. exists (sval form).
  abstract (simpl; subst; exact: (proj2_sig form)).
Defined.

Lemma Yoneda01_AtParam_transp'P
           (G : obGenerator) (param param' : Yoneda00_Param_F0' G) 
           (Heq : param = param') (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param) :
  sval form = sval (Yoneda01_AtParam_transp' Heq form).
Proof.
  reflexivity.
Qed.

Section Section1.

  Variables (Yoneda1_Param_project' : Yoneda1_Param_data Yoneda01_Param_F0' Yoneda01_Param_F).
  Definition Yoneda01_AtParam_transp : forall G (param param' : Yoneda00_Param_F0' G),
      sval Yoneda1_Param_project _ param = sval Yoneda1_Param_project' _ param' -> 
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param ->
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project' param' .
  Proof. 
    (** /!\ NO! intros until 1; subst; exact: id. Defined. /!\ **)
    intros ? ? ? Heq form. exists (sval form).
    abstract (simpl; rewrite  (proj2_sig form); assumption).
    (*  abstract (simpl; subst; exact: (proj2_sig form)). *)
  Defined.
End Section1.
  
End Yoneda01_AtParam_.

Section Yoneda00_Param_AtParam_.
Variables (Yoneda00_Param_F' : obGenerator -> Type)
          (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F' Yoneda01_Param_F).

Definition Yoneda00_Param_AtParam_
 (G : obGenerator) (param : Yoneda00_Param_F G)
  := {form : Yoneda00_Param_F' G | sval Yoneda1_Param_subst G form = param} .

Definition Yoneda01_Param_AtParam_action
  (Yoneda01_Param_AtParam : ( forall G (param : Yoneda00_Param_F G) (G' : obGenerator) (g : 'Parametrizator( Parameter0 G' ~> Parameter0 G )),
                          Yoneda00_Param_AtParam_ param -> Yoneda00_Param_AtParam_ ( g  o>Parametrizator_[sval Yoneda01_Param_F] param) ))
  G (param : Yoneda00_Param_F G) (G' : obGenerator) (g : 'Parametrizator( Parameter0 G' ~> Parameter0 G ))(form : Yoneda00_Param_AtParam_ param)
  := (Yoneda01_Param_AtParam G param G' g form).

Definition Yoneda00_Param_AtParam_self
           (G : obGenerator) (param : Yoneda00_Param_F' G): Yoneda00_Param_AtParam_ (sval Yoneda1_Param_subst G param).
Proof.
  exists param. abstract(reflexivity).
Defined.

Definition Yoneda00_Param_AtParam_selfP
           (G : obGenerator) (param : Yoneda00_Param_F' G):
  sval (Yoneda00_Param_AtParam_self param) = param .
Proof.
  reflexivity.
Qed.

Definition Yoneda00_Param_AtParam_self'
           (G : obGenerator) (param : Yoneda00_Param_F' G) paramlocal: (sval Yoneda1_Param_subst G param) = paramlocal -> Yoneda00_Param_AtParam_  paramlocal.
Proof.
  exists param. abstract(assumption).
Defined.

Definition Yoneda00_Param_AtParam_self'P
           (G : obGenerator) (param : Yoneda00_Param_F' G) paramlocal (Heqparam : (sval Yoneda1_Param_subst G param) = paramlocal) :
  sval (Yoneda00_Param_AtParam_self' Heqparam) = param .
Proof.
  reflexivity.
Qed.

End Yoneda00_Param_AtParam_.

Notation "''Parametrizator' (  G'  ~>  P  @_  param  )" :=
  (@Yoneda00_Param_AtParam_ _ _ _ _ (Yoneda1_Param_Id (Yoneda01_Param_View P)) G' param) (at level 0) : poly_scope.

Definition polyGenerator_Param_AtParam : forall P P' (g' : 'Parametrizator( P' ~> P )),
    forall (G'' : obGenerator) (param' : (Yoneda00_Param_View P') G'') , 'Parametrizator( G'' ~> P' @_ param' ) ->
      'Parametrizator( G'' ~> P  @_ (param' o>Parametrizator g') ) .
Proof.
  intros until param' . intros g_. exists (sval g_ o>Parametrizator g').
  - abstract (simpl; (*rewrite Parameter_morphism;*)
      rewrite [(*Parameter1*) (sval g_)](proj2_sig g_); reflexivity).
Defined.

Definition unitGenerator_Param_AtParam : forall {G : obGenerator} , 'Parametrizator( G ~> Parameter0 G @_  unitParametrizator ) .
Proof.
  intros. exists (@unitParametrizator (Parameter0 G)).
  abstract (simpl; reflexivity (* symmetry;  exact: Parameter_unitGenerator *) ).
Defined.

(*TODO: BAD NOTATION TODO: RENAME TO :  o>GeneratorAtParam_View *)
Notation "gp_ o>ParametrizatorAtParam g'" :=
  (@polyGenerator_Param_AtParam _ _ g' _ _ gp_) (at level 40, g' at next level) : poly_scope.
Notation "g o>ParametrizatorAtParam_ [ Yoneda01_Param_AtParam ] form" :=
  (@Yoneda01_Param_AtParam_action _ _ _ _ _ Yoneda01_Param_AtParam  _ _ _ g form)
    (at level 40, form at next level) : poly_scope.
Notation "g o>ParametrizatorAtParam_ form" :=
  (@Yoneda01_Param_AtParam_action _ _ _ _ _ _  _ _ _ g form)
    (at level 40, form at next level) : poly_scope.

Section Yoneda01_Param_AtParam_.
Variables (Yoneda00_Param_F' : obGenerator -> Type)
          (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F' Yoneda01_Param_F).

Definition Yoneda01_Param_AtParam_functor
  (Yoneda01_Param_AtParam : forall G (param : Yoneda00_Param_F G) (G' : obGenerator) (g : 'Parametrizator( Parameter0 G' ~> Parameter0 G )),
                                Yoneda00_Param_AtParam_ Yoneda1_Param_subst param ->
                                Yoneda00_Param_AtParam_ Yoneda1_Param_subst ( g  o>Parametrizator_[sval Yoneda01_Param_F] param) ) : Prop :=
  ( forall G param G' (g : 'Parametrizator( Parameter0 G' ~> Parameter0 G)) G'' (g' : 'Parametrizator( Parameter0 G'' ~> Parameter0 G')) (form : Yoneda00_Param_AtParam_ Yoneda1_Param_subst param),
      sval (g' o>ParametrizatorAtParam_[Yoneda01_Param_AtParam] (g o>ParametrizatorAtParam_[Yoneda01_Param_AtParam] form)) =
      sval ((g' o>Parametrizator g) o>ParametrizatorAtParam_[Yoneda01_Param_AtParam] form )) /\
  ( forall G param (form : Yoneda00_Param_AtParam_ Yoneda1_Param_subst param),
      sval form = sval ((@unitParametrizator (Parameter0 G)) o>ParametrizatorAtParam_[Yoneda01_Param_AtParam] form) ) .

Definition Yoneda01_Param_AtParam_data
  := { Yoneda01_Param_AtParam : ( forall G (param : Yoneda00_Param_F G) (G' : obGenerator) (g : 'Parametrizator( Parameter0 G' ~> Parameter0 G )),
                                Yoneda00_Param_AtParam_ Yoneda1_Param_subst param ->
                                Yoneda00_Param_AtParam_ Yoneda1_Param_subst ( g  o>Parametrizator_[sval Yoneda01_Param_F] param) ) |
       Yoneda01_Param_AtParam_functor Yoneda01_Param_AtParam }.

Definition Yoneda01_Param_AtParam_ : Yoneda01_Param_AtParam_data.
Proof.
  unshelve eexists.
  - intros G param G' g form. exists (g o>Parametrizator_[sval Yoneda01_Param_F'] (sval form)).
    abstract(rewrite -[LHS](proj2_sig Yoneda1_Param_subst); rewrite [in LHS](proj2_sig form); reflexivity).
  - abstract(split; move; simpl; intros; [ exact: (proj1 (proj2_sig Yoneda01_Param_F'))
                                         | exact: (proj2 (proj2_sig Yoneda01_Param_F')) ]).
Defined.


(**  TODO: AtParam_ is not functor , instead use everywhere only Local_
 which is functor and is really pullback/fiber of element and is over functor View and over functor Param_F .
 and also using Local_ in defining SumSubstFunctor will make SumSubstFunctor into more structured (?fibration over Param_F?) ... 
 and does such directly defined SumSubstFunctor functor fibration over Param_F coincides with colimit of over all the fibers/pullpacks transformations in the topos  ? **)
Definition Yoneda01_Param_AtParam_transp :
 forall G (param param' : Yoneda00_Param_F G), param = param' -> 
      Yoneda00_Param_AtParam_ Yoneda1_Param_subst param ->
      Yoneda00_Param_AtParam_ Yoneda1_Param_subst param' .
Proof. 
  (** /!\ NO! intros until 1; subst; exact: id. Defined. /!\ **)
  intros ? ? ? Heq form. exists (sval form).
  abstract (simpl; subst; exact: (proj2_sig form)).
Defined.
(*TODO: ERASE , obviously of no use in this form 
Lemma Yoneda01_Param_AtParam_transpP
           (G : obGenerator) (param param' : Yoneda00_Param_F G) 
           (Heq : param = param') (form : Yoneda00_Param_AtParam_ Yoneda1_Param_subst Yoneda1_Param_project param) :
  sval (Yoneda01_Param_AtParam_transp Heq form) = sval form.
Proof.
  reflexivity.
Qed. *)

(* forall G (param param' : Yoneda00_Param_F G), param = param' -> 
      Yoneda00_Param_AtParam_ Yoneda1_Param_subst Yoneda1_Param_project param ->
      Yoneda00_Param_AtParam_ Yoneda1_Param_subst Yoneda1_Param_project param' .
Definition Yoneda01_Param_AtParam_dep
           (G : obGenerator) (param : Yoneda00_Param_F G) G' (p : 'Parametrizator( Parameter0 G' ~> Parameter0 G)):
  Yoneda1_Param_data (Yoneda01_Param_AtParam Local_ (p o>Parametrizator_[sval Yoneda01_Param_F ] param))
                (Yoneda01_Local_ param).
Proof.
   unshelve eexists.
   intros H h_form. exists ( projT1 h_form o>Parametrizator p ). exists (sval (projT2 h_form)).
   abstract (simpl; rewrite [LHS](proj2_sig (projT2 h_form)); simpl; rewrite (proj1 (proj2_sig  Yoneda01_Param_F)); reflexivity).
   abstract (move; simpl; intros; apply: Yoneda00_Local_quotientLogical; simpl;
             [exact: polyParametrizator_morphism | reflexivity ]).
Defined. *)

End Yoneda01_Param_AtParam_.

Section Subst.
Section Section1.
Variables (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda00_Param_F_ : obGenerator -> Type)
          (Yoneda01_Param_F_ : Yoneda01_Param_data Yoneda00_Param_F_)
          (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_F_)
          (Yoneda00_Param_F_' : obGenerator -> Type)
          (Yoneda01_Param_F_' : Yoneda01_Param_data Yoneda00_Param_F_')
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F_' Yoneda01_Param_F_).

(** objectwise/componentwise pullback in functor category *)
Definition Yoneda00_Param_Subst : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { xf : Yoneda00_Param_F_' H &
                                   Yoneda00_Param_AtParam_ Yoneda1_Param_proj  (sval Yoneda1_Param_subst _ xf) } ).
Defined.

Axiom Yoneda00_Param_Subst_quotientLogical :
  forall G (form form' : Yoneda00_Param_Subst G), projT1 form = projT1 form' ->
                          (sval (projT2 form)) =  (sval (projT2 form')) -> form = form'.

Definition Yoneda01_Param_Subst : Yoneda01_Param_data Yoneda00_Param_Subst.
Proof.
  unshelve eexists.
  - intros H H' h xf.
    exists ( h o>Parametrizator_[sval Yoneda01_Param_F_'] (projT1 xf)).
    apply: Yoneda01_Param_AtParam_transp; last (by  exact (h o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ )] (projT2 xf)));
      abstract(exact:(proj2_sig Yoneda1_Param_subst)).
  - abstract (split; simpl;
    first (by intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
           [ rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_F_')))
           | rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_F)))]; reflexivity );
    intros H xf; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
      [ rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_F_')))
      | rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_F))) ]; reflexivity).
Defined.

Definition Yoneda1_Param_Subst_proj : Yoneda1_Param_data Yoneda01_Param_Subst Yoneda01_Param_F_'.
Proof.
  unshelve eexists.
  - intros G xf. exact: (projT1 xf).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda1_Param_Subst_subst : Yoneda1_Param_data Yoneda01_Param_Subst Yoneda01_Param_F.
Proof.
  unshelve eexists.
  - intros G xf. exact: (sval (projT2 xf)).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda1_Param_Subst : Yoneda1_Param_data Yoneda01_Param_Subst Yoneda01_Param_F_.
Proof.
  unshelve eexists.
  - intros G xf. exact: (sval Yoneda1_Param_subst _ (projT1 xf )).
  - abstract (move; simpl; intros; apply: (proj2_sig Yoneda1_Param_subst)).
Defined.
End Section1.

Definition Yoneda1_Param_Subst1 :
forall (Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_F_ : obGenerator -> Type)
(Yoneda01_Param_F_ : Yoneda01_Param_data Yoneda00_Param_F_)
(Yoneda1_Param_proj_FF_ : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_F_)
(Yoneda00_Param_F_' : obGenerator -> Type)
(Yoneda01_Param_F_' : Yoneda01_Param_data Yoneda00_Param_F_')
(Yoneda1_Param_subst_F_'F_ : Yoneda1_Param_data Yoneda01_Param_F_' Yoneda01_Param_F_)
(Yoneda00_Param_G : obGenerator -> Type)
(Yoneda01_Param_G : Yoneda01_Param_data Yoneda00_Param_G)
(Yoneda1_Param_proj_GF_ : Yoneda1_Param_data Yoneda01_Param_G Yoneda01_Param_F_)
(Yoneda00_Param_G_' : obGenerator -> Type)
(Yoneda01_Param_G_' : Yoneda01_Param_data Yoneda00_Param_G_')
(Yoneda1_Param_subst_G_'F_ : Yoneda1_Param_data Yoneda01_Param_G_' Yoneda01_Param_F_)
(Yoneda1_Param_FG : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_G)
(Heq_Param_FG : forall G param, (sval Yoneda1_Param_proj_GF_ G) ((sval Yoneda1_Param_FG G) param)
                                        = (sval Yoneda1_Param_proj_FF_ G) param)
(Yoneda1_Param_F_'G_' : Yoneda1_Param_data Yoneda01_Param_F_' Yoneda01_Param_G_')
(Heq_Param_F_'G_' : forall G param, (sval Yoneda1_Param_subst_G_'F_ G) ((sval Yoneda1_Param_F_'G_' G) param)
                                        = (sval Yoneda1_Param_subst_F_'F_ G) param),
Yoneda1_Param_data (Yoneda01_Param_Subst Yoneda1_Param_proj_FF_ Yoneda1_Param_subst_F_'F_) (Yoneda01_Param_Subst Yoneda1_Param_proj_GF_ Yoneda1_Param_subst_G_'F_).
Proof.
  intros; unshelve eexists.
  - intros G sp. exists ( sval Yoneda1_Param_F_'G_' _ (projT1 sp) ).
    exists ( sval Yoneda1_Param_FG _ (sval (projT2 sp)) ).
    + abstract(simpl; rewrite [LHS]Heq_Param_FG [RHS]Heq_Param_F_'G_'; exact: (proj2_sig (projT2 sp))).
  - abstract (move; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
              first (by exact: (proj2_sig Yoneda1_Param_F_'G_' _ _ )) ; 
    exact: (proj2_sig Yoneda1_Param_FG _ _ )) .
Defined.

End Subst.

Module Export is_Parameter0.

  Definition reparamMorSymGenerator (G' G : obGenerator) 
    := { reparam_reparam_rev : 'Generator( G' ~> G ) * 'Generator( G ~> G' )
       | ((fst reparam_reparam_rev) o>Generator (snd reparam_reparam_rev) = unitGenerator) /\
         ((snd reparam_reparam_rev) o>Generator (fst reparam_reparam_rev) = unitGenerator) } .

  Definition unitGenerator_reparamMorSymGenerator (G : obGenerator) : reparamMorSymGenerator G G.
    intros. unshelve eexists. split. 
    exact: unitGenerator.
    exact: unitGenerator.
    abstract (split; simpl; rewrite -unitGenerator_polyGenerator; reflexivity).
  Defined. 

  Definition reparamMorSymParametrizator (P' P : obParametrizator) 
    := { reparam_reparam_rev : 'Parametrizator( P' ~> P ) * 'Parametrizator( P ~> P' )
       | ((fst reparam_reparam_rev) o>Parametrizator (snd reparam_reparam_rev) = unitParametrizator) /\
         ((snd reparam_reparam_rev) o>Parametrizator (fst reparam_reparam_rev) = unitParametrizator) } .

  Definition unitParametrizator_reparamMorSymParametrizator (P : obParametrizator) : reparamMorSymParametrizator P P.
    intros. unshelve eexists. split. 
    exact: unitParametrizator.
    exact: unitParametrizator.
    abstract (split; simpl; rewrite -unitParametrizator_polyParametrizator; reflexivity).
  Defined. 

Notation Is_Parameter0 G := (unitParametrizator_reparamMorSymParametrizator (Parameter0 G)) .

Section is_Parameter0.
Variables (G : obGenerator).

Definition is_Parameter0 (P : obParametrizator) := reparamMorSymParametrizator (Parameter0 G) P .

(*TODO: INLINE *)Definition is_Parameter0_transp_rev_codom :  forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 P),
    forall Q (p : 'Parametrizator( Q ~> Parameter0 G )), 'Parametrizator( Q ~> P ).
Proof.
  intros.  exact: (p o>Parametrizator (fst (sval is_Parameter0_P))) .
Defined.

(*TODO: INLINE , AS NOTATION ? *)Definition is_Parameter0_transp_codom :  forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 P),
    forall Q (p : 'Parametrizator( Q ~> P )), 'Parametrizator( Q ~> Parameter0 G ).
Proof.
  intros.  exact: (p o>Parametrizator (snd (sval is_Parameter0_P))) .
Defined. 
End is_Parameter0.

Definition is_Parameter0_transformation : 
  forall (G' G : obGenerator) (g :  reparamMorSymGenerator G' G),
    ( forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P), is_Parameter0 G' P ) .
Proof.
  unshelve eexists. split.
  - exact: (Parameter1 (fst (sval g)) o>Parametrizator (fst (sval is_Parameter0_P))).
  - exact: ((snd (sval is_Parameter0_P)) o>Parametrizator (Parameter1 (snd (sval g)))).
  - abstract (split; simpl;
    [ simpl; rewrite polyParametrizator_morphism; rewrite -[X in X o>Parametrizator _ = _ ]polyParametrizator_morphism;
    rewrite (proj1 (proj2_sig is_Parameter0_P)); rewrite -unitParametrizator_polyParametrizator;
    rewrite -Parameter_morphism; rewrite (proj1 (proj2_sig g)); rewrite -Parameter_unitGenerator; reflexivity
    | simpl; rewrite polyParametrizator_morphism; rewrite -[X in X o>Parametrizator _ = _ ]polyParametrizator_morphism;
    rewrite -Parameter_morphism; rewrite (proj2 (proj2_sig g)); rewrite -Parameter_unitGenerator; rewrite -unitParametrizator_polyParametrizator;
    rewrite (proj2 (proj2_sig is_Parameter0_P)); reflexivity ] ).
Defined.
    

Lemma is_Parameter0_transformation_morphism : 
  forall (G : obGenerator)  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    sval is_Parameter0_P = sval (is_Parameter0_transformation (unitGenerator_reparamMorSymGenerator _) is_Parameter0_P) .
  intros. simpl. destruct is_Parameter0_P as [x ?]. simpl. destruct x. simpl. congr ( _ , _ ).
  rewrite -Parameter_unitGenerator; rewrite -polyParametrizator_unitParametrizator. reflexivity.
  rewrite -Parameter_unitGenerator; rewrite -unitParametrizator_polyParametrizator. reflexivity.
Qed.  
(*TODO: SAVE, THEN ERASE
Parameter is_Parameter0_transformation : 
  forall (G' G : obGenerator) (g : 'Generator( G' ~> G )),
    ( forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P), is_Parameter0 G' P ) .

Parameter is_Parameter0_transformation_morphism : 
  forall (G : obGenerator)  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    is_Parameter0_P = is_Parameter0_transformation (unitGenerator) is_Parameter0_P .

Parameter Yoneda1_Param_View1_proj_is_Parameter0_morphism :
        forall (G : obGenerator) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (G' : obGenerator) (g' : 'Generator( G' ~> G )) (H : obGenerator)
               (q : 'Parametrizator ( Parameter0 H ~> Parameter0 G' )),
          sval (Yoneda1_Param_View1_proj_is_Parameter0 (is_Parameter0_transformation g' is_Parameter0_P)) H q = sval (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P) H (q o>Parametrizator Parameter1 g').
*)
End is_Parameter0.

Definition element_to_polyelement : forall Yoneda00_F (Yoneda01_F : Yoneda01_Param_data Yoneda00_F) G,
    Yoneda00_F G -> Yoneda1_Param_data  (Yoneda01_Param_View (Parameter0 G)) Yoneda01_F .
Proof.
  intros ? ? G f. unshelve eexists. 
  apply: (fun G' g => g o>Parametrizator_[sval Yoneda01_F] f) . 
  abstract (move; simpl; intros G' G'' g' g;
            rewrite -(proj1 (proj2_sig Yoneda01_F)); reflexivity).
Defined.

Section Yoneda00_Local_.
Section Section0.
Variables (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F).          
Variables (Yoneda00_Param_F0' : obGenerator -> Type)
          (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0').
Variables (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_F0').

Definition Yoneda00_Local_ (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G)  : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { param : Yoneda00_Param_View (Parameter0 G) H &
                                         Yoneda00_Param_AtParam_ Yoneda1_Param_subst
                                                                 (sval (element_to_polyelement Yoneda01_Param_F0' paramlocal) _ param) } ).
Defined.
           

Axiom Yoneda00_Local_quotientLogical :
  forall (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G), forall H (param param' : Yoneda00_Local_ paramlocal H),
      projT1 param = projT1 param' ->
      (**TODO: add consequence lemma with : Yoneda1_Local_proj param = Yoneda1_Local_proj param -> _
         MEMO: must quotient the data as such , instead of using ex properties in Yoneda00_Local_ := { _ | ex _ } .
         sval (projT2 param) = sval (projT2 param') -> *)
      param = param' .
(*Proof.
  intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl; assumption.
Qed.*)

Definition Yoneda01_Local_
           (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G) : Yoneda01_Param_data (Yoneda00_Local_ paramlocal)
(*:= Yoneda01_Param_Subst Yoneda1_Param_subst (element_to_polyelement Yoneda01_Param_F0' param) *) . 
Proof.
  unshelve eexists.
  - intros H H' h param.
    exists ( h o>Parametrizator_[sval (Yoneda01_Param_View (Parameter0 G))] (projT1 param)).
    apply: Yoneda01_Param_AtParam_transp; last (by  exact (h o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ )] (projT2 param)));
      abstract(exact:(proj2_sig (element_to_polyelement Yoneda01_Param_F0' paramlocal))).
  - abstract (split; simpl;
      [ intros; apply: Yoneda00_Local_quotientLogical; simpl;
        rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_View (Parameter0 G)))); reflexivity
      | intros H param; apply: Yoneda00_Local_quotientLogical; simpl;
        rewrite -[in RHS](proj2 (proj2_sig ((Yoneda01_Param_View (Parameter0 G))))); reflexivity ] ).
Defined.

(*TODO: ERASE
Definition Yoneda00_Local_ (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G)
  := (fun H : obGenerator => { xf : Yoneda00_Param_View (Parameter0 G) H |
                             exists param , sval Yoneda1_Param_subst H param = (sval (element_to_polyelement Yoneda01_Param_F0' paramlocal) _ xf) } ) .


Axiom Yoneda00_Local_quotientLogical :
  forall (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G), forall H (param param' : Yoneda00_Local_ paramlocal H),
    projT1 param = projT1 param' -> (*TODO: use sigma sval (projT2 param) = sval (projT2 param') -> *) param = param' .
(*Proof.
  intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl; assumption.
Qed.*)

Definition Yoneda01_Local_
           (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G) : Yoneda01_Param_data (Yoneda00_Local_ paramlocal)
(*:= Yoneda01_Param_Subst Yoneda1_Param_subst (element_to_polyelement Yoneda01_Param_F0' param) *) . 
Proof.
  move. unshelve eexists.
  intros H H' h' param. exists (h' o>Parametrizator (sval param)). Locate projT1. Print Module Specif. Locate "exists".  Locate ex. Print Module Logic.
  exists (h' o>Parametrizator_[sval Yoneda01_Param_F ] (proj1 (proj2_sig param))).
  exact: (h' o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ _)] (projT2 param)).
  abstract (split; simpl; intros;
  [ apply: Yoneda00_Local_quotientLogical; simpl;
      [ rewrite [LHS]polyParametrizator_morphism; (*rewrite -[in LHS]Parameter_morphism; *) reflexivity
      | (*rewrite Parameter_morphism; *) exact: (proj1 (proj2_sig  Yoneda01_Param_F)) ]
  | apply: Yoneda00_Local_quotientLogical; simpl;
      [ (*rewrite -Parameter_unitGenerator; *) exact: polyParametrizator_unitParametrizator | (*rewrite -Parameter_unitGenerator; *) exact: (proj2 (proj2_sig  Yoneda01_Param_F))] ] ).
Defined. *)

(*TODO: ERASE this _proj and _subst *)
Definition Yoneda1_Local_proj (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G) : forall  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P), Yoneda1_Param_data (Yoneda01_Local_ paramlocal) (Yoneda01_Param_View P).
Proof.
  intros. refine (Yoneda1_Param_PolyCoMod _ (Yoneda1_Param_View1 (fst (sval is_Parameter0_P)))). unshelve eexists.
  - intros G0 param.  exact: (projT1 param).
  - abstract (move; intros; simpl; reflexivity).
Defined.
(*TODO: OLD ERASE
Definition Yoneda1_Local_proj (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G) : forall  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P), Yoneda1_Param_data (Yoneda01_Local_ paramlocal) (Yoneda01_Param_View P).
Proof.
  intros. unshelve eexists.
  - intros G0 param.  refine ( _ o>Parametrizator (fst (sval is_Parameter0_P))) .  exact: (projT1 param).
  - abstract (move; intros; simpl; exact: polyParametrizator_morphism).
Defined.*)

(*TODO: ERASE, NOT WELL-DEFINED !!!!
Definition Yoneda1_Local_subst (G : obGenerator) (param : Yoneda00_Param_F0' G) : Yoneda1_Param_data (Yoneda01_Local_ param) Yoneda01_Param_F
:= (Yoneda1_Param_Subst_subst Yoneda1_Param_subst (element_to_polyelement Yoneda01_Param_F0' param)). *)
(* Proof.
  unshelve eexists. intros H h_form. exact: (sval (projT2 h_form)).
  abstract (move; simpl; intros; reflexivity).
Defined. *)

Definition Yoneda1_Local (G : obGenerator) (paramlocal : Yoneda00_Param_F0' G) : Yoneda1_Param_data (Yoneda01_Local_ paramlocal) Yoneda01_Param_F0'.
Proof.
  unshelve eexists.
  - intros H param.
    exact: ((projT1 param) o>Parametrizator_[sval Yoneda01_Param_F0'] paramlocal).
    (** = exact: (sval (element_to_polyelement Yoneda01_Param_F0' paramlocal) _ (projT1 param )). *)
  - abstract (move; simpl; intros; exact: (proj1 (proj2_sig Yoneda01_Param_F0'))).
    (** = abstract (move; simpl; intros; apply: (proj2_sig (element_to_polyelement Yoneda01_Param_F0' paramlocal))). *)
Defined.
  
Definition Yoneda01_Local_transp
           (G : obGenerator) (param param' : Yoneda00_Param_F0' G) :
  param = param' -> Yoneda1_Param_data (Yoneda01_Local_ param)
                                  (Yoneda01_Local_ param').
Proof.
  (** /!\ NO! intros; subst; exact: Yoneda1_Param_Id. Defined. /!\ **)
  intros Heq. unshelve eexists.
  - intros H h_form. exists (projT1 h_form).
    apply: Yoneda01_Param_AtParam_transp; last (by exact: (projT2 h_form));
    abstract(simpl; subst; reflexivity).
  - abstract (move; intros; apply: Yoneda00_Local_quotientLogical; reflexivity). 
Defined.

Lemma Yoneda01_Local_transpP
           (G : obGenerator) (param param' : Yoneda00_Param_F0' G) (H : obGenerator)
           (Heq : param = param') (h_form : Yoneda00_Local_  param H) :
   projT1 h_form = projT1 (sval (Yoneda01_Local_transp Heq) _ h_form).
Proof.
  reflexivity.
Qed.

Definition Yoneda00_Local_of_Yoneda00_Param_AtParam_
           (G : obGenerator) (param : Yoneda00_Param_F0' G) :
  Yoneda00_Param_AtParam_ Yoneda1_Param_subst param -> Yoneda00_Local_  param G.
Proof.
  intros paramlocal. exists unitParametrizator. exists (sval paramlocal).
  abstract (simpl; rewrite -(proj2 (proj2_sig Yoneda01_Param_F0')); exact: (proj2_sig paramlocal)).
Defined.

(*TODO: ERASE , obviously of no use in this form
Lemma Yoneda01_Local_transpP
           (G : obGenerator) (param param' : Yoneda00_Param_F0' G) (H : obGenerator)
           (Heq : param = param') (h_form : Yoneda00_Local_ param H) :
  sval (sval (Yoneda01_Local_transp Heq) _ h_form) = sval h_form.
Proof.
  reflexivity.
Qed. *)
  
Definition Yoneda01_Local_dep
           (G : obGenerator) (param : Yoneda00_Param_F0' G) G' (p : 'Parametrizator( Parameter0 G' ~> Parameter0 G)):
  Yoneda1_Param_data (Yoneda01_Local_ (p o>Parametrizator_[sval Yoneda01_Param_F0' ] param))
                (Yoneda01_Local_ param).
Proof.
   unshelve eexists.
   intros H h_form. exists ( projT1 h_form o>Parametrizator p ). exists (sval (projT2 h_form)).
   abstract (simpl; rewrite [LHS](proj2_sig (projT2 h_form)); simpl; rewrite (proj1 (proj2_sig  Yoneda01_Param_F0')); reflexivity).
   abstract (move; simpl; intros; apply: Yoneda00_Local_quotientLogical; simpl;
             exact: polyParametrizator_morphism).
Defined.

Definition Yoneda01_Local_dep'
           (G : obGenerator) (param : Yoneda00_Param_F0' G) G'
           (p : 'Parametrizator( Parameter0 G' ~> Parameter0 G)) (param' : Yoneda00_Param_F0' G')
           (Heq: param' = (p o>Parametrizator_[sval Yoneda01_Param_F0' ] param)) :
  Yoneda1_Param_data (Yoneda01_Local_ param')
                (Yoneda01_Local_ param).
Proof.
  unshelve eexists. intros H h_form. exists ( projT1 h_form o>Parametrizator p ). exists (sval (projT2 h_form)).
   abstract (simpl; intros; subst; rewrite [LHS](proj2_sig (projT2 h_form)); simpl; rewrite (proj1 (proj2_sig  Yoneda01_Param_F0')); reflexivity).
   abstract (move; simpl; intros; apply: Yoneda00_Local_quotientLogical; simpl;
             exact: polyParametrizator_morphism).
Defined.

(*TODO: ERASE, OLD, NEVER USED
Definition Yoneda01_Local_to_Yoneda01_AtParam_ (G : obGenerator) (param : Yoneda00_Param_F0' G):
  forall H (h_form : Yoneda00_Local_ param H),
    Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project ( (fst (sval h_form)) o>Generator_ [sval Yoneda01_Param_F0' ] param ).
Proof.
  intros. exists (snd (sval h_form)).
  abstract (rewrite [LHS](proj2_sig h_form);  rewrite [LHS](proj2_sig Yoneda1_Param_project); reflexivity). 
Defined.

Definition Yoneda01_Local_to_Yoneda01_AtParam_morphism (G : obGenerator) (param : Yoneda00_Param_F0' G):
  forall H (h_form : Yoneda00_Local_ param H),
  forall H' (h : 'Generator( H' ~> H)), sval (Yoneda01_Local_to_Yoneda01_AtParam_ ( h o>Generator_[sval (Yoneda01_Local_ param) ] h_form ))
                                   =  sval (h o>GeneratorAtParam_[sval (Yoneda01_AtParam_  _ _) ] (Yoneda01_Local_to_Yoneda01_AtParam_ ( h_form ) ))  .
Proof.
  abstract (intros; simpl; reflexivity).
Defined. *)

End Section0.

Section Section1.
Variables (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F).          
Variables (Yoneda00_Param_F0' : obGenerator -> Type)
          (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0').
Variables (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_F0').
(**TODO: ERASE, already have  Yoneda00_Local_of_Yoneda00_Param_AtParam_*)
Definition unit_Local
 (G : obGenerator) (form : Yoneda00_Param_F G) : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst _ form) G.
Proof.
  intros. exists unitParametrizator . exists form. 
  abstract (simpl; rewrite -(proj2 (proj2_sig Yoneda01_Param_F0')); reflexivity).
Defined.  

End Section1.

End Yoneda00_Local_.

Section Sum.
Variables (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda00_Param_SumF : obGenerator -> Type)
          (Yoneda01_Param_SumF : Yoneda01_Param_data Yoneda00_Param_SumF)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_SumF).
  

Definition Yoneda00_Param_Sum : obGenerator -> Type
:= Yoneda00_Param_Subst Yoneda1_Param_subst (Yoneda1_Param_Id _) .

Lemma Yoneda00_Param_Sum_quotientLogical :
  forall G (form form' : Yoneda00_Param_Sum G), projT1 form = projT1 form' -> sval (projT2 form) = sval (projT2 form') -> form = form' .
Proof.
  intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl; assumption.
Qed.

 
Definition Yoneda01_Param_Sum : Yoneda01_Param_data Yoneda00_Param_Sum
:= Yoneda01_Param_Subst Yoneda1_Param_subst (Yoneda1_Param_Id _) .

Definition Yoneda1_Param_Sum : Yoneda1_Param_data Yoneda01_Param_Sum Yoneda01_Param_SumF
:= Yoneda1_Param_Subst Yoneda1_Param_subst (Yoneda1_Param_Id _) .

(**TODO: this is used at reparamMorSym_PolyElement_default_comp_PolyTransf_default_reparam *)
Definition Yoneda1_Param_Sum_subst : Yoneda1_Param_data Yoneda01_Param_Sum Yoneda01_Param_F
:= Yoneda1_Param_Subst_subst Yoneda1_Param_subst (Yoneda1_Param_Id _) .

End Sum.

Section SumImage.
Variables (Yoneda00_Param_SubstF : obGenerator -> Type)
          (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F).
  

Definition Yoneda00_Param_SumImage : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { param : Yoneda00_Param_F H &
                                   Yoneda00_Param_AtParam_ Yoneda1_Param_subst param } ).
Defined.

Axiom Yoneda00_Param_SumImage_quotientLogical :
  forall G (paramm paramm' : Yoneda00_Param_SumImage G), projT1 paramm = projT1 paramm' ->  paramm = paramm' .

 
Definition Yoneda01_Param_SumImage : Yoneda01_Param_data Yoneda00_Param_SumImage.
Proof.
  unshelve eexists.
  - intros G G' g paramm.
    exists ( g o>Parametrizator_[sval Yoneda01_Param_F] (projT1 paramm)).
    { (*logical part *)
      abstract (apply: Yoneda01_Param_AtParam_transp; first reflexivity;
                exact (g o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ )] (projT2 paramm))).
    }
  - abstract (split; simpl;
    first (by intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl;
           rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_F))); reflexivity);
    intros G paramm; apply: Yoneda00_Param_SumImage_quotientLogical; simpl;
      rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_F))); reflexivity).
Defined.

Definition Yoneda1_Param_SumImage : Yoneda1_Param_data Yoneda01_Param_SumImage Yoneda01_Param_F.
Proof.
  unshelve eexists.
  - intros G paramm. exact: (projT1 paramm).
  - abstract (move; reflexivity).
Defined.

End SumImage.

Section SumSubst.
Variables (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
          (Yoneda00_Param_SubstF : obGenerator -> Type)
          (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
          (Yoneda00_Param_SumSubstF : obGenerator -> Type)
          (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
          (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F).
  
(** . **)

Definition Yoneda00_Form_SumSubst : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { p : Yoneda00_Param_SumSubstF H & (* { V : obViewing H & *)
         { s : (* forall (H' : obGenerator) (h : 'Generator( H' ~> H (* | V *) ))  quantify some covering of H ...*)
             Yoneda00_Param_AtParam_ Yoneda1_Param_subst p &
             (* forall (H' : obGenerator) (h : 'Generator( H' ~> H (* | V *) ))    quantify same or included covering of H ? ... , *)
             Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project (sval s (* h *)) } } ).
Defined.

Axiom Yoneda00_Form_SumSubst_quotientLogical :
  forall G (form form' : Yoneda00_Form_SumSubst G), projT1 form = projT1 form ->
    sval (projT1 (projT2 form)) = sval (projT1 (projT2 form'))  -> sval (projT2 (projT2 form)) = sval (projT2 (projT2 form'))  -> form = form' .
    
  
Definition Yoneda01_Form_SumSubst : Yoneda01_data Yoneda00_Form_SumSubst.
Proof.
  unshelve eexists.
  - intros H H' h pf_.
    exists ( (Parameter1 h) o>Parametrizator_[sval Yoneda01_Param_SumSubstF] (projT1 pf_) ). unshelve eexists. 
    + exact: ((Parameter1 h) o>ParametrizatorAtParam_ [ sval (Yoneda01_Param_AtParam_ _) ] (projT1 (projT2 pf_))).
    + simpl. exact: ( h o>GeneratorAtParam_ [ sval (Yoneda01_AtParam_ _ _) ] (projT2 (projT2 pf_))) .
  - abstract (move; simpl; split;
    [ intros; apply: Yoneda00_Form_SumSubst_quotientLogical; simpl;
      [ reflexivity | rewrite Parameter_morphism; exact: (proj1 (proj2_sig Yoneda01_Param_SubstF))
      | exact: (proj1 (proj2_sig Yoneda01_Form_F)) ]
    | intros; apply: Yoneda00_Form_SumSubst_quotientLogical; simpl;
      [ reflexivity | rewrite -Parameter_unitGenerator; exact: (proj2 (proj2_sig Yoneda01_Param_SubstF))
      | exact: (proj2 (proj2_sig Yoneda01_Form_F)) ] ] ) .
Defined.

Definition Yoneda1_FormParam_SumSubst : Yoneda1_FormParam_data Yoneda01_Form_SumSubst (Yoneda01_Param_SumImage Yoneda1_Param_subst). (* well-defined *)
Proof.
  unshelve eexists.
  - intros G param_form. exists (projT1 param_form).
    { (* logical part *) abstract (exact: (projT1 (projT2 param_form))). }
  - abstract (move; intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; reflexivity).
Defined.

End SumSubst.

Section PiSubst.
Variables (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
          (Yoneda00_Param_SubstF : obGenerator -> Type)
          (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
          (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
          (Yoneda00_Param_PiSubstF : obGenerator -> Type)
          (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
          (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF).
  
Definition Yoneda00_Form_PiSubst : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { p : Yoneda00_Param_PiSubstF H &
    { f_ : ( forall (H' : obGenerator) (h : 'Generator( H' ~> H ) (* | V *) ) , (*  quantify some covering of H ...*)
               forall (s : Yoneda00_Param_AtParam_ Yoneda1_Param_project ((Parameter1 h) o>Parametrizator_[sval Yoneda01_Param_PiSubstF] p) ),
              Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_subst (sval s) ) |
      forall H' (h : 'Generator( H' ~> H )) s,
      forall H'' (h' : 'Generator( H'' ~> H' )) (h'h : 'Generator( H'' ~> H )) s_H'',
      forall Heq_arrow : h' o>Generator h = h'h ,
      forall Heq_param : sval ((Parameter1 h') o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ )] s) = sval s_H'' ,
        sval (h' o>GeneratorAtParam_[sval (Yoneda01_AtParam_ _ _)] (f_ H' h s)) = sval (f_ H'' h'h s_H'') } } ).
Defined.


(**TODO?: rewrite the _morphism property above with the common formulation , then show some lemma _quotientLogical lemma and next show this formulation as lemma instead; also memo the below Yoneda00_Form_PiSubst_quotientLogical_rev ... but in view of this formulation of _morphisms for PolyTransf-and-such , SHOULD DO?


TODO: shall instead? (forall  (G' : obGenerator) (g : 'Generator( G' ~> G )) s s', sval s = sval s' -> sval (sval (projT2 form) _ g s) = sval (sval (projT2 form') _ g s'))  -> *)
Axiom Yoneda00_Form_PiSubst_quotientLogical_ALT :
  forall G (form form' : Yoneda00_Form_PiSubst G),
    (forall  (G' : obGenerator) (g : 'Generator( G' ~> G )) s s', sval s = sval s' ->
                                                             sval (sval (projT2 form) _ g s) = sval (sval (projT2 form') _ g s')) -> form = form' .

Lemma Yoneda00_Form_PiSubst_quotientLogical_rev :
  forall G (form form' : Yoneda00_Form_PiSubst G),
    form = form' -> (forall s s', sval s = sval s' -> sval (sval (projT2 form) _ (unitGenerator) s) = sval (sval (projT2 form') _ (unitGenerator) s'))  .
  intros. subst. rewrite [LHS](proj2 (proj2_sig Yoneda01_Form_F)).  apply: (proj2_sig (projT2 form')) .
  - symmetry. exact: polyGenerator_unitGenerator.
  - rewrite -H0. symmetry. simpl. exact: (proj2 (proj2_sig (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_Param_SubstF))).
Qed.   
  
Definition Yoneda01_Form_PiSubst : Yoneda01_data Yoneda00_Form_PiSubst.
Proof.
  unshelve eexists.
  - intros H H' h pf_.
    exists ( (Parameter1 h) o>Parametrizator_[sval Yoneda01_Param_PiSubstF] (projT1 pf_) ). unshelve eexists.
    + intros H'' h' s. 
      have [:proj2_sig_s0] @f_ :  Yoneda00_Form_F H''. refine (sval (sval (projT2 pf_ ) _ (h' o>Generator h) _)). 
      exists (sval s).  abstract: proj2_sig_s0. abstract (simpl; intros; rewrite Parameter_morphism;
                                                     rewrite -[RHS](proj1 (proj2_sig Yoneda01_Param_PiSubstF)); exact: (proj2_sig s)).
      exists (  f_ ) .
      abstract (exact: (proj2_sig (sval (projT2 pf_) _ (h' o>Generator h) (exist _ (sval s) proj2_sig_s0)))).
    + abstract (simpl; intros H'' h' s H''' h'' h''h' s_H''' Heq_arrow Heq_param;
      apply: (proj2_sig (projT2 pf_) (* unitGenerator *)) ;
        first (by rewrite [LHS]polyGenerator_morphism ; congr (_ o>Generator _) ; eassumption);
      simpl; eassumption).
  - abstract (split; [ simpl; intros G G' g G'' g' f_ ; apply: Yoneda00_Form_PiSubst_quotientLogical_ALT; simpl; intros;
      rewrite [LHS](proj2 (proj2_sig (Yoneda01_Form_F)));
      apply: (proj2_sig (projT2 f_) (* unitGenerator *));
        first (by rewrite -[in LHS]polyGenerator_unitGenerator; symmetry; exact: polyGenerator_morphism); 
        simpl; rewrite -[in LHS]Parameter_unitGenerator; rewrite -[in LHS](proj2 (proj2_sig Yoneda01_Param_SubstF)); assumption
     | intros G f_; apply: Yoneda00_Form_PiSubst_quotientLogical_ALT; simpl; intros;
      rewrite [LHS](proj2 (proj2_sig (Yoneda01_Form_F)));
      apply: (proj2_sig (projT2 f_) (* unitGenerator *));
      first (by rewrite -polyGenerator_unitGenerator; rewrite -unitGenerator_polyGenerator ; reflexivity);
      simpl; rewrite -[in LHS]Parameter_unitGenerator; rewrite -[in LHS](proj2 (proj2_sig Yoneda01_Param_SubstF)); assumption ] ) . 
Defined.

Definition Yoneda1_FormParam_PiSubst : Yoneda1_FormParam_data Yoneda01_Form_PiSubst Yoneda01_Param_PiSubstF.
Proof.
  unshelve eexists.
  - intros G psf_. exact: (projT1 psf_).
  - abstract (move; reflexivity).
Defined.

End PiSubst.

End Senses_obCoMod.
(** # #
#+END_SRC

** Finiteness of the viewing-elements of some viewing-functor

#+BEGIN_SRC coq :exports both :results silent # # **)
(** # #
#+END_SRC

** Grammar of the objects, which carry the sense-decodings


#+BEGIN_SRC coq :exports both :results silent # # **)

(** # #
#+END_SRC

* Grammatical presentation of morphisms

** Sense-decodings of the morphisms


#+BEGIN_SRC coq :exports both :results silent # # **)
Module Export Senses_morCoMod.

Section Yoneda1_Form_data.
Variables (Yoneda00_Form_E : obGenerator -> Type)
          (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
          (Yoneda00_Param_E : obGenerator -> Type)
          (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
          (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E).
Variables  (Yoneda00_Form_F : obGenerator -> Type)
           (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type)
           (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F).
Variables (Yoneda00_Param_E0' : obGenerator -> Type)
          (Yoneda01_Param_E0' : Yoneda01_Param_data Yoneda00_Param_E0').
Variables (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E).
Variables (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_F).

  Section Section1.
  Variables (Yoneda1_Form_ff : forall (G : obGenerator) (param : Yoneda00_Param_E0' G),
                Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_project param ->
                Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_subst param). 

  Definition Yoneda1_Form_natural
    := forall (G : obGenerator) (param : Yoneda00_Param_E0' G) (G' : obGenerator)
         (g : 'Generator( G' ~> G )) (form : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_project param),
      sval (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) Yoneda1_Param_subst)] (@Yoneda1_Form_ff G param form))
      = sval (@Yoneda1_Form_ff G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_E0'] param)
             (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_E) Yoneda1_Param_project)] form)) .

  (** /!\ YES /!\ *)
  
  Definition Yoneda1_Form_quotientLogical
    := forall (G : obGenerator) (param : Yoneda00_Param_E0' G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_project  param)
         (param' : Yoneda00_Param_E0' G) (form' : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_project param'),
      param = param' -> sval form = sval form' ->
      sval (@Yoneda1_Form_ff G param form) = sval (@Yoneda1_Form_ff G param' form') .
  End Section1.

Definition Yoneda1_Form_data :=
  { Yoneda1_Form : forall (G : obGenerator) (param : Yoneda00_Param_E0' G),
      Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_project param ->
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_subst param |
    Yoneda1_Form_natural Yoneda1_Form /\
    Yoneda1_Form_quotientLogical Yoneda1_Form } .

End Yoneda1_Form_data.

Definition Yoneda1_UnitCoMod_Param := Yoneda1_Param_Id.

Section Yoneda1_PolyCoMod_pseudoCode_ReParam.
  Variables (Yoneda00_Param_F : obGenerator -> Type)
            (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
            (Yoneda00_Param_F' : obGenerator -> Type)
            (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
            (Yoneda00_Param_F'F : obGenerator -> Type)
            (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F)
            (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
            (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F)
            (Yoneda00_Param_F'' : obGenerator -> Type)
            (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
            (Yoneda00_Param_F''F' : obGenerator -> Type)
            (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')
            (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'')
            (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F').

Definition Yoneda1_PolyCoMod_pseudoCode_ReParam_proj : Yoneda1_Param_data (Yoneda01_Param_Subst Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff_) Yoneda01_Param_F''.
Proof.
  exact: (Yoneda1_Param_PolyCoMod (Yoneda1_Param_Subst_proj Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff_) Yoneda1_Param_proj_ff_).
Defined.

Definition Yoneda1_PolyCoMod_pseudoCode_ReParam_subst : Yoneda1_Param_data (Yoneda01_Param_Subst Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff_) Yoneda01_Param_F.
Proof.
  exact: (Yoneda1_Param_PolyCoMod (Yoneda1_Param_Subst_subst Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff_) Yoneda1_Param_subst_ff').
Defined.

End Yoneda1_PolyCoMod_pseudoCode_ReParam.

Definition Yoneda1_PolyElement_pseudoCode_ReParam_default_proj :
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
    forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D),
    forall (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D),
    forall (G : obGenerator) (param : Yoneda00_Param_D G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) (Yoneda01_Param_View P).
Proof.
  intros; exact: (Yoneda1_Local_proj Yoneda1_Param_subst param is_Parameter0_P).
Defined.

Definition Yoneda1_PolyElement_pseudoCode_ReParam_default_subst :
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
    forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D),
    forall (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D),
    forall (G : obGenerator) (param : Yoneda00_Param_D G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) (Yoneda01_Param_SumImage Yoneda1_Param_subst).
Proof.
  unshelve eexists.
  - intros G' paramm. exists ((projT1 paramm) o>Parametrizator_[sval Yoneda01_Param_D] param).
    { (* logical part *) abstract (exact: (projT2 paramm)). }
  - abstract (move; intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl;
              rewrite (proj1 (proj2_sig Yoneda01_Param_D)); reflexivity).
Defined.

Definition Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' :
forall (Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D),
Yoneda1_Param_data (Yoneda01_Param_Sum Yoneda1_Param_subst) (Yoneda01_Param_SumImage Yoneda1_Param_subst).
Proof.
  unshelve eexists.
  - intros G paramm. exists (projT1 paramm).
    { (* logical part *) abstract (exact: (projT2 paramm)). }
  - abstract (move; intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; reflexivity).
Defined.

(**TODO: lemma Yoneda01_Form_SumSubst -> Yoneda01_Local_ *)
Definition Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' :
forall (Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee : forall (G : obGenerator) (paramlocal : Yoneda00_Param_D G),
     Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_E)
(Yoneda1_Param_ee_morphism :  forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )),
    forall paramlocal paramlocal' (Heqparamlocal : paramlocal' = (p o>Parametrizator_ paramlocal)),
    forall H param' param, param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) _ param' ->
  sval (Yoneda1_Param_ee G paramlocal) H param =
  sval (Yoneda1_Param_ee G' paramlocal') H param' ),
Yoneda1_Param_data (Yoneda01_Param_Sum Yoneda1_Param_subst) Yoneda01_Param_E.
Proof.
  intros.   unshelve eexists.
  - intros G f_d. refine (sval (Yoneda1_Param_ee G  (projT1 f_d)) _ _ ).
    exists unitParametrizator . apply: Yoneda01_Param_AtParam_transp; last (by  exact (projT2 f_d));
                             abstract(exact:(proj2 (proj2_sig Yoneda01_Param_D))).
  - abstract (move; simpl; intros; rewrite (proj2_sig (Yoneda1_Param_ee _  _)); simpl;
              apply Yoneda1_Param_ee_morphism with (Heqparamlocal:= eq_refl);
              simpl; apply: Yoneda00_Local_quotientLogical ; simpl;
              rewrite -polyParametrizator_unitParametrizator; rewrite [RHS]unitParametrizator_polyParametrizator; reflexivity) .
Defined. 

Definition Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj :
forall (Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee : forall (G : obGenerator) (paramlocal : Yoneda00_Param_D G),
     Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_E)
(Yoneda1_Param_ee_morphism :  forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )),
    forall paramlocal paramlocal' (Heqparamlocal : paramlocal' = (p o>Parametrizator_ paramlocal)),
    forall H param' param, param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) _ param' ->
  sval (Yoneda1_Param_ee G paramlocal) H param =
  sval (Yoneda1_Param_ee G' paramlocal') H param' )
(Yoneda00_Param_EE' : obGenerator -> Type) (Yoneda01_Param_EE' : Yoneda01_Param_data Yoneda00_Param_EE')
(Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_EE' Yoneda01_Param_E),
Yoneda1_Param_data (Yoneda01_Param_Subst Yoneda1_Param_proj_ee' (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)) (Yoneda01_Param_SumImage Yoneda1_Param_subst).
Proof.
  intros. exact (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (* viewedfunctor ( _ ) *)Yoneda1_Param_proj_ee' (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst)
                                                                  (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)).
Defined.

Definition Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst :
forall (Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee : forall (G : obGenerator) (paramlocal : Yoneda00_Param_D G),
     Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_E)
(Yoneda1_Param_ee_morphism :  forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )),
    forall paramlocal paramlocal' (Heqparamlocal : paramlocal' = (p o>Parametrizator_ paramlocal)),
    forall H param' param, param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) _ param' ->
  sval (Yoneda1_Param_ee G paramlocal) H param =
  sval (Yoneda1_Param_ee G' paramlocal') H param' )
(Yoneda00_Param_E' : obGenerator -> Type) (Yoneda01_Param_E' : Yoneda01_Param_data Yoneda00_Param_E') 
(Yoneda00_Param_EE' : obGenerator -> Type) (Yoneda01_Param_EE' : Yoneda01_Param_data Yoneda00_Param_EE')
(Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_EE' Yoneda01_Param_E)
(Yoneda1_Param_subst_ee' : Yoneda1_Param_data Yoneda01_Param_EE' Yoneda01_Param_E'),
  Yoneda1_Param_data (Yoneda01_Param_Subst Yoneda1_Param_proj_ee' (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)) Yoneda01_Param_E'.
Proof.
  intros. exact (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee' 
                                                                  (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism) ).
Defined.

Module Export Format.

Definition Repres0 : obGenerator -> obGenerator := fun A => A.
Parameter Repres1 : forall A A' : obGenerator,
    'Parametrizator( Parameter0 A ~> Parameter0 A')  -> 'Generator( (** Repres0 *) A ~> (** Repres0 *) A' ) .
Axiom Repres_morphism : 
  forall (A A' : obGenerator) (p' : 'Parametrizator( Parameter0 A' ~> Parameter0 A )) 
    (A'' : obGenerator) (p_ : 'Parametrizator( Parameter0 A'' ~> Parameter0 A' )),
    Repres1 ( p_ o>Parametrizator p' ) = ( Repres1 p_ ) o>Generator (Repres1 p').
Axiom Repres_unitGenerator :
  forall (A : obGenerator),
    (@unitGenerator A) = ( Repres1 (@unitParametrizator (Parameter0 A)) ) .
Axiom Repres_Parameter : forall A A' : obGenerator,
    forall (p : 'Parametrizator( Parameter0 A ~> Parameter0 A')),
  Parameter1 (Repres1 p) = p .
Definition Yoneda01_Param_of_Yoneda01_Form (Yoneda00_Form_F : obGenerator -> Type)
           (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) :
  Yoneda01_Param_data Yoneda00_Form_F .
Proof.
  unshelve eexists. intros G G' p. exact: (sval Yoneda01_Form_F G G' (Repres1 p)).
  abstract (split; simpl; intros; rewrite /Yoneda01_Param_action /= ;
    [ rewrite Repres_morphism [LHS](proj1 (proj2_sig Yoneda01_Form_F)); reflexivity
    | rewrite -Repres_unitGenerator [LHS](proj2 (proj2_sig Yoneda01_Form_F)); reflexivity ] ).
Defined.

Definition Yoneda1_Param_of_Yoneda1_FormParam  (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) :
  Yoneda1_Param_data (Yoneda01_Param_of_Yoneda01_Form Yoneda01_Form_F) Yoneda01_Param_F .
Proof.
  exists (sval Yoneda1_FormParam_F).
  abstract (move; simpl; intros G G' p f;
    rewrite [in RHS]/Yoneda01_Param_action [in RHS]/= ;
    rewrite -[RHS](proj2_sig Yoneda1_FormParam_F);
    rewrite [in RHS]/Yoneda01_action [in RHS]/= ;
    rewrite [in RHS] Repres_Parameter; reflexivity ).
Defined.

Section Section1.
Variables (Yoneda00_Form_F : obGenerator -> Type)
          (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
          (Yoneda00_Param_F : obGenerator -> Type)
          (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda1_FormParam_F : Yoneda1_Param_data (Yoneda01_Param_of_Yoneda01_Form Yoneda01_Form_F) Yoneda01_Param_F)
          (Yoneda00_Param_F' : obGenerator -> Type)
          (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
          (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_F' Yoneda01_Param_F).

(** objectwise/componentwise pullback in functor category *)
Definition Yoneda00_Param_Format : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { xf : Yoneda00_Param_F' H &
                                   Yoneda00_Param_AtParam_ Yoneda1_FormParam_F  (sval Yoneda1_Param_proj _ xf) } ).
Defined.

Axiom Yoneda00_Param_Format_quotientLogical :
  forall G (form form' : Yoneda00_Param_Format G), projT1 form = projT1 form' ->
                          (sval (projT2 form)) =  (sval (projT2 form')) -> form = form'.

Definition Yoneda01_Param_Format : Yoneda01_Param_data Yoneda00_Param_Format.
Proof.
  unshelve eexists.
  - intros H H' h xf.
    exists ( h o>Parametrizator_[sval Yoneda01_Param_F'] (projT1 xf)).
    apply: Yoneda01_Param_AtParam_transp; last (by  exact (h o>ParametrizatorAtParam_[sval (Yoneda01_Param_AtParam_ _ )] (projT2 xf)));
      abstract(exact:(proj2_sig Yoneda1_Param_proj)).
  - abstract (split; simpl;
    first (by intros; apply: Yoneda00_Param_Format_quotientLogical; simpl;
           [ rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_F')))
           | rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Param_of_Yoneda01_Form Yoneda01_Form_F)))]; reflexivity );
    intros H xf; apply: Yoneda00_Param_Format_quotientLogical; simpl;
      [ rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_F')))
      | rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_of_Yoneda01_Form Yoneda01_Form_F))) ]; reflexivity).
Defined.

Definition Yoneda1_Param_Format_param : Yoneda1_Param_data Yoneda01_Param_Format Yoneda01_Param_F'.
Proof.
  unshelve eexists.
  - intros G xf. exact: (projT1 xf).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda1_Param_Format_form : Yoneda1_Param_data Yoneda01_Param_Format (Yoneda01_Param_of_Yoneda01_Form Yoneda01_Form_F).
Proof.
  unshelve eexists.
  - intros G xf. exact: (sval (projT2 xf)).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda1_Param_Format : Yoneda1_Param_data Yoneda01_Param_Format Yoneda01_Param_F.
Proof.
  unshelve eexists.
  - intros G xf. exact: (sval Yoneda1_Param_proj _ (projT1 xf )).
  - abstract (move; simpl; intros; apply: (proj2_sig Yoneda1_Param_proj)).
Defined.
End Section1.

Definition Yoneda1_Param_Format_subst :
forall (Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst),
  Yoneda1_Param_data (Yoneda01_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_E) Yoneda1_Param_proj)
               (Yoneda01_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_F) (Yoneda1_Param_Id Yoneda01_Param_F)).
Proof.
  unshelve eexists.
  - intros G e_ef. unshelve eexists.
    + refine (sval Yoneda1_Param_subst G _ ) ;  exact: (sval (Yoneda1_Param_Format_param _ _ ) _ e_ef).
    + unshelve eexists.
      * refine (sval (sval Yoneda1_Form_ff G  (sval (Yoneda1_Param_Format_param _ _ ) _ e_ef)  _ )).
        { exists (sval (Yoneda1_Param_Format_form _ _ ) _ e_ef).
          abstract (simpl; exact: (proj2_sig (projT2 e_ef))).
        }
      * abstract (simpl; exact: (proj2_sig (sval Yoneda1_Form_ff G  (sval (Yoneda1_Param_Format_param _ _ ) _ e_ef)  _ ))).
  - abstract (move; simpl; intros; apply: Yoneda00_Param_Format_quotientLogical; simpl; [
      exact: (proj2_sig Yoneda1_Param_subst )
    | rewrite [LHS](proj1 (proj2_sig Yoneda1_Form_ff)) ;  simpl; 
      apply (proj2 (proj2_sig Yoneda1_Form_ff)) ; simpl; last (by reflexivity);
      simpl; rewrite Repres_Parameter; reflexivity ] ).
Defined.

End Format.

(** -----OLD POSITION OF obCoMoD -------------*)

Section reparamMor .
  Variables  (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
             (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda00_Param_E0' : obGenerator -> Type) (Yoneda01_Param_E0' : Yoneda01_Param_data Yoneda00_Param_E0')
             (Yoneda1_Param_project_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_F)
             (Yoneda00_Param_E0'' : obGenerator -> Type) (Yoneda01_Param_E0'' : Yoneda01_Param_data Yoneda00_Param_E0'')
             (Yoneda1_Param_project_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_F).

  Definition reparamMor_prop (Yoneda1_Param_reparam : (Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E0''))
    := (forall G param, (sval Yoneda1_Param_project_E0'' G) ((sval Yoneda1_Param_reparam G) param)
                   = (sval Yoneda1_Param_project_E0' G) param) /\
       (forall G param, (sval Yoneda1_Param_subst_E0'' G) ((sval Yoneda1_Param_reparam G) param)
                   = (sval Yoneda1_Param_subst_E0' G) param) .

  Definition reparamMor := { Yoneda1_Param_reparam : (Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E0'')
                           | reparamMor_prop Yoneda1_Param_reparam }.

  Section Section1.
    Variables (Yoneda00_Form_E : obGenerator -> Type)
              (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
              (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E).
    Variables  (Yoneda00_Form_F : obGenerator -> Type)
               (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
               (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F).

    Definition reparamMor_Form : reparamMor
                                 ->  Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''
                                 ->  Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0' .
    Proof.
      intros reparam ff . unshelve eexists.
      - intros G param form. unshelve eexists.
        refine (sval (sval ff G (sval (sval reparam) G param) _ )).
        + exists (sval form).
          abstract (rewrite [RHS](proj1 (proj2_sig reparam)); exact: (proj2_sig form)).
        + abstract (simpl; rewrite [LHS](proj2_sig (sval ff G (sval (sval reparam) G param) _));
                    rewrite [LHS](proj2 (proj2_sig reparam)); reflexivity).
      - abstract (split;
        [ (move; simpl; intros; rewrite [LHS](proj1 (proj2_sig ff));
                    apply: (proj2 (proj2_sig ff)); simpl; first exact: (proj2_sig (sval reparam)); reflexivity)
        | (move; simpl; intros; apply (proj2 (proj2_sig ff)); simpl; last assumption ;
                    subst; reflexivity) ] ).
    Defined.
    
    End Section1.
    
End reparamMor.

Section reparamMorSym.
  Variables  (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
             (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda00_Param_E0' : obGenerator -> Type) (Yoneda01_Param_E0' : Yoneda01_Param_data Yoneda00_Param_E0')
             (Yoneda1_Param_project_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_F)
             (Yoneda00_Param_E0'' : obGenerator -> Type) (Yoneda01_Param_E0'' : Yoneda01_Param_data Yoneda00_Param_E0'')
             (Yoneda1_Param_project_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_F).

  Definition reparamMorSym_prop (Yoneda1_Param_reparam : (Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E0''))
             (Yoneda1_Param_reparam_rev : (Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_E0'))
    := (forall G param, (sval Yoneda1_Param_reparam_rev G) ((sval Yoneda1_Param_reparam G) param)
                   = (sval (Yoneda1_Param_Id Yoneda01_Param_E0') G param)) /\
       (forall G param, (sval Yoneda1_Param_reparam G) ((sval Yoneda1_Param_reparam_rev G) param)
                   = (sval (Yoneda1_Param_Id Yoneda01_Param_E0'') G param)) .

  Definition reparamMorSym := { reparam_reparam_rev : reparamMor Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0'
                                                      Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0'' *
                                                      reparamMor Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''
                                                                 Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0'
                              | reparamMorSym_prop (sval (fst reparam_reparam_rev)) (sval (snd reparam_reparam_rev)) } .

  Definition Coh_reparamMorSym (Yoneda1_Param_reparam_rr Yoneda1_Param_reparam_rr0 : reparamMorSym) :=
    forall G param , sval (sval (fst (sval Yoneda1_Param_reparam_rr))) G param = sval (sval (fst (sval Yoneda1_Param_reparam_rr0))) G param.

  Section Section1.
    Variables (Yoneda00_Form_E : obGenerator -> Type)
              (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
              (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E).
    Variables  (Yoneda00_Form_F : obGenerator -> Type)
               (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
               (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F).

    (*TODO: OLD ERASE, USE ALT
      Lemma reparamMor_Form_Sym : forall reparam : reparamMorSym,
        forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0' )
          (Yoneda1_Form_ff'' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''),
          ( forall G param form, sval (sval (reparamMor_Form (snd (sval reparam)) Yoneda1_Form_ff') G param form)
                            = sval (sval Yoneda1_Form_ff'' G param form) )
          -> ( forall G param form, sval (sval (reparamMor_Form (fst (sval reparam)) Yoneda1_Form_ff'') G param form)
                               = sval (sval Yoneda1_Form_ff' G param form) ).
    Proof.
      abstract(simpl; intros ? ? ? Heq *; rewrite -[LHS]Heq;
               apply: (proj2 (proj2_sig  Yoneda1_Form_ff')); simpl;
               [ rewrite (proj1 (proj2_sig reparam)); reflexivity | reflexivity ] ).
    Qed. *)

    Lemma reparamMor_Form_Sym' : forall reparam : reparamMorSym,
        forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0' )
          (Yoneda1_Form_ff'' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''),
          ( forall G param form, sval (sval (reparamMor_Form (fst (sval reparam)) Yoneda1_Form_ff'') G param form)
                            = sval (sval Yoneda1_Form_ff' G param form) ) ->
          ( forall G param form, sval (sval (reparamMor_Form (snd (sval reparam)) Yoneda1_Form_ff') G param form)
                            = sval (sval Yoneda1_Form_ff'' G param form) ).
    Proof.
      abstract(simpl; intros ? ? ? Heq *; rewrite -[LHS]Heq;
               apply: (proj2 (proj2_sig  Yoneda1_Form_ff'')); simpl;
               [ rewrite (proj2 (proj2_sig reparam)); reflexivity | reflexivity ] ).
    Qed.

  End Section1.

  Definition reparamMorSymGenerator (G' G : obGenerator) 
    := { reparam_reparam_rev : 'Generator( G' ~> G ) * 'Generator( G ~> G' )
       | ((fst reparam_reparam_rev) o>Generator (snd reparam_reparam_rev) = unitGenerator) /\
         ((snd reparam_reparam_rev) o>Generator (fst reparam_reparam_rev) = unitGenerator) } .

  Definition unitGenerator_reparamMorSymGenerator (G : obGenerator) : reparamMorSymGenerator G G.
    intros. unshelve eexists. split. 
    exact: unitGenerator.
    exact: unitGenerator.
    abstract (split; simpl; rewrite -unitGenerator_polyGenerator; reflexivity).
  Defined. 

End reparamMorSym.

Section reparamMorSym_Sym.
  Variables  (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
             (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda00_Param_E0' : obGenerator -> Type) (Yoneda01_Param_E0' : Yoneda01_Param_data Yoneda00_Param_E0')
             (Yoneda1_Param_project_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_F)
             (Yoneda00_Param_E0'' : obGenerator -> Type) (Yoneda01_Param_E0'' : Yoneda01_Param_data Yoneda00_Param_E0'')
             (Yoneda1_Param_project_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_E)
             (Yoneda1_Param_subst_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_F).

  Definition reparamMorSym_Sym : reparamMorSym Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0'
                                               Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0'' 
                                 -> reparamMorSym Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''
                                                  Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0' .
  Proof.
    intros reparam. unshelve eexists. split.
    - exact: (snd (sval reparam)).
    - exact: (fst (sval reparam)).
    - abstract (split; [ simpl; intros; exact: (proj2 (proj2_sig reparam))
             | simpl; intros; exact: (proj1 (proj2_sig reparam)) ] ).
  Defined. 
End reparamMorSym_Sym.

Section Yoneda00_Local_quotientLogical_reparamMorSym.
             
Variables (G : obGenerator) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
          (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
          (Yoneda00_Param_E0' : obGenerator -> Type) (Yoneda01_Param_E0' : Yoneda01_Param_data Yoneda00_Param_E0')
          (Yoneda1_Param_project_E0' : Yoneda1_Param_data Yoneda01_Param_E0' (Yoneda01_Param_View P))
          (Yoneda1_Param_subst_E0' : Yoneda1_Param_data Yoneda01_Param_E0' Yoneda01_Param_F).

Variables (Yoneda00_Param_SumSubstF : obGenerator -> Type)
          (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
          (Yoneda00_Param_SubstF : obGenerator -> Type)
           (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
           (paramlocal : Yoneda00_Param_SumSubstF G).
           

Let Yoneda00_Param_E0'' : obGenerator -> Type :=
       (Yoneda00_Local_ Yoneda1_Param_subst paramlocal).
Let Yoneda01_Param_E0'' : Yoneda01_Param_data Yoneda00_Param_E0'' :=
  (Yoneda01_Local_ Yoneda1_Param_subst paramlocal).
Let Yoneda1_Param_project_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' (Yoneda01_Param_View P)  :=
  (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P).
  
Variables (Yoneda1_Param_subst_E0'' : Yoneda1_Param_data Yoneda01_Param_E0'' Yoneda01_Param_F).
Variables (reparam : reparamMorSym Yoneda1_Param_project_E0'' Yoneda1_Param_subst_E0''
                                             Yoneda1_Param_project_E0' Yoneda1_Param_subst_E0').

Lemma Yoneda00_Local_quotientLogical_reparamMorSym :
  forall (G' : obGenerator) (param param' : Yoneda00_Param_E0' G'),
    sval Yoneda1_Param_project_E0' G' param = sval Yoneda1_Param_project_E0' G' param' -> param  = param' . 
Proof.
  intros. rewrite -[LHS](proj2 (proj2_sig reparam)). rewrite -[RHS](proj2 (proj2_sig reparam)).
  congr (sval _ _ _). apply: Yoneda00_Local_quotientLogical.
  rewrite [LHS]unitParametrizator_polyParametrizator.
  rewrite -[in LHS](proj1 (proj2_sig is_Parameter0_P)). rewrite [LHS]polyParametrizator_morphism.
  rewrite [RHS]unitParametrizator_polyParametrizator.
  rewrite -[in RHS](proj1 (proj2_sig is_Parameter0_P)). rewrite [RHS]polyParametrizator_morphism.
  congr ( _ o>Parametrizator _).
  rewrite [LHS](proj1 (proj2_sig (snd (sval reparam)))).
  rewrite [RHS](proj1 (proj2_sig (snd (sval reparam)))). assumption.
Qed.

End Yoneda00_Local_quotientLogical_reparamMorSym.

Section Assoc_reparam.
Variables (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(Yoneda00_Param_C : obGenerator -> Type)
(Yoneda01_Param_C : Yoneda01_Param_data Yoneda00_Param_C)
(Yoneda00_Param_CD : obGenerator -> Type)
(Yoneda01_Param_CD : Yoneda01_Param_data Yoneda00_Param_CD)
(Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_C)
(Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_D).
  
Definition reparamMorSym_Assoc_reparam :
 reparamMorSym
   (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
      Yoneda1_Param_proj_dd
      Yoneda1_Param_subst_dd)
   (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) 
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_subst_ee)
      Yoneda1_Param_subst_dd)

   (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff                                
                                              (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
                                              (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_subst_dd))
   (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff
                                               Yoneda1_Param_subst_ff
                                               (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_subst_dd)).
Proof. fold Yoneda1_PolyCoMod_pseudoCode_ReParam_proj.
  unshelve eexists.
  - split.
    { unshelve eexists.
      - unshelve eexists.
        + intros G cd__de_ef. unshelve eexists. 
          * exists ( projT1 cd__de_ef) . exists (projT1 (sval (projT2 cd__de_ef))) .
            abstract (simpl; exact: (proj2_sig (projT2 cd__de_ef))).
          * exists (sval (projT2 (sval (projT2 cd__de_ef)))).
            abstract (simpl; exact: (proj2_sig (projT2 (sval (projT2 cd__de_ef))))).
        + abstract (move; simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
                    [ apply: Yoneda00_Param_Subst_quotientLogical; simpl; reflexivity 
                    | reflexivity ]) .
      - abstract (split; [reflexivity | split; reflexivity]).
    }
    { unshelve eexists.
      - unshelve eexists.
        + intros G cd_de__ef. unshelve eexists. 
          * exact: (projT1 (projT1 cd_de__ef)).
          * unshelve eexists.
            exists ( sval (projT2 (projT1 cd_de__ef))).
            exact: (projT2 cd_de__ef).
            abstract (simpl; exact: (proj2_sig (projT2 (projT1 cd_de__ef)))).
        + abstract (move; simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
                    [ reflexivity
                    | apply: Yoneda00_Param_Subst_quotientLogical; simpl; reflexivity ]).
      - abstract (split; [reflexivity | split; reflexivity]).
    } 
  - abstract( split; [ simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl; first reflexivity;
      apply: Yoneda00_Param_Subst_quotientLogical; simpl; reflexivity
    | simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl; last reflexivity;
      apply: Yoneda00_Param_Subst_quotientLogical; simpl; reflexivity ] ).
Defined.
End Assoc_reparam.

Definition reparamMor_Trans :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda00_Param_EF0 : obGenerator -> Type)
(Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
(Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr0 : reparamMor Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
(Yoneda00_Param_EF1 : obGenerator -> Type)
(Yoneda01_Param_EF1 : Yoneda01_Param_data Yoneda00_Param_EF1)
(Yoneda1_Param_proj_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr1 : reparamMor Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1),
reparamMor Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1 .
Proof.
  intros. exists (Yoneda1_Param_PolyCoMod (sval Yoneda1_Param_reparam_rr0) (sval Yoneda1_Param_reparam_rr1)) .
  abstract ( split; [ intros; simpl; rewrite [LHS](proj1 (proj2_sig Yoneda1_Param_reparam_rr1)) [LHS](proj1 (proj2_sig Yoneda1_Param_reparam_rr0)); reflexivity
                  | intros; simpl; rewrite [LHS](proj2 (proj2_sig Yoneda1_Param_reparam_rr1)) [LHS](proj2 (proj2_sig Yoneda1_Param_reparam_rr0)); reflexivity ] ) .
Defined.

Definition reparamMorSym_Trans :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda00_Param_EF0 : obGenerator -> Type)
(Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
(Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr0 : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
(Yoneda00_Param_EF1 : obGenerator -> Type)
(Yoneda01_Param_EF1 : Yoneda01_Param_data Yoneda00_Param_EF1)
(Yoneda1_Param_proj_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr1 : reparamMorSym Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1),
reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1 .
Proof.
  intros. unshelve eexists. split.
  - apply: reparamMor_Trans . exact: (fst (sval Yoneda1_Param_reparam_rr0)).  exact: (fst (sval Yoneda1_Param_reparam_rr1)).
  - apply: reparamMor_Trans . exact: (snd (sval Yoneda1_Param_reparam_rr1)).  exact: (snd (sval Yoneda1_Param_reparam_rr0)).
  - abstract (split; [simpl; intros; rewrite (fst (proj2_sig  Yoneda1_Param_reparam_rr1)) (fst (proj2_sig  Yoneda1_Param_reparam_rr0)); reflexivity
           | simpl; intros; rewrite (snd (proj2_sig  Yoneda1_Param_reparam_rr0)) (snd (proj2_sig  Yoneda1_Param_reparam_rr1)); reflexivity ] ) . 
Defined.
  
Definition reparamMorSym_Refl :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E )
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff  .
Proof.
  intros. unshelve eexists. split.
  - { exists (Yoneda1_Param_Id _) .
      abstract (split; reflexivity).
    } 
  - { exists (Yoneda1_Param_Id _) .
      abstract (split; reflexivity).
    } 
  - abstract (split; reflexivity). 
Defined.

Definition reparamMor_PolyCoMod_pseudoCode_ReParam_cong :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda00_Param_EF0 : obGenerator -> Type)
(Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
(Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr : reparamMor Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(Yoneda00_Param_DE0 : obGenerator -> Type)
(Yoneda01_Param_DE0 : Yoneda01_Param_data Yoneda00_Param_DE0)
(Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_D)
(Yoneda1_Param_subst_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_E)
(Yoneda1_Param_reparam_qq : reparamMor Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0),
 reparamMor (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_subst_ee)
    (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff0 Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0)
    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 Yoneda1_Param_subst_ee0).
Proof.
  intros. exists (Yoneda1_Param_Subst1 (proj1 (proj2_sig Yoneda1_Param_reparam_rr)) (proj2 (proj2_sig Yoneda1_Param_reparam_qq)) ) . 
  abstract (split; [ simpl; intros; exact: (proj1 (proj2_sig (Yoneda1_Param_reparam_qq)))
                   | simpl; intros; exact: (proj2 (proj2_sig (Yoneda1_Param_reparam_rr))) ] ).
Defined.

Definition reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Yoneda00_Param_EF0 : obGenerator -> Type)
(Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
(Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
(Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
(Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(Yoneda00_Param_DE0 : obGenerator -> Type)
(Yoneda01_Param_DE0 : Yoneda01_Param_data Yoneda00_Param_DE0)
(Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_D)
(Yoneda1_Param_subst_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_E)
(Yoneda1_Param_reparam_qq : reparamMorSym Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0),
reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
              (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_subst_ee)
              (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff0 Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0)
    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 Yoneda1_Param_subst_ee0).
Proof.
  unshelve eexists. split. 
  - apply: reparamMor_PolyCoMod_pseudoCode_ReParam_cong. exact: (fst (sval Yoneda1_Param_reparam_rr)). exact: (fst (sval Yoneda1_Param_reparam_qq)).
  - apply: reparamMor_PolyCoMod_pseudoCode_ReParam_cong.  exact: (snd (sval Yoneda1_Param_reparam_rr)). exact: (snd (sval Yoneda1_Param_reparam_qq)).
  - abstract (split; [ simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
             [ rewrite (proj1 (proj2_sig  Yoneda1_Param_reparam_qq)); simpl; reflexivity
             | rewrite (proj1 (proj2_sig  Yoneda1_Param_reparam_rr)); simpl; reflexivity ]
           | simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
             [ rewrite (proj2 (proj2_sig  Yoneda1_Param_reparam_qq)); simpl; reflexivity
             | rewrite (proj2 (proj2_sig  Yoneda1_Param_reparam_rr)); simpl; reflexivity ] ] ).
Defined.

(** Definition reparamMorSym_UnitViewedFunctor_pseudoCode_ReParam_default_cong : *)


Definition Yoneda1_Param_PolyTransf_default_quotientLogical : 
forall (Yoneda00_Param_SumSubstF : obGenerator -> Type)
(Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E),
  
   forall (G : obGenerator) (paramlocal paramlocal' : Yoneda00_Param_SumSubstF G) (H : obGenerator)
     (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H)
     (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
     (Heqparamlocal : paramlocal = paramlocal') (Heqparam : projT1 param = projT1 param'),
     sval (Yoneda1_Param_ee G paramlocal) H param =
     sval (Yoneda1_Param_ee G paramlocal') H param' .
Proof.
  intros. subst.
  have Heqparam' :  param =  param'. apply: Yoneda00_Local_quotientLogical. assumption.
  subst. reflexivity.
Qed.

Definition reparamMorSym_PolyTransf_pseudoCode_ReParam_default_cong
(Yoneda00_Param_SumSubstF : obGenerator -> Type)
(Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
(Yoneda1_Param_ee_morphism :
forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
  (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H) (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_ee G paramlocal) H param = sval (Yoneda1_Param_ee G' paramlocal') H param')
(Yoneda1_Param_dd : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
(Yoneda1_Param_dd_morphism :
forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
  (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H) (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_dd G paramlocal) H param = sval (Yoneda1_Param_dd G' paramlocal') H param')
(Yoneda1_Param_reparam_eedd_ :
forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee G paramlocal) (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P)
  (Yoneda1_Param_dd G paramlocal)) :  
reparamMorSym (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst) (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)
    (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst) (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_dd_morphism).           
Proof.
  unshelve eexists. split. 
  - unshelve eexists. exact: (Yoneda1_Param_Id _). split.
    + abstract(simpl;intros; reflexivity).
    + abstract(intros G paramsum; simpl; rewrite -[RHS](proj2 (proj2_sig (fst (sval (Yoneda1_Param_reparam_eedd_ G (projT1 paramsum) _ (unitParametrizator_reparamMorSymParametrizator _))))));
      apply: (Yoneda1_Param_PolyTransf_default_quotientLogical Yoneda1_Param_dd); first reflexivity;
      simpl; rewrite [RHS]unitParametrizator_polyParametrizator; rewrite [RHS](proj1 (proj2_sig (fst (sval (Yoneda1_Param_reparam_eedd_ G (projT1 paramsum) _ (unitParametrizator_reparamMorSymParametrizator _)))))); simpl; rewrite -[RHS]unitParametrizator_polyParametrizator; reflexivity).
  - unshelve eexists. exact: (Yoneda1_Param_Id _). split.
    + abstract(simpl;intros; reflexivity).
    + abstract(intros G paramsum; simpl; rewrite -[RHS](proj2 (proj2_sig (snd (sval (Yoneda1_Param_reparam_eedd_ G (projT1 paramsum) _ (Is_Parameter0 _))))));
      apply: (Yoneda1_Param_PolyTransf_default_quotientLogical Yoneda1_Param_ee); first reflexivity;
      simpl; rewrite [RHS]unitParametrizator_polyParametrizator; rewrite [RHS](proj1 (proj2_sig (snd (sval (Yoneda1_Param_reparam_eedd_ G (projT1 paramsum) _ (Is_Parameter0 _)))))); simpl; rewrite -[RHS]unitParametrizator_polyParametrizator; reflexivity).
  - abstract(split; reflexivity).
Defined.

Lemma reparamMorSym_PolyElement_ReParam_default_comp_PolyTransf_ReParam_default :
 forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda00_Param_SubstF : obGenerator -> Type)
           (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Yoneda00_Param_K : obGenerator -> Type)
           (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
           (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
           (Yoneda1_Param_ee_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                               (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                               (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
               param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' ->
               sval (Yoneda1_Param_ee_ G paramlocal) H param = sval (Yoneda1_Param_ee_ G' paramlocal') H param') (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
           (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
      reparamMorSym
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst)
                                                   (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst paramlocal))
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst) (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)
                                                    (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst paramlocal))
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (Yoneda1_UnitCoMod_Param Yoneda01_Param_K) (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst (Yoneda1_UnitCoMod_Param Yoneda01_Param_K) (Yoneda1_UnitCoMod_Param Yoneda01_Param_K) (Yoneda1_Param_ee_ G paramlocal)).
Proof.
  unshelve eexists. split.
  - unshelve eexists.
    + unshelve eexists.
      * { intros G' param'_param''. unshelve eexists.
          - exists (sval (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj _ _ (Is_Parameter0 _))  _
                    (sval (Yoneda1_Param_Subst_proj _ _ ) _  param'_param'') ).
            (**TODO: add and use Yoneda1_Param_Sum_*)
            (*TODO: logical part starts here , but why necessary to be transparent in the first line  ...
              hmm OK to be transparent for the first line if no use the projT2 of another Local (the local here is projT1 param'_param'') .
              In short : any such use of projT2 of another Local shall be under abstract *)
            simpl; exists ( sval (Yoneda1_Param_Sum_subst _ ) _ (sval (Yoneda1_Param_Subst_subst _ _ ) _  param'_param'')).
            abstract (simpl; rewrite [LHS](proj2_sig (projT2 (sval (projT2 param'_param'')))); simpl;
              rewrite -[in RHS]unitParametrizator_polyParametrizator;
            rewrite -[RHS](f_equal (@projT1 _ _) (proj2_sig (projT2 param'_param''))); simpl; reflexivity).
          - exact: Yoneda00_Param_AtParam_self.
        }
      * { abstract (move; simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
          [ apply: Yoneda00_Local_quotientLogical; simpl; do 2 rewrite -unitParametrizator_polyParametrizator; reflexivity
          | rewrite (proj2_sig (Yoneda1_Param_ee_ _ _)); congr (sval _ _ _);
            apply: Yoneda00_Local_quotientLogical; simpl; do 2 rewrite -unitParametrizator_polyParametrizator; reflexivity ] ).
        }
    + abstract (split; simpl; intros G' param; first (simpl; do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity);
        simpl; intros; unshelve eapply Yoneda1_Param_ee_morphism with (p := (projT1 (projT1 param)));
          first (by exact: (f_equal (@projT1 _ _) (proj2_sig (projT2 param))));
          simpl; apply: Yoneda00_Local_quotientLogical; simpl; do 1 rewrite -unitParametrizator_polyParametrizator;
            exact: polyParametrizator_unitParametrizator) .
  - unshelve eexists.
    + unshelve eexists.
      * intros G' param' . exists (sval (Yoneda1_Param_Subst_proj _ _ ) _ param') . simpl.
        { unshelve eexists.
          exists (sval (Yoneda1_Local _ _) _ (sval (Yoneda1_Param_Subst_proj _ _ ) _ param')).
          exact: (projT2 (sval (Yoneda1_Param_Subst_proj _ _ ) _ param')).
          abstract (intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; reflexivity).
        }
      * abstract ( move; simpl; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl ; first reflexivity;
          apply: Yoneda00_Param_Sum_quotientLogical; simpl;
            [ rewrite [LHS](proj1 (proj2_sig Yoneda01_Param_SumSubstF)); reflexivity
            | reflexivity ] ) .
    + abstract (split; simpl; intros; first (by reflexivity);
                simpl; intros; rewrite [RHS](proj2_sig (projT2 param)); symmetry;
                unshelve eapply Yoneda1_Param_ee_morphism with (Heqparamlocal := eq_refl); simpl;
                apply: Yoneda00_Local_quotientLogical; simpl;
                exact: polyParametrizator_unitParametrizator) .
  - (*abstract*) (split; simpl; intros G0 param0;
    [ apply: Yoneda00_Param_Subst_quotientLogical; simpl;
      [ apply: Yoneda00_Local_quotientLogical; simpl;  do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity
      |  apply: Yoneda00_Param_Sum_quotientLogical; simpl;
        [  do 1 rewrite -unitParametrizator_polyParametrizator; symmetry; exact: (f_equal (@projT1 _ _) (proj2_sig (projT2 param0)))
        | (*MEMO: this require the first line of the logical part above to be transparent*) reflexivity ]  ]
    | apply: Yoneda00_Param_Subst_quotientLogical; simpl;
      [ apply: Yoneda00_Local_quotientLogical; simpl;  do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity
      | rewrite [RHS](proj2_sig (projT2 param0)); simpl;
        congr (sval _ _ _);
        apply: Yoneda00_Local_quotientLogical; simpl;  do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity ] ] ) .
Defined.

Definition Yoneda1_Form_PolyElement_default :
  forall (Yoneda00_Form_F : obGenerator -> Type)
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
  forall (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF),
  forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF),
  forall (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF),
  forall (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F),
  forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
 Yoneda1_Form_data (Yoneda1_FormParam_View G) (Yoneda1_FormParam_SumSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)
    (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
    (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)).
Proof.
  unshelve eexists.
  - intros H param' g. unshelve eexists.
    + unshelve eexists. 
      * exact: ((Parameter1 (sval g)) o>Parametrizator_[sval Yoneda01_Param_SumSubstF] (sval Yoneda1_Param_subst G param)).
      * unshelve eexists. exists ((Parameter1 (sval g)) o>Parametrizator_[sval Yoneda01_Param_SubstF] param).
        abstract (simpl; symmetry; exact: (proj2_sig Yoneda1_Param_subst)).
        simpl. exact: ((sval g) o>GeneratorAtParam_[sval (Yoneda01_AtParam_ _ _ )] form).
    + abstract (apply: Yoneda00_Param_SumImage_quotientLogical; simpl; rewrite [Parameter1 _](proj2_sig g); simpl; do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity).
  - abstract(split; move; simpl; intros;
    [ apply: Yoneda00_Form_SumSubst_quotientLogical; simpl;
      [ reflexivity
      | rewrite [in RHS]Parameter_morphism; exact: (proj1 (proj2_sig Yoneda01_Param_SubstF))
      | exact: (proj1 (proj2_sig Yoneda01_Form_F)) ]
    | apply: Yoneda00_Form_SumSubst_quotientLogical; simpl;
      [ reflexivity
      | congr ( _ o>Parametrizator_ _); first congr Parameter1; assumption
      | congr ( _ o>Generator_ _); assumption ] ] ) .
Defined.

Definition Yoneda1_reparam_PolyTransf_default_quotientLogical : 
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_SumSubstF : obGenerator -> Type)
(Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_Param_ee0 : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
(Yoneda1_Param_ee :
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
  Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param ->
  Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_E)
(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
    reparamMor (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee0 G (sval Yoneda1_Param_subst G param))
                  (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee G param form)),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) ,
    forall (param' : Yoneda00_Param_SubstF G) (form' : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param'),
    forall (Heqparam : param = param') (Heqform : sval form = sval form'),
    forall G' (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G')
      (paramm' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param') G'),
    forall (Heqparamm : projT1 paramm = projT1 paramm'),
      projT1 (sval (sval (Yoneda1_Param_reparam_ee_ G param  form) ) G' paramm)
      = projT1 (sval (sval (Yoneda1_Param_reparam_ee_ G param'  form') ) G' paramm') .
Proof.
  intros. subst.
  have Heqform' : form = form'. apply: Yoneda00_AtParam_quotientLogical. assumption.
  subst.
  have Heqparamm' :  paramm =  paramm'.  apply: Yoneda00_Local_quotientLogical. assumption.
  subst. reflexivity.
Qed.

Definition Yoneda1_Form_PolyTransf_default_quotientLogical : 
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_SumSubstF : obGenerator -> Type)
(Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(Yoneda1_Param_ee :
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
  Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param ->
  Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_E)
(Yoneda1_Form_ee :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee G param form)),

forall G (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (param' : Yoneda00_Param_SubstF G) (form' : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param'),
forall (Heqparam : param = param') (Heqform : sval form = sval form'),
forall (G0 : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G0)
  (formm : 'Generator ( G0 ~> G @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G) <| paramm ))
  (paramm' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param') G0)
  (formm' : 'Generator ( G0 ~> G @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param') (Is_Parameter0 G) <| paramm' )),
forall (Heqparamm : projT1 paramm = projT1 paramm') (Heqformm : sval formm = sval formm'),
  sval (sval (Yoneda1_Form_ee G param form) G0 paramm formm) =
  sval (sval (Yoneda1_Form_ee G param' form') G0 paramm' formm').
Proof.
  intros. subst.
  have Heqform' : form = form'. apply: Yoneda00_AtParam_quotientLogical. assumption.
  subst.
  have Heqparamm' :  paramm =  paramm'. apply: Yoneda00_Local_quotientLogical. assumption.
  subst.
  have Heqformm' : formm =  formm'.  apply: Yoneda00_AtParam_quotientLogical. assumption.
  subst. reflexivity.
Qed.

(*TODO: MOVE UP*)
Lemma Yoneda01_AtParam_transp'' (*TODO: DO Yoneda01_AtParam_transp''_prop *)
     : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_F0' : obGenerator -> Type) (Yoneda01_Param_F0' : Yoneda01_Param_data Yoneda00_Param_F0')
         (Yoneda1_Param_project : Yoneda1_Param_data Yoneda01_Param_F0' Yoneda01_Param_F)
         (Yoneda00_Param_F0'' : obGenerator -> Type) (Yoneda01_Param_F0'' : Yoneda01_Param_data Yoneda00_Param_F0'')
         (Yoneda1_Param_project' : Yoneda1_Param_data Yoneda01_Param_F0'' Yoneda01_Param_F)
         (G : obGenerator) (param : Yoneda00_Param_F0' G) ( param' : Yoneda00_Param_F0'' G),
       sval Yoneda1_Param_project G param = sval Yoneda1_Param_project' G param' ->
       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project param -> Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_project' param' .
  Proof. 
    (** /!\ NO! intros until 1; subst; exact: id. Defined. /!\ **)
    intros ? ? ? ? ? ? ?  ? ? ? ? ? ? ? Heq form. exists (sval form).
    abstract (simpl; rewrite  (proj2_sig form); assumption).
    (*  abstract (simpl; subst; exact: (proj2_sig form)). *)
  Defined.

  (*TODO: MOVE UP, next to Form_PolyTransf *)  Lemma Form_morphism_Heq:
   forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda00_Param_SubstF : obGenerator -> Type)
          (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (G G' : obGenerator)
          (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G) (G'' : obGenerator)
          (paramlocal : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'')
          (paramlocal' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G''
           := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramlocal),
     sval (Yoneda1_Param_PolyCoMod (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_[sval Yoneda01_Param_SubstF] param)) (Is_Parameter0 G')) (Yoneda1_Param_View1 (Parameter1 g))) G''
          paramlocal = sval (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) G'' paramlocal'.
 Proof.
   intros. simpl.  do 2 rewrite -unitParametrizator_polyParametrizator; reflexivity.
   Qed.
  
Definition Yoneda1_Form_PolyTransf_default : 
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_SumSubstF : obGenerator -> Type)
(Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(Yoneda1_Param_ee0 : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
(Yoneda1_Param_ee0_morphism :  forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )),
    forall paramlocal paramlocal' (Heqparamlocal : paramlocal' = (p o>Parametrizator_ paramlocal)),
    forall H param' param, param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) _ param' ->
  sval (Yoneda1_Param_ee0 G paramlocal) H param =
  sval (Yoneda1_Param_ee0 G' paramlocal') H param' )
(Yoneda1_Param_ee :
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
  Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param ->
  Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_E)
(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
    reparamMor (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee0 G (sval Yoneda1_Param_subst G param))
                  (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee G param form))
(Yoneda1_Param_reparam_ee_morphism : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) ,
    forall (G' : obGenerator) (g : 'Generator( G' ~> G )) ,
    forall  G'' (param' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'') ,
    forall (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G''
       := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _ param' ) ,
      projT1 (sval (sval (Yoneda1_Param_reparam_ee_ G param  form ) ) G'' paramm)
      = projT1 (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _
             (sval (sval (Yoneda1_Param_reparam_ee_ G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)
                                                    (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) _)] form) ) ) G'' param')))
(Yoneda1_Form_ee :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee G param form))
 (Yoneda1_Form_ee_morphism :
 forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G)
   (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
 forall (G'' : obGenerator) (paramlocal : Yoneda00_Local_ Yoneda1_Param_subst
    (sval Yoneda1_Param_subst G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)) G'')
   (formlocal : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst
    (sval Yoneda1_Param_subst G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)) (Is_Parameter0 G') <| paramlocal )),
 forall (paramlocal' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G''
    := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _ paramlocal )
   (formlocal' : 'Generator ( G'' ~> G @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G) <| paramlocal' )
    := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramlocal) (formlocal o>GeneratorAtParam g)) ),
   sval (sval (Yoneda1_Form_ee G param form) G'' (paramlocal') (formlocal')) =
   sval (sval (Yoneda1_Form_ee G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)
                               (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) _)] form))
              G'' paramlocal formlocal)) ,
  Yoneda1_Form_data (Yoneda1_FormParam_SumSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj) Yoneda1_FormParam_E
                    (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst)
                    (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee0_morphism).
(**TODO: ???  REDO Local_proj as composition ; TODO: DO Yoneda01_AtParam_transp''_prop*)
Proof.
  intros. unshelve eexists.
  - intros G paramsum paramlocal_form.
    have lemma1: (projT1 paramsum) = (sval Yoneda1_Param_subst G (sval (projT1 (projT2 (sval paramlocal_form)))))
      by abstract(rewrite [RHS](proj2_sig (projT1 (projT2 (sval paramlocal_form)))); simpl;
                  rewrite [RHS](f_equal (@projT1 _ _) (proj2_sig paramlocal_form)); reflexivity).
    unshelve eexists.
    + unshelve refine (sval (sval (Yoneda1_Form_ee G (sval (projT1 (projT2 (sval paramlocal_form)))) (projT2 (projT2 (sval paramlocal_form)))) G _ _)).
      * apply: (sval (sval (Yoneda1_Param_reparam_ee_ _ (sval (projT1 (projT2 (sval paramlocal_form)))) (projT2 (projT2 (sval paramlocal_form))))) _).
        apply: Yoneda00_Local_of_Yoneda00_Param_AtParam_ .
        apply: Yoneda01_Param_AtParam_transp; last (by  exact (projT2 paramsum)); exact: lemma1.
      * simpl; exists unitGenerator.
        abstract(simpl; rewrite [RHS](proj1 (proj2_sig (Yoneda1_Param_reparam_ee_ _ _ _)));
                 simpl; do 1 rewrite -unitParametrizator_polyParametrizator; rewrite -Parameter_unitGenerator; reflexivity).
    + Time abstract(simpl; rewrite [LHS](proj2_sig (sval (Yoneda1_Form_ee _ _ _) _ _ _));
        rewrite [LHS](proj2 (proj2_sig (Yoneda1_Param_reparam_ee_ _ _ _))) (*Heq_reparam_ee*);
        apply: (Yoneda1_Param_PolyTransf_default_quotientLogical Yoneda1_Param_ee0); first (by symmetry; exact: lemma1); reflexivity) .
 - Time abstract (split; [ (move; simpl; intros G paramsum G' g paramlocal_form;
        rewrite [LHS](proj1 (proj2_sig (Yoneda1_Form_ee G _ _))) /= ; rewrite -[RHS]Yoneda1_Form_ee_morphism;
          apply: (Yoneda1_Form_PolyTransf_default_quotientLogical Yoneda1_Form_ee); [ reflexivity | reflexivity
                                                    | | simpl; rewrite -[RHS]polyGenerator_unitGenerator; symmetry; exact:unitGenerator_polyGenerator];
          simpl; rewrite -[RHS]Yoneda1_Param_reparam_ee_morphism; simpl;
            set ee := (sval (Yoneda1_Param_reparam_ee_ _ _ _)); set paramm := (X in sval ee _ X);
            rewrite -[LHS]/(projT1 ( Parameter1 g o>Parametrizator_[sval (Yoneda01_Local_ _ _) ] (sval ee G paramm)));
            congr (projT1 _); rewrite [LHS](proj2_sig ee); congr (sval ee _ _);
              apply: Yoneda00_Local_quotientLogical; 
              simpl; rewrite -[RHS]polyParametrizator_unitParametrizator -[LHS]unitParametrizator_polyParametrizator; reflexivity)
    | (move; simpl; intros G paramsum paramlocal_form paramsum' paramlocal_form' Heqparamsum Heqparamlocal_form;
                       apply: (Yoneda1_Form_PolyTransf_default_quotientLogical Yoneda1_Form_ee);    
                       [ rewrite Heqparamlocal_form; reflexivity
                       | rewrite Heqparamlocal_form; reflexivity 
                       | simpl; apply: (Yoneda1_reparam_PolyTransf_default_quotientLogical Yoneda1_Param_reparam_ee_); simpl;
                         [ rewrite Heqparamlocal_form; reflexivity
                         | rewrite Heqparamlocal_form; reflexivity | reflexivity ]
                       | reflexivity  ]) ] ). (* 70sec *)
Defined.

Definition Yoneda1_Form_Forget :
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
(Yoneda00_Param_PiSubstF : obGenerator -> Type)
(Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF),
  Yoneda1_Form_data (Yoneda1_FormParam_PiSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj) Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst .
Proof.
  intros. unshelve eexists.
  - intros G param form . unshelve eexists.
    + refine (sval ( (sval (projT2 (sval form)) G unitGenerator) _ ) ). unshelve eexists.
      * exact: param .
      * abstract (rewrite -[in RHS]Parameter_unitGenerator; rewrite -[in RHS](proj2 (proj2_sig (Yoneda01_Param_PiSubstF)));
                  symmetry; exact: (proj2_sig form)).
    + abstract (set form_projSec := ( ( (sval (projT2 (sval form)) G unitGenerator) _ ) in LHS );
                            (** TODO: reverse final equation in Yoneda00_AtParam_ or Yoneda00_Form_PiSubst such to same side **)
                            rewrite [(sval form_projSec) in LHS](proj2 (proj2_sig (Yoneda01_Form_F)));
      rewrite -[in LHS](proj2 (proj2_sig Yoneda01_Form_F)); simpl;
      exact (proj2_sig form_projSec) ).
  - abstract (split; [ move; intros; simpl;
             apply: (proj2_sig (projT2 (sval form))); simpl; last reflexivity;
             rewrite -polyGenerator_unitGenerator -unitGenerator_polyGenerator;  reflexivity
           | move; simpl; intros;
             apply: Yoneda00_Form_PiSubst_quotientLogical_rev; simpl; assumption ] ).
Defined.

Definition Yoneda1_Form_PolyCoMod :
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Form_F' : obGenerator -> Type)
(Yoneda01_Form_F' : Yoneda01_data Yoneda00_Form_F')
(Yoneda00_Param_F' : obGenerator -> Type)
(Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
(Yoneda1_FormParam_F' : Yoneda1_FormParam_data Yoneda01_Form_F' Yoneda01_Param_F')
(Yoneda00_Param_F'0' : obGenerator -> Type)
(Yoneda01_Param_F'0' : Yoneda01_Param_data Yoneda00_Param_F'0')
(Yoneda1_Param_proj_Param_F' : Yoneda1_Param_data Yoneda01_Param_F'0' Yoneda01_Param_F')
(Yoneda1_Param_ff' : Yoneda1_Param_data Yoneda01_Param_F'0' Yoneda01_Param_F)
(Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_Param_F' Yoneda1_Param_ff')
(Yoneda00_Form_F'' : obGenerator -> Type)
(Yoneda01_Form_F'' : Yoneda01_data Yoneda00_Form_F'')
(Yoneda00_Param_F'' : obGenerator -> Type)
(Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
(Yoneda1_FormParam_F'' : Yoneda1_FormParam_data Yoneda01_Form_F'' Yoneda01_Param_F'')
(Yoneda00_Param_F''0' : obGenerator -> Type)
(Yoneda01_Param_F''0' : Yoneda01_Param_data Yoneda00_Param_F''0')
(Yoneda1_Param_proj_Param_F'' : Yoneda1_Param_data Yoneda01_Param_F''0' Yoneda01_Param_F'')
(Yoneda1_Param_ff_ : Yoneda1_Param_data Yoneda01_Param_F''0' Yoneda01_Param_F')
(Yoneda1_Form_ff_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_Param_F'' Yoneda1_Param_ff_),
  Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_Param_F'  Yoneda1_Param_proj_Param_F'' Yoneda1_Param_ff_)
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_Param_F' Yoneda1_Param_ff' Yoneda1_Param_ff_) .
Proof.
  intros. unshelve eexists.
  - intros G param dataIn. unshelve eexists.
    + apply: (sval (sval Yoneda1_Form_ff' G (sval (projT2 param)) _)).
      pose dataMid := (sval Yoneda1_Form_ff_ G (projT1 param) dataIn). unshelve eexists.
      * exact: (sval dataMid).
      * abstract(rewrite [LHS](proj2_sig dataMid); symmetry; exact (proj2_sig (projT2 param))).
    + abstract (set tmp := (sval Yoneda1_Form_ff' G (sval (projT2 param)) _);
                           exact: (proj2_sig tmp)).
  - abstract (split; [ move; simpl; intros; rewrite [LHS](proj1 (proj2_sig Yoneda1_Form_ff'));
      apply: (proj2 (proj2_sig Yoneda1_Form_ff')); first reflexivity;
        simpl; rewrite [LHS](proj1 (proj2_sig Yoneda1_Form_ff_));
          apply: (proj2 (proj2_sig Yoneda1_Form_ff_)); simpl; reflexivity
    | move; simpl; intros; apply: (proj2 (proj2_sig Yoneda1_Form_ff'));
      first ( subst; reflexivity ) ;
      simpl; apply: (proj2 (proj2_sig Yoneda1_Form_ff_));
        first ( subst; reflexivity ); assumption ] ).
Defined.

Definition Yoneda1_UnitCoMod 
           (Yoneda00_Form_F : obGenerator -> Type)
           (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type)
           (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) :
  Yoneda1_Form_data Yoneda1_FormParam_F Yoneda1_FormParam_F (Yoneda1_UnitCoMod_Param Yoneda01_Param_F)
                     (Yoneda1_UnitCoMod_Param Yoneda01_Param_F).
Proof.
  intros; unshelve eexists.
  - refine (fun G param => id).
  - abstract (split; move; simpl; intros; [ reflexivity | assumption ]).
Defined.

Definition Yoneda1_Form_Remember :
forall (Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(Yoneda00_Param_SubstF : obGenerator -> Type)
(Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
(Yoneda00_Param_PiSubstF : obGenerator -> Type)
(Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
(Yoneda00_Form_L : obGenerator -> Type)
(Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
(Yoneda00_Param_L : obGenerator -> Type)
(Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
(Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
(Yoneda00_Param_LPiSubstF : obGenerator -> Type)
(Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
(Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
(Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
(Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst) (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst)),
Yoneda1_Form_data Yoneda1_FormParam_L (Yoneda1_FormParam_PiSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj) Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst .
Proof.
  intros. unshelve eexists.
  - intros G param form. unshelve eexists.
    + unshelve eexists.
      * exact: (sval Yoneda1_Param_LPiSubstF_subst G param) .
      * { unshelve eexists.
          - intros H' h s. unshelve eexists.
            + simple refine (sval (sval Yoneda1_Form_ll H' _ _ )).
              * exists ((Parameter1 h) o>Parametrizator_[sval Yoneda01_Param_LPiSubstF ] param).
                exists (sval s).
                abstract (simpl; rewrite -[RHS](proj2_sig Yoneda1_Param_LPiSubstF_subst );
                  exact: (proj2_sig s)).
              * exists (sval (h o>GeneratorAtParam_[sval (Yoneda01_AtParam_ Yoneda1_FormParam_L Yoneda1_Param_LPiSubstF_proj) ] form)).
                abstract(simpl;  simpl;
                         rewrite -[LHS](proj2_sig Yoneda1_FormParam_L) -[RHS](proj2_sig Yoneda1_Param_LPiSubstF_proj);
                         congr ( h o>Generator_ _ ); exact: (proj2_sig form)).
            + abstract (simpl; rewrite [LHS](proj2_sig (sval Yoneda1_Form_ll _ _ _ )); reflexivity).
          - abstract (simpl; intros; rewrite [LHS](proj1 (proj2_sig Yoneda1_Form_ll ));
            apply: (proj2 (proj2_sig Yoneda1_Form_ll )); simpl;
            [ apply: Yoneda00_Param_Subst_quotientLogical; simpl; 
              [ rewrite -Heq_arrow; rewrite Parameter_morphism; exact: (proj1 (proj2_sig Yoneda01_Param_LPiSubstF))
              | exact: Heq_param ]
            | rewrite -Heq_arrow; exact: (proj1 (proj2_sig Yoneda01_Form_L)) ] ) .
        }            
    + abstract (simpl; reflexivity).
  - abstract (split;
    [ move; simpl; intros; apply: Yoneda00_Form_PiSubst_quotientLogical_ALT; simpl;
      intros; apply: (proj2 (proj2_sig Yoneda1_Form_ll )); simpl;
      [ apply: Yoneda00_Param_Subst_quotientLogical; simpl;
        [ rewrite Parameter_morphism; symmetry;  exact: (proj1 (proj2_sig Yoneda01_Param_LPiSubstF))
        | assumption ]
      | symmetry; exact: (proj1 (proj2_sig Yoneda01_Form_L)) ] 
    | move; simpl; intros; apply: Yoneda00_Form_PiSubst_quotientLogical_ALT; simpl;
      intros; apply: (proj2 (proj2_sig Yoneda1_Form_ll )); simpl;
      [ apply: Yoneda00_Param_Subst_quotientLogical; simpl;
          [ subst; reflexivity
          | assumption ]
      | congr ( _ o>Generator_ _ );
        assumption ] ] ) .
Defined.

Definition Yoneda1_Form_View1 :
    forall (Param_F : obParametrizator) (Yoneda00_Param_F := Yoneda00_Param_View Param_F)
      (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F := Yoneda01_Param_View Param_F),
    forall (D : obGenerator) (Yoneda00_D := Yoneda00_View D)
      (Param_D : obParametrizator  := Parameter0 D) (Yoneda00_Param_D := Yoneda00_Param_View Param_D)
      (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D := Yoneda01_Param_View Param_D),
    forall (param_subst : 'Parametrizator( Param_F ~> Param_D ))
      (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_F Yoneda01_Param_D
       := Yoneda1_Param_View1 param_subst),
    forall (G : obGenerator) (form : Yoneda00_D G),
 Yoneda1_Form_data (Yoneda1_FormParam_View G) (Yoneda1_FormParam_View D)
    (Yoneda1_Local_proj (Yoneda1_Param_View1 param_subst) (Parameter1 form) (Is_Parameter0 G))
    (Yoneda1_Local (Yoneda1_Param_View1 param_subst) (Parameter1 form)).
Proof.
  intros. unshelve eexists.
  - intros G0 param g. apply: (Yoneda01_AtParam_transp _ (g o>GeneratorAtParam form)).
    abstract (simpl; do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity).
  - abstract (split; [ move; simpl; intros ; rewrite /Yoneda01_action /= ; exact: polyGenerator_morphism
                     | move; simpl; intros; congr ( _ o>Generator form ); assumption ] ).
Defined.

Definition Yoneda1_Param_View1_proj_is_Parameter0 :
  forall (G : obGenerator) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    Yoneda1_Param_data (Yoneda01_Param_View (Parameter0 G)) (Yoneda01_Param_View P).
Proof.
  intros. exact: (Yoneda1_Param_View1 (fst (sval is_Parameter0_P))).
Defined.

Definition Yoneda1_Form_View1' :
  forall (G : obGenerator) (H : obGenerator) (g : 'Generator( H ~> G )),
    Yoneda1_Form_data (Yoneda1_FormParam_View H) (Yoneda1_FormParam_View G)
                     (Yoneda1_Param_View1_proj_is_Parameter0 (Is_Parameter0 _))
                  (Yoneda1_Param_View1 (Parameter1 g)) .
Proof.
  intros G H hg. unshelve eexists.
  - intros G0 x h . exists ( (sval h) o>Generator hg ).
    abstract (move: (proj2_sig h); rewrite /Yoneda1_Param_View1 /Yoneda1_FormParam_View  /= ;
              rewrite Parameter_morphism ; move -> ; do 1 rewrite -unitParametrizator_polyParametrizator; reflexivity).
  - abstract (split; [ move; simpl; intros ; rewrite /Yoneda01_action /= ; exact: polyGenerator_morphism
                     | move; simpl; intros; congr ( _ o>Generator hg ); assumption] ). 
Defined.

Definition Morphism_prop   (**MEMO: THIS SIMILAR AS ASSOCIATIVITY *) 
           (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
           (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) 
           (Yoneda1_Param_ee : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
  := forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G)
       (paramlocal' : Yoneda00_Param_SumSubstF G') (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator)
       (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H) (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
    param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' ->
    sval (Yoneda1_Param_ee G paramlocal) H param = sval (Yoneda1_Param_ee G' paramlocal') H param'.

Lemma Morphism_PolyElement_ReParam_default
     : forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
        (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
         (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF),
         Morphism_prop (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst).
Proof.
  intros. move. intros. apply: Yoneda00_Param_SumImage_quotientLogical; simpl. subst. simpl. rewrite (proj1 (proj2_sig Yoneda01_Param_SumSubstF)). reflexivity.
Qed.
Arguments Morphism_PolyElement_ReParam_default [_ _ _ _] _.

Definition Morphism_Form_prop
 (Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form)) :=
 forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G)
   (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
 forall (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst
    (sval Yoneda1_Param_subst G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)) G'')
   (formm : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst
    (sval Yoneda1_Param_subst G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)) (Is_Parameter0 G') <| paramm )),
 forall (paramm' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G''
    := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _ paramm )
   (formm' : 'Generator ( G'' ~> G @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G) <| paramm' )
    := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramm) (formm o>GeneratorAtParam g)) ),
   sval (sval (Yoneda1_Form_ee__ G param form) G'' (paramm') (formm')) =
   sval (sval (Yoneda1_Form_ee__ G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)
                               (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) _)] form))
              G'' paramm formm).

Lemma Morphism_PolyElement_default
  : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_SumSubstF : obGenerator -> Type)
      (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF),
    forall (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
      (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF),
    forall Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F,
      Morphism_Form_prop (Yoneda1_FormParam_F:=Yoneda1_FormParam_F)
                         (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst (Yoneda1_Param_proj:=Yoneda1_Param_proj)).
Proof.
  intros; move; intros; apply: Yoneda00_Form_SumSubst_quotientLogical; simpl.
  - reflexivity.
  - rewrite Parameter_morphism. rewrite (proj1 (proj2_sig Yoneda01_Param_SubstF)). reflexivity.
  - rewrite (proj1 (proj2_sig Yoneda01_Form_F)). reflexivity.
Qed.
Arguments Morphism_PolyElement_default [_ _ _ _] _ [_ _ _ _] _ _.

Definition Morphism_reparam_prop
 (Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda1_Param_reparam_ee : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form)) :=
  forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) ,
    forall (G' : obGenerator) (g : 'Generator( G' ~> G )) ,
    forall  G'' (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'') ,
    forall (paramm' : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) G''
       := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _ paramm ) ,
      projT1 (sval (sval (fst (sval (Yoneda1_Param_reparam_ee G param  form) ) )) G'' paramm')
      = projT1 (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym ((proj2_sig Yoneda1_Param_subst) _ _ _ _))) _
             (sval (sval (fst (sval (Yoneda1_Param_reparam_ee G' ((Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SubstF] param)
                                                    (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) _)] form)) ) )) G'' paramm)).

Lemma Refl_Morphism_reparam_prop
 (Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
      Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K
   := fun G param form => Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
  (Yoneda1_Param_reparam_ee : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
                                           (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form)
  :=  fun G param form => reparamMorSym_Refl _ _) :
  Morphism_reparam_prop Yoneda1_Param_reparam_ee.
Proof.
  move; intros; reflexivity.
Qed.

Module Export Finiteness.

Definition Yoneda00_Param_Binary : obGenerator -> Type := fun _ => bool .
Definition Yoneda01_Param_Binary : Yoneda01_Param_data Yoneda00_Param_Binary.
Proof.
  exists (fun _ _ _ => id). abstract (split; reflexivity). 
Defined.

Definition Yoneda01_Form_Binary := (Yoneda01_data_of_Yoneda01_Param_data Yoneda01_Param_Binary).
Definition Yoneda1_FormParam_Binary : Yoneda1_FormParam_data Yoneda01_Form_Binary Yoneda01_Param_Binary := (Yoneda1_FormParam_Id  Yoneda01_Param_Binary).
Definition Yoneda01_Param_SubstBinary := Yoneda01_Param_Binary.
Definition Yoneda01_Param_SumSubstBinary := Yoneda01_Param_Binary.
Definition Yoneda1_Param_subst_Binary : Yoneda1_Param_data Yoneda01_Param_SubstBinary Yoneda01_Param_SumSubstBinary := (Yoneda1_Param_Id Yoneda01_Param_Binary).
Definition Yoneda1_Param_proj_Binary : Yoneda1_Param_data Yoneda01_Param_SubstBinary Yoneda01_Param_Binary  := (Yoneda1_Param_Id Yoneda01_Param_Binary).
Definition true_Binary : forall (G : obGenerator), Yoneda00_Param_Binary G := fun _ => true.
Definition false_Binary : forall (G : obGenerator), Yoneda00_Param_Binary G := fun _ => false.
Definition Yoneda1_Param_subst_invert : Yoneda1_Param_data (Yoneda01_Param_SumImage Yoneda1_Param_subst_Binary)
                                                           (Yoneda01_Param_SumImage Yoneda1_Param_subst_Binary).
Proof.
  unshelve eexists.
  intros G param. exists (negb (projT1 param)). exists (negb (sval (projT2 param))).
  abstract (congr (negb _); exact: (proj2_sig (projT2 param))).
  abstract (move; intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; reflexivity).
Defined.
Definition true_Binary_Form : forall (G : obGenerator),  Yoneda00_AtParam_ Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary (true_Binary G) .
Proof.
  intros ?. exists true. abstract (reflexivity).
Defined.
Definition false_Binary_Form : forall (G : obGenerator),  Yoneda00_AtParam_ Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary (false_Binary G) .
Proof.
  intros ?. exists false. abstract (reflexivity).
Defined.

Inductive data_Yoneda01_Param_data' : forall  (Yoneda00_F : obGenerator -> Type),
    forall (Yoneda01_F : Yoneda01_Param_data Yoneda00_F),  Type :=
| Data_Yoneda01_Param_Binary' : data_Yoneda01_Param_data'   Yoneda01_Param_Binary  .

Inductive data_Yoneda00_Param_data : forall  (Yoneda00_F : obGenerator -> Type),   Type :=
| Data_Yoneda00_Param_Binary : data_Yoneda00_Param_data Yoneda00_Param_Binary  .

Inductive data_Yoneda01_Param_data : forall  (Yoneda00_F : obGenerator -> Type)( Data_Yoneda00_F :  data_Yoneda00_Param_data Yoneda00_F),
    forall (Yoneda01_F : Yoneda01_Param_data Yoneda00_F),  Type :=
| Data_Yoneda01_Param_Binary : data_Yoneda01_Param_data  Data_Yoneda00_Param_Binary Yoneda01_Param_Binary  .

Inductive data_Yoneda1_Param_data :
  forall Yoneda00_F ( Data_Yoneda00_F :  data_Yoneda00_Param_data Yoneda00_F)  (Yoneda01_F : Yoneda01_Param_data Yoneda00_F) (Data_Yoneda01_F : data_Yoneda01_Param_data  Data_Yoneda00_F Yoneda01_F ) ,
  forall Yoneda00_E ( Data_Yoneda00_E :  data_Yoneda00_Param_data Yoneda00_E)  (Yoneda01_E : Yoneda01_Param_data Yoneda00_E) (Data_Yoneda01_E : data_Yoneda01_Param_data  Data_Yoneda00_E Yoneda01_E ) ,
  forall (Yoneda1_FE : Yoneda1_Param_data Yoneda01_F Yoneda01_E) , Type :=
| Data_Yoneda1_Param_subst_Binary : data_Yoneda1_Param_data  Data_Yoneda01_Param_Binary Data_Yoneda01_Param_Binary Yoneda1_Param_subst_Binary .

Inductive data_Yoneda01_data : forall  (Yoneda00_F : obGenerator -> Type)( Data_Yoneda00_F :  data_Yoneda00_Param_data Yoneda00_F),
    forall (Yoneda01_F : Yoneda01_data Yoneda00_F),  Type :=
| Data_Yoneda01_Form_Binary : data_Yoneda01_data  Data_Yoneda00_Param_Binary Yoneda01_Form_Binary  .

Inductive data_Yoneda1_FormParam_data :
  forall Yoneda00_F ( Data_Yoneda00_F :  data_Yoneda00_Param_data Yoneda00_F)  (Yoneda01_F : Yoneda01_data Yoneda00_F) (Data_Yoneda01_F : data_Yoneda01_data  Data_Yoneda00_F Yoneda01_F ) ,
  forall Yoneda00_E ( Data_Yoneda00_E :  data_Yoneda00_Param_data Yoneda00_E)  (Yoneda01_E : Yoneda01_Param_data Yoneda00_E) (Data_Yoneda01_E : data_Yoneda01_Param_data  Data_Yoneda00_E Yoneda01_E ) ,
  forall (Yoneda1_FE : Yoneda1_FormParam_data Yoneda01_F Yoneda01_E) , Type :=
| Data_Yoneda1_FormParam_Binary : data_Yoneda1_FormParam_data  Data_Yoneda01_Form_Binary Data_Yoneda01_Param_Binary Yoneda1_FormParam_Binary .


Inductive obCoMod_Param_Data :
  forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF), Type :=

| Binary : obCoMod_Param_Data Yoneda1_Param_subst_Binary.

Inductive obCoMod_Data :
  forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst), Type :=

| Binary_Form : obCoMod_Data Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary Binary .


(*MEMO: later , [Inductive congrPseudoCode] shall depend on these constructors , so move these above *)
Parameter is_Parameter0Default_Constructors : forall (G : obGenerator),
  forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P), Type.

Parameter Unit_is_Parameter0Default_Constructors : 
  forall (G : obGenerator), is_Parameter0Default_Constructors (Is_Parameter0 G) .

Parameter viewingDefault_Constructors : forall (G' : obGenerator),
  forall (P : obParametrizator)  (p : 'Parametrizator( Parameter0 G' ~> P ))
    (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
    (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P'), Type.

Parameter viewingDefault_Constructors_action :
  forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
    (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
  forall  (G' : obGenerator) (p' : 'Parametrizator(  Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
     (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
     (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
    viewingDefault_Constructors ((is_Parameter0_transp_codom is_Parameter0_P p') o>Parametrizator p) cons_is_Parameter0_P' .

Parameter GBinary : obGenerator. (*or G_Top *)

Parameter Unit_viewingDefault_Constructors_Binary :
  viewingDefault_Constructors (@unitParametrizator (Parameter0 GBinary)) (Unit_is_Parameter0Default_Constructors GBinary) .

Inductive viewingDefault_Constructors_codomBinary :
  forall (G : obGenerator)(p : 'Parametrizator(  Parameter0 G ~> (Parameter0 GBinary) ))
    P (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
  (pp : viewingDefault_Constructors p cons_is_Parameter0_P), Type :=
| Unit_viewingDefault_Constructors_codomBinary : 
    viewingDefault_Constructors_codomBinary (Unit_viewingDefault_Constructors_Binary).

Axiom viewingDefault_Constructors_codomBinary_prop :
  forall (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> (Parameter0 GBinary) ))
    P (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    viewingDefault_Constructors_codomBinary pp .

Parameter constructors :
forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF: obCoMod_Param_Data Yoneda1_Param_subst),
forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
  (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P), Type.

Parameter constructors_action :
forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF: obCoMod_Param_Data Yoneda1_Param_subst),

forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),

forall (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
  (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ) ,

forall (G' : obGenerator) (p' : 'Parametrizator( Parameter0 G' ~> P)) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
  (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
  (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P' ),
  forall paramlocal' (Heq_paramlocal : ( (is_Parameter0_transp_codom is_Parameter0_P p') o>Parametrizator_[sval Yoneda01_Param_SumSubstF] paramlocal) = paramlocal'),
    constructors Param_SubstF paramlocal' cons_is_Parameter0_P' .

Parameter True_Binary :
  forall (G : obGenerator) (p : 'Parametrizator( Parameter0 G ~> Parameter0 GBinary (* Parameter0 G ~> _ | Viewing_Binary *) ))
    (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    (* enough for these arguments to be unit/reflexivity because of Yoneda1_Param_ee_morphism ..NOPE THERE IS MORE :
                 in fact this is quantified over some finitely-presented/compact geometry viewing (which by def accept action) Viewing_Binary (given functor, not the all 'Parametrizator) ,
                 SO THAT THE MANNER OF DESTRUCTION/ELIMINATION WILL BE GEOMETRIC !  *)
    
    constructors Binary ( p o>Parametrizator_[sval Yoneda01_Param_Binary] (true_Binary GBinary)) cons_is_Parameter0_P .

Parameter False_Binary :
  forall (G : obGenerator) (p : 'Parametrizator( Parameter0 G ~> Parameter0 GBinary (* Parameter0 G ~> _ | Viewing_Binary *) ))
    (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    constructors Binary ( p o>Parametrizator_[sval Yoneda01_Param_Binary] (false_Binary GBinary)) cons_is_Parameter0_P .

Module Constructors_dataBinary.
Inductive constructors :
forall (G : obGenerator) (paramlocal : Yoneda00_Param_Binary G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
  (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
  (cons_paramlocal : Finiteness.constructors Binary paramlocal cons_is_Parameter0_P), Type := 
| True_Binary :
  forall (G : obGenerator) (p : 'Parametrizator( Parameter0 G ~> Parameter0 GBinary (* Parameter0 G ~> _ | Viewing_Binary *) ))
    (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    constructors (True_Binary pp)
| False_Binary :
  forall (G : obGenerator) (p : 'Parametrizator( Parameter0 G ~> Parameter0 GBinary (* Parameter0 G ~> _ | Viewing_Binary *) ))
    (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    constructors (False_Binary pp).
End Constructors_dataBinary.

Parameter constructors_dataBinary_prop :
  forall (G : obGenerator) (paramlocal : Yoneda00_Param_Binary G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
    (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (cons_paramlocal : Finiteness.constructors Binary paramlocal cons_is_Parameter0_P),
    Constructors_dataBinary.constructors cons_paramlocal.

Module Constructors_dataTrue.
Inductive constructors :
  forall (cons_paramlocal : Finiteness.constructors Binary true (Unit_is_Parameter0Default_Constructors GBinary)), Type :=
| True_Binary :
      constructors (True_Binary Unit_viewingDefault_Constructors_Binary). 
End Constructors_dataTrue.

Module Constructors_dataFalse.
 Inductive constructors :
 forall (cons_paramlocal : Finiteness.constructors Binary false (Unit_is_Parameter0Default_Constructors GBinary)), Type :=
| False_Binary :
      constructors (False_Binary Unit_viewingDefault_Constructors_Binary). 
End Constructors_dataFalse.

Parameter constructors_dataTrueFalse_prop :
forall (paramlocal : Yoneda00_Param_Binary GBinary)
  (cons_paramlocal : Finiteness.constructors Binary paramlocal (Unit_is_Parameter0Default_Constructors GBinary)),
  ltac: (destruct paramlocal;
           [ refine (Constructors_dataTrue.constructors cons_paramlocal)
           | refine (Constructors_dataFalse.constructors cons_paramlocal)] ) .

Parameter viewingDefault_Constructors_Form :
  forall (G' G : obGenerator) (p : 'Generator(  G ~>  G' (*  G ~> _ | Viewing_Default *) )),Type .

(**MEMO: shall this be carried by [viewingDefault_Constructors_Form] ?  *)
Parameter viewingDefault_Constructors_of_viewingDefault_Constructors_Form :
  forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (gg : viewingDefault_Constructors_Form g),
viewingDefault_Constructors (Parameter1 g) (Unit_is_Parameter0Default_Constructors G').

Parameter viewingDefault_Constructors_Form_action :
    forall (G H : obGenerator) (g : 'Generator( G ~> H )) (gg : viewingDefault_Constructors_Form g),
    forall (G' : obGenerator) (g' : 'Generator( G' ~> G )) (g'g' : viewingDefault_Constructors_Form g'),
viewingDefault_Constructors_Form (g' o>Generator g).

Parameter Unit_viewingDefault_Constructors_Form_Binary : viewingDefault_Constructors_Form (@unitGenerator GBinary) .

Inductive viewingDefault_Constructors_Form_codomBinary :
  forall (G : obGenerator) (g : 'Generator( G ~> GBinary ))
    (gg : viewingDefault_Constructors_Form g), Type :=
| Unit_viewingDefault_Constructors_Form_codomBinary : 
    viewingDefault_Constructors_Form_codomBinary (Unit_viewingDefault_Constructors_Form_Binary).

Axiom viewingDefault_Constructors_Form_codomBinary_prop :
 forall (G : obGenerator) (g : 'Generator( G ~> GBinary ))
   (gg : viewingDefault_Constructors_Form g), viewingDefault_Constructors_Form_codomBinary gg.

Parameter constructors_Form :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param), Type .

Parameter constructors_Form_action :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (* (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param)) *),
forall (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (cons_form : constructors_Form F  form (*cons_paramlocal *)), 

forall (G' : obGenerator) (g : 'Generator( G' ~> G )) (gg : viewingDefault_Constructors_Form g),

  constructors_Form F (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_( Yoneda1_FormParam_F)  Yoneda1_Param_proj  ) ] form ) .

Parameter True_Binary_Form : forall (G' : obGenerator) (g : 'Generator( G' ~> GBinary ))
                       (gg : viewingDefault_Constructors_Form g) ,
      constructors_Form Binary_Form (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_( Yoneda1_FormParam_Binary)  Yoneda1_Param_proj_Binary  ) ] (true_Binary_Form GBinary)) .
Parameter False_Binary_Form : forall (G' : obGenerator) (g : 'Generator( G' ~> GBinary ))
                       (gg : viewingDefault_Constructors_Form g) ,
      constructors_Form Binary_Form (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_( Yoneda1_FormParam_Binary)  Yoneda1_Param_proj_Binary  ) ] (false_Binary_Form GBinary))  .

Module Constructors_Form_dataBinary.
Inductive constructors_Form :
  forall (G : obGenerator) (param : Yoneda00_Param_Binary G),
  forall form : Yoneda00_AtParam_ Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary param,
  forall (cons_form : Finiteness.constructors_Form Binary_Form form), Type :=

| True_Binary_Form : forall (G' : obGenerator) (g : 'Generator( G' ~> GBinary ))
                       (gg : viewingDefault_Constructors_Form g) ,
      constructors_Form  ( True_Binary_Form gg ) 
| False_Binary_Form : forall (G' : obGenerator) (g : 'Generator( G' ~> GBinary ))
                       (gg : viewingDefault_Constructors_Form g) ,
      constructors_Form  ( False_Binary_Form gg) .
End Constructors_Form_dataBinary.

Parameter constructors_Form_dataBinary_prop :
forall (G : obGenerator) (param : Yoneda00_Param_Binary G),
  forall form : Yoneda00_AtParam_ Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary param,
  forall (cons_form : Finiteness.constructors_Form Binary_Form form),
  Constructors_Form_dataBinary.constructors_Form cons_form .

Lemma constructors_Form_action_transp_Heq :
  forall  (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) ,
  forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
  forall (G' : obGenerator) (g : 'Generator( G' ~> G )),
    is_Parameter0_transp_codom (Is_Parameter0 G) (Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SumSubstF ] sval Yoneda1_Param_subst G param = sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_[sval Yoneda01_Param_SubstF] param) .
Proof.
  intros. rewrite -[RHS](proj2_sig  Yoneda1_Param_subst). rewrite -[LHS](proj1 (proj2_sig Yoneda01_Param_SumSubstF )) .
  congr ( _ o>Parametrizator_ _ ). rewrite -[LHS](proj2 (proj2_sig Yoneda01_Param_SumSubstF )) .   reflexivity.
Qed.  

Lemma test_cases_gradeCoMod_ReParam :
  forall (G : obGenerator) (paramlocal : Yoneda00_Param_Binary G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
    (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (cons_paramlocal : constructors Binary paramlocal cons_is_Parameter0_P) ,
    cons_paramlocal = cons_paramlocal .
Proof.
  intros; destruct (constructors_dataBinary_prop cons_paramlocal) as [ ? ? ? ? ? pp | ? ? ? ? ? pp ] .
  destruct (viewingDefault_Constructors_codomBinary_prop pp).
Abort.

Lemma test_cases_gradeCoMod :
  forall (G : obGenerator) (param : Yoneda00_Param_Binary G),
  forall (cons_paramlocal : constructors Binary (sval Yoneda1_Param_subst_Binary G param) (Unit_is_Parameter0Default_Constructors G)),
  forall form : Yoneda00_AtParam_ Yoneda1_FormParam_Binary Yoneda1_Param_proj_Binary param,
  forall (cons_form : constructors_Form Binary_Form form),
    (cons_paramlocal , cons_form) = (cons_paramlocal , cons_form) .
Proof.
  intros; destruct (constructors_Form_dataBinary_prop cons_form) as [? ? gg | ? ? gg].
  destruct (viewingDefault_Constructors_Form_codomBinary_prop gg).
  destruct (constructors_dataTrueFalse_prop cons_paramlocal).
Abort.

(**TODO: MOVE UP AND ADD CONSTRUCTORS CODES EVEN IN PSEUDOCODES , THIS ALSO ERASES SOLVES ATMEMBER_REPARAM_SUBST
TODO: DON'T FORGET REQUIRED ACTION ON CONSTRUCTORS ...
    AND DESTRUCTION OF THE CONSTRUCTORS-THEN-ACTORS WHERE THE CONCRETE CONTENT OF THE GRAMMATICAL-MORPHISMS-FAMILY OCCURS *)

End Finiteness.

Inductive pseudoCode
    : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
        (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
      forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
        (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
      forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
        (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
        Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff -> Type :=

| AtMember_Form :
forall (Yoneda00_Form_F : obGenerator -> Type) 
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
  (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
forall(Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
  (Form_ee : pseudoCode_Family Yoneda1_Form_ee_morphism),

    forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
      pseudoCode (Yoneda1_Form_ee__ G param form)
                 
| PolyCoMod_pseudoCode : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
                  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
                  (Yoneda00_Form_F' : obGenerator -> Type) (Yoneda01_Form_F' : Yoneda01_data Yoneda00_Form_F') (Yoneda00_Param_F' : obGenerator -> Type)
                  (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F') (Yoneda1_FormParam_F' : Yoneda1_FormParam_data Yoneda01_Form_F' Yoneda01_Param_F')
                  (Yoneda00_Param_F'F : obGenerator -> Type) (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F) (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
                  (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F) (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
                  (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
                pseudoCode Yoneda1_Form_ff' ->
                forall (Yoneda00_Form_F'' : obGenerator -> Type) (Yoneda01_Form_F'' : Yoneda01_data Yoneda00_Form_F'') (Yoneda00_Param_F'' : obGenerator -> Type)
                  (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'') (Yoneda1_FormParam_F'' : Yoneda1_FormParam_data Yoneda01_Form_F'' Yoneda01_Param_F'') 
                  (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')
                  (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'') (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
                  (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
                  (Yoneda1_Form_ff_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_),
                pseudoCode Yoneda1_Form_ff_  -> pseudoCode ( Yoneda1_Form_PolyCoMod Yoneda1_Form_ff' Yoneda1_Form_ff_ )

| UnitCoMod_pseudoCode : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
                  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
                pseudoCode ( Yoneda1_UnitCoMod Yoneda1_FormParam_F )

| View1_pseudoCode : forall (G H : obGenerator) (g : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
            (gg : viewingDefault_Constructors_Form g),
    pseudoCode ( Yoneda1_Form_View1' g )

| ViewedFunctor1_default_pseudoCode : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type)
                               (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) 
                                (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
                               (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) 
                                (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                               (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                               (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                               (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
    pseudoCode Yoneda10_Form_ff ->  pseudoCode ( Yoneda10_Form_ff )

| UnitViewedFunctor_default_pseudoCode' : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
                  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
                pseudoCode ( Yoneda1_UnitCoMod Yoneda1_FormParam_F )

| PolyTransf_default_pseudoCode' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                        (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
  (Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
  (Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism),

  pseudoCode (Yoneda1_Form_PolyTransf_default Yoneda1_Param_ee_morphism (Refl_Morphism_reparam_prop Yoneda1_Param_ee_) Yoneda1_Form_ee_morphism)

| Forget_pseudoCode : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
               (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) 
               (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
                (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
               (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
               (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),
             pseudoCode (Yoneda1_Form_Forget Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)

| Remember_pseudoCode : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type)
                 (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) 
                  (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
                  (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
                 (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
                 (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll'),

   pseudoCode ( (**TODO: Rephrase Yoneda1_Form_Remember  *) Yoneda1_Form_Remember (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' (Yoneda1_UnitCoMod  Yoneda1_FormParam_LF)) )

with pseudoCode_ReParam
           : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
             forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
             forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
               (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F), Type :=

| AtMember_ReParam :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
 forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) 
   (Yoneda1_Param_ee_ : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G),
       Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
   (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
   (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
   pseudoCode_ReParam (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal)

| PolyCoMod_pseudoCode_ReParam : forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) 
                          (Yoneda00_Param_F' : obGenerator -> Type) (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F') 
                          (Yoneda00_Param_F'F : obGenerator -> Type) (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F)
                          (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F') (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F)
                          (Param_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
                        forall (Yoneda00_Param_F'' : obGenerator -> Type) (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'') 
                          (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')
                          (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'') (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
                          (Param_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_),
   pseudoCode_ReParam (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj  Yoneda1_Param_proj_ff' Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
                              (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst  Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff' Yoneda1_Param_subst_ff_)

| UnitCoMod_pseudoCode_ReParam : forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) ,
    pseudoCode_ReParam (Yoneda1_UnitCoMod_Param Yoneda01_Param_F) (Yoneda1_UnitCoMod_Param Yoneda01_Param_F)

| View1_pseudoCode_ReParam : forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
      (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    pseudoCode_ReParam (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P) 
                       (Yoneda1_Param_View1 p)

| ViewedFunctor1_pseudoCode_ReParam_default : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                                       (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) 
                                       (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                                       (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                                       (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),

    pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff

| UnitViewedFunctor_pseudoCode_ReParam_default' : forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) ,
    pseudoCode_ReParam (Yoneda1_UnitCoMod_Param Yoneda01_Param_F) (Yoneda1_UnitCoMod_Param Yoneda01_Param_F)

| PolyTransf_pseudoCode_ReParam_default' :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

 forall (Yoneda00_Param_E : obGenerator -> Type)
    (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) 
    (Yoneda1_Param_ee_ : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
    (Yoneda1_Param_ee_morphism :  Morphism_prop Yoneda1_Param_ee_)
    (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),
    pseudoCode_ReParam (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj' Yoneda1_Param_subst)
                       (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst' Yoneda1_Param_ee_morphism)

| Formatting_pseudoCode_ReParam' : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type)
                   (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
                   (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
                   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type)
                   (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
                   (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst),
                 pseudoCode Yoneda1_Form_ff  ->                
                   pseudoCode_ReParam  (Yoneda1_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_E) Yoneda1_Param_proj)
                                                (Yoneda1_Param_Format_subst Yoneda1_Form_ff)

with pseudoCode_Family :
forall (Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__), Type :=

| PolyElement_default_pseudoCode :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
  
   pseudoCode_Family (Morphism_PolyElement_default Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)

with pseudoCode_ReParam_Family
           : forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
               (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
               (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
               (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) 
               (Yoneda1_Param_ee_ : forall (G : obGenerator) (param : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst param) Yoneda01_Param_E)
               (Yoneda1_Param_ee_morphism (**MEMO: THIS SIMILAR AS ASSOCIATIVITY *) : Morphism_prop Yoneda1_Param_ee_), Type :=

| PolyElement_pseudoCode_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

    pseudoCode_ReParam_Family (Yoneda1_Param_ee_ := Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst)
                              (Morphism_PolyElement_ReParam_default Yoneda1_Param_subst) .

Inductive obCoMod : forall Yoneda00_Form_F (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F),
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
    forall Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F, Type := 

| View : forall G : obGenerator, @obCoMod (Yoneda00_View G) (Yoneda01_View G)
  (Yoneda00_Param_View (Parameter0 G)) (Yoneda01_Param_View (Parameter0 G)) (Yoneda1_FormParam_View G)

| ViewingFunctorSumSubst_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
    
    obCoMod (Yoneda1_FormParam_SumSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)

| ViewedFunctor_default :
    forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
      (F: @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
      (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
      @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F

| PiSubst :
  forall (Yoneda00_Form_F : obGenerator -> Type)
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (F: @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
    (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
  forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
    (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
    (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),
  forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF),
  forall (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F),
  forall (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF),
  forall (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),
    obCoMod (Yoneda1_FormParam_PiSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)


with obCoMod_Param : forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F), Type :=

| View_Param : forall P : obParametrizator, @obCoMod_Param (Yoneda00_Param_View P) (Yoneda01_Param_View P)

| ViewingFunctor_Param_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
  
   obCoMod_Param (Yoneda01_Param_SumImage Yoneda1_Param_subst)

| ViewedFunctor_Param_default :
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Param_F : obCoMod_Param Yoneda01_Param_F),

   obCoMod_Param Yoneda01_Param_F 

| Format : forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
            (F: @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
            (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
    obCoMod_Param (Yoneda01_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_F)
                                         (Yoneda1_Param_Id Yoneda01_Param_F)) .

Section Congr_data.
  Variables   (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
        (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
       (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
        (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
       (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
        (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
        (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
        (Form_ff : pseudoCode Yoneda1_Form_ff)
        (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF') (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
        (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
        (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
        (Form_ff' : pseudoCode Yoneda1_Form_ff') .

  Variables (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                  Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff').

  Record Congr_data : Type :=
  { Congr_data_prop : ( forall (G' : obGenerator) (param' : Yoneda00_Param_EF G') (param'0 : Yoneda00_Param_EF' G'),
 forall Heqparam' : param'0 = (sval (sval (fst (sval Yoneda1_Param_reparam_rr))) G' param'),
 forall (form' : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_proj_ff param')
   (form'0 : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_proj_ff' param'0),
 forall Heq : sval form'0 = sval form',
   sval (sval Yoneda1_Form_ff' G' param'0 form'0) = sval (sval Yoneda1_Form_ff G' param' form') ) }.

  Definition Congr_data_ALT : Type :=
    forall (G : obGenerator) (param : Yoneda00_Param_EF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_E Yoneda1_Param_proj_ff param),
      sval (sval (reparamMor_Form (fst (sval Yoneda1_Param_reparam_rr)) Yoneda1_Form_ff') G param form)
      = sval (sval Yoneda1_Form_ff G param form)  .

  Lemma Congr_data_ALT_of_Congr_data : Congr_data -> Congr_data_ALT.
  Proof.
    intros [X]. move. intros. simpl. apply: X; reflexivity.
  Qed.
  
End Congr_data.

Lemma reparamMorSym_Formatting_cong:
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
         (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
         (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
         (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
          (Yoneda00_Param_EF0 : obGenerator -> Type)
         (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) (Yoneda1_Param_proj0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
         (Yoneda1_Param_subst0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F) (Yoneda1_Form_ff0 : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj0 Yoneda1_Param_subst0)
         (Yoneda1_Param_reparam_conv_ff : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj0 Yoneda1_Param_subst0),
  forall (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff0 Yoneda1_Param_reparam_conv_ff),
reparamMorSym (Yoneda1_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_E) Yoneda1_Param_proj) (Yoneda1_Param_Format_subst Yoneda1_Form_ff)
    (Yoneda1_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_E) Yoneda1_Param_proj0) (Yoneda1_Param_Format_subst Yoneda1_Form_ff0).
Proof.
unshelve eexists. split. 
  - unshelve eexists.
    + unshelve eexists. intros G param_form.
      exists ( sval (sval (fst (sval Yoneda1_Param_reparam_conv_ff))) _ (projT1 param_form)).
      * exists (sval (projT2 param_form)).
        abstract (simpl; rewrite [LHS](proj2_sig (projT2 param_form));  simpl; rewrite [RHS](proj1 (proj2_sig (fst (sval Yoneda1_Param_reparam_conv_ff)))); reflexivity).
      *  abstract (move; intros;  simpl; apply: Yoneda00_Param_Format_quotientLogical; simpl;
                   [exact: (proj2_sig (sval (fst (sval Yoneda1_Param_reparam_conv_ff)))) | reflexivity ]).
    + abstract (split; [ intros G param_format; simpl; exact: (proj1 (proj2_sig (fst (sval Yoneda1_Param_reparam_conv_ff))))
             | intros G param_format; apply: Yoneda00_Param_Format_quotientLogical; simpl;
               [ exact: (proj2 (proj2_sig (fst (sval Yoneda1_Param_reparam_conv_ff))))
               | simpl; apply: (Congr_data_prop Congr_congr_ff); reflexivity ] ] ) .
  - unshelve eexists.
    + unshelve eexists. intros G param_form.
      exists ( sval (sval (snd (sval Yoneda1_Param_reparam_conv_ff))) _ (projT1 param_form)).
      * exists (sval (projT2 param_form)).
        abstract (simpl; rewrite [LHS](proj2_sig (projT2 param_form));  simpl; rewrite [RHS](proj1 (proj2_sig (snd (sval Yoneda1_Param_reparam_conv_ff)))); reflexivity).
      *  abstract (move; intros;  simpl; apply: Yoneda00_Param_Format_quotientLogical; simpl;
                   [exact: (proj2_sig (sval (snd (sval Yoneda1_Param_reparam_conv_ff)))) | reflexivity ]).
    + abstract (split; [ intros G param_format; simpl; exact: (proj1 (proj2_sig (snd (sval Yoneda1_Param_reparam_conv_ff))))
             | intros G param_format; apply: Yoneda00_Param_Format_quotientLogical; simpl;
               [ exact: (proj2 (proj2_sig (snd (sval Yoneda1_Param_reparam_conv_ff))))
               | simpl; symmetry; apply: (Congr_data_prop Congr_congr_ff) ;
                 [ rewrite (proj2 (proj2_sig Yoneda1_Param_reparam_conv_ff)); reflexivity
                 | reflexivity ] ] ] ) . 
  - abstract (split; intros; 
      [ apply: Yoneda00_Param_Format_quotientLogical; simpl;
        [  rewrite (proj1 (proj2_sig Yoneda1_Param_reparam_conv_ff)); reflexivity | reflexivity ]
      | apply: Yoneda00_Param_Format_quotientLogical; simpl;
        [  rewrite (proj2 (proj2_sig Yoneda1_Param_reparam_conv_ff)); reflexivity | reflexivity ] ] ).
Defined.

Lemma congr_PolyCoMod_cong : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
                   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Form_F' : obGenerator -> Type) (Yoneda01_Form_F' : Yoneda01_data Yoneda00_Form_F')
                   (Yoneda00_Param_F' : obGenerator -> Type) (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F') (Yoneda1_FormParam_F' : Yoneda1_FormParam_data Yoneda01_Form_F' Yoneda01_Param_F')
                   (Yoneda00_Param_F'F : obGenerator -> Type) (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F) (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
                   (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F)
                   (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff') (Yoneda00_Form_F'' : obGenerator -> Type)
                   (Yoneda01_Form_F'' : Yoneda01_data Yoneda00_Form_F'') (Yoneda00_Param_F'' : obGenerator -> Type) (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
                   (Yoneda1_FormParam_F'' : Yoneda1_FormParam_data Yoneda01_Form_F'' Yoneda01_Param_F'') (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')
                   (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'') (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
                   (Yoneda1_Form_ff_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_) (Yoneda00_Param_E'E : obGenerator -> Type)
                   (Yoneda01_Param_E'E : Yoneda01_Param_data Yoneda00_Param_E'E) (Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F')
                   (Yoneda1_Param_subst_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F)
                   (Yoneda1_Form_ee' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee')
                   (Yoneda1_Param_reparam_F'F : reparamMorSym Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff' Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee')
                   (Congr_congr_ff' : Congr_data Yoneda1_Form_ff' Yoneda1_Form_ee' Yoneda1_Param_reparam_F'F),
              forall (Yoneda00_Param_E''E' : obGenerator -> Type) (Yoneda01_Param_E''E' : Yoneda01_Param_data Yoneda00_Param_E''E') (Yoneda1_Param_proj_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F'')
                     (Yoneda1_Param_subst_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F')
                     (Yoneda1_Form_ee_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
                     (Yoneda1_Param_reparam_F''F' : reparamMorSym Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_ Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
                     (Congr_congr_ff_ : Congr_data Yoneda1_Form_ff_ Yoneda1_Form_ee_ Yoneda1_Param_reparam_F''F'),
                Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ff' Yoneda1_Form_ff_) (Yoneda1_Form_PolyCoMod Yoneda1_Form_ee' Yoneda1_Form_ee_)
                          (reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong Yoneda1_Param_reparam_F'F Yoneda1_Param_reparam_F''F').
Proof.
  intros; constructor; intros; simpl.
  apply: (Congr_data_prop Congr_congr_ff'); first by rewrite Heqparam'; simpl; reflexivity.
  simpl. apply: (Congr_data_prop Congr_congr_ff_); first by rewrite Heqparam'; simpl; reflexivity.
  exact: Heq.
Qed.

Lemma Congr_Refl :
    forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      Congr_data Yoneda1_Form_ff Yoneda1_Form_ff (reparamMorSym_Refl Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff).
Proof.
    intros. constructor. intros. subst.
    have Heq' : form'0 = form'. apply: Yoneda00_AtParam_quotientLogical. assumption.
    subst. reflexivity.
Qed.    

Lemma Congr_Trans:
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
         (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
         (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
         (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF') (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
         (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
         (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
    forall (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr),
    forall (Yoneda00_Param_EF'' : obGenerator -> Type) (Yoneda01_Param_EF'' : Yoneda01_Param_data Yoneda00_Param_EF'') (Yoneda1_Param_proj_ff'' : Yoneda1_Param_data Yoneda01_Param_EF'' Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff'' : Yoneda1_Param_data Yoneda01_Param_EF'' Yoneda01_Param_F)
           (Yoneda1_Form_ff'' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff'' Yoneda1_Param_subst_ff'')
           (Yoneda1_Param_reparam_rr' : reparamMorSym Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff' Yoneda1_Param_proj_ff'' Yoneda1_Param_subst_ff''),
    forall (Congr_congr_ff' : Congr_data Yoneda1_Form_ff' Yoneda1_Form_ff'' Yoneda1_Param_reparam_rr'),
      Congr_data Yoneda1_Form_ff Yoneda1_Form_ff'' (reparamMorSym_Trans Yoneda1_Param_reparam_rr Yoneda1_Param_reparam_rr').
Proof.
  intros. constructor; intros.
  rewrite -(Congr_data_ALT_of_Congr_data Congr_congr_ff) ; simpl.
  rewrite -(Congr_data_ALT_of_Congr_data Congr_congr_ff') ; simpl.
  apply: (proj2 (proj2_sig Yoneda1_Form_ff'')); assumption.
Qed.

Lemma Congr_Forget_cong:
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
           (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
           (Yoneda00_Param_FE : obGenerator -> Type) (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE) (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
           (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_E) (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_F Yoneda1_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
           (Yoneda00_Param_FE0 : obGenerator -> Type) (Yoneda01_Param_FE0 : Yoneda01_Param_data Yoneda00_Param_FE0) (Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_FE0 Yoneda01_Param_F)
           (Yoneda1_Param_subst_ee0 : Yoneda1_Param_data Yoneda01_Param_FE0 Yoneda01_Param_E)
           (Yoneda1_Form_ee0 : Yoneda1_Form_data Yoneda1_FormParam_F Yoneda1_FormParam_E Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0)
           (Yoneda1_Param_reparam_conv_ee : reparamMorSym Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0),
      forall (Congr_congr_ee : Congr_data Yoneda1_Form_ee Yoneda1_Form_ee0 Yoneda1_Param_reparam_conv_ee),
      Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ee (Yoneda1_Form_Forget Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj))
                      (Yoneda1_Form_PolyCoMod Yoneda1_Form_ee0 (Yoneda1_Form_Forget Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj))
                      (reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong Yoneda1_Param_reparam_conv_ee (reparamMorSym_Refl Yoneda1_Param_proj Yoneda1_Param_subst)).
Proof.
  intros; constructor; intros; simpl. apply: (Congr_data_prop Congr_congr_ee); first by rewrite Heqparam'; simpl; reflexivity.
  simpl. apply: Yoneda00_Form_PiSubst_quotientLogical_rev.
  + exact: Heq.
  + simpl. rewrite Heqparam'. simpl. reflexivity.
Qed.

Lemma Congr_Remember_cong' :
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (Yoneda00_Form_LF : obGenerator -> Type) (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
           (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
           (Yoneda1_Form_ll' Yoneda1_Form_ll'0 : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst),
    forall (Congr_congr_ll'll'0 : Congr_data Yoneda1_Form_ll' Yoneda1_Form_ll'0 (reparamMorSym_Refl Yoneda1_Param_proj Yoneda1_Param_subst)),
      Congr_data (Yoneda1_Form_Remember (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' (Yoneda1_UnitCoMod Yoneda1_FormParam_LF)))
                 (Yoneda1_Form_Remember (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll'0 (Yoneda1_UnitCoMod Yoneda1_FormParam_LF)))
                 (reparamMorSym_Refl (Yoneda1_UnitCoMod_Param Yoneda01_Param_PiSubstF) (Yoneda1_UnitCoMod_Param Yoneda01_Param_PiSubstF)).
Proof.
  intros; constructor; intros; apply: Yoneda00_Form_PiSubst_quotientLogical_ALT; simpl; intros.
  rewrite -[RHS](Congr_data_ALT_of_Congr_data (Congr_congr_ll'll'0))  [RHS]/=.
  apply: (proj2 (proj2_sig Yoneda1_Form_ll'0)); simpl.
  - assumption.
  - simpl; congr ( _ _ ); assumption.
Qed.

Lemma reparamMorSym_morCoMod_comp_UnitCoMod
  : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
                (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
           reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (Yoneda1_UnitCoMod_Param Yoneda01_Param_F) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                         (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst (Yoneda1_UnitCoMod_Param Yoneda01_Param_F) (Yoneda1_UnitCoMod_Param Yoneda01_Param_F) Yoneda1_Param_subst_ff) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff.
Proof.
  intros. unshelve eexists. split. 
  - unshelve eexists.
    + exact: Yoneda1_Param_Subst_proj.
    + abstract (split; 
                [ intros; simpl; reflexivity
                |  intros; simpl; symmetry; exact: (proj2_sig (projT2 param)) ] ) .
  - unshelve eexists.
    + unshelve eexists. intros G param. exists param. exists (sval Yoneda1_Param_subst_ff G param). abstract reflexivity.
      abstract (move; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
                [ reflexivity | apply: (proj2_sig Yoneda1_Param_subst_ff) ]).
    + abstract (split; intros; reflexivity).
  - abstract( split; [ intros; simpl;  apply: Yoneda00_Param_Subst_quotientLogical; simpl;
             [ reflexivity
             | symmetry; exact: (proj2_sig (projT2 param)) ]
           | intros; simpl; reflexivity ] ).
Defined.         
       
Lemma Congr_morCoMod_comp_UnitCoMod
: forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_UnitCoMod Yoneda1_FormParam_F) Yoneda1_Form_ff) Yoneda1_Form_ff (reparamMorSym_morCoMod_comp_UnitCoMod Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff).
Proof.
  intros. constructor. intros. subst.
  have Heq' : form'0 = form'. apply: Yoneda00_AtParam_quotientLogical. assumption.
  subst. reflexivity.
Qed.

Lemma reparamMorSym_UnitCoMod_comp_morCoMod
  : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
                (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
           reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj  Yoneda1_Param_proj_ff (Yoneda1_UnitCoMod_Param Yoneda01_Param_E) (Yoneda1_UnitCoMod_Param Yoneda01_Param_E))
                         (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff (Yoneda1_UnitCoMod_Param Yoneda01_Param_E)) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff.
Proof.
  intros. unshelve eexists. split. 
  - unshelve eexists.
    + exact: Yoneda1_Param_Subst_subst.
    + abstract (split; 
                [ intros; simpl; exact: (proj2_sig (projT2 param))
                | intros; simpl; reflexivity] ) .
  - unshelve eexists.
    + unshelve eexists. intros G param. exists (sval Yoneda1_Param_proj_ff G param). exists param. abstract reflexivity.
      abstract (move; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
                [ apply: (proj2_sig Yoneda1_Param_proj_ff) | reflexivity  ]).
    + abstract (split; intros; reflexivity).
  - abstract( split; [ intros; simpl;  apply: Yoneda00_Param_Subst_quotientLogical; simpl;
                       [ exact: (proj2_sig (projT2 param))
                       | reflexivity ]
           | intros; simpl; reflexivity ] ).
Defined.
       
Lemma Congr_UnitCoMod_comp_morCoMod
: forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ff (Yoneda1_UnitCoMod Yoneda1_FormParam_E)) Yoneda1_Form_ff (reparamMorSym_UnitCoMod_comp_morCoMod Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff).
Proof.
  intros. constructor. intros. subst. simpl in *.
  apply: (proj2 (proj2_sig Yoneda1_Form_ff)).
  - reflexivity.
  - simpl. assumption.
Qed.

Lemma Congr_Remember_comp_Forget :
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (Yoneda00_Form_LF : obGenerator -> Type) (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
           (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
           (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst),
      Congr_data
        (Yoneda1_Form_PolyCoMod (Yoneda1_Form_Forget Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj)
                                (Yoneda1_Form_Remember (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' (Yoneda1_UnitCoMod Yoneda1_FormParam_LF)))) Yoneda1_Form_ll'
        (reparamMorSym_UnitCoMod_comp_morCoMod Yoneda1_Param_proj Yoneda1_Param_subst).
Proof.
  intros; constructor; intros; simpl. apply: (proj2 (proj2_sig Yoneda1_Form_ll')); simpl.
  - assumption. 
  - rewrite -(proj2 (proj2_sig Yoneda01_Form_LF)). assumption.
Qed.

Lemma Congr_PolyTransf_default_cong''' :
forall (Yoneda00_Form_F : obGenerator -> Type)
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_K : obGenerator -> Type)
    (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
    (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
    (Yoneda1_Param_ee_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
                              param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_ee_ G paramlocal) H param = sval (Yoneda1_Param_ee_ G' paramlocal') H param')
    (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
    (Yoneda00_Form_K : obGenerator -> Type)
    (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
    (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
    (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form))
    (Yoneda1_Form_ee_morphism : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
                               (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'')
                               (formm : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) (Is_Parameter0 G') <| paramm )),
                             let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                             let formm' := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramm) (formm o>GeneratorAtParam g)) in
                             sval (sval (Yoneda1_Form_ee__ G param form) G'' paramm' formm') =
                             sval (sval (Yoneda1_Form_ee__ G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form)) G'' paramm formm))
    (Yoneda1_Param_reparam_ee : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form))
    (Yoneda1_Param_reparam_ee_morphism : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (G' : obGenerator)
                                        (g : 'Generator( G' ~> G )) (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G''),
                                      let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                                      projT1 (sval (sval (sval (Yoneda1_Param_reparam_ee G param form)).1) G'' paramm') =
                                      projT1
                                        (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G''
                                           (sval (sval (sval (Yoneda1_Param_reparam_ee G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form))).1) G'' paramm)))
    (Yoneda1_Param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
    (Yoneda1_Param_dd_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
                              param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_dd_ G paramlocal) H param = sval (Yoneda1_Param_dd_ G' paramlocal') H param')
    (Yoneda1_Param_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
    (Yoneda1_Form_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_dd__ G param form))
    (Yoneda1_Form_dd_morphism : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
                               (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'')
                               (formm : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) (Is_Parameter0 G') <| paramm )),
                             let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                             let formm' := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramm) (formm o>GeneratorAtParam g)) in
                             sval (sval (Yoneda1_Form_dd__ G param form) G'' paramm' formm') =
                             sval (sval (Yoneda1_Form_dd__ G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form)) G'' paramm formm))
    (Yoneda1_Param_reparam_dd : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_dd_ G (sval Yoneda1_Param_subst G param))
                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_dd__ G param form))
    (Yoneda1_Param_reparam_dd_morphism : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (G' : obGenerator)
                                        (g : 'Generator( G' ~> G )) (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G''),
                                      let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                                      projT1 (sval (sval (sval (Yoneda1_Param_reparam_dd G param form)).1) G'' paramm') =
                                      projT1
                                        (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G''
                                           (sval (sval (sval (Yoneda1_Param_reparam_dd G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form))).1) G'' paramm)))
    (Yoneda1_Param_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
                                reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal)
                                  (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_dd_ G paramlocal))
    (Yoneda1_Param_reparam_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                                 reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form)
                                   (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_dd__ G param form))
    (Congr_congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                       Congr_data (Yoneda1_Form_ee__ G param form) (Yoneda1_Form_dd__ G param form) (Yoneda1_Param_reparam_eedd__ G param form)),
  Congr_data (Yoneda1_Form_PolyTransf_default Yoneda1_Param_ee_morphism Yoneda1_Param_reparam_ee_morphism Yoneda1_Form_ee_morphism)
    (Yoneda1_Form_PolyTransf_default Yoneda1_Param_dd_morphism Yoneda1_Param_reparam_dd_morphism Yoneda1_Form_dd_morphism)
    (reparamMorSym_PolyTransf_pseudoCode_ReParam_default_cong Yoneda1_Param_ee_morphism Yoneda1_Param_dd_morphism Yoneda1_Param_reparam_eedd_).
Proof.
  intros. constructor. intros. simpl.
  set parammm_for_dd : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (sval (projT1 (projT2 (sval form'0))))) G'
      := (X in sval (sval (Yoneda1_Form_dd__ _ _ _) _ X _) = _)  .
  set formmm_for_dd : 'Generator ( G' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (sval (projT1 (projT2 (sval form'0))))) (Is_Parameter0 G') <| parammm_for_dd )
      := (X in sval (sval (Yoneda1_Form_dd__ _ _ _) _ _ X) = _).
  set parammm_for_ee : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (sval (projT1 (projT2 (sval form'))))) G'
    := (X in _ = sval (sval (Yoneda1_Form_ee__ _ _ _) _ X _)) .
  set formmm_for_ee : 'Generator ( G' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (sval (projT1 (projT2 (sval form'))))) (Is_Parameter0 G') <| parammm_for_ee )
    := (X in _ = sval (sval (Yoneda1_Form_ee__ _ _ _) _ _ X)).

  remember (sval (projT1 (projT2 (sval form')))) as paramm eqn:Heqparamm in |- ; symmetry in Heqparamm.
  remember (Yoneda01_AtParam_transp' Heqparamm (projT2 (projT2 (sval form')))) as formm eqn:Heqformm in |- ; symmetry in Heqformm.
  have {Heqformm} Heqformm := (f_equal sval Heqformm).
  have Heqparamm0 : sval (projT1 (projT2 (sval form'0))) = paramm by rewrite Heq; exact: Heqparamm.
  have Heqformm0 : Yoneda01_AtParam_transp' Heqparamm0 (projT2 (projT2 (sval form'0))) = formm
    by apply: Yoneda00_AtParam_quotientLogical; simpl; rewrite Heq; exact: Heqformm.
  have {Heqformm0} Heqformm0 := (f_equal sval Heqformm0).
  rewrite [RHS](Yoneda1_Form_PolyTransf_default_quotientLogical Yoneda1_Form_ee__ Heqparamm Heqformm
              (Yoneda01_Local_transpP (f_equal (sval Yoneda1_Param_subst _) Heqparamm) parammm_for_ee) (Yoneda01_AtParam_transp'P (eq_refl _) _)).
  rewrite [LHS](Yoneda1_Form_PolyTransf_default_quotientLogical Yoneda1_Form_dd__ Heqparamm0 Heqformm0
              (Yoneda01_Local_transpP (f_equal (sval Yoneda1_Param_subst _) Heqparamm0) parammm_for_dd) (Yoneda01_AtParam_transp'P (eq_refl _) _)).

  set parammm_for'_dd := (X in sval (sval (Yoneda1_Form_dd__ _ _ _ ) _ X _) = _) .
  set formmm_for'_dd := (X in sval (sval (Yoneda1_Form_dd__ _ _ _) _ _ X) = _) .
  set parammm_for'_ee := (X in _ = sval (sval (Yoneda1_Form_ee__ _ _ _ ) _ X _) ) .
  set formmm_for'_ee := (X in _ = sval (sval (Yoneda1_Form_ee__ _ _ _) _ _ X) ) .

  apply (Congr_data_prop (Congr_congr_eedd__ _ _ _)); last reflexivity.
  apply: Yoneda00_Local_quotientLogical.
  rewrite [LHS]unitParametrizator_polyParametrizator;
  rewrite -[in LHS](proj1 (proj2_sig (Is_Parameter0 G'))); rewrite [LHS]polyParametrizator_morphism.
  rewrite [RHS]unitParametrizator_polyParametrizator;
  rewrite -[in RHS](proj1 (proj2_sig (Is_Parameter0 G'))); rewrite [RHS]polyParametrizator_morphism;
  congr ( _ o>Parametrizator _).
  rewrite [LHS](proj1 (proj2_sig (fst (sval (Yoneda1_Param_reparam_dd _ _ _ ))))). rewrite [LHS]/=.
  rewrite [RHS](proj1 (proj2_sig (fst (sval (Yoneda1_Param_reparam_eedd__ _ _ _ ))))). rewrite [RHS]/=.
  subst parammm_for'_ee; subst parammm_for_ee.
  rewrite [RHS](proj1 (proj2_sig (fst (sval (Yoneda1_Param_reparam_ee _ _ _ ))))). rewrite [RHS]/=. reflexivity.
Qed.

Lemma Congr_PolyElement_default_comp_PolyTransf_default' :
forall (  Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
                              param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_ee_ G paramlocal) H param = sval (Yoneda1_Param_ee_ G' paramlocal') H param')
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Form_ee_morphism : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
                               (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'')
                               (formm : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) (Is_Parameter0 G') <| paramm )),
                             let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                             let formm' := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramm) (formm o>GeneratorAtParam g)) in
                             sval (sval (Yoneda1_Form_ee__ G param form) G'' paramm' formm') =
                             sval (sval (Yoneda1_Form_ee__ G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form)) G'' paramm formm))
  (Yoneda1_Param_reparam_ee : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Param_reparam_ee_morphism : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (G' : obGenerator)
                                        (g : 'Generator( G' ~> G )) (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G''),
                                      let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                                      projT1 (sval (sval (sval (Yoneda1_Param_reparam_ee G param form)).1) G'' paramm') =
                                      projT1
                                        (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G''
                                           (sval (sval (sval (Yoneda1_Param_reparam_ee G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form))).1) G'' paramm)))
  (G : obGenerator)
  (param : Yoneda00_Param_SubstF G)
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
  Congr_data
    (Yoneda1_Form_PolyCoMod (Yoneda1_Form_PolyTransf_default Yoneda1_Param_ee_morphism Yoneda1_Param_reparam_ee_morphism Yoneda1_Form_ee_morphism) (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst form))
    (Yoneda1_Form_PolyCoMod (Yoneda1_UnitCoMod Yoneda1_FormParam_K) (Yoneda1_Form_ee__ G param form))
    (reparamMorSym_Trans (reparamMorSym_PolyElement_ReParam_default_comp_PolyTransf_ReParam_default Yoneda1_Param_ee_morphism (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
       (reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong (reparamMorSym_Refl (Yoneda1_UnitCoMod_Param Yoneda01_Param_K) (Yoneda1_UnitCoMod_Param Yoneda01_Param_K)) (Yoneda1_Param_reparam_ee G param form))) .
Proof.
  intros; constructor; intros;  simpl.
  rewrite -[RHS]Yoneda1_Form_ee_morphism [RHS]/=.
  apply: (Yoneda1_Form_PolyTransf_default_quotientLogical Yoneda1_Form_ee__); simpl;
    [ reflexivity | reflexivity
      | | rewrite -polyGenerator_unitGenerator; assumption ].
  rewrite Heqparam'. simpl. 
  rewrite -[RHS]Yoneda1_Param_reparam_ee_morphism [RHS]/=.
  congr (projT1 (sval _  _ _)).
  apply: Yoneda00_Local_quotientLogical; simpl. rewrite -[RHS]polyParametrizator_unitParametrizator.
  rewrite -[in RHS]Heq. rewrite [RHS](proj2_sig form'0).  rewrite Heqparam'; simpl. 
  rewrite [RHS](proj1 (proj2_sig (fst (sval (Yoneda1_Param_reparam_ee G param form))))). simpl.
   do 2 rewrite -unitParametrizator_polyParametrizator. reflexivity.
Qed.

Lemma Congr_Assoc_congrPseudoCode
: forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D) (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
           (Yoneda1_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D) (Yoneda00_Param_DE : obGenerator -> Type) (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
           (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
           (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_D Yoneda1_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) (Yoneda00_Form_C : obGenerator -> Type)
           (Yoneda01_Form_C : Yoneda01_data Yoneda00_Form_C) (Yoneda00_Param_C : obGenerator -> Type) (Yoneda01_Param_C : Yoneda01_Param_data Yoneda00_Param_C)
           (Yoneda1_FormParam_C : Yoneda1_FormParam_data Yoneda01_Form_C Yoneda01_Param_C) (Yoneda00_Param_CD : obGenerator -> Type) (Yoneda01_Param_CD : Yoneda01_Param_data Yoneda00_Param_CD)
           (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_C) (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_D)
           (Yoneda1_Form_dd : Yoneda1_Form_data Yoneda1_FormParam_C Yoneda1_FormParam_D Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd),
      Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_PolyCoMod Yoneda1_Form_ff Yoneda1_Form_ee) Yoneda1_Form_dd)
                 (Yoneda1_Form_PolyCoMod Yoneda1_Form_ff (Yoneda1_Form_PolyCoMod Yoneda1_Form_ee Yoneda1_Form_dd))
                 (reparamMorSym_Assoc_reparam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd).
Proof.
    intros; constructor; intros; simpl; apply: (proj2 (proj2_sig  Yoneda1_Form_ff)); first (by subst; reflexivity);
  simpl; apply: (proj2 (proj2_sig  Yoneda1_Form_ee)); first (by subst; reflexivity); 
  simpl; apply: (proj2 (proj2_sig  Yoneda1_Form_dd)); first (by subst; reflexivity); assumption.
Qed.

Lemma Congr_Sym :
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF') (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
           (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
           (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
           (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr),
    Congr_data Yoneda1_Form_ff' Yoneda1_Form_ff (reparamMorSym_Sym Yoneda1_Param_reparam_rr).
Proof.
  intros. constructor. intros. symmetry. eapply Congr_congr_ff.
  symmetry. subst. simpl. rewrite (proj2 (proj2_sig Yoneda1_Param_reparam_rr)). reflexivity. 
  symmetry. assumption.
Qed.

Lemma reparamMorSym_PolyTransf_default_morphism :
  forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda00_Param_SubstF : obGenerator -> Type)
           (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Yoneda00_Param_K : obGenerator -> Type)
           (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
           (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
           (Yoneda1_Param_ee_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                               (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                               (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
               param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' ->
               sval (Yoneda1_Param_ee_ G paramlocal) H param = sval (Yoneda1_Param_ee_ G' paramlocal') H param') (Yoneda00_Param_E : obGenerator -> Type)
           (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_KE_ : obGenerator -> Type) (Yoneda01_Param_KE_ : Yoneda01_Param_data Yoneda00_Param_KE_)
           (Yoneda1_Param_proj_ee'_ : Yoneda1_Param_data Yoneda01_Param_KE_ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'_ : Yoneda1_Param_data Yoneda01_Param_KE_ Yoneda01_Param_E)
           (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D) (Yoneda00_Param_ED : obGenerator -> Type) (Yoneda01_Param_ED : Yoneda01_Param_data Yoneda00_Param_ED)
           (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_E) (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_D),
      reparamMorSym
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_dd (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj Yoneda1_Param_ee_morphism Yoneda1_Param_proj_ee'_)
                                                   (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst Yoneda1_Param_ee_morphism Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_))
        (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd
                                                    (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst Yoneda1_Param_ee_morphism Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_))
        (Yoneda1_PolyTransf_pseudoCode_ReParam_default_proj Yoneda1_Param_ee_morphism (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_dd Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_))
        (Yoneda1_PolyTransf_pseudoCode_ReParam_default_subst Yoneda1_Param_ee_morphism (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_dd Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_)
                                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd Yoneda1_Param_subst_ee'_)).
Proof.
    intros. apply: reparamMorSym_Sym; exact: reparamMorSym_Assoc_reparam.
Defined.

Lemma Congr_PolyTransf_default_morphism :
forall (Yoneda00_Form_F : obGenerator -> Type)
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : forall (G G' : obGenerator) (p : 'Parametrizator ( Parameter0 G' ~> Parameter0 G )) (paramlocal : Yoneda00_Param_SumSubstF G) (paramlocal' : Yoneda00_Param_SumSubstF G')
                                (Heqparamlocal : paramlocal' = p o>Parametrizator_ paramlocal) (H : obGenerator) (param' : Yoneda00_Local_ Yoneda1_Param_subst paramlocal' H)
                                (param : Yoneda00_Local_ Yoneda1_Param_subst paramlocal H),
                              param = sval (Yoneda01_Local_dep' Yoneda1_Param_subst Heqparamlocal) H param' -> sval (Yoneda1_Param_ee_ G paramlocal) H param = sval (Yoneda1_Param_ee_ G' paramlocal') H param')
  (Yoneda00_Param_E : obGenerator -> Type)
  (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Yoneda00_Param_KE_ : obGenerator -> Type)
  (Yoneda01_Param_KE_ : Yoneda01_Param_data Yoneda00_Param_KE_)
  (Yoneda1_Param_proj_ee'_ : Yoneda1_Param_data Yoneda01_Param_KE_ Yoneda01_Param_K)
  (Yoneda1_Param_subst_ee'_ : Yoneda1_Param_data Yoneda01_Param_KE_ Yoneda01_Param_E)
  (Yoneda1_Param_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G),
                       Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param -> Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G param)) Yoneda01_Param_K)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Form_ee_morphism : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
                               (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G'')
                               (formm : 'Generator ( G'' ~> G' @_ Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) (Is_Parameter0 G') <| paramm )),
                             let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                             let formm' := (Yoneda01_AtParam_transp'' (Form_morphism_Heq paramm) (formm o>GeneratorAtParam g)) in
                             sval (sval (Yoneda1_Form_ee__ G param form) G'' paramm' formm') =
                             sval (sval (Yoneda1_Form_ee__ G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form)) G'' paramm formm))
  (Yoneda00_Form_E : obGenerator -> Type)
  (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
  (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
  (Yoneda00_Param_KE__ : obGenerator -> Type)
  (Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
  (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
  (Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
  (Yoneda1_Param_reparam_ee : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                             reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param))
                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_ee__ G param form))
  (Yoneda1_Param_reparam_ee_morphism : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (G' : obGenerator)
                                        (g : 'Generator( G' ~> G )) (G'' : obGenerator) (paramm : Yoneda00_Local_ Yoneda1_Param_subst (sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_ param)) G''),
                                      let paramm' := sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G'' paramm in
                                      projT1 (sval (sval (sval (Yoneda1_Param_reparam_ee G param form)).1) G'' paramm') =
                                      projT1
                                        (sval (Yoneda01_Local_dep' Yoneda1_Param_subst (eq_sym (proj2_sig Yoneda1_Param_subst G G' (Parameter1 g) param))) G''
                                           (sval (sval (sval (Yoneda1_Param_reparam_ee G' (Parameter1 g o>Parametrizator_ param) (g o>GeneratorAtParam_ form))).1) G'' paramm)))
  (Yoneda1_Param_reparam_ee' : reparamMorSym Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_ Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
  (Yoneda00_Form_D : obGenerator -> Type)
  (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D)
  (Yoneda00_Param_D : obGenerator -> Type)
  (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Yoneda1_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D)
  (Yoneda00_Param_ED : obGenerator -> Type)
  (Yoneda01_Param_ED : Yoneda01_Param_data Yoneda00_Param_ED)
  (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_E)
  (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_D)
  (Yoneda1_Form_dd : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_D Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd),
  Congr_data
    (Yoneda1_Form_PolyCoMod Yoneda1_Form_dd
       (Yoneda1_Form_PolyCoMod (reparamMor_Form (sval Yoneda1_Param_reparam_ee').1 Yoneda1_Form_ee'__)
          (Yoneda1_Form_PolyTransf_default Yoneda1_Param_ee_morphism Yoneda1_Param_reparam_ee_morphism Yoneda1_Form_ee_morphism)))
    (Yoneda1_Form_PolyCoMod
       (reparamMor_Form (sval (reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong (reparamMorSym_Refl Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd) Yoneda1_Param_reparam_ee')).1
          (Yoneda1_Form_PolyCoMod Yoneda1_Form_dd Yoneda1_Form_ee'__)) (Yoneda1_Form_PolyTransf_default Yoneda1_Param_ee_morphism Yoneda1_Param_reparam_ee_morphism Yoneda1_Form_ee_morphism))
    (reparamMorSym_PolyTransf_default_morphism Yoneda1_Param_ee_morphism Yoneda1_Param_proj_ee'_ Yoneda1_Param_subst_ee'_ Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd).
Proof.
  intros. apply: Congr_Sym. constructor. intros.
  etransitivity.
  eapply (Congr_data_prop (Congr_Assoc_congrPseudoCode Yoneda1_Form_dd (reparamMor_Form (sval Yoneda1_Param_reparam_ee').1 Yoneda1_Form_ee'__) _ )).
  eassumption. eassumption.
  Time simpl; eapply ((proj2 (proj2_sig  Yoneda1_Form_dd))); first reflexivity. (* 45sec *)
  simpl; apply: (proj2 (proj2_sig Yoneda1_Form_ee'__)); first reflexivity.
  Time simpl; apply: (proj2 (proj2_sig  (Yoneda1_Form_ee__ _ _ _))); reflexivity.  (* 34 sec *)
Qed. 

Lemma reparamMorSym_View1_ReParam_comp_View1_ReParam
     : forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator ( Parameter0 G ~> Q )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (G' : obGenerator)
         (p' : 'Parametrizator ( Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P'),
     reparamMorSym
                  (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P) (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P') (Yoneda1_Param_View1 p'))
                  (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P) (Yoneda1_Param_View1 p) (Yoneda1_Param_View1 p'))
                  (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P') (Yoneda1_Param_View1 (is_Parameter0_transp_codom is_Parameter0_P p' o>Parametrizator p)).
Proof.
  intros. unshelve eexists. split. 
  - unshelve eexists.
    + exact: Yoneda1_Param_Subst_proj.
    + abstract (split; [ intros; simpl; reflexivity
             | intros; simpl; rewrite polyParametrizator_morphism;
              congr ( _ _ ); rewrite polyParametrizator_morphism; rewrite -[X in X o>Parametrizator _ = _](proj2_sig (projT2 param));
              simpl; rewrite -polyParametrizator_morphism; rewrite (proj1 (proj2_sig is_Parameter0_P)); rewrite -unitParametrizator_polyParametrizator;
              reflexivity ] ).
  - unshelve eexists.
    + unshelve eexists. intros G0 param. exists param.
      exists (sval (Yoneda1_Param_View1 (snd (sval is_Parameter0_P))) _ (sval  (Yoneda1_Param_View1 p') G0 param)).
      abstract (simpl; rewrite -polyParametrizator_morphism; rewrite (proj2 (proj2_sig is_Parameter0_P));
                rewrite -unitParametrizator_polyParametrizator; reflexivity).
      abstract (move; intros; apply: Yoneda00_Param_Subst_quotientLogical; simpl;
        [ reflexivity
        | simpl; rewrite -?polyParametrizator_morphism; reflexivity ] ).
    + abstract (split; [ intros; reflexivity
                       | intros;  simpl;  rewrite -?polyParametrizator_morphism; reflexivity ] ).
  -  abstract (split; [ intros; simpl;  apply: Yoneda00_Param_Subst_quotientLogical; simpl;
             [ reflexivity
             | simpl; rewrite -[X in X o>Parametrizator _ = _](proj2_sig (projT2 param));
              simpl; rewrite -polyParametrizator_morphism; rewrite (proj1 (proj2_sig is_Parameter0_P)); rewrite -unitParametrizator_polyParametrizator;
                reflexivity ]
           | intros; simpl; reflexivity ] ) .
Defined.

Lemma reparamSym_View1_ReParam_comp_PolyElement_ReParam_default
     : forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
         (Yoneda00_Param_SubstF : obGenerator -> Type)
         (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
         (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator)
         (is_Parameter0_P : is_Parameter0 G P) (G' : obGenerator) (p' : 'Parametrizator ( Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P'),
     reparamMorSym
                  (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst paramlocal is_Parameter0_P)
                     (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P') (Yoneda1_Param_View1 p'))
                  (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst paramlocal is_Parameter0_P)
                     (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst paramlocal) (Yoneda1_Param_View1 p'))
                  (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst (is_Parameter0_transp_codom is_Parameter0_P p' o>Parametrizator_[sval Yoneda01_Param_SumSubstF] paramlocal) is_Parameter0_P')
                  (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst (is_Parameter0_transp_codom is_Parameter0_P p' o>Parametrizator_ paramlocal)).
Proof.
  intros. unshelve eexists. split.
  - unshelve eexists.
    + unshelve eexists.
      intros G0 paramsubst. exists (projT1 paramsubst).
      { (* logiccal modulo part *) 
        abstract (exists (sval (projT2 (*this projT2 of local must be under abstract ...*) (sval (projT2 paramsubst))));
                    simpl; rewrite (proj2_sig (projT2 (sval (projT2 paramsubst)))); simpl;
                    rewrite [RHS](proj1 (proj2_sig Yoneda01_Param_SumSubstF));
                    congr ( _  o>Parametrizator_ paramlocal ); rewrite polyParametrizator_morphism;
                    rewrite -[X in _ =  X o>Parametrizator _](proj2_sig (projT2 paramsubst)); simpl;
                    simpl; rewrite -polyParametrizator_morphism; rewrite (proj1 (proj2_sig is_Parameter0_P));
                    rewrite -unitParametrizator_polyParametrizator; reflexivity) .
      }
      abstract (move; intros; simpl; apply: Yoneda00_Local_quotientLogical; simpl; reflexivity).
    + abstract ( split; [intros; simpl;  reflexivity
             | intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl;  simpl; rewrite (proj1 (proj2_sig Yoneda01_Param_SumSubstF));
                congr ( _  o>Parametrizator_ paramlocal );  rewrite polyParametrizator_morphism;
              rewrite -[X in X o>Parametrizator _ = _ ](proj2_sig (projT2 param)); simpl;
              simpl; rewrite -polyParametrizator_morphism; rewrite (proj1 (proj2_sig is_Parameter0_P));
                rewrite -unitParametrizator_polyParametrizator; reflexivity ] ) .
  - unshelve eexists.
    + unshelve eexists.
      * intros G0 paramm. exists (projT1 paramm).
        unshelve eexists. exists (sval (Yoneda1_Param_View1 (snd (sval is_Parameter0_P))) _ (sval  (Yoneda1_Param_View1 p') _ (projT1 paramm))).
        (* exists (sval (Yoneda1_Param_View1 p') _ (projT1 paramm)). *)
        { (* logiccal modulo part *)
          abstract ( exists (sval (projT2 paramm)) (*/!\ HERE OK USE OF projT2 of _Local_ *);
                       simpl; rewrite (proj2_sig (projT2 paramm)); simpl;
                       rewrite (proj1 (proj2_sig Yoneda01_Param_SumSubstF)); rewrite -?polyParametrizator_morphism; reflexivity ). 
        }
        abstract (simpl; simpl; rewrite -polyParametrizator_morphism; rewrite (proj2 (proj2_sig is_Parameter0_P));
                  rewrite -unitParametrizator_polyParametrizator; reflexivity ).
      * abstract (move; intros; simpl; apply: Yoneda00_Param_Subst_quotientLogical; first (simpl; reflexivity);
                  apply: Yoneda00_Local_quotientLogical; simpl; rewrite -?polyParametrizator_morphism; reflexivity ).
    + abstract (split; [ intros; simpl; reflexivity
             | intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; rewrite (proj1 (proj2_sig Yoneda01_Param_SumSubstF));
               rewrite -?polyParametrizator_morphism; reflexivity ] ) .
  - abstract (split; [ intros; simpl;  apply: Yoneda00_Param_Subst_quotientLogical; first (simpl; reflexivity);
             apply: Yoneda00_Local_quotientLogical; simpl;
             rewrite -[X in X o>Parametrizator _ = _](proj2_sig (projT2 param)); simpl;
              simpl; rewrite -polyParametrizator_morphism; rewrite (proj1 (proj2_sig is_Parameter0_P));
                rewrite -unitParametrizator_polyParametrizator; reflexivity
             | intros; simpl; apply: Yoneda00_Local_quotientLogical; simpl; reflexivity ] ) . 
Defined.

Lemma reparamMorSym_PolyElement_ReParam_default_cong
     : forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
         (Yoneda00_Param_SubstF : obGenerator -> Type)
         (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
          (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator)
         (is_Parameter0_P : is_Parameter0 G P) (paramlocal' : Yoneda00_Param_SumSubstF G) (is_Parameter0_P' : is_Parameter0 G P)
         (Heqparamlocal : paramlocal' = paramlocal)
         (Heqis : fst (sval is_Parameter0_P') = fst (sval is_Parameter0_P)),
 reparamMorSym (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst paramlocal is_Parameter0_P)
                  (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst paramlocal) (Yoneda1_PolyElement_pseudoCode_ReParam_default_proj Yoneda1_Param_subst paramlocal' is_Parameter0_P')
                  (Yoneda1_PolyElement_pseudoCode_ReParam_default_subst Yoneda1_Param_subst paramlocal').
Proof.
  intros. unshelve eexists. split.
  - unshelve eexists.
    + unshelve eexists.
      * intros G0 paramm. exists (projT1 paramm).
        { (* logiccal modulo part *) abstract (exists (sval (projT2 paramm)); (*/!\ HERE OK USE OF projT2 of _Local_ *)
                                                 simpl; rewrite (proj2_sig (projT2 paramm)); simpl; subst; reflexivity). 
        }
      * abstract (move; intros; simpl; apply: Yoneda00_Local_quotientLogical; simpl; reflexivity).
    + abstract (split; [intros ? param; simpl; subst; simpl; congr ( (projT1 param) o>Parametrizator _); assumption
                       | intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; subst; simpl; reflexivity ] ).
  - unshelve eexists.
    + unshelve eexists.
      * intros G0 paramm. exists (projT1 paramm).
        { (* logiccal modulo part *) abstract (exists (sval (projT2 paramm)); (*/!\ HERE OK USE OF projT2 of _Local_ *)
                                                 simpl; rewrite (proj2_sig (projT2 paramm)); simpl; subst; reflexivity). 
        }
      * abstract (move; intros; simpl; apply: Yoneda00_Local_quotientLogical; simpl; reflexivity).
    + abstract ( split; [ intros ? param; simpl; subst; simpl; congr ( (projT1 param) o>Parametrizator _); symmetry; assumption
                        | intros; apply: Yoneda00_Param_SumImage_quotientLogical; simpl; subst; simpl; reflexivity ] ). 
  - abstract (split; [ intros; simpl;  apply: Yoneda00_Local_quotientLogical; simpl; reflexivity
                     | intros; simpl;  apply: Yoneda00_Local_quotientLogical; simpl; reflexivity ] ).
Defined.

Lemma Congr_PolyElement_default_cong
     : forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
         (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) 
         (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
         (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) 
         (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) 
         (G : obGenerator) (param : Yoneda00_Param_SubstF G)
         (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (param' : Yoneda00_Param_SubstF G) (form' : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param')
         (Heqparam : param' = param)
         (Heqform : sval form' = sval form),
    Congr_data (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst form) (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst form')
                   (reparamMorSym_PolyElement_ReParam_default_cong Yoneda1_Param_subst (f_equal (sval Yoneda1_Param_subst G) Heqparam) (erefl (fst (sval (Is_Parameter0 G))))).
Proof.
  intros. constructor. intros. apply: Yoneda00_Form_SumSubst_quotientLogical; simpl.
  - reflexivity.
  - subst. congr ((Parameter1  _) o>Parametrizator_ _). assumption.
  - congr ( _ o>Generator_ _ ); assumption.
Qed.

Lemma View1_comp_PolyElement_default_Heq :
    forall (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda00_Param_SubstF : obGenerator -> Type)
           (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (G : obGenerator)
           (param : Yoneda00_Param_SubstF G) (G' : obGenerator) (g : 'Generator( G' ~> G )),
    sval Yoneda1_Param_subst G' (Parameter1 g o>Parametrizator_[sval Yoneda01_Param_SubstF] param) = is_Parameter0_transp_codom (Is_Parameter0 G) (Parameter1 g) o>Parametrizator_[sval Yoneda01_Param_SumSubstF] sval Yoneda1_Param_subst G param .
Proof.
  intros. rewrite -[X in _ = X o>Parametrizator_ _]unitParametrizator_polyParametrizator. rewrite (proj2_sig Yoneda1_Param_subst). reflexivity.
Qed.

Lemma Congr_View1_comp_PolyElement_default :
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (G : obGenerator) (param : Yoneda00_Param_SubstF G)
           (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (G' : obGenerator) (g : 'Generator( G' ~> G )),
      Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst form) (Yoneda1_Form_View1' g)) (Yoneda1_Form_PolyElement_default Yoneda1_Param_subst (g o>GeneratorAtParam_[sval (Yoneda01_AtParam_(Yoneda1_FormParam_F) _)] form))
                 (reparamMorSym_Trans (reparamSym_View1_ReParam_comp_PolyElement_ReParam_default Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G) (Parameter1 g) (Is_Parameter0 G'))
                                      (reparamMorSym_PolyElement_ReParam_default_cong Yoneda1_Param_subst
                   (View1_comp_PolyElement_default_Heq _ _ _)
                   (erefl (fst (sval ((Is_Parameter0 G'))))))).
Proof.
  intros. constructor. intros. apply: Yoneda00_Form_SumSubst_quotientLogical; simpl.
  - reflexivity.
  - rewrite (proj1 (proj2_sig Yoneda01_Param_SubstF)). rewrite -Parameter_morphism.  congr ((Parameter1 ( _ o>Generator _)) o>Parametrizator_ _). assumption.
  - rewrite (proj1 (proj2_sig Yoneda01_Form_F)). congr ( ( _ o>Generator _) o>Generator_ _). assumption.
Qed.
        
Lemma reparamMorSym_View1_ReParam_cong : 
    forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    forall (G' : obGenerator) (p' : 'Parametrizator(  Parameter0 G' ~> Q )) (is_Parameter0_P' : is_Parameter0 G' P),
    forall (g : reparamMorSymGenerator G' G),
      forall (Heqparam : p' = (Parameter1 (fst (sval g))) o>Parametrizator p),
      forall (Heqis : fst (sval is_Parameter0_P') =  fst (sval (is_Parameter0_transformation  g is_Parameter0_P)) ),
        reparamMorSym (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P) (Yoneda1_Param_View1 p) (Yoneda1_Param_View1_proj_is_Parameter0 is_Parameter0_P') (Yoneda1_Param_View1 p') .
Proof.
  intros. unshelve eexists. split. 
  - unshelve eexists.
    + exact (Yoneda1_Param_View1 (Parameter1 (snd (sval g)))).
    + abstract (split;
      [ intros; simpl; subst; rewrite Heqis; rewrite -polyParametrizator_morphism;
        rewrite [X in _ o>Parametrizator X = _]polyParametrizator_morphism;
        rewrite - Parameter_morphism; rewrite (proj2 (proj2_sig g)); rewrite -Parameter_unitGenerator;
        rewrite -polyParametrizator_unitParametrizator; reflexivity
      | intros ? param; simpl; subst;
      rewrite -polyParametrizator_morphism; congr (param o>Parametrizator _);
      rewrite polyParametrizator_morphism;  rewrite - Parameter_morphism;  rewrite (proj2 (proj2_sig g)); rewrite -Parameter_unitGenerator; 
      rewrite -polyParametrizator_unitParametrizator; reflexivity ] ) .
  - unshelve eexists.
    + exact (Yoneda1_Param_View1 (Parameter1 (fst (sval g)))).
    + abstract (split;
                [ intros; simpl; subst; rewrite Heqis; rewrite -polyParametrizator_morphism; reflexivity
                | intros; simpl; subst; rewrite -polyParametrizator_morphism; reflexivity ] ) .
  - abstract (split; intros; simpl;
    [ rewrite -polyParametrizator_morphism;  rewrite - Parameter_morphism;  rewrite (proj2 (proj2_sig g)); rewrite -Parameter_unitGenerator;
    rewrite -unitParametrizator_polyParametrizator; reflexivity 
    | rewrite -polyParametrizator_morphism;  rewrite - Parameter_morphism;  rewrite (proj1 (proj2_sig g)); rewrite -Parameter_unitGenerator;
    rewrite -unitParametrizator_polyParametrizator; reflexivity ] ) .
Defined.

Lemma reparamMorSym_Heqparam_View1_comp_View1 :
  forall (G H : obGenerator) (g : 'Generator( G ~> H )) (G' : obGenerator) (g' : 'Generator( G' ~> G )),
    Parameter1 (g' o>Generator g) = Parameter1 (sval (unitGenerator_reparamMorSymGenerator G')).1 o>Parametrizator (is_Parameter0_transp_codom (Is_Parameter0 G) (Parameter1 g') o>Parametrizator Parameter1 g).
Proof.
  intros G H g G' g'.
  simpl. rewrite Parameter_morphism. rewrite -Parameter_unitGenerator.
  rewrite -polyParametrizator_unitParametrizator.
  rewrite -[X in _ = X o>Parametrizator _]unitParametrizator_polyParametrizator. reflexivity. 
Qed.

Lemma is_Parameter0_transformation_morphism' : 
  forall (G : obGenerator)  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    fst (sval is_Parameter0_P) = fst (sval (is_Parameter0_transformation (unitGenerator_reparamMorSymGenerator _) is_Parameter0_P)) .
  intros. simpl. destruct is_Parameter0_P as [x ?]. simpl. destruct x. simpl.
  rewrite -Parameter_unitGenerator; rewrite -polyParametrizator_unitParametrizator. reflexivity.
Qed.  

Lemma Congr_View1_comp_View1'
     : forall (G H : obGenerator) (g : 'Generator( G ~> H )) (G' : obGenerator) (g' : 'Generator( G' ~> G )),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_View1' g) (Yoneda1_Form_View1' g')) (Yoneda1_Form_View1' (g' o>Generator g))
               (reparamMorSym_Trans (reparamMorSym_View1_ReParam_comp_View1_ReParam (Parameter1 g) (Is_Parameter0 G) (Parameter1 g') (Is_Parameter0 G'))
   (reparamMorSym_View1_ReParam_cong (reparamMorSym_Heqparam_View1_comp_View1 g g') (is_Parameter0_transformation_morphism' (Is_Parameter0 G')))) .
Proof.
  intros. constructor. intros. simpl. rewrite polyGenerator_morphism. do 2 congr (_ _). assumption.
Qed. 

Lemma View1_cong_Heqparam : forall (G H : obGenerator) (g g' : 'Generator( G ~> H )) (Heqparam : g' = g),
    Parameter1 g' = Parameter1 (sval (unitGenerator_reparamMorSymGenerator G)).1 o>Parametrizator Parameter1 g .
Proof.
  intros. rewrite -Parameter_unitGenerator. rewrite -polyParametrizator_unitParametrizator. rewrite Heqparam. reflexivity.
Qed.
Lemma Congr_View1_cong :
  forall (G H : obGenerator) (g g' : 'Generator( G ~> H )),
  forall (Heqparam : g' = g),
    Congr_data (Yoneda1_Form_View1' g) (Yoneda1_Form_View1' g') (reparamMorSym_View1_ReParam_cong (View1_cong_Heqparam Heqparam) (is_Parameter0_transformation_morphism' (Is_Parameter0 G))) .
Proof.
  intros; constructor; intros; simpl.  subst. congr ( _ _ ). assumption.
Qed.

Reserved Notation "''CoMod_$' (  Param_EF  ~>  Param_EF0  @_  Yoneda1_Param_reparam_rr  )" (at level 0).
Reserved Notation "''CoMod$' (  Form_ff  ~>  Form_ff'  @_  Congr_congr_ff  )" (at level 0).

Inductive congrPseudoCode_ReParam : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) ,
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (Param_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                            Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0, Type :=
| Refl_reparam :
forall (Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E )
(Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
  'CoMod_$( Param_EF ~> Param_EF
                     @_ reparamMorSym_Refl Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff )

| Trans_reparam : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0),
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (Param_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall Yoneda1_Param_reparam_rr0 : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                          Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0,
 forall (reparam_rr0 : 'CoMod_$(  Param_EF  ~>  Param_EF0  @_  Yoneda1_Param_reparam_rr0 ) ) ,
 forall Yoneda00_Param_EF1 (Yoneda01_Param_EF1 : Yoneda01_Param_data Yoneda00_Param_EF1),
 forall Yoneda1_Param_proj_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff1 : Yoneda1_Param_data Yoneda01_Param_EF1 Yoneda01_Param_F,
 forall (Param_EF1 : pseudoCode_ReParam Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1),
 forall Yoneda1_Param_reparam_rr1 : reparamMorSym Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0
                                          Yoneda1_Param_proj_ff1 Yoneda1_Param_subst_ff1,
 forall (reparam_rr1 : 'CoMod_$(  Param_EF0  ~>  Param_EF1  @_  Yoneda1_Param_reparam_rr1 ) ), 

   'CoMod_$( Param_EF ~> Param_EF1
             @_ reparamMorSym_Trans Yoneda1_Param_reparam_rr0 Yoneda1_Param_reparam_rr1 )

| Assoc_reparam :  forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D),
 forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE) ,
 forall Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D,
 forall Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E,
 forall (Param_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee),
 forall Yoneda00_Param_C (Yoneda01_Param_C : Yoneda01_Param_data Yoneda00_Param_C),
 forall Yoneda00_Param_CD (Yoneda01_Param_CD : Yoneda01_Param_data Yoneda00_Param_CD) ,
 forall Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_C,
 forall Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_D,
 forall (Param_CD : pseudoCode_ReParam Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd),

   'CoMod_$( PolyCoMod_pseudoCode_ReParam (PolyCoMod_pseudoCode_ReParam Param_EF Param_DE) Param_CD ~>
             PolyCoMod_pseudoCode_ReParam Param_EF (PolyCoMod_pseudoCode_ReParam Param_DE Param_CD)
             @_  (reparamMorSym_Assoc_reparam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                        Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee
                                        Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd) )

| Sym_reparam : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) ,
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (Param_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                  Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0,           
   'CoMod_$( Param_EF ~> Param_EF0 @_ Yoneda1_Param_reparam_rr ) ->
   'CoMod_$( Param_EF0 ~> Param_EF @_ (reparamMorSym_Sym Yoneda1_Param_reparam_rr) )

| morCoMod_comp_UnitCoMod_reparam :
    forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F) ReParam_EF ~> ReParam_EF @_ reparamMorSym_morCoMod_comp_UnitCoMod Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff )

| UnitCoMod_comp_morCoMod_reparam :
    forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      'CoMod_$ ( PolyCoMod_pseudoCode_ReParam ReParam_EF (UnitCoMod_pseudoCode_ReParam Yoneda01_Param_E) ~> ReParam_EF @_ reparamMorSym_UnitCoMod_comp_morCoMod Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff )

| View1_ReParam_comp_View1_ReParam_reparam :
  forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
    (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
  forall (G' : obGenerator) (p' : 'Parametrizator ( Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
    (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
  (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
    'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (View1_pseudoCode_ReParam pp) (View1_pseudoCode_ReParam p'p') ~>
                                            View1_pseudoCode_ReParam (viewingDefault_Constructors_action pp p'p') @_
                                            reparamMorSym_View1_ReParam_comp_View1_ReParam p is_Parameter0_P p' is_Parameter0_P' )

| PolyCoMod_pseudoCode_ReParam_cong : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) ,
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (Param_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (*TODO: this _proj_ ( and _subst_ ) should be included in the Yoneda1_Param_reparam_rr of 'CoMod_& *)
   Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff  Yoneda1_Param_subst_ff
                                          Yoneda1_Param_proj_ff0  Yoneda1_Param_subst_ff0 ,
 forall (reparam_rr : 'CoMod_$(  Param_EF  ~>  Param_EF0  @_  Yoneda1_Param_reparam_rr  ) ),
 forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D),
 forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE) ,
 forall Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D,
 forall Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E,
 forall (Param_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee),
 forall Yoneda00_Param_DE0 (Yoneda01_Param_DE0 : Yoneda01_Param_data Yoneda00_Param_DE0) ,
 forall Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_D,
 forall Yoneda1_Param_subst_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_E,
 forall (Param_DE0 : pseudoCode_ReParam Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0),
 forall Yoneda1_Param_reparam_qq : reparamMorSym Yoneda1_Param_proj_ee  Yoneda1_Param_subst_ee
                                          Yoneda1_Param_proj_ee0  Yoneda1_Param_subst_ee0,
 forall (reparam_qq : 'CoMod_$(  Param_DE  ~>  Param_DE0  @_  Yoneda1_Param_reparam_qq ) ), 

   'CoMod_$( PolyCoMod_pseudoCode_ReParam Param_EF Param_DE ~>
             PolyCoMod_pseudoCode_ReParam Param_EF0 Param_DE0
             @_ reparamMorSym_PolyCoMod_pseudoCode_ReParam_cong Yoneda1_Param_reparam_rr Yoneda1_Param_reparam_qq )

| View1_ReParam_cong_reparam : 
 forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
 forall (G' : obGenerator) (p' : 'Parametrizator(  Parameter0 G' ~> Q )) (is_Parameter0_P' : is_Parameter0 G' P)
   (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
   (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
    forall (g : reparamMorSymGenerator G' G),
      forall (Heqparam : p' = (Parameter1 (fst (sval g))) o>Parametrizator p),
      forall (Heqis : fst (sval is_Parameter0_P') =  fst (sval (is_Parameter0_transformation  g is_Parameter0_P)) ),
        (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) if pp and p'p' *)
        'CoMod_$ ( View1_pseudoCode_ReParam pp ~> View1_pseudoCode_ReParam p'p' @_ reparamMorSym_View1_ReParam_cong Heqparam Heqis )
               
| ViewedFunctor1_ReParam_default_cong_reparam :
  forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Yoneda00_Param_EF0 : obGenerator -> Type)
         (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F) (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
         (Yoneda1_Param_reparam_conv_param_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
         (reparam_conv_param_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_param_ff )),
    'CoMod_$ ( ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF ~> ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF0 @_ Yoneda1_Param_reparam_conv_param_ff )

| PolyTransf_pseudoCode_ReParam_default_cong_reparam :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
  forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism :  Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)
  (Yoneda1_Param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_dd_morphism :  Morphism_prop Yoneda1_Param_dd_)
  (ReParam_dd_ : pseudoCode_ReParam_Family Yoneda1_Param_dd_morphism)
  (Yoneda1_Param_reparam_eedd_ :  forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
                                    (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
                                reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal)
                                  (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_dd_ G paramlocal))
  (reparam_eedd_ :  forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
                  'CoMod_$ ( AtMember_ReParam ReParam_ee_ cons_paramlocal ~> AtMember_ReParam ReParam_dd_ cons_paramlocal @_ Yoneda1_Param_reparam_eedd_ G paramlocal P is_Parameter0_P )),
 
  'CoMod_$ ( PolyTransf_pseudoCode_ReParam_default'  Param_SubstF ReParam_ee_ ~>
  PolyTransf_pseudoCode_ReParam_default' Param_SubstF ReParam_dd_ @_
  reparamMorSym_PolyTransf_pseudoCode_ReParam_default_cong Yoneda1_Param_ee_morphism Yoneda1_Param_dd_morphism Yoneda1_Param_reparam_eedd_ )
         
| PolyElement_ReParam_default_comp_PolyTransf_ReParam_default_reparam :
forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
forall (Yoneda00_Param_K : obGenerator -> Type) (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism :  Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),
 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
  'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (PolyTransf_pseudoCode_ReParam_default' Param_SubstF ReParam_ee_)
                                          (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal) ~>
                                          PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' Yoneda01_Param_K) (AtMember_ReParam ReParam_ee_ cons_paramlocal) @_
                                          reparamMorSym_PolyElement_ReParam_default_comp_PolyTransf_ReParam_default Yoneda1_Param_ee_morphism paramlocal is_Parameter0_P )

| Formatting_cong_reparam
: forall (Yoneda00_Form_E : obGenerator -> Type)
(  Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(  Yoneda00_Param_E : obGenerator -> Type)
(  Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(  Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(  Yoneda00_Form_F : obGenerator -> Type)
(  Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(  Yoneda00_Param_F : obGenerator -> Type)
(  Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(  Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(  Yoneda00_Param_EF : obGenerator -> Type)
(  Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(  Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(  Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(  ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
(  Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
(  Form_ff : pseudoCode Yoneda1_Form_ff)
  (Yoneda00_Param_EF0 : obGenerator -> Type)
  (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
  (Yoneda1_Param_proj0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
  (Yoneda1_Param_subst0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
  (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj0 Yoneda1_Param_subst0)
  (Yoneda1_Form_ff0 : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj0 Yoneda1_Param_subst0)
  (Form_ff0 : pseudoCode Yoneda1_Form_ff0)
  (Yoneda1_Param_reparam_conv_ff : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj0 Yoneda1_Param_subst0)
  (reparam_conv_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_ff ))
  (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff0 Yoneda1_Param_reparam_conv_ff)
  (congr_ff : 'CoMod$ ( Form_ff ~> Form_ff0 @_ Congr_congr_ff )),
  'CoMod_$ ( Formatting_pseudoCode_ReParam' ReParam_EF Form_ff ~> Formatting_pseudoCode_ReParam' ReParam_EF0 Form_ff0 @_
                                           reparamMorSym_Formatting_cong Congr_congr_ff )

| View1_ReParam_comp_PolyElement_ReParam_default_reparam :
forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
 forall (G' : obGenerator) (p' : 'Parametrizator ( Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
   (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
   (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
    'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal)
                 (View1_pseudoCode_ReParam p'p') ~>
               AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF)  (constructors_action cons_paramlocal p'p' (eq_refl _) ) @_
               reparamSym_View1_ReParam_comp_PolyElement_ReParam_default  Yoneda1_Param_subst paramlocal is_Parameter0_P p' is_Parameter0_P' )

| UnitViewedFunctor_ReParam_default_morphismPost_reparam' :
  forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) ,
    'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF) (UnitViewedFunctor_pseudoCode_ReParam_default' _) ~>
                               (PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) ReParam_EF) @_
                                            reparamMorSym_Trans (reparamMorSym_UnitCoMod_comp_morCoMod _ _) (reparamMorSym_Sym (reparamMorSym_morCoMod_comp_UnitCoMod _ _)) (* (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
                                            (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_subst_ee)  *) ) 
           
| ViewedFunctor1_ReParam_default_morphism_reparam :
    forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Yoneda00_Param_D : obGenerator -> Type)
           (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D) (Yoneda00_Param_DE : obGenerator -> Type) (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
           (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
           (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee),
      'CoMod_$ ( PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF) (ViewedFunctor1_pseudoCode_ReParam_default ReParam_DE) ~>
                                              ViewedFunctor1_pseudoCode_ReParam_default (PolyCoMod_pseudoCode_ReParam ReParam_EF ReParam_DE) @_
                                              reparamMorSym_Refl (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ff Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
                                              (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_subst_ee) )
             
| PolyElement_ReParam_default_cong_reparam
     :  forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
 forall (paramlocal' : Yoneda00_Param_SumSubstF G) (is_Parameter0_P' : is_Parameter0 G P)
   (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
   (cons_paramlocal' : constructors Param_SubstF paramlocal' cons_is_Parameter0_P' ),
 forall (Heqparamlocal : paramlocal' = paramlocal)
   (Heqis : fst (sval is_Parameter0_P') = fst (sval is_Parameter0_P)),
   (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of cons_paramlocal and cons_paramlocal' *)
       'CoMod_$ ( AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal ~>
                                   AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal' @_ (reparamMorSym_PolyElement_ReParam_default_cong  Yoneda1_Param_subst Heqparamlocal Heqis ) )

where "''CoMod_$' (  Param_EF  ~>  Param_EF0  @_  Yoneda1_Param_reparam_rr  )" :=
        (@congrPseudoCode_ReParam _ _ _ _ _ _ _ _ Param_EF _ _ _ _ Param_EF0 Yoneda1_Param_reparam_rr) : poly_scope 
with congrPseudoCode : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
                             (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
    forall (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Form_ff' : pseudoCode Yoneda1_Form_ff'),
    forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr), Type :=

| Refl_congrPseudoCode : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
                             (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
      'CoMod$( Form_ff ~> Form_ff @_ Congr_Refl Yoneda1_Form_ff )
       
| Trans_congrPseudoCode : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
                             (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
    forall (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Form_ff' : pseudoCode Yoneda1_Form_ff'),
    forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr)
      (congr_ff : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff )),
    forall (Yoneda00_Param_EF'' : obGenerator -> Type) (Yoneda01_Param_EF'' : Yoneda01_Param_data Yoneda00_Param_EF'')
      (Yoneda1_Param_proj_ff'' : Yoneda1_Param_data Yoneda01_Param_EF'' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff'' : Yoneda1_Param_data Yoneda01_Param_EF'' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff'' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff'' Yoneda1_Param_subst_ff'')
      (Form_ff'' : pseudoCode Yoneda1_Form_ff''),
    forall (Yoneda1_Param_reparam_rr' : reparamMorSym Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'
                                                Yoneda1_Param_proj_ff'' Yoneda1_Param_subst_ff'')
      (Congr_congr_ff' : Congr_data Yoneda1_Form_ff' Yoneda1_Form_ff'' Yoneda1_Param_reparam_rr')
      (congr_ff' : 'CoMod$( Form_ff' ~> Form_ff'' @_ Congr_congr_ff' )),
      'CoMod$( Form_ff ~> Form_ff'' @_ Congr_Trans Congr_congr_ff Congr_congr_ff'  )

| Assoc_congrPseudoCode :  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
                             (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff)
      (Param_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
      
    forall (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D)
      Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
      (Yoneda1_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D),
 forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE) ,
 forall Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D,
 forall Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E,
 forall (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_D Yoneda1_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
   (Form_ee : pseudoCode Yoneda1_Form_ee)
 (Param_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee),

 forall (Yoneda00_Form_C : obGenerator -> Type) (Yoneda01_Form_C : Yoneda01_data Yoneda00_Form_C)
   Yoneda00_Param_C (Yoneda01_Param_C : Yoneda01_Param_data Yoneda00_Param_C)
 (Yoneda1_FormParam_C : Yoneda1_FormParam_data Yoneda01_Form_C Yoneda01_Param_C),
 forall Yoneda00_Param_CD (Yoneda01_Param_CD : Yoneda01_Param_data Yoneda00_Param_CD) ,
 forall Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_C,
 forall Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_D,
 forall (Yoneda1_Form_dd : Yoneda1_Form_data Yoneda1_FormParam_C Yoneda1_FormParam_D Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
   (Form_dd : pseudoCode Yoneda1_Form_dd)
   (Param_CD : pseudoCode_ReParam Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd),
   'CoMod$( PolyCoMod_pseudoCode (PolyCoMod_pseudoCode_ReParam Param_EF Param_DE) (PolyCoMod_pseudoCode Param_EF Form_ff Param_DE Form_ee)
                                  Param_CD Form_dd ~>
                                  PolyCoMod_pseudoCode Param_EF Form_ff
                                  (PolyCoMod_pseudoCode_ReParam Param_DE Param_CD) (PolyCoMod_pseudoCode Param_DE Form_ee Param_CD Form_dd)
             @_  Congr_Assoc_congrPseudoCode Yoneda1_Form_ff Yoneda1_Form_ee Yoneda1_Form_dd )

| Sym_congrPseudoCode :
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
    (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Form_ff : pseudoCode Yoneda1_Form_ff)
           (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF') (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
           (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
           (Form_ff' : pseudoCode Yoneda1_Form_ff')
           (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
           (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr)
           (congr_ff : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff )),
          'CoMod$( Form_ff' ~> Form_ff @_ Congr_Sym Congr_congr_ff )

| PolyCoMod_cong_congrPseudoCode :  forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Form_F' : obGenerator -> Type) (Yoneda01_Form_F' : Yoneda01_data Yoneda00_Form_F')
         (Yoneda00_Param_F' : obGenerator -> Type) (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F') (Yoneda1_FormParam_F' : Yoneda1_FormParam_data Yoneda01_Form_F' Yoneda01_Param_F')
         (Yoneda00_Param_F'F : obGenerator -> Type) (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F) (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
         (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F) (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
         (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff') (Form_ff' : pseudoCode Yoneda1_Form_ff')
         (Yoneda00_Form_F'' : obGenerator -> Type) (Yoneda01_Form_F'' : Yoneda01_data Yoneda00_Form_F'') (Yoneda00_Param_F'' : obGenerator -> Type) (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
         (Yoneda1_FormParam_F'' : Yoneda1_FormParam_data Yoneda01_Form_F'' Yoneda01_Param_F'') (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')
         (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'') (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
         (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
         (Yoneda1_Form_ff_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_) (Form_ff_ : pseudoCode Yoneda1_Form_ff_)
         (Yoneda00_Param_E'E : obGenerator -> Type) (Yoneda01_Param_E'E : Yoneda01_Param_data Yoneda00_Param_E'E) (Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F')
         (Yoneda1_Param_subst_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F) (ReParam_E'E : pseudoCode_ReParam Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee')
         (Yoneda1_Form_ee' : Yoneda1_Form_data Yoneda1_FormParam_F' Yoneda1_FormParam_F Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee') (Form_ee' : pseudoCode Yoneda1_Form_ee')
         (Yoneda1_Param_reparam_F'F : reparamMorSym Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff' Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee')
         (reparam_F'F : 'CoMod_$(  ReParam_F'F  ~>  ReParam_E'E  @_ Yoneda1_Param_reparam_F'F ))
         (Congr_congr_ff' : Congr_data Yoneda1_Form_ff' Yoneda1_Form_ee' Yoneda1_Param_reparam_F'F),
    'CoMod$ ( Form_ff' ~> Form_ee' @_ Congr_congr_ff' ) ->
    forall (Yoneda00_Param_E''E' : obGenerator -> Type) (Yoneda01_Param_E''E' : Yoneda01_Param_data Yoneda00_Param_E''E') (Yoneda1_Param_proj_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F'')
           (Yoneda1_Param_subst_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F') (ReParam_E''E' : pseudoCode_ReParam Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
           (Yoneda1_Form_ee_ : Yoneda1_Form_data Yoneda1_FormParam_F'' Yoneda1_FormParam_F' Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_) (Form_ee_ : pseudoCode Yoneda1_Form_ee_)
           (Yoneda1_Param_reparam_F''F' : reparamMorSym Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_ Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
           (reparam_F''F' : 'CoMod_$(  ReParam_F''F'  ~>  ReParam_E''E'  @_ Yoneda1_Param_reparam_F''F' ))
           (Congr_congr_ff_ : Congr_data Yoneda1_Form_ff_ Yoneda1_Form_ee_ Yoneda1_Param_reparam_F''F'),
      'CoMod$ ( Form_ff_ ~> Form_ee_ @_ Congr_congr_ff_ ) ->
      'CoMod$ ( PolyCoMod_pseudoCode ReParam_F'F Form_ff' ReParam_F''F' Form_ff_ ~> PolyCoMod_pseudoCode ReParam_E'E Form_ee' ReParam_E''E' Form_ee_ @_
                                    congr_PolyCoMod_cong Congr_congr_ff' Congr_congr_ff_ )

| View1_cong_congrPseudoCode :
forall (G H : obGenerator) (g : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
  (gg : viewingDefault_Constructors_Form g),
forall(g' : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
  (g'g' : viewingDefault_Constructors_Form g'),
forall (Heqparam : g' = g),
  (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of gg and g'g' *)
    'CoMod$ ( View1_pseudoCode gg ~> View1_pseudoCode g'g' @_ (Congr_View1_cong Heqparam ) )

| ViewedFunctor1_default_cong_congrPseudoCode :
    forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda10_Form_ff)
           (Yoneda00_Param_EF0 : obGenerator -> Type) (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F) (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
           (Yoneda10_Form_ff0 : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0) (Form_ff0 : pseudoCode Yoneda10_Form_ff0)
           (Yoneda1_Param_reparam_conv_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
           (reparam_conv_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_ff )),
      forall (Congr_congr_conv_ff : Congr_data Yoneda10_Form_ff Yoneda10_Form_ff0 Yoneda1_Param_reparam_conv_ff)
        (congr_conv_ff :'CoMod$ ( Form_ff ~> Form_ff0 @_ Congr_congr_conv_ff )),
        'CoMod$ ( ViewedFunctor1_default_pseudoCode ReParam_EF Form_ff ~> ViewedFunctor1_default_pseudoCode ReParam_EF0 Form_ff0 @_ Congr_congr_conv_ff )

| PolyElement_default_cong_congrPseudoCode :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
forall (param' : Yoneda00_Param_SubstF G) (cons_paramlocal' : constructors Param_SubstF (sval Yoneda1_Param_subst G param') (Unit_is_Parameter0Default_Constructors G))
  (form' : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param')
  (cons_form' : constructors_Form F  form'),
  forall (Heqparam : param' = param)
    (Heqform : sval form' = sval form),
    (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of cons_paramlocal and cons_paramlocal' , moreover of cons_form and cons_form' *)
    'CoMod$ ( AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal cons_form ~>
                            AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal' cons_form' @_ Congr_PolyElement_default_cong  Yoneda1_Param_subst Heqparam Heqform  )

| PolyTransf_default_cong_congrPseudoCode''' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
forall (Yoneda00_Param_K : obGenerator -> Type)
    (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
    (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
    (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
    (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)
    (Yoneda00_Form_K : obGenerator -> Type)
    (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
    (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
    (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                        (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
    (Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
    (Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)
    (Yoneda1_Param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
        Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
    (Yoneda1_Param_dd_morphism : Morphism_prop Yoneda1_Param_dd_)
    (ReParam_dd_ : pseudoCode_ReParam_Family Yoneda1_Param_dd_morphism)
    (Yoneda1_Form_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_dd_ G (sval Yoneda1_Param_subst G param)))
    (Yoneda1_Form_dd_morphism : Morphism_Form_prop Yoneda1_Form_dd__)
    (Form_dd__ : pseudoCode_Family Yoneda1_Form_dd_morphism)
    (Yoneda1_Param_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
                                reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal)
                                  (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_dd_ G paramlocal))
    (reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
                       (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
                       (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
                  'CoMod_$ ( AtMember_ReParam ReParam_ee_ cons_paramlocal ~> AtMember_ReParam ReParam_dd_ cons_paramlocal @_ Yoneda1_Param_reparam_eedd_ G paramlocal P is_Parameter0_P ))
    (Congr_congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                       Congr_data (Yoneda1_Form_ee__ G param form) (Yoneda1_Form_dd__ G param form) (Yoneda1_Param_reparam_eedd_ _ (sval Yoneda1_Param_subst G param) _ (Is_Parameter0 G)))
    (congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
                      (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
                      (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
                      (cons_form : constructors_Form F  form),
                 'CoMod$ ( AtMember_Form Form_ee__ cons_paramlocal cons_form ~> AtMember_Form Form_dd__ cons_paramlocal cons_form @_ Congr_congr_eedd__ G param form )),
 'CoMod$ ( PolyTransf_default_pseudoCode' F ReParam_ee_ Form_ee__  ~>
                                          PolyTransf_default_pseudoCode' F ReParam_dd_ Form_dd__
  @_ Congr_PolyTransf_default_cong''' Yoneda1_Param_ee_morphism Yoneda1_Form_ee_morphism (Refl_Morphism_reparam_prop  Yoneda1_Param_ee_)
  Yoneda1_Param_dd_morphism Yoneda1_Form_dd_morphism (Refl_Morphism_reparam_prop  Yoneda1_Param_dd_)
  Yoneda1_Param_reparam_eedd_ Congr_congr_eedd__ )

| Remember_cong_congrPseudoCode :
  forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
         (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
         (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
         (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
         (Yoneda00_Form_LF : obGenerator -> Type) (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF) (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
         (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst) (Form_ll' : pseudoCode Yoneda1_Form_ll')
         (Yoneda1_Form_ll'0 : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst) (Form_ll'0 : pseudoCode Yoneda1_Form_ll'0)
         (Congr_congr_ll'll'0 : Congr_data Yoneda1_Form_ll' Yoneda1_Form_ll'0 (reparamMorSym_Refl Yoneda1_Param_proj Yoneda1_Param_subst)),
  forall (congr_ll'll'0 : 'CoMod$ ( Form_ll' ~> Form_ll'0 @_ Congr_congr_ll'll'0 ) ),
    'CoMod$ ( Remember_pseudoCode ReParam_SubstF Form_ll' ~> Remember_pseudoCode ReParam_SubstF Form_ll'0 @_ Congr_Remember_cong' Congr_congr_ll'll'0 )        
| morCoMod_comp_UnitCoMod_congrPseudoCode
: forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda1_Form_ff),
      'CoMod$ ( PolyCoMod_pseudoCode (UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F) (UnitCoMod_pseudoCode Yoneda1_FormParam_F) ReParam_EF Form_ff ~> Form_ff @_
                                     Congr_morCoMod_comp_UnitCoMod Yoneda1_Form_ff )

| UnitCoMod_comp_morCoMod_congrPseudoCode
: forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda1_Form_ff),
      'CoMod$ ( PolyCoMod_pseudoCode ReParam_EF Form_ff (UnitCoMod_pseudoCode_ReParam Yoneda01_Param_E) (UnitCoMod_pseudoCode Yoneda1_FormParam_E)  ~> Form_ff @_
                                     Congr_UnitCoMod_comp_morCoMod Yoneda1_Form_ff )

| View1_comp_View1_congrPseudoCode' :
  forall (G H : obGenerator) (g : 'Generator( G ~> H )) (gg : viewingDefault_Constructors_Form g),
  forall (G' : obGenerator) (g' : 'Generator( G' ~> G )) (g'g' : viewingDefault_Constructors_Form g'),
    'CoMod$ ( PolyCoMod_pseudoCode (View1_pseudoCode_ReParam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg)) (View1_pseudoCode gg)
                  (View1_pseudoCode_ReParam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form g'g')) (View1_pseudoCode g'g') ~>
                  View1_pseudoCode (viewingDefault_Constructors_Form_action gg g'g') @_ Congr_View1_comp_View1' g g' )

| View1_comp_PolyElement_default_congrPseudoCode :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
forall (G' : obGenerator) (g : 'Generator( G' ~> G )) (gg : viewingDefault_Constructors_Form g),
  'CoMod$ ( PolyCoMod_pseudoCode (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal)
                                 (AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal cons_form)
                                 (View1_pseudoCode_ReParam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg)) (View1_pseudoCode gg) ~>
                                 AtMember_Form (PolyElement_default_pseudoCode F)
                                 ( ( constructors_action cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (constructors_Form_action_transp_Heq Yoneda1_Param_subst param g) ))
                                 ( constructors_Form_action cons_form gg)
                                 @_ Congr_View1_comp_PolyElement_default Yoneda1_Param_subst form g )

| UnitViewedFunctor_default_morphismPost_congrPseudoCode' :
    forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda10_Form_ff),
      'CoMod$ (
              PolyCoMod_pseudoCode (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF) (ViewedFunctor1_default_pseudoCode ReParam_EF Form_ff)
                                   (UnitViewedFunctor_pseudoCode_ReParam_default' _) (UnitViewedFunctor_default_pseudoCode' _) ~>
           (PolyCoMod_pseudoCode (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) (UnitViewedFunctor_default_pseudoCode' _ ) ReParam_EF Form_ff)  @_
           Congr_Trans (Congr_UnitCoMod_comp_morCoMod _) (Congr_Sym (Congr_morCoMod_comp_UnitCoMod _)) )
            
| ViewedFunctor1_default_morphism_congrPseudoCode :
    forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda10_Form_ff)
           (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D) (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
           (Yoneda10_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D) (Yoneda00_Param_DE : obGenerator -> Type) (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
           (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
           (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
           (Yoneda10_Form_ee : Yoneda1_Form_data Yoneda10_FormParam_D Yoneda10_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) (Form_ee : pseudoCode Yoneda10_Form_ee),
      'CoMod$ (
              PolyCoMod_pseudoCode (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF) (ViewedFunctor1_default_pseudoCode ReParam_EF Form_ff) (ViewedFunctor1_pseudoCode_ReParam_default ReParam_DE)
                                   (ViewedFunctor1_default_pseudoCode ReParam_DE Form_ee) ~>
                                   ViewedFunctor1_default_pseudoCode (PolyCoMod_pseudoCode_ReParam ReParam_EF ReParam_DE) (PolyCoMod_pseudoCode ReParam_EF Form_ff ReParam_DE Form_ee) @_
                                   Congr_Refl (Yoneda1_Form_PolyCoMod Yoneda10_Form_ff Yoneda10_Form_ee) )

| Remember_comp_Forget_congrPseudoCode :
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
           (Yoneda00_Form_LF : obGenerator -> Type) (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF) (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
           (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst) (Form_ll' : pseudoCode Yoneda1_Form_ll'),
      'CoMod$ ( PolyCoMod_pseudoCode ReParam_SubstF (Forget_pseudoCode Yoneda1_FormParam_F ReParam_SubstF) (UnitCoMod_pseudoCode_ReParam Yoneda01_Param_PiSubstF) (Remember_pseudoCode ReParam_SubstF Form_ll') ~>
                                     Form_ll' @_ Congr_Remember_comp_Forget Yoneda1_Form_ll' )

| PolyElement_default_comp_PolyTransf_default_congrPseudoCode' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
  forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
  (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G), Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)
  (Yoneda00_Form_K : obGenerator -> Type)
  (Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
  (Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)
  (Yoneda1_Form_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
      Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                        (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                        (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
  (Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
  (Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism),
forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
  'CoMod$ ( PolyCoMod_pseudoCode (PolyTransf_pseudoCode_ReParam_default'  Param_SubstF ReParam_ee_)
      (PolyTransf_default_pseudoCode' F ReParam_ee_ Form_ee__)
      (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal)
      (AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal cons_form) ~>
      PolyCoMod_pseudoCode (UnitViewedFunctor_pseudoCode_ReParam_default' Yoneda01_Param_K) (UnitViewedFunctor_default_pseudoCode' Yoneda1_FormParam_K)
      (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) @_
  Congr_PolyElement_default_comp_PolyTransf_default' Yoneda1_Param_ee_morphism Yoneda1_Form_ee_morphism (Refl_Morphism_reparam_prop Yoneda1_Param_ee_) form )

where "''CoMod$' (  Form_ff  ~>  Form_ff'  @_  Congr_congr_ff  )" :=
   (@congrPseudoCode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Form_ff _ _ _ _ _ Form_ff' _ Congr_congr_ff) : poly_scope .

Notation "reparam_rr_ o>_$ reparam_rr'" := (@Trans_reparam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ reparam_rr_ _ _ _ _ _ _ reparam_rr')
               (at level 40 , reparam_rr' at next level , left associativity) : poly_scope.
Notation "congr_ff_ o>$ congr_ff'" := (@Trans_congrPseudoCode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  congr_ff_ _ _ _ _ _ _ _ _ congr_ff')
               (at level 40 , congr_ff' at next level , left associativity) : poly_scope.

Reserved Notation "''CoMod' (  E  ~>  F  @_  ReParam_EF  @^  Form_ff  )" (at level 0).
Reserved Notation "''CoMod__' (  Param_E  ~>  Param_F  @_  ReParam_EF  )" (at level 0).

Inductive morCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
   (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
   (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   (Form_ff : pseudoCode Yoneda1_Form_ff ), Type :=

(** -----cuts to be eliminated----- **)
| PolyCoMod : forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
                (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
    forall Yoneda00_Form_F' Yoneda01_Form_F' Yoneda00_Param_F' Yoneda01_Param_F' Yoneda1_FormParam_F'
      (F' : @obCoMod Yoneda00_Form_F' Yoneda01_Form_F' Yoneda00_Param_F' Yoneda01_Param_F' Yoneda1_FormParam_F'),
    forall Yoneda00_Param_F'F (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F)
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
      Yoneda1_Param_subst_ff' (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff') Yoneda1_Form_ff'
      (Form_ff' : pseudoCode Yoneda1_Form_ff')
      (ff' : 'CoMod( F' ~> F @_ ReParam_F'F @^ Form_ff' )),

    forall Yoneda00_Form_F'' Yoneda01_Form_F'' Yoneda00_Param_F'' Yoneda01_Param_F'' Yoneda1_FormParam_F''
      (F'' : @obCoMod Yoneda00_Form_F'' Yoneda01_Form_F'' Yoneda00_Param_F'' Yoneda01_Param_F'' Yoneda1_FormParam_F''),
    forall Yoneda00_Param_F''F' (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')      
       (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'')
       Yoneda1_Param_subst_ff_ (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
       Yoneda1_Form_ff_       (Form_ff_ : pseudoCode Yoneda1_Form_ff_)
      (ff_ : 'CoMod( F'' ~> F' @_ ReParam_F''F' @^ Form_ff_ )),

      'CoMod( F'' ~> F @_ (PolyCoMod_pseudoCode_ReParam ReParam_F'F ReParam_F''F')
                  @^ (PolyCoMod_pseudoCode ReParam_F'F Form_ff' ReParam_F''F' Form_ff_) )

(** -----solution morphisms----- **)
| UnitCoMod : forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
                (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
    'CoMod( F ~> F @_ UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F @^ UnitCoMod_pseudoCode Yoneda1_FormParam_F )

(**TODO: should viewingDefault_Constructors_Form  also carry a viewingDefault_Constructors code for (Parameter1 g) (Is_Parameter0 G) ? *)
| View1 : forall (G H : obGenerator) (g : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
            (gg : viewingDefault_Constructors_Form g),
      'CoMod( View G ~> View H @_ (View1_pseudoCode_ReParam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg))
                   @^ View1_pseudoCode gg )

| PolyElement_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
  (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
  
  'CoMod( View G ~> ViewingFunctorSumSubst_default F
               @_ (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal)
               @^ (AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal cons_form))

| ViewedFunctor1_default :
forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E
  (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F
  (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall Yoneda10_Form_ff (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

forall Yoneda00_Param_EF' (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF'),
forall Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F,
forall (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' )),

forall Yoneda1_Param_reparam_EF
  (reparam_EF : 'CoMod_$( ReParam_EF  ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF) ),

  'CoMod( ViewedFunctor_default E Param_E ~> ViewedFunctor_default F Param_F
                                @_ (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF)
                                @^ ViewedFunctor1_default_pseudoCode ReParam_EF Form_ff )

| UnitViewedFunctor_default
  : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
      (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
      (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E)
      (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F)
      (Param_F : obCoMod_Param Yoneda01_Param_F)
      (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
      (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )),

    'CoMod ( E ~> ViewedFunctor_default F Param_F
               @_ (PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) ReParam_EF)
               @^ (PolyCoMod_pseudoCode  (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) (UnitViewedFunctor_default_pseudoCode' _ ) ReParam_EF Form_ff) )

| PolyTransf_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),
  
  'CoMod( ViewingFunctorSumSubst_default F ~> ViewedFunctor_default E Param_E
      @_ (PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__) (PolyTransf_pseudoCode_ReParam_default' Param_SubstF  ReParam_ee_))
      @^ (PolyCoMod_pseudoCode (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__)
                               (ViewedFunctor1_default_pseudoCode ReParam_ee'__ Form_ee'__)
                               (PolyTransf_pseudoCode_ReParam_default' Param_SubstF  ReParam_ee_)
                               (PolyTransf_default_pseudoCode' F ReParam_ee_ Form_ee__)) )

| Forget :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
   (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
   (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E)
   (Yoneda00_Param_FE : obGenerator -> Type)
   (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)   
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
   (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_E)
   (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) Yoneda1_Form_ee
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( F ~> E @_  ReParam_FE @^ Form_ee )),
   
   'CoMod( PiSubst F Param_F Param_PiSubstF ReParam_SubstF ~> E
                   @_ (PolyCoMod_pseudoCode_ReParam ReParam_FE ReParam_SubstF)
                   @^ (PolyCoMod_pseudoCode ReParam_FE Form_ee ReParam_SubstF (Forget_pseudoCode _ ReParam_SubstF ) ) )

| Remember :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
   
 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' ) ),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_L : obGenerator -> Type)
   (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
   (Yoneda00_Param_L : obGenerator -> Type)
   (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
   (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
   (L : @obCoMod Yoneda00_Form_L Yoneda01_Form_L Yoneda00_Param_L Yoneda01_Param_L Yoneda1_FormParam_L)
   (Yoneda00_Param_LF : obGenerator -> Type)
   (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
   (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
   (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Form_ll : pseudoCode Yoneda1_Form_ll)
   (ll : 'CoMod( L ~> F @_ ReParam_LF @^ Form_ll )),

 forall (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
   (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
   (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll')
   (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
   (Form_ll_ : pseudoCode Yoneda1_Form_ll_),

 forall (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (reparam_remember : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF)
                                   ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ) ),
 forall (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
   (congr_ll : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_) ~> Form_ll @_ Congr_congr_ll ) ),

   'CoMod( L ~> PiSubst F Param_F Param_PiSubstF ReParam_SubstF
             @_ (PolyCoMod_pseudoCode_ReParam (UnitCoMod_pseudoCode_ReParam _) ReParam_LPiSubstF )
             @^ (PolyCoMod_pseudoCode (UnitCoMod_pseudoCode_ReParam _) (Remember_pseudoCode ReParam_SubstF Form_ll') ReParam_LPiSubstF Form_ll_ ) )
  
(**
/!\ TROLL /!\  REDO [REMEMBER] BY ASSUMING [FORM_LL] FASTOR AS [(FORM_LL' OVER REPARAM_LPISUBST) o>COMOD (FORM_LL'' OVER REPARAM_SUBSTF)]
   THEN THE OUTPUT IS JUST TO STRAIGHTEN THIS FACTORIZATION THROUGH [FORGET] ...
*)

where "''CoMod' ( E ~> F @_ ReParam_EF @^ Form_ff )" :=
        (@morCoMod _ _ _ _ _ E _ _ _ _ _ F  _ _ _ _ ReParam_EF _ Form_ff) : poly_scope

with morCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
   (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
   (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff), Type :=

(** -----cuts to be eliminated----- **)
| PolyCoMod_ReParam :
forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : obCoMod_Param Yoneda01_Param_F)
  (Yoneda00_Param_F' : obGenerator -> Type) (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
  (Param_F' : obCoMod_Param Yoneda01_Param_F') (Yoneda00_Param_F'F : obGenerator -> Type)
  (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F) (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
  (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F) (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
  (param_ff' : 'CoMod__( Param_F' ~> Param_F @_ ReParam_F'F  )),

forall (Yoneda00_Param_F'' : obGenerator -> Type)
  (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
  (Param_F'' : obCoMod_Param Yoneda01_Param_F'')
  (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F') (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'')
  (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
  (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
  (param_ff_ : 'CoMod__( Param_F'' ~> Param_F' @_ ReParam_F''F')),

  'CoMod__( Param_F'' ~> Param_F @_ PolyCoMod_pseudoCode_ReParam ReParam_F'F ReParam_F''F' )

(** -----solution morphisms----- **)
| UnitCoMod_ReParam : forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
    'CoMod__( Param_F ~> Param_F @_ UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F )

| View1_ReParam :
 forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
      'CoMod__( View_Param P ~> View_Param Q @_ (View1_pseudoCode_ReParam pp) )

| PolyElement_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
      
 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),

    'CoMod__( View_Param P ~> ViewingFunctor_Param_default Param_SubstF
                   @_ (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF ) cons_paramlocal ))

| ViewedFunctor1_ReParam_default : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

  'CoMod__( ViewedFunctor_Param_default Param_E ~> ViewedFunctor_Param_default Param_F  @_ ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF )

| UnitViewedFunctor_ReParam_default :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

  'CoMod__( Param_E ~> ViewedFunctor_Param_default Param_F  @_ (PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) ReParam_EF) )

| PolyTransf_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),
  
  'CoMod__( ViewingFunctor_Param_default Param_SubstF ~> ViewedFunctor_Param_default Param_E
      @_ (PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__) (PolyTransf_pseudoCode_ReParam_default' Param_SubstF ReParam_ee_)) )

| Formatting : (**MEMO: contrast this to comprehension-categry / category-with-family / natural-model ,
 where the representability conditions relates type-theory style (terms are section morphism) as-corresponding-to
 locally-catesian-closed style (arrows are morphism over one object) ,
now here section morphism (from terminal) is generalized/polymorph as morphism from any shape object , 
and morphism over one object is generalized/polymorph as morphism parametrized over any span morphism *)
forall (Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
(Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)

(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(ReParam_EF : pseudoCode_ReParam  Yoneda1_Param_proj Yoneda1_Param_subst)

(Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
(Form_ff : pseudoCode Yoneda1_Form_ff)
(ff : 'CoMod( E ~> F @_  ReParam_EF @^ Form_ff ))

(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
(Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)

(Yoneda00_Param_EF' : obGenerator -> Type)
(Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
(Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
(Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
(ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
(param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' ))

(Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
(reparam_EF :  'CoMod_$( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF ))

(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Param_D : obCoMod_Param Yoneda01_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(ReParam_DE : pseudoCode_ReParam  Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
(param_ee : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE )),
  
  'CoMod__( Param_D ~> Format F Param_F @_ (PolyCoMod_pseudoCode_ReParam (Formatting_pseudoCode_ReParam' ReParam_EF Form_ff) ReParam_DE) )

where "''CoMod__' (  Param_E  ~>  Param_F  @_ ReParam_EF )" :=
        (@morCoMod_ReParam _ _ Param_E _ _ Param_F _ _ _ _ ReParam_EF ) : poly_scope .

Notation "ff_ o>CoMod__ ff'" := (@PolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ ff' _ _ _ _ _ _ _ _ ff_ )
                                  (at level 40 , ff' at next level , left associativity) : poly_scope.
Notation "ff_ o>CoMod ff'" := (@PolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ )
                                (at level 40, left associativity) : poly_scope.

Module Export Coherence_Monoidal .
Parameter coh_congrPseudoCode_ReParam : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) ,
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                             Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (reparam_rr :  'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_rr )),
 forall (Yoneda1_Param_reparam_rr' : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                             Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (reparam_rr' :  'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_rr' )), Prop .

Infix "~~_$" := coh_congrPseudoCode_ReParam (at level 70) .

Parameter Refl_coh_congrPseudoCode_ReParam : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E),
 forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0) ,
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                             Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (reparam_rr :  'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_rr )),
   reparam_rr ~~_$ reparam_rr .

Hint Resolve Refl_coh_congrPseudoCode_ReParam : core .

Parameter coh_congrPseudoCode : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
                             (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
    forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
    forall (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Form_ff' : pseudoCode Yoneda1_Form_ff'),
    forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr)
      (congr_ff : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff )),
    forall (Yoneda1_Param_reparam_rr0 : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                 Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
    forall(Congr_congr_ff0 : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr0)
     (congr_ff0 : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff0 )), Prop .

Infix "~~$" := coh_congrPseudoCode (at level 70) .

Parameter Refl_coh_congrPseudoCode :
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
    (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
    (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
  forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
    forall (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Form_ff' : pseudoCode Yoneda1_Form_ff'),
    forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr)
      (congr_ff : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff )),
      congr_ff ~~$ congr_ff .

Hint Resolve Refl_coh_congrPseudoCode : core .

Parameter Preorder_coh_congrPseudoCode :
  forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
    (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
    (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E),
  forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F),
    forall (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda1_Form_ff),
    forall (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
      (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F),
    forall (Yoneda1_Form_ff' : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Form_ff' : pseudoCode Yoneda1_Form_ff'),
    forall (Yoneda1_Param_reparam_rr : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
      (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr)
      (congr_ff : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff )),
    forall (Yoneda1_Param_reparam_rr0 : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff
                                                 Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
    forall(Congr_congr_ff0 : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff' Yoneda1_Param_reparam_rr0)
     (congr_ff0 : 'CoMod$( Form_ff ~> Form_ff' @_ Congr_congr_ff0 )),
      congr_ff ~~$ congr_ff0 .

End Coherence_Monoidal .

Reserved Notation "ff0  [  reparam_rr @^ congr_ff  ]<~~  ff" (at level 10 ,  reparam_rr , congr_ff , ff at level 40).
Reserved Notation "param_ff0 [  reparam_rr  ]<~~__ param_ff" (at level 10 , reparam_rr , param_ff at level 40).

Inductive convCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
   (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
   Yoneda1_Param_subst_ff0 (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
   Yoneda1_Form_ff0 (Form_ff0 : pseudoCode Yoneda1_Form_ff0) (ff0 : 'CoMod( E ~> F @_ ReParam_EF0 @^ Form_ff0 )),
 forall (Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
   (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF ))
   (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff0 Yoneda1_Param_reparam_EF)
   (congr_ff : 'CoMod$( Form_ff ~> Form_ff0 @_ Congr_congr_ff  )), Prop :=

| convCoMod_Refl :  forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),
   ff [ Refl_reparam ReParam_EF  @^ Refl_congrPseudoCode Form_ff ]<~~ ff

| convCoMod_Trans :  forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
   (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
   Yoneda1_Param_subst_ff0 (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
   Yoneda1_Form_ff0 (Form_ff0 : pseudoCode Yoneda1_Form_ff0) (ff0 : 'CoMod( E ~> F @_ ReParam_EF0 @^ Form_ff0 )),
 forall (Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
   (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF ))
   (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff0 Yoneda1_Param_reparam_EF)
   (congr_ff : 'CoMod$( Form_ff ~> Form_ff0 @_ Congr_congr_ff  )),   
   ff0 [ reparam_EF  @^ congr_ff ]<~~ ff ->
 forall Yoneda00_Param_EF0' (Yoneda01_Param_EF0' : Yoneda01_Param_data Yoneda00_Param_EF0')
   (Yoneda1_Param_proj_ff0' : Yoneda1_Param_data Yoneda01_Param_EF0' Yoneda01_Param_E)
   Yoneda1_Param_subst_ff0' (ReParam_EF0' : pseudoCode_ReParam Yoneda1_Param_proj_ff0' Yoneda1_Param_subst_ff0')
   Yoneda1_Form_ff0' (Form_ff0' : pseudoCode Yoneda1_Form_ff0') (ff0' : 'CoMod( E ~> F @_ ReParam_EF0' @^ Form_ff0' )),
 forall (Yoneda1_Param_reparam_EF0 : reparamMorSym Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 Yoneda1_Param_proj_ff0' Yoneda1_Param_subst_ff0')
   (reparam_EF0 : 'CoMod_$( ReParam_EF0 ~> ReParam_EF0' @_ Yoneda1_Param_reparam_EF0 ))
   (Congr_congr_ff0 : Congr_data Yoneda1_Form_ff0 Yoneda1_Form_ff0' Yoneda1_Param_reparam_EF0)
   (congr_ff0 : 'CoMod$( Form_ff0 ~> Form_ff0' @_ Congr_congr_ff0  )),   
   ff0' [ reparam_EF0  @^ congr_ff0 ]<~~ ff0 ->
   ff0' [ reparam_EF o>_$ reparam_EF0  @^ congr_ff o>$ congr_ff0 ]<~~ ff

| PolyCoMod_cong :
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Form_F' Yoneda01_Form_F' Yoneda00_Param_F' Yoneda01_Param_F' Yoneda1_FormParam_F'
   (F' : @obCoMod Yoneda00_Form_F' Yoneda01_Form_F' Yoneda00_Param_F' Yoneda01_Param_F' Yoneda1_FormParam_F'),
 forall Yoneda00_Param_F'F (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F)
   (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
   Yoneda1_Param_subst_ff' (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff') Yoneda1_Form_ff'
   (Form_ff' : pseudoCode Yoneda1_Form_ff')
   (ff' : 'CoMod( F' ~> F @_ ReParam_F'F @^ Form_ff' )),

 forall Yoneda00_Form_F'' Yoneda01_Form_F'' Yoneda00_Param_F'' Yoneda01_Param_F'' Yoneda1_FormParam_F''
   (F'' : @obCoMod Yoneda00_Form_F'' Yoneda01_Form_F'' Yoneda00_Param_F'' Yoneda01_Param_F'' Yoneda1_FormParam_F''),
 forall Yoneda00_Param_F''F' (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F')      
   (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'')
   Yoneda1_Param_subst_ff_ (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
   Yoneda1_Form_ff_ (Form_ff_ : pseudoCode Yoneda1_Form_ff_)
   (ff_ : 'CoMod( F'' ~> F' @_ ReParam_F''F' @^ Form_ff_ )),

 forall Yoneda00_Param_E'E (Yoneda01_Param_E'E : Yoneda01_Param_data Yoneda00_Param_E'E)
   (Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F')
   Yoneda1_Param_subst_ee' (ReParam_E'E : pseudoCode_ReParam Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee') Yoneda1_Form_ee'
   (Form_ee' : pseudoCode Yoneda1_Form_ee')
   (ee' : 'CoMod( F' ~> F @_ ReParam_E'E @^ Form_ee' )),
 forall Yoneda1_Param_reparam_F'F
   (reparam_F'F : 'CoMod_$(  ReParam_F'F  ~>  ReParam_E'E  @_ Yoneda1_Param_reparam_F'F ))
   Congr_congr_ff' (congr_ff' : 'CoMod$( Form_ff' ~> Form_ee' @_ Congr_congr_ff' ) ),
   ee' [ reparam_F'F @^ congr_ff' ]<~~ ff' ->

   forall Yoneda00_Param_E''E' (Yoneda01_Param_E''E' : Yoneda01_Param_data Yoneda00_Param_E''E')      
     (Yoneda1_Param_proj_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F'')
     Yoneda1_Param_subst_ee_ (ReParam_E''E' : pseudoCode_ReParam Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
     Yoneda1_Form_ee_ (Form_ee_ : pseudoCode Yoneda1_Form_ee_)
     (ee_ : 'CoMod( F'' ~> F' @_ ReParam_E''E' @^ Form_ee_ )),
   forall Yoneda1_Param_reparam_F''F'
     (reparam_F''F' : 'CoMod_$(  ReParam_F''F'  ~>  ReParam_E''E'  @_ Yoneda1_Param_reparam_F''F' ))
     Congr_congr_ff_ (congr_ff_ : 'CoMod$( Form_ff_ ~> Form_ee_ @_ Congr_congr_ff_ ) ),
     ee_ [ reparam_F''F'  @^ congr_ff_ ]<~~ ff_ ->

     ( ee_ o>CoMod ee' )
       [ PolyCoMod_pseudoCode_ReParam_cong reparam_F'F reparam_F''F'
            @^ PolyCoMod_cong_congrPseudoCode reparam_F'F congr_ff' reparam_F''F' congr_ff_ ]<~~
       ( ff_ o>CoMod ff' )

(**TODO: MEMO:
| View1_cong : (**MEMO: this solution conversion is not used during cut-elimination resolution *)
forall (G H : obGenerator) (g : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
  (gg : viewingDefault_Constructors_Form g),
forall(g' : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
  (g'g' : viewingDefault_Constructors_Form g'),
forall (Heqparam : g' = g),

  (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of gg and g'g' *)
  ( View1 g'g' )
    [ View1_ReParam_cong_reparam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg)
                                 (viewingDefault_Constructors_of_viewingDefault_Constructors_Form g'g')
                                 (g:=(unitGenerator_reparamMorSymGenerator G)) (View1_cong_Heqparam Heqparam)
                                 ( is_Parameter0_transformation_morphism' (Is_Parameter0 _) )
                                 @^ View1_cong_congrPseudoCode gg g'g' Heqparam ]<~~
    ( View1 gg )
*)

(**TODO: MEMO:
| PolyElement_default_cong :  (**MEMO: this solution conversion is not used during cut-elimination resolution *)
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
forall (param' : Yoneda00_Param_SubstF G) (cons_paramlocal' : constructors Param_SubstF (sval Yoneda1_Param_subst G param') (Unit_is_Parameter0Default_Constructors G))
  (form' : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param')
  (cons_form' : constructors_Form F  form'),
  forall (Heqparam : param' = param)
    (Heqform : sval form' = sval form),
    (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of cons_paramlocal and cons_paramlocal' , moreover of cons_form and cons_form' *)
    ( PolyElement_default cons_paramlocal' cons_form' )
      [ PolyElement_ReParam_default_cong_reparam cons_paramlocal cons_paramlocal'
                                                 (f_equal (sval Yoneda1_Param_subst G ) Heqparam) (eq_refl _)
        @^ PolyElement_default_cong_congrPseudoCode cons_paramlocal cons_form cons_paramlocal' cons_form' Heqparam Heqform  ]<~~
      ( PolyElement_default cons_paramlocal cons_form ) 
*)

| ViewedFunctor1_default_cong :
forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E
  (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F
  (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall Yoneda10_Form_ff (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

forall Yoneda00_Param_EF' (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF'),
forall Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F,
forall (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' )),

forall Yoneda1_Param_reparam_EF
  (reparam_EF : 'CoMod_$( ReParam_EF  ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF) ),

forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0),
forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
forall Yoneda10_Form_ff0 (Form_ff0 : pseudoCode Yoneda10_Form_ff0) (ff0 : 'CoMod( E ~> F @_ ReParam_EF0 @^ Form_ff0 )),

forall (Yoneda1_Param_reparam_conv_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
  (reparam_conv_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_ff))
  Congr_congr_conv_ff (congr_conv_ff : 'CoMod$( Form_ff ~> Form_ff0 @_ Congr_congr_conv_ff ) ),
  (  ff0 )
    [ reparam_conv_ff @^ congr_conv_ff ]<~~
      (  ff ) ->
    
forall Yoneda00_Param_EF'0 (Yoneda01_Param_EF'0 : Yoneda01_Param_data Yoneda00_Param_EF'0),
forall Yoneda1_Param_proj_ff'0 : Yoneda1_Param_data Yoneda01_Param_EF'0 Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff'0 : Yoneda1_Param_data Yoneda01_Param_EF'0 Yoneda01_Param_F,
forall (ReParam_EF'0 : pseudoCode_ReParam Yoneda1_Param_proj_ff'0 Yoneda1_Param_subst_ff'0),
forall (param_ff0 : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF'0 )),

forall (Yoneda1_Param_reparam_conv_param_ff : reparamMorSym Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff' Yoneda1_Param_proj_ff'0 Yoneda1_Param_subst_ff'0)
  (reparam_conv_param_ff : 'CoMod_$ ( ReParam_EF' ~> ReParam_EF'0 @_ Yoneda1_Param_reparam_conv_param_ff)),

  (  param_ff0 )
    [ reparam_conv_param_ff ]<~~__
      (  param_ff ) ->

forall Yoneda1_Param_reparam_EF0
  (reparam_EF0 : 'CoMod_$( ReParam_EF0  ~> ReParam_EF'0 @_ Yoneda1_Param_reparam_EF0) ),

forall (Coh_reparam_EF0 : reparam_EF0 ~~_$ (Sym_reparam reparam_conv_ff) o>_$ (reparam_EF o>_$ reparam_conv_param_ff)),
  
  ( ViewedFunctor1_default ff0 param_ff0 reparam_EF0)
    [ ViewedFunctor1_ReParam_default_cong_reparam reparam_conv_ff @^ ViewedFunctor1_default_cong_congrPseudoCode reparam_conv_ff congr_conv_ff ]<~~
    ( ViewedFunctor1_default ff param_ff reparam_EF)

| UnitViewedFunctor_default_cong'
  : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
      (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
      (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E)
      (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F)
      (Param_F : obCoMod_Param Yoneda01_Param_F)
      (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
      (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )),

    forall (Yoneda00_Param_EF0 : obGenerator -> Type) (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
      (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E) (Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
      (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
      (Yoneda10_Form_ff0 : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
      (Form_ff0 : pseudoCode Yoneda10_Form_ff0) (ff0 : 'CoMod ( E ~> F @_ ReParam_EF0 @^ Form_ff0 )),

    forall (Yoneda1_Param_reparam_conv_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
      (reparam_conv_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_ff))
      Congr_congr_conv_ff (congr_conv_ff : 'CoMod$( Form_ff ~> Form_ff0 @_ Congr_congr_conv_ff ) ),
      (  ff0 )
        [ reparam_conv_ff @^ congr_conv_ff ]<~~
        (  ff ) ->

  ( UnitViewedFunctor_default Param_F ff0 )
    [ PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) reparam_conv_ff
        @^ PolyCoMod_cong_congrPseudoCode (Refl_reparam _) (Refl_congrPseudoCode _) reparam_conv_ff congr_conv_ff ]<~~
    ( UnitViewedFunctor_default Param_F ff )    

| PolyTransf_default_cong''' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),
  
forall (Yoneda1_Param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_dd_morphism : Morphism_prop Yoneda1_Param_dd_)
(ReParam_dd_ : pseudoCode_ReParam_Family Yoneda1_Param_dd_morphism)

(Yoneda00_Param_KE'__ : obGenerator -> Type)
(Yoneda01_Param_KE'__ : Yoneda01_Param_data Yoneda00_Param_KE'__)
(Yoneda1_Param_proj_dd'__ : Yoneda1_Param_data Yoneda01_Param_KE'__ Yoneda01_Param_K)
(Yoneda1_Param_subst_dd'__ : Yoneda1_Param_data Yoneda01_Param_KE'__ Yoneda01_Param_E)
(ReParam_dd'__ : pseudoCode_ReParam Yoneda1_Param_proj_dd'__ Yoneda1_Param_subst_dd'__)

(Yoneda00_Param_SubszF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubszF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subsz0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_dd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_dd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subsz0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_dd'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_dd_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_dd'__ Yoneda1_Param_subst_dd'__ (Yoneda1_Param_dd_ G paramlocal))
      (Yoneda1_Param_subsz0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_dd'__ (AtMember_ReParam ReParam_dd_ cons_paramlocal)
                          ~> ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda1_Form_dd__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_dd_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_dd_morphism : Morphism_Form_prop Yoneda1_Form_dd__)
(Form_dd__ : pseudoCode_Family Yoneda1_Form_dd_morphism)

(Yoneda1_Form_dd'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_dd'__ Yoneda1_Param_subst_dd'__)
(Form_dd'__ : pseudoCode Yoneda1_Form_dd'__ )

(Yoneda00_Param_SubszF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubszF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubszF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subsz0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_dd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_dd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subsz0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_dd0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_dd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subsz0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_dd0__ G param cons_paramlocal form cons_form))
(Form_dd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode (Yoneda1_Form_dd0__ G param cons_paramlocal form cons_form))
(dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form),
    'CoMod( View G ~> E @_ (ReParam_dd0__ G param cons_paramlocal form cons_form) @^ (Form_dd0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_dd'__ (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G)) (Yoneda1_Param_dd_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_dd'__ Yoneda1_Param_subst_dd'__ (Yoneda1_Param_dd_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subsz0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_dd0__ G param cons_paramlocal form cons_form) )
(reparam_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_dd'__ (AtMember_ReParam ReParam_dd_ cons_paramlocal) ~> ReParam_dd0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_dd__ G param cons_paramlocal form cons_form)))
(Congr_congr_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_dd'__) (Yoneda1_Form_dd__ G param form)) (Yoneda1_Form_dd0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_dd__ G param cons_paramlocal form cons_form))
(congr_dd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_dd'__ Form_dd'__ (AtMember_ReParam ReParam_dd_ cons_paramlocal) (AtMember_Form Form_dd__ cons_paramlocal cons_form) ~> (Form_dd0__ G param cons_paramlocal form cons_form) @_ Congr_congr_dd__ G param cons_paramlocal form cons_form ) ),
  
forall (Yoneda1_Param_reparam_eedd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
      reparamMorSym (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_subsz0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
  (reparam_eedd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
      'CoMod_$( ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal
                             ~> ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

forall (conv_param_eedd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
      (param_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P  cons_paramlocal)
        [ reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ]<~~__
        (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) ),

forall (Yoneda1_Param_reparam_eedd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form)
                    (Yoneda1_Param_subsz0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_dd0__ G param cons_paramlocal form cons_form))
(reparam_eedd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( ReParam_ee0__ G param cons_paramlocal form cons_form ~> ReParam_dd0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_eedd0__ G param cons_paramlocal form cons_form)))
(Congr_congr_eedd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Form_dd0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_eedd0__ G param cons_paramlocal form cons_form))
(congr_eedd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( Form_ee0__ G param cons_paramlocal form cons_form ~> Form_dd0__ G param cons_paramlocal form cons_form @_ Congr_congr_eedd0__ G param cons_paramlocal form cons_form )),
  
forall (conv_eedd0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form),
    (dd__ G param cons_paramlocal form cons_form)
    [ (reparam_eedd0__ G param cons_paramlocal form cons_form)
        @^ (congr_eedd0__ G param cons_paramlocal form cons_form) ]<~~
    (ee__ G param cons_paramlocal form cons_form)), 

forall (Yoneda1_Param_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
      reparamMorSym (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal)
                  (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_dd_ G paramlocal) )
(reparam_eedd_ :  forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( AtMember_ReParam ReParam_ee_ cons_paramlocal
                               ~> AtMember_ReParam ReParam_dd_ cons_paramlocal @_ (Yoneda1_Param_reparam_eedd_ G paramlocal P is_Parameter0_P))),

forall (Congr_congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
                       Congr_data (Yoneda1_Form_ee__ G param form) (Yoneda1_Form_dd__ G param form)
                                  (Yoneda1_Param_reparam_eedd_ _ (sval Yoneda1_Param_subst G param) _ (Is_Parameter0 G)))
(congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
    'CoMod$ ( AtMember_Form Form_ee__ cons_paramlocal cons_form ~> AtMember_Form Form_dd__ cons_paramlocal cons_form @_ Congr_congr_eedd__ G param form )),

forall (Yoneda1_Param_reparam_ee'dd'__ : reparamMorSym Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ Yoneda1_Param_proj_dd'__ Yoneda1_Param_subst_dd'__)
  (reparam_ee'dd'__ : 'CoMod_$( ReParam_ee'__  ~> ReParam_dd'__ @_ Yoneda1_Param_reparam_ee'dd'__ ) )
  (Congr_congr_ee'dd'__ : Congr_data Yoneda1_Form_ee'__ Yoneda1_Form_dd'__ Yoneda1_Param_reparam_ee'dd'__)
  (congr_ee'dd'__ : 'CoMod$( Form_ee'__ ~> Form_dd'__ @_ Congr_congr_ee'dd'__ )),

forall (Coh_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    (reparam_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
        ~~_$ (*to be refl*) ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'dd'__ (reparam_eedd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal (*to be refl*))))
                               o>_$ ((reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))))
  (Coh_reparam_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      (reparam_dd__ G param cons_paramlocal form cons_form)
        ~~_$ (*to be refl*) ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'dd'__  (reparam_eedd_ G (sval Yoneda1_Param_subst G param) (Parameter0 G) (Is_Parameter0 G) (Unit_is_Parameter0Default_Constructors G) cons_paramlocal)))
                               o>_$ ((reparam_ee__ G param cons_paramlocal form cons_form) o>_$ (reparam_eedd0__ G param cons_paramlocal form cons_form))))
  (Coh_congr_eedd__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      (congr_dd__ G param cons_paramlocal form cons_form)
        ~~$ (*to be refl*) (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode reparam_ee'dd'__ congr_ee'dd'__ (reparam_eedd_ G (sval Yoneda1_Param_subst G param) (Parameter0 G) (Is_Parameter0 G) (Unit_is_Parameter0Default_Constructors G) cons_paramlocal) (congr_eedd__ G param cons_paramlocal form cons_form)))
        o>$ ((congr_ee__ G param cons_paramlocal form cons_form) o>$ (congr_eedd0__ G param cons_paramlocal form cons_form))),

  ( PolyTransf_default param_dd_ reparam_dd_ dd__ reparam_dd__ congr_dd__ )

    [ (PolyCoMod_pseudoCode_ReParam_cong (ViewedFunctor1_ReParam_default_cong_reparam reparam_ee'dd'__)
                                         (PolyTransf_pseudoCode_ReParam_default_cong_reparam reparam_eedd_ ) )
        @^ (PolyCoMod_cong_congrPseudoCode (ViewedFunctor1_ReParam_default_cong_reparam reparam_ee'dd'__)
                                           (ViewedFunctor1_default_cong_congrPseudoCode reparam_ee'dd'__ congr_ee'dd'__)
                                           (PolyTransf_pseudoCode_ReParam_default_cong_reparam reparam_eedd_ )
                                           (PolyTransf_default_cong_congrPseudoCode''' reparam_eedd_ congr_eedd__ ) ) ]<~~

    ( PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__ )    

| Forget_cong :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
   (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
   (Yoneda00_Param_FE : obGenerator -> Type)
   (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)   
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
   Yoneda1_Param_subst_ee (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) Yoneda1_Form_ee
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( F ~> E @_  ReParam_FE @^ Form_ee )),

 forall (Yoneda00_Param_SubstF'0 : obGenerator -> Type)
   (Yoneda01_Param_SubstF'0 : Yoneda01_Param_data Yoneda00_Param_SubstF'0)   
   (Yoneda1_Param_proj'0 : Yoneda1_Param_data Yoneda01_Param_SubstF'0 Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst'0 : Yoneda1_Param_data Yoneda01_Param_SubstF'0 Yoneda01_Param_F)
   (ReParam_SubstF'0 : pseudoCode_ReParam Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)
   (param_forget'0 : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF'0 ) ),

 forall (Yoneda1_Param_reparam_forget'0 : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)
   (reparam_forget'0 : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF'0 @_ Yoneda1_Param_reparam_forget'0 )),

 forall Yoneda1_Param_reparam_conv_forget'
   (reparam_conv_forget' : 'CoMod_$(  ReParam_SubstF'  ~>  ReParam_SubstF'0  @_  Yoneda1_Param_reparam_conv_forget' )),
   param_forget'0 [ reparam_conv_forget' ]<~~__ param_forget' ->

   forall (Coh_reparam_conv_forget' : reparam_forget'0 ~~_$ ( reparam_forget' o>_$ reparam_conv_forget' )),
   
 forall (Yoneda00_Param_FE0 : obGenerator -> Type)
   (Yoneda01_Param_FE0 : Yoneda01_Param_data Yoneda00_Param_FE0)   
   (Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_FE0 Yoneda01_Param_F)
   Yoneda1_Param_subst_ee0 (ReParam_FE0 : pseudoCode_ReParam Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0) Yoneda1_Form_ee0
   (Form_ee0 : pseudoCode Yoneda1_Form_ee0)
   (ee0 : 'CoMod( F ~> E @_  ReParam_FE0 @^ Form_ee0 )),

 forall Yoneda1_Param_reparam_conv_ee
   (reparam_conv_ee : 'CoMod_$(  ReParam_FE  ~>  ReParam_FE0  @_  Yoneda1_Param_reparam_conv_ee ))
   Congr_congr_ee (congr_ee : 'CoMod$( Form_ee ~> Form_ee0 @_ Congr_congr_ee )),
   ee0 [ reparam_conv_ee @^ congr_ee ]<~~ ee ->
     
   (Forget param_forget'0 reparam_forget'0 ee0)
     [ PolyCoMod_pseudoCode_ReParam_cong reparam_conv_ee (Refl_reparam ReParam_SubstF)
       @^ ( PolyCoMod_cong_congrPseudoCode reparam_conv_ee congr_ee (Refl_reparam ReParam_SubstF)
                                           (Refl_congrPseudoCode (Forget_pseudoCode Yoneda1_FormParam_F ReParam_SubstF)) ) ]<~~
     (Forget param_forget' reparam_forget' ee)

| Remember_cong :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
   
 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' ) ),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_L : obGenerator -> Type)
   (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
   (Yoneda00_Param_L : obGenerator -> Type)
   (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
   (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
   (L : @obCoMod Yoneda00_Form_L Yoneda01_Form_L Yoneda00_Param_L Yoneda01_Param_L Yoneda1_FormParam_L)
   (Yoneda00_Param_LF : obGenerator -> Type)
   (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
   (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
   (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Form_ll : pseudoCode Yoneda1_Form_ll)
   (ll : 'CoMod( L ~> F @_ ReParam_LF @^ Form_ll )),

 forall (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
   (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
   (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll')
   (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
   (Form_ll_ : pseudoCode Yoneda1_Form_ll_),

 forall (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (reparam_remember : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF)
                                   ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ) ),
 forall (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
   (congr_ll : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_) ~> Form_ll @_ Congr_congr_ll ) ),

 forall (Yoneda00_Param_SubstF'0 : obGenerator -> Type)
   (Yoneda01_Param_SubstF'0 : Yoneda01_Param_data Yoneda00_Param_SubstF'0)   
   (Yoneda1_Param_proj'0 : Yoneda1_Param_data Yoneda01_Param_SubstF'0 Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst'0 : Yoneda1_Param_data Yoneda01_Param_SubstF'0 Yoneda01_Param_F)
   (ReParam_SubstF'0 : pseudoCode_ReParam Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)
   (param_forget'0 : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF'0 ) ),

 forall (Yoneda1_Param_reparam_forget'0 : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)
   (reparam_forget'0 : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF'0 @_ Yoneda1_Param_reparam_forget'0 )),

 forall Yoneda1_Param_reparam_conv_forget'
   (reparam_conv_forget' : 'CoMod_$(  ReParam_SubstF'  ~>  ReParam_SubstF'0  @_  Yoneda1_Param_reparam_conv_forget' )),
   param_forget'0 [ reparam_conv_forget' ]<~~__ param_forget' ->

 forall (Yoneda00_Param_LF0 : obGenerator -> Type)
   (Yoneda01_Param_LF0 : Yoneda01_Param_data Yoneda00_Param_LF0)
   (Yoneda1_Param_subst_ll0 : Yoneda1_Param_data Yoneda01_Param_LF0 Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll0 : Yoneda1_Param_data Yoneda01_Param_LF0 Yoneda01_Param_L)
   (ReParam_LF0 : pseudoCode_ReParam Yoneda1_Param_proj_ll0 Yoneda1_Param_subst_ll0)
   (Yoneda1_Form_ll0 : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll0 Yoneda1_Param_subst_ll0)
   (Form_ll0 : pseudoCode Yoneda1_Form_ll0)
   (ll0 : 'CoMod( L ~> F @_ ReParam_LF0 @^ Form_ll0 )),

 forall Yoneda1_Param_reparam_conv_ll
   (reparam_conv_ll : 'CoMod_$(  ReParam_LF  ~>  ReParam_LF0  @_  Yoneda1_Param_reparam_conv_ll ))
   Congr_congr_conv_ll (congr_conv_ll : 'CoMod$( Form_ll ~> Form_ll0 @_ Congr_congr_conv_ll )),
   ll0 [ reparam_conv_ll @^ congr_conv_ll ]<~~ ll ->

 forall (Yoneda00_Param_LPiSubstF0 : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF0 : Yoneda01_Param_data Yoneda00_Param_LPiSubstF0)
   (Yoneda1_Param_LPiSubstF_subst0 : Yoneda1_Param_data Yoneda01_Param_LPiSubstF0 Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj0 : Yoneda1_Param_data Yoneda01_Param_LPiSubstF0 Yoneda01_Param_L)
   (ReParam_LPiSubstF0 : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj0 Yoneda1_Param_LPiSubstF_subst0),
 forall (Yoneda1_Form_ll'0 : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll'0 : pseudoCode Yoneda1_Form_ll'0)
   (Yoneda1_Form_ll_0 : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj0 Yoneda1_Param_LPiSubstF_subst0)
   (Form_ll_0 : pseudoCode Yoneda1_Form_ll_0),

 forall (Yoneda1_Param_reparam_remember0 : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj0 Yoneda1_Param_LPiSubstF_subst0)
                                         (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst0) Yoneda1_Param_proj_ll0 Yoneda1_Param_subst_ll0)
   (reparam_remember0 : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF0)
                                   ~>  ReParam_LF0 @_ Yoneda1_Param_reparam_remember0 ) ),
 forall (Congr_congr_ll0 : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll'0 Yoneda1_Form_ll_0) Yoneda1_Form_ll0 Yoneda1_Param_reparam_remember0)
   (congr_ll0 : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll'0 ReParam_LPiSubstF0 Form_ll_0) ~> Form_ll0 @_ Congr_congr_ll0 ) ),

 forall (Yoneda1_Param_reparam_LPiSubstF : reparamMorSym _ _ _ _ )
   (reparam_LPiSubstF : 'CoMod_$( ReParam_LPiSubstF ~> ReParam_LPiSubstF0 @_ Yoneda1_Param_reparam_LPiSubstF ) )
   (Congr_congr_ll_ll_0 : Congr_data Yoneda1_Form_ll_ Yoneda1_Form_ll_0 Yoneda1_Param_reparam_LPiSubstF)
   (congr_ll_ll_0 : 'CoMod$( Form_ll_ ~> Form_ll_0 @_ Congr_congr_ll_ll_0 ) ),
   
 forall (Congr_congr_ll'll'0 : Congr_data Yoneda1_Form_ll' Yoneda1_Form_ll'0 (reparamMorSym_Refl _ _))
   (congr_ll'll'0 : 'CoMod$( Form_ll' ~> Form_ll'0 @_ Congr_congr_ll'll'0 ) ),

 forall (Coh_reparam_conv_forget' : reparam_forget'0 ~~_$ ( reparam_forget' o>_$ reparam_conv_forget' ))
   (Coh_reparam_remember0 : (reparam_remember0)
                              ~~_$ ( (Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) reparam_LPiSubstF))
                                       o>_$ (reparam_remember o>_$ reparam_conv_ll) ))
   (Coh_congr_ll0 : congr_ll0 ~~$ ( (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode (Refl_reparam _) congr_ll'll'0 reparam_LPiSubstF congr_ll_ll_0 ))
                                      o>$ (congr_ll o>$ congr_conv_ll) )),
   
(**TODO: ERASE   Remember_cong_congrPseudoCode ReParam_SubstF reparam_LPiSubstF congr_ll'll'0 *)
   (** /!\ YES /!\ *)
   ( Remember param_forget'0 reparam_forget'0 ll0 reparam_remember0 congr_ll0 )
     [  ( PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) reparam_LPiSubstF )
          @^ ( PolyCoMod_cong_congrPseudoCode  (Refl_reparam _) (Remember_cong_congrPseudoCode ReParam_SubstF  congr_ll'll'0) reparam_LPiSubstF congr_ll_ll_0 ) ]<~~
     ( Remember param_forget' reparam_forget' ll reparam_remember congr_ll )

| morCoMod_comp_UnitCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

   ( ff )
     [ morCoMod_comp_UnitCoMod_reparam ReParam_EF @^ morCoMod_comp_UnitCoMod_congrPseudoCode ReParam_EF Form_ff ]<~~
     ( ff o>CoMod (UnitCoMod F) )
   
| UnitCoMod_comp_morCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

   ( ff )
     [ UnitCoMod_comp_morCoMod_reparam ReParam_EF @^ UnitCoMod_comp_morCoMod_congrPseudoCode ReParam_EF Form_ff ]<~~
     ( (UnitCoMod E) o>CoMod ff  )

| View1_comp_View1' :
    forall (G H : obGenerator) (g : 'Generator( G ~> H )) (gg : viewingDefault_Constructors_Form g),
    forall (G' : obGenerator) (g' : 'Generator( G' ~> G )) (g'g' : viewingDefault_Constructors_Form g'),

      ( View1 (g := ( g' o>Generator g )) (viewingDefault_Constructors_Form_action gg g'g') )
        [ View1_ReParam_comp_View1_ReParam_reparam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg)
                                                   (viewingDefault_Constructors_of_viewingDefault_Constructors_Form g'g')
         o>_$ (**MEMO: keep this factorization through the lower/ReParam  [View1_ReParam_comp_View1_ReParam_reparam] *)
            (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) *)
            (View1_ReParam_cong_reparam (viewingDefault_Constructors_action (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (viewingDefault_Constructors_of_viewingDefault_Constructors_Form g'g'))
                                          (viewingDefault_Constructors_of_viewingDefault_Constructors_Form (viewingDefault_Constructors_Form_action gg g'g'))
                                          (g:= unitGenerator_reparamMorSymGenerator _)
                                          (reparamMorSym_Heqparam_View1_comp_View1 g g')
                                          (is_Parameter0_transformation_morphism' _)  ) 
            @^ View1_comp_View1_congrPseudoCode' gg g'g' ]<~~
        (( View1 g'g' ) o>CoMod ( View1 gg ))     

| View1_comp_PolyElement_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
forall (G' : obGenerator) (g : 'Generator( G' ~> G )) (gg : viewingDefault_Constructors_Form g),
    
  (PolyElement_default (form := (g o>GeneratorAtParam_ form))
                       ( ( constructors_action cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (constructors_Form_action_transp_Heq Yoneda1_Param_subst param g) ) )
                       ( constructors_Form_action cons_form gg))
    [ (View1_ReParam_comp_PolyElement_ReParam_default_reparam cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) )
          o>_$ (**MEMO: keep this factorization through the lower/ReParam  [View1_ReParam_comp_PolyElement_ReParam_default_reparam] *)
             (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) *)
             (PolyElement_ReParam_default_cong_reparam (constructors_action cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (eq_refl _))
              ( (constructors_action cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (constructors_Form_action_transp_Heq Yoneda1_Param_subst param g)) )
              (View1_comp_PolyElement_default_Heq Yoneda1_Param_subst param g) (erefl (sval (Is_Parameter0 G')).1))
             @^ (View1_comp_PolyElement_default_congrPseudoCode cons_paramlocal cons_form gg) ]<~~
      (View1 gg o>CoMod PolyElement_default cons_paramlocal cons_form )

| UnitViewedFunctor_default_morphism'
  : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
      (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
      (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E)
      (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F)
      (Param_F : obCoMod_Param Yoneda01_Param_F)
      (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
      (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )),

    forall (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D)
      (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
      (Yoneda10_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D) (D : obCoMod Yoneda10_FormParam_D),
       
    forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
      (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
      (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
      (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
      (Yoneda10_Form_ee : Yoneda1_Form_data Yoneda10_FormParam_D Yoneda10_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
      (Form_ee : pseudoCode Yoneda10_Form_ee) (ee : 'CoMod ( D ~> E @_ ReParam_DE @^ Form_ee )),

        ( UnitViewedFunctor_default Param_F ( ee o>CoMod ff ) )
          [ (Assoc_reparam _ _ _)  @^ (Assoc_congrPseudoCode _ _ _ _ _ _) ]<~~
          ( ee o>CoMod ( UnitViewedFunctor_default Param_F ff ) )
          
| UnitViewedFunctor_default_morphismPost' :
forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E
  (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F
  (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall Yoneda10_Form_ff (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

forall Yoneda00_Param_EF' (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF'),
forall Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F,
forall (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' )),

forall Yoneda1_Param_reparam_EF
  (reparam_EF : 'CoMod_$( ReParam_EF  ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF) ),

forall (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D)
  (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Yoneda10_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D) (D : obCoMod Yoneda10_FormParam_D),
  
forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
  (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
  (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
  (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (Yoneda10_Form_ee : Yoneda1_Form_data Yoneda10_FormParam_D Yoneda10_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (Form_ee : pseudoCode Yoneda10_Form_ee) (ee : 'CoMod ( D ~> E @_ ReParam_DE @^ Form_ee )),

  (  UnitViewedFunctor_default Param_F ( ee o>CoMod ff ) )
      [  (Sym_reparam (Assoc_reparam _ _ _))
          o>_$ ( PolyCoMod_pseudoCode_ReParam_cong (UnitViewedFunctor_ReParam_default_morphismPost_reparam' ReParam_EF) (Refl_reparam ReParam_DE) )
             o>_$ (Assoc_reparam _ _ _)
       @^ (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _))
          o>$ ( PolyCoMod_cong_congrPseudoCode (UnitViewedFunctor_ReParam_default_morphismPost_reparam' ReParam_EF) (UnitViewedFunctor_default_morphismPost_congrPseudoCode' ReParam_EF Form_ff) (Refl_reparam ReParam_DE) (Refl_congrPseudoCode Form_ee) )
             o>$ (Assoc_congrPseudoCode _ _ _ _ _ _)  ]<~~
      ( ( UnitViewedFunctor_default Param_E ee ) o>CoMod ( ViewedFunctor1_default ff param_ff reparam_EF ) )

| ViewedFunctor1_default_morphism :
forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E
  (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F
  (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall Yoneda10_Form_ff (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

forall Yoneda00_Param_EF' (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF'),
forall Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F,
forall (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' )),

forall Yoneda1_Param_reparam_EF
  (reparam_EF : 'CoMod_$( ReParam_EF  ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF) ),

forall (Yoneda00_Form_D : obGenerator -> Type) (Yoneda01_Form_D : Yoneda01_data Yoneda00_Form_D)
  (Yoneda00_Param_D : obGenerator -> Type) (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Yoneda10_FormParam_D : Yoneda1_FormParam_data Yoneda01_Form_D Yoneda01_Param_D) (D : obCoMod Yoneda10_FormParam_D)
  (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),
  
forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
  (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
  (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
  (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (Yoneda10_Form_ee : Yoneda1_Form_data Yoneda10_FormParam_D Yoneda10_FormParam_E Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (Form_ee : pseudoCode Yoneda10_Form_ee) (ee : 'CoMod ( D ~> E @_ ReParam_DE @^ Form_ee )),

forall Yoneda00_Param_DE' (Yoneda01_Param_DE' : Yoneda01_Param_data Yoneda00_Param_DE'),
forall Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_DE' Yoneda01_Param_D,
forall Yoneda1_Param_subst_ee' : Yoneda1_Param_data Yoneda01_Param_DE' Yoneda01_Param_E,
forall (ReParam_DE' : pseudoCode_ReParam Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee'),
forall (param_ee : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE' )),

forall Yoneda1_Param_reparam_DE
  (reparam_DE : 'CoMod_$( ReParam_DE  ~> ReParam_DE' @_ Yoneda1_Param_reparam_DE) ),

    ( ViewedFunctor1_default ( ee o>CoMod ff ) ( param_ee o>CoMod__ param_ff ) ( PolyCoMod_pseudoCode_ReParam_cong reparam_EF reparam_DE ) )
      [ ViewedFunctor1_ReParam_default_morphism_reparam ReParam_EF ReParam_DE
          @^ ViewedFunctor1_default_morphism_congrPseudoCode ReParam_EF Form_ff ReParam_DE Form_ee ]<~~
      ( ( ViewedFunctor1_default ee param_ee reparam_DE ) o>CoMod ( ViewedFunctor1_default ff param_ff reparam_EF ) )

| PolyTransf_default_morphism' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),
  
 forall Yoneda00_Form_D Yoneda01_Form_D Yoneda00_Param_D Yoneda01_Param_D Yoneda1_FormParam_D
   (D : @obCoMod Yoneda00_Form_D Yoneda01_Form_D Yoneda00_Param_D Yoneda01_Param_D Yoneda1_FormParam_D)
   (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),
 forall Yoneda00_Param_ED (Yoneda01_Param_ED : Yoneda01_Param_data Yoneda00_Param_ED)      
   (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_E)
   (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_D)
   (ReParam_ED : pseudoCode_ReParam Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
   (Yoneda1_Form_dd : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_D Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
   (Form_dd : pseudoCode Yoneda1_Form_dd )
   (dd : 'CoMod( E ~> D @_ ReParam_ED @^ Form_dd )),

 forall Yoneda00_Param_ED' (Yoneda01_Param_ED' : Yoneda01_Param_data Yoneda00_Param_ED')      
   (Yoneda1_Param_proj_dd' : Yoneda1_Param_data Yoneda01_Param_ED' Yoneda01_Param_E)
   (Yoneda1_Param_subst_dd' : Yoneda1_Param_data Yoneda01_Param_ED' Yoneda01_Param_D)
   (ReParam_ED' : pseudoCode_ReParam Yoneda1_Param_proj_dd' Yoneda1_Param_subst_dd')
   (param_dd : 'CoMod__( Param_E ~> Param_D @_ ReParam_ED' )),
   
forall Yoneda1_Param_reparam_ED
  (reparam_ED : 'CoMod_$( ReParam_ED  ~> ReParam_ED' @_ Yoneda1_Param_reparam_ED) ),

  ( PolyTransf_default  (fun G paramlocal  P is_Parameter0_P cons_is_Parameter0_P  cons_paramlocal => (param_ee_ G paramlocal  P is_Parameter0_P cons_is_Parameter0_P  cons_paramlocal) o>CoMod__ param_dd)
                       (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (Assoc_reparam ReParam_ED ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal))
                                                              o>_$ (PolyCoMod_pseudoCode_ReParam_cong reparam_ED (reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
                       (fun G param cons_paramlocal form cons_form => (ee__ G param cons_paramlocal form cons_form) o>CoMod dd)
                       (fun G param cons_paramlocal form cons_form => (Assoc_reparam ReParam_ED ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) )
                                            o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam ReParam_ED) (reparam_ee__ G param cons_paramlocal form cons_form)))
                       (fun G param cons_paramlocal form cons_form => (Assoc_congrPseudoCode Form_dd ReParam_ED Form_ee'__ ReParam_ee'__ (AtMember_Form Form_ee__ cons_paramlocal cons_form) (AtMember_ReParam ReParam_ee_ cons_paramlocal))
                                            o>$ PolyCoMod_cong_congrPseudoCode (Refl_reparam ReParam_ED) (Refl_congrPseudoCode Form_dd) (reparam_ee__ G param cons_paramlocal form cons_form) (congr_ee__ G param cons_paramlocal form cons_form)) )

    [ (Sym_reparam (Assoc_reparam _ _ _))
        o>_$ (PolyCoMod_pseudoCode_ReParam_cong (ViewedFunctor1_ReParam_default_morphism_reparam ReParam_ED ReParam_ee'__) (Refl_reparam _))
      @^ (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _))
      o>$ (PolyCoMod_cong_congrPseudoCode (ViewedFunctor1_ReParam_default_morphism_reparam ReParam_ED ReParam_ee'__)
                                          (ViewedFunctor1_default_morphism_congrPseudoCode ReParam_ED Form_dd ReParam_ee'__ Form_ee'__)
                                          (Refl_reparam _) (Refl_congrPseudoCode _))  ]<~~

    ( ( PolyTransf_default param_ee_ reparam_ee_  ee__ reparam_ee__ congr_ee__ )
     o>CoMod ( ViewedFunctor1_default dd param_dd reparam_ED ) )

| PolyElement_default_comp_PolyTransf_default' :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form),
  
  (UnitViewedFunctor_default Param_E ( ee__ G param cons_paramlocal form cons_form ))
    [ (Assoc_reparam _ _ _)
        o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _)
                                                ((PolyElement_ReParam_default_comp_PolyTransf_ReParam_default_reparam ReParam_ee_ cons_paramlocal)
                                                   o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) (Refl_reparam _))))
           o>_$ (Sym_reparam (Assoc_reparam _ _ _))
              o>_$ (PolyCoMod_pseudoCode_ReParam_cong (UnitViewedFunctor_ReParam_default_morphismPost_reparam' _)
                                                      (Refl_reparam _))
                 o>_$ (Assoc_reparam _ _ _)
                    o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _)
                                                (reparam_ee__ G param cons_paramlocal form cons_form))
    @^ (Assoc_congrPseudoCode _ _ _ _ _ _)
        o>$ (PolyCoMod_cong_congrPseudoCode (Refl_reparam _) (Refl_congrPseudoCode _)
                                                ((PolyElement_ReParam_default_comp_PolyTransf_ReParam_default_reparam ReParam_ee_ cons_paramlocal)
                                                   o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) (Refl_reparam _)))
                                                (PolyElement_default_comp_PolyTransf_default_congrPseudoCode' ReParam_ee_ Form_ee__ cons_paramlocal cons_form))
           o>$ (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _))
              o>$ (PolyCoMod_cong_congrPseudoCode (UnitViewedFunctor_ReParam_default_morphismPost_reparam' _) (UnitViewedFunctor_default_morphismPost_congrPseudoCode' _ _ )
                                                      (Refl_reparam _) (Refl_congrPseudoCode _))
                 o>$ (Assoc_congrPseudoCode _ _ _ _ _ _)
                    o>$ (PolyCoMod_cong_congrPseudoCode (Refl_reparam _) (Refl_congrPseudoCode _)
                                                (reparam_ee__ G param cons_paramlocal form cons_form) (congr_ee__ G param cons_paramlocal form cons_form) ) ]<~~

    ( ( PolyElement_default cons_paramlocal cons_form )
        o>CoMod ( PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__ ) )

| Forget_morphism :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
   (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
   (Yoneda00_Param_FE : obGenerator -> Type)
   (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)   
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
   Yoneda1_Param_subst_ee (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) Yoneda1_Form_ee
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( F ~> E @_  ReParam_FE @^ Form_ee )),
   
 forall Yoneda00_Form_D Yoneda01_Form_D Yoneda00_Param_D Yoneda01_Param_D Yoneda1_FormParam_D
   (D : @obCoMod Yoneda00_Form_D Yoneda01_Form_D Yoneda00_Param_D Yoneda01_Param_D Yoneda1_FormParam_D)
   (Yoneda00_Param_ED : obGenerator -> Type)
   (Yoneda01_Param_ED : Yoneda01_Param_data Yoneda00_Param_ED)   
   (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_E)
   (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_D)
   (ReParam_ED : pseudoCode_ReParam Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd) Yoneda1_Form_dd
   (Form_dd : pseudoCode Yoneda1_Form_dd)
   (dd : 'CoMod( E ~> D @_ ReParam_ED @^ Form_dd )),
     
   ( Forget param_forget' reparam_forget' ( ee o>CoMod dd ) ) [
       (Sym_reparam (Assoc_reparam _ _ _))
         @^ (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _))
     ]<~~ ( (Forget param_forget' reparam_forget' ee) o>CoMod dd )

| Remember_morphism :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
   
 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' ) ),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_L : obGenerator -> Type)
   (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
   (Yoneda00_Param_L : obGenerator -> Type)
   (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
   (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
   (L : @obCoMod Yoneda00_Form_L Yoneda01_Form_L Yoneda00_Param_L Yoneda01_Param_L Yoneda1_FormParam_L)
   (Yoneda00_Param_LF : obGenerator -> Type)
   (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
   (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
   (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Form_ll : pseudoCode Yoneda1_Form_ll)
   (ll : 'CoMod( L ~> F @_ ReParam_LF @^ Form_ll )),

 forall (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
   (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
   (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll')
   (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
   (Form_ll_ : pseudoCode Yoneda1_Form_ll_),

 forall (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (reparam_remember : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF)
                                   ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ) ),
 forall (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
   (congr_ll : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_) ~> Form_ll @_ Congr_congr_ll ) ),

 forall (Yoneda00_Form_E : obGenerator -> Type)
   (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
   (Yoneda00_Param_E : obGenerator -> Type)
   (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
   (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
   (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
   (Yoneda00_Param_EL : obGenerator -> Type)
   (Yoneda01_Param_EL : Yoneda01_Param_data Yoneda00_Param_EL)
   (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_EL Yoneda01_Param_L)
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_EL Yoneda01_Param_E)
   (ReParam_EL : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
   (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_L Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( E ~> L @_ ReParam_EL @^ Form_ee )),

   (** /!\ HAHA TACKLE /!\ [Form_ll] shall factorize through [Forget_pseudoCode ReParam_SubstF] , similar as when [ReParam_LF] factorizes through [ReParam_SubstF]
      DONE! /!\ YES /!\  *)
     ( Remember param_forget' reparam_forget' ( ee o>CoMod ll )
                ( (Sym_reparam (Assoc_reparam _ _ _)) o>_$ (PolyCoMod_pseudoCode_ReParam_cong reparam_remember (Refl_reparam ReParam_EL)) )
                ( (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _)) o>$ (PolyCoMod_cong_congrPseudoCode reparam_remember congr_ll (Refl_reparam ReParam_EL) (Refl_congrPseudoCode Form_ee) ) ) )
     [ (Assoc_reparam _ _ _)  @^ (Assoc_congrPseudoCode _ _ _ _ _ _) ]<~~
     ( ee o>CoMod ( Remember param_forget' reparam_forget' ll reparam_remember congr_ll ) )


| Remember_comp_Forget :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
   
 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' ) ),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_L : obGenerator -> Type)
   (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
   (Yoneda00_Param_L : obGenerator -> Type)
   (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
   (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
   (L : @obCoMod Yoneda00_Form_L Yoneda01_Form_L Yoneda00_Param_L Yoneda01_Param_L Yoneda1_FormParam_L)
   (Yoneda00_Param_LF : obGenerator -> Type)
   (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
   (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
   (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Form_ll : pseudoCode Yoneda1_Form_ll)
   (ll : 'CoMod( L ~> F @_ ReParam_LF @^ Form_ll )),

 forall (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
   (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
   (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll')
   (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
   (Form_ll_ : pseudoCode Yoneda1_Form_ll_),

 forall (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (reparam_remember : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF)
                                   ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ) ),
 forall (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
   (congr_ll : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_) ~> Form_ll @_ Congr_congr_ll ) ),

 forall (Yoneda00_Param_SubstF'' : obGenerator -> Type)
   (Yoneda01_Param_SubstF'' : Yoneda01_Param_data Yoneda00_Param_SubstF'')   
   (Yoneda1_Param_proj'' : Yoneda1_Param_data Yoneda01_Param_SubstF'' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst'' : Yoneda1_Param_data Yoneda01_Param_SubstF'' Yoneda01_Param_F)
   (ReParam_SubstF'' : pseudoCode_ReParam Yoneda1_Param_proj'' Yoneda1_Param_subst'')
   (param_forget'' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF'' )),

 forall (Yoneda1_Param_reparam_forget'' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj'' Yoneda1_Param_subst'')
   (reparam_forget'' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF'' @_ Yoneda1_Param_reparam_forget'' )),

 forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
   (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
   (Yoneda00_Param_FE : obGenerator -> Type)
   (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)   
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
   Yoneda1_Param_subst_ee (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) Yoneda1_Form_ee
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( F ~> E @_  ReParam_FE @^ Form_ee )), 
   
   ( ll o>CoMod ee ) [
       (Assoc_reparam _ _ _)
         o>_$ ( PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam ReParam_FE) 
                ( (Sym_reparam (Assoc_reparam _ _ _)) o>_$
                     ( ( PolyCoMod_pseudoCode_ReParam_cong (UnitCoMod_comp_morCoMod_reparam _)
                                                         (Refl_reparam ReParam_LPiSubstF) ) o>_$ reparam_remember ) ) )
    @^ (Assoc_congrPseudoCode _ _ _ _ _ _)
         o>$ ( PolyCoMod_cong_congrPseudoCode (Refl_reparam ReParam_FE) (Refl_congrPseudoCode Form_ee)
                ( (Sym_reparam (Assoc_reparam _ _ _)) o>_$
                      ( ( PolyCoMod_pseudoCode_ReParam_cong (UnitCoMod_comp_morCoMod_reparam _)
                                                            (Refl_reparam ReParam_LPiSubstF) ) o>_$ reparam_remember ) )
                ( (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _)) o>$
                      ( ( PolyCoMod_cong_congrPseudoCode (UnitCoMod_comp_morCoMod_reparam _) (Remember_comp_Forget_congrPseudoCode ReParam_SubstF Form_ll')
                                                         (Refl_reparam ReParam_LPiSubstF) (Refl_congrPseudoCode Form_ll_) ) o>$ congr_ll ) ) ) 
     ]<~~ ( (Remember param_forget' reparam_forget' ll reparam_remember congr_ll) o>CoMod (Forget param_forget'' reparam_forget'' ee) )

where "ff0 [  reparam_rr @^ congr_ff  ]<~~ ff" := (@convCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff _ _ _ _ _ _ _ ff0 _ reparam_rr _ congr_ff)
with convCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0),
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (param_ff0 : 'CoMod__( Param_E ~> Param_F @_  ReParam_EF0 )),
 forall Yoneda1_Param_reparam_EF (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF)), Prop :=

| convCoMod_ReParam_Refl : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),
   param_ff [ Refl_reparam ReParam_EF ]<~~__ param_ff
  
| convCoMod_ReParam_Trans :  forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0),
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (param_ff0 : 'CoMod__( Param_E ~> Param_F @_  ReParam_EF0 )),
 forall Yoneda1_Param_reparam_EF (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF)),
param_ff0 [ reparam_EF ]<~~__ param_ff ->

 forall Yoneda00_Param_EF0' (Yoneda01_Param_EF0' : Yoneda01_Param_data Yoneda00_Param_EF0'),
 forall Yoneda1_Param_proj_ff0' : Yoneda1_Param_data Yoneda01_Param_EF0' Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0' : Yoneda1_Param_data Yoneda01_Param_EF0' Yoneda01_Param_F,
 forall (ReParam_EF0' : pseudoCode_ReParam Yoneda1_Param_proj_ff0' Yoneda1_Param_subst_ff0'),
 forall (param_ff0' : 'CoMod__( Param_E ~> Param_F @_  ReParam_EF0' )),
 forall Yoneda1_Param_reparam_EF' (reparam_EF' : 'CoMod_$( ReParam_EF0 ~> ReParam_EF0' @_ Yoneda1_Param_reparam_EF')),
param_ff0' [ reparam_EF' ]<~~__ param_ff0 ->
param_ff0' [ reparam_EF o>_$ reparam_EF' ]<~~__ param_ff

| PolyCoMod_ReParam_cong :
forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : obCoMod_Param Yoneda01_Param_F)
  (Yoneda00_Param_F' : obGenerator -> Type) (Yoneda01_Param_F' : Yoneda01_Param_data Yoneda00_Param_F')
  (Param_F' : obCoMod_Param Yoneda01_Param_F') (Yoneda00_Param_F'F : obGenerator -> Type)
  (Yoneda01_Param_F'F : Yoneda01_Param_data Yoneda00_Param_F'F) (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F')
  (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_F'F Yoneda01_Param_F) (ReParam_F'F : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
  (param_ff' : 'CoMod__( Param_F' ~> Param_F @_ ReParam_F'F  )),

forall (Yoneda00_Param_F'' : obGenerator -> Type)
  (Yoneda01_Param_F'' : Yoneda01_Param_data Yoneda00_Param_F'')
  (Param_F'' : obCoMod_Param Yoneda01_Param_F'')
  (Yoneda00_Param_F''F' : obGenerator -> Type) (Yoneda01_Param_F''F' : Yoneda01_Param_data Yoneda00_Param_F''F') (Yoneda1_Param_proj_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F'')
  (Yoneda1_Param_subst_ff_ : Yoneda1_Param_data Yoneda01_Param_F''F' Yoneda01_Param_F')
  (ReParam_F''F' : pseudoCode_ReParam Yoneda1_Param_proj_ff_ Yoneda1_Param_subst_ff_)
  (param_ff_ : 'CoMod__( Param_F'' ~> Param_F' @_ ReParam_F''F')),

forall Yoneda00_Param_E'E (Yoneda01_Param_E'E : Yoneda01_Param_data Yoneda00_Param_E'E)
  (Yoneda1_Param_proj_ee' : Yoneda1_Param_data Yoneda01_Param_E'E Yoneda01_Param_F')
  Yoneda1_Param_subst_ee' (ReParam_E'E : pseudoCode_ReParam Yoneda1_Param_proj_ee' Yoneda1_Param_subst_ee')
  (param_ee' : 'CoMod__( Param_F' ~> Param_F @_ ReParam_E'E  )),
forall Yoneda1_Param_reparam_F'F
  (reparam_F'F : 'CoMod_$(  ReParam_F'F  ~>  ReParam_E'E  @_ Yoneda1_Param_reparam_F'F )),
  param_ee' [ reparam_F'F ]<~~__ param_ff' ->

  forall Yoneda00_Param_E''E' (Yoneda01_Param_E''E' : Yoneda01_Param_data Yoneda00_Param_E''E')      
    (Yoneda1_Param_proj_ee_ : Yoneda1_Param_data Yoneda01_Param_E''E' Yoneda01_Param_F'')
    Yoneda1_Param_subst_ee_ (ReParam_E''E' : pseudoCode_ReParam Yoneda1_Param_proj_ee_ Yoneda1_Param_subst_ee_)
    (param_ee_ : 'CoMod__( Param_F'' ~> Param_F' @_ ReParam_E''E')),
  forall Yoneda1_Param_reparam_F''F'
  (reparam_F''F' : 'CoMod_$(  ReParam_F''F'  ~>  ReParam_E''E'  @_ Yoneda1_Param_reparam_F''F' )),
    param_ee_ [ reparam_F''F' ]<~~__ param_ff_ ->

  
     ( param_ee_ o>CoMod__ param_ee' )
       [ PolyCoMod_pseudoCode_ReParam_cong reparam_F'F reparam_F''F' ]<~~__
       ( param_ff_ o>CoMod__ param_ff' )

(**TODO: MEMO:
| View1_ReParam_cong : (**MEMO: this solution conversion is not used during cut-elimination resolution *)
 forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
 forall (G' : obGenerator) (p' : 'Parametrizator(  Parameter0 G' ~> Q )) (is_Parameter0_P' : is_Parameter0 G' P)
   (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
   (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
    forall (g : reparamMorSymGenerator G' G),
      forall (Heqparam : p' = (Parameter1 (fst (sval g))) o>Parametrizator p),
      forall (Heqis : fst (sval is_Parameter0_P') =  fst (sval (is_Parameter0_transformation  g is_Parameter0_P)) ),
        (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of pp and p'p' *)
        ( View1_ReParam p'p' )
          [ View1_ReParam_cong_reparam pp p'p' Heqparam Heqis ]<~~__
          ( View1_ReParam pp )
*)

(**TODO: MEMO:
| PolyElement_ReParam_default_cong : (**MEMO: this solution conversion is not used during cut-elimination resolution *)
    (**MEMO: the action polymorphism is similar as congruence with some non-iso [g : G ~> G] variation ... *)
forall (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
  (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
  (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
forall (paramlocal' : Yoneda00_Param_SumSubstF G) (is_Parameter0_P' : is_Parameter0 G P)
  (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
  (cons_paramlocal' : constructors Param_SubstF paramlocal' cons_is_Parameter0_P' ),
forall (Heqparamlocal : paramlocal' = paramlocal)
  (Heqis : fst (sval is_Parameter0_P') = fst (sval is_Parameter0_P)),
  (**TODO: for now this uses senses, but shall be fully grammatical (using the common sameness at some viewing-intersection) of cons_paramlocal and cons_paramlocal' *)
  ( PolyElement_ReParam_default cons_paramlocal' )
    [ PolyElement_ReParam_default_cong_reparam  cons_paramlocal cons_paramlocal' Heqparamlocal Heqis ]<~~__
    ( PolyElement_ReParam_default cons_paramlocal )
*)

| ViewedFunctor1_ReParam_default_cong : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
  (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
  (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
  (param_ff0 : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF0 )),
forall (Yoneda1_Param_reparam_conv_param_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
  (reparam_conv_param_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_param_ff)),

  (  param_ff0 )
    [ reparam_conv_param_ff ]<~~__
      (  param_ff ) ->

  ( ViewedFunctor1_ReParam_default  param_ff0 )
    [  ViewedFunctor1_ReParam_default_cong_reparam reparam_conv_param_ff ]<~~__
    ( ViewedFunctor1_ReParam_default param_ff )

| UnitViewedFunctor_ReParam_default_cong' :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
  (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
  (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
  (param_ff0 : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF0 )),

forall (Yoneda1_Param_reparam_conv_param_ff : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
  (reparam_conv_param_ff : 'CoMod_$ ( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_param_ff)),

  (  param_ff0 )
    [ reparam_conv_param_ff ]<~~__
      (  param_ff ) ->

  ( UnitViewedFunctor_ReParam_default param_ff0 )
    [  PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) reparam_conv_param_ff ]<~~__
    ( UnitViewedFunctor_ReParam_default param_ff )
    
| PolyTransf_ReParam_default_cong :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

forall (Yoneda1_Param_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_dd_morphism : Morphism_prop Yoneda1_Param_dd_)
  (ReParam_dd_ :  pseudoCode_ReParam_Family Yoneda1_Param_dd_morphism)

(Yoneda00_Param_dd'__ : obGenerator -> Type) (Yoneda01_Param_dd'__ : Yoneda01_Param_data Yoneda00_Param_dd'__)
(Yoneda1_Param_proj_dd' : Yoneda1_Param_data Yoneda01_Param_dd'__ Yoneda01_Param_K) (Yoneda1_Param_subst_dd' : Yoneda1_Param_data Yoneda01_Param_dd'__ Yoneda01_Param_E)
(ReParam_dd'__ : pseudoCode_ReParam Yoneda1_Param_proj_dd' Yoneda1_Param_subst_dd')

(Yoneda00_Param_SubszF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubszF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subsz0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_dd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubszF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_dd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subsz0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_dd_ :  forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym _ _ _ _ )
(reparam_dd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_dd'__  (AtMember_ReParam ReParam_dd_ cons_paramlocal)
                          ~> ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

forall (Yoneda1_Param_reparam_eedd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym _ _ _ _ )
  (reparam_eedd0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal
                          ~> ReParam_dd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

forall (conv_param_eedd0_ :  forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
      (param_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
        [ (reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) ]<~~__
        (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)),

forall (Yoneda1_Param_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P),
    reparamMorSym _ _ _ _ )
(reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( AtMember_ReParam ReParam_ee_ cons_paramlocal
                          ~> AtMember_ReParam ReParam_dd_ cons_paramlocal @_ (Yoneda1_Param_reparam_eedd_ G paramlocal P is_Parameter0_P))),
forall (Yoneda1_Param_reparam_ee'dd'__ : reparamMorSym _ _ _ _ )
  (reparam_ee'dd'__ : 'CoMod_$( ReParam_ee'__ ~> ReParam_dd'__ @_ Yoneda1_Param_reparam_ee'dd'__)),

forall (Coh_reparam_eedd_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
      (reparam_dd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
        ~~_$ (*to be refl*) ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'dd'__ (reparam_eedd_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal (*to be refl*))))
                               o>_$ ((reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_eedd0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))),
           
  
  ( PolyTransf_ReParam_default param_dd_ reparam_dd_ )

    [ (PolyCoMod_pseudoCode_ReParam_cong (ViewedFunctor1_ReParam_default_cong_reparam reparam_ee'dd'__)
                                         (PolyTransf_pseudoCode_ReParam_default_cong_reparam reparam_eedd_ ) ) ]<~~__

    ( PolyTransf_ReParam_default param_ee_ reparam_ee_ )

| Formatting_cong :
forall (Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
(Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)

(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(ReParam_EF : pseudoCode_ReParam  Yoneda1_Param_proj Yoneda1_Param_subst)

(Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
(Form_ff : pseudoCode Yoneda1_Form_ff)
(ff : 'CoMod( E ~> F @_  ReParam_EF @^ Form_ff ))

(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
(Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)

(Yoneda00_Param_EF' : obGenerator -> Type)
(Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
(Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
(Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
(ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
(param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' ))

(Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
(reparam_EF :  'CoMod_$( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF ))

(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Param_D : obCoMod_Param Yoneda01_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(ReParam_DE : pseudoCode_ReParam  Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
(param_ee : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE )),

forall (Yoneda00_Param_EF0 : obGenerator -> Type)
(Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
(Yoneda1_Param_proj0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
(Yoneda1_Param_subst0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F)
(ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj0 Yoneda1_Param_subst0)

(Yoneda1_Form_ff0 : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj0 Yoneda1_Param_subst0)
(Form_ff0 : pseudoCode Yoneda1_Form_ff0)
(ff0 : 'CoMod( E ~> F @_  ReParam_EF0 @^ Form_ff0 ))

(Yoneda1_Param_reparam_conv_ff : _ )
(reparam_conv_ff :  'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_conv_ff ))
Congr_congr_conv_ff (congr_conv_ff : 'CoMod$( Form_ff ~> Form_ff0 @_ Congr_congr_conv_ff )),
  ff0 [reparam_conv_ff @^ congr_conv_ff]<~~ ff ->

forall (Yoneda00_Param_EF'0 : obGenerator -> Type)
(Yoneda01_Param_EF'0 : Yoneda01_Param_data Yoneda00_Param_EF'0)
(Yoneda1_Param_proj'0 : Yoneda1_Param_data Yoneda01_Param_EF'0 Yoneda01_Param_E)
(Yoneda1_Param_subst'0 : Yoneda1_Param_data Yoneda01_Param_EF'0 Yoneda01_Param_F)
(ReParam_EF'0 : pseudoCode_ReParam Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)

(param_ff0 : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF'0 ))

(Yoneda1_Param_reparam_EF0 : reparamMorSym Yoneda1_Param_proj0 Yoneda1_Param_subst0 Yoneda1_Param_proj'0 Yoneda1_Param_subst'0)
(reparam_EF0 :  'CoMod_$( ReParam_EF0 ~> ReParam_EF'0 @_ Yoneda1_Param_reparam_EF0 ))

(Yoneda1_Param_reparam_conv_param_ff : _ )
(reparam_conv_param_ff :  'CoMod_$( ReParam_EF' ~> ReParam_EF'0 @_ Yoneda1_Param_reparam_conv_param_ff )),
  param_ff0 [reparam_conv_param_ff]<~~__ param_ff ->

forall (Yoneda00_Param_DE0 : obGenerator -> Type)
(Yoneda01_Param_DE0 : Yoneda01_Param_data Yoneda00_Param_DE0)
(Yoneda1_Param_proj_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_D)
(Yoneda1_Param_subst_ee0 : Yoneda1_Param_data Yoneda01_Param_DE0 Yoneda01_Param_E)
(ReParam_DE0 : pseudoCode_ReParam  Yoneda1_Param_proj_ee0 Yoneda1_Param_subst_ee0)
(param_ee0 : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE0 ))

(Yoneda1_Param_reparam_conv_param_ee : _ )
(reparam_conv_param_ee :  'CoMod_$( ReParam_DE ~> ReParam_DE0 @_ Yoneda1_Param_reparam_conv_param_ee )),
  param_ee0 [reparam_conv_param_ee]<~~__ param_ee ->

forall (Coh_reparam_EF0 : reparam_EF0 ~~_$ (Sym_reparam reparam_conv_ff) o>_$ (reparam_EF o>_$ reparam_conv_param_ff)),
    
(*  forall YKK (KK : 'CoMod_$ ( _ ~> _ @_ YKK )), forall (YKK2 : Congr_data _ _ YKK) (KK2 : 'CoMod$ ( _ ~> _ @_ YKK2 )),   *)
(** AMBUSH /!\ TODO: create codes for Yoneda1_Form and reformulate conv_sense as codes 'CoMod$ which carry only-proofs no-data , and is carried by the conversion relation *)
  ( Formatting ff0 param_ff0 reparam_EF0 param_ee0 )
    [ ( PolyCoMod_pseudoCode_ReParam_cong (Formatting_cong_reparam reparam_conv_ff congr_conv_ff) reparam_conv_param_ee ) ]<~~__
    ( Formatting ff param_ff reparam_EF param_ee )

| morCoMod_ReParam_comp_UnitCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
                    Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)
                    Yoneda00_Param_EF  (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                    (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                    (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),

   ( param_ff )
     [ morCoMod_comp_UnitCoMod_reparam ReParam_EF ]<~~__
     ( param_ff o>CoMod__ (UnitCoMod_ReParam Param_F) )
   
| UnitCoMod_ReParam_comp_morCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
                    Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)
                    Yoneda00_Param_EF  (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                    (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                    (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),

   ( param_ff )
     [ UnitCoMod_comp_morCoMod_reparam ReParam_EF ]<~~__
     ( (UnitCoMod_ReParam Param_E) o>CoMod__ param_ff  )
    
| View1_ReParam_comp_View1_ReParam : (**MEMO: THIS ACTION POLYMORPHISM IS ALREADY THE MOST GENERAL POSSIBLE CONGRUENCE , SO THE NON-LACKED COMMON CONGRUENCE OCCURS AS META/DEFINITIONAL-CONVERSION ONLY *)
    forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
      (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
      (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
    forall  (G' : obGenerator) (p' : 'Parametrizator(  Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P') (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
       (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P'),
  
      ( View1_ReParam (p:=((is_Parameter0_transp_codom is_Parameter0_P p') o>Parametrizator p))
                      (viewingDefault_Constructors_action pp p'p'))
     [ View1_ReParam_comp_View1_ReParam_reparam pp p'p'  ]<~~__
     (( View1_ReParam p'p') o>CoMod__ ( View1_ReParam pp ))

| View1_ReParam_comp_PolyElement_ReParam_default : (**MEMO: THIS ACTION POLYMORPHISM IS ALREADY THE MOST GENERAL POSSIBLE CONGRUENCE , SO THE NON-LACKED COMMON CONGRUENCE OCCURS AS META/DEFINITIONAL-CONVERSION ONLY *)
forall (Yoneda00_Param_SubstF : obGenerator -> Type)                            
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
    
 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
forall (G' : obGenerator) (p' : 'Parametrizator( Parameter0 G' ~> P )) (P' : obParametrizator) (is_Parameter0_P' : is_Parameter0 G' P')
  (cons_is_Parameter0_P' : is_Parameter0Default_Constructors is_Parameter0_P')
  (p'p' : viewingDefault_Constructors p' cons_is_Parameter0_P' ),

  ( PolyElement_ReParam_default  (constructors_action cons_paramlocal p'p' (eq_refl _))  )

     [ View1_ReParam_comp_PolyElement_ReParam_default_reparam cons_paramlocal p'p' ]<~~__
     (( View1_ReParam p'p' ) o>CoMod__ ( PolyElement_ReParam_default cons_paramlocal ))

| UnitViewedFunctor_ReParam_default_morphism' :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),

forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
  (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
  (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
  (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (param_ee : 'CoMod__( Param_D ~> Param_E  @_ ReParam_DE )),

  ( UnitViewedFunctor_ReParam_default ( param_ee o>CoMod__ param_ff ) )
    [  (Assoc_reparam _ _ _)  ]<~~__
    ( param_ee o>CoMod__ ( UnitViewedFunctor_ReParam_default param_ff ) )

| UnitViewedFunctor_ReParam_default_morphismPost' :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),

forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
  (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
  (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
  (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (param_ee : 'CoMod__( Param_D ~> Param_E  @_ ReParam_DE )),

  ( UnitViewedFunctor_ReParam_default ( param_ee o>CoMod__ param_ff ) )
    [ (Sym_reparam (Assoc_reparam _ _ _))
          o>_$ ( PolyCoMod_pseudoCode_ReParam_cong (UnitViewedFunctor_ReParam_default_morphismPost_reparam' ReParam_EF) (Refl_reparam ReParam_DE) )
             o>_$ (Assoc_reparam _ _ _)  ]<~~__
    ( ( UnitViewedFunctor_ReParam_default param_ee ) o>CoMod__ ( ViewedFunctor1_ReParam_default param_ff ) )

| ViewedFunctor1_ReParam_default_morphism :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

forall Yoneda00_Param_D (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
  (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),

forall Yoneda00_Param_DE (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
  (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
  (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
  (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
  (param_ee : 'CoMod__( Param_D ~> Param_E  @_ ReParam_DE )),
  
  ( ViewedFunctor1_ReParam_default ( param_ee o>CoMod__ param_ff ) )
    [ ViewedFunctor1_ReParam_default_morphism_reparam ReParam_EF ReParam_DE ]<~~__
    ( ( ViewedFunctor1_ReParam_default param_ee ) o>CoMod__ ( ViewedFunctor1_ReParam_default param_ff ) )

| PolyTransf_ReParam_default_morphism :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

 forall Yoneda00_Param_D Yoneda01_Param_D 
   (Param_D : @obCoMod_Param Yoneda00_Param_D Yoneda01_Param_D),
 forall Yoneda00_Param_ED (Yoneda01_Param_ED : Yoneda01_Param_data Yoneda00_Param_ED)      
   (Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_E)
   (Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_ED Yoneda01_Param_D)
   (ReParam_ED : pseudoCode_ReParam Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
   (param_dd : 'CoMod__( Param_E ~> Param_D @_ ReParam_ED )),

   ( PolyTransf_ReParam_default 
                       (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (param_ee_ G paramlocal  P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>CoMod__ param_dd)
                       (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (Assoc_reparam ReParam_ED ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal))
                                                              o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) (reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))) )

    [ (Sym_reparam (Assoc_reparam _ _ _))
        o>_$ (PolyCoMod_pseudoCode_ReParam_cong (ViewedFunctor1_ReParam_default_morphism_reparam ReParam_ED ReParam_ee'__) (Refl_reparam _)) ]<~~__

    ( ( PolyTransf_ReParam_default  param_ee_ reparam_ee_ )
        o>CoMod__ ( ViewedFunctor1_ReParam_default param_dd ) )

|  PolyElement_ReParam_default_comp_PolyTransf_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),

 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),

  (UnitViewedFunctor_ReParam_default ( param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P  cons_paramlocal ))

    [ (Assoc_reparam _ _ _)
        o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _)
                                                (PolyElement_ReParam_default_comp_PolyTransf_ReParam_default_reparam ReParam_ee_ cons_paramlocal) )
           o>_$ (Sym_reparam (Assoc_reparam _ _ _))
              o>_$ (PolyCoMod_pseudoCode_ReParam_cong (UnitViewedFunctor_ReParam_default_morphismPost_reparam' _)
                                                      (Refl_reparam _))
                 o>_$ (Assoc_reparam _ _ _)
                    o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _)
                                                (reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)) ]<~~__

    ( ( PolyElement_ReParam_default cons_paramlocal )
        o>CoMod__ ( PolyTransf_ReParam_default  param_ee_ reparam_ee_ ) )

| Formatting_morphism :
forall (Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
(Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)

(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(ReParam_EF : pseudoCode_ReParam  Yoneda1_Param_proj Yoneda1_Param_subst)

(Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
(Form_ff : pseudoCode Yoneda1_Form_ff)
(ff : 'CoMod( E ~> F @_  ReParam_EF @^ Form_ff ))

(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
(Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)

(Yoneda00_Param_EF' : obGenerator -> Type)
(Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
(Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
(Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
(ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
(param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' ))

(Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
(reparam_EF :  'CoMod_$( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF ))

(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Param_D : obCoMod_Param Yoneda01_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(ReParam_DE : pseudoCode_ReParam  Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
(param_ee : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE )),

forall (Yoneda00_Param_C : obGenerator -> Type)
(Yoneda01_Param_C : Yoneda01_Param_data Yoneda00_Param_C)
(Param_C : obCoMod_Param Yoneda01_Param_C)
(Yoneda00_Param_CD : obGenerator -> Type)
(Yoneda01_Param_CD : Yoneda01_Param_data Yoneda00_Param_CD)
(Yoneda1_Param_proj_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_C)
(Yoneda1_Param_subst_dd : Yoneda1_Param_data Yoneda01_Param_CD Yoneda01_Param_D)
(ReParam_CD : pseudoCode_ReParam  Yoneda1_Param_proj_dd Yoneda1_Param_subst_dd)
(param_dd : 'CoMod__( Param_C ~> Param_D @_ ReParam_CD )),

(**TODO: ERASE Formatting_morphism_reparam  *)
    ( Formatting ff param_ff reparam_EF (param_dd o>CoMod__ param_ee) )
      [ (Assoc_reparam _ _ _)  ]<~~__
      ( param_dd o>CoMod__ (Formatting ff param_ff reparam_EF param_ee) )

where "param_ff0  [  reparam_rr  ]<~~__ param_ff" := (@convCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff _ _ _ _ _ param_ff0  _ reparam_rr).


(** ----HERE---NEXT----
**)
(**TODO: OLD ERASE
TODO: add this property into Format that :  for x : Param_E , condition (ff , subst_ff) is constant on the proj_ff-fibre (Format E Param_EF proj_ff)(x) , therefore get "span-function"  correspondence from input (x : Param_E) to single output  (Format F Param_F) but such correspondence has multiplicity (Format E Param_EF proj_ff)(x) . at the end is similar to the common formulation, but with general shapes of elements 

WAIT THERE IS MORE: this top-property gives this bottom-property formulation of structure that : the span  Param_E <- (Format E Param_EF proj_ff) -> (Format F Param_F)  factors as some  (Format E Param_EF proj_ff) -> Param_E - - -> (Format F Param_F) . finally this bottom-property is used to show the top-property of the polymorph-Forget in the particular Format in the contractum of the conversion .  BUT THE TOP-DOMAIN-OBJECT IS STILL GENERAL SHAPE !

MEMO: the bottom-property everywhere with the terminal-top-domain-object condition on Format solves the top-property condition for any Format ... but this singleton-shape at the top and singleton-shape at the bottom is precisely the contrast to the general-shape above (GENERAL TOP-DOMAIN-OBJECT) and general-shape at the bottom (GENERAL SPAN) !

SOLVED!!! the prj part of Format is some projection, therefore Format shall be in polymorph/accumulator formulation for precompositions in morCOMod_ReParam
*)
            
Hint Constructors convCoMod convCoMod_ReParam : core.

Notation max m n := (Nat.add m (Nat.sub n m)).
Arguments Nat.sub : simpl nomatch.
Arguments Nat.add : simpl nomatch.

Notation Is_Parameter0_Unit := (Unit_is_Parameter0Default_Constructors _).
Notation True_Binary_Unit := (True_Binary Unit_viewingDefault_Constructors_Binary).
Notation False_Binary_Unit := (False_Binary Unit_viewingDefault_Constructors_Binary).
Notation True_Binary_Form_Unit := (True_Binary_Form Unit_viewingDefault_Constructors_Form_Binary).
Notation False_Binary_Form_Unit := (False_Binary_Form Unit_viewingDefault_Constructors_Form_Binary).

Fixpoint gradeCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
         (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
         Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
         (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
         Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
         (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
         (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Form_ff : pseudoCode Yoneda1_Form_ff)
         (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )) {struct ff} : nat
with gradeCoMod_ReParam Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
                    Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)
                    Yoneda00_Param_EF  (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                    (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                    (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )) {struct param_ff} : nat .
Proof.
{ case : Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E E Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F F  Yoneda00_Param_EF Yoneda01_Param_EF  Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF Yoneda1_Form_ff Form_ff / ff. 
  - (** PolyCoMod *) intros.
    exact: ( 2 * (S (gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  ff_ + gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff')%nat ) )%nat . 
  - (** UnitCoMod *) intros. 
    exact: (S O).
  - (** View1 *)  intros. 
    exact: (S O).
  -  (** PolyElement_default *) intros.
     exact: (S (S O)).
  - (** ViewedFunctor1_default *) intros.
    exact: (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff + gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)%nat ) .
  - (**  UnitViewedFunctor_default *) intros.
    exact: (S (gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)%nat ) .
  - (** PolyTransf_default *) intros. destruct F.
    exact (S (S ((max (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _
                         (param_ee_ GBinary (unitParametrizator o>Parametrizator_ true_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary)
                                    Is_Parameter0_Unit True_Binary_Unit))
                      (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _
                         (param_ee_ GBinary (unitParametrizator o>Parametrizator_ false_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary)
                                    Is_Parameter0_Unit False_Binary_Unit))) +
                 (max (gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                  (ee__ GBinary (Parameter1 unitGenerator o>Parametrizator_ true_Binary GBinary)
                                        True_Binary_Unit
                                        (unitGenerator o>GeneratorAtParam_ true_Binary_Form GBinary)
                                        True_Binary_Form_Unit))
                      (gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                  (ee__ GBinary (Parameter1 unitGenerator o>Parametrizator_ false_Binary GBinary)
                                        False_Binary_Unit
                                        (unitGenerator o>GeneratorAtParam_ false_Binary_Form GBinary)
                                        False_Binary_Form_Unit))))%nat )).
  - (** Forget *) intros.
    exact: ( S (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_forget' + gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee)%nat ) ) . 
  - (** Remember *) intros.
    exact: ( S (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_forget' + gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ll)%nat ) ) . }

{ case : Yoneda00_Param_E Yoneda01_Param_E Param_E Yoneda00_Param_F Yoneda01_Param_F Param_F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF / param_ff.
  - (** PolyCoMod_ReParam *) intros.
    exact: ( 2 * (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff_ + gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff')%nat ) )%nat . 
  - (** UnitCoMod_ReParam *) intros.
    exact: (S O ).
  - (** View1_ReParam *) intros.
    exact: (S O).
  - (** PolyElement_ReParam_default *) intros.
    exact: (S (S O)).
  - (** ViewedFunctor1_ReParam_default *) intros.
    exact: (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff)%nat ).
  - (** UnitViewedFunctor_ReParam_default *) intros.
    exact: (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff)%nat).
  - (** PolyTransf_ReParam_default *) intros. destruct Param_SubstF.
    exact (S (S (max (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _
                         (param_ee_ GBinary (unitParametrizator o>Parametrizator_ true_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary)
                                    Is_Parameter0_Unit True_Binary_Unit))
                      (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _
                         (param_ee_ GBinary (unitParametrizator o>Parametrizator_ false_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary)
                                    Is_Parameter0_Unit False_Binary_Unit))))).
  - (** Formatting *) intros.
    exact: ( S (S (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ee + (gradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff + gradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)%nat )%nat ) ) . }
Defined.

Ltac tac_simpl_Data  :=
   match goal with
         | [ Param_SubstF : obCoMod_Param_Data ?Yoneda1_Param_subst ,
             F : obCoMod_Data ?Yoneda1_FormParam_F ?Yoneda1_Param_proj ?Param_SubstF
             |- _ ] => destruct F; simpl gradeCoMod; simpl gradeCoMod_ReParam
         | [ Param_SubstF : obCoMod_Param_Data ?Yoneda1_Param_subst
             |- _ ] => destruct Param_SubstF; simpl gradeCoMod; simpl gradeCoMod_ReParam
         | [  |- _ ] => simpl gradeCoMod; simpl gradeCoMod_ReParam
         end.

Arguments gradeCoMod : simpl nomatch.
Arguments gradeCoMod_ReParam : simpl nomatch.

Lemma gradeCoMod_gt0 Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
         (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
         Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
         (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
         Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
         (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
         (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Form_ff : pseudoCode Yoneda1_Form_ff)
         (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )) : ((S O) <= (gradeCoMod ff))%nat
with gradeCoMod_ReParam_gt0 Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
                    Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)
                    Yoneda00_Param_EF  (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                    (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                    (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )) : ((S O) <= (gradeCoMod_ReParam param_ff))%nat .
Proof.
{ Time case : Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E E Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F F  Yoneda00_Param_EF Yoneda01_Param_EF  Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF Yoneda1_Form_ff Form_ff / ff ;
    intros; tac_simpl_Data; abstract Lia.lia. (** Finished transaction in 18.908 secs (18.887u,0.01s) (successful) ; 23sec ; 4secs *) }

{ case : Yoneda00_Param_E Yoneda01_Param_E Param_E Yoneda00_Param_F Yoneda01_Param_F Param_F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF / param_ff  ;
    intros; tac_simpl_Data; abstract Lia.lia. }
Qed.

Ltac tac_gradeCoMod_gt0 :=
  match goal with
  | [ gg1 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
            gg2 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
                        gg4 : 'CoMod( _ ~> _ @_ _ @^ _ ) |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
                                          (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg3)
                                          (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
            gg2 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @_ _ @^ _ ) |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
                                          (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod( _ ~> _ @_ _ @^ _ ) ,
            gg2 : 'CoMod( _ ~> _ @_ _ @^ _ )  |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
  | [ gg1 : 'CoMod( _ ~> _ @_ _ @^ _ )  |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) 
  end.

Ltac tac_gradeCoMod_ReParam_gt0 :=
  match goal with
  | [ gg1 : 'CoMod__( _ ~> _ @_ _ ) ,
            gg2 : 'CoMod__( _ ~> _ @_ _ ) ,
                  gg3 : 'CoMod__( _ ~> _ @_ _ ) ,
                        gg4 : 'CoMod__( _ ~> _ @_ _ ) |- _ ] =>
    move : (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg1)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg2)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg3)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod__( _ ~> _ @_ _ ) ,
            gg2 : 'CoMod__( _ ~> _ @_ _ ) ,
                  gg3 : 'CoMod__( _ ~> _ @_ _ ) |- _ ] =>
    move : (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg1)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg2)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod__( _ ~> _ @_ _ ) ,
            gg2 : 'CoMod__( _ ~> _ @_ _ )  |- _ ] =>
    move : (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg1)
             (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg2)
  | [ gg1 : 'CoMod__( _ ~> _ @_ _ )  |- _ ] =>
    move : (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _ gg1) 
  end.

Ltac tac_gradeCoMod_gt0_Data :=
match goal with
| [ gg1 : (forall (G : obGenerator) (param : ?Yoneda00_Param_SubstF G)
             (cons_paramlocal : constructors ?Param_SubstF (sval ?Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
             (form : Yoneda00_AtParam_ ?Yoneda1_FormParam_F ?Yoneda1_Param_proj param)
             (cons_form : constructors_Form ?F  form),
              'CoMod( _ ~> _ @_ _ @^ _ )),
    gg2 : (forall (G : obGenerator) (param : ?Yoneda00_Param_SubstF G)
             (cons_paramlocal : constructors ?Param_SubstF (sval ?Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
             (form : Yoneda00_AtParam_ ?Yoneda1_FormParam_F ?Yoneda1_Param_proj param)
             (cons_form : constructors_Form ?F  form),
              'CoMod( _ ~> _ @_ _ @^ _ ))
    |- _ ] => try (move:
              (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                               (@gg1 _ _ True_Binary_Unit _ True_Binary_Form_Unit))
                (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (@gg1 _ _ False_Binary_Unit _ False_Binary_Form_Unit))
                (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (@gg2 _ _ True_Binary_Unit _ True_Binary_Form_Unit))
                (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (@gg2 _ _ False_Binary_Unit _ False_Binary_Form_Unit)))

| [ gg1 : (forall (G : obGenerator) (param : ?Yoneda00_Param_SubstF G)
             (cons_paramlocal : constructors ?Param_SubstF (sval ?Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
             (form : Yoneda00_AtParam_ ?Yoneda1_FormParam_F ?Yoneda1_Param_proj param)
             (cons_form : constructors_Form ?F  form),
              'CoMod( _ ~> _ @_ _ @^ _ ))
    |- _ ] => try (move:
              (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                               (@gg1 _ _ True_Binary_Unit _ True_Binary_Form_Unit))
                (@gradeCoMod_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (@gg1 _ _ False_Binary_Unit _ False_Binary_Form_Unit)))
end.

Ltac tac_gradeCoMod_ReParam_gt0_Data :=
match goal with
| [ gg1 : (forall (G : obGenerator) (paramlocal : ?Yoneda00_Param_SumSubstF G)
             (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
             (cons_paramlocal : constructors ?Param_SubstF paramlocal cons_is_Parameter0_P ),
             'CoMod__( _ ~> _ @_ _ )),
    gg2 : (forall (G : obGenerator) (paramlocal : ?Yoneda00_Param_SumSubstF G)
             (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
             (cons_paramlocal : constructors ?Param_SubstF paramlocal cons_is_Parameter0_P ),
              'CoMod__( _ ~> _ @_ _ ))
    |- _ ] => try (move:
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 _ _ _ _ Is_Parameter0_Unit True_Binary_Unit))
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 _ _ _ _ Is_Parameter0_Unit False_Binary_Unit))
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg2 _ _ _ _ Is_Parameter0_Unit True_Binary_Unit))
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg2 _ _ _ _ Is_Parameter0_Unit False_Binary_Unit)))
| [ gg1 : (forall (G : obGenerator) (paramlocal : ?Yoneda00_Param_SumSubstF G)
             (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
             (cons_paramlocal : constructors ?Param_SubstF paramlocal cons_is_Parameter0_P ),
             'CoMod__( _ ~> _ @_ _ ))
    |- _ ] => try (move:
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 _ _ _ _ Is_Parameter0_Unit True_Binary_Unit))
              (@gradeCoMod_ReParam_gt0 _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 _ _ _ _ Is_Parameter0_Unit False_Binary_Unit)))
end.

Ltac tac_induction_degrade degradeCoMod degradeCoMod_ReParam :=
  repeat match goal with
         | [ conv_ff : ( _ [ _ @^ _ ]<~~ _ )%poly  |- _ ] =>
           move: {conv_ff} (degradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ conv_ff)

         | [ conv_param_ff : ( _ [ _ ]<~~__ _ )%poly  |- _ ] =>
           move: {conv_param_ff} (degradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ conv_param_ff)
         end.

Ltac tac_induction_degrade_Data degradeCoMod degradeCoMod_ReParam :=
  repeat match goal with
         | [ conv_ee__ : (forall (G : obGenerator) (param : ?Yoneda00_Param_SubstF G)
                       (cons_paramlocal : constructors ?Param_SubstF (sval ?Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
                       (form : Yoneda00_AtParam_ ?Yoneda1_FormParam_F ?Yoneda1_Param_proj param)
                       (cons_form : constructors_Form ?F  form),
                          ( _ [ _ @^ _ ]<~~ _ )%poly )
             |- _ ] =>
           try move: (degradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                      (conv_ee__ GBinary (Parameter1 unitGenerator o>Parametrizator_ true_Binary GBinary)
                                        True_Binary_Unit
                                        (unitGenerator o>GeneratorAtParam_ true_Binary_Form GBinary)
                                        True_Binary_Form_Unit))
                        (degradeCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                      (conv_ee__ GBinary (Parameter1 unitGenerator o>Parametrizator_ false_Binary GBinary)
                                        False_Binary_Unit
                                        (unitGenerator o>GeneratorAtParam_ false_Binary_Form GBinary)
                                        False_Binary_Form_Unit));
           clear conv_ee__

         | [ conv_param_ee_ : (forall (G : obGenerator) (paramlocal : ?Yoneda00_Param_SumSubstF G)
                       (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
                       (cons_paramlocal : constructors ?Param_SubstF paramlocal cons_is_Parameter0_P ),
                          ( _ [ _ ]<~~__ _ )%poly )
             |- _ ] =>
           try move: (degradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                              (conv_param_ee_ GBinary (unitParametrizator o>Parametrizator_ true_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary) Is_Parameter0_Unit True_Binary_Unit))
                        (degradeCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                              (conv_param_ee_ GBinary (unitParametrizator o>Parametrizator_ false_Binary GBinary) (Parameter0 GBinary) (Is_Parameter0 GBinary) Is_Parameter0_Unit False_Binary_Unit));
           clear conv_param_ee_
         end.

Ltac tac_constructors_Data  :=
   match goal with
         | [ G : obGenerator,
             param : ?Yoneda00_Param_SubstF ?G ,
             cons_paramlocal : constructors ?Param_SubstF (sval ?Yoneda1_Param_subst ?G ?param) (Unit_is_Parameter0Default_Constructors ?G),
             form : Yoneda00_AtParam_ ?Yoneda1_FormParam_F ?Yoneda1_Param_proj ?param,
             cons_form : constructors_Form ?F  ?form
             |- _ ] =>
           try (destruct (constructors_Form_dataBinary_prop cons_form) as [? ? gg | ? ? gg] ;
           destruct (viewingDefault_Constructors_Form_codomBinary_prop gg) ;
           destruct (constructors_dataTrueFalse_prop cons_paramlocal))
         | [ G : obGenerator,
           paramlocal : ?Yoneda00_Param_SumSubstF ?G,
           P : obParametrizator,
           is_Parameter0_P : is_Parameter0 ?G ?P ,
           cons_is_Parameter0_P : is_Parameter0Default_Constructors ?is_Parameter0_P ,
           cons_paramlocal : constructors ?Param_SubstF ?paramlocal ?cons_is_Parameter0_P 
             |- _ ] =>
         try (destruct (constructors_dataBinary_prop cons_paramlocal) as [ ? ? ? ? ? pp | ? ? ? ? ? pp ] ;
         destruct (viewingDefault_Constructors_codomBinary_prop pp))
   end.

Ltac tac_degrade0 degradeCoMod degradeCoMod_ReParam  :=
   match goal with
         | [ Param_SubstF : obCoMod_Param_Data ?Yoneda1_Param_subst ,
             F : obCoMod_Data ?Yoneda1_FormParam_F ?Yoneda1_Param_proj ?Param_SubstF
             |- context [ PolyTransf_default ] ] =>
           destruct F;
           simpl gradeCoMod; simpl gradeCoMod_ReParam; intros;
           try tac_gradeCoMod_gt0; try tac_gradeCoMod_ReParam_gt0;
           try tac_gradeCoMod_gt0_Data; try tac_gradeCoMod_ReParam_gt0_Data;
           tac_induction_degrade degradeCoMod degradeCoMod_ReParam;
           tac_induction_degrade_Data degradeCoMod degradeCoMod_ReParam;
           try tac_constructors_Data
             
         | [ Param_SubstF : obCoMod_Param_Data ?Yoneda1_Param_subst
             |- context [ PolyTransf_ReParam_default ] ] =>
           destruct Param_SubstF;
           simpl gradeCoMod; simpl gradeCoMod_ReParam; intros;
           try tac_gradeCoMod_gt0; try tac_gradeCoMod_ReParam_gt0;
           try tac_gradeCoMod_gt0_Data; try tac_gradeCoMod_ReParam_gt0_Data;
           tac_induction_degrade degradeCoMod degradeCoMod_ReParam;
           tac_induction_degrade_Data degradeCoMod degradeCoMod_ReParam;
           try tac_constructors_Data
                                                          
         | [  |- _ ] => simpl gradeCoMod; simpl gradeCoMod_ReParam; intros;
                      try tac_gradeCoMod_gt0; try tac_gradeCoMod_ReParam_gt0;
                      tac_induction_degrade degradeCoMod degradeCoMod_ReParam
         end;
   simpl gradeCoMod; simpl gradeCoMod_ReParam;
   intros; abstract Lia.lia. 

Lemma degradeCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0)
   (Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E)
   Yoneda1_Param_subst_ff0 (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0)
   Yoneda1_Form_ff0 (Form_ff0 : pseudoCode Yoneda1_Form_ff0) (ff0 : 'CoMod( E ~> F @_ ReParam_EF0 @^ Form_ff0 )),
 forall Yoneda1_Param_reparam_EF (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF )),
 forall (Congr_congr_ff : Congr_data Yoneda1_Form_ff Yoneda1_Form_ff0 Yoneda1_Param_reparam_EF)
   (congr_ff : 'CoMod$ ( Form_ff ~> Form_ff0 @_ Congr_congr_ff )),
 forall convCoMod_ff0_ff : ff0 [  reparam_EF  @^ congr_ff ]<~~ ff ,
   ( gradeCoMod ff0 <= gradeCoMod ff )%nat 
with degradeCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),
 forall Yoneda00_Param_EF0 (Yoneda01_Param_EF0 : Yoneda01_Param_data Yoneda00_Param_EF0),
 forall Yoneda1_Param_proj_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff0 : Yoneda1_Param_data Yoneda01_Param_EF0 Yoneda01_Param_F,
 forall (ReParam_EF0 : pseudoCode_ReParam Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0),
 forall (param_ff0 : 'CoMod__( Param_E ~> Param_F @_  ReParam_EF0 )),
 forall Yoneda1_Param_reparam_EF (reparam_EF : 'CoMod_$( ReParam_EF ~> ReParam_EF0 @_ Yoneda1_Param_reparam_EF)),
 forall convCoMod_ReParam_param_ff0_param_ff : param_ff0  [  reparam_EF  ]<~~__ param_ff ,
   ( gradeCoMod_ReParam param_ff0 <= gradeCoMod_ReParam param_ff )%nat .
Proof.
(*  intros; exfalso; apply: myadmit2.
  intros; exfalso; apply: myadmit2.*)
  Time all : [> intros; case: Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 E Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF
   Yoneda1_Form_ff Form_ff ff Yoneda00_Param_EF0 Yoneda01_Param_EF0  Yoneda1_Param_proj_ff0
   Yoneda1_Param_subst_ff0 ReParam_EF0 Yoneda1_Form_ff0 Form_ff0 ff0  Yoneda1_Param_reparam_EF reparam_EF Congr_congr_ff congr_ff / convCoMod_ff0_ff
             | intros; case: Yoneda00_Param_E Yoneda01_Param_E Param_E Yoneda00_Param_F Yoneda01_Param_F Param_F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff  ReParam_EF param_ff Yoneda00_Param_EF0 Yoneda01_Param_EF0 Yoneda1_Param_proj_ff0 Yoneda1_Param_subst_ff0 ReParam_EF0 param_ff0  Yoneda1_Param_reparam_EF reparam_EF / convCoMod_ReParam_param_ff0_param_ff ];
    intros; try solve [ tac_degrade0 degradeCoMod degradeCoMod_ReParam ].
  (* Time: Finished transaction in 361.96 secs (361.935u,0.01s) (successful) *)
  (* Finished transaction in 3.491 secs (3.491u,0.s) (successful) *)
  (* Finished transaction in 21.574 secs (21.566u,0.007s) (successful) *)
  (* Finished transaction in 173.196 secs (172.912u,0.095s) (successful) *)
Qed.

Ltac tac_degrade := tac_degrade0 (@degradeCoMod) (@degradeCoMod_ReParam).

Module Sol.
Section Section1.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Inductive morCoMod : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
   (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
   (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   (Form_ff : pseudoCode Yoneda1_Form_ff ), Type :=

| UnitCoMod : forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
                (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
    'CoMod( F ~> F @_ UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F @^ UnitCoMod_pseudoCode Yoneda1_FormParam_F )

(**TODO: should viewingDefault_Constructors_Form  also carry a viewingDefault_Constructors code for (Parameter1 g) (Is_Parameter0 G) ? *)
| View1 : forall (G H : obGenerator) (g : 'Generator( G ~> H (** | H_Viewing ... only the viewing elements*)))
            (gg : viewingDefault_Constructors_Form g),
      'CoMod( View G ~> View H @_ (View1_pseudoCode_ReParam (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg))
                   @^ View1_pseudoCode gg )

| PolyElement_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
  (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
  (Yoneda00_Param_F : obGenerator -> Type)
  (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
  (Yoneda00_Param_SubstF : obGenerator -> Type)
  (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
  (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
  (Yoneda00_Param_SumSubstF : obGenerator -> Type)
  (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
  (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
  (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
  (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
  (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
  (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
  (cons_form : constructors_Form F  form),
  
  'CoMod( View G ~> ViewingFunctorSumSubst_default F
               @_ (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF) cons_paramlocal)
               @^ (AtMember_Form (PolyElement_default_pseudoCode F) cons_paramlocal cons_form))

| ViewedFunctor1_default :
forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E
  (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda10_FormParam_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F
  (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda10_FormParam_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall Yoneda10_Form_ff (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )),

forall Yoneda00_Param_EF' (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF'),
forall Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E,
forall Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F,
forall (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff'),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' )),

forall Yoneda1_Param_reparam_EF
  (reparam_EF : 'CoMod_$( ReParam_EF  ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF) ),

  'CoMod( ViewedFunctor_default E Param_E ~> ViewedFunctor_default F Param_F
                                @_ (ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF)
                                @^ ViewedFunctor1_default_pseudoCode ReParam_EF Form_ff )

| UnitViewedFunctor_default
  : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
      (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
      (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E)
      (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
      (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F)
      (Param_F : obCoMod_Param Yoneda01_Param_F)
      (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
      (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
      (Form_ff : pseudoCode Yoneda10_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )),

    'CoMod ( E ~> ViewedFunctor_default F Param_F
               @_ (PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) ReParam_EF)
               @^ (PolyCoMod_pseudoCode  (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) (UnitViewedFunctor_default_pseudoCode' _ ) ReParam_EF Form_ff) )

| PolyTransf_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ))

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),
  
  'CoMod( ViewingFunctorSumSubst_default F ~> ViewedFunctor_default E Param_E
      @_ (PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__) (PolyTransf_pseudoCode_ReParam_default' Param_SubstF  ReParam_ee_))
      @^ (PolyCoMod_pseudoCode (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__)
                               (ViewedFunctor1_default_pseudoCode ReParam_ee'__ Form_ee'__)
                               (PolyTransf_pseudoCode_ReParam_default' Param_SubstF  ReParam_ee_)
                               (PolyTransf_default_pseudoCode' F ReParam_ee_ Form_ee__)) )

| Forget :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
   (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
   (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E)
   (Yoneda00_Param_FE : obGenerator -> Type)
   (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)   
   (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
   (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_E)
   (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) Yoneda1_Form_ee
   (Form_ee : pseudoCode Yoneda1_Form_ee)
   (ee : 'CoMod( F ~> E @_  ReParam_FE @^ Form_ee )),
   
   'CoMod( PiSubst F Param_F Param_PiSubstF ReParam_SubstF ~> E
                   @_ (PolyCoMod_pseudoCode_ReParam ReParam_FE ReParam_SubstF)
                   @^ (PolyCoMod_pseudoCode ReParam_FE Form_ee ReParam_SubstF (Forget_pseudoCode _ ReParam_SubstF ) ) )

| Remember :
 forall (Yoneda00_Form_F : obGenerator -> Type)
   (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
   (Yoneda00_Param_F : obGenerator -> Type)
   (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
   (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
   (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
   
 forall (Yoneda00_Param_PiSubstF : obGenerator -> Type)
   (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
   (Param_PiSubstF : @obCoMod_Param Yoneda00_Param_PiSubstF Yoneda01_Param_PiSubstF),

 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
   (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)   
   (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
   (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
   (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),

 forall (Yoneda00_Param_SubstF' : obGenerator -> Type)
   (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')   
   (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
   (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
   (param_forget' : 'CoMod__( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' ) ),

 forall (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst
                                               Yoneda1_Param_proj' Yoneda1_Param_subst')
   (reparam_forget' : 'CoMod_$( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )),

 forall (Yoneda00_Form_L : obGenerator -> Type)
   (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
   (Yoneda00_Param_L : obGenerator -> Type)
   (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L)
   (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
   (L : @obCoMod Yoneda00_Form_L Yoneda01_Form_L Yoneda00_Param_L Yoneda01_Param_L Yoneda1_FormParam_L)
   (Yoneda00_Param_LF : obGenerator -> Type)
   (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
   (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F)
   (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
   (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (Form_ll : pseudoCode Yoneda1_Form_ll)
   (ll : 'CoMod( L ~> F @_ ReParam_LF @^ Form_ll )),

 forall (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
   (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF)
   (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
   (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L)
   (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst),
 forall (Yoneda00_Form_LF : obGenerator -> Type)
   (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF)
   (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
   (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
   (Form_ll' : pseudoCode Yoneda1_Form_ll')
   (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
   (Form_ll_ : pseudoCode Yoneda1_Form_ll_),

 forall (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                             (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
   (reparam_remember : 'CoMod_$( (PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF)
                                   ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ) ),
 forall (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
   (congr_ll : 'CoMod$( (PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_) ~> Form_ll @_ Congr_congr_ll ) ),

   'CoMod( L ~> PiSubst F Param_F Param_PiSubstF ReParam_SubstF
             @_ (PolyCoMod_pseudoCode_ReParam (UnitCoMod_pseudoCode_ReParam _) ReParam_LPiSubstF )
             @^ (PolyCoMod_pseudoCode (UnitCoMod_pseudoCode_ReParam _) (Remember_pseudoCode ReParam_SubstF Form_ll') ReParam_LPiSubstF Form_ll_ ) )

where "''CoMod' ( E ~> F @_ ReParam_EF @^ Form_ff )" :=
        (@morCoMod _ _ _ _ _ E _ _ _ _ _ F  _ _ _ _ ReParam_EF _ Form_ff) : sol_scope

with morCoMod_ReParam : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
   (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
   (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff), Type :=

| UnitCoMod_ReParam : forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
    'CoMod__( Param_F ~> Param_F @_ UnitCoMod_pseudoCode_ReParam Yoneda01_Param_F )

| View1_ReParam :
 forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator(  Parameter0 G ~> Q (** | Q_Viewing ... only the viewing elements*) )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (pp : viewingDefault_Constructors p cons_is_Parameter0_P),
      'CoMod__( View_Param P ~> View_Param Q @_ (View1_pseudoCode_ReParam pp) )

| PolyElement_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),
      
 forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
   (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
   (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),

    'CoMod__( View_Param P ~> ViewingFunctor_Param_default Param_SubstF
                   @_ (AtMember_ReParam (PolyElement_pseudoCode_ReParam_default Param_SubstF ) cons_paramlocal ))

| ViewedFunctor1_ReParam_default : forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
    forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
      (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

  'CoMod__( ViewedFunctor_Param_default Param_E ~> ViewedFunctor_Param_default Param_F  @_ ViewedFunctor1_pseudoCode_ReParam_default ReParam_EF )

| UnitViewedFunctor_ReParam_default :
forall Yoneda00_Param_E (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
  (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),

forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
  (param_ff : 'CoMod__( Param_E ~> Param_F  @_ ReParam_EF )),

  'CoMod__( Param_E ~> ViewedFunctor_Param_default Param_F  @_ (PolyCoMod_pseudoCode_ReParam (UnitViewedFunctor_pseudoCode_ReParam_default' _ ) ReParam_EF) )

| PolyTransf_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),
  
  'CoMod__( ViewingFunctor_Param_default Param_SubstF ~> ViewedFunctor_Param_default Param_E
      @_ (PolyCoMod_pseudoCode_ReParam (ViewedFunctor1_pseudoCode_ReParam_default ReParam_ee'__) (PolyTransf_pseudoCode_ReParam_default' Param_SubstF ReParam_ee_)) )

| Formatting : (**MEMO: contrast this to comprehension-categry / category-with-family / natural-model ,
 where the representability conditions relates type-theory style (terms are section morphism) as-corresponding-to
 locally-catesian-closed style (arrows are morphism over one object) ,
now here section morphism (from terminal) is generalized/polymorph as morphism from any shape object , 
and morphism over one object is generalized/polymorph as morphism parametrized over any span morphism *)
forall (Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
(Yoneda00_Form_F : obGenerator -> Type)
(Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
(Yoneda00_Param_F : obGenerator -> Type)
(Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
(Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
(F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)

(Yoneda00_Param_EF : obGenerator -> Type)
(Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
(Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
(Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
(ReParam_EF : pseudoCode_ReParam  Yoneda1_Param_proj Yoneda1_Param_subst)

(Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
(Form_ff : pseudoCode Yoneda1_Form_ff)
(ff : 'CoMod( E ~> F @_  ReParam_EF @^ Form_ff ))

(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
(Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)

(Yoneda00_Param_EF' : obGenerator -> Type)
(Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
(Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
(Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
(ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
(param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF' ))

(Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
(reparam_EF :  'CoMod_$( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF ))

(Yoneda00_Param_D : obGenerator -> Type)
(Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D)
(Param_D : obCoMod_Param Yoneda01_Param_D)
(Yoneda00_Param_DE : obGenerator -> Type)
(Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
(Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D)
(Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
(ReParam_DE : pseudoCode_ReParam  Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
(param_ee : 'CoMod__( Param_D ~> Param_E @_ ReParam_DE )),
  
  'CoMod__( Param_D ~> Format F Param_F @_ (PolyCoMod_pseudoCode_ReParam (Formatting_pseudoCode_ReParam' ReParam_EF Form_ff) ReParam_DE) )

where "''CoMod__' (  Param_E  ~>  Param_F  @_ ReParam_EF )" :=
        (@morCoMod_ReParam _ _ Param_E _ _ Param_F _ _ _ _ ReParam_EF ) : sol_scope .

End Section1.

Module Export Ex_Notations.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Notation "''CoMod' ( E ~> F @_ ReParam_EF @^ Form_ff )" :=
  (@morCoMod _ _ _ _ _ E _ _ _ _ _ F  _ _ _ _ ReParam_EF _ Form_ff) : sol_scope .
                                                                        
Notation "''CoMod__' (  Param_E  ~>  Param_F  @_ ReParam_EF )" :=
    (@morCoMod_ReParam _ _ Param_E _ _ Param_F _ _ _ _ ReParam_EF ) : sol_scope .

End Ex_Notations.

Fixpoint toPolyCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
         (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)
         Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
         (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F)
         Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
         (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
         (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
         (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
         (Form_ff : pseudoCode Yoneda1_Form_ff)
         (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )%sol) {struct ff} : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )%poly
with toPolyCoMod_ReParam Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)
                    Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F)
                    Yoneda00_Param_EF  (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
                    (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
                    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                    (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )%sol) {struct param_ff} : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )%poly .
Proof.
{ case : Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E E Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F F  Yoneda00_Param_EF Yoneda01_Param_EF  Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF Yoneda1_Form_ff Form_ff / ff. 
  - (** UnitCoMod *) intros.
    exact: (Senses_morCoMod.UnitCoMod _).
  - (** View1 *)  intros. 
    exact: (Senses_morCoMod.View1 _).
  - (** PolyElement_default *) intros.
    exact: (Senses_morCoMod.PolyElement_default _ _ ).
  - (** ViewedFunctor1_default *) intros.
    exact: (Senses_morCoMod.ViewedFunctor1_default (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff) (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff) reparam_EF) .
  - (**  UnitViewedFunctor_default *) intros.
    exact: (Senses_morCoMod.UnitViewedFunctor_default Param_F (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)) .
  - (** PolyTransf_default *) intros.
    exact (Senses_morCoMod.PolyTransf_default
             (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
             reparam_ee_
             (fun G param cons_paramlocal form cons_form =>
                (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee__ G param cons_paramlocal form cons_form)))
             reparam_ee__ congr_ee__ ).
  - (** Forget *) intros.
    exact: (Senses_morCoMod.Forget (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_forget') reparam_forget' (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee)) . 
  - (** Remember *) intros.
    exact: (Senses_morCoMod.Remember (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_forget') reparam_forget' (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ll) reparam_remember ) . }
{ case : Yoneda00_Param_E Yoneda01_Param_E Param_E Yoneda00_Param_F Yoneda01_Param_F Param_F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF / param_ff.
  - (** UnitCoMod_ReParam *) intros.
    exact: (Senses_morCoMod.UnitCoMod_ReParam _).
  - (** View1_ReParam *) intros.
    exact: (Senses_morCoMod.View1_ReParam _).
  - (** PolyElement_ReParam_default *) intros.
    exact: (Senses_morCoMod.PolyElement_ReParam_default _).
  - (** ViewedFunctor1_ReParam_default *) intros.
    exact: (Senses_morCoMod.ViewedFunctor1_ReParam_default (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff)).
  - (** UnitViewedFunctor_ReParam_default *) intros.
    exact: (Senses_morCoMod.UnitViewedFunctor_ReParam_default (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff)).
  - (** PolyTransf_ReParam_default *) intros.
    exact (Senses_morCoMod.PolyTransf_ReParam_default
             (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))) reparam_ee_).
  - (** Formatting *) intros.
    exact: (Senses_morCoMod.Formatting  (toPolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff) (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ff) reparam_EF
                                        (toPolyCoMod_ReParam _ _ _ _ _ _ _ _ _ _ _ param_ee)) . }
Defined.

Arguments toPolyCoMod : simpl nomatch.
Arguments toPolyCoMod_ReParam : simpl nomatch. 

(**TODO: TOOL , DON'T ERASE **)
Module TOOL.
Axiom morCoMod : forall T, forall t: T, Type.
Lemma morCoMod_codomP
  : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )%sol), morCoMod ff.
Proof. 
  intros. destruct F.
  admit.
  admit.
  admit.
  admit. Undo 5. 
  intros. destruct ff. 
  destruct F.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  destruct E.
  admit.
  admit.
  admit.
  admit.
  admit.
Abort All.
End TOOL.     
     
Module MorCoMod_codomView.
Inductive morCoMod : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (G : obGenerator) (Yoneda00_Param_EF : obGenerator -> Type)
           (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF (Yoneda01_Param_View (Parameter0 G))) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E (Yoneda1_FormParam_View G) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda1_Form_ff)
           (ff : 'CoMod ( E ~> View G @_ ReParam_EF @^ Form_ff )%sol), Type :=
| UnitCoMod:
    forall G : obGenerator, morCoMod (UnitCoMod (View G))
| View1:
    forall (G H : obGenerator) (g : 'Generator( G ~> H )) (gg : viewingDefault_Constructors_Form g), morCoMod (View1 gg)
| Forget:
       forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
              (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
              (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
              (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
              (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
              (Yoneda00_Param_SubstF' : obGenerator -> Type) (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')
              (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF) (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
              (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst') (param_forget' : 'CoMod__ ( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )%sol)
              (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
              (reparam_forget' : 'CoMod_$ ( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )) (G : obGenerator) (Yoneda00_Param_FE : obGenerator -> Type)
              (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE) (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F)
              (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE (Yoneda01_Param_View (Parameter0 G))) (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
              (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_F (Yoneda1_FormParam_View G) Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) (Form_ee : pseudoCode Yoneda1_Form_ee)
              (ff : 'CoMod ( F ~> View G @_ ReParam_FE @^ Form_ee )%sol), morCoMod (Forget param_forget' reparam_forget' ff)
.                                                                                   
End MorCoMod_codomView.

Module MorCoMod_codomViewingFunctorSumSubst_default.
Inductive morCoMod : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
           (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF (Yoneda01_Param_SumImage Yoneda1_Param_subst))
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E (Yoneda1_FormParam_SumSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod ( E ~> ViewingFunctorSumSubst_default F @_ ReParam_EF @^ Form_ff )%sol), Type :=
|  UnitCoMod:
      forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
           (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),
        morCoMod (UnitCoMod (ViewingFunctorSumSubst_default F))
| PolyElement_default:
forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
           (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF) (G : obGenerator) (param : Yoneda00_Param_SubstF G)
           (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) Is_Parameter0_Unit) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
           (cons_form : constructors_Form F form), morCoMod (PolyElement_default cons_paramlocal cons_form)
|  Forget:
forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
           (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
           (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
           (Yoneda00_Param_SubstF' : obGenerator -> Type) (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')
           (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF) (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
           (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst') (param_forget' : 'CoMod__ ( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )%sol)
           (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
           (reparam_forget' : 'CoMod_$ ( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )) (Yoneda00_Form_F0 : obGenerator -> Type) (Yoneda01_Form_F0 : Yoneda01_data Yoneda00_Form_F0)
           (Yoneda00_Param_F0 : obGenerator -> Type) (Yoneda01_Param_F0 : Yoneda01_Param_data Yoneda00_Param_F0) (Yoneda1_FormParam_F0 : Yoneda1_FormParam_data Yoneda01_Form_F0 Yoneda01_Param_F0)
           (Yoneda00_Param_SubstF0 : obGenerator -> Type) (Yoneda01_Param_SubstF0 : Yoneda01_Param_data Yoneda00_Param_SubstF0) (Yoneda1_Param_proj0 : Yoneda1_Param_data Yoneda01_Param_SubstF0 Yoneda01_Param_F0)
           (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda1_Param_subst0 : Yoneda1_Param_data Yoneda01_Param_SubstF0 Yoneda01_Param_SumSubstF) (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst0)
           (F0 : obCoMod_Data Yoneda1_FormParam_F0 Yoneda1_Param_proj0 Param_SubstF) (Yoneda00_Param_FE : obGenerator -> Type) (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)
           (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE (Yoneda01_Param_SumImage Yoneda1_Param_subst0))
           (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
           (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_F (Yoneda1_FormParam_SumSubst Yoneda1_FormParam_F0 Yoneda1_Param_subst0 Yoneda1_Param_proj0) Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
           (Form_ee : pseudoCode Yoneda1_Form_ee) (ff : 'CoMod ( F ~> ViewingFunctorSumSubst_default F0 @_ ReParam_FE @^ Form_ee )%sol), morCoMod (Forget param_forget' reparam_forget' ff)
.
End MorCoMod_codomViewingFunctorSumSubst_default.

Module MorCoMod_codomViewedFunctor_default.
Inductive morCoMod : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod ( E ~> ViewedFunctor_default F Param_F @_ ReParam_EF @^ Form_ff )%sol), Type :=
| UnitCoMod:
      forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F),
        morCoMod (UnitCoMod (ViewedFunctor_default F Param_F))
| ViewedFunctor1_default:
      forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
             (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type)
             (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type)
             (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
             (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
             (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda10_Form_ff)
             (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )%sol) (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF')
             (Yoneda1_Param_proj_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E) (Yoneda1_Param_subst_ff' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F)
             (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff') (param_ff : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EF' )%sol)
             (Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ff' Yoneda1_Param_subst_ff')
             (reparam_EF : 'CoMod_$ ( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF )), morCoMod (ViewedFunctor1_default ff param_ff reparam_EF)
| UnitViewedFunctor_default:
      forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
             (Yoneda10_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda10_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type)
             (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda10_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda10_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type)
             (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
             (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
             (Yoneda10_Form_ff : Yoneda1_Form_data Yoneda10_FormParam_E Yoneda10_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Form_ff : pseudoCode Yoneda10_Form_ff)
             (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )%sol), morCoMod (UnitViewedFunctor_default Param_F ff)

| PolyTransf_default :
forall (Yoneda00_Form_F : obGenerator -> Type) 
    (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type)
    (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
    (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst)
    (F : obCoMod_Data Yoneda1_FormParam_F Yoneda1_Param_proj Param_SubstF),

  forall (Yoneda00_Param_K : obGenerator -> Type)
(Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K)
(Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
    Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
(Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
(ReParam_ee_ : pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism)

(Yoneda00_Param_E : obGenerator -> Type)
(Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
(Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E)

(Yoneda00_Param_KE__ : obGenerator -> Type)
(Yoneda01_Param_KE__ : Yoneda01_Param_data Yoneda00_Param_KE__)
(Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_K)
(Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_KE__ Yoneda01_Param_E)
(ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)

(Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                       (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )%sol)

(Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__ (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__ (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))

(Yoneda00_Form_K : obGenerator -> Type)
(Yoneda01_Form_K : Yoneda01_data Yoneda00_Form_K)
(Yoneda1_FormParam_K : Yoneda1_FormParam_data Yoneda01_Form_K Yoneda01_Param_K)

(Yoneda1_Form_ee__ :
   forall (G : obGenerator) (param : Yoneda00_Param_SubstF G) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param),
     Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_K
                       (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                       (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
(Yoneda1_Form_ee_morphism : Morphism_Form_prop Yoneda1_Form_ee__)
(Form_ee__ : pseudoCode_Family Yoneda1_Form_ee_morphism)

(Yoneda00_Form_E : obGenerator -> Type)
(Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E)
(Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E)
(E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E)

(Yoneda1_Form_ee'__ : Yoneda1_Form_data Yoneda1_FormParam_K Yoneda1_FormParam_E Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__)
(Form_ee'__ : pseudoCode Yoneda1_Form_ee'__ )

(Yoneda00_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), obGenerator -> Type)
(Yoneda01_Param_SubstF0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ), Yoneda01_Param_data (Yoneda00_Param_SubstF0__ G param cons_paramlocal form cons_form))
(Yoneda1_Param_subst0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) (Yoneda01_Param_View (Parameter0 G)))
(Yoneda1_Param_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0__ G param cons_paramlocal form cons_form) Yoneda01_Param_E)
(ReParam_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    pseudoCode_ReParam (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form) )
(Yoneda1_Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Yoneda1_Form_data (Yoneda1_FormParam_View G) Yoneda1_FormParam_E
                      (Yoneda1_Param_subst0__  G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(Form_ee0__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
pseudoCode (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form))
(ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod( View G ~> E @_ (ReParam_ee0__ G param cons_paramlocal form cons_form) @^ (Form_ee0__ G param cons_paramlocal form cons_form))%sol),

forall (Yoneda1_Param_reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
      reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                               (Yoneda1_Local_proj Yoneda1_Param_subst (sval Yoneda1_Param_subst G param) (Is_Parameter0 G))
                                                               (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                                (Yoneda1_Param_ee_ G (sval Yoneda1_Param_subst G param)))
                    (Yoneda1_Param_subst0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_ee0__ G param cons_paramlocal form cons_form))
(reparam_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) ~> ReParam_ee0__ G param cons_paramlocal form cons_form @_ (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form)))
(Congr_congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    Congr_data (Yoneda1_Form_PolyCoMod (Yoneda1_Form_ee'__) (Yoneda1_Form_ee__ G param form)) (Yoneda1_Form_ee0__ G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_ee__ G param cons_paramlocal form cons_form))
(congr_ee__ : forall (G : obGenerator) (param : Yoneda00_Param_SubstF G)
          (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) (Unit_is_Parameter0Default_Constructors G))
          (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param)
          (cons_form : constructors_Form F  form ),
    'CoMod$( PolyCoMod_pseudoCode ReParam_ee'__ Form_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal) (AtMember_Form Form_ee__ cons_paramlocal cons_form) ~> (Form_ee0__ G param cons_paramlocal form cons_form) @_ Congr_congr_ee__ G param cons_paramlocal form cons_form ) ),
    morCoMod (PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__)

|  Forget:
       forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
              (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
              (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
              (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
              (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
              (Yoneda00_Param_SubstF' : obGenerator -> Type) (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')
              (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF) (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
              (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst') (param_forget' : 'CoMod__ ( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )%sol)
              (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
              (reparam_forget' : 'CoMod_$ ( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )) (Yoneda00_Form_F0 : obGenerator -> Type) (Yoneda01_Form_F0 : Yoneda01_data Yoneda00_Form_F0)
              (Yoneda00_Param_F0 : obGenerator -> Type) (Yoneda01_Param_F0 : Yoneda01_Param_data Yoneda00_Param_F0) (Yoneda1_FormParam_F0 : Yoneda1_FormParam_data Yoneda01_Form_F0 Yoneda01_Param_F0)
              (E : obCoMod Yoneda1_FormParam_F0) (Param_F0 : obCoMod_Param Yoneda01_Param_F0) (Yoneda00_Param_FE : obGenerator -> Type) (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)
              (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F0)
              (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_F Yoneda1_FormParam_F0 Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
              (Form_ee : pseudoCode Yoneda1_Form_ee) (ff : 'CoMod ( F ~> ViewedFunctor_default E Param_F0 @_ ReParam_FE @^ Form_ee )%sol), morCoMod (Forget param_forget' reparam_forget' ff)
.
End MorCoMod_codomViewedFunctor_default.

Module MorCoMod_codomPiSubst.
Inductive morCoMod : forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
                                             (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
                                             (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
                                             (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF)
                                             (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF) (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
                                             (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F) (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF)
                                             (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
                                             (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_PiSubstF)
                                             (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                                             (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E (Yoneda1_FormParam_PiSubst Yoneda1_FormParam_F Yoneda1_Param_subst Yoneda1_Param_proj) Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
                                             (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod ( E ~> PiSubst F Param_F Param_PiSubstF ReParam_SubstF @_ ReParam_EF @^ Form_ff )%sol), Type :=
|  UnitCoMod:
      forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
             (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
             (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
             (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
             (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst),
        morCoMod (UnitCoMod (PiSubst F Param_F Param_PiSubstF ReParam_SubstF))
|  Forget:
       forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
              (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
              (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
              (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
              (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
              (Yoneda00_Param_SubstF' : obGenerator -> Type) (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')
              (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF) (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
              (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst') (param_forget' : 'CoMod__ ( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )%sol)
              (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
              (reparam_forget' : 'CoMod_$ ( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )) (Yoneda00_Form_F0 : obGenerator -> Type) (Yoneda01_Form_F0 : Yoneda01_data Yoneda00_Form_F0)
              (Yoneda00_Param_F0 : obGenerator -> Type) (Yoneda01_Param_F0 : Yoneda01_Param_data Yoneda00_Param_F0) (Yoneda1_FormParam_F0 : Yoneda1_FormParam_data Yoneda01_Form_F0 Yoneda01_Param_F0)
              (E : obCoMod Yoneda1_FormParam_F0) (Param_F0 : obCoMod_Param Yoneda01_Param_F0) (Yoneda00_Param_PiSubstF0 : obGenerator -> Type) (Yoneda01_Param_PiSubstF0 : Yoneda01_Param_data Yoneda00_Param_PiSubstF0)
              (Param_PiSubstF0 : obCoMod_Param Yoneda01_Param_PiSubstF0) (Yoneda00_Param_SubstF0 : obGenerator -> Type) (Yoneda01_Param_SubstF0 : Yoneda01_Param_data Yoneda00_Param_SubstF0)
              (Yoneda1_Param_subst0 : Yoneda1_Param_data Yoneda01_Param_SubstF0 Yoneda01_Param_F0) (Yoneda1_Param_proj0 : Yoneda1_Param_data Yoneda01_Param_SubstF0 Yoneda01_Param_PiSubstF0)
              (ReParam_SubstF0 : pseudoCode_ReParam Yoneda1_Param_proj0 Yoneda1_Param_subst0) (Yoneda00_Param_FE : obGenerator -> Type) (Yoneda01_Param_FE : Yoneda01_Param_data Yoneda00_Param_FE)
              (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_F) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_FE Yoneda01_Param_PiSubstF0)
              (ReParam_FE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
              (Yoneda1_Form_ee : Yoneda1_Form_data Yoneda1_FormParam_F (Yoneda1_FormParam_PiSubst Yoneda1_FormParam_F0 Yoneda1_Param_subst0 Yoneda1_Param_proj0) Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee)
              (Form_ee : pseudoCode Yoneda1_Form_ee) (ff : 'CoMod ( F ~> PiSubst E Param_F0 Param_PiSubstF0 ReParam_SubstF0 @_ ReParam_FE @^ Form_ee )%sol), morCoMod (Forget param_forget' reparam_forget' ff)
                                                                                                                                                                      
| Remember :
 forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
        (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
        (Yoneda00_Param_PiSubstF : obGenerator -> Type) (Yoneda01_Param_PiSubstF : Yoneda01_Param_data Yoneda00_Param_PiSubstF) (Param_PiSubstF : obCoMod_Param Yoneda01_Param_PiSubstF)
        (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_F)
        (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_PiSubstF) (ReParam_SubstF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst)
        (Yoneda00_Param_SubstF' : obGenerator -> Type) (Yoneda01_Param_SubstF' : Yoneda01_Param_data Yoneda00_Param_SubstF')
        (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_PiSubstF) (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_SubstF' Yoneda01_Param_F)
        (ReParam_SubstF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst') (param_forget' : 'CoMod__ ( Param_PiSubstF ~> Param_F @_ ReParam_SubstF' )%sol)
        (Yoneda1_Param_reparam_forget' : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
        (reparam_forget' : 'CoMod_$ ( ReParam_SubstF ~> ReParam_SubstF' @_ Yoneda1_Param_reparam_forget' )) (Yoneda00_Form_L : obGenerator -> Type) (Yoneda01_Form_L : Yoneda01_data Yoneda00_Form_L)
        (Yoneda00_Param_L : obGenerator -> Type) (Yoneda01_Param_L : Yoneda01_Param_data Yoneda00_Param_L) (Yoneda1_FormParam_L : Yoneda1_FormParam_data Yoneda01_Form_L Yoneda01_Param_L)
        (L : obCoMod Yoneda1_FormParam_L) (Yoneda00_Param_LF : obGenerator -> Type) (Yoneda01_Param_LF : Yoneda01_Param_data Yoneda00_Param_LF)
        (Yoneda1_Param_subst_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_F) (Yoneda1_Param_proj_ll : Yoneda1_Param_data Yoneda01_Param_LF Yoneda01_Param_L)
        (ReParam_LF : pseudoCode_ReParam Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll) (Yoneda1_Form_ll : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_F Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
        (Form_ll : pseudoCode Yoneda1_Form_ll) (ff : 'CoMod ( L ~> F @_ ReParam_LF @^ Form_ll )%sol) (Yoneda00_Param_LPiSubstF : obGenerator -> Type)
        (Yoneda01_Param_LPiSubstF : Yoneda01_Param_data Yoneda00_Param_LPiSubstF) (Yoneda1_Param_LPiSubstF_subst : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_PiSubstF)
        (Yoneda1_Param_LPiSubstF_proj : Yoneda1_Param_data Yoneda01_Param_LPiSubstF Yoneda01_Param_L) (ReParam_LPiSubstF : pseudoCode_ReParam Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
        (Yoneda00_Form_LF : obGenerator -> Type) (Yoneda01_Form_LF : Yoneda01_data Yoneda00_Form_LF) (Yoneda1_FormParam_LF : Yoneda1_FormParam_data Yoneda01_Form_LF Yoneda01_Param_PiSubstF)
        (Yoneda1_Form_ll' : Yoneda1_Form_data Yoneda1_FormParam_LF Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst) (Form_ll' : pseudoCode Yoneda1_Form_ll')
        (Yoneda1_Form_ll_ : Yoneda1_Form_data Yoneda1_FormParam_L Yoneda1_FormParam_LF Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst) (Form_ll_ : pseudoCode Yoneda1_Form_ll_)
        (Yoneda1_Param_reparam_remember : reparamMorSym (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj Yoneda1_Param_LPiSubstF_proj Yoneda1_Param_LPiSubstF_subst)
                                                        (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_LPiSubstF_subst) Yoneda1_Param_proj_ll Yoneda1_Param_subst_ll)
        (reparam_remember : 'CoMod_$ ( PolyCoMod_pseudoCode_ReParam ReParam_SubstF ReParam_LPiSubstF ~> ReParam_LF @_ Yoneda1_Param_reparam_remember ))
        (Congr_congr_ll : Congr_data (Yoneda1_Form_PolyCoMod Yoneda1_Form_ll' Yoneda1_Form_ll_) Yoneda1_Form_ll Yoneda1_Param_reparam_remember)
        (congr_ll : 'CoMod$ ( PolyCoMod_pseudoCode ReParam_SubstF Form_ll' ReParam_LPiSubstF Form_ll_ ~> Form_ll @_ Congr_congr_ll )),
   morCoMod (Remember param_forget' reparam_forget' ff reparam_remember congr_ll)
.
End MorCoMod_codomPiSubst.

Lemma morCoMod_codomP
  : forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
 (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)      
   (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E),
 forall Yoneda1_Param_subst_ff (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
   Yoneda1_Form_ff (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )%sol),
   ltac:( destruct F; [ refine (MorCoMod_codomView.morCoMod ff)
                      | refine (MorCoMod_codomViewingFunctorSumSubst_default.morCoMod ff)
                      | refine (MorCoMod_codomViewedFunctor_default.morCoMod ff)
                      | refine (MorCoMod_codomPiSubst.morCoMod ff) ] ).
Proof. 
  intros. destruct ff.
  - destruct F.
    apply: MorCoMod_codomView.UnitCoMod.
    apply: MorCoMod_codomViewingFunctorSumSubst_default.UnitCoMod.
    apply: MorCoMod_codomViewedFunctor_default.UnitCoMod.
    apply: MorCoMod_codomPiSubst.UnitCoMod.
  - apply: MorCoMod_codomView.View1.
  - apply: MorCoMod_codomViewingFunctorSumSubst_default.PolyElement_default.
  - apply: MorCoMod_codomViewedFunctor_default.ViewedFunctor1_default.
  - apply: MorCoMod_codomViewedFunctor_default.UnitViewedFunctor_default.
  - apply: MorCoMod_codomViewedFunctor_default.PolyTransf_default.
  - destruct E.
    apply: MorCoMod_codomView.Forget.
    apply: MorCoMod_codomViewingFunctorSumSubst_default.Forget.
    apply: MorCoMod_codomViewedFunctor_default.Forget.
    apply: MorCoMod_codomPiSubst.Forget.
  - apply: MorCoMod_codomPiSubst.Remember.
Defined.

(**TODO: TOOLR , DON'T ERASE **)
Module TOOLR.
Axiom morCoMod_ReParam : forall T, forall t: T, Type.
Lemma morCoMod_ReParam_codomP
  : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )%sol), morCoMod_ReParam param_ff.
Proof. 
  intros. destruct Param_F.
  admit.
  admit.
  admit.
  admit. Undo 6.
  intros. destruct param_ff. 
  destruct Param_F.
  admit.
  admit.
  admit.
  admit.
    
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Abort All.
End TOOLR.
     
Module MorCoMod_codomView_Param.
Inductive morCoMod_ReParam : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (P : obParametrizator)
           (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF (Yoneda01_Param_View P)) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (param_ff : 'CoMod__ ( Param_E ~> View_Param P @_ ReParam_EF )%sol), Type :=
| UnitCoMod_ReParam:
  forall P : obParametrizator, morCoMod_ReParam (UnitCoMod_ReParam (View_Param P))
| View1_ReParam:
forall (Q : obParametrizator) (G : obGenerator) (p : 'Parametrizator ( Parameter0 G ~> Q )) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
           (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (pp : viewingDefault_Constructors p cons_is_Parameter0_P), morCoMod_ReParam (View1_ReParam pp).
        
End MorCoMod_codomView_Param.

Module MorCoMod_codomViewingFunctor_Param_default.
Inductive morCoMod_ReParam : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Param_SubstF : obGenerator -> Type)
           (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda00_Param_SumSubstF : obGenerator -> Type) (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
           (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF) (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst) (Yoneda00_Param_EF : obGenerator -> Type)
           (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF (Yoneda01_Param_SumImage Yoneda1_Param_subst)) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
           (param_ff : 'CoMod__ ( Param_E ~> ViewingFunctor_Param_default Param_SubstF @_ ReParam_EF )%sol), Type :=

| UnitCoMod_ReParam:
forall (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda00_Param_SumSubstF : obGenerator -> Type)
           (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
           (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst), morCoMod_ReParam (UnitCoMod_ReParam (ViewingFunctor_Param_default Param_SubstF))
| PolyElement_ReParam_default :
forall (Yoneda00_Param_SubstF : obGenerator -> Type) (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF) (Yoneda00_Param_SumSubstF : obGenerator -> Type)
           (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
           (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst) (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
           (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P),
  morCoMod_ReParam (PolyElement_ReParam_default cons_paramlocal)
.
End MorCoMod_codomViewingFunctor_Param_default.

Module MorCoMod_codomViewedFunctor_Param_default.
Inductive morCoMod_ReParam : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Param_F : obGenerator -> Type)
           (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (param_ff : 'CoMod__ ( Param_E ~> ViewedFunctor_Param_default Param_F @_ ReParam_EF )%sol), Type :=

| UnitCoMod_ReParam:
forall (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Param_F : obCoMod_Param Yoneda01_Param_F),
  morCoMod_ReParam (UnitCoMod_ReParam (ViewedFunctor_Param_default Param_F))

| ViewedFunctor1_ReParam_default:
forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Param_F : obGenerator -> Type)
           (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (param_ff : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EF )%sol), morCoMod_ReParam (ViewedFunctor1_ReParam_default param_ff)

| UnitViewedFunctor_ReParam_default :
forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Param_F : obGenerator -> Type)
           (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (param_ff : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EF )%sol),
      morCoMod_ReParam (UnitViewedFunctor_ReParam_default param_ff)

| PolyTransf_ReParam_default :
 forall (Yoneda00_Param_SubstF : obGenerator -> Type)
    (Yoneda01_Param_SubstF : Yoneda01_Param_data Yoneda00_Param_SubstF)
    (Yoneda00_Param_SumSubstF : obGenerator -> Type)
    (Yoneda01_Param_SumSubstF : Yoneda01_Param_data Yoneda00_Param_SumSubstF)
    (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_SubstF Yoneda01_Param_SumSubstF)
    (Param_SubstF : obCoMod_Param_Data Yoneda1_Param_subst),

forall (Yoneda00_Param_K : obGenerator -> Type)
  (Yoneda01_Param_K : Yoneda01_Param_data Yoneda00_Param_K),

forall (Yoneda1_Param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G),
      Yoneda1_Param_data (Yoneda01_Local_ Yoneda1_Param_subst paramlocal) Yoneda01_Param_K)
  (Yoneda1_Param_ee_morphism : Morphism_prop Yoneda1_Param_ee_)
  (ReParam_ee_ :  pseudoCode_ReParam_Family Yoneda1_Param_ee_morphism),

forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
  (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),

forall (Yoneda00_Param_ee'__ : obGenerator -> Type) (Yoneda01_Param_ee'__ : Yoneda01_Param_data Yoneda00_Param_ee'__)
  (Yoneda1_Param_proj_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_K) (Yoneda1_Param_subst_ee'__ : Yoneda1_Param_data Yoneda01_Param_ee'__ Yoneda01_Param_E)
  (ReParam_ee'__ : pseudoCode_ReParam Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__),
  
forall (Yoneda00_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), obGenerator -> Type)
(Yoneda01_Param_SubstF0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ), Yoneda01_Param_data (Yoneda00_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))
(Yoneda1_Param_subst0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda01_Param_View P))
(Yoneda1_Param_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    Yoneda1_Param_data (Yoneda01_Param_SubstF0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) Yoneda01_Param_E)
(ReParam_ee0_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    pseudoCode_ReParam (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                    (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(param_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)               
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod__( View_Param P ~> Param_E @_ ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal )%sol),

forall (Yoneda1_Param_reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    reparamMorSym
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_proj Yoneda1_Param_proj_ee'__
                                                 (Yoneda1_Local_proj Yoneda1_Param_subst paramlocal is_Parameter0_P) (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_PolyCoMod_pseudoCode_ReParam_subst Yoneda1_Param_proj_ee'__ Yoneda1_Param_subst_ee'__
                                                  (Yoneda1_Param_ee_ G paramlocal))
      (Yoneda1_Param_subst0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
(reparam_ee_ : forall (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G)
               (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P)
               (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P ),
    'CoMod_$( PolyCoMod_pseudoCode_ReParam ReParam_ee'__ (AtMember_ReParam ReParam_ee_ cons_paramlocal)
                          ~> ReParam_ee0_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal @_ (Yoneda1_Param_reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))),
 morCoMod_ReParam (PolyTransf_ReParam_default param_ee_ reparam_ee_)
.
End MorCoMod_codomViewedFunctor_Param_default.

Module MorCoMod_codomFormat.
Inductive morCoMod_ReParam : forall (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E) (Yoneda00_Form_F : obGenerator -> Type)
           (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F) (Yoneda00_Param_EF : obGenerator -> Type)
           (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
           (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF (Yoneda01_Param_Format (Yoneda1_Param_of_Yoneda1_FormParam Yoneda1_FormParam_F) (Yoneda1_Param_Id Yoneda01_Param_F)))
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (param_ff : 'CoMod__ ( Param_E ~> Format F Param_F @_ ReParam_EF )%sol), Type :=

| UnitCoMod_ReParam:
forall (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F) (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F)
           (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F) (F : obCoMod Yoneda1_FormParam_F) (Param_F : obCoMod_Param Yoneda01_Param_F),
  morCoMod_ReParam (UnitCoMod_ReParam (Format F Param_F))

| Formatting :
forall (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
           (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
           (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
           (F : obCoMod Yoneda1_FormParam_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
           (Yoneda1_Param_proj : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
           (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj Yoneda1_Param_subst) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj Yoneda1_Param_subst)
           (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )%sol) (Param_E : obCoMod_Param Yoneda01_Param_E) (Param_F : obCoMod_Param Yoneda01_Param_F)
           (Yoneda00_Param_EF' : obGenerator -> Type) (Yoneda01_Param_EF' : Yoneda01_Param_data Yoneda00_Param_EF') (Yoneda1_Param_proj' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_E)
           (Yoneda1_Param_subst' : Yoneda1_Param_data Yoneda01_Param_EF' Yoneda01_Param_F) (ReParam_EF' : pseudoCode_ReParam Yoneda1_Param_proj' Yoneda1_Param_subst')
           (param_ff1 : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EF' )%sol) (Yoneda00_Param_D : obGenerator -> Type)
           (Yoneda1_Param_reparam_EF : reparamMorSym Yoneda1_Param_proj Yoneda1_Param_subst Yoneda1_Param_proj' Yoneda1_Param_subst')
           (reparam_EF : 'CoMod_$ ( ReParam_EF ~> ReParam_EF' @_ Yoneda1_Param_reparam_EF ))
           (Yoneda01_Param_D : Yoneda01_Param_data Yoneda00_Param_D) (Param_D : obCoMod_Param Yoneda01_Param_D) (Yoneda00_Param_DE : obGenerator -> Type) (Yoneda01_Param_DE : Yoneda01_Param_data Yoneda00_Param_DE)
           (Yoneda1_Param_proj_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_D) (Yoneda1_Param_subst_ee : Yoneda1_Param_data Yoneda01_Param_DE Yoneda01_Param_E)
           (ReParam_DE : pseudoCode_ReParam Yoneda1_Param_proj_ee Yoneda1_Param_subst_ee) (param_ff2 : 'CoMod__ ( Param_D ~> Param_E @_ ReParam_DE )%sol),
      morCoMod_ReParam (Formatting ff param_ff1 reparam_EF param_ff2)
.
End MorCoMod_codomFormat.

Lemma morCoMod_ReParam_codomP
  : forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
 forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
 forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF),
 forall Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E,
 forall Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F,
 forall (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
 forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )%sol),
   ltac:( destruct Param_F; [ refine (MorCoMod_codomView_Param.morCoMod_ReParam param_ff)
                      | refine (MorCoMod_codomViewingFunctor_Param_default.morCoMod_ReParam param_ff)
                      | refine (MorCoMod_codomViewedFunctor_Param_default.morCoMod_ReParam param_ff)
                      | refine (MorCoMod_codomFormat.morCoMod_ReParam param_ff) ] ).
Proof. 
  intros. destruct param_ff.
  - destruct Param_F.
    apply: MorCoMod_codomView_Param.UnitCoMod_ReParam.
    apply: MorCoMod_codomViewingFunctor_Param_default.UnitCoMod_ReParam.
    apply: MorCoMod_codomViewedFunctor_Param_default.UnitCoMod_ReParam.
    apply: MorCoMod_codomFormat.UnitCoMod_ReParam.
  - apply: MorCoMod_codomView_Param.View1_ReParam.
  - apply: MorCoMod_codomViewingFunctor_Param_default.PolyElement_ReParam_default.
  - apply: MorCoMod_codomViewedFunctor_Param_default.ViewedFunctor1_ReParam_default.
  - apply: MorCoMod_codomViewedFunctor_Param_default.UnitViewedFunctor_ReParam_default.
  - apply: MorCoMod_codomViewedFunctor_Param_default.PolyTransf_ReParam_default.
  - apply: MorCoMod_codomFormat.Formatting.
Defined.
End Sol.

Module Resolve.
Export Sol.Ex_Notations.

Ltac tac_simpl := simpl.
Ltac tac_reduce := tac_simpl; repeat (intro; tac_simpl); intuition eauto 9.

Module SR.
Section solveCoMod_return.
  Variables (Yoneda00_Form_E : obGenerator -> Type) (Yoneda01_Form_E : Yoneda01_data Yoneda00_Form_E) (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E)
    (Yoneda1_FormParam_E : Yoneda1_FormParam_data Yoneda01_Form_E Yoneda01_Param_E) (E : obCoMod Yoneda1_FormParam_E) (Yoneda00_Form_F : obGenerator -> Type) (Yoneda01_Form_F : Yoneda01_data Yoneda00_Form_F)
    (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Yoneda1_FormParam_F : Yoneda1_FormParam_data Yoneda01_Form_F Yoneda01_Param_F)
    (F : obCoMod Yoneda1_FormParam_F) (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
    (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E) (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
    (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff) (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
    (Form_ff : pseudoCode Yoneda1_Form_ff) (ff : 'CoMod ( E ~> F @_ ReParam_EF @^ Form_ff )).

(**MEMO; use Record , else cost of nested projections : 1 projT2 = 0.1 sec , 2 projT2 = 2 sec , 3 projT2 56sec , where 12 projT2 required *)  
Record solveCoMod_return : Type := 
  {Yoneda00_Param_EFSol : obGenerator -> Type ;
  Yoneda01_Param_EFSol : Yoneda01_Param_data Yoneda00_Param_EFSol ;
  Yoneda1_Param_proj_ffSol : Yoneda1_Param_data Yoneda01_Param_EFSol Yoneda01_Param_E ;
  Yoneda1_Param_subst_ffSol : Yoneda1_Param_data Yoneda01_Param_EFSol Yoneda01_Param_F ;
  ReParam_EFSol : pseudoCode_ReParam Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ;
  Yoneda1_Form_ffSol : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ;
  Form_ffSol : pseudoCode Yoneda1_Form_ffSol ;
  ffSol : 'CoMod ( E ~> F @_ ReParam_EFSol @^ Form_ffSol )%sol ;
  Yoneda1_Param_reparam_EFSol : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ;
  reparam_EFSol : 'CoMod_$ ( ReParam_EF ~> ReParam_EFSol @_ Yoneda1_Param_reparam_EFSol ) ;
  Congr_congr_ffSol : Congr_data Yoneda1_Form_ff Yoneda1_Form_ffSol Yoneda1_Param_reparam_EFSol ;
  congr_ffSol : 'CoMod$ ( Form_ff ~> Form_ffSol @_ Congr_congr_ffSol ) ;
  conv_ffSol : (Sol.toPolyCoMod ffSol) [ reparam_EFSol @^ congr_ffSol ]<~~ ff } .

End solveCoMod_return.
End SR.

Module SRR.
Section solveCoMod_ReParam_return.
  Variables (Yoneda00_Param_E : obGenerator -> Type) (Yoneda01_Param_E : Yoneda01_Param_data Yoneda00_Param_E) (Param_E : obCoMod_Param Yoneda01_Param_E)
            (Yoneda00_Param_F : obGenerator -> Type) (Yoneda01_Param_F : Yoneda01_Param_data Yoneda00_Param_F) (Param_F : obCoMod_Param Yoneda01_Param_F)
            (Yoneda00_Param_EF : obGenerator -> Type) (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF) (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
            (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F) (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
            (param_ff : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EF )).

  Record solveCoMod_ReParam_return : Type :=
    {Yoneda00_Param_EFSol : obGenerator -> Type ;
     Yoneda01_Param_EFSol : Yoneda01_Param_data Yoneda00_Param_EFSol ;
     Yoneda1_Param_proj_ffSol : Yoneda1_Param_data Yoneda01_Param_EFSol Yoneda01_Param_E ;
     Yoneda1_Param_subst_ffSol : Yoneda1_Param_data Yoneda01_Param_EFSol Yoneda01_Param_F ;
     ReParam_EFSol : pseudoCode_ReParam Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ;
     param_ffSol : 'CoMod__ ( Param_E ~> Param_F @_ ReParam_EFSol )%sol ;
     Yoneda1_Param_reparam_EFSol : reparamMorSym Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ;
     reparam_EFSol : 'CoMod_$ ( ReParam_EF ~> ReParam_EFSol @_ Yoneda1_Param_reparam_EFSol ) ;
     conv_param_ffSol : (Sol.toPolyCoMod_ReParam param_ffSol) [ reparam_EFSol ]<~~__ param_ff }.

End solveCoMod_ReParam_return.
End SRR.

Ltac tac_SR solveCoMod len ff blurb :=
  move: (SR.Yoneda00_Param_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Yoneda01_Param_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Yoneda1_Param_proj_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Yoneda1_Param_subst_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.ReParam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Yoneda1_Form_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Form_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Yoneda1_Param_reparam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.reparam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.Congr_congr_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))
          (SR.congr_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb)).

Ltac tac_SRR solveCoMod_ReParam len param_ff blurbp :=
  move: (SRR.Yoneda00_Param_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.Yoneda01_Param_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.Yoneda1_Param_proj_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.Yoneda1_Param_subst_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.ReParam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.Yoneda1_Param_reparam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp))
          (SRR.reparam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp)).

  Ltac tac_SR_Family solveCoMod len ff__ blurb_ :=
  have @Yoneda00_Param_EF_ffSol := (fun G param cons_paramlocal form cons_form => (SR.Yoneda00_Param_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Yoneda01_Param_EF_ffSol : forall G param cons_paramlocal form cons_form, Yoneda01_Param_data (Yoneda00_Param_EF_ffSol G param cons_paramlocal form cons_form) :=
    (fun G param cons_paramlocal form cons_form => (SR.Yoneda01_Param_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Yoneda1_Param_proj_ffSol : forall G param cons_paramlocal form cons_form, Yoneda1_Param_data (Yoneda01_Param_EF_ffSol G param cons_paramlocal form cons_form) _
    := (fun G param cons_paramlocal form cons_form => (SR.Yoneda1_Param_proj_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Yoneda1_Param_subst_ffSol : forall G param cons_paramlocal form cons_form, Yoneda1_Param_data (Yoneda01_Param_EF_ffSol G param cons_paramlocal form cons_form) _
    := (fun G param cons_paramlocal form cons_form => (SR.Yoneda1_Param_subst_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @ReParam_EF_ffSol : forall G param cons_paramlocal form cons_form, pseudoCode_ReParam (Yoneda1_Param_proj_ffSol G param cons_paramlocal form cons_form) (Yoneda1_Param_subst_ffSol G param cons_paramlocal form cons_form) 
    := (fun G param cons_paramlocal form cons_form => (SR.ReParam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Yoneda1_Form_ffSol : forall G param cons_paramlocal form cons_form, Yoneda1_Form_data _ _ (Yoneda1_Param_proj_ffSol G param cons_paramlocal form cons_form) (Yoneda1_Param_subst_ffSol G param cons_paramlocal form cons_form)
    := (fun G param cons_paramlocal form cons_form => (SR.Yoneda1_Form_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Form_ffSol : forall G param cons_paramlocal form cons_form, pseudoCode (Yoneda1_Form_ffSol G param cons_paramlocal form cons_form)
    := (fun G param cons_paramlocal form cons_form => (SR.Form_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @ffSol : forall G param cons_paramlocal form cons_form, 'CoMod ( _ ~> _ @_ (ReParam_EF_ffSol G param cons_paramlocal form cons_form) @^ (Form_ffSol G param cons_paramlocal form cons_form) )%sol
    := (fun G param cons_paramlocal form cons_form => (SR.ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Yoneda1_Param_reparam_EF_ffSol : forall G param cons_paramlocal form cons_form, reparamMorSym _ _ (Yoneda1_Param_proj_ffSol G param cons_paramlocal form cons_form) (Yoneda1_Param_subst_ffSol G param cons_paramlocal form cons_form)
    := (fun G param cons_paramlocal form cons_form => (SR.Yoneda1_Param_reparam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @reparam_EF_ffSol : forall G param cons_paramlocal form cons_form, 'CoMod_$ ( _ ~> (ReParam_EF_ffSol G param cons_paramlocal form cons_form) @_ (Yoneda1_Param_reparam_EF_ffSol G param cons_paramlocal form cons_form) )
    := (fun G param cons_paramlocal form cons_form => (SR.reparam_EFSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @Congr_congr_ffSol : forall G param cons_paramlocal form cons_form, Congr_data _ (Yoneda1_Form_ffSol G param cons_paramlocal form cons_form) (Yoneda1_Param_reparam_EF_ffSol G param cons_paramlocal form cons_form)
    := (fun G param cons_paramlocal form cons_form => (SR.Congr_congr_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  have @congr_ffSol : forall G param cons_paramlocal form cons_form, 'CoMod$ ( _ ~> (Form_ffSol G param cons_paramlocal form cons_form) @_ (Congr_congr_ffSol G param cons_paramlocal form cons_form) )
    := (fun G param cons_paramlocal form cons_form => (SR.congr_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff__ G param cons_paramlocal form cons_form) (blurb_ G param cons_paramlocal form cons_form))));
  intros conv_ffSol;
  have {conv_ffSol} : forall G param cons_paramlocal form cons_form, (Sol.toPolyCoMod (ffSol G param cons_paramlocal form cons_form)) [ (reparam_EF_ffSol G param cons_paramlocal form cons_form) @^ (congr_ffSol G param cons_paramlocal form cons_form) ]<~~ _
    := conv_ffSol.

  Ltac tac_SRR_Family solveCoMod_ReParam len param_ff_ blurbp_ :=
  have @Yoneda00_Param_EF_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, obGenerator -> Type
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.Yoneda00_Param_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @Yoneda01_Param_EF_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, Yoneda01_Param_data (Yoneda00_Param_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.Yoneda01_Param_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @Yoneda1_Param_proj_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, Yoneda1_Param_data (Yoneda01_Param_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) _
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.Yoneda1_Param_proj_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @Yoneda1_Param_subst_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, Yoneda1_Param_data (Yoneda01_Param_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) _
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.Yoneda1_Param_subst_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @ReParam_EF_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, pseudoCode_ReParam (Yoneda1_Param_proj_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_subst_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.ReParam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, 'CoMod__ ( _ ~> _ @_ (ReParam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )%sol
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @Yoneda1_Param_reparam_EF_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, reparamMorSym  _ _ (Yoneda1_Param_proj_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (Yoneda1_Param_subst_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.Yoneda1_Param_reparam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  have @reparam_EF_param_ffSol  : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, 'CoMod_$ ( _ ~> (ReParam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) @_ (Yoneda1_Param_reparam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) )
    := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal => (SRR.reparam_EFSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ (param_ff_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
  intros conv_param_ffSol;
  have {conv_param_ffSol} : forall G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal, (Sol.toPolyCoMod_ReParam (param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)) [ (reparam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) ]<~~__ _
    := conv_param_ffSol.

Fixpoint solveCoMod (len : nat) {struct len} :
 forall Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E
   (E : @obCoMod Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E),
 forall Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F
   (F : @obCoMod Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F),
    forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
      (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
      (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
      (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
    forall (Yoneda1_Form_ff : Yoneda1_Form_data Yoneda1_FormParam_E Yoneda1_FormParam_F Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff)
       (Form_ff : pseudoCode Yoneda1_Form_ff)
      (ff : 'CoMod( E ~> F @_ ReParam_EF @^ Form_ff )), 
    forall grade_ff : ( gradeCoMod ff  <= len)%nat,
      SR.solveCoMod_return ff

with solveCoMod_ReParam (len : nat) {struct len} :
forall Yoneda00_Param_E Yoneda01_Param_E (Param_E : @obCoMod_Param Yoneda00_Param_E Yoneda01_Param_E),
forall Yoneda00_Param_F Yoneda01_Param_F (Param_F : @obCoMod_Param Yoneda00_Param_F Yoneda01_Param_F),
forall Yoneda00_Param_EF (Yoneda01_Param_EF : Yoneda01_Param_data Yoneda00_Param_EF)
  (Yoneda1_Param_proj_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_E)
  (Yoneda1_Param_subst_ff : Yoneda1_Param_data Yoneda01_Param_EF Yoneda01_Param_F)
  (ReParam_EF : pseudoCode_ReParam Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff),
forall (param_ff : 'CoMod__( Param_E ~> Param_F @_ ReParam_EF )),
forall grade_ff : ( gradeCoMod_ReParam param_ff <= len)%nat,
      SRR.solveCoMod_ReParam_return param_ff .
Proof.
{ (** solveCoMod *) case : len => [ | len ].

(** len is O **)
- intros; exfalso;
    by intros; move: grade_ff; clear; abstract tac_degrade.

(** len is (S len) **)
- intros until ff. case : Yoneda00_Form_E Yoneda01_Form_E Yoneda00_Param_E Yoneda01_Param_E Yoneda1_FormParam_E E Yoneda00_Form_F Yoneda01_Form_F Yoneda00_Param_F Yoneda01_Param_F Yoneda1_FormParam_F F  Yoneda00_Param_EF Yoneda01_Param_EF  Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF Yoneda1_Form_ff Form_ff / ff; intros. 

(** ff is  (ff o>CoMod ff') *) all: cycle 1.
   
(** ff is  (UnitMod F) **)
+ eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.UnitCoMod F )%sol).
  clear; tac_reduce.

(** ff is  (View1 gg)  **)
+ eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.View1 gg )%sol).
  clear; tac_reduce.

(** ff is  (PolyElement_default cons_paramlocal cons_form) **)
+ eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.PolyElement_default cons_paramlocal cons_form )%sol).
  clear; tac_reduce.

(** ff is  (ViewedFunctor1_default ff param_ff reparam_EF) **)
+ have [:blurb] := (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb));
                     first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ff blurb; move =>
  Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol
                          Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol conv_ffSol .
  have [:blurbp]:= (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp));
                     first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff blurbp; move  =>
  Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol .
  clear solveCoMod solveCoMod_ReParam.

  eapply SR.Build_solveCoMod_return with (ffSol :=
  (Sol.ViewedFunctor1_default ffSol param_ffSol ((Sym_reparam reparam_EF_ffSol) o>_$ (reparam_EF o>_$ reparam_EF_param_ffSol)))%sol).

  move: conv_param_ffSol conv_ffSol; clear; tac_reduce.

(** ff is  (UnitViewedFunctor_default Param_F ff) **)
+ have [:blurb] := (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb));
                     first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ff blurb; move =>
  Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol
                          Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol conv_ffSol .
  clear solveCoMod solveCoMod_ReParam.

  eapply SR.Build_solveCoMod_return with (ffSol :=
  (Sol.UnitViewedFunctor_default Param_F ffSol)%sol).

  move: conv_ffSol; clear; tac_reduce.

(** ff is  (PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__) **)
+ Time have [:blurb_] := (fun G param cons_paramlocal form cons_form =>
         (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                    (ee__ G param cons_paramlocal form cons_form)
                                    (blurb_ G param cons_paramlocal form cons_form))));
                           first by intros; move: grade_ff; clear; abstract tac_degrade. (* 16 secs *)
  tac_SR_Family solveCoMod len ee__ blurb_ ;
    move : Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol
                                   Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol;
    move => Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol
                                   Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol conv_ffSol.

  Time have [:blurbp_] := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
         (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _
                                                   (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                                                   (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
                            first by intros; move: grade_ff; clear; abstract tac_degrade. (* 15 secs *)
  tac_SRR_Family solveCoMod_ReParam len param_ee_ blurbp_ ;
    move: Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                        ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol;
    move => Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                         ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol.
  clear solveCoMod solveCoMod_ReParam.

  pose reparam_eeeeSol9_ := (fun (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
                         (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P) =>
                               Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
  pose reparam_eeeeSol9__ := (fun (G : obGenerator) (param : Yoneda00_Param_SubstF G) (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) Is_Parameter0_Unit) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (cons_form : constructors_Form F form) =>
                                Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
  pose congr_eeeeSol9__ := (fun (G : obGenerator) (param : Yoneda00_Param_SubstF G) (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) Is_Parameter0_Unit) (form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (cons_form : constructors_Form F form) =>
                              Refl_congrPseudoCode (AtMember_Form Form_ee__ cons_paramlocal cons_form)).
  pose reparam_ee'eeSol'__ := (Refl_reparam (ReParam_ee'__)).
  pose congr_ee'eeSol'__ := (Refl_congrPseudoCode (Form_ee'__)).

  (** HAHA /!\ AMBUSH /!\ ALSO FOR THE SENSE, THE FAMILY MUST BE INDEXED BY CODES ---> SOLVED ! *)
  pose reparam_eeSol_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                            ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'eeSol'__ (reparam_eeeeSol9_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
                               o>_$ ((reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))).
  pose reparam_eeSol__ := (fun G param cons_paramlocal form cons_form => ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'eeSol'__  (reparam_eeeeSol9__ G param cons_paramlocal form cons_form)))
                                                o>_$ ((reparam_ee__ G param cons_paramlocal form cons_form) o>_$ (reparam_EF_ffSol G param cons_paramlocal form cons_form)))).
  pose congr_eeSol__ := (fun G param cons_paramlocal form cons_form => (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode reparam_ee'eeSol'__ congr_ee'eeSol'__ (reparam_eeeeSol9__ G param cons_paramlocal form cons_form) (congr_eeeeSol9__ G param cons_paramlocal form cons_form)))
                                             o>$ ((congr_ee__ G param cons_paramlocal form cons_form) o>$ (congr_ffSol G param cons_paramlocal form cons_form))).

  (** HAHA /!\ AMBUSH2 /!\ ONLY FOR THE (0-LABELLED) SENSES SUPPORTING THE MORPHISMS , THE FAMILY MUST BE INDEXED BY CODES ---> SOLVED ! *)
  eapply SR.Build_solveCoMod_return with (ffSol :=
        ( Sol.PolyTransf_default param_ffSol reparam_eeSol_
                                 ffSol reparam_eeSol__ congr_eeSol__ )%sol).

  (** -TODO: codes for all the morphisms-families (Param_morphism , Form_morphism , reparamMorSym_morphism) , add coherence of those codes in [PolyTransf_cong] with reflexivity hints , and add codes for the extensionality [PolyTransf(PolyElement)]
-TODO: rename _morphism to _family ? *) 
  move: conv_param_ffSol conv_ffSol; clear; intros; (*MEMO: no simpl *)
    eapply PolyTransf_default_cong'''; intuition (try apply Refl_coh_congrPseudoCode_ReParam; try apply Refl_coh_congrPseudoCode; eauto).

(** ff is (Forget param_forget' reparam_forget' ee) **)
+ have [:blurb] :=
    (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee blurb));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ee blurb; move =>
  Yoneda00_Param_EF_eeSol Yoneda01_Param_EF_eeSol Yoneda1_Param_proj_eeSol Yoneda1_Param_subst_eeSol ReParam_EF_eeSol Yoneda1_Form_eeSol
                          Form_eeSol eeSol Yoneda1_Param_reparam_EF_eeSol reparam_EF_eeSol Congr_congr_eeSol congr_eeSol conv_eeSol.
  have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_forget' blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_forget' blurbp; move  =>
  Yoneda00_Param_EF_param_forget'Sol Yoneda01_Param_EF_param_forget'Sol Yoneda1_Param_proj_param_forget'Sol Yoneda1_Param_subst_param_forget'Sol ReParam_EF_param_forget'Sol param_forget'Sol Yoneda1_Param_reparam_EF_param_forget'Sol reparam_EF_param_forget'Sol conv_param_forget'Sol.
  clear solveCoMod solveCoMod_ReParam.

  eapply SR.Build_solveCoMod_return with (ffSol :=
    (Sol.Forget param_forget'Sol (reparam_forget' o>_$ reparam_EF_param_forget'Sol) eeSol)%sol).

  move: conv_param_forget'Sol conv_eeSol; clear; tac_reduce.

(** ff is  (Remember param_forget' reparam_forget' ll reparam_remember congr_ll)  **)  
+ have [:blurb] :=
    (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ll blurb));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ll blurb; move =>
  Yoneda00_Param_EF_llSol Yoneda01_Param_EF_llSol Yoneda1_Param_proj_llSol Yoneda1_Param_subst_llSol ReParam_EF_llSol Yoneda1_Form_llSol Form_llSol llSol Yoneda1_Param_reparam_EF_llSol reparam_EF_llSol Congr_congr_llSol congr_llSol conv_llSol.
  have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_forget' blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_forget' blurbp; move =>
  Yoneda00_Param_EF_param_forget'Sol Yoneda01_Param_EF_param_forget'Sol Yoneda1_Param_proj_param_forget'Sol Yoneda1_Param_subst_param_forget'Sol ReParam_EF_param_forget'Sol param_forget'Sol Yoneda1_Param_reparam_EF_param_forget'Sol reparam_EF_param_forget'Sol conv_param_forget'Sol.
  clear solveCoMod solveCoMod_ReParam.

  eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.Remember param_forget'Sol
            ( reparam_forget' o>_$ reparam_EF_param_forget'Sol ) llSol
            ( (Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) (Refl_reparam ReParam_LPiSubstF)))
                o>_$ (reparam_remember o>_$ reparam_EF_llSol) )
            ( (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode (Refl_reparam _) (Refl_congrPseudoCode Form_ll')
                                                                   (Refl_reparam ReParam_LPiSubstF) (Refl_congrPseudoCode Form_ll_)))
                o>$ (congr_ll o>$ congr_llSol) ) )%sol).

  move: conv_param_forget'Sol conv_llSol; clear; tac_reduce.
  
(** ff is (ff_ o>CoMod ff') **)
+ have [:blurb] :=
    (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' blurb));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ff' blurb; move =>
  Yoneda00_Param_F'FSol Yoneda01_Param_F'FSol Yoneda1_Param_proj_ff'Sol Yoneda1_Param_subst_ff'Sol ReParam_F'FSol Yoneda1_Form_ff'Sol
                        Form_ff'Sol ff'Sol Yoneda1_Param_reparam_F'FSol reparam_F'FSol Congr_congr_ff'Sol congr_ff'Sol conv_ff'Sol.
  have [:blurb] :=
     (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ blurb));
       first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ff_ blurb; move =>
  Yoneda00_Param_F''F'Sol Yoneda01_Param_F''F'Sol Yoneda1_Param_proj_ff_Sol Yoneda1_Param_subst_ff_Sol ReParam_F''F'Sol Yoneda1_Form_ff_Sol
                          Form_ff_Sol ff_Sol Yoneda1_Param_reparam_F''F'Sol reparam_F''F'Sol Congr_congr_ff_Sol congr_ff_Sol conv_ff_Sol.

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  **)
  destruct ff'Sol; simpl in conv_ff'Sol; set Sol_toPolyCoMod_ff'Sol := (X in X [ _ @^ _ ]<~~ ff' ) in conv_ff'Sol.

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.UnitCoMod F)) **)
  * clear solveCoMod solveCoMod_ReParam.
    eapply SR.Build_solveCoMod_return with (ffSol := ( ff_Sol )%sol).
    move: conv_ff_Sol conv_ff'Sol; clear;
      (tac_simpl; intros; eapply convCoMod_Trans with
                              (ff0 := ff_ o>CoMod Sol_toPolyCoMod_ff'Sol);
       subst Sol_toPolyCoMod_ff'Sol; tac_reduce).

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.View1 gg)) **)
  * move: (Sol.morCoMod_codomP ff_Sol) => ff_Sol_morCoMod_codomP.
    { destruct ff_Sol_morCoMod_codomP;
        simpl in conv_ff_Sol; set Sol_toPolyCoMod_ff_Sol := (X in X [ _ @^ _ ]<~~ ff_ ) in conv_ff_Sol.

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitCoMod (View G)) o>CoMod (Sol.View1 gg)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.View1 gg )%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
        
      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.View1 gg0) o>CoMod (Sol.View1 gg)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol :=
         (Sol.View1 (g:= g0 o>Generator g) (viewingDefault_Constructors_Form_action gg gg0))%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Forget param_forget' reparam_forget' ff) o>CoMod (Sol.View1 gg)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol_toPolyCoMod_ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol :=
                ( Sol.Forget param_forget' (reparam_forget' o>_$ (Refl_reparam _) (*/!\ ... *)) ff_Sol_o_ff'Sol )%sol).
        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
    }

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.PolyElement_default cons_paramlocal cons_form)) **)
  * move: (Sol.morCoMod_codomP ff_Sol) => ff_Sol_morCoMod_codomP.
    { destruct ff_Sol_morCoMod_codomP;
        simpl in conv_ff_Sol; set Sol_toPolyCoMod_ff_Sol := (X in X [ _ @^ _ ]<~~ ff_ ) in conv_ff_Sol.

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitCoMod (View G)) o>CoMod (Sol.PolyElement_default cons_paramlocal cons_form)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol :=
           (Sol.PolyElement_default cons_paramlocal cons_form)%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
        
      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.View1 gg) o>CoMod (Sol.PolyElement_default cons_paramlocal cons_form)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol :=
          (Sol.PolyElement_default (form := (g o>GeneratorAtParam_ form))
                                ( ( constructors_action cons_paramlocal (viewingDefault_Constructors_of_viewingDefault_Constructors_Form gg) (constructors_Form_action_transp_Heq Yoneda1_Param_subst param g) ) )
                                ( constructors_Form_action cons_form gg))%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Forget param_forget' reparam_forget' ff) o>CoMod (Sol.PolyElement_default cons_paramlocal cons_form)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol_toPolyCoMod_ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol :=
          (Sol.Forget param_forget' (reparam_forget' o>_$ (Refl_reparam _) (*/!\ ... *)) ff_Sol_o_ff'Sol)%sol).
        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
    }

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
  * move: (Sol.morCoMod_codomP ff_Sol) => ff_Sol_morCoMod_codomP.
    { destruct ff_Sol_morCoMod_codomP;
        simpl in conv_ff_Sol; set Sol_toPolyCoMod_ff_Sol := (X in X [ _ @^ _ ]<~~ ff_ ) in conv_ff_Sol.

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitCoMod (ViewedFunctor_default F0 Param_F0)) o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol :=
          (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
        
      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.ViewedFunctor1_default ff param_ff0 reparam_EF0) o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol.toPolyCoMod ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol.

        pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := ( Sol.toPolyCoMod_ReParam param_ff0 o>CoMod__ Sol.toPolyCoMod_ReParam param_ff ).
        have [:blurbp] :=
          (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SRR solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp; move =>
        Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.

        pose reparam_EFSol := (Sym_reparam reparam_EF_ff_Sol_o_ff'Sol) o>_$ (( PolyCoMod_pseudoCode_ReParam_cong reparam_EF reparam_EF0 ) o>_$ reparam_EF_param_ff_Sol_o_param_ff'Sol) .
        eapply SR.Build_solveCoMod_return with (ffSol :=
                ( Sol.ViewedFunctor1_default ( ff_Sol_o_ff'Sol ) ( param_ff_Sol_o_param_ff'Sol ) ( reparam_EFSol ) )%sol).
        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol conv_param_ff_Sol_o_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitViewedFunctor_default Param_F0 ff) o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol.toPolyCoMod ff'Sol ) .
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb ; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.

        eapply SR.Build_solveCoMod_return with (ffSol :=
          (Sol.UnitViewedFunctor_default Param_F ff_Sol_o_ff'Sol)%sol).
        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__) o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := (fun G param cons_paramlocal form cons_form =>
                                                   Sol.toPolyCoMod (ee__ G param cons_paramlocal form cons_form) o>CoMod Sol.toPolyCoMod ff'Sol ) .
        Time have [:blurb_] := (fun G param cons_paramlocal form cons_form =>
               (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                          (Sol_toPolyCoMod_ff_Sol_o_ff'Sol G param cons_paramlocal form cons_form)
                                          (blurb_ G param cons_paramlocal form cons_form))));
                                 first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol;
                                   subst Sol_toPolyCoMod_ff_Sol; subst Sol_toPolyCoMod_ff'Sol; clear; abstract tac_degrade. (* 300 secs; 108 secs; ? *)
        tac_SR_Family solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb_ ;
          move : Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol
                                   Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol;
          move => Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol.

        pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                Sol.toPolyCoMod_ReParam (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                                                        o>CoMod__ Sol.toPolyCoMod_ReParam param_ff).
         Time have [:blurbp_] := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
               (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _
                                                         (Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                                                         (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
                                   first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol;
                                     subst Sol_toPolyCoMod_ff_Sol; subst Sol_toPolyCoMod_ff'Sol; clear; abstract tac_degrade. (* 104 sec ; 83 secs ; ? *)
        tac_SRR_Family solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp_ ;
          move: Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol;
          move => Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.

        pose reparam_ffSol_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                  (Assoc_reparam _ _ _)
                                    o>_$ (PolyCoMod_pseudoCode_ReParam_cong reparam_EF (reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))) .
        pose reparam_ffSol__ := (fun G param cons_paramlocal form cons_form =>
                                   (Assoc_reparam _ _ _ )
                                     o>_$ (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam ReParam_EF) (reparam_ee__ G param cons_paramlocal form cons_form))).
        pose congr_ffSol__ := (fun G param cons_paramlocal form cons_form =>
                                 (Assoc_congrPseudoCode _ _ _ _ _ _)
                                   o>$ PolyCoMod_cong_congrPseudoCode (Refl_reparam ReParam_EF) (Refl_congrPseudoCode Form_ff) (reparam_ee__ G param cons_paramlocal form cons_form) (congr_ee__ G param cons_paramlocal form cons_form)).

        pose reparam_ffSolffSol9_ := (fun (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P) =>
                                        Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
        pose reparam_ffSolffSol9__ := (fun (G : obGenerator) (param : Yoneda00_Param_SubstF G) (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) Is_Parameter0_Unit)(form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (cons_form : constructors_Form F0 form) =>
                                         Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
        pose congr_ffSolffSol9__ := (fun (G : obGenerator) (param : Yoneda00_Param_SubstF G) (cons_paramlocal : constructors Param_SubstF (sval Yoneda1_Param_subst G param) Is_Parameter0_Unit)(form : Yoneda00_AtParam_ Yoneda1_FormParam_F Yoneda1_Param_proj param) (cons_form : constructors_Form F0 form) =>
                                       Refl_congrPseudoCode (AtMember_Form Form_ee__ cons_paramlocal cons_form)).
        pose reparam_ffSol'ffSol9'__ := (Refl_reparam (PolyCoMod_pseudoCode_ReParam ReParam_EF ReParam_ee'__)).
        pose congr_ffSol'ffSol9'__ := (Refl_congrPseudoCode (PolyCoMod_pseudoCode ReParam_EF Form_ff ReParam_ee'__ Form_ee'__)).
  
        pose reparam_ffSol9_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                   ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ffSol'ffSol9'__ (reparam_ffSolffSol9_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
                                      o>_$ ((reparam_ffSol_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_EF_param_ff_Sol_o_param_ff'Sol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))).
        pose reparam_ffSol9__ := (fun G param cons_paramlocal form cons_form => ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ffSol'ffSol9'__  (reparam_ffSolffSol9__ G param cons_paramlocal form cons_form)))
                                                       o>_$ ((reparam_ffSol__ G param cons_paramlocal form cons_form) o>_$ (reparam_EF_ff_Sol_o_ff'Sol G param cons_paramlocal form cons_form)))).
        pose congr_ffSol9__ := (fun G param cons_paramlocal form cons_form => (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode reparam_ffSol'ffSol9'__ congr_ffSol'ffSol9'__ (reparam_ffSolffSol9__ G param cons_paramlocal form cons_form) (congr_ffSolffSol9__ G param cons_paramlocal form cons_form)))
                                                    o>$ ((congr_ffSol__ G param cons_paramlocal form cons_form) o>$ (congr_ff_Sol_o_ff'Sol G param cons_paramlocal form cons_form))).

        eapply SR.Build_solveCoMod_return with (ffSol :=
          (Sol.PolyTransf_default param_ff_Sol_o_param_ff'Sol reparam_ffSol9_
                                   ff_Sol_o_ff'Sol reparam_ffSol9__ congr_ffSol9__ )%sol).

        Time move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol conv_param_ff_Sol_o_param_ff'Sol; clear; intros; (*MEMO: no simpl *)
          eapply convCoMod_Trans with (ff0 :=
            (PolyTransf_default Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol reparam_ffSol_
                                Sol_toPolyCoMod_ff_Sol_o_ff'Sol reparam_ffSol__ congr_ffSol__ ));
          last (by eapply PolyTransf_default_cong'''; intuition (try apply Refl_coh_congrPseudoCode_ReParam; try apply Refl_coh_congrPseudoCode; eauto));
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce). (* 75 sec *)

      (**TODO: AtMember shall take codes as argument ; in PolyTransf_default_cong reparam_eedd_ congr_eedd__ shall take codes as argument  *)
        
      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Forget param_forget' reparam_forget' ff) o>CoMod (Sol.ViewedFunctor1_default ff'Sol param_ff reparam_EF)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol_toPolyCoMod_ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol .
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol :=
                ( Sol.Forget param_forget' (reparam_forget' o>_$ (Refl_reparam _) (*/!\ ... *)) ff_Sol_o_ff'Sol )%sol).
        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
    }

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.UnitViewedFunctor_default Param_F ff'Sol)) **)
  * pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff_Sol o>CoMod (Sol.toPolyCoMod ff'Sol) ).
    have [:blurb] :=
      (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
        first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
    tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
    Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol .
    clear solveCoMod solveCoMod_ReParam.
    
    eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.UnitViewedFunctor_default Param_F ff_Sol_o_ff'Sol )%sol).
    move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
      (tac_simpl; intros; eapply convCoMod_Trans with
                              (ff0 := Sol.toPolyCoMod ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
       subst Sol_toPolyCoMod_ff'Sol; tac_reduce).

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__)) **)
  * move: (Sol.morCoMod_codomP ff_Sol) => ff_Sol_morCoMod_codomP.
    { destruct ff_Sol_morCoMod_codomP;
        simpl in conv_ff_Sol; set Sol_toPolyCoMod_ff_Sol := (X in X [ _ @^ _ ]<~~ ff_ ) in conv_ff_Sol.

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitCoMod (ViewingFunctorSumSubst_default F)) o>CoMod (Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__ )%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.PolyElement_default cons_paramlocal cons_form) o>CoMod (Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.UnitViewedFunctor_default Param_E ( ee__ G param cons_paramlocal form cons_form ) )%sol).
        Time move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce). (* 17 secs  *)

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Forget param_forget' reparam_forget' ff) o>CoMod (Sol.PolyTransf_default param_ee_ reparam_ee_ ee__ reparam_ee__ congr_ee__)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol_toPolyCoMod_ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade. (* ? sec *)
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol . (* ? sec *)
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol :=
          ( Sol.Forget param_forget' (reparam_forget' o>_$ (Refl_reparam _) (*/!\ ... *)) ff_Sol_o_ff'Sol )%sol).

        Time move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce). (* ? sec *)
    }

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.Forget param_forget' reparam_forget' ff'Sol)) **)
  * move: (Sol.morCoMod_codomP ff_Sol) => ff_Sol_morCoMod_codomP.
    { destruct ff_Sol_morCoMod_codomP;
        simpl in conv_ff_Sol; set Sol_toPolyCoMod_ff_Sol := (X in X [ _ @^ _ ]<~~ ff_ ) in conv_ff_Sol.

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.UnitCoMod (PiSubst F Param_F Param_PiSubstF ReParam_SubstF)) o>CoMod (Sol.Forget param_forget' reparam_forget' ff'Sol)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.Forget param_forget' reparam_forget' ff'Sol )%sol).
        move: conv_ff_Sol conv_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Forget param_forget'0 reparam_forget'0 ff) o>CoMod (Sol.Forget param_forget' reparam_forget' ff'Sol)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol_toPolyCoMod_ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol .
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol :=
          ( Sol.Forget param_forget'0 (reparam_forget'0 o>_$ (Refl_reparam _) (*/!\ ... *)) ff_Sol_o_ff'Sol )%sol).

        Time move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce). (* 78 sec *)

      (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
          is ((Sol.Remember param_forget'0 reparam_forget'0 ff) o>CoMod (Sol.Forget param_forget' reparam_forget' ff'Sol)) **)
      - pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff o>CoMod Sol.toPolyCoMod ff'Sol ).
        have [:blurb] :=
          (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
            first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
        tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
        Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol .
        clear solveCoMod solveCoMod_ReParam.
        
        eapply SR.Build_solveCoMod_return with (ffSol := ( ff_Sol_o_ff'Sol )%sol).

        move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_Trans with
                                  (ff0 := Sol_toPolyCoMod_ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
           subst Sol_toPolyCoMod_ff_Sol Sol_toPolyCoMod_ff'Sol; tac_reduce).
    }

  (** ff is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
      is (ff_Sol o>CoMod (Sol.Remember param_forget' reparam_forget' ff'Sol reparam_remember congr_ll)) **)
  * pose Sol_toPolyCoMod_ff_Sol_o_ff'Sol := ( Sol.toPolyCoMod ff_Sol o>CoMod (Sol.toPolyCoMod ff'Sol) ).
    have [:blurb] :=
      (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb));
        first by intros; move: grade_ff conv_ff_Sol conv_ff'Sol; clear; abstract tac_degrade.
    tac_SR solveCoMod len Sol_toPolyCoMod_ff_Sol_o_ff'Sol blurb; move =>
    Yoneda00_Param_EF_ff_Sol_o_ff'Sol Yoneda01_Param_EF_ff_Sol_o_ff'Sol Yoneda1_Param_proj_ff_Sol_o_ff'Sol Yoneda1_Param_subst_ff_Sol_o_ff'Sol ReParam_EF_ff_Sol_o_ff'Sol Yoneda1_Form_ff_Sol_o_ff'Sol Form_ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol Yoneda1_Param_reparam_EF_ff_Sol_o_ff'Sol reparam_EF_ff_Sol_o_ff'Sol Congr_congr_ff_Sol_o_ff'Sol congr_ff_Sol_o_ff'Sol conv_ff_Sol_o_ff'Sol .
    clear solveCoMod solveCoMod_ReParam.

    pose reparam_forget'_ffSol := reparam_forget'.
    pose reparam_remember_ffSol := ( (Sym_reparam (Assoc_reparam _ _ _)) o>_$ (PolyCoMod_pseudoCode_ReParam_cong reparam_remember (Refl_reparam ReParam_F''F'Sol)) ).
    pose congr_ll_ffSol := ( (Sym_congrPseudoCode (Assoc_congrPseudoCode _ _ _ _ _ _)) o>$ (PolyCoMod_cong_congrPseudoCode reparam_remember congr_ll (Refl_reparam ReParam_F''F'Sol) (Refl_congrPseudoCode Form_ff_Sol) ) ).
    
    pose reparam_forget'_ffSol9 := (reparam_forget'_ffSol o>_$ (Refl_reparam _)).
    pose reparam_remember_ffSol9 := ( (Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong (Refl_reparam _) (Refl_reparam _)))
                o>_$ (reparam_remember_ffSol o>_$ reparam_EF_ff_Sol_o_ff'Sol) ).
    pose congr_ll_ffSol9 := ( (Sym_congrPseudoCode (PolyCoMod_cong_congrPseudoCode (Refl_reparam _) (Refl_congrPseudoCode _)
                                                                   (Refl_reparam _) (Refl_congrPseudoCode _)))
                o>$ (congr_ll_ffSol o>$ congr_ff_Sol_o_ff'Sol) ).

    eapply SR.Build_solveCoMod_return with (ffSol := ( Sol.Remember param_forget' reparam_forget'_ffSol9
                                                         ff_Sol_o_ff'Sol reparam_remember_ffSol9 congr_ll_ffSol9 )%sol).

    move: conv_ff_Sol conv_ff'Sol conv_ff_Sol_o_ff'Sol; clear; 
      (simpl; intros; eapply convCoMod_Trans with
                          (ff0 := ( Remember (Sol.toPolyCoMod_ReParam param_forget') reparam_forget'_ffSol
                                             Sol_toPolyCoMod_ff_Sol_o_ff'Sol reparam_remember_ffSol congr_ll_ffSol )));
      last (by eapply Remember_cong; intuition (try apply Refl_coh_congrPseudoCode_ReParam; try apply Refl_coh_congrPseudoCode; eauto));
      (tac_simpl; intros; eapply convCoMod_Trans with
                              (ff0 := Sol.toPolyCoMod ff_Sol o>CoMod Sol_toPolyCoMod_ff'Sol);
       subst Sol_toPolyCoMod_ff'Sol; tac_reduce).
}
{ (** solveCoMod_ReParam *) case : len => [ | len ].

(** len is O **)
- intros; exfalso;
    by intros; move: grade_ff; clear; abstract tac_degrade.

(** len is (S len) **)
- intros until param_ff. case : Yoneda00_Param_E Yoneda01_Param_E Param_E Yoneda00_Param_F Yoneda01_Param_F Param_F Yoneda00_Param_EF Yoneda01_Param_EF Yoneda1_Param_proj_ff Yoneda1_Param_subst_ff ReParam_EF / param_ff ; intros. 

(** param_ff is  (param_ff_ o>CoMod__ param_ff') *) all: cycle 1.
   
(** param_ff is  (UnitCoMod_ReParam Param_F) **)
+ clear solveCoMod solveCoMod_ReParam.
  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.UnitCoMod_ReParam Param_F )%sol).
  clear; tac_reduce.

(** param_ff is  (View1_ReParam pp)  **)
+ clear solveCoMod solveCoMod_ReParam.
  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.View1_ReParam pp )%sol).
  clear; tac_reduce.

(** param_ff is  (PolyElement_ReParam_default cons_paramlocal) **)
+ clear solveCoMod solveCoMod_ReParam.
  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.PolyElement_ReParam_default cons_paramlocal )%sol).
  clear; tac_reduce.

(** param_ff is  (ViewedFunctor1_ReParam_default param_ff) **)
+ have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff blurbp; move =>
  Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol .
  clear solveCoMod solveCoMod_ReParam.

  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
    ( Sol.ViewedFunctor1_ReParam_default param_ffSol )%sol).

  move: conv_param_ffSol; clear; tac_reduce.

(** param_ff is  (UnitViewedFunctor_ReParam_default param_ff) **)
+ have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff blurbp; move =>
  Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol .
  clear solveCoMod solveCoMod_ReParam.

  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
   ( Sol.UnitViewedFunctor_ReParam_default param_ffSol )%sol).

  move: conv_param_ffSol; clear; tac_reduce.

(** ff is  (PolyTransf_ReParam_default param_ee_ reparam_ee_) **)
+ Time have [:blurbp_] := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
         (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _
                                                   (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                                                   (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
                            first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR_Family solveCoMod_ReParam len param_ee_ blurbp_ ;
    move: Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                        ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol;
    move => Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                         ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol.
  clear solveCoMod solveCoMod_ReParam.

  pose reparam_eeeeSol9_ := (fun (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P)
                                               (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P) =>
                             Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
  pose reparam_ee'eeSol'__ := (Refl_reparam (ReParam_ee'__)).

  pose reparam_eeSol_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                            ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ee'eeSol'__ (reparam_eeeeSol9_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
                               o>_$ ((reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_EF_param_ffSol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))).

  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := 
    ( Sol.PolyTransf_ReParam_default param_ffSol reparam_eeSol_ )%sol).

  move: conv_param_ffSol; clear; intros;
    eapply PolyTransf_ReParam_default_cong; intuition (try apply Refl_coh_congrPseudoCode_ReParam; eauto).
  
(** param_ff is  (Formatting ff param_ff reparam_EF param_ee) **)
+ have [:blurb] :=
    (SR.conv_ffSol (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SR solveCoMod len ff blurb; move =>
  Yoneda00_Param_EF_ffSol Yoneda01_Param_EF_ffSol Yoneda1_Param_proj_ffSol Yoneda1_Param_subst_ffSol ReParam_EF_ffSol Yoneda1_Form_ffSol Form_ffSol ffSol Yoneda1_Param_reparam_EF_ffSol reparam_EF_ffSol Congr_congr_ffSol congr_ffSol conv_ffSol .

  have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff blurbp; move  =>
  Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol conv_param_ffSol .

  have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ee blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ee blurbp; move  =>
  Yoneda00_Param_EF_param_eeSol Yoneda01_Param_EF_param_eeSol Yoneda1_Param_proj_param_eeSol Yoneda1_Param_subst_param_eeSol ReParam_EF_param_eeSol param_eeSol Yoneda1_Param_reparam_EF_param_eeSol reparam_EF_param_eeSol conv_param_eeSol .
  clear solveCoMod solveCoMod_ReParam.

  eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
    (Sol.Formatting ffSol param_ffSol ( (Sym_reparam reparam_EF_ffSol) o>_$
                (reparam_EF o>_$ reparam_EF_param_ffSol) ) param_eeSol)%sol ).

  move:  conv_param_eeSol conv_param_ffSol conv_ffSol; clear; tac_reduce.

(** param_ff is  (param_ff_ o>CoMod__ param_ff') *) 
+ have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff' blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff' blurbp; move =>
  Yoneda00_Param_EF_param_ff'Sol Yoneda01_Param_EF_param_ff'Sol Yoneda1_Param_proj_param_ff'Sol Yoneda1_Param_subst_param_ff'Sol ReParam_EF_param_ff'Sol param_ff'Sol Yoneda1_Param_reparam_EF_param_ff'Sol reparam_EF_param_ff'Sol conv_param_ff'Sol .
  have [:blurbp] :=
    (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ param_ff_ blurbp));
      first by intros; move: grade_ff; clear; abstract tac_degrade.
  tac_SRR solveCoMod_ReParam len param_ff_ blurbp; move =>
  Yoneda00_Param_EF_param_ff_Sol Yoneda01_Param_EF_param_ff_Sol Yoneda1_Param_proj_param_ff_Sol Yoneda1_Param_subst_param_ff_Sol ReParam_EF_param_ff_Sol param_ff_Sol Yoneda1_Param_reparam_EF_param_ff_Sol reparam_EF_param_ff_Sol conv_param_ff_Sol .

  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol)  **)
  destruct param_ff'Sol; simpl in conv_param_ff'Sol; set Sol_toPolyCoMod_ReParam_param_ff'Sol := (X in X [ _ ]<~~__ param_ff') in conv_param_ff'Sol.

  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) , 
      is (param_ff_Sol o>CoMod__ (Sol.UnitCoMod_ReParam Param_F)) **)
  * clear solveCoMod solveCoMod_ReParam.
    eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( param_ff_Sol )%sol).
    move: conv_param_ff_Sol conv_param_ff'Sol; clear;
      (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                              (param_ff0 := param_ff_ o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
       subst Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    
  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) , 
      is (param_ff_Sol o>CoMod__ (Sol.View1_ReParam pp)) **)
  * move: (Sol.morCoMod_ReParam_codomP param_ff_Sol) => param_ff_Sol_morCoMod_ReParam_codomP.
    { destruct param_ff_Sol_morCoMod_ReParam_codomP;
        simpl in conv_param_ff_Sol; set Sol_toPolyCoMod_ReParam_param_ff_Sol := (X in X [ _ ]<~~__ param_ff_ ) in conv_param_ff_Sol.

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.UnitCoMod_ReParam (View_Param P)) o>CoMod__ (Sol.View1_ReParam pp)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.View1_ReParam pp )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                                  (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
        
      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.View1_ReParam pp0) o>CoMod__ (Sol.View1_ReParam pp)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
                  ( Sol.View1_ReParam (p:=((is_Parameter0_transp_codom is_Parameter0_P p0) o>Parametrizator p))
                      (viewingDefault_Constructors_action pp pp0) )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                                  (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    }

  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
      is (param_ff_Sol o>CoMod__ (Sol.PolyElement_ReParam_default cons_paramlocal)) **)
  * move: (Sol.morCoMod_ReParam_codomP param_ff_Sol) => param_ff_Sol_morCoMod_ReParam_codomP.
    { destruct param_ff_Sol_morCoMod_ReParam_codomP;
        simpl in conv_param_ff_Sol; set Sol_toPolyCoMod_ReParam_param_ff_Sol := (X in X [ _ ]<~~__ param_ff_ ) in conv_param_ff_Sol.

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.UnitCoMod_ReParam (View_Param P)) o>CoMod__ (Sol.PolyElement_ReParam_default cons_paramlocal)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.PolyElement_ReParam_default cons_paramlocal )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                                  (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
                                                                                      
      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.View1_ReParam pp) o>CoMod__ (Sol.PolyElement_ReParam_default cons_paramlocal)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.PolyElement_ReParam_default (constructors_action cons_paramlocal pp (eq_refl _)) )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                                  (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    }

  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
      is (param_ff_Sol o>CoMod__ (Sol.ViewedFunctor1_ReParam_default param_ff'Sol)) **)
  * move: (Sol.morCoMod_ReParam_codomP param_ff_Sol) => param_ff_Sol_morCoMod_ReParam_codomP.
    { destruct param_ff_Sol_morCoMod_ReParam_codomP;
        simpl in conv_param_ff_Sol; set Sol_toPolyCoMod_ReParam_param_ff_Sol := (X in X [ _ ]<~~__ param_ff_ ) in conv_param_ff_Sol.

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol. UnitCoMod_ReParam (ViewedFunctor_Param_default Param_F0)) o>CoMod__ (Sol.ViewedFunctor1_ReParam_default param_ff'Sol)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol := ( Sol.ViewedFunctor1_ReParam_default param_ff'Sol )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                                  (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
                                                                                      
      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.ViewedFunctor1_ReParam_default param_ff) o>CoMod__ (Sol.ViewedFunctor1_ReParam_default param_ff'Sol)) **)
      - pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := ( Sol.toPolyCoMod_ReParam param_ff o>CoMod__ Sol.toPolyCoMod_ReParam param_ff'Sol ).
        have [:blurbp] :=
          (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp));
            first by intros; move: grade_ff conv_param_ff_Sol conv_param_ff'Sol; clear; abstract tac_degrade.
        tac_SRR solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp; move =>
        Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol .
        clear solveCoMod solveCoMod_ReParam.

        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.ViewedFunctor1_ReParam_default param_ff_Sol_o_param_ff'Sol )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
              (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.UnitViewedFunctor_ReParam_default param_ff) o>CoMod__ (Sol.ViewedFunctor1_ReParam_default param_ff'Sol)) **)
      - pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := ( Sol.toPolyCoMod_ReParam param_ff o>CoMod__ Sol.toPolyCoMod_ReParam param_ff'Sol ).
        have [:blurbp] :=
          (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp));
            first by intros; move: grade_ff conv_param_ff_Sol conv_param_ff'Sol; clear; abstract tac_degrade.
        tac_SRR solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp; move =>
        Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol .
        clear solveCoMod solveCoMod_ReParam.

        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.UnitViewedFunctor_ReParam_default param_ff_Sol_o_param_ff'Sol )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
             (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
        
      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.PolyTransf_ReParam_default param_ee_ reparam_ee_) o>CoMod__ (Sol.ViewedFunctor1_ReParam_default param_ff'Sol)) **)
      - pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                Sol.toPolyCoMod_ReParam (param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                                                        o>CoMod__ Sol.toPolyCoMod_ReParam param_ff'Sol).
        have [:blurbp_] := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
               (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _
                      (Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)
                      (blurbp_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))));
                             first by intros; move: grade_ff conv_param_ff_Sol conv_param_ff'Sol;
                               subst Sol_toPolyCoMod_ReParam_param_ff_Sol; subst Sol_toPolyCoMod_ReParam_param_ff'Sol; clear; abstract tac_degrade.
        tac_SRR_Family solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp_ ;
          move: Yoneda00_Param_EF_param_ffSol Yoneda01_Param_EF_param_ffSol Yoneda1_Param_proj_param_ffSol Yoneda1_Param_subst_param_ffSol
                                              ReParam_EF_param_ffSol param_ffSol Yoneda1_Param_reparam_EF_param_ffSol reparam_EF_param_ffSol;
          move => Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol.
        clear solveCoMod solveCoMod_ReParam.

        pose reparam_ffSol_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                  (Assoc_reparam _ _ _) o>_$ (PolyCoMod_pseudoCode_ReParam_cong  (Refl_reparam ReParam_EF)
                                    (reparam_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal))) .

        pose reparam_ffSolffSol9_ := (fun (G : obGenerator) (paramlocal : Yoneda00_Param_SumSubstF G) (P : obParametrizator) (is_Parameter0_P : is_Parameter0 G P) (cons_is_Parameter0_P : is_Parameter0Default_Constructors is_Parameter0_P) (cons_paramlocal : constructors Param_SubstF paramlocal cons_is_Parameter0_P) =>
                                        Refl_reparam (AtMember_ReParam ReParam_ee_ cons_paramlocal)).
        pose reparam_ffSol'ffSol9'__ := (Refl_reparam (PolyCoMod_pseudoCode_ReParam ReParam_EF ReParam_ee'__)).
  
        pose reparam_ffSol9_ := (fun G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal =>
                                   ((Sym_reparam (PolyCoMod_pseudoCode_ReParam_cong reparam_ffSol'ffSol9'__ (reparam_ffSolffSol9_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))
                                      o>_$ ((reparam_ffSol_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal) o>_$ (reparam_EF_param_ff_Sol_o_param_ff'Sol G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal)))).

        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.PolyTransf_ReParam_default param_ff_Sol_o_param_ff'Sol reparam_ffSol9_ )%sol).

        move: conv_param_ff_Sol conv_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol; clear;
          (simpl; intros; eapply convCoMod_ReParam_Trans with
            (param_ff0 := ( PolyTransf_ReParam_default Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol reparam_ffSol_ )));
          last (by eapply PolyTransf_ReParam_default_cong; intuition (try apply Refl_coh_congrPseudoCode_ReParam; eauto));
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
              (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    }
    
  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
      is (param_ff_Sol o>CoMod__ (Sol.UnitViewedFunctor_ReParam_default param_ff'Sol)) **)
  * pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := ( Sol.toPolyCoMod_ReParam param_ff_Sol o>CoMod__ Sol.toPolyCoMod_ReParam param_ff'Sol ).
    have [:blurbp] :=
      (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp));
        first by intros; move: grade_ff conv_param_ff_Sol conv_param_ff'Sol; clear; abstract tac_degrade.
    tac_SRR solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp; move =>
    Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol .
    clear solveCoMod solveCoMod_ReParam.

    eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
      ( Sol.UnitViewedFunctor_ReParam_default param_ff_Sol_o_param_ff'Sol )%sol).
    move: conv_param_ff_Sol conv_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol; clear;
      (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
         (param_ff0 := Sol.toPolyCoMod_ReParam param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
       subst Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    
  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
      is (param_ff_Sol o>CoMod__ (Sol.PolyTransf_ReParam_default param_ee_ reparam_ee_)) **)
  * move: (Sol.morCoMod_ReParam_codomP param_ff_Sol) => param_ff_Sol_morCoMod_ReParam_codomP.
    { destruct param_ff_Sol_morCoMod_ReParam_codomP;
        simpl in conv_param_ff_Sol; set Sol_toPolyCoMod_ReParam_param_ff_Sol := (X in X [ _ ]<~~__ param_ff_ ) in conv_param_ff_Sol.

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.UnitCoMod_ReParam (ViewingFunctor_Param_default Param_SubstF)) o>CoMod__ (Sol.PolyTransf_ReParam_default param_ee_ reparam_ee_)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.PolyTransf_ReParam_default param_ee_ reparam_ee_ )%sol).
        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
             (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).

      (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol) ,
          is ((Sol.PolyElement_ReParam_default cons_paramlocal) o>CoMod__ (Sol.PolyTransf_ReParam_default param_ee_ reparam_ee_)) **)
      - clear solveCoMod solveCoMod_ReParam.
        eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
          ( Sol.UnitViewedFunctor_ReParam_default ( param_ee_ G paramlocal P is_Parameter0_P cons_is_Parameter0_P cons_paramlocal ) )%sol).

        move: conv_param_ff_Sol conv_param_ff'Sol; clear;
          (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
             (param_ff0 := Sol_toPolyCoMod_ReParam_param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
           subst Sol_toPolyCoMod_ReParam_param_ff_Sol Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
    (** /!\ GHOST /!\ REQUIRES MORE GENERAL REDUCTION OF 
        PolyElement_ReParam_default isFiniteness_Transf_SubstF0 o>CoMod__ PolyTransf_ReParam_default isFiniteness_Transf_SubstF  *)
    }

  (** param_ff is (param_ff_ o>CoMod__ param_ff') , to (param_ff_Sol o>CoMod__ param_ff'Sol)  , 
      is (param_ff_Sol o>CoMod__ (Sol.Formatting ff param_ff'Sol1 reparam_EF param_ff'Sol2)) **)
  * pose Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol := ( Sol.toPolyCoMod_ReParam param_ff_Sol o>CoMod__ Sol.toPolyCoMod_ReParam param_ff'Sol2 ).
    have [:blurbp] :=
      (SRR.conv_param_ffSol (solveCoMod_ReParam len _ _ _ _ _ _ _ _ _ _ _ Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp));
        first by intros; move: grade_ff conv_param_ff_Sol conv_param_ff'Sol; clear; abstract tac_degrade.
    tac_SRR solveCoMod_ReParam len Sol_toPolyCoMod_ReParam_param_ff_Sol_o_param_ff'Sol blurbp; move =>
    Yoneda00_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda01_Param_EF_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_proj_param_ff_Sol_o_param_ff'Sol Yoneda1_Param_subst_param_ff_Sol_o_param_ff'Sol ReParam_EF_param_ff_Sol_o_param_ff'Sol param_ff_Sol_o_param_ff'Sol Yoneda1_Param_reparam_EF_param_ff_Sol_o_param_ff'Sol reparam_EF_param_ff_Sol_o_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol .
    clear solveCoMod solveCoMod_ReParam.

    eapply SRR.Build_solveCoMod_ReParam_return with (param_ffSol :=
      ( Sol.Formatting ff param_ff'Sol1 ( (Sym_reparam (Refl_reparam _)) o>_$ (reparam_EF o>_$ (Refl_reparam _)) ) param_ff_Sol_o_param_ff'Sol )%sol).
    move: conv_param_ff_Sol conv_param_ff'Sol conv_param_ff_Sol_o_param_ff'Sol; clear;
      (tac_simpl; intros; eapply convCoMod_ReParam_Trans with
                              (param_ff0 := Sol.toPolyCoMod_ReParam param_ff_Sol o>CoMod__ Sol_toPolyCoMod_ReParam_param_ff'Sol);
       subst Sol_toPolyCoMod_ReParam_param_ff'Sol; tac_reduce).
}
Time Optimize Heap. (* 48 secs , end: Heap 12G *)
Time Optimize Proof. (* Evars: 50982 -> 0 <infomsg>Finished transaction in 55.567 secs (55.564u,0.s) (successful)</infomsg> *)
Time Defined.

(** # #
#+END_SRC

Voila.

**)
