(** # #
#+TITLE: cartierSolution8.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution8.v
https://gitlab.com/1337777/cartier/blob/master/cartierSolution8.v.pdf

solves half of some question of Cartier which is how to program grammatical polymorph « modos » / modified-colimit-into-viewed-metafunctor ( "sheafification" , "forcing" ) ...

SHORT ::

  The ends is to 

  For instant first impression , the sense-decoding ( "Yoneda" ) of the modified-colimit-into-viewed-metafunctor , is written as :

#+BEGIN_EXAMPLE
#+END_EXAMPLE

KEYWORDS :: 1337777.OOO ; COQ ; cut-elimination ; modified-colimit-into-viewed-metafunctor ; modos

OUTLINE ::

  * BLA
    + BLABLA
    + BLABLA

  * BLA

-----

HINT :: free master-engineering ; program this grammatical polymorph 

-----

BUY MOM RECURSIVE T-SQUARE :: paypal.me/1337777 1337777.OOO@gmail.com ; 微信支付 2796386464@qq.com ; eth 0x54810dcb93b37DBE874694407f78959Fa222D920 ; amazon amazon.com/hz/wishlist/ls/28SN02HR4EB8W ; irc #OOO1337777

-----

TODO:
-memo: viewing-functor-data is similar as local epimorphism but more forward/constructive , and is the mod-ified colimit ( « modos » )
-memo: for each (viewed/"partial") cocone out of some viewing-functor-data colimit into some other functor , then the (extended) viewed-functor of this functor is the recipient of the forced colimitator/copairing out of this modified colimit
- memo: local epimorphisms is blend of galois-topology on the generators with colimit-structure/topology on the presheaves
- memo:  the quantification forall Yoneda00_F Yoneda01_F F V_ , signify function with viewing , which is then internalized as viewed-functor ViewedFunctor F
- memo: inclusion for dense generators is the generic model
-todo: shortcut for mophism of views 
-memo: viewing/morphology ; algebraic/structural contrast visualization/morphological/geometrical/topological
-todo: modos or morphos or both
-todo: v :>Generator|V_ = v' :>Generator|V_' -> PolyElement F V_ G f H v ~ PolyElement F V_'other G f H v'  
-TODO: NEXT redo lemma ViewedFunctor_PolyTransf with input of the form 'CoMod( View H ~> ViewingFunctor (ViewedFunctor E) None @ _ ) with optional views such can destruct morphism which has only-constructors-and-variables indexes , now extracted sense of views is computed by case ,  now PolyElement and PolyTranst input optional view and output optional view
-todo: shall hypotheses Yoneda10_ee_morphism be prefixed in the form  polyelement_to_element ( _ ) = polyelement_to_element ( _ ) 
-memo: errata in cartierSolution7.v polymorphism for counitgenerated : errata where polymorphism occurs , errata naming ?unitgenerated
-TODO: (**TODO: in below term , primo fix Yoneda10_ee_ to be Yoneda10_PolyElement then for primo index  (projT1 (projT2 wv)) below term is depended only as
 ( (projT1 (projT2 wv)) :>Generator ) , secondo in Yoneda00_ViewedFunctor add property Yoneda10_natural_toView as for morViews , such that for second index (projT2 (projT2 wv)) is depended only as ( (projT2 (projT2 wv)) :>Generator )
finally hypothesis ( w :>Generator o>Generator v :>Generator == ) wv :>Generator = wv_' :>Generator can be used because below term depends only on such 
---
   (projT2 (projT1 (polyelement_to_element (Yoneda10_ee_ G f (projT1 wv) (projT1 (projT2 wv)))))
          H' (projT2 (projT2 wv))) **)
-todo: TODO change (projT1 (polyelement_to_element (Yoneda10_ee_ G f _ _ ))) to 
(sval (polyelement_to_element (Yoneda10_ee_ G f _ _ ))) 
-todo: rename Views to Viewing
-todo: the common term ( projT2_sval_polyelement_to_element_Yoneda10_ee_
             G f (projT1 wv) (projT1 (projT2 wv)) H' (projT2 (projT2 wv)) )
  when ee_ is actions, will depend on input only ( (Q_prop w).1 :>Generator ) == ( (Q_prop w).2 :>Generator ) == ( ((Q_prop w) :>Generator ) o>Generator (hex :>Generator) ) == ( ( ((Q_prop w) :>Generator) o>Generator hex | ?? _ projT1 ee_Hex?? ) :>Generator ) ... gives output ( Yoneda01_E ( (Q_prop w : U_ by choice of W_ v <= U_ (projT2 (ee_ v))) :>Generator ) (ee_Hex hex) )
NOT REALLY   | ?? _ projT1 ee_Hex?? 
-todo: wrap Yoneda01_F inside notation
-todo: change Yoneda10_ee_morphism to polyelemtn_to_element (Yoneda10_ee_ _) = polyelemtn_to_element (Yoneda10_ee_ _)
-todo: solve "abstract" cannot handle existentials. in solve [[ ee_ @ F , V_prop ]] 
-todo: in | UnitCoMod :  forall B : obGenerator, 
    morCoMod_codomView ( ( @'UnitCoMod (View B) )%sol )
    rename B to G
-todo: add cut-adherence for ViewedFunctor _E ~~ ViewedFunctor E -> ViewingFunctor _E _U_prop ~~ ViewingFunctor _E V_prop
-time: for preformat : wed july 18 h16m27  to  august 15 = 29 days - 3 days - 2 days = 24 days
predicted after format : + 7 days = 31 days = 1 month 
-todo: in definitions, fold any possible polyelement_to_element
-todo: wrtie for  (g : 'Generator( G' ~> G )) (v' : 'Generator( H ~> G' | _ )) of (fst (sval (sval (V_prop G G' g f) H v'))) as  ( v' o>>Generator`V_prop` g ) or of similar
-todo: change Yoneda10_PolyElement implicits
-todo: move Yoneda10_ee_natural_prop  Yoneda10_ee_toView_prop  up to Yoneda10_ee_morphism_prop
-todo: at Lemme Yoneda10_PolyTransf add uniqueness is computationally
-todo:  inYoneda00_ViewedFunctor_quotient'' change projT1 to sval
-todo: ERRATA cartierSOlution7.v counitgenerated has cut at R , therefore solve by not accepting argument-morphism 


-----

* BLA


** BLABLA

#+BEGIN_SRC coq :exports both :results silent # # **)
From mathcomp
    Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Psatz.

Module VIEWEDFUNCTOR.

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Delimit Scope poly_scope with poly.
Open Scope poly.

Parameter obGenerator : Type.
Parameter morGenerator : obGenerator -> obGenerator -> Type.
Parameter polyGenerator :
  forall A A', morGenerator A' A -> forall A'', morGenerator A'' A' -> morGenerator A'' A .
Parameter unitGenerator : forall {A : obGenerator}, morGenerator A A.

Notation "''Generator' ( A' ~> A )" := (@morGenerator A' A)
                  (at level 0, format "''Generator' (  A'  ~>  A  )") : poly_scope.
Notation "_@ A'' o>Generator a'" := (@polyGenerator _ _ a' A'')
          (at level 40, A'' , a' at next level, left associativity,
           format "_@ A''  o>Generator  a'") : poly_scope.
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

Definition Yoneda01_functor (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : forall G G' : obGenerator,
               'Generator( G' ~> G ) -> Yoneda00 G -> Yoneda00 G') : Prop :=
  ( (* binary/composing functoriality *)
    ( forall G G' (g : 'Generator( G' ~> G)) G'' (g' : 'Generator( G'' ~> G')) x,
        Yoneda01 _ _ g' (Yoneda01 _ _ g x) = Yoneda01 _ _ (g' o>Generator g) x ) /\
    ( (* empty/unit functoriality is held only in PolyElement_Pairing *)
      forall G x, x = Yoneda01 _ _ (@unitGenerator G) x ) ) .

Definition Yoneda10_natural
           Yoneda00_F (Yoneda01_F : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           Yoneda00_E (Yoneda01_E : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           (Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G) : Prop :=
  forall G G' (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
    (proj1_sig Yoneda01_E) _ _ g (Yoneda10 G f)
    = Yoneda10 G' ((proj1_sig Yoneda01_F) _ _ g f) .

Lemma Yoneda00_View : forall (B : obGenerator), (obGenerator -> Type).
Proof. intros B. refine (fun A => 'Generator( A ~> B ) ). Defined.

Lemma Yoneda01_View : forall (B : obGenerator),
    {Yoneda01 : ( forall A A' : obGenerator,
          'Generator( A' ~> A ) -> (Yoneda00_View B) A -> (Yoneda00_View B) A' ) |
     Yoneda01_functor Yoneda01} .
Proof.
  intros. exists (fun A A' a x => a o>Generator x).
  abstract (split; [intros; exact: polyGenerator_morphism
                   | intros; exact: polyGenerator_unitGenerator]).
Defined.

Lemma Yoneda10_View_toView : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )),
    {Yoneda10 : _ | @Yoneda10_natural (Yoneda00_View G') (Yoneda01_View G')
                                      (Yoneda00_View G) (Yoneda01_View G) Yoneda10 }.
Proof.
  intros. unshelve eexists.
  - intros H g'. exact: (g' o>Generator g).
  - abstract (move; simpl; intros; exact: polyGenerator_morphism).
Defined.

(*Parameter obViews_prop : obGenerator -> Type.*)
Record obViews (G : obGenerator) : Type := ObViews
{ Yoneda00_Views : (obGenerator -> Type)
  ; Yoneda01_Views : {Yoneda01 : forall H H' : obGenerator,
                         'Generator( H' ~> H ) -> Yoneda00_Views H -> Yoneda00_Views H' |
                      Yoneda01_functor Yoneda01}
  ; Yoneda10_Views_toView :  {Yoneda10 : forall H : obGenerator,
                                 Yoneda00_Views H -> Yoneda00_View G H |
                              Yoneda10_natural (Yoneda01_Views) (Yoneda01_View G) Yoneda10} }.

Parameter obViews_prop : forall (G : obGenerator), (obViews G) -> Prop.

Notation "''Generator' ( G' ~> G | V )" := (@Yoneda00_Views G V G')
        (at level 0, 
         format "''Generator' (  G'  ~>  G  |  V  )") : poly_scope.
Notation "h o>Generator _@ G | V" := (sval (@Yoneda01_Views G V) _ _ h)
          (at level 40, G at next level, V at next level , left associativity,
           format "h  o>Generator  _@  G  |  V") : poly_scope.
Notation "h o>Generator v | V" := (sval (@Yoneda01_Views _ V) _ _ h v)
          (at level 40, v , V at next level, format "h  o>Generator  v  |  V") : poly_scope.
Notation "v :>Generator" := (sval (@Yoneda10_Views_toView _ _) _ v)
          (at level 40) : poly_scope.

Section unitViews.

  Definition unitViews (G G' : obGenerator) (g : 'Generator( G' ~> G )) :=
    (@ObViews G (Yoneda00_View G') (Yoneda01_View G') (Yoneda10_View_toView g)).
  Parameter unitViewsP : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )),
      @obViews_prop G (unitViews g).

End unitViews.

Section intersecViews.

Variables (G : obGenerator) (V : obViews G)
          (G' : obGenerator) (g : 'Generator( G' ~> G )).

Definition Yoneda00_intersecViews : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { vg' : (Yoneda00_Views V H * Yoneda00_Views (unitViews g) H)%type |
                                ( fst vg' :>Generator ) = ( snd vg' :>Generator ) } ).
Defined.

Axiom ax1_Yoneda00_intersecViews : forall G (v v' : Yoneda00_intersecViews G), sval v = sval v' -> v = v'.
                  
Definition Yoneda01_intersecViews
  : {Yoneda01 : forall H H' : obGenerator, 'Generator( H' ~> H ) -> Yoneda00_intersecViews H -> Yoneda00_intersecViews H' |
     Yoneda01_functor Yoneda01} .
Proof.
  unshelve eexists.
  - intros H H' h vg'.
    exists ( h o>Generator (fst (sval vg')) | _ , h o>Generator (snd (sval vg')) | _ ) .
    abstract (simpl; rewrite -(proj2_sig (Yoneda10_Views_toView V)); rewrite -(polyGenerator_morphism);
              rewrite (proj2_sig vg'); reflexivity).
  - abstract (split; simpl;
              first (by intros; apply: ax1_Yoneda00_intersecViews; simpl;
                     rewrite -(proj1 (proj2_sig (Yoneda01_Views V))); rewrite -(polyGenerator_morphism); reflexivity);
              intros H vh; apply: ax1_Yoneda00_intersecViews; simpl;
              rewrite -(proj2 (proj2_sig (Yoneda01_Views V))); rewrite -(polyGenerator_unitGenerator);
              move: (sval vh) => sval_vh; destruct sval_vh; reflexivity).
Defined.

Definition Yoneda10_intersecViews_toView
  : {Yoneda10 : forall H : obGenerator, Yoneda00_intersecViews H -> Yoneda00_Views (unitViews g) H |
     Yoneda10_natural Yoneda01_intersecViews (Yoneda01_View G') Yoneda10 }.
Proof.
  unshelve eexists.
  - intros H vg'. exact: (snd (sval vg')).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda10_intersecViews_toViews
  : {Yoneda10 : forall H : obGenerator, Yoneda00_intersecViews H -> Yoneda00_Views V H |
     Yoneda10_natural Yoneda01_intersecViews (Yoneda01_Views V) Yoneda10 }.
Proof.
  unshelve eexists.
  - intros H vg'. exact: (fst (sval vg')).
  - abstract (move; reflexivity).
Defined.


Definition intersecViews := (@ObViews G' Yoneda00_intersecViews Yoneda01_intersecViews Yoneda10_intersecViews_toView).

Axiom intersecViewsP : @obViews_prop G V -> @obViews_prop G' intersecViews.

End intersecViews.

Definition Yoneda10_intersecViews_toViews_unitGenerator (G : obGenerator) (V : obViews G)
           (H : obGenerator) (v :  'Generator( H ~> G | V )) :
  { h_unit : 'Generator( H ~> H | intersecViews V (v :>Generator ) )
  | v = sval (Yoneda10_intersecViews_toViews V (v :>Generator)) _ h_unit } .
Proof.
  unshelve eexists. exists ( v , @unitGenerator _ ).
  abstract(simpl; rewrite -[RHS]polyGenerator_unitGenerator; reflexivity).
  abstract(simpl; reflexivity).
Defined.

(**Notation "<<< G' ; v ; w >>>" := (existT (fun v0 : {G'0 : obGenerator & _ } => _ ) (existT _ G' v) w)
                                (at level 0, format "<<<  G'  ;  v  ;  w  >>>"). **)
Notation "<<< G' ; v ; w >>>" := (existT _ (existT _ G' v) w)
                                (at level 0, format "<<<  G'  ;  v  ;  w  >>>").

Section sumViews.

Variables (G : obGenerator) (V : obViews G)
          (WP_ : forall G' : obGenerator, 'Generator( G' ~> G | V ) -> obViews G' ).

Definition Yoneda00_sumViews : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { v : {G' : obGenerator & Yoneda00_Views V G'} & Yoneda00_Views (WP_ (projT2 v)) H }).
Defined.

Definition Yoneda01_sumViews
  : {Yoneda01 : forall H H' : obGenerator, 'Generator( H' ~> H ) -> Yoneda00_sumViews H -> Yoneda00_sumViews H' |
     Yoneda01_functor Yoneda01} .
Proof.
  unshelve eexists.
  - intros H H' h w.
    refine ( <<< projT1 (projT1 w) ; projT2 (projT1 w) ;
              h o>Generator (projT2 w) | _ >>> ).
  + abstract (split; simpl;
              first (by intros; rewrite -(proj1 (proj2_sig (@Yoneda01_Views _ (WP_ _)))); reflexivity);
              intros ? wv; rewrite -(proj2 (proj2_sig (@Yoneda01_Views _ (WP_ _))));
              destruct wv as [[? ?] ?]; reflexivity).
Defined.

Definition Yoneda10_sumViews_toView
  : {Yoneda10 : forall H : obGenerator, Yoneda00_sumViews H -> Yoneda00_View G H |
     Yoneda10_natural Yoneda01_sumViews (Yoneda01_View G) Yoneda10 }.
Proof.
  unshelve eexists.
  - simpl. intros ? wv . refine ( ((projT2 wv) :>Generator)
                                    o>Generator ( (projT2 (projT1 wv)) :>Generator ) ).
  - abstract (rewrite /Yoneda10_natural ; simpl; intros;
              rewrite [in LHS]polyGenerator_morphism;
              rewrite -[in RHS]( proj2_sig (Yoneda10_Views_toView (WP_ _))); reflexivity).
Defined.

Definition sumViews := (@ObViews G Yoneda00_sumViews Yoneda01_sumViews Yoneda10_sumViews_toView).
Parameter sumViewsP : @obViews_prop G V ->
                     ( forall (G' : obGenerator) (v : 'Generator( G' ~> G | V )),
                         @obViews_prop G' (@WP_ G' v) ) -> @obViews_prop G sumViews.

End sumViews.

(**Notation "<< V ; ff >>" := (existT (fun V0 : obViews _ => _) V ff)
                                (at level 0, format "<<  V  ; '/'  ff  >>").
**)
Arguments exist [_] {_} _ _ .

Section Senses_obCoMod.

Notation "<< V ; ff >>" := (existT (fun V0 : obViews _ => _) V ff)
                                (at level 0, format "<<  V  ; '/'  ff  >>").

Definition Yoneda00_ViewedFunctor (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 }) :
  (obGenerator -> Type) := 
  ( fun G => { V_ff : { V : obViews G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) } 
             | @obViews_prop G (projT1 V_ff) /\
               @Yoneda10_natural (Yoneda00_Views (projT1 V_ff)) (Yoneda01_Views (projT1 V_ff)) 
                                 (Yoneda00_F) (Yoneda01_F) (projT2 V_ff) /\
               ( forall H v v', v :>Generator = v' :>Generator ->
                                projT2 V_ff H v = projT2 V_ff H v' ) } ). 

Definition morViews G (V1 V2 : obViews G) :=
      {Yoneda10 : forall H : obGenerator, Yoneda00_Views V1 H -> Yoneda00_Views V2 H |
              Yoneda10_natural (Yoneda01_Views V1) (Yoneda01_Views V2) Yoneda10 /\
              forall H v1, ( Yoneda10 H v1 :>Generator ) = ( v1 :>Generator )  } .

Axiom Yoneda00_ViewedFunctor_quotient : forall Yoneda00_F Yoneda01_F G,
    forall (V1_ff1 : { V : obViews G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) }) V1_ff1_P
      (V2_ff2 : { V : obViews G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) }) V2_ff2_P,
    forall (W : obViews G)
      (vv1 : morViews W (projT1 V1_ff1))
      (vv2 : morViews W (projT1 V2_ff2)),
      ( forall H, (projT2 V1_ff1) H \o sval vv1 H =1 (projT2 V2_ff2) H \o sval vv2 H ) ->
      ( @exist _ _ V1_ff1 V1_ff1_P  )
      = ( @exist _ _ V2_ff2 V2_ff2_P : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G ).

Lemma Yoneda00_ViewedFunctor_quotient'' : forall Yoneda00_F Yoneda01_F G,
    forall (V1_ff1 V2_ff2 : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G),
    forall (W : obViews G)
      (vv1 : morViews W (projT1 (sval V1_ff1)))
      (vv2 : morViews W (projT1 (sval V2_ff2))),
      ( forall H, (projT2 (sval V1_ff1)) H \o sval vv1 H =1 (projT2 (sval V2_ff2)) H \o sval vv2 H ) ->
      V1_ff1 = V2_ff2 .
Proof.
  destruct V1_ff1; destruct V2_ff2. exact: Yoneda00_ViewedFunctor_quotient.
Qed.

Definition views_identity_arrow : forall G (V : obViews G), morViews V V .
Proof.
  intros. exists (fun H => id).
  abstract (split; move; reflexivity).
Defined.

Definition views_identity_arrow'' : forall G (V V' : obViews G),
    V = V' -> { Z_prop : morViews V V' * morViews V' V | forall H , sval (snd Z_prop) H \o sval (fst Z_prop) H =1 id }.
Proof.
  intros. subst. unshelve eexists. split;  exact: views_identity_arrow.
  abstract (intros; move; reflexivity).
Defined.

Lemma Yoneda00_ViewedFunctor_quotient_rev : forall Yoneda00_F Yoneda01_F G,
     forall (V1_ff1 V2_ff2 : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G),
       V1_ff1 = V2_ff2 ->
       { vv2 : morViews (projT1 (sval V1_ff1)) (projT1 (sval V2_ff2)) |
       ( forall H, (projT2 (sval V1_ff1)) H =1 (projT2 (sval V2_ff2)) H \o sval vv2 H ) }.
Proof.
  intros. subst. exists (views_identity_arrow _).
  abstract (intros; move; reflexivity).
Qed.

Definition views_identity_unitViews_arrow : forall G (V : obViews G), morViews V (unitViews unitGenerator) .
Proof.
  intros. exists (fun H v => (v :>Generator)).
  abstract (split; move; simpl; intros;
            [ exact: (proj2_sig (Yoneda10_Views_toView V))
            | rewrite -unitGenerator_polyGenerator; reflexivity ]).
Defined.

Lemma intersecViews_identity_arrow :
  forall (G : obGenerator) (V : obViews G), morViews V (intersecViews V (unitGenerator)).
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact: v.
      * exact: (v :>Generator).
    + abstract(simpl; exact: unitGenerator_polyGenerator). 
  - split;
      [ abstract (move; simpl; intros; apply: ax1_Yoneda00_intersecViews; simpl;
                  rewrite -(proj2_sig (Yoneda10_Views_toView V)); reflexivity) 
      | move; reflexivity].
Defined.

Lemma intersecViews_composition_arrow :
  forall (G : obGenerator) (V : obViews G)
    (G' : obGenerator) (g : 'Generator( G' ~> G )),
  forall (G'' : obGenerator) (g' : 'Generator( G'' ~> G' )), morViews (intersecViews (intersecViews V g) g') (intersecViews V (g' o>Generator g)).
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact:  ( sval (Yoneda10_intersecViews_toViews V g) _ (fst (sval v)) )  .
      * exact: ((snd (sval v)) ).
    + abstract (simpl; rewrite (proj2_sig (fst (sval v))); simpl;
                rewrite [X in X o>Generator _ = _](proj2_sig v);
                rewrite [in RHS]polyGenerator_morphism; reflexivity).
  - split.
    + abstract (move; simpl; intros;
                apply: ax1_Yoneda00_intersecViews; simpl; reflexivity).
    + abstract (move; simpl; intros; reflexivity).
Defined.

Lemma intersecViews_unitViews :
  forall (G : obGenerator)  (G' : obGenerator) (g : 'Generator( G' ~> G )), morViews (unitViews unitGenerator) (intersecViews (unitViews unitGenerator) g) .
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact: (v o>Generator g).
      * exact: v.
    + simpl. abstract(simpl; rewrite -polyGenerator_morphism -unitGenerator_polyGenerator; reflexivity).
  - split.
    + abstract (move; simpl; intros;
                apply: ax1_Yoneda00_intersecViews; simpl;  rewrite polyGenerator_morphism; reflexivity).
    + abstract (move; simpl; intros; rewrite -unitGenerator_polyGenerator; reflexivity).
Defined.

Definition Yoneda01_ViewedFunctor : forall (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 }),
    { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_ViewedFunctor Yoneda01_F G -> Yoneda00_ViewedFunctor Yoneda01_F G' ) |
      Yoneda01_functor Yoneda01 }.
Proof.
  intros. unshelve eexists.
  - intros G G' g V_ff.
    unshelve eexists.
    + exists (intersecViews (projT1 (sval V_ff)) g).
    + exact: (fun H =>
                  projT2 (sval V_ff) H \o
                       (sval (Yoneda10_intersecViews_toViews (projT1 (sval V_ff)) g) H)).
  - abstract (simpl; split;
              first (by exact: (intersecViewsP g (proj1 (proj2_sig V_ff))));
              split; first (by abstract (move; simpl; intros;
                                         rewrite (proj1 (proj2 (proj2_sig V_ff))); reflexivity));
              abstract (intros H v v' Heq; apply: (proj2 (proj2 (proj2_sig V_ff)));
                        rewrite (proj2_sig v) (proj2_sig v');
                        congr ( _ :>Generator ); exact: Heq)).
  - abstract (split; simpl;
      [ intros G G' g G'' g' V_ff;
        unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=(intersecViews (intersecViews (projT1 (sval V_ff)) g) g'));
        [ exact: views_identity_arrow
        | exact: intersecViews_composition_arrow
        | abstract (intros; move; reflexivity) ]
      | intros G V_ff; destruct V_ff as [V_ff ?];
        unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=(projT1 V_ff));
        [ exact: views_identity_arrow
        | exact: intersecViews_identity_arrow
        | abstract (intros; move; reflexivity) ] ]).
Defined.

Definition morViews_Yoneda01_ViewedFunctor : forall (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                    Yoneda01_functor Yoneda01 }) (G G' : obGenerator) (g : 'Generator( G' ~> G ))
    (ff : Yoneda00_ViewedFunctor Yoneda01_F G),
    { Z_prop : morViews (intersecViews (projT1 (sval ff)) g)
                        (projT1 (sval (sval (Yoneda01_ViewedFunctor Yoneda01_F) G G' g ff)))
    | forall H0, (projT2 (sval ff)) H0 \o sval (Yoneda10_intersecViews_toViews (projT1 (sval ff)) g) H0
                 =1 (projT2 (sval (sval (Yoneda01_ViewedFunctor Yoneda01_F) G G' g ff))) H0 \o sval Z_prop H0 }.
Proof.
  intros; exists (views_identity_arrow _ ).
  abstract (intros; move; simpl; intros; reflexivity).
Defined.

Definition views_at_functor_prop
           (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : {Yoneda01
               : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' |
               Yoneda01_functor Yoneda01})
    (V_ : forall G : obGenerator, Yoneda00_F G -> obViews G) :=
  forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
     morViews (V_ G' (sval Yoneda01_F G G' g f)) (intersecViews (V_ G f) g).

Definition sval_  (Yoneda00_F : obGenerator -> Type)
           (V_ : forall G : obGenerator, Yoneda00_F G -> { V : obViews G | obViews_prop V} ) :
  ( forall G : obGenerator, Yoneda00_F G -> obViews G) .
  intros G f. exact (sval (V_ G f)).
Defined.

End Senses_obCoMod.

Inductive obCoMod : forall Yoneda00 : obGenerator -> Type,
 { Yoneda01 : ( forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00 G -> Yoneda00 G' ) |
   Yoneda01_functor Yoneda01 } -> Type := 

| View : forall G : obGenerator, @obCoMod (Yoneda00_View G) (Yoneda01_View G) 

| ViewingFunctor : forall Yoneda00_F Yoneda01_F,
    @obCoMod Yoneda00_F Yoneda01_F ->
    forall (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
      views_at_functor_prop Yoneda01_F (sval_ V_) ->
      @obCoMod Yoneda00_F Yoneda01_F

| ViewedFunctor : forall Yoneda00_F Yoneda01_F,
    @obCoMod Yoneda00_F Yoneda01_F ->
    @obCoMod (Yoneda00_ViewedFunctor Yoneda01_F) (Yoneda01_ViewedFunctor Yoneda01_F) .

Section Senses_morCoMod.

Lemma Yoneda10_PolyCoMod :
  forall Yoneda00_F1 Yoneda01_F1 Yoneda00_F2 Yoneda01_F2
   (Yoneda10_ff_ : {Yoneda10 : forall A : obGenerator, Yoneda00_F1 A -> Yoneda00_F2 A |
                     Yoneda10_natural Yoneda01_F1 Yoneda01_F2 Yoneda10 })
    Yoneda00_F2' Yoneda01_F2'
  (Yoneda10_ff' : {Yoneda10 : forall A : obGenerator, Yoneda00_F2 A -> Yoneda00_F2' A |
                   Yoneda10_natural Yoneda01_F2 Yoneda01_F2' Yoneda10}),
    {Yoneda10 : ( forall A : obGenerator, Yoneda00_F1 A -> Yoneda00_F2' A ) |
     Yoneda10_natural Yoneda01_F1 Yoneda01_F2' Yoneda10}.
Proof.
  intros. exists (fun A => (proj1_sig Yoneda10_ff') A \o (proj1_sig Yoneda10_ff_) A ).
  abstract (intros; move; intros; simpl; rewrite (proj2_sig Yoneda10_ff')
                                            (proj2_sig Yoneda10_ff_); reflexivity).
Defined.

Lemma Yoneda10_UnitCoMod :
  forall Yoneda00_F Yoneda01_F,
    {Yoneda10 : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_F A ) |
     Yoneda10_natural Yoneda01_F Yoneda01_F Yoneda10 } .
Proof.
  intros. exists (fun A => id).
  abstract (intros; move; intros; reflexivity).
Defined.

Lemma Yoneda10_View1
(G H : obGenerator)
(g : 'Generator( H ~> G )) :
 {Yoneda10 : forall G0 : obGenerator, Yoneda00_View H G0 -> Yoneda00_View G G0 |
  Yoneda10_natural (Yoneda01_View H) (Yoneda01_View G) Yoneda10}.
Proof.
  exists (polyGenerator g).
  abstract (move; intros; apply: polyGenerator_morphism).
Defined.

Lemma Yoneda10_ViewedFunctor1 :
  forall Yoneda00_F Yoneda01_F Yoneda00_E Yoneda01_E 
    (Yoneda10_ee : {Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G |
                Yoneda10_natural Yoneda01_F Yoneda01_E Yoneda10}),
    {Yoneda10 : forall G : obGenerator, Yoneda00_ViewedFunctor Yoneda01_F G ->
                                   Yoneda00_ViewedFunctor Yoneda01_E G |
     Yoneda10_natural (Yoneda01_ViewedFunctor Yoneda01_F)
                      (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10}.
Proof.
  intros. unshelve eexists.
  - intros G ff_ . unshelve eexists.
    + exists (projT1 (sval ff_)). exact: (fun H => (sval Yoneda10_ee H) \o (projT2 (sval ff_) H)).
    + abstract(simpl; split; first (by exact: (proj1 (proj2_sig ff_)));
               split; first (by move; intros; rewrite (proj2_sig Yoneda10_ee);
                             rewrite (proj1 (proj2 (proj2_sig ff_))); reflexivity);
               last (by intros H v v' Heq; congr (sval Yoneda10_ee H);
                     apply: (proj2 (proj2 (proj2_sig ff_))); exact: Heq)).
  - abstract ( move; simpl; intros G G' g V_ff;
              unshelve eapply Yoneda00_ViewedFunctor_quotient
              with (W:= (intersecViews (projT1 (sval V_ff)) g));
              [ exact: views_identity_arrow
              | exact: views_identity_arrow
              | abstract (intros; move; reflexivity) ] ). 
Defined.

Lemma Yoneda10_UnitViewedFunctor :
forall Yoneda00_F Yoneda01_F Yoneda00_E Yoneda01_E 
(Yoneda10_ff :
{Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_F G |
Yoneda10_natural Yoneda01_E Yoneda01_F Yoneda10}),
{Yoneda10 : forall G : obGenerator,
    Yoneda00_E G -> Yoneda00_ViewedFunctor Yoneda01_F G |
  Yoneda10_natural Yoneda01_E (Yoneda01_ViewedFunctor Yoneda01_F) Yoneda10}.
Proof.
  intros. unshelve eexists.
  - intros G e. unshelve eexists.
    + exists ( unitViews (@unitGenerator G)). intros H g. exact: (sval Yoneda01_F _ _ g (sval Yoneda10_ff _ e)).
    + abstract (simpl; split; first (by exact: unitViewsP);
                split; first (by move; intros; exact: (proj1 (proj2_sig Yoneda01_F)));
                last (by intros H v v' (* Heq*);
                      do 2 rewrite -unitGenerator_polyGenerator; move -> (* Heq *); reflexivity)).
  - abstract (move; simpl; intros G G' g V_ff;
              unshelve eapply Yoneda00_ViewedFunctor_quotient
              with (W:= (unitViews unitGenerator));
              [ exact: intersecViews_unitViews
              | exact: views_identity_arrow
              | abstract (intros; move; simpl; intros;
                          rewrite -(proj2_sig Yoneda10_ff)
                          -(proj1 (proj2_sig Yoneda01_F)); reflexivity) ]).
    (*  intersecViewsP (unitViewsP unitGenerator) g == unitViews unitGenerator
        F (v' o> g) (ff f)   =show   F v' (ff (E (g) (f)))  (..=ffnat F v' (F (g) (ff f)) Ffunc=... )
     *)
Defined.
  
Definition element_to_polyelement : forall Yoneda00_F Yoneda01_F G,
    Yoneda00_F G ->
         { Yoneda10 : ( forall G' : obGenerator, Yoneda00_View G G' -> Yoneda00_F G' ) |
           Yoneda10_natural (Yoneda01_View G) Yoneda01_F Yoneda10 } .
Proof.
  intros ? ? G f. unshelve eexists. 
  apply: (fun G' g => (sval Yoneda01_F G G') g f) . 
  abstract (move; simpl; intros G' G'' g' g;
            rewrite -(proj1 (proj2_sig Yoneda01_F)); reflexivity).
Defined.

Definition polyelement_to_element : forall Yoneda00_F Yoneda01_F G,
    { Yoneda10 : ( forall G' : obGenerator, Yoneda00_View G G' -> Yoneda00_F G' ) |
      Yoneda10_natural (Yoneda01_View G) Yoneda01_F Yoneda10 } ->
    Yoneda00_F G .
Proof.
  intros ? ? G ff.
  exact: (sval ff G (@unitGenerator G)).
Defined.

Lemma element_to_polyelement_to_element : forall Yoneda00_F Yoneda01_F G
                                            (f : Yoneda00_F G),
    polyelement_to_element (element_to_polyelement Yoneda01_F f) = f .
Proof.
  intros. simpl. rewrite -(proj2 (proj2_sig Yoneda01_F)). reflexivity.
Qed. 

Lemma polyelement_to_element_to_polyelement : forall Yoneda00_F Yoneda01_F G
    (ff: { Yoneda10 : ( forall G' : obGenerator, Yoneda00_View G G' -> Yoneda00_F G' ) |
           Yoneda10_natural (Yoneda01_View G) Yoneda01_F Yoneda10 }),
    forall G' g, sval (element_to_polyelement Yoneda01_F (polyelement_to_element ff)) G' g = sval ff G' g.
Proof.
  intros. rewrite /polyelement_to_element. simpl. rewrite (proj2_sig ff). simpl.
  rewrite -unitGenerator_polyGenerator. reflexivity.
Qed.

(**TODO: SHOW BIJECTION *)

Lemma Yoneda10_PolyElement Yoneda00_F Yoneda01_F
      (V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V})
      (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
      (v : 'Generator( H ~> G | sval (V_ G f) )) :
  {Yoneda10 : forall G : obGenerator, Yoneda00_View H G -> Yoneda00_F G |
   Yoneda10_natural (Yoneda01_View H) Yoneda01_F Yoneda10} .
Proof.
  exact: (element_to_polyelement _ (sval Yoneda01_F _ _ ( v :>Generator ) f )).
Defined.

Lemma Yoneda10_PolyTransf :
  forall Yoneda00_F Yoneda01_F (V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V})
    (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_))
    Yoneda00_E Yoneda01_E
    (Yoneda10_ee_ :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
         'Generator( H ~> G | sval (V_ G f) ) ->
         {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
          Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
    (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v)))
    (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
           polyelement_to_element (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v'))
    (Yoneda10_ee_toView :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
    {Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
     Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10}.
Proof.
  intros. unshelve eexists.
  - intros G f. unshelve eexists.
    + eexists. (* exists (sval (@V_ G f)).*)
      exact: (fun H v => (polyelement_to_element (Yoneda10_ee_ G f H v))).
    + abstract (simpl; split;
                first (by exact: (proj2_sig (@V_ G f)));
                split; first (by move; intros;
                              exact: ((Yoneda10_ee_natural G f )));
                last by intros H v v' Heq; apply: Yoneda10_ee_toView; exact: Heq).
  - move; simpl; intros G G' g f;
      unshelve eapply Yoneda00_ViewedFunctor_quotient
      with (W:= (sval (V_ G' (sval Yoneda01_F G G' g f)))); 
      [ exact: V_prop
      | exact: views_identity_arrow
      | abstract (intros H; move; simpl; intros v';
                  exact: Yoneda10_ee_morphism) ] .
    (*MEMO: (1) add assumption on the viewed-functor (the views at the functor) that
       V_(g o>f) <= pullback of V_(f) along g , which is same as
       sigma of V_(g o> f) along g <= V_(f)
       (2) add assumption that the sections ee_ hold
       v' |=> ee_(f) (v' o> g) is 
       v' |=> ee_(g o> f) v'         

f
|--------->
v |- mymap_(f) v
|--------->>
v' |- mymap_(f) (v' o> g)
---------------------

f
|---------->
g o> f
|---------->
v' |- mymap_(g o> f) v'
 *)
Defined.
    
End Senses_morCoMod.

Reserved Notation "''CoMod' ( E ~> F @ Yoneda10 )"
         (at level 0, format "''CoMod' (  E  ~>  F  @  Yoneda10  )").

Inductive morCoMod : forall Yoneda00_E Yoneda01_E,
    @obCoMod Yoneda00_E Yoneda01_E ->
    forall Yoneda00_F Yoneda01_F,
      @obCoMod Yoneda00_F Yoneda01_F ->
      { Yoneda10 : ( forall G : obGenerator, Yoneda00_E G -> Yoneda00_F G ) |
                   Yoneda10_natural Yoneda01_E Yoneda01_F Yoneda10 } -> Type :=

(** -----cuts to be eliminated----- **)

| PolyCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
                Yoneda10_ff' , 'CoMod( F' ~> F @ Yoneda10_ff' ) ->
            forall Yoneda00_F'' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F'' Yoneda01_F''),
            forall Yoneda10_ff_ , 'CoMod( F'' ~> F' @ Yoneda10_ff_ ) ->
              'CoMod( F'' ~> F @ Yoneda10_PolyCoMod Yoneda10_ff_ Yoneda10_ff' )
  
(** ----solution morphisms---- **)

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    'CoMod( F ~> F @ Yoneda10_UnitCoMod Yoneda01_F )

| View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    'CoMod( View H ~> View G @ Yoneda10_View1 g)

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee (ee : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee )),
      'CoMod( ViewedFunctor F ~> ViewedFunctor (ViewingFunctor E U_prop) @ Yoneda10_ViewedFunctor1 Yoneda10_ee )

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                             (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                             (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )),
      'CoMod( E ~> ViewedFunctor (ViewingFunctor F V_prop) @ Yoneda10_UnitViewedFunctor Yoneda10_ff )

(** PolyElemant(s) because internalize/poly the element , or PolyElement or injection/section *)              
| PolyElement : (* memo that cannot yet grammatically distinguish whether any f: Yoneda00_View G H is come from some ( _ :>Generator) , therefore solution is this extra constructor PolyElement ; also therefore such can cancel PolyTransf instead of evaluate as for PolyElement , also shall separate grammatical for touching this many/family/cover-arrows at once ?  *)
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),
      'CoMod( View H ~> ViewingFunctor F V_prop @ Yoneda10_PolyElement Yoneda01_F v) 

(** PolyTransf because internalize the indexing (F) , or CoLimitator or Copairing *)
| PolyTransf : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                      (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
               forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
              Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10} )
    (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v)))
    (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
           polyelement_to_element (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v'))
    (Yoneda10_ee_toView :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
       (**memo: similar as graph of elements of G viewed through V *)
      ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
               (v : 'Generator( H ~> G | sval (V_ G f) )),
          'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) ) ->
      'CoMod( ViewingFunctor F V_prop ~> ViewedFunctor (ViewingFunctor E U_prop) @ Yoneda10_PolyTransf Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView )

where "''CoMod' ( F' ~> F @ Yoneda10 )" :=
        (@morCoMod _ _ F' _ _ F Yoneda10) : poly_scope.

Notation "''CoMod' ( F' ~> F )" := (@morCoMod _ _ F' _ _ F _)
       (at level 0, only parsing, format "''CoMod' (  F'  ~>  F  )") : poly_scope.

Notation "ff_ o>CoMod ff'" := (@PolyCoMod _ _ _ _ _ _ _ ff' _ _ _ _ ff_)
               (at level 40 , ff' at next level , left associativity) : poly_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ F)
                                 (at level 10, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _) (at level 0) : poly_scope.

Notation "''View1' g" := (@View1 _ _ g)
                   (at level 10, g at next level) : poly_scope.

Notation "''ViewedFunctor1' ee" := (@ViewedFunctor1 _ _ _ _ _ _ _ _ _ ee)
                   (at level 10, ee at next level) : poly_scope.

Notation "ff o>CoMod 'UnitViewedFunctor" := (@UnitViewedFunctor _ _ _ _ _ _ _ _ _ ff  )
                  (at level 4, right associativity) : poly_scope.

Notation "''PolyElement' F V_prop v" := (@PolyElement _ _ F _ V_prop _ _ _ v)
                           (at level 10, F , V_prop , v at next level) : poly_scope.

Notation "[[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]]" :=
  (@PolyTransf _ _ F _ V_prop _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView ee_ )
    (at level 4, F , V_prop , Yoneda10_ee_natural, Yoneda10_ee_morphism, Yoneda10_ee_toView at next level ,
     format "[[  ee_  @  F  ,  V_prop  ,  Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_toView  ]]" ) : poly_scope.

Notation "[[ ee_ @ F , V_prop ]]" :=
  (@PolyTransf _ _ F _ V_prop _ _ _ _ _ _ _ _ _ ee_ )
    (at level 4, F , V_prop at next level ,
     format "[[  ee_  @  F  ,  V_prop  ]]" ) : poly_scope.

Module Senses_ViewedFunctor.

Notation "<{ G' ; v ; w }>" := (existT _ G' (existT _ v w))
                                (at level 0, format "<{  G'  ;  v  ;  w  }>").

Local Arguments Yoneda10_PolyElement : clear implicits.

Lemma Vsum_ :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),

    forall projT1_sval_polyelement_to_element_Yoneda10_ee_ :
          ( forall G f H, 'Generator( H ~> G | sval (V_ G f) ) -> obViews H ),
    forall proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
    forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
               obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v),

    forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V} .
Proof.
  intros until G. intros f.
  exists (@sumViews _ (sval (V_ G f)) (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f)).
  refine (@sumViewsP _ _ _ (proj2_sig (V_ G f)) (proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ G f) ) .
Defined.

Lemma Yoneda10_ee_morphism_prop :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
         (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let projT2_sval_polyelement_to_element_Yoneda10_ee_ : (forall G f H v H', 'Generator( H' ~> H | (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v) ) -> Yoneda00_E H')
        := (fun G f H v => (projT2 (sval (Yoneda10_ee_ G f H v)))) in
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
          (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
          (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')),
    forall G G' g f H v', { Yoneda10_ee_morphism_prop : morViews
  (projT1_sval_polyelement_to_element_Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')
  (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) |
  forall H', (projT2_sval_polyelement_to_element_Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v') H'
    =1 (projT2_sval_polyelement_to_element_Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) H'
       \o sval Yoneda10_ee_morphism_prop H' } .
Proof.
  abstract (intros; apply: Yoneda00_ViewedFunctor_quotient_rev;
            symmetry; exact: Yoneda10_ee_morphism).
Qed.

Lemma Yoneda10_ee_toView_prop :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let projT2_sval_polyelement_to_element_Yoneda10_ee_ : (forall G f H v H', 'Generator( H' ~> H | (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v) ) -> Yoneda00_E H')
        := (fun G f H v => (projT2 (sval (Yoneda10_ee_ G f H v)))) in
    forall (Yoneda10_ee_toView :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_ee_ G f H v)
               =  (Yoneda10_ee_ G f H v')),
  forall G f H v v', ((v :>Generator) = (v' :>Generator)) ->
 { Yoneda10_ee_toView_prop : morViews
              (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)
              (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v') |
   ( forall H0, (projT2_sval_polyelement_to_element_Yoneda10_ee_ G f H v) H0
                =1 ( (projT2_sval_polyelement_to_element_Yoneda10_ee_ G f H v') H0 \o sval Yoneda10_ee_toView_prop H0 ) ) }.
Proof.
   abstract (intros until G; intros f H v v' Heq; apply: Yoneda00_ViewedFunctor_quotient_rev;
             exact: (Yoneda10_ee_toView G f H v v' Heq)).
Qed.

Lemma Yoneda10_ee_natural_prop :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let projT2_sval_polyelement_to_element_Yoneda10_ee_ : (forall G f H v H', 'Generator( H' ~> H | (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v) ) -> Yoneda00_E H')
        := (fun G f H v => (projT2 (sval (Yoneda10_ee_ G f H v)))) in
    forall (Yoneda10_ee_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             (Yoneda10_ee_ G f H v))),
    forall G (f : Yoneda00_F G) H H' (h : 'Generator( H' ~> H )) (v : 'Generator( H ~> G | sval (V_ G f) )), 
    { Yoneda10_ee_natural_prop : morViews
                 (projT1 (sval (sval (Yoneda01_ViewedFunctor Yoneda01_E) _ _ h (Yoneda10_ee_ G f _ v) )))
                 (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H' (h o>Generator v | sval (V_ G f))) |
      ( forall H0, (projT2 (sval (sval (Yoneda01_ViewedFunctor Yoneda01_E) _ _ h (Yoneda10_ee_ G f _ v)))) H0
                   =1 ( (projT2_sval_polyelement_to_element_Yoneda10_ee_ G f H' (h o>Generatorv | sval (V_ G f))) H0 \o sval Yoneda10_ee_natural_prop H0 ) ) } .
Proof.
   Time abstract (intros; apply: Yoneda00_ViewedFunctor_quotient_rev;
                    exact: Yoneda10_ee_natural).
Qed.

Lemma Vsum_prop :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
         (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
          (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
          (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')),

    views_at_functor_prop Yoneda01_F (sval_ (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_)) .
Proof.
  intros; move; intros G G' g f; simpl.
  unshelve eexists.
  { (** Vsum_prop ; sval morViews *) intros H' Hv'w'.
    set H : obGenerator := projT1 (projT1 Hv'w').
    set v'  : 'Generator( H ~> _ | sval (V_ G' (sval Yoneda01_F G G' g f)) )
      := projT2 (projT1 Hv'w').
    set w' : 'Generator( H' ~> _ | projT1_sval_polyelement_to_element_Yoneda10_ee_ G'
                          (sval Yoneda01_F G G' g f) H v' )
      := projT2 Hv'w'.
    set v : 'Generator( H ~> _ | intersecViews (sval_ V_ f) g )
      := (sval (V_prop G G' g f) H v').
    set w  : 'Generator( H' ~> _ | projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H (sval v).1 )
      := (sval (sval (Yoneda10_ee_morphism_prop Yoneda10_ee_morphism v')) H' w'). 
    unshelve eexists.
    { (** Vsum_prop ; sval morViews  ; Yoneda00_intersecViews *)
      exact: ((existT _ (existT _ H (fst (sval v))) w) , ( (w :>Generator) o>Generator (v :>Generator) )).
    }
    clear. move: H v' w' v w. clear. simpl. intros.
    Time abstract(rewrite [in LHS](proj2_sig v); rewrite [LHS] /= ; rewrite [LHS]polyGenerator_morphism;  reflexivity).
  }
Axiom admit : forall (T : Type), T.
intros; apply: admit.
(**  Time clear; simpl; split.
  - Time abstract ( move; intros H' H0 h wv;
               apply ax1_Yoneda00_intersecViews;
               congr pair;
               [ simpl;
                 rewrite [in LHS ](proj1 (proj2_sig (sval (Yoneda10_ee_morphism_prop Yoneda10_ee_morphism (projT2 (projT1 wv)))))); reflexivity
               | simpl;
                 rewrite -[in RHS ](proj1 (proj2_sig (sval (Yoneda10_ee_morphism_prop Yoneda10_ee_morphism (projT2 (projT1 wv))))));
                 rewrite -[in RHS](proj2_sig (Yoneda10_Views_toView _)) [RHS]/= ;
                 rewrite -[in RHS]polyGenerator_morphism; reflexivity ] ).
  - Time abstract (simpl; intros H' wv;
              rewrite [X in _ o>Generator X = _ ](proj2 (proj2_sig (V_prop _ _ _ _ )));
              rewrite [X in X o>Generator _ = _ ](proj2 (proj2_sig (sval (Yoneda10_ee_morphism_prop Yoneda10_ee_morphism _ ))));
              reflexivity). (* TIME 2600s *) **)
Time Defined.

Lemma transf_sum :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    ( forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
             (wv : 'Generator( H' ~> G | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )), Yoneda00_E H' ) .
Proof.
  intros; refine ( projT2 (sval (Yoneda10_ee_
                                   G f (projT1 (projT1 wv)) (projT2 (projT1 wv)))) H'  (projT2 wv) ).
Defined.

(*memo: uniqueness is by computationally *)
Lemma transf_sum_unique :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall transf_sum' : ( forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
             (wv : 'Generator( H' ~> G | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )), Yoneda00_E H' ),
    (forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
           (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) ))
           (w : 'Generator( H' ~> H | projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v )),
      transf_sum' G f H' (existT _ (existT _ H v) w) = ( projT2 (sval (Yoneda10_ee_ G f H v)) H' w ) )->
 forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
        (wv : 'Generator( H' ~> G | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )),      
   transf_sum' G f H' wv = transf_sum wv .
Proof.
  intros until transf_sum'; intros Heq; intros; destruct wv as [ [H v] w]; rewrite Heq; reflexivity.
Qed.

Lemma transf_sum_natural :
  forall Yoneda00_F 
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    
    forall (G : obGenerator) (f : Yoneda00_F G),
      Yoneda10_natural (Yoneda01_Views (sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_  f))) Yoneda01_E
                       (fun (H : obGenerator) (wv : 'Generator( H ~> _ | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )) => transf_sum wv ).
Proof.
  intros; move; simpl; intros H' H0 h wv.
  rewrite [LHS](proj1 (proj2 (proj2_sig ((Yoneda10_ee_ G f _ _ ))))).
  reflexivity.
Qed.

Lemma transf_sum_morphism :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
         (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
          (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
          (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')),
  forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G) 
         (H : obGenerator) (v' : 'Generator( H ~> _ | (sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ (sval Yoneda01_F G G' g f))) )),
    (transf_sum (sval (sval (Vsum_prop Yoneda10_ee_morphism g f) H v')).1)
    = (transf_sum v').
(*    (@transf_sum _ _ _ _ Yoneda10_ee_ G f H
          (sval (sval (@Vsum_prop _ _ _ _ _ _ _ Yoneda10_ee_morphism G G' g f) H v')).1) =
    (@transf_sum _ _ _ _ Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v'). *)
Proof. 
  clear; intros G G' g f H' wv;
  symmetry; exact: (proj2_sig (Yoneda10_ee_morphism_prop Yoneda10_ee_morphism _)).
Qed.

Lemma transf_sum_toView :
  forall Yoneda00_F
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall (Yoneda10_ee_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             (Yoneda10_ee_ G f H v))),
    forall (Yoneda10_ee_toView :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_ee_ G f H v)
               =  (Yoneda10_ee_ G f H v')),
    forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
    (wv wv_' : 'Generator( H' ~> _ | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )),
  wv :>Generator = wv_' :>Generator ->
  (transf_sum (* Yoneda10_ee_  G f H' *) wv)
  = (transf_sum (* Yoneda10_ee_ G f H' *) wv_').
Admitted. (**
Proof.
  intros until wv_' ; intros Heq.
  rewrite /transf_sum.
  Time rewrite [in LHS](proj2_sig (Yoneda10_intersecViews_toViews_unitGenerator (projT2 wv) )).
  Time rewrite [LHS](proj2_sig (morViews_Yoneda01_ViewedFunctor _ _)).
  rewrite [in RHS](proj2_sig (Yoneda10_intersecViews_toViews_unitGenerator (projT2 wv_') )).
  Time rewrite [RHS](proj2_sig (morViews_Yoneda01_ViewedFunctor (projT2 wv_' :>Generator) (Yoneda10_ee_ G f (projT1 (projT1 wv_')) (projT2 (projT1 wv_'))) )).

  Time rewrite [LHS](proj2_sig (@Yoneda10_ee_natural_prop _ _ _ _ _ Yoneda10_ee_natural G f _ _ (projT2 wv :>Generator) (projT2 (projT1 wv)))). rewrite [LHS]/=. 
  rewrite [RHS](proj2_sig (@Yoneda10_ee_natural_prop  _ _ _ _ _ Yoneda10_ee_natural G f _ _ (projT2 wv_' :>Generator) (projT2 (projT1 wv_')))). rewrite [RHS]/=. 

  Time set w_v := (((_ :>Generator) o>Generator _ | _ ) in LHS). 
  set w'_v' := (((_ :>Generator) o>Generator _ | _ ) in RHS). 
  Time have Heq_toView : ( w_v :>Generator ) = ( w'_v' :>Generator) by
      (do 2 rewrite -(proj2_sig (Yoneda10_Views_toView _ )); exact: Heq).
  Time rewrite [LHS](proj2_sig (@Yoneda10_ee_toView_prop _ _ _ _ _ Yoneda10_ee_toView _ _ _ _ _ Heq_toView)) [LHS]/= . clear Heq.
  Time apply: (proj2 (proj2 (proj2_sig (Yoneda10_ee_ G f H' w'_v')))).
  Time rewrite [LHS](proj2 (proj2_sig (sval (@Yoneda10_ee_toView_prop _ _ _ _ _ Yoneda10_ee_toView _ _ _ _ _ _ )))).
  Time do 2 rewrite (proj2 (proj2_sig (sval (@Yoneda10_ee_natural_prop _ _ _ _ _ Yoneda10_ee_natural _ _ _ _ _ _ )))).
  Time simpl. (* unit = unit *) reflexivity.
Time Qed. (* /!\ TIME QED  693s *) **)

Lemma transf_sum_polytransf :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
         (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
          (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
          (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')),
    forall (Yoneda10_ee_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             (Yoneda10_ee_ G f H v))),
    forall (Yoneda10_ee_toView :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_ee_ G f H v)
               =  (Yoneda10_ee_ G f H v')),
     { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
       Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10 } .
Proof.
  intros; set element_to_polyelement_transf_sum :=
    ( fun (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
          (wv : 'Generator( H' ~> G | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )) => element_to_polyelement Yoneda01_E (transf_sum wv) ).

  apply (@ Yoneda10_PolyTransf Yoneda00_F Yoneda01_F (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_) (Vsum_prop Yoneda10_ee_morphism) Yoneda00_E Yoneda01_E element_to_polyelement_transf_sum).
  (* transf_sum_natural *)
  intros; move; intros; do 2 rewrite element_to_polyelement_to_element;
    exact: transf_sum_natural.
  (* transf_sum_morphism *)
  intros; do 2 rewrite element_to_polyelement_to_element. exact: (transf_sum_morphism Yoneda10_ee_morphism).
  (* transf_sum_toView *)
  intros; do 2 rewrite element_to_polyelement_to_element. exact: (transf_sum_toView Yoneda10_ee_natural Yoneda10_ee_toView).
Defined.

Lemma transf_sum_polytransf_unique :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
         (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_polyelement_to_element_Yoneda10_ee_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_ee_ G f H v))) in
    let proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | sval (V_ G f) )),
              obViews_prop (projT1_sval_polyelement_to_element_Yoneda10_ee_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_ee_ G f H v ))) in
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
          (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
          (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')),
    forall (Yoneda10_ee_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             (Yoneda10_ee_ G f H v))),
    forall (Yoneda10_ee_toView :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_ee_ G f H v)
               =  (Yoneda10_ee_ G f H v')),
    forall (transf_sum_polytransf' : { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
                                       Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10 }) ,
    forall (Heq_Views : forall (G : obGenerator) (f : Yoneda00_F G),
                           projT1 (sval (sval transf_sum_polytransf' G f))
                           = sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f)), 
      (forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
              (wv : 'Generator( H' ~> G | sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f) )),
          projT2 (sval (sval transf_sum_polytransf' G f)) H'
                 (sval (sval (views_identity_arrow'' (Heq_Views G f))).2 H' wv)
          = (transf_sum wv)) ->
      forall (G : obGenerator) (f : Yoneda00_F G),
        sval transf_sum_polytransf' G f
        = sval (transf_sum_polytransf Yoneda10_ee_morphism Yoneda10_ee_natural Yoneda10_ee_toView) G f.
Proof.
  intros until Heq_Views; intros Heq; intros.
  unshelve eapply Yoneda00_ViewedFunctor_quotient''
  with (W:= sval (Vsum_ proj1_proj2Sig_polyelement_to_element_Yoneda10_ee_ f)).
  - exact: (sval (views_identity_arrow'' (Heq_Views G f))).2 .
  - exact: ((sval (views_identity_arrow'' Logic.eq_refl)).2) .
  - intros H'; move; intros wv; simpl.
    rewrite -[RHS](proj2 (proj2_sig Yoneda01_E)). exact: Heq.
Qed.


(**TODO: IN OTHER WORDS
 have outer-parameter (the first component of viewed-functor) fixed, then show

 [ W_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) -> obViews H ] (*hypothesis fix : projT1 sval polyelement_to_element Yoneda10_ee_ = W_ *)
    ;  forall (G : obGenerator) (f : Yoneda00_F G),
       forall (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )),
       (* { e : Yoneda00_ViewedFunctor Yoneda01_E H | fst e = W_ } hyp via Yoneda10_ee_  == *)
       forall (H' : obGenerator) (w : 'Generator( H' ~> H | W_ G f H v ))  |-  Yoneda00_E H'
----------------------bij
... ;  forall (G : obGenerator) (f : Yoneda00_F G),
       forall (H' : obGenerator) (vw : 'Generator( H' ~> G | sumViews (W_ G f) ))  |-  Yoneda00_E H'
----------------------bij
... |- ViewingFunctor F (\G f => sumViews (W_ G f)) ~> Yoneda00_E H'

  **)

End Senses_ViewedFunctor.

Section Senses_convCoMod.

Lemma Yoneda10_PolyElement_toView Yoneda00_F Yoneda01_F
      (V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V}) :
  forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
         (v v' : 'Generator( H ~> G | sval (V_ G f) ))
         (Heq : (v :>Generator) = (v' :>Generator)),
  polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v)
  = polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v').
Proof. 
  intros; rewrite /Yoneda10_PolyElement. rewrite Heq. reflexivity.
Qed.
  
Lemma Yoneda10_PolyElement_natural
      Yoneda00_F Yoneda01_F  
      ( V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V} ) :
  forall (G : obGenerator) (f : Yoneda00_F G),
    Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) Yoneda01_F
                     (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                        polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v)).
Proof.
  intros; move; simpl; intros.
  do 2 rewrite [in LHS](proj1 (proj2_sig Yoneda01_F)).
  do 1 rewrite [in RHS](proj1 (proj2_sig Yoneda01_F)).
  rewrite -[in LHS]unitGenerator_polyGenerator.
  rewrite -[in RHS]polyGenerator_unitGenerator.
  rewrite -[in RHS](proj2_sig (Yoneda10_Views_toView (sval (V_ G f)))). reflexivity.
Qed. 

Lemma Yoneda10_PolyElement_morphism
      Yoneda00_F Yoneda01_F  
      ( V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V} )
      (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)) :
 forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) 
    (f : Yoneda00_F G) (H : obGenerator)
    (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
   polyelement_to_element (Yoneda10_PolyElement Yoneda01_F (sval (sval (V_prop G G' g f) H v')).1) =
   polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v') .
Proof.
  intros; congr polyelement_to_element;
    move; simpl; intros. rewrite /Yoneda10_PolyElement. simpl.
  rewrite -[in RHS](proj2 (proj2_sig (V_prop G G' g f))). rewrite [in RHS]/= .
  rewrite [in RHS](proj1 (proj2_sig Yoneda01_F)).
  rewrite [in LHS](proj2_sig (sval (V_prop G G' g f) H v')). rewrite [in LHS]/=.
  reflexivity.
Qed.   

Lemma Yoneda10_PolyTransf_morphism_natural
Yoneda00_F 
(V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V})
Yoneda00_E 
Yoneda01_E 
(Yoneda10_ee_ :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | sval (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_natural :
forall (G : obGenerator) (f : Yoneda00_F G),
Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) Yoneda01_E
  (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
   polyelement_to_element (Yoneda10_ee_ G f H v)))
Yoneda00_E' 
Yoneda01_E' 
(Yoneda10_e'e' :
{Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10}) :
 forall (G : obGenerator) (f : Yoneda00_F G),
  Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) 
    Yoneda01_E'
    (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
     polyelement_to_element ( Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v)
                           Yoneda10_e'e')) .
Proof.
  intros; move; simpl; intros.
  rewrite (proj2_sig Yoneda10_e'e').
  rewrite [in LHS]Yoneda10_ee_natural. reflexivity.
Qed.

Lemma Yoneda10_PolyTransf_morphism_morphism
Yoneda00_F
Yoneda01_F 
(V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V})
(V_prop : views_at_functor_prop Yoneda01_F (sval_ V_))
Yoneda00_E 
Yoneda01_E 
(Yoneda10_ee_ :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | sval (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_morphism :
forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) 
  (f : Yoneda00_F G) (H : obGenerator)
  (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
polyelement_to_element (Yoneda10_ee_ G f H (sval (sval (V_prop G G' g f) H v')).1) =
polyelement_to_element (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v'))
Yoneda00_E' 
Yoneda01_E' 
( Yoneda10_e'e' :
{Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10} ) :
forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) 
    (f : Yoneda00_F G) (H : obGenerator)
    (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
  polyelement_to_element (Yoneda10_PolyCoMod
    (Yoneda10_ee_ G f H (sval (sval (V_prop G G' g f) H v')).1) Yoneda10_e'e') =
  polyelement_to_element (Yoneda10_PolyCoMod (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v')
                                             Yoneda10_e'e').
Proof.
  intros; rewrite /polyelement_to_element /= in Yoneda10_ee_morphism *.
  rewrite Yoneda10_ee_morphism. reflexivity.
Qed.

Lemma Yoneda10_PolyTransf_morphism_toView
      Yoneda00_F
      (Yoneda01_F : {Yoneda01
               : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' |
               Yoneda01_functor Yoneda01})
(V_ : forall G : obGenerator, Yoneda00_F G -> {V : obViews G | obViews_prop V})
Yoneda00_E 
Yoneda01_E 
(Yoneda10_ee_ :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | sval (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_toView :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
  (v v' : 'Generator( H ~> G | sval (V_ G f) )),
v :>Generator = v' :>Generator ->
polyelement_to_element (Yoneda10_ee_ G f H v) =
polyelement_to_element (Yoneda10_ee_ G f H v'))
Yoneda00_E'
Yoneda01_E' 
(Yoneda10_e'e' :
{Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10}) :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
    (v v' : 'Generator( H ~> G | sval (V_ G f) )),
  v :>Generator = v' :>Generator ->
  polyelement_to_element
    (Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v) Yoneda10_e'e') =
  polyelement_to_element
    (Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v') Yoneda10_e'e') .
Proof.
  intros ? ? ? ? ? Heq; simpl. rewrite /polyelement_to_element in Yoneda10_ee_toView.
  rewrite (Yoneda10_ee_toView _ _ _ _ _ Heq). reflexivity.
Qed.
  
End Senses_convCoMod.
  
Reserved Notation "ff0 <~~ ff" (at level 70).

Inductive convCoMod : forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda10_ff ( ff : 'CoMod( E ~> F @ Yoneda10_ff ) ),
    forall Yoneda10_ff0 ( ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 ) ), Prop :=

(**  ----- the total/(multi-step) conversions -----  **)

| convCoMod_Refl :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
      Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) ),
      gg <~~ gg

| convCoMod_Trans :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) ),
    forall Yoneda10_uTrans (uTrans : 'CoMod( F ~> G @ Yoneda10_uTrans ) ),
      ( uTrans <~~ gg ) ->
      forall Yoneda10_gg0 (gg0 : 'CoMod( F ~> G @ Yoneda10_gg0 ) ),
        ( gg0 <~~ uTrans ) -> ( gg0 <~~ gg )

(**  ----- the congruences (recursive) conversions for singleton morphisms -----  **)

| PolyCoMod_cong :
    forall Yoneda00_F Yoneda01_F' (F' : @obCoMod Yoneda00_F Yoneda01_F')
      Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda10_ff' (ff' : 'CoMod( F' ~> F @ Yoneda10_ff' ))
      Yoneda00_F' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F' Yoneda01_F'')
      Yoneda10_ff_ (ff_ : 'CoMod( F'' ~> F' @ Yoneda10_ff_ ))
      Yoneda10_ff_0 (ff_0 : 'CoMod( F'' ~> F' @ Yoneda10_ff_0 ))
      Yoneda10_ff'0 (ff'0 : 'CoMod( F' ~> F @ Yoneda10_ff'0 )),
      ff_0 <~~ ff_ -> ff'0 <~~ ff' -> ( ff_0 o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )
                             
| ViewedFunctor1_cong : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee (ee : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee )),
    forall Yoneda10_ee0 (ee0 : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee0 )),
      ee0 <~~ ee ->
      ( 'ViewedFunctor1 ee0 ) <~~ ( 'ViewedFunctor1 ee )

| UnitViewedFunctor_cong : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                             (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                             (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )),
    forall Yoneda10_ff0 (ff0 : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff0 )),
      ff0 <~~ ff ->
      (ff0 o>CoMod 'UnitViewedFunctor) <~~ (ff o>CoMod 'UnitViewedFunctor)

(** grammatical conversions shall be sense-complete , therefore : **)
| PolyElement_cong :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),
    forall (G0 : obGenerator) (f0 : Yoneda00_F G0) (v0 : 'Generator( H ~> G0 | sval(V_ G0 f0) )),
      (sval Yoneda01_F _ _ ( v0 :>Generator ) f0 ) = (sval Yoneda01_F _ _ ( v :>Generator ) f )
      -> ( 'PolyElement F V_prop v0 ) <~~ ( 'PolyElement F V_prop v )

| PolyTransf_cong : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) V_ V_prop ,
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
      (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
      (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView
      (ee_ : ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
                 (v : 'Generator( H ~> G | sval (V_ G f) )),
                 'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) )),
    forall Yoneda10_ee0_ Yoneda10_ee0_natural Yoneda10_ee0_morphism Yoneda10_ee0_toView ,
    forall (ee0_ : ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
               (v : 'Generator( H ~> G | sval (V_ G f) )),
                  'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee0_ G f H v ) )),
      ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
          (v : 'Generator( H ~> G | sval (V_ G f) )),
          ee0_(G)(f)(H)(v) <~~ ee_(G)(f)(H)(v) ) ->
      [[ ee0_ @ F , V_prop , Yoneda10_ee0_natural , Yoneda10_ee0_morphism , Yoneda10_ee0_toView ]]
        <~~ [[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]]

(** ----- the constant conversions which are used during the PolyCoMod
polymorphism elimination ----- **)

| PolyCoMod'UnitCoMod :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)    
      Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg )),
      gg <~~ ( gg o>CoMod ('UnitCoMod) )

(** not all cases of this conversion are necessary **)
| PolyCoMod_UnitCoMod :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)    
      Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg )),
      gg <~~ ( ('UnitCoMod) o>CoMod gg )

| View1_View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )) (H' : obGenerator) (h : 'Generator( H' ~> H )),
    ('View1 (h o>Generator g))
      <~~ ('View1 h o>CoMod 'View1 g)

| ViewedFunctor1_ViewedFunctor1 :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
      (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
      (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee (ee : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee )),
    forall Yoneda00_D Yoneda01_D (D : @obCoMod Yoneda00_D Yoneda01_D)
      (W_ : (forall (G : obGenerator) (e : Yoneda00_D G), { W : obViews G | obViews_prop W }))
      (W_prop : views_at_functor_prop Yoneda01_D (sval_ W_)),
    forall Yoneda10_dd (dd : 'CoMod( ViewingFunctor E U_prop ~> ViewingFunctor D W_prop @ Yoneda10_dd )),
      ( 'ViewedFunctor1 (ee o>CoMod dd ) )
        <~~ ( 'ViewedFunctor1 ee ) o>CoMod ( 'ViewedFunctor1 dd )

(** a.k.a ViewedFunctor1_UnitViewedFunctor **)
| UnitViewedFunctor_morphismPost : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),                                      
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )),
    forall Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
           (V'_ : (forall (G : obGenerator) (f : Yoneda00_F' G), { V' : obViews G | obViews_prop V' }))
           (V'_prop : views_at_functor_prop Yoneda01_F' (sval_ V'_)),
    forall Yoneda10_f'f' (f'f' : 'CoMod( ViewingFunctor F V_prop ~> ViewingFunctor F' V'_prop @ Yoneda10_f'f' )), 

      ( ( ff o>CoMod f'f' ) o>CoMod 'UnitViewedFunctor )
        <~~ ( ( ff o>CoMod 'UnitViewedFunctor ) o>CoMod ( 'ViewedFunctor1 f'f' )
              : 'CoMod( E ~> ViewedFunctor (ViewingFunctor F' V'_prop) @ _ ) )

(** a.k.a ViewedFunctor1_PolyTransf **)
| PolyTransf_morphism :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
    (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
              Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10} )
      Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView
      (ee_ : ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
                 (v : 'Generator( H ~> G | sval (V_ G f) )),
                 'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) )),
    forall Yoneda00_E' Yoneda01_E' (E' : @obCoMod Yoneda00_E' Yoneda01_E')
           (U'_ : (forall (G : obGenerator) (e' : Yoneda00_E' G), { U' : obViews G | obViews_prop U' }))
           (U'_prop : views_at_functor_prop Yoneda01_E' (sval_ U'_)),
    forall Yoneda10_e'e' (e'e' : 'CoMod( ViewingFunctor E U_prop ~> ViewingFunctor E' U'_prop @ Yoneda10_e'e' )),

        ( [[ ( fun G f H v =>  ee_ G f H v o>CoMod e'e' )
               @ F , V_prop , Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural Yoneda10_e'e' , Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism  Yoneda10_e'e' ,  Yoneda10_PolyTransf_morphism_toView Yoneda01_F Yoneda10_ee_toView  Yoneda10_e'e' ]] )
          <~~  ( [[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]]
                   o>CoMod 'ViewedFunctor1 e'e'
                 : 'CoMod( ViewingFunctor F V_prop ~> ViewedFunctor (ViewingFunctor E' U'_prop) @ _ ) )

(** a.k.a UnitViewedFunctor_PolyCoMod **)
| UnitViewedFunctor_morphismPre : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                             (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                             (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )),
    forall Yoneda00_D Yoneda01_D (D : @obCoMod Yoneda00_D Yoneda01_D),
    forall Yoneda10_ee (ee : 'CoMod( D ~> E @ Yoneda10_ee )),
      ( (ee o>CoMod ff) o>CoMod 'UnitViewedFunctor )
        <~~ ( ee o>CoMod ( ff o>CoMod 'UnitViewedFunctor ) )

| PolyElement_View1 :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),
    forall (H' : obGenerator) (h : 'Generator( H' ~> H )),
      ( 'PolyElement F V_prop ( h o>Generator v | sval(V_ G f) ) )
                   <~~ ( 'View1 h o>CoMod 'PolyElement F V_prop v )

| PolyTransf_PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
    (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
              Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10} )
    Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView
    (ee_ : ( (**memo: similar as graph of elements of G viewed through V *)
        forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
          (v : 'Generator( H ~> G | sval (V_ G f) )),
          'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) )),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),

      ( (ee_ G f H v) o>CoMod 'UnitViewedFunctor )
        <~~ ( ('PolyElement F V_prop v) o>CoMod [[ ee_ @ F , V_prop ,  Yoneda10_ee_natural , Yoneda10_ee_morphism  , Yoneda10_ee_toView ]]
              : 'CoMod( View H ~> ViewedFunctor (ViewingFunctor E U_prop) @ _ ) )

(** ----- the constant conversions which are only for the wanted sense of
viewed-metafunctor-along-views-data grammar ----- **)

| PolyTransf'PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
      (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
        (* problem: how to recognize grammatically such many/family/cover of arrows in 'PolyElement ? *)
        ( 'UnitCoMod o>CoMod 'UnitViewedFunctor )
          <~~  ( [[ PolyElement F V_prop @ F , V_prop , @Yoneda10_PolyElement_natural _ Yoneda01_F V_ , Yoneda10_PolyElement_morphism V_prop , @Yoneda10_PolyElement_toView _ Yoneda01_F V_ ]]
                 : 'CoMod( ViewingFunctor F V_prop ~> ViewedFunctor (ViewingFunctor F V_prop) @ _ ) )

(** ----- the constant symmetrized-conversions which are symmetrized-derivable by
using the finished cut-elimination lemma ----- TODO: COMMENT ALL THIS SECTION
----- **)

(** (**MEMO: commented now so that it non-prevent the degradation lemma *)
| PolyCoMod_morphism :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
      Yoneda10_ff' (ff' : 'CoMod( F' ~> F @ Yoneda10_ff' )),
      forall Yoneda00_F'' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F'' Yoneda01_F'')
        Yoneda10_ff_ (ff_ : 'CoMod( F'' ~> F' @ Yoneda10_ff_ )),
      forall Yoneda00_F''' Yoneda01_F''' (F''' : @obCoMod Yoneda00_F''' Yoneda01_F''')
        Yoneda10_ff__ (ff__ : 'CoMod( F''' ~> F'' @ Yoneda10_ff__ )),
        ((ff__ o>CoMod ff_) o>CoMod ff')
          <~~ (ff__ o>CoMod (ff_ o>CoMod ff'))  **)

where "gg0 <~~ gg" := (@convCoMod _ _ _ _ _ _ _ gg _ gg0) : poly_scope.

Hint Constructors convCoMod.

Lemma convCoMod_sense :
  forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
      forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
      forall Yoneda10_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff )),
      forall Yoneda10_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 )),
        ff0 <~~ ff -> forall G' : obGenerator,
          (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G').
Proof.
  intros until ff0. intros conv_ff.
  elim : Yoneda00_E Yoneda01_E E Yoneda00_F Yoneda01_F F
                    Yoneda10_ff ff Yoneda10_ff0 ff0 / conv_ff .

  (**  ----- the total/(multi-step) conversions -----  **)
  - (* convCoMod_Refl *)  intros. move. intros f. reflexivity.
  - (* convCoMod_Trans *) intros until 1. intros gg_eq .
    intros until 1. intros uTrans_eq.
    intros. move. intros f. rewrite gg_eq uTrans_eq . reflexivity. 

  (**  ----- the congruences (recursive) conversions for singleton morphisms -----  **)
  - (* PolyCoMod_cong *)  intros until 1. intros ff__eq .
    intros ? ff'_eq ? . move. intros f'.
    rewrite /Yoneda10_PolyCoMod /= . rewrite ff__eq ff'_eq. reflexivity.
  - (* ViewedFunctor1_cong *) intros until 1. intros ee_eq . intros; move; intros ff. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:= projT1 (sval ff));
    [ exact: views_identity_arrow
    | exact: views_identity_arrow | ].
    intros; move; simpl; intros; rewrite ee_eq; reflexivity.
  - (* UnitViewedFunctor_cong *)
    intros until 1. intros ff_eq . intros; move; intros e. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=  unitViews unitGenerator);
    [ exact: views_identity_arrow
    | exact: views_identity_arrow | ].
    intros; move; simpl; intros; rewrite ff_eq; reflexivity.
  - (* PolyElement_cong  *)
    intros until 2. intros ? ? ? ? ? ? ? vf_eq . intros; move; intros h. simpl.
    rewrite vf_eq; reflexivity.
  - (* PolyTransf_cong *)
    intros until 2. intros ee_eq . intros; move; intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=  sval (V_ G' f));
    [ exact: views_identity_arrow
    | exact: views_identity_arrow | ].
    intros; move; simpl; intros; rewrite /polyelement_to_element;
      rewrite ee_eq; reflexivity.

  (** ----- the constant conversions which are used during the PolyCoMod
      polymorphism elimination ----- **)
  - (* PolyCoMod'UnitCoMod *) intros; move; intros f; simpl; reflexivity.
  - (* PolyCoMod_UnitCoMod *) intros; move; intros f; simpl; reflexivity.
  - (* View1_View1 *)
    intros; move; simpl; symmetry; exact: polyGenerator_morphism.
  - (* ViewedFunctor1_ViewedFunctor1 *)
    intros; move; intros f_ ; simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:=  projT1 (sval f_));
      [ exact: views_identity_arrow
      | exact: views_identity_arrow | ].
    intros; move; simpl; reflexivity.
  - (* UnitViewedFunctor_morphismPost *)
    intros until 1. intros ? ? ? ? ? Yoneda10_f'f'; intros; move; simpl; intros;
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:=  unitViews unitGenerator);
      [ exact: views_identity_arrow
      | exact: views_identity_arrow | ].
    intros; move; simpl; intros; rewrite (proj2_sig Yoneda10_f'f'); reflexivity.
  - (* PolyTransf_morphism *)
    intros. move. intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (sval (V_ G' f)));
      [ exact: views_identity_arrow
      | exact: views_identity_arrow | ].
    intros H; move; simpl; intros v; reflexivity.
  - (* UnitViewedFunctor_morphismPre *)
    intros. move. intros d. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= unitViews unitGenerator);
      [ exact: views_identity_arrow
      | exact: views_identity_arrow | ].
    intros; move; simpl; reflexivity.
  - (* PolyElement_View1 *)
    intros ? Yoneda01_F; intros; move; simpl; intros.
    rewrite [LHS](proj1 (proj2_sig Yoneda01_F)) [RHS](proj1 (proj2_sig Yoneda01_F)).
    rewrite -[in RHS](proj2_sig (Yoneda10_Views_toView _)) [RHS]/=.
    rewrite [in RHS]polyGenerator_morphism. reflexivity.
  - (* PolyTransf_PolyElement *)
    intros until 2. intros G f H v G'. move. intros h. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (sval (V_ G' (sval Yoneda01_F H G' h (sval Yoneda01_F G H (v :>Generator) f))))); 
      [ exact: views_identity_arrow
      | exact: views_identity_unitViews_arrow
      | ].
    intros H'; move; simpl. 
    rewrite (proj1 (proj2_sig Yoneda01_F)).
    rewrite [h]unitGenerator_polyGenerator. intros v'.
    rewrite -[in RHS](proj2_sig (Yoneda10_ee_ _ _ _ _)).
    rewrite [in RHS](proj1 (proj2_sig Yoneda01_E)).
    rewrite [in RHS](Yoneda10_ee_natural _ _ ).
    rewrite -[in LHS]Yoneda10_ee_morphism.
    apply: Yoneda10_ee_toView. 

    rewrite -[in RHS](proj1 (proj2_sig (Yoneda01_Views _))).
    rewrite -[RHS](proj2_sig (Yoneda10_Views_toView _)) [RHS]/= .
    move: v'. rewrite -unitGenerator_polyGenerator.
    rewrite [_ o>Generator (_ :>Generator)](proj2_sig (Yoneda10_Views_toView _)).
    move : (_ o>Generator _ | _) => hv; clear h v; clear. move => v'.
    rewrite [in LHS](proj2_sig (sval (V_prop _ _ (hv :>Generator) f) _ v')) [LHS]/=.
    rewrite [X in ( X o>Generator _ ) = _ ](proj2 (proj2_sig (V_prop _ _ (hv :>Generator) f))).
    reflexivity.
  - (* PolyTransf'PolyElement *)
    intros. move. intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (sval (V_ G' f))); 
      [ exact: views_identity_arrow
      | exact: views_identity_unitViews_arrow | ].
    intros; move; simpl; intros; rewrite (proj1 (proj2_sig Yoneda01_F));
      rewrite -polyGenerator_unitGenerator; reflexivity.
  (** ----- the constant symmetrized-conversions which are symmetrized-derivable
  by using the finished cut-elimination lemma ----- **)
  (**  - (* PolyCoMod_morphism *) intros. move. intros f.
    reflexivity (* associativity of function composition *). **)
Qed.
      
Module Card'.

Parameter (G1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), obGenerator) .
Parameter (f1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), Yoneda00_F (G1 F V_)).
Parameter (H1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), obGenerator).
Parameter (v1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
              'Generator( (H1 F V_) ~> (G1 F V_) | sval(@V_ (G1 F V_) (f1 F V_)) )).
Parameter (G2 : forall Yoneda00_F Yoneda02_F (F : @obCoMod Yoneda00_F Yoneda02_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), obGenerator) .
Parameter (f2 : forall Yoneda00_F Yoneda02_F (F : @obCoMod Yoneda00_F Yoneda02_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), Yoneda00_F (G2 F V_)).
Parameter (H2 : forall Yoneda00_F Yoneda02_F (F : @obCoMod Yoneda00_F Yoneda02_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })), obGenerator).
Parameter (v2 : forall Yoneda00_F Yoneda02_F (F : @obCoMod Yoneda00_F Yoneda02_F)
                  (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })),
              'Generator( (H2 F V_) ~> (G2 F V_) | sval(@V_ (G2 F V_) (f2 F V_)) )).

Section Section1.

Variables (Yoneda00_F : obGenerator -> Type)
          (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                                         'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                          Yoneda01_functor Yoneda01 }) (F : @obCoMod Yoneda00_F Yoneda01_F)
          (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V })).

Inductive is_elementsUnderView12 : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(@V_ G f) )), Type :=
| Is_elementsUnderView12_elementsUnderView1 : is_elementsUnderView12 (v1 F V_)
| Is_elementsUnderView12_elementsUnderView2 : is_elementsUnderView12 (v2 F V_) .

Axiom is_elementsUnderView12_allP :  forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(@V_ G f) )), is_elementsUnderView12 v.

End Section1. 

End Card'.
      
Notation max m n := ((Nat.add m (Nat.sub n m))%coq_nat).
Arguments Nat.sub : simpl nomatch.
Arguments Nat.add : simpl nomatch.

Fixpoint grade
  Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
     Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
     Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) ) {struct gg} : nat . 
Proof.
  case : Yoneda00_F Yoneda01_F F Yoneda00_G Yoneda01_G G Yoneda10_gg / gg .
  - (* PolyCoMod *) intros ? ? F ? ? F' ? ff' ? ? F'' ? ff_ .
    exact: ( 2 * (S (grade _ _ _ _ _ _ _ ff' + grade _ _ _ _ _ _ _ ff_)%coq_nat ) )%coq_nat .
  - (* UnitCoMod *) intros ? ? F .
    exact: (S ( (* gradeOb F = *) O )).
  - (* View1 *) intros ? ? ? .
    exact: (S O).
  - (* ViewedFunctor1 *) intros ? ?  F ? ? E ? ? ? ee .
    exact: (S (grade _ _ _ _ _ _ _ ee)).
  - (*  UnitViewedFunctor *) intros ? ? F ? ? ? ? E ? ff .
    exact: (S (grade _ _ _ _ _ _ _ ff)).
  - (* PolyElement *) intros ? ? F ? ? ? ? ? ?  .
    exact: (S (S O)).
  - (* PolyTransf *) intros ? ? F V_ ? ? ? E ? ? ? ? ? ? ee .
    exact: (S (S (max (grade _ _ _ _ _ _ _ (@ee (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_)))
                      (grade _ _ _ _ _ _ _ (@ee (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_))) ))).
Defined.

Lemma grade_gt0 :
  forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
     Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
     Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) ),
      ((S O) <= (grade gg))%coq_nat.
Proof.
  intros; case : gg; intros; apply/leP; intros; simpl; auto.
Qed.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'CoMod( _ ~> _ @ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @ _ ) ,
                        gg4 : 'CoMod( _ ~> _ @ _ ) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg3)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod( _ ~> _ @ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @ _ ) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod( _ ~> _ @ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ )  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)
  | [ gg1 : 'CoMod( _ ~> _ @ _ )  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) 
  end.

About Card'.is_elementsUnderView12_allP.

Ltac tac_indexed_all :=
  repeat match goal with
         | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F ,
                 v : 'Generator( ?H ~> ?G | sval (?V_ ?G ?f) )
             |- context [max _ _] ] =>
           destruct (Card'.is_elementsUnderView12_allP F v)
         | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F ,
                 Hgrade : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                             (v : 'Generator( H ~> G | sval (?V_ G f) )),
                              ( _ <= _ )%coq_nat) |- context [max _ _] ] =>
           move: {Hgrade} (Hgrade (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_) )
                          (Hgrade (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_) );
           simpl
         end.

Ltac tac_grade_gt0_indexing :=
match goal with
| [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F ,
        gg1 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
             (v : 'Generator( H ~> G | sval (?V_ G f) )), 'CoMod( _ ~> _ @ _ )),
          gg2 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                   (v : 'Generator( H ~> G | sval (?V_ G f) )), 'CoMod( _ ~> _ @ _ ))
    |- _ ] => move:
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg1 (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_)))
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg1 (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_)))
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg2 (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_)))
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg2 (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_)))
| [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F ,
        gg1 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                 (v : 'Generator( H ~> G | sval (?V_ G f) )), 'CoMod( _ ~> _ @ _ ))
    |- _ ] => move:
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg1 (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_)))
              (@grade_gt0 _ _ _ _ _ _ _
                          (@gg1 (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_)))
end.

Lemma degrade :
  forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
  forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
  forall Yoneda10_ff ( ff : 'CoMod( E ~> F @ Yoneda10_ff ) ),
  forall Yoneda10_ff0 ( ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 ) ),
    ff0 <~~ ff -> ( grade ff0 <= grade ff )%coq_nat .
Proof.
Time intros until ff0; intros red_ff;
  elim : red_ff;
  try solve [intros; simpl;
               try tac_grade_gt0; 
               try tac_grade_gt0_indexing;
               tac_indexed_all;
               intros; abstract Psatz.lia].
Qed. (* /!\ LONG TIME 9s , WAS 13s FOR CORE *)

Ltac tac_degrade H_grade :=
  intuition idtac;
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
           move : (degrade Hred) ; clear Hred
         | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F ,
             Hred : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                       (v : 'Generator( H ~> G | sval (?V_ G f) )),
                        ( _ <~~ _ )%poly) |- _ ] =>
           move: {Hred} (degrade (Hred (Card'.G1 F V_) (Card'.f1 F V_) (Card'.H1 F V_) (Card'.v1 F V_)))
                        (degrade (Hred (Card'.G2 F V_) (Card'.f2 F V_) (Card'.H2 F V_) (Card'.v2 F V_)))
         end;
  move: H_grade; clear; simpl;
  intros; try tac_grade_gt0; try tac_grade_gt0_indexing;
  intros; Psatz.lia.

Module Sol.
Section Section1.
Delimit Scope sol_scope with sol.

Inductive morCoMod : forall Yoneda00_E Yoneda01_E,
    @obCoMod Yoneda00_E Yoneda01_E ->
    forall Yoneda00_F Yoneda01_F,
      @obCoMod Yoneda00_F Yoneda01_F ->
      { Yoneda10 : ( forall G : obGenerator, Yoneda00_E G -> Yoneda00_F G ) |
                   Yoneda10_natural Yoneda01_E Yoneda01_F Yoneda10 } -> Type :=

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    'CoMod( F ~> F @ Yoneda10_UnitCoMod Yoneda01_F )

| View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    'CoMod( View H ~> View G @ Yoneda10_View1 g)

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee (ee : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee )),
      'CoMod( ViewedFunctor F ~> ViewedFunctor (ViewingFunctor E U_prop) @ Yoneda10_ViewedFunctor1 Yoneda10_ee )

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                             (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                             (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )),
      'CoMod( E ~> ViewedFunctor (ViewingFunctor F V_prop) @ Yoneda10_UnitViewedFunctor Yoneda10_ff )

(** PolyElemant(s) because internalize/poly the element , or PolyElement or injection/section *)              
| PolyElement : (* memo that cannot yet grammatically distinguish whether any f: Yoneda00_View G H is come from some ( _ :>Generator) , therefore solution is this extra constructor PolyElement ; also therefore such can cancel PolyTransf instead of evaluate as for PolyElement , also shall separate grammatical for touching this many/family/cover-arrows at once ?  *)
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),
      'CoMod( View H ~> ViewingFunctor F V_prop @ Yoneda10_PolyElement Yoneda01_F v) 

(** PolyTransf because internalize the indexing (F) , or CoLimitator or Copairing *)
| PolyTransf : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                      (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
               forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
              Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10} )
    (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Views (sval (V_ G f))) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | sval (V_ G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v)))
    (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | sval (V_ G' (sval Yoneda01_F G G' g f)) )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval (sval (V_prop G G' g f) H v')))) =
           polyelement_to_element (Yoneda10_ee_ G' (sval Yoneda01_F G G' g f) H v'))
    (Yoneda10_ee_toView :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | sval (V_ G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
       (**memo: similar as graph of elements of G viewed through V *)
      ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
               (v : 'Generator( H ~> G | sval (V_ G f) )),
          'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) ) ->
      'CoMod( ViewingFunctor F V_prop ~> ViewedFunctor (ViewingFunctor E U_prop) @ Yoneda10_PolyTransf Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView )

where "''CoMod' ( F' ~> F @ Yoneda10 )" :=
        (@morCoMod _ _ F' _ _ F Yoneda10) : sol_scope.

End Section1.

Module Export Ex_Notations.
Delimit Scope sol_scope with sol.

Notation "''CoMod' ( F' ~> F @ Yoneda10 )" :=
  (@morCoMod _ _ F' _ _ F Yoneda10) : sol_scope.

Notation "''CoMod' ( F' ~> F )" := (@morCoMod _ _ F' _ _ F _)
       (at level 0, only parsing, format "''CoMod' (  F'  ~>  F  )") : sol_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ F)
                                 (at level 10, only parsing) : sol_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _) (at level 0) : sol_scope.

Notation "''View1' g" := (@View1 _ _ g)
                    (at level 10, g at next level) : sol_scope.

Notation "''ViewedFunctor1' ee" := (@ViewedFunctor1 _ _ _ _ _ _ _ _ _ ee)
                   (at level 10, ee at next level) : sol_scope.

Notation "ff o>CoMod 'UnitViewedFunctor" := (@UnitViewedFunctor _ _ _ _ _ _ _ _ _ ff  )
                  (at level 4, right associativity) : sol_scope.

Notation "''PolyElement' F V_prop v" := (@PolyElement _ _ F _ V_prop _ _ _ v)
                           (at level 10, F , V_prop , v at next level) : sol_scope.

Notation "[[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]]" :=
  (@PolyTransf _ _ F _ V_prop _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView ee_ )
    (at level 4, F , V_prop , Yoneda10_ee_natural, Yoneda10_ee_morphism, Yoneda10_ee_toView at next level ,
     format "[[  ee_  @  F  ,  V_prop  ,  Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_toView  ]]" ) : sol_scope.

Notation "[[ ee_ @ F , V_prop ]]" :=
  (@PolyTransf _ _ F _ V_prop _ _ _ _ _ _ _ _ _ ee_ )
    (at level 4, F , V_prop at next level ,
     format "[[  ee_  @  F  ,  V_prop  ]]" ) : sol_scope.

End Ex_Notations.

Fixpoint toPolyMor
    Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
    Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
    Yoneda10_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff ) %sol ) {struct ff}
      : 'CoMod( E ~> F @ Yoneda10_ff ) %poly .
Proof.
  refine
    match ff with
    | ( @'UnitCoMod F )%sol => ( @'UnitCoMod F )%poly
    | ( 'View1 g )%sol => ( 'View1 g )%poly
    | ( 'ViewedFunctor1 ee )%sol => ( 'ViewedFunctor1 (toPolyMor _ _ _ _ _ _ _ ee) )%poly
    | ( ff o>CoMod 'UnitViewedFunctor )%sol => ( (toPolyMor _ _ _ _ _ _ _ ff) o>CoMod 'UnitViewedFunctor )%poly
    | ( 'PolyElement F V_prop v )%sol => ( 'PolyElement F V_prop v )%poly
    | ( [[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]]%sol )%sol =>
      ( [[ ( fun G f H v => (toPolyMor _ _ _ _ _ _ _  (ee_ G f H v)) )
             @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]] )%poly
    end.
Defined.

(*MEMO: after destructing which function , now filter admissible inputs ... 
  similar as in f(x)  primo destruct f then filter admissible x *)

Module Destruct_codomView.

Inductive morCoMod_codomView
: forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F ),
    forall (G : obGenerator), forall Yoneda10_ff,
        'CoMod( F ~> (View G) @ Yoneda10_ff ) %sol -> Type :=

| UnitCoMod :  forall B : obGenerator, 
    morCoMod_codomView ( ( @'UnitCoMod (View B) )%sol )

|  View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    morCoMod_codomView ( ( 'View1 g )%sol ) .

Lemma morCoMod_codomViewP
  : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) %sol ),
      ltac:( destruct G; [ | refine (unit : Type) .. ];
               refine (morCoMod_codomView gg) ).
Proof.
  intros. case: _ _ F _ _ G Yoneda10_gg / gg.
  - destruct F; [ | intros; exact: tt .. ].
    constructor 1.
  - constructor 2.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
Defined.
  
End Destruct_codomView.
  
Module Destruct_codomViewingFunctor.

Inductive morCoMod_codomViewingFunctor :
   forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E ),
   forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
   forall (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
          (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)), forall Yoneda10_ff,
       'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff ) %sol -> Type :=

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
      morCoMod_codomViewingFunctor ( @'UnitCoMod (ViewingFunctor F V_prop) )%sol

| PolyElement : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
           (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
           (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | sval(V_ G f) )),
      morCoMod_codomViewingFunctor ('PolyElement F V_prop v )%sol .

Lemma morCoMod_codomViewingFunctorP
  : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) %sol ),
      ltac:( destruct G ; [ refine (unit : Type) | | refine (unit : Type) ];
               refine (morCoMod_codomViewingFunctor gg) ).
Proof.
  intros. case: _ _ F _ _ G Yoneda10_gg / gg.
  - destruct F; [ intros; exact: tt | | intros; exact: tt ].
    constructor 1.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
  - constructor 2.
  - intros; exact: tt.
Defined. 

End Destruct_codomViewingFunctor.

Module Destruct_codomViewedFunctor.

Inductive morCoMod_codomViewedFunctor :
   forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E ),
   forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F), forall Yoneda10_ff,
       'CoMod( E ~> ViewedFunctor F @ Yoneda10_ff ) %sol -> Type :=

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
      morCoMod_codomViewedFunctor ( @'UnitCoMod (ViewedFunctor F) )%sol

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall Yoneda10_ee (ee : 'CoMod( F ~> ViewingFunctor E U_prop @ Yoneda10_ee )%sol),
      morCoMod_codomViewedFunctor ( 'ViewedFunctor1 ee )%sol

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                             (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                             (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod( E ~> ViewingFunctor F V_prop @ Yoneda10_ff )%sol),
      morCoMod_codomViewedFunctor ( ff o>CoMod 'UnitViewedFunctor)%sol

| PolyTransf : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                      (V_ : (forall (G : obGenerator) (f : Yoneda00_F G), { V : obViews G | obViews_prop V }))
                      (V_prop : views_at_functor_prop Yoneda01_F (sval_ V_)),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
           (U_ : (forall (G : obGenerator) (e : Yoneda00_E G), { U : obViews G | obViews_prop U }))
           (U_prop : views_at_functor_prop Yoneda01_E (sval_ U_)),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
               forall (H : obGenerator), 'Generator( H ~> G | sval (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
              Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10} )
      Yoneda10_ee_natural Yoneda10_ee_morphism  Yoneda10_ee_toView
      (ee_ : ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
               (v : 'Generator( H ~> G | sval (V_ G f) )),
          'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee_ G f H v ) %sol)),
      morCoMod_codomViewedFunctor ( [[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]] )%sol .

Lemma morCoMod_codomViewedFunctorP
  : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod( F ~> G @ Yoneda10_gg ) %sol ),
      ltac:( destruct G ; [ refine (unit : Type) .. | ];
               refine (morCoMod_codomViewedFunctor gg) ).
Proof.
  intros. case: _ _ F _ _ G Yoneda10_gg / gg.
  - destruct F; [ intros; exact: tt .. | ].
    constructor 1.
  - intros; exact: tt.
  - constructor 2.
  - constructor 3.
  - intros; exact: tt.
  - econstructor 4.
Defined. 

End Destruct_codomViewedFunctor.

End Sol.

Module Resolve.
Export Sol.Ex_Notations.

Ltac tac_reduce := simpl in * ; intuition eauto.

Fixpoint solveCoMod len {struct len} :
  forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
         Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
         Yoneda10_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff )),
  forall grade_ff : (grade ff <= len)%coq_nat,
    { ffSol : { Yoneda10_ffSol : _ & 'CoMod( E ~> F @ Yoneda10_ffSol )%sol}
    | (Sol.toPolyMor (projT2 ffSol)) <~~ ff } .
Proof.
{ (** solveCoMod **)
case : len => [ | len ].

(** len is O **)
- ( move => ? ? E ? ? F ? ff grade_ff ); exfalso;
    clear - grade_ff; abstract tac_degrade grade_ff.

(** len is (S len) **)
- move => ? ? E ? ? F Yoneda10_ff ff; case : _ _ E _ _ F Yoneda10_ff / ff =>
  [ Yoneda00_F Yoneda01_F F Yoneda00_F' Yoneda01_F' F'
               Yoneda10_ff' ff' Yoneda00_F'' Yoneda01_F'' F''
               Yoneda10_ff_ ff_  (** ff_ o>CoMod ff' **)
  | Yoneda00_F Yoneda01_F F (** @'UnitCoMod F **)
  | G H g (** 'View1 g **)
  | Yoneda00_F Yoneda01_F F Yoneda00_E Yoneda01_E E U_ U_prop Yoneda10_ee ee
  (** 'ViewedFunctor1 ee **)
  | Yoneda00_F Yoneda01_F F V_ V_prop Yoneda00_E Yoneda01_E E 
               Yoneda10_ff ff (** ff o>CoMod 'UnitViewedFunctor **)
  | Yoneda00_F Yoneda01_F F V_ V_prop G f H v (** 'PolyElement F V_prop v **)
  | Yoneda00_F Yoneda01_F F V_ V_prop Yoneda00_E Yoneda01_E E U_ U_prop Yoneda10_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView ee_ (** [[ ee_ @ F , V_prop ]] **)
  ] grade_ff .

(** ff is ff_ o>CoMod ff' *)
+ all: cycle 1.

(** ff is @'UnitCoMod F **)
+ unshelve eexists. eexists. refine ( @'UnitCoMod F )%sol.
  clear; abstract exact: convCoMod_Refl.

(** ff is 'View1 g **)
+ unshelve eexists. eexists. refine ( 'View1 g )%sol.
  clear; abstract exact: convCoMod_Refl.

(** ff is 'ViewedFunctor1 ee **)
+ have [:blurb] eeSol_prop :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ee blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ee blurb)))
          (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ee blurb))) eeSol_prop 
  => Yoneda10_eeSol eeSol eeSol_prop .

  unshelve eexists. eexists. refine ( 'ViewedFunctor1 eeSol )%sol.
  move: eeSol_prop; clear; abstract tac_reduce.

(** ff is ff o>CoMod 'UnitViewedFunctor **)
+ have [:blurb] ffSol_prop :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff blurb)))
          (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff blurb))) ffSol_prop 
  => Yoneda10_ffSol ffSol ffSol_prop .

  unshelve eexists. eexists. refine ( ffSol o>CoMod 'UnitViewedFunctor )%sol.
  move: ffSol_prop; clear; abstract tac_reduce.

(** ff is 'PolyElement F V_prop v **)
+ unshelve eexists. eexists. refine ( 'PolyElement F V_prop v )%sol.
  clear; abstract exact: convCoMod_Refl.

(** [[ ee_ @ F , V_prop ]] **)
+ have [:blurb_] eeSol_prop G f H (v : 'Generator( H ~> G | sval (V_ G f) )) :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)));
      first by clear -grade_ff;
      abstract((move => G f H v);
               match goal with
               | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F |- _ ] =>
                 destruct (Card'.is_elementsUnderView12_allP F v)
               end;
               tac_degrade grade_ff).
    
  have @Yoneda10_eeSol_ := (fun G f H v =>
     projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)))).
  have @eeSol_ : (forall G f H v,
   'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_eeSol_ G f H v ) %sol)
    := (fun G f H v => projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                                                (ee_(G)(f)(H)(v)) (blurb_ G f H v)))) .
  have {eeSol_prop}: (forall G f H v,
                         Sol.toPolyMor (eeSol_(G)(f)(H)(v)) <~~ ee_(G)(f)(H)(v)) := eeSol_prop.
  move: Yoneda10_eeSol_ eeSol_ => Yoneda10_eeSol_ eeSol_ eeSol_prop.
  clear solveCoMod.
  unshelve eexists. eexists.
  refine ( @Sol.PolyTransf _ _ F _ V_prop _ _ _ _ _ Yoneda10_eeSol_ _ _ _ eeSol_ ) . 

  (**memo: convCoMod_sense is really necessary here for Yoneda10_eeSol_natural Yoneda10_eeSol_morphism Yoneda10_eeSol_toView  **)
  (* Yoneda10_eeSol_natural *)
  { clear -Yoneda10_ee_natural eeSol_prop;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_prop G f H v)) => eeSol_prop_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_prop_eq; exact: Yoneda10_ee_natural ).
  }
  (* Yoneda10_eeSol_morphism *)
  { clear -Yoneda10_ee_morphism eeSol_prop;
    abstract (move : (fun G f H v => convCoMod_sense (eeSol_prop G f H v))
              => eeSol_prop_eq; intros; move;
                rewrite /= /polyelement_to_element /= ; intros;
                do 2 rewrite -eeSol_prop_eq ; exact: Yoneda10_ee_morphism).
  }
  (* Yoneda10_eeSol_toView *)
  { clear -Yoneda10_ee_toView eeSol_prop;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_prop G f H v)) => eeSol_prop_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_prop_eq; exact: Yoneda10_ee_toView ).
  }

  simpl; move: eeSol_prop; clear; simpl; abstract tac_reduce.
  
(** ff is ff_ o>CoMod ff' *)
+ have [:blurb] ff'Sol_prop :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff' blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff' blurb)))
          (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff' blurb))) ff'Sol_prop 
  => Yoneda10_ff'Sol ff'Sol ff'Sol_prop .
  have [:blurb] ff_Sol_prop :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff_ blurb));
        first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff_ blurb)))
          (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff_ blurb))) ff_Sol_prop 
  => Yoneda10_ff_Sol ff_Sol ff_Sol_prop .

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  **)
  destruct ff'Sol as
      [ Yoneda00_F Yoneda01_F F (** @'UnitCoMod F **)
      | G H g (** 'View1 g **)
      | Yoneda00_F Yoneda01_F F Yoneda00_E Yoneda01_E E U_ U_prop Yoneda10_ee ee
      (** 'ViewedFunctor1 ee **)
      | Yoneda00_F Yoneda01_F F V_ V_prop Yoneda00_E Yoneda01_E E 
               Yoneda10_ff ff (** ff o>CoMod 'UnitViewedFunctor **)
      | Yoneda00_F Yoneda01_F F V_ V_prop G f H v (** 'PolyElement F V_prop v **)
      | Yoneda00_F Yoneda01_F F V_ V_prop Yoneda00_E Yoneda01_E E U_ U_prop Yoneda10_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView ee_ (** [[ ee_ @ F , V_prop ]] **)
      ] .

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod (@'UnitCoMod F)) **)
  * unshelve eexists. eexists. refine (ff_Sol)%sol.
    move:ff_Sol_prop ff'Sol_prop; clear;
      abstract (simpl; intros; eapply convCoMod_Trans with
                               (uTrans := ff_ o>CoMod ('UnitCoMod)); tac_reduce).

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ('View1 g)) **)
  * move:  (Sol.Destruct_codomView.morCoMod_codomViewP ff_Sol) => ff_Sol_codomViewP.
    { destruct ff_Sol_codomViewP as
          [ _G (** @'UnitCoMod (View _G) **)
          | _G _H _g (** 'View1 _g **) ].
        
      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( @'UnitCoMod (View _G) ) o>CoMod ( 'View1 g )) **)
      - unshelve eexists. eexists. refine ('View1 g)%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ('View1 g)); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( 'View1 _g ) o>CoMod ( 'View1 g )) **)
      - unshelve eexists. eexists.
        refine ( 'View1 (_g o>Generator g) )%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                                   (uTrans := ('View1 _g) o>CoMod ('View1 g)); tac_reduce).
    } 

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'ViewedFunctor1 ee )) **)
  * move:  (Sol.Destruct_codomViewedFunctor.morCoMod_codomViewedFunctorP ff_Sol) => ff_Sol_codomViewedFunctorP.
    { destruct ff_Sol_codomViewedFunctorP as
          [ Yoneda00_F Yoneda01_F F (** @'UnitCoMod F **)
          | Yoneda00_F Yoneda01_F F _Yoneda00_E _Yoneda01_E _E U_' _U_prop _Yoneda10_ee _ee
          (** 'ViewedFunctor1 _ee **)
          | Yoneda00_F Yoneda01_F F V_' _V_prop _Yoneda00_E _Yoneda01_E _E 
                       Yoneda10_ff ff (** ff o>CoMod 'UnitViewedFunctor **)
          | Yoneda00_F Yoneda01_F F V_' _V_prop _Yoneda00_E _Yoneda01_E _E U'_ _U_prop Yoneda10_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_toView ee_ (** [[ ee_ @ F , _V_prop ]] **)
          ] .

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is ((@'UnitCoMod F) o>CoMod ('ViewedFunctor1 ee)) **)
      - unshelve eexists. eexists. refine ('ViewedFunctor1 ee)%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ee))); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (('ViewedFunctor1 _ee) o>CoMod ('ViewedFunctor1 ee)) **)
      - have [:blurb] _ee_o_ee_prop :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                                 (Sol.toPolyMor _ee o>CoMod Sol.toPolyMor ee) blurb));
            first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
            abstract tac_degrade grade_ff.
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                                        (Sol.toPolyMor _ee o>CoMod Sol.toPolyMor ee) blurb)))
                (projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                                          (Sol.toPolyMor _ee o>CoMod Sol.toPolyMor ee) blurb))) _ee_o_ee_prop 
        => Yoneda10__ee_o_ee _ee_o_ee _ee_o_ee_prop .

        unshelve eexists. eexists.
        refine ( 'ViewedFunctor1 _ee_o_ee )%sol.
        move: ff_Sol_prop ff'Sol_prop _ee_o_ee_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                        (uTrans := ( 'ViewedFunctor1 (Sol.toPolyMor _ee) ) o>CoMod
                           ( 'ViewedFunctor1 (Sol.toPolyMor ee) )); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( ff o>CoMod 'UnitViewedFunctor ) o>CoMod ('ViewedFunctor1 ee)) **)
      - have [:blurb] ff_o_ee_prop :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                                 (Sol.toPolyMor ff o>CoMod Sol.toPolyMor ee) blurb));
            first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
            abstract tac_degrade grade_ff.
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                                        (Sol.toPolyMor ff o>CoMod Sol.toPolyMor ee) blurb)))
                (projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                                          (Sol.toPolyMor ff o>CoMod Sol.toPolyMor ee) blurb))) ff_o_ee_prop 
        => Yoneda10_ff_o_ee ff_o_ee ff_o_ee_prop .

        unshelve eexists. eexists.
        refine ( ff_o_ee o>CoMod 'UnitViewedFunctor )%sol.
        move: ff_Sol_prop ff'Sol_prop ff_o_ee_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
             (uTrans := ( (Sol.toPolyMor ff) o>CoMod 'UnitViewedFunctor ) o>CoMod
                     ( 'ViewedFunctor1 (Sol.toPolyMor ee) )); tac_reduce).
          
      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( [[ ee_ @ F , _V_prop ]] ) o>CoMod ('ViewedFunctor1 ee)) **)
      - have [:blurb_] ee__o_ee_prop G f H  (v : 'Generator( H ~> G | sval (V_' G f) )) :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ee) (blurb_ G f H v)));
            first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
            abstract((move => G f H v);
                     match goal with
                     | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F |- _ ] =>
                       destruct (Card'.is_elementsUnderView12_allP F v)
                     end;
                     tac_degrade grade_ff).
        have @Yoneda10_ee__o_ee_ := (fun G f H v =>
               projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ee) (blurb_ G f H v)))).
        have @ee__o_ee_ : (forall G f H v,
                      'CoMod( View H ~> ViewingFunctor E U_prop @ Yoneda10_ee__o_ee_ G f H v ) %sol)
          := (fun G f H v => projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ee) (blurb_ G f H v)))) .
        have {ee__o_ee_prop}: (forall G f H v,
                            Sol.toPolyMor (ee__o_ee_(G)(f)(H)(v)) <~~ (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ee)) := ee__o_ee_prop.
        move: Yoneda10_ee__o_ee_ ee__o_ee_ => Yoneda10_ee__o_ee_ ee__o_ee_ ee__o_ee_prop.
        clear solveCoMod.
        unshelve eexists. eexists.
        refine ( @Sol.PolyTransf _ _ F _ _V_prop _ _ _ _ _
                                 Yoneda10_ee__o_ee_ _ _ _ ee__o_ee_ ) . 

        (**memo: convCoMod_sense is really necessary here for Yoneda10_ee__o_ee_natural Yoneda10_ee__o_ee_morphism Yoneda10_ee__o_ee_toView  **)
        (* Yoneda10_ee__o_ee_natural *)
        { clear -Yoneda10_ee_natural ee__o_ee_prop.
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ee_prop G f H v)) => ee__o_ee_prop_eq);
                    intros; move; rewrite /= /polyelement_to_element /= ; intros;
                    do 2 rewrite -ee__o_ee_prop_eq;
                    exact: (Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural)).
        }
        (* Yoneda10_ee__o_ee_morphism *)
        { clear -Yoneda10_ee_morphism ee__o_ee_prop;
          abstract( move : (fun G f H v => convCoMod_sense (ee__o_ee_prop G f H v))
                    => ee__o_ee_prop_eq; intros; move;
                      rewrite /= /polyelement_to_element /= ;
                      do 2 rewrite -ee__o_ee_prop_eq ;
                      exact: (Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism) ) .
        }
        (* Yoneda10_ee__o_ee_toView *)
        { clear - Yoneda01_F Yoneda10_ee_toView ee__o_ee_prop;
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ee_prop G f H v)) => ee__o_ee_prop_eq );
                    intros; move; rewrite /= /polyelement_to_element /= ;
                    do 2 rewrite -ee__o_ee_prop_eq;
                    exact: (Yoneda10_PolyTransf_morphism_toView Yoneda01_F Yoneda10_ee_toView ) ).
        }

        move: ff_Sol_prop ff'Sol_prop ee__o_ee_prop; clear;
          abstract( simpl; intros;
                    eapply convCoMod_Trans with
                    (uTrans := ( [[ fun G f H v => (Sol.toPolyMor (ee_(G)(f)(H)(v)))
                                      @ F , _V_prop , Yoneda10_ee_natural ,
                                                     Yoneda10_ee_morphism , Yoneda10_ee_toView ]] )
                                 o>CoMod ( 'ViewedFunctor1 (Sol.toPolyMor ee) ));
                    first (by simpl; eauto); (* eapply convCoMod_Trans with *)
                    simpl; by eauto).
    }

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod (ff o>CoMod 'UnitViewedFunctor)) **)
  * have [:blurb] ff_Sol_o_ff_prop :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                             (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb));
        first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
        abstract tac_degrade grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                                    (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb)))
            (projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                                      (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb))) ff_Sol_o_ff_prop 
    => Yoneda10_ff_Sol_o_ff ff_Sol_o_ff ff_Sol_o_ff_prop .

    unshelve eexists. eexists.
    refine ( ff_Sol_o_ff o>CoMod 'UnitViewedFunctor )%sol.
    move: ff_Sol_prop ff'Sol_prop ff_Sol_o_ff_prop; clear;
      abstract (simpl; intros; eapply convCoMod_Trans with
                   (uTrans := ( Sol.toPolyMor ff_Sol ) o>CoMod
                              ( (Sol.toPolyMor ff) o>CoMod 'UnitViewedFunctor )); tac_reduce).

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement F V_prop v )) **)
  * move:  (Sol.Destruct_codomView.morCoMod_codomViewP ff_Sol) => ff_Sol_codomViewP.
    { destruct ff_Sol_codomViewP as
          [ _G (** @'UnitCoMod (View _G) **)
          | _G H g (** 'View1 g **) ].
        
      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement F V_prop v )) , is (( @'UnitCoMod (View _G)) o>CoMod ( 'PolyElement F V_prop v )) **)
      - unshelve eexists. eexists. refine ( 'PolyElement F V_prop v )%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ( 'PolyElement F V_prop v )); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement F V_prop v )) , is (( 'View1 g ) o>CoMod ( 'PolyElement F V_prop v )) **)
      - unshelve eexists. eexists.
        refine ( 'PolyElement F V_prop ( g o>Generator v | sval(V_ G f) ) )%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                                   (uTrans := ( 'View1 g ) o>CoMod ( 'PolyElement F V_prop v )); tac_reduce).
    } 

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( [[ ee_ @ F , V_prop ]] )) **)
  * move:  (Sol.Destruct_codomViewingFunctor.morCoMod_codomViewingFunctorP ff_Sol) => ff_Sol_codomViewingFunctorP.
    { destruct ff_Sol_codomViewingFunctorP as
          [ Yoneda00_F Yoneda01_F F V_ V_prop (** @'UnitCoMod (ViewingFunctor F V_prop) **)
          | Yoneda00_F Yoneda01_F F V_ V_prop G f H v (** 'PolyElement F V_prop v **)
          ] .

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is ((@'UnitCoMod (ViewingFunctor F V_prop)) o>CoMod ( [[ ee_ @ F , V_prop ]] )) **)
      - unshelve eexists. eexists. refine ( [[ ee_ @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]] )%sol.
        move: ff_Sol_prop ff'Sol_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ([[ (fun G H f v => Sol.toPolyMor (ee_(G)(H)(f)(v))) @ F , V_prop , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_toView ]])); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (('PolyElement F V_prop v) o>CoMod ( [[ ee_ @ F , V_prop ]] )) **)
      - have [:blurb] ee_v_prop :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb));
            first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
            abstract(match goal with
                     | [ F : @obCoMod ?Yoneda00_F ?Yoneda01_F |- _ ] =>
                       destruct (Card'.is_elementsUnderView12_allP F v)
                     end;
                     tac_degrade grade_ff).
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                                        (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb)))
                (projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                                          (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb))) ee_v_prop 
        => Yoneda10_ee_v ee_v ee_v_prop .

        unshelve eexists. eexists.
        refine ( ee_v o>CoMod 'UnitViewedFunctor )%sol.
        move: ff_Sol_prop ff'Sol_prop ee_v_prop; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                        (uTrans := ( 'PolyElement F V_prop v ) o>CoMod
                           ( [[ (fun G H f v => Sol.toPolyMor (ee_(G)(H)(f)(v))) @ F , V_prop ,  Yoneda10_ee_natural , Yoneda10_ee_morphism  , Yoneda10_ee_toView ]] )); tac_reduce).
    }
}
Defined.
End Resolve.
End VIEWEDFUNCTOR.
(** # #
#+END_SRC

Voila.
# # **)
