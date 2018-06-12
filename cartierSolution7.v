(** # #
#+TITLE: cartierSolution7.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution7.v
https://github.com/1337777/cartier/blob/master/cartierSolution7.v.pdf

solves half of some question of Cartier which is how to program grammatical polymorph generated-functor-along-reindexing ( "Kan extension" ) ...

SHORT ::


#+BEGIN_EXAMPLE
#+END_EXAMPLE

KEYWORDS :: 1337777.OOO ; COQ ; cut-elimination ; polymorph generated-functor-along-reindexing ; polymorph metafunctors-grammar ; modos

OUTLINE ::

  * BLA
    + BLABLA

  * BLA

  * BLA
    + BLABLA
    + BLABLA

-----

HINT :: free master-engineering-thesis ; program this grammatical polymorph generated-functor-along-reindexing ( "Kan extension" ) :

generatedFunc ( I : IndexerCat ) ( G : GeneratorsCat ) :=
 { R : ReIndexerCat & { f : G ~> generatingFunc R | p : reIndexingFunc R |- I } }

generatedFunc ( I : IndexerCat ) := fun ( G : GeneratorsCat ) =>
 coReflectionOf_ ( G : GeneratorsCat ) := 
 { { R : ReIndexerCat | p : reIndexingFunc R |- I } &  f : G ~> generatingFunc R }

-----

BUY MOM RECURSIVE T-SQUARE :: paypal.me/1337777 1337777.OOO@gmail.com ; 微信支付 2796386464@qq.com ; eth 0x54810dcb93b37DBE874694407f78959Fa222D920 ; amazon amazon.com/hz/wishlist/ls/28SN02HR4EB8W ; irc #OOO1337777

-----

TODO: 
- rename GENERATEDFUNCTOR to GENERATEDFUNCTOR
- shall morIndexer in Prop ; also shall projT1 instead of proj1_sig 
- NEXT: make (I : obIndexer) as global parameter of CoUnitGenerated and Reflector such is as Generated(I) is colimit over { (R, ReIndexing R |- I) } ... but will it be more than colimit, regardless that for Set it is immediately only-limit 
-TODO: Reflector_morphism this is derivable , instantiate ee_ by [[ hh_ ]]_
-memo: indeed one colimit of multiple cocones , instead of multiple colimits of each cocone
- for adjunction, instead of Generating as global parameter, the have Generating as natural/polygeneration variable/argument/[carry-on] ; polymorphism polyarrowing polygeneration ; adjunction property : structurally-assume presence functor betwen the two obCoMod such that the Yoneda-style square commute and the Generating triangle commute ; now when the two Generator is already cocomplete, then these two Generator have identity Yoneda-style functors to obCoMod and this general property become the common adjunction property that the Generating triangle commute 
- for limits projection-pairing , cut-elimation by starting-destruction of the argument f_ of (f_ o>coMod f') such to use full-polymorphism of projection and half-polymorphism of pairing (good) or  by starting-destruction of the parameter f' of (f_ o>coMod f') such to use half-polymorphism of projection and full-polymorphism of pairing (bad) ... but for colimits counitgenerated-reflector (coprojection-copairing) , cut-elimination shall be by starting-destruction of the parameter f' of (f_ o>coMod f') such to use full-polymorphism of coprojection/counitgenerated and half-polymorphism of copairing/reflector (good) , now the alternative which is by starting-destruction of the argumenr f_ of (f_ o>coMod f') will still use full-polymorphism of coprojection/counitgenerated and half-polymorphism of copairing/reflector (good but more complicated-destructions)
-memo : alternative where presence of conversion of objects and presence of cut-adherence and possibility of constantly-indexed object where AtIndexOb (fun _ => F) I ~~~ F such to permit expressibility and confluence via [[ ff_ ]]_ o>CoMod 'CoUnitGenerated
-memo: possible alternative formulation where morCoMod_indexed is mutual along morCoMod with constructor AtIndexMorCoMod such that in Reflector_morphism_derivable instead of ee_(J) oneself has AtIndexMorCoMod (ee_ : morCoMod_indexed) J and where [[ ff_ @ J]]_ is AtIndexMorCoMod [[[ ff_ ]]_] J 
-NEXT: more general domain for j o>* ; new action s o>$ ; both grammatically-capture somethings already present ;  both with PolyCoMod polymorph ; both are in solution ; both are atomic rewrite-step ; 
-TODO:  is Reflector_morphism_derivable really derivable?
-TODO: memo completeness lemma with soundness lemma , because reflexivity conversion
-TODO: rename Reflector_morphismIndexer to Reflector_naturalIndexer
-TODO: Erase simpl no add from grade grade_indexed toPolyMor toPolyMor_indexed
-NEXT: make obCoMod_indexed carry Yoneda10_F_Poly
-TODO: ERASE admit definition
-TODO: ERASE Sol. 

-----

* BLA

  The ends is to do polymorph mathematics which is 2-folded/enriched ref some indexer which is made of all the graphs as indexes and all the graph-morphisms as arrows .
#+BEGIN_SRC coq :exports both :results silent # # **)

From mathcomp
    Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Omega Psatz.

Module GENERATEDFUNCTOR.

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments Nat.sub : simpl nomatch.
Arguments Nat.add : simpl nomatch.

Delimit Scope poly_scope with poly.
Open Scope poly.

(** # #
#+END_SRC

** BLABLA


#+BEGIN_SRC coq :exports both :results silent # # **)

Delimit Scope poly_scope with poly.
Open Scope poly.

Parameter obIndexer : Type.
Parameter morIndexer : obIndexer -> obIndexer -> Type.
Parameter polyIndexer : forall A A', morIndexer A' A -> forall A'', morIndexer A'' A' -> morIndexer A'' A .
Parameter unitIndexer : forall {A : obIndexer}, morIndexer A A.

Notation "''Indexer' (0 A' ~> A )0" :=
  (@morIndexer A' A) (at level 0, format "''Indexer' (0  A'  ~>  A  )0") : poly_scope.
Notation "a_ o>Indexer a'" :=
  (@polyIndexer _ _ a' _ a_) (at level 40, a' at next level, left associativity) : poly_scope.

Axiom polyIndexer_morphism :
  forall (A A' : obIndexer) (a' : 'Indexer(0 A' ~> A )0) 
    (A'' : obIndexer) (a_ : 'Indexer(0 A'' ~> A' )0),
  forall B (b : 'Indexer(0 B ~> A'' )0),
      b o>Indexer ( a_ o>Indexer a' ) = ( b o>Indexer a_ ) o>Indexer a' .

Axiom polyIndexer_unitIndexer :
  forall (A A' : obIndexer) (a' : 'Indexer(0 A' ~> A )0),
    a' = ( (@unitIndexer A') o>Indexer a' ) .

Axiom unitIndexer_polyIndexer :
  forall (A : obIndexer), forall (A'' : obIndexer) (a_ : 'Indexer(0 A'' ~> A )0),
    a_ = ( a_ o>Indexer (@unitIndexer A) ) .

Parameter obReIndexer : Type.
Parameter morReIndexer : obReIndexer -> obReIndexer -> Type.
Parameter polyReIndexer : forall A A', morReIndexer A' A -> forall A'', morReIndexer A'' A' -> morReIndexer A'' A .
Parameter unitReIndexer : forall {A : obReIndexer}, morReIndexer A A.

Notation "''ReIndexer' (0 A' ~> A )0" :=
  (@morReIndexer A' A) (at level 0, format "''ReIndexer' (0  A'  ~>  A  )0") : poly_scope.
Notation "a_ o>ReIndexer a'" :=
  (@polyReIndexer _ _ a' _ a_) (at level 40, a' at next level, left associativity) : poly_scope.

Axiom polyReIndexer_morphism :
  forall (A A' : obReIndexer) (a' : 'ReIndexer(0 A' ~> A )0) 
    (A'' : obReIndexer) (a_ : 'ReIndexer(0 A'' ~> A' )0),
  forall B (b : 'ReIndexer(0 B ~> A'' )0),
      b o>ReIndexer ( a_ o>ReIndexer a' ) = ( b o>ReIndexer a_ ) o>ReIndexer a' .

Axiom polyReIndexer_unitReIndexer :
  forall (A A' : obReIndexer) (a' : 'ReIndexer(0 A' ~> A )0),
    a' = ( (@unitReIndexer A') o>ReIndexer a' ) .

Axiom unitReIndexer_polyReIndexer :
  forall (A : obReIndexer), forall (A'' : obReIndexer) (a_ : 'ReIndexer(0 A'' ~> A )0),
    a_ = ( a_ o>ReIndexer (@unitReIndexer A) ) .

(*TODO: whether separate shall be polymorph functor instead of combinatorial functor *)
Parameter ReIndexing0 : obReIndexer -> obIndexer.
Parameter ReIndexing1 : forall A A' : obReIndexer, 'ReIndexer(0 A ~> A' )0 -> 'Indexer(0 ReIndexing0 A ~> ReIndexing0 A')0 .

Axiom ReIndexing_morphism : 
  forall (A A' : obReIndexer) (a' : 'ReIndexer(0 A' ~> A )0) 
    (A'' : obReIndexer) (a_ : 'ReIndexer(0 A'' ~> A' )0),
      ReIndexing1 ( a_ o>ReIndexer a' ) = ( ReIndexing1 a_ ) o>Indexer ( ReIndexing1 a' ) .

Axiom ReIndexing_unitReIndexer :
  forall (A : obReIndexer),
    (@unitIndexer (ReIndexing0 A)) = ( ReIndexing1 (@unitReIndexer A) ) .

(* for simplify the definition of grade and automatic arithmetic ;
   but shall again proceed when everything is finite or is below some fixed regular cardinal *)
Parameter ObIndexer1 : obIndexer.
Parameter ObIndexer2 : obIndexer.
Inductive is_ObIndexer12 : obIndexer -> Type :=
| Is_ObIndexer12_ObIndexer1 : is_ObIndexer12 (ObIndexer1)
| Is_ObIndexer12_ObIndexer2 : is_ObIndexer12 (ObIndexer2) .

Axiom is_ObIndexer12_allP : forall (I : obIndexer), is_ObIndexer12 I.

Parameter ObReIndexer1_ : obIndexer -> obReIndexer.
Parameter ObReIndexer2_ : obIndexer -> obReIndexer.
Parameter MorIndexer1_ : forall I : obIndexer, 'Indexer(0 ReIndexing0 (ObReIndexer1_ I) ~> I )0.
Parameter MorIndexer2_ : forall I : obIndexer, 'Indexer(0 ReIndexing0 (ObReIndexer2_ I) ~> I )0.

Inductive is_MorIndexer12_ (I : obIndexer) : forall R : obReIndexer, 'Indexer(0 ReIndexing0 R ~> I )0 -> Type :=
| Is_MorIndexer12_MorIndexer1_ : is_MorIndexer12_ (MorIndexer1_ I)
| Is_MorIndexer12_MorIndexer2_ : is_MorIndexer12_ (MorIndexer2_ I) .

Axiom is_MorIndexer12_allP : forall (I : obIndexer), forall (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0), is_MorIndexer12_ ri.

Parameter obGenerator : Type.
Parameter morGenerator : obGenerator -> obGenerator -> Type.
Parameter polyGenerator : forall A A', morGenerator A' A -> forall A'', morGenerator A'' A' -> morGenerator A'' A .
Parameter unitGenerator : forall {A : obGenerator}, morGenerator A A.

Notation "''Generator' (0 A' ~> A )0" :=
  (@morGenerator A' A) (at level 0, format "''Generator' (0  A'  ~>  A  )0") : poly_scope.
Notation "a_ o>Generator a'" :=
  (@polyGenerator _ _ a' _ a_) (at level 40, a' at next level, left associativity) : poly_scope.

Axiom polyGenerator_morphism :
  forall (A A' : obGenerator) (a' : 'Generator(0 A' ~> A )0) 
    (A'' : obGenerator) (a_ : 'Generator(0 A'' ~> A' )0),
  forall B (b : 'Generator(0 B ~> A'' )0),
      b o>Generator ( a_ o>Generator a' ) = ( b o>Generator a_ ) o>Generator a' .

Axiom polyGenerator_unitGenerator :
  forall (A A' : obGenerator) (a' : 'Generator(0 A' ~> A )0),
    a' = ( (@unitGenerator A') o>Generator a' ) .

Axiom unitGenerator_polyGenerator :
  forall (A : obGenerator), forall (A'' : obGenerator) (a_ : 'Generator(0 A'' ~> A )0),
    a_ = ( a_ o>Generator (@unitGenerator A) ) .

(*TODO: whether separate shall be polymorph functor instead of combinatorial functor *)
Parameter Generating0 : obReIndexer -> obGenerator.
Parameter Generating1 : forall A A' : obReIndexer, 'ReIndexer(0 A ~> A' )0 -> 'Generator(0 Generating0 A ~> Generating0 A')0 .

Axiom Generating_morphism : 
  forall (A A' : obReIndexer) (a' : 'ReIndexer(0 A' ~> A )0) 
    (A'' : obReIndexer) (a_ : 'ReIndexer(0 A'' ~> A' )0),
      Generating1 ( a_ o>ReIndexer a' ) = ( Generating1 a_ ) o>Generator ( Generating1 a' ) .

Axiom Generating_unitReIndexer :
  forall (A : obReIndexer),
    (@unitGenerator (Generating0 A)) = ( Generating1 (@unitReIndexer A) ) .

Definition Yoneda01_functor (Yoneda00 : obGenerator -> Type)
           (Yoneda01 : (forall A A' : obGenerator, 'Generator(0 A' ~> A )0 -> Yoneda00 A -> Yoneda00 A')) : Prop :=
  ( (* binary/composing functoriality *)
    ( forall A A' (a : 'Generator(0 A' ~> A)0) A'' (a' : 'Generator(0 A'' ~> A')0) x,
        Yoneda01 _ _ a' (Yoneda01 _ _ a x) = Yoneda01 _ _ (a' o>Generator a) x ) /\
    ( (* empty/unit functoriality is held only in PolyElement_Pairing *)
      forall A x, x = Yoneda01 _ _ (@unitGenerator A) x ) ) .

Definition Yoneda10_natural
           Yoneda00_F (Yoneda01_F : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           Yoneda00_G (Yoneda01_G : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           (Yoneda10 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A) : Prop :=
  forall A A' (a : 'Generator(0 A' ~> A )0) (f : Yoneda00_F A),
    (proj1_sig Yoneda01_G) _ _ a (Yoneda10 A f) = Yoneda10 A' ((proj1_sig Yoneda01_F) _ _ a f) .

Axiom ax1_Yoneda10_natural
  : forall Yoneda00_F Yoneda01_F Yoneda00_G Yoneda01_G,
    forall (Yoneda10_gg : {Yoneda10 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A |
                      Yoneda10_natural Yoneda01_F Yoneda01_G Yoneda10}),
    forall (Yoneda10_gg0 : {Yoneda10 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A |
                       Yoneda10_natural Yoneda01_F Yoneda01_G Yoneda10}),
      ( forall A0, (proj1_sig Yoneda10_gg0 A0) =1 (proj1_sig Yoneda10_gg A0) ) ->
      Yoneda10_gg0 = Yoneda10_gg .

(*Notation "<< R ; i >>" := (existT _ R i) (at level 0).*)
Notation "<< R ; i ; g >>" := (existT _ (existT _ R i) g) (at level 0, format "<<  R  ;  i  ;  g  >>").

Section Senses_obCoMod.
  
  Lemma Yoneda00_View : forall (B : obGenerator), (obGenerator -> Type).
  Proof. intros B. refine (fun A => 'Generator(0 A ~> B )0 ). Defined.

  Lemma Yoneda01_View : forall (B : obGenerator),
      {Yoneda01 : ( forall A A' : obGenerator, 'Generator(0 A' ~> A )0 -> (Yoneda00_View B) A -> (Yoneda00_View B) A' ) |
       Yoneda01_functor Yoneda01} .
  Proof.
    intros. exists (fun A A' a x => a o>Generator x).
    abstract (split; [intros; exact: polyGenerator_morphism | intros; exact: polyGenerator_unitGenerator]).
  Defined.

  Definition Yoneda00_Generated :
    forall (I : obIndexer),
      (obGenerator -> Type) .
  Proof.
    intros I. refine (fun G : obGenerator =>
                        { R : { R : obReIndexer & 'Indexer(0 ReIndexing0 R ~> I )0 }
                                    & 'Generator(0 G ~> Generating0 (projT1 R) )0 } ).
  Defined.

  Axiom Yoneda00_Generated_quotient :
    forall (I : obIndexer) (G : obGenerator),
    forall (R S : obReIndexer) (rs : 'ReIndexer(0 R ~> S )0)
      (ii : 'Indexer(0 ReIndexing0 S ~> I )0)
      (gg : 'Generator(0 G ~> Generating0 R )0),
      ( existT _ (existT _ S ii) (gg o>Generator Generating1 rs) )
      = ( existT _ (existT _ R (ReIndexing1 rs o>Indexer ii)) gg
          : { R : { R : obReIndexer & 'Indexer(0 ReIndexing0 R ~> I )0 }
                  & 'Generator(0 G ~> Generating0 (projT1 R) )0 } ) .
  (*Axiom Yoneda00_Generated_quotient :
    forall (I : obIndexer) (G : obGenerator),
    forall (R : obReIndexer) (ii : 'Indexer(0 ReIndexing0 R ~> I )0)
      (gg : 'Generator(0 G ~> Generating0 R )0),
    forall (I' : obIndexer) (i : 'Indexer(0 I ~> I' )0),
    forall (G' : obGenerator) (g : 'Generator(0 G' ~> G )0),
    forall (R' : obReIndexer) (r : 'ReIndexer(0 R' ~> R )0),
      (existT _ (existT _ R ii) gg
       : { R : { R : obReIndexer & 'Indexer(0 ReIndexing0 R ~> I )0 }
               & 'Generator(0 G ~> Generating0 (projT1 R) )0 } )
      = (existT _ (existT _ R' (ReIndexing1 r o>Indexer ii))
                (gg o>Generator Generating1 r)) .*)

  Lemma Yoneda01_Generated :
    forall (I : obIndexer),
      { Yoneda01 : ( forall G G' : obGenerator, 'Generator(0 G' ~> G )0 ->
                                      Yoneda00_Generated I G -> Yoneda00_Generated I G' ) |
        Yoneda01_functor Yoneda01 }.
  Proof.
    unshelve eexists.
    - intros G G' g ii.
      refine (existT _ (existT _ (projT1 (projT1 ii)) (projT2 (projT1 ii)))
                       (g o>Generator (projT2 ii))) .
    - abstract (split; [ intros; rewrite -polyGenerator_morphism; reflexivity
                       | intros G ii;
                         rewrite -polyGenerator_unitGenerator;
                         destruct ii as [[? ?] ?]; reflexivity ]) .
  Defined.

  Lemma Yoneda01_Generated_PolyIndexer :
    forall (I : obIndexer) (J : obIndexer) (i : 'Indexer(0 I ~> J )0),
      {Yoneda10 : forall G : obGenerator, Yoneda00_Generated I G -> Yoneda00_Generated J G |
       Yoneda10_natural (Yoneda01_Generated I) (Yoneda01_Generated J) Yoneda10} .
    intros. unshelve eexists.
    refine (fun G gi => existT _ (existT _ (projT1 (projT1 gi))
                                      ((projT2 (projT1 gi)) o>Indexer i))
                            (projT2 gi) )  .
    abstract(intros; move; reflexivity).
  Defined.

End Senses_obCoMod.

Inductive obCoMod : forall Yoneda00 : obGenerator -> Type,
    { Yoneda01 : ( forall A A' : obGenerator, 'Generator(0 A' ~> A )0 -> Yoneda00 A -> Yoneda00 A' ) |
                 Yoneda01_functor Yoneda01 } -> Type := 

| AtIndexOb : forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _)
                (Yoneda01_F_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 -> _),
    (@obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly) ->
    forall I : obIndexer, @obCoMod (Yoneda00_F_(I)) (Yoneda01_F_(I))

| View : forall B : obGenerator, @obCoMod (Yoneda00_View B) (Yoneda01_View B)

with obCoMod_indexed (**memo: non-recursive , only some form of nested grammatical bookeeping **) :
       forall Yoneda00_ : obIndexer -> obGenerator -> Type,
       forall Yoneda01_ : (forall I : obIndexer, { Yoneda01 : ( forall A A' : obGenerator, 'Generator(0 A' ~> A )0 -> Yoneda00_ I A -> Yoneda00_ I A' ) | Yoneda01_functor Yoneda01 }),
         forall Yoneda01_Poly : (forall I J : obIndexer, 'Indexer(0 I ~> J )0 ->
                {Yoneda10_Poly_i : forall G : obGenerator, Yoneda00_ I G -> Yoneda00_ J G |
                 Yoneda10_natural (Yoneda01_ I) (Yoneda01_ J) Yoneda10_Poly_i}), Type := 
       
| ObCoMod_indexed :  forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly,
    (forall I : obIndexer, @obCoMod (Yoneda00_F_(I)) (Yoneda01_F_(I))) ->
    @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly

| Generated : @obCoMod_indexed Yoneda00_Generated Yoneda01_Generated Yoneda01_Generated_PolyIndexer .

Section Senses_morCoMod.

  Lemma Yoneda10_PolyCoMod :
    forall Yoneda00_F1 Yoneda01_F1 Yoneda00_F2 Yoneda01_F2
      (Yoneda10_ff_ : {Yoneda10 : ( forall A : obGenerator, Yoneda00_F1 A -> Yoneda00_F2 A ) |
                       Yoneda10_natural Yoneda01_F1 Yoneda01_F2 Yoneda10 })
      Yoneda00_F2' Yoneda01_F2'
      (Yoneda10_ff' : {Yoneda10 : ( forall A : obGenerator, Yoneda00_F2 A -> Yoneda00_F2' A ) |
                       Yoneda10_natural Yoneda01_F2 Yoneda01_F2' Yoneda10}),
      {Yoneda10 : ( forall A : obGenerator, Yoneda00_F1 A -> Yoneda00_F2' A ) |
       Yoneda10_natural Yoneda01_F1 Yoneda01_F2' Yoneda10}.
  Proof.
    intros. exists (fun A => (proj1_sig Yoneda10_ff') A \o (proj1_sig Yoneda10_ff_) A ).
    abstract (intros; move; intros; simpl;
              rewrite (proj2_sig Yoneda10_ff') (proj2_sig Yoneda10_ff_); reflexivity).
  Defined.

  Lemma Yoneda10_UnitCoMod :
    forall Yoneda00_F Yoneda01_F,
      {Yoneda10 : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_F A ) |
       Yoneda10_natural Yoneda01_F Yoneda01_F Yoneda10 } .
  Proof.
    intros. exists (fun A => id).
    abstract (intros; move; intros; reflexivity).
  Defined.
  
  Lemma Yoneda10_PolyElement :
    forall Yoneda00_F Yoneda01_F (B : obGenerator) (f : Yoneda00_F B),
      {Yoneda10 : ( forall A : obGenerator, Yoneda00_View B A -> Yoneda00_F A ) |
       Yoneda10_natural (Yoneda01_View B) Yoneda01_F Yoneda10} .
  Proof.
    intros. exists (fun A b => proj1_sig Yoneda01_F _ _  b f) .
    abstract (intros; move; intros; apply: (proj1 (proj2_sig Yoneda01_F))).
  Defined.
  
  Lemma Yoneda10_PolyTransf :
    forall Yoneda00_F Yoneda01_F Yoneda00_G  Yoneda01_G
      (transf : {transf : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A ) |
                 Yoneda10_natural Yoneda01_F Yoneda01_G transf })
      (A : obGenerator)
      (Yoneda10_ff : {Yoneda10 : ( forall A0 : obGenerator, 'Generator(0 A0 ~> A )0 -> Yoneda00_F A0 ) |
                      Yoneda10_natural (Yoneda01_View A) Yoneda01_F Yoneda10 }),  
      {Yoneda10 : ( forall A0 : obGenerator, 'Generator(0 A0 ~> A )0 -> Yoneda00_G A0 ) |
       Yoneda10_natural (Yoneda01_View A) Yoneda01_G Yoneda10 } .
  Proof.
    intros. exists (fun A' => (proj1_sig transf) A' \o (proj1_sig Yoneda10_ff) A' ).
    abstract (intros; move; intros; simpl in *;
              rewrite (proj2_sig transf) (proj2_sig Yoneda10_ff); reflexivity).
  Defined.

  Lemma Yoneda10_CoUnitGenerated :
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
        forall Yoneda00_F Yoneda01_F,
        forall Yoneda10_rr : {Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_View (Generating0 R) G |
                         Yoneda10_natural Yoneda01_F (Yoneda01_View (Generating0 R)) Yoneda10},
          { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_Generated (I) G |
           Yoneda10_natural Yoneda01_F (Yoneda01_Generated I) Yoneda10}.
  Proof.
    intros. unshelve eexists.
    refine (fun G ff => sval (Yoneda01_Generated_PolyIndexer i) G
                          (existT _ (existT _ R (@unitIndexer (ReIndexing0 R)))
                                  ((proj1_sig Yoneda10_rr) G ff))).
    abstract (intros; move; intros; rewrite -(proj2_sig Yoneda10_rr); reflexivity). (* blind attempt /!\!1? *)
  Defined.

  Lemma Yoneda10_Reflector :
    forall (Yoneda00_F_ : obIndexer -> _)
      (Yoneda01_F_ : forall I : obIndexer, _)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : _ |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i}),
    forall (I : obIndexer),
      {Yoneda10 : forall G : obGenerator, Yoneda00_Generated I G -> Yoneda00_F_ I G |
       Yoneda10_natural (Yoneda01_Generated I) (Yoneda01_F_ I) Yoneda10} .
  Proof.
    intros. unshelve eexists.
    - intros G ii. refine ( sval (Yoneda10_ff_ _ _ (projT2 (projT1 ii))) G (projT2 ii) ) .
    - abstract (intros G G' g ii; rewrite [in LHS](proj2_sig (Yoneda10_ff_ _ _ _ )); reflexivity).
  Defined.

  Definition Yoneda10_functorIndexer (Yoneda00_F_ : obIndexer -> _)
             (Yoneda01_F_ : forall I : obIndexer, _)
             (Yoneda01_F_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 ->
                {Yoneda01_F_Poly_i : forall G : obGenerator, Yoneda00_F_ I G -> Yoneda00_F_ J G |
                 Yoneda10_natural (Yoneda01_F_ I) (Yoneda01_F_ J) Yoneda01_F_Poly_i})
    := ( forall (I J : obIndexer) (i : 'Indexer(0 I ~> J )0) 
           (K : obIndexer) (j : 'Indexer(0 J ~> K )0),
           forall (G : obGenerator),
             sval (Yoneda01_F_Poly J K j) G \o sval (Yoneda01_F_Poly I J i) G
             =1 sval (Yoneda01_F_Poly I K (i o>Indexer j)) G )
       /\ ( forall (I : obIndexer),
             forall (G : obGenerator),
               id =1 sval (Yoneda01_F_Poly I I (@unitIndexer I)) G ) .

  Section Section1.
  Variables (Yoneda00_F_ : obIndexer -> _)
      (Yoneda01_F_ : forall I : obIndexer, _)
      (Yoneda01_F_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 ->
                                            {Yoneda01_F_Poly_i : forall G : obGenerator, Yoneda00_F_ I G -> Yoneda00_F_ J G |
                                             Yoneda10_natural (Yoneda01_F_ I) (Yoneda01_F_ J) Yoneda01_F_Poly_i})
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_(I) G |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i}).

  Definition Yoneda10_morphismReIndexer_morphismIndexer
    := (  forall (I : obIndexer),
          forall (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0),
          forall (S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
          forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
          forall (G : obGenerator),
            ( sval (Yoneda10_ff_  ((ReIndexing1 sr o>Indexer ri) o>Indexer ij)) G )
            =1 ( sval (Yoneda01_F_Poly ij) G \o
                 (sval (Yoneda10_ff_ ri) G \o
                  sval (Yoneda10_PolyElement (Yoneda01_View (Generating0 R)) (Generating1 sr)) G) )) .

  Definition Yoneda10_morphismIndexerOnly
    := (  forall (I : obIndexer),
          forall (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0),
          forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
          forall (G : obGenerator),
            ( sval (Yoneda10_ff_  (ri o>Indexer ij)) G )
            =1 ( sval (Yoneda01_F_Poly ij) G \o
                 (sval (Yoneda10_ff_ ri) G) )) .

  Lemma Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly :
      Yoneda10_morphismReIndexer_morphismIndexer
      -> Yoneda10_morphismIndexerOnly .
  Proof.
    intros H. move. intros. move. intros x.
    move => /(_  I R ri _ (unitReIndexer) J ij G) in H.
    rewrite -ReIndexing_unitReIndexer in H.
    rewrite -polyIndexer_unitIndexer in H.
    rewrite -Generating_unitReIndexer in H. 
    move => /(_ x) in H. rewrite /= -unitGenerator_polyGenerator in H.
    exact: H.
  Qed.

  Definition Yoneda10_naturalIndexer 
             (Yoneda00_E_ : obIndexer -> _)
             (Yoneda01_E_ : forall I : obIndexer, _)
             (Yoneda01_E_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 ->
                                                   {Yoneda01_E_Poly_i : forall G : obGenerator, Yoneda00_E_ I G -> Yoneda00_E_ J G |
                                                    Yoneda10_natural (Yoneda01_E_ I) (Yoneda01_E_ J) Yoneda01_E_Poly_i})
             (Yoneda10_ee_ : forall I : obIndexer, {Yoneda10_ee_I : forall G : obGenerator, Yoneda00_F_(I) G -> Yoneda00_E_(I) G |
                                     Yoneda10_natural (Yoneda01_F_(I)) (Yoneda01_E_(I)) Yoneda10_ee_I})
    := ( forall (I J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
           forall (G : obGenerator),
             ( sval (Yoneda10_ee_ J) G  \o
                    sval (Yoneda01_F_Poly ij) G  )
             =1 ( sval (Yoneda01_E_Poly _ _ ij) G \o
                       (sval (Yoneda10_ee_ I) G  )) ) .

  End Section1.
 
  Lemma Yoneda10_Reflector_naturalIndexer_ALT :
    forall (Yoneda00_F_ : obIndexer -> _)
      (Yoneda01_F_ : forall I : obIndexer, _)
      (Yoneda01_F_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 ->
                                            {Yoneda01_F_Poly_i : forall G : obGenerator, Yoneda00_F_ I G -> Yoneda00_F_ J G |
                                             Yoneda10_natural (Yoneda01_F_ I) (Yoneda01_F_ J) Yoneda01_F_Poly_i})
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_(I) G |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i}),
    forall (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
      Yoneda10_naturalIndexer Yoneda01_Generated_PolyIndexer Yoneda01_F_Poly (Yoneda10_Reflector Yoneda10_ff_).
(*      ( forall (I J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
           forall (G : obGenerator),
             ( sval (Yoneda10_Reflector Yoneda10_ff_ J) G  \o
                    sval (Yoneda01_Generated_PolyIndexer ij) G  )
             =1 ( sval (Yoneda01_F_Poly ij) G \o
                       (sval (Yoneda10_Reflector Yoneda10_ff_ I) G  )) ) . *)
  Proof.
    intros. rewrite /Yoneda10_naturalIndexer.
      intros; move. intros i.
      apply: (Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly
                Yoneda10_ff_morphismReIndexer_morphismIndexer).
  Qed.

End Senses_morCoMod.

(*
   PolyElement : View G ~> F
   PolyTransf : (View G ~> E) -> View G ~> F
   Generated_PolyIndexer : (View G ~> AtIndexOb Generated(I)) -> (View G ~> AtIndexOb Generated(J))
   CoUnitGenerated : (F ~> View (Generating0 R)) -> F ~> AtIndexOb Generated(ReIndexing0 R)
   Reflector : (View (Generating0 R) ~> AtIndexOb F_(ReIndexing0 R)) -> AtIndexOb Generated(I) ~> AtIndexOb F_(I)

   PolyTransf : View G ~> F
   Generated_PolyIndexer : View G ~> AtIndexOb Generated(J)

   vx   polyyoneda o> generated_poly (via sense)
   v~~ Generated_PolyIndexer o| CoUnitGenerated (via sense)
   v~  Generated_PolyIndexer o> reflector (deriv)

   PolyTransf : View G ~> F

   PolyElement : View G ~> F
   CoUnitGenerated : F ~> AtIndexOb Generated(ReIndexing0 R)
   Reflector : AtIndexOb Generated(I) ~> AtIndexOb F_(I)

   v  polyyoneda00 o> (rr o> 'counitgenerated) (via sense)
   v  polyyoneda o> reflector (via sense)
   v  CoUnitGenerated o> Reflector  (cancel)
   v  CoUnitGenerated o> CoUnitGenerated  (morphism)
   v  Reflector o> CoUnitGenerated  (morphism) 
   v  Reflector o> Reflector   (morphism) 

   PolyElement : View G ~> F
   PolyTransf : (View G ~> E) -> 
                 View G ~> F
   CoUnitGenerated : (F ~> View (Generating0 R)) -> 
                      F ~> AtIndexOb Generated(I)
   Reflector : ((R : _) -> View (Generating0 R) ~> AtIndexOb F_(I)) -> 
                AtIndexOb Generated(I) ~> AtIndexOb F_(I)

 *)

Reserved Notation "''CoMod' (0 E ~> F @ Yoneda10 )0"
         (at level 0, format "''CoMod' (0  E  ~>  F  @  Yoneda10  )0").
Reserved Notation "''CoMod_' (0 E_ ~> F_ @ Yoneda10_ )0"
         (at level 0, format "''CoMod_' (0  E_  ~>  F_  @  Yoneda10_  )0").

Inductive morCoMod : forall Yoneda00_E Yoneda01_E,
    @obCoMod Yoneda00_E Yoneda01_E ->
    forall Yoneda00_F Yoneda01_F,
      @obCoMod Yoneda00_F Yoneda01_F ->
      { Yoneda10 : ( forall A : obGenerator, Yoneda00_E A -> Yoneda00_F A ) |
                   Yoneda10_natural Yoneda01_E Yoneda01_F Yoneda10 } -> Type :=

| AtIndexMor : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _),
      'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 ->
      forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0

(** -----cuts to be eliminated----- **)

| PolyCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
                Yoneda10_ff' ,
                'CoMod(0 F' ~> F @ Yoneda10_ff' )0 ->
                  forall Yoneda00_F'' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F'' Yoneda01_F''),
                  forall Yoneda10_ff_ ,
                  'CoMod(0 F'' ~> F' @ Yoneda10_ff_ )0 ->
                  'CoMod(0 F'' ~> F @ Yoneda10_PolyCoMod Yoneda10_ff_ Yoneda10_ff' )0

(* input: transformation of elements ; output: transformation of actions  *)
| PolyTransf : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                 Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
                 (transf : {transf : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A ) |
                                     Yoneda10_natural Yoneda01_F Yoneda01_G transf}) 
                 (A : obGenerator) Yoneda10_ff ,
                 'CoMod(0 View A ~> F @ Yoneda10_ff )0 ->
                 'CoMod(0 View A ~> G @ Yoneda10_PolyTransf transf Yoneda10_ff )0

(** ----solution morphisms---- **)

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    'CoMod(0 F ~> F @ Yoneda10_UnitCoMod Yoneda01_F )0

(* input: element ; output: action  *)
| PolyElement : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                   (G : obGenerator) (f : Yoneda00_F G),
    'CoMod(0 View G ~> F @ Yoneda10_PolyElement Yoneda01_F f )0

(* injection/section/coprojection ;   ?Co?UnitGenerated *)
| CoUnitGenerated : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) Yoneda10_rr,
      'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0 ->
      'CoMod(0 F ~> AtIndexOb Generated(I) @ Yoneda10_CoUnitGenerated i Yoneda10_rr )0


where "''CoMod' (0 F' ~> F @ Yoneda10 )0" := (@morCoMod _ _ F' _ _ F Yoneda10) : poly_scope

with morCoMod_indexed (**memo: non-recursive , only some form of nested grammatical bookeeping **)
     : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly,
    @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly ->
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly,
      @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly ->
      (forall I : obIndexer, { Yoneda10 : ( forall A : obGenerator, Yoneda00_E_(I) A -> Yoneda00_F_(I) A ) |
                          Yoneda10_natural (Yoneda01_E_(I)) (Yoneda01_F_(I)) Yoneda10 }) -> Type := 

| MorCoMod_indexed :
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _),
      (forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0 ) ->
      'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0

| Reflector :
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_(I) G |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i})
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (**memo: Yoneda01_F_Poly_functorIndexer and Yoneda10_ff_morphismReIndexerOnly not used in to show convCoMod_sense **)
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
      'CoMod_(0 Generated ~> F_ @ Yoneda10_Reflector Yoneda10_ff_ )0

where "''CoMod_' (0 E_ ~> F_ @ Yoneda10_ )0" := (@morCoMod_indexed _ _ _ E_ _ _ _ F_ Yoneda10_) : poly_scope .

Notation "''CoMod' (0 F' ~> F )0" :=
  (@morCoMod _ _ F' _ _ F _) (at level 0, only parsing, format "''CoMod' (0  F'  ~>  F  )0") : poly_scope.
Notation "''CoMod_' (0 E_ ~> F_ )0" :=
  (@morCoMod_indexed _ _ _ E_ _ _ _ F_ _) (at level 0, format "''CoMod_' (0  E_  ~>  F_  )0") : poly_scope .

Notation "''AtIndexMor' ff_ I" := (@AtIndexMor _ _ _ _ _ _ _ _ _ ff_ I) (at level 10, ff_ at next level, I at next level) : poly_scope.

Notation "ff_ o>CoMod ff'" :=
  (@PolyCoMod _ _ _ _ _ _ _ ff' _ _ _ _ ff_) (at level 40 , ff' at next level , left associativity) : poly_scope.

Notation "ff o>Transf_ transf @ G" :=
  (@PolyTransf _ _ _ _ _ G transf _ _ ff) (at level 3, transf at next level, G at level 0, left associativity) : poly_scope.

Notation "ff o>Transf_ transf" :=
  (@PolyTransf _ _ _ _ _ _ transf _ _ ff) (at level 3, transf at next level) : poly_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ F) (at level 10, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _) (at level 0) : poly_scope.

Notation "''PolyElement' F f" := (@PolyElement _ _ F _ f) (at level 10, F at next level, f at next level) : poly_scope.

Notation "rr o>CoMod 'CoUnitGenerated @ i" :=
  (@CoUnitGenerated _ _ i _ _ _ _ rr) (at level 4, i at next level, right associativity) : poly_scope.

Notation "''MorCoMod_indexed' ff_" := (@MorCoMod_indexed _ _ _ _ _ _ _ _ _ ff_) (at level 10, ff_ at next level) : poly_scope.

Notation "[[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_" :=
  (@Reflector _ _ _ _ _ ff_ Yoneda01_F_Poly_functorIndexer Yoneda10_ff_morphismReIndexer_morphismIndexer)
    (at level 4, Yoneda01_F_Poly_functorIndexer at next level, Yoneda10_ff_morphismReIndexer_morphismIndexer at next level,
     format "[[  ff_  @  Yoneda01_F_Poly_functorIndexer  ,  Yoneda10_ff_morphismReIndexer_morphismIndexer  ]]_" ) : poly_scope.

Notation "[[ ff_ ]]_" :=
  (@Reflector _ _ _ _ _ ff_ _ _ )
    (at level 4, format "[[  ff_  ]]_" ) : poly_scope.

Module Sol.
Section Section1.
Delimit Scope sol_scope with sol.

Inductive morCoMod : forall Yoneda00_E Yoneda01_E,
    @obCoMod Yoneda00_E Yoneda01_E ->
    forall Yoneda00_F Yoneda01_F,
      @obCoMod Yoneda00_F Yoneda01_F ->
      { Yoneda10 : ( forall A : obGenerator, Yoneda00_E A -> Yoneda00_F A ) |
                   Yoneda10_natural Yoneda01_E Yoneda01_F Yoneda10 } -> Type :=

| AtIndexMor : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _),
      'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 ->
      forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0

(** ----solution morphisms---- **)

| UnitCoMod : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    'CoMod(0 F ~> F @ Yoneda10_UnitCoMod Yoneda01_F )0

(* input: element ; output: action  *)
| PolyElement : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                   (G : obGenerator) (f : Yoneda00_F G),
    'CoMod(0 View G ~> F @ Yoneda10_PolyElement Yoneda01_F f )0

(* injection/section/coprojection ;   ?Co?UnitGenerated *)
| CoUnitGenerated : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) Yoneda10_rr,
      'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0 ->
      'CoMod(0 F ~> AtIndexOb Generated(I) @ Yoneda10_CoUnitGenerated i Yoneda10_rr )0

where "''CoMod' (0 F' ~> F @ Yoneda10 )0" := (@morCoMod _ _ F' _ _ F Yoneda10) : sol_scope

with morCoMod_indexed (**memo: non-recursive , only some form of nested grammatical bookeeping **)
     : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly,
    @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly ->
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly,
      @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly ->
      (forall I : obIndexer, { Yoneda10 : ( forall A : obGenerator, Yoneda00_E_(I) A -> Yoneda00_F_(I) A ) |
                          Yoneda10_natural (Yoneda01_E_(I)) (Yoneda01_F_(I)) Yoneda10 }) -> Type := 

| MorCoMod_indexed :
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _),
      (forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0 ) ->
      'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0

| Reflector :
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_(I) G |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i})
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (**memo: Yoneda01_F_Poly_functorIndexer and Yoneda10_ff_morphismReIndexerOnly not used in to show convCoMod_sense **)
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
      'CoMod_(0 Generated ~> F_ @ Yoneda10_Reflector Yoneda10_ff_ )0

where "''CoMod_' (0 E_ ~> F_ @ Yoneda10_ )0" := (@morCoMod_indexed _ _ _ E_ _ _ _ F_ Yoneda10_) : sol_scope .

End Section1.

Module Export Ex_Notations.
Delimit Scope sol_scope with sol.

Notation "''CoMod' (0 F' ~> F @ Yoneda10 )0" :=
  (@morCoMod _ _ F' _ _ F Yoneda10) (at level 0, format "''CoMod' (0  F'  ~>  F  @  Yoneda10  )0") : sol_scope.

Notation "''CoMod' (0 F' ~> F )0" :=
  (@morCoMod _ _ F' _ _ F _) (at level 0, only parsing, format "''CoMod' (0  F'  ~>  F  )0") : sol_scope.

Notation  "''CoMod_' (0 E_ ~> F_ @ Yoneda10_ )0" :=
  (@morCoMod_indexed _ _ _ E_ _ _ _ F_ Yoneda10_) (at level 0, format "''CoMod_' (0  E_  ~>  F_  @  Yoneda10_  )0") : sol_scope .

Notation "''CoMod_' (0 E_ ~> F_ )0" :=
  (@morCoMod_indexed _ _ _ E_ _ _ _ F_ _) (at level 0, format "''CoMod_' (0  E_  ~>  F_  )0") : sol_scope .

Notation "''AtIndexMor' ff_ I" := (@AtIndexMor _ _ _ _ _ _ _ _ _ ff_ I) (at level 10, ff_ at next level, I at next level) : sol_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ F) (at level 10, only parsing) : sol_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _) (at level 0) : sol_scope.

Notation "''PolyElement' F f" := (@PolyElement _ _ F _ f) (at level 10, F at next level, f at next level) : sol_scope.

Notation "rr o>CoMod 'CoUnitGenerated @ i" :=
  (@CoUnitGenerated _ _ i _ _ _ _ rr) (at level 4, i at next level, right associativity) : sol_scope.

Notation "''MorCoMod_indexed' ff_" := (@MorCoMod_indexed _ _ _ _ _ _ _ _ _ ff_) (at level 10, ff_ at next level) : sol_scope.

Notation "[[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_" :=
  (@Reflector _ _ _ _ _ ff_ Yoneda01_F_Poly_functorIndexer Yoneda10_ff_morphismReIndexer_morphismIndexer)
    (at level 4, Yoneda01_F_Poly_functorIndexer at next level, Yoneda10_ff_morphismReIndexer_morphismIndexer at next level,
     format "[[  ff_  @  Yoneda01_F_Poly_functorIndexer  ,  Yoneda10_ff_morphismReIndexer_morphismIndexer  ]]_" ) : sol_scope.

Notation "[[ ff_ ]]_" :=
  (@Reflector _ _ _ _ _ ff_ _ _ )
    (at level 4, format "[[  ff_  ]]_" ) : sol_scope.

End Ex_Notations.

Scheme  morCoMod_morCoMod_indexed_ind :=
  Induction for morCoMod Sort Prop
  with  morCoMod_indexed_morCoMod_ind :=
    Induction for morCoMod_indexed Sort Prop.
Combined Scheme morCoMod_morCoMod_indexed_mutind from
         morCoMod_morCoMod_indexed_ind, morCoMod_indexed_morCoMod_ind.
Scheme  morCoMod_morCoMod_indexed_rect :=
  Induction for morCoMod Sort Type
  with  morCoMod_indexed_morCoMod_rect :=
    Induction for morCoMod_indexed Sort Type.
Definition morCoMod_morCoMod_indexed_mutrect P P0 a b c d e f := 
  pair (@morCoMod_morCoMod_indexed_rect P P0 a b c d e f )
       (@morCoMod_indexed_morCoMod_rect P P0 a b c d e f ).

Definition toPolyMor_mut :
  (forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
    Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
    Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 %sol ),
      'CoMod(0 E ~> F @ Yoneda10_ff )0 %poly ) *
( forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly)
    Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
    Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 %sol ),
      'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 %poly ) .
Proof.
  apply morCoMod_morCoMod_indexed_mutrect.
  - (* AtIndexMor *) intros ? ? ? ? ? ? ? ? ?  ff_ IHff_ I .
    exact: ('AtIndexMor IHff_ I)%poly.
  - (* UnitCoMod *) intros ? ? F .
    exact: ( @'UnitCoMod F ) %poly.
  - (* PolyElement *) intros ? ? F ? f .
    exact: ( 'PolyElement F f ) %poly.
  - (* CoUnitGenerated *) intros ? ? ? ? ? ? ? rr IHrr.
    exact: ( IHrr o>CoMod 'CoUnitGenerated @ i )%poly.
  - (* MorCoMod_indexed *) intros ? ? ? ? ? ? ? ? ? ff_ IHff_ .
    exact: ( 'MorCoMod_indexed (fun I : obIndexer => IHff_(I)) )%poly.
  - (* Reflector *) intros ? ? ? F_ ? ff_ IHff_
                           Yoneda01_F_Poly_functorIndexer Yoneda10_ff_morphismReIndexer_morphismIndexer.
    exact: ( [[ ( fun (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0) =>
                    (IHff_ I R i) )
                  @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ )%poly.
Defined.

Definition toPolyMor := fst Sol.toPolyMor_mut. 
Definition toPolyMor_indexed := snd Sol.toPolyMor_mut. 
Lemma toPolyMor_mut_AtIndexMor :
  forall (Yoneda00_E_ : obIndexer -> obGenerator -> Type)
    (Yoneda01_E_ : forall I : obIndexer,
                   {Yoneda01
                   : forall A A' : obGenerator,
                     'Generator(0 A' ~> A )0 -> Yoneda00_E_ I A -> Yoneda00_E_ I A' |
                   Yoneda01_functor Yoneda01}) Yoneda01_E_Poly (E_ : obCoMod_indexed Yoneda01_E_Poly)
    (Yoneda00_F_ : obIndexer -> obGenerator -> Type)
    (Yoneda01_F_ : forall I : obIndexer,
                   {Yoneda01
                   : forall A A' : obGenerator,
                     'Generator(0 A' ~> A )0 -> Yoneda00_F_ I A -> Yoneda00_F_ I A' |
                   Yoneda01_functor Yoneda01}) Yoneda01_F_Poly (F_ : obCoMod_indexed Yoneda01_F_Poly)
    (Yoneda10_ff_ : forall I : obIndexer,
                    {Yoneda10 : forall A : obGenerator, Yoneda00_E_ I A -> Yoneda00_F_ I A |
                    Yoneda10_natural (Yoneda01_E_ I) (Yoneda01_F_ I) Yoneda10}),
    forall (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0%sol),
      forall I : obIndexer,
        toPolyMor (AtIndexMor ff_ I) = ('AtIndexMor (toPolyMor_indexed ff_) I)%poly.
Proof. reflexivity. Qed.

Lemma toPolyMor_mut_UnitCoMod :
 forall (Yoneda00_F : obGenerator -> Type)
   (Yoneda01_F : {Yoneda01
                 : forall A A' : obGenerator,
                   'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                 Yoneda01_functor Yoneda01}) (F : obCoMod Yoneda01_F),
   toPolyMor (@'UnitCoMod F)%sol = (@'UnitCoMod F)%poly.
Proof. reflexivity. Qed.

Lemma toPolyMor_mut_PolyElement :
 forall (Yoneda00_F : obGenerator -> Type)
   (Yoneda01_F : {Yoneda01
                 : forall A A' : obGenerator,
                   'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                 Yoneda01_functor Yoneda01}) (F : obCoMod Yoneda01_F) (G : obGenerator)
   (f : Yoneda00_F G),
        toPolyMor ( 'PolyElement F f )%sol = ( 'PolyElement F f ) %poly.
Proof. reflexivity. Qed.

Lemma toPolyMor_mut_CoUnitGenerated :
 forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0)
   (Yoneda00_F : obGenerator -> Type)
   (Yoneda01_F : {Yoneda01
                 : forall A A' : obGenerator,
                   'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                 Yoneda01_functor Yoneda01}) (F : obCoMod Yoneda01_F)
   (Yoneda10_rr : {Yoneda10 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_View (Generating0 R) A
                  | Yoneda10_natural Yoneda01_F (Yoneda01_View (Generating0 R)) Yoneda10}),
 forall (rr: 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0%sol),
   toPolyMor (rr o>CoMod 'CoUnitGenerated @ i)%sol = ((toPolyMor rr) o>CoMod 'CoUnitGenerated @ i)%poly.
Proof. reflexivity. Qed.

Lemma toPolyMor_mut_MorCoMod_indexed :
 forall (Yoneda00_E_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_E_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_E_ I A -> Yoneda00_E_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_E_Poly (E_ : obCoMod_indexed Yoneda01_E_Poly)
   (Yoneda00_F_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_F_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F_ I A -> Yoneda00_F_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_F_Poly (F_ : obCoMod_indexed Yoneda01_F_Poly)
   (Yoneda10_ff_ : forall I : obIndexer,
                   {Yoneda10 : forall A : obGenerator, Yoneda00_E_ I A -> Yoneda00_F_ I A |
                   Yoneda10_natural (Yoneda01_E_ I) (Yoneda01_F_ I) Yoneda10})
   (ff_: (forall I : obIndexer, 'CoMod(0 AtIndexOb E_ I ~> AtIndexOb F_ I @ Yoneda10_ff_ I )0%sol)),
   toPolyMor_indexed ('MorCoMod_indexed ff_ )%sol = ( 'MorCoMod_indexed (fun I : obIndexer => toPolyMor (ff_(I))) )%poly.
Proof. reflexivity. Qed.

Lemma toPolyMor_mut_Reflector :
 forall (Yoneda00_F_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_F_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F_ I A -> Yoneda00_F_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_F_Poly (F_ : obCoMod_indexed Yoneda01_F_Poly)
   (Yoneda10_ff_ : forall (I : obIndexer) (R : obReIndexer),
                   'Indexer(0 ReIndexing0 R ~> I )0 ->
                   {Yoneda10_ff_i
                   : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_ I G |
                   Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_ I) Yoneda10_ff_i})
   (ff_ : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
              'CoMod(0 View (Generating0 R) ~> AtIndexOb F_ I @ Yoneda10_ff_ I R i )0%sol))
 (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
 (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
   toPolyMor_indexed ([[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ )%sol =
    ( [[ ( fun (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0) =>
                    toPolyMor (ff_(I)(R)(i)) )
                  @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ )%poly.
Proof. reflexivity. Qed.

Definition toPolyMor_mut_rewrite := (toPolyMor_mut_AtIndexMor, toPolyMor_mut_UnitCoMod, toPolyMor_mut_PolyElement, toPolyMor_mut_CoUnitGenerated, toPolyMor_mut_MorCoMod_indexed, toPolyMor_mut_Reflector).

Module Destruct_codomView.

Inductive morCoMod_codomView
: forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F ), forall (G : obGenerator), 
      forall Yoneda10_ff, 'CoMod(0 F ~> (View G) @ Yoneda10_ff )0 %sol -> Type :=

| UnitCoMod :  forall B : obGenerator, 
    morCoMod_codomView ( ( @'UnitCoMod (View B) )%sol )

| PolyElement : forall (G G' : obGenerator) (f : Yoneda00_View G G'),
    morCoMod_codomView ( ( 'PolyElement (View G) f )%sol ) .

Lemma morCoMod_codomViewP
  : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 %sol ),
      ltac:( destruct G; [ refine (unit : Type) | ];
               refine (morCoMod_codomView gg) ).
Proof.
  intros. case: _ _ F _ _ G Yoneda10_gg / gg.
  - intros; exact: tt.
  - destruct F; [intros; exact: tt | ].
    constructor 1.
  - destruct F; [intros; exact: tt | ].
    constructor 2.
  - intros; exact: tt.
Defined.

End Destruct_codomView.

Module Destruct_codomAtIndexObGenerated.

Inductive morCoMod_codomAtIndexObGenerated
: forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E ),
    forall (I : obIndexer),
    forall Yoneda10_ee, 'CoMod(0 E ~> (AtIndexOb Generated I) @ Yoneda10_ee )0 %sol -> Type :=

| UnitCoMod : forall (I : obIndexer),
      morCoMod_codomAtIndexObGenerated ( @'UnitCoMod (AtIndexOb Generated I) )%sol

| PolyElement : forall (I : obIndexer) (G : obGenerator) (f : Yoneda00_Generated I G),
    morCoMod_codomAtIndexObGenerated (PolyElement (AtIndexOb Generated I) f )%sol

| CoUnitGenerated : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) Yoneda10_rr
      (rr : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0 %sol),
        morCoMod_codomAtIndexObGenerated ( rr o>CoMod 'CoUnitGenerated @ i )%sol

| MorCoMod_indexed :
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _)
      (ff_ : (forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb Generated(I) @ (Yoneda10_ff_(I)) )0 %sol)),
      forall (J : obIndexer),
        morCoMod_codomAtIndexObGenerated (AtIndexMor ( MorCoMod_indexed ff_ ) J)%sol

| Reflector :
    forall (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb Generated(I) @ (Yoneda10_ff_ _ _ (i)) )0 %sol)
      (Yoneda01_Generated_PolyIndexer_functorIndexer : Yoneda10_functorIndexer Yoneda01_Generated_PolyIndexer)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_Generated_PolyIndexer Yoneda10_ff_),
    forall (J : obIndexer),
      morCoMod_codomAtIndexObGenerated (AtIndexMor [[ ff_ @ Yoneda01_Generated_PolyIndexer_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J)%sol .

  Lemma morCoMod_codomAtIndexObGeneratedP
    : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
      forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
      forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 %sol ),
      ltac:( destruct G as [? ? ? F_ I | ]; [ | refine (unit : Type) ];
               destruct F_; [ refine (unit : Type) | ];
                 refine (morCoMod_codomAtIndexObGenerated gg) ).
  Proof.
    intros. case: _ _ F _ _ G Yoneda10_gg / gg.
    - intros ? ? ? E_ ? ? ? F_ ? ff_ J.
      destruct ff_ .
      + destruct F_; [ intros; exact: tt | ].
        constructor 4.
      + destruct F_; [ intros; exact: tt | ].
        constructor 5.
    - destruct F as [? ? ? F_ I | ]; [ | intros; exact: tt ].
      destruct F_; [ intros; exact: tt | ];
        constructor 1.
    - destruct F as [? ? ? F_ I | ]; [ | intros; exact: tt ].
      destruct F_; [ intros; exact: tt | ];
        constructor 2.
    - constructor 3.
  Defined.

End Destruct_codomAtIndexObGenerated.

(**TODO: ?ERASE? Destruct_domView *)
Module Destruct_domView.

Inductive morCoMod_domView
: forall (B : obGenerator), forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F ),
      forall Yoneda10_ff, 'CoMod(0 (View B) ~> F @ Yoneda10_ff )0 %sol -> Type :=

| UnitCoMod :  forall B : obGenerator, 
    morCoMod_domView ( ( @'UnitCoMod (View B) )%sol )

| PolyElement : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                   (A : obGenerator) (f : Yoneda00_F A),
    morCoMod_domView ( ( 'PolyElement F f )%sol )

| CoUnitGenerated : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
      forall (G : obGenerator) Yoneda10_rr (rr : 'CoMod(0 View G ~> View (Generating0 R) @ Yoneda10_rr )0 %sol),
        morCoMod_domView ( rr o>CoMod 'CoUnitGenerated @ i)%sol .

Lemma morCoMod_domViewP
  : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 %sol ),
      ltac:( destruct F; [ refine (unit : Type) | ];
               refine (morCoMod_domView gg) ).
Proof.
  intros. case: _ _ F _ _ G Yoneda10_gg / gg.
  - intros; exact: tt.
  - destruct F; [intros; exact: tt | ].
    constructor 1.
  - constructor 2.
  - destruct F; [intros; exact: tt | ].
    constructor 3.
Defined.

End Destruct_domView.

(**TODO: ?ERASE? Destruct_domAtIndexOb *)
Module Destruct_domAtIndexOb.

Inductive morCoMod_domAtIndexOb
: forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
     (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly) (I : obIndexer),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E ),
    forall Yoneda10_ee, 'CoMod(0 (AtIndexOb F_ I) ~> E @ Yoneda10_ee )0 %sol -> Type :=

| AtIndexMor : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _)
      (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 %sol),
    forall (J : obIndexer),
      morCoMod_domAtIndexOb (AtIndexMor ff_ J)%sol

| UnitCoMod : forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
     (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly) (I : obIndexer),
      morCoMod_domAtIndexOb ( @'UnitCoMod (AtIndexOb F_ I) )%sol

| CoUnitGenerated : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
      forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
        (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly) (J : obIndexer) Yoneda10_rr
        (rr : 'CoMod(0 AtIndexOb F_(J) ~> View (Generating0 R) @ Yoneda10_rr )0 %sol),
        morCoMod_domAtIndexOb ( rr o>CoMod 'CoUnitGenerated @ i )%sol

| Reflector :
    forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 %sol)
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall (J : obIndexer),
      morCoMod_domAtIndexOb ( AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J )%sol .

  Lemma morCoMod_domAtIndexObP
    : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
      forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
      forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 %sol ),
        ltac:( destruct F; [ | refine (unit : Type)];
                 refine (morCoMod_domAtIndexOb gg) ).
  Proof.
    intros. case: _ _ F _ _ G Yoneda10_gg / gg.
    - constructor 1.
    - destruct F; [ | intros; exact: tt ].
      constructor 2.
    - intros; exact: tt.
    - destruct F; [ | intros; exact: tt].
      constructor 3.
  Defined.

End Destruct_domAtIndexOb.

End Sol.

Section Senses_convCoMod.

  Definition PolyTransf_morphismPolyTransf_transf :
    forall Yoneda00_F Yoneda01_F Yoneda00_G Yoneda01_G
      (transf : {transf : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A ) |
                 Yoneda10_natural Yoneda01_F Yoneda01_G transf}) 
      Yoneda00_H Yoneda01_H
      (transf' : {transf : ( forall A : obGenerator, Yoneda00_G A -> Yoneda00_H A ) |
                  Yoneda10_natural Yoneda01_G Yoneda01_H transf}),
      {transf0 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_H A |
       Yoneda10_natural Yoneda01_F Yoneda01_H transf0}.
  Proof.
    intros. unshelve eexists.
    refine (fun G => sval transf' G \o sval transf G).
    - intros. move. intros. simpl. rewrite (proj2_sig transf') (proj2_sig transf) . reflexivity.
  Defined.


  Definition Yoneda10_ViewGenerating_PolyReIndexer_form :
    forall (R S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
      {Yoneda10 : forall G : obGenerator, Yoneda00_View (Generating0 S) G -> Yoneda00_View (Generating0 R) G |
       Yoneda10_natural (Yoneda01_View (Generating0 S)) (Yoneda01_View (Generating0 R)) Yoneda10} .
  Proof.
    intros. unshelve eexists.
    refine (fun G s => (sval (Yoneda01_View (Generating0 R)) (Generating0 S) G s (Generating1 sr))).
    abstract (intros; move; intros; simpl; exact: polyGenerator_morphism).
  Defined.

  Lemma Yoneda01_Generated_PolyIndexer_functorIndexer :
    ( forall (I J : obIndexer) (i : 'Indexer(0 I ~> J )0) 
        (K : obIndexer) (j : 'Indexer(0 J ~> K )0),
        forall (G : obGenerator),
          sval (Yoneda01_Generated_PolyIndexer j) G \o sval (Yoneda01_Generated_PolyIndexer  i) G
          =1 sval (Yoneda01_Generated_PolyIndexer  (i o>Indexer j)) G )
    /\ ( forall (I : obIndexer),
          forall (G : obGenerator),
            id =1 sval (Yoneda01_Generated_PolyIndexer (@unitIndexer I)) G ) . 
  Proof.
    split.
    - intros. move. intros g. simpl.
    rewrite -[in LHS]polyIndexer_morphism . reflexivity.
    - intros. move. intros g. simpl.
    rewrite -[in RHS]unitIndexer_polyIndexer . case: g => - [? ?] ?. reflexivity.
  Qed.

  Lemma Yoneda10_CoUnitGenerated_form :
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
      { Yoneda10 : _ |
        Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_Generated (I)) Yoneda10}.
  Proof.
    intros. unshelve eexists.
    refine (fun G r => sval (Yoneda01_Generated_PolyIndexer i) G
                         (existT _ (existT _ R (@unitIndexer (ReIndexing0 R))) r) ) .
    abstract (intros; move; reflexivity).
  Defined.
  
  Lemma Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer : forall (I : obIndexer),
      forall (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0),
      forall (S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
      forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
      forall (G : obGenerator),
        ( sval (Yoneda10_CoUnitGenerated_form  ((ReIndexing1 sr o>Indexer ri) o>Indexer ij)) G )
        =1 ( sval (Yoneda01_Generated_PolyIndexer ij) G \o
             (sval (Yoneda10_CoUnitGenerated_form ri) G \o
              sval (Yoneda10_PolyElement (Yoneda01_View (Generating0 R)) (Generating1 sr)) G) ) .
  Proof.
    intros. move. intros g. simpl.
    rewrite -[in LHS]polyIndexer_unitIndexer. 
    rewrite -[in RHS]polyIndexer_unitIndexer. 
    rewrite -[in LHS]polyIndexer_morphism.
    symmetry. apply: Yoneda00_Generated_quotient.
  Qed.

  Definition Yoneda10_CoUnitGenerated_form_morphismIndexerOnly 
    := Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly
      Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer .
      
  Lemma Yoneda10_CoUnitGenerated_form_morphismIndexerOnly_ALT : forall (I : obIndexer),
      forall (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0),
      forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
      forall (G : obGenerator),
        ( sval (Yoneda10_CoUnitGenerated_form ( ri o>Indexer ij )) G )
        =1 ( sval (Yoneda01_Generated_PolyIndexer ij) G \o
             (sval (Yoneda10_CoUnitGenerated_form ri) G ) ) .
  Proof.
    intros. move. intros g. simpl.
    rewrite -[in LHS]polyIndexer_unitIndexer. 
    rewrite -[in RHS]polyIndexer_unitIndexer.
    reflexivity.
  Qed.

  (*TODO: ERASE
 Lemma Reflector_morphism_morphismReIndexer_morphismIndexer :
    forall (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_Generated_PolyIndexer Yoneda10_ff_),
    forall (Yoneda00_E_ : obIndexer -> _) (Yoneda01_E_ : forall I : obIndexer, _),
    forall (Yoneda10_hh_ : forall (I : obIndexer) (R : obReIndexer), 'Indexer(0 ReIndexing0 R ~> I )0 ->
             {Yoneda10 : forall A : obGenerator, Yoneda00_View (Generating0 R) A -> Yoneda00_E_ I A |
              Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_E_ I) Yoneda10})
      Yoneda01_E_Poly
      (* (Yoneda01_E_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_E_Poly) *)
      (Yoneda10_hh_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_E_Poly Yoneda10_hh_),
    forall (J : obIndexer),
      Yoneda10_morphismReIndexer_morphismIndexer
        Yoneda01_E_Poly
        (fun (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0) =>
           Yoneda10_PolyCoMod (Yoneda10_ff_ I R i) (Yoneda10_Reflector Yoneda10_hh_ I)).
  Proof.
    intros. move. intros. simpl. move. intros gs. simpl.
    rewrite Yoneda10_ff_morphismReIndexer_morphismIndexer. simpl.
    rewrite  (Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly
                Yoneda10_hh_morphismReIndexer_morphismIndexer).
    simpl. reflexivity.
  Qed. *)

  Lemma Reflector_morphism_morphismReIndexer_morphismIndexer :
    forall (Yoneda00_F_ : obIndexer -> _)
      (Yoneda01_F_ : forall I : obIndexer, _)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            {Yoneda10_ff_i : _ |
             Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_(I)) Yoneda10_ff_i})
      (Yoneda01_F_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 -> _)
      (* (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly) *)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
 forall (Yoneda00_E_ : obIndexer -> _)
   (Yoneda01_E_ : forall I : obIndexer, _),
 forall (Yoneda10_ee_ : forall I : obIndexer, {Yoneda10_ee_I : forall G : obGenerator, Yoneda00_F_(I) G -> Yoneda00_E_(I) G |
                                     Yoneda10_natural (Yoneda01_F_(I)) (Yoneda01_E_(I)) Yoneda10_ee_I}),
 forall (Yoneda01_E_Poly : forall I J : obIndexer, 'Indexer(0 I ~> J )0 -> _)
   (* (Yoneda01_E_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_E_Poly) *)
   (Yoneda10_ee_naturalIndexer : Yoneda10_naturalIndexer Yoneda01_F_Poly Yoneda01_E_Poly Yoneda10_ee_ ),
   Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_E_Poly
    (fun (I : obIndexer) (R : obReIndexer)
       (i : 'Indexer(0 ReIndexing0 R ~> I )0) =>
       Yoneda10_PolyCoMod (Yoneda10_ff_ I R i) (Yoneda10_ee_ I)) .
  Proof.
    intros. move. intros. simpl. move.  intros gs. simpl.
    rewrite Yoneda10_ff_morphismReIndexer_morphismIndexer.
    simpl. rewrite [LHS]Yoneda10_ee_naturalIndexer. reflexivity.
  Qed.

End Senses_convCoMod.

Reserved Notation "ff0 <~~ ff" (at level 70).
Reserved Notation "ff0_ <~~_ ff_" (at level 70).

Inductive convCoMod : forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda10_ff ( ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
    forall Yoneda10_ff0 ( ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ), Prop :=

(**  ----- the total/(multi-step) conversions -----  **)

| convCoMod_Refl :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
      Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 ),
      gg <~~ gg

| convCoMod_Trans :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
    forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 ),
    forall Yoneda10_uTrans (uTrans : 'CoMod(0 F ~> G @ Yoneda10_uTrans )0 ),
      ( uTrans <~~ gg ) ->
      forall Yoneda10_gg0 (gg0 : 'CoMod(0 F ~> G @ Yoneda10_gg0 )0 ),
        ( gg0 <~~ uTrans ) -> ( gg0 <~~ gg )

(**  ----- the congruences conversions -----  **)

| AtIndexMor_cong : forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0),
    forall Yoneda10_ff0_ (ff0_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff0_ )0),
      ff0_ <~~_ ff_ ->
      forall (I : obIndexer), (AtIndexMor ff0_ I) <~~ (AtIndexMor ff_ I)

| PolyCoMod_cong :
    forall Yoneda00_F Yoneda01_F' (F' : @obCoMod Yoneda00_F Yoneda01_F')
      Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda10_ff' (ff' : 'CoMod(0 F' ~> F @ Yoneda10_ff' )0)
      Yoneda00_F' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F' Yoneda01_F'')
      Yoneda10_ff_ (ff_ : 'CoMod(0 F'' ~> F' @ Yoneda10_ff_ )0)
      Yoneda10_ff_0 (ff_0 : 'CoMod(0 F'' ~> F' @ Yoneda10_ff_0 )0)
      Yoneda10_ff'0 (ff'0 : 'CoMod(0 F' ~> F @ Yoneda10_ff'0 )0),
      ff_0 <~~ ff_ -> ff'0 <~~ ff' -> ( ff_0 o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )
        
| PolyTransf_cong :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
      (transf : {transf : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A |
                 Yoneda10_natural Yoneda01_F Yoneda01_G transf}) 
      (A : obGenerator)
      Yoneda10_ff (ff : 'CoMod(0 View A ~> F @ Yoneda10_ff )0)
      Yoneda10_ff0 (ff0 : 'CoMod(0 View A ~> F @ Yoneda10_ff0 )0),
      ff0 <~~ ff -> ( ff0 o>Transf_ transf @ G ) <~~ ( ff o>Transf_ transf @ G )

| CoUnitGenerated_cong : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) Yoneda10_rr
      (rr : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0),
    forall Yoneda10_rr0 (rr0 : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr0 )0),
      rr0 <~~ rr -> (rr0 o>CoMod 'CoUnitGenerated @ i) <~~ (rr o>CoMod 'CoUnitGenerated @ i)

(** ----- the constant conversions which are used during the PolyTransf polymorphism elimination ----- **)

| PolyTransf_UnitCoMod :
    forall (B : obGenerator) Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G) transf,
      ( PolyElement G (proj1_sig transf _ (@unitGenerator B)) )
          <~~ ( (@'UnitCoMod (View B)) o>Transf_ transf @ G )

| PolyTransf_PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
      transf (A : obGenerator),
    forall (f : Yoneda00_F A),
        ( PolyElement G (proj1_sig transf _ f) )
          <~~ ( (PolyElement F f) o>Transf_ transf @ G )

| PolyTransf_CoUnitGenerated :
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
        forall (G : obGenerator) Yoneda10_rr
          (rr : 'CoMod(0 View G ~> View (Generating0 R) @ Yoneda10_rr )0),
        forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
          (transf : {transf : ( forall G : obGenerator, Yoneda00_Generated I G -> Yoneda00_E G ) |
                     Yoneda10_natural (Yoneda01_Generated I) Yoneda01_E transf}),
          ( PolyElement E (proj1_sig transf _
                                      (sval (Yoneda10_CoUnitGenerated i Yoneda10_rr) G (@unitGenerator G))) )
            <~~ ( (rr o>CoMod 'CoUnitGenerated @ i) o>Transf_ transf @ E
                : 'CoMod(0 View G ~> E @ _ )0 )

(** ----- the constant conversions which are used during the PolyCoMod polymorphism elimination ----- **)

| PolyCoMod'UnitCoMod :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)    
      Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0),
      gg <~~ ( gg o>CoMod ('UnitCoMod) )

| PolyCoMod_UnitCoMod :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)    
      Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0),
      gg <~~ ( ('UnitCoMod) o>CoMod gg )

| PolyElement_PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (A : obGenerator) (f : Yoneda00_F A) A' (a : Yoneda00_View A A'),
      ( PolyElement F (proj1_sig Yoneda01_F A A' a f) )
        <~~ ( (PolyElement (View A) a) o>CoMod (PolyElement F f) )

| CoUnitGenerated_PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (G : obGenerator) (f : Yoneda00_F G),
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
        forall Yoneda10_rr (rr : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0),
          ( PolyElement (AtIndexOb Generated(I))
                         (sval (Yoneda01_Generated_PolyIndexer i) G
                               (existT _ (existT _ R unitIndexer) (sval Yoneda10_rr G f)) ) )
          <~~ ( (PolyElement F f) o>CoMod (rr o>CoMod 'CoUnitGenerated @ i)
              : 'CoMod(0 View G ~> AtIndexOb Generated(I) @ _ )0 )

| Reflector_PolyElement :
    forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall (I : obIndexer), forall (G : obGenerator) (i : Yoneda00_Generated I G),
        (PolyElement (AtIndexOb F_(I)) ( ( sval (Yoneda10_ff_ _ _ (projT2 (projT1 i))) G (projT2 i) ) ))
          <~~ ( (PolyElement (AtIndexOb Generated(I)) i)
                o>CoMod ( AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer, Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ I )
              : 'CoMod(0 View G ~> AtIndexOb F_(I) @ _ )0 )

| CoUnitGenerated_morphism :
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
      forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F) Yoneda10_rr
        (rr : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0),
      forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E) Yoneda10_ff
        (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0),
        ( (ff o>CoMod rr) o>CoMod 'CoUnitGenerated @ i )
          <~~ ( ff o>CoMod (rr o>CoMod 'CoUnitGenerated @ i)
              : 'CoMod(0 E ~> AtIndexOb Generated(I) @ _ )0 )

(*TODO: this is ?derivable? , instantiate ee_ by [[ hh_ ]]_ *)
| Reflector_morphism :
    forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda10_ee_ (ee_ : 'CoMod_(0 F_ ~> E_ @ Yoneda10_ee_ )0 ),
    forall (Yoneda01_E_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_E_Poly)
      (Yoneda10_ee_naturalIndexer : Yoneda10_naturalIndexer Yoneda01_F_Poly Yoneda01_E_Poly Yoneda10_ee_ ),
    forall (J : obIndexer),
      ( AtIndexMor [[ (fun (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0)
            => ff_ _ _ i o>CoMod AtIndexMor ee_(I) )
             @ Yoneda01_E_Poly_functorIndexer
           , (Reflector_morphism_morphismReIndexer_morphismIndexer Yoneda10_ff_morphismReIndexer_morphismIndexer Yoneda10_ee_naturalIndexer) ]]_ J )
        <~~ ( AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J o>CoMod AtIndexMor ee_(J)
            : 'CoMod(0 AtIndexOb Generated(J) ~> AtIndexOb E_(J) @ _ )0 )
(*TODO: ERASE
| Reflector_morphism :
    forall (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb Generated(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_Generated_PolyIndexer Yoneda10_ff_),
    forall (Yoneda00_E_ : obIndexer -> _)
      (Yoneda01_E_ : forall I : obIndexer, _)
      (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_),
    forall (Yoneda10_hh_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (hh_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb E_(I) @ (Yoneda10_hh_ _ _ (i)) )0 )
      Yoneda01_E_Poly (Yoneda01_E_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_E_Poly)
      (Yoneda10_hh_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_E_Poly Yoneda10_hh_),
    forall (J : obIndexer),
      ( AtIndexMor [[ (fun (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0)
            => ff_ _ _ i o>CoMod AtIndexMor [[ hh_ @ Yoneda01_E_Poly_functorIndexer , Yoneda10_hh_morphismReIndexer_morphismIndexer ]]_ I )
             @ Yoneda01_E_Poly_functorIndexer
           , (Reflector_morphism_morphismReIndexer_morphismIndexer Yoneda10_ff_morphismReIndexer_morphismIndexer Yoneda10_hh_morphismReIndexer_morphismIndexer J) ]]_ J )
        <~~ ( AtIndexMor [[ ff_ @ Yoneda01_Generated_PolyIndexer_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J
              o>CoMod AtIndexMor [[ hh_ @ Yoneda01_E_Poly_functorIndexer , Yoneda10_hh_morphismReIndexer_morphismIndexer ]]_ J
            : 'CoMod(0 AtIndexOb Generated(J) ~> AtIndexOb E_(J) @ _ )0 )
*)
| Reflector_CoUnitGenerated :
    forall (Yoneda00_F_ : obIndexer -> _ ) (Yoneda01_F_ : forall I : obIndexer, _ ) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
     (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _ )
     (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
           'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)(R)(i)) )0 )
     (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
     (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
        forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E) Yoneda10_rr
          (rr : 'CoMod(0 E ~> View (Generating0 R) @ Yoneda10_rr )0),
          ( rr o>CoMod ff_(I)(R)(i) )
            <~~ ( (rr o>CoMod 'CoUnitGenerated @ i)
                  o>CoMod AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer ,
                                        Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ I
                : 'CoMod(0 E ~> AtIndexOb F_(I) @ Yoneda10_PolyCoMod
                                 (Yoneda10_CoUnitGenerated i Yoneda10_rr)
                                 (Yoneda10_Reflector Yoneda10_ff_ I) )0 )

(** ----- the constant conversions which are only for the wanted sense of generated-functor-along-reindexing-grammar ----- **)

| AtIndexMor'MorCoMod_indexed :
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _)
           (ff_ : (forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0 )),
    forall (J : obIndexer),
      (ff_ J  : 'CoMod(0 AtIndexOb E_ J ~> AtIndexOb F_ J @ Yoneda10_ff_ J )0 )
        <~~ (AtIndexMor (MorCoMod_indexed ff_) J
             : 'CoMod(0 AtIndexOb E_ J ~> AtIndexOb F_ J @ Yoneda10_ff_ J )0 )

| UnitCoMod_'PolyElement : forall (G : obGenerator),
    (PolyElement (View G) ((@unitGenerator G) : 'Generator(0 G ~> G)0))
      <~~ (@'UnitCoMod (View G)) 

| CoUnitGenerated'PolyElement :
    forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 (ReIndexing0 R) ~> I )0),
    forall (G : obGenerator) (f : Yoneda00_View (Generating0 R) G),
      (PolyElement (AtIndexOb Generated(I)) (sval (Yoneda10_CoUnitGenerated_form i) G f))
        <~~ ( (PolyElement (View (Generating0 R )) f) o>CoMod 'CoUnitGenerated @ i
            : 'CoMod(0 View G ~> AtIndexOb Generated(I) @ _ )0 )

(* for sense , for secondo reduction *)
| Reflector'CoUnitGenerated :
    (* ALT: knowing existence, this is equivalent as general form :
     forall Yoneda01_Generated_PolyIndexer_morphismIndexer, forall ... *)
    forall (I : obIndexer),
      (@'UnitCoMod (AtIndexOb Generated(I)))
        <~~ ( AtIndexMor [[ (fun (I : obIndexer) (R : obReIndexer) (ri : 'Indexer(0 ReIndexing0 R ~> I )0)
                => (@'UnitCoMod (View (Generating0 R))) o>CoMod 'CoUnitGenerated @ ri)
                 @ Yoneda01_Generated_PolyIndexer_functorIndexer , 
               Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer ]]_ I
            : 'CoMod(0 AtIndexOb Generated(I) ~> AtIndexOb Generated(I) @ _ )0 )

(** ----- the constant conversions which are only for the confluence lemma ---- **)

(** none **)

(** ----- the constant symmetrized-conversions which are symmetrized-derivable by using the finished cut-elimination lemma ----- **)

(**
(*TODO: COMMENT*)        
| PolyCoMod_morphism : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                         Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
                         Yoneda10_ff' (ff' : 'CoMod(0 F' ~> F @ Yoneda10_ff' )0),
      forall Yoneda00_F'' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F'' Yoneda01_F'')
        Yoneda10_ff_ (ff_ : 'CoMod(0 F'' ~> F' @ Yoneda10_ff_ )0),
      forall Yoneda00_F''' Yoneda01_F''' (F''' : @obCoMod Yoneda00_F''' Yoneda01_F''')
        Yoneda10_ff__ (ff__ : 'CoMod(0 F''' ~> F'' @ Yoneda10_ff__ )0),
        ((ff__ o>CoMod ff_) o>CoMod ff')
          <~~ (ff__ o>CoMod (ff_ o>CoMod ff')
             : 'CoMod(0 F''' ~> F @ _ )0 ) **)

| ViewView_'PolyElement :
    forall (H G : obGenerator) Yoneda01_ff (ff : 'CoMod(0 View G ~> View H @ Yoneda01_ff)0),
    (PolyElement (View H) (sval Yoneda01_ff G (@unitGenerator G) : 'Generator(0 G ~> H)0))
      <~~ ff

| PolyTransf_morphism :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)    
      (transf : {transf : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A |
                 Yoneda10_natural Yoneda01_F Yoneda01_G transf}) 
      (A : obGenerator)
      Yoneda10_ff (ff : 'CoMod(0 View A ~> F @ Yoneda10_ff )0),
    forall A' Yoneda10_aa (aa : 'CoMod(0 View A' ~> View A @ Yoneda10_aa )0),
      ( (aa o>CoMod ff) o>Transf_ transf @ G )
        <~~ ( aa o>CoMod (ff o>Transf_ transf @ G) )

| PolyTransf_morphismPolyTransf : forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                 Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
                 (transf : {transf : ( forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A ) |
                                     Yoneda10_natural Yoneda01_F Yoneda01_G transf}) 
                 (A : obGenerator) Yoneda10_ff
                 (ff : 'CoMod(0 View A ~> F @ Yoneda10_ff )0)
                 Yoneda00_H Yoneda01_H (H : @obCoMod Yoneda00_H Yoneda01_H)
                 (transf' : {transf : ( forall A : obGenerator, Yoneda00_G A -> Yoneda00_H A ) |
                             Yoneda10_natural Yoneda01_G Yoneda01_H transf}) (transf_transf' : nat),
    (ff o>Transf_ (PolyTransf_morphismPolyTransf_transf transf transf') @ H)
      <~~ ((ff o>Transf_ transf @ G) o>Transf_ transf' @ H)

| View_'PolyElement :
    forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
      (G : obGenerator) Yoneda01_ff (ff : 'CoMod(0 View G ~> F @ Yoneda01_ff)0),
    (PolyElement F (sval Yoneda01_ff G (@unitGenerator G) : Yoneda00_F G))
      <~~ ff

| CoUnitGenerated_morphismReIndexer_morphismIndexer :
  forall (I : obIndexer) (R : obReIndexer) (ri : 'Indexer(0 (ReIndexing0 R) ~> I )0),
  forall (S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
  forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
  forall (G : obGenerator) Yoneda10_ff (ff : 'CoMod(0 View G ~> View (Generating0 S) @ Yoneda10_ff)0),
    ( ff o>CoMod 'CoUnitGenerated
                 @ ((ReIndexing1 sr o>Indexer ri) o>Indexer ij) )
    <~~ ( ( ( ff o>CoMod (PolyElement (View (Generating0 R)) (Generating1 sr)) )
            o>CoMod 'CoUnitGenerated @ ri )
          o>Transf_ (Yoneda01_Generated_PolyIndexer ij)
        : 'CoMod(0 View G ~> AtIndexOb Generated(J) @ _ )0 )

| Reflector_naturalIndexer :
    forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall (I J : obIndexer) (j : 'Indexer(0 I ~> J )0),
    forall (G : obGenerator) Yoneda10_ii (ii : 'CoMod(0 View G ~> AtIndexOb Generated(I) @ Yoneda10_ii )0),
      ( ( ii o>CoMod AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ I )
          o>Transf_ (Yoneda01_F_Poly _ _ j) @ (AtIndexOb F_(J)) )
        <~~ ( ( ii o>Transf_ (Yoneda01_Generated_PolyIndexer j) @ (AtIndexOb Generated(J)) )
              o>CoMod AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J
            : 'CoMod(0 View G ~> AtIndexOb F_(J) @ _ )0 )

where "gg0 <~~ gg" := (@convCoMod _ _ _ _ _ _ _ gg _ gg0)

with convCoMod_indexed (**memo: non-recursive , only some form of nested grammatical bookeeping **) :
       forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
       forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
       forall Yoneda10_ff_ ( ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 ),
       forall Yoneda10_ff0_ ( ff0_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff0_ )0 ), Prop :=

| MorCoMod_indexed_cong (**memo: some form of extensionality *):
    forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
    forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
    forall (Yoneda10_ff_ : forall I : obIndexer, _)
      (ff_ : forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff_(I)) )0 ),
    forall (Yoneda10_ff0_ : forall I : obIndexer, _)
      (ff0_ : forall (I : obIndexer), 'CoMod(0 AtIndexOb E_(I) ~> AtIndexOb F_(I) @ (Yoneda10_ff0_(I)) )0 ),
      (forall I : obIndexer, ff0_(I) <~~ ff_(I)) ->
      (MorCoMod_indexed ff0_) <~~_ (MorCoMod_indexed ff_)

| Reflector_cong :
    forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
      (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
      (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
      (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
      (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
    forall (Yoneda10_ff0_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
      (ff0_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
            'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff0_ _ _ (i)) )0 )
      (Yoneda10_ff0_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff0_),
      ( forall (I : obIndexer) (**memo: allowed eveywhere-simultaneously **), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
          ff0_ _ _ i <~~ ff_ _ _ i ) ->
      (**memo:  possible to do more direct-form (forall J , AtIndexMor [[ ff0_ ]]_ J <~~ _ ) and avoid another conversion relation <~~_ for only morCoMod_indexed *)
      [[ ff0_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff0_morphismReIndexer_morphismIndexer ]]_
        <~~_ [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_

where "gg0_ <~~_ gg_" := (@convCoMod_indexed _ _ _ _ _ _ _ _ _ gg_ _ gg0_).

Hint Constructors convCoMod.
Hint Constructors convCoMod_indexed.

Section SomeInstances.
(** this lemma formulation is only for some PolyElement input .. no generalization , which would be derivable by using the finished cut-elimination lemma **)
Lemma CoUnitGenerated_morphismReIndexer_morphismIndexer_PolyElement_ALT :
  forall (I : obIndexer) (R : obReIndexer) (ri : 'Indexer(0 (ReIndexing0 R) ~> I )0),
  forall (S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
  forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
  forall (G : obGenerator) (f : Yoneda00_View (Generating0 S) G),
    ( PolyElement (AtIndexOb Generated(J))
                  (sval (Yoneda01_Generated_PolyIndexer ij) G
                        (sval (Yoneda10_CoUnitGenerated_form ri) G
                              (sval (Yoneda10_ViewGenerating_PolyReIndexer_form sr) G f))) )
      <~~ ( (PolyElement (View (Generating0 S)) f)
            o>CoMod 'CoUnitGenerated
                    @ ((ReIndexing1 sr o>Indexer ri) o>Indexer ij)
          : 'CoMod(0 View G ~> AtIndexOb Generated(J) @ _ )0 ) .
Proof.
  intros. eapply convCoMod_Trans; first by exact: CoUnitGenerated'PolyElement.
  rewrite Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer.
  exact: convCoMod_Refl.
Qed.

Hypothesis Hyp_convCoMod_Sym :
  forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
  forall Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G),
  forall Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 ),
  forall Yoneda10_gg0 (gg0 : 'CoMod(0 F ~> G @ Yoneda10_gg0 )0 ),
    ( gg0 <~~ gg ) -> ( gg <~~ gg0 ).

(** memo: the more-general (than [(PolyElement (View (Generating0 S)) f)] input) lemma which will be derivable by using the finished cut-elimination lemma **)
Lemma CoUnitGenerated_morphismReIndexer_morphismIndexer_PolyElement :
  forall (I : obIndexer) (R : obReIndexer) (ri : 'Indexer(0 (ReIndexing0 R) ~> I )0),
  forall (S : obReIndexer) (sr : 'ReIndexer(0 S ~> R )0),
  forall (J : obIndexer) (ij : 'Indexer(0 I ~> J )0),
  forall (G : obGenerator) (f : Yoneda00_View (Generating0 S) G),
    ( (PolyElement (View (Generating0 S)) f)
        o>CoMod 'CoUnitGenerated
                @ ((ReIndexing1 sr o>Indexer ri) o>Indexer ij) )
      <~~ ( ( ( (PolyElement (View (Generating0 S)) f)
                o>CoMod (PolyElement (View (Generating0 R)) (Generating1 sr)) )
              o>CoMod 'CoUnitGenerated @ ri )
            o>Transf_ (Yoneda01_Generated_PolyIndexer ij)
          : 'CoMod(0 View G ~> AtIndexOb Generated(J) @ _ )0 ) .
Proof.
  intros. eapply convCoMod_Trans.
  - { eapply convCoMod_Trans. eapply PolyTransf_cong. eapply CoUnitGenerated_cong. apply: PolyElement_PolyElement. 
      eapply convCoMod_Trans. eapply PolyTransf_cong. apply: CoUnitGenerated'PolyElement.
      eapply PolyTransf_PolyElement. }
  - apply: Hyp_convCoMod_Sym.
    { eapply convCoMod_Trans. apply: CoUnitGenerated'PolyElement.
      rewrite Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer.
      simpl. exact: convCoMod_Refl. }
Qed. 

(** memo: the more-general (than [(PolyElement (View (Generating0 S)) f)] input) lemma will be derivable by using the finished cut-elimination lemma **)
Lemma Reflector_naturalIndexer_PolyElement :
  forall (Yoneda00_F_ : obIndexer -> _) (Yoneda01_F_ : forall I : obIndexer, _) Yoneda01_F_Poly
    (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
    (Yoneda10_ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), _)
    (ff_ : forall (I : obIndexer), forall (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
          'CoMod(0 View (Generating0 R) ~> AtIndexOb F_(I) @ (Yoneda10_ff_ _ _ (i)) )0 )
    (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
    (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
  forall (I J : obIndexer) (j : 'Indexer(0 I ~> J )0),
  forall (G : obGenerator) (ii : Yoneda00_Generated(I) G) (*is some PolyElement ??*),
    ( ( (PolyElement (AtIndexOb Generated(I)) ii) o>CoMod AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ I )
        o>Transf_ (Yoneda01_F_Poly _ _ j) @ (AtIndexOb F_(J)) )
      <~~ ( ( (PolyElement (AtIndexOb Generated(I)) ii) o>Transf_ (Yoneda01_Generated_PolyIndexer j) @ (AtIndexOb Generated(J)) )
            o>CoMod AtIndexMor [[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_ J
          : 'CoMod(0 View G ~> AtIndexOb F_(J) @ _ )0 ).
Proof.
  intros. eapply convCoMod_Trans.
  - { eapply convCoMod_Trans. eapply PolyCoMod_cong. eapply PolyTransf_PolyElement. apply: convCoMod_Refl.
      eapply convCoMod_Trans. apply: Reflector_PolyElement.
      simpl. rewrite (Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly Yoneda10_ff_morphismReIndexer_morphismIndexer). 
      exact: convCoMod_Refl. }
  - apply: Hyp_convCoMod_Sym.
    { eapply convCoMod_Trans. eapply PolyTransf_cong. apply: Reflector_PolyElement. 
      eapply PolyTransf_PolyElement. }
Qed.

End SomeInstances.

Scheme  convCoMod_convCoMod_indexed_ind :=
  Induction for convCoMod Sort Prop
  with  convCoMod_indexed_convCoMod_ind :=
    Induction for convCoMod_indexed Sort Prop.
Combined Scheme convCoMod_convCoMod_indexed_mutind from
         convCoMod_convCoMod_indexed_ind, convCoMod_indexed_convCoMod_ind.
Check convCoMod_convCoMod_indexed_mutind .
(**memo: Yoneda01_F_Poly_functorIndexer and Yoneda10_ff_morphismReIndexer not used to show convCoMod_sense **)
(*Lemma convCoMod_sense
  : (forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
    forall Yoneda10_ff0 (ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ),
    forall H : ff0 <~~ ff, forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G')).
Proof.
  intros.
  eapply convCoMod_convCoMod_indexed_ind with (P0:=( fun _ _ _ _ _ _ Yoneda10_ff_ _ Yoneda10_ff0_ _ _  =>
                forall I : obIndexer, forall G' : obGenerator,
                    (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G'))).


                                                                                            
  apply (convCoMod_convCoMod_indexed_ind (P0:=( fun _ _ _ _ _ _ Yoneda10_ff_ _ Yoneda10_ff0_ _ _  =>
                forall I : obIndexer, forall G' : obGenerator,
                    (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')))). ( fun _ _ _ _ _ _ Yoneda10_ff _ _ _ _  =>
                     forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G') ).
  eapply  convCoMod_convCoMod_indexed_mutind with
  (P0 := fun Yoneda00_E_ Yoneda01_E_ E_ Yoneda00_F_ Yoneda01_F_ F_ Yoneda10_ff_ ff_
           Yoneda10_ff0_ ff0_ H =>
           ( forall I : obIndexer, forall G' : obGenerator,
                 (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G'))).
  
*)

(*         eapply convCoMod_convCoMod_indexed_mutind with
  (P:=( fun _ _ _ _ _ _ Yoneda10_ff _ Yoneda10_ff0 _ _  =>
                 forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G') ))
           (P0:=( fun _ _ _ _ _ _ Yoneda10_ff_ _ Yoneda10_ff0_ _ _  =>
                    forall I : obIndexer, forall G' : obGenerator,
                        (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')) ).

  Lemma convCoMod_sense
  : (forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
    forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
    forall Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
    forall Yoneda10_ff0 (ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ),
    forall H : ff0 <~~ ff, ( fun _ _ _ _ _ _ Yoneda10_ff _ Yoneda10_ff0 _ _  =>
                     forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G') )
     Yoneda00_F Yoneda01_F F Yoneda00_E Yoneda01_E E Yoneda10_ff ff Yoneda10_ff0 ff0 H )
    /\ (forall Yoneda00_E_ Yoneda01_E_ (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_)
         Yoneda00_F_ Yoneda01_F_ (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_)
         Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0)
         Yoneda10_ff0_ (ff0_ : 'CoMod_(0 E_ ~> F_  @ Yoneda10_ff0_ )0),
          forall H : ff0_ <~~_ ff_,
            ( fun _ _ _ _ _ _ Yoneda10_ff_ _ Yoneda10_ff0_ _ _  =>
                forall I : obIndexer, forall G' : obGenerator,
                    (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G'))
      Yoneda00_E_ Yoneda01_E_ E_ Yoneda00_F_ Yoneda01_F_ F_ Yoneda10_ff_ ff_ Yoneda10_ff0_ ff0_ H ).
Proof.
  About  convCoMod_convCoMod_indexed_mutind.
  eapply convCoMod_convCoMod_indexed_mutind with
  (P:=( fun _ _ _ _ _ _ Yoneda10_ff _ Yoneda10_ff0 _ _  =>
                 forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G') ))
           (P0:=( fun _ _ _ _ _ _ Yoneda10_ff_ _ Yoneda10_ff0_ _ _  =>
                    forall I : obIndexer, forall G' : obGenerator,
                        (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')) ).
  eapply  convCoMod_convCoMod_indexed_mutind with
  (P0 := fun Yoneda00_E_ Yoneda01_E_ E_ Yoneda00_F_ Yoneda01_F_ F_ Yoneda10_ff_ ff_
           Yoneda10_ff0_ ff0_ H =>
           ( forall I : obIndexer, forall G' : obGenerator,
                 (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G'))).
  
  
  evar (T00 : Type).
  evar (P00 : T00).
  evar (T01 : Type).
  evar (P01 : T01).
  split. intros. eapply convCoMod_convCoMod_indexed_ind. (*with (P0:=P01).*)
  
  
  intros Yoneda00_F Yoneda01_F F
   Yoneda00_E Yoneda01_E E


   have [:ppp] [:qq] dd := (@convCoMod_convCoMod_indexed_mutind ppp qq).
  intros Yoneda00_F Yoneda01_F F
   Yoneda00_E Yoneda01_E E
   Yoneda10_ff ff
   Yoneda10_ff0 ff0 _ . refine (forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G')).
  intros. refine (forall I : obIndexer, forall G' : obGenerator,
              (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')).
  simpl in * . apply dd.
  split. intros.
    evar (T00 : Type).
  evar (P00 : T00).
  eapply convCoMod_convCoMod_indexed_ind  with (P0 := P00).
  Grab Existential Variables.
   Existential 1 := (forall I : obIndexer, forall G' : obGenerator,
              (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')).
   intros. refine (forall I : obIndexer, forall G' : obGenerator,
              (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G')).
  evar (T00 : Type).
  evar (P00 : T00).
  split; first last. intros. 2: eapply convCoMod_convCoMod_indexed_ind with (P0 := P00).
  split; first last. intros. 
  2: unshelve eapply convCoMod_convCoMod_indexed_ind.
  
  eapply convCoMod_convCoMod_indexed_mutind. About convCoMod_convCoMod_indexed_ind.
  intros until ff0. intros conv_ff.
  elim :  Yoneda00_E Yoneda01_E E Yoneda00_F Yoneda01_F F
                     Yoneda10_ff ff Yoneda10_ff0 ff0 / conv_ff .
*)

Lemma convCoMod_sense
  : (forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
        forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
        forall Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
        forall Yoneda10_ff0 (ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ),
          ff0 <~~ ff -> forall G' : obGenerator, (proj1_sig Yoneda10_ff G') =1 (proj1_sig Yoneda10_ff0 G') )
    /\ (forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly)
         Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
         Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0)
         Yoneda10_ff0_ (ff0_ : 'CoMod_(0 E_ ~> F_  @ Yoneda10_ff0_ )0),
          ff0_ <~~_ ff_ ->
          forall I : obIndexer, forall G' : obGenerator,
              (proj1_sig (Yoneda10_ff_(I)) G') =1 (proj1_sig (Yoneda10_ff0_(I)) G') ).
Proof.
  apply convCoMod_convCoMod_indexed_mutind.

  (**  ----- the total/(multi-step) conversions -----  **)
  - (* convCoMod_Refl *)  intros. move. intros f. reflexivity.
  - (* convCoMod_Trans *)  intros until 1. intros gg_eq . intros until 1. intros uTrans_eq.
    intros. move. intros f. rewrite gg_eq uTrans_eq . reflexivity.

  (**  ----- the congruences conversions -----  **)
  - (* AtIndexMor_cong *) intros until 1. intros Heq. exact: Heq.
  - (* PolyCoMod_cong *)  intros until 1. intros ff__eq . intros ? ff'_eq ? . move. intros f'.
    rewrite /Yoneda10_PolyCoMod /= . rewrite ff__eq ff'_eq. reflexivity.
  - (* PolyTransf_cong *)  intros until 2. intros ff_eq . intros. move. intros a.
    simpl. (* rewrite /Yoneda10_PolyTransf /= . *) rewrite ff_eq. reflexivity.
  - (* CoUnitGenerated_cong *)  intros until 1. intros rr_eq . intros. move. intros f.
    simpl. rewrite rr_eq. reflexivity.

  (** ----- the constant conversions which are used during the PolyTransf polymorphism elimination ----- **)
  - (* PolyTransf_UnitCoMod *) intros. move. intros b. 
    simpl. rewrite [RHS](proj2_sig transf).  simpl.
    congr 1 (proj1_sig transf _) . rewrite -unitGenerator_polyGenerator ; reflexivity . 
  - (* PolyTransf_PolyElement *) intros. move. intros a. simpl. symmetry.
    exact: (proj2_sig transf). 
  - (* PolyTransf_CoUnitGenerated *) intros. move. intros g. simpl.
    rewrite (proj2_sig transf). simpl.
    rewrite [g o>Generator _ in RHS](proj2_sig Yoneda10_rr). simpl.
    rewrite -[in RHS]unitGenerator_polyGenerator. reflexivity.
  
  (** ----- the constant conversions which are used during the PolyCoMod polymorphism elimination ----- **)
  - (* PolyCoMod'UnitCoMod *) intros. move. intros f. 
    simpl.  reflexivity.
  - (* PolyCoMod_UnitCoMod *) intros. move. intros f. 
    simpl.  reflexivity.
  - (* PolyElement_PolyElement *) intros. move. intros a'. 
    simpl.  symmetry. exact: (proj1 (proj2_sig Yoneda01_F)).
  - (* CoUnitGenerated_PolyElement *) intros. move. intros g. simpl.
    rewrite -[in LHS](proj2_sig Yoneda10_rr).
    simpl. reflexivity.
  - (* Reflector_PolyElement *) intros. move. intros g. simpl.
    rewrite [in RHS](proj2_sig (Yoneda10_ff_ _ _ _)). simpl. reflexivity.
  - (* CoUnitGenerated_morphism *) intros. move. intros e. simpl.
    reflexivity.
  - (* Reflector_morphism *) intros. move. intros jj. simpl.
    reflexivity.
  - (* Reflector_CoUnitGenerated *) intros. move. intros e. simpl.
    rewrite -[in LHS]polyIndexer_unitIndexer . reflexivity.

  (** ----- the constant conversions which are only for the wanted sense of generated-functor-along-reindexing-grammar ----- **)
  - (* AtIndexMor'MorCoMod_indexed *)
    intros. move. intros j. simpl. reflexivity.
  - (* UnitCoMod_'PolyElement *)
    intros. move. intros g. simpl.
    exact: unitGenerator_polyGenerator.
  - (* CoUnitGenerated'PolyElement  *)
    intros. move. intros g. simpl. reflexivity.
  - (* Reflector'CoUnitGenerated *)
    intros. move. intros i. simpl.
    rewrite -[in LHS]polyIndexer_unitIndexer. destruct i as [ [? ?] ?]; reflexivity.

  (** ----- the constant symmetrized-conversions which are symmetrized-derivable by using the finished cut-elimination lemma ----- **)
(**  - (* PolyCoMod_morphism *) intros. move. intros f.
    reflexivity (* associativity of function composition *). **)
  - (* ViewView_'PolyElement *)
    intros. move. intros g. simpl.
    rewrite [g in LHS]unitGenerator_polyGenerator.
    rewrite -[in LHS](proj2_sig Yoneda01_ff). simpl. reflexivity.
  - (* PolyTransf_morphism *)  intros. move. intros g. reflexivity.
  - (* PolyTransf_morphismPolyTransf *) intros. move. intros g. reflexivity.
  - (* View_'PolyElement *)
    intros. move. intros g. simpl.
    rewrite [g in LHS]unitGenerator_polyGenerator.
    rewrite -[in LHS](proj2_sig Yoneda01_ff). simpl. reflexivity.
  - (* CoUnitGenerated_morphismReIndexer_morphismIndexer *)
    intros. move. intros g. simpl.
    rewrite [RHS]Yoneda10_CoUnitGenerated_form_morphismReIndexer_morphismIndexer.
    simpl. reflexivity.
  - (* Reflector_naturalIndexer *)
    intros. move. intros g. simpl.
    exact: (Yoneda10_morphismReIndexer_morphismIndexer_to_Yoneda10_morphismIndexerOnly
              Yoneda10_ff_morphismReIndexer_morphismIndexer).

    (*TODO: ERASE
    (** ----- the constant conversions which are derivable immediately without using the finished cut-elimination lemma ----- **)
  - (* Reflector_morphism_derivable *) intros. move. intros jj. simpl.
    reflexivity. *)

  - (* MorCoMod_indexed_cong *) intros until 1. intros Heq. exact: Heq. 
  - (*  Reflector_cong *) intros until 4. intros ff_eq . intros. move. intros ii.
    simpl. exact: ff_eq.
Qed.

Lemma convCoMod_sense'_mut
  : (forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
        forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
        forall Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
        forall Yoneda10_ff0 (ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ),
          ff0 <~~ ff -> Yoneda10_ff = Yoneda10_ff0 )
    /\ (forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly)
         Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
         Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0)
         Yoneda10_ff0_ (ff0_ : 'CoMod_(0 E_ ~> F_  @ Yoneda10_ff0_ )0),
          ff0_ <~~_ ff_ ->
          forall I : obIndexer, Yoneda10_ff_(I) = Yoneda10_ff0_(I) ).
Proof. split; intros; apply: ax1_Yoneda10_natural;
         [apply: (proj1 convCoMod_sense) | apply: (proj2 convCoMod_sense)]; eassumption.
Qed.

Definition convCoMod_sense' := proj1 convCoMod_sense'_mut. 
Definition convCoMod_sense'_indexed := proj2 convCoMod_sense'_mut.

Notation max m n := ((Nat.add m (Nat.sub n m))%coq_nat).

Scheme  morCoMod_morCoMod_indexed_ind :=
  Induction for morCoMod Sort Prop
  with  morCoMod_indexed_morCoMod_ind :=
    Induction for morCoMod_indexed Sort Prop.
Combined Scheme morCoMod_morCoMod_indexed_mutind from
         morCoMod_morCoMod_indexed_ind, morCoMod_indexed_morCoMod_ind.
Scheme  morCoMod_morCoMod_indexed_rect :=
  Induction for morCoMod Sort Type
  with  morCoMod_indexed_morCoMod_rect :=
    Induction for morCoMod_indexed Sort Type.
Definition morCoMod_morCoMod_indexed_mutrect P P0 a b c d e f g h := 
  pair (@morCoMod_morCoMod_indexed_rect P P0 a b c d e f g h)
       (@morCoMod_indexed_morCoMod_rect P P0 a b c d e f g h ).

Definition grade_mut : (forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
                    Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
                    Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 ), nat ) *
                 (forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
                    Yoneda00_G_ Yoneda01_G_ Yoneda01_G_Poly (G_ : @obCoMod_indexed Yoneda00_G_ Yoneda01_G_ Yoneda01_G_Poly)
                    Yoneda10_gg_ (gg_ : 'CoMod_(0 F_ ~> G_ @ Yoneda10_gg_ )0 ), nat ). 
Proof.
  apply morCoMod_morCoMod_indexed_mutrect.
  - (* AtIndexMor *) intros ? ? ? ? ? ? ? ? ?  ff_ IHff_ (*I*) _ . exact: (S IHff_).
  - (* PolyCoMod *) intros ? ? F ? ? F' ? ff' IHff' ? ? F'' ? ff_ IHff_ .
    exact: ( 2 * (S (IHff' + IHff_)%coq_nat ) )%coq_nat .
  - (* PolyTransf *) intros ? ?  F ? ? G transf A ? ff IHff .
    exact: (S IHff).
  - (* UnitCoMod *) intros ? ? F . exact: (S ( (* gradeOb F = *) O )).
  - (* PolyElement *) intros ? ? F ? f . exact: (S ( O (* = grade? *) )).
  - (* CoUnitGenerated *) intros ? ? ? ? ? ? ? rr IHrr.
    exact: (S (S IHrr)).
  - (* MorCoMod_indexed *) intros ? ? ? ? ? ? ? ? ? ff_ IHff_ .
    exact: (S (max (IHff_ ObIndexer1) (IHff_ ObIndexer2) )).
  - (* Reflector *) intros ? ? ? F_ ? ff_ IHff_ ? ? .
    exact: (S (S (max (max (IHff_(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1))
                           (IHff_(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
                      (max (IHff_(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2))
                           (IHff_(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))))).
Defined.

Definition grade := fst grade_mut.
Definition grade_indexed := snd grade_mut.

Arguments grade_mut : simpl nomatch.

Lemma grade_mut_AtIndexMor :
  forall Yoneda00_E_  Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly)
    Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
    Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0),
    forall I : obIndexer, grade (AtIndexMor ff_ I) = S (grade_indexed ff_).
Proof. reflexivity. Qed.

Lemma grade_mut_PolyCoMod :
    forall Yoneda00_F Yoneda01_F  (F : @obCoMod Yoneda00_F Yoneda01_F)
      Yoneda00_F' Yoneda01_F' (F' : @obCoMod Yoneda00_F' Yoneda01_F')
      Yoneda10_ff' (ff' : 'CoMod(0 F' ~> F @ Yoneda10_ff' )0)
      Yoneda00_F'' Yoneda01_F'' (F'' : @obCoMod Yoneda00_F'' Yoneda01_F'')
      Yoneda10_ff_ (ff_ : 'CoMod(0 F'' ~> F' @ Yoneda10_ff_ )0),
      grade (ff_ o>CoMod ff') = ( 2 * (S (grade ff' + grade ff_)%coq_nat ) )%coq_nat .
Proof. reflexivity. Qed.

Lemma grade_mut_PolyTransf :
  forall (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                  Yoneda01_functor Yoneda01}) (F : obCoMod Yoneda01_F)
    (Yoneda00_G : obGenerator -> Type)
    (Yoneda01_G : {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_G A -> Yoneda00_G A' |
                  Yoneda01_functor Yoneda01})
  (G : obCoMod Yoneda01_G)
  (transf : {transf : forall A : obGenerator, Yoneda00_F A -> Yoneda00_G A |
  Yoneda10_natural Yoneda01_F Yoneda01_G transf}),
  forall (A : obGenerator)
    (Yoneda10_ff : {Yoneda10 : forall A0 : obGenerator, Yoneda00_View A A0 -> Yoneda00_F A0 |
                   Yoneda10_natural (Yoneda01_View A) Yoneda01_F Yoneda10})
    (ff : 'CoMod(0 View A ~> F @ Yoneda10_ff )0),
      grade (ff o>Transf_ transf @ G) = (S (grade ff) )%coq_nat .
Proof. reflexivity. Qed.
    
Lemma grade_mut_UnitCoMod :
  forall (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                   Yoneda01_functor Yoneda01})
    (F : obCoMod Yoneda01_F),
    grade (@'UnitCoMod F) = (S (O) )%coq_nat .
Proof. reflexivity. Qed.


Lemma grade_mut_PolyElement :
 forall (Yoneda00_F : obGenerator -> Type)
   (Yoneda01_F : {Yoneda01
                 : forall A A' : obGenerator,
                   'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                 Yoneda01_functor Yoneda01})
   (F: obCoMod Yoneda01_F) (G : obGenerator) (f : Yoneda00_F G),
    grade (PolyElement F f) = (S (O) )%coq_nat .
Proof. reflexivity. Qed.
   
Lemma grade_mut_CoUnitGenerated :
 forall (I : obIndexer) (R : obReIndexer)
   (i : 'Indexer(0 ReIndexing0 R ~> I )0),
 forall (Yoneda00_F : obGenerator -> Type)
   (Yoneda01_F : {Yoneda01
                 : forall A A' : obGenerator,
                   'Generator(0 A' ~> A )0 -> Yoneda00_F A -> Yoneda00_F A' |
                 Yoneda01_functor Yoneda01}) (F : obCoMod Yoneda01_F)
   (Yoneda10_rr : {Yoneda10 : forall A : obGenerator, Yoneda00_F A -> Yoneda00_View (Generating0 R) A
                  | Yoneda10_natural Yoneda01_F (Yoneda01_View (Generating0 R)) Yoneda10})
   (rr : 'CoMod(0 F ~> View (Generating0 R) @ Yoneda10_rr )0),
    grade (rr o>CoMod 'CoUnitGenerated @ i) = (S (S (grade rr) ))%coq_nat .
Proof. reflexivity. Qed.
   
Lemma grade_mut_MorCoMod_indexed :
 forall (Yoneda00_E_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_E_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_E_ I A -> Yoneda00_E_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_E_Poly (E_ : obCoMod_indexed Yoneda01_E_Poly)
   (Yoneda00_F_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_F_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F_ I A -> Yoneda00_F_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_F_Poly (F_ : obCoMod_indexed Yoneda01_F_Poly)
   (Yoneda10_ff_ : forall I : obIndexer,
                   {Yoneda10 : forall A : obGenerator, Yoneda00_E_ I A -> Yoneda00_F_ I A |
                   Yoneda10_natural (Yoneda01_E_ I) (Yoneda01_F_ I) Yoneda10})
   (ff_ : (forall I : obIndexer, 'CoMod(0 AtIndexOb E_ I ~> AtIndexOb F_ I @ Yoneda10_ff_ I )0)), 
   grade_indexed (MorCoMod_indexed ff_) = (S (max (grade(ff_ ObIndexer1)) (grade(ff_ ObIndexer2)))) .
Proof. reflexivity. Qed.

Lemma grade_mut_Reflector :
 forall (Yoneda00_F_ : obIndexer -> obGenerator -> Type)
   (Yoneda01_F_ : forall I : obIndexer,
                  {Yoneda01
                  : forall A A' : obGenerator,
                    'Generator(0 A' ~> A )0 -> Yoneda00_F_ I A -> Yoneda00_F_ I A' |
                  Yoneda01_functor Yoneda01}) Yoneda01_F_Poly (F_ : obCoMod_indexed Yoneda01_F_Poly)
   (Yoneda10_ff_ : forall (I : obIndexer) (R : obReIndexer),
                   'Indexer(0 ReIndexing0 R ~> I )0 ->
                   {Yoneda10_ff_i
                   : forall G : obGenerator, Yoneda00_View (Generating0 R) G -> Yoneda00_F_ I G |
                   Yoneda10_natural (Yoneda01_View (Generating0 R)) (Yoneda01_F_ I) Yoneda10_ff_i})
 (ff_ : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
  'CoMod(0 View (Generating0 R) ~> AtIndexOb F_ I @ Yoneda10_ff_ I R i )0)),
 forall (Yoneda01_F_Poly_functorIndexer : Yoneda10_functorIndexer Yoneda01_F_Poly)
 (Yoneda10_ff_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ff_),
   grade_indexed ([[ ff_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ff_morphismReIndexer_morphismIndexer ]]_) =
   (S (S (max (max (grade (ff_(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
                           (grade (ff_(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1))))
                      (max (grade (ff_(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
                           (grade (ff_(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2))))))) .
Proof. reflexivity. Qed.

Definition grade_rewrite := (grade_mut_AtIndexMor, grade_mut_PolyCoMod,  grade_mut_PolyTransf, grade_mut_UnitCoMod, grade_mut_PolyElement,  grade_mut_CoUnitGenerated, grade_mut_MorCoMod_indexed, grade_mut_Reflector).

Arguments grade_indexed : simpl nomatch.
Arguments grade : simpl nomatch.

Ltac tac_indexed_all :=
  repeat match goal with
         | [ ri : 'Indexer(0 ReIndexing0 _ ~> ?I )0
             |- context [max _ _] ] => destruct (is_ObIndexer12_allP I);
                                     destruct (is_MorIndexer12_allP ri)
         | (* after above *)
         [ I : obIndexer
           |- context [max _ _] ] => destruct (is_ObIndexer12_allP I)
         | [ Hgrade : (forall (I : obIndexer),
                          ( _ <= _ )%coq_nat) |- context [max _ _] ] =>
           move: {Hgrade} (Hgrade ObIndexer2) (Hgrade ObIndexer1);
           rewrite ?grade_rewrite
         | [ Hgrade : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
                          ( _ <= _ )%coq_nat) |- context [max _ _] ] =>
           move: {Hgrade} (Hgrade ObIndexer2 _ (MorIndexer2_ ObIndexer2))
                          (Hgrade ObIndexer2 _ (MorIndexer1_ ObIndexer2))
                          (Hgrade ObIndexer1 _ (MorIndexer2_ ObIndexer1))
                          (Hgrade ObIndexer1 _ (MorIndexer1_ ObIndexer1));
           rewrite ?grade_rewrite
         (** | [ H : (forall (I : obIndexer),
                     ( _ <~~ _ )%poly) |- context [ _ <~~ _ ] ] =>
           move: {H} (H ObIndexer2) (H ObIndexer1)
         | [ H : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
                     ( _ <~~ _ )%poly) |- context [ _ <~~ _ ] ] =>
           move: {H} (H ObIndexer2 _ (MorIndexer2_ ObIndexer2))
                     (H ObIndexer2 _ (MorIndexer1_ ObIndexer2))
                     (H ObIndexer1 _ (MorIndexer2_ ObIndexer1))
                     (H ObIndexer1 _ (MorIndexer1_ ObIndexer1)) **)
         end.

Lemma grade_mut_gt0 :
  (forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
     Yoneda00_G Yoneda01_G (G : @obCoMod Yoneda00_G Yoneda01_G)
     Yoneda10_gg (gg : 'CoMod(0 F ~> G @ Yoneda10_gg )0 ),
      ((S O) <= (grade gg))%coq_nat ) /\
  (forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
     Yoneda00_G_ Yoneda01_G_ Yoneda01_G_Poly (G_ : @obCoMod_indexed Yoneda00_G_ Yoneda01_G_ Yoneda01_G_Poly)
     Yoneda10_gg_ (gg_ : 'CoMod_(0 F_ ~> G_ @ Yoneda10_gg_ )0 ),
      ((S O) <= (grade_indexed gg_))%coq_nat ).
Proof.
  apply morCoMod_morCoMod_indexed_mutind;
    intros; rewrite ?grade_rewrite; tac_indexed_all; intros; Omega.omega.
Qed.

Definition grade_gt0 := fst grade_mut_gt0.
Definition grade_indexed_gt0 := snd grade_mut_gt0.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ @ _ )0 ,
                  gg3 : 'CoMod(0 _ ~> _ @ _ )0 ,
                        gg4 : 'CoMod(0 _ ~> _ @ _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg3)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ @ _ )0 ,
                  gg3 : 'CoMod(0 _ ~> _ @ _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ @ _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ ~> _ @ _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ gg1) 
  end.

Ltac tac_grade_indexed_gt0 :=
  match goal with
  | [ gg1 : 'CoMod_(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod_(0 _ ~> _ @ _ )0 ,
                  gg3 : 'CoMod_(0 _ ~> _ @ _ )0 ,
                        gg4 : 'CoMod_(0 _ ~> _ @ _ )0 |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg1) (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg2)
                                          (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg3)
                                          (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod_(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod_(0 _ ~> _ @ _ )0 ,
                  gg3 : 'CoMod_(0 _ ~> _ @ _ )0 |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg1) (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg2)
                                          (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod_(0 _ ~> _ @ _ )0 ,
            gg2 : 'CoMod_(0 _ ~> _ @ _ )0  |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg1) (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg2)

  | [ gg1 : 'CoMod_(0 _ ~> _ @ _ )0  |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ gg1) 
  end.

Ltac tac_grade_indexed_gt0_indexing :=
  match goal with
(*  | [ gg1 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
            gg2 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
                  gg3 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
                        gg4 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg3 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg3 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg4 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg4 ObIndexer2))
  | [ gg1 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
            gg2 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
                  gg3 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg3 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg3 ObIndexer2)) *)
  | [ gg1 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0) ,
            gg2 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0)  |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer2))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg2 ObIndexer2))

  | [ gg1 : (forall I : obIndexer, 'CoMod_(0 _ ~> _ @ _ )0)  |- _ ] =>
    move : (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer1))
             (@grade_indexed_gt0 _ _ _ _ _ _ _ _ _ (gg1 ObIndexer2))
  end.

Ltac tac_grade_gt0_indexing :=
  match goal with
(*  | [ gg1 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
            gg2 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
                  gg3 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
                        gg4 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))        
             (@grade_gt0 _ _ _ _ _ _ _ (gg4(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg4(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg4(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg4(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))        
  | [ gg1 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
            gg2 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
                  gg3 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg3(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
*)                         
  | [ gg1 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0) ,
            gg2 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0)  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg2(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))

  | [ gg1 : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0), 'CoMod(0 _ ~> _ @ _ )0)  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer1_ ObIndexer1)(MorIndexer1_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer1)(ObReIndexer2_ ObIndexer1)(MorIndexer2_ ObIndexer1)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer1_ ObIndexer2)(MorIndexer1_ ObIndexer2)))
             (@grade_gt0 _ _ _ _ _ _ _ (gg1(ObIndexer2)(ObReIndexer2_ ObIndexer2)(MorIndexer2_ ObIndexer2)))
  end.

Axiom admit : forall T : Type,  T.

Lemma degrade_mut
    : ( forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E),
          forall Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F),
          forall Yoneda10_ff ( ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
          forall Yoneda10_ff0 ( ff0 : 'CoMod(0 E ~> F @ Yoneda10_ff0 )0 ),
            ff0 <~~ ff -> ( grade ff0 <= grade ff )%coq_nat ) /\
      ( forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly),
       forall Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly),
       forall Yoneda10_ff_ ( ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 ),
       forall Yoneda10_ff0_ ( ff0_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff0_ )0 ),
         ff0_ <~~_ ff_ -> ( grade_indexed ff0_ <= grade_indexed ff_ )%coq_nat ).
  (*TODO: HOLD?? ,  without convCoMod_Refl : ( grade ggDeg < grade gg )%coq_nat *)
Proof.
  Time apply convCoMod_convCoMod_indexed_mutind;
    try solve [intros; rewrite ?grade_rewrite;
                 try tac_grade_gt0; try tac_grade_indexed_gt0;
                   try tac_grade_gt0_indexing; try tac_grade_indexed_gt0_indexing;
                     tac_indexed_all;
                     intros; abstract Psatz.lia].
Qed. (* /!\ LONG TIME 30s ,  WAS 40s *)

Definition degrade := proj1 degrade_mut.
Definition degrade_indexed := proj2 degrade_mut.

Ltac tac_degrade_mut H_grade :=
  intuition idtac;
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
           move : (degrade Hred) ; clear Hred
         | [ Hred : ( _ <~~_ _ )%poly |- _ ] =>
           move : (degrade_indexed Hred) ; clear Hred
         | [ Hred : (forall (I : obIndexer),
                     ( _ <~~ _ )%poly) |- _ ] =>
           move: {Hred} (degrade (Hred ObIndexer2)) (degrade (Hred ObIndexer1))
         | [ Hred : (forall (I : obIndexer) (R : obReIndexer) (i : 'Indexer(0 ReIndexing0 R ~> I )0),
                     ( _ <~~ _ )%poly) |- _ ] =>
           move: {Hred} (degrade (Hred ObIndexer2 _ (MorIndexer2_ ObIndexer2)))
                     (degrade (Hred ObIndexer2 _ (MorIndexer1_ ObIndexer2)))
                     (degrade (Hred ObIndexer1 _ (MorIndexer2_ ObIndexer1)))
                     (degrade (Hred ObIndexer1 _ (MorIndexer1_ ObIndexer1)))
         end;
  move: H_grade; clear; rewrite ?(Sol.toPolyMor_mut_rewrite, grade_rewrite); intros;
  try tac_grade_gt0; try tac_grade_indexed_gt0;
  try tac_grade_gt0_indexing; try tac_grade_indexed_gt0_indexing;
  intros; Psatz.lia.

Module Resolve.
Export Sol.Ex_Notations.
  
Ltac tac_simpl := rewrite ?grade_rewrite; rewrite ?Sol.toPolyMor_mut_rewrite;
                   cbn -[grade grade_indexed Sol.toPolyMor Sol.toPolyMor_indexed].
Ltac tac_reduce := tac_simpl; intuition eauto.
  
Fixpoint solveCoMod len {struct len} :
  forall Yoneda00_E Yoneda01_E (E : @obCoMod Yoneda00_E Yoneda01_E)
    Yoneda00_F Yoneda01_F (F : @obCoMod Yoneda00_F Yoneda01_F)
    Yoneda10_ff (ff : 'CoMod(0 E ~> F @ Yoneda10_ff )0 ),
  forall grade_ff : (grade ff <= len)%coq_nat,
    { ffSol : { Yoneda10_ffSol : _ &  'CoMod(0 E ~> F @ Yoneda10_ffSol )0 %sol }
    | (Sol.toPolyMor (projT2 ffSol)) <~~ ff }
with solveCoMod_indexed len {struct len} :
  forall Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly (E_ : @obCoMod_indexed Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly)
    Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly (F_ : @obCoMod_indexed Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly)
    Yoneda10_ff_ (ff_ : 'CoMod_(0 E_ ~> F_ @ Yoneda10_ff_ )0 ),
  forall grade_ff_ : (grade_indexed ff_ <= len)%coq_nat,
    { ffSol_ : { Yoneda10_ffSol_ : _ &  'CoMod_(0 E_ ~> F_ @ Yoneda10_ffSol_ )0 %sol }
    | (Sol.toPolyMor_indexed (projT2 ffSol_)) <~~_ ff_ } .
Proof.
{ (** solveCoMod **)
case : len => [ | len ].

(** len is O **)
- ( move => ? ? E ? ? F ? ff grade_ff ); exfalso; clear - grade_ff; abstract tac_degrade_mut grade_ff.

(** len is (S len) **)
- move => ? ? E ? ? F Yoneda10_ff ff; case : _ _ E _ _ F Yoneda10_ff / ff =>
  [ Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly E_
                Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_
                Yoneda10_ff_ ff_ I (** AtIndexMor ff_ I **)
  | Yoneda00_F Yoneda01_F F Yoneda00_F' Yoneda01_F' F'
               Yoneda10_ff' ff' Yoneda00_F'' Yoneda01_F'' F''
               Yoneda10_ff_ ff_  (** ff_ o>CoMod ff' **)
  | Yoneda00_E Yoneda01_E E Yoneda00_F Yoneda01_F F
               transf A Yoneda10_ff ff (** ff o>Transf_ transf @ F **)
  | Yoneda00_F Yoneda01_F F (** @'UnitCoMod F **)
  | Yoneda00_F Yoneda01_F F A f (** PolyElement F f **)
  | I R i Yoneda00_F Yoneda01_F F Yoneda10_rr rr (** rr o>CoMod 'CoUnitGenerated @ i **)
  ] grade_ff .

  (** ff is AtIndexMor ff_ I **)
  + have [:blurb] ffSol_prop :=
      (proj2_sig (solveCoMod_indexed len _ _ _ _ _ _ _ _ _ ff_ blurb));
        first by clear -grade_ff; abstract tac_degrade_mut grade_ff.
    move: (projT1 (sval (solveCoMod_indexed len _ _ _ _ _ _ _ _ _ ff_ blurb)))
            (projT2 (sval (solveCoMod_indexed len _ _ _ _ _ _ _ _ _ ff_ blurb))) ffSol_prop 
    => Yoneda10_ffSol_ ffSol_ ffSol_prop .

    unshelve eexists. eexists. refine ( Sol.AtIndexMor ffSol_ I )%sol.
    clear - ffSol_prop. abstract tac_reduce.

  (** ff is ff_ o>CoMod ff' *)
  + all: cycle 1.

  (** ff is ff o>Transf_ transf @ G **)
  + have [:blurb] ffSol_prop :=
        (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff blurb));
          first by clear -grade_ff; abstract tac_degrade_mut grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff blurb)))
            (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff blurb))) ffSol_prop 
      => Yoneda10_ffSol ffSol ffSol_prop .

      move: (Sol.Destruct_domView.morCoMod_domViewP ffSol) => ffSol_domViewP.
      destruct ffSol_domViewP as
          [ B (* @'UnitCoMod (View B) *)
          | _Yoneda00_F _Yoneda01_F _F A f (* PolyElement F f *)
          | I R i G Yoneda10_rr rr (* rr o>CoMod 'CoUnitGenerated @ i *) ] .
      
      * unshelve eexists. eexists.
        refine ( 'PolyElement F (proj1_sig transf _ (@unitGenerator B)) )%sol.
        move: ffSol_prop; clear. (*; move: (convCoMod_sense' ffSol_prop) => ffSol_prop_eq ; subst*)
        abstract(tac_simpl; intros; eapply convCoMod_Trans with
                 (uTrans := ('UnitCoMod) o>Transf_ transf ); tac_reduce).
        
      * unshelve eexists. eexists.
        refine ( 'PolyElement F (proj1_sig transf _ f) )%sol.
        move: ffSol_prop; clear. (*; move : (convCoMod_sense' ffSol_prop) => ffSol_prop_eq ; subst*)
        abstract(tac_simpl; intros; eapply convCoMod_Trans with
                                    (uTrans := (PolyElement _F f) o>Transf_ transf ); tac_reduce).
        
      * unshelve eexists. eexists.
        refine ( 'PolyElement _ (proj1_sig transf _
                   (sval (Yoneda10_CoUnitGenerated i Yoneda10_rr) G (@unitGenerator G))) )%sol.
        move: ffSol_prop; clear. (*; move : (convCoMod_sense' ffSol_prop) => ffSol_prop_eq ; subst*)
        abstract(tac_simpl; intros; eapply convCoMod_Trans with
                 (uTrans := ( (Sol.toPolyMor rr) o>CoMod 'CoUnitGenerated @ i ) o>Transf_ transf );
                 tac_reduce).
     
  (** gg is @'UnitCoMod F **)
  + unshelve eexists. eexists. refine (@'UnitCoMod F)%sol. apply: convCoMod_Refl.

  (** gg is PolyYoneda00 F f **)
  + unshelve eexists. eexists. refine ('PolyElement F f)%sol. apply: convCoMod_Refl.

  (** ff is rr o>CoMod 'CoUnitGenerated @ i **)
  + have [:blurb] rrSol_prop :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ rr blurb));
        first by clear -grade_ff; abstract tac_degrade_mut grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ rr blurb)))
            (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ rr blurb))) rrSol_prop 
    => Yoneda10_rrSol rrSol rrSol_prop .

    unshelve eexists. eexists. refine ( rrSol o>CoMod 'CoUnitGenerated @ i )%sol.
    clear - rrSol_prop(*; move : (convCoMod_sense' rrSol_prop) => rrSol_prop_eq; subst*).
    Time abstract tac_reduce. (*0.441sec with convCoMod_sense' , 0.435sec without convCoMod_sense' *)

  (** ff is ff_ o>CoMod ff' *)
  + have [:blurb] ff'Sol_prop :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff' blurb));
        first by clear -grade_ff; abstract tac_degrade_mut grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff' blurb)))
            (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff' blurb))) ff'Sol_prop 
    => Yoneda10_ff'Sol ff'Sol ff'Sol_prop .
    have [:blurb] ff_Sol_prop :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ ff_ blurb));
        first by clear -grade_ff; abstract tac_degrade_mut grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ ff_ blurb)))
            (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ ff_ blurb))) ff_Sol_prop 
    => Yoneda10_ff_Sol ff_Sol ff_Sol_prop .

    (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  **)
    destruct ff'Sol as
        [ Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly E_
                      Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_
                      Yoneda10_ff'Sol_ ff'Sol_ I (* AtIndexMor ff'Sol_ I *)
        | Yoneda00_F Yoneda01_F F (* @'UnitCoMod F *)
        | Yoneda00_F Yoneda01_F F A f (* PolyElement F f *)
        | I R i Yoneda00_F Yoneda01_F F Yoneda10_rr rrSol (* rrSol o>CoMod 'CoUnitGenerated @ i *) ].

    (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (AtIndexMor ff'Sol_ I) ) **)
    * { destruct ff'Sol_ as
            [ Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly E_
                          Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_
                          Yoneda10_ff'Sol_ ff'Sol_ (* MorCoMod_indexed ff'Sol_ *)
            | Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_ Yoneda10_ffSol_ ffSol_
                          Yoneda01_F_Poly_functorIndexer
                          Yoneda10_ffSol_morphismReIndexer_morphismIndexer (* [[ ffSol_ ]]_ *) ].

        (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (AtIndexMor ( MorCoMod_indexed ff'Sol_ ) I) ) **)
        - have [:blurb] ff_Sol_o_ff'Sol_I_prop :=
            (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor (ff'Sol_ I)) blurb));
              first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
              abstract(destruct (is_ObIndexer12_allP I); tac_degrade_mut grade_ff).
          move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor (ff'Sol_ I)) blurb)))
                  (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor (ff'Sol_ I)) blurb))) ff_Sol_o_ff'Sol_I_prop 
          => Yoneda10_ff_Sol_o_ff'Sol_I ff_Sol_o_ff'Sol_I ff_Sol_o_ff'Sol_I_prop .

          unshelve eexists. eexists. refine ( ff_Sol_o_ff'Sol_I )%sol.
          move: ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_I_prop; clear. tac_simpl.
          abstract (tac_simpl; intros; eapply convCoMod_Trans with
                     (uTrans := (Sol.toPolyMor ff_Sol) o>CoMod
                     ('AtIndexMor ( 'MorCoMod_indexed (fun I0 => Sol.toPolyMor (ff'Sol_ I0))) I));
                    tac_reduce).

        (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (AtIndexMor [[ ffSol_ ]]_ I) ) **)
        - move: (Sol.Destruct_codomAtIndexObGenerated.morCoMod_codomAtIndexObGeneratedP ff_Sol) => ff_Sol_codomAtIndexObGeneratedP.
          { destruct ff_Sol_codomAtIndexObGeneratedP as
                [ J (* ( @'UnitCoMod (AtIndexOb Generated J) ) *)
                | J G f (* (PolyElement (AtIndexOb Generated J) f ) *)
                | J R j Yoneda00_F Yoneda01_F F Yoneda10_rrSol rrSol (* rrSol o>CoMod 'CoUnitGenerated @ j *)
                | Yoneda00_E_ Yoneda01_E_ Yoneda01_Poly E_
                              Yoneda10_ggSol_ ggSol_ J (* AtIndeMor (MorCoMod_indexed ggSol_) *)
                | Yoneda10_ggSol_ ggSol_
                              Yoneda01_Generated_PolyIndexer_functorIndexer'
                              Yoneda10_ggSol_morphismReIndexer_morphismIndexer J (* AtIndexMor [[ ffSol_' ]]_ J  ... TODO: BAD /!\ must instantiate Yoneda01_F_Poly' (instead carried by obCoMod_indexed) *) ].

            (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (( @'UnitCoMod (AtIndexOb Generated J) ) o>CoMod (AtIndexMor [[ ffSol_ ]]_ J) ) **)
            - unshelve eexists. eexists.
              refine ('AtIndexMor [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                                     Yoneda10_ffSol_morphismReIndexer_morphismIndexer  ]]_ J)%sol.
              move: ff_Sol_prop ff'Sol_prop; clear.
              abstract (tac_simpl; intros; eapply convCoMod_Trans with
                                    (uTrans := ( 'UnitCoMod ) o>CoMod (Sol.toPolyMor ('AtIndexMor [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                                     Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol)); tac_reduce).
              
            (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is ((PolyElement (AtIndexOb Generated J) f ) o>CoMod (AtIndexMor [[ ffSol_ ]]_ J) ) **)
            - unshelve eexists. eexists.
              refine ('PolyElement (AtIndexOb F_(J)) (
                          ( sval (Yoneda10_ffSol_ _ _ (projT2 (projT1 f))) G (projT2 f) ) ))%sol.
              move: ff_Sol_prop ff'Sol_prop. clear.
              abstract (rewrite ?Sol.toPolyMor_mut_rewrite; intros;
                        eapply convCoMod_Trans with
                        (uTrans := ('PolyElement (AtIndexOb Generated J) f)
                      o>CoMod (Sol.toPolyMor ('AtIndexMor [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                         Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol));
                        rewrite ?Sol.toPolyMor_mut_rewrite; by eauto).       

            (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (rrSol o>CoMod 'CoUnitGenerated @ j) o>CoMod (AtIndexMor [[ ffSol_ ]]_ J) **)
            - have [:blurb] rrSol_o_ffSol_prop :=
                (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor rrSol o>CoMod Sol.toPolyMor (ffSol_(J)(R)(j))) blurb));
                  first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
                          abstract(destruct (is_ObIndexer12_allP J);
                                   destruct (is_MorIndexer12_allP j); tac_degrade_mut grade_ff).
              move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor rrSol o>CoMod Sol.toPolyMor (ffSol_(J)(R)(j))) blurb)))
              (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor rrSol o>CoMod Sol.toPolyMor (ffSol_(J)(R)(j))) blurb))) rrSol_o_ffSol_prop 
      => Yoneda10_rrSol_o_ffSol rrSol_o_ffSol rrSol_o_ffSol_prop .

              unshelve eexists. eexists. refine ( rrSol_o_ffSol )%sol.
              move: ff_Sol_prop ff'Sol_prop rrSol_o_ffSol_prop . clear.
              abstract (rewrite ?Sol.toPolyMor_mut_rewrite; intros;
                        eapply convCoMod_Trans with
                        (uTrans := ((Sol.toPolyMor rrSol) o>CoMod 'CoUnitGenerated @ j)
                      o>CoMod (Sol.toPolyMor ('AtIndexMor [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                         Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol));
                        rewrite ?Sol.toPolyMor_mut_rewrite; by eauto).       
              
            (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is ('AtIndexMor ('MorCoMod_indexed ggSol_) J) o>CoMod (AtIndexMor [[ ffSol_ ]]_ J) **)
            - have [:blurb] ggSol_J_o_ff'Sol_prop :=
            (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor (ggSol_ J) o>CoMod Sol.toPolyMor ('AtIndexMor [[ ffSol_ @  Yoneda01_F_Poly_functorIndexer , Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol) blurb));
              first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
              abstract(destruct (is_ObIndexer12_allP J); tac_degrade_mut grade_ff).
              move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor (ggSol_ J) o>CoMod Sol.toPolyMor ('AtIndexMor [[ ffSol_ @  Yoneda01_F_Poly_functorIndexer , Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol) blurb)))
                  (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor (ggSol_ J) o>CoMod Sol.toPolyMor ('AtIndexMor [[ ffSol_ @  Yoneda01_F_Poly_functorIndexer , Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol) blurb))) ggSol_J_o_ff'Sol_prop 
          => Yoneda10_ggSol_J_o_ff'Sol ggSol_J_o_ff'Sol ggSol_J_o_ff'Sol_prop .

              unshelve eexists. eexists. refine ( ggSol_J_o_ff'Sol )%sol.
              move: ff_Sol_prop ff'Sol_prop ggSol_J_o_ff'Sol_prop; clear. tac_simpl.
              abstract (tac_simpl; intros; eapply convCoMod_Trans with
                     (uTrans := ('AtIndexMor ('MorCoMod_indexed (fun I : obIndexer => Sol.toPolyMor (ggSol_ I))) J) o>CoMod
                     (Sol.toPolyMor ('AtIndexMor [[ ffSol_ @  Yoneda01_F_Poly_functorIndexer , Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ J)%sol));
                    tac_reduce).

            (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (AtIndexMor [[ ggSol_ ]]_ J) o>CoMod (AtIndexMor [[ ffSol_ ]]_ J) **)
            - have [:blurb_] ggSol_o_ffSol_prop I0 R0 (i0 : 'Indexer(0 ReIndexing0 R0 ~> I0 )0) :=
                (proj2_sig (solveCoMod len _ _ _ _ _ _ _
                      ((Sol.toPolyMor (ggSol_ I0 R0 i0)) o>CoMod
                       AtIndexMor (Sol.toPolyMor_indexed ( [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                       Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol))
                                                          (I0)) (blurb_ I0 R0 i0)));
                  first by clear -grade_ff ff_Sol_prop ff'Sol_prop;
                  abstract((move => I0 R0 i0); destruct (is_ObIndexer12_allP I0);
                           destruct (is_MorIndexer12_allP i0); tac_degrade_mut grade_ff).

              have @Yoneda10_ggSol_o_ffSol_ := (fun I0 R0 (i0 : 'Indexer(0 ReIndexing0 R0 ~> I0 )0) =>
                (projT1 (sval (solveCoMod len _ _ _ _ _ _ _
                      ((Sol.toPolyMor (ggSol_ I0 R0 i0)) o>CoMod
                       AtIndexMor (Sol.toPolyMor_indexed ( [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                       Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol))
                                                          (I0)) (blurb_ I0 R0 i0))))).
              have @ggSol_o_ffSol_ : forall I0 R0 i0,
                  'CoMod(0 View (Generating0 R0) ~> AtIndexOb F_ I0 @ Yoneda10_ggSol_o_ffSol_ I0 R0 i0 )0%sol
      := (fun I0 R0 (i0 : 'Indexer(0 ReIndexing0 R0 ~> I0 )0) =>
                (projT2 (sval (solveCoMod len _ _ _ _ _ _ _
                      ((Sol.toPolyMor (ggSol_ I0 R0 i0)) o>CoMod
                       AtIndexMor (Sol.toPolyMor_indexed ( [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                       Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol))
                                                          (I0)) (blurb_ I0 R0 i0))))).
              have {ggSol_o_ffSol_prop}: (forall I0 R0 i0, Sol.toPolyMor (ggSol_o_ffSol_(I0)(R0)(i0)) <~~
                                                            ((Sol.toPolyMor (ggSol_ I0 R0 i0)) o>CoMod
                       AtIndexMor (Sol.toPolyMor_indexed ( [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                       Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol))
                                                          (I0))) := ggSol_o_ffSol_prop.
              move: Yoneda10_ggSol_o_ffSol_ ggSol_o_ffSol_ =>
              Yoneda10_ggSol_o_ffSol_ ggSol_o_ffSol_ ggSol_o_ffSol_prop.
              clear solveCoMod solveCoMod_indexed.

              (**memo: convCoMod_sense' is really necessary here **)
              have Yoneda10_ggSol_o_ffSol_morphismReIndexer_morphismIndexer :
                Yoneda10_morphismReIndexer_morphismIndexer Yoneda01_F_Poly Yoneda10_ggSol_o_ffSol_ .
              { clear - Yoneda10_ffSol_morphismReIndexer_morphismIndexer
                          Yoneda10_ggSol_morphismReIndexer_morphismIndexer
                          ggSol_o_ffSol_prop;
                  move : (fun I0 R0 i0 => convCoMod_sense' (ggSol_o_ffSol_prop I0 R0 i0)) => ggSol_o_ffSol_prop_eq.
                rewrite /Yoneda10_morphismReIndexer_morphismIndexer.
                intros. do 2 rewrite - ggSol_o_ffSol_prop_eq.
                exact: (Reflector_morphism_morphismReIndexer_morphismIndexer Yoneda10_ggSol_morphismReIndexer_morphismIndexer (Yoneda10_Reflector_naturalIndexer_ALT Yoneda10_ffSol_morphismReIndexer_morphismIndexer )).
              }

              unshelve eexists. eexists.
              refine ( 'AtIndexMor [[ ( fun I0 R0 i0 => ggSol_o_ffSol_(I0)(R0)(i0) )
                                       @ Yoneda01_F_Poly_functorIndexer ,
                                      Yoneda10_ggSol_o_ffSol_morphismReIndexer_morphismIndexer ]]_ J )%sol.
              move: ff_Sol_prop ff'Sol_prop ggSol_o_ffSol_prop . clear.
              abstract( rewrite ?Sol.toPolyMor_mut_rewrite; (*invisible*) progress simpl; intros;
                        eapply convCoMod_Trans with
                        (uTrans := (AtIndexMor [[ (fun I0 R0 i0 => Sol.toPolyMor (ggSol_ I0 R0 i0))
                                                    @ Yoneda01_Generated_PolyIndexer_functorIndexer',
                         Yoneda10_ggSol_morphismReIndexer_morphismIndexer ]]_ J)
                                     o>CoMod ( 'AtIndexMor (Sol.toPolyMor_indexed [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                         Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol) J));
                        first (by rewrite ?Sol.toPolyMor_mut_rewrite; eauto);
                        eapply convCoMod_Trans with
                        (uTrans := (AtIndexMor [[ (fun I0 R0 i0 => Sol.toPolyMor (ggSol_ I0 R0 i0)
              o>CoMod ( 'AtIndexMor (Sol.toPolyMor_indexed [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer,
                         Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ %sol) I0))
                                                    @ Yoneda01_F_Poly_functorIndexer,
                         (Reflector_morphism_morphismReIndexer_morphismIndexer Yoneda10_ggSol_morphismReIndexer_morphismIndexer (Yoneda10_Reflector_naturalIndexer_ALT Yoneda10_ffSol_morphismReIndexer_morphismIndexer )) ]]_ J)  );
                        rewrite ?Sol.toPolyMor_mut_rewrite; by eauto).
          } 
      }

    (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (@'UnitCoMod F)) **)
    * unshelve eexists. eexists. refine (ff_Sol)%sol.
      clear -ff_Sol_prop ff'Sol_prop.
      abstract (tac_simpl; intros; eapply convCoMod_Trans with
                                (uTrans := ff_ o>CoMod ('UnitCoMod)); tac_reduce).

    (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (PolyElement F f)) **)
    * move: (Sol.Destruct_codomView.morCoMod_codomViewP ff_Sol) => ff_Sol_codomViewP.
      { destruct ff_Sol_codomViewP as
            [ G (* @'UnitCoMod (View G) *)
            | G G' g (* PolyElement (View G) g *) ].
        - unshelve eexists. eexists. refine ('PolyElement F f)%sol.
          move: ff_Sol_prop ff'Sol_prop; clear.
          abstract (tac_simpl; intros; eapply convCoMod_Trans with
                                (uTrans := ('UnitCoMod) o>CoMod ('PolyElement F f)); tac_reduce).
          
        - unshelve eexists. eexists. refine ('PolyElement F (proj1_sig Yoneda01_F G G' g f) )%sol.
          move: ff_Sol_prop ff'Sol_prop; clear.
          abstract (tac_simpl; intros; eapply convCoMod_Trans with
                                       (uTrans := ('PolyElement (View G) g) o>CoMod ('PolyElement F f)); tac_reduce).
      } 

    (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , is (ff_Sol o>CoMod (rrSol o>CoMod 'CoUnitGenerated @ i)) **)
    * have [:blurb] ff_Sol_o_rrSol_prop :=
        (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor rrSol) blurb));
          first by clear -grade_ff ff_Sol_prop ff'Sol_prop; abstract tac_degrade_mut grade_ff.
      move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor rrSol) blurb)))
              (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor rrSol) blurb))) ff_Sol_o_rrSol_prop 
      => Yoneda10_ff_Sol_o_rrSol ff_Sol_o_rrSol ff_Sol_o_rrSol_prop .

      unshelve eexists. eexists. refine ( ff_Sol_o_rrSol o>CoMod 'CoUnitGenerated @ i )%sol.
      move: ff_Sol_prop ff'Sol_prop ff_Sol_o_rrSol_prop; clear.
      abstract (tac_simpl; intros; eapply convCoMod_Trans with
                            (uTrans := (Sol.toPolyMor ff_Sol) o>CoMod ((Sol.toPolyMor rrSol) o>CoMod 'CoUnitGenerated @ i)); tac_reduce).
}

{ (** solveCoMod_indexed **)
case : len => [ | len ].

(** len is O **)
- ( move => ? ? ? E_ ? ? ? F_ ? ff_ grade_ff_ ); exfalso; clear - grade_ff_; abstract tac_degrade_mut grade_ff_.

(** len is (S len) **)
- move => ? ? ? E_ ? ? ? F_ Yoneda10_ff_ ff_; case : _ _ _ E_ _ _ _ F_ Yoneda10_ff_ / ff_ =>
  [ Yoneda00_E_ Yoneda01_E_ Yoneda01_E_Poly E_
                Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_
                Yoneda10_ff_ ff_ (** MorCoMod_indexed ff_ **)
  | Yoneda00_F_ Yoneda01_F_ Yoneda01_F_Poly F_ Yoneda10_ff_ ff_
                Yoneda01_F_Poly_functorIndexer
                Yoneda10_ff_morphismReIndexer_morphismIndexer (** [[ ff_ ]]_ **)
  ] grade_ff_ .

  (** ff is MorCoMod_indexed ff_ **)
  + have [:blurb_] ffSol_prop (I : obIndexer) :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (ff_(I)) (blurb_ I)));
        first by clear -grade_ff_;
        abstract(move => I; destruct (is_ObIndexer12_allP I); tac_degrade_mut grade_ff_).
    
      have @Yoneda10_ffSol_ := (fun (I : obIndexer) =>
                        projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (ff_(I)) (blurb_ I)))).
      have @ffSol_ : (forall I, 'CoMod(0 AtIndexOb E_ I ~> AtIndexOb F_ I @ Yoneda10_ffSol_ I )0%sol)
        := (fun (I : obIndexer) =>
              projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (ff_(I)) (blurb_ I)))).
      have {ffSol_prop}: (forall (I : obIndexer), Sol.toPolyMor (ffSol_(I)) <~~ ff_ I) := ffSol_prop.
      move: Yoneda10_ffSol_ ffSol_ => Yoneda10_ffSol_ ffSol_ ffSol_prop.

      unshelve eexists. eexists. refine ( 'MorCoMod_indexed ffSol_ )%sol.
      move: ffSol_prop; clear. (*; move : (fun I => convCoMod_sense' (ffSol_prop I)) => ffSol_prop_eq *)
      Time abstract tac_reduce. (*0.588sec with convCoMod_sense' , 0.564sec without convCoMod_sense' *)

  (* ff is [[ ff_ @ I ]] *)
  + have [:blurb_] ffSol_prop I R (i : 'Indexer(0 ReIndexing0 R ~> I )0) :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ (ff_(I)(R)(i)) (blurb_ I R i)));
        first by clear -grade_ff_;
        abstract((move => I R i); destruct (is_ObIndexer12_allP I);
                 destruct (is_MorIndexer12_allP i); tac_degrade_mut grade_ff_).
    
    have @Yoneda10_ffSol_ := (fun I R i =>
                       projT1 (sval (solveCoMod len _ _ _ _ _ _ _ (ff_(I)(R)(i)) (blurb_ I R i)))).
    have @ffSol_ : (forall I R i,
                       'CoMod(0 View (Generating0 R) ~> AtIndexOb F_ I @ Yoneda10_ffSol_ I R i )0 %sol)
      := (fun I R i => projT2 (sval (solveCoMod len _ _ _ _ _ _ _ (ff_(I)(R)(i)) (blurb_ I R i)))) .
    have {ffSol_prop}: (forall I R i, Sol.toPolyMor (ffSol_(I)(R)(i)) <~~ ff_(I)(R)(i)) := ffSol_prop.
    move: Yoneda10_ffSol_ ffSol_ => Yoneda10_ffSol_ ffSol_ ffSol_prop.
    clear solveCoMod solveCoMod_indexed.

    (**memo: convCoMod_sense' is really necessary here **)
    have Yoneda10_ffSol_morphismReIndexer_morphismIndexer : Yoneda10_morphismReIndexer_morphismIndexer
                                                    Yoneda01_F_Poly Yoneda10_ffSol_ .
    { clear - Yoneda10_ff_morphismReIndexer_morphismIndexer ffSol_prop;
        move : (fun I R i => convCoMod_sense' (ffSol_prop I R i)) => ffSol_prop_eq.
      rewrite /Yoneda10_morphismReIndexer_morphismIndexer.
      intros. do 2 rewrite - ffSol_prop_eq.
      apply Yoneda10_ff_morphismReIndexer_morphismIndexer.
    }
    
    unshelve eexists. eexists. refine ( [[ ffSol_ @ Yoneda01_F_Poly_functorIndexer , Yoneda10_ffSol_morphismReIndexer_morphismIndexer ]]_ )%sol.
    move: ffSol_prop; clear. abstract tac_reduce.
}
Defined.
End Resolve.
End GENERATEDFUNCTOR.

(** # #
#+END_SRC

Voila.
# # **)
