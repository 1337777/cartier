(**#+TITLE: cartierSolution4.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution4.v

solves half of some question of Cartier which is how to program grammatical polymorph internal ( "typed" , "small" ) functors ...

The ends is to do polymorph mathematics which is internal/small/typed ref some indexer/types (metacategory/topos/modos) ; this infers that the objects and morphisms can no longer be touched individually but many objects shall be touched at the same time via some indexing/dimension/type and many morphisms shall be touched at the same time via some indexing/dimension/type . And for internal polymorph mathematics , the common operations on the morphisms are pointwise/dimensional ; this contrast from enriched/multifolded polymorph mathematics where each object is touched individually and many morphisms are touched at the same time and the common operations on the morphisms are multiplicative .

Oneself shall start from some generating data which is internal/small/typed ref some indexer/types (metacategory/topos/modos) and then add pairing-projections ( "product" ) ; but how to describe the two indexes which encode those pair objects and those pairing-projections morphisms ? Oneself could decode ( "Yoneda" ) these two index-for-objects and index-for-morphisms as two metafunctors on this indexer/metacategory ; then these two metafunctors may be commonly programmed by two inductive-families-presentations where the constructors of these two inductive-families-presentations are the decoding ( "Yoneda" ) as metatransformations of the whatever-is-interesting arrows between these two index-for-objects and index-for-morphisms .

The conversion-relation shall convert across two morphisms whose domain/codomain-computation arguments are not syntactically/grammatically-the-same. But oneself does show that, by logical-deduction, these two domain/codomain-computations are indeed propositionally equal ( "soundness lemma" ) .

Finally, some linear total/asymptotic grade is defined on the morphisms and the tactics-automated degradation lemma shows that each of the conversion indeed degrades the redex morphism .

For instant first impression , the conversion-relation constructor which says that the first projection morphism is natural/polyarrow (commutativity with the polyarrow-cut-constructor) , is written as :

#+BEGIN_EXAMPLE
| Project1_arrow : forall (A : obIndexer) (F1 F2 : obCoMod A),
    forall (Z1 : obCoMod A) (zz1 : 'CoMod(0 F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
          ( ~_1 @ (ObCoMod_Poly a F2) o>CoMod (a o>* zz1) )
            <~~ ( a o>* ( ~_1 @ F2 o>CoMod zz1 ) )
#+END_EXAMPLE

KEYWORDS : 1337777.OOO ; COQ ; cut-elimination ; internal functors ; internal product ; polymorph metafunctors-grammar ; modos

OUTLINE :

  * Generating data internal some indexer , by decoding the indexes as metafunctors and the arrows as metatransformations

  * Grammatical presentation of objects and morphisms internal some indexer , by decoding the indexes as metafunctors and the arrows as metatransformations
  ** Grammatical presentation of objects
  ** Grammatical presentation of morphisms

  * Grammatical conversions of morphisms , which infer the same domain/codomain-computation
  ** Grammatical conversions of morphisms
  ** Same domain/codomain-computation for convertible morphisms
  ** Linear total/asymptotic grade and the degradation lemma

  * Solution
  ** Solution morphisms without polyarrow/polymorphism
  ** Destruction of morphisms with inner-instantiation of object-indexes

  * Polyarrow/polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

-----

BUY RECURSIVE T-SQUARE paypal.me/1337777 ; 微信支付 2796386464@qq.com ; eth 0x54810dcb93b37DBE874694407f78959Fa222D920 ; amazon amazon.com/hz/wishlist/ls/28SN02HR4EB8W ; irc #OOO1337777

**)

(**

* Generating data internal some indexer , by decoding the indexes as metafunctors and the arrows as metatransformations

The ends is to do polymorph mathematics which is internal/small/typed ref some indexer/types (metacategory/topos/modos) ; this infers that the objects and morphisms can no longer be touched individually but many objects shall be touched at the same time via some indexing/dimension/type and many morphisms shall be touched at the same time via some indexing/dimension/type . And for internal polymorph mathematics , the common operations on the morphisms are pointwise/dimensional ; this contrast from enriched/multifolded polymorph mathematics where each object is touched individually and many morphisms are touched at the same time and the common operations on the morphisms are multiplicative .

Oneself shall start from some generating data which is internal/small/typed ref some indexer/types (metacategory/topos/modos) and then add pairing-projections ( "product" ) ; but how to describe the two indexes which encode those pair objects and those pairing-projections morphisms ? Oneself could decode ( "Yoneda" ) these two index-for-objects and index-for-morphisms as two metafunctors on this indexer/metacategory ; then these two metafunctors may be commonly programmed by two inductive-families-presentations where the constructors of these two inductive-families-presentations are the decoding ( "Yoneda" ) as metatransformations of the whatever-is-interesting arrows between these two index-for-objects and index-for-morphisms .

Memo that the functoriality ( "arrows-action" ) of each metafunctor (decoded index) and the naturality ( "arrows-action" ) of each metatransformation (decoded arrow-between-indexes) is signified via some additional/embedded constructors of the inductive-families-presentations or is immediately-accumulated onto the constant constructors . Also memo that here polyarrow/polymorphism/cut-elimination says that both this cut-constructor for arrows ( "arrow-action" , "polyarrow" ) and the common cut-constructor for morphisms ( "composition" , "polymorphism" ) are eliminated/erased .

Memo that the decoding ( "Yoneda" ) preserves/(commute-with) any possible limits and pullbacks in the indexer into the limits and pullback in the COQ-sets . In fact oneself could do internal polymorph mathematics only-in the COQ-sets , without assuming limits (terminal) or pullbacks in the indexer ; but such lemmas cannot be linked back to the indexer .

For sure, polyarrow/polymorphism/cut-elimination cannot proceed beyond the polyarrows/polymorphisms/cuts which are contained in the atomic morphisms generated by the generating data . Therefore oneself shall start by presenting the atomic objects and atomic morphisms , and then inject them into all the objects and morphisms .

#+BEGIN_SRC coq :exports both :results silent **)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Omega.

Module INTERNAL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
 
Parameter obIndexer : Type.
Parameter morIndexer : obIndexer -> obIndexer -> Type.
Parameter polyIndexer : forall A A', morIndexer A' A -> forall A'', morIndexer A'' A' -> morIndexer A'' A .
Parameter unitIndexer : forall {A : obIndexer}, morIndexer A A.

Delimit Scope poly_scope with poly.
Open Scope poly.

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

Parameter obCoMod_Gen : forall (A : obIndexer), Type.
Parameter morCoMod_Gen : forall A (F G : obCoMod_Gen A), Type.

Reserved Notation "''CoMod' (0 F' ~> F )0" (at level 0, format "''CoMod' (0  F'  ~>  F  )0").

Reserved Notation "gg0 <~~ gg" (at level 70).

Module Atom.

  Inductive obCoMod : obIndexer -> Type := 
  | ObCoMod_Poly : forall (A A' : obIndexer), 'Indexer(0 A' ~> A )0 -> obCoMod A -> obCoMod A'
  | ObCoMod_Gen : forall A, obCoMod_Gen A -> forall A' (a : 'Indexer(0 A' ~> A )0), obCoMod A' .

  Reserved Notation "F0 ~~~ F" (at level 70).

  Section Section0.
  Delimit Scope atom_scope with atom.

  Inductive convObCoMod : forall A (F G : obCoMod A), Prop :=

  | convObCoMod_Refl :
      forall A (F : obCoMod A),
        F ~~~ F

  | convObCoMod_Sym :
      forall A (F G : obCoMod A),
        G ~~~ F -> F ~~~ G

  | convObCoMod_Trans :
      forall A (F uTrans : obCoMod A),
        uTrans ~~~ F -> forall (G : obCoMod A), G ~~~ uTrans -> G ~~~ F

  | ObCoMod_Poly_cong : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0) (F F0 : obCoMod A),
      F0 ~~~ F -> ObCoMod_Poly a F0 ~~~ ObCoMod_Poly a F

  | ObCoMod_Poly_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0) (F : obCoMod A) A'' (a' : 'Indexer(0 A'' ~> A' )0),
      ObCoMod_Poly (a' o>Indexer a) F ~~~ ObCoMod_Poly a' (ObCoMod_Poly a F)

  | ObCoMod_Poly_unitIndexer : forall (A : obIndexer) (F : obCoMod A),
      (ObCoMod_Poly (@unitIndexer A) F) ~~~ F

  | ObCoMod_Gen_arrow : forall A (F : obCoMod_Gen A), forall A' (a : 'Indexer(0 A' ~> A )0),
        forall A'' (a' : 'Indexer(0 A'' ~> A' )0),
          ObCoMod_Gen F (a' o>Indexer a) ~~~ ObCoMod_Poly a' (ObCoMod_Gen F a)

  where "F0 ~~~ F" := (@convObCoMod _ F F0) : atom_scope. 

  End Section0.

  Module Import Ex_Notations0.
      Delimit Scope atom_scope with atom.
      Notation "F0 ~~~ F" := (@convObCoMod _ F F0) : atom_scope. 
      Hint Constructors convObCoMod.
  End Ex_Notations0.

  Axiom ax1_convObCoMod_extensionality :  forall A (F G : obCoMod A), ( G ~~~ F )%atom -> G = F .
  
  Section Section1.
  Delimit Scope atom_scope with atom.

  Inductive morCoMod : forall A : obIndexer, obCoMod A -> obCoMod A -> Type :=

  | MorCoMod_Poly : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
    forall (F G : obCoMod A), 'CoMod(0 F ~> G )0 -> 'CoMod(0 (ObCoMod_Poly a F) ~> (ObCoMod_Poly a G) )0

  | PolyCoMod : forall A (F F' : obCoMod A),
    'CoMod(0 F' ~> F )0 -> forall (F'' : obCoMod A),
      'CoMod(0 F'' ~> F' )0 -> 'CoMod(0 F'' ~> F )0

  | MorCoMod_Gen : forall A (F G : obCoMod_Gen A),
    @morCoMod_Gen A F G -> forall A' (a : 'Indexer(0 A' ~> A )0),
      'CoMod(0 (ObCoMod_Gen F a) ~> (ObCoMod_Gen G a) )0

  where "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : atom_scope. 

  End Section1.

  Module Import Ex_Notations1.
    Export Ex_Notations0.

    Notation "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : atom_scope. 

    Notation "a o>* ff" :=
      (@MorCoMod_Poly _ _ a _ _ ff) (at level 3 , ff at next level, left associativity) : atom_scope.

    Notation "ff_ o>CoMod ff'" :=
      (@PolyCoMod _ _ _ ff' _ ff_) (at level 40 , ff' at next level) : atom_scope.

    Notation "a o>| ''MorCoMod_Gen' ff" :=
      (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : atom_scope.
  End Ex_Notations1.

  Section Section2.
  Local Open Scope atom_scope.

  Inductive convMorCoMod : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 %poly ),
        forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 %poly ), Prop :=

  | convMorCoMod_Refl : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
      gg <~~ gg

  | convMorCoMod_Trans :
      forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) (uTrans : 'CoMod(0 F0 ~> G0 )0 ),
        uTrans <~~ gg -> forall (F00 G00 : obCoMod A) (gg00 : 'CoMod(0 F00 ~> G00 )0 ),
          gg00 <~~ uTrans -> gg00 <~~ gg

  | MorCoMod_Poly_cong : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      forall (F G : obCoMod A) (gg gg0 : 'CoMod(0 F ~> G )0),
        gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )

  | PolyCoMod_cong_Pre : forall A (F F' : obCoMod A) (ff' : 'CoMod(0 F' ~> F )0),
      forall (F'' : obCoMod A) (ff_ ff_0 : 'CoMod(0 F'' ~> F' )0 ),
        ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

  | PolyCoMod_cong_Post : forall A (F F' : obCoMod A) (ff' ff'0 : 'CoMod(0 F' ~> F )0 ),
      forall (F'' : obCoMod A) (ff_ : 'CoMod(0 F'' ~> F' )0),
        ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

  | PolyCoMod_arrow : forall A (F F' : obCoMod A) (ff' : 'CoMod(0 F' ~> F )0) (F'' : obCoMod A)
                        (ff_ : 'CoMod(0 F'' ~> F' )0), forall A' (a : 'Indexer(0 A' ~> A )0),

        ( ( a o>* ff_ ) o>CoMod ( a o>* ff' ) )
          <~~ ( a o>* (ff_ o>CoMod ff') ) 
          
  | MorCoMod_Gen_arrow : forall A (F G : obCoMod_Gen A) (gg : @morCoMod_Gen A F G)
                           A' (a : 'Indexer(0 A' ~> A )0),
      forall A'' (a' : 'Indexer(0 A'' ~> A' )0),

        ( (a' o>Indexer a) o>| 'MorCoMod_Gen gg )
          <~~ ( a' o>* ( a o>| 'MorCoMod_Gen gg ) )
              
  where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg _ _ gg0) : atom_scope.

  End Section2.

  Module Export Ex_Notations.
    Export Ex_Notations1.
    Notation "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg _ _ gg0) : atom_scope.
    Hint Constructors convMorCoMod.
  End Ex_Notations.

  Lemma convMorCoMod_sense_dom : ( forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
        gg0 <~~ gg -> F0 ~~~ F )%atom .
  Proof. induction 1; simpl; eauto. Qed.

  Lemma convMorCoMod_sense_dom' : ( forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
        forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
          gg0 <~~ gg -> F0 = F )%atom .
  Proof.
    intros; apply: ax1_convObCoMod_extensionality ;
      apply: convMorCoMod_sense_dom. eassumption.
  Qed.

  Lemma convMorCoMod_sense_codom : ( forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
        forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
          gg0 <~~ gg -> G0 ~~~ G )%atom .
  Proof. induction 1; simpl; eauto. Qed.

  Lemma convMorCoMod_sense_codom' : ( forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
        forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
          gg0 <~~ gg -> G0 = G )%atom .
  Proof.
    intros; apply: ax1_convObCoMod_extensionality ;
      apply: convMorCoMod_sense_codom. eassumption.
  Qed.
  
End Atom.

(**#+END_SRC

* Grammatical presentation of objects and morphisms internal some indexer , by decoding the indexes as metafunctors and the arrows as metatransformations

The decoding ( "Yoneda" ) of the index-for-objects which encode all the objects is some metafunctor which is programmed by the inductive-family-presentation [obCoMod] .

The decoding ( "Yoneda" ) of the index-for-morphisms which encode all the morphisms is some metafunctor which is programmed by the inductive-family-presentation [morCoMod] .

The decoding ( "Yoneda" ) of the arrow-for-domain and arrow-for-codomain which encode the domain/source and codomain/target are some metatransformations which are programmed as some additional/embedded grammatical-arguments/parameters of the inductive-family-presentation [morCoMod] of morphisms . Memo that it is not critical for sense that the domain function and codomain function must be computed via some inductive-recursive presentation ; indeed these two functions may be embedded as some additional grammatical-arguments/parameters of the inductive-family-presentation [morCoMod] of morphisms .

The decoding ( "Yoneda" ) of the whatever-is-interesting arrows between the index-for-objects and the index-for-morphims are metatransformations which are programmed as some grammatical-constructors of the inductive-presentation-for-objects and the inductive-presentation-for-morphisms .

Memo that the functoriality ( "arrows-action" ) of each metafunctor (decoded index) and the naturality ( "arrows-action" ) of each metatransformation (decoded arrow-between-indexes) is signified via some additional/embedded constructors [ObCoMod_Poly] [MorCoMod_Poly] of the inductive-families-presentations or is immediately-accumulated onto the constant constructors [UnitCoMod] [MorCoMod_Gen] .

** Grammatical presentation of objects

The decoding ( "Yoneda" ) of the index-for-objects which encode all the objects is some metafunctor which is programmed by the inductive-family-presentation [obCoMod] whose only argument/parameter is over all the indexes of the indexer [obIndexer] . 

The decoding ( "Yoneda" ) of the arrow-for-pair-of-objects between the index-for-objects is some metatransformation which is programmed as some grammatical-constructor of the inductive-presentation-for-objects  [obCoMod] .

The functoriality ( "arrows-action" ) of this decoded index-for-objects and the naturality ( "arrows-action" ) of the decoded arrow-for-pair-of-objects is signified via the constructor [ObCoMod_Poly] of this inductive-family-presentation [obCoMod] and by the conversion relation [convObCoMod] relating the grammatical-objects .

The common practice in polymorph mathematics assumes some propositional-extensionality properties ; for example that convertible objects/propositions are the same/equal . Therefore the COQ logic shall express such property , via some very-direct axiom [ax1_convObCoMod_extensionality] for example .

#+BEGIN_SRC coq :exports both :results silent **)

Import Atom.Ex_Notations.

Inductive obCoMod : obIndexer -> Type := 
| ObCoMod_Poly : forall (A A' : obIndexer), 'Indexer(0 A' ~> A )0 -> obCoMod A -> obCoMod A'
| ObCoMod_Atom : forall A, Atom.obCoMod A -> obCoMod A
| Pair : forall A, obCoMod A -> obCoMod A -> obCoMod A .

Reserved Notation "F0 ~~~ F" (at level 70).

Inductive convObCoMod : forall A (F G : obCoMod A), Prop :=

| convObCoMod_Refl :
    forall A (F : obCoMod A),
      F ~~~ F

| convObCoMod_Sym :
    forall A (F G : obCoMod A),
      G ~~~ F -> F ~~~ G

| convObCoMod_Trans :
    forall A (F uTrans : obCoMod A),
      uTrans ~~~ F -> forall (G : obCoMod A), G ~~~ uTrans -> G ~~~ F

| ObCoMod_Poly_cong : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0) (F F0 : obCoMod A),
    F0 ~~~ F -> ObCoMod_Poly a F0 ~~~ ObCoMod_Poly a F

| ObCoMod_Atom_cong : forall A (F F0 : Atom.obCoMod A),
    ( F0 ~~~ F )%atom -> ObCoMod_Atom F0 ~~~ ObCoMod_Atom F
           
| Pair_cong_1 : forall A (F1 F1' F2 : obCoMod A),
    F1' ~~~ F1 -> Pair F1' F2 ~~~ Pair F1 F2

| Pair_cong_2 : forall A (F1 F2 F2' : obCoMod A),
    F2' ~~~ F2 -> Pair F1 F2' ~~~ Pair F1 F2
                                                         
| ObCoMod_Poly_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0) (F : obCoMod A) A'' (a' : 'Indexer(0 A'' ~> A' )0),
     ObCoMod_Poly (a' o>Indexer a) F ~~~ ObCoMod_Poly a' (ObCoMod_Poly a F)

| ObCoMod_Poly_unitIndexer : forall (A : obIndexer) (F : obCoMod A),
    (ObCoMod_Poly (@unitIndexer A) F) ~~~ F

| ObCoMod_Atom_arrow : forall A (F : Atom.obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
        ObCoMod_Atom (Atom.ObCoMod_Poly a F)%atom  ~~~ ObCoMod_Poly a (ObCoMod_Atom F)

| Pair_arrow : forall A (F G : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
      Pair (ObCoMod_Poly a F) (ObCoMod_Poly a G) ~~~ ObCoMod_Poly a (Pair F G)

where "F0 ~~~ F" := (@convObCoMod _ F F0) : poly_scope.

Hint Constructors convObCoMod.

Axiom ax1_convObCoMod_extensionality :  forall A (F G : obCoMod A), G ~~~ F -> G = F .

(**#+END_SRC

** Grammatical presentation of morphisms

The decoding ( "Yoneda" ) of the index-for-morphisms which encode all the morphisms is some metafunctor which is programmed by the inductive-family-presentation [morCoMod] .

The decoding ( "Yoneda" ) of the arrow-for-domain and arrow-for-codomain which encode the domain/source and codomain/target are some metatransformations which are programmed as some additional/embedded grammatical-arguments/parameters of the inductive-family-presentation [morCoMod] of morphisms . Memo that it is not critical for sense that the domain function and codomain function must be computed via some inductive-recursive presentation ; indeed these two functions may be embedded as some additional grammatical-arguments/parameters of the inductive-family-presentation [morCoMod] of morphisms .

The decoding ( "Yoneda" ) of the whatever-is-interesting arrows between the index-for-objects and the index-for-morphims are metatransformations which are programmed as some grammatical-constructors of the inductive-presentation-for-objects and the inductive-presentation-for-morphisms .

The functoriality ( "arrows-action" ) of this decoded index-for-morphisms and the naturality ( "arrows-action" ) of the decoded arrows for pairing-projections is signified via the constructor [MorCoMod_Poly] of this inductive-family-presentation [morCoMod] and by the conversion relation [convMorCoMod] relating the grammatical-morphisms . Also memo that here polymorphism/cut-elimination says that both this cut-constructor for arrows ( "arrow-action" , "polyarrow" ) and the common cut-constructor for morphisms ( "composition" , "polymorphism" ) are eliminated/erased .

For internal polymorph mathematics , the common operations on the morphisms are pointwise/dimensional ; this contrast from enriched/multifolded polymorph mathematics where the objects are touched individually and the common operations on the morphisms are multiplicative .

#+BEGIN_SRC coq :exports both :results silent **)

Inductive morCoMod : forall A : obIndexer,
    (*MEMO: THESE ARE COMPUTED INDEX *) obCoMod A -> obCoMod A -> Type :=

| MorCoMod_Poly : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
    forall (F G : obCoMod A), 'CoMod(0 F ~> G )0 -> 'CoMod(0 (ObCoMod_Poly a F) ~> (ObCoMod_Poly a G) )0

| PolyCoMod : forall A (F F' : obCoMod A),
    'CoMod(0 F' ~> F )0 -> forall (F'' : obCoMod A),
      'CoMod(0 F'' ~> F' )0 -> 'CoMod(0 F'' ~> F )0

| UnitCoMod : forall A (F : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
      'CoMod(0 (ObCoMod_Poly a F) ~> (ObCoMod_Poly a F) )0

| MorCoMod_Atom : forall A (F G : Atom.obCoMod A),
    'CoMod(0 F ~> G )0 %atom -> 'CoMod(0 (ObCoMod_Atom F) ~> (ObCoMod_Atom G) )0

| Project1 : forall A (F1 F2 : obCoMod A), forall Z1 : obCoMod A,
      'CoMod(0 F1 ~> Z1 )0 ->
        'CoMod(0 (Pair F1 F2) ~> Z1 )0

| Project2 : forall A (F1 F2 : obCoMod A), forall Z2 : obCoMod A,
      'CoMod(0 F2 ~> Z2 )0 ->
        'CoMod(0 (Pair F1 F2) ~> Z2 )0

| Pairing : forall A (L : obCoMod A) (F1 F2 : obCoMod A), 
      'CoMod(0 L ~> F1 )0 -> 'CoMod(0 L ~> F2 )0 ->
          'CoMod(0 L ~> (Pair F1 F2) )0 

where "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : poly_scope. 

Notation "a o>* ff" :=
  (@MorCoMod_Poly _ _ a _ _ ff) (at level 3 , ff at next level, left associativity) : poly_scope.

Notation "ff_ o>CoMod ff'" :=
  (@PolyCoMod _ _ _ ff' _ ff_) (at level 40 , ff' at next level) : poly_scope.

Notation "a o>| @ ''UnitCoMod' F" := (@UnitCoMod _ F _ a) (at level 3, only parsing) : poly_scope.

Notation "a o>| ''UnitCoMod'" := (@UnitCoMod _ _ _ a) (at level 3) : poly_scope.

Notation "''MorCoMod_Atom' ff" :=
      (@MorCoMod_Atom _ _ _ ff) (at level 3) : poly_scope.

Notation "~_1 @ F2 o>CoMod zz1" :=
  (@Project1 _ _ F2 _ zz1) (at level 4, F2 at next level) : poly_scope.

Notation "~_1 o>CoMod zz1" :=
  (@Project1 _ _ _ _ zz1) (at level 4) : poly_scope.

Notation "~_2 @ F1 o>CoMod zz2" :=
  (@Project2 _ F1 _ _ zz2) (at level 4, F1 at next level) : poly_scope.

Notation "~_2 o>CoMod zz2" :=
  (@Project2 _ _ _ _ zz2) (at level 4) : poly_scope.

Notation "<< ff1 ,CoMod ff2 >>" :=
  (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : poly_scope.

(**#+END_SRC

* Grammatical conversions of morphisms , which infer the same domain/codomain-computation

As common, the grammatical conversions are classified into the total/(multi-step) conversions , and the congruences conversions , and the constant conversions which are used in the polyarrow/polymorphism/cut-elimination lemma , and the constant conversions which are only for the wanted sense of pairing-projections-grammar , and the constant conversions which are only for the confluence lemma .

Also in contrast, because of the embedded extra-arguments/parameters in the inductive-family-presentation of the morphisms, the conversion-relation shall convert across two morphisms whose domain/codomain-computation arguments are not syntactically/grammatically-the-same. But oneself does show that, by logical-deduction [convMorCoMod_sense_dom], these two domain/codomain-computations are indeed propositionally equal ( "soundness lemma" ) . 

Finally, some linear total/asymptotic grade is defined on the morphisms and the tactics-automated degradation lemma shows that each of the conversion indeed degrades the redex morphism . (ERRATA: Memo that this new grade function is simplified in comparison from earlier attempts , because strict-degrading-of-the-conversions is not really required but some form of strict-degrading occurs during the computational/total/asymptotic cut-elimination ... )

** Grammatical conversions of morphisms

#+BEGIN_SRC coq :exports both :results silent **)

Reserved Notation "gg0 <~~ gg" (at level 70).

Inductive convMorCoMod : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 %poly ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 %poly ), Prop :=

| convMorCoMod_Refl : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
    gg <~~ gg

| convMorCoMod_Trans :
    forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
    forall (F0 G0 : obCoMod A) (uTrans : 'CoMod(0 F0 ~> G0 )0 ),
      uTrans <~~ gg -> forall (F00 G00 : obCoMod A) (gg00 : 'CoMod(0 F00 ~> G00 )0 ),
        gg00 <~~ uTrans -> gg00 <~~ gg

| MorCoMod_Poly_cong : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
    forall (F G : obCoMod A) (gg gg0 : 'CoMod(0 F ~> G )0),
      gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )

| PolyCoMod_cong_Pre : forall A (F F' : obCoMod A) (ff' : 'CoMod(0 F' ~> F )0),
    forall (F'' : obCoMod A) (ff_ ff_0 : 'CoMod(0 F'' ~> F' )0 ),
      ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

| PolyCoMod_cong_Post : forall A (F F' : obCoMod A) (ff' ff'0 : 'CoMod(0 F' ~> F )0 ),
    forall (F'' : obCoMod A) (ff_ : 'CoMod(0 F'' ~> F' )0),
      ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

| MorCoMod_Atom_cong : forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom ),
    forall (F' G' : Atom.obCoMod A) (gg0 : 'CoMod(0 F' ~> G' )0 %atom ),
    ( gg0 <~~ gg )%atom -> ( 'MorCoMod_Atom gg0 ) <~~ ( 'MorCoMod_Atom gg )

(*TODO: ?ERRATA?: as in cartierSolution3.v Project1_cong ,  shall allow more general : additional F2' with F2' ~~~ F2  *)
| Project1_cong : forall A (F2 : obCoMod A) , forall (F1 Z1 : obCoMod A) (zz1 : 'CoMod(0 F1 ~> Z1 )0),
      forall (F1' Z1' : obCoMod A) (zz1' : 'CoMod(0 F1' ~> Z1' )0),
        zz1' <~~ zz1 ->
        ( ~_1 @ F2 o>CoMod zz1' ) <~~ ( ~_1 @ F2 o>CoMod zz1 )

| Project2_cong : forall A (F1 : obCoMod A), forall (F2 Z2 : obCoMod A) (zz2 : 'CoMod(0 F2 ~> Z2 )0),
      forall (F2' Z2' : obCoMod A) (zz2' : 'CoMod(0 F2' ~> Z2' )0),
        zz2' <~~ zz2 ->
        ( ~_2 @ F1 o>CoMod zz2' ) <~~ ( ~_2 @ F1 o>CoMod zz2 )

| Pairing_cong_1 : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                     (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall (F1' : obCoMod A) (ff1' : 'CoMod(0 L ~> F1' )0),
      ff1' <~~ ff1 -> ( << ff1' ,CoMod ff2 >> ) <~~ ( << ff1 ,CoMod ff2 >> )
    
| Pairing_cong_2 : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                     (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall (F2' : obCoMod A) (ff2' : 'CoMod(0 L ~> F2' )0),
      ff2' <~~ ff2 -> ( << ff1 ,CoMod ff2' >> ) <~~ ( << ff1 ,CoMod ff2 >> )

(* for sense only , not in solution,  derivable after cut-elimination , not for reduction *)
| MorCoMod_Poly_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
    forall (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0),
    forall (A'' : obIndexer) (a' : 'Indexer(0 A'' ~> A' )0),
      ( (a' o>Indexer a) o>* gg ) <~~ ( a' o>* (a o>* gg) )

(* for sense only , not in solution , derivable after cut-elimination , not for reduction *)
| MorCoMod_Poly_unitIndexer : forall (A : obIndexer),
    forall (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0),
      gg <~~ ( (@unitIndexer A) o>* gg )

(**
(* for sense only , not in solution , derivable after cut-elimination , NOT FOR ANY REDUCTION ,
   memo this non-linearity with complex grades which is luckily avoided *)
| PolyCoMod_arrow : forall A (F F' : obCoMod A) (ff' : 'CoMod(0 F' ~> F )0) (F'' : obCoMod A)
                      (ff_ : 'CoMod(0 F'' ~> F' )0), forall A' (a : 'Indexer(0 A' ~> A )0),

      ( ( a o>* ff_ ) o>CoMod ( a o>* ff' ) )
        <~~ ( a o>* (ff_ o>CoMod ff') ) **)

| UnitCoMod_arrow : forall A (F : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
      forall A'' (a' : 'Indexer(0 A'' ~> A' )0),

        ( (a' o>Indexer a) o>| @ 'UnitCoMod F )
          <~~ ( a' o>* (a o>| @ 'UnitCoMod F) )

| MorCoMod_Atom_arrow : forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom),
    forall A' (a : 'Indexer(0 A' ~> A )0),
      ( ( 'MorCoMod_Atom ( (a o>* gg)%atom ) )%poly )
        <~~ ( ( a o>* ( 'MorCoMod_Atom gg ) )%poly )
        
| Project1_arrow : forall (A : obIndexer) (F1 F2 : obCoMod A),
    forall (Z1 : obCoMod A) (zz1 : 'CoMod(0 F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
          ( ~_1 @ (ObCoMod_Poly a F2) o>CoMod (a o>* zz1) )
            <~~ ( a o>* ( ~_1 @ F2 o>CoMod zz1 ) )

| Project2_arrow : forall A (F1 F2 : obCoMod A),
    forall (Z2 : obCoMod A) (zz2 : 'CoMod(0 F2 ~> Z2 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),

          ( ~_2 @ (ObCoMod_Poly a F1) o>CoMod (a o>* zz2) )
            <~~ ( a o>* ( ~_2 @ F1 o>CoMod zz2 ) )

(* memo this non-linearity for the arrow-action *)
| Pairing_arrow : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                    (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall A' (a : 'Indexer(0 A' ~> A )0),

      ( << a o>* ff1 ,CoMod a o>* ff2 >> )
        <~~ ( a o>* ( << ff1 ,CoMod ff2 >> ) )

(**
(* for sense only , not in solution , derivable after cut-elimination , NOT FOR ANY REDUCTION *)
| PolyCoMod_morphism : forall A (F F' : obCoMod A) (ff' : 'CoMod(0 F' ~> F )0) (F'' : obCoMod A)
                         (ff_' : 'CoMod(0 F'' ~> F' )0),
    forall (F''' : obCoMod A) (ff__ : 'CoMod(0 F''' ~> F'' )0),
      ( (ff__ o>CoMod ff_') o>CoMod ff' )
        <~~ ( ff__ o>CoMod (ff_' o>CoMod ff') ) **)

| Project1_morphism : forall A (F1 F2 : obCoMod A), forall Z1 : obCoMod A,
      forall (zz1 : 'CoMod(0 F1 ~> Z1 )0), forall Y1 : obCoMod A, forall (yy : 'CoMod(0 Z1 ~> Y1 )0),

            ( ~_1 @ F2 o>CoMod (zz1 o>CoMod yy) )
              <~~ ( ( ~_1 @ F2 o>CoMod zz1 ) o>CoMod yy ) 

| Project2_morphism : forall A (F1 F2 : obCoMod A), forall Z2 : obCoMod A,
      forall (zz2 : 'CoMod(0 F2 ~> Z2 )0), forall Y2 : obCoMod A, forall (yy : 'CoMod(0 Z2 ~> Y2 )0),

            ( ~_2 @ F1 o>CoMod (zz2 o>CoMod yy) )
              <~~ ( ( ~_2 @ F1 o>CoMod zz2 ) o>CoMod yy ) 

(* memo this non-linearity for the morphism-action *)
| Pairing_morphism : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                       (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall (L' : obCoMod A) (ll : 'CoMod(0 L' ~> L )0),

      ( << ll o>CoMod ff1 ,CoMod ll o>CoMod ff2 >> )
        <~~ ( ll o>CoMod ( << ff1 ,CoMod ff2 >> ) )

| UnitCoMod_PolyCoMod : forall A (F : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
      forall (F'' : obCoMod A') (ff_ : 'CoMod(0 F'' ~> (ObCoMod_Poly a F) )0),
        ff_ <~~ ( ff_ o>CoMod (a o>| @'UnitCoMod F) )

| PolyCoMod_UnitCoMod : forall A (F : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
      forall (F' : obCoMod A') (ff' : 'CoMod(0 (ObCoMod_Poly a F) ~> F' )0),
        ff' <~~ ( (a o>| @'UnitCoMod F) o>CoMod ff' )

| MorCoMod_Atom_MorCoMod_Atom : forall A (F' F : Atom.obCoMod A)
    (gg' : 'CoMod(0 F' ~> F )0 %atom) (F'' : Atom.obCoMod A)
    (gg_ : 'CoMod(0 F'' ~> F' )0 %atom),
    ( 'MorCoMod_Atom ( gg_ o>CoMod gg' )%atom )
      <~~ ( ( 'MorCoMod_Atom gg_ ) o>CoMod ( 'MorCoMod_Atom gg' ) )%poly

| Pairing_Project1 : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                       (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall Z1 : obCoMod A, forall (zz1 : 'CoMod(0 F1 ~> Z1 )0),

        ( ff1 o>CoMod zz1 )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1 ) )

| Pairing_Project2 : forall A (L : obCoMod A) (F1 F2 : obCoMod A)
                       (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0),
    forall Z2 : obCoMod A, forall (zz2 : 'CoMod(0 F2 ~> Z2 )0),

        ( ff2 o>CoMod zz2 )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2 ) )
          
(* for sense , also in solution , not for primo reduction , but may for secondo reduction *)
| Project1_Project2_Pairing : forall A (F1 F2 : obCoMod A),
    forall A' (a : 'Indexer(0 A' ~> A )0),   

    ( a o>| @ 'UnitCoMod (Pair F1 F2) )
      <~~ ( << ( ~_1 @ (ObCoMod_Poly a F2) o>CoMod ( a o>| @ 'UnitCoMod F1 ) )
          ,CoMod ( ~_2 @ (ObCoMod_Poly a F1) o>CoMod ( a o>| @ 'UnitCoMod F2 ) ) >> )

(* for confluence , also in solution , immediately-derivable in polymorphism , not for primo reduction , but may for secondo reduction *)
| Project1_Pairing : forall A (L : obCoMod A) (F1 F2 : obCoMod A) 
                       (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0) (H : obCoMod A),
    ( ~_1 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( ~_1 @ H o>CoMod ff1 ) ,CoMod ( ~_1 @ H o>CoMod ff2 ) >> )

(* for confluence , also in solution , immediately-derivable in polymorphism , not for primo reduction , but may for secondo reduction *)
| Project2_Pairing : forall A (L : obCoMod A) (F1 F2 : obCoMod A) 
                       (ff1 : 'CoMod(0 L ~> F1 )0) (ff2 : 'CoMod(0 L ~> F2 )0) (H : obCoMod A),
    ( ~_2 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( ~_2 @ H o>CoMod ff1 ) ,CoMod ( ~_2 @ H o>CoMod ff2 ) >> )

where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg _ _ gg0).

Hint Constructors convMorCoMod.

(**#+END_SRC

** Same domain/codomain-computation for convertible morphisms

#+BEGIN_SRC coq :exports both :results silent **)

Lemma convMorCoMod_sense_dom : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
        gg0 <~~ gg -> F0 ~~~ F .
Proof. induction 1; simpl; intros;
         try match goal with
             | [ Hred : ( _ <~~ _ )%atom |- _ ] =>
               move : (Atom.convMorCoMod_sense_dom Hred)
             end; eauto.
Qed.

Lemma convMorCoMod_sense_dom' : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
        gg0 <~~ gg -> F0 = F .
Proof.
  intros; apply: ax1_convObCoMod_extensionality ;
    apply: convMorCoMod_sense_dom. eassumption.
Qed.

Lemma convMorCoMod_sense_codom : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
        gg0 <~~ gg -> G0 ~~~ G .
Proof. induction 1; simpl; intros;
         try match goal with
             | [ Hred : ( _ <~~ _ )%atom |- _ ] =>
               move : (Atom.convMorCoMod_sense_codom Hred)
             end; eauto.
Qed.

Lemma convMorCoMod_sense_codom' : forall A, forall (F G : obCoMod A) ( gg : 'CoMod(0 F ~> G )0 ),
      forall (F0 G0 : obCoMod A) ( gg0 : 'CoMod(0 F0 ~> G0 )0 ),
        gg0 <~~ gg -> G0 = G .
Proof.
    intros; apply: ax1_convObCoMod_extensionality ;
      apply: convMorCoMod_sense_codom. eassumption.
Qed.

(**#+END_SRC

** Linear total/asymptotic grade and the degradation lemma

#+BEGIN_SRC coq :exports both :results silent **)

Notation max m n := ((m + (Nat.sub n m))%coq_nat).

Fixpoint grade_Atom A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom ) {struct gg} : nat . 
Proof.
  case : A F G / gg . 
  - intros ? ? a ? ? gg .
    exact:  ( S ( grade_Atom _ _ _ gg + ( grade_Atom _ _ _ gg + grade_Atom _ _ _ gg )%coq_nat )%coq_nat ) .
  - intros ? ? ? ff' ? ff_ .
    exact: ( S (grade_Atom _ _ _ ff' + grade_Atom _ _ _ ff_)%coq_nat )%coq_nat .
  - intros. exact: (S O).
Defined.

Fixpoint grade A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ) {struct gg} : nat . 
Proof.
  case : A F G / gg . 
  - intros ? ? a ? ? gg .
    exact:  ( (S (grade _ _ _ gg) ) + (S (grade _ _ _ gg) + S (grade _ _ _ gg) )%coq_nat )%coq_nat .
  - intros ? ? ? ff' ? ff_ .
    exact: (S (grade _ _ _ ff' + grade _ _ _ ff_)%coq_nat + S (grade _ _ _ ff' + grade _ _ _ ff_)%coq_nat)%coq_nat .
  - intros. exact: (S O).
  - intros ? ? ? gg. exact: (S (grade_Atom gg)).
  - intros ? ? ? ? zz1 .
    exact: (S (grade _ _ _ zz1)).
  - intros ? ? ? ? zz2 .
    exact: (S (grade _ _ _ zz2)).
  - intros ? ? ? ? ff1 ff2 .
    refine (S (max (grade _ _ _ ff1) (grade _ _ _ ff2))).
Defined.

Lemma grade_Atom_gt0 : forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom),
     ((S O) <= (grade_Atom gg))%coq_nat.
Proof. intros; case : gg; intros; apply/leP; intros; simpl; auto. Qed.

Lemma grade_gt0 : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
     ((S O) <= (grade gg))%coq_nat.
Proof. intros; case : gg; intros; try exact: grade_Atom_gt0; apply/leP; intros; simpl; auto. Qed.

Ltac tac_grade_Atom_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ ~> _ )0 %atom ,
                        gg4 : 'CoMod(0 _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
                                          (@grade_Atom_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ ~> _ )0 %atom ,
                        gg4 : 'CoMod(0 _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
                                          (@grade_Atom_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ ~> _ )0 %atom  |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ ~> _ )0 %atom  |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) 
  end.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ ~> _ )0 ,
                        gg4 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
                                          (@grade_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ ~> _ )0 ,
                        gg4 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
                                          (@grade_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ ~> _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ ~> _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) 
  end.

Lemma degrade_Atom
  : ( forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 )
      (F0 G0 : Atom.obCoMod A) (gg0 : 'CoMod(0 F0 ~> G0 )0 ),
    gg0 <~~ gg -> ( grade_Atom gg0 <= grade_Atom gg )%coq_nat )%atom .
Proof.
  intros until gg0. intros red_gg.
  elim : A F G gg F0 G0 gg0 / red_gg ;
    try solve [ simpl; intros; abstract intuition Omega.omega ].
Qed.

Lemma degrade
  : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 )
      (F0 G0 : obCoMod A) (gg0 : 'CoMod(0 F0 ~> G0 )0 ),
    gg0 <~~ gg -> ( grade gg0 <= grade gg )%coq_nat .
Proof.
  intros until gg0. intros red_gg.
  elim : A F G gg F0 G0 gg0 / red_gg ;
    try solve [ simpl; intros;
                try match goal with
                    | [ Hred : ( _ <~~ _ )%atom |- _ ] =>
                      move : (degrade_Atom Hred) ; clear Hred
                    end;
                abstract intuition Omega.omega ].
Qed.

Ltac tac_degrade H_grade :=
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%atom |- _ ] =>
           move : (degrade_Atom Hred) ; clear Hred
         | [ Hred : ( _ <~~ _ ) |- _ ] =>
           move : (degrade Hred) ; clear Hred
         end;
  move: H_grade; simpl; intros;
  try tac_grade_Atom_gt0; try tac_grade_gt0; intros; Omega.omega.

(**#+END_SRC

* Solution

As common, the purely-grammatical polyarrow [MorCoMod_Poly] cut-constructor and polymorphism cut-constructor [PolyCoMod] are not part of the solution .

For sure, polyarrow/polymorphism/cut-elimination cannot proceed beyond the polyarrows/polymorphisms/cuts which are contained in the atomic morphisms generated by the generating data .

** Solution morphisms without polyarrow/polymorphism

#+BEGIN_SRC coq :exports both :results silent **)

Module Sol.

  Module Atom.

    Section Section1.
    Delimit Scope sol_atom_scope with sol_atom.

    Inductive morCoMod : forall A : obIndexer, Atom.obCoMod A -> Atom.obCoMod A -> Type :=

    | PolyCoMod : forall A (F F' : Atom.obCoMod A),
        'CoMod(0 F' ~> F )0 -> forall (F'' : Atom.obCoMod A),
          'CoMod(0 F'' ~> F' )0 -> 'CoMod(0 F'' ~> F )0

    | MorCoMod_Gen : forall A (F G : obCoMod_Gen A),
        @morCoMod_Gen A F G -> forall A' (a : 'Indexer(0 A' ~> A )0),
          'CoMod(0 (Atom.ObCoMod_Gen F a) ~> (Atom.ObCoMod_Gen G a) )0

    where "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : sol_atom_scope. 

    End Section1.

    Module Export Ex_Notations.
      Delimit Scope sol_atom_scope with sol_atom.

      Notation "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : sol_atom_scope. 

      Notation "ff_ o>CoMod ff'" :=
        (@PolyCoMod _ _ _ ff' _ ff_) (at level 40 , ff' at next level) : sol_atom_scope.

      Notation "a o>| ''MorCoMod_Gen' ff" :=
        (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : sol_atom_scope.
    End Ex_Notations.
    
  End Atom.

  Section Section1.
  Import Atom.Ex_Notations.
  Delimit Scope sol_scope with sol.

  Inductive morCoMod : forall A : obIndexer, obCoMod A -> obCoMod A -> Type :=

  | UnitCoMod : forall A (F : obCoMod A), forall A' (a : 'Indexer(0 A' ~> A )0),
        'CoMod(0 (ObCoMod_Poly a F) ~> (ObCoMod_Poly a F) )0

  | MorCoMod_Atom : forall A (F G : Atom.obCoMod A),
      'CoMod(0 F ~> G )0 %sol_atom -> 'CoMod(0 (ObCoMod_Atom F) ~> (ObCoMod_Atom G) )0

  | Project1 : forall A (F1 F2 : obCoMod A), forall Z1 : obCoMod A,
        'CoMod(0 F1 ~> Z1 )0 ->
        'CoMod(0 (Pair F1 F2) ~> Z1 )0

  | Project2 : forall A (F1 F2 : obCoMod A), forall Z2 : obCoMod A,
        'CoMod(0 F2 ~> Z2 )0 ->
        'CoMod(0 (Pair F1 F2) ~> Z2 )0

  | Pairing : forall A (L : obCoMod A) (F1 F2 : obCoMod A), 
      'CoMod(0 L ~> F1 )0 -> 'CoMod(0 L ~> F2 )0 ->
      'CoMod(0 L ~> (Pair F1 F2) )0 

  where "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : sol_scope. 

  End Section1.

  Module Import Ex_Notations.
    Export Atom.Ex_Notations.
    Delimit Scope sol_scope with sol.

    Notation "''CoMod' (0 F' ~> F )0" := (@morCoMod _ F' F) : sol_scope. 

    Notation "a o>| @ ''UnitCoMod' F" := (@UnitCoMod _ F _ a) (at level 3, only parsing) : sol_scope.

    Notation "a o>| ''UnitCoMod'" := (@UnitCoMod _ _ _ a) (at level 3) : sol_scope.

    Notation "''MorCoMod_Atom' ff" :=
      (@MorCoMod_Atom _ _ _ ff) (at level 3) : sol_scope.

    Notation "~_1 @ F2 o>CoMod zz1" :=
      (@Project1 _ _ F2 _ zz1) (at level 4, F2 at next level) : sol_scope.

    Notation "~_1 o>CoMod zz1" :=
      (@Project1 _ _ _ _ zz1) (at level 4) : sol_scope.

    Notation "~_2 @ F1 o>CoMod zz2" :=
      (@Project2 _ F1 _ _ zz2) (at level 4, F1 at next level) : sol_scope.

    Notation "~_2 o>CoMod zz2" :=
      (@Project2 _ _ _ _ zz2) (at level 4) : sol_scope.

    Notation "<< ff1 ,CoMod ff2 >>" :=
      (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : sol_scope.
  End Ex_Notations.

  Fixpoint toPolyMor_Atom A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol_atom)
           {struct gg} : 'CoMod(0 F ~> G )0 %atom . 
  Proof.
    refine match gg with
           | ( ff_ o>CoMod ff' )%sol_atom => ( (toPolyMor_Atom _ _ _ ff_) o>CoMod (toPolyMor_Atom _ _ _ ff') )%atom
           | ( a o>| 'MorCoMod_Gen gg )%sol_atom => ( a o>| 'MorCoMod_Gen gg )%atom
           end.
  Defined.

  Fixpoint toPolyMor A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol)
           {struct gg} : 'CoMod(0 F ~> G )0 . 
  Proof.
    refine match gg with
           | ( a o>| @'UnitCoMod F )%sol => ( a o>| @'UnitCoMod F )%poly
           | ( 'MorCoMod_Atom gg )%sol => ( 'MorCoMod_Atom (toPolyMor_Atom gg) )%poly
           | ( ~_1 @ F2 o>CoMod zz1 )%sol => ( ~_1 @ F2 o>CoMod (toPolyMor _ _ _ zz1) )%poly
           | ( ~_2 @ F1 o>CoMod zz2 )%sol => ( ~_2 @ F1 o>CoMod (toPolyMor _ _ _ zz2) )%poly
           | ( << ff1 ,CoMod ff2 >> )%sol => ( << (toPolyMor _ _ _ ff1) ,CoMod (toPolyMor _ _ _ ff2) >> )%poly
           end.
  Defined.

  (**#+END_SRC

** Destruction of morphisms with inner-instantiation of object-indexes

Regardless the extra-arguments/parameters in the inductive-family-presentations , oneself easily still-gets the common dependent-destruction of morphisms with inner-instantiation of object-indexes

#+BEGIN_SRC coq :exports both :results silent **)
  
  Module Destruct_domPair.

  Inductive morCoMod_domPair
  : forall A (F1 F2 : obCoMod A), forall (G : obCoMod A),
        'CoMod(0 (Pair F1 F2) ~> G )0 %sol -> Type :=

  | Project1 : forall A (F1 F2 : obCoMod A), forall (Z1 : obCoMod A) (zz1 : 'CoMod(0 F1 ~> Z1 )0 %sol),
        morCoMod_domPair ( ~_1 @ F2 o>CoMod zz1 )%sol

  | Project2 : forall A (F1 F2 : obCoMod A), forall (Z2 : obCoMod A) (zz2 : 'CoMod(0 F2 ~> Z2 )0 %sol),
        morCoMod_domPair ( ~_2 @ F1 o>CoMod zz2 )%sol

  | Pairing : forall A (M M' : obCoMod A) (F1 F2 : obCoMod A)
                (ff1 : 'CoMod(0 (Pair M M') ~> F1 )0 %sol) (ff2 : 'CoMod(0 (Pair M M') ~> F2 )0 %sol),
      morCoMod_domPair ( << ff1 ,CoMod ff2 >> )%sol .

  Definition morCoMod_domPairP_Type
             A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol ) :=
    ltac:( destruct F; [ intros; refine (unit : Type)
                       | intros; refine (unit : Type)
                       | refine (morCoMod_domPair gg) ] ).

  Lemma morCoMod_domPairP
    : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol ), morCoMod_domPairP_Type gg .
  Proof.
    intros. case: A F G / gg.
    - intros; exact: tt.
    - intros; exact: tt.
    - constructor 1.
    - constructor 2.
    - destruct L; [ intros; exact: tt .. | ].
      constructor 3.
  Defined.

  End Destruct_domPair.

  Module Destruct_domAtom.

  Inductive morCoMod_domAtom
  : forall A (F : Atom.obCoMod A) (G : obCoMod A),
        'CoMod(0 (ObCoMod_Atom F) ~> G )0 %sol -> Type :=

  | MorCoMod_Atom : forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol_atom ),
      morCoMod_domAtom ( 'MorCoMod_Atom gg )%sol

  | Pairing : forall A (L : Atom.obCoMod A) (F1 F2 : obCoMod A)
                (ff1 : 'CoMod(0 (ObCoMod_Atom L) ~> F1 )0 %sol)
                (ff2 : 'CoMod(0 (ObCoMod_Atom L) ~> F2 )0 %sol),
      morCoMod_domAtom ( << ff1 ,CoMod ff2 >> )%sol .

  Definition morCoMod_domAtomP_Type
             A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol ) :=
    ltac:( destruct F; [ intros; refine (unit : Type)
                       | refine (morCoMod_domAtom gg)
                       | intros; refine (unit : Type) ] ).

  Lemma morCoMod_domAtomP
    : forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 %sol ), morCoMod_domAtomP_Type gg .
  Proof.
    intros. case: A F G / gg.
    - intros; exact: tt.
    - constructor 1.
    - intros; exact: tt. 
    - intros; exact: tt. 
    - destruct L; [ intros; exact: tt | | intros; exact: tt ].
      constructor 2.
  Defined.

  End Destruct_domAtom.
  
End Sol.

(**#+END_SRC

* Polyarrow/polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

As common, this resolution is by some non-structurally recursive function .

In contrast, this resolution also computes the domain/codomain argument/parameter of the resolved morphism, this argument/parameter is inferred as metavariable from the actual resolved morphism via the [eexists] tactic. The technical progress of this resolution does require the earlier lemma [convMorCoMod_sense_dom'] that convertible morphisms do have the same domain/codomain-computation arguments .

This COQ program and deduction is mostly-automated ; but memo that COQ lacks inductive-recursive presentations and memo that here the automation-tactics use only logical eauto-resolution because COQ lacks some more-efficient heterogeneous-rewriting tactics, because the conversion-relation do convert across two morphisms whose domain/codomain-computation arguments/parameters are not syntactically/grammatically-the-same.

#+BEGIN_SRC coq :exports both :results silent **)

Module Resolve.

  Import Sol.Ex_Notations.
  
  Ltac tac_reduce_eauto12 := simpl in * ; eauto 12.
  Ltac tac_reduce := simpl in * ; eauto.

  Fixpoint solveCoMod_Atom len {struct len} :
     forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom),
     forall grade_gg : (grade_Atom gg <= len)%coq_nat,
       { F0 : Atom.obCoMod A & { G0 : Atom.obCoMod A &
                                      { ggSol : 'CoMod(0 F0 ~> G0 )0 %sol_atom
                                      | ( (Sol.toPolyMor_Atom ggSol) <~~ gg )%atom } } }.
  Proof.
    case : len => [ | len ].

    (* len is O *)
    - ( move => ? F G gg grade_gg ); exfalso; abstract tac_degrade grade_gg.

    (* len is (S len) *)
    - move => ? F G gg; case : _ F G / gg =>
      [ A A' a F G gg (* a o>* gg *)
      | A F F' ff' F'' ff_ (* ff_ o>CoMod ff' *)
      | F G A gg A' a (* a o>| 'MorCoMod_Gen gg *)
      ] grade_gg .

      (* gg is a o>* gg *)
      + case: (solveCoMod_Atom len _ _ _ gg)
        => [ | F0_gg [ G0_gg [ ggSol ggSol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (Atom.convMorCoMod_sense_dom' ggSol_prop) => ggSol_prop_eq; subst.
        move : (Atom.convMorCoMod_sense_codom' ggSol_prop) => ggSol_prop_eq; subst.
        
        { destruct ggSol as
              [ A F F' ff'Sol F'' ff_Sol (* ff_Sol o>CoMod ff'Sol *)
              | F G A ggSol _A' _a (* _a o>| 'MorCoMod_Gen ggSol *) ] .

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* ( ff_Sol o>CoMod ff'Sol ) *)          
          - case: (solveCoMod_Atom len _ _ _ ((a o>* (Sol.toPolyMor_Atom ff_Sol))%atom))
            => [ | F0_a_o_ff_Sol [ G0_a_o_ff_Sol [ a_o_ff_Sol a_o_ff_Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (Atom.convMorCoMod_sense_dom' a_o_ff_Sol_prop) => a_o_ff_Sol_prop_eq; subst.
            move : (Atom.convMorCoMod_sense_codom' a_o_ff_Sol_prop) => a_o_ff_Sol_prop_eq; subst.

            case: (solveCoMod_Atom len _ _ _ ((a o>* (Sol.toPolyMor_Atom ff'Sol))%atom))
            => [ | F0_a_o_ff'Sol [ G0_a_o_ff'Sol [ a_o_ff'Sol a_o_ff'Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (Atom.convMorCoMod_sense_dom' a_o_ff'Sol_prop) => a_o_ff'Sol_prop_eq; subst.
            move : (Atom.convMorCoMod_sense_codom' a_o_ff'Sol_prop) => a_o_ff'Sol_prop_eq; subst.            
            eexists. eexists. exists ( a_o_ff_Sol o>CoMod a_o_ff'Sol )%sol_atom .
            clear - ggSol_prop a_o_ff_Sol_prop a_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is  a o>* gg , to  a o>* ggSol , is _a o>| 'MorCoMod_Gen ggSol *)          
          - eexists. eexists. exists ( (a o>Indexer _a) o>| 'MorCoMod_Gen ggSol )%sol_atom .
            clear - ggSol_prop. tac_reduce.
        }

      (* gg is  ff_ o>CoMod ff' *)          
      + case: (solveCoMod_Atom len _ _ _ ff_)
        => [ | F0_ff_Sol [ G0_ff_Sol [ ff_Sol ff_Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (Atom.convMorCoMod_sense_dom' ff_Sol_prop) => ff_Sol_prop_eq; subst.
        move : (Atom.convMorCoMod_sense_codom' ff_Sol_prop) => ff_Sol_prop_eq; subst.

        case: (solveCoMod_Atom len _ _ _ ff')
        => [ | F0_ff'Sol [ G0_ff'Sol [ ff'Sol ff'Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (Atom.convMorCoMod_sense_dom' ff'Sol_prop) => ff'Sol_prop_eq; subst.
        move : (Atom.convMorCoMod_sense_codom' ff'Sol_prop) => ff'Sol_prop_eq; subst.
        
        eexists. eexists. exists ( ff_Sol o>CoMod ff'Sol )%sol_atom .
        clear - ff_Sol_prop ff'Sol_prop . tac_reduce_eauto12.

      (* gg is  a o>| 'MorCoMod_Gen gg *)          
      + eexists. eexists. exists ( a o>| 'MorCoMod_Gen gg )%sol_atom .
        apply: Atom.convMorCoMod_Refl.
  Defined.

  Definition solveCoMod_Atom' :
    forall A (F G : Atom.obCoMod A) (gg : 'CoMod(0 F ~> G )0 %atom),
      { F0 : Atom.obCoMod A & { G0 : Atom.obCoMod A &
                                     { ggSol : 'CoMod(0 F0 ~> G0 )0 %sol_atom
                                     | ( (Sol.toPolyMor_Atom ggSol) <~~ gg )%atom } } }.
  Admitted.
  
  Fixpoint solveCoMod len {struct len} :
     forall A (F G : obCoMod A) (gg : 'CoMod(0 F ~> G )0 ),
     forall grade_gg : (grade gg <= len)%coq_nat,
       { F0 : obCoMod A & { G0 : obCoMod A & { ggSol : 'CoMod(0 F0 ~> G0 )0 %sol
                                             | (Sol.toPolyMor ggSol) <~~ gg } } }.
  Proof.
    case : len => [ | len ].

    (* len is O *)
    - ( move => ? F G gg grade_gg ); exfalso; abstract tac_degrade grade_gg.

    (* len is (S len) *)
    - move => ? F G gg; case : _ F G / gg =>
      [ A A' a F G gg (* a o>* gg *)
      | A F F' ff' F'' ff_ (* ff_ o>CoMod ff' *)
      | A F A' a  (* a o>| @'UnitCoMod F *)
      | A F G gg (* 'MorCoMod_Atom gg *)
      | A F1 F2 Z1 zz1 (* ~_1 @ F2 o>CoMod zz1 *)
      | A F1 F2 Z2 zz2 (* ~_2 @ F1 o>CoMod zz2 *)
      | A L F1 F2 ff1 ff2 (* << ff1 ,CoMod ff2 >> *)
      ] grade_gg .

      (* gg is a o>* gg *)
      + all: cycle 1. 
      
      (* gg is ff_ o>CoMod ff' *)
      + all: cycle 1. 
        
      (* gg is a o>| @'UnitCoMod F *)
      + eexists. eexists. exists (a o>| @'UnitCoMod F)%sol. apply: convMorCoMod_Refl.

      (* gg is  'MorCoMod_Atom gg *)
      + case: (solveCoMod_Atom' gg)
        => [ F0_gg [ G0_gg [ ggSol ggSol_prop ] ] ] .
        eexists. eexists. exists ( 'MorCoMod_Atom ggSol )%sol.
        clear - ggSol_prop. abstract tac_reduce.

      (* gg is ~_1 @ F2 o>CoMod zz1 *)
      + case: (solveCoMod len _ _ _ zz1)
        => [ | F0_zz1 [ G0_zz1 [ zz1Sol zz1Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.

        eexists. eexists. exists ( ~_1 @ F2 o>CoMod zz1Sol )%sol.
        clear - zz1Sol_prop. abstract tac_reduce.

      (* gg is ~_2 @ F1 o>CoMod zz2 *)
      + case: (solveCoMod len _ _ _ zz2)
        => [ | F0_zz2 [ G0_zz2 [ zz2Sol zz2Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.

        eexists. eexists. exists ( ~_2 @ F1 o>CoMod zz2Sol )%sol.
        clear - zz2Sol_prop. abstract tac_reduce.

      (* gg is << ff1 ,CoMod ff2 >> *)
      + case: (solveCoMod len _ _ _ ff1)
        => [ | F0_ff1 [ G0_ff1 [ ff1Sol ff1Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (convMorCoMod_sense_dom' ff1Sol_prop) => ff1Sol_prop_eq; subst.
        move : (convMorCoMod_sense_codom' ff1Sol_prop) => ff1Sol_prop_eq; subst.
        
        case: (solveCoMod len _ _ _ ff2)
        => [ | F0_ff2 [ G0_ff2 [ ff2Sol ff2Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (convMorCoMod_sense_dom' ff2Sol_prop) => ff2Sol_prop_eq; subst.
        move : (convMorCoMod_sense_codom' ff2Sol_prop) => ff2Sol_prop_eq; subst.

        eexists. eexists. exists ( << ff1Sol ,CoMod ff2Sol >> )%sol.

        clear - ff1Sol_prop ff2Sol_prop. tac_reduce.

      (* gg is a o>* gg *)
      + case: (solveCoMod len _ _ _ gg)
        => [ | F0_gg [ G0_gg [ ggSol ggSol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (convMorCoMod_sense_dom' ggSol_prop) => ggSol_prop_eq; subst.
        move : (convMorCoMod_sense_codom' ggSol_prop) => ggSol_prop_eq; subst.
        
        { destruct ggSol as
              [ A F _A' _a  (* _a o>| @'UnitCoMod F %sol *)
              | A F G ggSol (* 'MorCoMod_Atom ggSol %sol *)
              | A F1 F2 Z1 zz1Sol (* ~_1 @ F2 o>CoMod zz1Sol %sol *)
              | A F1 F2 Z2 zz2Sol (* ~_2 @ F1 o>CoMod zz2Sol %sol *)
              | A L F1 F2 ff1Sol ff2Sol (* << ff1Sol ,CoMod ff2Sol >> %sol *) ] .
          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* ( _a o>| @'UnitCoMod F ) *)          
          - eexists. eexists. exists ( (a o>Indexer _a) o>| @'UnitCoMod F )%sol.
            clear - ggSol_prop. tac_reduce.

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* 'MorCoMod_Atom ggSol *)          
          - case: (solveCoMod_Atom' ((a o>* (Sol.toPolyMor_Atom ggSol))%atom))
            => [ F0_a_o_ggSol [ G0_a_o_ggSol [ a_o_ggSol a_o_ggSol_prop ] ] ] .

            eexists. eexists. exists ( 'MorCoMod_Atom ( a_o_ggSol )%atom )%sol .
            clear - ggSol_prop a_o_ggSol_prop . tac_reduce.
            
          (* gg is a o>* gg , to a o>* ggSol , is   a o>* ~_1 @ F2 o>CoMod zz1Sol *)          
          - case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor zz1Sol)))
            => [ | F0_a_o_zz1Sol [ G0_a_o_zz1Sol [ a_o_zz1Sol a_o_zz1Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.

            eexists. eexists. exists ( ~_1 @ (ObCoMod_Poly a F2) o>CoMod a_o_zz1Sol )%sol .
            clear - ggSol_prop a_o_zz1Sol_prop. tac_reduce.
        
          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ~_2 @ F1 o>CoMod zz2Sol *)          
          - case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor zz2Sol)))
            => [ | F0_a_o_zz2Sol [ G0_a_o_zz2Sol [ a_o_zz2Sol a_o_zz2Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.

            eexists. eexists. exists ( ~_2 @ (ObCoMod_Poly a F1) o>CoMod a_o_zz2Sol )%sol .
            clear - ggSol_prop a_o_zz2Sol_prop. tac_reduce.

          (* gg is a o>* gg , to a o>* ggSol , is   a o>* << ff1Sol ,CoMod ff2Sol >> *)          
          - case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor ff1Sol)))
            => [ | F0_a_o_ff1Sol [ G0_a_o_ff1Sol [ a_o_ff1Sol a_o_ff1Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' a_o_ff1Sol_prop) => a_o_ff1Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' a_o_ff1Sol_prop) => a_o_ff1Sol_prop_eq; subst.

            case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor ff2Sol)))
            => [ | F0_a_o_ff2Sol [ G0_a_o_ff2Sol [ a_o_ff2Sol a_o_ff2Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' a_o_ff2Sol_prop) => a_o_ff2Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' a_o_ff2Sol_prop) => a_o_ff2Sol_prop_eq; subst.
 
           eexists. eexists. exists ( << a_o_ff1Sol ,CoMod a_o_ff2Sol >> )%sol .
           clear - ggSol_prop a_o_ff1Sol_prop a_o_ff2Sol_prop . tac_reduce_eauto12.
        }

      (* gg is ff_ o>CoMod ff' *)
      + case: (solveCoMod len _ _ _ ff_)
        => [ | F0_ff_ [ G0_ff_ [ ff_Sol ff_Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (convMorCoMod_sense_dom' ff_Sol_prop) => ff_Sol_prop_eq; subst.
        move : (convMorCoMod_sense_codom' ff_Sol_prop) => ff_Sol_prop_eq; subst.

        case: (solveCoMod len _ _ _ ff')
        => [ | F0_ff' [ G0_ff' [ ff'Sol ff'Sol_prop ] ] ] ;
            first by abstract tac_degrade grade_gg.
        move : (convMorCoMod_sense_dom' ff'Sol_prop) => ff'Sol_prop_eq; subst.
        move : (convMorCoMod_sense_codom' ff'Sol_prop) => ff'Sol_prop_eq; subst.

        (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol)  *)
        { destruct ff_Sol as
              [ A _F A' a  (* a o>| @'UnitCoMod F %sol *)
              | A _F G gg_Sol (* 'MorCoMod_Atom gg_Sol %sol *)
              | A F1 F2 Z1 zz1Sol (* ~_1 @ F2 o>CoMod zz1Sol %sol *)
              | A F1 F2 Z2 zz2Sol (* ~_2 @ F1 o>CoMod zz2Sol %sol *)
              | A L F1 F2 ff1Sol ff2Sol (* << ff1Sol ,CoMod ff2Sol >> %sol *) ] .

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is (a o>| @'UnitCoMod F) o>CoMod ff'Sol  *)
          - eexists. eexists. exists (ff'Sol). 
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.
          
          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom gg_Sol ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domAtom.morCoMod_domAtomP ff'Sol) => ff'Sol_domAtomP.
            destruct ff'Sol_domAtomP as
                [ A F G gg'Sol (* 'MorCoMod_Atom gg'Sol %sol *)
                | A L F1 F2 ff1Sol ff2Sol (* << ff1Sol ,CoMod ff2Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom gg_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom gg_Sol ) o>CoMod ( 'MorCoMod_Atom gg'Sol )   *)
            + case: (solveCoMod_Atom' ( ( (Sol.toPolyMor_Atom gg_Sol) o>CoMod (Sol.toPolyMor_Atom gg'Sol) )%atom ))
              => [ F0_ff_Sol_o_ff'Sol [ G0_ff_Sol_o_ff'Sol [ ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ] ].

              eexists. eexists. exists ( 'MorCoMod_Atom ff_Sol_o_ff'Sol )%sol . 
              clear -ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

              (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom gg_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom gg_Sol ) o>CoMod ( << ff1Sol ,CoMod ff2Sol >>  )   *)
            + case: (solveCoMod len _ _ _ (( Sol.toPolyMor ('MorCoMod_Atom gg_Sol)%sol ) o>CoMod (Sol.toPolyMor ff1Sol)))
              => [ | F0_gg_Sol_o_ff1Sol [ G0_gg_Sol_o_ff1Sol [ gg_Sol_o_ff1Sol gg_Sol_o_ff1Sol_prop ] ] ] ;
                  first by abstract tac_degrade grade_gg.
              move : (convMorCoMod_sense_dom' gg_Sol_o_ff1Sol_prop) => gg_Sol_o_ff1Sol_prop_eq; subst.
              move : (convMorCoMod_sense_codom' gg_Sol_o_ff1Sol_prop) => gg_Sol_o_ff1Sol_prop_eq; subst.

              case: (solveCoMod len _ _ _ ((  Sol.toPolyMor ('MorCoMod_Atom gg_Sol)%sol ) o>CoMod (Sol.toPolyMor ff2Sol)))
              => [ | F0_gg_Sol_o_ff2Sol [ G0_gg_Sol_o_ff2Sol [ gg_Sol_o_ff2Sol gg_Sol_o_ff2Sol_prop ] ] ] ;
                  first by abstract tac_degrade grade_gg.
              move : (convMorCoMod_sense_dom' gg_Sol_o_ff2Sol_prop) => gg_Sol_o_ff2Sol_prop_eq; subst.
              move : (convMorCoMod_sense_codom' gg_Sol_o_ff2Sol_prop) => gg_Sol_o_ff2Sol_prop_eq; subst.
 
              eexists. eexists. exists ( << gg_Sol_o_ff1Sol ,CoMod gg_Sol_o_ff2Sol >> )%sol .
              clear - ff_Sol_prop ff'Sol_prop gg_Sol_o_ff1Sol_prop gg_Sol_o_ff2Sol_prop .
              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := ( Sol.toPolyMor('MorCoMod_Atom gg_Sol)%sol ) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( Sol.toPolyMor('MorCoMod_Atom gg_Sol)%sol ) o>CoMod ( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( << (( Sol.toPolyMor('MorCoMod_Atom gg_Sol)%sol ) o>CoMod (Sol.toPolyMor ff1Sol)) ,CoMod (( Sol.toPolyMor('MorCoMod_Atom gg_Sol)%sol ) o>CoMod (Sol.toPolyMor ff2Sol)) >> )); by eauto).

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_1 @ F2 o>CoMod zz1Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz1Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | F0_zz1Sol_o_ff'Sol [ G0_zz1Sol_o_ff'Sol [ zz1Sol_o_ff'Sol zz1Sol_o_ff'Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' zz1Sol_o_ff'Sol_prop) => zz1Sol_o_ff'Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' zz1Sol_o_ff'Sol_prop) => zz1Sol_o_ff'Sol_prop_eq; subst.

            eexists. eexists. exists ( ~_1 @ F2 o>CoMod zz1Sol_o_ff'Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz1Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_2 @ F1 o>CoMod zz2Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz2Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | F0_zz2Sol_o_ff'Sol [ G0_zz2Sol_o_ff'Sol [ zz2Sol_o_ff'Sol zz2Sol_o_ff'Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' zz2Sol_o_ff'Sol_prop) => zz2Sol_o_ff'Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' zz2Sol_o_ff'Sol_prop) => zz2Sol_o_ff'Sol_prop_eq; subst.

            eexists. eexists. exists ( ~_2 @ F1 o>CoMod zz2Sol_o_ff'Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz2Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1Sol ,CoMod ff2Sol >> ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domPair.morCoMod_domPairP ff'Sol) => ff'Sol_domPairP.
            destruct ff'Sol_domPairP as
                [ A F1 F2 Z1 zz1Sol (*  ~_1 @ F2 o>CoMod zz1Sol %sol *)
                | A F1 F2 Z2 zz2Sol (*  ~_2 @ F1 o>CoMod zz2Sol %sol *)
                | A M M' F1 F2 _ff1Sol _ff2Sol (* << _ff1Sol ,CoMod _ff2Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1Sol ,CoMod ff2Sol >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff1Sol) o>CoMod (Sol.toPolyMor zz1Sol) ))
              => [ | F0_ff1Sol_o_zz1Sol [ G0_ff1Sol_o_zz1Sol [ ff1Sol_o_zz1Sol ff1Sol_o_zz1Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' ff1Sol_o_zz1Sol_prop) => ff1Sol_o_zz1Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' ff1Sol_o_zz1Sol_prop) => ff1Sol_o_zz1Sol_prop_eq; subst.

            eexists. eexists. exists ( ff1Sol_o_zz1Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop  ff1Sol_o_zz1Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1Sol ,CoMod ff2Sol >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff2Sol) o>CoMod (Sol.toPolyMor zz2Sol) ))
              => [ | F0_ff2Sol_o_zz2Sol [ G0_ff2Sol_o_zz2Sol [ ff2Sol_o_zz2Sol ff2Sol_o_zz2Sol_prop ] ] ] ;
                first by abstract tac_degrade grade_gg.
            move : (convMorCoMod_sense_dom' ff2Sol_o_zz2Sol_prop) => ff2Sol_o_zz2Sol_prop_eq; subst.
            move : (convMorCoMod_sense_codom' ff2Sol_o_zz2Sol_prop) => ff2Sol_o_zz2Sol_prop_eq; subst.

            eexists. eexists. exists ( ff2Sol_o_zz2Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop  ff2Sol_o_zz2Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1Sol ,CoMod ff2Sol >> ) o>CoMod ( << _ff1Sol ,CoMod _ff2Sol >> )  *)
            + case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod (Sol.toPolyMor _ff1Sol)))
              => [ | F0_ff_Sol_o_ff1Sol [ G0_ff_Sol_o_ff1Sol [ ff_Sol_o_ff1Sol ff_Sol_o_ff1Sol_prop ] ] ] ;
                  first by abstract tac_degrade grade_gg.
              move : (convMorCoMod_sense_dom' ff_Sol_o_ff1Sol_prop) => ff_Sol_o_ff1Sol_prop_eq; subst.
              move : (convMorCoMod_sense_codom' ff_Sol_o_ff1Sol_prop) => ff_Sol_o_ff1Sol_prop_eq; subst.

              case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod (Sol.toPolyMor _ff2Sol)))
              => [ | F0_ff_Sol_o_ff2Sol [ G0_ff_Sol_o_ff2Sol [ ff_Sol_o_ff2Sol ff_Sol_o_ff2Sol_prop ] ] ] ;
                  first by abstract tac_degrade grade_gg.
              move : (convMorCoMod_sense_dom' ff_Sol_o_ff2Sol_prop) => ff_Sol_o_ff2Sol_prop_eq; subst.
              move : (convMorCoMod_sense_codom' ff_Sol_o_ff2Sol_prop) => ff_Sol_o_ff2Sol_prop_eq; subst.

              eexists. eexists. exists ( << ff_Sol_o_ff1Sol ,CoMod ff_Sol_o_ff2Sol >> )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff1Sol_prop ff_Sol_o_ff2Sol_prop .
              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod ( << Sol.toPolyMor _ff1Sol ,CoMod Sol.toPolyMor _ff2Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( << (( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod (Sol.toPolyMor _ff1Sol)) ,CoMod (( << Sol.toPolyMor ff1Sol ,CoMod Sol.toPolyMor ff2Sol >> ) o>CoMod (Sol.toPolyMor _ff2Sol)) >> )); by eauto).
        } 

  Defined.

End Resolve.

End INTERNAL.

(**#+END_SRC

Voila. **)
