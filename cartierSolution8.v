(** # #
#+TITLE: cartierSolution8.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution8.v
https://gitlab.com/1337777/cartier/blob/master/cartierSolution8.v.pdf

solves half of some question of CARTIER which is how to program grammatical polymorph « modos » / modified-colimits-into-viewed-functors ( "sheafification" , "forcing" ) ...
 
ERRATA :: this also solves cartierSolution7.v where the default-colimiting was "confused" .

SHORT ::

  The ends is to start with some given viewing-data on some generator-morphology and then to modify the default-colimiting which says that « each functor is the sum/colimit of its elements ; which is that the (outer) indexings/cocones of the elements of some target functor over all the elements of some source functor correspond with the (inner) transformations from this source functor into this target functor » . In other words : any outer indexing ( X ; (s : S X) |- T X ) corresponds with some inner transformation (   |- (S ~> T) ) . But where are those modified-colimits ? Oneself could get them as metafunctors over this generator-morphology , as long as oneself grammatically-distinguishes whatever-is-interesting . 

  The modified-colimiting presents this « summing/colimiting/copairing » even when any such indexing ( « real polymorph-cocones » ) is over only some viewing-elements of this source « grammatical viewing-functor » ( "local epimorphism" ) ( which assumes some finiteness properties such as finite-compact or finite-dimensional or finite-generated  ) , as long as the corresponding transformation is into the (tautologically extended) « viewed-functor » ( "sheafification") of this target functor ; and does such coherently/continuously for the viewing-data/topology sense-decodings .

   Memo that when the target functor is already viewed-functor ( "sheaf" ) then this modified-colimiting becomes the default-colimiting ; in other words it is valid to move from-to :

#+BEGIN_EXAMPLE
(f : F) ; (v : viewing at f) |- (w : viewing indexing the
                                       inner cocone (e_ f v)) -> (e_ f v w : E)
#+END_EXAMPLE

#+BEGIN_EXAMPLE
(f : F) ; ((v : viewing at f) , (w : viewing indexing the
                                       inner cocone (e_ f v))) |- (e_ f v w : E) 
#+END_EXAMPLE

  « MODOS » (modified-colimitS) is the alpha-omega of polymorph mathematics . It shows the interdependence of computational-logic along geometry : sensible "soundness" lemma , cut-elimination , confluence lemma , sense-completeness lemma ( in presheaves whose combinatorics mimick "links"/"proof-net" ) , maximality lemma , asymptotics of randomness , DOSEN book ... ; generated-functors ( "Diaconescu lemma" ) , equalizer completion ,  image ( "regular" ) completion , essential geometric-morphisms ( "Cauchy completion" ) , BORCEUX book 1-2-3 ...

  For instant first impression , the conversion/computation-relation constructor which says that the polyelement (injection) morphism laxly-cancels the polytransf (summing/colimiting/copairing) morphism , is written as :

#+BEGIN_EXAMPLE
| PolyTransf_PolyElement : (* ... *)
 forall G f H (v : 'Generator( H ~> G | (Viewing_F G f) )),
 ( (ee_(G)(f)(H)(v)) o>CoMod 'UnitViewedFunctor )
   <~~ ( ( ( 'PolyElement v @ isFiniteness_F )
           : 'CoMod( View H ~> ViewingFunctor isFiniteness_F @ _ @~ _ ) )
         o>CoMod ( [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural ,
                            Yoneda10_ee_morphism , Yoneda10_ee_real ]]
                   : 'CoMod( _ ~> ViewedFunctor E @ _ @~ _ ) ) )
#+END_EXAMPLE

KEYWORDS :: OOO1337777 ; COQ ; MODOS

OUTLINE ::

  * Indexer metalogic , viewing data
    + Indexer metalogic
    + Viewing data
    + Unit (total) viewing
    + Intersection (point) viewing
    + Inner (dependent sum) viewing

  * Grammatical presentation of objects
    + Sense-decodings of the objects
    + Finiteness of the viewing-elements of some viewing-functor
    + Grammar of the objects , which carry the sense-decodings

  * Grammatical presentation of morphisms
    + Sense-decodings of the morphisms
    + Modified colimiting is default (common) colimiting when into viewed-functors
    + Grammar of the morphisms , which carry the sense-decodings

  * Grammatical conversions of morphisms , which infer the same sense-decoding
    + Grammatical conversions of morphisms
    + Same sense-decoding for convertible morphisms
    + Linear total/asymptotic grade and the degradation lemma

  * Solution morphisms
    + Solution morphisms without polymorphism
    + Destruction of morphisms with inner-instantiation of object-indexes

  * Polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

-----

HINT :: secondary-school engineering : redo the generated-functor-along-reindexing cartierSolution7.v as some modified-colimitS ( "Diaconescu lemma" ) : 
#+BEGIN_EXAMPLE
| PolyTransfGenerated_ : ( forall (I : obIndexer), forall (G : obGenerator) 
 (R : obReIndexer) (gr : 'Generator( G ~> Generating0 R ))
 (R_viewing : obViewingReIndexer R) 
 (ri : 'Indexer( ReIndexing0 R |- ViewedIndex I )),
 forall R' (v : 'ReIndexer( R' |- R | R_viewing )),
  'CoMod( View_Generating0 R' ~> E_ (ViewedIndex I) @ Yoneda10_ee_ gr ri v ) ) ->
'CoMod_indexed( Generated_ ~> ViewedFunctor_indexed E_ @ _ )
#+END_EXAMPLE

-----

MEMO :: 1337777.OOO ends to discover-engineer-and-teach 计算鸡-COQ polymorph mathematics to billions of secondary-school persons ( https://v.youku.com/v_show/id_XMzgwNzY2MTYxNg ) ; « MODOS » (modified-colimitS) is the alpha-omega of polymorph mathematics contra « NOISEA » (forced-fool-and-theft/lie/falsification) ...

-----

BUY MOM RECURSIVE T-SQUARE :: paypal.me/1337777 1337777.OOO@gmail.com ; 微信支付 2796386464@qq.com ; irc #OOO1337777

-----


* Indexer metalogic , viewing data

  The ends is to start with some given viewing-data on some generator-morphology and then to modify the default-colimiting which says that « each functor is the sum/colimit of its elements ; which is that the (outer) indexings/cocones of the elements of some target functor over all the elements of some source functor correspond with the (inner) transformations from this source functor into this target functor » . In other words : any outer indexing ( X ; (s : S X) |- T X ) corresponds with some inner transformation (   |- (S ~> T) ) . But where are those modified-colimits ? Oneself could get them as metafunctors over this generator-morphology , as long as oneself grammatically-distinguishes whatever-is-interesting . 

  The modified-colimiting presents this « copairing » even when any such indexing ( « real polymorph-cocones » ) is over only some viewing-elements of this source « viewing-functor » ( "local epimorphism" ) , as long as the corresponding transformation is into the (tautologically extended) « viewed-functor » ( "sheafification") of this target functor . Memo that when the target functor is already viewed-functor ( "sheaf" ) then this modified-colimiting becomes the default-colimiting ; in other words it is valid to move from-to :

#+BEGIN_EXAMPLE
(f : F) ; (v : viewing at f) |- (w : viewing indexing the
                                       inner cocone (e_ f v)) -> (e_ f v w : E)
#+END_EXAMPLE

#+BEGIN_EXAMPLE
(f : F) ; ((v : viewing at f) , (w : viewing indexing the
                                       inner cocone (e_ f v))) |- (e_ f v w : E) 
#+END_EXAMPLE

  « MODOS » (modified-colimitS) is the alpha-omega of polymorph mathematics . It shows the interdependence of computational-logic along geometry : sensible "soundness" lemma , cut-elimination , confluence lemma , sense-completeness lemma ( in presheaves whose combinatorics mimick "links"/"proof-net" ) , maximality lemma , asymptotics of randomness , DOSEN book ... ; generated-functors ( "Diaconescu lemma" ) , equalizer completion ,  image ( "regular" ) completion , essential geometric-morphisms ( "Cauchy completion" ) , BORCEUX book 1-2-3 ...

** Indexer metalogic

  As common , some generator-morphology is assumed . And the sense-decodings ( "Yoneda" ) of the things/codes in the generated grammar will be (meta-)functors [Yoneda01_functor] or natural transformations [Yoneda10_natural] over this generator-morphology .

#+BEGIN_SRC coq :exports both :results silent # # **)
Require Import ssreflect ssrfun ssrbool.
Require Lia.

Module MODIFIEDCOLIMIT.

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Primitive Projections.

Delimit Scope poly_scope with poly.
Open Scope poly.

Parameter TMP_AXIOM_OUT_OF_MEMORY : forall T, T.

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

Definition Yoneda10_natural
           Yoneda00_F (Yoneda01_F : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           Yoneda00_E (Yoneda01_E : { Yoneda01 : _ | Yoneda01_functor Yoneda01 })
           (Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G) : Prop :=
  forall G G' (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
    g o>Generator_[sval Yoneda01_E] (Yoneda10 G f)
    = Yoneda10 G' (g o>Generator_[sval Yoneda01_F] f) .

Definition Yoneda10_data
           Yoneda00_F (Yoneda01_F : Yoneda01_data Yoneda00_F)
           Yoneda00_E (Yoneda01_E : Yoneda01_data Yoneda00_E)
  :=  { Yoneda10 : ( forall G : obGenerator, Yoneda00_F G -> Yoneda00_E G ) |
      Yoneda10_natural Yoneda01_F Yoneda01_E Yoneda10 } .

(** # #
#+END_SRC

** Viewing data

  Some viewing-data [viewingData] is assumed on each object of the generator-morphology . Commonly , any viewing/cover [V] on some object [G] is some functor which is subfunctor/subobject of the functor [G] in the presheaf topos ; but here oneself shall say that any viewing [V] is any (not only subfunctor) functor with natural transformation into the functor [G] . Therefore the elements of [V] shall be regarded as indexes , and the natural transformation [Yoneda10_realize] from [V] to [G] shall be regarded as realizing/coercing those indexes into actual arrows in the generator-morphology . Memo that in this ongoing COQ program , the material mathematics will always only-depend on the actual arrow of the viewing , not how it is indexed .

  And at each object of the generator-morphology , oneself may define some transport (cast) of indexes-for-arrows from one viewing to another viewing . This is done via the class [transpViewing] which is the class of natural transformations across two viewings which preserve the realization/coercion to actual arrows .

  The properties of this viewing-data are presented and assumed in the next 3 sections : unit (total) viewing ; intersection (point) viewing ; inner (dependent sum) viewing . Moreover in some later section , oneself shall extend the presentation of viewing on any object (representable functor) to some presentation of viewings on any functor .

  Memo that clearly it can be shown that all the operations (  action and realizatiion ) can be extended (well-defined) along the quotienting axioms ( immediate for [Yoneda00_intersecViewing_quotientLogical] , common for [Yoneda00_ViewedFunctor_quotient] , new but immediate for [Yoneda00_innerViewing_quotientLogical] ) .

#+BEGIN_SRC coq :exports both :results silent # # **)
Lemma Yoneda00_View : forall (B : obGenerator), (obGenerator -> Type).
Proof. intros B. refine (fun A => 'Generator( A ~> B ) ). Defined.

Lemma Yoneda01_View : forall (B : obGenerator),
    {Yoneda01 : ( forall A A' : obGenerator,
          'Generator( A' ~> A ) -> (Yoneda00_View B) A -> (Yoneda00_View B) A' ) |
     Yoneda01_functor Yoneda01} .
Proof.
  intros. unshelve eexists.
  - intros A A' a. refine (fun b => a o>Generator b).
  - abstract (split; [intros; exact: polyGenerator_morphism
                   | intros; exact: polyGenerator_unitGenerator]).
Defined.

Record obViewing (G : obGenerator) : Type := ObViewing
{ Yoneda00_Viewing : (obGenerator -> Type) ;
  Yoneda01_Viewing : {Yoneda01 : forall H H' : obGenerator,
                         'Generator( H' ~> H ) -> Yoneda00_Viewing H -> Yoneda00_Viewing H' |
                      Yoneda01_functor Yoneda01} ;
  Yoneda10_realize : {Yoneda10 : forall H : obGenerator,
                                Yoneda00_Viewing H -> Yoneda00_View G H |
                             Yoneda10_natural (Yoneda01_Viewing) (Yoneda01_View G) Yoneda10} }.

Parameter viewingData : forall (G : obGenerator), (obViewing G) -> Prop.

Notation "''Generator' ( G' ~> G | V )" := (@Yoneda00_Viewing G V G')
     (at level 0, format "''Generator' (  G'  ~>  G  |  V  )") : poly_scope.

Notation "h o>Generator _@ G | V" := (sval (@Yoneda01_Viewing G V) _ _ h)
          (at level 40, G , V at next level, left associativity,
           format "h  o>Generator  _@  G  |  V") : poly_scope.

Notation "h o>Generator v _@ G | V" := (sval (@Yoneda01_Viewing G V) _ _ h v)
          (at level 40, v, G , V at next level,
           format "h  o>Generator  v  _@  G  |  V") : poly_scope.

Notation "h o>Generator v | V" := (h o>Generator_[sval (@Yoneda01_Viewing _ V)] v)
          (at level 40, v , V at next level, format "h  o>Generator  v  |  V") : poly_scope.

Notation "v :>Generator" := (sval (@Yoneda10_realize _ _) _ v)
          (at level 40) : poly_scope.

Definition transpViewing G (V1 V2 : obViewing G) :=
      {Yoneda10 : forall H : obGenerator, Yoneda00_Viewing V1 H -> Yoneda00_Viewing V2 H |
              Yoneda10_natural (Yoneda01_Viewing V1) (Yoneda01_Viewing V2) Yoneda10 /\
              forall H v1, ( Yoneda10 H v1 :>Generator ) = ( v1 :>Generator )  } .

Definition identity_transpViewing : forall G (V : obViewing G), transpViewing V V .
Proof.
  intros. exists (fun H => id).
  abstract (split; move; reflexivity).
Defined.

Definition identity_transpViewing' : forall G (V V' : obViewing G),
    V = V' -> { transp : transpViewing V V' * transpViewing V' V |
                forall H , sval (snd transp) H \o sval (fst transp) H =1 id }.
Proof.
  intros; subst. unshelve eexists.
  split; exact: identity_transpViewing.
  abstract (intros; move; reflexivity).
Defined.

Definition composition_transpViewing : forall G (V1 V2 V3 : obViewing G) (transp1 : transpViewing V1 V2) (transp2 : transpViewing V2 V3),  transpViewing V1 V3.
Proof.
  intros.  exists (fun H => sval transp2 H \o sval transp1 H).
  abstract (split; move; simpl; intros;
    [ rewrite (proj1 (proj2_sig transp2)) (proj1 (proj2_sig transp1)); reflexivity
    | rewrite (proj2 (proj2_sig transp2)) (proj2 (proj2_sig transp1)); reflexivity ]) . 
Defined.
(** # #
#+END_SRC

** Unit (total) viewing

  As common , at each object of the generator-morphology , the unit (total) viewing [unitViewing] which contains the unit arrow [unitGenerator] , is assumed [unitViewingP] to be (contained in the) viewing-data . 

#+BEGIN_SRC coq :exports both :results silent # # **)
Section unitViewing.

Lemma Yoneda10_View_real : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )),
    {Yoneda10 : _ | @Yoneda10_natural (Yoneda00_View G') (Yoneda01_View G')
                                      (Yoneda00_View G) (Yoneda01_View G) Yoneda10 }.
Proof.
  intros. unshelve eexists.
  - intros H g'. exact: (g' o>Generator g).
  - abstract (move; simpl; intros; exact: polyGenerator_morphism).
Defined.

Definition unitViewing (G G' : obGenerator) (g : 'Generator( G' ~> G )) :=
  (@ObViewing G (Yoneda00_View G') (Yoneda01_View G') (Yoneda10_View_real g)).

Parameter unitViewingP : forall (G G' : obGenerator) (g : 'Generator( G' ~> G )),
    @viewingData G (unitViewing g).

Definition real_transpViewing : forall G (V : obViewing G), transpViewing V (unitViewing unitGenerator) .
Proof.
  intros. exists (fun H v => (v :>Generator)).
  abstract (split; move; simpl; intros;
            [ exact: (proj2_sig (Yoneda10_realize V))
              | rewrite -unitGenerator_polyGenerator; reflexivity ]).
Defined.

End unitViewing.
(** # #
#+END_SRC

** Intersection (point) viewing

  As common , given some arrow (point) into some object of the generator-morphology and some viewing at this object , then oneself presents the intersection (point) viewing at (the source of) the arrow/point . This is presented as the pullback / [indexed-equalizer] / [indexed-intersection] / [equalized-product] [Yoneda00_intersecViewing] ; and as is common in polymorph mathematics , the particular-deduction of the second-component equalizing-property of this pullback shall not matter ( shall be unique ) , therefore this is expressed for example via the very-direct axiom [Yoneda00_intersecViewing_quotientLogical] . Finally any intersection (point) viewing is assumed [intersecViewingP] to be (contained in the) viewing-data .

  Memo the lemma [intersecViewing_real_unitGenerator] which says that , given some viewing and some viewing-arrow contained in this viewing , then the intersection viewing of this viewing along this arrow is the unit (total) viewing . This lemma will be held in the lemma [Yoneda10_PolyElement_default_modulo] in the section [Senses_defaultColimit] where it is shown that modified-colimiting into already viewed-functors becomes the default-colimiting .

#+BEGIN_SRC coq :exports both :results silent # # **)
Section intersecViewing.

Section Section1.
Variables (G : obGenerator) (V : obViewing G)
          (G' : obGenerator) (g : 'Generator( G' ~> G )).

Definition Yoneda00_intersecViewing : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { vg' : (Yoneda00_Viewing V H * Yoneda00_Viewing (unitViewing g) H)%type |
                                ( fst vg' :>Generator ) = ( snd vg' :>Generator ) } ).
Defined.

Axiom Yoneda00_intersecViewing_quotientLogical : forall G (v v' : Yoneda00_intersecViewing G), sval v = sval v' -> v = v'.
                  
Definition Yoneda01_intersecViewing
  : {Yoneda01 : forall H H' : obGenerator, 'Generator( H' ~> H ) -> Yoneda00_intersecViewing H -> Yoneda00_intersecViewing H' |
     Yoneda01_functor Yoneda01} .
Proof.
  unshelve eexists.
  - intros H H' h vg'.
    exists ( h o>Generator (fst (sval vg')) | _ , h o>Generator (snd (sval vg')) | _ ) .
    abstract (simpl; rewrite -(proj2_sig (Yoneda10_realize V)); rewrite -(polyGenerator_morphism);
              rewrite (proj2_sig vg'); reflexivity).
  - abstract (split; simpl;
              first (by intros; apply: Yoneda00_intersecViewing_quotientLogical; simpl;
                     rewrite -(proj1 (proj2_sig (Yoneda01_Viewing V))); rewrite -[X in _ = ( _ , X )](polyGenerator_morphism); reflexivity);
              intros H vh; apply: Yoneda00_intersecViewing_quotientLogical; simpl;
              rewrite -(proj2 (proj2_sig (Yoneda01_Viewing V))); rewrite -[X in _ = ( _ , X )](polyGenerator_unitGenerator);
              move: (sval vh) => sval_vh; destruct sval_vh; reflexivity).
Defined.

Definition Yoneda10_intersecViewing_real
  : {Yoneda10 : forall H : obGenerator, Yoneda00_intersecViewing H -> Yoneda00_Viewing (unitViewing g) H |
     Yoneda10_natural Yoneda01_intersecViewing (Yoneda01_View G') Yoneda10 }.
Proof.
  unshelve eexists.
  - intros H vg'. exact: (snd (sval vg')).
  - abstract (move; reflexivity).
Defined.

Definition Yoneda10_intersecViewing_toViewing
  : {Yoneda10 : forall H : obGenerator, Yoneda00_intersecViewing H -> Yoneda00_Viewing V H |
     Yoneda10_natural Yoneda01_intersecViewing (Yoneda01_Viewing V) Yoneda10 }.
Proof.
  unshelve eexists.
  - intros H vg'. exact: (fst (sval vg')).
  - abstract (move; reflexivity).
Defined.


Definition intersecViewing := (@ObViewing G' Yoneda00_intersecViewing Yoneda01_intersecViewing Yoneda10_intersecViewing_real).

Axiom intersecViewingP : @viewingData G V -> @viewingData G' intersecViewing.
End Section1.
  
Lemma intersecViewing_unitGenerator :
  forall (G : obGenerator) (V : obViewing G), transpViewing V (intersecViewing V (unitGenerator)).
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact: v.
      * exact: (v :>Generator).
    + abstract(simpl; exact: unitGenerator_polyGenerator). 
  - split;
      [ abstract (move; simpl; intros; apply: Yoneda00_intersecViewing_quotientLogical; simpl;
                  rewrite -(proj2_sig (Yoneda10_realize V)); reflexivity) 
      | move; reflexivity].
Defined.

Lemma intersecViewing_polyGenerator :
  forall (G : obGenerator) (V : obViewing G)
    (G' : obGenerator) (g : 'Generator( G' ~> G )),
  forall (G'' : obGenerator) (g' : 'Generator( G'' ~> G' )), transpViewing (intersecViewing (intersecViewing V g) g') (intersecViewing V (g' o>Generator g)).
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact:  ( sval (Yoneda10_intersecViewing_toViewing V g) _ (fst (sval v)) )  .
      * exact: ((snd (sval v)) ).
    + abstract (simpl; rewrite (proj2_sig (fst (sval v))); simpl;
                rewrite [X in X o>Generator _ = _](proj2_sig v);
                rewrite [in RHS]polyGenerator_morphism; reflexivity).
  - split.
    + abstract (move; simpl; intros;
                apply: Yoneda00_intersecViewing_quotientLogical; simpl; reflexivity).
    + abstract (move; simpl; intros; reflexivity).
Defined.

Lemma transpViewing_real :
    forall G (V : obViewing G) H (v : 'Generator( H ~> G | V )),
      transpViewing (unitViewing unitGenerator) (intersecViewing V (v :>Generator)).
Proof.
  intros. unshelve eexists.
  - simpl. intros H0 h . unshelve eexists.
    + split.
      * exact: (h o>Generator v | V).
      * exact: h.
    + abstract (simpl; rewrite -(proj2_sig (Yoneda10_realize _)); reflexivity).
  - abstract (split;
    [ move; simpl; intros; apply: Yoneda00_intersecViewing_quotientLogical;
      simpl; rewrite (proj1 (proj2_sig (Yoneda01_Viewing _ ))); reflexivity
    | move; simpl; intros; rewrite -unitGenerator_polyGenerator; reflexivity ]).
Defined.

Definition intersecViewing_real_unitGenerator (G : obGenerator) (V : obViewing G)
           (H : obGenerator) (v :  'Generator( H ~> G | V )) :
  { h_unit : 'Generator( H ~> H | intersecViewing V (v :>Generator ) )
  | v = sval (Yoneda10_intersecViewing_toViewing V (v :>Generator)) _ h_unit } .
Proof.
  intros. (** exists ( v , @unitGenerator H ) **)
  exists ((sval (transpViewing_real v )) _ (@unitGenerator H)).
  abstract(simpl; rewrite -(proj2 (proj2_sig (Yoneda01_Viewing _))); reflexivity).
Defined.

Lemma intersecViewing_unitViewing :
  forall (G : obGenerator)  (G' : obGenerator) (g : 'Generator( G' ~> G )), transpViewing (unitViewing unitGenerator) (intersecViewing (unitViewing unitGenerator) g) .
Proof.
  intros. unshelve eexists.
  - intros H v . unshelve eexists.
    + split.
      * exact: (v o>Generator g).
      * exact: v.
    + simpl. abstract(simpl; rewrite -polyGenerator_morphism -unitGenerator_polyGenerator; reflexivity).
  - split.
    + abstract (move; simpl; intros; apply: Yoneda00_intersecViewing_quotientLogical;
                rewrite /Yoneda01_action /=; rewrite polyGenerator_morphism; reflexivity).
    + abstract (move; simpl; intros; rewrite -unitGenerator_polyGenerator; reflexivity).
Defined.

End intersecViewing.
(** # #
#+END_SRC

** Inner (dependent sum) viewing

  The common backward phrasing is that , starting from some viewing , if its intersections along the arrows/points of some other viewing-data are viewing-data , then this viewing becomes viewing-data . 

  In contrast , the new formulation below is more forward/constructive . Oneself starts with the collection of all the "would-be-intersections" viewings along the arrows of some other (outer) viewing-data , and then oneself constructs the inner/sum viewing of this collection and assumes that it is viewing-data .

  This construction and assumption will be held in the section [Senses_defaultColimit] in the definitions [viewingDefault_] and [Yoneda10_PolyElement_default] , where it is shown that the immediate/easy uncurrying of some (nested) cocone into any viewed-functor will output some (unnested) cocone whose constructed (dependent sum) indexing is indeed viewing-data by assumption . In other words : it is valid to move from-to

#+BEGIN_EXAMPLE
(f : F) ; (v : viewing at f) |- (w : viewing indexing the
                                       inner cocone (e_ f v)) -> (e_ f v w : E)
#+END_EXAMPLE

#+BEGIN_EXAMPLE
(f : F) ; ((v : viewing at f) , (w : viewing indexing the
                                       inner cocone (e_ f v))) |- (e_ f v w : E) 
#+END_EXAMPLE
#+BEGIN_SRC coq :exports both :results silent # # **)
Notation "{< G' ; v ; w >}" := (existT (fun v0 : { G'0 : obGenerator & _ } => _ ) (existT _ G' v) w)
                                (at level 0, format "{<  G'  ; '/'  v  ; '/'  w  >}").

Section innerViewing.

Section Section1.
Variables (G : obGenerator) (V : obViewing G)
          (WP_ : forall G' : obGenerator, 'Generator( G' ~> G | V ) -> obViewing G' ).

Definition Yoneda00_innerViewing : obGenerator -> Type.
Proof.
  refine (fun H : obGenerator => { v : {G' : obGenerator & Yoneda00_Viewing V G'} & Yoneda00_Viewing (WP_ (projT2 v)) H }).
Defined.

(**MEMO: also ref [PolyTransf_default_PolyElement] **)
Axiom Yoneda00_innerViewing_quotientLogical : forall (H : obGenerator),  forall (wv w'v' : Yoneda00_innerViewing H),
        (((projT2 wv) :>Generator) o>Generator (projT2 (projT1 wv)) | V)
        = (((projT2 w'v') :>Generator) o>Generator (projT2 (projT1 w'v')) | V) -> wv = w'v'.

Lemma Yoneda00_innerViewing_quotientLogical' : forall (H : obGenerator), forall H0 (v : Yoneda00_Viewing V H0) (w : Yoneda00_Viewing (WP_  v) H),  forall H0' (v' : Yoneda00_Viewing V H0') (w' : Yoneda00_Viewing (WP_ v') H),  
        ((w :>Generator) o>Generator v | V)
        = ((w' :>Generator) o>Generator v' | V) -> {< H0 ; v ; w >} = ( {< H0' ; v' ; w' >} : Yoneda00_innerViewing H ).
Proof.
  intros. apply: Yoneda00_innerViewing_quotientLogical. assumption.
Qed.
  
Definition Yoneda01_innerViewing
  : {Yoneda01 : forall H H' : obGenerator, 'Generator( H' ~> H ) -> Yoneda00_innerViewing H -> Yoneda00_innerViewing H' |
     Yoneda01_functor Yoneda01} .
Proof.
  unshelve eexists.
  - intros H H' h w.
    refine ( {< projT1 (projT1 w) ; projT2 (projT1 w) ;
              h o>Generator (projT2 w) | _ >} ).
  - abstract (split; simpl;
              first (by intros ? ? ? ? ? wv; rewrite /Yoneda01_action /= ;
                     rewrite -[ X in  _ = {<  projT1 (projT1 wv) ; projT2 (projT1 wv) ; X >}  ]
                                (proj1 (proj2_sig (@Yoneda01_Viewing _ (WP_ _)))); reflexivity);
              intros ? wv; rewrite /Yoneda01_action /= ;
              rewrite -[X in _ = {< projT1 (projT1 wv) ; projT2 (projT1 wv) ; X >}]
                         (proj2 (proj2_sig (@Yoneda01_Viewing _ (WP_ _))));
              destruct wv as [[? ?] ?]; reflexivity).
Defined.

Definition Yoneda10_innerViewing_real
  : {Yoneda10 : forall H : obGenerator, Yoneda00_innerViewing H -> Yoneda00_View G H |
     Yoneda10_natural Yoneda01_innerViewing (Yoneda01_View G) Yoneda10 }.
Proof.
  unshelve eexists.
  - simpl. intros ? wv . refine ( ((projT2 wv) :>Generator)
                                    o>Generator ( (projT2 (projT1 wv)) :>Generator ) ).
  - abstract (rewrite /Yoneda10_natural ; simpl; intros;
              rewrite /Yoneda01_action /= [in LHS]polyGenerator_morphism;
              rewrite -[in RHS]( proj2_sig (Yoneda10_realize (WP_ _))); reflexivity).
Defined.

Definition innerViewing := (@ObViewing G Yoneda00_innerViewing Yoneda01_innerViewing Yoneda10_innerViewing_real).

Parameter innerViewingP : @viewingData G V ->
                     ( forall (G' : obGenerator) (v : 'Generator( G' ~> G | V )),
                         @viewingData G' (@WP_ G' v) ) -> @viewingData G innerViewing.

End Section1.

Lemma identity_transpViewing_innerViewing :
  forall G (V_ :  obViewing G)
    (W_ : forall (H : obGenerator),'Generator( H ~> G | V_ ) -> obViewing H)
    (W0_ : forall (H : obGenerator),'Generator( H ~> G | V_  ) -> obViewing H)
    (Heq : forall (H : obGenerator) (v : 'Generator( H ~> G | V_ )),
        W_ H v = W0_ H v  ),
    transpViewing (innerViewing W_) (innerViewing W0_).
Proof.      
  unshelve eexists.
  - intros H' wv. simpl.
    move: (identity_transpViewing' (Heq _ (projT2 (projT1 wv)))) => Heq_transp .
    unshelve eexists.
    exists (projT1 (projT1 wv)).
    refine (projT2 (projT1 wv)).
    apply (sval (fst (sval Heq_transp)) _ (projT2 wv)).
  - abstract (split; [ move; simpl; intros H' H'' h wv;
      move: (identity_transpViewing' (Heq _ (projT2 (projT1 wv))));
      set H : obGenerator := projT1 (projT1 wv);
            set v : 'Generator( H ~> _ | V_ )
      := projT2 (projT1 wv);
         set w : 'Generator( H' ~> _ | W_ H v )
      := projT2 wv;
         move => Heq_transp;
                set w0 := sval (fst (sval Heq_transp)) H' w;
         rewrite [in LHS]/Yoneda01_action [LHS]/= ;
         rewrite -[in RHS](proj1 (proj2_sig (fst (sval Heq_transp))));
         reflexivity
    | intros H' wv; 
      move: (identity_transpViewing' (Heq _ (projT2 (projT1 wv))));
      set H : obGenerator := projT1 (projT1 wv);
            set v : 'Generator( H ~> _ | V_ )
      := projT2 (projT1 wv);
         set w : 'Generator( H' ~> _ | W_ H v )
      := projT2 wv;
         move => Heq_transp;
                simpl; rewrite [in LHS](proj2 (proj2_sig (fst (sval Heq_transp))));
                reflexivity ]).
Defined. 

End innerViewing.
(** # #
#+END_SRC

* Grammatical presentation of objects

  The sense-decoding of any object is some metafunctor ( [Yoneda01_data] ) together with some viewing-data/topology ( [viewingData] ) which is polymorph ( [viewingFunctor] ) . ( MEMO: the earlier presentation had the errata that the transformation [viewingFunctor] was reversed ! ) .  Memo that this data (or really property) [viewingFunctor] is some form of second (factor) projection for [Yoneda00_intersecViewing] which is carried-as-index by the inductive-type-family of functors/objects instead of being global . ( TODO : this second (factor) component should be changed to logical (not extractable existential) ? )

  The sense-decoding of any morphism is some metatransformation [Yoneda10_data] together with some continuity-property [viewingContinuous]  . 

  The grammatical objects are simultaneously-mutually presented with their sense-decoding ; this could be done via some common inductive-recursive presentation or alternatively by inferring the sense-decoding computation into extra indexes of the type-family of the objects . This same comment holds for the presentation of grammatical morphisms .

  Memo that these sense-decodings may be held for two ends : (1) to express the cocone logical-condition on any input cocone data as held by the reflector-constructor ( "universality-morphism" , copairing ) ; (2) to express the dependence of the output limit-object on the morphisms contained in some given input diagram . In the ongoing COQ program , the description (2) will not be necessary because the morphisms contained in the input diagrams are touched indirectly via the (sense-)elements of the viewing functor .

** Sense-decodings of the objects

  Oneself presents [viewingFunctor] any « viewing-functor » as any functor which polymorphly holds some viewings at each of its elements ; therefore oneself has extended the presentation of viewing on any object (representable functor) to some presentation of viewings on any functor . Memo that viewing-functors are similar as forward/constructive "local epimorphisms" ...

  The motive is that each viewing-functor is now some modified-colimit of its « viewing-elements » (action of some viewing-arrow onto some element) : the (outer) indexings/cocones of the elements of some target functor over only the viewing-elements of some viewing-functor correspond with the (inner) transformations from this viewing-functor into the target « viewed-functor » ...

  Therefore oneself tautologically defines « viewed-functor » ( "sheaf" ) of some functor as all the cocones over any viewing into this functor . As is common , two cocones over viewings are the same [Yoneda00_ViewedFunctor_quotient] if they coincide on some smaller viewing .

  TODO: ERRATA: The grammatical colimiting/sum/sigma/viewing-functor-object constructor [ViewingFunctor] shall assume some finiteness properties ( such as finite-compact or finite-dimensional or finite-generated ) onto the viewing-data/topology sense-decodings which they internalize . The required finiteness properties by the cut-elimination lemma are really only used for [ViewingFunctor] .

#+BEGIN_SRC coq :exports both :results silent # # **)
Notation "''exists' x ..." := (exist _ x _)
                                (at level 10, format "''exists'  x  ...").

Notation "[< V_ff | ... >]" := (exist (fun V_ff0 : { V0 : obViewing _ & _ } => _ ) V_ff _)
                                (at level 0, format "[<  V_ff  |  ...  >]").

Notation "[< V ; ff >]" := (existT (fun V0 : obViewing _ => _ ) V ff)
                                (at level 0, format "[<  V  ; '/'  ff  >]").

Section Senses_obCoMod.

Definition viewingFunctor (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : {Yoneda01
               : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' |
               Yoneda01_functor Yoneda01})
    (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G) :=
  forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
     transpViewing (intersecViewing (V_ G f) g) (V_ G' (g o>Generator_[sval Yoneda01_F] f)).

Definition Yoneda00_ViewedFunctor (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 }) :
  (obGenerator -> Type) := 
  ( fun G => { V_ff : { V : obViewing G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) } 
             | @viewingData G (projT1 V_ff) /\
               @Yoneda10_natural (Yoneda00_Viewing (projT1 V_ff)) (Yoneda01_Viewing (projT1 V_ff)) 
                                 (Yoneda00_F) (Yoneda01_F) (projT2 V_ff) /\
               ( forall H v v', v :>Generator = v' :>Generator ->
                                projT2 V_ff H v = projT2 V_ff H v' ) } ). 

Axiom Yoneda00_ViewedFunctor_quotient : forall Yoneda00_F Yoneda01_F G,
    forall (V1_ff1 : { V : obViewing G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) }) V1_ff1_P
      (V2_ff2 : { V : obViewing G & (forall H : obGenerator, 'Generator( H ~> G | V ) -> Yoneda00_F H) }) V2_ff2_P,
    forall (W : obViewing G)
      (vv1 : transpViewing W (projT1 V1_ff1))
      (vv2 : transpViewing W (projT1 V2_ff2)),
      ( forall H, (projT2 V1_ff1) H \o sval vv1 H =1 (projT2 V2_ff2) H \o sval vv2 H ) ->
      ( @exist _ _ V1_ff1 V1_ff1_P  )
      = ( @exist _ _ V2_ff2 V2_ff2_P : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G ).

Lemma Yoneda00_ViewedFunctor_quotient' : forall Yoneda00_F Yoneda01_F G,
    forall (V1_ff1 V2_ff2 : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G),
    forall (W : obViewing G)
      (vv1 : transpViewing W (projT1 (sval V1_ff1)))
      (vv2 : transpViewing W (projT1 (sval V2_ff2))),
      ( forall H, (projT2 (sval V1_ff1)) H \o sval vv1 H =1 (projT2 (sval V2_ff2)) H \o sval vv2 H ) ->
      V1_ff1 = V2_ff2 .
Proof.
  destruct V1_ff1; destruct V2_ff2. exact: Yoneda00_ViewedFunctor_quotient.
Qed.

Definition transpViewingCocone  Yoneda00_F Yoneda01_F G
      (V1_ff1 V2_ff2 : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G) :=
  { vv2 : transpViewing (projT1 (sval V1_ff1)) (projT1 (sval V2_ff2)) |
       ( forall H, (projT2 (sval V1_ff1)) H =1 (projT2 (sval V2_ff2)) H \o sval vv2 H ) }.

Lemma Yoneda00_ViewedFunctor_quotient_rev : forall Yoneda00_F Yoneda01_F G,
     forall (V1_ff1 V2_ff2 : @Yoneda00_ViewedFunctor Yoneda00_F Yoneda01_F G),
       V1_ff1 = V2_ff2 -> transpViewingCocone V1_ff1 V2_ff2.
Proof.
  intros. subst. exists (identity_transpViewing _).
  abstract (intros; move; reflexivity).
Qed.

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
    + exists (intersecViewing (projT1 (sval V_ff)) g).
      exact: (fun H => projT2 (sval V_ff) H \o
                       (sval (Yoneda10_intersecViewing_toViewing (projT1 (sval V_ff)) g) H)).
    + abstract (simpl; split;
                first (by exact: (intersecViewingP g (proj1 (proj2_sig V_ff))));
                split; first (by abstract (move; simpl; intros;
                                         rewrite (proj1 (proj2 (proj2_sig V_ff))); reflexivity));
              abstract (intros H v v' Heq; apply: (proj2 (proj2 (proj2_sig V_ff)));
                        rewrite (proj2_sig v) (proj2_sig v');
                        congr ( _ :>Generator ); exact: Heq)).
  - abstract (split; simpl;
       [ intros G G' g G'' g' V_ff; rewrite /Yoneda01_action /= ;
         unshelve eapply Yoneda00_ViewedFunctor_quotient
         with (W:=(intersecViewing (intersecViewing (projT1 (sval V_ff)) g) g'));
         [ exact: identity_transpViewing
         | exact: intersecViewing_polyGenerator
         | abstract (intros; move; reflexivity) ]
       | intros G V_ff; destruct V_ff as [ sval_V_ff ? ]; rewrite /Yoneda01_action /= ;
         unshelve eapply Yoneda00_ViewedFunctor_quotient
         with (W:=(projT1 sval_V_ff));
         [ exact: identity_transpViewing
         | exact: intersecViewing_unitGenerator
         | abstract (intros; move; reflexivity) ] ] ).
Defined.

Definition identity_transpViewing_Yoneda01_ViewedFunctor : forall (Yoneda00_F : obGenerator -> Type)
    (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                    Yoneda01_functor Yoneda01 }) (G G' : obGenerator) (g : 'Generator( G' ~> G ))
    (ff : Yoneda00_ViewedFunctor Yoneda01_F G),
    { transp : transpViewing (intersecViewing (projT1 (sval ff)) g)
                        (projT1 (sval (g o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_F)] ff)))
    | forall H0, (projT2 (sval ff)) H0 \o sval (Yoneda10_intersecViewing_toViewing (projT1 (sval ff)) g) H0
                 =1 (projT2 (sval (g o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_F)] ff))) H0 \o sval transp H0 }.
Proof.
  intros; exists (identity_transpViewing _ ).
  abstract (intros; move; simpl; intros; reflexivity).
Defined.

Section Senses_viewingTopology.

  Definition Viewing_View : forall (G G' : obGenerator), (Yoneda00_View G) G' -> obViewing G' .
Proof.
  intros G G' g. exact (unitViewing unitGenerator).
Defined.

Definition Viewing_data_View : forall (G G' : obGenerator) (g : Yoneda00_View G G'),
    viewingData ((@Viewing_View G) G' g) .
Proof.
  intros G G' g. exact (unitViewingP unitGenerator).
Qed.

Definition Viewing_transp_View: forall (G : obGenerator), viewingFunctor (Yoneda01_View G) (@Viewing_View G).
Proof.
  intros G. move. intros. exact: real_transpViewing.
Defined.

Section Viewing_ViewedFunctor.

Variables (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
          (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
          (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F f))
          (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F).

Definition Viewing_ViewedFunctor : forall (G' : obGenerator), (Yoneda00_ViewedFunctor Yoneda01_F) G' -> obViewing G' .
Proof.
  intros G' V_ff. exact: (innerViewing (fun H v => (@Viewing_F H (projT2 (sval V_ff) H v)))).
  (*exact: (innerViewing (fun H => (@Viewing_F H) \o (projT2 (sval V_ff) H))).*)
Defined.

Definition Viewing_data_ViewedFunctor : forall (G' : obGenerator) (V_ff : (Yoneda00_ViewedFunctor Yoneda01_F) G'),
    viewingData (Viewing_ViewedFunctor V_ff) .
Proof.
  intros G' V_ff. apply: innerViewingP.
  exact: (proj1 (proj2_sig V_ff)). intros; exact: Viewing_data_F.
Qed.

Definition Viewing_transp_ViewedFunctor: viewingFunctor (Yoneda01_ViewedFunctor Yoneda01_F) Viewing_ViewedFunctor.
Proof.
  move. simpl; intros G G' g V_ff. unshelve eexists.
  - intros H' wv_g' .
    (set H : obGenerator := projT1 (projT1 (sval wv_g').1));
      (set v : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval wv_g').1));
      (set w : 'Generator( _ ~> _ | _ H v ) := projT2 (sval wv_g').1).
    now_show ('Generator( H' ~> _ | Viewing_ViewedFunctor (g o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_F)] V_ff) )) .
    unshelve eexists.
    + simpl. now_show ( {H0 : obGenerator & Yoneda00_intersecViewing (projT1 (sval V_ff)) g H0} ).
      exists H'. unshelve eexists.
      * split. exact: ( ( w :>Generator ) o>Generator v | _ ). exact: ( (sval wv_g').2 ).
      * abstract (simpl; rewrite -[LHS](proj2_sig (@Yoneda10_realize _ _)); exact: (proj2_sig wv_g')).
    + simpl. now_show ('Generator( H' ~> _ | Viewing_F (projT2 (sval V_ff) H' ((w :>Generator) o>Generator v | projT1 (sval V_ff))) )).
      (**MEMO: LOGICAL, NOT REALLY /!\*)
      unshelve eapply (sval (fst (sval (@identity_transpViewing' _ (Viewing_F ((w :>Generator) o>Generator_[sval Yoneda01_F] projT2 (sval V_ff) H v)) _ _ )))).
      abstract (rewrite -(proj1 (proj2 (proj2_sig V_ff))); reflexivity).
      rewrite /Yoneda01_action /= . apply: (sval (Viewing_transp_F _ _)). unshelve eexists.
      split. exact: w. exact: unitGenerator.
      abstract (exact: polyGenerator_unitGenerator).
  - exact: TMP_AXIOM_OUT_OF_MEMORY.
(**COMMENT  - split.
    + move; intros G0 G0' g0' wv_g'. Time cbn zeta beta.
      Time (set H : obGenerator := projT1 (projT1 (sval wv_g').1));
        (set v : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval wv_g').1));
        (set w : 'Generator( _ ~> _ | _ H v ) := projT2 (sval wv_g').1). (* 234s *)
      Time (set wv_g'0 := (g0' o>Generator wv_g' | intersecViewing (Viewing_ViewedFunctor V_ff) g));
        (set H0 : obGenerator := projT1 (projT1 (sval wv_g'0).1));
        (set v0 : 'Generator( H0 ~> _ | _ ) := projT2 (projT1 (sval wv_g'0).1));
        (set w0 : 'Generator( _ ~> _ | _ H v ) := projT2 (sval wv_g'0).1). (* 174s *)
      Time rewrite // [LHS]/Yoneda01_action [LHS]/= . (* 88s *)
      (**MEMO: /!\ DONT FORGET THE EALIER SIMPLIFIED [Yoneda10_intersecViewing_toViewing] /!\ *)
      Time apply: (Yoneda00_innerViewing_quotientLogical' (WP_ := (fun J => (@Viewing_F J) \o ((projT2 (sval V_ff) J) \o (sval (Yoneda10_intersecViewing_toViewing (projT1 (sval V_ff)) g) J)) : 'Generator( J ~> _ | intersecViewing (projT1 (sval V_ff)) g ) -> obViewing J ))). (* 8s *)
      Time rewrite [in LHS](proj1 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 196s *)
      rewrite [in LHS](proj1 (proj2_sig (Viewing_transp_F _ _))).  (* 180s *)
      simpl. (* 2s *) Time rewrite /Yoneda01_action /= . (* 382s *) 
      Time apply: Yoneda00_intersecViewing_quotientLogical. (* 47s *)
      Time simpl.
      Time congr ( _ , _  ). (* 178s *)
      * Time rewrite [in LHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 73s *)
        rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _))).  (* 49s *)
        Time rewrite [in RHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 203s *)
        Time rewrite [in RHS](proj2 (proj2_sig (Viewing_transp_F _ _))).  (* 49s *)
        Time simpl. (* s *)
        Time rewrite -[in LHS]unitGenerator_polyGenerator. (* 1s *)
        Time rewrite [LHS](proj1 (proj2_sig (Yoneda01_Viewing _))).
        Time rewrite -[RHS](proj2 (proj2_sig (Yoneda01_Viewing _))).
        Time rewrite [X in X o>Generator _ | _ = _](proj2_sig (@Yoneda10_realize _ _)).
        reflexivity.
      * Time rewrite [in LHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 73s *)
        Time rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _))).  (* 62s *)
        Time rewrite [in RHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 190s *)
        Time rewrite [in RHS](proj2 (proj2_sig (Viewing_transp_F _ _))).  (* 49s *)
        Time simpl.  Time rewrite -[in LHS]unitGenerator_polyGenerator -[in RHS]polyGenerator_unitGenerator. (* 1s *)
        reflexivity.
    + intros H' wv_g'. Time cbn zeta beta. (* 3s *)
      Time (set H : obGenerator := projT1 (projT1 (sval wv_g').1));
        (set v : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval wv_g').1));
        (set w : 'Generator( _ ~> _ | _ H v ) := projT2 (sval wv_g').1). (* 19s *)
      Time simpl. (* 229s vs 3s *)
      Time rewrite [in LHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* OOs vs 10s *)
      Time rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _))).  (* 10s *)
      Time simpl. Time rewrite -[in LHS]polyGenerator_unitGenerator. reflexivity. *)
Defined.
End Viewing_ViewedFunctor.
End Senses_viewingTopology.
End Senses_obCoMod.
(** # #
#+END_SRC

** Finiteness of the viewing-elements of some viewing-functor

  The grammatical colimiting/sum/sigma/viewing-functor-objects [ViewingFunctor] assume some finiteness properties ( such as finite-compact or finite-dimensional or finite-generated ) onto the viewing-data/topology sense-decodings which they internalize . And these viewing-functor-objects are similar as generators ( representable-functors ) but to be used for functors which are already viewed-functors ( "sheaf" ) .

  To facilitate the COQ automatic-arithmetic during the degradation lemma , here oneself shall assume that the cardinality is fixed-the-same ( here 2 ) for each of the viewing-functor which is grammatically internalized .

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Finiteness.

Parameter isFiniteness_ : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
  (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
  (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
  (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F), Prop.

Parameter (G1 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
       (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),  obGenerator) .
Parameter (f1 : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                  (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
   (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),
                   Yoneda00_F (G1 isFiniteness_F)).
Parameter (H1 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
  (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
  (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),  obGenerator).
Parameter (v1 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),                 
              'Generator( (H1 isFiniteness_F) ~> (G1 isFiniteness_F) | (@Viewing_F (G1 isFiniteness_F ) (f1 isFiniteness_F )) )).

Parameter (G2 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
       (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),  obGenerator) .
Parameter (f2 : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                  (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
   (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),
                   Yoneda00_F (G2 isFiniteness_F)).
Parameter (H2 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
  (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
  (isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),  obGenerator).
Parameter (v2 : forall(Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F),                 
              'Generator( (H2 isFiniteness_F) ~> (G2 isFiniteness_F) | (@Viewing_F (G2 isFiniteness_F ) (f2 isFiniteness_F )) )).

Section Section1.
Variables (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
          (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F f)) (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(isFiniteness_F : isFiniteness_ Viewing_data_F Viewing_transp_F) .

Inductive is_viewingFunctorElement12 : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (@Viewing_F G f) )), Type :=
| Is_viewingFunctorElement12_viewingFunctorElement1 : is_viewingFunctorElement12 (v1 isFiniteness_F)
| Is_viewingFunctorElement12_viewingFunctorElement2 : is_viewingFunctorElement12 (v2 isFiniteness_F) .

Axiom is_viewingFunctorElement12_allP :  forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (@Viewing_F G f) )), is_viewingFunctorElement12 v.
End Section1. 
End Finiteness.
(** # #
#+END_SRC

** Grammar of the objects, which carry the sense-decodings

  As common , the [View] constructor is the (covariant) Yoneda-embedding ( therefore [View G] is some contravariant metafunctor ) .

  Memo that the sense-decoding of some [ViewingFunctor] viewing-functor is the same sense-decoding as this same functor without the viewings . But grammatically , only the viewing-elements of the viewing-functor are touchable (via the morphism constructor [PolyElement]) .

  Lastly , memo that the viewings-data or polymorph-viewings-transport logical-conditions are not carried by the grammatical objects and will be carried only by the [PolyTransf] reflector/copairing grammatical morphism .

#+BEGIN_SRC coq :exports both :results silent # # **)
Inductive obCoMod : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                      (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                      (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                      (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F),  Type :=

| View : forall G : obGenerator, @obCoMod (Yoneda00_View G) (Yoneda01_View G) (@Viewing_View G) (@Viewing_data_View G) (@Viewing_transp_View G)

| ViewingFunctor : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                     (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                     (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                     (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F),
    forall (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F

| ViewedFunctor : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                    (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                    (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                    (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F),
    forall (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
      @obCoMod (Yoneda00_ViewedFunctor Yoneda01_F) (Yoneda01_ViewedFunctor Yoneda01_F)
               (Viewing_ViewedFunctor Viewing_F)
               (Viewing_data_ViewedFunctor Viewing_data_F)
               (Viewing_transp_ViewedFunctor Viewing_transp_F)
               (* old bad (Viewing_transp_ViewedFunctor Viewing_F) did not use Viewing_transp_F *) .
(** # #
#+END_SRC

* Grammatical presentation of morphisms

** Sense-decodings of the morphisms

  The sense-decoding of any morphism is some metatransformation [Yoneda10_data] together with some continuity-property [viewingContinuous] .

  Memo that these sense-decodings will be held in the constructor [Reflector] to express the cocone logical-condition on any input cocone data as held by the output reflector-constructor ( "universality-morphism" , copairing ) .

  As common , the [View1] constructor is the (covariant) Yoneda-embedding ( therefore [View G] is some contravariant metafunctor ) .

  Now the « viewed-functor » construction is functorial via the constructor [ViewedFunctor1] ( « viewed-transformation » ). And the sense-decoding of the constructor [ViewedFunctor1] takes some transformation parameter and then inputs some cocone over some viewing , and finally ouputs some other cocone over the same viewing but whose sections have been post-composed/transformed by this transformation parameter . Memo that the formulation of this [ViewedFunctor1] constructor is (functoriality) polymorphism .

  For modified-colimits , the [PolyElement] (injection) morphism cancels ( via the conversion [PolyTransf_PolyElement] ) the [PolyTransf] (copairing) morphism , but not tightly/precisely . This cancellation is relaxed by the constructor [UnitViewedFunctor] . Now the sense-decoding of the constructor [UnitViewedFunctor] takes some transformation parameter and then inputs some element of some functor , and finally outputs the polyelement form of [this element which has been pre-composed/transformed by this transformation parameter] . Memo that the formulation of this [UnitViewedFunctor] constructor is (naturality) polymorphism .

  And the constructor [PolyElement] are the sections/injections/coprojection of the modified-colimit [ViewingFunctor] viewing-functor ; therefore only the viewing-elements (action of some viewing-arrow onto some element) of this viewing-functor are accessible via this [PolyElement] constructor . Memo the dependence of [PolyElement] not in the pair (element , viewing-arrow) but only in its action (sense) , both in the sense-decoding [Yoneda10_PolyElement] and in the conversion [PolyElement_cong] (this is necessary for sense-completeness ... ) .

  And the constructor [PolyTransf] is the reflector/copairing of the modified-colimit [ViewingFunctor] viewing-functor . Its sense-decoding takes some « real polymorph-cocones » into one target functor over the viewings at each element of some viewing-functor and then inputs some element of this functor , and finally outputs the cocone at this element ; such output cocone is indeed some element of the viewed-functor of the target functor . Memo that any real polymorph-cocones

#+BEGIN_EXAMPLE
ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
      forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
      forall (H' : obGenerator), Yoneda00_View H H' -> Yoneda00_E H'
ALT:  e_ f v := ee_ f v 1
#+END_EXAMPLE

is such that it is cocones ( [Yoneda10_ee_natural] ) :
#+BEGIN_EXAMPLE
ee_ f (g o> v) h  =  ee_ f v (h o> g)
ALT:  e_ f (g o> v)  =  g o> (e_ f v)
#+END_EXAMPLE

and it is polymorph-cocones ( [Yoneda10_ee_morphism] ) :
#+BEGIN_EXAMPLE
ee_ (g o> f) v h  =  ee_ f (v o> g) h
ALT:  e_ (g o> f) v  =  e_ f (v o> g)
#+END_EXAMPLE

and it is real polymorph-cocones ( [Yoneda10_ee_real] ) :
#+BEGIN_EXAMPLE
ee_ f v h  =  ee_ f (v :>Generator) h
ALT:  e_ f v  =  e_ f (v :>Generator)
#+END_EXAMPLE

  Finally the constructor [PolyTransf_default] corresponds to the constructor [PolyTransf] when the target functor is already some viewed-functor . The sense-decoding of this constructor [PolyTransf_default] is less-immediate to present , and therefore will be presented in the next section [Senses_defaultColimit] .

#+BEGIN_SRC coq :exports both :results silent # # **)
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
  intros. exists (fun A => (sval Yoneda10_ff') A \o (sval Yoneda10_ff_) A ).
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
(G H : obGenerator) (g : 'Generator( H ~> G )) :
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
  - intros G V_ff . unshelve eexists.
    + exists (projT1 (sval V_ff)). exact: (fun H => (sval Yoneda10_ee H) \o (projT2 (sval V_ff) H)).
    + abstract(simpl; split; first (by exact: (proj1 (proj2_sig V_ff)));
               split; first (by move; intros; rewrite (proj2_sig Yoneda10_ee);
                             rewrite (proj1 (proj2 (proj2_sig V_ff))); reflexivity);
               last (by intros H v v' Heq; congr (sval Yoneda10_ee H);
                     apply: (proj2 (proj2 (proj2_sig V_ff))); exact: Heq)).
  - abstract ( move; simpl; intros G G' g V_ff;
              unshelve eapply Yoneda00_ViewedFunctor_quotient
              with (W:= (intersecViewing (projT1 (sval V_ff)) g));
              [ exact: identity_transpViewing
              | exact: identity_transpViewing
              | abstract (intros; move; reflexivity) ] ). 
Defined.

Definition element_to_polyelement : forall Yoneda00_F Yoneda01_F G,
    Yoneda00_F G ->
         { Yoneda10 : ( forall G' : obGenerator, Yoneda00_View G G' -> Yoneda00_F G' ) |
           Yoneda10_natural (Yoneda01_View G) Yoneda01_F Yoneda10 } .
Proof.
  intros ? ? G f. unshelve eexists. 
  apply: (fun G' g => g o>Generator_[sval Yoneda01_F] f) . 
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
  rewrite /Yoneda01_action /= -unitGenerator_polyGenerator. reflexivity.
Qed.

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
    + exists ( unitViewing (@unitGenerator G)).
      refine (sval (element_to_polyelement (Yoneda01_F) (sval Yoneda10_ff _ e))).
      (** intros H g. exact: (g o>Generator_[sval Yoneda01_F] (sval Yoneda10_ff _ e)). **)
    + abstract (simpl; split; first (by exact: unitViewingP);
                split; first (by move; intros; exact: (proj1 (proj2_sig Yoneda01_F)));
                last (by intros H v v' (* Heq*);
                      do 2 rewrite -unitGenerator_polyGenerator; move -> (* Heq *); reflexivity)).
  - abstract (move; simpl; intros G G' g V_ff;
              unshelve eapply Yoneda00_ViewedFunctor_quotient
              with (W:= (unitViewing unitGenerator));
              [ exact: intersecViewing_unitViewing
              | exact: identity_transpViewing
              | abstract (intros; move; simpl; intros;
                          rewrite -(proj2_sig Yoneda10_ff)
                          -(proj1 (proj2_sig Yoneda01_F)); reflexivity) ]).
Defined.
  

Lemma Yoneda10_PolyElement Yoneda00_F Yoneda01_F
      (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
      (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
      (v : 'Generator( H ~> G | (V_ G f) )) :
  {Yoneda10 : forall G : obGenerator, Yoneda00_View H G -> Yoneda00_F G |
   Yoneda10_natural (Yoneda01_View H) Yoneda01_F Yoneda10} .
Proof.
  exact: (element_to_polyelement _ (( v :>Generator ) o>Generator_[sval Yoneda01_F] f )).
Defined.

(*MEMO: dependence of this lemma in that the viewing is indeed viewing-data [V_data : viewingData (V_ G f)] .
MEMO: uniqueness is by computationally *)
Lemma Yoneda10_PolyTransf :
  forall Yoneda00_F Yoneda01_F (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
    (V_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (V_ G f))
    (V_transp : viewingFunctor Yoneda01_F V_)
    Yoneda00_E Yoneda01_E
    (Yoneda10_ee_ :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
         'Generator( H ~> G | (V_ G f) ) ->
         {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
          Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
    (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Viewing (V_ G f)) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v)))
    (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v')))
    (Yoneda10_ee_real :
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
    {Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
     Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10}.
Proof.
  intros. unshelve eexists.
  - intros G f. unshelve eexists.
    + eexists. (* exists (@V_ G f). *)
      exact: (fun H v => (polyelement_to_element (Yoneda10_ee_ G f H v))).
    + abstract (simpl; split;
                first (by exact: (V_data G f));
                split; first (by move; intros;
                              exact: ((Yoneda10_ee_natural G f )));
                last by intros H v v' Heq; apply: Yoneda10_ee_real; exact: Heq).
  - abstract (move; simpl; intros G G' g f; rewrite [LHS]/Yoneda01_action [LHS]/= ;
      unshelve eapply Yoneda00_ViewedFunctor_quotient
      with (W:= (intersecViewing (V_ G f) g)); 
      [ exact: identity_transpViewing
      | exact: V_transp
      | intros H; move; simpl; intros v';
        exact: Yoneda10_ee_morphism ] ).
Defined.

(** # #
#+END_SRC

** Modified colimiting is default (common) colimiting when into viewed-functors

  Finally the constructor [PolyTransf_default] corresponds to the constructor [PolyTransf] when the target functor is already some viewed-functor . Modified colimiting is default (common) colimiting when into viewed-metafunctors . It is less-immediate to find the sense-decodings which validate this grammatical construction [PolyTransf_default] and grammatical conversion [PolyTransf_default_PolyElement] . 

  In short : given some « nested real polymorph-cocones » into some viewed-functor (whose elements are therefore inner cocones) :

#+BEGIN_EXAMPLE
e_ : forall (G : obGenerator) (f : Yoneda00_F G),
     forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                        (Yoneda00_ViewedFunctor Yoneda01_E) H 
#+END_EXAMPLE

it is valid to move from-to :

#+BEGIN_EXAMPLE
(f : F) ; (v : viewing at f) |- (w : viewing indexing the
                                       inner cocone (e_ f v)) -> (e_ f v w : E)
#+END_EXAMPLE

#+BEGIN_EXAMPLE
(f : F) ; ((v : viewing at f) , (w : viewing indexing the
                                       inner cocone (e_ f v))) |- (e_ f v w : E) 
#+END_EXAMPLE

where the later (unnested) real polymorph-cocones [Yoneda10_PolyElement_default] are each over some constructed inner (dependent sum) viewing [viewingDefault_] ( « viewings-for-default-colimiting » ) .

  Memo that here the form of the assumed logical-conditions for such (nested) real polymorph-cocones into some viewed-functor will become :

that it is cocones ( [Yoneda10_e_natural] ) :
#+BEGIN_EXAMPLE
e_ f (g o> v) w = (g o> (e_ f v)) w == e_ f v (w o> g)
#+END_EXAMPLE

and (same) that it is polymorph-cocones ( [Yoneda10_e_morphism] ) :
#+BEGIN_EXAMPLE
e_ (g o> f) v w  =  e_ f (v o> g) w
#+END_EXAMPLE

and that it is real polymorph-cocones ( [Yoneda10_e_real] ) :
#+BEGIN_EXAMPLE
e_ f v w  ==  e_ f v (1 o> (w :>Generator))
  ==  (w :>Generator) o> (e_ f v 1)
  ==  e_ f ((w :>Generator) o> v) 1
  =   e_ f (((w :>Generator) o> v) :>Generator) 1 
  ==   e_ f ((w :>Generator) o> (v :>Generator)) 1 
#+END_EXAMPLE

#+BEGIN_SRC coq :exports both :results silent # # **)
Section Senses_defaultColimit.

(**memo:   ee_ := Yoneda10_ee_ : (forall G f H (v : 'Generator( H ~> G | (V_ G f) )) H' (h : 'Generator( H' ~> H )), Yoneda00_E H')  ;
           e_ := polyelement_to_element ee_  ;
           e__ := Yoneda10_PolyElement_default : (forall G f H' (wv : 'Generator( H' ~> G | (viewingDefault_ (projT1 (sval (e_ f))) )), Yoneda00_E H')  ;
           ee__ := element_to_polyelement e__  **)

Section transp.
Variables (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
         (V_transp : viewingFunctor Yoneda01_F V_).
Variables (Yoneda00_E : obGenerator -> Type) (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }).
Variables (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (@V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ).
Variables (Yoneda10_e_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ f) g )),
          (@Yoneda10_e_ G f H (fst (sval v'))) =
          (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp g f) H v'))).
Variables (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (@V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (@V_ G f) )) =>
                             (@Yoneda10_e_ G f H v))).
Variables (Yoneda10_e_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (@V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (@Yoneda10_e_ G f H v)
               =  (@Yoneda10_e_ G f H v')).

Lemma Yoneda10_e_morphism_transp :
    forall G G' g f H v',  transpViewingCocone
  (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp g f) H v'))
  (@Yoneda10_e_ G f H (fst (sval v'))) .
Proof.
  abstract (intros; apply: Yoneda00_ViewedFunctor_quotient_rev;
            symmetry; exact: Yoneda10_e_morphism).
Qed.

Lemma Yoneda10_e_real_transp :
  forall G f H v v', ((v :>Generator) = (v' :>Generator)) ->
                     transpViewingCocone (@Yoneda10_e_ G f H v) (@Yoneda10_e_ G f H v').
Proof.
   abstract (intros until G; intros f H v v' Heq; apply: Yoneda00_ViewedFunctor_quotient_rev;
             exact: (@Yoneda10_e_real G f H v v' Heq)).
Qed.

Lemma Yoneda10_e_natural_transp :
    forall G (f : Yoneda00_F G) H H' (h : 'Generator( H' ~> H )) (v : 'Generator( H ~> G | (@V_ G f) )),
      transpViewingCocone (h o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_E)] (@Yoneda10_e_ G f _ v)) (@Yoneda10_e_ G f H' (h o>Generator v | (@V_ G f))).
Proof.
  abstract (intros; apply: Yoneda00_ViewedFunctor_quotient_rev;
            exact: Yoneda10_e_natural).
Qed.

Lemma Yoneda10_e_natural_transp_rev :
    forall G (f : Yoneda00_F G) H H' (h : 'Generator( H' ~> H )) (v : 'Generator( H ~> G | (@V_ G f) )),
      transpViewingCocone (@Yoneda10_e_ G f H' (h o>Generator v | (@V_ G f)))
          (h o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_E)] (@Yoneda10_e_ G f _ v)) .
Proof.
  abstract (intros; apply: Yoneda00_ViewedFunctor_quotient_rev; apply: Logic.eq_sym;
            exact: Yoneda10_e_natural).
Qed.

End transp.

Lemma viewingDefault_ :
  forall Yoneda00_F
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G),
    forall projT1_sval_Yoneda10_e_ :
          ( forall G f H, 'Generator( H ~> G | (V_ G f) ) -> obViewing H ),
    forall G : obGenerator, Yoneda00_F G -> obViewing G .
Proof.
  intros until G. intros f.
  exact: (@innerViewing _ (V_ G f) (projT1_sval_Yoneda10_e_ G f)).
Defined.

Lemma viewingDefault_data :
  forall Yoneda00_F
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
         (V_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (V_ G f)),
    forall projT1_sval_Yoneda10_e_ :
          ( forall G f H, 'Generator( H ~> G | (V_ G f) ) -> obViewing H ),
    forall proj1_proj2Sig_Yoneda10_e_ :
    forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
               viewingData (projT1_sval_Yoneda10_e_ G f H v),

    forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault_ projT1_sval_Yoneda10_e_ f) .
Proof.
  intros until G. intros f.
  exact: (@innerViewingP _ _ _ (V_data G f) (proj1_proj2Sig_Yoneda10_e_ G f) ) .
Qed.

(*MEMO: TODO: ref also below
[Lemma viewingContinuous_PolyTransf_default : viewingContinuous viewingDefault'_ (Viewing_ViewedFunctor Viewing_E) (Yoneda10_PolyTransf_default Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real)]  *)
Lemma viewingDefault_transp :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
         (V_transp : viewingFunctor Yoneda01_F V_),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
          (@Yoneda10_e_ G f H (fst (sval v'))) =
          (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v')))
      (Yoneda10_e_natural :
         forall (G : obGenerator) (f : Yoneda00_F G),
           Yoneda10_natural (Yoneda01_Viewing (@V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                            (fun (H : obGenerator) (v : 'Generator( H ~> G | (@V_ G f) )) =>
                               (@Yoneda10_e_ G f H v))),
    viewingFunctor Yoneda01_F (viewingDefault_ projT1_sval_Yoneda10_e_) .
Proof.
  intros; move; intros G G' g f. unshelve eexists.
  - intros H' v'w'_g'.
    (set g' := ((sval v'w'_g').2));
      (set H : obGenerator := projT1 (projT1 (sval v'w'_g').1));
      (set v' : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval v'w'_g').1));
      (set w' : 'Generator( _ ~> _ | _ H v' ) := projT2 (sval v'w'_g').1).
    simpl. unshelve eexists.
    + exists H'. apply: (sval (V_transp _ _ _ _)). unshelve eexists.
      * split. exact: ( (w' :>Generator) o>Generator v' | _ ). exact: g'. 
      * abstract (simpl; rewrite -[LHS](proj2_sig (@Yoneda10_realize _ _)); exact: (proj2_sig v'w'_g')).
    + simpl. unshelve eapply (sval (fst (sval (@identity_transpViewing' _ (projT1_sval_Yoneda10_e_ G f H' ((w' :>Generator) o>Generator v' | V_ G f)) _ _ )))).
      abstract (congr (projT1 (sval _ )); rewrite -[RHS]Yoneda10_e_morphism; reflexivity).
      unshelve eapply (sval (fst (sval (@identity_transpViewing' _ (projT1 (sval ((w' :>Generator) o>Generator_[sval (Yoneda01_ViewedFunctor Yoneda01_E)] Yoneda10_e_ G f H v'))) _ _ )))).
      abstract (congr (projT1 (sval _ )); exact: Yoneda10_e_natural).
      simpl. unshelve eexists.
      * split. exact: ( w' ). exact: ( unitGenerator ).
      * abstract (simpl; exact: polyGenerator_unitGenerator).
  - Time Optimize Heap. exfalso; clear; abstract (exact: TMP_AXIOM_OUT_OF_MEMORY). 

(**  - split.
    + move. intros H' H'' h v'w'_g'. cbn beta zeta.
      Time (set g' := ((sval v'w'_g').2));
        (set H : obGenerator := projT1 (projT1 (sval v'w'_g').1));
        (set v' : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval v'w'_g').1));
        (set w' : 'Generator( _ ~> _ | _ H v' ) := projT2 (sval v'w'_g').1). (* 312s *)
      Time (set v'w'_g'0 := (h o>Generator v'w'_g' | intersecViewing (viewingDefault_ projT1_sval_Yoneda10_e_ f) g));
        (set g'0 := ((sval v'w'_g'0).2));
        (set H0 : obGenerator := projT1 (projT1 (sval v'w'_g'0).1));
        (set v'0 : 'Generator( H0 ~> _ | _ ) := projT2 (projT1 (sval v'w'_g'0).1));
        (set w'0 : 'Generator( _ ~> _ | _ H0 v'0 ) := projT2 (sval v'w'_g'0).1). (* 350s *)
      Time rewrite [LHS]/Yoneda01_action [LHS]/= . (* 84s *)
      apply: (Yoneda00_innerViewing_quotientLogical' (WP_ := projT1_sval_Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f))).
      Time Optimize Heap.
      Time rewrite [LHS](proj1 (proj2_sig (V_transp _ _ _ _))).  (* 262s *)
      Time rewrite [RHS](proj1 (proj2_sig (V_transp _ _ _ _))).  (* 256s *)
      Time congr (sval (V_transp _ _ _ _) _ ). (* 73s *)
      Time rewrite [in RHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 319s *)
      Time set RHS_identity_transpViewing' := ((identity_transpViewing' _) in RHS). (* 45s *)
      Time rewrite [in RHS](proj2 (proj2_sig (fst (sval RHS_identity_transpViewing')))). (* s *)
      Time rewrite -[ X in ( X o>Generator _ | _ ) = _ ](proj2_sig (@Yoneda10_realize _ _)). (* 177s *)
      Time rewrite [in LHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* 227s s *)
      Time set LHS_identity_transpViewing' := ((identity_transpViewing' _) in LHS). (* 45s *)
      Time rewrite [in LHS](proj2 (proj2_sig (fst (sval LHS_identity_transpViewing')))). (* 12s *)
      clear. Time rewrite [in LHS]/Yoneda01_action [LHS]/= . (* 6s *)
      Time apply: Yoneda00_intersecViewing_quotientLogical. (* 1s *) Time simpl. (* 1s *)
      Time congr ( _ , _  ).  (* 1s *)
      Time rewrite [LHS](proj1 (proj2_sig (Yoneda01_Viewing _))).
      Time rewrite -[RHS](proj2 (proj2_sig (Yoneda01_Viewing _))).
      Time rewrite [X in X o>Generator _ | _ = _](proj2_sig (@Yoneda10_realize _ _)).
      rewrite -[in LHS]unitGenerator_polyGenerator.
      { destruct v'w'_g' as [ ]. reflexivity. }
      Time rewrite [in RHS]/Yoneda01_action [RHS]/= . (* 6s *)
      rewrite -[in LHS]unitGenerator_polyGenerator -[in RHS]polyGenerator_unitGenerator. reflexivity.
    + intros H' v'w'_g'. cbn beta zeta.
      Time (set g' := ((sval v'w'_g').2));
        (set H : obGenerator := projT1 (projT1 (sval v'w'_g').1));
        (set v' : 'Generator( H ~> _ | _ ) := projT2 (projT1 (sval v'w'_g').1));
        (set w' : 'Generator( _ ~> _ | _ H v' ) := projT2 (sval v'w'_g').1). (* 141s *) 
      Time simpl. (* 229s vs 3s *)
      Time rewrite [in LHS](proj2 (proj2_sig (V_transp _ _ _ _))).  (* 73s *)
      Time rewrite [in LHS](proj2 (proj2_sig (fst (sval (identity_transpViewing' _))))). (* s *)
      Time set LHS_identity_transpViewing' := ((identity_transpViewing' _) in LHS). (* s *)
      Time rewrite [in LHS](proj2 (proj2_sig (fst (sval LHS_identity_transpViewing')))). (* 200s *)
      Time simpl. Time rewrite -[in LHS]polyGenerator_unitGenerator. reflexivity. **)
Time Defined. (* 112s .... TOTAL TIME 66s + 25s + 38s *)
(**TODO: REVIEW LACK SUCH ?  Lemma viewingDefault_transp_rewrite :  **)

(**memo: e__ := Yoneda10_PolyElement_default ;
         ee__ := element_to_polyelement e__ **)
Lemma Yoneda10_PolyElement_default :
  forall Yoneda00_F
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    ( forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
             (wv : 'Generator( H' ~> G | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )), Yoneda00_E H' ) .
Proof.
  intros; refine ( projT2 (sval (Yoneda10_e_
                                   G f (projT1 (projT1 wv)) (projT2 (projT1 wv)))) H'  (projT2 wv) ).
Defined.

(**memo:
e_ f (g o> v) w  =[outer natural]  (g o> (e_ f v)) w
  =  e_ f v (w o> g) 

form with full polyelement ee_ :
ee_ f (h' o> v) h w  =  (h o> (ee_ f (h' o> v) 1)) w
  =[outer natural]  (h o> (h' o> (ee_ f v 1))) w
( =  ee_ f v (h o> h') w  ;  =  (ee_ f v h') (w o> h)  )
  =  (ee_ f v 1) (w o> (h o> h'))  **)
Lemma Yoneda10_PolyElement_default_outerNatural :
  forall Yoneda00_F
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    forall (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             (Yoneda10_e_ G f H v))),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
           (v : 'Generator( H ~> _ | V_ G f ))
           (H0 : obGenerator) (h : 'Generator( H0 ~> H ))
           H' (w : 'Generator( H' ~> _ | projT1_sval_Yoneda10_e_ G f H0 (h o>Generator v | V_ G f) )),
      { w0 : 'Generator( H' ~> H0 | intersecViewing (projT1_sval_Yoneda10_e_ G f H v) h ) &
             (w0 :>Generator = w :>Generator) /\
             projT2 (sval (Yoneda10_e_ G f H0 (h o>Generator v | V_ G f))) H' w =
             projT2 (sval (Yoneda10_e_ G f H v)) H' (fst (sval w0))}.
Proof.
  intros. exists (sval (sval (Yoneda10_e_natural_transp_rev Yoneda10_e_natural h v)) H' w).
  abstract (split; [rewrite (proj2 (proj2_sig (sval (Yoneda10_e_natural_transp_rev _ _ _)))); reflexivity
                   | rewrite [in LHS](proj2_sig (Yoneda10_e_natural_transp_rev Yoneda10_e_natural h v)); reflexivity ]).
Defined.

(**memo:
e__ f wv  =  e_ f v w
  =[w factorize along w as 1]  (w o> (e_ f v)) 1 
  =[outer naturality]  e_ f (w o> v) 1  
  =[real]  e_ f (w0 o> v0) 1  =  ...  =  e__ f w0v0 

alternative using lemma Yoneda10_PolyElement_default_outerNatural :
e_ f v (1 o> w)  =[lemma]  e_ f (w o> v) 1
  =[real]  e_ f (w0 o> v0) 1 
  =[lemma] e_ f v0 (1 o> w0)    **)
Lemma Yoneda10_PolyElement_default_modulo :
  forall Yoneda00_F
         (V_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             (Yoneda10_e_ G f H v))),
    forall (Yoneda10_e_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_e_ G f H v)
               =  (Yoneda10_e_ G f H v')),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
             (v : 'Generator( H ~> _ | V_ G f )) H'
             (w : 'Generator( H' ~> _ | projT1_sval_Yoneda10_e_ G f H v )),
    forall (H0 : obGenerator)
             (v0 : 'Generator( H0 ~> _ | V_ G f )) 
             (w0 : 'Generator( H' ~> _ | projT1_sval_Yoneda10_e_ G f H0 v0 )),
      ( ((w :>Generator) o>Generator v | (V_ G f) ) :>Generator
        = ((w0 :>Generator) o>Generator v0 | (V_ G f) ) :>Generator ) ->
      ( projT2 (sval (Yoneda10_e_ G f H v)) H' w )
      = ( projT2 (sval (Yoneda10_e_ G f H0 v0)) H' w0 ) .        
Proof.
  intros until w0. intros Heq_real.
  rewrite [w in LHS](proj2_sig (intersecViewing_real_unitGenerator w)).
  rewrite [LHS](proj2_sig (identity_transpViewing_Yoneda01_ViewedFunctor (w :>Generator) (Yoneda10_e_ G f H v))).
  rewrite [w0 in RHS](proj2_sig (intersecViewing_real_unitGenerator w0)).
  rewrite [RHS](proj2_sig (identity_transpViewing_Yoneda01_ViewedFunctor (w0 :>Generator) (Yoneda10_e_ G f H0 v0))).
  rewrite [LHS](proj2_sig (Yoneda10_e_natural_transp Yoneda10_e_natural (w :>Generator) v)).
  rewrite [RHS](proj2_sig (Yoneda10_e_natural_transp Yoneda10_e_natural (w0 :>Generator) v0)).
  set w_v := ( ((w :>Generator) o>Generator v | (V_ G f) ) in LHS).
  set w0_v0 := (((w0 :>Generator) o>Generator v0 | (V_ G f) ) in RHS).
  rewrite [LHS](proj2_sig (Yoneda10_e_real_transp Yoneda10_e_real Heq_real)).
  apply: (proj2 (proj2 (proj2_sig (Yoneda10_e_ G f H' w0_v0)))).
  rewrite [LHS](proj2 (proj2_sig (sval (Yoneda10_e_real_transp Yoneda10_e_real Heq_real)))).
  rewrite [LHS](proj2 (proj2_sig (sval (Yoneda10_e_natural_transp Yoneda10_e_natural (w :>Generator) v)))).
  rewrite [RHS](proj2 (proj2_sig (sval (Yoneda10_e_natural_transp Yoneda10_e_natural (w0 :>Generator) v0)))).
  simpl. (*  unitGenerator = unitGenerator *) reflexivity.
Qed.

(**memo: uniqueness is by computationally *)
Lemma Yoneda10_PolyElement_default_unique :
  forall Yoneda00_F
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),

  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall Yoneda10_PolyElement_default' : ( forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
             (wv : 'Generator( H' ~> G | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )), Yoneda00_E H' ),
    (forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
           (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) ))
           (w : 'Generator( H' ~> H | projT1_sval_Yoneda10_e_ G f H v )),
      Yoneda10_PolyElement_default' G f H' (existT _ (existT _ H v) w) = ( projT2 (sval (Yoneda10_e_ G f H v)) H' w ) )->
 forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
        (wv : 'Generator( H' ~> G | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )),      
   Yoneda10_PolyElement_default' G f H' wv = Yoneda10_PolyElement_default wv .
Proof.
  intros until Yoneda10_PolyElement_default'; intros Heq; intros; destruct wv as [ [H v] w]; rewrite Heq; reflexivity.
Qed.

(**memo: Yoneda10_e_morphism (outer v naturality) is not lacked here ;
e__ f (g o> wv)  =  e_ f v (g o> w) 
  =[inner w naturality]  g o> (e_ f v w)  =  g o> (e__ f wv) 
**)
Lemma Yoneda10_PolyElement_default_natural :
  forall Yoneda00_F 
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    
    forall (G : obGenerator) (f : Yoneda00_F G),
      Yoneda10_natural (Yoneda01_Viewing (viewingDefault_ projT1_sval_Yoneda10_e_  f)) Yoneda01_E
                       (fun (H : obGenerator) (wv : 'Generator( H ~> _ | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )) => Yoneda10_PolyElement_default wv ).
Proof.
  intros; move; simpl; intros H' H0 h wv.
  rewrite [LHS](proj1 (proj2 (proj2_sig ((Yoneda10_e_ G f _ _ ))))).
  reflexivity.
Qed.

(**memo: (todo: reverse equalities)
e__ (g o> f) wv  =  e_ (g o> f) v w
  =[morphism]  e_ f (v o> g) w  =  e__ f (w o> (v o> g))
  =  e__ f (wv o> g) **)
Lemma Yoneda10_PolyElement_default_morphism :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                                    Yoneda01_functor Yoneda01 })
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
         (V_transp : viewingFunctor Yoneda01_F V_),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
          (@Yoneda10_e_ G f H (fst (sval v'))) =
          (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v')))
      (Yoneda10_e_natural :
         forall (G : obGenerator) (f : Yoneda00_F G),
           Yoneda10_natural (Yoneda01_Viewing (@V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                            (fun (H : obGenerator) (v : 'Generator( H ~> G | (@V_ G f) )) =>
                               (@Yoneda10_e_ G f H v))),
  forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G) 
         (H' : obGenerator) (wv : 'Generator( H' ~> _ | intersecViewing (viewingDefault_ projT1_sval_Yoneda10_e_ f) g )),
    Yoneda10_PolyElement_default (sval wv).1 =
    Yoneda10_PolyElement_default (sval (viewingDefault_transp Yoneda10_e_morphism Yoneda10_e_natural g f) H' wv)
                                                                            (*    Yoneda10_PolyElement_default (sval v').1 =
    Yoneda10_PolyElement_default (sval (viewingDefault_transp Yoneda10_e_morphism Yoneda10_e_natural g f) H v')*)
(*                                                                            (Yoneda10_PolyElement_default (sval (viewingDefault_transp Yoneda10_e_morphism Yoneda10_e_natural g f) H' wv))
    = (Yoneda10_PolyElement_default wv)*).
Proof. 
  intros until Yoneda10_e_natural; intros G G' g f H' wv. intros; abstract (exact: TMP_AXIOM_OUT_OF_MEMORY).
(*  symmetry. rewrite / Yoneda10_PolyElement_default.
  Time rewrite -viewingDefault_transp_rewrite. 
  Time simpl. 
  exact ((proj2_sig (Yoneda10_e_morphism_transp Yoneda10_e_morphism wv)) _ _).*)
Qed.

(**memo: this holds lemma [Yoneda10_PolyElement_default_modulo] **)
Lemma Yoneda10_PolyElement_default_real :
  forall Yoneda00_F
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             (Yoneda10_e_ G f H v))),
    forall (Yoneda10_e_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_e_ G f H v)
               =  (Yoneda10_e_ G f H v')),
    forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
           (wv w0v0 : 'Generator( H' ~> _ | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )),
      wv :>Generator = w0v0 :>Generator ->
  (Yoneda10_PolyElement_default wv)
  = (Yoneda10_PolyElement_default w0v0).
Proof.
  intros until w0v0; intros Heq. apply: (Yoneda10_PolyElement_default_modulo Yoneda10_e_natural Yoneda10_e_real).
  set H : obGenerator := projT1 (projT1 wv).
  set v : 'Generator( H ~> _ | (V_ G f) )
    := projT2 (projT1 wv).
  set w : 'Generator( H' ~> _ |  projT1_sval_Yoneda10_e_ G f H v )
    := projT2 wv.
  set H0 : obGenerator := projT1 (projT1 w0v0).
  set v0 : 'Generator( H0 ~> _ | (V_ G f) )
    := projT2 (projT1 w0v0).
  set w0 : 'Generator( H' ~> _ |  projT1_sval_Yoneda10_e_ G f H0 v0 )
    := projT2 w0v0.
  Time do 2 rewrite -(proj2_sig (Yoneda10_realize (V_ G f) )).
  (* TIME WITHOUT set : 27s + 18s QED = ; TIME WITH set : 0.1 *)  
  exact: Heq. 
Qed. 

Lemma Yoneda10_PolyTransf_default0 :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
         (V_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (V_ G f))
         (V_transp : viewingFunctor Yoneda01_F V_),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
          (@Yoneda10_e_ G f H (fst (sval v'))) =
          (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v'))),
    forall (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             (Yoneda10_e_ G f H v))),
    forall (Yoneda10_e_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_e_ G f H v)
               =  (Yoneda10_e_ G f H v')),
     { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
       Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10 } .
Proof.
  intros; set element_to_polyelement_Yoneda10_PolyElement_default :=
    ( fun (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
          (wv : 'Generator( H' ~> G | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )) => element_to_polyelement Yoneda01_E (Yoneda10_PolyElement_default wv) ).

  apply (@ Yoneda10_PolyTransf Yoneda00_F Yoneda01_F (viewingDefault_ projT1_sval_Yoneda10_e_) (viewingDefault_data V_data proj1_proj2Sig_Yoneda10_e_) (viewingDefault_transp Yoneda10_e_morphism Yoneda10_e_natural) Yoneda00_E Yoneda01_E element_to_polyelement_Yoneda10_PolyElement_default).
  (* Yoneda10_PolyElement_default_natural *)
  - abstract (intros; move; intros; do 2 rewrite element_to_polyelement_to_element;
              exact: Yoneda10_PolyElement_default_natural).
  (* Yoneda10_PolyElement_default_morphism *)
  - abstract (intros; do 2 rewrite element_to_polyelement_to_element;
              exact: (Yoneda10_PolyElement_default_morphism Yoneda10_e_morphism Yoneda10_e_natural)).
  (* Yoneda10_PolyElement_default_real *)
  - abstract (intros; do 2 rewrite element_to_polyelement_to_element;
              exact: (Yoneda10_PolyElement_default_real Yoneda10_e_natural Yoneda10_e_real)).
Defined.

Lemma Yoneda10_PolyTransf_default0_unique :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                                    Yoneda01_functor Yoneda01 })
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
         (V_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (V_ G f))
         (V_transp : viewingFunctor Yoneda01_F V_),
  forall Yoneda00_E (Yoneda01_E : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_E G -> Yoneda00_E G' ) |
                 Yoneda01_functor Yoneda01 }),
  forall (Yoneda10_e_ : forall (G : obGenerator) (f : Yoneda00_F G),
        forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
                                  (Yoneda00_ViewedFunctor Yoneda01_E) H ),
    let projT1_sval_Yoneda10_e_ :=
        ( fun G f H v => projT1 (sval (Yoneda10_e_ G f H v))) in
    let proj1_proj2Sig_Yoneda10_e_ :
          (forall G f (H : obGenerator) (v : 'Generator( H ~> _ | (V_ G f) )),
              viewingData (projT1_sval_Yoneda10_e_ G f H v)) :=
        (fun G f H v => proj1 (proj2_sig ( Yoneda10_e_ G f H v ))) in
    forall (Yoneda10_e_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
       forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
          (@Yoneda10_e_ G f H (fst (sval v'))) =
          (@Yoneda10_e_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v'))),
    forall (Yoneda10_e_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                             (Yoneda10_e_ G f H v))),
    forall (Yoneda10_e_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
               (Yoneda10_e_ G f H v)
               =  (Yoneda10_e_ G f H v')),
    forall (Yoneda10_PolyTransf_default0' : { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
                                       Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10 }) ,
    forall (Heq_Viewing : forall (G : obGenerator) (f : Yoneda00_F G),
                           projT1 (sval (sval Yoneda10_PolyTransf_default0' G f))
                           = (viewingDefault_ projT1_sval_Yoneda10_e_ f)), 
      (forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
              (wv : 'Generator( H' ~> G | (viewingDefault_ projT1_sval_Yoneda10_e_ f) )),
          projT2 (sval (sval Yoneda10_PolyTransf_default0' G f)) H'
                 (sval (sval (identity_transpViewing' (Heq_Viewing G f))).2 H' wv)
          = (Yoneda10_PolyElement_default wv)) ->
      forall (G : obGenerator) (f : Yoneda00_F G),
        sval Yoneda10_PolyTransf_default0' G f
        = sval (Yoneda10_PolyTransf_default0 V_data Yoneda10_e_morphism Yoneda10_e_natural Yoneda10_e_real) G f.
Proof.
  intros until Heq_Viewing; intros Heq; intros.
  unshelve eapply Yoneda00_ViewedFunctor_quotient'
  with (W:= (viewingDefault_ projT1_sval_Yoneda10_e_ f)).
  - exact: (sval (identity_transpViewing' (Heq_Viewing G f))).2 .
  - exact: ((sval (identity_transpViewing' Logic.eq_refl)).2) .
  - intros H'; move; intros wv; simpl.
    rewrite -[RHS](proj2 (proj2_sig Yoneda01_E)). exact: Heq.
Qed.

Lemma Yoneda10_PolyTransf_default :
  forall Yoneda00_F (Yoneda01_F : { Yoneda01 : ( forall G G' : obGenerator,
                     'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' ) |
                 Yoneda01_functor Yoneda01 })
         (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
         (V_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (V_ G f))
         (V_transp : viewingFunctor Yoneda01_F V_),
  forall Yoneda00_E Yoneda01_E,
  forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
             forall (H : obGenerator), 'Generator( H ~> G | (V_ G f) ) ->
            {Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> (@Yoneda00_ViewedFunctor Yoneda00_E Yoneda01_E) H' |
              Yoneda10_natural (Yoneda01_View H) (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10} ),
  forall (Yoneda10_ee_natural :
            forall (G : obGenerator) (f : Yoneda00_F G),
              Yoneda10_natural (Yoneda01_Viewing (V_ G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                               (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                                  polyelement_to_element (Yoneda10_ee_ G f H v))),
  forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v'))),
  forall (Yoneda10_ee_real :
            forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (V_ G f) )),
              ((v :>Generator) = (v' :>Generator)) ->
              polyelement_to_element (Yoneda10_ee_ G f H v)
              = polyelement_to_element (Yoneda10_ee_ G f H v') ),
     { Yoneda10 : forall G : obGenerator, Yoneda00_F G -> Yoneda00_ViewedFunctor Yoneda01_E G |
       Yoneda10_natural Yoneda01_F (Yoneda01_ViewedFunctor Yoneda01_E) Yoneda10 } .
Proof.
  intros; apply: (@Yoneda10_PolyTransf_default0 Yoneda00_F Yoneda01_F V_ V_data V_transp Yoneda00_E Yoneda01_E (fun G f H v => polyelement_to_element (Yoneda10_ee_ G f H v)) Yoneda10_ee_morphism Yoneda10_ee_natural Yoneda10_ee_real ).
Defined.
End Senses_defaultColimit.

Section Senses_viewingContinuous.

Definition viewingContinuous (**TODO: rename this to viewingMorphism or continuousMorphism or :   [viewingContinuity] *)
 (Yoneda00_E : obGenerator -> Type) (Yoneda01_E : Yoneda01_data Yoneda00_E) (Viewing_E : forall G : obGenerator, Yoneda00_E G -> obViewing G)
   (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F) (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
 (Yoneda10_ff : Yoneda10_data Yoneda01_E Yoneda01_F)
  := ( forall (G : obGenerator) (e : Yoneda00_E G), transpViewing (Viewing_E G e) (Viewing_F G (sval Yoneda10_ff G e)) ). 

Lemma viewingContinuous_PolyCoMod :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Yoneda00_F' : obGenerator -> Type)
(Yoneda01_F' : Yoneda01_data Yoneda00_F')
(Viewing_F' : forall G : obGenerator, Yoneda00_F' G -> obViewing G)
(Yoneda10_ff' : Yoneda10_data Yoneda01_F' Yoneda01_F)
(viewingContinuous_ff' : viewingContinuous Viewing_F' Viewing_F Yoneda10_ff')
(Yoneda00_F'' : obGenerator -> Type)
(Yoneda01_F'' : Yoneda01_data Yoneda00_F'')
(Viewing_F'' : forall G : obGenerator, Yoneda00_F'' G -> obViewing G)
(Yoneda10_ff_ : Yoneda10_data Yoneda01_F'' Yoneda01_F')
(viewingContinuous_ff_ : viewingContinuous Viewing_F'' Viewing_F' Yoneda10_ff_),
viewingContinuous Viewing_F'' Viewing_F (Yoneda10_PolyCoMod Yoneda10_ff_ Yoneda10_ff').
Proof.
  intros. move. intros G e. unshelve eexists.
  - intros H. refine ( sval (viewingContinuous_ff' _ _) H \o sval (viewingContinuous_ff_ _ _) H).
  - abstract (split; [
      move; intros G0 G0' g0 v;
      rewrite [LHS](proj1 (proj2_sig (viewingContinuous_ff' _ _)));
      rewrite [in LHS](proj1 (proj2_sig (viewingContinuous_ff_ _ _))); reflexivity
    | intros H v; rewrite [LHS](proj2 (proj2_sig (viewingContinuous_ff' _ _)));
      rewrite [LHS](proj2 (proj2_sig (viewingContinuous_ff_ _ _))); reflexivity ]) .
Defined.

Lemma viewingContinuous_UnitCoMod :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G),
viewingContinuous Viewing_F Viewing_F (Yoneda10_UnitCoMod Yoneda01_F).
Proof.
  intros. move. intros G e. unshelve eexists.
  - intros H. refine id.
  - abstract ( split; [
      move; reflexivity
    | reflexivity ] ).
Defined.


Lemma viewingContinuous_View1 :
  forall (G : obGenerator) (H : obGenerator) (g : 'Generator( H ~> G )),
    viewingContinuous (@Viewing_View H) (@Viewing_View G) (Yoneda10_View1 g).
Proof.
  intros. move. intros H' h. simpl. unshelve eexists.
  - simpl. clear h. intros H'' v. exact: v.
  - abstract (split; [
      move; simpl; reflexivity
    | reflexivity ] ).
Defined.

Definition viewingContinuous_ViewedFunctor1 :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Yoneda00_E : obGenerator -> Type)
(Yoneda01_E : Yoneda01_data Yoneda00_E)
(Viewing_E : forall G : obGenerator, Yoneda00_E G -> obViewing G)
(Yoneda10_ff : Yoneda10_data Yoneda01_E Yoneda01_F)
(viewingContinuous_ff : viewingContinuous Viewing_E Viewing_F Yoneda10_ff),
viewingContinuous (Viewing_ViewedFunctor Viewing_E) (Viewing_ViewedFunctor Viewing_F) (Yoneda10_ViewedFunctor1 Yoneda10_ff).
Proof.
  intros. move. intros G ee. unshelve eexists.
  - intros H wv. unshelve eexists.
    + exact: (existT _ (projT1 (projT1 wv)) (projT2 (projT1 wv))).
    + apply: (sval (viewingContinuous_ff _ _)). apply: (projT2 wv).
  - Time abstract(split; [ move; intros H H' h wv;
                      (set H0 : obGenerator := projT1 (projT1 wv));
                      (set v : 'Generator( H0 ~> _ | _ ) := projT2 (projT1 wv));
                      (set w : 'Generator( _ ~> _ |  _ H0 v ) := projT2 wv);
                      simpl; rewrite [in LHS]/Yoneda01_action [LHS]/= ;
                      rewrite [X in {< projT1 (projT1 wv) ; projT2 (projT1 wv) ; X >} = _ ]
                              (proj1 (proj2_sig (viewingContinuous_ff _ _)));
                      reflexivity
                    | intros H wv;
                      (set H0 : obGenerator := projT1 (projT1 wv));
                      (set v : 'Generator( H0 ~> _ | _ ) := projT2 (projT1 wv));
                      (set w : 'Generator( _ ~> _ |  _ H0 v ) := projT2 wv);
                      simpl; rewrite [in LHS](proj2 (proj2_sig (viewingContinuous_ff _ _)));
                      reflexivity ]). (* 53s , 35s *)
Time Defined. (* 4s *)

Definition viewingContinuous_UnitViewedFunctor :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(Yoneda00_E : obGenerator -> Type)
(Yoneda01_E : Yoneda01_data Yoneda00_E)
(Viewing_E : forall G : obGenerator, Yoneda00_E G -> obViewing G)
(Yoneda10_ff : Yoneda10_data Yoneda01_E Yoneda01_F)
(viewingContinuous_ff : viewingContinuous Viewing_E Viewing_F Yoneda10_ff),
viewingContinuous Viewing_E (Viewing_ViewedFunctor Viewing_F) (Yoneda10_UnitViewedFunctor Yoneda10_ff).
Proof.
  intros. move. intros G e. set V_fee := (sval (Yoneda10_UnitViewedFunctor Yoneda10_ff) G e). unshelve eexists.
  - intros H v. unshelve eexists.
    + simpl. exact: (existT _ G (unitGenerator) ).
    + simpl. apply: (sval (Viewing_transp_F _ _  _ _)). unshelve eexists.
      * { split.
          - apply (sval (viewingContinuous_ff _ _)). exact: v.
          - simpl. exact: ( (sval (viewingContinuous_ff G e) H v) :>Generator).
        }
      * abstract (simpl; exact: unitGenerator_polyGenerator).
  - exfalso; clear; abstract (exact: TMP_AXIOM_OUT_OF_MEMORY).
   (*TODO: WAS OK
      abstract (split; [
      move; intros H H' h v;
      simpl; rewrite [in LHS]/Yoneda01_action [LHS]/= ;
      apply: (Yoneda00_innerViewing_quotientLogical' (WP_ := (fun J => (@Viewing_F J) \o ((projT2 (sval V_fee) J)))));
      simpl; rewrite [X in ( X :>Generator ) o>Generator_ _ = _ ](proj1 (proj2_sig (Viewing_transp_F _ _  _ _)));
      simpl;  rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _ _ _)));
      rewrite [in RHS](proj2 (proj2_sig (Viewing_transp_F _ _ _ _)));
      simpl; rewrite -[in RHS](proj1 (proj2_sig (viewingContinuous_ff _ _)));
      rewrite -[in RHS](proj2_sig (Yoneda10_realize _)); reflexivity
    | intros H v; simpl; rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _ _ _))); simpl;
      rewrite [in LHS](proj2 (proj2_sig (viewingContinuous_ff _ _)));
      do 2 rewrite -unitGenerator_polyGenerator; reflexivity ]). *)
Defined.

Definition viewingContinuous_PolyElement :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(G : obGenerator)
(f : Yoneda00_F G)
(H : obGenerator)
(v : 'Generator( H ~> _ | Viewing_F G f )),
viewingContinuous (@Viewing_View H) Viewing_F (Yoneda10_PolyElement Yoneda01_F v) .
Proof.
  intros. move; simpl.  intros H' h. unshelve eexists.
  - apply: (sval (@element_to_polyelement _ (@Yoneda01_Viewing _ _ ) _ _)).
    apply: ( (sval  ( (Viewing_transp_F _ _  _ _)))). unshelve eexists.
    + split.
      * apply: ( (sval  ( (Viewing_transp_F _ _  _ _)))).
        { unshelve eexists.
          - split.
            + exact: ( h o>Generator v | Viewing_F G f ).
            + exact: h.
          - abstract (simpl; rewrite -[LHS](proj2_sig (Yoneda10_realize _)); reflexivity).
        }
      * simpl. exact: (@unitGenerator H').
    + abstract (simpl; rewrite [LHS](proj2 (proj2_sig (Viewing_transp_F _ _  _ _)));
                simpl; exact: polyGenerator_unitGenerator).
  - abstract (split; [
      move; simpl; intros G0 G0' g0 f0;
      rewrite -[RHS](proj1 (proj2_sig (@Yoneda01_Viewing _ _))); simpl; reflexivity
    | simpl; intros H'' w; rewrite -[LHS](proj2_sig (@Yoneda10_realize _ _));
      rewrite [in LHS](proj2 (proj2_sig (Viewing_transp_F _ _  _ _))); simpl; reflexivity ]).
Defined.

Lemma viewingContinuous_PolyTransf :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
(Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(Yoneda00_E : obGenerator -> Type)
(Yoneda01_E : Yoneda01_data Yoneda00_E)
(Viewing_E : forall G : obGenerator, Yoneda00_E G -> obViewing G)
(Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator), 'Generator( H ~> _ | Viewing_F G f ) -> Yoneda10_data (Yoneda01_View H) Yoneda01_E)
(viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> _ | Viewing_F G f )), viewingContinuous (Viewing_View (G:=H)) Viewing_E (Yoneda10_ee_ G f H v))
(Yoneda10_ee_natural :
forall (G : obGenerator) (f : Yoneda00_F G),
Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) Yoneda01_E (fun (H : obGenerator) (v : 'Generator( H ~> _ | Viewing_F G f )) => polyelement_to_element (Yoneda10_ee_ G f H v)))
(Yoneda10_ee_morphism :
   forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
   forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
     polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
     polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v')))
(Yoneda10_ee_real :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> _ | Viewing_F G f )),
(v :>Generator = v' :>Generator -> polyelement_to_element (Yoneda10_ee_ G f H v) = polyelement_to_element (Yoneda10_ee_ G f H v'))),
   viewingContinuous Viewing_F (Viewing_ViewedFunctor Viewing_E) (Yoneda10_PolyTransf Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real).
Proof.
  (* fun f v => (v ,viewingContinuous_ee_ G f H v 1 1) *)
  intros. move. intros G f. unshelve eexists.
  - intros H v. unshelve eexists.
    + exact: (existT _ _ v).
    + simpl. exact: ((sval (@viewingContinuous_ee_ G f H v _ unitGenerator)) _ unitGenerator).
  - abstract (split; [
      move; intros H H' h v; simpl; rewrite [in LHS]/Yoneda01_action [LHS]/= ;
      apply: Yoneda00_innerViewing_quotientLogical; simpl;
      rewrite -[in LHS](proj2_sig (@Yoneda10_realize _ _)); simpl;
      rewrite [in LHS](proj2 (proj2_sig (viewingContinuous_ee_ _ _ _ _ _ _ )));
      rewrite [in RHS](proj2 (proj2_sig (viewingContinuous_ee_ _ _ _ _ _ _ )));
      simpl; rewrite [RHS](proj1 (proj2_sig (@Yoneda01_Viewing _ _)));
      congr ( _ o>Generator _ | _ ) ; rewrite [in LHS]/Yoneda01_action [LHS]/= -?[in LHS]unitGenerator_polyGenerator;
      rewrite -?[in RHS]polyGenerator_unitGenerator; reflexivity 
    | intros H v; simpl; rewrite [in LHS](proj2 (proj2_sig (viewingContinuous_ee_ _ _ _ _ _ _ )));
      simpl; rewrite -?[in LHS]polyGenerator_unitGenerator; reflexivity ]).
Defined.

(* ----- this lemma for next lemma only ----- **)
Definition Yoneda01_innerViewing_rewrite  (G : obGenerator) (V : obViewing G)
           (W_ : forall G' : obGenerator, 'Generator( G' ~> G | V ) -> obViewing G' ) :
forall (H : obGenerator), forall H0 (v : Yoneda00_Viewing V H0) (w : Yoneda00_Viewing (W_  _ v) H),  
  forall (H' : obGenerator) (h : 'Generator( H' ~> H )),
    h o>Generator {< H0 ; v ; w >} | (innerViewing W_) = {< H0 ; v ; h o>Generator w | (W_ _ v) >} .
Proof. reflexivity. Qed.
(*TODO: ref also above
[Lemma viewingDefault_transp : viewingFunctor Yoneda01_F (viewingDefault_ projT1_sval_Yoneda10_e_)]
may use to ease viewingContinuous_PolyTransf_default ? 
also can use above [viewingDefault_transp] [viewingDefault_transp] ? *)
Lemma viewingContinuous_PolyTransf_default :
forall (Yoneda00_F : obGenerator -> Type)
(Yoneda01_F : Yoneda01_data Yoneda00_F)
(Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
(Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
(Yoneda00_E : obGenerator -> Type)
(Yoneda01_E : Yoneda01_data Yoneda00_E)
(Viewing_E : forall G : obGenerator, Yoneda00_E G -> obViewing G)
(Viewing_transp_E : viewingFunctor Yoneda01_E Viewing_E)
(Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator), 'Generator( H ~> _ | Viewing_F G f ) -> Yoneda10_data (Yoneda01_View H) (Yoneda01_ViewedFunctor Yoneda01_E))
(viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> _ | Viewing_F G f )), viewingContinuous (Viewing_View (G:=H)) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v))
(Yoneda10_ee_natural : forall (G : obGenerator) (f : Yoneda00_F G),
Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) (Yoneda01_ViewedFunctor Yoneda01_E) (fun (H : obGenerator) (v : 'Generator( H ~> _ | Viewing_F G f )) => polyelement_to_element (Yoneda10_ee_ G f H v)))
(Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v')))
(Yoneda10_ee_real : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> _ | Viewing_F G f )),
v :>Generator = v' :>Generator -> polyelement_to_element (Yoneda10_ee_ G f H v) = polyelement_to_element (Yoneda10_ee_ G f H v'))
(sval_Yoneda10_ee_ := (fun G f H v => (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))))
(projT1_sval_Yoneda10_ee_ := (fun (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> _ | Viewing_F G f )) => projT1 (sval_Yoneda10_ee_ G f H v)) :
(forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator), 'Generator( H ~> _ | Viewing_F G f ) -> obViewing H))
(viewingDefault'_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(viewingDefault'_poly_transp : forall (G : obGenerator) (f : Yoneda00_F G), transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f) ),
viewingContinuous viewingDefault'_ (Viewing_ViewedFunctor Viewing_E) (Yoneda10_PolyTransf_default Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real) .
Proof.
(* fun f wv => ( ( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) , (w :>Generator) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) *)
  (* intros; (set (projT2_sval_Yoneda10_ee_ := (fun G f H v => projT2 (sval (polyelement_to_element (Yoneda10_ee_ G f H v))))
                 : (forall G f H v H0 , 'Generator( H0 ~> _ | projT1_sval_Yoneda10_ee_ G f H v ) -> Yoneda00_E H0))). *)
  intros (*;  (set (sval_Yoneda10_ee_ := (fun G f H v => (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))))) *).
  move. intros G f. unshelve eexists.
  - intros H' wv0. set wv := (sval (viewingDefault'_poly_transp _ _) _ wv0).
    (set H : obGenerator := projT1 (projT1 wv));
      (set v : 'Generator( H ~> _ | _ ) := projT2 (projT1 wv));
      (set w : 'Generator( _ ~> _ |  _ H v ) := projT2 wv).
    (set _wv := ((sval (viewingContinuous_ee_ G f H v H unitGenerator) H unitGenerator)));
      (set _H : obGenerator := projT1 (projT1 _wv));
      (set _v : 'Generator( _H ~> _ | projT1 (sval_Yoneda10_ee_ G f H v) ) := projT2 (projT1 _wv));
      (set _w : 'Generator( _ ~> _ |  Viewing_E _H (projT2 (sval_Yoneda10_ee_ G f H v) _H _v) ) := projT2 _wv);
      (set w_w : 'Generator( _ ~> _ | _ ) := ( (w :>Generator) o>Generator _w | _ )).
    unshelve eexists.
    (*Goal: {G' : obGenerator & Yoneda00_innerViewing (fun (H0 : obGenerator) (v0 : 'Generator( H0 ~> _ | Viewing_F G f )) => projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H0 v0)))) G'} *)
    + simpl. exists ( _H ) . unshelve eexists.
      * exact: ( existT _ H v ).
      * exact: ( _v ).
    (*Goal: 'Generator( H' ~> _ | Viewing_E _H (unitGenerator o>Generator_ projT2 (sval (polyelement_to_element (Yoneda10_ee_ G f H v))) _H _v) )  *)
    + Time rewrite /= /Yoneda10_PolyElement_default /= .
      apply: (sval (Viewing_transp_E _H _H unitGenerator (projT2 (sval_Yoneda10_ee_ G f H v) _H _v))).
      { unshelve eexists.
        + exact: ( w_w , w_w :>Generator ) .
        + clear. revert dependent H'. revert dependent G.  revert dependent projT1_sval_Yoneda10_ee_ .
          revert sval_Yoneda10_ee_ .
          Time abstract (intros; exact: unitGenerator_polyGenerator). (* 29s , 38s , 19s , 25s , 28s , 13s *)
      }
  - Time Optimize Heap. exfalso; clear; abstract (exact: TMP_AXIOM_OUT_OF_MEMORY).
(** - split.
    + move. intros G0 G0' g0 wv0. Time rewrite [LHS]Yoneda01_innerViewing_rewrite. (* 946s 14G *) Time Optimize Heap. (* 42s, 12G *)
      Time apply Yoneda00_innerViewing_quotientLogical.
     Time set wv := (sval (viewingDefault'_poly_transp _ _) _ wv0). (* 303s *)
      Time (set H : obGenerator := (projT1 (projT1 wv) in LHS)).  (* 253s , inlhs 355*)
      Time (set v : 'Generator( H ~> _ | _ ) := projT2 (projT1 wv)). (* 252s *) Time Optimize Heap.
      Time (set w : 'Generator( _ ~> _ |  _ H v ) := porjT2 wv). (* 247s *) 
      Time (set _wv := ((sval (viewingContinuous_ee_ G f H v H unitGenerator) H unitGenerator))). (* 289s *)
      Time (set _H : obGenerator := projT1 (projT1 _wv)). (* 259s *)
      Time (set _v : 'Generator( _H ~> _ | projT1 (sval_Yoneda10_ee_ G f H v) ) := projT2 (projT1 _wv)).
      Time (set _w : 'Generator( _ ~> _ |  Viewing_E _H (projT2 (sval_Yoneda10_ee_ G f H v) _H _v) ) := projT2 _wv).
      Time (set w_w : 'Generator( _ ~> _ | _ ) := ( (w :>Generator) o>Generator _w | _ )).
      Time rewrite [LHS]Yoneda01_innerViewing_rewrite.
      Time apply Yoneda00_innerViewing_quotientLogical.
 g o>Generator ( ( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) , ((w :>Generator) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) )
= ( ( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) , g o>Generator ( (w :>Generator) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) )
= ( ( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) , ( (g o>Generator (w :>Generator)) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) )
~ (( (g o>Generator (w :>Generator)) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) :>Generator) o>Generator {< v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) >}
~  {< v , (( (g o>Generator (w :>Generator)) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) :>Generator) o>Generator (projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1))) >}
~ ( ( (( (g o>Generator (w :>Generator)) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) :>Generator) o>Generator (projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1))) | _ ) :>Generator ) o>Generator v | _
~  (((g o>Generator (w :>Generator)) o>Generator 1) o>Generator 1) o>Generator v | _
~? (((w' :>Generator) o>Generator 1) o>Generator 1) o>Generator v' | _
   ... (sval (viewingDefault'_poly_transp _ _) _ (g o>Generator wv0 | _ )) = g o>Generator (sval (viewingDefault'_poly_transp _ _) _ wv0) | _   =  g o>Generator wv | _ = (v , g o>Generator w | _ ) 
~ ((( (g o>Generator w | _ ) :>Generator) o>Generator 1) o>Generator 1) o>Generator v | _
~ (( (g o>Generator (w :>Generator)) o>Generator 1) o>Generator 1) o>Generator v | _

+ intros H' wv0.
( ( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) , ((w :>Generator) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) ) :>Generator
= (((w :>Generator) o>Generator (projT2 (viewingContinuous_ee_ G f H v 1 1)) | _ ) :>Generator) o>Generator 
    (( v , projT2 (projT1 (viewingContinuous_ee_ G f H v 1 1)) ) :>Generator)
= ((w :>Generator) o>Generator 1) o>Generator ( 1 o>Generator (v :>Generator) )
?= wv0 :>Generator
= (sval (viewingDefault'_poly_transp _ _) _ wv0) :>Generator
= wv :>Generator
= ((w :>Generator) o>Generator (v :>Generator))
 **)
Defined.
End Senses_viewingContinuous.
End Senses_morCoMod.
(** # #
#+END_SRC

** Grammar of the morphisms , which carry the sense-decodings

  Memo that grammatically , the target/codomain functor of the parameter transformation of the constructor [ViewedFunctor1] is some viewing-functor . This same memo holds for the constructors [UnitViewedFunctor] and [PolyTransf].

  And , as wanted , the target/codomain functor of the parameter transformation of the constructor [PolyTransf_default] is some viewed-functor ; moreover the codomain of the output is indeed not changed , as for the common default-colimiting . 

  Now the section/injection [PolyElement] constructor inputs some viewing-element of any viewing-functor and changes its format (internalizes) and outputs some grammatical transformation which is the « polyelement » ( the generator-arrows-(functorial-)action ( "Yoneda" ) ) of this viewing-element  . 

  Also the modified-colimiting reflector/copairing [PolyTransf] constructor inputs some real polymorph-cocones at the elements of some viewing-functor into some target functor and changes its format (internalizes) and outputs some grammatical transformation from this same viewing-functor into the viewed-functor of the target functor .

   In contrast , the default-colimiting reflector/copairing [PolyTransf_default] constructor inputs some (nested) real polymorph-cocones at the elements of some viewing-functor into some viewed-functor and changes its format (internalizes) and outputs some grammatical transformation into this same viewed-functor from this sense-same source functor but grammatically with the viewings-for-default-colimiting ( [viewingDefault_] , inner (dependent sum) viewings ) . Attention the « polyviewing » formulation of [PolyTransf_default] where the output viewings is not precisely the expected « viewings-for-default-colimiting » ( [viewingDefault_] ) but is any viewings which is contained/smaller than this viewings-for-default-colimiting .

  Lastly , memo that the viewings-data or polymorph-viewings-transport logical-conditions are carried only by the two constructors [PolyTransf] and [PolyTransf_default] , and are not carried by the other constructors .

#+BEGIN_SRC coq :exports both :results silent # # **)
Reserved Notation "''CoMod' (  F'  ~>  F  @  Yoneda10_ff  @~  viewingContinuous_ff  )" (at level 0).

Inductive morCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ff : Yoneda10_data Yoneda01_F Yoneda01_E)
        (viewingContinuous_ff : viewingContinuous Viewing_F Viewing_E Yoneda10_ff), Type :=

| PolyCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F)
                 Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F'
                (F' : @obCoMod Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F')
                Yoneda10_ff' viewingContinuous_ff'  (ff' : 'CoMod( F' ~> F @ Yoneda10_ff' @~ viewingContinuous_ff' )),
            forall Yoneda00_F'' Yoneda01_F'' Viewing_F'' Viewing_data_F'' Viewing_transp_F''
               (F'' : @obCoMod Yoneda00_F'' Yoneda01_F'' Viewing_F'' Viewing_data_F'' Viewing_transp_F''),
            forall Yoneda10_ff_ viewingContinuous_ff_  (ff_ : 'CoMod( F'' ~> F' @ Yoneda10_ff_ @~ viewingContinuous_ff_ )),
              'CoMod( F'' ~> F @ Yoneda10_PolyCoMod Yoneda10_ff_ Yoneda10_ff' @~ viewingContinuous_PolyCoMod viewingContinuous_ff' viewingContinuous_ff_ )

| UnitCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    'CoMod( F ~> F @ Yoneda10_UnitCoMod Yoneda01_F @~ viewingContinuous_UnitCoMod Yoneda01_F Viewing_F )

| View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    'CoMod( View H ~> View G @ Yoneda10_View1 g @~ viewingContinuous_View1 g)

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
      'CoMod( ViewedFunctor E ~> ViewedFunctor F @ Yoneda10_ViewedFunctor1 Yoneda10_ff @~ viewingContinuous_ViewedFunctor1 viewingContinuous_ff ) 

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
      'CoMod( E ~> ViewedFunctor F @ Yoneda10_UnitViewedFunctor Yoneda10_ff @~ viewingContinuous_UnitViewedFunctor Viewing_transp_F viewingContinuous_ff )

| PolyElement : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
      'CoMod( View H ~> ViewingFunctor isFiniteness_F
                   @ Yoneda10_PolyElement Yoneda01_F v @~ viewingContinuous_PolyElement Viewing_transp_F v )

| PolyTransf : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                                 Yoneda10_data (Yoneda01_View H) Yoneda01_E),
      forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              viewingContinuous (@Viewing_View H) Viewing_E (Yoneda10_ee_ G f H v)),
      forall (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v))),
      forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v'))),
      forall (Yoneda10_ee_real : 
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (Viewing_F G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
      'CoMod( ViewingFunctor isFiniteness_F ~> ViewedFunctor E @ Yoneda10_PolyTransf Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real @~ viewingContinuous_PolyTransf Viewing_data_F viewingContinuous_ee_  Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real )

| PolyTransf_default : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                               Yoneda10_data (Yoneda01_View H)  (Yoneda01_ViewedFunctor Yoneda01_E) ),
    forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
            viewingContinuous (@Viewing_View H) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v)),
    forall (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v))),
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v'))),
    forall (Yoneda10_ee_real :
                forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (Viewing_F G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
        let projT1_sval_Yoneda10_ee_ G f H v
            := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
        forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
          (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
          (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
          (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
        forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
          'CoMod( ViewingFunctor viewingDefault'_isFiniteness ~> ViewedFunctor E
                                 @ (Yoneda10_PolyTransf_default Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism  Yoneda10_ee_real)
                                 @~ viewingContinuous_PolyTransf_default Viewing_data_F Viewing_transp_E viewingContinuous_ee_  Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real viewingDefault'_poly_transp)

where "''CoMod' (  F'  ~>  F  @  Yoneda10_ff  @~  viewingContinuous_ff  )" :=
        (@morCoMod _ _ _ _ _ F' _ _ _ _ _ F Yoneda10_ff viewingContinuous_ff) : poly_scope. 

(*MEMO: OLD:      forall (Yoneda10_ee_morphism : 
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | (V_ G' (g o>Generator_[sval Yoneda01_F] f)) )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval (sval (V_transp G G' g f) H v')))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H v')), *)

Notation "''CoMod' (  F'  ~>  F  )" := (@morCoMod _ _ _ _ _ F' _ _ _ _ _ F _ _ )
       (at level 0, only parsing) : poly_scope.

Notation "ff_ o>CoMod ff'" := (@PolyCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' _ _ _ _ _ _ _ _ ff_)
                                (at level 40 , ff' at next level , left associativity) : poly_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ _ _ _ F)
                                 (at level 10, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _ _ _ _) (at level 0) : poly_scope.

Notation "''View1' g" := (@View1 _ _ g)
                   (at level 10, g at next level) : poly_scope.

Notation "''ViewedFunctor1' ee" := (@ViewedFunctor1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee)
                   (at level 10, ee at next level) : poly_scope.

Notation "ff o>CoMod 'UnitViewedFunctor" := (@UnitViewedFunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)
                  (at level 4, right associativity) : poly_scope.

Notation "''PolyElement'  v  @  isFiniteness_F" :=
  (@PolyElement _ _ _ _ _ isFiniteness_F _ _ _ v) (at level 10, v, isFiniteness_F at next level) : poly_scope.

Notation "[[  ee_  @  isFiniteness_F  ,  Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_real  ]]" :=
  (@PolyTransf _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_ )
    (at level 4, ee_ , isFiniteness_F , Yoneda10_ee_natural, Yoneda10_ee_morphism, Yoneda10_ee_real at next level ) : poly_scope.

Notation "[[  ee_  @  isFiniteness_F  ]]" :=
  (@PolyTransf _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ _ _ _ ee_ )
    (at level 4, ee_ , isFiniteness_F at next level ) : poly_scope.

Notation "[[[  ee_  @  isFiniteness_F , Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_real  ,  viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]]" :=
  (@PolyTransf_default _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_ _ _ _ viewingDefault'_isFiniteness viewingDefault'_poly_transp)
    (at level 4, ee_ , isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp at next level ) : poly_scope.

Notation "[[[  ee_  @  isFiniteness_F ,  viewingDefault'_isFiniteness ]]]" :=
  (@PolyTransf_default _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ _ _ _ ee_ _ _ _ viewingDefault'_isFiniteness _)
    (at level 4, ee_ , isFiniteness_F , viewingDefault'_isFiniteness at next level ) : poly_scope.
(** # #
#+END_SRC

* Grammatical conversions of morphisms , which infer the same sense-decoding

  As common , the grammatical conversions are classified into : the total/(multi-step) conversions , and the congruences (recursive) conversions , and the constant (non-recursive) conversions which are used in the polymorphism/cut-elimination lemma , and the constant conversions which are only for the wanted sense of modified-colimits-into-viewed-functors , and the constant conversions which are only for the confluence lemma (TODO:) , and the constant conversions which are derivable by using the finished cut-elimination lemma . ( Memo that the section/injection [PolyElement] transformation has constructor-ed functors at both the codomain ( [ViewingFunctor] ) and the codomain ( [View] ) , therefore the confluence lemma will not ( ? ) lack any additional conversion ... )

  In contrast , because of the embedded sense-decoding extra-indexes/arguments in the datatype-families [morCoMod] of the morphisms , the conversion-relation shall convert across two morphisms whose sense-decoding datatype-indexes/arguments are not syntactically/grammatically-the-same . But oneself does show that , by logical-deduction [convCoMod_sense] , these two sense-decodings are indeed propositionally equal ( « sensible lemma » , "soundness lemma" ) .

  The converse inference is the « sense-completeness lemma » , whose deduction will lack the finished cut-elimination lemma . Such sense-completeness lemma is expected because : some sense-completeness lemma are known to hold for adjunctions and for comonad and for (cartesian) products but using the combinatorial "links" sense ( in the style of Dosen ) ; the attention is that this combinatorial "links" sense is the combinatorial essense of this ongoing (algebraic) metafunctors ( "presheaf" ) sense ; therefore those completeness lemma shall transfer . Similarly the « maximality lemma » says that any non-deductible extra conversion constructor which is assumed to hold in the sense (model) , will make any two grammatical morphisms equal ( preorder ) in the sense . Such maximality lemma which are known to hold for adjunctions and for comonad and for (cartesian) products shall transfer to this ongoing metafunctors ( "presheaf" ) sense .

  Memo that the polymorphism conversions [PolyTransf_morphism] and [PolyTransf_default_morphism] have different form ; where [PolyTransf_default_morphism] has the more-common form for default-colimiting but only among the viewed-transformations ( of the form [ViewedFunctor1] ) . Also memo that the cancellation conversions [PolyTransf_PolyElement] and [PolyTransf_default_PolyElement] have different form ; where for [PolyTransf_PolyElement] the pair ( element , viewing-arrow ) of the viewing-element of the viewing-functor is material and the contractum (the selected component) is relaxed by [UnitViewedFunctor] , but for [PolyTransf_default_PolyElement] only the (acted/resulting) viewing-element is material and the contractum (the selected component) is not relaxed by [UnitViewedFunctor] .

  Now memo the conversion-for-morphisms constructor [AtIndexMor'MorCoMod_indexed] which says that [ grammatically collecting/familiarize many morphisms and then grammatically selecting some singleton morphism from this collection/family at some index ] is convertible to [ applying/substituting this index in the original collection/family/function ] . This conversion-relation will be held during the polymorphism/cut-elimination resolution . One question is whether such similar conversion-for-objects ( instead of for-morphisms ) across singleton-objects and indexed-objects would be useful ?

  Finally , some linear total/asymptotic grade is defined on the morphisms and the tactics-automated degradation lemma shows that each of the conversion indeed degrades the redex morphism .

** Grammatical conversions of morphisms

#+BEGIN_SRC coq :exports both :results silent # # **)
Section Senses_convCoMod.

Lemma Yoneda10_PolyElement_real Yoneda00_F Yoneda01_F
      (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G) :
  forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
         (v v' : 'Generator( H ~> G | (V_ G f) ))
         (Heq : (v :>Generator) = (v' :>Generator)),
  polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v)
  = polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v').
Proof. 
  intros; rewrite /Yoneda10_PolyElement. rewrite Heq. reflexivity.
Qed.
  
Lemma Yoneda10_PolyElement_natural
      Yoneda00_F Yoneda01_F  
      (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G) :
  forall (G : obGenerator) (f : Yoneda00_F G),
    Yoneda10_natural (Yoneda01_Viewing (V_ G f)) Yoneda01_F
                     (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
                        polyelement_to_element (Yoneda10_PolyElement Yoneda01_F v)).
Proof.
  intros; move; simpl; intros.
  do 2 rewrite [in LHS](proj1 (proj2_sig Yoneda01_F)).
  do 1 rewrite [in RHS](proj1 (proj2_sig Yoneda01_F)).
  rewrite -[in LHS]unitGenerator_polyGenerator.
  rewrite -[in RHS]polyGenerator_unitGenerator.
  rewrite -[in RHS](proj2_sig (Yoneda10_realize (V_ G f))). reflexivity.
Qed. 

Lemma Yoneda10_PolyElement_morphism
      Yoneda00_F Yoneda01_F  
      (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
      (V_transp : viewingFunctor Yoneda01_F V_) :
 forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) 
   (f : Yoneda00_F G) (H : obGenerator)
   (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
   polyelement_to_element (Yoneda10_PolyElement Yoneda01_F (fst (sval v'))) =
   polyelement_to_element (Yoneda10_PolyElement Yoneda01_F (sval (V_transp G G' g f) H v')) .
Proof.
  intros; congr polyelement_to_element;
    move; simpl; intros. rewrite /Yoneda10_PolyElement. simpl.
  rewrite [in RHS](proj2 (proj2_sig (V_transp G G' g f))). rewrite [in RHS]/= .
  rewrite [in RHS](proj1 (proj2_sig Yoneda01_F)).
  simpl. rewrite (proj2_sig v'). reflexivity.
Qed.

Lemma Yoneda10_PolyTransf_morphism_natural
Yoneda00_F  (V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
Yoneda00_E  Yoneda01_E 
(Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_natural : forall (G : obGenerator) (f : Yoneda00_F G),
Yoneda10_natural (Yoneda01_Viewing (V_ G f)) Yoneda01_E
  (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
   polyelement_to_element (Yoneda10_ee_ G f H v)))
Yoneda00_E'  Yoneda01_E' 
(Yoneda10_e'e' : {Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10}) :
 forall (G : obGenerator) (f : Yoneda00_F G),
  Yoneda10_natural (Yoneda01_Viewing (V_ G f)) 
    Yoneda01_E'
    (fun (H : obGenerator) (v : 'Generator( H ~> G | (V_ G f) )) =>
     polyelement_to_element ( Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v)
                           Yoneda10_e'e')) .
Proof.
  intros; move; simpl; intros.
  rewrite (proj2_sig Yoneda10_e'e').
  rewrite [in LHS]Yoneda10_ee_natural. reflexivity.
Qed.

Lemma Yoneda10_PolyTransf_morphism_morphism
Yoneda00_F Yoneda01_F 
(V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
(V_transp : viewingFunctor Yoneda01_F V_)
Yoneda00_E  Yoneda01_E 
(Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v')))
Yoneda00_E'  Yoneda01_E' 
( Yoneda10_e'e' : {Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10} ) :
forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) 
  (f : Yoneda00_F G) (H : obGenerator)
  (v' : 'Generator( H ~> G' | intersecViewing (V_ G f) g )),
  polyelement_to_element (Yoneda10_PolyCoMod
    (Yoneda10_ee_ G f H (fst (sval v'))) Yoneda10_e'e') =
  polyelement_to_element (Yoneda10_PolyCoMod (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (V_transp G G' g f) H v'))
                                             Yoneda10_e'e').
Proof.
  intros; rewrite /polyelement_to_element /= in Yoneda10_ee_morphism *.
  rewrite Yoneda10_ee_morphism. reflexivity.
Qed.

Lemma Yoneda10_PolyTransf_morphism_real
 Yoneda00_F (Yoneda01_F : {Yoneda01
               : forall G G' : obGenerator, 'Generator( G' ~> G ) -> Yoneda00_F G -> Yoneda00_F G' |
               Yoneda01_functor Yoneda01})
(V_ : forall G : obGenerator, Yoneda00_F G -> obViewing G)
Yoneda00_E  Yoneda01_E 
(Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator),
'Generator( H ~> G | (V_ G f) ) ->
{Yoneda10 : forall H' : obGenerator, Yoneda00_View H H' -> Yoneda00_E H' |
Yoneda10_natural (Yoneda01_View H) Yoneda01_E Yoneda10})
(Yoneda10_ee_real :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
  (v v' : 'Generator( H ~> G | (V_ G f) )),
v :>Generator = v' :>Generator ->
polyelement_to_element (Yoneda10_ee_ G f H v) =
polyelement_to_element (Yoneda10_ee_ G f H v'))
Yoneda00_E' Yoneda01_E' 
(Yoneda10_e'e' : {Yoneda10 : forall G : obGenerator, Yoneda00_E G -> Yoneda00_E' G |
Yoneda10_natural Yoneda01_E Yoneda01_E' Yoneda10}) :
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
    (v v' : 'Generator( H ~> G | (V_ G f) )),
  v :>Generator = v' :>Generator ->
  polyelement_to_element
    (Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v) Yoneda10_e'e') =
  polyelement_to_element
    (Yoneda10_PolyCoMod (Yoneda10_ee_ G f H v') Yoneda10_e'e') .
Proof.
  intros ? ? ? ? ? Heq; simpl. rewrite /polyelement_to_element in Yoneda10_ee_real.
  rewrite (Yoneda10_ee_real _ _ _ _ _ Heq). reflexivity.
Qed.

End Senses_convCoMod.
  
Reserved Notation "ff0 <~~ ff" (at level 70).

Inductive convCoMod : forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
    forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0)),  Prop :=

(**  ----- the total/(multi-step) conversions -----  **)

| convCoMod_Refl :
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
      ff <~~ ff

| convCoMod_Trans :
    forall  Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
    forall Yoneda10_uTrans viewingContinuous_uTrans (uTrans : 'CoMod( E ~> F @ Yoneda10_uTrans @~ viewingContinuous_uTrans)),
      ( uTrans <~~ ff ) ->
      forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0) ),
        ( ff0 <~~ uTrans ) -> ( ff0 <~~ ff )

(**  ----- the congruences (recursive) conversions for morphisms -----  **)

| PolyCoMod_cong :
    forall Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F'
      (F' : @obCoMod Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F')
     Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
     (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F)
      Yoneda10_ff' viewingContinuous_ff' (ff' : 'CoMod( F' ~> F @ Yoneda10_ff' @~ viewingContinuous_ff'))
      Yoneda00_F'' Yoneda01_F'' Viewing_F'' Viewing_data_F'' Viewing_transp_F''
      (F'' : @obCoMod Yoneda00_F'' Yoneda01_F'' Viewing_F'' Viewing_data_F'' Viewing_transp_F'')
      Yoneda10_ff_ viewingContinuous_ff_ (ff_ : 'CoMod( F'' ~> F' @ Yoneda10_ff_ @~ viewingContinuous_ff_))
      Yoneda10_ff_0 viewingContinuous_ff_0  (ff_0 : 'CoMod( F'' ~> F' @ Yoneda10_ff_0 @~ viewingContinuous_ff_0 ))
      Yoneda10_ff'0 viewingContinuous_ff'0 (ff'0 : 'CoMod( F' ~> F @ Yoneda10_ff'0 @~ viewingContinuous_ff'0 )),
      ff_0 <~~ ff_ -> ff'0 <~~ ff' -> ( ff_0 o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )
                             
| ViewedFunctor1_cong : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
    forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0)),
      ff0 <~~ ff ->
      ( 'ViewedFunctor1 ff0 ) <~~ ( 'ViewedFunctor1 ff )

| UnitViewedFunctor_cong : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
    forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0)),
      ff0 <~~ ff ->
      (ff0 o>CoMod 'UnitViewedFunctor) <~~ (ff o>CoMod 'UnitViewedFunctor)

(** grammatical conversions shall be sense-complete , therefore : **)
| PolyElement_cong :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
    forall (G0 : obGenerator) (f0 : Yoneda00_F G0) (v0 : 'Generator( H ~> G0 | (Viewing_F G0 f0) )),

      ( ( v0 :>Generator ) o>Generator_[sval Yoneda01_F] f0 ) = ( ( v :>Generator ) o>Generator_[sval Yoneda01_F] f )
      -> ( 'PolyElement v0 @ isFiniteness_F ) <~~ ( 'PolyElement v @ isFiniteness_F )

| PolyTransf_cong : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F
                      (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real
      (ee_ : ( forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) )),
    forall Yoneda10_ee0_ viewingContinuous_ee0_ Yoneda10_ee0_natural Yoneda10_ee0_morphism Yoneda10_ee0_real ,
    forall (ee0_ : ( forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee0_ G f H v @~ viewingContinuous_ee0_ G f H v ) )),
      ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
          (v : 'Generator( H ~> G | (Viewing_F G f) )),
          ee0_(G)(f)(H)(v) <~~ ee_(G)(f)(H)(v) ) ->
      [[ ee0_ @ isFiniteness_F , Yoneda10_ee0_natural , Yoneda10_ee0_morphism , Yoneda10_ee0_real ]]
        <~~ [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]]

| PolyTransf_default_cong : forall  Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F
                               (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                               (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real
      (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v )),
      let projT1_sval_Yoneda10_ee_ G f H v
          := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
        forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
          (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
          (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
          (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
        forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
    forall Yoneda10_ee0_ viewingContinuous_ee0_
      Yoneda10_ee0_natural Yoneda10_ee0_morphism Yoneda10_ee0_real ,
    forall (ee0_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee0_ G f H v @~ viewingContinuous_ee0_ G f H v )),
      let projT1_sval_Yoneda10_ee0_ G f H v
          := (projT1 (sval (polyelement_to_element (Yoneda10_ee0_ G f H v)))) in 
      forall (viewingDefault'_poly_transp0 : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee0_ f)),
      ( forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator)
          (v : 'Generator( H ~> G | (Viewing_F G f) )),
          ee0_(G)(f)(H)(v) <~~ ee_(G)(f)(H)(v) ) ->
      [[[ ee0_ @ isFiniteness_F , Yoneda10_ee0_natural , Yoneda10_ee0_morphism , Yoneda10_ee0_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp0 ]]]
        <~~ [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]]

(** ----- the constant conversions which are used during the polymorphism elimination ----- **)

| PolyCoMod'UnitCoMod :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
      ff <~~ ( ff o>CoMod ('UnitCoMod) )

(**memo: not all cases of this conversion are necessary **)
| PolyCoMod_UnitCoMod :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
      ff <~~ ( ('UnitCoMod) o>CoMod ff )

(** a.k.a View1_View1 **)         
| View1_morphism : forall (G H : obGenerator) (g : 'Generator( H ~> G )) (H' : obGenerator) (h : 'Generator( H' ~> H )),
    ('View1 (h o>Generator g))
      <~~ ('View1 h o>CoMod 'View1 g)

(** a.k.a ViewedFunctor1_ViewedFunctor1  **)
| ViewedFunctor1_morphism :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
    forall Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D
      (D : @obCoMod Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D),
    forall Yoneda10_dd viewingContinuous_dd (dd : 'CoMod( F ~> D @ Yoneda10_dd @~ viewingContinuous_dd)),
      ( 'ViewedFunctor1 (ff o>CoMod dd ) )
        <~~ ( 'ViewedFunctor1 ff ) o>CoMod ( 'ViewedFunctor1 dd )

(** a.k.a ViewedFunctor1_UnitViewedFunctor **)
| UnitViewedFunctor_morphismPost :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
    forall Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D
      (D : @obCoMod Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D),
    forall Yoneda10_dd viewingContinuous_dd (dd : 'CoMod( F ~> D @ Yoneda10_dd @~ viewingContinuous_dd)),

      ( ( ff o>CoMod dd ) o>CoMod 'UnitViewedFunctor )
        <~~ ( ( ff o>CoMod 'UnitViewedFunctor ) o>CoMod ( 'ViewedFunctor1 dd ) )

(** a.k.a ViewedFunctor1_PolyTransf **)
| PolyTransf_morphism :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                                 Yoneda10_data (Yoneda01_View H) Yoneda01_E),
      forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              viewingContinuous (@Viewing_View H) Viewing_E (Yoneda10_ee_ G f H v)),
      forall Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real
      (ee_ :  forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v )),
    forall Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D
      (D : @obCoMod Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D),
    forall Yoneda10_dd viewingContinuous_dd (dd : 'CoMod( E ~> D @ Yoneda10_dd @~ viewingContinuous_dd)),

        ( [[ ( fun G f H v => ee_ G f H v o>CoMod dd )
               @ isFiniteness_F , Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural Yoneda10_dd , Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism  Yoneda10_dd ,  Yoneda10_PolyTransf_morphism_real Yoneda01_F Yoneda10_ee_real  Yoneda10_dd ]] )
          <~~  ( [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]]
                   o>CoMod ( 'ViewedFunctor1 dd ) )

(** a.k.a ViewedFunctor1_PolyTransf_default **)
| PolyTransf_default_morphism :
    forall  Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
       (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                               Yoneda10_data (Yoneda01_View H)  (Yoneda01_ViewedFunctor Yoneda01_E) ),
    forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
            viewingContinuous (@Viewing_View H) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v)),
    forall Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real,
    forall ( ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
      let projT1_sval_Yoneda10_ee_ G f H v
          := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
      forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
        (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
        (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
        (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
      forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
    forall Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D
      (D : @obCoMod Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D),
    forall Yoneda10_dd viewingContinuous_dd (dd : 'CoMod( E ~> D @ Yoneda10_dd @~ viewingContinuous_dd)),

      ( [[[ ( fun G f H v => ( ee_ G f H v ) o>CoMod ( 'ViewedFunctor1 dd ) )
               @ isFiniteness_F , Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural (Yoneda10_ViewedFunctor1 Yoneda10_dd) , Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism  (Yoneda10_ViewedFunctor1 Yoneda10_dd) ,  Yoneda10_PolyTransf_morphism_real Yoneda01_F Yoneda10_ee_real  (Yoneda10_ViewedFunctor1 Yoneda10_dd) , viewingDefault'_isFiniteness , viewingDefault'_poly_transp  ]]] )
<~~ ( [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]] o>CoMod ( 'ViewedFunctor1 dd ) )

(** a.k.a UnitViewedFunctor_PolyCoMod **)
| UnitViewedFunctor_morphismPre :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
    forall Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D
      (D : @obCoMod Yoneda00_D Yoneda01_D Viewing_D Viewing_data_D Viewing_transp_D),
    forall Yoneda10_dd viewingContinuous_dd (dd : 'CoMod( D ~> E @ Yoneda10_dd @~ viewingContinuous_dd)),
      ( (dd o>CoMod ff) o>CoMod 'UnitViewedFunctor )
        <~~ ( dd o>CoMod ( ff o>CoMod 'UnitViewedFunctor ) )

(** a.k.a PolyElement_View1 **)
| PolyElement_morphism :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
    forall (H' : obGenerator) (h : 'Generator( H' ~> H )),
      ( 'PolyElement ( h o>Generator v | (Viewing_F G f) ) @  isFiniteness_F ) 
                   <~~ ( 'View1 h o>CoMod 'PolyElement v @ isFiniteness_F )

| PolyTransf_PolyElement :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                                 Yoneda10_data (Yoneda01_View H) Yoneda01_E),
      forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              viewingContinuous (@Viewing_View H) Viewing_E (Yoneda10_ee_ G f H v)),
      forall Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real
           (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v )),
    forall G f H v,
      ( (ee_(G)(f)(H)(v)) o>CoMod 'UnitViewedFunctor )
        <~~ ( ( 'PolyElement v @  isFiniteness_F
                : 'CoMod( View H ~> ViewingFunctor isFiniteness_F @ _ @~ _ ) )
                o>CoMod [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural,
                           Yoneda10_ee_morphism, Yoneda10_ee_real ]]
              : 'CoMod( View H ~> ViewedFunctor E @ _ @~ _ ) )

| PolyTransf_default_PolyElement :
    forall  Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
       (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                               Yoneda10_data (Yoneda01_View H)  (Yoneda01_ViewedFunctor Yoneda01_E) ),
    forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
            viewingContinuous (@Viewing_View H) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v)),
    forall Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real,
    forall ( ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
      let projT1_sval_Yoneda10_ee_ G f H v
          := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
        forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
          (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
          (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
          (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
        forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
    forall (G : obGenerator) (f : Yoneda00_F G) (H' : obGenerator)
           (wv : 'Generator( H' ~> G | (viewingDefault'_ G f) )),
      ( (ee_(G)(f)(H')(((projT2 (sval (viewingDefault'_poly_transp G f) H' wv)) :>Generator) o>Generator (projT2 (projT1 (sval (viewingDefault'_poly_transp G f) H' wv))) | (Viewing_F G f)))  )
        <~~ ( 'PolyElement wv @ viewingDefault'_isFiniteness
                o>CoMod [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural,
                           Yoneda10_ee_morphism, Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]] )

(** ----- the constant conversions which are only for the wanted sense of
modified-colimits-into-viewed-functors grammar ----- **)

(* TODO: add conversion [PolyTransf_default'PolyElement] *)     
| PolyTransf'PolyElement :
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
      (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
  (*todo: problem: how to recognize grammatically such many/family/cover of arrows in PolyElement ? *)
        ( 'UnitCoMod o>CoMod 'UnitViewedFunctor )
          <~~  ( [[ (fun G (f : Yoneda00_F) H v => 'PolyElement v @ isFiniteness_F)
                    @ isFiniteness_F , @Yoneda10_PolyElement_natural _ Yoneda01_F Viewing_F , Yoneda10_PolyElement_morphism Viewing_transp_F , @Yoneda10_PolyElement_real _ Yoneda01_F Viewing_F ]] )

(** ----- the constant conversions which are only for the confluence lemma (TODO:) ----- **)

(** none ? **)

(** ----- the constant conversions which are derivable by using the finished cut-elimination lemma
 ----- TODO: COMMENT ALL THIS SECTION----- **)

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

where "ff0 <~~ ff" := (@convCoMod _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff _ _ ff0) : poly_scope.

Hint Constructors convCoMod.
(** # #
#+END_SRC

** Same sense-decoding for convertible morphisms

  Because of the embedded sense-decoding extra-indexes/arguments in the datatype-families [morCoMod] of the morphisms , the conversion-relation shall convert across two morphisms whose sense-decoding datatype-indexes/arguments are not syntactically/grammatically-the-same . But oneself does show that , by logical-deduction [convCoMod_sense] , these two sense-decodings are indeed propositionally equal ( « sensible lemma » , "soundness lemma" ) .   The converse inference is the « sense-completeness lemma » , whose deduction will lack the finished cut-elimination lemma . Such sense-completeness lemma is expected because : some sense-completeness lemma does hold for adjunctions and for comonad and for (cartesian) products but using the combinatorial "links" sense ( in the style of Dosen ) ; the attention is that this combinatorial "links" sense is the combinatorial essense of this ongoing (algebraic) metafunctors ( "presheaf" ) sense ; therefore those completeness lemma shall transfer .

  The converse inference is the « sense-completeness lemma » , whose deduction will lack the finished cut-elimination lemma . Such sense-completeness lemma is expected because : some sense-completeness lemma are known to hold for adjunctions and for comonad and for (cartesian) products but using the combinatorial "links" sense ( in the style of Dosen ) ; the attention is that this combinatorial "links" sense is the combinatorial essense of this ongoing (algebraic) metafunctors ( "presheaf" ) sense ; therefore those completeness lemma shall transfer . Similarly the « maximality lemma » says that any non-deductible extra conversion constructor which is assumed to hold in the sense (model) , will make any two grammatical morphisms equal ( preorder ) in the sense . Such maximality lemma which are known to hold for adjunctions and for comonad and for (cartesian) products shall transfer to this ongoing metafunctors ( "presheaf" ) sense .

  Memo that the lemma [convCoMod_sense] will only be used during the polymorphism/cut-elimination resolution [solveCoMod] to show/transfer the logical-properties of some real polymorph-cocones ( [Yoneda10_ee_natural] , [Yoneda10_ee_morphism] , [Yoneda10_ee_real] ) and to show/transfer the polymorphism of some viewings-for-default-colimiting ( [viewingDefault'_transp] ) .

#+BEGIN_SRC coq :exports both :results silent # # **)
Lemma convCoMod_sense :
 forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
    forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0)),
      ff0 <~~ ff -> forall G : obGenerator,
          (sval Yoneda10_ff G) =1 (sval Yoneda10_ff0 G).
Proof.
  intros until ff0. intros conv_ff.
  elim : Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F
                    Yoneda10_ff viewingContinuous_ff ff Yoneda10_ff0 viewingContinuous_ff0 ff0 / conv_ff .

  (**  ----- the total/(multi-step) conversions -----  **)
  - (* convCoMod_Refl *)  intros. move. intros f. reflexivity.
  - (* convCoMod_Trans *) intros until 1. intros gg_eq .
    intros until 1. intros uTrans_eq.
    intros. move. intros f. rewrite gg_eq uTrans_eq . reflexivity. 

  (**  ----- the congruences (recursive) conversions for singleton morphisms -----  **)
  - (* PolyCoMod_cong *)  intros until 1. intros ff__eq .
    intros ? ff'_eq ? . move. intros f'.
    rewrite /Yoneda10_PolyCoMod /= . rewrite ff__eq ff'_eq. reflexivity.
  - (* ViewedFunctor1_cong *) intros until 1. intros ff_eq . intros; move; intros ee. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:= projT1 (sval ee));
    [ exact: identity_transpViewing
    | exact: identity_transpViewing | ].
    intros; move; simpl; intros; rewrite ff_eq; reflexivity.
  - (* UnitViewedFunctor_cong *)
    intros until 1. intros ff_eq . intros; move; intros e. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=  unitViewing unitGenerator);
    [ exact: identity_transpViewing
    | exact: identity_transpViewing | ].
    intros; move; simpl; intros; rewrite ff_eq; reflexivity.
  - (* PolyElement_cong  *)
    intros until 1. intros ? ? ? ? ? ? ? vf_eq . intros; move; intros h. simpl.
    rewrite [X in _ = h o>Generator_ X ]vf_eq; reflexivity.
  - (* PolyTransf_cong *)
    intros until 2. intros ee_eq . intros; move; intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
        with (W:=  (Viewing_F G f));
    [ exact: identity_transpViewing
    | exact: identity_transpViewing | ].
    intros; move; simpl; intros; rewrite /polyelement_to_element;
      rewrite ee_eq; reflexivity.
  - (* PolyTransf_default_cong *)
    intros until 5. intros ee_eq . intros; move; intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (viewingDefault'_ _ f));
      [ exact: viewingDefault'_poly_transp
      | exact: viewingDefault'_poly_transp0 | ]. 
    intros H'; move; simpl; intros wv.
    set wv_' := ((sval (viewingDefault'_poly_transp _ f) H' wv) in LHS).
    set wv_'0 := ((sval (viewingDefault'_poly_transp0 _ f) H' wv) in RHS). 
    congr (unitGenerator o>Generator_ _ ).
    rewrite [in LHS]/Yoneda10_PolyElement_default.
    rewrite /polyelement_to_element.
    move: (fun G f H v H0 h0 => Yoneda00_ViewedFunctor_quotient_rev (ee_eq G f H v H0 h0)) => ee_eq_transp.
    rewrite (proj2_sig (ee_eq_transp _ f _ (projT2 (projT1 wv_')) _ unitGenerator)).
    apply: (Yoneda10_PolyElement_default_modulo Yoneda10_ee0_natural Yoneda10_ee0_real) . 
    rewrite (proj2 (proj2_sig (sval (ee_eq_transp _ f _ (projT2 (projT1 wv_')) _ unitGenerator)))).
    Time do 2 rewrite -(proj2_sig (Yoneda10_realize (Viewing_F G f) )).
    rewrite [LHS](proj2 (proj2_sig (viewingDefault'_poly_transp G f)) _ wv).
    rewrite [RHS](proj2 (proj2_sig (viewingDefault'_poly_transp0 G f)) _ wv).
    (*  wv :>Generator = wv :>Generator *) reflexivity.

  (** ----- the constant conversions which are used during the PolyCoMod
      polymorphism elimination ----- **)
  - (* PolyCoMod'UnitCoMod *) intros; move; intros f; simpl; reflexivity.
  - (* PolyCoMod_UnitCoMod *) intros; move; intros f; simpl; reflexivity.
  - (* View1_morphism *)
    intros; move; simpl; symmetry; exact: polyGenerator_morphism.
  - (* ViewedFunctor1_morphism *)
    intros; move; intros f_ ; simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:=  projT1 (sval f_));
      [ exact: identity_transpViewing
      | exact: identity_transpViewing | ].
    intros; move; simpl; reflexivity.
  - (* UnitViewedFunctor_morphismPost *)
    intros until 1. intros ? ? ? ?  ? ? Yoneda10_f'f'; intros; move; simpl; intros;
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:=  unitViewing unitGenerator);
      [ exact: identity_transpViewing
      | exact: identity_transpViewing | ].
    intros; move; simpl; intros; rewrite (proj2_sig Yoneda10_f'f'); reflexivity.
  - (* PolyTransf_morphism *)
    intros; move; intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (Viewing_F G f));
      [ exact: identity_transpViewing
      | exact: identity_transpViewing | ].
    intros H; move; simpl; intros v; reflexivity.
  - (* PolyTransf_default_morphism *)
    intros; move; intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (viewingDefault'_ _ f));
      [ exact: viewingDefault'_poly_transp
      | exact: viewingDefault'_poly_transp | ].
    intros H; move; simpl; intros wv.
    set wv_' := (sval (viewingDefault'_poly_transp G f) H wv).
    rewrite -[LHS](proj2_sig Yoneda10_dd). reflexivity.
  - (* UnitViewedFunctor_morphismPre *)
    intros. move. intros d. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= unitViewing unitGenerator);
      [ exact: identity_transpViewing
      | exact: identity_transpViewing | ].
    intros; move; simpl; reflexivity.
  - (* PolyElement_morphism *)
    intros ? Yoneda01_F; intros; move; simpl; intros.
    rewrite [LHS](proj1 (proj2_sig Yoneda01_F)) [RHS](proj1 (proj2_sig Yoneda01_F)).
    rewrite -[in RHS](proj2_sig (Yoneda10_realize _)) [RHS]/=.
    rewrite [in RHS]polyGenerator_morphism. reflexivity.
  - (* PolyTransf_PolyElement *)
    intros until 2; intros G f H v H0; move; intros h; simpl.
    rewrite (proj1 (proj2_sig Yoneda01_F)). (**TODO: MEMO: instead define and use [intersecViewing_polyGenerator_rev] ? *)
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (intersecViewing (Viewing_F _  f) (h o>Generator (v :>Generator)) ));
      [ exact: Viewing_transp_F
      | exact: real_transpViewing
      | ].
    intros H'; move; simpl. intros w.
    rewrite [RHS](proj2_sig (Yoneda10_ee_ _ _ _ _)).
    rewrite [((sval w).2 o>Generator_ h)]unitGenerator_polyGenerator.
    rewrite -[RHS](proj2_sig (Yoneda10_ee_ _ _ _ _)).
    rewrite [in RHS](Yoneda10_ee_natural G f).
    rewrite -[LHS]Yoneda10_ee_morphism.
    apply: Yoneda10_ee_real.

    rewrite -[RHS](proj2_sig (Yoneda10_realize _)) [RHS]/= .
    rewrite (proj2_sig w). simpl.
    exact: polyGenerator_morphism.
  - (* PolyTransf_dafault_PolyElement *)
    exfalso; exact: TMP_AXIOM_OUT_OF_MEMORY.
(*TODO: COMPLETE    intros until wv.  intros H'' h. simpl.
    rewrite (proj1 (proj2_sig Yoneda01_F)).
    unshelve eapply Yoneda00_ViewedFunctor_quotient'
    with (W:= (intersecViewing (viewingDefault'_ _ f) (h o>Generator (wv :>Generator)) ) ).
    simpl. apply: TMP_AXIOM_OUT_OF_MEMORY. simpl. apply: TMP_AXIOM_OUT_OF_MEMORY.  simpl.  intros KK. intros LL. simpl.
  - (* PolyTransf_default_PolyElement *)
    intros until 2. intros projT1_sval_Yoneda10_ee_ viewingDefault'_
                           viewingDefault'_transp G f H' wv H''. move. intros h.

    have lem1 :   
    polyelement_to_element (Yoneda10_PolyCoMod (Yoneda10_PolyElement Yoneda01_F wv)
       (Yoneda10_PolyTransf_default V_data Yoneda10_ee_natural
          Yoneda10_ee_morphism Yoneda10_ee_real)) =
    polyelement_to_element (Yoneda10_ee_ G f H'
       ((projT2 (sval (viewingDefault'_transp G f) H' wv) :>Generator) o>Generator 
               projT2 (projT1 (sval (viewingDefault'_transp G f) H' wv)) | V_ G f)) .
    { set H0 := (projT1 (projT1 (sval (viewingDefault'_transp G f) H' wv))).
    set v0 : 'Generator( H0 ~> _ |  V_ G f )
      := (projT2 (projT1 (sval (viewingDefault'_transp G f) H' wv))).
    set w0  : 'Generator( H' ~> _ | projT1_sval_Yoneda10_ee_ G f H0 v0 )
      := (projT2 (sval (viewingDefault'_transp G f) H' wv)).
    have transp2 : transpViewing (viewingDefault'_ _ ((wv :>Generator) o>Generator_[sval Yoneda01_F] f))
              (projT1 (sval (polyelement_to_element
                               (Yoneda10_ee_ G f H' ((w0 :>Generator) o>Generator v0 | V_ G f))))).
    { abstract (apply: (composition_transpViewing (viewingDefault'_transp _ _));
      apply: (composition_transpViewing (real_transpViewing _));
      apply: (composition_transpViewing (transpViewing_real w0));
      apply: (fst (sval (identity_transpViewing' _ ))); 
      rewrite -[in RHS](Yoneda10_ee_natural _ _ ); reflexivity). }
     simpl.  rewrite -(proj2 (proj2_sig Yoneda01_F)).  simpl.

    unshelve eapply Yoneda00_ViewedFunctor_quotient'
    with (W:= (viewingDefault'_ _ ((wv :>Generator) o>Generator_[sval Yoneda01_F] f)));
      [ exact: viewingDefault'_transp
      | exact: transp2 | ]. 
    intros H'''; move; simpl. intros yx.
     rewrite -[LHS](proj2 (proj2_sig Yoneda01_E)).
    move: transp2 H''' yx. set wvf := ((wv :>Generator) o>Generator_ f). intros transp2 H''' yx.
     cbn beta delta [Yoneda10_PolyElement_default]. 
    set yx_' := sval (viewingDefault'_transp H' wvf) H''' yx.
     simpl.  unfold   Yoneda10_PolyElement_default.
    move: (Yoneda00_ViewedFunctor_quotient_rev (Logic.eq_sym (Yoneda10_ee_morphism _ _ (wv :>Generator) f _ (projT2 (projT1 yx_'))))) => Yoneda10_ee_morphism_transp.
    rewrite [LHS](proj2_sig Yoneda10_ee_morphism_transp).  simpl. 
    apply: (Yoneda10_PolyElement_default_modulo Yoneda10_ee_natural Yoneda10_ee_real). 

    abstract (repeat rewrite -(proj2_sig (Yoneda10_realize _));
    rewrite (proj2 (proj2_sig transp2));
    rewrite (proj2 (proj2_sig (sval Yoneda10_ee_morphism_transp)));
    rewrite (proj2_sig (sval (V_transp G H' (wv :>Generator) f) (projT1 (projT1 yx_'))
                      (projT2 (projT1 yx_'))) ) /=;
    rewrite [X in X o>Generator (wv :>Generator)](proj2 (proj2_sig (V_transp G H' (wv :>Generator) f)));
    rewrite -[((w0 :>Generator) o>Generator_ (v0 :>Generator))]/((sval (viewingDefault'_transp G f) H' wv) :>Generator);
    rewrite (proj2 (proj2_sig (viewingDefault'_transp G f)));
    rewrite [LHS]polyGenerator_morphism; 
    rewrite -[((projT2 yx_' :>Generator) o>Generator (projT2 (projT1 yx_') :>Generator))]/(yx_' :>Generator);
    rewrite (proj2 (proj2_sig (viewingDefault'_transp H' wvf)));
    (*   (yx :>Generator) o>Generator (wv :>Generator) = ... *) reflexivity).
    }

    rewrite -[LHS]polyelement_to_element_to_polyelement.
    rewrite -[RHS]polyelement_to_element_to_polyelement. rewrite lem1. reflexivity.
*)
    (**
ee_ ((w o> v) o> f) x y  = y o> x o> ( ( w o> v ) o> f )  =  y o> (x o> (w o> v)) o> f 
==
ee_ f (w o> v) (y o> x)  = ( y o> x ) o> ( w o> v ) o> f    =  y o> (x o> (w o> v)) o> f  **)
    
  - (* PolyTransf'PolyElement *)
    intros. move. intros f. simpl.
    unshelve eapply Yoneda00_ViewedFunctor_quotient
    with (W:= (Viewing_F G f)); 
      [ exact: identity_transpViewing
      | exact: real_transpViewing | ].
    intros; move; simpl; intros; rewrite (proj1 (proj2_sig Yoneda01_F));
      rewrite -polyGenerator_unitGenerator; reflexivity.

(** ----- the constant conversions which are derivable by using the finished cut-elimination lemma ----- **)

    (**  - (* PolyCoMod_morphism *) intros. move. intros f.
    reflexivity (* associativity of function composition *). **)
Time Qed. (* /!\ TIME QED 201s *)
(** # #
#+END_SRC

** Linear total/asymptotic grade and the degradation lemma

  As is common , the grade of the composition constructor [PolyCoMod] is defined as the double of the (sucessor of the) sum of the grades of its arguments ; such doubling is such that for each of the polymorphism conversion-constructors , the enclosing/outer constructor in the contractum has less « effect » than itself in the redex . For example , this polymorphism conversion [(ConstructorX (atomA o> atomB))  <~~  ((ConstructorX atomA) o> atomB)] will produce the degradation [(1 + (2 + 2 + 2))  <  ((2 + 2) + 2 + 2)] . 

  Memo that the grade of the reflector/copairing-constructors [PolyTransf] and [PolyTransf_default] are defined identically , as some (successor of the) maximum of the grades of the component transformations over (only) the viewing-elements .

  Elsewhere , memo that if the conversion-relation constructor [convCoMod_Refl] was absent , then oneself would get some degradation lemma with tight/strict less-than : [( grade ff0 < grade ff )] ; this is the tight/strict-degrading which will occur during the polymorphism/cut-elimination resolution ( by the automatic-arithmetic-tactic calls therein ) .

#+BEGIN_SRC coq :exports both :results silent # # **)
Notation max m n := ((Nat.add m (Nat.sub n m))%nat).
Arguments Nat.sub : simpl nomatch.
Arguments Nat.add : simpl nomatch.

Fixpoint grade
Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E)
     Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F)
     Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)) {struct ff} : nat . 
Proof.
  case : Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E  E 
     Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F  F
     Yoneda10_ff viewingContinuous_ff / ff .
  - (* PolyCoMod *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F' F' Yoneda10_ff' viewingContinuous_ff' ff' Yoneda00_F'' Yoneda01_F''
                           Viewing_F'' Viewing_data_F'' Viewing_transp_F'' F'' Yoneda10_ff_ viewingContinuous_ff_ ff_.
    exact: ( 2 * (S (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  ff' + grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  ff_)%nat ) )%nat .
  - (* UnitCoMod *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F.
 
    exact: (S ( (* gradeOb F = *) O )).
  - (* View1 *)  intros G H g.
    exact: (S O).
  - (* ViewedFunctor1 *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff.
    exact: (S (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  ff)).
  - (*  UnitViewedFunctor *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff.
    exact: (S (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  ff)).
  - (* PolyElement *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F G f H v.

    exact: (S (S O)).
  - (* PolyTransf *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural
                            Yoneda10_ee_morphism Yoneda10_ee_real ee_.
    exact: (S (S (max (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  (@ee_ (Finiteness.G1 isFiniteness_F ) (Finiteness.f1 isFiniteness_F ) (Finiteness.H1 isFiniteness_F ) (Finiteness.v1 isFiniteness_F )))
                      (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  (@ee_ (Finiteness.G2 isFiniteness_F ) (Finiteness.f2 isFiniteness_F ) (Finiteness.H2 isFiniteness_F ) (Finiteness.v2 isFiniteness_F ))) ))).
  - (* PolyTransf_default *) intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural
                                    Yoneda10_ee_morphism Yoneda10_ee_real ee_ projT1_sval_Yoneda10_ee_ viewingDefault'_ viewingDefault'_data viewingDefault'_transp viewingDefault'_isFiniteness viewingDefault'_poly_transp.
    exact: (S (S (max (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  (@ee_ (Finiteness.G1 isFiniteness_F ) (Finiteness.f1 isFiniteness_F ) (Finiteness.H1 isFiniteness_F ) (Finiteness.v1 isFiniteness_F )))
                      (grade _ _ _ _ _ _ _ _ _ _ _ _ _ _  (@ee_ (Finiteness.G2 isFiniteness_F ) (Finiteness.f2 isFiniteness_F ) (Finiteness.H2 isFiniteness_F ) (Finiteness.v2 isFiniteness_F ))) ))).
Defined.

Lemma grade_gt0 :
forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E)
     Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F)
     Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
      ((S O) <= (grade ff))%nat.
Proof.
  intros; case : ff; intros; simpl in *; abstract (Lia.lia).
Qed.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
                        gg4 : 'CoMod( _ ~> _ @ _ @~ _ ) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg3)
                                          (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg4)
  | [ gg1 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
                  gg3 : 'CoMod( _ ~> _ @ _ @~ _ ) |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
                                          (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg3)
  | [ gg1 : 'CoMod( _ ~> _ @ _ @~ _ ) ,
            gg2 : 'CoMod( _ ~> _ @ _ @~ _ )  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg2)
  | [ gg1 : 'CoMod( _ ~> _ @ _ @~ _ )  |- _ ] =>
    move : (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ gg1) 
  end.

Ltac tac_grade_gt0_indexing :=
match goal with
| [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
    gg1 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
         (v : 'Generator( H ~> G | (?Viewing_F G f) )), 'CoMod( _ ~> _ @ _ @~ _ )),
    gg2 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
         (v : 'Generator( H ~> G | (?Viewing_F G f) )), 'CoMod( _ ~> _ @ _ @~ _ ))
    |- _ ] => move:
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 (Finiteness.G1 isFiniteness_F) (Finiteness.f1 isFiniteness_F) (Finiteness.H1 isFiniteness_F) (Finiteness.v1 isFiniteness_F)))
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 (Finiteness.G2 isFiniteness_F) (Finiteness.f2 isFiniteness_F) (Finiteness.H2 isFiniteness_F) (Finiteness.v2 isFiniteness_F)))
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg2 (Finiteness.G1 isFiniteness_F) (Finiteness.f1 isFiniteness_F) (Finiteness.H1 isFiniteness_F) (Finiteness.v1 isFiniteness_F)))
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg2 (Finiteness.G2 isFiniteness_F) (Finiteness.f2 isFiniteness_F) (Finiteness.H2 isFiniteness_F) (Finiteness.v2 isFiniteness_F)))
| [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
   gg1 : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
        (v : 'Generator( H ~> G | (?Viewing_F G f) )), 'CoMod( _ ~> _ @ _ @~ _ ))
   |- _ ] => move:
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 (Finiteness.G1 isFiniteness_F) (Finiteness.f1 isFiniteness_F) (Finiteness.H1 isFiniteness_F) (Finiteness.v1 isFiniteness_F)))
              (@grade_gt0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          (@gg1 (Finiteness.G2 isFiniteness_F) (Finiteness.f2 isFiniteness_F) (Finiteness.H2 isFiniteness_F) (Finiteness.v2 isFiniteness_F)))
end.

Ltac tac_indexed_all :=
  repeat match goal with
         | (* this match shall be above , for [PolyTransf_default_PolyElement] *)
         [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
           wv : 'Generator( ?H' ~> ?G | (?viewingDefault'_ ?G ?f) )
           |- context [(((projT2 (sval (?viewingDefault'_poly_transp ?G ?f) ?H' ?wv)) :>Generator) o>Generator (projT2 (projT1 (sval (?viewingDefault'_poly_transp ?G ?f) ?H' ?wv))) | (?Viewing_F ?G ?f))] ] =>
         (move: (((projT2 (sval (viewingDefault'_poly_transp G f) H' wv)) :>Generator) o>Generator (projT2 (projT1 (sval (viewingDefault'_poly_transp G f) H' wv))) | (Viewing_F G f))); clear wv; intros tmp;
         destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F tmp)
         | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
             v : 'Generator( ?H ~> ?G | (?Viewing_F ?G ?f) )
             |- context [max _ _] ] =>
           destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F v)
         | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
             Hgrade : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                             (v : 'Generator( H ~> G | (?Viewing_F G f) )),
                              ( _ <= _ )%nat) |- context [max _ _] ] =>
           move: {Hgrade} (Hgrade (Finiteness.G1 isFiniteness_F) (Finiteness.f1 isFiniteness_F) (Finiteness.H1 isFiniteness_F) (Finiteness.v1 isFiniteness_F) )
                          (Hgrade (Finiteness.G2 isFiniteness_F) (Finiteness.f2 isFiniteness_F) (Finiteness.H2 isFiniteness_F) (Finiteness.v2 isFiniteness_F) );
           simpl
         end.

Lemma degrade :
 forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
   (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
 forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
   (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
 forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
 forall Yoneda10_ff0 viewingContinuous_ff0 (ff0 : 'CoMod( E ~> F @ Yoneda10_ff0 @~ viewingContinuous_ff0)),
   ff0 <~~ ff ->  ( grade ff0 <= grade ff )%nat .
Proof.
  Time intros until ff0; intros red_ff; induction red_ff;
  try solve [intros; simpl; try tac_grade_gt0; try tac_grade_gt0_indexing; tac_indexed_all;
               intros; abstract Lia.lia]. (* 10s *)
Qed.

Ltac tac_degrade H_grade :=
  intuition idtac;
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
           move : (degrade Hred) ; clear Hred
         | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F ,
             Hred : (forall (G : obGenerator) (f : ?Yoneda00_F G) (H : obGenerator)
                       (v : 'Generator( H ~> G | (?Viewing_F G f) )),
                        ( _ <~~ _ )%poly) |- _ ] =>
           move: {Hred} (degrade (Hred (Finiteness.G1 isFiniteness_F) (Finiteness.f1 isFiniteness_F) (Finiteness.H1 isFiniteness_F) (Finiteness.v1 isFiniteness_F)))
                        (degrade (Hred (Finiteness.G2 isFiniteness_F) (Finiteness.f2 isFiniteness_F) (Finiteness.H2 isFiniteness_F) (Finiteness.v2 isFiniteness_F)))
         end;
  move: H_grade; clear; simpl;
  intros; try tac_grade_gt0; try tac_grade_gt0_indexing;
  intros; Lia.lia.
(** # #
#+END_SRC

* Solution morphisms

  As common, the polymorphism cut-constructor [PolyCoMod] is not part of the solution terminology .

** Solution morphisms without polymorphism

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Sol.
Section Section1.
Delimit Scope sol_scope with sol.

Inductive morCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ff : Yoneda10_data Yoneda01_F Yoneda01_E)
        (viewingContinuous_ff : viewingContinuous Viewing_F Viewing_E Yoneda10_ff), Type :=

| UnitCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    'CoMod( F ~> F @ Yoneda10_UnitCoMod Yoneda01_F @~ viewingContinuous_UnitCoMod Yoneda01_F Viewing_F )

| View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    'CoMod( View H ~> View G @ Yoneda10_View1 g @~ viewingContinuous_View1 g)

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)),
      'CoMod( ViewedFunctor E ~> ViewedFunctor F @ Yoneda10_ViewedFunctor1 Yoneda10_ff @~ viewingContinuous_ViewedFunctor1 viewingContinuous_ff ) 

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
      'CoMod( E ~> ViewedFunctor F @ Yoneda10_UnitViewedFunctor Yoneda10_ff @~ viewingContinuous_UnitViewedFunctor Viewing_transp_F viewingContinuous_ff )

| PolyElement : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
      'CoMod( View H ~> ViewingFunctor isFiniteness_F
                   @ Yoneda10_PolyElement Yoneda01_F v @~ viewingContinuous_PolyElement Viewing_transp_F v )

| PolyTransf : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                                 Yoneda10_data (Yoneda01_View H) Yoneda01_E),
      forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              viewingContinuous (@Viewing_View H) Viewing_E (Yoneda10_ee_ G f H v)),
      forall (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) Yoneda01_E
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v))),
      forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v'))),
      forall (Yoneda10_ee_real : 
       forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (Viewing_F G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
      'CoMod( ViewingFunctor isFiniteness_F ~> ViewedFunctor E @ Yoneda10_PolyTransf Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real @~ viewingContinuous_PolyTransf Viewing_data_F viewingContinuous_ee_  Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real )

| PolyTransf_default : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                               Yoneda10_data (Yoneda01_View H)  (Yoneda01_ViewedFunctor Yoneda01_E) ),
    forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
            viewingContinuous (@Viewing_View H) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v)),
    forall (Yoneda10_ee_natural :
       forall (G : obGenerator) (f : Yoneda00_F G),
         Yoneda10_natural (Yoneda01_Viewing (Viewing_F G f)) (Yoneda01_ViewedFunctor Yoneda01_E)
                          (fun (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )) =>
                             polyelement_to_element (Yoneda10_ee_ G f H v))),
    forall (Yoneda10_ee_morphism :
       forall (G G' : obGenerator) (g : 'Generator( G' ~> G )) (f : Yoneda00_F G),
         forall (H : obGenerator) (v' : 'Generator( H ~> G' | intersecViewing (Viewing_F G f) g )),
           polyelement_to_element (Yoneda10_ee_ G f H (fst (sval v'))) =
           polyelement_to_element (Yoneda10_ee_ G' (g o>Generator_[sval Yoneda01_F] f) H (sval (Viewing_transp_F G G' g f) H v'))),
    forall (Yoneda10_ee_real :
                forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v v' : 'Generator( H ~> G | (Viewing_F G f) )),
         ((v :>Generator) = (v' :>Generator)) ->
         polyelement_to_element (Yoneda10_ee_ G f H v)
         = polyelement_to_element (Yoneda10_ee_ G f H v') ),
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) ),
        let projT1_sval_Yoneda10_ee_ G f H v
            := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
        forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
          (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
          (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
          (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
        forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
          'CoMod( ViewingFunctor viewingDefault'_isFiniteness ~> ViewedFunctor E
                                 @ (Yoneda10_PolyTransf_default Viewing_data_F Yoneda10_ee_natural Yoneda10_ee_morphism  Yoneda10_ee_real)
                                 @~ viewingContinuous_PolyTransf_default Viewing_data_F Viewing_transp_E viewingContinuous_ee_  Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real viewingDefault'_poly_transp)

where "''CoMod' (  F'  ~>  F  @  Yoneda10_ff  @~  viewingContinuous_ff  )" :=
        (@morCoMod _ _ _ _ _ F' _ _ _ _ _ F Yoneda10_ff viewingContinuous_ff) : sol_scope. 

End Section1.

Module Export Ex_Notations.
Delimit Scope sol_scope with sol.

Notation "''CoMod' (  F'  ~>  F  @  Yoneda10_ff  @~  viewingContinuous_ff  )" :=
        (@morCoMod _ _ _ _ _ F' _ _ _ _ _ F Yoneda10_ff viewingContinuous_ff) : sol_scope. 

Notation "''CoMod' (  F'  ~>  F  )" := (@morCoMod _ _ _ _ _ F' _ _ _ _ _ F _ _ )
       (at level 0, only parsing) : sol_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod _ _ _ _ _ F)
                                 (at level 10, only parsing) : sol_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _ _ _ _ _ _) (at level 0) : sol_scope.

Notation "''View1' g" := (@View1 _ _ g)
                   (at level 10, g at next level) : sol_scope.

Notation "''ViewedFunctor1' ee" := (@ViewedFunctor1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee)
                   (at level 10, ee at next level) : sol_scope.

Notation "ff o>CoMod 'UnitViewedFunctor" := (@UnitViewedFunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff)
                  (at level 4, right associativity) : sol_scope.

Notation "''PolyElement'  v  @  isFiniteness_F" :=
  (@PolyElement _ _ _ _ _ isFiniteness_F _ _ _ v) (at level 10, v, isFiniteness_F at next level) : sol_scope.

Notation "[[  ee_  @  isFiniteness_F  ,  Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_real  ]]" :=
  (@PolyTransf _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_ )
    (at level 4, ee_ , isFiniteness_F , Yoneda10_ee_natural, Yoneda10_ee_morphism, Yoneda10_ee_real at next level ) : sol_scope.

Notation "[[  ee_  @  isFiniteness_F  ]]" :=
  (@PolyTransf _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ _ _ _ ee_ )
    (at level 4, ee_ , isFiniteness_F at next level ) : sol_scope.

Notation "[[[  ee_  @  isFiniteness_F , Yoneda10_ee_natural  ,  Yoneda10_ee_morphism  ,  Yoneda10_ee_real  ,  viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]]" :=
  (@PolyTransf_default _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_ _ _ _ viewingDefault'_isFiniteness viewingDefault'_poly_transp)
    (at level 4, ee_ , isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp at next level ) : sol_scope.

Notation "[[[  ee_  @  isFiniteness_F ,  viewingDefault'_isFiniteness ]]]" :=
  (@PolyTransf_default _ _ _ _ _ isFiniteness_F _ _ _ _ _ _ _ _ _ _ _ ee_ _ _ _ viewingDefault'_isFiniteness _)
    (at level 4, ee_ , isFiniteness_F , viewingDefault'_isFiniteness at next level ) : sol_scope.
End Ex_Notations.

Fixpoint toPolyMor
         Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E)
         Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F)
      Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff) %sol) {struct ff}
      : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff) %poly .
Proof.
  refine
    match ff with
    | ( @'UnitCoMod F )%sol => ( @'UnitCoMod F )%poly
    | ( 'View1 g )%sol => ( 'View1 g )%poly
    | ( 'ViewedFunctor1 ee )%sol => ( 'ViewedFunctor1 (toPolyMor _ _ _ _ _ _ _ _ _ _ _ _ _ _ ee) )%poly
    | ( ff o>CoMod 'UnitViewedFunctor )%sol => ( (toPolyMor _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff) o>CoMod 'UnitViewedFunctor )%poly
    | ( 'PolyElement v  @ isFiniteness_F)%sol => ( 'PolyElement v  @ isFiniteness_F )%poly
    | ( [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]]%sol )%sol =>
      ( [[ ( fun G f H v => (toPolyMor _ _ _ _ _ _ _ _ _ _ _ _ _ _  (ee_ G f H v)) )
             @  isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]] )%poly
    | ( [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]]%sol )%sol =>
      ( [[[ ( fun G f H v => (toPolyMor _ _ _ _ _ _ _ _ _ _ _ _ _ _  (ee_ G f H v)) )
             @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]] )%poly
    end.
Defined.
(** # #
#+END_SRC

** Destruction of morphisms with inner-instantiation of object-indexes

  As common , the polymorphism/cut-elimination resolution will require the destruction of some morphism which is constrained by the structure of its domain/codomain objects .

  Memo that in this ongoing COQ program for colimits , oneself starts to general-destruct the postfix-parameter [f'] of the composition [(f_ o>CoMod f')] and then to constrained-destruct (filter the admissible inputs) the prefix-argument [f_] . This may be more sensible ...

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Destruct_codomView.

Inductive morCoMod_codomView
: forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall (G : obGenerator), forall Yoneda10_ff viewingContinuous_ff,
        'CoMod( F ~> (View G) @ Yoneda10_ff @~ viewingContinuous_ff ) %sol -> Type :=

| UnitCoMod :  forall G : obGenerator, 
    morCoMod_codomView ( ( @'UnitCoMod (View G) )%sol )

|  View1 : forall (G H : obGenerator) (g : 'Generator( H ~> G )),
    morCoMod_codomView ( ( 'View1 g )%sol ) .

Lemma morCoMod_codomViewP
  :  forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff) %sol), 
      ltac:( destruct F; [ | refine (unit : Type) .. ];
               refine (morCoMod_codomView ff) ).
Proof.
  intros. destruct ff.
  - destruct F; [ | intros; exact: tt .. ].
    constructor 1.
  - constructor 2.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
Defined.
End Destruct_codomView.
  
Module Destruct_codomViewingFunctor.

Inductive morCoMod_codomViewingFunctor :
   forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
   forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
     (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
     (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
     (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
     (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
   forall Yoneda10_ff viewingContinuous_ff,
       'CoMod( E ~> ViewingFunctor isFiniteness_F @ Yoneda10_ff @~ viewingContinuous_ff ) %sol -> Type :=

| UnitCoMod : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
     (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
     (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
     (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
     (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      morCoMod_codomViewingFunctor ( @'UnitCoMod (ViewingFunctor isFiniteness_F) )%sol

| PolyElement : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall (G : obGenerator) (f : Yoneda00_F G) (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
      morCoMod_codomViewingFunctor ('PolyElement v @ isFiniteness_F )%sol .

Lemma morCoMod_codomViewingFunctorP
  :  forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff) %sol), 
      ltac:( destruct F ; [ refine (unit : Type) | | refine (unit : Type) ];
               refine (morCoMod_codomViewingFunctor ff) ).
Proof.
  intros. destruct ff.
  - destruct F; [ intros; exact: tt | | intros; exact: tt ].
    constructor 1.
  - intros; exact: tt.
  - intros; exact: tt.
  - intros; exact: tt.
  - constructor 2.
  - intros; exact: tt.
  - intros; exact: tt.
Defined. 
End Destruct_codomViewingFunctor.

Module Destruct_codomViewedFunctor.

Inductive morCoMod_codomViewedFunctor :
  forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
    (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
  forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
    (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
  forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> ViewedFunctor F @ Yoneda10_ff @~ viewingContinuous_ff) %sol), Type :=

| UnitCoMod : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
    (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
      morCoMod_codomViewedFunctor ( @'UnitCoMod (ViewedFunctor F) )%sol

| ViewedFunctor1 : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                     (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)%sol),
      morCoMod_codomViewedFunctor ( 'ViewedFunctor1 ff )%sol

| UnitViewedFunctor : forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
                       (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)%sol),
      morCoMod_codomViewedFunctor ( ff o>CoMod 'UnitViewedFunctor)%sol

| PolyTransf : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
      forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
      forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                                 Yoneda10_data (Yoneda01_View H) Yoneda01_E),
      forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              viewingContinuous (@Viewing_View H) Viewing_E (Yoneda10_ee_ G f H v)),
      forall Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real,
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
          'CoMod( View H ~> E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) %sol ),
      morCoMod_codomViewedFunctor ( [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]] )%sol

| PolyTransf_default : forall (Yoneda00_F : obGenerator -> Type) (Yoneda01_F : Yoneda01_data Yoneda00_F)
                 (Viewing_F : forall G : obGenerator, Yoneda00_F G -> obViewing G)
                 (Viewing_data_F : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (Viewing_F G f))
                 (Viewing_transp_F : viewingFunctor Yoneda01_F Viewing_F)
                 (isFiniteness_F : Finiteness.isFiniteness_ Viewing_data_F Viewing_transp_F),
    forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
      (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall (Yoneda10_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator), 'Generator( H ~> G | (Viewing_F G f) ) ->
                               Yoneda10_data (Yoneda01_View H)  (Yoneda01_ViewedFunctor Yoneda01_E) ),
    forall (viewingContinuous_ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
          forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
            viewingContinuous (@Viewing_View H) (Viewing_ViewedFunctor Viewing_E) (Yoneda10_ee_ G f H v)),
    forall Yoneda10_ee_natural  Yoneda10_ee_morphism Yoneda10_ee_real ,
      forall (ee_ : forall (G : obGenerator) (f : Yoneda00_F G),
            forall (H : obGenerator) (v : 'Generator( H ~> G | (Viewing_F G f) )),
              'CoMod( View H ~> ViewedFunctor E @ Yoneda10_ee_ G f H v @~ viewingContinuous_ee_ G f H v ) %sol),
        let projT1_sval_Yoneda10_ee_ G f H v
            := (projT1 (sval (polyelement_to_element (Yoneda10_ee_ G f H v)))) in 
        forall (viewingDefault'_ : forall (G : obGenerator) (f : Yoneda00_F G), obViewing G)
          (viewingDefault'_data : forall (G : obGenerator) (f : Yoneda00_F G), viewingData (viewingDefault'_ G f))
          (viewingDefault'_transp : viewingFunctor Yoneda01_F viewingDefault'_)
          (viewingDefault'_isFiniteness : Finiteness.isFiniteness_ viewingDefault'_data viewingDefault'_transp),
        forall (viewingDefault'_poly_transp : forall G f, transpViewing (viewingDefault'_ G f) (viewingDefault_ projT1_sval_Yoneda10_ee_ f)),
      morCoMod_codomViewedFunctor ( [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]] )%sol
.

Lemma morCoMod_codomViewedFunctorP
  :  forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff) %sol), 
      ltac:( destruct F ; [ refine (unit : Type) .. | ];
               refine (morCoMod_codomViewedFunctor ff) ).
Proof.
  intros. destruct ff.
  - destruct F; [ intros; exact: tt .. | ].
    constructor 1.
  - intros; exact: tt.
  - constructor 2.
  - constructor 3.
  - intros; exact: tt.
  - econstructor 4.
  - econstructor 5.
Defined. 
End Destruct_codomViewedFunctor.
End Sol.
(** # #
#+END_SRC

* Polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

  As common , this resolution is not programmed by morphisms-structural recursion but instead is programmed by grade-structural recursion .

  In contrast , this resolution also computes the sense-decoding datatype-index/argument of the resolved morphism , this datatype-index/argument is inferred as metavariable from the actual resolved morphism via the [eexists] tactic . The technical progress of this resolution does require the earlier lemma [convCoMod_sense] , which will only be used during the polymorphism/cut-elimination resolution [solveCoMod] to show/transfer the logical-properties of some real polymorph-cocones ( [Yoneda10_ee_natural] , [Yoneda10_ee_morphism] , [Yoneda10_ee_real] ) and to show/transfer the polymorphism of some viewings-for-default-colimiting ( [viewingDefault'_transp] ) .

  This COQ program and deduction is mostly-automated ; but memo that COQ lacks inductive-recursive presentations and memo that here the automation-tactics use only logical eauto-resolution because COQ lacks some more-efficient heterogeneous-rewriting tactics , because the conversion-relation do convert across two morphisms whose sense-decoding indexes are not syntactically/grammatically-the-same .

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Resolve.
Export Sol.Ex_Notations.

Ltac tac_reduce := simpl in * ; intuition eauto.

Fixpoint solveCoMod len {struct len} :
 forall Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E
        (E : @obCoMod Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E),
    forall Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F
      (F : @obCoMod Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F),
    forall Yoneda10_ff viewingContinuous_ff (ff : 'CoMod( E ~> F @ Yoneda10_ff @~ viewingContinuous_ff)), 
  forall grade_ff : (grade ff <= len)%nat,
    { ffSol : { Yoneda10_ffSol : _ &  { viewingContinuous_ffSol : _ & 'CoMod( E ~> F @ Yoneda10_ffSol @~ viewingContinuous_ffSol )%sol} }
    | (Sol.toPolyMor (projT2 (projT2 ffSol))) <~~ ff } .
Proof.
case : len => [ | len ].

(** len is O **)
- intros Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda10_ff viewingContinuous_ff ff grade_ff.
  exfalso; clear - grade_ff; abstract tac_degrade grade_ff.

(** len is (S len) **)
- intros Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda10_ff viewingContinuous_ff ff .
  case : Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda10_ff viewingContinuous_ff / ff;
  [ intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_F' Yoneda01_F' Viewing_F' Viewing_data_F' Viewing_transp_F' F' Yoneda10_ff' viewingContinuous_ff' ff' Yoneda00_F'' Yoneda01_F''
         Viewing_F'' Viewing_data_F'' Viewing_transp_F'' F'' Yoneda10_ff_ viewingContinuous_ff_ ff_ grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F grade_ff
  | intros G H g grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F G f H v grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism
         Yoneda10_ee_real ee_ grade_ff
  | intros Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism
         Yoneda10_ee_real ee_ projT1_sval_Yoneda10_ee_ viewingDefault'_ viewingDefault'_data viewingDefault'_transp viewingDefault'_isFiniteness viewingDefault'_poly_transp grade_ff ].

(** ff is ff_ o>CoMod ff' *)
all: cycle 1.
(** ff is @'UnitCoMod F **)
+ unshelve eexists. do 2 eexists. refine ( @'UnitCoMod F )%sol.
  clear; abstract exact: convCoMod_Refl.

(** ff is 'View1 g **)
+ unshelve eexists. do 2 eexists. refine ( 'View1 g )%sol.
  clear; abstract exact: convCoMod_Refl.

(** ff is 'ViewedFunctor1 ff **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb)))
          (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))))
          (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb)))) ffSol_transp 
  => Yoneda10_ffSol viewingContinuous_ffSol ffSol ffSol_transp .

  unshelve eexists. do 2 eexists. refine ( 'ViewedFunctor1 ffSol )%sol.
  move: ffSol_transp; clear; abstract tac_reduce.

(** ff is ff o>CoMod 'UnitViewedFunctor **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb)))
          (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb))))
          (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff blurb)))) ffSol_transp 
  => Yoneda10_ffSol viewingContinuous_ffSol ffSol ffSol_transp .

  unshelve eexists. do 2 eexists. refine ( ffSol o>CoMod 'UnitViewedFunctor )%sol.
  move: ffSol_transp; clear; abstract tac_reduce.

(** ff is 'PolyElement v @ isFiniteness_F **)
+ unshelve eexists. do 2 eexists. refine ( 'PolyElement v @ isFiniteness_F )%sol.
  clear; abstract exact: convCoMod_Refl.

(** [[  ee_  @  isFiniteness_F  ]] **)
+ have [:blurb_] eeSol_transp G f H (v : 'Generator( H ~> G | (Viewing_F G f) )) :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)));
      first by clear -grade_ff;
      abstract((move => G f H v);
               match goal with
               | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F |- _ ] =>
                 destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F  v)
               end;
               tac_degrade grade_ff).
    
  have @Yoneda10_eeSol_ := (fun G f H v =>
     projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)))).
  have @viewingContinuous_eeSol_ : (forall G f H v, viewingContinuous _ _ (Yoneda10_eeSol_ G f H v) )
    := (fun G f H v => projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v))))).
  have @eeSol_ : (forall G f H v, 'CoMod( View H ~> E @ Yoneda10_eeSol_ G f H v @~ viewingContinuous_eeSol_ G f H v ) %sol)
    := (fun G f H v => projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                (ee_(G)(f)(H)(v)) (blurb_ G f H v))))) .
  have {eeSol_transp}: (forall G f H v,
                         Sol.toPolyMor (eeSol_(G)(f)(H)(v)) <~~ ee_(G)(f)(H)(v)) := eeSol_transp.
  move: Yoneda10_eeSol_ viewingContinuous_eeSol_ eeSol_ => Yoneda10_eeSol viewingContinuous_eeSol_ eeSol_ eeSol_transp.
  clear solveCoMod.
  unshelve eexists. do 2 eexists.
  refine ( [[  eeSol_  @  isFiniteness_F  ,  _   ,  _  ,  _  ]] %sol ).

  (**memo: convCoMod_sense is really necessary here for Yoneda10_eeSol_natural Yoneda10_eeSol_morphism Yoneda10_eeSol_real  **)
  (* Yoneda10_eeSol_natural *)
  { clear -Yoneda10_ee_natural eeSol_transp;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v)) => eeSol_transp_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_transp_eq; exact: Yoneda10_ee_natural ).
  }
  (* Yoneda10_eeSol_morphism *)
  { clear -Yoneda10_ee_morphism eeSol_transp;
    abstract (move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v))
              => eeSol_transp_eq; intros; move;
                rewrite /= /polyelement_to_element /= ; intros;
                do 2 rewrite -eeSol_transp_eq ; exact: Yoneda10_ee_morphism).
  }
  (* Yoneda10_eeSol_real *)
  { clear -Yoneda10_ee_real eeSol_transp;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v)) => eeSol_transp_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_transp_eq; exact: Yoneda10_ee_real ).
  }

  simpl; move: eeSol_transp; clear; simpl; abstract tac_reduce.
  
(** [[[  ee_  @  isFiniteness_F ]]] **)
+ have [:blurb_] eeSol_transp G f H (v : 'Generator( H ~> G | (Viewing_F G f) )) :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)));
      first by clear -grade_ff;
      abstract((move => G f H v);
               match goal with
               | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F  |- _ ] =>
                 destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F  v)
               end;
               tac_degrade grade_ff).
    
  have @Yoneda10_eeSol_ := (fun G f H v => projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v)))).
  have @viewingContinuous_eeSol_ : (forall G f H v, viewingContinuous _ _ (Yoneda10_eeSol_ G f H v) )
    := (fun G f H v => projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ee_(G)(f)(H)(v)) (blurb_ G f H v))))).
  have @eeSol_ : (forall G f H v, 'CoMod( View H ~> ViewedFunctor E  @ Yoneda10_eeSol_ G f H v @~ viewingContinuous_eeSol_ G f H v) %sol)
    := (fun G f H v => projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                (ee_(G)(f)(H)(v)) (blurb_ G f H v))))) .
  have {eeSol_transp}: (forall G f H v, Sol.toPolyMor (eeSol_(G)(f)(H)(v)) <~~ ee_(G)(f)(H)(v)) := eeSol_transp.
  move: Yoneda10_eeSol_ viewingContinuous_eeSol_ eeSol_ => Yoneda10_eeSol viewingContinuous_eeSol_ eeSol_ eeSol_transp.
  clear solveCoMod.
  unshelve eexists. do 2 eexists.
  refine ( [[[  eeSol_  @  isFiniteness_F , _  ,  _  ,  _  ,  viewingDefault'_isFiniteness , _ ]]] %sol ).

  (**memo: convCoMod_sense is really necessary here for Yoneda10_eeSol_natural Yoneda10_eeSol_morphism Yoneda10_eeSol_real  viewingDefault'_transpSol **)
  (* Yoneda10_eeSol_natural *)
  { clear -Yoneda10_ee_natural eeSol_transp;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v)) => eeSol_transp_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_transp_eq; exact: Yoneda10_ee_natural ).
  }
  (* Yoneda10_eeSol_morphism *)
  { clear -Yoneda10_ee_morphism eeSol_transp;
    abstract (move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v))
              => eeSol_transp_eq; intros; move;
                rewrite /= /polyelement_to_element /= ; intros;
                do 2 rewrite -eeSol_transp_eq ; exact: Yoneda10_ee_morphism).
  }
  (* Yoneda10_eeSol_real *)
  { clear -Yoneda10_ee_real eeSol_transp;
    abstract( move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v)) => eeSol_transp_eq;
      intros; move; rewrite /= /polyelement_to_element /= ; intros;
      do 2 rewrite -eeSol_transp_eq; exact: Yoneda10_ee_real ).
  }
  (* viewingDefault'_poly_transpSol  *)
  { clear -viewingDefault'_poly_transp eeSol_transp.
    abstract ((move : (fun G f H v => convCoMod_sense (eeSol_transp G f H v)) => eeSol_transp_eq);
    intros; apply: (composition_transpViewing (viewingDefault'_poly_transp _ _));
    apply: identity_transpViewing_innerViewing;
      intros; simpl; congr (projT1 (sval _)); exact: eeSol_transp_eq).
  } 

  simpl; move: eeSol_transp; clear; simpl; abstract tac_reduce.

(** ff is ff_ o>CoMod ff' *)
+ have [:blurb] ff'Sol_transp :=
    (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' blurb)))
          (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' blurb))))
          (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff' blurb)))) ff'Sol_transp 
  => Yoneda10_ff'Sol viewingContinuous_ff'Sol ff'Sol ff'Sol_transp .
  have [:blurb] ff_Sol_transp :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ blurb));
        first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ blurb)))
          (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ blurb))))
          (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff_ blurb)))) ff_Sol_transp 
  => Yoneda10_ff_Sol viewingContinuous_ff_Sol ff_Sol ff_Sol_transp .

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  **)
  destruct ff'Sol as
      [ Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F
      | G H g 
      | Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff
      | Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ff viewingContinuous_ff ff
      | Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F G f H v
      | Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism
         Yoneda10_ee_real ee_
      | Yoneda00_F Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E Yoneda10_ee_ viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism
         Yoneda10_ee_real ee_ projT1_sval_Yoneda10_ee_ viewingDefault'_ viewingDefault'_data viewingDefault'_transp viewingDefault'_isFiniteness viewingDefault'_poly_transp ] .

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod (@'UnitCoMod F)) **)
  * unshelve eexists. do 2 eexists. refine (ff_Sol)%sol.
    move:ff_Sol_transp ff'Sol_transp; clear;
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
      - unshelve eexists. do 2 eexists. refine ('View1 g)%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ('View1 g)); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( 'View1 _g ) o>CoMod ( 'View1 g )) **)
      - unshelve eexists. do 2 eexists.
        refine ( 'View1 (_g o>Generator g) )%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                                   (uTrans := ('View1 _g) o>CoMod ('View1 g)); tac_reduce).
    } 

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'ViewedFunctor1 ff )) **)
  * move:  (Sol.Destruct_codomViewedFunctor.morCoMod_codomViewedFunctorP ff_Sol) => ff_Sol_codomViewedFunctorP.
    { destruct ff_Sol_codomViewedFunctorP as
          [ _Yoneda00_F _Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F _F
          | _Yoneda00_F _Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F _F
                       Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E
                       _Yoneda10_ff _viewingContinuous_ff _ff
          | _Yoneda00_F _Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F _F
                       Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E
                       _Yoneda10_ff _viewingContinuous_ff _ff
          | _Yoneda00_F _Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F isFiniteness_F
                       Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E
                       Yoneda10_ee_  viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_
          | _Yoneda00_F _Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F isFiniteness_F
                       Yoneda00_E Yoneda01_E Viewing_E Viewing_data_E Viewing_transp_E E
                       Yoneda10_ee_  viewingContinuous_ee_ Yoneda10_ee_natural Yoneda10_ee_morphism Yoneda10_ee_real ee_
                       projT1_sval_Yoneda10_ee_ viewingDefault'_  viewingDefault'_data  viewingDefault'_transp viewingDefault'_isFiniteness viewingDefault'_poly_transp
          ] .

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is ((@'UnitCoMod F) o>CoMod ('ViewedFunctor1 ff)) **)
      - unshelve eexists. do 2 eexists. refine ('ViewedFunctor1 ff)%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff))); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (('ViewedFunctor1 _ff) o>CoMod ('ViewedFunctor1 ff)) **)
      - have [:blurb] _ff_o_ff_transp :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract tac_degrade grade_ff.
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                        (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb)))
                (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb))))
                (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb))))_ff_o_ff_transp 
        => Yoneda10__ff_o_ff viewingContinuous__ff_o_ff _ff_o_ff _ff_o_ff_transp .

        unshelve eexists. do 2 eexists.
        refine ( 'ViewedFunctor1 _ff_o_ff )%sol.
        move: ff_Sol_transp ff'Sol_transp _ff_o_ff_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                        (uTrans := ( 'ViewedFunctor1 (Sol.toPolyMor _ff) ) o>CoMod
                           ( 'ViewedFunctor1 (Sol.toPolyMor ff) )); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( ff o>CoMod 'UnitViewedFunctor ) o>CoMod ('ViewedFunctor1 ff)) **)
      - have [:blurb] _ff_o_ff_transp :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract tac_degrade grade_ff.
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                        (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb)))
                (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb))))
                (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor _ff o>CoMod Sol.toPolyMor ff) blurb)))) _ff_o_ff_transp 
        => Yoneda10__ff_o_ff viewingContinuous__ff_o_ff _ff_o_ff _ff_o_ff_transp .

        unshelve eexists. do 2 eexists.
        refine ( _ff_o_ff o>CoMod 'UnitViewedFunctor )%sol.
        move: ff_Sol_transp ff'Sol_transp _ff_o_ff_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
             (uTrans := ( (Sol.toPolyMor _ff) o>CoMod 'UnitViewedFunctor ) o>CoMod
                     ( 'ViewedFunctor1 (Sol.toPolyMor ff) )); tac_reduce).
          
      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( [[ ee_ @ isFiniteness_F ]] ) o>CoMod ('ViewedFunctor1 ff)) **)
      - have [:blurb_] ee__o_ff_transp G f H  (v : 'Generator( H ~> G | (_Viewing_F G f) )) :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ff) (blurb_ G f H v)));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract((move => G f H v);
                     match goal with
                     | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F |- _ ] =>
                       destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F  v)
                     end;
                     tac_degrade grade_ff).
        have @Yoneda10_ee__o_ff_ := (fun G f H v =>
               projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ff) (blurb_ G f H v)))).
        have @viewingContinuous_ee__o_ff_ : (forall G f H v, viewingContinuous _ _ (Yoneda10_ee__o_ff_ G f H v) )
          := (fun G f H v => projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ff) (blurb_ G f H v))))).
        have @ee__o_ff_ : (forall G f H v, 'CoMod( View H ~> F @ Yoneda10_ee__o_ff_ G f H v @~ viewingContinuous_ee__o_ff_ G f H v ) %sol)
          := (fun G f H v => projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ff) (blurb_ G f H v))))) .
        have {ee__o_ff_transp}: (forall G f H v,
                            Sol.toPolyMor (ee__o_ff_(G)(f)(H)(v)) <~~ (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod Sol.toPolyMor ff)) := ee__o_ff_transp.
        move: Yoneda10_ee__o_ff_ viewingContinuous_ee__o_ff_ ee__o_ff_ => Yoneda10_ee__o_ff_ viewingContinuous_ee__o_ff_ ee__o_ff_ ee__o_ff_transp.
        clear solveCoMod.
        unshelve eexists. do 2 eexists.
        refine ( [[  ee__o_ff_  @  isFiniteness_F  ,  _  , _ , _  ]] %sol ).

        (**memo: convCoMod_sense is really necessary here for Yoneda10_ee__o_ee_natural Yoneda10_ee__o_ee_morphism Yoneda10_ee__o_ee_real viewingDefault'_transpSol **)
        (* Yoneda10_ee__o_ee_natural *)
        { clear -Yoneda10_ee_natural ee__o_ff_transp.
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v)) => ee__o_ff_transp_eq);
                    intros; move; rewrite /= /polyelement_to_element /= ; intros;
                    do 2 rewrite -ee__o_ff_transp_eq;
                    exact: (Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural)).
        }
        (* Yoneda10_ee__o_ff_morphism *)
        { clear -Yoneda10_ee_morphism ee__o_ff_transp;
          abstract( move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v))
                    => ee__o_ff_transp_eq; intros; move;
                      rewrite /= /polyelement_to_element /= ;
                      do 2 rewrite -ee__o_ff_transp_eq ;
                      exact: (Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism) ) .
        }
        (* Yoneda10_ee__o_ff_real *)
        { clear - _Yoneda01_F Yoneda10_ee_real ee__o_ff_transp;
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v)) => ee__o_ff_transp_eq );
                    intros; move; rewrite /= /polyelement_to_element /= ;
                    do 2 rewrite -ee__o_ff_transp_eq;
                    exact: (Yoneda10_PolyTransf_morphism_real _Yoneda01_F Yoneda10_ee_real ) ).
        }

        move: ff_Sol_transp ff'Sol_transp ee__o_ff_transp; clear;
          abstract( simpl; intros;
                    eapply convCoMod_Trans with
                    (uTrans := ( [[ fun G f H v => (Sol.toPolyMor (ee_(G)(f)(H)(v)))
                                      @ isFiniteness_F , Yoneda10_ee_natural ,
                                                     Yoneda10_ee_morphism , Yoneda10_ee_real ]] )
                                 o>CoMod ( 'ViewedFunctor1 (Sol.toPolyMor ff) ));
                    first (by simpl; eauto); (* eapply convCoMod_Trans with *)
                    simpl; by eauto).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (( [[[ ee_ @ _Yoneda01_F, _Viewing_F]]] ) o>CoMod ('ViewedFunctor1 ff)) **)
      - have [:blurb_] ee__o_ff_transp G f H  (v : 'Generator( H ~> G | (_Viewing_F G f) )) :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff))) (blurb_ G f H v)));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract((move => G f H v);
                     match goal with
                     | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F  |- _ ] =>
                       destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F  v)
                     end;
                     tac_degrade grade_ff).
        have @Yoneda10_ee__o_ff_ := (fun G f H v =>
               projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff))) (blurb_ G f H v)))).
        have @viewingContinuous_ee__o_ff_ : (forall G f H v, viewingContinuous _ _ (Yoneda10_ee__o_ff_ G f H v) )
          := (fun G f H v => projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff))) (blurb_ G f H v))))).
        have @ee__o_ff_ : (forall G f H v, 'CoMod( View H ~> ViewedFunctor F @ Yoneda10_ee__o_ff_ G f H v @~ viewingContinuous_ee__o_ff_ G f H v) %sol)
          := (fun G f H v => projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff))) (blurb_ G f H v))))) .
        have {ee__o_ff_transp}: (forall G f H v,
                            Sol.toPolyMor (ee__o_ff_(G)(f)(H)(v)) <~~ (Sol.toPolyMor (ee_(G)(f)(H)(v)) o>CoMod ('ViewedFunctor1 (Sol.toPolyMor ff)))) := ee__o_ff_transp.
        move: Yoneda10_ee__o_ff_ viewingContinuous_ee__o_ff_ ee__o_ff_ => Yoneda10_ee__o_ff_ viewingContinuous_ee__o_ff_ ee__o_ff_ ee__o_ff_transp.
        clear solveCoMod.
        unshelve eexists. do 2 eexists.
        refine ( [[[  ee__o_ff_  @  isFiniteness_F  ,  _  , _ , _ , viewingDefault'_isFiniteness , _ ]]] %sol ).

        (**memo: convCoMod_sense is really necessary here for Yoneda10_ee__o_ff_natural Yoneda10_ee__o_ff_morphism Yoneda10_ee__o_ff_real  **)
        (* Yoneda10_ee__o_ff_natural *)
        { clear -Yoneda10_ee_natural ee__o_ff_transp.
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v)) => ee__o_ff_transp_eq);
                    intros; move; rewrite /= /polyelement_to_element /= ; intros;
                    do 2 rewrite -ee__o_ff_transp_eq;
                    exact: (Yoneda10_PolyTransf_morphism_natural Yoneda10_ee_natural (Yoneda10_ViewedFunctor1 Yoneda10_ff))).
        }
        (* Yoneda10_ee__o_ff_morphism *)
        { clear -Yoneda10_ee_morphism ee__o_ff_transp;
          abstract( move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v))
                    => ee__o_ff_transp_eq; intros; move;
                      rewrite /= /polyelement_to_element /= ;
                      do 2 rewrite -ee__o_ff_transp_eq ;
                      exact: (Yoneda10_PolyTransf_morphism_morphism Yoneda10_ee_morphism (Yoneda10_ViewedFunctor1 Yoneda10_ff)) ) .
        }
        (* Yoneda10_ee__o_ff_real *)
        { clear - _Yoneda01_F Yoneda10_ee_real ee__o_ff_transp;
          abstract( (move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v)) => ee__o_ff_transp_eq );
                    intros; move; rewrite /= /polyelement_to_element /= ;
                    do 2 rewrite -ee__o_ff_transp_eq;
                    exact: (Yoneda10_PolyTransf_morphism_real _Yoneda01_F Yoneda10_ee_real  (Yoneda10_ViewedFunctor1 Yoneda10_ff)) ).
        }
        (* viewingDefault'_transpSol *)
        { clear -viewingDefault'_poly_transp ee__o_ff_transp.
           abstract ((move : (fun G f H v => convCoMod_sense (ee__o_ff_transp G f H v)) => ee__o_ff_transp_eq);
                     intros; apply: (composition_transpViewing (viewingDefault'_poly_transp _ _));
                     apply: identity_transpViewing_innerViewing;
                     intros; rewrite /polyelement_to_element;
                     rewrite -ee__o_ff_transp_eq; reflexivity). 
        }

        move: ff_Sol_transp ff'Sol_transp ee__o_ff_transp; clear;
          abstract( simpl; intros;
                    eapply convCoMod_Trans with
                    (uTrans := ( [[[ fun G f H v => (Sol.toPolyMor (ee_(G)(f)(H)(v)))
                                      @ isFiniteness_F , Yoneda10_ee_natural ,
                                                     Yoneda10_ee_morphism , Yoneda10_ee_real , viewingDefault'_isFiniteness , viewingDefault'_poly_transp ]]] )
                                 o>CoMod ( 'ViewedFunctor1 (Sol.toPolyMor ff) ));
                    first (by simpl; eauto); (* eapply convCoMod_Trans with *)
                    simpl; by eauto).
    }

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod (ff o>CoMod 'UnitViewedFunctor)) **)
  * have [:blurb] ff_Sol_o_ff_transp :=
      (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                             (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb));
        first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
        abstract tac_degrade grade_ff.
    move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                    (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb)))
            (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                              (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb))))
            (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                      (Sol.toPolyMor ff_Sol o>CoMod Sol.toPolyMor ff) blurb)))) ff_Sol_o_ff_transp 
    => Yoneda10_ff_Sol_o_ff viewingContinuous_ff_Sol_o_ff ff_Sol_o_ff ff_Sol_o_ff_transp .

    unshelve eexists. do 2 eexists.
    refine ( ff_Sol_o_ff o>CoMod 'UnitViewedFunctor )%sol.
    move: ff_Sol_transp ff'Sol_transp ff_Sol_o_ff_transp; clear;
      abstract (simpl; intros; eapply convCoMod_Trans with
                   (uTrans := ( Sol.toPolyMor ff_Sol ) o>CoMod
                              ( (Sol.toPolyMor ff) o>CoMod 'UnitViewedFunctor )); tac_reduce).

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement v @ isFiniteness_F )) **)
  * move:  (Sol.Destruct_codomView.morCoMod_codomViewP ff_Sol) => ff_Sol_codomViewP.
    { destruct ff_Sol_codomViewP as
          [ _G (** @'UnitCoMod (View _G) **)
          | _G H g (** 'View1 g **) ].
        
      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement v @ isFiniteness_F )) , is (( @'UnitCoMod (View _G)) o>CoMod ( 'PolyElement v @ isFiniteness_F )) **)
      - unshelve eexists. do 2 eexists. refine ( 'PolyElement v @ isFiniteness_F )%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ( 'PolyElement v @ isFiniteness_F )); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( 'PolyElement v @ isFiniteness_F )) , is (( 'View1 g ) o>CoMod ( 'PolyElement v @ isFiniteness_F )) **)
      - unshelve eexists. do 2 eexists.
        refine ( 'PolyElement ( g o>Generator v | (Viewing_F G f) ) @ isFiniteness_F )%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                                   (uTrans := ( 'View1 g ) o>CoMod ( 'PolyElement v @ isFiniteness_F )); tac_reduce).
    }

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( [[ ee_ @ isFiniteness_F ]] )) **)
  * move:  (Sol.Destruct_codomViewingFunctor.morCoMod_codomViewingFunctorP ff_Sol) => ff_Sol_codomViewingFunctorP.
    { destruct ff_Sol_codomViewingFunctorP as
          [ Yoneda00_F  Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F
          | Yoneda00_F  Yoneda01_F Viewing_F Viewing_data_F Viewing_transp_F isFiniteness_F G f H v
          ] .

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is ((@'UnitCoMod (ViewingFunctor isFiniteness_F)) o>CoMod ( [[ ee_ @ isFiniteness_F ]] )) **)
      - unshelve eexists. do 2 eexists. refine ( [[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]] )%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ([[ (fun G H f v => Sol.toPolyMor (ee_(G)(H)(f)(v))) @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real ]])); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (('PolyElement v @ isFiniteness_F) o>CoMod ( [[ ee_ @ isFiniteness_F ]] )) **)
      - have [:blurb] ee_v_transp :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract(match goal with
                     | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F  |- _ ] =>
                       destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F  v)
                     end;
                     tac_degrade grade_ff).
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                        (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb)))
                (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb))))
                (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor (ee_(G)(f)(H)(v))) blurb)))) ee_v_transp 
        => Yoneda10_ee_v viewingContinuous_ee_v ee_v ee_v_transp .

        unshelve eexists. do 2 eexists.
        refine ( ee_v o>CoMod 'UnitViewedFunctor )%sol.
        move: ff_Sol_transp ff'Sol_transp ee_v_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                        (uTrans := ( 'PolyElement v @ isFiniteness_F ) o>CoMod
                           ( [[ (fun G H f v => Sol.toPolyMor (ee_(G)(H)(f)(v))) @ isFiniteness_F ,  Yoneda10_ee_natural , Yoneda10_ee_morphism  , Yoneda10_ee_real ]] )); tac_reduce).
    }

  (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (ff_Sol o>CoMod ( [[[ ee_ @ isFiniteness_F , _isFiniteness_F]]] )) **)
  * move:  (Sol.Destruct_codomViewingFunctor.morCoMod_codomViewingFunctorP ff_Sol) => ff_Sol_codomViewingFunctorP.
    { destruct ff_Sol_codomViewingFunctorP as
          [ Yoneda00_F  Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F _isFiniteness_F
          | Yoneda00_F  Yoneda01_F _Viewing_F _Viewing_data_F _Viewing_transp_F _isFiniteness_F G f H v
          ] .

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is ((@'UnitCoMod (ViewingFunctor _isFiniteness_F)) o>CoMod ( [[[ ee_ @ isFiniteness_F , _isFiniteness_F]]] )) **)
      - unshelve eexists. do 2 eexists. refine ( [[[ ee_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real , _isFiniteness_F , viewingDefault'_poly_transp ]]] )%sol.
        move: ff_Sol_transp ff'Sol_transp; clear;
          abstract (simpl; intros; eapply convCoMod_Trans with
                (uTrans := ('UnitCoMod) o>CoMod ([[[ (fun G H f v => Sol.toPolyMor (ee_(G)(H)(f)(v))) @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism , Yoneda10_ee_real  , _isFiniteness_F , viewingDefault'_poly_transp ]]])); tac_reduce).

      (** gg is (ff_ o>CoMod ff') , to (ff_Sol o>CoMod ff'Sol)  , 
is (('PolyElement F wv) o>CoMod ( [[[ ee_ @ isFiniteness_F , _isFiniteness_F]]] )) **)
      - set w'v' := (((projT2 (sval (viewingDefault'_poly_transp G f) H v)) :>Generator) o>Generator (projT2 (projT1 (sval (viewingDefault'_poly_transp G f) H v))) | (Viewing_F G f)).
        have [:blurb] ee_w'v'_transp :=
          (proj2_sig (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                 (Sol.toPolyMor (ee_(G)(f)(H)(w'v'))) blurb));
            first by clear -grade_ff ff_Sol_transp ff'Sol_transp;
            abstract(match goal with
                     | [ isFiniteness_F : Finiteness.isFiniteness_ ?Viewing_data_F ?Viewing_transp_F  |- _ ] =>
                       move : w'v'; intros w'v';
                       destruct (Finiteness.is_viewingFunctorElement12_allP isFiniteness_F w'v')
                     end;
                     tac_degrade grade_ff).
        move: (projT1 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                        (Sol.toPolyMor (ee_(G)(f)(H)(w'v'))) blurb)))
                (projT1 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                  (Sol.toPolyMor (ee_(G)(f)(H)(w'v'))) blurb))))
                (projT2 (projT2 (sval (solveCoMod len _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                          (Sol.toPolyMor (ee_(G)(f)(H)(w'v'))) blurb)))) ee_w'v'_transp 
        => Yoneda10_ee_w'v' viewingContinuous_ee_w'v' ee_w'v' ee_w'v'_transp .

        unshelve eexists. do 2 eexists.
        refine ( ee_w'v' )%sol.
        move: ff_Sol_transp ff'Sol_transp ee_w'v'_transp; clear;
          abstract( simpl; set eeSol_ := (fun G0 f0 H0 v0 => Sol.toPolyMor (ee_(G0)(f0)(H0)(v0)));
        intros; eapply convCoMod_Trans with
                (uTrans := ( 'PolyElement v @ _isFiniteness_F ) o>CoMod
                          ( [[[ eeSol_ @ isFiniteness_F , Yoneda10_ee_natural , Yoneda10_ee_morphism  , Yoneda10_ee_real , _isFiniteness_F , viewingDefault'_poly_transp ]]] ));
        first (by simpl; eauto);
        eapply convCoMod_Trans with (uTrans := eeSol_ G f H w'v');
        first (by apply PolyTransf_default_PolyElement); eauto).
    }
Defined.
End Resolve.
End MODIFIEDCOLIMIT.
(** # #
#+END_SRC

Voila.
# # **)
