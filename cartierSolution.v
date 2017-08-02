(**#+TITLE: cartierSolution.v

Proph

https://gitlab.com/1337777/cartier/blob/master/cartierSolution.v

solves some question of Cartier which is how to program grammatical meta
(metafunctors) ...

This starting lemma of polymorph mathematics ( "categories" ) :

Coreflections( Set , Funtors( op C , Prop ) ) <=> Funtors( C , Set )

says that the senses ( "metafunctors models" ) onfrom some given primitive-syntax
graph may be instead dually viewed as senses ( "coreflective-metafunctors models" )
into some more-complete metafunctors-grammar ( "classifying topos" ). And this
starting lemma may be upgraded such to perceive flat metafunctors via geometric
morphisms into this metafunctors-grammar. Also this starting lemma may be upgraded
such to perceive continuous flat metafunctors via geometric morphisms into some sheaf
metafunctors-grammar ...

The question is whether these new more-complete metafunctors-grammars are relatively
computational/decidable ? This COQ text solves half of this question, the resting half
is promised only ...

Outline: Primo, the things shall be confined to some meta regular cardinal, and this
COQ text assumes-as-axiom some maximum operation inside this regular cardinal and this
COQ text assumes-as-axiom some functional extensionality of families of morphisms
which are confined to this regular cardinal. Secondo, as was done in the earlier COQ
text for colimits, one shall erase/extract some logical cocone-conditions by assuming
some erasure/extraction scheme as axiom instead of some very-complicated-induction
scheme (beyond induction-induction) ... Tertio, the degradation lemma is more
technical than in the earlier COQ texts, because for the congruent-reduction from the
copairing operation applied onto some cocone of morphisms, one shall require
simultaneous full-reduction of every reductible morphism in the cocone. Most of this
COQ program and deduction is automated.

Keywords: 1337777.OOO//cartierSolution.v ; metafunctors-grammar ; duality ;
classifying topos

-----

Memo :

The 1337777.OOO SOLUTION PROGRAMME originates from some random-moment discovery of
some convergence of the DOSEN PROGRAMME [[http://www.mi.sanu.ac.rs/~kosta]] along the
COQ PROGRAMME [[https://coq.inria.fr]].
   
The 1337777.OOO has discovered [[1337777.OOO//coherence2.v]]
[[google.com/#q=1337777.OOO/coherence2.v]]
[[https://web.archive.org/web/20170516011054/https://github.com/1337777/dosen/blob/master/coherence2.v]]
[fn:4] [fn:5] that the attempt to deduce associative coherence by Maclane is not the
reality, because this famous pentagone is in fact some recursive square. This
associative coherence is the meta of the semiassociative coherence
[[1337777.OOO//coherence.v]] which does lack some more-common Newman-style confluence
lemma.

Moreover the 1337777.OOO has discovered [[1337777.OOO//borceuxSolution2.v]]
[[1337777.OOO//chic05.pdf]] that the "categories" ( "enriched categories" ) only-named
by the homologist Maclane are in reality interdependent-cyclic with the natural
polymorphism of the logic of Gentzen, this enables some programming of congruent
resolution by cut-elimination [[1337777.OOO//dosenSolution3.v]] which will serve as
specification (reflection) technique to semi-decide the questions of coherence, in
comparasion from the ssreflect-style.

Furthermore the 1337777.OOO has discovered [[1337777.OOO//aignerSolution.v]]
[[1337777.OOO//ocic04-where-is-combinatorics.pdf]] that the Galois-action for the
resolution-modulo ( "symmetry groupoid action" ), is in fact some instance of
polymorph functors.

And the 1337777.OOO has discovered [[1337777.OOO//ocic03-what-is-normal.djvu]]
[[1337777.OOO//laoziSolution2.v]] how to program polymorph coparametrism functors (
"comonad" ).

And the 1337777.OOO has discovered [[1337777.OOO//chuSolution.v]] how to program
contextual limits of polymorph functors ( "Kan extension" ).

And the 1337777.OOO has discovered [[1337777.OOO//cartierSolution.v]] how to program
the metafunctors-grammar ( "topos" ), as the primo step towards the programming of the
( "classifying-topos" ) sheaf-metafunctors-grammar which is held as augmented-syntax
in the Diaconescu duality lemma ( "coreflective-metafunctors models" ). Another
further step shall be to GAP-and-COQ program [[https://www.gap-system.org]] the
computational logic for Tarski's decidability in free groups and for convergence in
infinite groups ...

Additionnally, the 1337777.OOO has discovered random dia-para-logic discoveries
[[1337777.OOO//1337777solution.txt]] and information-technology
[[1337777.OOO//init.html]] [[1337777.OOO//init.pdf]] [[1337777.OOO//makegit.sh.org]]
[[1337777.OOO//editableTree.urp]] [[1337777.OOO//gongji.ml4]] based on the _EMACS
org-mode_ logiciel which enables communication of _timed-synchronized_ _geolocated_
_simultaneously-edited_ _multi-authors_ _format-able_ _searchable_ text, and therefore
_personal email_ and _public communication_ of _multiple-market/language_ (中文话）
textual COQ math programming, and which enables _personal archiving_ and _public
archiving_ and therefore _public reviews / webcitations_ .

Whatever is discovered, its format, its communication is simultaneously some
predictable-time (1337) computational-logical discovery and some random-moment (777)
dia-para-computalogical discovery.

-----

paypal 1337777.OOO@gmail.com , wechatpay 2796386464@qq.com , irc #OOO1337777


**)

(**

#+BEGIN_SRC coq :exports both :results silent **)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import Setoid.
Require Omega. 

Module METAFUNCTORS.

Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.
 
Parameter obIndexer : Type (* regular cardinal *).
Parameter Indexer : obIndexer -> obIndexer -> Type (* regular cardinal *).
Notation "''Indexer' (0 A1 ~> A2 )0" :=
  (@Indexer A1 A2) (at level 25, format "''Indexer' (0  A1  ~>  A2  )0").
Parameter polyIndexer : forall (A2 A1 : obIndexer),
    Indexer A2 A1 -> forall A1' : obIndexer, (Indexer A1 A1') -> (Indexer A2 A1').
Notation "a_ o>Indexer a'" :=
  (@polyIndexer _ _ a_ _ a') (at level 25, right associativity).
Parameter unitIndexer : forall {A : obIndexer}, Indexer A A.
Parameter convIndexer : forall (A1 A2 : obIndexer),
    'Indexer(0 A1 ~> A2 )0 -> 'Indexer(0 A1 ~> A2 )0 -> Prop.
Notation "a2 ~~ a1" := (@convIndexer _ _ a2 a1) (at level 70).

Inductive obTopos : Type (* larger cardinal *) :=
| View0 : forall A : obIndexer, obTopos
| MetaFunctor : forall (func0 : obIndexer -> Type (* regular cardinal *))  
                  (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    obTopos.

Reserved Notation "''Topos' (0 F1 ~> F2 )0"
         (at level 25, format "''Topos' (0  F1  ~>  F2  )0").

Inductive Topos00 : obTopos -> obTopos -> Type (* larger cardinal, possible *) :=

| UnitTopos : forall {F : obTopos}, 'Topos(0 F ~> F )0

| PolyTopos : forall (F2 : obTopos) (F1 : obTopos)
  , 'Topos(0 F2 ~> F1 )0 -> forall F1' : obTopos,
      'Topos(0 F1 ~> F1' )0 -> 'Topos(0 F2 ~> F1' )0

| View1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 ->
                                'Topos(0 (View0 A) ~> (View0 A') )0

| PolyMetaFunctor :
    forall (func0 : obIndexer -> Type (* same, regular cardinal *))
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      (forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)

| PolyMetaTransf :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      (forall (A : obIndexer), 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0
                          -> 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0)

| CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      (* cocone func1 v_ ->    cocone logical-condition erased *)
      'Topos(0 (MetaFunctor func1) ~> F )0

where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).

Notation "'uTopos'" := (@UnitTopos _)(at level 0).
Notation "@ 'uTopos' F" :=
  (@UnitTopos F) (at level 11, only parsing).

Notation "f_ o>Topos f'" :=
  (@PolyTopos _ _ f_ _ f') (at level 25, right associativity).

Notation "f o>Topos_ transf @ func'1" :=
  (@PolyMetaTransf _ _ _ func'1 transf _ f) (at level 25, transf at level 0, right associativity).

Notation "f o>Topos_ transf" :=
  (@PolyMetaTransf _ _ _ _ transf _ f) (at level 25, transf at level 0, right associativity).

Notation "[[ v_ @ func1 ]]" :=
  (@CoLimitator _ func1 _ v_ ) (at level 0).

Notation "[[ v_ ]]" :=
  (@CoLimitator _ _ _ v_ ) (at level 0).

Ltac rewriterTopos :=
  repeat match goal with
         | [ HH : @eq (Topos00 _ _) _ _  |- _ ] =>
           try rewrite -> HH in *; clear HH
         end. 

Reserved Notation "f2 ~~~ f1"  (at level 70).

Inductive convTopos : forall (F1 F2 : obTopos),
    'Topos(0 F1 ~> F2 )0 -> 'Topos(0 F1 ~> F2 )0 -> Prop :=

(* equivalence *)
  
| Topos_Refl : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
    f ~~~ f
      
| Topos_Trans : forall (F1 F2 : obTopos) (uTrans f : 'Topos(0 F1 ~> F2 )0),
    uTrans ~~~ f -> forall (f0 : 'Topos(0 F1 ~> F2 )0),
      f0 ~~~ uTrans -> f0 ~~~ f
                         
| Topos_Sym : forall (F1 F2 : obTopos) (f f0 : 'Topos(0 F1 ~> F2 )0),
    f ~~~ f0 -> f0 ~~~ f

(* congruences *)
                  
| PolyTopos_cong :
    forall (F F' : obTopos) (f_ f_0 : 'Topos(0 F ~> F' )0),
    forall (F'' : obTopos) (f' f'0 : 'Topos(0 F' ~> F'' )0),
      f_0 ~~~ f_ -> f'0 ~~~ f' -> ( f_0 o>Topos f'0 ) ~~~ ( f_ o>Topos f' )

| View_cong : forall (A A' : obIndexer) (a a0 : 'Indexer(0 A ~> A' )0),
    a0 ~~ a -> View1 a0 ~~~ ( View1 a
                             : 'Topos(0 View0 A ~> View0 A' )0 )

| PolyMetaFunctor_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (A : obIndexer) (x x0 : func0 A),
      x0 = x -> PolyMetaFunctor func1 x0 ~~~ ( (PolyMetaFunctor func1 x)
                                              : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
                               
| PolyMetaTransf_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
    forall (A : obIndexer) (v v0 : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
      (* none lack to hold changes to transf because no such changes and uniform *)
      v0 ~~~ v -> v0 o>Topos_transf ~~~ ( v o>Topos_transf
                                          : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0 )

| CoLimitator_cong :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ v_0 : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      (* cocone func1 f_ ->    cocone erased *)
      ( forall (A : obIndexer) (x : func0 A), v_0 A x ~~~ v_ A x ) 
      ->  [[ v_0 @ func1 ]] ~~~ ( [[ v_ @ func1 ]]
                                 : 'Topos(0 MetaFunctor func1 ~> F )0 )

(* units *)

| Topos_unit :
    forall (F F' : obTopos) (f : 'Topos(0 F ~> F' )0),
      ( f )
        ~~~ ( ( uTopos ) o>Topos f
              : 'Topos(0 F ~> F' )0 )

| Topos_inputUnitTopos :
    forall (G F : obTopos) (g : 'Topos(0 G ~> F )0),
      ( g )
        ~~~  ( g o>Topos ( uTopos )
               : 'Topos(0 G ~> F )0 )

(* for sense only, non-necessary for reduction *)
| View_unitIndexer : forall (A : obIndexer),
    ( @UnitTopos (View0 A) )
      ~~~ ( View1 (@unitIndexer A)
            : 'Topos(0 View0 A ~> View0 A )0 )

(* polymorphism *)

(* non for reduction *)
| Topos_morphism :
    forall (G F : obTopos) (g : 'Topos(0 G ~> F )0)
      (F' : obTopos) (f_ : 'Topos(0 F ~> F' )0)
      (F'' : obTopos) (f' : 'Topos(0 F' ~> F'' )0),
      ( g o>Topos ( f_ o>Topos f' ) )
        ~~~ ( ( g o>Topos f_ ) o>Topos f'
              : 'Topos(0 G ~> F'' )0 )

| View_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0)
                       (A'' : obIndexer) (a' : 'Indexer(0 A' ~> A'' )0),
    (View1 (a o>Indexer a'))
      ~~~ ( (View1 a) o>Topos (View1 a')
            : 'Topos(0 View0 A ~> View0 A'' )0 )

(* functoriality-polymorphism follows from this _cocone property and
associativity-polymorphism of PolyTopos and functoriality-polymorphism
of View1 *)
| PolyMetaFunctor_cocone :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( PolyMetaFunctor func1 (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (PolyMetaFunctor func1 x)
              : 'Topos(0 View0 A' ~> MetaFunctor func1 )0 )

(* naturality-polymorphism is this, which is in operational form *)
| PolyMetaTransf_poly :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
      (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
      (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( ((View1 a) o>Topos v) o>Topos_transf )
        ~~~ ( (View1 a) o>Topos (v o>Topos_transf)
              : 'Topos(0 View0 A' ~> MetaFunctor func'1 )0 )

(* naturality-polymorphism of the bijection*)
| CoLimitator_morphism :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos) (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (F' : obTopos) (f : 'Topos(0 F ~> F' )0),
      ( [[ (fun A x => (v_ A x) o>Topos f) @ func1 ]] )
        ~~~ ( [[ v_ @ func1 ]] o>Topos f
              : 'Topos(0 MetaFunctor func1 ~> F' )0 )

| PolyMetaFunctor_CoLimitator :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (A : obIndexer) (x : func0 A),
      ( v_ A x )
        ~~~ ( (PolyMetaFunctor func1 x) o>Topos [[ v_ @ func1 ]]
              : 'Topos(0 View0 A ~> F )0 )

| PolyMetaTransf_CoLimitator :
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall F : obTopos,
    forall (v_ : forall (A : obIndexer), func'0 A -> 'Topos(0 (View0 A) ~> F )0),
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A)
      (A : obIndexer) (w : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
      (w o>Topos [[ (fun A0 => (v_ A0) \o (transf A0)) @ func1 ]])
        ~~~ (w o>Topos_transf) o>Topos [[ v_ @ func'1 ]]

| PolyMetaTransf_PolyMetaFunctor :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
      (transf : forall A : obIndexer, func0 A -> func'0 A),
    forall (A : obIndexer) (x : func0 A),
      ( PolyMetaFunctor func'1 (transf A x) )
        ~~~ ( (PolyMetaFunctor func1 x o>Topos_transf)
              : 'Topos(0 View0 A ~> MetaFunctor func'1 )0 )

| PolyMetaTransf_PolyMetaTransf :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (func'0 : obIndexer -> Type)
      (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
    forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
    forall (func''0 : obIndexer -> Type)
      (func''1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func''0 A' -> func''0 A),
    forall (transf' : forall (A : obIndexer), func'0 A -> func''0 A),
    forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
      ( v o>Topos_( fun A0 => (transf' A0) \o (transf A0) ) )
        ~~~ ( ( v o>Topos_transf @ func'1 ) o>Topos_transf' @ func''1
              : 'Topos(0 View0 A ~> MetaFunctor func''1 )0 )

(* for sense only, non-necessary for reduction *)
| CoLimitator_PolyMetaFunctor :
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      ( @UnitTopos (MetaFunctor func1) )
        ~~~ ( [[ PolyMetaFunctor func1 ]]
              : 'Topos(0 (MetaFunctor func1) ~> (MetaFunctor func1) )0 )
        
where "f2 ~~~ f1" := (@convTopos _ _ f2 f1).

Hint Constructors convTopos.

Definition cocone_def := 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( v_ A' (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (v_ A x)
              : 'Topos(0 View0 A' ~> F )0 ) .

Notation cocone func1 v_ :=
  (forall (A : obIndexer) (x : _ A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
      ( v_ A' (func1 _ _ a x) )
        ~~~ ( (View1 a) o>Topos (v_ A x)
              : 'Topos(0 View0 A' ~> _ )0 )) .

Check 
    forall (func0 : obIndexer -> Type)
      (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
    forall (F : obTopos)
      (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      cocone func1 v_ ->
      'Topos(0 (MetaFunctor func1) ~> F )0.

Lemma topos_functional_extensionality :
  forall (func0 : obIndexer -> Type)
    (func1 : forall A A' : obIndexer, 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A)
    (F : obTopos)
    (f_ g_ : forall A : obIndexer, func0 A -> ('Topos(0 View0 A ~> F )0)),
    (forall A x, f_ A x = g_ A x ) -> f_ = g_ .
Admitted.

Definition regularCardinalAll : forall (obIndexer : Type) (func0 : obIndexer -> Type),
    (forall (A : obIndexer), func0 A -> bool (* or same regular cardinal *)) -> bool (* or same regular cardinal *).
Admitted.

Lemma regularCardinalAllP : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                              (b_ : forall (A : obIndexer), func0 A -> bool),
    reflect (exists A, exists x, ~~ b_ A x) (~~ regularCardinalAll b_).
Admitted.

Definition regularCardinalMax : forall (obIndexer : Type (* regular cardinal *))
                                  (func0 : obIndexer -> Type (* same, regular cardinal *))
                                  (filter : (forall (A : obIndexer), func0 A -> Prop)),
    (forall (A : obIndexer), func0 A -> nat (* same regular cardinal *) ) -> nat (* same regular cardinal *).
Admitted.

Lemma regularCardinalMax_falsefilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                         (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x <-> False) ->
      regularCardinalMax filter v_ = 0 .
Admitted.

Lemma regularCardinalMax_subfilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (filter' : (forall (A : obIndexer), func0 A -> Prop)),
      (forall A x, filter' A x -> filter A x) ->
      ( regularCardinalMax filter' v_ <= regularCardinalMax filter v_ )%coq_nat.
Admitted.

Lemma regularCardinalMax_samefilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (filter' : (forall (A : obIndexer), func0 A -> Prop)),
      (forall A x, filter' A x <-> filter A x) ->
      ( regularCardinalMax filter' v_ = regularCardinalMax filter v_ )%coq_nat.
Admitted.

Lemma regularCardinalMax_unionfilter : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                                       (filter filter' : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      ( regularCardinalMax (fun A x => filter A x \/ filter' A x) v_ <= (regularCardinalMax filter v_ + regularCardinalMax filter' v_)%coq_nat )%coq_nat.
Admitted.

Lemma regularCardinalMax_congr : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x = v_ A x )%coq_nat) ->
      ( regularCardinalMax filter w_ = regularCardinalMax filter v_ )%coq_nat.
Admitted.

Lemma regularCardinalMax_monotone_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x <= v_ A x )%coq_nat) ->
      ( regularCardinalMax filter w_ <= regularCardinalMax filter v_ )%coq_nat.
Admitted.

Lemma regularCardinalMax_monotone_gt : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (forall A x, filter A x -> ( w_ A x < v_ A x )%coq_nat) ->
      forall A x, filter A x -> ( w_ A x < v_ A x )%coq_nat ->
             ( regularCardinalMax filter w_ < regularCardinalMax filter v_ )%coq_nat.
Admitted.

Lemma regularCardinalMax_addr_const : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      regularCardinalMax filter (fun A x => (v_ A x + n)%coq_nat) = ((regularCardinalMax filter v_) + n)%coq_nat.
Admitted.

Lemma regularCardinalMax_addl_const : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) (n : nat),
      regularCardinalMax filter (fun A x => (n + v_ A x)%coq_nat) = (n + (regularCardinalMax filter v_))%coq_nat.
Admitted.

Lemma regularCardinalMax_add_succ : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                            (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
      regularCardinalMax filter (fun A x => S (v_ A x)%coq_nat) = (S (regularCardinalMax filter v_))%coq_nat.
Admitted.

Lemma regularCardinalMax_add_le : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (w_ v_ : forall (A : obIndexer), func0 A -> nat),
      (regularCardinalMax filter (fun A x => (w_ A x + v_ A x)%coq_nat) <= ((regularCardinalMax filter w_) + (regularCardinalMax filter v_))%coq_nat)%coq_nat.
Admitted.

Lemma regularCardinalMax_ge : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                   (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat) A (x : func0 A),
      filter A x -> ( (v_ A x) <= (regularCardinalMax filter v_) )%coq_nat .
Admitted.

Lemma regularCardinalMax_transf : forall (obIndexer : Type) (func0 : obIndexer -> Type)
                       (filter : (forall (A : obIndexer), func0 A -> Prop)),
    forall (v_ : forall (A : obIndexer), func0 A -> nat),
    forall (func'0 : obIndexer -> Type) (transf : forall (A : obIndexer), func'0 A -> func0 A),
      ( regularCardinalMax (fun A => filter A \o transf A) (fun A => v_ A \o transf A) <= regularCardinalMax filter v_ )%coq_nat .
Admitted.

Module Sol.

  Section Section1.

    Inductive Topos00 : obTopos -> obTopos -> Type :=

    | UnitTopos : forall {F : obTopos}, 'Topos(0 F ~> F )0

    | View1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 ->
                                    'Topos(0 (View0 A) ~> (View0 A') )0

    | PolyMetaFunctor :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
          (forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)

    | CoLimitator :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall F : obTopos,
        forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
          (* cocone func1 v_ ->    cocone erased *)
          'Topos(0 (MetaFunctor func1) ~> F )0

    where "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2).

  End Section1.

  Module Import Ex_Notations.
    Delimit Scope sol_scope with sol.
    Notation "''Topos' (0 F1 ~> F2 )0" := (@Topos00 F1 F2) : sol_scope.
    Notation "'uTopos'" := (@UnitTopos _)(at level 0) : sol_scope. 
    Notation "@ 'uTopos' F" :=
      (@UnitTopos F) (at level 11, only parsing) : sol_scope.


    Notation "f o>Topos_ transf @ func'1" :=
      (@PolyMetaTransf _ _ _ func'1 transf _ f) (at level 25, transf at level 0, right associativity) : sol_scope.

    Notation "f o>Topos_ transf" :=
      (@PolyMetaTransf _ _ _ _ transf _ f) (at level 25, transf at level 0, right associativity) : sol_scope.

    Notation "[[ v_ @ func1 ]]" :=
      (@CoLimitator _ func1 _ v_ ) (at level 0) : sol_scope.

    Notation "[[ v_ ]]" :=
      (@CoLimitator _ _ _ v_ ) (at level 0) : sol_scope.
  End Ex_Notations.

  Module Destruct_domView.

    Inductive Topos00_domView : forall (A : obIndexer) (F2 : obTopos),
      ( 'Topos(0 View0 A ~> F2 )0 %sol ) -> Type :=

    | UnitTopos : forall {A : obIndexer}, Topos00_domView (@uTopos (View0 A))%sol

    | View1 : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0),
        Topos00_domView (Sol.View1 a)%sol

    | PolyMetaFunctor :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall (A : obIndexer) (x : func0 A),
          Topos00_domView (Sol.PolyMetaFunctor func1 x)%sol .

    Lemma Topos00_domViewP : forall F1 F2 ( f : 'Topos(0 F1 ~> F2 )0 %sol ),
        ltac:( destruct F1; [| intros; refine (unit : Type)];
                 refine (Topos00_domView f) ).
    (*
  forall (F1 F2 : obTopos) (f : ('Topos(0 F1 ~> F2 )0)%sol),
  match F1 as o return (('Topos(0 o ~> F2 )0)%sol -> Type) with
  | View0 A => [eta Topos00_domView (F2:=F2)]
  | @MetaFunctor func0 func1 => fun _ : ('Topos(0 MetaFunctor func1 ~> F2 )0)%sol => unit : Type
  end f
     *)
    Proof.
      intros. case: F1 F2 / f.
      - destruct F; [| intros; exact: tt].
        constructor 1.
      - constructor 2.
      - constructor 3.
      - intros; exact: tt.
    Defined.

  End Destruct_domView.

  Module Destruct_domMetaFunctor.

    Inductive Topos00_domMetaFunctor :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (F2 : obTopos),
        ( 'Topos(0 MetaFunctor func1 ~> F2 )0 %sol ) -> Type :=

    | UnitTopos : forall (func0 : obIndexer -> Type)
                    (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        Topos00_domMetaFunctor (@uTopos (MetaFunctor func1))%sol

    | CoLimitator :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall F : obTopos,
        forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0 %sol),
          Topos00_domMetaFunctor ([[ v_ @ func1 ]] %sol).

    Lemma Topos00_domMetaFunctorP : forall F1 F2 ( f : 'Topos(0 F1 ~> F2 )0 %sol ),
        ltac:( destruct F1; [intros; refine (unit : Type)|];
                 refine (Topos00_domMetaFunctor f) ).
    Proof.
      intros. case: F1 F2 / f.
      - destruct F.  exact: tt. constructor 1.
      - intros. exact: tt.
      - intros. exact: tt.
      - constructor 2.
    Defined.

  End Destruct_domMetaFunctor.

  Module Destruct_domView_codomMetaFunctor.

    Inductive Topos00_domView_codomMetaFunctor :
      forall (A : obIndexer)
        (func0 : obIndexer -> Type)  
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        ( 'Topos(0 View0 A ~> MetaFunctor func1 )0 %sol ) -> Type :=

    | PolyMetaFunctor :
        forall (func0 : obIndexer -> Type)
          (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
        forall (A : obIndexer) (x : func0 A),
          Topos00_domView_codomMetaFunctor (Sol.PolyMetaFunctor func1 x)%sol .

    Lemma Topos00_domView_codomMetaFunctorP : forall F1 F2 ( f : 'Topos(0 F1 ~> F2 )0 %sol ),
        ltac:( destruct F1; [| intros; refine (unit : Type)];
                 destruct F2; [intros; refine (unit) |];
                   refine (Topos00_domView_codomMetaFunctor f) ).
    Proof.
      intros. case: F1 F2 / f.
      - destruct F; intros; exact: tt.
      - intros; exact: tt.
      - constructor 1.
      - intros; exact: tt.
    Defined.

  End Destruct_domView_codomMetaFunctor.

  Definition toTopos :
    forall (F1 F2 : obTopos), 'Topos(0 F1 ~> F2 )0 %sol -> 'Topos(0 F1 ~> F2 )0.
  Proof.
    (move => F1 F2 f); elim : F1 F2 / f =>
    [ F
    | A A' a
    | func0 func1 A x
    | func0 func1 F vSol_ vSol_toMod ];
      [ apply: (@uTopos F)
      | apply: (METAFUNCTORS.View1 a)
      | apply: (METAFUNCTORS.PolyMetaFunctor func1 x)
      | apply: [[ vSol_toMod ]]
      ].
  Defined.

  Definition isSolb : forall (F1 F2 : obTopos), forall (f : 'Topos(0 F1 ~> F2 )0), bool.
    move => F1 F2 f. elim: F1 F2 /f.
    - intros. exact: true.
    - intros. exact: false.
    - intros. exact: true.
    - intros. exact: true.
    - intros. exact: false.
    - intros func0 func1 F v_ IH_v_. exact: (regularCardinalAll IH_v_). 
  Defined.

  Lemma isSolbP2 : forall (F1 F2 : obTopos), forall (f : 'Topos(0 F1 ~> F2 )0),
        reflect (exists fSol : 'Topos(0 F1 ~> F2 )0 %sol , Sol.toTopos fSol = f) (isSolb f).
  Admitted.

  Lemma isSolb_isSol : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      isSolb f -> ({ fSol : 'Topos(0 F1 ~> F2 )0 %sol | Sol.toTopos fSol = f}).
  Proof.
    move => F1 F2 f ; elim : F1 F2 / f => 
    [ F _  (* @uTopos F %sol*)
    | F2 F1 f_ F1' f' //  (* f_ o>Topos f' *)
    | A A' a (* SolView1 a *)
    | func0 func1 A x _ (* SolPolyMetaFunctor func1 x *)
    | func0 func1 func'0 func'1 transf A f //  (* f o>Topos_transf %sol *)
    | func0 func1 F f_ ] (* [[ f_ @ func1 ]] %sol *).
    - exists ((@uTopos F)%sol). reflexivity.
    - exists ((Sol.View1 a)%sol). reflexivity.
    - exists ((Sol.PolyMetaFunctor func1 x)%sol). reflexivity.
    - move => IH /= /regularCardinalAllP f_isSolb.
      have f_isSolb' : (forall (A : obIndexer) (x : func0 A), isSolb (f_ A x))
        by intros; clear -f_isSolb; apply/negPn/negP; intuition eauto.
      set fSol_ := (fun A x => projT1(IH A x (f_isSolb' A x))).
      set fSol_prop := (fun A x => projT2(IH A x (f_isSolb' A x))).
      exists ([[ fSol_ ]] %sol). simpl; apply: congr1.
      apply: (topos_functional_extensionality func1).
        by move => A x; move: fSol_prop => <- .
  Qed.

  Lemma isSolbN_isSolN : forall (F1 F2 : obTopos),
      forall fSol : 'Topos(0 F1 ~> F2 )0 %sol, forall (f : 'Topos(0 F1 ~> F2 )0), (Sol.toTopos fSol) = f -> isSolb f.
  Proof.
    move => F1 F2 fSol ; elim : F1 F2 / fSol ; try (intros; subst; reflexivity).
    intros; subst; simpl. intuition.
    intros; subst; simpl. apply/regularCardinalAllP.
    move => [A [x isSolb_v_] ]. move: isSolb_v_. apply/negP/negPn. eapply H; reflexivity.
  Qed.

  Lemma isSolbN_isSolN_alt : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ~~ isSolb f ->  ~ ( exists fSol : 'Topos(0 F1 ~> F2 )0 %sol , (Sol.toTopos fSol) = f ).
  Proof.
    intros F1 F2 f f_isSolbN []. move: f_isSolbN. apply/negP/negPn. apply: isSolbN_isSolN.
    eauto.
  Qed.
  
End Sol.

  
Fixpoint grade (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0) {struct f} : nat.
Proof. (* non-really mutual at the end *)
  case : F1 F2 / f.
  - intros F.
    exact (S O). (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine ((S  (S (grade _ _ f_ + grade _ _ f')%coq_nat)))%coq_nat. (* PolyTopos *)
  - intros A A' a.
    exact (S (S O)). (* View1 *)
  - intros func0 func1 A x.
    exact (S (S O)). (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine ((S (S (grade _ _ f))))%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine (S (S ((regularCardinalMax (fun A x => ~~ Sol.isSolb (f_ A x)) (fun A x => (  grade _ _ (f_ A x)  )%coq_nat)) +
                  (regularCardinalMax (fun A x => Sol.isSolb (f_ A x)) (fun A x => (  grade _ _ (f_ A x) )%coq_nat)))%coq_nat )). (* CoLimitator *)
Defined.
Fixpoint gradeTotal (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0) {struct f} : nat.
Proof.
  case : F1 F2 / f.
  - intros F.
    exact ((S O))%coq_nat. (* UnitTopos *)
  - intros F2 F1 f_ F1' f'.
    refine ((S  (S (gradeTotal _ _ f_ + gradeTotal _ _ f')%coq_nat)) +
            (  ( ((* gradeMaxCom _ _ f_ + *) ((* gradeMaxCom _ _ f' + *)
                     (S (S (@grade _ _ f_ + @grade _ _ f')%coq_nat)) )%coq_nat)%coq_nat)) )%coq_nat. (* PolyTopos *)
  - intros A A' a.
    exact (S (S O)). (* View1 *)
  - intros func0 func1 A x.
    exact (S (S O)). (* PolyMetaFunctor *)
  - intros func0 func1 func'0 func'1 transf A f.
    refine ((S (S (gradeTotal _ _ f)))  (* + (gradeMaxCom _ _ f) *) )%coq_nat. (* PolyMetaTransf *)
  - intros func0 func1 F f_.
    refine (S (S ((regularCardinalMax (fun A x => ~~ Sol.isSolb (f_ A x)) (fun A x => (  gradeTotal _ _ (f_ A x) )%coq_nat)) +
                 (regularCardinalMax (fun A x => Sol.isSolb (f_ A x)) (fun A x => (  gradeTotal _ _ (f_ A x) )%coq_nat)) )%coq_nat)). (* CoLimitator *)
Defined.

Module Red.

  Import Sol.Ex_Notations.
  Reserved Notation "f2 <~~ f1" (at level 70).

  Inductive convTopos : forall (F1 F2 : obTopos),
      'Topos(0 F1 ~> F2 )0 -> 'Topos(0 F1 ~> F2 )0 -> Prop :=

  (* equivalence *)
        
  | Topos_Trans : forall (F1 F2 : obTopos) (uTrans f : 'Topos(0 F1 ~> F2 )0),
      uTrans <~~ f -> forall (f0 : 'Topos(0 F1 ~> F2 )0),
        f0 <~~ uTrans -> f0 <~~ f
                         
  (* congruences *)
                  
  | PolyTopos_cong_Pre :
      forall (F F' : obTopos) (f_ f_0 : 'Topos(0 F ~> F' )0),
      forall (F'' : obTopos) (f' : 'Topos(0 F' ~> F'' )0),
        f_0 <~~ f_ -> ( f_0 o>Topos f' ) <~~ ( f_ o>Topos f' )

  | PolyTopos_cong_Post :
      forall (F F' : obTopos) (f_ : 'Topos(0 F ~> F' )0),
      forall (F'' : obTopos) (f' f'0 : 'Topos(0 F' ~> F'' )0),
        f'0 <~~ f' -> ( f_ o>Topos f'0 ) <~~ ( f_ o>Topos f' )

  | PolyMetaTransf_cong :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      forall (A : obIndexer) (v v0 : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        (* none lack to hold changes to transf because no such changes and uniform *)
        v0 <~~ v -> v0 o>Topos_transf <~~ ( v o>Topos_transf
                                        : 'Topos(0 (View0 A) ~> (MetaFunctor func'1) )0 )

  | CoLimitator_cong :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall F : obTopos,
      forall (v_ v_0 : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
        (* cocone func1 f_ ->    cocone erased *)
        (forall (A : obIndexer) (x : func0 A), ~~ Sol.isSolb (v_ A x) -> v_0 A x <~~ v_ A x) ->
        (forall (A : obIndexer) (x : func0 A), Sol.isSolb (v_ A x) -> v_0 A x = v_ A x) ->
        (forall (A : obIndexer) (x : func0 A), Sol.isSolb (v_0 A x)) ->
        forall (A : obIndexer) (x : func0 A), ~~ Sol.isSolb (v_ A x) ->
        [[ v_0 @ func1 ]] <~~ ( [[ v_ @ func1 ]]
                              : 'Topos(0 MetaFunctor func1 ~> F )0 )

  (* units *)

  | Topos_unit :
      forall (F F' : obTopos) (f : 'Topos(0 F ~> F' )0),
        ( f )
          <~~ ( ( uTopos ) o>Topos f
              : 'Topos(0 F ~> F' )0 )

  | Topos_inputUnitTopos :
      forall (G F : obTopos) (g : 'Topos(0 G ~> F )0),
        ( g )
          <~~  ( g o>Topos ( uTopos )
               : 'Topos(0 G ~> F )0 )

  (* polymorphism *)

  | View_polyIndexer : forall (A A' : obIndexer) (a : 'Indexer(0 A ~> A' )0)
                         (A'' : obIndexer) (a' : 'Indexer(0 A' ~> A'' )0),
      (View1 (a o>Indexer a'))
        <~~ ( (View1 a) o>Topos (View1 a')
            : 'Topos(0 View0 A ~> View0 A'' )0 )

  (* functoriality-polymorphism follows from this _cocone property and
associativity-polymorphism of PolyTopos and functoriality-polymorphism
of View1 *)
  | PolyMetaFunctor_cocone :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (A : obIndexer) (x : func0 A) (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
        ( PolyMetaFunctor func1 (func1 _ _ a x) )
          <~~ ( (View1 a) o>Topos (PolyMetaFunctor func1 x)
              : 'Topos(0 View0 A' ~> MetaFunctor func1 )0 )

  (* naturality-polymorphism is this, which is in operational form *)
  | PolyMetaTransf_poly :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
        (transf : forall A : obIndexer, func0 A -> func'0 A),
      forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0)
        (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0),
        ( ((View1 a) o>Topos v) o>Topos_transf )
          <~~ ( (View1 a) o>Topos (v o>Topos_transf)
              : 'Topos(0 View0 A' ~> MetaFunctor func'1 )0 )

  (* naturality-polymorphism of the bijection*)
  | CoLimitator_morphism :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (F : obTopos) (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (F' : obTopos) (f : 'Topos(0 F ~> F' )0),
        ( [[ (fun A x => (v_ A x) o>Topos f) @ func1 ]] )
          <~~ ( [[ v_ @ func1 ]] o>Topos f
              : 'Topos(0 MetaFunctor func1 ~> F' )0 )

  | PolyMetaFunctor_CoLimitator :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall F : obTopos,
      forall (v_ : forall (A : obIndexer), func0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (A : obIndexer) (x : func0 A),
        ( v_ A x )
          <~~ ( (PolyMetaFunctor func1 x) o>Topos [[ v_ @ func1 ]]
              : 'Topos(0 View0 A ~> F )0 )

  | PolyMetaTransf_CoLimitator :
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall F : obTopos,
      forall (v_ : forall (A : obIndexer), func'0 A -> 'Topos(0 (View0 A) ~> F )0),
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A)
        (A : obIndexer) (w : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        (w o>Topos [[ (fun A0 => (v_ A0) \o (transf A0)) @ func1 ]])
          <~~ (w o>Topos_transf) o>Topos [[ v_ @ func'1 ]]
                                       
  | PolyMetaTransf_PolyMetaFunctor :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A)
        (transf : forall A : obIndexer, func0 A -> func'0 A),
      forall (A : obIndexer) (x : func0 A),
        ( PolyMetaFunctor func'1 (transf A x) )
          <~~ ( (PolyMetaFunctor func1 x o>Topos_transf)
                : 'Topos(0 View0 A ~> MetaFunctor func'1 )0 )

  | PolyMetaTransf_PolyMetaTransf :
      forall (func0 : obIndexer -> Type)
        (func1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func0 A' -> func0 A),
      forall (func'0 : obIndexer -> Type)
        (func'1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func'0 A' -> func'0 A),
      forall (transf : forall (A : obIndexer), func0 A -> func'0 A),
      forall (func''0 : obIndexer -> Type)
        (func''1 : forall (A A' : obIndexer), 'Indexer(0 A ~> A' )0 -> func''0 A' -> func''0 A),
      forall (transf' : forall (A : obIndexer), func'0 A -> func''0 A),
      forall (A : obIndexer) (v : 'Topos(0 (View0 A) ~> (MetaFunctor func1) )0),
        ( v o>Topos_( fun A0 => (transf' A0) \o (transf A0) ) )
          <~~ ( ( v o>Topos_transf @ func'1 ) o>Topos_transf' @ func''1
              : 'Topos(0 View0 A ~> MetaFunctor func''1 )0 )

  where "f2 <~~ f1" := (@convTopos _ _ f2 f1).

  Module Export Ex_Notations.

    Notation "f2 <~~ f1" := (@convTopos _ _ f2 f1).
    Hint Constructors convTopos.

    (* help PolyMetaFunctor_CoLimitator to decompose 
       the double-applications in (v_ A x) *)
    Hint Extern 0 (_ <~~ _) =>
    ( apply: Red.PolyMetaFunctor_CoLimitator ) .

  End Ex_Notations.
  
  Lemma Red_convTopos_convTopos :
  forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
    fDeg <~~ f -> fDeg ~~~ f.
  Proof.
    move => F1 F2 f fDeg. elim; rewriterTopos; try eauto.
    intros func0 func1 F v_ v_0 H1 H2 H3 H4 A x H5.
    apply: METAFUNCTORS.CoLimitator_cong.
    intros A0 x0. (case_eq (Sol.isSolb (v_ A0 x0)) => H6);
                    [ rewrite H3 => // 
                    | apply: H2; rewrite H6 => // ].
  Qed.

  Lemma degrade :
    forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
      fDeg <~~ f ->  ((grade fDeg) <= (grade f))%coq_nat
                  /\ ((gradeTotal fDeg) < (gradeTotal f))%coq_nat.
  Proof.
    move => F1 F2 fDeg f red_f; elim : F1 F2 fDeg f / red_f;
             try solve [ rewrite /= => * ;
                                      abstract intuition Omega.omega ].
    - (* CoLimitator_cong *)
      move => func0 func1 F v_ v_0 red_v_ IH_red_v iden_v_ sol_v0 A x red_v_A_x.

      move: (IH_red_v _ _ red_v_A_x) => IH_red_v_A_x.

      move: (fun A x p => congr1 (@grade _ _) (iden_v_ A x p)).
      move => /(@regularCardinalMax_congr _ _ (fun A x => Sol.isSolb (v_ A x)) (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).
      move: (fun A x p => congr1 (@gradeTotal _ _) (iden_v_ A x p)).
      move => /(@regularCardinalMax_congr _ _ (fun A x => Sol.isSolb (v_ A x)) (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))).

      move: (fun A x p => proj1 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_ge _ _ (fun A x => ~~ Sol.isSolb (v_ A x)) (fun A x => grade (v_0 A x)) (fun A x => grade (v_ A x))).

      move: (fun A x p => proj2 (IH_red_v A x p)).
      move => /(@regularCardinalMax_monotone_gt _ _ (fun A x => ~~ Sol.isSolb (v_ A x)) (fun A x => gradeTotal (v_0 A x)) (fun A x => gradeTotal (v_ A x))) /(_ _ _ red_v_A_x (proj2 IH_red_v_A_x)) .

      have Hlogical : forall (A : obIndexer) (x : func0 A), ~~ Sol.isSolb (v_0 A x) <-> False .
      { move => A0 x0. move: (sol_v0 A0 x0) -> => //. }
      move : (Hlogical) => /(regularCardinalMax_falsefilter (fun A x => grade (v_0 A x))).
      move : Hlogical => /(regularCardinalMax_falsefilter (fun A x => gradeTotal (v_0 A x))).
      
      have Hlogical2 : forall (A : obIndexer) (x : func0 A), Sol.isSolb (v_0 A x) <-> (~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x)) .
      { move => A0 x0. by case: ( Sol.isSolb (v_ A0 x0)); intuition. }
      move : (Hlogical2) => /(regularCardinalMax_samefilter (fun A x => grade (v_0 A x))).
      move : Hlogical2 => /(regularCardinalMax_samefilter (fun A x => gradeTotal (v_0 A x))).

      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
               (fun A x => grade (v_0 A x)) ).
      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
                                            (fun A x => gradeTotal (v_0 A x)) ).

      simpl; abstract intuition Omega.omega.
      
    - (* CoLimitator_morphism *)
      move => func0 func1 F v_ F' f .

      have Hlogical : forall (A : obIndexer) (x : func0 A), Sol.isSolb (v_ A x o>Topos f) <-> False .
      { move => A0 x0 //= . }
      move : (Hlogical) => /(regularCardinalMax_falsefilter (fun A x => grade (v_ A x o>Topos f))).
      move : Hlogical => /(regularCardinalMax_falsefilter (fun A x => gradeTotal (v_ A x o>Topos f))).

      have Hlogical2 : forall (A : obIndexer) (x : func0 A), ~~ Sol.isSolb (v_ A x o>Topos f) <-> (~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x)) .
      { move => A0 x0 /=. by case: ( Sol.isSolb (v_ A0 x0)); intuition. }
      move : (Hlogical2) => /(regularCardinalMax_samefilter (fun A x => grade (v_ A x o>Topos f))).
      move : Hlogical2 => /(regularCardinalMax_samefilter (fun A x => gradeTotal (v_ A x o>Topos f))).

      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
               (fun A x => grade (v_ A x o>Topos f)) ).
      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
                                            (fun A x => gradeTotal (v_ A x o>Topos f)) ).
      
      rewrite /= !(regularCardinalMax_add_succ , regularCardinalMax_addl_const , regularCardinalMax_addr_const) /=.
      move: (regularCardinalMax_add_le (fun A x => ~~ Sol.isSolb (v_ A x)) (fun (A : obIndexer) (x : func0 A) => (gradeTotal (v_ A x) + gradeTotal f)%coq_nat)
                          (fun (A : obIndexer) (x : func0 A) => (grade (v_ A x) + grade f)%coq_nat.+2) ).
      move: (regularCardinalMax_add_le (fun A x => Sol.isSolb (v_ A x)) (fun (A : obIndexer) (x : func0 A) => (gradeTotal (v_ A x) + gradeTotal f)%coq_nat)
                          (fun (A : obIndexer) (x : func0 A) => (grade (v_ A x) + grade f)%coq_nat.+2) ).
      rewrite /= !(regularCardinalMax_add_succ , regularCardinalMax_addl_const , regularCardinalMax_addr_const) /=.
      simpl; abstract intuition Omega.omega. (* YES /!\ ONCE *)

    - (* PolyMetaFunctor_CoLimitator *)
      move => func0 func1 F v_ A x .

      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
               (fun A x => grade (v_ A x)) ).
      move: (regularCardinalMax_unionfilter (fun A x => ~~ Sol.isSolb (v_ A x))
                                            (fun A x => Sol.isSolb (v_ A x))
                                            (fun A x => gradeTotal (v_ A x)) ).

      have Hlogical: (~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x)).
      { by case: ( Sol.isSolb (v_ A x)); intuition. }
      move: (Hlogical) => /(@regularCardinalMax_ge _ _ (fun A x => ~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x))
                                                 (fun (A0 : obIndexer) (x0 : func0 A0) => grade (v_ A0 x0)) ).
      move: Hlogical => /(@regularCardinalMax_ge _ _ (fun A x => ~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x))
                                              (fun (A0 : obIndexer) (x0 : func0 A0) => gradeTotal (v_ A0 x0)) ).
      simpl; abstract intuition Omega.omega.

    - (* PolyMetaTransf_CoLimitator *)
      move => func'0 func'1 F v_ func0 func1 transf A w /=.  

      move: (regularCardinalMax_transf (fun A0 x => ~~ Sol.isSolb (v_ A0 x)) (fun A0 x => grade (v_ A0 x)) transf)
              (regularCardinalMax_transf (fun A0 x => Sol.isSolb (v_ A0 x)) (fun A0 x => grade (v_ A0 x)) transf)
              (regularCardinalMax_transf (fun A0 x => ~~ Sol.isSolb (v_ A0 x)) (fun A0 x => gradeTotal (v_ A0 x)) transf)
              (regularCardinalMax_transf (fun A0 x => Sol.isSolb (v_ A0 x)) (fun A0 x => gradeTotal (v_ A0 x)) transf).
      rewrite /funcomp => /= . abstract intuition Omega.omega.

  Defined.

  Lemma degradeTotal :
    forall (F1 F2 : obTopos) (fDeg f : 'Topos(0 F1 ~> F2 )0),
      fDeg <~~ f ->  ((gradeTotal fDeg) < (gradeTotal f))%coq_nat.
  Proof.
    eapply degrade.
  Qed.

  Lemma degrade_gt0 :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ((S O) <= (grade f))%coq_nat.
  Proof.
    move=> F1 F2 f; apply/leP; case : f; simpl; auto. (* alt: Omega omega  *)
  Qed.

  Lemma degradeTotal_gt0 :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      ((S O) <= (gradeTotal f))%coq_nat.
  Proof.
    move=> F1 F2 f; case : f => /= * ; Omega.omega.
  Qed.

  Lemma isSolb_isRed_False_alt : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      forall fRed, fRed <~~ f ->
              Sol.isSolb f -> False.
  Proof.
    induction 1; move => //= .
    move/regularCardinalAllP. move => J. apply: J. exists A , x. assumption.
  Qed.
  
  Lemma isSolb_isRed_False : forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0),
      forall fSol : 'Topos(0 F1 ~> F2 )0 %sol,  Sol.toTopos fSol = f ->
                                           forall fRed, fRed <~~ f -> False.
    intros ? ? ? ? ? ? Hred. apply: (isSolb_isRed_False_alt Hred).
    apply: Sol.isSolbN_isSolN. eassumption.
  Qed.

End Red.

Section Section1.

  Import Sol.Ex_Notations.
  Import Red.Ex_Notations.

  Ltac tac_reduce :=
    simpl in *; abstract (
                    intuition (eauto; try subst; rewriterTopos; try congruence;
                               eauto 12)).

  Ltac tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop :=
    destruct a_Sol_prop as [a_Sol_prop |a_Sol_prop];
    [ move : (Red.degrade a_Sol_prop);
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    | subst;
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    ];
    move : H_gradeTotal; clear; rewrite /= ;
    move => * ; abstract intuition Omega.omega.

  Ltac tac_degrade_union v_ A x :=
    move: (regularCardinalMax_unionfilter
             (fun A x => ~~ Sol.isSolb (v_ A x))
             (fun A x => Sol.isSolb (v_ A x))
             (fun A x => grade (v_ A x)));
    move: (regularCardinalMax_unionfilter
             (fun A x => ~~ Sol.isSolb (v_ A x))
             (fun A x => Sol.isSolb (v_ A x))
             (fun A x => gradeTotal (v_ A x)));
    (have: (~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x))
      by (case: (Sol.isSolb (v_ A x)); intuition)); intros Hlogical;
    move: (Hlogical) =>
    /(@regularCardinalMax_ge
        _ _ (fun A x => ~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x))
        (fun (A0 : obIndexer) (x0 : func0 A0) => grade (v_ A0 x0)) );
    move: Hlogical =>
    /(@regularCardinalMax_ge
        _ _ (fun A x => ~~ Sol.isSolb (v_ A x) \/ Sol.isSolb (v_ A x))
        (fun (A0 : obIndexer) (x0 : func0 A0) => gradeTotal (v_ A0 x0)) ).

  Ltac tac_degrade_transf v_ transf :=
    move: (regularCardinalMax_transf
             (fun A0 x => ~~ Sol.isSolb (v_ A0 x))
             (fun A0 x => grade (v_ A0 x)) transf)
            (regularCardinalMax_transf
               (fun A0 x => Sol.isSolb (v_ A0 x))
               (fun A0 x => grade (v_ A0 x)) transf)
            (regularCardinalMax_transf
               (fun A0 x => ~~ Sol.isSolb (v_ A0 x))
               (fun A0 x => gradeTotal (v_ A0 x)) transf)
            (regularCardinalMax_transf
               (fun A0 x => Sol.isSolb (v_ A0 x))
               (fun A0 x => gradeTotal (v_ A0 x)) transf);
    rewrite !/funcomp.

  Fixpoint solveTopos len {struct len} :
    forall (F1 F2 : obTopos) (f : 'Topos(0 F1 ~> F2 )0)
      (H_gradeTotal : (gradeTotal f <= len)%coq_nat),
      { fSol : 'Topos(0 F1 ~> F2 )0 %sol
      & {( (Sol.toTopos fSol) <~~ f )} + {( (Sol.toTopos fSol) = f )} }.
  Proof.
    case : len => [ | len ].

    (* n is O *)
    - clear; ( move => F1 F2 f H_gradeTotal ); exfalso;
        move : (Red.degradeTotal_gt0 f) => H_degradeTotal_gt0; abstract Omega.omega.

    (* n is (S n) *)
    - move => F1 F2 f; case : F1 F2 / f =>
      [ F  (* @uTopos F *)
      | F1 F2 f_ F1' f' (* f_ o>Topos f' *)
      | A A' a (* View1 a *)
      | func0 func1 A x (* PolyMetaFunctor func1 x *)
      | func0 func1 func'0 func'1 transf A f (* f o>Topos_transf *)
      | func0 func1 F v_ ] (* [[ v_ @ func1 ]] *).

      (* f is @uTopos F *)
      + move => H_gradeTotal. exists (@uTopos F)%sol. right. reflexivity.

      (* f id f_ o>Topos f' *)
      + all: cycle 1. 
        
      (* f is View1 a *)
      + move => H_gradeTotal. exists (Sol.View1 a). right. reflexivity.
      
      (* f is PolyMetaFunctor func1 x *)
      + move => H_gradeTotal. exists (Sol.PolyMetaFunctor func1 x). right. reflexivity.

      (* f is f o>Topos_transf *)
      + move => H_gradeTotal.
        case : (solveTopos len _ _ f) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega.
        * { clear - solveTopos H_gradeTotal fSol_prop.
            move: (Sol.Destruct_domView_codomMetaFunctor.Topos00_domView_codomMetaFunctorP fSol) => fSol_domView_codomMetaFunctorP.
            destruct fSol_domView_codomMetaFunctorP as
                [ func0 func1 A x (* SolPolyMetaFunctor func1 x *) ].
            
            + exists (Sol.PolyMetaFunctor func'1 (transf A x))%sol.
              clear -fSol_prop. tac_reduce.
          }

      (* f is [[ v_ @ func1 ]] *)
      + move => H_gradeTotal.
        have gradeTotal_v_ : forall A x , (gradeTotal (v_ A x) <= len)%coq_nat.
        { move => A x.
          clear -H_gradeTotal.
          tac_degrade_union v_ A x.
          move: H_gradeTotal; clear; simpl;
            abstract intuition Omega.omega.
        }
        
        set solveTopos_v_ := (fun A x => solveTopos len (View0 A) F (v_ A x) (gradeTotal_v_ A x)).
        set vSol_ := (fun A x => projT1 (solveTopos_v_ A x)).
        set vSol_prop_ := (fun A x => projT2 (solveTopos_v_ A x)).
        set vSol_propb_ := (fun A x => ~~ ((projT2 (solveTopos_v_ A x)) : bool)).

        case: (regularCardinalAllP (fun A x => Sol.isSolb (v_ A x))) => H_someRed.
        * have vSol_prop_isRed_: forall (A : obIndexer) (x : func0 A),
            ~~ Sol.isSolb (v_ A x) ->
            Sol.toTopos (vSol_ A x) <~~ v_ A x .
          { clear - vSol_prop_. intros A x.
            (case: (vSol_prop_ A x) => //= ) ;
              ( case (Sol.isSolbP2 (v_ A x)) => //= ).
            move: (solveTopos_v_ A x) vSol_. clear. intros; exfalso.
            intuition eauto.
          }

          have vSol_prop_isSol_: forall (A : obIndexer) (x : func0 A),
              Sol.isSolb (v_ A x) ->
              Sol.toTopos (vSol_ A x) = v_ A x .
          { clear - vSol_prop_. intros A x. (case: (vSol_prop_ A x) => //= ) .
            ( case (Sol.isSolbP2 (v_ A x)) => //= ).
            intros [v_A_x_Sol v_A_x_Sol_prop] v_A_x_Red; exfalso;
            apply: Red.isSolb_isRed_False; eassumption.
          }

          exists [[ fun A x => (vSol_ A x) ]]%sol. left.
          clear - H_someRed vSol_prop_isRed_ vSol_prop_isSol_ .
          simpl. move: H_someRed  => [A [x H_someRed_prop] ].
          apply: Red.CoLimitator_cong; [assumption | assumption | | eassumption].
          intros; apply/(introT (Sol.isSolbP2 (_))); eexists; reflexivity.

        * have v_A_x_allSol : forall A x,  ({ fSol  | Sol.toTopos fSol = v_ A x}).
          { intros. apply: Sol.isSolb_isSol.
            case E : (Sol.isSolb _) => //=. exfalso; apply: H_someRed.
            exists A , x . by move: E => -> . }

          set v_A_x_allSol_data := (fun A x => projT1 (v_A_x_allSol A x)).
          set v_A_x_allSol_prop := (fun A x => projT2 (v_A_x_allSol A x)).

          exists [[ fun A x => (v_A_x_allSol_data A x) ]]%sol. right.
          simpl; apply: congr1.
          apply: (topos_functional_extensionality func1) => A x.
          apply: v_A_x_allSol_prop.

    - (* f is f_ o>Topos f' *)
      move => H_gradeTotal.
      case : (solveTopos len _ _ f_) =>
        [ | f_Sol f_Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega | ].
        case : (solveTopos len _ _ f') =>
        [ | f'Sol f'Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite /gradeTotal /=; move => *; abstract Omega.omega | ].

        (* f is (f_ o>Mod f') , to (f_Sol o>Mod f'Sol) *)
        destruct f_Sol as
            [ F  (* @uTopos F %sol*)
            | A A' f_a (* SolView1 f_a *)
            | func0 func1 A x (* SolPolyMetaFunctor func1 x *)
            | func0 func1 F f_Sol_ ] (* [[ f_Sol_ @ func1 ]] %sol *).


      (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is ((@uTopos F) o>Topos f'Sol) *)
      + case : (solveTopos len _ _ ((Sol.toTopos f'Sol))) =>
        [ | f_Sol_o_f'Sol f_Sol_o_f'Sol_prop ].
        * tac_degrade H_gradeTotal f_Sol_prop f'Sol_prop.
        * exists (f_Sol_o_f'Sol).
          clear -f_Sol_prop f'Sol_prop f_Sol_o_f'Sol_prop. tac_reduce.

      (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (View1 f_a o>Topos f'Sol) *)
      + clear - solveTopos H_gradeTotal f_Sol_prop f'Sol_prop.
        move: (Sol.Destruct_domView.Topos00_domViewP f'Sol) => f'Sol_domViewP.
        destruct f'Sol_domViewP as
            [ _A  (* @uTopos F %sol*)
            | _A A' f'a (* SolView1 f'a *)
            | func0 func1 _A x (* SolPolyMetaFunctor func1 x *) ].

        (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (View1 f_a o>Topos f'Sol) , is  (View1 f_a o>Topos (@uTopos _A)) *)
        * exists ( (Sol.View1 f_a)%sol ) .
          clear -f_Sol_prop f'Sol_prop. tac_reduce.

        (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (View1 f_a o>Topos f'Sol) , is  (View1 f_a o>Topos View1 f'a) *)            
        * exists (Sol.View1 (f_a o>Indexer f'a)%sol).
          clear -f_Sol_prop f'Sol_prop. tac_reduce.

        (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (View1 f_a o>Topos f'Sol) , is  (View1 f_a o>Topos SolPolyMetaFunctor func1 x) *)
        * exists (Sol.PolyMetaFunctor func1 (func1 _ _ f_a x)%sol).
          clear -f_Sol_prop f'Sol_prop. tac_reduce.

      (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (SolPolyMetaFunctor func1 x o>Topos f'Sol) *)
      + clear - solveTopos H_gradeTotal f_Sol_prop f'Sol_prop.
        move: (Sol.Destruct_domMetaFunctor.Topos00_domMetaFunctorP f'Sol) => f'Sol_domMetaFunctorP.
        destruct f'Sol_domMetaFunctorP as
            [ func0 func1  (* @uTopos (MetaFunctor func1) %sol*)
            | func0 func1 F f'Sol_ ] (* [[ f'Sol_ @ func1 ]] *).

        (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (SolPolyMetaFunctor func1 x o>Topos (@uTopos (MetaFunctor func1))) *)
        * exists ( Sol.PolyMetaFunctor func1 x )%sol .
          clear -f_Sol_prop f'Sol_prop. tac_reduce.

        (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is (SolPolyMetaFunctor func1 x o>Topos [[ f'Sol_ ]]) *)
        * exists ((f'Sol_ A x))%sol.
          clear -f_Sol_prop f'Sol_prop. tac_reduce.

      (* f is (f_ o>Topos f') , to (f_Sol o>Topos f'Sol)  , is ( [[ f_Sol_ ]] o>Topos f'Sol) *)
      + have gradeTotal_f_Sol_o_f'Sol : forall A x , (gradeTotal (((fun A1 x1 => Sol.toTopos (f_Sol_ A1 x1)) A x) o>Topos (Sol.toTopos f'Sol)) <= len)%coq_nat.
        { move => A x.
          clear -H_gradeTotal f_Sol_prop f'Sol_prop.
          tac_degrade_union (fun A1 x1 => Sol.toTopos (f_Sol_ A1 x1)) A x.
          tac_degrade H_gradeTotal f_Sol_prop f'Sol_prop.
        }

        set v_ := (fun A x => (((fun A1 x1 => Sol.toTopos (f_Sol_ A1 x1)) A x) o>Topos (Sol.toTopos f'Sol))).
        set solveTopos_v_ := (fun A x => solveTopos len (View0 A) F1' (v_ A x) (gradeTotal_f_Sol_o_f'Sol A x)).
        set f_Sol_o_f'Sol := (fun A x => projT1 (solveTopos_v_ A x)).
        set f_Sol_o_f'Sol_prop := (fun A x => projT2 (solveTopos_v_ A x)).
        set f_Sol_o_f'Sol_propb := (fun A x => ~~ ((projT2 (solveTopos_v_ A x)) : bool)).

        exists ([[ f_Sol_o_f'Sol ]])%sol. left.

        (* now similar as the above congruence case:  f is [[ v_ @ func1 ]] *)
        case: (regularCardinalAllP (fun A x => Sol.isSolb (v_ A x))) => H_someRed.
        * { apply: (Red.Topos_Trans (uTrans := [[ v_ ]] ));
            first by clear -f_Sol_prop f'Sol_prop; subst v_; tac_reduce.

            clear -H_someRed f_Sol_o_f'Sol_prop.
            have f_Sol_o_f'Sol_prop_isRed_ : forall (A : obIndexer) (x : func0 A),
                ~~ Sol.isSolb (v_ A x) ->
                Sol.toTopos (f_Sol_o_f'Sol A x) <~~ (v_ A x) .
            { intros A x.  (case: (f_Sol_o_f'Sol_prop A x) => // ) ;
              ( case (Sol.isSolbP2 (v_ A x)) => //= ) .
              move: (f_Sol_o_f'Sol A x) ((solveTopos_v_ A x)). move: (v_ A x).
              clear. intros. exfalso. intuition eauto.
            }

            have f_Sol_o_f'Sol_prop_isSol_ : forall (A : obIndexer) (x : func0 A),
                Sol.isSolb (v_ A x) ->
                Sol.toTopos (f_Sol_o_f'Sol A x) = v_ A x .
            { by []. (* shorter exfalso on form of v_ *)
            }

            clear - H_someRed f_Sol_o_f'Sol_prop_isRed_ f_Sol_o_f'Sol_prop_isSol_ .
            move: H_someRed  => [A [x H_someRed_prop] ].
            apply: Red.CoLimitator_cong;
              [assumption | assumption | | eassumption].
            intros A1 x1; apply/(introT (Sol.isSolbP2 (_))); eexists; reflexivity.
          }
        * (* memo: contradictory context [ H_someRed constrast form of v_ ] 
             when the elements (A , x) of functor are non-empty *)
          suff: Sol.toTopos [[f_Sol_o_f'Sol]]%sol = [[ v_ @ func1 ]]
            by move ->; clear -f_Sol_prop f'Sol_prop; subst v_; tac_reduce.

          clear -H_someRed. simpl; apply: congr1.
          apply: (topos_functional_extensionality func1) => A x.
          (* here the elements (A , x) of functor are non-empty *)
          exfalso. apply: H_someRed. exists A , x. reflexivity.

  Defined.

End Section1.

End METAFUNCTORS.

(**#+END_SRC

Voila. **)
