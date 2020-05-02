(** # #
#+TITLE: cartierSolution1.v

Proph

https://github.com/1337777/cartier/blob/master/cartierSolution1.v

shows the general outline of the solutions to some question of CARTIER which is how to program « geometric homotopic parametrization modos » ... 

The outline is along two examples : the comonad cut-elimination and the adjunction cut-elimination , both formulated in the common style of the pairing-projections cancellation for the cartesian-product .

OUTLINE ::

  * Generating objects and generating morphisms

  * Grammatical presentation of the objects

  * Grammatical presentation of the morphisms

  * Grammatical presentation of the conversions

  * Linear total/asymptotic grade and the degradation lemma

  * Solution morphisms
    + Solution morphisms without composition
    + Cases-refinement of morphisms with inner-instantiation of the domain object-index

  * Composition/cut-elimination into polymorphic soiution by computational/total/asymptotic/reduction/(multi-step) resolution using conversions

-----

PART 1 : COMONAD (NON-IDEMPOTENT)

* Generating objects and generating morphisms

#+BEGIN_SRC coq :exports both :results silent # # **)
Require Import ssreflect ssrfun ssrbool.
Require Lia.

Module COMONAD. (** non-idempotent comonad *)

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections.

Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Module Mole.

  Parameter obMod_Gen : Type.
  Parameter morMod_Gen : forall F F' : obMod_Gen, Type.

  Inductive obMod : Type := 
  | ObMod_Gen : obMod_Gen -> obMod .

  Reserved Notation "''Mod' (  F  ~>  F'  )" (at level 0).

  Section Section1.
  Delimit Scope mole_scope with mole.

  Inductive morMod : forall F F' : obMod, Type :=

  | Composition : forall F F' : obMod, 'Mod( F ~> F' ) ->
                                      forall F'' : obMod, 'Mod( F' ~> F'' ) -> 'Mod( F ~> F'' )

  | MorMod_Gen : forall F F' : obMod_Gen, @morMod_Gen F F' ->
                                     'Mod( ObMod_Gen F ~> ObMod_Gen F' )

  where "''Mod' ( F ~> F' )" := (@morMod F F') : mole_scope.
  End Section1.

  Module Import Ex_Notations.
    Delimit Scope mole_scope with mole.
  
    Notation "''Mod' ( F ~> F' )" := (@morMod F F') : mole_scope.
    Notation "ff_  o>  ff'" := (@Composition _ _ ff_ _ ff')
         (at level 40 , ff' at next level , left associativity) : mole_scope.
  End Ex_Notations.

End Mole.
(** # #
#+END_SRC

* Grammatical presentation of the objects

#+BEGIN_SRC coq :exports both :results silent # # **)
Import Mole.Ex_Notations.

Inductive obMod : Type :=
  ConstantOfProduct : obMod -> obMod
| ObMod_Mole : Mole.obMod -> obMod. 
(** # #
#+END_SRC

* Grammatical presentation of the morphisms

#+BEGIN_SRC coq :exports both :results silent # # **)
Reserved Notation "''Mod' (  F  ~>  F'  )" (at level 0).

Inductive morMod : forall F F' : obMod, Type :=

| Composition : forall F F' : obMod, 'Mod( F ~> F' ) -> forall F'' : obMod, 'Mod( F' ~> F'' ) -> 'Mod( F ~> F'' )

| Unit : forall F : obMod, 'Mod( F ~> F )

| Projections_PolyPost : forall F F' : obMod, 'Mod( F ~> F' ) -> 'Mod( ConstantOfProduct F ~> F' )

| ConstantOfPairing_aka_ReverseOfProjections_PolyPre :
    forall F F' : obMod, 'Mod( ConstantOfProduct F ~> F' ) -> 'Mod( ConstantOfProduct F ~> ConstantOfProduct F' ) 

| MorMod_Mole : forall F F' : Mole.obMod,
    'Mod( F ~> F' ) %mole -> 'Mod( ObMod_Mole F ~> ObMod_Mole F' )

where "''Mod' ( F ~> F' )" := (@morMod F F') : poly_scope.

Notation "ff_  o>  ff'" := (@Composition _ _ ff_ _ ff')
         (at level 40 , ff' at next level , left associativity) : poly_scope.

Notation "@ ''Unit'  F" := (@Unit F)
          (at level 10, F at next level, only parsing) : poly_scope.

Notation "''Unit'" := (@Unit _) (at level 0) : poly_scope.

Notation "''Projections'  o>  ff" :=
  (@Projections_PolyPost _ _ ff) (at level 10, ff at next level) : poly_scope.

Notation "ff  o>  'Pairing" :=
  (@ConstantOfPairing_aka_ReverseOfProjections_PolyPre _ _ ff) (at level 4, right associativity) : poly_scope.

Notation "''MorMod_Mole' ff" :=
  (@MorMod_Mole _ _ ff) (at level 10, ff at next level) : poly_scope.
(** # #
#+END_SRC

* Grammatical presentation of the conversions

#+BEGIN_SRC coq :exports both :results silent # # **)
Reserved Notation "ff' <~~ ff" (at level 70).

Inductive convMod : forall (F F' : obMod), 'Mod( F ~> F' ) -> 'Mod( F ~> F' ) -> Prop :=

(**  ----- the total/(multi-step) conversions -----  **)
| convMod_Refl : forall (F F' : obMod), forall ff : 'Mod( F ~> F' ),
      ff <~~ ff
  
| convMod_Trans : forall (F F' : obMod), forall ff ff0 ff_trans : 'Mod( F ~> F' ),
      ff_trans <~~ ff -> ff0 <~~ ff_trans -> ff0 <~~ ff
  
(**  ----- the congruences (recursive) conversions for morphisms -----  **)

| Composition_cong : forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ), forall F'' : obMod, forall ff' ff'0 : 'Mod( F' ~> F'' ),
          ff0 <~~ ff -> ff'0 <~~ ff' ->
          ( ff0 o> ff'0 ) <~~ ( ff o> ff' )

| Projections_PolyPost_cong : forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ),
      ( ff0 ) <~~ ( ff ) ->
      ( 'Projections o> ff0 ) <~~ ( 'Projections o> ff )

| ConstantOfPairing_aka_ReverseOfProjections_PolyPre_cong :
    forall F F' : obMod, forall ff ff0 : 'Mod( ConstantOfProduct F ~> F' ),
      ( ff0 ) <~~ ( ff ) ->
      ( ff0 o> 'Pairing ) <~~ ( ff o> 'Pairing )
  
(** ----- the constant conversions which are used during the polymorphism elimination ----- 
    This polymorphism elimination proceeds by : 
    - firstly destructing the pre/left/input argument of the composition ,
    - lastly destructing the post/right/operator argument of the composition .
    The precedence is better for describing this non-idempotent comonad . *)

| Unit_comp_morMod : forall F F' : obMod, forall ff : 'Mod( F ~> F' ),
      ( ff ) <~~ ( 'Unit o> ff )

| Projections_PolyPost_comp_morMod : forall F F' : obMod, forall ff : 'Mod( F ~> F' ),
      forall F'' : obMod , forall ff' : 'Mod( F' ~> F'' ),
          ( 'Projections o> ( ff o> ff' ) )
              <~~ ( ( 'Projections o> ff ) o> ff' )

| morMod_comp_Unit :
    forall F F' : obMod, forall ff : 'Mod(  F ~> F' ),
        ( ff ) <~~ ( ff o> 'Unit )

| ConstantOfPairing_aka_ReverseOfProjections_comp_PolyPre_Projections_PolyPost :
    forall F F' : obMod, forall ff : 'Mod( ConstantOfProduct F ~> F' ), forall F'' : obMod, forall ff' : 'Mod( F' ~> F'' ),
            ( ff o> ff' )
              <~~ ( ( ff o> 'Pairing ) o> ( 'Projections o> ff' ) )

(** memo: the prefix morphism is not of general form , but is of the form of the form 
   [ConstantOfPairing_aka_ReverseOfProjections_PolyPre] because otherwise the sense is idempotent comonad ,
   which produces some preorder  *)              
| ConstantOfPairing_aka_ReverseOfProjections_PolyPre_comp_ConstantOfPairing_aka_ReverseOfProjections_PolyPre :
    forall F F' : obMod, forall ff : 'Mod( ConstantOfProduct F ~> F' ),
    forall F'' : obMod, forall ff' : 'Mod( ConstantOfProduct F' ~> F'' ),
        ( ( ( ff o> 'Pairing ) o> ff' ) o> 'Pairing ) 
          <~~ ( ( ff o> 'Pairing ) o> ( ff' o> 'Pairing ) )

| MorMod_Mole_comp_MorMod_Mole :  forall F F' : Mole.obMod, forall ff : 'Mod( F ~> F' ) %mole, forall F'' : Mole.obMod, forall ff' : 'Mod( F' ~> F'' ) %mole,
          ( MorMod_Mole (ff o> ff')%mole )
            <~~ ( ( MorMod_Mole ff ) o> ( MorMod_Mole ff' ) )

(** ----- the constant conversions which are not for polymorphism elimination 
          but are only for the wanted sense of extensionality for comonad ----- **)

| ConstantOfPairing_aka_ReverseOfProjections_subst_PolyPre_Projections_PolyPost :
    forall F : obMod, 
            ( @'Unit ( ConstantOfProduct F ) )
              <~~ (  ( 'Projections o> ( @'Unit F ) ) o> 'Pairing )

where "ff' <~~ ff" := (@convMod _ _ ff ff').

Hint Constructors convMod : core.
(** # #
#+END_SRC

* Linear total/asymptotic grade and the degradation lemma

#+BEGIN_SRC coq :exports both :results silent # # **)
Arguments Nat.add : simpl nomatch.

Definition grade :
   forall F F' : obMod, forall ff : 'Mod( F ~> F' ), nat .
Proof.
  intros F F' ff. elim: F F' / ff.
  - (**) intros F F' ff grade_ff F'' ff' grade_ff' .
    exact: ( 2 * (S (grade_ff + grade_ff')%nat ) )%nat . 
  - intros F.
    exact: (S O).
  - intros F F' ff grade_ff. 
    exact: (S grade_ff).
  - intros F F' ff grade_ff. 
    exact: (S grade_ff).
  - intros F F' ff.
    exact: (S O).
Defined.

Arguments grade : simpl nomatch.

Lemma grade_gt0 :
  forall F F' : obMod, forall ff : 'Mod( F ~> F' ), 
      ((S O) <= (grade ff))%nat .
Proof.
  intros F F' ff. elim: F F' / ff ;
    simpl; intros; abstract Lia.lia.
Qed.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ ) ,
                  gg3 : 'Mod( _ ~> _ ) ,
                        gg4 : 'Mod( _ ~> _ ) |- _ ] =>
    move : (@grade_gt0 _ _ gg1) (@grade_gt0 _ _ gg2)
                                          (@grade_gt0 _ _ gg3)
                                          (@grade_gt0 _ _ gg4)
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ ) ,
                  gg3 : 'Mod( _ ~> _ ) |- _ ] =>
    move : (@grade_gt0 _ _ gg1) (@grade_gt0 _ _ gg2)
                                          (@grade_gt0 _ _ gg3)
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ )  |- _ ] =>
    move : (@grade_gt0 _ _ gg1) (@grade_gt0 _ _ gg2)
  | [ gg1 : 'Mod( _ ~> _ )  |- _ ] =>
    move : (@grade_gt0 _ _ gg1) 
  end.

Lemma degrade :
  forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ),
      ff0 <~~ ff  -> ( grade ff0 <= grade ff )%nat .
Proof.
  intros F F' ff ff0 convMod_ff0_ff .
  Time elim: F F' ff ff0 / convMod_ff0_ff;
    try solve [simpl; try tac_grade_gt0;
                 simpl; intros; abstract Lia.lia].
  (* "Finished transaction in 0.258 secs (0.258u,0.s) (successful)" *)
Qed.
(** # #
#+END_SRC

* Solution morphisms

** Solution morphisms without composition

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Sol.
Section Section1.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Inductive morMod : forall F F' : obMod, Type :=

| Unit : forall F : obMod, 'Mod( F ~> F )

| Projections_PolyPost : forall F F' : obMod, 'Mod( F ~> F' ) -> 'Mod( ConstantOfProduct F ~> F' )

| ConstantOfPairing_aka_ReverseOfProjections_PolyPre :
    forall F F' : obMod, 'Mod( ConstantOfProduct F ~> F' ) -> 'Mod( ConstantOfProduct F ~> ConstantOfProduct F' ) 

| MorMod_Mole : forall F F' : Mole.obMod,
    'Mod( F ~> F' ) %mole -> 'Mod( ObMod_Mole F ~> ObMod_Mole F' )

where "''Mod' ( F ~> F' )" := (@morMod F F') : sol_scope.
End Section1.

Module Export Ex_Notations.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Notation "''Mod' ( F ~> F' )" := (@morMod F F') : sol_scope.

Notation "@ ''Unit'  F" := (@Unit F)
          (at level 10, F at next level, only parsing) : sol_scope.

Notation "''Unit'" := (@Unit _) (at level 0) : sol_scope.

Notation "''Projections'  o>  ff" :=
  (@Projections_PolyPost _ _ ff) (at level 10, ff at next level) : sol_scope.

Notation "ff  o>  'Pairing" :=
  (@ConstantOfPairing_aka_ReverseOfProjections_PolyPre _ _ ff) (at level 4, right associativity) : sol_scope.

Notation "''MorMod_Mole' ff" :=
  (@MorMod_Mole _ _ ff) (at level 10, ff at next level) : sol_scope.
End Ex_Notations.

Definition toPolyMor :
   forall F F' : obMod, 'Mod( F ~> F' )%sol ->  'Mod( F ~> F' )%poly .
Proof.
  intros F F' ff . elim: F F' / ff.

  - (** Unit *) intros F .
    exact: ( @'Unit F ) %poly.
  - (** Projections_PolyPost *)
    intros F F' ff toPolyMor_ff . 
    exact: ( 'Projections o> toPolyMor_ff ) %poly.
  - (** ConstantOfPairing_aka_ReverseOfProjections_PolyPre *)
    intros F F' ff toPolyMor_ff . 
    exact: ( toPolyMor_ff o> 'Pairing ) %poly.
  - (** MorMod_Mole **) intros F F' ff.
    exact: ( 'MorMod_Mole ff )%poly. 
Defined.

Arguments toPolyMor : simpl nomatch.
(** # #
#+END_SRC

** Cases-refinement of morphisms with inner-instantiation of the domain object-index

#+BEGIN_SRC coq :exports both :results silent # # **)
Module MorMod_domConstantOfProduct.
Inductive morMod
: forall F F' : obMod, 'Mod( ConstantOfProduct F ~> F' )%sol -> Type :=
| Unit :  forall F : obMod, 
    morMod ( @'Unit (ConstantOfProduct F) )%sol

| Projections_PolyPost : forall F F' : obMod, forall ff : 'Mod( F ~> F' )%sol,
      morMod ( 'Projections o> ff )%sol

| ConstantOfPairing_aka_ReverseOfProjections_PolyPre :
    forall F F' : obMod, forall ff : 'Mod( ConstantOfProduct F ~> F' )%sol,
      morMod ( ff o> 'Pairing )%sol.
End MorMod_domConstantOfProduct.

Module MorMod_domObMod_Mole.
Inductive morMod
: forall (F : Mole.obMod) (F' : obMod), 'Mod( ObMod_Mole F ~> F' )%sol -> Type :=
| Unit :  forall F : Mole.obMod, 
    morMod ( @'Unit (ObMod_Mole F) )%sol

| MorMod_Mole : forall F F' : Mole.obMod,
    forall ff : 'Mod( F ~> F' ) %mole,
      morMod ( 'MorMod_Mole ff )%sol.
End MorMod_domObMod_Mole.

Lemma morMod_domP
  : forall F F' : obMod, forall ff : 'Mod( F ~> F' )%sol,
      ltac:( destruct F; [ refine (MorMod_domConstantOfProduct.morMod ff)
                         | refine (MorMod_domObMod_Mole.morMod ff) ] ).
Proof. 
  intros. destruct ff.
  - destruct F; [ constructor 1 | constructor 1].
  - constructor 2.
  - constructor 3.
  - constructor 2.
Defined.
End Sol.
(** # #
#+END_SRC

* Composition/cut-elimination into polymorphic soiution by computational/total/asymptotic/reduction/(multi-step) resolution using conversions

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Resolve.
Export Sol.Ex_Notations.

Ltac tac_degrade H_grade :=
  intuition idtac;
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
           move : (degrade Hred) ; clear Hred
         end;
  move: H_grade; clear; simpl;
  intros; try tac_grade_gt0; intros; Lia.lia.

Ltac tac_simpl := simpl.
Ltac tac_reduce := tac_simpl; repeat (intro; tac_simpl); intuition eauto 9.

Fixpoint solveMod len {struct len} :
 forall F F' : obMod, forall ff : 'Mod( F ~> F' ), forall grade_ff : (grade ff <= len)%nat,
   { ffSol : 'Mod( F ~> F' )%sol | (Sol.toPolyMor ffSol) <~~ ff } .
Proof.
case : len => [ | len ].

(** len is O **)
- intros F F' ff grade_ff; exfalso;
    clear - grade_ff; abstract tac_degrade grade_ff.

(** len is (S len) **)
-  intros F F' ff.  case : F F' / ff;
   [ intros F F' ff F'' ff' grade_ff
   | intros F grade_ff
   | intros F F' ff grade_ff 
   | intros F F' ff grade_ff
   | intros F F' ff grade_ff ]. 

(** ff is  (ff o> ff') *) all: cycle 1.
   
(** ff is  (@'Unit F) **)
+ unshelve eexists. refine ( @'Unit F )%sol.
  clear; abstract tac_reduce.
  
(** ff is  ('Projections o> ff) **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff blurb)) ffSol_transp => ffSol ffSol_transp .
  clear solveMod.

  unshelve eexists. refine ( 'Projections o> ffSol )%sol.
  move: ffSol_transp; clear; abstract tac_reduce. 

(** ff is  (ff o> 'Pairing)  **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff blurb)) ffSol_transp => ffSol ffSol_transp .
  clear solveMod.

  unshelve eexists. refine ( ffSol o> 'Pairing )%sol.
  move: ffSol_transp; clear; abstract tac_reduce. 

(** ff is  ('MorMod_Mole ff) **)
+ unshelve eexists. refine ( 'MorMod_Mole ff )%sol.
  clear; abstract tac_reduce.

(** ff is  (ff o> ff') **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff blurb)) ffSol_transp => ffSol ffSol_transp .
  have [:blurb] ff'Sol_transp :=
    (proj2_sig (solveMod len _ _ ff' blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff' blurb)) ff'Sol_transp => ff'Sol ff'Sol_transp .

  (** ff is  (ff o> ff') , to (ffSol o> ff'Sol)  **)
  destruct ffSol as
   [ F 
   | F F' ffSol  
   | F F' ffSol  
   | F F' ffSol  ]. 

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
         is ((@'Unit F) o> ff'Sol) **)
  * unshelve eexists. refine (ff'Sol)%sol.
    move:ffSol_transp ff'Sol_transp; clear;
      abstract (tac_simpl; intros; eapply convMod_Trans with
                                   (ff_trans := ('Unit) o> ff'); tac_reduce).

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( ('Projections o> ffSol) o> ff'Sol **)
  * have [:blurb] ffSol_o_ff'Sol_transp :=
      (proj2_sig (solveMod len _ _ (Sol.toPolyMor ffSol o> Sol.toPolyMor ff'Sol) blurb));
        first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
    move: (sval (solveMod len _ _ (Sol.toPolyMor ffSol o> Sol.toPolyMor ff'Sol) blurb)) ffSol_o_ff'Sol_transp 
        => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
    clear solveMod .
    
    unshelve eexists.
    refine ( 'Projections o> ffSol_o_ff'Sol )%sol.
    move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
    abstract (tac_simpl; intros; eapply convMod_Trans with
        (ff_trans := ( 'Projections o> (Sol.toPolyMor ffSol) ) o> ( Sol.toPolyMor ff'Sol )); tac_reduce).
    
  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( (ffSol o> 'Pairing) o> ff'Sol ) **)
  * move: (Sol.morMod_domP ff'Sol) => ff'Sol_morMod_domP.
    { destruct ff'Sol_morMod_domP as
          [ _F
          | _F F' ff'Sol
          | _F F' ff'Sol ].

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( (ffSol o> 'Pairing) o> ('Unit) ) **)
      - unshelve eexists. refine (ffSol o> 'Pairing)%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := ( (Sol.toPolyMor ffSol) o> 'Pairing) o> ('Unit)); tac_reduce).

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( (ffSol o> 'Pairing) o> ('Projections o> ff'Sol) ) **)
      -  have [:blurb] ffSol_o_ff'Sol_transp :=
           (proj2_sig (solveMod len _ _ (Sol.toPolyMor ffSol o> Sol.toPolyMor ff'Sol) blurb));
             first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
         move: (sval (solveMod len _ _ (Sol.toPolyMor ffSol o> Sol.toPolyMor ff'Sol) blurb)) ffSol_o_ff'Sol_transp 
         => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
         clear solveMod .

        unshelve eexists.
        refine ( ffSol_o_ff'Sol )%sol.
        move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                 (ff_trans := ((Sol.toPolyMor ffSol) o> 'Pairing) o> ('Projections o> (Sol.toPolyMor ff'Sol))); tac_reduce). 

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( (ffSol o> 'Pairing) o> (ff'Sol o> 'Pairing) ) **)
      - pose Sol_toPolyMor_ffSol := ( (Sol.toPolyMor ffSol) o> 'Pairing ).
         have [:blurb] ffSol_o_ff'Sol_transp :=
          (proj2_sig (solveMod len _ _ (Sol_toPolyMor_ffSol o> (Sol.toPolyMor ff'Sol)) blurb));
            first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
        move: (sval (solveMod len _ _ (Sol_toPolyMor_ffSol o> (Sol.toPolyMor ff'Sol)) blurb)) ffSol_o_ff'Sol_transp 
        => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
        clear solveMod .

        unshelve eexists.
        refine ( ffSol_o_ff'Sol o> 'Pairing )%sol.
        move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                                           (ff_trans := Sol_toPolyMor_ffSol o> ((Sol.toPolyMor ff'Sol) o> 'Pairing));
                    subst Sol_toPolyMor_ffSol;  tac_reduce).
    }

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( ('MorMod_Mole ffSol) o> ff'Sol ) **)
  * move: (Sol.morMod_domP ff'Sol) => ff'Sol_morMod_domP.
    { destruct ff'Sol_morMod_domP as
          [ _F
          | _F F' ff'Sol ].

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ('MorMod_Mole ffSol) o> ('Unit) ) **)
      - unshelve eexists. refine ( 'MorMod_Mole ffSol )%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := ( 'MorMod_Mole ffSol ) o> ('Unit)); tac_reduce).

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ('MorMod_Mole ffSol) o> ('MorMod_Mole ff'Sol) ) **)
      - unshelve eexists. refine ( 'MorMod_Mole (ffSol o> ff'Sol)%mole )%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := ( 'MorMod_Mole ffSol ) o> ( 'MorMod_Mole ff'Sol )); tac_reduce).
    }
Defined.
End Resolve.
End COMONAD.
(** # #
#+END_SRC

-----

PART 2 : ADJUNCTION

* Generating objects and generating morphisms

#+BEGIN_SRC coq :exports both :results silent # # **)
Module ADJUNCTION.

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections.

Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Module Mole.

  Parameter obMod_Gen : Type.
  Parameter morMod_Gen : forall F F' : obMod_Gen, Type.
  Parameter obCoMod_Gen : Type.
  Parameter morCoMod_Gen : forall S S' : obCoMod_Gen, Type.

  Inductive obMod : Type := 
  | ObMod_Gen : obMod_Gen -> obMod.

  Inductive obCoMod : Type := 
  | ObCoMod_Gen : obCoMod_Gen -> obCoMod.

  Reserved Notation "''Mod' (  F  ~>  F'  )" (at level 0).
  Reserved Notation "''CoMod' (  S  ~>  S'  )" (at level 0).

  Section Section1.
  Delimit Scope mole_scope with mole.

  Inductive morMod : forall F F' : obMod, Type :=

  | CompositionMod : forall F F' : obMod, 'Mod( F ~> F' ) -> forall F'' : obMod, 'Mod( F' ~> F'' ) -> 'Mod( F ~> F'' )

  | MorMod_Gen : forall F F' : obMod_Gen, @morMod_Gen F F' ->
                                     'Mod( ObMod_Gen F ~> ObMod_Gen F' )

  where "''Mod' ( F ~> F' )" := (@morMod F F') : mole_scope.
  Inductive morCoMod : forall S S' : obCoMod, Type :=

  | CompositionCoMod : forall S S' : obCoMod, 'CoMod( S ~> S' ) -> forall S'' : obCoMod, 'CoMod( S' ~> S'' ) -> 'CoMod( S ~> S'' )

  | MorCoMod_Gen : forall S S' : obCoMod_Gen, @morCoMod_Gen S S' ->
                                         'CoMod( ObCoMod_Gen S ~> ObCoMod_Gen S' )

  where "''CoMod' ( S ~> S' )" := (@morCoMod S S') : mole_scope.
  End Section1.

  Module Import Ex_Notations.
    Delimit Scope mole_scope with mole.
  
    Notation "''Mod' ( F ~> F' )" := (@morMod F F') : mole_scope.
    Notation "''CoMod' ( S ~> S' )" := (@morCoMod S S') : mole_scope.
    Notation "ff  o>  ff'" := (@CompositionMod _ _ ff _ ff')
         (at level 40 , ff' at next level , left associativity) : mole_scope.
    Notation "s  o>'  s'" := (@CompositionCoMod _ _ s _ s')
         (at level 40 , s' at next level , left associativity) : mole_scope.
  End Ex_Notations.

End Mole.
(** # #
#+END_SRC

* Grammatical presentation of the objects

#+BEGIN_SRC coq :exports both :results silent # # **)
Import Mole.Ex_Notations.

Inductive obMod : Type :=
  Constant : obCoMod -> obMod
| ObMod_Mole : Mole.obMod -> obMod

with obCoMod : Type :=
  Product : obMod -> obCoMod
| ObCoMod_Mole : Mole.obCoMod -> obCoMod. 
(** # #
#+END_SRC

* Grammatical presentation of the morphisms

#+BEGIN_SRC coq :exports both :results silent # # **)
Reserved Notation "''Mod' (  F  ~>  F'  )" (at level 0).
Reserved Notation "''CoMod' (  S  ~>  S'  )" (at level 0).

Inductive morMod : forall F F' : obMod, Type :=

| CompositionMod : forall F F' : obMod, 'Mod( F ~> F' ) -> forall F'' : obMod, 'Mod( F' ~> F'' ) -> 'Mod( F ~> F'' )

| UnitMod : forall F : obMod, 'Mod( F ~> F )

| Constant_PolyMor : forall S S' : obCoMod, 'CoMod( S ~> S' ) -> 'Mod( Constant S ~> Constant S' )

| Projections_PolyPost : forall F F' : obMod, 'Mod( F ~> F' ) -> 'Mod( Constant (Product F) ~> F' )

| MorMod_Mole : forall F F' : Mole.obMod,
    'Mod( F ~> F' ) %mole -> 'Mod( ObMod_Mole F ~> ObMod_Mole F' )

where "''Mod' ( F ~> F' )" := (@morMod F F') : poly_scope
with morCoMod : forall S S' : obCoMod, Type :=

| CompositionCoMod : forall S S' : obCoMod, 'CoMod( S ~> S' ) -> forall S'' : obCoMod, 'CoMod( S' ~> S'' ) -> 'CoMod( S ~> S'' )

| UnitCoMod : forall S : obCoMod, 'CoMod( S ~> S )

| Pairing_aka_ReverseOfProjections_PolyPre :
    forall S : obCoMod, forall F : obMod, 'Mod( Constant S ~> F ) -> 'CoMod( S ~> Product F )

| MorCoMod_Mole : forall S S' : Mole.obCoMod,
    'CoMod( S ~> S' ) %mole -> 'CoMod( ObCoMod_Mole S ~> ObCoMod_Mole S' )

where "''CoMod' ( S ~> S' )" := (@morCoMod S S') : poly_scope.

Notation "ff  o>  ff'" := (@CompositionMod _ _ ff _ ff')
         (at level 40 , ff' at next level , left associativity) : poly_scope.

Notation "@ ''UnitMod'  F" := (@UnitMod F)
          (at level 10, F at next level, only parsing) : poly_scope.

Notation "''UnitMod'" := (@UnitMod _) (at level 0) : poly_scope.

Notation "(  s  )o>>" :=
  (@Constant_PolyMor _ _ s) (at level 0) : poly_scope.

Notation "''Projections'  o>  ff" :=
  (@Projections_PolyPost _ _ ff) (at level 10, ff at next level) : poly_scope.

Notation "''MorMod_Mole' ff" :=
  (@MorMod_Mole _ _ ff) (at level 10, ff at next level) : poly_scope.

Notation "s  o>'  s'" := (@CompositionCoMod _ _ s _ s')
         (at level 40 , s' at next level , left associativity) : poly_scope.

Notation "@ ''UnitCoMod'  S" := (@UnitCoMod S)
          (at level 10, S at next level, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : poly_scope.

Notation "ff  o>'  'Pairing" :=
  (@Pairing_aka_ReverseOfProjections_PolyPre _ _ ff) (at level 4, right associativity) : poly_scope.

Notation "''MorCoMod_Mole' s" :=
  (@MorCoMod_Mole _ _ s) (at level 10, s at next level) : poly_scope.
(** # #
#+END_SRC

* Grammatical presentation of the conversions

#+BEGIN_SRC coq :exports both :results silent # # **)
Reserved Notation "ff' <~~ ff" (at level 70).
Reserved Notation "s' <~~' s" (at level 70).

Inductive convMod : forall (F F' : obMod), 'Mod( F ~> F' ) -> 'Mod( F ~> F' ) -> Prop :=

(**  ----- the total/(multi-step) conversions -----  **)
| convMod_Refl : forall (F F' : obMod), forall ff : 'Mod( F ~> F' ),
      ff <~~ ff
  
| convMod_Trans : forall (F F' : obMod), forall ff ff0 ff_trans : 'Mod( F ~> F' ),
      ff_trans <~~ ff -> ff0 <~~ ff_trans -> ff0 <~~ ff
  
(**  ----- the congruences (recursive) conversions for morphisms -----  **)

| CompositionMod_cong : forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ), forall F'' : obMod, forall ff' ff'0 : 'Mod( F' ~> F'' ),
          ff0 <~~ ff -> ff'0 <~~ ff' ->
          ( ff0 o> ff'0 ) <~~ ( ff o> ff' )

| Constant_PolyMor_cong : forall S S' : obCoMod, forall s s0 : 'CoMod( S ~> S' ), 
      s0 <~~' s -> ( s0 )o>> <~~ ( s )o>>

| Projections_PolyPost_cong : forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ),
      ( ff0 ) <~~ ( ff ) ->
      ( 'Projections o> ff0 ) <~~ ( 'Projections o> ff )


(** ----- the constant conversions which are used during the polymorphism elimination ----- 
    This polymorphism elimination proceeds by : 
    - firstly destructing the pre/left/input argument of the composition ,
    - lastly destructing the post/right/operator argument of the composition . *)

| UnitMod_comp_morMod : forall F F' : obMod, forall ff : 'Mod( F ~> F' ),
      ( ff ) <~~ ( 'UnitMod o> ff )

| morMod_comp_UnitMod : forall F F' : obMod, forall ff : 'Mod( F ~> F' ),
      ( ff ) <~~ ( ff o> 'UnitMod )

| Constant_PolyMor_comp_Constant_PolyMor : forall S S' : obCoMod, forall s : 'CoMod( S ~> S' ),
      forall S'' : obCoMod, forall s' : 'CoMod( S' ~> S'' ),
          ( ( s o>' s' )o>> )  <~~ ( ( s )o>> o> ( s' )o>> )

| Constant_PolyMor_subst_UnitCoMod_comp_morMod : forall S : obCoMod, forall F : obMod, forall ff : 'Mod( Constant S ~> F ),
        ( ff )  <~~  ( ( @'UnitCoMod S )o>> o> ff )

| Constant_PolyMor_subst_Pairing_aka_ReverseOfProjections_PolyPre_comp_Projections_PolyPost :
    forall S : obCoMod, forall F : obMod, forall ff : 'Mod( Constant S ~> F ), forall F' : obMod, forall ff' : 'Mod( F ~> F' ),
              ( ff o> ff' )
                <~~ ( ( ff o>' 'Pairing )o>> o> ( 'Projections o> ff' ) )

| Projections_PolyPost_comp_morMod : forall F F' : obMod, forall ff : 'Mod( F ~> F' ),
      forall F'' : obMod , forall ff' : 'Mod( F' ~> F'' ),
          ( 'Projections o> ( ff o> ff' ) )
              <~~ ( ( 'Projections o> ff ) o> ff' )

| MorMod_Mole_comp_MorMod_Mole :  forall F F' : Mole.obMod, forall ff : 'Mod( F ~> F' ) %mole, forall F'' : Mole.obMod, forall ff' : 'Mod( F' ~> F'' ) %mole,
          ( MorMod_Mole (ff o> ff')%mole )
            <~~ ( ( MorMod_Mole ff ) o> ( MorMod_Mole ff' ) )

where "ff' <~~ ff" := (@convMod _ _ ff ff')
with convCoMod : forall (S S' : obCoMod), 'CoMod( S ~> S' ) -> 'CoMod( S ~> S' ) -> Prop :=

(**  ----- the total/(multi-step) conversions -----  **)
| convCoMod_Refl : forall (S S' : obCoMod), forall s : 'CoMod( S ~> S' ),
      s <~~' s
  
| convCoMod_Trans : forall (S S' : obCoMod), forall s s0 s_trans : 'CoMod( S ~> S' ),
      s_trans <~~' s -> s0 <~~' s_trans -> s0 <~~' s
  
(**  ----- the congruences (recursive) conversions for morphisms -----  **)

| CompositionCoMod_cong : forall S S' : obCoMod, forall s s0 : 'CoMod( S ~> S' ), forall S'' : obCoMod, forall s' s'0 : 'CoMod( S' ~> S'' ),
          s0 <~~' s -> s'0 <~~' s' ->
          ( s0 o>' s'0 ) <~~' ( s o>' s' )

| Pairing_aka_ReverseOfProjections_PolyPre_cong :
    forall S : obCoMod, forall F : obMod, forall ff ff0 : 'Mod( Constant S ~> F ),
          ( ff0 ) <~~ ( ff ) ->
          ( ff0 o>' 'Pairing ) <~~' ( ff o>' 'Pairing )

(** ----- the constant conversions which are used during the polymorphism elimination ----- 
    This polymorphism elimination proceeds by : 
    - firstly destructing the post/right/operator argument of the composition ,
    - lastly destructing the pre/left/input argument of the composition . *)

| morCoMod_comp_UnitCoMod :
    forall S S' : obCoMod, forall s : 'CoMod( S ~> S' ) ,
        ( s )  <~~' ( ( s ) o>' 'UnitCoMod )

| morCoMod_comp_Pairing_aka_ReverseOfProjections_PolyPre :
    forall S S' : obCoMod, forall s : 'CoMod( S ~> S' ),
    forall F : obMod, forall ff : 'Mod( Constant S' ~> F ),
        ( ( ( s )o>> o> ff ) o>' 'Pairing )
          <~~' ( s o>' ( ff o>' 'Pairing ) )

| UnitCoMod_comp_morCoMod :
    forall S S' : obCoMod, forall s : 'CoMod( S ~> S' ) ,
        ( s )  <~~' ( 'UnitCoMod o>' ( s ) )

| MorCoMod_Mole_comp_MorCoMod_Mole :  forall S S' : Mole.obCoMod, forall s : 'CoMod( S ~> S' ) %mole, forall S'' : Mole.obCoMod, forall s' : 'CoMod( S' ~> S'' ) %mole,
          ( MorCoMod_Mole (s o>' s')%mole )
            <~~' ( ( MorCoMod_Mole s ) o>' ( MorCoMod_Mole s' ) )

(** ----- the constant conversions which are not for polymorphism elimination 
          but are only for the wanted sense of extensionality for adjunction ----- **)

| Pairing_aka_ReverseOfProjections_PolyPre_subst_Projections_PolyPost :
    forall F : obMod, 
      ( @'UnitCoMod ( Product F ) )
        <~~' ( ( 'Projections o> ( @'UnitMod F ) ) o>' 'Pairing )

where "s' <~~' s" := (@convCoMod _ _ s s').

Hint Constructors convMod convCoMod : core.
(** # #
#+END_SRC

* Linear total/asymptotic grade and the degradation lemma

#+BEGIN_SRC coq :exports both :results silent # # **)
Arguments Nat.add : simpl nomatch.

Fixpoint gradeMod (F F' : obMod) (ff : 'Mod( F ~> F' )) {struct ff} : nat
with gradeCoMod (T T' : obCoMod) (t : 'CoMod( T ~> T' )) {struct t} : nat .
Proof.
  { case: F F' / ff.
    - intros F F' ff F'' ff'.
      exact: ( 2 * (S (gradeMod _ _ ff + gradeMod _ _ ff')%nat ) )%nat . 
    - intros F.
      exact: (S O).
    - intros T T' t.
      exact : (S (gradeCoMod _ _ t)).
    - intros F F' ff. 
      exact: (S (S (gradeMod _ _ ff))).
    - intros F F' ff.
      exact: (S O). }
  { case: T T' / t.
    - intros T T' t T'' t'.
      exact: ( 2 * (S (gradeCoMod _ _ t + gradeCoMod _ _ t')%nat ) )%nat . 
    - intros T.
      exact: (S O).
    - intros T F ff.
      exact : (S (S (gradeMod _ _ ff))).
    - intros T T' t.
      exact: (S O). }
Defined.

Arguments gradeMod : simpl nomatch.
Arguments gradeCoMod : simpl nomatch.

Lemma gradeMod_gt0 :
  forall F F' : obMod, forall ff : 'Mod( F ~> F' ), 
      ((S O) <= (gradeMod ff))%nat
with gradeCoMod_gt0 :
  forall T T' : obCoMod, forall t : 'CoMod( T ~> T' ), 
      ((S O) <= (gradeCoMod t))%nat .
Proof.
  { intros F F' ff. case: F F' / ff ;
                      simpl; intros; abstract Lia.lia. }
  { intros T T' s. case: T T' / s ;
                      simpl; intros; abstract Lia.lia. }
Qed.


Ltac tac_gradeMod_gt0 :=
  match goal with
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ ) ,
                  gg3 : 'Mod( _ ~> _ ) ,
                        gg4 : 'Mod( _ ~> _ ) |- _ ] =>
    move : (@gradeMod_gt0 _ _ gg1) (@gradeMod_gt0 _ _ gg2)
                                          (@gradeMod_gt0 _ _ gg3)
                                          (@gradeMod_gt0 _ _ gg4)
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ ) ,
                  gg3 : 'Mod( _ ~> _ ) |- _ ] =>
    move : (@gradeMod_gt0 _ _ gg1) (@gradeMod_gt0 _ _ gg2)
                                          (@gradeMod_gt0 _ _ gg3)
  | [ gg1 : 'Mod( _ ~> _ ) ,
            gg2 : 'Mod( _ ~> _ )  |- _ ] =>
    move : (@gradeMod_gt0 _ _ gg1) (@gradeMod_gt0 _ _ gg2)
  | [ gg1 : 'Mod( _ ~> _ )  |- _ ] =>
    move : (@gradeMod_gt0 _ _ gg1) 
  end.

Ltac tac_gradeCoMod_gt0 :=
  match goal with
  | [ gg1 : 'CoMod( _ ~> _ ) ,
            gg2 : 'CoMod( _ ~> _ ) ,
                  gg3 : 'CoMod( _ ~> _ ) ,
                        gg4 : 'CoMod( _ ~> _ ) |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ gg1) (@gradeCoMod_gt0 _ _ gg2)
                                          (@gradeCoMod_gt0 _ _ gg3)
                                          (@gradeCoMod_gt0 _ _ gg4)
  | [ gg1 : 'CoMod( _ ~> _ ) ,
            gg2 : 'CoMod( _ ~> _ ) ,
                  gg3 : 'CoMod( _ ~> _ ) |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ gg1) (@gradeCoMod_gt0 _ _ gg2)
                                          (@gradeCoMod_gt0 _ _ gg3)
  | [ gg1 : 'CoMod( _ ~> _ ) ,
            gg2 : 'CoMod( _ ~> _ )  |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ gg1) (@gradeCoMod_gt0 _ _ gg2)
  | [ gg1 : 'CoMod( _ ~> _ )  |- _ ] =>
    move : (@gradeCoMod_gt0 _ _ gg1) 
  end.

Lemma degradeMod :
  forall F F' : obMod, forall ff ff0 : 'Mod( F ~> F' ),
      ff0 <~~ ff  -> ( gradeMod ff0 <= gradeMod ff )%nat
with degradeCoMod :
  forall S S' : obCoMod, forall s s0 : 'CoMod( S ~> S' ),
      s0 <~~' s  -> ( gradeCoMod s0 <= gradeCoMod s )%nat .
Proof.
  Time all : [> intros F F' ff ff0 convMod_ff0_ff;
         case: F F' ff ff0 / convMod_ff0_ff
        | intros S S' s s0 convCoMod_s0_s;
          case: S S' s s0 / convCoMod_s0_s ];
    try solve [simpl; intuition idtac;
      repeat match goal with
             | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
               move : (degradeMod _ _ _ _ Hred) ; clear Hred
             | [ Hred : ( _ <~~' _ )%poly |- _ ] =>
               move : (degradeCoMod _ _ _ _ Hred) ; clear Hred
             end;
      clear; intros; try tac_gradeMod_gt0;  try tac_gradeCoMod_gt0;
        simpl; intros; abstract Lia.lia] .
  (* Time: "Finished transaction in 0.938 secs (0.938u,0.s) (successful)" *)
Qed.
(** # #
#+END_SRC

* Solution morphisms

** Solution morphisms without composition

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Sol.
Section Section1.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Inductive morMod : forall F F' : obMod, Type :=

| UnitMod : forall F : obMod, 'Mod( F ~> F )

| Constant_PolyMor : forall S S' : obCoMod, 'CoMod( S ~> S' ) -> 'Mod( Constant S ~> Constant S' )

| Projections_PolyPost : forall F F' : obMod, 'Mod( F ~> F' ) -> 'Mod( Constant (Product F) ~> F' )

| MorMod_Mole : forall F F' : Mole.obMod,
    'Mod( F ~> F' ) %mole -> 'Mod( ObMod_Mole F ~> ObMod_Mole F' )

where "''Mod' ( F ~> F' )" := (@morMod F F') : sol_scope
with morCoMod : forall S S' : obCoMod, Type :=

| UnitCoMod : forall S : obCoMod, 'CoMod( S ~> S )

| Pairing_aka_ReverseOfProjections_PolyPre :
    forall S : obCoMod, forall F : obMod, 'Mod( Constant S ~> F ) -> 'CoMod( S ~> Product F )

| MorCoMod_Mole : forall S S' : Mole.obCoMod,
    'CoMod( S ~> S' ) %mole -> 'CoMod( ObCoMod_Mole S ~> ObCoMod_Mole S' )

where "''CoMod' ( S ~> S' )" := (@morCoMod S S') : sol_scope.
End Section1.

Module Export Ex_Notations.
Declare Scope sol_scope. Delimit Scope sol_scope with sol.

Notation "''Mod' ( F ~> F' )" := (@morMod F F') : sol_scope.

Notation "@ ''UnitMod'  F" := (@UnitMod F)
          (at level 10, F at next level, only parsing) : sol_scope.

Notation "''UnitMod'" := (@UnitMod _) (at level 0) : sol_scope.

Notation "(  s  )o>>" :=
  (@Constant_PolyMor _ _ s) (at level 0) : sol_scope.

Notation "''Projections'  o>  ff" :=
  (@Projections_PolyPost _ _ ff) (at level 10, ff at next level) : sol_scope.

Notation "''MorMod_Mole' ff" :=
  (@MorMod_Mole _ _ ff) (at level 10, ff at next level) : sol_scope.

Notation "''CoMod' ( S ~> S' )" := (@morCoMod S S') : sol_scope.

Notation "@ ''UnitCoMod'  S" := (@UnitCoMod S)
          (at level 10, S at next level, only parsing) : sol_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : sol_scope.

Notation "ff  o>'  'Pairing" :=
  (@Pairing_aka_ReverseOfProjections_PolyPre _ _ ff) (at level 4, right associativity) : sol_scope.

Notation "''MorCoMod_Mole' s" :=
  (@MorCoMod_Mole _ _ s) (at level 10, s at next level) : sol_scope.
End Ex_Notations.

Fixpoint toPolyMorMod (F F' : obMod) (ff : 'Mod( F ~> F' )%sol) : 'Mod( F ~> F' )%poly
with toPolyMorCoMod (S S' : obCoMod) (s : 'CoMod( S ~> S' )%sol) : 'CoMod( S ~> S' )%poly .
Proof.
  { case: F F' / ff.
    - intros F .
      exact: ( @'UnitMod F ) %poly.
    - intros S S' s. 
      exact: ( ( toPolyMorCoMod _ _ s )o>> ) %poly.
    - intros F F' ff . 
      exact: ( 'Projections o> (toPolyMorMod _ _ ff) ) %poly.
    - intros F F' ff.
      exact: ( 'MorMod_Mole ff )%poly. }
  { case: S S' / s.
    - intros S .
      exact: ( @'UnitCoMod S ) %poly.
    - intros S F ff. 
      exact: ( (toPolyMorMod _ _ ff) o>' 'Pairing ) %poly.
    - intros S S' s.
      exact: ( 'MorCoMod_Mole s )%poly. }
Defined.

Arguments toPolyMorMod : simpl nomatch.
Arguments toPolyMorCoMod : simpl nomatch. 
(** # #
#+END_SRC

** Cases-refinement of morphisms with inner-instantiation of the domain object-index

#+BEGIN_SRC coq :exports both :results silent # # **)
Module MorMod_domConstant.
Inductive morMod
: forall S : obCoMod , forall F : obMod, 'Mod( Constant S ~> F )%sol -> Type :=
| UnitMod :  forall S : obCoMod, 
    morMod ( @'UnitMod (Constant S) )%sol

| Constant_PolyMor : forall S S' : obCoMod, forall s : 'CoMod( S ~> S' )%sol,
        morMod ( ( s )o>> )%sol

| Projections_PolyPost : forall F F' : obMod, forall ff : 'Mod( F ~> F' )%sol,
      morMod ( 'Projections o> ff )%sol .
End MorMod_domConstant.

Module MorMod_domObMod_Mole.
Inductive morMod
: forall (F : Mole.obMod) (F' : obMod), 'Mod( ObMod_Mole F ~> F' )%sol -> Type :=
| UnitMod :  forall F : Mole.obMod, 
    morMod ( @'UnitMod (ObMod_Mole F) )%sol

| MorMod_Mole : forall F F' : Mole.obMod,
    forall ff : 'Mod( F ~> F' ) %mole,
      morMod ( 'MorMod_Mole ff )%sol.
End MorMod_domObMod_Mole.

Lemma morMod_domP
  : forall F F' : obMod, forall ff : 'Mod( F ~> F' )%sol,
      ltac:( destruct F; [ refine (MorMod_domConstant.morMod ff)
                         | refine (MorMod_domObMod_Mole.morMod ff) ] ).
Proof. 
  intros. destruct ff.
  - destruct F; [ constructor 1 | constructor 1 ].
  - constructor 2.
  - constructor 3.
  - constructor 2.
Defined.

Module MorCoMod_codomProduct.
Inductive morCoMod
: forall S : obCoMod , forall  F : obMod, 'CoMod( S ~> Product F )%sol -> Type :=

| UnitCoMod : forall F : obMod, 
    morCoMod ( @'UnitCoMod (Product F) )%sol

| Pairing_aka_ReverseOfProjections_PolyPre :
    forall S : obCoMod, forall F : obMod, forall ff : 'Mod( Constant S ~> F )%sol,
      morCoMod ( ff o>' 'Pairing )%sol .
End MorCoMod_codomProduct.

Module MorCoMod_codomObCoMod_Mole.
Inductive morCoMod
: forall (S : obCoMod) (S' : Mole.obCoMod), 'CoMod( S ~> ObCoMod_Mole S' )%sol -> Type :=
| UnitCoMod :  forall S : Mole.obCoMod, 
    morCoMod ( @'UnitCoMod (ObCoMod_Mole S) )%sol

| MorCoMod_Mole : forall S S' : Mole.obCoMod,
    forall s : 'CoMod( S ~> S' ) %mole,
      morCoMod ( 'MorCoMod_Mole s )%sol.
End MorCoMod_codomObCoMod_Mole.

Lemma morCoMod_codomP
  : forall S S' : obCoMod, forall s : 'CoMod( S ~> S' )%sol,
      ltac:( destruct S'; [ refine (MorCoMod_codomProduct.morCoMod s)
                          | refine (MorCoMod_codomObCoMod_Mole.morCoMod s) ] ).
Proof. 
  intros. destruct s.
  - destruct S; [ constructor 1 | constructor 1 ].
  - constructor 2.
  - constructor 2.
Defined.
End Sol.
(** # #
#+END_SRC

* Composition/cut-elimination into polymorphic soiution by computational/total/asymptotic/reduction/(multi-step) resolution using conversions

#+BEGIN_SRC coq :exports both :results silent # # **)
Module Resolve.
Export Sol.Ex_Notations.

Ltac tac_degrade H_grade :=
  intuition idtac;
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%poly |- _ ] =>
           move : (degradeMod Hred) ; clear Hred
         | [ Hred : ( _ <~~' _ )%poly |- _ ] =>
           move : (degradeCoMod Hred) ; clear Hred
         end;
  move: H_grade; clear; simpl; intros;
  try tac_gradeMod_gt0; try tac_gradeCoMod_gt0;
  simpl; intros; (*abstract*) Lia.lia.

Ltac tac_simpl := simpl.
Ltac tac_reduce := tac_simpl; repeat (intro; tac_simpl); intuition eauto 9.

Fixpoint solveMod len {struct len} :
 forall F F' : obMod, forall ff : 'Mod( F ~> F' ), forall grade_ff : (gradeMod ff <= len)%nat,
       { ffSol : 'Mod( F ~> F' )%sol | (Sol.toPolyMorMod ffSol) <~~ ff }
with solveCoMod len {struct len} :
 forall S S' : obCoMod, forall s : 'CoMod( S ~> S' ), forall grade_s : (gradeCoMod s <= len)%nat,
   { sSol : 'CoMod( S ~> S' )%sol | (Sol.toPolyMorCoMod sSol) <~~' s } .         
Proof.
{ (** solveMod *) case : len => [ | len ].

(** len is O **)
- intros F F' ff grade_ff; exfalso;
    clear - grade_ff; abstract tac_degrade grade_ff.

(** len is (S len) **)
-  intros F F' ff.  case : F F' / ff;
   [ intros F F' ff F'' ff' grade_ff
   | intros F grade_ff
   | intros S S' s grade_ff
   | intros F F' ff  grade_ff
   | intros F F' ff grade_ff ]. 

(** ff is  (ff o> ff') *) all: cycle 1.
   
(** ff is  (@'UnitMod F) **)
+ unshelve eexists. refine ( @'UnitMod F )%sol.
  clear; abstract exact: convMod_Refl.

(** ff is  ( s )o>> **)
+ have [:blurb] sSol_transp :=
    (proj2_sig (solveCoMod len _ _ s blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveCoMod len _ _ s blurb)) sSol_transp => sSol sSol_transp .
  clear solveMod solveCoMod.

  unshelve eexists. refine ( ( sSol )o>> )%sol.
  move: sSol_transp; clear; abstract tac_reduce.

(** ff is  ( 'Projections o> ff ) **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff blurb)) ffSol_transp => ffSol ffSol_transp .
  clear solveMod solveCoMod.

  unshelve eexists. refine ( 'Projections o> ffSol )%sol.
  move: ffSol_transp; clear; abstract tac_reduce.

(** ff is  ('MorMod_Mole ff) **)
+ unshelve eexists. refine ( 'MorMod_Mole ff )%sol.
  clear; abstract tac_reduce.

(** ff is  (ff o> ff') **)
+ have [:blurb] ffSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff blurb)) ffSol_transp => ffSol ffSol_transp .
  have [:blurb] ff'Sol_transp :=
    (proj2_sig (solveMod len _ _ ff' blurb));
      first by clear -grade_ff; abstract tac_degrade grade_ff.
  move: (sval (solveMod len _ _ ff' blurb)) ff'Sol_transp => ff'Sol ff'Sol_transp .

  (** ff is  (ff o> ff') , to (ffSol o> ff'Sol)  **)
  destruct ffSol as
   [ F 
   | F F' ffSol  
   | F F' ffSol
   | F F' ffSol ]. 

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
         is (('UnitMod) o> ff'Sol) **)
  * unshelve eexists. refine (ff'Sol)%sol.
    move:ffSol_transp ff'Sol_transp; clear;
      abstract (tac_simpl; intros; eapply convMod_Trans with
                                   (ff_trans := ('UnitMod) o> (Sol.toPolyMorMod ff'Sol)); tac_reduce).

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( ( ffSol )o>> o> ff'Sol ) **)
  * move: (Sol.morMod_domP ff'Sol) => ff'Sol_morMod_domP.
    { destruct ff'Sol_morMod_domP as
          [ _F
          | S S' ff'Sol
          | _F F' ff'Sol ].

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ( ffSol )o>> o> ('UnitMod) ) **)
      - unshelve eexists. refine ( ( ffSol )o>> )%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := (Sol.toPolyMorCoMod ffSol)o>> o> ('UnitMod)); tac_reduce).

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ( ffSol )o>> o> ( ff'Sol )o>> ) **)
      -  have [:blurb] ffSol_o_ff'Sol_transp :=
           (proj2_sig (solveCoMod len _ _ (Sol.toPolyMorCoMod ffSol o>' Sol.toPolyMorCoMod ff'Sol) blurb));
             first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
         move: (sval (solveCoMod len _ _ (Sol.toPolyMorCoMod ffSol o>' Sol.toPolyMorCoMod ff'Sol) blurb)) ffSol_o_ff'Sol_transp 
         => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
         clear solveMod solveCoMod.

        unshelve eexists.
        refine ( ( ffSol_o_ff'Sol )o>> )%sol.
        move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                 (ff_trans := ( (Sol.toPolyMorCoMod ffSol)o>> ) o> ( (Sol.toPolyMorCoMod ff'Sol)o>> )); tac_reduce). 

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ( ffSol )o>> o> ('Projections o> ff'Sol) ) **)
      - move: (Sol.morCoMod_codomP ffSol) => ffSol_morCoMod_codomP.
        { destruct ffSol_morCoMod_codomP as
              [ S
              | S F ffSol ].

          (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
              is ( ( 'UnitCoMod )o>> o> ('Projections o> ff'Sol) ) **)
          - unshelve eexists. refine ( 'Projections o> ff'Sol )%sol.
            move: ffSol_transp ff'Sol_transp; clear;
              abstract (tac_simpl; intros; eapply convMod_Trans with
                          (ff_trans := ('UnitCoMod)o>> o> ('Projections o> (Sol.toPolyMorMod ff'Sol))); tac_reduce).

          (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
              is ( ( ffSol o>' 'Pairing )o>> o> ('Projections o> ff'Sol) ) **)
          - have [:blurb] ffSol_o_ff'Sol_transp :=
              (proj2_sig (solveMod len _ _ (Sol.toPolyMorMod ffSol o> Sol.toPolyMorMod ff'Sol) blurb));
                first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
            move: (sval (solveMod len _ _ (Sol.toPolyMorMod ffSol o> Sol.toPolyMorMod ff'Sol) blurb)) ffSol_o_ff'Sol_transp 
            => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
            clear solveMod solveCoMod.

            unshelve eexists.
            refine ( ffSol_o_ff'Sol)%sol.
            move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
              abstract (tac_simpl; intros; eapply convMod_Trans with
                         (ff_trans := ( (Sol.toPolyMorMod ffSol) o>' 'Pairing )o>>
                            o> ('Projections o> (Sol.toPolyMorMod ff'Sol) )); tac_reduce).
        }
    }

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( ('Projections o> ffSol) o> ff'Sol **)
  * have [:blurb] ffSol_o_ff'Sol_transp :=
      (proj2_sig (solveMod len _ _ (Sol.toPolyMorMod ffSol o> Sol.toPolyMorMod ff'Sol) blurb));
        first by clear -grade_ff ffSol_transp ff'Sol_transp; abstract tac_degrade grade_ff.
    move: (sval (solveMod len _ _ (Sol.toPolyMorMod ffSol o> Sol.toPolyMorMod ff'Sol) blurb)) ffSol_o_ff'Sol_transp 
        => ffSol_o_ff'Sol ffSol_o_ff'Sol_transp .
    clear solveMod .
    
    unshelve eexists.
    refine ( 'Projections o> ffSol_o_ff'Sol )%sol.
    move: ffSol_transp ff'Sol_transp ffSol_o_ff'Sol_transp; clear;
    abstract (tac_simpl; intros; eapply convMod_Trans with
        (ff_trans := ( 'Projections o> (Sol.toPolyMorMod ffSol) ) o> ( Sol.toPolyMorMod ff'Sol )); tac_reduce).

  (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
      is ( ('MorMod_Mole ffSol) o> ff'Sol ) **)
  * move: (Sol.morMod_domP ff'Sol) => ff'Sol_morMod_domP.
    { destruct ff'Sol_morMod_domP as
          [ _F
          | _F F' ff'Sol ].

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ('MorMod_Mole ffSol) o> ('UnitMod) ) **)
      - unshelve eexists. refine ( 'MorMod_Mole ffSol )%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := ( 'MorMod_Mole ffSol ) o> ('UnitMod)); tac_reduce).

      (** ff is (ff o> ff') , to (ffSol o> ff'Sol)  , 
          is ( ('MorMod_Mole ffSol) o> ('MorMod_Mole ff'Sol) ) **)
      - unshelve eexists. refine ( 'MorMod_Mole (ffSol o> ff'Sol)%mole )%sol.
        move: ffSol_transp ff'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convMod_Trans with
                     (ff_trans := ( 'MorMod_Mole ffSol ) o> ( 'MorMod_Mole ff'Sol )); tac_reduce).
    }
}
{ (** solveCoMod *) case : len => [ | len ].

(** len is O **)
- intros F F' ff grade_s; exfalso;
    clear - grade_s; abstract tac_degrade grade_s.

(** len is (S len) **)
-  intros S S' s.  case : S S' / s;
   [ intros S S' s S'' s' grade_s
   | intros S grade_s
   | intros S F ff grade_s
   | intros S S' s grade_s ]. 

(** s is  (s o>' s') *) all: cycle 1.
   
(** s is  (@'UnitCoMod S) **)
+ unshelve eexists. refine ( @'UnitCoMod S )%sol.
  clear; abstract exact: convCoMod_Refl.

(** s is  ( ff o>' 'Pairing ) **)
+ have [:blurb] sSol_transp :=
    (proj2_sig (solveMod len _ _ ff blurb));
      first by clear -grade_s; abstract tac_degrade grade_s.
  move: (sval (solveMod len _ _ ff blurb)) sSol_transp => sSol sSol_transp .
  clear solveMod solveCoMod.

  unshelve eexists. refine ( ( sSol o>' 'Pairing ) )%sol.
  move: sSol_transp; clear; abstract tac_reduce.

(** s is  ('MorCoMod_Mole s) **)
+ unshelve eexists. refine ( 'MorCoMod_Mole s )%sol.
  clear; abstract tac_reduce.

(** s is  (s o>' s') **)
+ have [:blurb] sSol_transp :=
    (proj2_sig (solveCoMod len _ _ s blurb));
      first by clear -grade_s; abstract tac_degrade grade_s.
  move: (sval (solveCoMod len _ _ s blurb)) sSol_transp => sSol sSol_transp .
  have [:blurb] s'Sol_transp :=
    (proj2_sig (solveCoMod len _ _ s' blurb));
      first by clear -grade_s; abstract tac_degrade grade_s.
  move: (sval (solveCoMod len _ _ s' blurb)) s'Sol_transp => s'Sol s'Sol_transp .

  (** s is  (s o>' s') , to (sSol o>' s'Sol)  **)
  destruct s'Sol as
   [ _S 
   | _S F s'Sol
   | _S S' s'Sol ]. 

  (** s is (s o>' s') , to (sSol o>' s'Sol)  , 
         is (sSol o>' ('UnitCoMod)) **)
  * unshelve eexists. refine (sSol)%sol.
    move:sSol_transp s'Sol_transp; clear;
      abstract (tac_simpl; intros; eapply convCoMod_Trans with
                                   (s_trans := (Sol.toPolyMorCoMod sSol) o>' ('UnitCoMod)); tac_reduce).

  (** s is (s o>' s') , to (sSol o>' s'Sol)  , 
      is ( sSol o>' ( s'Sol o>' 'Pairing ) ) **)
  * have [:blurb] sSol_o_s'Sol_transp :=
      (proj2_sig (solveMod len _ _ ( (Sol.toPolyMorCoMod sSol)o>> o> Sol.toPolyMorMod s'Sol) blurb));
        first by clear -grade_s sSol_transp s'Sol_transp; abstract tac_degrade grade_s.
    move: (sval (solveMod len _ _ ( (Sol.toPolyMorCoMod sSol)o>> o> Sol.toPolyMorMod s'Sol) blurb)) sSol_o_s'Sol_transp 
    => sSol_o_s'Sol sSol_o_s'Sol_transp .
    clear solveMod solveCoMod.

    unshelve eexists.
    refine ( sSol_o_s'Sol o>' 'Pairing )%sol.
    move: sSol_transp s'Sol_transp sSol_o_s'Sol_transp; clear;
      abstract (tac_simpl; intros; eapply convCoMod_Trans with
               (s_trans := (Sol.toPolyMorCoMod sSol) o>' ((Sol.toPolyMorMod s'Sol) o>' 'Pairing)); tac_reduce). 

  (** s is (s o>' s') , to (sSol o>' s'Sol)  , 
      is ( sSol o>' ('MorCoMod_Mole s'Sol) ) **)
  * move: (Sol.morCoMod_codomP sSol) => sSol_morCoMod_codomP.
    { destruct sSol_morCoMod_codomP as
          [ S
          | S _S' sSol ].

      (** s is (s o>' s') , to (sSol o>' s'Sol)  , 
          is ( ('UnitCoMod) o>' ('MorCoMod_Mole s'Sol) ) **)
      - unshelve eexists. refine ( 'MorCoMod_Mole s'Sol )%sol.
        move: sSol_transp s'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convCoMod_Trans with
                     (s_trans := ('UnitCoMod) o>' ( 'MorCoMod_Mole s'Sol )); tac_reduce).

      (** s is (s o> s') , to (sSol o> s'Sol)  , 
          is ( ('MorCoMod_Mole sSol) o> ('MorCoMod_Mole s'Sol) ) **)
      - unshelve eexists. refine ( 'MorCoMod_Mole (sSol o>' s'Sol)%mole )%sol.
        move: sSol_transp s'Sol_transp; clear;
          abstract (tac_simpl; intros; eapply convCoMod_Trans with
                     (s_trans := ( 'MorCoMod_Mole sSol ) o>' ( 'MorCoMod_Mole s'Sol )); tac_reduce).
    }
}
Defined.
End Resolve.
End ADJUNCTION.
(** # #
#+END_SRC

Voila.
# # **)
