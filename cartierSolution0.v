(** # #
#+TITLE: cartierSolution0.v

Proph

https://github.com/1337777/cartier/blob/master/cartierSolution0.v

Grammatical sheaf cohomology, its MODOS proof-assistant and WorkSchool 365 market for learning reviewers

Its significance would be similar as the significance of the development of hott types
 from the idea of "equality of equalities". Indeed, the idea of "family of families" leads,
 via Kosta Dosen techniques, to grammatical sheaf cohomology: 
 that the grammatical sieves (nerve) could be programmed such to inductively store both
 the (possibly incompatible) glued-data along with 
 its differentials (incompatibilities) of the gluing.

The computing example prototype is to quickly convey the idea, but far from the generality 
 (where pullback-sieves are blended within the sum-sieve constructor).

OUTLINE ::

* Module EXAMPLE. Computing example prototype (newest version 4.0)

* Module NERVE. Grammatical nerve-sieves (version 3.0)

* Module SHEAF. General sieves (version 2.0)

* Module EARLIER_PRELIM_SHEAF. Singleton sieves (version 1.0)


-----

#+BEGIN_SRC coq :exports both :results silent # # **)

Module EXAMPLE.

From Coq Require Lia Vectors.Vector.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype tuple finfun. 
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.

Section tools.
Definition to_nat := fun m => fun i : Fin.t (S m) => (proj1_sig  (Fin.to_nat i)).

Definition one_cases : forall (P : Fin.t (S 0) -> Type)
 (P1 : P Fin.F1)  (p : Fin.t (S 0)), P p.
Proof. intros. apply: Fin.caseS'. apply P1.
clear p; intros p. pattern p. apply: Fin.case0.
Defined.

Definition two_cases : forall (P : Fin.t (S 1) -> Type)
 (P1 : P Fin.F1) (P2 : P (Fin.FS Fin.F1)) (p : Fin.t (S 1)), P p.
Proof. intros. apply: Fin.caseS'. apply P1.
apply: one_cases. apply P2.
Defined.

Variable dimCell : nat.
Variable typeAt_ : Fin.t (S dimCell) -> Type.

Inductive ilist : nat -> Type :=
  | Nil_ilist : ilist O
  | Cons_ilist : forall n (H : (n < (S dimCell))%coq_nat),
       typeAt_ ( Fin.of_nat_lt H) -> ilist n -> ilist (S n).

Definition to_ilist (t: forall i : Fin.t (S dimCell), typeAt_ i) n (H : (n <= S dimCell)%coq_nat) : ilist n.
Proof. induction n.
- apply: Nil_ilist.
- apply: Cons_ilist.
  + exact: (t (Fin.of_nat_lt H)).
  + apply IHn. abstract(Lia.lia).
Defined. 
End tools.

Section nerveSieve.
Variable nerveStruct : seq nat -> bool.
Variable topSieve : nat.

Inductive nerveSieve: forall (dimCoef: nat) (dimCell: nat) (cell: seq nat), Type :=

| Diff_nerveSieve: forall (dimCoef: nat) (dimCell: nat) (cell: seq nat) 
 (outer_: Fin.t (S dimCell) -> Fin.t (S topSieve))
 (innerCell_: forall (outerIndex: Fin.t (S dimCell)), seq nat)
 (cell_eq: forall (outerIndex: Fin.t (S dimCell)),
   seq.perm_eq cell ((to_nat (outer_ outerIndex): nat) :: (innerCell_ outerIndex)))
 (cell_nerveStruct: nerveStruct cell),
 forall (inner_nerveSieve: forall (outerIndex: Fin.t (S dimCell)),
   nerveSieve dimCoef dimCell (innerCell_ outerIndex)),
 nerveSieve (S dimCoef) (S dimCell) cell

| Glue_nerveSieve: forall (dimCoef: nat) (dimCell: nat) (cell: seq nat),
  forall (inner_nerveSieve: forall (outerIndex: Fin.t (S topSieve)),
    nerveSieve dimCoef dimCell cell),
  nerveSieve (S dimCoef) dimCell cell

| Unit_nerveSieve: 
  nerveSieve 0 0 [:: ].

Parameter shfyCoef : forall (cell: seq nat), Type.
Parameter restrict_shfyCoef : forall (cell0: seq nat), forall (cell: seq nat) (i : nat), 
 perm_eq cell (i :: cell0) -> shfyCoef cell0 -> shfyCoef cell.
Parameter diff_shfyCoef : forall (dimCell: nat) (cell: seq nat),
  ilist (fun (outerIndex: Fin.t (S dimCell)) => shfyCoef cell) (S dimCell) -> shfyCoef cell.
Parameter glue_shfyCoef : forall (cell: seq nat),
 ilist (fun (outerIndex: Fin.t (S topSieve)) => shfyCoef ((to_nat outerIndex) :: cell)) (S topSieve)  -> shfyCoef cell.
Parameter congr_shfyCoef : forall (cell0: seq nat), forall (cell: seq nat),
 perm_eq cell cell0 -> shfyCoef cell0 -> shfyCoef cell.

Definition diffGluing: forall (dimCoef: nat),
forall (inner_coef: forall (outerIndex: Fin.t (S topSieve)), forall (dimCell: nat) (cell: seq nat),
  nerveSieve dimCoef dimCell cell  -> shfyCoef cell),
forall (dimCell: nat) (cell: seq nat),
nerveSieve (S dimCoef) dimCell cell -> shfyCoef cell.
Proof. intros ? ?  ? ? ns. inversion ns; subst.
{ (* Diff_nerveSieve *) 
  (* apply: (diff_shfyCoef (fun i : 'I_(_.+1) => 
                restrict_shfyCoef (cell_eq i)
                  (inner_coef (outer_ i) _  (innerCell_ i) (inner_nerveSieve i)))). *)
  eapply diff_shfyCoef. refine (to_ilist _ (le_n _) ). intros i. apply: restrict_shfyCoef.
  + apply: (cell_eq i).
  + eapply (inner_coef (outer_ i)). apply: inner_nerveSieve. } 
{ (* Glue_nerveSieve *) 
  (* apply: glue_shfyCoef (fun i : 'I_topSieve => 
                inner_coef i dimCell cell (inner_nerveSieve i)). *)
  apply glue_shfyCoef. refine (to_ilist _ (le_n _) ). intros i. eapply restrict_shfyCoef.
  + exact: perm_refl.
  + eapply (inner_coef i). apply: (inner_nerveSieve i). }
Defined.

Definition diffGluing_unit: 
forall (unit_coef: shfyCoef [:: ]),
forall (dimCell: nat) (cell: seq nat),
nerveSieve 0 dimCell cell -> shfyCoef cell.
Proof. intros ? ? ? ns. inversion ns; subst.
{ (* Unit_nerveSieve *) exact: unit_coef. }
Defined.
End nerveSieve.

Section example1_shfyCoef.

Definition example1_nerveSieve: nerveSieve (fun _ => true) 1  2 1 [:: 0].
Proof. apply: Glue_nerveSieve. apply: two_cases.
{ unshelve eapply Diff_nerveSieve. 
  apply: one_cases. exact: (@Fin.F1 1). 
  apply: one_cases. exact: [:: ].
  apply: one_cases. reflexivity. 
  reflexivity.
  apply: one_cases. apply Unit_nerveSieve.  }
{ unshelve eapply Diff_nerveSieve. 
  apply: one_cases. exact: (@Fin.F1 1). 
  apply: one_cases. exact: [:: ].
  apply: one_cases. reflexivity. 
  reflexivity.
  apply: one_cases. apply Unit_nerveSieve.  }
Defined.

Notation Diff y x := (@Diff_nerveSieve _ _ _ _ _ y _ _ _ x). 
Print example1_nerveSieve.
(* Glue_nerveSieve (two_cases 
   (Diff (one_cases Fin.F1) (one_cases (Unit_nerveSieve xpredT 1)))
	 (Diff (one_cases Fin.F1) (one_cases (Unit_nerveSieve xpredT 1))))
     : nerveSieve xpredT 1 2 1 [:: 0] *)

Variable aa bb cc dd : shfyCoef [:: ].

Definition example1_shfyCoef:  shfyCoef [:: 0].
Proof. apply: (diffGluing _ example1_nerveSieve). apply: two_cases.
{  apply: diffGluing.
  { apply: two_cases.
    exact: (diffGluing_unit aa). exact: (diffGluing_unit bb). } }
{ apply: diffGluing.
  { apply: two_cases.
    exact: (diffGluing_unit cc). exact: (diffGluing_unit dd). } }
Defined. 

Notation "[< x2 ;; .. ;; xn >]" := (Cons_ilist x2 .. (Cons_ilist xn (@Nil_ilist _ _)) ..)
  (at level 0, format "[< '['  x2  ;;  '/'  ..  ;;  '/'  xn  ']' >]" ) .
Arguments Nil_ilist {_ _}.
Arguments restrict_shfyCoef [_] cell [_ _] _.
Arguments congr_shfyCoef {_ _ _} _.

Eval compute in example1_shfyCoef.
(* = glue_shfyCoef
[< restrict_shfyCoef [:: 1; 0]
     (diff_shfyCoef [< restrict_shfyCoef [:: 0] cc >]) ;;
   restrict_shfyCoef [:: 0; 0]
     (diff_shfyCoef [< restrict_shfyCoef [:: 0] aa >]) >]
: shfyCoef [:: 0] *)
End example1_shfyCoef.

Section example2_shfyCoef.

Example example2_nerveSieve: nerveSieve (fun _ => true) 1  3 2 [:: 0; 1].
Proof. apply: Glue_nerveSieve. apply: two_cases.
{ unshelve eapply Diff_nerveSieve.
  exact: id.
  { apply: two_cases. exact: [:: 1]. exact: [:: 0]. }
  { apply: two_cases. reflexivity. reflexivity. }
  reflexivity.
  { apply: two_cases.
    { unshelve eapply Diff_nerveSieve.
      apply: one_cases. exact: (Fin.FS (@Fin.F1 0)).
      apply: one_cases. exact: [::].
      apply: one_cases. reflexivity.
      reflexivity.
      apply: one_cases. apply: Unit_nerveSieve. }
    { unshelve eapply Diff_nerveSieve.
      apply: one_cases.  exact: (@Fin.F1 1).
      apply: one_cases.  exact: [::].
      apply: one_cases. reflexivity.
      reflexivity.
      apply: one_cases. apply: Unit_nerveSieve. } } }
{ unshelve eapply Diff_nerveSieve.
  { (* permute, not id inclusion *) 
    apply: two_cases. exact: (Fin.FS (@Fin.F1 0)). exact: (@Fin.F1 1). }
  { apply: two_cases. exact: [:: 0]. exact: [:: 1]. }
  { apply: two_cases. reflexivity. reflexivity. }
  reflexivity.
  { apply: two_cases.
    { unshelve eapply Diff_nerveSieve.
      apply: one_cases. exact: (@Fin.F1 1).
      apply: one_cases. exact: [::].
      apply: one_cases. reflexivity.
      reflexivity.
      apply: one_cases. apply: Unit_nerveSieve. }
    { unshelve eapply Diff_nerveSieve.
      apply: one_cases. exact: (Fin.FS (@Fin.F1 0)).
      apply: one_cases. exact: [::].
      apply: one_cases. reflexivity.
      reflexivity.
      apply: one_cases. apply: Unit_nerveSieve. } } }
Defined.

Notation Diff y x := (@Diff_nerveSieve _ _ _ _ _ y _ _ _ x). 
Print example2_nerveSieve.
(*Glue_nerveSieve (two_cases
(Diff id (two_cases
      (Diff (one_cases (Fin.FS Fin.F1))
          (one_cases (Unit_nerveSieve xpredT 1)))
      (Diff (one_cases Fin.F1) (one_cases (Unit_nerveSieve xpredT 1)))))
(Diff (two_cases (Fin.FS Fin.F1) Fin.F1) (two_cases
      (Diff (one_cases Fin.F1) (one_cases (Unit_nerveSieve xpredT 1)))
      (Diff (one_cases (Fin.FS Fin.F1))
          (one_cases (Unit_nerveSieve xpredT 1))))))
  : nerveSieve xpredT 1 3 2 [:: 0; 1] *)

Variable aa bb  : shfyCoef [:: 0].
Variable  cc dd : shfyCoef [:: 1].

Definition example2_shfyCoef: shfyCoef [:: 0; 1].
Proof. apply: (diffGluing _ example2_nerveSieve). apply: two_cases.
{ apply: diffGluing. intros _.
  { intros ? ? ns. inversion ns; subst. (* TODO: for case-analysis, everywhere should use destructible ilist instead of function,
      together with conversion operation ilist -> function, similar as ssreflect finfun *)
    { move:   (outer_ (@Fin.F1 dimCell0)) (innerCell_ (@Fin.F1 dimCell0))(cell_eq (@Fin.F1 dimCell0)) (inner_nerveSieve (@Fin.F1 dimCell0)).
      apply: two_cases.
      { move => innerCell_0 cell_eq0 inner_nerveSieve0. inversion inner_nerveSieve0; subst. apply: (congr_shfyCoef cell_eq0).
        exact: aa. }
      { move => innerCell_0 cell_eq0 inner_nerveSieve0. inversion inner_nerveSieve0; subst. apply: (congr_shfyCoef cell_eq0).
        exact: cc. }  }
    { move:  (inner_nerveSieve (@Fin.F1 1)). move =>  inner_nerveSieve0. inversion inner_nerveSieve0; subst.
      apply: glue_shfyCoef. refine (to_ilist _ (le_n 2) ).  apply: two_cases. exact: aa. exact: cc. } } }
{ apply: diffGluing. intros _.
  { intros ? ? ns. inversion ns; subst. 
    {  move:   (outer_ (@Fin.F1 dimCell0)) (innerCell_ (@Fin.F1 dimCell0))(cell_eq (@Fin.F1 dimCell0)) (inner_nerveSieve (@Fin.F1 dimCell0)).
      apply: two_cases.
      { move => innerCell_0 cell_eq0 inner_nerveSieve0. inversion inner_nerveSieve0; subst. apply: (congr_shfyCoef cell_eq0).
        exact: bb. }
      { move => innerCell_0 cell_eq0 inner_nerveSieve0. inversion inner_nerveSieve0; subst. apply: (congr_shfyCoef cell_eq0).
        exact: dd. } }
    { move:  (inner_nerveSieve (@Fin.F1 1)). move =>  inner_nerveSieve0. inversion inner_nerveSieve0; subst.
      apply: glue_shfyCoef. refine (to_ilist _ (le_n 2) ).  apply: two_cases. exact: bb. exact: dd. } } }
Defined.

Notation "[< x2 ;; .. ;; xn >]" := (Cons_ilist x2 .. (Cons_ilist xn (@Nil_ilist _ _)) ..)
  (at level 0, format "[< '['  x2  ;;  '/'  ..  ;;  '/'  xn  ']' >]" ) .
Arguments Nil_ilist {_ _}.
Arguments restrict_shfyCoef [_] cell [_ _] _.
Arguments congr_shfyCoef {_ _ _} _.

Eval compute in example2_shfyCoef. (* note that because of the permute instruction in example2_nerveSieve, 
then the order dd,bb is permuted as contrasted to aa,cc *)
(* = glue_shfyCoef
[< restrict_shfyCoef [:: 1; 0; 1]
     (diff_shfyCoef
        [< restrict_shfyCoef [:: 0; 1] (congr_shfyCoef dd) ;;
           restrict_shfyCoef [:: 0; 1] (congr_shfyCoef bb) >]) ;;
   restrict_shfyCoef [:: 0; 0; 1]
     (diff_shfyCoef
        [< restrict_shfyCoef [:: 0; 1] (congr_shfyCoef aa) ;;
           restrict_shfyCoef [:: 0; 1] (congr_shfyCoef cc) >]) >]
: shfyCoef [:: 0; 1]
 *)
End example2_shfyCoef.
End EXAMPLE.

Reset Initial.

Module NERVE.
From Coq Require Import RelationClasses Setoid SetoidClass
     Classes.Morphisms_Prop RelationPairs CRelationClasses CMorphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype tuple finfun. 
From Coq Require Lia.

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections. Set Universe Polymorphism.

Close Scope bool. Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Module Type GENE.

Class relType : Type := RelType
{ _type_relType : Type;
  _rel_relType : crelation _type_relType;
  _equiv_relType :> Equivalence _rel_relType }.
About relType.
Coercion _type_relType : relType >-> Sortclass.

Definition equiv {A: Type} {R: crelation A} `{Equivalence A R} : crelation A := R.

 (* TODO: keep or comment *)
Arguments _rel_relType : simpl never.
Arguments _equiv_relType : simpl never.
Arguments equiv : simpl never.

Notation " x == y " := (@equiv (* (@_type_relType _) *) _ (@_rel_relType _)  (@_equiv_relType _) x y) 
  (at level 70, no associativity) : type_scope.
Notation LHS := (_ : fun XX => XX == _).
Notation RHS := (_ : fun XX => _ == XX).
Notation "[|  x  ; .==. |]" := (exist (fun t => (_ == _)) x _) (at level 10, x at next level) : poly_scope.
Notation "[|  x  ; .=. |]" := (exist (fun t => (_ = _)) x _) (at level 10, x at next level) : poly_scope.

Parameter vertexGene : eqType.

Parameter arrowGene : vertexGene -> vertexGene -> relType.
Notation "''Gene' ( V ~> U )" := (@arrowGene U V)
(at level 0, format "''Gene' (  V  ~>  U  )") : poly_scope.

Parameter composGene :
forall U, forall V W, 'Gene( W ~> V ) -> 'Gene( V ~> U ) -> 'Gene( W ~> U ).
Notation "wv o:>gene vu" := (@composGene _ _ _ wv vu)
(at level 40, vu at next level) : poly_scope.

Declare Instance composGene_Proper: forall U V W, Proper (equiv ==> equiv ==> equiv) (@composGene U V W).

Parameter identGene : forall {U : vertexGene}, 'Gene( U ~> U ).

Parameter composGene_compos :
forall (U V : vertexGene) (vu : 'Gene( V ~> U ))
        (W : vertexGene) (wv : 'Gene( W ~> V )),
forall X (xw : 'Gene( X ~> W )),
  xw o:>gene ( wv o:>gene vu ) == ( xw o:>gene wv ) o:>gene vu.
Parameter composGene_identGene :
forall (U V : vertexGene) (vu : 'Gene( V ~> U )),
  (@identGene V) o:>gene vu == vu .
Parameter identGene_composGene :
forall (U : vertexGene), forall (W : vertexGene) (wv : 'Gene( W ~> U )),
  wv o:>gene (@identGene U) == wv.

Notation typeOf_objects_functor := (vertexGene -> relType).

Class relFunctor (F : typeOf_objects_functor) (G G' : vertexGene)  : Type := RelFunctor
{ _fun_relFunctor : 'Gene( G' ~> G ) -> F G -> F G' ;
  _congr_relFunctor :> Proper (equiv ==> @equiv _ _ (@_equiv_relType ( F G )) 
                         ==> @equiv _ _ (@_equiv_relType ( F G'))) _fun_relFunctor ; }.

Coercion _fun_relFunctor : relFunctor >-> Funclass.

Definition typeOf_arrows_functor (F : typeOf_objects_functor)
:= forall G G' : vertexGene, relFunctor F G G' .

Definition fun_arrows_functor_ViewOb := composGene.

Notation "wv o>gene vu" := (@fun_arrows_functor_ViewOb _ _ _ wv vu)
(at level 40, vu at next level) : poly_scope.

Definition fun_transf_ViewObMor (G H: vertexGene) (g: 'Gene( H ~> G )) (H': vertexGene) :
'Gene(H' ~> H) -> 'Gene(H' ~> G) .
Proof. exact: ( fun h =>  h o:>gene g ). Defined.

(* TODO: REDO GENERAL fun_transf_ViewObMor_Proper *)
Global Instance fun_transf_ViewObMor_Proper G H g H' : Proper (equiv ==> equiv) (@fun_transf_ViewObMor G H g H').
Proof.    move. intros ? ? Heq. unfold fun_transf_ViewObMor. rewrite -> Heq; reflexivity.
Qed.

Notation "wv :>gene vu" := (@fun_transf_ViewObMor _ _ vu _ wv)
(at level 40, vu at next level) : poly_scope.

Definition typeOf_functorialCompos_functor (F : typeOf_objects_functor)
 (F_ : typeOf_arrows_functor F)  :=
  forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
    F_ _ _ g' (F_ _ _ g f) == 
    F_ _ _ ( g' o>gene g (*? or  g' :>gene g  or  g' o:>gene g ?*) ) f.

Definition typeOf_functorialIdent_functor (F : typeOf_objects_functor)
 (F_ : typeOf_arrows_functor F) :=
  forall G (f : F G), F_ _ _ (@identGene G) f == f.

Record functor := Functor 
 { _objects_functor :> typeOf_objects_functor ;
   _arrows_functor :> (* :> ??? *) typeOf_arrows_functor _objects_functor;
   _functorialCompos_functor : typeOf_functorialCompos_functor _arrows_functor;
   _functorialIdent_functor : typeOf_functorialIdent_functor _arrows_functor;
 }.

Notation "g o>functor_ [ F ] f" := (@_arrows_functor F _ _ g f)
  (at level 40, f at next level) : poly_scope.
Notation "g o>functor_ f" := (@_arrows_functor _ _ _ g f)
  (at level 40, f at next level) : poly_scope.

Definition equiv_rel_functor_ViewOb (G H : vertexGene) : crelation 'Gene( H ~> G ).
Proof.    exact: equiv.
Defined.
(* (* no lack for now, unless want uniformity of the (opaque) witness... *)
Arguments equiv_rel_functor_ViewOb /.
 *)

Definition functor_ViewOb (G : vertexGene) : functor.
Proof. unshelve eexists.
- (* typeOf_objects_functor *) intros H. exact: 'Gene( H ~> G ).
- (* typeOf_arrows_functor *) intros H H'. exists (@fun_arrows_functor_ViewOb G H H').
  abstract (typeclasses eauto).
- (* typeOf_functorialCompos_functor *) abstract (move; intros; exact: composGene_compos).
- (* typeOf_functorialIdent_functor *) abstract (move; intros; exact: composGene_identGene).
Defined.

Definition _functorialCompos_functor' {F : functor} :
   forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
   g' o>functor_ [ F ] (g o>functor_ [ F ]  f) 
   == (g' o>functor_ [ functor_ViewOb G ] g) o>functor_ [ F ] f
:= @_functorialCompos_functor F.

Class relTransf (F E : typeOf_objects_functor) (G : vertexGene) : Type := RelTransf
{ _fun_relTransf : F G -> E G ;
  _congr_relTransf :> Proper (@equiv _ _ (@_equiv_relType ( F G )) 
                          ==> @equiv _  _ (@_equiv_relType ( E G))) _fun_relTransf ; }.

Coercion _fun_relTransf : relTransf >-> Funclass.

Notation typeOf_arrows_transf F E
:= (forall G : vertexGene, relTransf F E G) .

Definition typeOf_natural_transf (F E : functor)
 (ee : typeOf_arrows_transf F E) :=
  forall G G' (g : 'Gene( G' ~> G )) (f : F G),
  g o>functor_[E] (ee G f) == ee G' (g o>functor_[F] f).

Record transf (F : functor) (E : functor) := Transf
{ _arrows_transf :> typeOf_arrows_transf F E ;
  _natural_transf : typeOf_natural_transf _arrows_transf;
}.

Notation "f :>transf_ [ G ] ee" := (@_arrows_transf _ _ ee G f)
  (at level 40, ee at next level) : poly_scope.

Notation "f :>transf_ ee" := (@_arrows_transf _ _ ee _ f)
  (at level 40, ee at next level) : poly_scope.

Definition transf_ViewObMor (G : vertexGene) (H : vertexGene) (g : 'Gene( H ~> G )) :
transf (functor_ViewOb H) (functor_ViewOb G).
Proof.  unshelve eexists.
- (* _arrows_transf *)  unshelve eexists.
  + (* _fun_relTransf *) exact: (fun_transf_ViewObMor g).
  + (* _congr_relTransf  *) exact: fun_transf_ViewObMor_Proper.
- (* _natural_transf *)abstract (move; simpl; intros; exact: composGene_compos).
Defined.

Definition _functorialCompos_functor'' {F : functor} :
   forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
   g' o>functor_ [ F ] (g o>functor_ [ F ]  f) 
   == (g' :>transf_ (transf_ViewObMor g)) o>functor_ [ F ] f
:= @_functorialCompos_functor F.
 
Record sieveFunctor (U : vertexGene) : Type := 
  { _functor_sieveFunctor :> functor ;
    _transf_sieveFunctor : transf _functor_sieveFunctor (functor_ViewOb U) ; }.

Lemma transf_sieveFunctor_Proper (U : vertexGene) (UU : sieveFunctor U) H: 
Proper (equiv ==> equiv) (_transf_sieveFunctor UU H).
  apply: _congr_relTransf.
Qed.

Notation "''Sieve' ( G' ~> G | VV )" := (@_functor_sieveFunctor G VV G')
     (at level 0, format "''Sieve' (  G'  ~>  G  |  VV  )") : poly_scope.
Notation "h o>sieve_ v " := (h o>functor_[@_functor_sieveFunctor _ _] v)
          (at level 40, v at next level, format "h  o>sieve_  v") : poly_scope.
Notation "v :>sieve_" := (v :>transf_ (_transf_sieveFunctor _)) (at level 40) : poly_scope.

Record preSieve (U : vertexGene) : Type := 
  { _functor_preSieve :>  vertexGene -> Type;
    _transf_preSieve : forall G : vertexGene, (_functor_preSieve G) -> (functor_ViewOb U G) ; }.

Arguments _transf_preSieve {_ _ _} .

Notation "''preSieve' ( G' ~> G | VV )" := (@_functor_preSieve G VV G')
     (at level 0, format "''preSieve' (  G'  ~>  G  |  VV  )") : poly_scope.
Notation "v :>preSieve_" := (@_transf_preSieve _ _ _ v) (at level 40) : poly_scope.

Global Ltac cbn_ := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve].
Global Ltac cbn_equiv := unfold _rel_relType, equiv; cbn -[ _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve].
Global Ltac cbn_view := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor  _arrows_functor 
                             _arrows_transf  _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor].
Global Ltac cbn_functor := cbn -[equiv _type_relType _rel_relType _equiv_relType functor_ViewOb
                               _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve].
Global Ltac cbn_transf := cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
                               transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve].
Global Ltac cbn_sieve := cbn -[equiv _type_relType _rel_relType _equiv_relType   functor_ViewOb
                                 transf_ViewObMor ].

Tactic Notation "cbn_" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve] in H.
Tactic Notation "cbn_equiv" "in" hyp_list(H) := unfold _rel_relType, equiv in H; cbn -[ _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve] in H.
Tactic Notation "cbn_view" "in"  hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor  _arrows_functor 
                             _arrows_transf  _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve] in H.
Tactic Notation "cbn_functor" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType functor_ViewOb
                               _arrows_transf transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve] in H.
Tactic Notation "cbn_transf" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
                               transf_ViewObMor _functor_sieveFunctor _functor_preSieve _transf_sieveFunctor _transf_preSieve] in H.
Tactic Notation "cbn_sieve" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType   functor_ViewOb
                                 transf_ViewObMor ] in H.

End GENE.

Module Type COMOD (Gene : GENE).
Import Gene.

Ltac tac_unsimpl := repeat
lazymatch goal with
| [ |- context [@fun_transf_ViewObMor ?G ?H ?g ?H' ?h] ] => 
change (@fun_transf_ViewObMor G H g H' h) with 
(h :>transf_ (transf_ViewObMor g))
| [ |- context [@fun_arrows_functor_ViewOb ?U ?V ?W ?wv ?vu] ] => 
change (@fun_arrows_functor_ViewOb U V W wv vu) with 
(wv o>functor_[functor_ViewOb U] vu)

(* no lack*)
| [ |- context [@equiv_rel_functor_ViewOb ?G ?H ?x ?y] ] =>  
  change (@equiv_rel_functor_ViewOb G H x y) with 
(@equiv _ _ (@_equiv_relType ( (functor_ViewOb G) H )) x y) 
(* | [ |- context [@equiv_rel_arrowSieve ?G ?G' ?g ?H ?x ?y] ] =>  
  change (@equiv_rel_arrowSieve G G' g H x y) with 
(@equiv _ (@_rel_relType ( (arrowSieve g) H )) x y)  *)
end.

Definition transf_Compos :
forall (F F'' F' : functor) (ff_ : transf F'' F') (ff' : transf F' F),
transf F'' F.
Proof.  intros. unshelve eexists.
- intros G. unshelve eexists. intros f. exact:((f :>transf_ ff_) :>transf_ ff').
  abstract(solve_proper).
(*   exists (Basics.compose (ff' G) (ff_ G) ).  abstract(typeclasses eauto). *)
- abstract (move; cbn_; intros; (* unfold Basics.compose; *)
    rewrite -> _natural_transf , _natural_transf; reflexivity).
Defined.

Definition transf_Ident :
forall (F : functor), transf F F.
Proof.  intros. unshelve eexists.
- intros G. exists id. 
  abstract(simpl_relation).
- abstract (move; cbn_; intros; reflexivity).
Defined.

Definition typeOf_commute_sieveTransf
(G : vertexGene) (V1 V2 : sieveFunctor G) (vv : transf V1 V2)  : Type :=
  forall (H : vertexGene)  (v : 'Sieve( H ~> G | V1 )),
  (v :>transf_ vv) :>sieve_ ==  v :>sieve_ .

Record sieveTransf G (V1 V2 : sieveFunctor G) : Type :=
  { _transf_sieveTransf :> transf V1 V2 ;
    _commute_sieveTransf : typeOf_commute_sieveTransf _transf_sieveTransf} .

Instance fun_transf_ViewObMor_measure {G H: vertexGene} {g: 'Gene( H ~> G )} {H': vertexGene}:
 @Measure 'Gene(H' ~> H)  'Gene(H' ~> G) (@fun_transf_ViewObMor G H g H') := { }.

Definition sieveTransf_Compos :
forall U (F F'' F' : sieveFunctor U) (ff_ : sieveTransf F'' F') (ff' : sieveTransf F' F),
sieveTransf F'' F.
Proof.  intros. unshelve eexists.
- exact: (transf_Compos ff_ ff').
- abstract(move; intros; cbn_transf; autounfold; do 2 rewrite -> _commute_sieveTransf; reflexivity).
Defined.

Definition sieveTransf_Ident :
forall U (F  : sieveFunctor U) , sieveTransf F F.
Proof.  intros. unshelve eexists.
- exact: (transf_Ident F).
- abstract(move; intros; reflexivity).
Defined.

Definition identSieve (G: vertexGene) : sieveFunctor G.
unshelve eexists.
exact: (functor_ViewOb G).
exact: (transf_Ident (functor_ViewOb G)).
Defined.

Inductive myunit : Type := mytt.
Inductive myEmpty_set : Type := .

Definition identPreSieve (G: vertexGene) : preSieve G.
unshelve eexists.
- intros H. destruct (@eq_op _ G H). exact: myunit. exact: myEmpty_set.
- intros H. simpl. case: eqP. 
  + intros; subst. intros. exact: identGene.
  + abstract(move => ? []).
Defined.

Definition sieveTransf_identSieve :
forall U (F  : sieveFunctor U) , sieveTransf F (identSieve U).
Proof.  intros. unshelve eexists.
- exact: (_transf_sieveFunctor F).
- abstract(move; intros; reflexivity).
Defined.
(* TODO MERE WITH sieveTransf_identSieve *)
Lemma sieveTransf_sieveFunctor G (VV : sieveFunctor G) :
sieveTransf VV (identSieve G).
Proof. unshelve eexists. exact: _transf_sieveFunctor.
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Record sieveEquiv G (V1 V2 : sieveFunctor G) : Type :=
  { _sieveTransf_sieveEquiv :> sieveTransf V1 V2 ;
  _revSieveTransf_sieveEquiv : sieveTransf V2 V1 ;
  _injProp_sieveEquiv : forall H v, (v :>transf_[H] _revSieveTransf_sieveEquiv )
                            :>transf_ _sieveTransf_sieveEquiv == v ; 
_surProp_sieveEquiv : forall H v, (v :>transf_[H] _sieveTransf_sieveEquiv )
                            :>transf_ _revSieveTransf_sieveEquiv == v } .

Definition rel_sieveEquiv G : crelation (sieveFunctor G) := fun V1 V2 => sieveEquiv V1 V2.

Instance equiv_sieveEquiv G: Equivalence (@rel_sieveEquiv G ).
unshelve eexists.
- intros V1. unshelve eexists. exact (sieveTransf_Ident _). exact (sieveTransf_Ident _).
abstract (reflexivity). abstract (reflexivity).
- intros V1 V2 Hseq. unshelve eexists. 
   exact (_revSieveTransf_sieveEquiv Hseq). exact (_sieveTransf_sieveEquiv Hseq).
abstract(intros; rewrite -> _surProp_sieveEquiv; reflexivity).
abstract(intros; rewrite -> _injProp_sieveEquiv; reflexivity).
- intros V1 V2 V3 Hseq12 Hseq23. unshelve eexists. exact (sieveTransf_Compos Hseq12 Hseq23). 
exact (sieveTransf_Compos (_revSieveTransf_sieveEquiv Hseq23) (_revSieveTransf_sieveEquiv Hseq12)).
abstract(intros; cbn_transf;  rewrite -> _injProp_sieveEquiv; rewrite -> _injProp_sieveEquiv; reflexivity).
abstract(intros; cbn_transf;  rewrite -> _surProp_sieveEquiv; rewrite -> _surProp_sieveEquiv; reflexivity).
Defined.

Section interSieve.

 Section Section1.
 Variables (G : vertexGene) (VV : sieveFunctor G)
           (G' : vertexGene) (g : 'Gene( G' ~> G ))
           (UU : sieveFunctor G').

Record type_interSieve H :=
  { _factor_interSieve : 'Sieve( H ~> _ | UU ) ;
    _whole_interSieve : 'Sieve( H ~> _ | VV ) ;
    _wholeProp_interSieve : _whole_interSieve :>sieve_ 
        == (_factor_interSieve :>sieve_) o>functor_[functor_ViewOb G] g }.

Definition rel_interSieve H : crelation (type_interSieve H).
intros v v'. exact (((_factor_interSieve v == _factor_interSieve v') *
(_whole_interSieve v == _whole_interSieve v')) %type ).
Defined.

Instance equiv_interSieve H : Equivalence (@rel_interSieve H).
abstract(unshelve eexists;
[ (move; intros; move; split; reflexivity)
| (move; intros ? ? [? ?]; move; intros; split; symmetry; assumption)
| (move; intros ? ? ? [? ?] [? ?]; move; intros; split; etransitivity; eassumption)]).
Qed.

Definition interSieve : sieveFunctor G'.
Proof. unshelve eexists.
{ (* functor *) unshelve eexists.
  - (* typeOf_objects_functor *) intros H. 
    + (* relType *) unshelve eexists. exact (type_interSieve H).
      exact (@rel_interSieve H).
      exact (@equiv_interSieve H).
  - (* typeOf_arrows_functor *) unfold typeOf_arrows_functor. intros H H'.
    +  (* relFunctor *) unshelve eexists.
      * (* -> *) cbn_. intros h vg'. unshelve eexists.          
          exact: (h o>sieve_ (_factor_interSieve vg')).
          exact: (h o>sieve_ (_whole_interSieve vg')). 
          abstract(cbn_; tac_unsimpl; rewrite <- 2!_natural_transf; 
          rewrite -> _wholeProp_interSieve, _functorialCompos_functor'; reflexivity).
      * (* Proper *) abstract(move; autounfold;
      intros h1 h2 Heq_h vg'1 vg'2; case => /= Heq_vg' Heq_vg'0;
      split; cbn_; rewrite -> Heq_h;  [rewrite -> Heq_vg' | rewrite -> Heq_vg'0]; reflexivity).
  - (* typeOf_functorialCompos_functor *) abstract(move; intros; autounfold; split; cbn_;
  rewrite -> _functorialCompos_functor; reflexivity).
  - (* typeOf_functorialIdent_functor *) abstract(move; intros; autounfold; split; cbn_;
    rewrite -> _functorialIdent_functor; reflexivity). }
{ (* transf *) unshelve eexists.
  - (* typeOf_arrows_transf *) intros H. unshelve eexists.
    + (* -> *) cbn_; intros vg'. exact: ((_factor_interSieve vg') :>sieve_).
    + (* Proper *)  abstract(move; autounfold; cbn_;
    intros vg'1 vg'2; case => /= Heq0 Heq; rewrite -> Heq0; reflexivity).
  - (* typeOf_natural_transf *) abstract(move; cbn -[_arrows_functor]; intros; 
  rewrite -> _natural_transf; reflexivity). }
Defined.

Lemma transf_interSieve_Eq  H  (v : 'Sieve(H ~> _ | interSieve )) :
 ((_factor_interSieve v) :>sieve_ ) == (v :>sieve_ ) .
Proof. reflexivity.
Qed.

Global Instance whole_interSieve_Proper  H : Proper (equiv ==> equiv) 
 (@_whole_interSieve  H : 'Sieve( H ~> _ | interSieve  ) -> 'Sieve( H ~> _ | VV )). 
Proof.    move. cbn_. intros v1 v2 [Heq Heq']. exact Heq'.
Qed.

Global Instance factor_interSieve_Proper  H : Proper (equiv ==> equiv) 
 (@_factor_interSieve  H : 'Sieve( H ~> _ | interSieve  ) -> 'Sieve( H ~> _ | UU )). 
Proof.    move. cbn_. intros v1 v2 [Heq Heq']. exact Heq.
Qed.

Definition interSieve_projWhole : transf interSieve VV.
Proof. unshelve eexists. unshelve eexists.
- (* -> *) exact: _whole_interSieve.
- (* Proper *) exact: whole_interSieve_Proper. (* abstract (typeclasses eauto).  *)
- (* typeOf_natural_transf *) abstract(intros H H' h f; cbn_; reflexivity).
Defined.

Definition interSieve_projFactor : sieveTransf interSieve UU.
Proof. unshelve eexists.  unshelve eexists. unshelve eexists.
- (* -> *) exact: _factor_interSieve.
- (* Proper *) exact: factor_interSieve_Proper. (* abstract (typeclasses eauto).  *)
- (* typeOf_natural_transf *) abstract(intros H H' h f; cbn_;  reflexivity).
- (* _commute_sieveTransf *) abstract(move; cbn_; intros; reflexivity).
Defined.

End Section1.

Definition pullSieve G VV G' g := @interSieve G  VV G' g (identSieve G').
Definition meetSieve G VV UU := @interSieve G VV G (@identGene G) UU.

Definition pullSieve_projWhole G VV G' g : 
transf (@pullSieve G VV G' g) VV
:= (@interSieve_projWhole G  VV G' g (identSieve G')).

Definition pullSieve_projFactor G VV G' g : 
sieveTransf (@pullSieve G VV G' g) (identSieve G')
:= (@interSieve_projFactor G  VV G' g (identSieve G')).

Definition meetSieve_projFactor G VV UU : 
sieveTransf (@meetSieve G VV UU) UU := @interSieve_projFactor G VV G (@identGene G) UU  .

Definition meetSieve_projWhole G VV UU : 
sieveTransf (@meetSieve G VV UU) VV.
exists (interSieve_projWhole _ _ _).
intros H v; simpl. rewrite -> _wholeProp_interSieve.
(* HERE *) abstract(exact: identGene_composGene).
Defined.

Section Section2.
Variables (G : vertexGene) (VV : sieveFunctor G)
  (G' : vertexGene) (g : 'Gene( G' ~> G ))
  (UU : sieveFunctor G')
  (G'' : vertexGene) (g' : 'Gene( G'' ~> G' ))(WW : sieveFunctor G'').

Definition interSieve_compos : transf (interSieve VV (g' o>functor_[functor_ViewOb G] g)
(interSieve UU g' WW) ) (interSieve VV g UU).
Proof. unshelve eexists. intros H. unshelve eexists.
- (* -> *) intros v; unshelve eexists. 
    exact: ((_whole_interSieve (_factor_interSieve v)) ).
    exact: (_whole_interSieve v) .
    abstract(do 2 rewrite -> _wholeProp_interSieve; 
    rewrite -> _functorialCompos_functor'; simpl; reflexivity).
- (* Proper *) abstract(move; move => f1 f2 Heq;
split; autounfold; simpl; [rewrite -> (whole_interSieve_Proper (factor_interSieve_Proper Heq)); reflexivity
| rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (* typeOf_natural_transf *) abstract (intros H H' h f; autounfold; split; simpl; reflexivity).
Defined.

Definition pullSieve_compos : transf (pullSieve VV (g' o>functor_[functor_ViewOb G] g)) (pullSieve VV g).
Proof. unshelve eexists. intros H. unshelve eexists.
- (* -> *) intros v; unshelve eexists. 
    exact: ((_factor_interSieve v) o>functor_[functor_ViewOb G'] g').
    exact: (_whole_interSieve v) .
    abstract(rewrite -> _wholeProp_interSieve; rewrite -> _functorialCompos_functor'; simpl; reflexivity).
- (* Proper *) abstract(move; move => f1 f2 Heq;
split; autounfold; simpl; [rewrite ->  (factor_interSieve_Proper Heq); reflexivity
| rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (* typeOf_natural_transf *) intros H H' h f; autounfold; split; cbn_sieve; cbn_functor;
[ rewrite -> _functorialCompos_functor'; reflexivity
| reflexivity ].
Defined.
End Section2.

Lemma interSieve_congr G (VV1 VV2 : sieveFunctor G)  (vv: sieveTransf VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2)
  (UU1 UU2 : sieveFunctor G') (uu: sieveTransf UU1 UU2): 
  sieveTransf (interSieve VV1 g1 UU1) (interSieve VV2 g2 UU2).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact: ((_factor_interSieve v) :>transf_ uu). 
  (* _whole_interSieve *) exact: ((_whole_interSieve v) :>transf_ vv).
  (* _wholeProp_interSieve *) abstract(simpl; rewrite  -> _commute_sieveTransf ,
  _commute_sieveTransf , _wholeProp_interSieve , genEquiv; reflexivity).
  (* _congr_relTransf  *) abstract(move; intros ? ? Heq; split; autounfold; simpl;
  [ rewrite -> (factor_interSieve_Proper Heq); reflexivity
  | rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (*  _natural_transf  *) abstract(intros H' H h v; split; simpl;
  rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(intros H v; simpl; rewrite -> _commute_sieveTransf; reflexivity).
Defined.

Definition pullSieve_congr G (VV1 VV2 : sieveFunctor G)  (vv: sieveTransf VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2): 
  sieveTransf (pullSieve VV1 g1) (pullSieve VV2 g2)
  := @interSieve_congr G VV1 VV2 vv G' g1 g2 genEquiv _ _ (sieveTransf_Ident _).

Lemma pullSieve_pullSieve G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G)) G'' (g' : 'Gene(G'' ~> G')): 
sieveTransf (pullSieve (pullSieve VV g) g') (pullSieve VV (g' o>functor_[functor_ViewOb _] g)).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) exact: ((_whole_interSieve (_whole_interSieve v))).
  (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
   rewrite -> _functorialCompos_functor';
   setoid_rewrite <- _wholeProp_interSieve at 2; simpl; reflexivity).
  (* _congr_relTransf  *) abstract(move; intros ? ? Heq; split; autounfold; cbn -[_rel_relType];
   [ rewrite -> (factor_interSieve_Proper Heq); reflexivity
   | rewrite -> (whole_interSieve_Proper (whole_interSieve_Proper Heq)); reflexivity]) .
- (*  _natural_transf  *) abstract(move; split; simpl; reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma pullSieve_pullSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')): sieveTransf (pullSieve VV (g' o>functor_[functor_ViewOb _] g)) (pullSieve (pullSieve VV g) g') .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) { unshelve eexists.
        (* _factor_interSieve *) exact (_factor_interSieve v o>functor_[functor_ViewOb _] g'). 
        (* _whole_interSieve *) exact: ( _whole_interSieve v).
        (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
        rewrite -> _functorialCompos_functor'; reflexivity). }
  (* _wholeProp_interSieve *)  abstract(reflexivity).
  (* _congr_relTransf  *) abstract  (move; intros v1 v2; case; autounfold; cbn_; 
  move => Heq_factor Heq_whole; split; autounfold; cbn -[_rel_relType];
  [rewrite -> Heq_factor; reflexivity | ]; split; autounfold; cbn -[_rel_relType];
  [rewrite -> Heq_factor; reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
[reflexivity | split; cbn_sieve; 
[ rewrite -> _functorialCompos_functor'; reflexivity | reflexivity ]]).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma pullSieve_ident G (VV : sieveFunctor G) : sieveTransf (pullSieve VV identGene) VV.
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. exact: (_whole_interSieve v).
  (* _congr_relTransf  *) abstract (move; move => x y Heq;
   rewrite -> (whole_interSieve_Proper Heq); reflexivity).
- (* _natural_transf *) abstract(move; intros; simpl; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; simpl; rewrite -> _wholeProp_interSieve; simpl; 
(* FUNCTOR/TRANSF PROBLEM *) apply: identGene_composGene).
Defined.

Lemma pullSieve_ident_rev G (VV : sieveFunctor G) : sieveTransf VV (pullSieve VV identGene).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact (v :>sieve_). exact v.
        abstract (cbn_sieve; symmetry; apply: identGene_composGene).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *) abstract(move; intros; cbn_sieve; split; cbn_sieve; 
            last reflexivity; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
Defined.

End interSieve.

Existing Instance whole_interSieve_Proper.
Existing Instance factor_interSieve_Proper.

Lemma interSieve_composeOuter G (VV : sieveFunctor G) 
G' (g : 'Gene(G' ~> G)) (UU : sieveFunctor G')
 G'' (g' : 'Gene(G'' ~> G')) G''' (g'' : 'Gene(G''' ~> G''))    : 
  transf (interSieve    (pullSieve VV (g' o>gene g))  g'' (pullSieve UU (g'' o>gene g')))
   (interSieve VV g UU).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact: ((v :>transf_ (interSieve_projFactor _ _ _)) 
      :>transf_ (pullSieve_projWhole _ _ ) ). 
  (* _whole_interSieve *) exact: ((v :>transf_ (interSieve_projWhole _ _ _)) 
      :>transf_ (pullSieve_projWhole _ _ ) ). 
  (* _wholeProp_interSieve *) abstract (cbn_transf; do 2 rewrite -> _wholeProp_interSieve;
  rewrite -> (_wholeProp_interSieve v); tac_unsimpl;
   do 3 rewrite <- _functorialCompos_functor';
  reflexivity).
  (* _congr_relTransf  *) abstract (move; intros ? ? Heq; split; cbn_transf;
  rewrite -> Heq; reflexivity).
- (*  _natural_transf  *) abstract (intros H' H h v; split; cbn_sieve; reflexivity).
Defined.

Lemma interSieve_composeOuter_ident G (VV : sieveFunctor G) 
G' (g : 'Gene(G' ~> G)) (UU : sieveFunctor G')
 G'' (g' : 'Gene(G'' ~> G'))  : 
  transf (interSieve    (pullSieve VV (g' o>gene g))  (identGene)    (pullSieve UU ( g')))
   (interSieve VV g UU).
Proof. refine (transf_Compos _ (interSieve_composeOuter _ _ _ g' identGene)).
refine (interSieve_congr (sieveTransf_Ident _) (reflexivity _) _).
refine (pullSieve_congr (sieveTransf_Ident _) _).
abstract (symmetry; exact: composGene_identGene).
Defined.

Lemma interSieve_congr_sieveEquiv G (VV1 VV2 : sieveFunctor G)  (vv: sieveEquiv VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2)
  (UU1 UU2 : sieveFunctor G') (uu: sieveEquiv UU1 UU2): 
  sieveEquiv (interSieve VV1 g1 UU1) (interSieve VV2 g2 UU2).
Proof. unshelve eexists.
exact: (interSieve_congr vv genEquiv uu).
exact (interSieve_congr (_revSieveTransf_sieveEquiv vv) 
  (symmetry genEquiv) (_revSieveTransf_sieveEquiv uu)).
abstract (intros; split; simpl; rewrite -> _injProp_sieveEquiv; reflexivity).
abstract(intros; split; simpl; rewrite -> _surProp_sieveEquiv; reflexivity).
Defined.

Definition pullSieve_congr_sieveEquiv G (VV1 VV2 : sieveFunctor G)  (vv: sieveEquiv VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2): 
  sieveEquiv (pullSieve VV1 g1) (pullSieve VV2 g2)
  := @interSieve_congr_sieveEquiv G VV1 VV2 vv G' g1 g2 genEquiv _ _ (reflexivity _).

Lemma pullSieve_pullSieve_sieveEquiv G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')): sieveEquiv (pullSieve (pullSieve VV g) g') 
  (pullSieve VV (g' o>functor_[functor_ViewOb _] g)).
Proof. unshelve eexists.
exact: pullSieve_pullSieve.
exact: pullSieve_pullSieve_rev.
abstract(intros; split; cbn_transf; reflexivity).
abstract(intros H v; split; cbn_transf; first reflexivity;
last split; cbn_transf; first (rewrite -> (_wholeProp_interSieve v); reflexivity);
     last reflexivity).
Defined.

Lemma pullSieve_ident_sieveEquiv G (VV : sieveFunctor G) : 
  sieveEquiv (pullSieve VV identGene) VV.
Proof. unshelve eexists.
exact: pullSieve_ident.
exact: pullSieve_ident_rev.
abstract(intros; cbn_transf; reflexivity).
abstract(intros H v; split; cbn_transf; last reflexivity;
first rewrite -> _wholeProp_interSieve; apply: identGene_composGene).
Defined.

Definition interSieve_identSieve_sieveEquiv (G G': vertexGene)
(g: 'Gene( G' ~> G )) (WW : sieveFunctor G')
: sieveEquiv (interSieve (identSieve G) g WW) WW.
Proof. unshelve eexists. exact: interSieve_projFactor.
- {  unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact v. exact ((v :>sieve_) :>transf_ (transf_ViewObMor g)).
        abstract (cbn_sieve; reflexivity).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; 
        cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
abstract(move; intros; cbn_sieve; split; cbn_sieve; first reflexivity; 
    do 2 rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
}
- abstract (intros; cbn_transf; reflexivity).
- abstract (intros H v; cbn_transf; split; cbn_transf; first reflexivity; 
  symmetry; apply: (_wholeProp_interSieve v)).
Defined.

(* TODO: REDO: instance of interSieve_identSieve_sieveEquiv *)
Definition pullSieve_identSieve_sieveEquiv (G G': vertexGene)
(g: 'Gene( G' ~> G ))
: sieveEquiv (pullSieve (identSieve G) g) (identSieve G').
Proof. unshelve eexists. exact: interSieve_projFactor.
- { unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact (v :>sieve_). exact (v :>transf_ (transf_ViewObMor g)).
        abstract (cbn_sieve; reflexivity).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; 
      cbn_transf; split; cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
  abstract(move; intros; cbn_sieve; split; cbn_sieve; 
    first reflexivity; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
}
- abstract (intros; cbn_transf; reflexivity).
- abstract (intros H v; cbn_transf; split; cbn_transf; first reflexivity; 
  symmetry; apply: (_wholeProp_interSieve v)).
Defined.

Lemma interSieve_interSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU))
  (interSieve (interSieve VV g WW) g' UU) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve (_factor_interSieve v)). 
  (* _whole_interSieve *) refine ( v :>transf_  (interSieve_compos _ _ _ _ _) ).
  (* _wholeProp_interSieve *)  abstract (cbn_sieve; rewrite -> _wholeProp_interSieve; reflexivity).
  (* _congr_relTransf  *) abstract (move; intros v1 v2; case; cbn_sieve;
  move => Heq_factor Heq_whole; split; cbn_sieve;
  [rewrite -> (factor_interSieve_Proper Heq_factor); reflexivity | ]; split; cbn_sieve;
  [rewrite -> (whole_interSieve_Proper Heq_factor); reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
    first reflexivity;  split; cbn_sieve; reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma interSieve_interSieve G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve (interSieve VV g WW) g' UU) 
  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU)).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) refine ( v :>transf_  (interSieve_congr (interSieve_projFactor _ _ _) 
      (reflexivity _) (sieveTransf_Ident _)) ). 
  (* _whole_interSieve *) exact: ((_whole_interSieve (_whole_interSieve v))).
  (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
   rewrite -> _functorialCompos_functor';
   setoid_rewrite <- _wholeProp_interSieve at 2; simpl; reflexivity).
  (* _congr_relTransf  *) abstract (move; intros ? ? [Heq_outer Heq_inner];split;  cbn_sieve;
  first (split; cbn_sieve; first (rewrite -> Heq_outer; reflexivity); 
        rewrite -> (factor_interSieve_Proper Heq_inner); reflexivity );
  last rewrite -> (whole_interSieve_Proper Heq_inner); reflexivity).
- (*  _natural_transf  *) abstract(move; split; cbn_sieve; first (split; cbn_sieve; reflexivity);
                          last reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma interSieve_interSieve_sieveEquiv  G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveEquiv  (interSieve (interSieve VV g WW) g' UU) 
  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU)).
Proof. unshelve eexists.
exact: interSieve_interSieve.
exact: interSieve_interSieve_rev.
abstract(intros; split; cbn_transf; first (split; cbn_transf; reflexivity); reflexivity).
abstract(intros H v; split; cbn_transf; first reflexivity;
last split; cbn_transf; reflexivity).
Defined.

(*  NOT LACKED, SEE GENERAL interSieve_interSieve_rev *)
Lemma interSieve_pullSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve VV (g' o>functor_[functor_ViewOb _] g) UU)
  (interSieve (pullSieve VV g) g' UU) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) { refine ( v :>transf_  _ ).
      refine (transf_Compos (interSieve_congr (sieveTransf_Ident _) (reflexivity _) 
                                    (sieveTransf_sieveFunctor _)) _). 
      exact (pullSieve_compos _ _ _). }
  (* _wholeProp_interSieve *)  abstract(reflexivity).
  (* _congr_relTransf  *) abstract  (move; intros v1 v2; case; cbn_sieve;
  move => Heq_factor Heq_whole; split; cbn_sieve;
  [rewrite -> Heq_factor; reflexivity | ]; split; cbn_sieve;
  [rewrite -> Heq_factor; reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
[reflexivity | split; cbn_sieve; 
[ rewrite -> _functorialCompos_functor'; 
  rewrite -> _natural_transf; reflexivity | reflexivity ]]).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Definition interSieve_image_rev (G : vertexGene)
(UU : sieveFunctor G)
(H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (VV : sieveFunctor H)
: sieveTransf (interSieve UU (u :>sieve_)  VV) VV.
Proof. exact: interSieve_projFactor.
Defined.

Definition interSieve_image (G : vertexGene)
(UU : sieveFunctor G)
(H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (VV : sieveFunctor H)
: sieveTransf VV (interSieve UU (u :>sieve_)  VV) .
Proof.  unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros K. unshelve eexists.
(* _fun_relTransf *) intros v. unshelve eexists. 
      exact v. exact ((v :>sieve_) o>sieve_ u).
      abstract (cbn_sieve; rewrite -> _natural_transf; reflexivity).
(* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; 
    cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
abstract(move; intros; cbn_sieve; split; cbn_sieve; first reflexivity; 
    rewrite <- _natural_transf, <- _functorialCompos_functor' ; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
Defined.

Section sumSieve.

Section Section1.
Variables (G : vertexGene) (VV : preSieve G).

Record typeOf_outer_sumSieve :=
  { _object_typeOf_outer_sumSieve :> vertexGene ; 
    _arrow_typeOf_outer_sumSieve :> 'preSieve( _object_typeOf_outer_sumSieve ~> G | VV ) }.

(* higher/congruent structure is possible... *)
Variables (WP_ : forall (object_: vertexGene) (outer_: 'preSieve( object_ ~> G | VV )),
 sieveFunctor object_).
 

(*
(* higher/congruent structure is possible... *)
Definition typeOf_sieveCongr :=
  forall (object_ : vertexGene)
  (outer_ outer_' : 'preSieve( object_ ~> _ | VV )),
outer_  == outer_' ->
sieveEquiv (WP_  outer_) (WP_  outer_').

Variables WP_congr : typeOf_sieveCongr. *)

Record type_sumSieve H :=
  { _object_sumSieve : vertexGene ;
    _outer_sumSieve : 'preSieve( _object_sumSieve ~> G | VV ) ; 
    _inner_sumSieve : 'Sieve( H ~> _ | WP_ _outer_sumSieve ) }.

Inductive rel_sumSieve H  (wv : type_sumSieve H) : type_sumSieve H  -> Type :=
| Rel_sumSieve : forall
  (inner': (WP_  (_outer_sumSieve wv)) H),
  (* higher/congruent structure is possible... *)
  (* inner' :>transf_ (WP_congr Heq_outer) == (_inner_sumSieve wv) -> *)
  inner'  == (_inner_sumSieve wv) ->
  rel_sumSieve wv
  {| _object_sumSieve := _ ;
  _outer_sumSieve := _ ; 
  _inner_sumSieve := inner' |}.

Instance rel_sumSieve_Equivalence H : Equivalence (@rel_sumSieve H).
abstract(unshelve eexists;
      [ (intros [object_wv outer_wv inner_wv]; constructor; reflexivity)
      | (* intros wv1 wv2 []. *) (intros [object_wv1 outer_wv1 inner_wv1] [object_wv2 outer_wv2 inner_wv2] [];
       constructor; symmetry; assumption)
      | (intros wv1 wv2 wv3 Heq12 Heq23; destruct Heq23 as [ inner3  Heq23'];
      destruct Heq12 as [ inner2  Heq12']; simpl; constructor; simpl;
       rewrite -> Heq23'; simpl; rewrite -> Heq12'; simpl; reflexivity)]).
Qed.

(* TODO: sumSieve_projOuter : sumSieve -> UU  *)
Definition sumSieve : sieveFunctor G.
Proof. unshelve eexists.
{ (* functor *) unshelve eexists.
  - (* typeOf_objects_functor *) intros H.
    + (* relType *) unshelve eexists. exact (type_sumSieve H).
    + (* Setoid *)  exact (@rel_sumSieve H).
     (* exists (equiv @@ (@compos_sumSieve H))%signature. *)
    + (* Equivalence *) exact: rel_sumSieve_Equivalence.
  - (* typeOf_arrows_functor *) move. intros H H'.
    (* relFunctor *) unshelve eexists.
    + (* -> *) simpl. intros h wv. unshelve eexists.
        exact: (_object_sumSieve wv). exact: (_outer_sumSieve wv).
        exact: (h o>sieve_ _inner_sumSieve wv).
    + (* Proper *) abstract(move;  autounfold; simpl;
    intros h1 h2 Heq_h [object_wv1 outer_wv1 inner_wv1] wv2 Heq; tac_unsimpl;
    case: wv2 / Heq => /= [ inner_wv2  Heq12']; constructor; simpl; 
    rewrite -> Heq_h , Heq12'; reflexivity).
  - (* typeOf_functorialCompos_functor *) abstract(intros H H' h H'' h' [object_wv outer_wv inner_wv];
     simpl; constructor; simpl; rewrite -> _functorialCompos_functor; reflexivity).
  - (* typeOf_functorialIdent_functor *) abstract(intros H [object_wv outer_wv inner_wv];
  simpl; constructor; simpl; rewrite ->  _functorialIdent_functor; reflexivity). }
{ (* transf *) unshelve eexists.
  - (* typeOf_arrows_transf *) intros H. unshelve eexists.
    + (* -> *) simpl; intros wv. exact: ((_inner_sumSieve wv :>sieve_) o>functor_ (_outer_sumSieve wv :>preSieve_)). 
    + (* Proper *) abstract(move; autounfold; simpl;
    intros wv1 wv2 Heq; tac_unsimpl;
    case: wv2 / Heq => /= [ inner_wv2  Heq12']; tac_unsimpl; 
    rewrite -> Heq12'; reflexivity).
  - (* typeOf_natural_transf *) abstract(move; cbn_functor; move; cbn_functor; intros H H' h wv;
  rewrite -> _functorialCompos_functor'; rewrite -> _natural_transf; reflexivity). }
Defined.

End Section1.

Section genSieve.

Definition genSieve (U : vertexGene) (UU : preSieve U)
  := (sumSieve (fun (object: vertexGene) (outer: 'preSieve( object ~> U | UU )) =>  identSieve object ) ). 

Definition preSieveTransf_unit  (U : vertexGene) (UU : preSieve U)  :
  forall G (outer: 'preSieve( G ~> U | UU )), 'Sieve( G ~> U | (genSieve UU)  ) .
Proof. intros. exists _ outer. exact: (identGene). Defined.

Definition transf_of_preSieveTransf 
  (U : vertexGene) (UU : preSieve U) (V : vertexGene) (VV : sieveFunctor V)
   (ff : forall G, 'preSieve( G ~> U | UU ) -> 'Sieve( G ~> V | VV) ) :
   transf (genSieve UU) VV .
Proof. unshelve eexists. unshelve eexists.
- (* -> *) intros u. exact ( (_inner_sumSieve u) o>functor_ (ff _ (_outer_sumSieve u)) ).  
- (* Proper *) abstract(move; move => u1 u2 [inner_u Heq]; cbn_transf; rewrite -> Heq; reflexivity).
- (* typeOf_natural_transf *) abstract(intros H H' h u; cbn_sieve; rewrite -> _functorialCompos_functor'; reflexivity).
Defined.

Definition preSieveTransf_of_transf (U : vertexGene) (UU : preSieve U) (V : vertexGene) (VV : sieveFunctor V)
(ff : transf (genSieve UU) VV ) := (fun G (outer: 'preSieve( G ~> U | UU )) =>
((preSieveTransf_unit outer) :>transf_ ff) ).

Lemma transf_of_preSieveTransf_surj (U : vertexGene) (UU : preSieve U) (V : vertexGene) (VV : sieveFunctor V)
(ff : transf (genSieve UU) VV ) :
forall  G (outer: 'Sieve( G ~> U | (genSieve UU) )),
outer :>transf_ ff == outer :>transf_ transf_of_preSieveTransf (preSieveTransf_of_transf ff) . 
Proof.  intros . unfold preSieveTransf_of_transf. cbn_sieve.
  rewrite -> _natural_transf. apply: _congr_relTransf.  split. cbn_sieve. apply: identGene_composGene.
Qed.

Definition typeOf_commute_presieveTransfArrow
  (U : vertexGene) (UU : preSieve U) (V : vertexGene) (VV : sieveFunctor V)  (uv : 'Gene( U ~> V)) 
   (ff : forall G, 'preSieve( G ~> U | UU ) -> 'Sieve( G ~> V | VV) ) : Type :=
  forall (H : vertexGene)  (u : 'preSieve( H ~> U | UU )),
   (ff _ u ) :>sieve_  ==  (u :>preSieve_) o>functor_[functor_ViewOb _] uv .

Record presieveTransfArrow 
(U : vertexGene) (UU : preSieve U) (V : vertexGene) (VV : sieveFunctor V)  (uv : 'Gene( U ~> V))  : Type :=
  { _transf_presieveTransfArrow :> forall G, 'preSieve( G ~> U | UU ) -> 'Sieve( G ~> V | VV);
    _commute_presieveTransfArrow : typeOf_commute_presieveTransfArrow uv _transf_presieveTransfArrow} .

Definition typeOf_commute_sieveTransfArrow
(G1 : vertexGene) (V1: sieveFunctor G1) (G2 : vertexGene) (V2: sieveFunctor G2)
(g12 : 'Gene( G1 ~> G2))  (vv : transf V1 V2)  : Type :=
  forall (H : vertexGene)  (v : 'Sieve( H ~> G1 | V1 )),
  (v :>transf_ vv) :>sieve_ ==  (v :>sieve_)  o>functor_[functor_ViewOb _] g12.

Record sieveTransfArrow (G1 : vertexGene) (V1: sieveFunctor G1) (G2 : vertexGene) (V2: sieveFunctor G2)
(g12 : 'Gene( G1 ~> G2)) : Type :=
  { _transf_sieveTransfArrow :> transf V1 V2 ;
    _commute_sieveTransfArrow : typeOf_commute_sieveTransfArrow g12 _transf_sieveTransfArrow} .

Definition sieveTransfArrow_of_preSieveTransf 
(U : vertexGene) (UU : preSieve U)  (V : vertexGene) (VV : sieveFunctor V)  (uv : 'Gene( U ~> V)) 
(ff : presieveTransfArrow UU VV uv)  : sieveTransfArrow (genSieve UU) VV uv.
Proof. exists (transf_of_preSieveTransf ff).
abstract(move; intros; cbn_sieve; rewrite <- _functorialCompos_functor', <- _natural_transf; 
rewrite -> _commute_presieveTransfArrow; reflexivity).
Defined.

Definition preSieveTransf_of_sieveTransfArrow 
(U : vertexGene) (UU : preSieve U)  (V : vertexGene) (VV : sieveFunctor V)  (uv : 'Gene( U ~> V)) 
(ff : sieveTransfArrow (genSieve UU) VV uv)  : presieveTransfArrow UU VV uv.
Proof. exists (preSieveTransf_of_transf ff).
abstract(move; intros; unfold preSieveTransf_of_transf;
rewrite -> _commute_sieveTransfArrow;  cbn_sieve; rewrite -> _functorialIdent_functor; reflexivity).
Defined.

Definition sieveTransfArrow_Compos :
forall U U' U'' F F'' F' (u_ : 'Gene( U'' ~> U')) (ff_ : sieveTransfArrow F'' F' u_) 
(u' : 'Gene( U' ~> U)) (ff' : sieveTransfArrow F' F u'),
sieveTransfArrow F'' F (u_ o>gene u').
Proof.  intros. unshelve eexists.
- exact: (transf_Compos ff_ ff').
- abstract(move; intros; cbn_transf; do 2 rewrite -> _commute_sieveTransfArrow;
  rewrite <- _functorialCompos_functor'; reflexivity). 
Defined.

End genSieve.

Definition sumSieve_projOuter :
forall (U : vertexGene) (UU : preSieve U) 
(VV_ : forall (H: vertexGene) (outer_: 'preSieve( H ~> U | UU )), sieveFunctor H),
 sieveTransf (sumSieve VV_) (genSieve UU).
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros wv. eexists. exact (_outer_sumSieve wv). exact (_inner_sumSieve wv :>sieve_).
  + (* _congr_relTransf *) abstract(move;  intros wv1 wv2 [ inner_wv2  Heq_inner_wv2];
  cbn_transf; split;cbn_transf; rewrite -> Heq_inner_wv2; reflexivity). 
- (* _natural_transf *) abstract(move; intros; cbn_sieve; split; cbn_sieve; rewrite  -> _natural_transf; reflexivity ).  
- (* _commute_sieveTransf *) abstract(move; intros; simpl; reflexivity).
Defined.

Definition sumSieve_sectionPull :
forall (U : vertexGene) (UU : preSieve U) 
(VV_ : forall (H: vertexGene) (outer_: 'preSieve( H ~> U | UU )), sieveFunctor H)
(H: vertexGene)
(u: 'preSieve( H ~> _ | UU )),
 sieveTransf (VV_ H u)
  (pullSieve (sumSieve VV_) (u:>preSieve_)) .
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros v.  unshelve eexists.
    * (* _factor_interSieve *)exact: ((v :>sieve_) ). 
      (* _whole_interSieve *) unshelve eexists.
    * (* _object_sumSieve *) exact: H.
    * (* _outer_sumSieve *) exact: u.
    * (* _inner_sumSieve *) exact: v.
    * (* _wholeProp_interSieve *) abstract(simpl; reflexivity).
  + (* _congr_relTransf *) abstract(move;  intros v1 v2 Heq_v; split; autounfold; simpl;
  first (rewrite -> Heq_v; reflexivity); split; autounfold; simpl;
  rewrite -> Heq_v; reflexivity).
- (* _natural_transf *) abstract(move; intros;  split; cbn_transf; last reflexivity;
cbn_sieve; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; simpl; reflexivity).
Defined.

Definition sumSieve_section:
forall (U : vertexGene) (UU : preSieve U) 
(VV_ : forall (H: vertexGene) (outer_: 'preSieve( H ~> U | UU )), sieveFunctor H)
(H: vertexGene)
(u: 'preSieve( H ~> _ | UU )),
 transf (VV_ H u)  (sumSieve VV_) .
Proof. intros. exact: (transf_Compos (sumSieve_sectionPull _ _) (pullSieve_projWhole _ _) ).
Defined.

End sumSieve.

Section sumPreSieve.

Section Section1.
Variables (G : vertexGene) (VV : preSieve G).

Record typeOf_outer_sumPreSieve :=
  { _object_typeOf_outer_sumPreSieve :> vertexGene ; 
    _arrow_typeOf_outer_sumPreSieve :> 'preSieve( _object_typeOf_outer_sumPreSieve ~> G | VV ) }.

(* higher/congruent structure is possible... *)
Variables (WP_ : forall (object_: vertexGene) (outer_: 'preSieve( object_ ~> G | VV )),
 preSieve object_).
 

Record type_sumPreSieve H :=
  { _object_sumPreSieve : vertexGene ;
    _outer_sumPreSieve : 'preSieve( _object_sumPreSieve ~> G | VV ) ; 
    _inner_sumPreSieve : 'preSieve( H ~> _ | WP_ _outer_sumPreSieve ) }.

Inductive rel_sumPreSieve H  (wv : type_sumPreSieve H) : type_sumPreSieve H  -> Type :=
| Rel_sumPreSieve : forall 
  (inner': (WP_  (_outer_sumPreSieve wv)) H),
  inner' :>preSieve_  == (_inner_sumPreSieve wv) :>preSieve_ ->
  rel_sumPreSieve wv
  {| _object_sumPreSieve := _ ;
  _outer_sumPreSieve := _ ; 
  _inner_sumPreSieve := inner' |}.

Instance rel_sumPreSieve_Equivalence H : Equivalence (@rel_sumPreSieve H).
abstract(unshelve eexists;
      [ (intros [object_wv outer_wv inner_wv]; constructor; reflexivity)
      | (* intros wv1 wv2 []. *) (intros [object_wv1 outer_wv1 inner_wv1] [object_wv2 outer_wv2 inner_wv2] [];
       constructor; symmetry; assumption)
      | (intros wv1 wv2 wv3 Heq12 Heq23; destruct Heq23 as [ inner3  Heq23'];
      destruct Heq12 as [ inner2  Heq12']; simpl; constructor; simpl;
       rewrite -> Heq23'; simpl; rewrite -> Heq12'; simpl; reflexivity)]).
Qed.

(* TODO: sumPreSieve_projOuter : sumPreSieve -> UU  *)
Definition sumPreSieve : preSieve G.
Proof. 
unshelve eexists.
  - (* typeOf_objects_functor *) intros H.
    +  exact (type_sumPreSieve H).
  - (* typeOf_arrows_transf *) intros H.
    + (* -> *) simpl; intros wv. exact: ((_inner_sumPreSieve wv :>preSieve_) o>functor_ (_outer_sumPreSieve wv :>preSieve_)). 
Defined.

Definition sumPreSieve_projOuter : presieveTransfArrow (sumPreSieve)  (genSieve VV) (identGene). 
Proof.  unshelve eexists.
  -  intros H uv. exists _ (_outer_sumPreSieve uv). exact ((_inner_sumPreSieve uv) :>preSieve_).
  - abstract(move; intros; cbn_sieve; rewrite <- _functorialCompos_functor';
    apply: _congr_relFunctor; first reflexivity; symmetry; exact: identGene_composGene).
Defined.

End Section1.

End sumPreSieve.

Section sumPullSieve.

Section Section1.
Variables (G : vertexGene) (VV : preSieve G).

(*  *)
Variables (famVertex_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
  vertexGene).

Variables (famArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
 'Gene( object ~> famVertex_  outer )).

Variables (famSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
 sieveFunctor (famVertex_  outer)).

Variables (famInterPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
 preSieve object).

Definition sumPullSieve := @sumSieve G  VV (fun object outer => interSieve (famSieve_ outer) (famArrow_ outer) (genSieve (famInterPreSieve_ outer)) ).

Definition sumPullSieve_projSumPreSieve :
 sieveTransf sumPullSieve (genSieve (sumPreSieve famInterPreSieve_)).
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros wv. eexists.
    * { unshelve eexists; cycle 1. exact (_outer_sumSieve wv). exact (_outer_sumSieve (_factor_interSieve (_inner_sumSieve wv))). }
    simpl. exact (_inner_sumSieve (_factor_interSieve (_inner_sumSieve wv))).
  + (* _congr_relTransf *) abstract (move;  intros wv1 wv2  [ inner_wv2  [[outer_factor_inner_wv2 Heq_inner_factor_inner_wv2_] Heq_whole_inner_wv2]];
  cbn_transf; split; cbn_transf; rewrite -> Heq_inner_factor_inner_wv2_; reflexivity).
- (* _natural_transf *) abstract(move; intros; cbn_sieve; split; cbn_sieve; reflexivity). 
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; rewrite -> _functorialCompos_functor'; reflexivity).
Defined.

End Section1. 
End sumPullSieve.

Definition typeOf_commute_preSieveTransf
(G : vertexGene) (V1 V2 : preSieve G) (vv : forall G : vertexGene, V1 G -> V2 G)  : Type :=
  forall (H : vertexGene)  (v : 'preSieve( H ~> G | V1 )),
   (vv _ v ) :>preSieve_   ==  v :>preSieve_ .

Record preSieveTransf G (V1 V2 : preSieve G) : Type :=
  { _transf_preSieveTransf :> forall G : vertexGene, V1 G -> V2 G ;
    _commute_preSieveTransf : typeOf_commute_preSieveTransf _transf_preSieveTransf} .

Notation "f :>preSieveTransf_ ee" := (@_transf_preSieveTransf _ _ _ ee _ f)
  (at level 40, ee at next level) : poly_scope.

Lemma sumSieve_congrTransf (G : vertexGene) (UU1  : preSieve G)
G' ( UU2 : preSieve G')
(uu : forall G : vertexGene, UU1 G -> UU2 G)
(VV1_ : forall H : vertexGene, 'preSieve( H ~> _ | UU1 ) -> sieveFunctor H)
(VV2_ : forall H : vertexGene, 'preSieve( H ~> _ | UU2 ) -> sieveFunctor H)
(vv_ : forall (H: vertexGene) (u1: 'preSieve( H ~> _ | UU1 )),
 sieveTransf  (VV1_ _ u1) (VV2_ _ (uu _ u1 ))) :
transf  (sumSieve VV1_ ) (sumSieve VV2_).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros K. unshelve eexists.
  (* _fun_relTransf *) intros vu. unshelve eexists. 
  (* _object_sumSieve *) exact: (_object_sumSieve vu). 
  (* _outer_sumSieve *) exact: (uu _ (_outer_sumSieve vu ) ).
  (* _inner_sumSieve *) exact: (_inner_sumSieve vu :>transf_ (vv_ _ _)).
  (* _congr_relTransf  *) abstract(move; intros vu1 vu2 [ inner_vu2  Heq_inner_vu2];
  simpl; constructor; simpl; rewrite -> Heq_inner_vu2; reflexivity).
- (*  _natural_transf  *) abstract(intros K K' k vvu; cbn_sieve;
  constructor; simpl;  rewrite -> _natural_transf; reflexivity).
Defined.

Lemma sumSieve_congr (G : vertexGene) (UU1 UU2 : preSieve G)
(uu : preSieveTransf UU1 UU2)
(VV1_ : forall H : vertexGene, 'preSieve( H ~> _ | UU1 ) -> sieveFunctor H)
(VV2_ : forall H : vertexGene, 'preSieve( H ~> _ | UU2 ) -> sieveFunctor H)
(vv_ : forall (H: vertexGene) (u1: 'preSieve( H ~> _ | UU1 )),
sieveTransf  (VV1_ _ u1) (VV2_ _ (uu _ u1))) :
sieveTransf  (sumSieve VV1_ ) (sumSieve VV2_).
Proof. unshelve eexists. (* _transf_sieveTransf *) exact: sumSieve_congrTransf.
(* _commute_sieveTransf *) abstract(intros K vu; simpl; rewrite -> _commute_sieveTransf;  rewrite -> _commute_preSieveTransf; reflexivity).
Defined.

Definition identSieve_sieveTransf_identPreSieve (G: vertexGene) : sieveTransf (identSieve G) (genSieve (identPreSieve G)).
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros v. { unshelve eexists. 2: simpl. 2: case: eqP. 2: intros; exact mytt. 3:(exact: v).
  abstract(move => [];  reflexivity). 
     (* unshelve eexists. 2: simpl. 2: case: eqP. (@eqP _ G G).  last (exact: v);
     simpl. case: (@eqP _ G G); first (intros; exact tt); last abstract(move => [];  reflexivity).  *)}
  + (* _congr_relTransf *) abstract(move; intros v1 v2 Heq;
      cbn_transf; split; cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *) abstract(move; intros; cbn_sieve; split; cbn_sieve; reflexivity). 
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; case: eqP; first (simpl; intros ; rewrite (eq_axiomK p); apply: identGene_composGene);
     last (move => []; reflexivity)).
Defined.


Definition typeOf_basePreSieve (U : vertexGene) (UU : preSieve U) :=
  forall (H : vertexGene) (u u' : 'preSieve( H ~> _ | UU )), u :>preSieve_ == u' :>preSieve_  -> u = u'.  

Parameter basePreSieve : forall (U : vertexGene) (UU : preSieve U) 
  (UU_base : typeOf_basePreSieve UU) , Type.

Inductive isCover : forall (U : vertexGene) (UU_pre : preSieve U) (UU : sieveFunctor U), sieveTransf UU (genSieve UU_pre)  -> Type :=

| BasePreSieve_isCover : forall (U : vertexGene) (UU : preSieve U) (UU_base : typeOf_basePreSieve UU),
    basePreSieve UU_base -> @isCover _ UU (genSieve UU) (sieveTransf_Ident _)

| IdentSieve_isCover : forall (G : vertexGene),
 @isCover _ (identPreSieve G)  (identSieve G) (identSieve_sieveTransf_identPreSieve G)
  
 | InterSieve_isCover : forall (G : vertexGene) (VV_pre : preSieve G) (VV : sieveFunctor G) (VV_transf : sieveTransf VV (genSieve VV_pre))
    (G' : vertexGene) (g : 'Gene( G' ~> G ))  (UU_pre : preSieve G') (UU : sieveFunctor G') (UU_transf : sieveTransf UU (genSieve UU_pre)),
     @isCover  _ VV_pre VV VV_transf -> @isCover  _ UU_pre UU UU_transf ->  @isCover _ UU_pre (interSieve VV g UU) (sieveTransf_Compos (interSieve_projFactor _ _ _) UU_transf)

| SumSieve_isCover : forall (G : vertexGene) (VV : preSieve G) (VV_base : typeOf_basePreSieve VV)
(VV_base_cover : basePreSieve VV_base),
forall (famVertex_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
  vertexGene)
  (famPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
 preSieve (famVertex_  object outer))
 (famSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
 sieveFunctor (famVertex_  object outer))
 (famSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
    sieveTransf (famSieve_  object outer) (genSieve (famPreSieve_  object outer)))
(famIsCover_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )), 
    @isCover _ (famPreSieve_ object outer) (famSieve_ object outer) (famSieveTransf_ object outer))

 (famPullArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
   'Gene( object ~> famVertex_  object outer ))
 (famPullPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
      preSieve object)
  (famPullPreSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> G | VV )),
      sieveTransfArrow (genSieve (famPullPreSieve_ object outer)) (genSieve (famPreSieve_ object outer)) (famPullArrow_ object outer)),

  @isCover _ (sumPreSieve famPullPreSieve_) (sumPullSieve famPullArrow_ famSieve_ famPullPreSieve_) 
    (sumPullSieve_projSumPreSieve famPullArrow_ famSieve_ famPullPreSieve_).


Section nerveSieve.

Variables (topPreSieveVertexes: vertexGene) (topPreSieve: preSieve topPreSieveVertexes) (structCoSheaf: typeOf_objects_functor). 

Inductive nerveSieve: forall (U : vertexGene) (UU_pre : (preSieve U)) (UU : sieveFunctor U) (UU_transf: sieveTransf UU (genSieve UU_pre)) (UU_isCover : isCover UU_transf),
forall (u_arrowTop : 'Gene( U ~> topPreSieveVertexes)) (UU_transfTop : presieveTransfArrow UU_pre (genSieve topPreSieve) u_arrowTop), 
forall (G : vertexGene) (g_sense : 'Gene( G ~> U)),
forall (dim: nat) (diffPreSieveVertexes: 'I_(dim) ->  vertexGene )
       (diffPreSieve: forall i : 'I_(dim), 'preSieve( (diffPreSieveVertexes i) ~> _ | topPreSieve )), Type :=

| NerveSieve_Diff  (* at cell dim +1 , at coeffiecients degree +1 *) :
forall (U : vertexGene) (UU_pre : (preSieve U)) (UU_pre_base : typeOf_basePreSieve UU_pre) (UU_pre_cover : basePreSieve UU_pre_base),

forall (u_arrowTop : 'Gene( U ~> topPreSieveVertexes)) (UU_transfTop : presieveTransfArrow UU_pre (genSieve topPreSieve) u_arrowTop),

forall (famVertex_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), vertexGene) 
(famPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), preSieve (famVertex_ object outer))
(famSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), sieveFunctor (famVertex_ object outer))
(famSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
    sieveTransf (famSieve_  object outer) (genSieve (famPreSieve_  object outer)))
(famIsCover_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
    isCover (famSieveTransf_  object outer))

(famTopArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 'Gene( (famVertex_ object outer) ~> topPreSieveVertexes ) )
(famTransfTop_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), presieveTransfArrow (famPreSieve_ object outer) (genSieve topPreSieve) (famTopArrow_ object outer))

(famPullArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 'Gene( object ~> famVertex_ object outer ))
(famPullPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
      preSieve object)
(famPullPreSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
      sieveTransfArrow (genSieve (famPullPreSieve_ object outer)) (genSieve (famPreSieve_ object outer)) (famPullArrow_ object outer))
(famHeqArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 
   (*  (outer :>sieve_)  o>functor_[functor_ViewOb _]  u_arrowTop :=: *)  (UU_transfTop _ outer) :>sieve_
  == (famPullArrow_ object outer) o>functor_[functor_ViewOb _] (famTopArrow_ object outer) ),

forall (G : vertexGene) (g_sense : 'Gene( G ~> U)),
forall (dim: nat) (object: 'I_(S dim) -> vertexGene),
forall (outer: forall i : 'I_(S dim), 'preSieve( object i ~> U | UU_pre )),
forall (inner: forall i : 'I_(S dim), 
               'Sieve( G ~> _ | interSieve (famSieve_ (object i) (outer i)) (famPullArrow_ (object i) (outer i))
                                           (genSieve (famPullPreSieve_ (object i) (outer i))) ) ), 
forall (inner_nerveSieve: forall i : 'I_(S dim), 
  nerveSieve (famIsCover_ (object i) (outer i))
     (famTransfTop_ (object i) (outer i))
(*      ((_outer_sumSieve (((inner i) :>transf_ (interSieve_projWhole _ _ _)) :>transf_ (famSieveTransf_ (object i) (outer i)) )) :>preSieve_ ) *)
     ((_outer_sumSieve ( (famPullPreSieveTransf_ (object i) (outer i)) _ ((inner i) :>transf_ (interSieve_projFactor _ _ _))  )) :>preSieve_ )
     (fun j : 'I_(dim) => _outer_sumSieve (UU_transfTop _ (outer (lift i j))))),
forall (inner_senseCompat : forall i : 'I_(S dim), ((inner i) :>sieve_) o>functor_[functor_ViewOb _] ((outer i) :>preSieve_) == g_sense ),

forall (G_weight : structCoSheaf G),

nerveSieve (SumSieve_isCover UU_pre_cover famIsCover_ famPullPreSieveTransf_)
  (preSieveTransf_of_sieveTransfArrow (sieveTransfArrow_Compos (sieveTransfArrow_of_preSieveTransf (sumPreSieve_projOuter famPullPreSieve_)) 
        (sieveTransfArrow_of_preSieveTransf UU_transfTop)))  g_sense
   (fun i : 'I_(S dim) => _outer_sumSieve (UU_transfTop _ (outer i)))

| NerveSieve_Gluing (* at same cell dim >= 0, at coefficients degree +1 *) :
forall (U : vertexGene) (UU_pre : (preSieve U)) (UU_pre_base : typeOf_basePreSieve UU_pre) (UU_pre_cover : basePreSieve UU_pre_base),

forall (u_arrowTop : 'Gene( U ~> topPreSieveVertexes)) (UU_transfTop : presieveTransfArrow UU_pre (genSieve topPreSieve) u_arrowTop),

forall (famVertex_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), vertexGene) 
(famPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), preSieve (famVertex_ object outer))
(famSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), sieveFunctor (famVertex_ object outer))
(famSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
    sieveTransf (famSieve_  object outer) (genSieve (famPreSieve_  object outer)))
(famIsCover_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
    isCover (famSieveTransf_  object outer))

(famTopArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 'Gene( (famVertex_ object outer) ~> topPreSieveVertexes ) )
(famTransfTop_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), presieveTransfArrow (famPreSieve_ object outer) (genSieve topPreSieve) (famTopArrow_ object outer))

(famPullArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 'Gene( object ~> famVertex_ object outer ))
(famPullPreSieve_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
      preSieve object)
(famPullPreSieveTransf_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
      sieveTransfArrow (genSieve (famPullPreSieve_ object outer)) (genSieve (famPreSieve_ object outer)) (famPullArrow_ object outer))
(famHeqArrow_ : forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )), 
   (*  (outer :>sieve_)  o>functor_[functor_ViewOb _]  u_arrowTop :=: *)  (UU_transfTop _ outer) :>sieve_
  == (famPullArrow_ object outer) o>functor_[functor_ViewOb _] (famTopArrow_ object outer) ),

forall (G : vertexGene) (g_sense : 'Gene( G ~> U)),
forall (dim: nat) (diffPreSieveVertexes: 'I_(dim) ->  vertexGene )
       (diffPreSieve: forall i : 'I_(dim), topPreSieve (diffPreSieveVertexes i)),

forall (fam_nerveSieve: forall (object: vertexGene) (outer: 'preSieve( object ~> U | UU_pre )),
      nerveSieve (famIsCover_ object outer)
      (famTransfTop_ object outer) 
      (famPullArrow_ object outer) 
      diffPreSieve),

forall (G_weight : structCoSheaf G),

nerveSieve (SumSieve_isCover UU_pre_cover famIsCover_ famPullPreSieveTransf_)
(preSieveTransf_of_sieveTransfArrow (sieveTransfArrow_Compos (sieveTransfArrow_of_preSieveTransf (sumPreSieve_projOuter famPullPreSieve_)) 
      (sieveTransfArrow_of_preSieveTransf UU_transfTop)))  g_sense diffPreSieve
      
| NerveSieve_Base (* at cell dim = 0, at coeffiecients degree = 0 *) : 
forall (U : vertexGene) (UU_pre : preSieve U) (UU_pre_base : typeOf_basePreSieve UU_pre) (UU_pre_isBase: basePreSieve UU_pre_base ),
forall (u_arrowTop : 'Gene( U ~> topPreSieveVertexes)) (UU_transfTop : presieveTransfArrow UU_pre (genSieve topPreSieve) u_arrowTop), 
forall (G : vertexGene) (g_sense : 'preSieve( G ~> _ | UU_pre)),
nerveSieve (BasePreSieve_isCover UU_pre_isBase)  UU_transfTop (g_sense :>preSieve_ ) 
 (fun i : 'I_0 => (ffun0 (card_ord 0) : forall i : 'I_(0), 'preSieve( ((ffun0 (card_ord 0)) i) ~> _ | topPreSieve )) i).
 
End nerveSieve.
End COMOD.
End NERVE.

Reset Initial.
(** # #
#+TITLE: cartierSolution0.v

Proph

https://github.com/1337777/cartier/blob/master/cartierSolution0.v

Grammatical sheaf cohomology, its MODOS proof-assistant and WorkSchool 365 market for learning reviewers

The “double plus” definition of sheafification says that not-only the outer families-of-families are modulo the germ-equality, but-also the inner families are modulo the germ-equality. This outer-inner contrast is the hint that the “double plus” should be some inductive construction... that grammatical sheaf cohomology exists!
    And the MODOS proof-assistant implements the cut-elimination confluence of this inductive construction where the decreasing measure of families-gluing is the restricting covering: | Gluing : (forall (G : Site) (v : Site( G → V | in sieveV )), PreSheaves(Restrict F (sievesW_ v) → Sheafified E)) ⊢ PreSheaves(Restrict F (Sum sievesV_ over sieveU) → Sheafified E). And the separateness-property is expressed via the congruence-conversions clauses. Then the generalization to cohomology beyond 0th (sheaf) is that the grammatical sieves could be programmed such to inductively store the (possibly incompatible) data along with its gluing-differentials: Any list of (semantically-equal) arrows in the grammatical sieve now stores both data (on the singleton lists) and differentials (on the exhaustive ordered listings), and the (inductive) differentials of the outer-gluing of inner-gluings correctly-compute the differentials of the total/sum gluing because ∂∂ = 0… Moreover, the generating topological site has its own cut-elimination confluence of arrow-terms, each arrow-term is covered by its arrow-subterms, and the algebra-operation of composition ⟦f⟧*⟦B⟧*⟦g⟧ → ⟦f ∘_B g⟧ is indeed geometric, is some sheaf condition. Possible applications are the constructive connecting-snake lemma for additive sheaves, or the constructive dependent homotopy types or the constructive geometry of quantum fields in physics.
    This research is the fusion of prompts from two expert mathematicians: Kosta Dosen and Pierre Cartier. But should this research be immediately-conclusive and peer-reviewed only by experts in some publishing-market susceptible under falsifications/intoxications? And what sense is peer review of already-computer-verified mathematics? WorkSchool 365 is Your Market for Learning Reviewers. WorkSchool 365 is your education marketplace where the prompting authors pay to get peer reviews of their documents from any learning reviewers who pass the test quiz inside the prompting document, with shareable transcripts receipts of the school work. WorkSchool 365 documents are Word templates with business-logic automation and playable Coq scripts. WorkSchool 365 is free open-source code Microsoft Teams app in the web browser with authentication via only no-password email. Enroll today! WorkSchool365.com

| Constructing : (G : Site); (u : Site( G ~> U | in sieveU ));
 			(f : F G); (_ : isGene f)
⊢   Element( G ~> Restrict F sieveU )

| UnitSheafified : (G : Site); (u : Site( G ~> U | in sieveU ));
 		(e : Element( G ~> E )); (ut : Site( U ~> T | in sieveT ))
⊢   Element( G ~> Sheafified (Restrict E sieveT) )

| RestrictCast :
(ut : Site( U ~> T | in sieveT ))
⊢   PreSheaves( Restrict E sieveU ~> Restrict E sieveT )

| SheafifiedMor : 
	PreSheaves( F ~> E )
⊢   PreSheaves( Sheafified F ~> Sheafified E )

| Destructing : (forall (G : Site) (u : Site( G ~> U | in sieveU ))
    (f : F G) (_ : isGene f), Element( G ~> E )); (ut : Site( U ~> T | in sieveT ))
⊢   PreSheaves( Restrict F sieveU ~> Sheafified (Restrict E sieveT) )

| Gluing : (forall (G : Site) (u : Site( G ~> U | in sieveU )), 
			PreSheaves( Restrict F (sievesV_ u) ~> Sheafified E ))
⊢   PreSheaves( Restrict F (sum sievesV_ over sieveU) ~> Sheafified E )

Lemma: cut-elimination holds. Corollary: grammatical sheaf cohomology exists.

And to express fibred morphisms, the shape of the point is now any “A” instead of the singleton, and the context-extension is polymorph…
for (B over Delta) and for variable (Theta), then
Span(Theta ~> (Delta;B))  :<=>  Hom( (x: Gamma; a: A( h(x) )) ~> B( f(x) ) ) with some (f: Gamma -> Delta) and (h: Gamma -> Theta) and (A over Theta)

OUTLINE ::

* Module SHEAF. General sieves

* Module EARLIER_PRELIM_SHEAF. Singleton sieves.

-----

#+BEGIN_SRC coq :exports both :results silent # # **)
From Coq Require Import RelationClasses Setoid SetoidClass
     Classes.Morphisms_Prop RelationPairs CRelationClasses CMorphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat fintype. 
From Coq Require Lia.

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.
Set Primitive Projections. Set Universe Polymorphism.

Module SHEAF.

Close Scope bool. Declare Scope poly_scope. Delimit Scope poly_scope with poly. Open Scope poly.

Module Type GENE.

Class relType : Type := RelType
{ _type_relType : Type;
  _rel_relType : crelation _type_relType;
  _equiv_relType :> Equivalence _rel_relType }.
About relType.
Coercion _type_relType : relType >-> Sortclass.

Definition equiv {A: Type} {R: crelation A} `{Equivalence A R} : crelation A := R.

 (* TODO: keep or comment *)
Arguments _rel_relType : simpl never.
Arguments _equiv_relType : simpl never.
Arguments equiv : simpl never.

Notation " x == y " := (@equiv (* (@_type_relType _) *) _ (@_rel_relType _)  (@_equiv_relType _) x y) 
  (at level 70, no associativity) : type_scope.
Notation LHS := (_ : fun XX => XX == _).
Notation RHS := (_ : fun XX => _ == XX).
Notation "[|  x  ; .==. |]" := (exist (fun t => (_ == _)) x _) (at level 10, x at next level) : poly_scope.
Notation "[|  x  ; .=. |]" := (exist (fun t => (_ = _)) x _) (at level 10, x at next level) : poly_scope.

Parameter vertexGene : Type.

Parameter arrowGene : vertexGene -> vertexGene -> relType.
Notation "''Gene' ( V ~> U )" := (@arrowGene U V)
(at level 0, format "''Gene' (  V  ~>  U  )") : poly_scope.

Parameter composGene :
forall U, forall V W, 'Gene( W ~> V ) -> 'Gene( V ~> U ) -> 'Gene( W ~> U ).
Notation "wv o:>gene vu" := (@composGene _ _ _ wv vu)
(at level 40, vu at next level) : poly_scope.

Declare Instance composGene_Proper: forall U V W, Proper (equiv ==> equiv ==> equiv) (@composGene U V W).

Parameter identGene : forall {U : vertexGene}, 'Gene( U ~> U ).

Parameter composGene_compos :
forall (U V : vertexGene) (vu : 'Gene( V ~> U ))
        (W : vertexGene) (wv : 'Gene( W ~> V )),
forall X (xw : 'Gene( X ~> W )),
  xw o:>gene ( wv o:>gene vu ) == ( xw o:>gene wv ) o:>gene vu.
Parameter composGene_identGene :
forall (U V : vertexGene) (vu : 'Gene( V ~> U )),
  (@identGene V) o:>gene vu == vu .
Parameter identGene_composGene :
forall (U : vertexGene), forall (W : vertexGene) (wv : 'Gene( W ~> U )),
  wv o:>gene (@identGene U) == wv.

Notation typeOf_objects_functor := (vertexGene -> relType).

Class relFunctor (F : typeOf_objects_functor) (G G' : vertexGene)  : Type := RelFunctor
{ _fun_relFunctor : 'Gene( G' ~> G ) -> F G -> F G' ;
  _congr_relFunctor :> Proper (equiv ==> @equiv _ _ (@_equiv_relType ( F G )) 
                         ==> @equiv _ _ (@_equiv_relType ( F G'))) _fun_relFunctor ; }.

Coercion _fun_relFunctor : relFunctor >-> Funclass.

Definition typeOf_arrows_functor (F : typeOf_objects_functor)
:= forall G G' : vertexGene, relFunctor F G G' .

Definition fun_arrows_functor_ViewOb := composGene.

Notation "wv o>gene vu" := (@fun_arrows_functor_ViewOb _ _ _ wv vu)
(at level 40, vu at next level) : poly_scope.

Definition fun_transf_ViewObMor (G H: vertexGene) (g: 'Gene( H ~> G )) (H': vertexGene) :
'Gene(H' ~> H) -> 'Gene(H' ~> G) .
Proof. exact: ( fun h =>  h o:>gene g ). Defined.

(* TODO: REDO GENERAL fun_transf_ViewObMor_Proper *)
Global Instance fun_transf_ViewObMor_Proper G H g H' : Proper (equiv ==> equiv) (@fun_transf_ViewObMor G H g H').
Proof.    move. intros ? ? Heq. unfold fun_transf_ViewObMor. rewrite -> Heq; reflexivity.
Qed.

Notation "wv :>gene vu" := (@fun_transf_ViewObMor _ _ vu _ wv)
(at level 40, vu at next level) : poly_scope.

Definition typeOf_functorialCompos_functor (F : typeOf_objects_functor)
 (F_ : typeOf_arrows_functor F)  :=
  forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
    F_ _ _ g' (F_ _ _ g f) == 
    F_ _ _ ( g' o>gene g (*? or  g' :>gene g  or  g' o:>gene g ?*) ) f.

Definition typeOf_functorialIdent_functor (F : typeOf_objects_functor)
 (F_ : typeOf_arrows_functor F) :=
  forall G (f : F G), F_ _ _ (@identGene G) f == f.

Record functor := Functor 
 { _objects_functor :> typeOf_objects_functor ;
   _arrows_functor :> (* :> ??? *) typeOf_arrows_functor _objects_functor;
   _functorialCompos_functor : typeOf_functorialCompos_functor _arrows_functor;
   _functorialIdent_functor : typeOf_functorialIdent_functor _arrows_functor;
 }.

Notation "g o>functor_ [ F ] f" := (@_arrows_functor F _ _ g f)
  (at level 40, f at next level) : poly_scope.
Notation "g o>functor_ f" := (@_arrows_functor _ _ _ g f)
  (at level 40, f at next level) : poly_scope.

Definition equiv_rel_functor_ViewOb (G H : vertexGene) : crelation 'Gene( H ~> G ).
Proof.    exact: equiv.
Defined.
(* (* no lack for now, unless want uniformity of the (opaque) witness... *)
Arguments equiv_rel_functor_ViewOb /.
 *)

Definition functor_ViewOb (G : vertexGene) : functor.
Proof. unshelve eexists.
- (* typeOf_objects_functor *) intros H. exact: 'Gene( H ~> G ).
- (* typeOf_arrows_functor *) intros H H'. exists (@fun_arrows_functor_ViewOb G H H').
  abstract (typeclasses eauto).
- (* typeOf_functorialCompos_functor *) abstract (move; intros; exact: composGene_compos).
- (* typeOf_functorialIdent_functor *) abstract (move; intros; exact: composGene_identGene).
Defined.

Definition _functorialCompos_functor' {F : functor} :
   forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
   g' o>functor_ [ F ] (g o>functor_ [ F ]  f) 
   == (g' o>functor_ [ functor_ViewOb G ] g) o>functor_ [ F ] f
:= @_functorialCompos_functor F.

Class relTransf (F E : typeOf_objects_functor) (G : vertexGene) : Type := RelTransf
{ _fun_relTransf : F G -> E G ;
  _congr_relTransf :> Proper (@equiv _ _ (@_equiv_relType ( F G )) 
                          ==> @equiv _  _ (@_equiv_relType ( E G))) _fun_relTransf ; }.

Coercion _fun_relTransf : relTransf >-> Funclass.

Notation typeOf_arrows_transf F E
:= (forall G : vertexGene, relTransf F E G) .

Definition typeOf_natural_transf (F E : functor)
 (ee : typeOf_arrows_transf F E) :=
  forall G G' (g : 'Gene( G' ~> G )) (f : F G),
  g o>functor_[E] (ee G f) == ee G' (g o>functor_[F] f).

Record transf (F : functor) (E : functor) := Transf
{ _arrows_transf :> typeOf_arrows_transf F E ;
  _natural_transf : typeOf_natural_transf _arrows_transf;
}.

Notation "f :>transf_ [ G ] ee" := (@_arrows_transf _ _ ee G f)
  (at level 40, ee at next level) : poly_scope.

Notation "f :>transf_ ee" := (@_arrows_transf _ _ ee _ f)
  (at level 40, ee at next level) : poly_scope.

Definition transf_ViewObMor (G : vertexGene) (H : vertexGene) (g : 'Gene( H ~> G )) :
transf (functor_ViewOb H) (functor_ViewOb G).
Proof.  unshelve eexists.
- (* _arrows_transf *)  unshelve eexists.
  + (* _fun_relTransf *) exact: (fun_transf_ViewObMor g).
  + (* _congr_relTransf  *) exact: fun_transf_ViewObMor_Proper.
- (* _natural_transf *)abstract (move; simpl; intros; exact: composGene_compos).
Defined.

Definition _functorialCompos_functor'' {F : functor} :
   forall G G' (g : 'Gene( G' ~> G)) G'' (g' : 'Gene( G'' ~> G')) (f : F G),
   g' o>functor_ [ F ] (g o>functor_ [ F ]  f) 
   == (g' :>transf_ (transf_ViewObMor g)) o>functor_ [ F ] f
:= @_functorialCompos_functor F.
 
Record sieveFunctor (U : vertexGene) : Type := 
  { _functor_sieveFunctor :> functor ;
    _transf_sieveFunctor : transf _functor_sieveFunctor (functor_ViewOb U) ; }.

Lemma transf_sieveFunctor_Proper (U : vertexGene) (UU : sieveFunctor U) H: 
Proper (equiv ==> equiv) (_transf_sieveFunctor UU H).
  apply: _congr_relTransf.
Qed.

Notation "''Sieve' ( G' ~> G | VV )" := (@_functor_sieveFunctor G VV G')
     (at level 0, format "''Sieve' (  G'  ~>  G  |  VV  )") : poly_scope.
Notation "h o>sieve_ v " := (h o>functor_[@_functor_sieveFunctor _ _] v)
          (at level 40, v at next level, format "h  o>sieve_  v") : poly_scope.
Notation "v :>sieve_" := (v :>transf_ (_transf_sieveFunctor _)) (at level 40) : poly_scope.

Global Ltac cbn_ := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor].
Global Ltac cbn_equiv := unfold _rel_relType, equiv; cbn -[ _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor].
Global Ltac cbn_view := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor  _arrows_functor 
                             _arrows_transf  _functor_sieveFunctor _transf_sieveFunctor].
Global Ltac cbn_functor := cbn -[equiv _type_relType _rel_relType _equiv_relType functor_ViewOb
                               _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor].
Global Ltac cbn_transf := cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
                               transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor].
Global Ltac cbn_sieve := cbn -[equiv _type_relType _rel_relType _equiv_relType   functor_ViewOb
                                 transf_ViewObMor ].

Tactic Notation "cbn_" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor] in H.
Tactic Notation "cbn_equiv" "in" hyp_list(H) := unfold _rel_relType, equiv in H; cbn -[ _arrows_functor functor_ViewOb
                             _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor] in H.
Tactic Notation "cbn_view" "in"  hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor  _arrows_functor 
                             _arrows_transf  _functor_sieveFunctor _transf_sieveFunctor] in H.
Tactic Notation "cbn_functor" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType functor_ViewOb
                               _arrows_transf transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor] in H.
Tactic Notation "cbn_transf" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
                               transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor] in H.
Tactic Notation "cbn_sieve" "in" hyp_list(H) := cbn -[equiv _type_relType _rel_relType _equiv_relType   functor_ViewOb
                                 transf_ViewObMor ] in H.

Definition compatEquiv {U : vertexGene} {UU : sieveFunctor U}  {G} : crelation ('Sieve( G ~> _ | UU ))
:= fun u u' : 'Sieve( G ~> _ | UU ) => u :>sieve_ == u' :>sieve_ .
Arguments compatEquiv /.

Definition compatEquiv_Equivalence (U : vertexGene) (UU : sieveFunctor U)  G : Equivalence (@compatEquiv U UU G).
unshelve eexists.
-  abstract(move; intros; move; reflexivity).
-  abstract(move; intros; move; intros; symmetry; assumption).
- abstract(move; intros; move; intros; etransitivity; eassumption).
Qed.

Definition compatRelType (U : vertexGene) (UU : sieveFunctor U)  (G : vertexGene) : relType.
exists ('Sieve( G ~> _ | UU )) compatEquiv.
exact: compatEquiv_Equivalence.
Defined.

Instance compatEquiv_subrelation (U : vertexGene) (UU : sieveFunctor U)  (G : vertexGene) :
subrelation (@equiv _ _ (@_equiv_relType _)) (@compatEquiv U UU G).
move. intros u1 u2 Heq. cbn_. rewrite -> Heq. reflexivity.
Qed.

Notation "u ==s v" := (@equiv (* (@_type_relType (compatRelType _ _)) *) _ 
      (@_rel_relType (compatRelType _ _)) (@_equiv_relType (compatRelType _ _)) u v)
(at level 70, no associativity) : type_scope.

Definition typeOf_baseSieve (U : vertexGene) (UU : sieveFunctor U) :=
  forall (H : vertexGene) (u u' : 'Sieve( H ~> _ | UU )), u ==s u' -> u == u'.  

Parameter baseSieve : forall (U : vertexGene) (UU : sieveFunctor U) 
  (UU_base : typeOf_baseSieve UU), Type.

End GENE.

Module Type COMOD (Gene : GENE).
Import Gene.

Ltac tac_unsimpl := repeat
lazymatch goal with
| [ |- context [@fun_transf_ViewObMor ?G ?H ?g ?H' ?h] ] => 
change (@fun_transf_ViewObMor G H g H' h) with 
(h :>transf_ (transf_ViewObMor g))
| [ |- context [@fun_arrows_functor_ViewOb ?U ?V ?W ?wv ?vu] ] => 
change (@fun_arrows_functor_ViewOb U V W wv vu) with 
(wv o>functor_[functor_ViewOb U] vu)

(* no lack*)
| [ |- context [@equiv_rel_functor_ViewOb ?G ?H ?x ?y] ] =>  
  change (@equiv_rel_functor_ViewOb G H x y) with 
(@equiv _ _ (@_equiv_relType ( (functor_ViewOb G) H )) x y) 
(* | [ |- context [@equiv_rel_arrowSieve ?G ?G' ?g ?H ?x ?y] ] =>  
  change (@equiv_rel_arrowSieve G G' g H x y) with 
(@equiv _ (@_rel_relType ( (arrowSieve g) H )) x y)  *)
end.

Definition transf_Compos :
forall (F F'' F' : functor) (ff_ : transf F'' F') (ff' : transf F' F),
transf F'' F.
Proof.  intros. unshelve eexists.
- intros G. unshelve eexists. intros f. exact:((f :>transf_ ff_) :>transf_ ff').
  abstract(solve_proper).
(*   exists (Basics.compose (ff' G) (ff_ G) ).  abstract(typeclasses eauto). *)
- abstract (move; cbn_; intros; (* unfold Basics.compose; *)
    rewrite -> _natural_transf , _natural_transf; reflexivity).
Defined.

Definition transf_Ident :
forall (F : functor), transf F F.
Proof.  intros. unshelve eexists.
- intros G. exists id. 
  abstract(simpl_relation).
- abstract (move; cbn_; intros; reflexivity).
Defined.

Definition typeOf_commute_sieveTransf
(G : vertexGene) (V1 V2 : sieveFunctor G) (vv : transf V1 V2)  : Type :=
  forall (H : vertexGene)  (v : 'Sieve( H ~> G | V1 )),
  (v :>transf_ vv) :>transf_ (_transf_sieveFunctor V2) ==  v :>sieve_ .

Record sieveTransf G (V1 V2 : sieveFunctor G) : Type :=
  { _transf_sieveTransf :> transf V1 V2 ;
    _commute_sieveTransf : typeOf_commute_sieveTransf _transf_sieveTransf} .

Instance fun_transf_ViewObMor_measure {G H: vertexGene} {g: 'Gene( H ~> G )} {H': vertexGene}:
 @Measure 'Gene(H' ~> H)  'Gene(H' ~> G) (@fun_transf_ViewObMor G H g H') := { }.

Definition sieveTransf_Compos :
forall U (F F'' F' : sieveFunctor U) (ff_ : sieveTransf F'' F') (ff' : sieveTransf F' F),
sieveTransf F'' F.
Proof.  intros. unshelve eexists.
- exact: (transf_Compos ff_ ff').
- abstract(move; intros; cbn_transf; autounfold; do 2 rewrite -> _commute_sieveTransf; reflexivity).
Defined.

Definition sieveTransf_Ident :
forall U (F  : sieveFunctor U) , sieveTransf F F.
Proof.  intros. unshelve eexists.
- exact: (transf_Ident F).
- abstract(move; intros; reflexivity).
Defined.

Definition identSieve (G: vertexGene) : sieveFunctor G.
unshelve eexists.
exact: (functor_ViewOb G).
exact: (transf_Ident (functor_ViewOb G)).
Defined.

Definition sieveTransf_identSieve :
forall U (F  : sieveFunctor U) , sieveTransf F (identSieve U).
Proof.  intros. unshelve eexists.
- exact: (_transf_sieveFunctor F).
- abstract(move; intros; reflexivity).
Defined.
(* TODO MERE WITH sieveTransf_identSieve *)
Lemma sieveTransf_sieveFunctor G (VV : sieveFunctor G) :
sieveTransf VV (identSieve G).
Proof. unshelve eexists. exact: _transf_sieveFunctor.
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Record sieveEquiv G (V1 V2 : sieveFunctor G) : Type :=
  { _sieveTransf_sieveEquiv :> sieveTransf V1 V2 ;
  _revSieveTransf_sieveEquiv : sieveTransf V2 V1 ;
  _injProp_sieveEquiv : forall H v, (v :>transf_[H] _revSieveTransf_sieveEquiv )
                            :>transf_ _sieveTransf_sieveEquiv == v ; 
_surProp_sieveEquiv : forall H v, (v :>transf_[H] _sieveTransf_sieveEquiv )
                            :>transf_ _revSieveTransf_sieveEquiv == v } .

Definition rel_sieveEquiv G : crelation (sieveFunctor G) := fun V1 V2 => sieveEquiv V1 V2.

Instance equiv_sieveEquiv G: Equivalence (@rel_sieveEquiv G ).
unshelve eexists.
- intros V1. unshelve eexists. exact (sieveTransf_Ident _). exact (sieveTransf_Ident _).
abstract (reflexivity). abstract (reflexivity).
- intros V1 V2 Hseq. unshelve eexists. 
   exact (_revSieveTransf_sieveEquiv Hseq). exact (_sieveTransf_sieveEquiv Hseq).
abstract(intros; rewrite -> _surProp_sieveEquiv; reflexivity).
abstract(intros; rewrite -> _injProp_sieveEquiv; reflexivity).
- intros V1 V2 V3 Hseq12 Hseq23. unshelve eexists. exact (sieveTransf_Compos Hseq12 Hseq23). 
exact (sieveTransf_Compos (_revSieveTransf_sieveEquiv Hseq23) (_revSieveTransf_sieveEquiv Hseq12)).
abstract(intros; cbn_transf;  rewrite -> _injProp_sieveEquiv; rewrite -> _injProp_sieveEquiv; reflexivity).
abstract(intros; cbn_transf;  rewrite -> _surProp_sieveEquiv; rewrite -> _surProp_sieveEquiv; reflexivity).
Defined.

Section interSieve.

 Section Section1.
 Variables (G : vertexGene) (VV : sieveFunctor G)
           (G' : vertexGene) (g : 'Gene( G' ~> G ))
           (UU : sieveFunctor G').

Record type_interSieve H :=
  { _factor_interSieve : 'Sieve( H ~> _ | UU ) ;
    _whole_interSieve : 'Sieve( H ~> _ | VV ) ;
    _wholeProp_interSieve : _whole_interSieve :>sieve_ 
        == (_factor_interSieve :>sieve_) o>functor_[functor_ViewOb G] g }.

Definition rel_interSieve H : crelation (type_interSieve H).
intros v v'. exact (((_factor_interSieve v == _factor_interSieve v') *
(_whole_interSieve v == _whole_interSieve v')) %type ).
Defined.

Instance equiv_interSieve H : Equivalence (@rel_interSieve H).
abstract(unshelve eexists;
[ (move; intros; move; split; reflexivity)
| (move; intros ? ? [? ?]; move; intros; split; symmetry; assumption)
| (move; intros ? ? ? [? ?] [? ?]; move; intros; split; etransitivity; eassumption)]).
Qed.

Definition interSieve : sieveFunctor G'.
Proof. unshelve eexists.
{ (* functor *) unshelve eexists.
  - (* typeOf_objects_functor *) intros H. 
    + (* relType *) unshelve eexists. exact (type_interSieve H).
      exact (@rel_interSieve H).
      exact (@equiv_interSieve H).
  - (* typeOf_arrows_functor *) unfold typeOf_arrows_functor. intros H H'.
    +  (* relFunctor *) unshelve eexists.
      * (* -> *) cbn_. intros h vg'. unshelve eexists.          
          exact: (h o>sieve_ (_factor_interSieve vg')).
          exact: (h o>sieve_ (_whole_interSieve vg')). 
          abstract(cbn_; tac_unsimpl; rewrite <- 2!_natural_transf; 
          rewrite -> _wholeProp_interSieve, _functorialCompos_functor'; reflexivity).
      * (* Proper *) abstract(move; autounfold;
      intros h1 h2 Heq_h vg'1 vg'2; case => /= Heq_vg' Heq_vg'0;
      split; cbn_; rewrite -> Heq_h;  [rewrite -> Heq_vg' | rewrite -> Heq_vg'0]; reflexivity).
  - (* typeOf_functorialCompos_functor *) abstract(move; intros; autounfold; split; cbn_;
  rewrite -> _functorialCompos_functor; reflexivity).
  - (* typeOf_functorialIdent_functor *) abstract(move; intros; autounfold; split; cbn_;
    rewrite -> _functorialIdent_functor; reflexivity). }
{ (* transf *) unshelve eexists.
  - (* typeOf_arrows_transf *) intros H. unshelve eexists.
    + (* -> *) cbn_; intros vg'. exact: ((_factor_interSieve vg') :>sieve_).
    + (* Proper *)  abstract(move; autounfold; cbn_;
    intros vg'1 vg'2; case => /= Heq0 Heq; rewrite -> Heq0; reflexivity).
  - (* typeOf_natural_transf *) abstract(move; cbn -[_arrows_functor]; intros; 
  rewrite -> _natural_transf; reflexivity). }
Defined.

Lemma transf_interSieve_Eq  H  (v : 'Sieve(H ~> _ | interSieve )) :
 ((_factor_interSieve v) :>sieve_ ) == (v :>sieve_ ) .
Proof. reflexivity.
Qed.

Global Instance whole_interSieve_Proper  H : Proper (equiv ==> equiv) 
 (@_whole_interSieve  H : 'Sieve( H ~> _ | interSieve  ) -> 'Sieve( H ~> _ | VV )). 
Proof.    move. cbn_. intros v1 v2 [Heq Heq']. exact Heq'.
Qed.

Global Instance factor_interSieve_Proper  H : Proper (equiv ==> equiv) 
 (@_factor_interSieve  H : 'Sieve( H ~> _ | interSieve  ) -> 'Sieve( H ~> _ | UU )). 
Proof.    move. cbn_. intros v1 v2 [Heq Heq']. exact Heq.
Qed.

Definition interSieve_projWhole : transf interSieve VV.
Proof. unshelve eexists. unshelve eexists.
- (* -> *) exact: _whole_interSieve.
- (* Proper *) exact: whole_interSieve_Proper. (* abstract (typeclasses eauto).  *)
- (* typeOf_natural_transf *) abstract(intros H H' h f; cbn_; reflexivity).
Defined.

Definition interSieve_projFactor : sieveTransf interSieve UU.
Proof. unshelve eexists.  unshelve eexists. unshelve eexists.
- (* -> *) exact: _factor_interSieve.
- (* Proper *) exact: factor_interSieve_Proper. (* abstract (typeclasses eauto).  *)
- (* typeOf_natural_transf *) abstract(intros H H' h f; cbn_;  reflexivity).
- (* _commute_sieveTransf *) abstract(move; cbn_; intros; reflexivity).
Defined.

End Section1.

Definition pullSieve G VV G' g := @interSieve G  VV G' g (identSieve G').
Definition meetSieve G VV UU := @interSieve G VV G (@identGene G) UU.

Definition pullSieve_projWhole G VV G' g : 
transf (@pullSieve G VV G' g) VV
:= (@interSieve_projWhole G  VV G' g (identSieve G')).

Definition pullSieve_projFactor G VV G' g : 
sieveTransf (@pullSieve G VV G' g) (identSieve G')
:= (@interSieve_projFactor G  VV G' g (identSieve G')).

Definition meetSieve_projFactor G VV UU : 
sieveTransf (@meetSieve G VV UU) UU := @interSieve_projFactor G VV G (@identGene G) UU  .

Definition meetSieve_projWhole G VV UU : 
sieveTransf (@meetSieve G VV UU) VV.
exists (interSieve_projWhole _ _ _).
intros H v; simpl. rewrite -> _wholeProp_interSieve.
(* HERE *) abstract(exact: identGene_composGene).
Defined.

Section Section2.
Variables (G : vertexGene) (VV : sieveFunctor G)
  (G' : vertexGene) (g : 'Gene( G' ~> G ))
  (UU : sieveFunctor G')
  (G'' : vertexGene) (g' : 'Gene( G'' ~> G' ))(WW : sieveFunctor G'').

Definition interSieve_compos : transf (interSieve VV (g' o>functor_[functor_ViewOb G] g)
(interSieve UU g' WW) ) (interSieve VV g UU).
Proof. unshelve eexists. intros H. unshelve eexists.
- (* -> *) intros v; unshelve eexists. 
    exact: ((_whole_interSieve (_factor_interSieve v)) ).
    exact: (_whole_interSieve v) .
    abstract(do 2 rewrite -> _wholeProp_interSieve; 
    rewrite -> _functorialCompos_functor'; simpl; reflexivity).
- (* Proper *) abstract(move; move => f1 f2 Heq;
split; autounfold; simpl; [rewrite -> (whole_interSieve_Proper (factor_interSieve_Proper Heq)); reflexivity
| rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (* typeOf_natural_transf *) abstract (intros H H' h f; autounfold; split; simpl; reflexivity).
Defined.

Definition pullSieve_compos : transf (pullSieve VV (g' o>functor_[functor_ViewOb G] g)) (pullSieve VV g).
Proof. unshelve eexists. intros H. unshelve eexists.
- (* -> *) intros v; unshelve eexists. 
    exact: ((_factor_interSieve v) o>functor_[functor_ViewOb G'] g').
    exact: (_whole_interSieve v) .
    abstract(rewrite -> _wholeProp_interSieve; rewrite -> _functorialCompos_functor'; simpl; reflexivity).
- (* Proper *) abstract(move; move => f1 f2 Heq;
split; autounfold; simpl; [rewrite ->  (factor_interSieve_Proper Heq); reflexivity
| rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (* typeOf_natural_transf *) intros H H' h f; autounfold; split; cbn_sieve; cbn_functor;
[ rewrite -> _functorialCompos_functor'; reflexivity
| reflexivity ].
Defined.
End Section2.

Lemma interSieve_congr G (VV1 VV2 : sieveFunctor G)  (vv: sieveTransf VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2)
  (UU1 UU2 : sieveFunctor G') (uu: sieveTransf UU1 UU2): 
  sieveTransf (interSieve VV1 g1 UU1) (interSieve VV2 g2 UU2).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact: ((_factor_interSieve v) :>transf_ uu). 
  (* _whole_interSieve *) exact: ((_whole_interSieve v) :>transf_ vv).
  (* _wholeProp_interSieve *) abstract(simpl; rewrite  -> _commute_sieveTransf ,
  _commute_sieveTransf , _wholeProp_interSieve , genEquiv; reflexivity).
  (* _congr_relTransf  *) abstract(move; intros ? ? Heq; split; autounfold; simpl;
  [ rewrite -> (factor_interSieve_Proper Heq); reflexivity
  | rewrite -> (whole_interSieve_Proper Heq); reflexivity]).
- (*  _natural_transf  *) abstract(intros H' H h v; split; simpl;
  rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(intros H v; simpl; rewrite -> _commute_sieveTransf; reflexivity).
Defined.

Definition pullSieve_congr G (VV1 VV2 : sieveFunctor G)  (vv: sieveTransf VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2): 
  sieveTransf (pullSieve VV1 g1) (pullSieve VV2 g2)
  := @interSieve_congr G VV1 VV2 vv G' g1 g2 genEquiv _ _ (sieveTransf_Ident _).

Lemma pullSieve_pullSieve G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G)) G'' (g' : 'Gene(G'' ~> G')): 
sieveTransf (pullSieve (pullSieve VV g) g') (pullSieve VV (g' o>functor_[functor_ViewOb _] g)).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) exact: ((_whole_interSieve (_whole_interSieve v))).
  (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
   rewrite -> _functorialCompos_functor';
   setoid_rewrite <- _wholeProp_interSieve at 2; simpl; reflexivity).
  (* _congr_relTransf  *) abstract(move; intros ? ? Heq; split; autounfold; cbn -[_rel_relType];
   [ rewrite -> (factor_interSieve_Proper Heq); reflexivity
   | rewrite -> (whole_interSieve_Proper (whole_interSieve_Proper Heq)); reflexivity]) .
- (*  _natural_transf  *) abstract(move; split; simpl; reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma pullSieve_pullSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')): sieveTransf (pullSieve VV (g' o>functor_[functor_ViewOb _] g)) (pullSieve (pullSieve VV g) g') .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) { unshelve eexists.
        (* _factor_interSieve *) exact (_factor_interSieve v o>functor_[functor_ViewOb _] g'). 
        (* _whole_interSieve *) exact: ( _whole_interSieve v).
        (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
        rewrite -> _functorialCompos_functor'; reflexivity). }
  (* _wholeProp_interSieve *)  abstract(reflexivity).
  (* _congr_relTransf  *) abstract  (move; intros v1 v2; case; autounfold; cbn_; 
  move => Heq_factor Heq_whole; split; autounfold; cbn -[_rel_relType];
  [rewrite -> Heq_factor; reflexivity | ]; split; autounfold; cbn -[_rel_relType];
  [rewrite -> Heq_factor; reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
[reflexivity | split; cbn_sieve; 
[ rewrite -> _functorialCompos_functor'; reflexivity | reflexivity ]]).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma pullSieve_ident G (VV : sieveFunctor G) : sieveTransf (pullSieve VV identGene) VV.
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. exact: (_whole_interSieve v).
  (* _congr_relTransf  *) abstract (move; move => x y Heq;
   rewrite -> (whole_interSieve_Proper Heq); reflexivity).
- (* _natural_transf *) abstract(move; intros; simpl; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; simpl; rewrite -> _wholeProp_interSieve; simpl; 
(* FUNCTOR/TRANSF PROBLEM *) apply: identGene_composGene).
Defined.

Lemma pullSieve_ident_rev G (VV : sieveFunctor G) : sieveTransf VV (pullSieve VV identGene).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact (v :>sieve_). exact v.
        abstract (cbn_sieve; symmetry; apply: identGene_composGene).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *) abstract(move; intros; cbn_sieve; split; cbn_sieve; 
            last reflexivity; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
Defined.

End interSieve.

Existing Instance whole_interSieve_Proper.
Existing Instance factor_interSieve_Proper.

Lemma interSieve_composeOuter G (VV : sieveFunctor G) 
G' (g : 'Gene(G' ~> G)) (UU : sieveFunctor G')
 G'' (g' : 'Gene(G'' ~> G')) G''' (g'' : 'Gene(G''' ~> G''))    : 
  transf (interSieve    (pullSieve VV (g' o>gene g))  g'' (pullSieve UU (g'' o>gene g')))
   (interSieve VV g UU).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact: ((v :>transf_ (interSieve_projFactor _ _ _)) 
      :>transf_ (pullSieve_projWhole _ _ ) ). 
  (* _whole_interSieve *) exact: ((v :>transf_ (interSieve_projWhole _ _ _)) 
      :>transf_ (pullSieve_projWhole _ _ ) ). 
  (* _wholeProp_interSieve *) abstract (cbn_transf; do 2 rewrite -> _wholeProp_interSieve;
  rewrite -> (_wholeProp_interSieve v); tac_unsimpl;
   do 3 rewrite <- _functorialCompos_functor';
  reflexivity).
  (* _congr_relTransf  *) abstract (move; intros ? ? Heq; split; cbn_transf;
  rewrite -> Heq; reflexivity).
- (*  _natural_transf  *) abstract (intros H' H h v; split; cbn_sieve; reflexivity).
Defined.

Lemma interSieve_composeOuter_ident G (VV : sieveFunctor G) 
G' (g : 'Gene(G' ~> G)) (UU : sieveFunctor G')
 G'' (g' : 'Gene(G'' ~> G'))  : 
  transf (interSieve    (pullSieve VV (g' o>gene g))  (identGene)    (pullSieve UU ( g')))
   (interSieve VV g UU).
Proof. refine (transf_Compos _ (interSieve_composeOuter _ _ _ g' identGene)).
refine (interSieve_congr (sieveTransf_Ident _) (reflexivity _) _).
refine (pullSieve_congr (sieveTransf_Ident _) _).
abstract (symmetry; exact: composGene_identGene).
Defined.

Lemma interSieve_congr_sieveEquiv G (VV1 VV2 : sieveFunctor G)  (vv: sieveEquiv VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2)
  (UU1 UU2 : sieveFunctor G') (uu: sieveEquiv UU1 UU2): 
  sieveEquiv (interSieve VV1 g1 UU1) (interSieve VV2 g2 UU2).
Proof. unshelve eexists.
exact: (interSieve_congr vv genEquiv uu).
exact (interSieve_congr (_revSieveTransf_sieveEquiv vv) 
  (symmetry genEquiv) (_revSieveTransf_sieveEquiv uu)).
abstract (intros; split; simpl; rewrite -> _injProp_sieveEquiv; reflexivity).
abstract(intros; split; simpl; rewrite -> _surProp_sieveEquiv; reflexivity).
Defined.

Definition pullSieve_congr_sieveEquiv G (VV1 VV2 : sieveFunctor G)  (vv: sieveEquiv VV1 VV2) 
G' (g1 g2 : 'Gene(G' ~> G)) (genEquiv: g1 == g2): 
  sieveEquiv (pullSieve VV1 g1) (pullSieve VV2 g2)
  := @interSieve_congr_sieveEquiv G VV1 VV2 vv G' g1 g2 genEquiv _ _ (reflexivity _).

Lemma pullSieve_pullSieve_sieveEquiv G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')): sieveEquiv (pullSieve (pullSieve VV g) g') 
  (pullSieve VV (g' o>functor_[functor_ViewOb _] g)).
Proof. unshelve eexists.
exact: pullSieve_pullSieve.
exact: pullSieve_pullSieve_rev.
abstract(intros; split; cbn_transf; reflexivity).
abstract(intros H v; split; cbn_transf; first reflexivity;
last split; cbn_transf; first (rewrite -> (_wholeProp_interSieve v); reflexivity);
     last reflexivity).
Defined.

Lemma pullSieve_ident_sieveEquiv G (VV : sieveFunctor G) : 
  sieveEquiv (pullSieve VV identGene) VV.
Proof. unshelve eexists.
exact: pullSieve_ident.
exact: pullSieve_ident_rev.
abstract(intros; cbn_transf; reflexivity).
abstract(intros H v; split; cbn_transf; last reflexivity;
first rewrite -> _wholeProp_interSieve; apply: identGene_composGene).
Defined.

Definition interSieve_identSieve_sieveEquiv (G G': vertexGene)
(g: 'Gene( G' ~> G )) (WW : sieveFunctor G')
: sieveEquiv (interSieve (identSieve G) g WW) WW.
Proof. unshelve eexists. exact: interSieve_projFactor.
- {  unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact v. exact ((v :>sieve_) :>transf_ (transf_ViewObMor g)).
        abstract (cbn_sieve; reflexivity).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; 
        cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
abstract(move; intros; cbn_sieve; split; cbn_sieve; first reflexivity; 
    do 2 rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
}
- abstract (intros; cbn_transf; reflexivity).
- abstract (intros H v; cbn_transf; split; cbn_transf; first reflexivity; 
  symmetry; apply: (_wholeProp_interSieve v)).
Defined.

(* TODO: REDO: instance of interSieve_identSieve_sieveEquiv *)
Definition pullSieve_identSieve_sieveEquiv (G G': vertexGene)
(g: 'Gene( G' ~> G ))
: sieveEquiv (pullSieve (identSieve G) g) (identSieve G').
Proof. unshelve eexists. exact: interSieve_projFactor.
- { unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
        exact (v :>sieve_). exact (v :>transf_ (transf_ViewObMor g)).
        abstract (cbn_sieve; reflexivity).
  (* _congr_relTransf  *) abstract(move; move => x y Heq; 
      cbn_transf; split; cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
  abstract(move; intros; cbn_sieve; split; cbn_sieve; 
    first reflexivity; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
}
- abstract (intros; cbn_transf; reflexivity).
- abstract (intros H v; cbn_transf; split; cbn_transf; first reflexivity; 
  symmetry; apply: (_wholeProp_interSieve v)).
Defined.

Lemma interSieve_interSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU))
  (interSieve (interSieve VV g WW) g' UU) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve (_factor_interSieve v)). 
  (* _whole_interSieve *) refine ( v :>transf_  (interSieve_compos _ _ _ _ _) ).
  (* _wholeProp_interSieve *)  abstract (cbn_sieve; rewrite -> _wholeProp_interSieve; reflexivity).
  (* _congr_relTransf  *) abstract (move; intros v1 v2; case; cbn_sieve;
  move => Heq_factor Heq_whole; split; cbn_sieve;
  [rewrite -> (factor_interSieve_Proper Heq_factor); reflexivity | ]; split; cbn_sieve;
  [rewrite -> (whole_interSieve_Proper Heq_factor); reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
    first reflexivity;  split; cbn_sieve; reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma interSieve_interSieve G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve (interSieve VV g WW) g' UU) 
  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU)).
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) refine ( v :>transf_  (interSieve_congr (interSieve_projFactor _ _ _) 
      (reflexivity _) (sieveTransf_Ident _)) ). 
  (* _whole_interSieve *) exact: ((_whole_interSieve (_whole_interSieve v))).
  (* _wholeProp_interSieve *)  abstract(rewrite -> _wholeProp_interSieve;
   rewrite -> _functorialCompos_functor';
   setoid_rewrite <- _wholeProp_interSieve at 2; simpl; reflexivity).
  (* _congr_relTransf  *) abstract (move; intros ? ? [Heq_outer Heq_inner];split;  cbn_sieve;
  first (split; cbn_sieve; first (rewrite -> Heq_outer; reflexivity); 
        rewrite -> (factor_interSieve_Proper Heq_inner); reflexivity );
  last rewrite -> (whole_interSieve_Proper Heq_inner); reflexivity).
- (*  _natural_transf  *) abstract(move; split; cbn_sieve; first (split; cbn_sieve; reflexivity);
                          last reflexivity).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Lemma interSieve_interSieve_sieveEquiv  G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
(WW : sieveFunctor G')
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveEquiv  (interSieve (interSieve VV g WW) g' UU) 
  (interSieve VV (g' o>functor_[functor_ViewOb _] g) (interSieve WW g' UU)).
Proof. unshelve eexists.
exact: interSieve_interSieve.
exact: interSieve_interSieve_rev.
abstract(intros; split; cbn_transf; first (split; cbn_transf; reflexivity); reflexivity).
abstract(intros H v; split; cbn_transf; first reflexivity;
last split; cbn_transf; reflexivity).
Defined.

(*  NOT LACKED, SEE GENERAL interSieve_interSieve_rev *)
Lemma interSieve_pullSieve_rev G (VV : sieveFunctor G) G' (g : 'Gene(G' ~> G))
G'' (g' : 'Gene(G'' ~> G')) (UU : sieveFunctor G'') : 
sieveTransf  (interSieve VV (g' o>functor_[functor_ViewOb _] g) UU)
  (interSieve (pullSieve VV g) g' UU) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists. 
  (* _factor_interSieve *) exact (_factor_interSieve v). 
  (* _whole_interSieve *) { refine ( v :>transf_  _ ).
      refine (transf_Compos (interSieve_congr (sieveTransf_Ident _) (reflexivity _) 
                                    (sieveTransf_sieveFunctor _)) _). 
      exact (pullSieve_compos _ _ _). }
  (* _wholeProp_interSieve *)  abstract(reflexivity).
  (* _congr_relTransf  *) abstract  (move; intros v1 v2; case; cbn_sieve;
  move => Heq_factor Heq_whole; split; cbn_sieve;
  [rewrite -> Heq_factor; reflexivity | ]; split; cbn_sieve;
  [rewrite -> Heq_factor; reflexivity | rewrite -> Heq_whole; reflexivity ]).
- (*  _natural_transf  *) abstract (move; split; cbn_sieve;
[reflexivity | split; cbn_sieve; 
[ rewrite -> _functorialCompos_functor'; 
  rewrite -> _natural_transf; reflexivity | reflexivity ]]).
- (* _commute_sieveTransf *) abstract(move; reflexivity).
Defined.

Definition interSieve_image_rev (G : vertexGene)
(UU : sieveFunctor G)
(H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (VV : sieveFunctor H)
: sieveTransf (interSieve UU (u :>sieve_)  VV) VV.
Proof. exact: interSieve_projFactor.
Defined.

Definition interSieve_image (G : vertexGene)
(UU : sieveFunctor G)
(H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (VV : sieveFunctor H)
: sieveTransf VV (interSieve UU (u :>sieve_)  VV) .
Proof.  unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros K. unshelve eexists.
(* _fun_relTransf *) intros v. unshelve eexists. 
      exact v. exact ((v :>sieve_) o>sieve_ u).
      abstract (cbn_sieve; rewrite -> _natural_transf; reflexivity).
(* _congr_relTransf  *) abstract(move; move => x y Heq; cbn_transf; split; 
    cbn_transf; rewrite -> Heq; reflexivity).
- (* _natural_transf *)
abstract(move; intros; cbn_sieve; split; cbn_sieve; first reflexivity; 
    rewrite <- _natural_transf, <- _functorialCompos_functor' ; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; cbn_sieve; reflexivity).
Defined.

Definition interSieve_image_sieveEquiv (G : vertexGene)
(UU : sieveFunctor G)
(H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (VV : sieveFunctor H)
 (UU_base: typeOf_baseSieve UU)
 : sieveEquiv VV (interSieve UU (u :>sieve_)  VV) .
Proof. unshelve eexists.
- exact:  interSieve_image.
-  exact: interSieve_image_rev.
- abstract (intros K v; cbn_transf; split; cbn_transf; first reflexivity;
apply: UU_base; unfold _rel_relType, equiv; simpl; rewrite <- _natural_transf;
 symmetry; apply: (_wholeProp_interSieve v)).
 - abstract (intros; cbn_transf; reflexivity).
Defined.

Section sumSieve.

Section Section1.
Variables (G : vertexGene) (VV : sieveFunctor G).

Record typeOf_outer_sumSieve :=
  { _object_typeOf_outer_sumSieve :> vertexGene ; 
    _arrow_typeOf_outer_sumSieve :> 'Sieve( _object_typeOf_outer_sumSieve ~> G | VV ) }.

(* higher/congruent structure is possible... *)
Variables (WP_ : forall (object_: vertexGene) (outer_: 'Sieve( object_ ~> G | VV )),
 sieveFunctor object_).
 

Record type_sumSieve H :=
  { _object_sumSieve : vertexGene ;
    _outer_sumSieve : 'Sieve( _object_sumSieve ~> G | VV ) ; 
    _inner_sumSieve : 'Sieve( H ~> _ | WP_ _outer_sumSieve ) }.

Inductive rel_sumSieve H  (wv : type_sumSieve H) : type_sumSieve H  -> Type :=
| Rel_sumSieve : forall (outer': 'Sieve( _object_sumSieve wv ~> G | VV ))
  (inner': (WP_  outer') H),
  outer' == _outer_sumSieve wv ->
  (* higher/congruent structure is possible... *)
  inner' :>sieve_ == (_inner_sumSieve wv) :>sieve_ ->
  rel_sumSieve wv
  {| _object_sumSieve := _ ;
  _outer_sumSieve := outer' ; 
  _inner_sumSieve := inner' |}.

Instance rel_sumSieve_Equivalence H : Equivalence (@rel_sumSieve H).
abstract(unshelve eexists;
      [ (intros [object_wv outer_wv inner_wv]; constructor; reflexivity)
      | (* intros wv1 wv2 []. *) (intros [object_wv1 outer_wv1 inner_wv1] [object_wv2 outer_wv2 inner_wv2] [];
       constructor; symmetry; assumption)
      | (intros wv1 wv2 wv3 Heq12 Heq23; destruct Heq23 as [outer3 inner3 Heq23 Heq23'];
      destruct Heq12 as [outer2 inner2 Heq12 Heq12']; simpl; constructor; simpl;
      [ rewrite -> Heq23; simpl; rewrite -> Heq12; simpl; reflexivity 
       | rewrite -> Heq23'; simpl; rewrite -> Heq12'; simpl; reflexivity])]).
Qed.

(* TODO: sumSieve_projOuter : sumSieve -> UU  *)
Definition sumSieve : sieveFunctor G.
Proof. unshelve eexists.
{ (* functor *) unshelve eexists.
  - (* typeOf_objects_functor *) intros H.
    + (* relType *) unshelve eexists. exact (type_sumSieve H).
    + (* Setoid *)  exact (@rel_sumSieve H).
     (* exists (equiv @@ (@compos_sumSieve H))%signature. *)
    + (* Equivalence *) exact: rel_sumSieve_Equivalence.
  - (* typeOf_arrows_functor *) move. intros H H'.
    (* relFunctor *) unshelve eexists.
    + (* -> *) simpl. intros h wv. unshelve eexists.
        exact: (_object_sumSieve wv). exact: (_outer_sumSieve wv).
        exact: (h o>sieve_ _inner_sumSieve wv).
    + (* Proper *) abstract(move;  autounfold; simpl;
    intros h1 h2 Heq_h [object_wv1 outer_wv1 inner_wv1] wv2 Heq; tac_unsimpl;
    case: wv2 / Heq => /= [outer_wv2 inner_wv2 Heq12 Heq12']; constructor; simpl;
    [ rewrite -> Heq12; reflexivity
     | do 2 rewrite <- _natural_transf; rewrite -> Heq_h , Heq12'; reflexivity]).
  - (* typeOf_functorialCompos_functor *) abstract(intros H H' h H'' h' [object_wv outer_wv inner_wv];
     simpl; constructor; simpl; [ reflexivity | rewrite -> _functorialCompos_functor; reflexivity]).
  - (* typeOf_functorialIdent_functor *) abstract(intros H [object_wv outer_wv inner_wv];
  simpl; constructor; simpl; [ reflexivity | rewrite ->  _functorialIdent_functor; reflexivity]). }
{ (* transf *) unshelve eexists.
  - (* typeOf_arrows_transf *) intros H. unshelve eexists.
    + (* -> *) simpl; intros wv. exact: ((_inner_sumSieve wv :>sieve_) o>functor_ (_outer_sumSieve wv :>sieve_)). 
    + (* Proper *) abstract(move; autounfold; simpl;
    intros wv1 wv2 Heq; tac_unsimpl;
    case: wv2 / Heq => /= [outer_wv2 inner_wv2 Heq12 Heq12']; tac_unsimpl; rewrite -> Heq12;
    rewrite -> Heq12'; reflexivity).
  - (* typeOf_natural_transf *) move. cbn_functor. abstract(move; cbn_functor; intros H H' h wv;
   rewrite -> _functorialCompos_functor';
  setoid_rewrite -> _natural_transf at 2; reflexivity). }
Defined.

Definition sumSieve_projOuter :
 sieveTransf sumSieve VV.
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros wv. exact: ((_inner_sumSieve wv :>sieve_) o>sieve_ (_outer_sumSieve wv)).
  + (* _congr_relTransf *) abstract(move;  intros wv1 wv2 [outer_wv2 inner_wv2 Heq_outer_wv2 Heq_inner_wv2];
  cbn_transf; rewrite -> Heq_outer_wv2, -> Heq_inner_wv2; reflexivity).
- (* _natural_transf *) abstract(move; intros; cbn_sieve; 
    rewrite -> _functorialCompos_functor', -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; simpl; rewrite <- _natural_transf; reflexivity).
Defined.

End Section1.

Definition sumSieve_sectionPull :
forall (U : vertexGene) (UU : sieveFunctor U) 
(VV_ : forall (H: vertexGene) (outer_: 'Sieve( H ~> U | UU )), sieveFunctor H)
(H: vertexGene)
(u: 'Sieve( H ~> _ | UU )),
 sieveTransf (VV_ H u)
  (pullSieve (sumSieve VV_) (u:>sieve_)) .
Proof. unshelve eexists. unshelve eexists.
- intros K. unshelve eexists.
  + (* _fun_relTransf *) intros v.  unshelve eexists.
    * (* _factor_interSieve *)exact: ((v :>sieve_) ). 
      (* _whole_interSieve *) unshelve eexists.
    * (* _object_sumSieve *) exact: H.
    * (* _outer_sumSieve *) exact: u.
    * (* _inner_sumSieve *) exact: v.
    * (* _wholeProp_interSieve *) abstract(simpl; reflexivity).
  + (* _congr_relTransf *) abstract(move;  intros v1 v2 Heq_v; split; autounfold; simpl;
  first (rewrite -> Heq_v; reflexivity); split; autounfold; simpl;
  first reflexivity; rewrite -> Heq_v; reflexivity).
- (* _natural_transf *) abstract(move; intros;  split; cbn_transf; last reflexivity;
cbn_sieve; rewrite -> _natural_transf; reflexivity).
- (* _commute_sieveTransf *) abstract(move; intros; simpl; reflexivity).
Defined.

Definition sumSieve_section:
forall (U : vertexGene) (UU : sieveFunctor U) 
(VV_ : forall (H: vertexGene) (outer_: 'Sieve( H ~> U | UU )), sieveFunctor H)
(H: vertexGene)
(u: 'Sieve( H ~> _ | UU )),
 transf (VV_ H u)  (sumSieve VV_) .
Proof. intros. exact: (transf_Compos (sumSieve_sectionPull _ _) (pullSieve_projWhole _ _) ).
Defined.

End sumSieve.
(* Global Hint Unfold compos_sumSieve : poly. *)

Lemma sumSieve_congrTransf (G : vertexGene) (UU1  : sieveFunctor G)
G' ( UU2 : sieveFunctor G')
(uu : transf UU1 UU2)
(VV1_ : forall H : vertexGene, 'Sieve( H ~> _ | UU1 ) -> sieveFunctor H)
(VV2_ : forall H : vertexGene, 'Sieve( H ~> _ | UU2 ) -> sieveFunctor H)
(vv_ : forall (H: vertexGene) (u1: 'Sieve( H ~> _ | UU1 )),
 sieveTransf  (VV1_ _ u1) (VV2_ _ (u1 :>transf_ uu))) :
transf  (sumSieve VV1_ ) (sumSieve VV2_).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros K. unshelve eexists.
  (* _fun_relTransf *) intros vu. unshelve eexists. 
  (* _object_sumSieve *) exact: (_object_sumSieve vu). 
  (* _outer_sumSieve *) exact: (_outer_sumSieve vu :>transf_ uu).
  (* _inner_sumSieve *) exact: (_inner_sumSieve vu :>transf_ (vv_ _ _)).
  (* _congr_relTransf  *) abstract(move; intros vu1 vu2 [outer_vu2 inner_vu2 Heq_outer_vu2 Heq_inner_vu2];
  simpl; constructor; simpl; [rewrite -> Heq_outer_vu2; reflexivity 
  | do 2 rewrite -> _commute_sieveTransf; rewrite -> Heq_inner_vu2; reflexivity  ]).
- (*  _natural_transf  *) abstract(intros K K' k vvu; cbn_sieve;
  constructor; simpl; [reflexivity | rewrite -> _natural_transf; reflexivity]).
Defined.

Lemma sumSieve_congr (G : vertexGene) (UU1 UU2 : sieveFunctor G)
(uu : sieveTransf UU1 UU2)
(VV1_ : forall H : vertexGene, 'Sieve( H ~> _ | UU1 ) -> sieveFunctor H)
(VV2_ : forall H : vertexGene, 'Sieve( H ~> _ | UU2 ) -> sieveFunctor H)
(vv_ : forall (H: vertexGene) (u1: 'Sieve( H ~> _ | UU1 )),
sieveTransf  (VV1_ _ u1) (VV2_ _ (u1 :>transf_ uu))) :
sieveTransf  (sumSieve VV1_ ) (sumSieve VV2_).
Proof. unshelve eexists. (* _transf_sieveTransf *) exact: sumSieve_congrTransf.
(* _commute_sieveTransf *) abstract(intros K vu; simpl; do 2 rewrite -> _commute_sieveTransf; reflexivity).
Defined.

Lemma sumSieve_interSieve' (G : vertexGene) (UU : sieveFunctor G)
G' (g : 'Gene(G' ~> G))  (WW : sieveFunctor G')
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | (interSieve UU g WW) ) -> sieveFunctor H)
G'' (g' : 'Gene(G'' ~> G')) 
(pullVV_ := fun (H : vertexGene) (v : 'Sieve( H ~> _ | (interSieve UU (g' o>gene g) (pullSieve WW g') ) )) =>
    VV_ _ ( v :>transf_ (interSieve_compos _ g _ g' (identSieve _))) ) :
sieveTransf  (sumSieve pullVV_ ) (pullSieve (sumSieve VV_) g').
Proof. unshelve eexists. unshelve eexists.
intros K. unshelve eexists. intros vu.
{ unshelve eexists. refine (_factor_interSieve (((_inner_sumSieve vu) :>sieve_) 
                                      o>functor_ (_factor_interSieve (_outer_sumSieve vu)))).
unshelve eexists; cycle 1.
 refine ( (_outer_sumSieve vu):>transf_ (interSieve_compos _ g _ g' (identSieve _)) ).
 refine (_inner_sumSieve vu).
 abstract (cbn_sieve; rewrite -> _wholeProp_interSieve; rewrite -> _functorialCompos_functor'; reflexivity).
}

- abstract (subst pullVV_; move; intros vu1 vu2 [outer_vu2 inner_vu2 Heq_outer_vu2 Heq_inner_vu2]; cbn_sieve; split; cbn_sieve;
[rewrite -> Heq_inner_vu2; rewrite -> (factor_interSieve_Proper (factor_interSieve_Proper Heq_outer_vu2)); reflexivity | ];
constructor; cbn_sieve; [ split; cbn_sieve; [rewrite -> (whole_interSieve_Proper (factor_interSieve_Proper Heq_outer_vu2)); reflexivity
| rewrite -> (whole_interSieve_Proper Heq_outer_vu2); reflexivity]
| rewrite -> Heq_inner_vu2; reflexivity]).

- abstract(intros K K' k vu; cbn_sieve; split; cbn_sieve;
first (rewrite <- _natural_transf;
rewrite -> _functorialCompos_functor'; reflexivity);
reflexivity).

- abstract(intros K vu; simpl; reflexivity).
Defined.

Lemma sumSieve_pullSieve' (G : vertexGene) (UU : sieveFunctor G)
G' (g : 'Gene(G' ~> G))
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | (pullSieve UU g) ) -> sieveFunctor H)
G'' (g' : 'Gene(G'' ~> G')) 
(pullVV_ := fun (H : vertexGene) (v : 'Sieve( H ~> _ | (pullSieve UU (g' o>gene g)) )) =>
    VV_ _ ( v :>transf_ (pullSieve_compos _ g g')) ) :
sieveTransf  (sumSieve pullVV_ ) (pullSieve (sumSieve VV_) g').
Proof. unshelve eexists. unshelve eexists.
intros K. unshelve eexists. intros vu.
{ unshelve eexists. refine (((_inner_sumSieve vu) :>sieve_) o>functor_ (_factor_interSieve (_outer_sumSieve vu))).
unshelve eexists; cycle 1.
 refine ( (_outer_sumSieve vu):>transf_ (pullSieve_compos _ g g') ).
 refine (_inner_sumSieve vu).
 abstract(cbn_sieve; rewrite -> _functorialCompos_functor'; reflexivity).
}

- abstract (subst pullVV_; move; intros vu1 vu2 [outer_vu2 inner_vu2 Heq_outer_vu2 Heq_inner_vu2]; cbn_sieve; split; cbn_sieve;
[rewrite -> Heq_inner_vu2; rewrite -> (factor_interSieve_Proper Heq_outer_vu2); reflexivity | ];
constructor; cbn_sieve; [ split; cbn_sieve; [rewrite -> (factor_interSieve_Proper Heq_outer_vu2); reflexivity
| rewrite -> (whole_interSieve_Proper Heq_outer_vu2); reflexivity]
| rewrite -> Heq_inner_vu2; reflexivity]).

- abstract(intros K K' k vu; cbn_sieve; split; cbn_sieve;
first (rewrite <- _natural_transf;
rewrite -> _functorialCompos_functor'; reflexivity);
reflexivity).

- abstract(intros K vu; simpl; reflexivity).
Defined.

(* sumSieve_pullSieve' ->  sumSieve_pullSieve *)
Lemma sumSieve_pullSieve (G : vertexGene) (UU : sieveFunctor G)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
G' (g : 'Gene(G' ~> G)) 
(pullVV_ := fun (H : vertexGene) (v : 'Sieve( H ~> _ | (pullSieve UU g) )) => 
    VV_ _ (_whole_interSieve v) ) :
sieveTransf  (sumSieve pullVV_ ) (pullSieve (sumSieve VV_) g).
Proof. unshelve eexists. unshelve eexists.
intros K. unshelve eexists. intros vu.
{ unshelve eexists. refine (((_inner_sumSieve vu) :>sieve_) o>functor_ (_factor_interSieve (_outer_sumSieve vu))).
unshelve eexists; cycle 1.
 refine (_whole_interSieve (_outer_sumSieve vu)).
 refine (_inner_sumSieve vu).
- abstract(cbn_sieve; rewrite -> _wholeProp_interSieve;  rewrite -> _functorialCompos_functor'; reflexivity). }
- abstract (subst pullVV_; move; intros vu1 vu2 [outer_vu2 inner_vu2 Heq_outer_vu2 Heq_inner_vu2]; cbn_sieve; split; cbn_sieve;
[rewrite -> Heq_inner_vu2; rewrite -> (factor_interSieve_Proper Heq_outer_vu2); reflexivity | ];
constructor; cbn_sieve; [rewrite -> (whole_interSieve_Proper Heq_outer_vu2); reflexivity
| rewrite -> Heq_inner_vu2; reflexivity ]).
- abstract (intros K K' k vu; cbn_sieve; split;
first (cbn_sieve; tac_unsimpl; rewrite <- _natural_transf;
rewrite -> _functorialCompos_functor'; reflexivity);
cbn_sieve;  reflexivity).
- abstract(intros K vu; simpl; reflexivity).
Defined.

(* TODO: KEEEP FOR GENERAL VIEW OBJECT*)
Definition sumSieve_interSieve_image_general
 (U : vertexGene) (UU : sieveFunctor U)
 (H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
 (WW : sieveFunctor H)
(VV_ : forall object_ : vertexGene,
        'Sieve( object_ ~> _ | (interSieve UU (u :>sieve_) WW) ) -> sieveFunctor object_)
        (K : vertexGene) (w : 'Sieve( K ~> _ | WW )) :
sieveTransf (VV_ _ (w :>transf_ interSieve_image u WW)) (pullSieve (sumSieve VV_) (w :>sieve_) ) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros L. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists.
    (* _factor_interSieve *) exact: (v :>sieve_).
    (* _whole_interSieve *) unshelve eexists.
      * (* _object_sumSieve *) exact: K.
      * (* _outer_sumSieve *) exact (w :>transf_ interSieve_image u WW).
      * (* _inner_sumSieve *) exact: v.
    (* _wholeProp_interSieve *) abstract (cbn_sieve; reflexivity).
  (* _congr_relTransf  *) abstract (move; intros v1 v2 Heq_v; unshelve eexists; cbn_sieve;
  first (rewrite -> Heq_v; reflexivity);
   split; cbn_sieve; first reflexivity; last (rewrite -> Heq_v; reflexivity)).
- (*  _natural_transf  *) abstract (move; unshelve eexists; cbn_sieve; first (rewrite -> _natural_transf; reflexivity);
 reflexivity).
- (* _commute_sieveTransf *) abstract (move; intros; cbn_sieve; reflexivity).
Defined.

Definition sumSieve_interSieve_image
 (U : vertexGene) (UU : sieveFunctor U)
 (H : vertexGene) (u : 'Sieve( H ~> _ | UU ))
(VV_ : forall object_ : vertexGene,
        'Sieve( object_ ~> _ | (pullSieve UU (u :>sieve_) ) ) -> sieveFunctor object_) :
sieveTransf (VV_ _ (identGene :>transf_ interSieve_image u (identSieve _))) (sumSieve VV_) .
Proof. unshelve eexists. (* _transf_sieveTransf *)  unshelve eexists. 
- (* _arrows_transf *) intros K. unshelve eexists.
  (* _fun_relTransf *) intros v. unshelve eexists.
    * (* _object_sumSieve *) exact: H.
    * (* _outer_sumSieve *) exact: (identGene :>transf_ interSieve_image u (identSieve _)).
    * (* _inner_sumSieve *) exact: v.
  (* _congr_relTransf  *) abstract (move; intros v1 v2 Heq_v; unshelve eexists; cbn_sieve;
  first reflexivity; last (rewrite -> Heq_v; reflexivity)).
- (*  _natural_transf  *) abstract (move; unshelve eexists; cbn_sieve; reflexivity). 
- (* _commute_sieveTransf *) abstract (move; intros; cbn_sieve; (* TODO: HERE *)
exact: identGene_composGene).
Defined.

Definition imageSieve (U : vertexGene) (UU : sieveFunctor U) : (sieveFunctor U).
Proof. unshelve eexists.
{ (* functor *) unshelve eexists.
  - (* typeOf_objects_functor *) intros H. exact: (@compatRelType _ UU H).
  - (* _arrows_functor *)  move. intros H H'.
    (* relFunctor *) unshelve eexists.
    + (* -> *)  simpl. intros h u. exact: (h o>sieve_ u).
    + (* Proper *) abstract(move; cbn_transf;
    intros h1 h2 Heq_h u1 u2 Heq; rewrite -> Heq_h; move: Heq; unfold _rel_relType, equiv;
    simpl; intros Heq; do 2 rewrite <- _natural_transf; rewrite -> Heq; reflexivity).
  - (* typeOf_functorialCompos_functor *) abstract (intros H H' h H'' h' u;
    unfold _rel_relType, equiv; simpl;
    do 3 rewrite <- _natural_transf; exact: _functorialCompos_functor).
  - (* typeOf_functorialIdent_functor *) abstract(intros H u; unfold _rel_relType, equiv; simpl;
      rewrite <- _natural_transf; exact:  _functorialIdent_functor). }
{ (* transf *) unshelve eexists.
  - (* typeOf_arrows_transf *) intros H. unshelve eexists.
    + (* -> *) simpl. intros u. exact: (u :>sieve_). 
    + (* Proper *) abstract(move; cbn_transf;
                    intros u1 u2 Heq; exact: Heq).
  - (* typeOf_natural_transf *) abstract (move; cbn_transf; intros H H' h u;
    exact: _natural_transf).  }
Defined.

Inductive isCover : forall (U : vertexGene), (sieveFunctor U) -> Type :=

| BaseSieve_isCover : forall (U : vertexGene) (UU : sieveFunctor U) (UU_base : typeOf_baseSieve UU ),
    baseSieve UU_base -> isCover UU 

| IdentSieve_isCover : forall (G : vertexGene),
 isCover (identSieve G)
  
| InterSieve_isCover : forall (G : vertexGene) (VV : sieveFunctor G)
    (G' : vertexGene) (g : 'Gene( G' ~> G )) (UU : sieveFunctor G'),
     isCover  VV -> isCover (interSieve VV g UU)

| SumSieve_isCover : forall (G : vertexGene) (VV : sieveFunctor G)
(WP_ : forall (object_: vertexGene) (outer_: 'Sieve( object_ ~> G | VV )),
sieveFunctor object_),
   isCover VV ->
  (forall G' v, isCover (WP_ G' v)) -> isCover (sumSieve WP_).

Record type_Restrict (F : functor) (U : vertexGene) (UU : sieveFunctor U) 
(G : vertexGene) : Type :=
{ _indexer_type_Restrict : 'Gene( G ~> U ) ;
  _sieve_type_Restrict : sieveFunctor G;
 _data_type_Restrict :> transf (interSieve UU _indexer_type_Restrict _sieve_type_Restrict) F;
 _congr_type_Restrict : forall H (u1 u2 : 'Sieve(H ~> _| interSieve UU _indexer_type_Restrict _sieve_type_Restrict )), 
  _factor_interSieve u1 == _factor_interSieve u2 -> 
  u1 :>transf_ _data_type_Restrict  ==  u2 :>transf_ _data_type_Restrict }.

Record equiv_Restrict (F : functor) (U : vertexGene) (UU : sieveFunctor U) 
(G : vertexGene) (f1_ f2_: type_Restrict F UU G)  :=
{ _indexerEquiv_equiv_Restrict : _indexer_type_Restrict f1_ == _indexer_type_Restrict f2_ ;
  _sieveEquiv_equiv_Restrict : sieveEquiv (_sieve_type_Restrict f1_) (_sieve_type_Restrict f2_) ;
  _dataProp_equiv_Restrict : forall (H : vertexGene)
	(c : 'Sieve( H ~> _ | interSieve UU (_indexer_type_Restrict f1_) (_sieve_type_Restrict f1_)  )),
  c :>transf_ f1_ ==
  (c :>transf_ interSieve_congr (sieveTransf_Ident UU) _indexerEquiv_equiv_Restrict _sieveEquiv_equiv_Restrict)
  :>transf_ f2_ }.

Instance equiv_Restrict_Equivalence (F : functor) (U : vertexGene) (UU : sieveFunctor U) 
(G : vertexGene) : Equivalence (@equiv_Restrict F U UU G).
Proof. unshelve eexists.
* abstract(intros f1_ ; exists (reflexivity _) (reflexivity _) ; cbn_transf; intros K c;
rewrite -> _congr_relTransf; first reflexivity; split; simpl; reflexivity).
* abstract(intros f1_ f2_ [indexerEquiv_ sieveEquiv_ dataProp_]; exists (symmetry indexerEquiv_) (symmetry sieveEquiv_);
intros K c; rewrite -> dataProp_;
rewrite -> _congr_relTransf; first reflexivity; split; simpl; first rewrite -> _injProp_sieveEquiv; reflexivity).
* abstract(intros f1_ f2_ f3_  [indexerEquiv12 sieveEquiv12_ Heq12] [indexerEquiv23 sieveEquiv23_ Heq23];
exists (transitivity indexerEquiv12 indexerEquiv23)
(transitivity sieveEquiv12_ sieveEquiv23_) ;
intros K c; rewrite -> Heq12, Heq23;
rewrite -> _congr_relTransf; first reflexivity; split; simpl; reflexivity).
Qed.

Definition functor_Restrict (F : functor) (U : vertexGene) (UU : sieveFunctor U) : functor.
Proof. unshelve eexists.
- (* typeOf_objects_functor *) intros G.  unshelve eexists. exact (type_Restrict F UU G).
   (* relation *) exact (@equiv_Restrict F U UU G).
   (* Equivalence *) exact: equiv_Restrict_Equivalence.
- (* _arrows_functor *) intros H H'. unshelve eexists. 
  (* _fun_relFunctor *) simpl. intros h f_. unshelve eexists.
    (* _indexer_type_Restrict *) exact (h o>functor_[functor_ViewOb U] (_indexer_type_Restrict f_)).
    (* _sieve_type_Restrict *) exact (pullSieve (_sieve_type_Restrict f_) h).
    (* _data_type_Restrict *) exact (transf_Compos (interSieve_compos _ _ _ _ (identSieve _)) (_data_type_Restrict f_)).
    (* _congr_type_Restrict *) abstract(cbn_transf; intros K u1 u2 Heq_u;
      apply: _congr_type_Restrict; cbn_transf; rewrite -> (whole_interSieve_Proper Heq_u); reflexivity).
  (* _congr_relFunctor *) abstract(move; cbn_transf; intros h1 h2 Heq_h f1_ f2_  [indexerEquiv sieveEquiv_ Heq];
  unshelve eexists; first (cbn_transf; rewrite -> Heq_h, indexerEquiv; reflexivity);
  cbn_transf; first (exact: (pullSieve_congr_sieveEquiv sieveEquiv_ Heq_h));
  last intros K c; rewrite -> Heq; rewrite -> _congr_relTransf;
        first reflexivity; split; simpl; reflexivity).
- (* _functorialCompos_functor *) abstract (move; cbn_transf;
intros  G G' g G'' g' f_; unshelve eexists; first(cbn_transf;
rewrite -> _functorialCompos_functor'; reflexivity);
  first (cbn_transf; exact: pullSieve_pullSieve_sieveEquiv);
  last (cbn_transf; intros H c; rewrite -> _congr_relTransf;
        first reflexivity; split; cbn_transf; reflexivity)).
- (* _functorialIdent_functor *) abstract(move; cbn_transf; intros  G f_;
 unshelve eexists; first(cbn_transf;
rewrite -> _functorialIdent_functor; reflexivity);
  first (cbn_transf; exact: pullSieve_ident_sieveEquiv);
  last (cbn_transf; intros H c; rewrite -> _congr_relTransf;
        first reflexivity; split; cbn_transf; reflexivity)).
Defined.

Ltac tac_unsimpl ::= repeat
lazymatch goal with
| [ |- context [@fun_transf_ViewObMor ?G ?H ?g ?H' ?h] ] => 
change (@fun_transf_ViewObMor G H g H' h) with 
(h :>transf_ (transf_ViewObMor g))
| [ |- context [@fun_arrows_functor_ViewOb ?U ?V ?W ?wv ?vu] ] => 
change (@fun_arrows_functor_ViewOb U V W wv vu) with 
(wv o>functor_[functor_ViewOb U] vu)

(* no lack*)
| [ |- context [@equiv_rel_functor_ViewOb ?G ?H ?x ?y] ] =>  
 change (@equiv_rel_functor_ViewOb G H x y) with 
(@equiv _ _ (@_equiv_relType ( (functor_ViewOb G) H )) x y) 
| [ |- context [@equiv_Restrict ?F ?U ?UU ?H ?x ?y] ] =>  
 change (@equiv_Restrict F U UU H x y) with 
(@equiv _ _ (@_equiv_relType ( (@functor_Restrict F U UU) H )) x y) 
end.

Instance indexer_type_Restrict_Proper :
forall [F : functor] [U : vertexGene] [UU : sieveFunctor U] [G : vertexGene],
Proper (equiv ==> equiv) (@_indexer_type_Restrict F U UU G).
Proof.    intros. move. intros f1_ f2_ [indexerEquiv_ sieveEquiv_ Heq_f].
  exact: indexerEquiv_.
Qed.

(* TODO: note that ff and uu are never non-identity at the same time; \
so the grammatical transformation instead should be  transf_RestrictCast  *)
Definition transf_RestrictMor (F E : functor) 
(ff : transf F E) (U : vertexGene) (UU VV : sieveFunctor U)
(uu : sieveTransf VV UU) :
transf (functor_Restrict F UU) (functor_Restrict E VV).
Proof. intros. unshelve eexists.
- (* _arrows_transf *) intros H. unshelve eexists.
  + (* _fun_relTransf *) intros f_. unshelve eexists.
    * (* _indexer_type_Restrict *) exact: (_indexer_type_Restrict f_).
    * (* _sieve_type_Restrict *) exact: (_sieve_type_Restrict f_).
    * (* _data_type_Restrict *) exact (transf_Compos (interSieve_congr uu (reflexivity _) (sieveTransf_Ident _)) 
                                          (transf_Compos (_data_type_Restrict f_) ff)).
    * (* _congr_type_Restrict *) abstract (intros K u1 u2  Heq_u; cbn_transf; apply: _congr_relTransf;
      apply: _congr_type_Restrict; cbn_transf; rewrite -> Heq_u; reflexivity).
  + (* _congr_relTransf  *) abstract (move; intros f1_ f2_ [indexerEquiv sieveEquiv_ Heq]; unshelve eexists; cbn_transf;
  first exact: indexerEquiv; first exact: sieveEquiv_; 
  last intros K c;  cbn_transf; apply: _congr_relTransf; 
  rewrite -> Heq; apply: _congr_type_Restrict; cbn_transf; reflexivity).
- (* _natural_transf *) abstract (move; intros; unshelve eexists; cbn_transf;
first exact: (reflexivity _); first exact: (reflexivity _);
cbn_sieve; intros H c; apply: _congr_relTransf;
apply: _congr_type_Restrict; cbn_transf; reflexivity).
Defined.

Definition ident_functor_Restrict G (U : vertexGene) (UU : sieveFunctor U) (u: 'Sieve( G ~> _ | UU ))
: functor_Restrict (functor_ViewOb G) UU G.
Proof.  unshelve eexists. exact: (u :>sieve_). exact: (identSieve _). unshelve eexists.
- (* _arrows_transf *)  intros H. unshelve eexists.
  + (* _fun_relTransf *) intros g. exact: (g :>sieve_).
  + (* _congr_relTransf *) abstract(solve_proper).
- (* _natural_transf *) abstract (move; intros; cbn_transf; exact: _natural_transf).
- (* _congr_type_Restrict *) abstract (intros; cbn_sieve; assumption).
Defined.

Definition ident_functor_Restrict_natural G (U : vertexGene) (UU : sieveFunctor U)
 (u: 'Sieve( G ~> _ | UU )) G' (g:  'Gene( G' ~> G )):
g o>functor_ ident_functor_Restrict (u) ==
ident_functor_Restrict (g o>sieve_  u)
:>transf_ transf_RestrictMor (transf_ViewObMor g) (sieveTransf_Ident UU).
Proof.    unshelve eexists. cbn_transf; cbn_functor.
  rewrite <- _natural_transf. reflexivity.
  - cbn_sieve. exact: pullSieve_identSieve_sieveEquiv.
  - cbn_transf; intros H c. cbn_sieve. exact: (_wholeProp_interSieve (_factor_interSieve c)).
Qed.

Instance ident_functor_Restrict_Proper G U UU 
: Proper (equiv ==> equiv) (@ident_functor_Restrict G U UU).
Proof. move. intros u1 u2 Heq. unshelve eexists.
 - simpl. rewrite -> Heq; reflexivity.
 - cbn_sieve. reflexivity.
 - intros K c; reflexivity.
Qed.

Definition functor_Restrict_interSieve  (U : vertexGene) (UU : sieveFunctor U) 
(F : functor) G (g : 'Gene(G ~> U)) (VV : sieveFunctor G) 
(* (uv: sieveTransf (pullSieve UU g) VV) *) :
transf (functor_Restrict F VV) (functor_Restrict F UU).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros H. unshelve eexists.
  (* _fun_relTransf *) intros f_. { unshelve eexists. 
  - (* _indexer_type_Restrict *) exact: (_indexer_type_Restrict f_ o>functor_[functor_ViewOb _] g).
  - (* _sieve_type_Restrict *) exact: (interSieve VV (_indexer_type_Restrict f_) (_sieve_type_Restrict f_) ) .
  - (* _data_type_Restrict *) refine (transf_Compos (interSieve_projFactor _ _ _) (_data_type_Restrict f_)).
  - (* _congr_type_Restrict *) abstract (intros K u1 u2 Heq_u; cbn_transf;
    apply: _congr_type_Restrict; cbn_transf;  rewrite -> (factor_interSieve_Proper Heq_u); reflexivity). }
   (* _congr_relTransf  *) abstract(move; intros f1_ f2_ [indexerEquiv_ sieveEquiv_ Heq_];
    unshelve eexists; cbn_transf; 
    first abstract (rewrite -> indexerEquiv_; reflexivity);
    first exact: (interSieve_congr_sieveEquiv (reflexivity _) indexerEquiv_ sieveEquiv_);
    last intros K c; rewrite -> Heq_; apply: _congr_relTransf;
      split; cbn_transf; reflexivity).
- (*  _natural_transf  *) abstract (intros H' H h f_; unshelve eexists; cbn_sieve;
first (rewrite -> _functorialCompos_functor'; reflexivity);
first exact: interSieve_interSieve_sieveEquiv;
last intros K c; apply: _congr_relTransf; split; cbn_sieve;  reflexivity).
Defined. 

Record type_Sheafified (F : functor) 
(G : vertexGene) : Type :=
{ _sieve_type_Sheafified : sieveFunctor G ;
 _data_type_Sheafified :> transf _sieve_type_Sheafified F;
  _compat_type_Sheafified : forall (I : vertexGene), Proper ((@equiv _ _ (@_equiv_relType (compatRelType _ _)))
   ==> (@equiv _ _ (@_equiv_relType _))) (_arrows_transf _data_type_Sheafified I) }.

Record equiv_Sheafified (F : functor) 
(G : vertexGene) (f1_ f2_: type_Sheafified F G)  :=
{ conflSieve_Sheafified : sieveFunctor G  ;
 conflTransf1_Sheafified : sieveTransf conflSieve_Sheafified (_sieve_type_Sheafified f1_) ;
 conflTransf2_Sheafified : sieveTransf conflSieve_Sheafified (_sieve_type_Sheafified f2_) ;
 conflEquiv_Sheafified : forall (J : vertexGene) (c : 'Sieve( J ~> _ | conflSieve_Sheafified )),
  (c :>transf_ conflTransf1_Sheafified) :>transf_ (_data_type_Sheafified f1_) ==
  (c :>transf_ conflTransf2_Sheafified) :>transf_ (_data_type_Sheafified f2_) }.

Instance equiv_Sheafified_Equivalence (F : functor) 
(G : vertexGene) : Equivalence (@equiv_Sheafified F G).
Proof. unshelve eexists.
- abstract (intros f1_ ; eexists (_sieve_type_Sheafified f1_) (sieveTransf_Ident _) (sieveTransf_Ident _); reflexivity).
- abstract (intros f1_ f2_ [conflSieve conflTransf1 conflTransf2 Heq];
    exists conflSieve conflTransf2 conflTransf1; symmetry; exact: Heq). 
- abstract (intros f1_ f2_ f3_  [conflSieve12 conflTransf1 conflTransf2 Heq12]
[conflSieve23 conflTransf2' conflTransf3 Heq23];
exists (meetSieve conflSieve12 conflSieve23)
 (sieveTransf_Compos (meetSieve_projWhole _ _) conflTransf1)
 (sieveTransf_Compos (meetSieve_projFactor _ _) conflTransf3);
intros H c; cbn_sieve; tac_unsimpl; rewrite -> Heq12; rewrite <- Heq23;
apply _compat_type_Sheafified; move; rewrite -/(equiv _ _); rewrite -> _commute_sieveTransf; rewrite -> _commute_sieveTransf;
rewrite -> _wholeProp_interSieve; (* FUNCTOR/TRANSF PROBLEM *) exact: identGene_composGene).
Qed.

Definition functor_Sheafified (F : functor) : functor.
Proof. unshelve eexists.
- (* typeOf_objects_functor *) intros G. unshelve eexists. exact (type_Sheafified F G).
  + (* relation *) exact (@equiv_Sheafified F G).
  + (* Equivalence *) exact: equiv_Sheafified_Equivalence.
- (* _arrows_functor *) intros H H'. unshelve eexists. 
  (* _fun_relFunctor *) simpl. intros h f_. unshelve eexists.
  exact: (pullSieve (_sieve_type_Sheafified f_) h).
  exact (transf_Compos (pullSieve_projWhole _ _) (_data_type_Sheafified f_)).
  abstract(intros I v v' Heq;  cbn_transf; apply: _compat_type_Sheafified;
  move: Heq; unfold  _rel_relType, equiv; simpl; intros Heq;
  do 2 rewrite -> _wholeProp_interSieve; rewrite -> Heq; reflexivity).
  (* _congr_relFunctor *) abstract(move; simpl; intros h1 h2 Heq_h f1_ f2_ 
  [conflSieve12 conflTransf1 conflTransf2 Heq12]; simpl;
  exists (pullSieve conflSieve12 h1)
    (pullSieve_congr conflTransf1 (reflexivity _) )
    (pullSieve_congr conflTransf2 Heq_h );
  intros K c; cbn -[_rel_relType]; rewrite -> Heq12; reflexivity).
- (* _functorialCompos_functor *) abstract(move; simpl; intros  G G' g G'' g' f_;
  unshelve eexists;
 first exact (pullSieve (pullSieve ((_sieve_type_Sheafified f_)) g) g'); 
 first exact  (sieveTransf_Ident _ );
 first (simpl; exact (pullSieve_pullSieve _ _ _)); 
   intros K c; simpl; tac_unsimpl; reflexivity). 
- (* _functorialIdent_functor *) abstract(move; simpl; intros G f_; unshelve eexists;
 first exact (pullSieve (_sieve_type_Sheafified f_) identGene); simpl;
 first exact  (sieveTransf_Ident _ );
 first exact (pullSieve_ident _ );
  intros K c; simpl; tac_unsimpl; reflexivity).
Defined.

Ltac tac_unsimpl ::= repeat
lazymatch goal with
| [ |- context [@fun_transf_ViewObMor ?G ?H ?g ?H' ?h] ] => 
change (@fun_transf_ViewObMor G H g H' h) with 
(h :>transf_ (transf_ViewObMor g))
| [ |- context [@fun_arrows_functor_ViewOb ?U ?V ?W ?wv ?vu] ] => 
change (@fun_arrows_functor_ViewOb U V W wv vu) with 
(wv o>functor_[functor_ViewOb U] vu)

(* no lack*)
| [ |- context [@equiv_rel_functor_ViewOb ?G ?H ?x ?y] ] =>  
 change (@equiv_rel_functor_ViewOb G H x y) with 
(@equiv _ _ (@_equiv_relType ( (functor_ViewOb G) H )) x y) 
| [ |- context [@equiv_Restrict ?F ?U ?UU ?H ?x ?y] ] =>  
 change (@equiv_Restrict F U UU H x y) with 
(@equiv _ _ (@_equiv_relType ( (@functor_Restrict F U UU) H )) x y) 
| [ |- context [@equiv_Sheafified ?F ?U ?UU ?H ?x ?y] ] =>  
 change (@equiv_Sheafified F U UU H x y) with 
(@equiv _ _ (@_equiv_relType ( (@functor_Sheafified F U UU) H )) x y) 
end.
 
Definition relation_transf (F E : functor) : crelation (transf F E).  (* in context of assuming congr *)
intros ee1 ee2. exact (forall G (f1 f2 : F G), f1 == f2 -> f1 :>transf_ ee1 == f2 :>transf_ ee2).
Defined. 

Instance equiv_transf (F E : functor) : Equivalence (@relation_transf F E).
unshelve eexists;
first (move; intros; move; intros ? ? ? ->; reflexivity);
first (move; intros ? ? Heq; move; intros; symmetry; apply: Heq; symmetry; assumption);
 move; intros ? ? ? Heq1 Heq2; move; intros; etransitivity;
   [apply:Heq1; eassumption
    | apply: Heq2; reflexivity].
Qed.

Definition rel_transf (F E : functor) : relType.
exists (transf F E) (@relation_transf F E). exact (@equiv_transf F E).
Defined.

Definition transf_RestrictMor_pullSieve
 (U : vertexGene) (UU : sieveFunctor U)  (F : functor) (G : vertexGene)
(f_: functor_Restrict F UU G) (G' : vertexGene) (g: 'Gene( G' ~> G)) :
functor_Restrict F (pullSieve UU (g o>gene _indexer_type_Restrict f_ )) G'.
Proof. 
  unshelve eexists. 
  - exact: (@identGene G').
  - exact: (pullSieve (_sieve_type_Restrict f_) g).
  -  refine (transf_Compos (interSieve_composeOuter_ident _ _ _ _) (_data_type_Restrict f_)).
  - abstract (intros H u1 u2 Heq_u; cbn_transf; apply: _congr_type_Restrict;
     rewrite -> (whole_interSieve_Proper Heq_u); reflexivity).
Defined.

Section Gluing_typeOf.

Variables (U : vertexGene) (UU : sieveFunctor U) (UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H).

Definition typeOf_sieveCongr :=
  forall (object_ : vertexGene)
  (outer_ outer_' : 'Sieve( object_ ~> _ | UU )),
outer_  == outer_' ->
sieveEquiv (VV_  outer_) (VV_  outer_').

Definition typeOf_sieveNatural :=
  forall (object_ : vertexGene)
  (outer_ : 'Sieve( object_ ~> _ | UU )) 
  (K : vertexGene) (w : 'Gene( K ~> object_ )),
(* TODO: sieveEquiv? *) sieveTransf (VV_  (w o>sieve_ outer_))
  (pullSieve (VV_  outer_) w).

Variables (VV_congr : typeOf_sieveCongr)
  (VV_natural : typeOf_sieveNatural)   (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
        transf (functor_Restrict F (VV_ u)) (functor_Sheafified E)).

Definition typeOf_gluingCongr :=
forall (H : vertexGene) (u1 u2 : 'Sieve( H ~> _ | UU )) 
  (K : vertexGene) (f1_ : functor_Restrict F (VV_  u1) K)
  (f2_ : functor_Restrict F (VV_  u2) K) (Hequ : u1 == u2)
(Heq_f : f1_ == f2_ :>transf_ transf_RestrictMor (transf_Ident F) (VV_congr Hequ) ),
  (f1_ :>transf_ ee_  u1) == (f2_ :>transf_ ee_  u2).

Definition typeOf_gluingNatural  :=
forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )) 
  (K : vertexGene) (f_ : functor_Restrict F (VV_ u) K) 
  (K' : vertexGene) (k : 'Gene( K' ~> K )),
k o>functor_ (f_ :>transf_ ee_ u) ==
(transf_RestrictMor_pullSieve f_ k
  :>transf_ transf_RestrictMor (transf_Ident F)
              (VV_natural u  (k o>gene _indexer_type_Restrict f_)))
:>transf_ ee_ ((k o>gene _indexer_type_Restrict f_) o>sieve_ u).

Definition typeOf_gluingCompat  :=
forall (H1 : vertexGene) (u1 : 'Sieve( H1 ~> _ | UU )) 
(K1 : vertexGene) (f1_ : functor_Restrict F (VV_ u1) K1)
(H2 : vertexGene) (u2 : 'Sieve( H2 ~> _ | UU )) 
(K2 : vertexGene) (f2_ : functor_Restrict F (VV_ u2) K2) 
(I : vertexGene)
(w1 : 'Sieve( I ~> K1 | _sieve_type_Sheafified (f1_ :>transf_ ee_ u1) ))
(w2 : 'Sieve( I ~> K2 | _sieve_type_Sheafified (f2_ :>transf_ ee_ u2) ))
(Heq_wu : ((w1 :>sieve_) o>functor_[functor_ViewOb _] _indexer_type_Restrict f1_) o>functor_ u1 
      ==  ((w2 :>sieve_) o>functor_[functor_ViewOb _] _indexer_type_Restrict f2_) o>functor_ u2 )
(Heq_f_ : ( (transf_RestrictMor_pullSieve f1_ (w1 :>sieve_)) 
                    :>transf_ transf_RestrictMor (transf_Ident _) (VV_natural  _  _ ) )
      == ( (transf_RestrictMor_pullSieve f2_ (w2  :>sieve_)) 
              :>transf_ transf_RestrictMor (transf_Ident _) (VV_natural  _ _ ) )  
          :>transf_ transf_RestrictMor (transf_Ident _) (VV_congr   Heq_wu) ),
    w1 :>transf_ (f1_ :>transf_ ee_  u1) ==
    w2 :>transf_ (f2_ :>transf_ ee_  u2).

Lemma gluingNatural_identGene_of_gluingNatural 
(ee_natural : typeOf_gluingNatural) : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )) 
(K : vertexGene) (f_ : functor_Restrict F (VV_  u) K) ,
(f_ :>transf_ ee_  u) ==
(transf_RestrictMor_pullSieve f_ identGene
:>transf_ transf_RestrictMor (transf_Ident F)
           (VV_natural  u  (identGene o>gene _indexer_type_Restrict f_)))
:>transf_ ee_  ((identGene o>gene _indexer_type_Restrict f_) o>sieve_ u).
Proof. intros. etransitivity. symmetry; apply: _functorialIdent_functor.
etransitivity. apply: ee_natural. reflexivity.
Qed.

End Gluing_typeOf. 

Definition transf_Gluing_lemma :
forall (U : vertexGene) (UU : sieveFunctor U) 
(VV_ : forall (H: vertexGene) (outer_: 'Sieve( H ~> U | UU )), sieveFunctor H)
(F : functor)
(G: vertexGene)
(f_: functor_Restrict F (sumSieve VV_) G)
(H: vertexGene)
(u: 'Sieve( H ~> _ | interSieve UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_) )),
functor_Restrict F
  (VV_ H (u :>transf_ interSieve_projWhole UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_))) H.
Proof. unshelve eexists.
- (* _indexer_type_Restrict *) exact: (@identGene H).
- (* _sieve_type_Restrict *) exact: (pullSieve (_sieve_type_Restrict f_) (u :>sieve_) ).
- (* _data_type_Restrict *)
(* transf
  (interSieve (VV_ H (u :>transf_ interSieve_projWhole UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_)))
     identGene (pullSieve (_sieve_type_Restrict f_) (u :>sieve_))) F *)
refine (transf_Compos _ (_data_type_Restrict f_)).
refine (transf_Compos (interSieve_congr (sumSieve_sectionPull _ _) (reflexivity _) (sieveTransf_Ident _)) _).
refine (transf_Compos (interSieve_congr 
  (pullSieve_congr (sieveTransf_Ident _) (_wholeProp_interSieve u))
  (reflexivity _) (sieveTransf_Ident _)) _).
exact: interSieve_composeOuter_ident.

- (* _congr_type_Restrict *) abstract (intros K v1 v2 Heq_v;
cbn_transf; apply: _congr_type_Restrict; cbn_transf;
rewrite -> (whole_interSieve_Proper Heq_v); reflexivity).
Defined.

Arguments transf_Gluing_lemma [_ _ _ _ _] f_ [_] u.

Definition transf_Gluing :
forall (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
(VV_congr : typeOf_sieveCongr VV_)
(VV_natural : typeOf_sieveNatural VV_) 
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
         transf (functor_Restrict F (VV_ H u)) (functor_Sheafified E))
  (ee_congr : typeOf_gluingCongr VV_congr ee_)
(* ee_natural used in code only not sense *)
(ee_natural : typeOf_gluingNatural VV_natural ee_) 
(ee_compat : typeOf_gluingCompat VV_congr VV_natural ee_),
transf (functor_Restrict F (sumSieve VV_)) (functor_Sheafified E).
Proof. unshelve eexists.
- (* _arrows_transf *)  intros G. unshelve eexists.
  + (* _fun_relTransf *) intros f_. unshelve eexists.
    * { (* _sieve_type_Sheafified *) 
      - (* sieveFunctor G *) refine (@sumSieve G  (interSieve UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_) ) _).
      - (* sieveFunctor H *) intros H u. refine (_sieve_type_Sheafified ( _ :>transf_ ee_ H (u :>transf_ interSieve_projWhole _ _ _) )).
      - (* functor_Restrict F (VV_ H (u :>transf_ interSieve_projWhole UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_))) H *)
        exact: transf_Gluing_lemma. } 
    * { (* _data_type_Sheafified *) unshelve eexists.
          + (* _arrows_transf *)  intros H. unshelve eexists.
            * (* _fun_relTransf *) intros wu.
            refine ( (_inner_sumSieve wu) :>transf_ (_data_type_Sheafified ( (transf_Gluing_lemma _ (_outer_sumSieve wu)) 
                :>transf_ ee_ _ ((_outer_sumSieve wu) :>transf_ interSieve_projWhole _ _ _) )) ).
            * (* _congr_relTransf *) abstract(move; cbn_sieve;
            intros wu1 wu2 [outer_wu2 inner_wu2 Heq_outer_wu2 Heq_inner_wu2]; cbn_sieve;
            unshelve apply: ee_compat;
            first abstract (cbn_; rewrite -> Heq_outer_wu2 , Heq_inner_wu2; reflexivity);
            cbn_; unshelve eexists; first reflexivity;
            [ cbn_transf; refine (pullSieve_congr_sieveEquiv (pullSieve_congr_sieveEquiv (reflexivity _) _) _);
              first abstract (rewrite -> Heq_outer_wu2; reflexivity);
              abstract (rewrite -> Heq_inner_wu2; reflexivity)
            |  (* no use _congr_type_Restrict *)  (cbn_transf; intros K c; 
              apply: _congr_relTransf; cbn_transf; 
              split; cbn_transf; first reflexivity;
              split; cbn_transf; first  (rewrite -> Heq_outer_wu2; reflexivity);
              rewrite -> _wholeProp_interSieve, transf_interSieve_Eq, _commute_sieveTransf, _commute_sieveTransf; 
              rewrite -> _wholeProp_interSieve, transf_interSieve_Eq, _commute_sieveTransf;
              rewrite -> Heq_inner_wu2; reflexivity) ]).
          + (* _natural_transf *) abstract(move; intros H H' h u;  cbn_sieve; rewrite -> _natural_transf; reflexivity). }
    * (* _compat_type_Sheafified *) { abstract(intros I wu1 wu2 Heq_wu; cbn_transf; unshelve apply: ee_compat; 
      [ abstract(apply: UU_base; move: Heq_wu; unfold equiv, _rel_relType, compatRelType; cbn_sieve; intros Heq_wu;
      (* HERE *) simpl (_ o>functor_[functor_ViewOb _] (@identGene _)); do 2 rewrite -> identGene_composGene;
      do 2 rewrite <- _natural_transf; do 2 rewrite -> _wholeProp_interSieve;
      do 2 rewrite -> _functorialCompos_functor'; rewrite -> Heq_wu; reflexivity)
      | unshelve eexists; cbn -[equiv _type_relType _rel_relType _equiv_relType _objects_functor _arrows_functor functor_ViewOb
              transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor transf_Gluing_lemma];
        [ abstract (reflexivity)
        | cbn_transf; etransitivity; first exact: pullSieve_pullSieve_sieveEquiv;
          etransitivity; last (symmetry; exact: pullSieve_pullSieve_sieveEquiv);
          refine (pullSieve_congr_sieveEquiv (reflexivity _) _); exact: Heq_wu
        | abstract (cbn_transf;
          intros H c; cbn_transf;
          apply: _congr_type_Restrict; cbn_transf; reflexivity) ] ]). }
    + (* _congr_relTransf  *) abstract (intros f1_ f2_ [indexerEquiv_ sieveEquiv_ dataProp_]; cbn_transf;
      pose l_  := fun (H : vertexGene)
         (u1 : 'Sieve( H ~> _ | interSieve UU (_indexer_type_Restrict f1_) (_sieve_type_Restrict f1_) )) =>
         (transf_Gluing_lemma _ u1 :>transf_ ee_ H (_whole_interSieve u1));
      pose r_  := fun (H : vertexGene)
         (u1 : 'Sieve( H ~> _ | interSieve UU (_indexer_type_Restrict f1_) (_sieve_type_Restrict f1_) )) =>
        (transf_Gluing_lemma _ (u1 :>transf_ interSieve_congr (sieveTransf_Ident UU) indexerEquiv_ sieveEquiv_)
        :>transf_ ee_ H (_whole_interSieve (u1 :>transf_ interSieve_congr (sieveTransf_Ident UU) indexerEquiv_ sieveEquiv_)));
      have ee_congr' : forall H u1,
        l_ H u1 == r_ H u1;
      first abstract (intros; unshelve apply: ee_congr; intros;
        [ reflexivity
        | (* HERE LEMMA for transf_Gluing_lemma *) unshelve eexists; cbn_transf;
          [ reflexivity
          | refine (pullSieve_congr_sieveEquiv sieveEquiv_ _);
            cbn_sieve; rewrite -> _commute_sieveTransf; reflexivity
          | intros K c; rewrite -> dataProp_; apply: _congr_relTransf; split; cbn_transf;
            [ reflexivity
            | split; cbn_transf; first reflexivity; rewrite -> _commute_sieveTransf; reflexivity ] ] ]);
      unshelve eexists;
      first exact: (sumSieve (fun H u => conflSieve_Sheafified (ee_congr' H u)));
      first (cbn_transf;
        refine (sumSieve_congr (uu := sieveTransf_Ident _)
        (VV1_ := (fun H u => conflSieve_Sheafified (ee_congr' H u))) 
        (VV2_ := (fun H u => _sieve_type_Sheafified (l_ H u))) 
        (fun H u => conflTransf1_Sheafified (ee_congr' H u)) ));
      first (cbn_transf;
        refine (sieveTransf_Compos
          (sumSieve_congr (uu := sieveTransf_Ident _)
          (VV1_ := (fun H u => conflSieve_Sheafified (ee_congr' H u))) 
          (VV2_ := (fun H u => _sieve_type_Sheafified (r_ H u))) 
          (fun H u => conflTransf2_Sheafified (ee_congr' H u)) ) _ );
        refine (@sumSieve_congr _ _ _ 
          (interSieve_congr (sieveTransf_Ident _) indexerEquiv_ sieveEquiv_ )
          _ _ ( fun H u1 => sieveTransf_Ident _ ) ));
      abstract(intros J c; cbn_transf; exact: conflEquiv_Sheafified)). 

- (* _natural_transf *) abstract(intros G; intros G' g f_; cbn_; cbn_transf;
pose l_  := fun (H : vertexGene) (u : 'Sieve( H ~> _ | 
    interSieve UU (_indexer_type_Restrict (g o>functor_ f_)) (_sieve_type_Restrict (g o>functor_ f_)) )) =>
transf_Gluing_lemma _ u :>transf_ ee_ H (_whole_interSieve u);
pose r_  := fun (H : vertexGene) (u : 'Sieve( H ~> _ | 
    interSieve UU (_indexer_type_Restrict (g o>functor_ f_)) (_sieve_type_Restrict (g o>functor_ f_)) )) =>
transf_Gluing_lemma _ (u :>transf_ 
    interSieve_compos UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_) g (identSieve _) )
:>transf_ ee_ H (_whole_interSieve (u :>transf_ 
  interSieve_compos UU (_indexer_type_Restrict f_) (_sieve_type_Restrict f_) g (identSieve _) ));

have Heq_inner:  forall (H : vertexGene) (u : 'Sieve( H ~> _ | 
    interSieve UU (_indexer_type_Restrict (g o>functor_ f_)) (_sieve_type_Restrict (g o>functor_ f_)) )),
l_ H u == r_ H u;
first  (intros; subst l_ r_; cbn_transf; apply: _congr_relTransf;
(* HERE LEMMA for transf_Gluing_lemma *) unshelve eexists; first (cbn_transf; reflexivity);
  [ cbn_transf; cbn_sieve;
    etransitivity; first exact: (pullSieve_pullSieve_sieveEquiv (reflexivity _) _ _);
    refine (pullSieve_congr_sieveEquiv (reflexivity _) _);
      abstract (rewrite -> _wholeProp_interSieve; reflexivity)
  | intros K c; cbn_transf; cbn_sieve; apply: _congr_relTransf;
   split; cbn_sieve; reflexivity]);

unshelve eexists;
first exact: (sumSieve (fun H u => conflSieve_Sheafified (Heq_inner H u)));
only 2: (cbn -[_indexer_type_Restrict functor_Restrict  ];
  refine (sumSieve_congr (uu := sieveTransf_Ident _)
  (VV1_ := (fun H u => conflSieve_Sheafified (Heq_inner H u))) 
  (VV2_ := (fun H u => _sieve_type_Sheafified (l_ H u))) 
  (fun H u => conflTransf1_Sheafified (Heq_inner H u)) )); 
first (cbn -[_indexer_type_Restrict functor_Restrict  ];
refine (sieveTransf_Compos (sumSieve_congr (uu := sieveTransf_Ident _)
                      (VV1_ := (fun H u => conflSieve_Sheafified (Heq_inner H u))) 
                      (VV2_ := (fun H u => _sieve_type_Sheafified (r_ H u))) 
                      (fun H u => conflTransf2_Sheafified (Heq_inner H u)) ) _);
simpl (_indexer_type_Restrict _);
exact (sumSieve_interSieve'  _ _  ));
last intros J c; cbn_sieve; subst l_ r_; rewrite -> conflEquiv_Sheafified; reflexivity).
Defined.

Definition transf_RestrictCast (F E : functor) 
 (ff : transf F E) (U : vertexGene) (UU  : sieveFunctor U)
 (UU_base: typeOf_baseSieve UU)
 (V : vertexGene) (vu : 'Sieve(V ~> U | UU)) ( VV : sieveFunctor V)
 (VV_base: typeOf_baseSieve VV) :
 transf (functor_Restrict F VV) (functor_Restrict E UU).
Proof.    intros. refine (transf_Compos (transf_RestrictMor ff (sieveTransf_Ident _))
  (functor_Restrict_interSieve _ _ (vu :>sieve_) _)).  
(* intros. refine (transf_Compos (transf_RestrictMor ff (interSieve_projFactor _  (vu :>sieve_) _ ))
(functor_Restrict_interSieve _ _ (vu :>sieve_) _)). *)
Defined.

Definition transf_SheafifiedMor (F E : functor) (ee : transf F E) :
  transf (functor_Sheafified F) (functor_Sheafified E).
Proof. unshelve eexists.
- (* _arrows_transf *) intros H. unshelve eexists.
  + (* _fun_relTransf *) intros f_. unshelve eexists.
    * (* _sieve_type_Sheafified *) exact: (_sieve_type_Sheafified f_).
    * (* _data_type_Sheafified *) exact: (transf_Compos (_data_type_Sheafified f_) ee).
    * (* _compat_type_Sheafified *) abstract (intros K u1 u2  Heq_u; cbn_transf; apply: _congr_relTransf;
      apply: _compat_type_Sheafified; cbn_transf; rewrite -> Heq_u; reflexivity).
  + (* _congr_relTransf  *) abstract (move; intros f1_ f2_ 
  [conflSieve_ conflTransf1_ conflTransf2_ conflEquiv_]; 
  unshelve eexists; cbn_transf;
  first exact: conflSieve_; first exact: conflTransf1_;  first exact: conflTransf2_; 
  last intros K c;  cbn_transf; apply: _congr_relTransf; 
  rewrite -> conflEquiv_; apply: _compat_type_Sheafified; cbn_transf; reflexivity).
- (* _natural_transf *) abstract (move; intros; unshelve eexists; cbn_transf;
first shelve; first exact: (sieveTransf_Ident _);  first exact: (sieveTransf_Ident _);
cbn_sieve; intros H c; apply: _congr_relTransf;
apply: _compat_type_Sheafified; cbn_transf; reflexivity).
Defined.

Section Destructing_typeOf.
Variables (U : vertexGene) (UU : sieveFunctor U).
Variables (UU_base: typeOf_baseSieve UU).
Variables  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf  (functor_ViewOb H)  E).

Definition typeOf_destructCongr :=
  forall H, Proper ((@equiv _ _  (@_equiv_relType _)) ==> equiv ==>
   (@equiv _ _  (@_equiv_relType (@rel_transf _ _)))  ) (@ee_ H).

Definition typeOf_destructNatural  :=
forall (G : vertexGene) (u : 'Sieve(G ~> _ | UU)) (form : F G) (H : vertexGene)
  (f : (functor_ViewOb G) H)
  (G' : vertexGene) (g : 'Gene( G' ~> G ))
  u' form' f',
  (g o>functor_ u) == u' ->
  (g o>functor_ form) == form' ->
  f == f' :>transf_ (transf_ViewObMor g)  ->
f :>transf_ ee_  u form == f' :>transf_ ee_  u' form'.

End Destructing_typeOf. 
 
Definition transf_Destructing_preCast :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU )
(F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf (functor_ViewOb H) E)
(ee_congr : typeOf_destructCongr ee_)
(ee_natural : typeOf_destructNatural ee_),
transf (functor_Restrict F UU) (functor_Restrict E UU).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros G. unshelve eexists.
  (* _fun_relTransf *) intros f_. { unshelve eexists. 
    - (* _indexer_type_Restrict *) exact: (_indexer_type_Restrict f_).
    - (* _sieve_type_Restrict *) exact:  (_sieve_type_Restrict f_)  .
    - { (* _data_type_Restrict *) unshelve eexists.
        + (* _arrows_transf *)  intros H. unshelve eexists.
          * (* _fun_relTransf *) intros u.  exact: (identGene
        :>transf_ ee_ H (u :>transf_ interSieve_projWhole _ _ _) (u :>transf_ f_)).
          * (* _congr_relTransf *) abstract (move; intros u1 u2 Heq; cbn_transf; cbn_functor;
          rewrite -> ee_congr; first reflexivity;
           first (rewrite -> (whole_interSieve_Proper Heq); reflexivity);
           first (rewrite -> Heq; reflexivity);
           last reflexivity).
          (* abstract(move; intros u1 u2 Heq; cbn_transf; cbn_functor;
          apply: ee_congr; rewrite -> Heq; reflexivity). *)
        + (* _natural_transf *) abstract(move; intros H H' h u; cbn_transf;
        rewrite -> _natural_transf; setoid_rewrite <- ee_natural at 2; first reflexivity;
        first (cbn_sieve; reflexivity);
        first (rewrite <- _natural_transf; reflexivity); etransitivity;
        first (exact:identGene_composGene ); symmetry; exact: composGene_identGene). }
    - (* _congr_type_Restrict *) abstract (intros I v v' Heq; cbn_transf;
    have Heq_whole : _whole_interSieve v == _whole_interSieve v'; 
      first (apply UU_base; move: Heq; unfold  _rel_relType, equiv; simpl; 
        intros Heq; do 2 rewrite -> _wholeProp_interSieve; rewrite -> Heq; reflexivity);
    apply: ee_congr;
    first (rewrite -> Heq_whole; reflexivity);
    first (apply: _congr_type_Restrict; exact Heq); reflexivity).  }
  (* _congr_relTransf  *) abstract(move; intros f1_ f2_ [indexerEquiv sieveEquiv_ Heq];
  unshelve eexists; cbn_sieve;
  first (rewrite -> indexerEquiv; reflexivity);
  first exact: sieveEquiv_;
  last intros J c; cbn_sieve; apply: ee_congr; cbn_sieve; first reflexivity; last reflexivity;
    rewrite -> Heq; apply: _congr_relTransf; split; cbn_sieve; reflexivity).
- (*  _natural_transf  *) abstract(intros H' H h f_; unshelve eexists; cbn_sieve;
  first reflexivity; first reflexivity; 
  first (intros K c; cbn_sieve;
  apply: ee_congr; first reflexivity; last reflexivity;
  apply: _congr_relTransf; split; cbn_sieve;  reflexivity)).
Defined.

Definition transf_UnitSheafified_prePoly_preCast :
forall (F : functor),
transf  F  (functor_Sheafified F).
Proof. unshelve eexists.
- (* _arrows_transf *)  intros G. unshelve eexists.
  + (* _fun_relTransf *) intros f_. unshelve eexists.
    * (* _sieve_type_Sheafified *) exact: (identSieve _).
    * { - (* _data_type_Sheafified *) unshelve eexists.
          + (* _arrows_transf *)  intros H. unshelve eexists.
            * (* _fun_relTransf *) intros u. exact: (u o>functor_ f_).
            * (* _congr_relTransf *)  abstract(move; intros u1 u2 Heq; cbn -[functor_Restrict];
            tac_unsimpl; rewrite -> Heq; reflexivity).
          + (* _natural_transf *) abstract(move; intros H H' h u;  cbn -[functor_Restrict];
          tac_unsimpl; rewrite -> _functorialCompos_functor'; reflexivity).  }
       * (* _compat_type_Sheafified *) abstract(intros I v v'; simpl; intros Heqs; rewrite -> Heqs; reflexivity).
  + (* _congr_relTransf  *) abstract(move; intros f1_ f2_ Heq; unshelve eexists; cycle 1;
  first exact (sieveTransf_Ident _); first exact (sieveTransf_Ident _);
  intros K c; cbn -[functor_Restrict]; tac_unsimpl; rewrite -> Heq; reflexivity).
- (* _natural_transf *) abstract(move; intros G G' g f_; cbn_transf; cbn_functor;
unshelve eexists; cycle 1; first exact (sieveTransf_Ident _); first exact (sieveTransf_identSieve _);
cbn_transf; cbn_functor; intros K c;  rewrite -> _functorialCompos_functor';
apply: _congr_relFunctor; last reflexivity;
apply: (_wholeProp_interSieve c)).
Defined.

Definition transf_Destructing
 (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU )
(F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf (functor_ViewOb H) E)
(ee_congr : typeOf_destructCongr ee_)
(ee_natural : typeOf_destructNatural ee_)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) )  :
transf (functor_Restrict F UU) (functor_Sheafified (functor_Restrict E VV)).
Proof. 
  refine (transf_Compos (transf_Destructing_preCast UU_base ee_congr ee_natural) _).
  refine (transf_Compos (transf_RestrictCast  (transf_Ident _) VV_base uv UU_base) _).  
  exact: (transf_UnitSheafified_prePoly_preCast _).
Defined.

Definition transf_Constructing (* AKA UnitRestrict *)
 (U : vertexGene) (UU : sieveFunctor U) 
(F  : functor)
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(form : F K) :
transf (functor_ViewOb K)  (functor_Restrict F UU).
Proof.  unshelve eexists. 
- (* _arrows_transf *) intros G. unshelve eexists.
  (* _fun_relTransf *) intros f_. { unshelve eexists. 
    - (* _indexer_type_Restrict *) exact: ((f_ o>functor_ u) :>sieve_).
    - (* _sieve_type_Restrict *) exact:  (identSieve _).
    - { (* _data_type_Restrict *) unshelve eexists.
        + (* _arrows_transf *)  intros H. unshelve eexists.
          * (* _fun_relTransf *) intros u'. refine (( (_factor_interSieve u') o>functor_ f_ ) o>functor_ form).
          * (* _congr_relTransf *) 
          abstract (move; intros u1 u2 Heq; cbn_sieve; rewrite -> (factor_interSieve_Proper Heq); reflexivity).
        + (* _natural_transf *) abstract(move; intros H H' h u'; cbn_transf;
        do 2 rewrite -> _functorialCompos_functor';  reflexivity). }
    - (* _congr_type_Restrict *) abstract (intros I v v' Heq; cbn_transf;
    rewrite -> Heq; reflexivity).  }
  (* _congr_relTransf  *) abstract (move; intros f1_ f2_ Heq;
    unshelve eexists; cbn_sieve;
    first (rewrite -> Heq; reflexivity);
    first reflexivity;
    last intros J c; cbn_sieve; rewrite -> Heq; reflexivity).
- (*  _natural_transf  *) abstract(intros H' H h f_; unshelve eexists; cbn_sieve;
first (rewrite <- _functorialCompos_functor'; setoid_rewrite <- _natural_transf at 2; reflexivity);
first exact: pullSieve_identSieve_sieveEquiv;
last intros K0 c; cbn_transf;
apply: _congr_relFunctor; last reflexivity;
 rewrite -> _functorialCompos_functor';
apply: _congr_relFunctor; last reflexivity;
 apply: (_wholeProp_interSieve (_factor_interSieve c))).
Defined.

Definition transf_UnitSheafified
 (U : vertexGene) (UU : sieveFunctor U) 
 (UU_base: typeOf_baseSieve UU)
(F  : functor) 
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(ff: transf  (functor_ViewOb K)  F)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) )  :
transf  (functor_ViewOb K)  (functor_Sheafified (functor_Restrict F VV)).
Proof. 
    refine (transf_Compos (transf_Constructing u ( identGene :>transf_ ff)) _).
    refine (transf_Compos (transf_RestrictCast  (transf_Ident _) VV_base uv UU_base) _).  
    refine  (transf_UnitSheafified_prePoly_preCast _) .
Defined.

Lemma Constructing_destructNatural
 (U : vertexGene) (UU : sieveFunctor U) 
(F  : functor):
typeOf_destructNatural (@transf_Constructing U UU F ).
Proof.  intros; move. intros G u form H f G' g u' form' f' Heq_u Heq_form Heq_f . 
unshelve eexists; cbn_sieve.
- rewrite ->  Heq_f, <- Heq_u, -> _functorialCompos_functor'. reflexivity.
- reflexivity.
- intros K c. rewrite <- Heq_form. rewrite -> _functorialCompos_functor'.
apply: _congr_relFunctor; last reflexivity. rewrite ->  Heq_f. cbn_transf.
rewrite <- _functorialCompos_functor'. reflexivity.
Qed.

Time Inductive elemCode : forall (G: vertexGene) (F : functor)  (ff : transf (functor_ViewOb G) F), Type :=

| Compos_elemCode : forall (F : functor) ( F''  : vertexGene) (F' : functor) 
(ff_ : transf (functor_ViewOb F'') F') (ff' : transf F' F),

elemCode ff_ -> morCode ff' -> elemCode ( transf_Compos ff_ ff' )

| Constructing_elemCode :
forall (U : vertexGene) (UU : sieveFunctor U) 
(F  : functor)
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(form : F K),

elemCode (transf_Constructing  u form)

| UnitSheafified_elemCode :
forall  (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU)
(F  : functor) 
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(ff: transf  (functor_ViewOb K)  F)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) ) 
(Code_ff : elemCode ff),

elemCode ( transf_UnitSheafified UU_base u ff VV_base uv )

with morCode : forall (E: functor) (F : functor)  (ff : transf E F), Type :=

| Compos_morCode :
forall (F F'' F' : functor) (ff_ : transf F'' F') (ff' : transf F' F),

morCode ff_ -> morCode ff' -> morCode ( transf_Compos ff_ ff' )

| Ident_morCode :
forall (F : functor),

@morCode F F ( transf_Ident F )

| SheafifiedMor_morCode :
forall (F E : functor) (ee : transf F E)
(Code_ee : morCode ee),

morCode (transf_SheafifiedMor ee )

| RestrictCast_morCode :
forall (F : functor)  (U : vertexGene) (UU  : sieveFunctor U)
 (UU_base: typeOf_baseSieve UU)
 (V : vertexGene) (vu : 'Sieve(V ~> U | UU)) ( VV : sieveFunctor V)
  (VV_base: typeOf_baseSieve VV),

morCode (transf_RestrictCast (transf_Ident F) UU_base vu VV_base)

| Destructing_morCode :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU )
(F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf (functor_ViewOb H) E)
(ee_congr : typeOf_destructCongr ee_)
(ee_natural : typeOf_destructNatural ee_)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) ) ,
forall (Code_ee__ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU))
    (form: F H) , elemCode (ee_ H u form) ),

morCode (transf_Destructing UU_base ee_congr ee_natural VV_base uv)

| Gluing_morCode :
forall (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
(VV_congr : typeOf_sieveCongr VV_)
(VV_natural : typeOf_sieveNatural VV_) 
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
         transf (functor_Restrict F (VV_ H u)) (functor_Sheafified E))
  (ee_congr : typeOf_gluingCongr VV_congr ee_)
(ee_natural : typeOf_gluingNatural VV_natural ee_) 
(ee_compat : typeOf_gluingCompat VV_congr VV_natural ee_),
forall (Code_ee : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
        morCode (ee_ H u)),

morCode (transf_Gluing UU_base ee_congr ee_natural ee_compat).

 (* /!\ LONG TIME /!\ 
Finished transaction in 534.461 secs (533.984u,0.031s) (successful)
33 sec without Gluing_morCode
 /!\  NOPE  /!\  after delete all polymorphism config leaving only Set Universe Polymorphism.:
Finished transaction in 0.183 secs (0.171u,0.s) (successful)
Finished transaction in 0.214 secs (0.218u,0.s) (successful) *)

Inductive obCoMod : forall (F : functor), Type :=

| Restrict : forall (F : functor) (U : vertexGene) (UU : sieveFunctor U),
obCoMod (functor_Restrict F UU)

| SheafifiedOb : forall (F : functor), 
obCoMod (functor_Sheafified F)

| ViewOb : forall (G : vertexGene),
obCoMod (functor_ViewOb G).

Notation "u ==1 v" := (@relation_transf _ _ u v)
(at level 70, no associativity) : type_scope.
Tactic Notation "cbn_rel_transf"  := 
cbn_equiv;  unfold  rel_transf, relation_transf.
Tactic Notation "cbn_rel_transf" "in" hyp_list(H) := 
cbn_equiv in H;  unfold  rel_transf, relation_transf in H.

Lemma Congr_Compos_cong :
forall (F F'' F' : functor) (ff_ : transf F'' F') (ff' : transf F' F),
forall (dd_ : transf F'' F') (dd' : transf F' F)
(Congr_congr_ff_ :  ff_ ==1 dd_)
(Congr_congr_ff' :  ff' ==1 dd'),
 (transf_Compos ff_ ff') ==1 (transf_Compos dd_ dd').
Proof. intros. cbn_rel_transf in Congr_congr_ff_ Congr_congr_ff'. cbn_rel_transf. intros.
apply: ( Congr_congr_ff').  apply: ( Congr_congr_ff_). assumption.
Qed.

(* TODO: keep or erase *)
Instance Congr_Compos_cong' :
forall (F F'' F' : functor),
Proper ( @equiv  _ (@_rel_relType (rel_transf _ _)) (@_equiv_relType (rel_transf _ _))
 ==> @equiv  _ (@_rel_relType (rel_transf _ _)) (@_equiv_relType (rel_transf _ _))
 ==> @equiv  _ (@_rel_relType (rel_transf _ _)) (@_equiv_relType (rel_transf _ _)) )
 (@transf_Compos F F'' F').
Proof. intros. move.  intros ff_  dd_ Congr_congr_ff_  ff' dd' Congr_congr_ff'.
 cbn_rel_transf in Congr_congr_ff_ Congr_congr_ff'. cbn_rel_transf. intros.
apply: ( Congr_congr_ff').  apply: ( Congr_congr_ff_). assumption.
Qed.

Lemma Congr_Constructing_cong:
forall (U : vertexGene) (UU : sieveFunctor U) 
(F  : functor)
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(form : F K),
forall (u' : 'Sieve(K ~> _ | UU))
(form' : F K),
forall (Heq_u : u == u')
(Heq_form : form == form'),
 (transf_Constructing  u form) ==1
(transf_Constructing  u' form').
Proof.  intros. cbn_rel_transf. intros G k k' Heq_k . rewrite -> Heq_k. unshelve eexists; cbn_transf;
first (rewrite -> Heq_u; reflexivity);
first reflexivity;
last intros H c; cbn_sieve; rewrite -> Heq_form; reflexivity. 
Qed.

Definition Congr_UnitSheafified_cong :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU)
(F  : functor) 
(K : vertexGene) (u : 'Sieve(K ~> _ | UU))
(ff: transf  (functor_ViewOb K)  F)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) )  
(U' : vertexGene) (UU' : sieveFunctor U') 
(UU_base': typeOf_baseSieve UU')

(u' : 'Sieve(K ~> _ | UU'))
(ff': transf  (functor_ViewOb K)  F)
(VV_base': typeOf_baseSieve VV)
(uv' : 'Sieve(U' ~> V | VV) )
(KK : sieveFunctor K) 
 (Congr_ff_Sieve: forall (K' : vertexGene) (k : 'Sieve( K' ~> _ | KK )) ,
( (k :>sieve_)) :>transf_ ff == ( (k :>sieve_)) :>transf_ ff') 
(Congr_UU_u : sieveEquiv (pullSieve UU (u :>sieve_))
(pullSieve UU' (u' :>sieve_)))
(* (Congr_u : (u :>sieve_) == (u' :>sieve_)) *)
(* MEMO DO NOT USE Congr_Restrict_cast_cong *)
(Congr_u_uv : (u :>sieve_) o>sieve_  uv   == (u' :>sieve_) o>sieve_  uv'  ),
(transf_UnitSheafified UU_base u ff VV_base uv) ==1 (transf_UnitSheafified UU_base' u' ff' VV_base' uv').
Proof. intros. intros H f f' Heq_f.
unfold transf_UnitSheafified.
cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
      transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor
      transf_Constructing transf_RestrictCast  transf_UnitSheafified_prePoly_preCast].
rewrite -> Heq_f; clear Heq_f.
unshelve eexists; cbn_transf.
exact:  (pullSieve KK f'). exact: sieveTransf_identSieve. exact: sieveTransf_identSieve.
intros J c; cbn_transf.
unshelve eexists;  cbn_sieve;
first (do 2 rewrite <- _natural_transf, <- _functorialCompos_functor';
setoid_rewrite -> _natural_transf;
rewrite ->  Congr_u_uv; reflexivity).
apply: (pullSieve_congr_sieveEquiv  _ (reflexivity _)).
etransitivity;
 first (apply: (interSieve_congr_sieveEquiv (reflexivity _) _ (reflexivity _));
  do 1 rewrite  <- _natural_transf; reflexivity).
etransitivity;
 last (apply: (interSieve_congr_sieveEquiv (reflexivity _) _ (reflexivity _));
  do 1 rewrite  <- _natural_transf; reflexivity).
etransitivity;
  last apply: pullSieve_pullSieve_sieveEquiv.
etransitivity;
  first (symmetry; apply: pullSieve_pullSieve_sieveEquiv).
apply: (interSieve_congr_sieveEquiv Congr_UU_u  (reflexivity _) (reflexivity _)).

intros H0 c0. cbn_transf. do 2 rewrite -> _natural_transf. cbn_equiv in c0.
set ll := (X in X :>transf_ _ == X :>transf_ _  ).
have Heq : ll == ( _whole_interSieve (((_factor_interSieve c0) :>sieve_) o>sieve_ c) ) :>sieve_ ;
last (rewrite -> Heq; apply: Congr_ff_Sieve).
subst ll. etransitivity; first apply: identGene_composGene.
rewrite -> _wholeProp_interSieve. setoid_rewrite <- _natural_transf.
rewrite <- (_wholeProp_interSieve (_factor_interSieve c0 )). reflexivity.
Qed.

Lemma Congr_SheafifiedMor_cong :
forall (F E : functor) (ee : transf F E),
forall (ee' : transf F E)
(Congr_ee :  ee ==1 ee'),
 (transf_SheafifiedMor ee ) ==1 (transf_SheafifiedMor ee' ).
Proof. intros. intros G f f' Heq_f . rewrite -> Heq_f. unshelve eexists;
first shelve;
first exact (sieveTransf_Ident _);
first exact (sieveTransf_Ident _).
abstract (intros H c; cbn_sieve; apply: Congr_ee; reflexivity). 
Qed.

Definition Congr_Destructing_cong :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU )
(F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf (functor_ViewOb H) E)
(ee_congr : typeOf_destructCongr ee_)
(ee_natural : typeOf_destructNatural ee_)
(V : vertexGene) (VV : sieveFunctor V) 
(VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) ),
forall 
(UU_base': typeOf_baseSieve UU)
(dd_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf  (functor_ViewOb H)  E)
(dd_congr : typeOf_destructCongr dd_)
(dd_natural : typeOf_destructNatural dd_)
(VV_base': typeOf_baseSieve VV)
 (uv' : 'Sieve(U ~> V | VV) ),

forall (Congr_ee_: forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
  forall (f : F H ), identGene :>transf_ ee_ H u f   == identGene :>transf_ dd_ H u f ) ,
forall  (Congr_uv : uv == uv'),

 (transf_Destructing UU_base ee_congr ee_natural VV_base uv)
==1  (transf_Destructing UU_base' dd_congr dd_natural VV_base' uv').
Proof. intros. intros H f_ f_' Heq_f_.
rewrite -> Heq_f_; clear Heq_f_.
unshelve eexists; cbn_transf.
- exact (identSieve _).
- exact: (sieveTransf_Ident _).
- exact: (sieveTransf_Ident _).
- intros J c.  cbn_transf;  unshelve eexists.
  + abstract (cbn_sieve; rewrite -> Congr_uv; reflexivity).
  + cbn_sieve; reflexivity.
  +  cbn_sieve. intros H0 c0. etransitivity; first apply: Congr_ee_. apply dd_congr.
     * abstract (reflexivity).
     * apply: _congr_relTransf. unshelve eexists; cbn_transf; reflexivity.
     * reflexivity.
Qed.

Definition Congr_Gluing_cong :
forall (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
(VV_congr : typeOf_sieveCongr VV_)
(VV_natural : typeOf_sieveNatural VV_) 
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
         transf (functor_Restrict F (VV_ H u)) (functor_Sheafified E))
  (ee_congr : typeOf_gluingCongr VV_congr ee_)
(* ee_natural used in code only not sense *)
(ee_natural : typeOf_gluingNatural VV_natural ee_) 
(ee_compat : typeOf_gluingCompat VV_congr VV_natural ee_),

forall (UU_base': typeOf_baseSieve UU)
(VV_congr' : typeOf_sieveCongr VV_)
(VV_natural' :  typeOf_sieveNatural VV_) 
(dd_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
      transf (functor_Restrict F (VV_ H u)) (functor_Sheafified E))
(dd_congr : typeOf_gluingCongr VV_congr' dd_)  
(dd_natural : typeOf_gluingNatural VV_natural' dd_)
(dd_compat: typeOf_gluingCompat VV_congr' VV_natural' dd_),

forall (Congr_ee_: forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
  ee_ H u ==1 dd_ H u) ,

(transf_Gluing UU_base ee_congr ee_natural ee_compat) 
==1 (transf_Gluing UU_base' dd_congr dd_natural dd_compat) .
Proof. intros. intros H f_ f_' Heq_f_.
rewrite -> Heq_f_; clear Heq_f_.

have @Congr_ee_': (forall (H0 : vertexGene)
        (u : 'Sieve( H0 ~> _ | interSieve UU (_indexer_type_Restrict f_')
                                 (_sieve_type_Restrict f_') )),
        (transf_Gluing_lemma f_' u :>transf_ ee_ H0 (_whole_interSieve u))
        == (transf_Gluing_lemma f_' u :>transf_ dd_ H0 (_whole_interSieve u)) );
first (intros; apply: Congr_ee_;reflexivity).

unshelve eexists; cbn_transf.
- exact: (sumSieve (fun H0 u => (conflSieve_Sheafified (Congr_ee_' H0 u)) )).
- exact: (sumSieve_congr (uu := sieveTransf_Ident _ ) 
    (fun H0 u => (conflTransf1_Sheafified (Congr_ee_' H0 u)) )).
- exact:  (sumSieve_congr (uu := sieveTransf_Ident _ ) 
    (fun H0 u => (conflTransf2_Sheafified (Congr_ee_' H0 u)) )).
- abstract (cbn_transf; intros J c;
  apply: (@conflEquiv_Sheafified _ _ _ _ (Congr_ee_' _ _))).
Qed.

Definition Congr_Restrict_cong (F E : functor) 
 (ff : transf F E) (U : vertexGene) (UU VV : sieveFunctor U)
 (uu : sieveTransf VV UU) (ff' : transf F E) (uu' : sieveTransf VV UU)
 (Congr_ff : ff ==1 ff')
 (* TODO MEMO (Congr_uu : uu ==1 uu')  
 NOT LACKED BECAUSE OF _congr_type_Restrict  *) :
 (transf_RestrictMor ff uu) ==1 (transf_RestrictMor ff' uu').
Proof. cbn_rel_transf in Congr_ff.  intros G f_ f_' [indexerEquiv_ sieveEquiv_ Heq_f_ ].
 unshelve eexists; cbn_transf;
first (exact: indexerEquiv_);
first (exact: sieveEquiv_);
last intros H c; cbn_sieve. apply: Congr_ff.
rewrite -> Heq_f_; 
(* TODO: HERE  *) apply: _congr_type_Restrict; cbn_transf; reflexivity.
(*  apply: _congr_relTransf;
unshelve eexists; cbn_transf; first reflexivity; last apply: Congr_uu; reflexivity. 
 *)
Qed.

Definition Congr_Restrict_cast_cong (F E : functor) 
(ff : transf F E) (U : vertexGene) (UU  : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(V : vertexGene) (vu : 'Sieve(V ~> U | UU)) ( VV : sieveFunctor V)
(VV_base: typeOf_baseSieve VV)
(ff' : transf F E)  (UU_base': typeOf_baseSieve UU) (vu' : 'Sieve(V ~> U | UU)) 
 (VV_base': typeOf_baseSieve VV)
 (Congr_ff : ff ==1 ff') (Congr_vu : vu == vu')   :
 (transf_RestrictCast ff UU_base vu VV_base) ==1 (transf_RestrictCast ff' UU_base' vu' VV_base').
Proof. cbn_rel_transf in Congr_ff.  intros G f_ f_' [indexerEquiv_ sieveEquiv_ Heq_f_ ].
 unshelve eexists; cbn_transf;
first (rewrite -> Congr_vu, -> indexerEquiv_; reflexivity);
first refine (interSieve_congr_sieveEquiv (reflexivity _) indexerEquiv_ sieveEquiv_);
last intros H c; cbn_sieve. apply: Congr_ff.
rewrite -> Heq_f_. (* TODO: HERE POSSIBLE _congr_type_Restrict  *)
 apply: _congr_relTransf. unshelve eexists; cbn_transf;  reflexivity.
Qed.
 
Definition Congr_Compos_Ident (F E : functor) 
(ff : transf F E)  :
(transf_Compos ff  (transf_Ident E))
 ==1 ff.
Proof.  intros G f f' Heq_f. cbn_transf. rewrite -> Heq_f; reflexivity.
Qed.

Definition Congr_Restrict_comp_Restrict (F E : functor) 
 (ff : transf F E) (U : vertexGene) (UU VV : sieveFunctor U)
 (uu : sieveTransf VV UU) 
 (D : functor) 
 (ff' : transf E D) (WW : sieveFunctor U) (vv : sieveTransf WW VV) :
 (transf_Compos (transf_RestrictMor ff uu) (transf_RestrictMor ff' vv))
  ==1 (transf_RestrictMor (transf_Compos ff ff') (sieveTransf_Compos vv uu)).
Proof.  intros G f_ f_' [indexerEquiv_ sieveEquiv_ Heq_f_ ].
 unshelve eexists; cbn_transf;
first (exact: indexerEquiv_);
first (exact: sieveEquiv_);
last intros H c; cbn_sieve.
rewrite -> Heq_f_. do 3 apply: _congr_relTransf.
unshelve eexists; cbn_transf; reflexivity.
Qed.

Definition Congr_Restrict_cast_comp_Restrict_cast (F E : functor) 
(ff : transf F E) (U : vertexGene) (UU  : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(V : vertexGene) (vu : 'Sieve(V ~> U | UU)) ( VV : sieveFunctor V)
(VV_base: typeOf_baseSieve VV)
(D : functor)   (ff' : transf E D) (W : vertexGene) (WW  : sieveFunctor W)
(WW_base: typeOf_baseSieve WW)
(uw : 'Sieve(U ~> W | WW)) 
(UU_base': typeOf_baseSieve UU)  :
  (transf_Compos (transf_RestrictCast ff UU_base vu VV_base) 
    (transf_RestrictCast ff' WW_base uw UU_base'))
==1 (transf_RestrictCast (transf_Compos ff ff') WW_base ((vu :>sieve_) o>sieve_ uw ) VV_base).
Proof.  intros G f_ f_' [indexerEquiv_ sieveEquiv_ Heq_f_ ].
 unshelve eexists; cbn_transf;
 first(rewrite -> indexerEquiv_; rewrite <- _functorialCompos_functor', -> _natural_transf;
  reflexivity).
 - etransitivity. refine (interSieve_congr_sieveEquiv (reflexivity _) _ _).
  (rewrite  -> _natural_transf; reflexivity).
  refine (interSieve_congr_sieveEquiv (reflexivity _) indexerEquiv_ sieveEquiv_).
    symmetry; apply: interSieve_image_sieveEquiv. exact: UU_base.
 - intros H c; cbn_sieve.
  rewrite -> Heq_f_. do 3 apply: _congr_relTransf.
unshelve eexists; cbn_transf; reflexivity.
Qed.
 
Definition Congr_SheafifiedMor_comp_SheafifiedMor :
 forall (F E : functor) (ee : transf F E),
 forall (D : functor) (dd : transf E D), 
 (transf_Compos (transf_SheafifiedMor ee) (transf_SheafifiedMor dd))
==1 (transf_SheafifiedMor (transf_Compos ee dd )).
Proof.  intros. move. intros H f_ f_' Heq_f_. rewrite -> Heq_f_. unshelve eexists; cbn_transf.
- exact (_sieve_type_Sheafified f_'). 
- exact: (sieveTransf_Ident _). 
- exact: (sieveTransf_Ident _).
- abstract (intros J c; reflexivity).  
Qed.

Section Gluing_comp_SheafifiedMor.
Variables (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
(VV_congr : typeOf_sieveCongr VV_)
(VV_natural : typeOf_sieveNatural VV_) 
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
         transf (functor_Restrict F (VV_ u)) (functor_Sheafified E)).
Variables  (ee_congr : typeOf_gluingCongr VV_congr ee_)
(ee_natural : typeOf_gluingNatural VV_natural ee_)
(ee_compat : typeOf_gluingCompat VV_congr VV_natural ee_).

Variables (D : functor) (dd : transf E D).

Lemma Gluing_comp_SheafifiedMor_gluingCongr : 
typeOf_gluingCongr VV_congr (fun H u => (transf_Compos (ee_  u) (transf_SheafifiedMor dd))) .
Proof.     move. intros.
  cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
  transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor transf_SheafifiedMor].
  apply: _congr_relTransf. apply: ee_congr; eassumption.
Qed.

Lemma Gluing_comp_SheafifiedMor_gluingNatural : 
typeOf_gluingNatural VV_natural (fun H u => (transf_Compos (ee_  u) (transf_SheafifiedMor dd))) .
Proof.     move. intros.
  cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
  transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor transf_SheafifiedMor transf_RestrictMor].
  rewrite -> _natural_transf.
  apply: _congr_relTransf. apply: ee_natural; eassumption.
Qed.

Lemma Gluing_comp_SheafifiedMor_gluingCompat : 
typeOf_gluingCompat VV_congr VV_natural (fun H u => (transf_Compos (ee_  u) (transf_SheafifiedMor dd))) .
Proof.     move. intros.
  cbn -[equiv _type_relType _rel_relType _equiv_relType  _arrows_functor functor_ViewOb
  transf_ViewObMor _functor_sieveFunctor _transf_sieveFunctor  ].
  apply: _congr_relTransf. apply: ee_compat; eassumption.
Qed.

Definition Congr_Gluing_comp_SheafifiedMor:
(transf_Compos (transf_Gluing UU_base ee_congr ee_natural ee_compat) (transf_SheafifiedMor dd) )
==1 (transf_Gluing UU_base (Gluing_comp_SheafifiedMor_gluingCongr) 
             (Gluing_comp_SheafifiedMor_gluingNatural)  (Gluing_comp_SheafifiedMor_gluingCompat) ).
Proof. intros. move. intros H f_ f_' Heq_f_. rewrite -> Heq_f_. unshelve eexists; cbn_transf.
- shelve.
- exact: (sieveTransf_Ident _). 
- exact: (sieveTransf_Ident _).
- abstract (intros J c; reflexivity). 
Qed.

End Gluing_comp_SheafifiedMor.

Section Destructing_comp_SheafifiedMor.
Variables (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
  F H -> transf  (functor_ViewOb H)  E).
Variables  (ee_congr : typeOf_destructCongr  ee_)
(ee_natural : typeOf_destructNatural  ee_)
(V : vertexGene) (VV : sieveFunctor V)
(VV_base:  typeOf_baseSieve VV)
 (uv : 'Sieve(U ~> V | VV) ) .
Variables (D : functor) (dd : transf E D)
(W : vertexGene)   (WW : sieveFunctor W) 
(WW_base:  typeOf_baseSieve WW) (vw : 'Sieve(V ~> W | WW))
(VV_base':  typeOf_baseSieve VV)  .

Lemma Destructing_comp_SheafifiedMor_destructCongr  : 
typeOf_destructCongr  (fun H u f => (transf_Compos (@ee_ H u f)  dd)) .
Proof.     do 4 (move; intros).  cbn_transf.
  apply: _congr_relTransf. apply: ee_congr; eassumption.
Qed.

Lemma Destructing_comp_SheafifiedMor_destructNatural : 
typeOf_destructNatural  (fun H u f => (transf_Compos (@ee_ H u f)  dd)) .
Proof.     move. intros. cbn_transf.
  apply: _congr_relTransf. apply: ee_natural; eassumption.
Qed.

Definition Congr_Destructing_comp_SheafifiedMor:
(transf_Compos (transf_Destructing UU_base ee_congr ee_natural VV_base uv) 
    (transf_SheafifiedMor (transf_RestrictCast dd WW_base vw VV_base' )) )
==1 (transf_Destructing UU_base (Destructing_comp_SheafifiedMor_destructCongr) 
         (Destructing_comp_SheafifiedMor_destructNatural) WW_base  ((uv :>sieve_) o>sieve_ vw)   ).
Proof. intros. move. intros H f_ f_' Heq_f_. rewrite -> Heq_f_.
clear Heq_f_.  unshelve eexists.
- shelve.
- cbn_sieve. exact: (sieveTransf_Ident _). 
- cbn_sieve. exact: (sieveTransf_Ident _).
- intros J c.  unshelve eexists. 
  + abstract(cbn_sieve;  rewrite <- _natural_transf;
   do 3 rewrite -> _functorialCompos_functor; reflexivity).
  + cbn_sieve. cbn_sieve in c.
  etransitivity. refine (interSieve_congr_sieveEquiv (reflexivity _) _ (reflexivity _)).
  (rewrite -> _functorialCompos_functor', -> _natural_transf; reflexivity).
    symmetry; apply: interSieve_image_sieveEquiv. exact: VV_base.
  + abstract(intros H0 c0; cbn_sieve; reflexivity).
Qed.

End Destructing_comp_SheafifiedMor.

Section RestrictCast_comp_Destructing.
Variables (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
  (F E : functor)
  (ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
  F H -> transf  (functor_ViewOb H)  E).
Variables  (ee_congr : typeOf_destructCongr  ee_)
(ee_natural : typeOf_destructNatural  ee_)
(V : vertexGene) (VV : sieveFunctor V)
(VV_base:  typeOf_baseSieve VV)
 (uv : 'Sieve(U ~> V | VV) ) .
Variables (D : functor) (dd : transf D F) (UU_base':  typeOf_baseSieve UU) 
(W : vertexGene) (wu : 'Sieve(W ~> U | UU))
(WW : sieveFunctor W) (WW_base: typeOf_baseSieve WW) .

Lemma RestrictCast_comp_Destructing_destructCongr  : 
typeOf_destructCongr (fun H (w : 'Sieve(H ~> W | WW)) f => 
    @ee_ H ((w :>sieve_) o>sieve_ wu) (f :>transf_ dd)) .
Proof. move. intros H. move. intros w1 w2 Heq_w. move. intros d1 d2 Heq_d.
apply: ee_congr.  rewrite -> Heq_w. reflexivity.
rewrite -> Heq_d. reflexivity.
Qed.

Lemma RestrictCast_comp_Destructing_destructNatural : 
typeOf_destructNatural (fun H (w : 'Sieve(H ~> W | WW)) f => 
    @ee_ H ((w :>sieve_) o>sieve_ wu) (f :>transf_ dd)).
Proof.     move. intros G w form H f G' g w' form' f' Heq_w Heq_form Heq_f.
     apply: (ee_natural (g:= g)).
   - rewrite <- Heq_w. rewrite <- _natural_transf. 
     rewrite <-  _functorialCompos_functor'. reflexivity.
   - rewrite <- Heq_form. rewrite <- _natural_transf. reflexivity.
   - exact: Heq_f.
Qed.

Definition Congr_RestrictCast_comp_Destructing:
(transf_Compos (transf_RestrictCast dd UU_base' wu WW_base ) 
  (transf_Destructing UU_base ee_congr ee_natural VV_base uv)   )
==1 (transf_Destructing WW_base (RestrictCast_comp_Destructing_destructCongr) 
         (RestrictCast_comp_Destructing_destructNatural) VV_base  ((wu :>sieve_) o>sieve_ uv)   ).
Proof. intros. move. intros H f_ f_' Heq_f_. rewrite -> Heq_f_.
clear Heq_f_.  unshelve eexists.
- shelve.
- cbn_sieve. exact: (sieveTransf_Ident _). 
- cbn_sieve. exact: (sieveTransf_Ident _).
- intros J c.  unshelve eexists. 
  + cbn_sieve. rewrite <- _natural_transf.
  do 1 rewrite <- _functorialCompos_functor'. reflexivity.
  + cbn_sieve. cbn_sieve in c.
  refine (interSieve_congr_sieveEquiv _ (reflexivity _) (reflexivity _)).
  etransitivity. refine (interSieve_congr_sieveEquiv (reflexivity _) _ (reflexivity _)).
  (rewrite -> _natural_transf; reflexivity).
  symmetry; apply: interSieve_image_sieveEquiv. exact: UU_base.
  + intros H0 c0; cbn_sieve. apply: ee_congr.
    * apply: UU_base.  unfold  _rel_relType, equiv; simpl.
    do 2 rewrite -> _wholeProp_interSieve. cbn_sieve.
    rewrite -> _functorialCompos_functor'. do 1 rewrite <- _natural_transf. reflexivity. 
    * do 2 apply: _congr_relTransf. unshelve eexists; cbn_transf; reflexivity.
    * reflexivity. 
Qed.

End RestrictCast_comp_Destructing.

Definition Congr_Constructing_comp_Restrict_cast :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU)
(F  : functor) (K : vertexGene) (u : 'Sieve(K ~> _ | UU)) (form : F K),
forall ( E : functor)  (ff : transf F E) (V : vertexGene) (VV  : sieveFunctor V)
 (VV_base: typeOf_baseSieve VV)
 (uv : 'Sieve(U ~> V | VV)), 
(transf_Compos (transf_Constructing u form) (transf_RestrictCast ff VV_base uv UU_base) )
==1 (transf_Constructing  ((u :>sieve_) o>sieve_ uv) (form :>transf_ ff))  .
Proof. intros. intros G k1 k2 Heq_k.
 unshelve eexists; cbn_transf;
first (rewrite -> Heq_k; rewrite -> _functorialCompos_functor';
do 2 rewrite <- _natural_transf; reflexivity).
 - symmetry; apply: interSieve_image_sieveEquiv. exact: UU_base.
 - intros H c; cbn_sieve.
 rewrite <- _natural_transf. apply: _congr_relFunctor; last reflexivity.
 apply: _congr_relFunctor; last rewrite -> Heq_k; reflexivity.
Qed.

(* /!\ SOLUTION /!\ *)
Definition Congr_Constructing_comp_Destructing :
forall (U : vertexGene) (UU : sieveFunctor U) 
(UU_base: typeOf_baseSieve UU) (F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve(H ~> _ | UU)),
      F H -> transf  (functor_ViewOb H)  E)
(ee_congr : typeOf_destructCongr ee_)
(ee_natural : typeOf_destructNatural ee_)
(V : vertexGene) (VV : sieveFunctor V)  (VV_base: typeOf_baseSieve VV)
(uv : 'Sieve(U ~> V | VV) ),
forall   (K : vertexGene) (u : 'Sieve(K ~> _ | UU)) (form : F K),
 (transf_Compos (transf_Constructing u form) 
              (transf_Destructing UU_base ee_congr ee_natural VV_base uv))
==1 (transf_UnitSheafified UU_base u (ee_ K u  form) VV_base uv).
Proof.  intros. move. intros H h h0 Heq. rewrite -> Heq. unshelve eexists.
- exact (identSieve _). 
- exact: (sieveTransf_Ident _). 
- exact: (sieveTransf_Ident _).
- intros J c.  unshelve eexists.
  + reflexivity. 
  + reflexivity.
  + intros H0 c0. cbn_sieve. cbn_sieve in c0. rewrite -> _natural_transf. 
    symmetry; apply: ee_natural. 
    * apply: UU_base.  unfold  _rel_relType, equiv; simpl.
    rewrite -> _wholeProp_interSieve. cbn_sieve.
     do 2 rewrite <- _natural_transf. 
     rewrite -> _functorialCompos_functor'.
    reflexivity.
    * cbn_transf. reflexivity.
    * cbn_sieve. etransitivity; first exact: identGene_composGene; 
    symmetry; exact: composGene_identGene.
Qed.

Definition Congr_Constructing_comp_Gluing :
forall (U : vertexGene) (UU : sieveFunctor U)
(UU_base: typeOf_baseSieve UU)
(VV_ : forall H : vertexGene, 'Sieve( H ~> _ | UU ) -> sieveFunctor H)
(VV_congr : typeOf_sieveCongr VV_)
(VV_natural : typeOf_sieveNatural VV_) 
(F E : functor)
(ee_ : forall (H : vertexGene) (u : 'Sieve( H ~> _ | UU )),
        transf (functor_Restrict F (VV_ H u)) (functor_Sheafified E))
(ee_congr : typeOf_gluingCongr VV_congr ee_)
(ee_natural : typeOf_gluingNatural VV_natural ee_)
(ee_compat : typeOf_gluingCompat VV_congr VV_natural ee_),
forall (K : vertexGene) (u : 'Sieve(K ~> _ | (sumSieve VV_))) (form : F K), 
   (transf_Compos (transf_Constructing u form)
      (transf_Gluing UU_base ee_congr ee_natural ee_compat))
   ==1   (transf_Compos (transf_Constructing (_inner_sumSieve u) form)
      (ee_ (_object_sumSieve u) (_outer_sumSieve u))).
Proof.  intros. symmetry. move. intros G form'0 form'  Heq. rewrite -> Heq. clear Heq. etransitivity.
cbn -[equiv _type_relType _rel_relType _equiv_relType   functor_ViewOb
                                 transf_ViewObMor transf_Constructing ].
apply: (gluingNatural_identGene_of_gluingNatural ee_natural).

have @identGene_u : 'Sieve(G ~> _ | interSieve UU
((( form' o>sieve_ _inner_sumSieve u) :>sieve_)
o>functor_ (_outer_sumSieve u :>sieve_)) (identSieve G)) .
  refine (((identGene : 'Sieve(G ~> _ | identSieve G) ) 
            :>transf_ interSieve_image 
                        ((( form' o>sieve_ _inner_sumSieve u) :>sieve_)
                          o>functor_ _outer_sumSieve u) _)
        :>transf_ (interSieve_congr (sieveTransf_Ident _) _ (sieveTransf_Ident _) )).
  abstract (rewrite <- _natural_transf; reflexivity).

 (* To get this unsimplification, continue and do 
  refine (sieveTransf_Compos _ (sumSieve_interSieve_image _  )).
 *)
have Heq_ee: ((transf_RestrictMor_pullSieve (form' :>transf_ transf_Constructing (_inner_sumSieve u) form) identGene
       :>transf_ transf_RestrictMor (transf_Ident F)
                   (VV_natural (_object_sumSieve u) (_outer_sumSieve u) G
                      (identGene o>gene _indexer_type_Restrict (form' :>transf_ transf_Constructing (_inner_sumSieve u) form))))
  :>transf_ ee_ G  ((identGene o>gene _indexer_type_Restrict (form' :>transf_ transf_Constructing (_inner_sumSieve u) form)) o>sieve_ 
                   _outer_sumSieve u))
==  (transf_Gluing_lemma (form' :>transf_ transf_Constructing u form) identGene_u
  :>transf_ ee_ G (identGene_u
                   :>transf_ interSieve_projWhole UU (_indexer_type_Restrict (form' :>transf_ transf_Constructing u form))
                               (_sieve_type_Restrict (form' :>transf_ transf_Constructing u form)))).
abstract (unshelve apply: ee_congr;
first abstract (cbn_sieve; rewrite -> _functorialCompos_functor'; reflexivity);
last unshelve eexists; cbn_sieve;
  first reflexivity;
  first reflexivity;
  last intros H c; reflexivity).

unshelve eexists.
- exact: (conflSieve_Sheafified Heq_ee) . (*  exact (identSieve _).  *)
- exact: (conflTransf1_Sheafified _).  (* READ Heq_ee HERE *)
- refine (sieveTransf_Compos (conflTransf2_Sheafified _) _).
 refine (sieveTransf_Compos _ (sumSieve_congr 
(UU1 := pullSieve UU (((( form' o>sieve_ _inner_sumSieve u) :>sieve_)
o>functor_ _outer_sumSieve u) :>sieve_) )  (fun H0 u0 => sieveTransf_Ident _)   ) ).
refine (sieveTransf_Compos _ (sumSieve_interSieve_image _  )).
subst identGene_u. exact: (sieveTransf_Ident _).
apply: (@conflEquiv_Sheafified _ _ _ _ Heq_ee).
Defined.

End COMOD.
End SHEAF.
(** # #
#+END_SRC

Voila.
# # **)

Reset Initial.
Module EARLIER_PRELIM_SHEAF.

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

End EARLIER_PRELIM_SHEAF.