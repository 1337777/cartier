(**#+TITLE: cartierSolution5.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution5.v

solves half of some question of Cartier which is how to program grammatical polymorph contextual ( "weighted" ) multifold ( "enriched" ) pairing-projections ( "product" ) ...

The ends is to do polymorph mathematics which is multifolded/enriched ref some indexer (symmetric-associative-monoidal metalogic/metacategory) ; this infers that the morphisms can no longer be touched individually but many morphisms shall be touched at the same time via some indexing/multiplier . And for multifold-enriched polymorph mathematics , the common operations on the morphisms are multifold/multiplicative ; this contrast from internal polymorph mathematics where many objects are touched at the same time and moreover many morphisms are touched at the same time and the common operations on the morphisms are coordinatewise/dimensional/pointwise .

Each decoding ( "Yoneda" ) of some index-for-morphisms which encodes all the morphisms-at-some-domain-codomain is some metafunctor , which is programmed by some inductive-family-presentation whose additional/embedded 2 constructors  signify the functoriality ( "parameter-arrow-action" and  "structure-arrow-action" ) . Each decoding ( "Yoneda" ) of the whatever-is-interesting arrows between the indexes-for-morphisms are metatransformations which are programmed as some grammatical-constructors of this inductive-family-presentation of the morphisms .

The conversion-relation would convert across two morphisms whose multiplicities-indexes are not syntactically/grammatically-the-same. But oneself does show that , by structure-arrow-action ( metalogic-deduction ) , these two multiplicities are indeed ( symmetric-associative-monoidal-metalogic ) propositionally equal ( "soundness lemma" ) .

Finally, some linear total/asymptotic grade is defined on the morphisms and the tactics-automated degradation lemma shows that each of the conversion indeed degrades the redex morphism .

For instant first impression , the conversion-relation constructor which says that the first projection morphism is natural/polyarrowing (commutativity along the parameter-arrow-action cut-constructor) , is written as :

#+BEGIN_EXAMPLE
| Project1_MorCoMod_Poly_Param : forall (F1 F2 : obCoMod) (Z1 : obCoMod)
    (A : obIndexer) (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0), forall (A' : obIndexer)
    (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      ( ~_1 @ F2 o>CoMod (a o>* zz1) )
        <~~ ( (Cong.Context1_arrow a) o>* ( ~_1 @ F2 o>CoMod zz1 ) )
#+END_EXAMPLE

KEYWORDS : 1337777.OOO ; COQ ; cut-elimination ; multifold-enriched functors ; contextual-weighted multifold-enriched product ; polymorph metafunctors-grammar ; modos

OUTLINE :

  * Indexer metalogic for multifold-enrichment , lemma for commutation of parameter-polyarrowing along structure-arrow-action
  ** Indexer metalogic is half-grammatical half-sense and is symmetric-associative-monoidal with some context ( "product-weight" ) constructor , and is presented in the congruent-rewrite style
  ** Lemma for commutation of parameter-polyarrowing along structure-arrow-action

  * Generating data multifolded-enriched ref some indexer

  * Grammatical presentation of objects and morphisms multifolded/enriched ref some indexer , by distinguishing parameter-polyarrowing from structure-arrow-action

  * Grammatical conversions of morphisms , which infer the same multiplicity-computation
  ** Grammatical conversions of morphisms
  ** Same multiplicity-computation for convertible morphisms
  ** Linear total/asymptotic grade and the degradation lemma

  * Solution
  ** Solution morphisms without (parameter-polyarrowing)/polymorphism
  ** Destruction of morphisms with inner-instantiation of object-indexes

  * (parameter-polyarrowing)/polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

-----

BUY MOM RECURSIVE T-SQUARE paypal.me/1337777 1337777.OOO@gmail.com ; 微信支付 2796386464@qq.com ; eth 0x54810dcb93b37DBE874694407f78959Fa222D920 ; amazon amazon.com/hz/wishlist/ls/28SN02HR4EB8W ; irc #OOO1337777

**)

(**

* Indexer metalogic for multifold-enrichment , lemma for commutation of parameter-polyarrowing along structure-arrow-action

The ends is to do polymorph mathematics which is multifolded/enriched ref some indexer (symmetric-associative-monoidal metalogic/metacategory) ; this infers that the morphisms can no longer be touched individually but many morphisms shall be touched at the same time via some indexing/multiplier . And for multifold-enriched polymorph mathematics , the common operations on the morphisms are multifold/multiplicative ; this contrast from internal polymorph mathematics where many objects are touched at the same time and moreover many morphisms are touched at the same time and the common operations on the morphisms are coordinatewise/dimensional/pointwise .

** Indexer metalogic is half-grammatical half-sense and is symmetric-associative-monoidal with some context ( "product-weight" ) constructor , and is presented in the congruent-rewrite style

As common , the indexer metalogic/metacategory is symmetric associative monoidal ; but there are 3 contrasts .

Primo contrast : the presentation of the indexer indexes and indexer arrows is half-grammatical ( "structural" indexes and arrows , which says symmetric-associative-monoidal(-and-contextual) ) and half-sense ( "opaque" / "parametric" indexes and arrows , which is injected in the metalogic ) .

Secondo contrast : the presentation of the indexer arrows is in the congruent-rewrite style , which is that the compositions (metalogical-cut) of such arrows is always top-most ( no inner-compositions ) . It is well-known that such alternative from the reduction-style presentation is always possible via some induction ; that this induction is really non-structural non-linear is less known ... One consequence of this rewrite-style presentation is that structure-arrow action on the morphisms are not-real cuts ( because the automatic-search of any such structure-arrow is bounded by the size of the source-index ) but only parameter-arrow-action on the morphisms are questionable cuts which shall be eliminated/erased ( or accumulated onto the atomic generating morphisms ) .

For sure , (parameter-polyarrowing)/polymorphism/cut-elimination cannot proceed beyond the (parameter-polyarrowings)/polymorphisms/cuts which are contained in the molecular morphisms generated by the atomic generating data ; but memo that the molecular parameter-polyarrowing [Mole.MorCoMod_Poly_Param] cut-constructor will be pseudo-erased from the solution molecules by accumulating it onto the atomic generating morphisms .

Tertio contrast : the presentation of the indexer arrows has some context ( "product-weight" ) constructor because such context ( "product-weight" ) of the pairing-projections lacks to be grammatically distinguished during the polyarrowing-cut-elimination resolution .

#+BEGIN_SRC coq :exports both :results silent **)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Omega.

Module MULTIFOLD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments Nat.sub : simpl nomatch.
Arguments Nat.add : simpl nomatch.

Delimit Scope poly_scope with poly.
Open Scope poly.

Module Import Indexer.

  Delimit Scope param_scope with param.

  Parameter obIndexer_Param : Type.
  Parameter morIndexer_Param : obIndexer_Param -> obIndexer_Param -> Type.
  Notation "''Indexer' (0 A' ~> A )0" := (@morIndexer_Param A' A) (at level 0, format "''Indexer' (0  A'  ~>  A  )0") : param_scope .
  Parameter polyIndexer_Param : ( forall A A', 'Indexer(0 A' ~> A )0 -> forall A'', 'Indexer(0 A'' ~> A' )0 -> 'Indexer(0 A'' ~> A )0 )%param .
  Notation "a_ o>Indexer a'" :=
    (@polyIndexer_Param _ _ a' _ a_) (at level 40, a' at next level, left associativity) : param_scope.
  Parameter unitIndexer_Param : forall {A : obIndexer_Param}, 'Indexer(0 A ~> A )0 %param.

  Inductive obIndexer : Type :=
  | ObIndexer_Param : obIndexer_Param -> obIndexer
  | Multiply : obIndexer -> obIndexer -> obIndexer
  | One : obIndexer
  | Context1 : obIndexer -> obIndexer
  | Context2 : obIndexer -> obIndexer.

  Module Cong.

    (* as basic form  *)
    Module MorIndexer_Param.

      Variant morIndexer : obIndexer -> obIndexer -> Type :=
      | MorIndexer_Param : forall A B : obIndexer_Param, 'Indexer(0 A ~> B )0 %param -> 'Indexer(0 (ObIndexer_Param A) ~> (ObIndexer_Param B) )0 
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End MorIndexer_Param.

    (* as basic form , for sense *)
    Module Context1One.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Context1One : forall A : obIndexer, 'Indexer(0 Multiply (Context1 One) A ~> (Context1 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Context1One.

    (* Module Context1One_Rev. *)

    (* as basic form for sense *)
    Module Context2One.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Context2One : forall A : obIndexer, 'Indexer(0 Multiply (Context2 One) A ~> (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Context2One.

    (* Module Context2One_Rev. *)

    (* as basic form *)
    Module Assoc.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Assoc : forall A B C : obIndexer, 'Indexer(0 (Multiply (Multiply A B) C) ~> (Multiply A (Multiply B C)) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Assoc.

    (* Module Assoc_Rev. *)

    (* as basic form *)
    Module Sym.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Sym : forall A B : obIndexer, 'Indexer(0 (Multiply A B) ~> (Multiply B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Sym.

    (* as basic form *)
    Module OneMultiplyL.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | OneMultiplyL : forall A : obIndexer, 'Indexer(0 (Multiply One A) ~> A )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End OneMultiplyL.

    (* as basic form *)
    Module OneMultiplyR.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | OneMultiplyR : forall A : obIndexer, 'Indexer(0 (Multiply A One) ~> A )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End OneMultiplyR.

    (* as basic form *)
    Module OneMultiplyL_Rev.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | OneMultiplyL_Rev : forall A : obIndexer, 'Indexer(0 A ~> (Multiply One A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End OneMultiplyL_Rev.

    (* as basic form *)
    Module OneMultiplyR_Rev.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | OneMultiplyR_Rev : forall A : obIndexer, 'Indexer(0 A ~> (Multiply A One) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End OneMultiplyR_Rev.

    (* may definable form later using cong and many arrow-actions *)
    Module SymContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymContext1 : forall A : obIndexer, 'Indexer(0 Context1 (Context2 A) ~> Context2 (Context1 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymContext1.

    (* may definable form later using cong and many arrow-actions *)
    Module SymContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymContext2 : forall A : obIndexer, 'Indexer(0 Context2 (Context1 A) ~> Context1 (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymContext2.

    (* may definable form later using cong and many arrow-actions *)
    Module AssocContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocContext1 : forall A B : obIndexer, 'Indexer(0 Context1 (Multiply B A) ~> Multiply (Context1 A) B )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocContext1.

    (* may definable form later using cong and many arrow-actions *)
    Module AssocContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocContext2 : forall A B : obIndexer, 'Indexer(0 Context2 (Multiply B A) ~> Multiply (Context2 A) B )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocContext2.

    (* may definable form later using cong and many arrow-actions *)
    Module AssocMultiplyContext1.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocMultiplyContext1 : forall A B : obIndexer, 'Indexer(0 Multiply (Context1 B) A ~> Multiply B (Context1 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocMultiplyContext1.

    (* may definable form later using cong and many arrow-actions *)
    Module AssocMultiplyContext2.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocMultiplyContext2 : forall A B : obIndexer, 'Indexer(0 Multiply (Context2 B) A ~> Multiply B (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocMultiplyContext2.

    (* may definable form later using cong and many arrow-actions *)
    Module SymMultiplyContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymMultiplyContext1 : forall A B : obIndexer, 'Indexer(0 Multiply B (Context1 A) ~> Context1 (Multiply B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymMultiplyContext1.
    
    (* may definable form later using cong and many arrow-actions *)
    Module SymMultiplyContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymMultiplyContext2 : forall A B : obIndexer, 'Indexer(0 Multiply B (Context2 A) ~> Context2 (Multiply B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymMultiplyContext2.
 
    Section Section1.

      Variable morIndexer_Constant : obIndexer -> obIndexer -> Type .

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | MorIndexer_Constant : forall A B : obIndexer, @morIndexer_Constant A B -> 'Indexer(0 A ~> B )0 
      | Multiply_arrowL : forall B A A' : obIndexer, 'Indexer(0 A' ~>  A )0 ->
                                              'Indexer(0 (Multiply A' B) ~> (Multiply A B) )0
      | Multiply_arrowR : forall A B B' : obIndexer, 'Indexer(0 B' ~>  B )0 ->
                                              'Indexer(0 (Multiply A B') ~> (Multiply A B) )0
      | Context1_arrow : forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                             'Indexer(0 (Context1 A') ~> (Context1 A) )0
      | Context2_arrow : forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                             'Indexer(0 (Context2 A') ~> (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Section1.
    
    Module Export Ex_Notations.
      Delimit Scope cong_scope with cong.
      Hint Constructors MorIndexer_Param.morIndexer.
      Hint Constructors Context1One.morIndexer.
      Hint Constructors Context2One.morIndexer.
      Hint Constructors Assoc.morIndexer.
      Hint Constructors Sym.morIndexer.
      Hint Constructors OneMultiplyL.morIndexer.
      Hint Constructors OneMultiplyR.morIndexer.
      Hint Constructors OneMultiplyL_Rev.morIndexer.
      Hint Constructors OneMultiplyR_Rev.morIndexer.
      Hint Constructors SymContext1.morIndexer.
      Hint Constructors SymContext2.morIndexer.
      Hint Constructors AssocContext1.morIndexer.
      Hint Constructors AssocContext2.morIndexer.
      Hint Constructors AssocMultiplyContext1.morIndexer.
      Hint Constructors AssocMultiplyContext2.morIndexer.
      Hint Constructors SymMultiplyContext1.morIndexer.
      Hint Constructors SymMultiplyContext2.morIndexer.
      Hint Constructors morIndexer.

      Notation "''Indexer' (0 A' ~> A )0" := (@morIndexer _ A' A) : cong_scope.
      Notation "''Indexer' (0 A' ~> A @ R )0" := (@morIndexer R A' A) (at level 0, format "''Indexer' (0  A'  ~>  A  @  R  )0") : cong_scope .
    End Ex_Notations.

    Module Destruct_MorIndexer_Param_codomContext1.

      Inductive morIndexer_codomContext1 : forall (A A' : obIndexer),
        'Indexer(0 A' ~> Context1 A @ MorIndexer_Param.morIndexer )0 %cong -> Type :=
      | Context1_arrow : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomContext1  ( Context1_arrow a ) .

      Definition morIndexer_codomContext1P_Type
                 (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %cong)  :=
        ltac:( destruct A; [ intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | refine (morIndexer_codomContext1 a)
                           | intros; refine (unit : Type) ] ).

      Lemma morIndexer_codomContext1P
        : forall A A' ( a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ), morIndexer_codomContext1P_Type a .
      Proof.
        intros. case: A' A / a .
        - destruct m . intros; exact: tt.
        - intros; exact: tt.
        - intros; exact: tt.
        - constructor 1.
        - intros; exact: tt.
      Defined.

    End Destruct_MorIndexer_Param_codomContext1.

    Module Destruct_MorIndexer_Param_codomContext2.

      Inductive morIndexer_codomContext2 : forall (A A' : obIndexer),
        'Indexer(0 A' ~> Context2 A @ MorIndexer_Param.morIndexer )0 %cong -> Type :=
      | Context2_arrow : forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomContext2  ( Context2_arrow a ) .

      Definition morIndexer_codomContext2P_Type
                 (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %cong)  :=
        ltac:( destruct A; [ intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | refine (morIndexer_codomContext2 a) ] ).

      Lemma morIndexer_codomContext2P
        : forall A A' ( a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ), morIndexer_codomContext2P_Type a .
      Proof.
        intros. case: A' A / a .
        - destruct m . intros; exact: tt.
        - intros; exact: tt.
        - intros; exact: tt.
        - intros; exact: tt.
        - constructor 1.
      Defined.

    End Destruct_MorIndexer_Param_codomContext2.

    Module Destruct_MorIndexer_Param_codomMultiply.

      Inductive morIndexer_codomMultiply : forall (A B A' : obIndexer),
        'Indexer(0 A' ~> Multiply A B @ MorIndexer_Param.morIndexer )0 %cong -> Type :=
      | Multiply_arrowL : forall (B A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomMultiply ( Multiply_arrowL B a ) 
      | Multiply_arrowR : forall (A B B' : obIndexer) (b : 'Indexer(0 B' ~> B @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomMultiply ( Multiply_arrowR A b ) .

      Definition morIndexer_codomMultiplyP_Type
                 (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %cong)  :=
        ltac:( destruct A; [ intros; refine (unit : Type)
                           | refine (morIndexer_codomMultiply a)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type) ] ).

      Lemma morIndexer_codomMultiplyP
        : forall A A' ( a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ), morIndexer_codomMultiplyP_Type a .
      Proof.
        intros. case: A' A / a .
        - destruct m . intros; exact: tt.
        - constructor 1.
        - constructor 2.
        - intros; exact: tt.
        - intros; exact: tt.
      Defined.

    End Destruct_MorIndexer_Param_codomMultiply.

    Module Destruct_MorIndexer_Param_codomObIndexer_Param.

      Inductive morIndexer_codomObIndexer_Param : forall (A : obIndexer_Param) (A' : obIndexer),
        'Indexer(0 A' ~> ObIndexer_Param A @ MorIndexer_Param.morIndexer )0 %cong -> Type :=
      | MorIndexer_Constant : forall (A A' : obIndexer_Param) (a : 'Indexer(0 A' ~> A )0 %param),
          morIndexer_codomObIndexer_Param
            (MorIndexer_Constant ( MorIndexer_Param.MorIndexer_Param a )) .

      Definition morIndexer_codomObIndexer_ParamP_Type
                 (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %cong)  :=
        ltac:( destruct A; [ refine (morIndexer_codomObIndexer_Param a)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type) ] ).

      Lemma morIndexer_codomObIndexer_ParamP
        : forall A A' ( a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ), morIndexer_codomObIndexer_ParamP_Type a .
      Proof.
        intros. case: A' A / a .
        - destruct m . constructor 1. 
        - intros; exact: tt.
        - intros; exact: tt.
        - intros; exact: tt.
        - intros; exact: tt.
      Defined.

    End Destruct_MorIndexer_Param_codomObIndexer_Param.

  End Cong.

  Module OnceStruc.
    
    Section Section1.
    Import Cong.Ex_Notations.

    Variant morIndexer : obIndexer -> obIndexer -> Type :=

    (** (* not necessary ... *)

    | Iden : forall A : obIndexer, 'Indexer(0 A  ~> A )0 *)

    (** next constructors as basic form : *)

    (* not used in [convMorCoMod] , but for example of sense *)
    | Context1One : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Context1One.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* not used in [convMorCoMod] , but for example of sense *)
    | Context2One : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Context2One.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0

    (* used in [convMorCoMod] [PolyCoMod_morphism] *)
    | Assoc : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Assoc.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Pairing_morphism] *)
    | Sym : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Sym.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [UnitCoMod_PolyCoMod] *)
    | OneMultiplyL : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.OneMultiplyL.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [UnitCoMod_PolyCoMod] *)
    | OneMultiplyR : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.OneMultiplyR.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* not used in [convMorCoMod] , but for example of reverse arrow *)
    | OneMultiplyL_Rev : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.OneMultiplyL_Rev.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* not used in [convMorCoMod] , but for example of reverse arrow *)
    | OneMultiplyR_Rev : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.OneMultiplyR_Rev.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0

    (** next constructors may be definable form later using cong and many arrow-actions : *)

    (* may be used in [convMorCoMod] [Project1_Pairing] *)
    | SymContext1 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* may be used in [convMorCoMod] [Project2_Pairing] *)
    | SymContext2 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Pairing_morphism] *)
    | AssocContext1 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Pairing_morphism] *)
    | AssocContext2 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Pairing_Project1] *)
    | AssocMultiplyContext1 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocMultiplyContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Pairing_Project2] *)
    | AssocMultiplyContext2 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocMultiplyContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Project1_morphism] *)
    | SymMultiplyContext1 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymMultiplyContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    (* used in [convMorCoMod] [Project2_morphism] *)
    | SymMultiplyContext2 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymMultiplyContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Section1.

    Module Export Ex_Notations.
      Export Cong.Ex_Notations.
      Delimit Scope oncestruc_scope with oncestruc.
      Hint Constructors morIndexer.

      Notation "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A) : oncestruc_scope.
    End Ex_Notations.

    Module _Cong.

      Lemma Multiply_arrowL : ( forall B A A' : obIndexer, 'Indexer(0 A' ~>  A )0 ->
                                              'Indexer(0 (Multiply A' B) ~> (Multiply A B) )0 )%oncestruc.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14 | constructor 15 | constructor 16 ];
        apply: Cong.Multiply_arrowL; eassumption.
      Defined.
      Lemma Multiply_arrowR : ( forall A B B' : obIndexer, 'Indexer(0 B' ~>  B )0 ->
                                                    'Indexer(0 (Multiply A B') ~> (Multiply A B) )0 )%oncestruc.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14 | constructor 15 | constructor 16 ];
        apply: Cong.Multiply_arrowR; eassumption.
      Defined.

      Lemma Context1_arrow : ( forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                                   'Indexer(0 (Context1 A') ~> (Context1 A) )0 )%oncestruc.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14 | constructor 15 | constructor 16 ];
        apply: Cong.Context1_arrow; eassumption.
      Defined.

      Lemma Context2_arrow : ( forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                                   'Indexer(0 (Context2 A') ~> (Context2 A) )0 )%oncestruc.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14 | constructor 15 | constructor 16 ];
        apply: Cong.Context2_arrow; eassumption.
      Defined.

    End _Cong.

  End OnceStruc.

(**

** Lemma for commutation of parameter-polyarrowing along structure-arrow-action

One consequence of this rewrite-style presentation is that the constructor for the structure-arrow action on the morphisms is not real cuts . Therefore it does not lack to be eliminated/erased , for now ...

For sure , (parameter-polyarrowing)/polymorphism/cut-elimination cannot proceed beyond the (parameter-polyarrowings)/polymorphisms/cuts which are contained in the molecular morphisms generated by the atomic generating data ; but memo that the molecular parameter-polyarrowing [Mole.MorCoMod_Poly_Param] cut-constructor will be pseudo-erased from the solution molecules by accumulating it onto the atomic generating morphisms .

Now memo that oneself shall say , via the conversion-relation , how the parameter-arrow-action cut-constructor interacts/traverses/commutes along all the other constructors ( that is how each of these other constructors is parameter-polyarrowing ) . In particular oneself shall say [commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc] how the parameter-polyarrowing cut-constructor interacts/traverses/commutes along the structure-arrow-action constructor .

#+BEGIN_SRC coq :exports both :results silent **)

  Section Section1.

  Import OnceStruc.Ex_Notations.
  
  Local Ltac tac_Multiply_arrowL B A A' aa IHaa :=
    intros CC bb; inversion_clear bb;
    [ match goal with [X : Cong.MorIndexer_Param.morIndexer _ _ |- _ ] =>
                      solve [inversion X] end
    | match goal with [X : 'Indexer(0 _ ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      specialize (IHaa _ X); destruct IHaa as [IHBB0 [IHaa' IHbb'] ];
                      exists (Multiply IHBB0 B); clear X; destruct IHbb'; eauto end
    | match goal with [X : 'Indexer(0 ?B' ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      exists (Multiply A B') ; clear IHaa; eauto end ] .

  Local Ltac tac_Multiply_arrowR A B B' aa IHaa :=
    intros CC bb; inversion_clear bb;
    [ match goal with [X : Cong.MorIndexer_Param.morIndexer _ _ |- _ ] =>
                      solve [inversion X] end
    | match goal with [X : 'Indexer(0 ?A' ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      exists (Multiply A' B) ; clear IHaa; eauto end
    | match goal with [X : 'Indexer(0 _ ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      specialize (IHaa _ X); destruct IHaa as [IHBB0 [IHaa' IHbb'] ];
                      exists (Multiply A IHBB0); clear X; destruct IHbb'; eauto end ] .

  Local Ltac tac_Context1_arrow A A' aa IHaa :=
    intros CC bb; inversion_clear bb;
    [ match goal with [X : Cong.MorIndexer_Param.morIndexer _ _ |- _ ] =>
                      solve [inversion X] end
    | match goal with [X : 'Indexer(0 _ ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      specialize (IHaa _ X); destruct IHaa as [IHBB0 [IHaa' IHbb'] ];
                      exists (Context1 IHBB0); clear X; destruct IHbb'; eauto end ] .

  Local Ltac tac_Context2_arrow A A' aa IHaa :=
    intros CC bb; inversion_clear bb;
    [ match goal with [X : Cong.MorIndexer_Param.morIndexer _ _ |- _ ] =>
                      solve [inversion X] end
    | match goal with [X : 'Indexer(0 _ ~> _ @ Cong.MorIndexer_Param.morIndexer )0%cong |- _ ] =>
                      specialize (IHaa _ X); destruct IHaa as [IHBB0 [IHaa' IHbb'] ];
                      exists (Context2 IHBB0); clear X; destruct IHbb'; eauto end ] .

  Lemma commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA )0 %oncestruc),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                               ( 'Indexer(0 CC ~> BB0 )0 %oncestruc ) } .
  Proof.
    intros AA BB aa. case: aa => {AA}AA {BB}BB aa.

    (* Context1One ; Context2One *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] 
          | inversion_clear X0;
            [ solve [inversion X] ] ]
        | eexists; eauto 12 ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* Assoc *)
    induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] 
          | eexists; eauto 12
          | eexists; eauto 12 ]
        | eexists; eauto 12 ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* Sym *)
    induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | eexists; eauto 12
        | eexists; eauto 12 ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* OneMultiplyL *)
    induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] ]
        | eexists; eauto 12 ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .
    
    (* OneMultiplyR *)
    induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros; inversion_clear bb;
        [ solve [inversion X]
        | eexists; eauto 12
        | inversion_clear X;
          [ solve [inversion X0] ] ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* OneMultiplyL_Rev , OneMultiplyR_Rev *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb;
        eexists; eauto 15
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* SymContext1 , SymContext2 *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] 
          | eexists; eauto 12 ] ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* AssocContext1 , AssocContext2  *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] 
          | eexists; eauto 12
          | eexists; eauto 12 ] ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* AssocMultiplyContext1 , AssocMultiplyContext2 *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | inversion_clear X;
          [ solve [inversion X0] 
          | eexists; eauto 12 ]
        | eexists; eauto 12 ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

    (* SymMultiplyContext1 , SymMultiplyContext2 *)
    1-2 : induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ];
      [ destruct aa; intros CC bb; inversion_clear bb;
        [ solve [inversion X]
        | eexists; eauto 12
        | inversion_clear X;
          [ solve [inversion X0] 
          | eexists; eauto 12 ] ]
      | tac_Multiply_arrowL B A A' aa IHaa
      | tac_Multiply_arrowR A B B' aa IHaa
      | tac_Context1_arrow A A' aa IHaa
      | tac_Context2_arrow A A' aa IHaa ] .

  Defined.

  End Section1.

End Indexer.

(**

* Generating data multifolded-enriched ref some indexer

Oneself shall start from some generating data which is multifolded/enriched ref some indexer ( symmetric-associative-monoidal metalogic/metacategory ) and then grammatically add pairing-projections ( "product" ) . But there are 2 intermediate steps .

Primo the atomic generating morphisms are obtained by coupling/accumulating parameter-polyarrowing onto the generating data . For sure all the other parameter-polyarrowing cut-constructors will ultimately be accumulated onto these atomic generating morphisms .

Secondo the molecular morphisms are obtained by starting from the atomic generating morphisms and then grammatically inductively-adding the polymorphism cut-constructor and the parameter-polyarrowing cut-constructor . For sure all the other polymorphism cut-constructors will ultimately either be eliminated/erased or be molecularized/absorbed into this molecular morphisms subgrammar .

Finally , as common , the molecular morphisms will be injected into the entire of the morphisms . The form of the inductive-family-presentation [Mole.morCoMod] of the molecular morphisms will be explained in the next section which describes the entire of the morphisms .

#+BEGIN_SRC coq :exports both :results silent **)

Import Indexer.OnceStruc.Ex_Notations.

Parameter obCoMod_Gen : Type.
Parameter morCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param), Type.

Reserved Notation "''CoMod' (0 A |- F' ~> F )0" (at level 0, format "''CoMod' (0  A  |-  F'  ~>  F  )0").

Reserved Notation "gg0 <~~ gg" (at level 70).

Module Mole.

  Inductive obCoMod : Type := 
  | ObCoMod_Gen : obCoMod_Gen -> obCoMod .

  Section Section1.
  Delimit Scope mole_scope with mole.

  Inductive morCoMod : obCoMod -> obCoMod -> obIndexer -> Type :=

  | MorCoMod_Poly_Param : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A  @ Cong.MorIndexer_Param.morIndexer )0 % cong),
        'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

  | PolyCoMod : forall (F F' : obCoMod) A,
      'CoMod(0 A |- F' ~> F )0 -> forall (F'' : obCoMod) B,
        'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Multiply A B |- F'' ~> F )0

  | MorCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param),
      @morCoMod_Gen F G A -> forall A' (a : 'Indexer(0 A' ~> A )0 %param),
        'CoMod(0 ObIndexer_Param A' |- (ObCoMod_Gen F) ~> (ObCoMod_Gen G) )0

  where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : mole_scope. 

  End Section1.

  Module Import Ex_Notations0.
    Delimit Scope mole_scope with mole.

    Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : mole_scope. 

    (*  *  in  o>*  says multiplication *)
    Notation "a o>* ff" :=
      (@MorCoMod_Poly_Param _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : mole_scope.

    Notation "ff_ o>CoMod ff'" :=
      (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : mole_scope.

    (*  @  in  o>*@  says atomic or accumulated *)
    Notation "a o>*@ ''MorCoMod_Gen' ff" :=
      (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : mole_scope.
  End Ex_Notations0.

  Local Open Scope mole_scope.

  Inductive convMorCoMod : forall (F G : obCoMod) (A : obIndexer) (gg gg0 : 'CoMod(0 A |- F ~> G )0), Prop :=

  | convMorCoMod_Refl : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
      gg <~~ gg

  | convMorCoMod_Trans :
      forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
        (uTrans : 'CoMod(0 A |- F ~> G )0 ),
        uTrans <~~ gg -> forall  (gg00 : 'CoMod(0 A |- F ~> G )0 ),
          gg00 <~~ uTrans -> gg00 <~~ gg

  | MorCoMod_Poly_Param_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
        forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
          gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )
                                    
  | PolyCoMod_cong_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0),
      forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0 )  (ff_0 : 'CoMod(0 B |- F'' ~> F' )0 ),
        ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

  | PolyCoMod_cong_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 )
                            (ff'0 : 'CoMod(0 A |- F' ~> F )0 ),
      forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
        ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

  | MorCoMod_Poly_Param_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 ) (F'' : obCoMod) B
                                    (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      forall B' (b : 'Indexer(0 B' ~> B @ Cong.MorIndexer_Param.morIndexer )0 %cong),

        ( ( b o>* ff_ ) o>CoMod ( ff' ) )
          <~~ ( (Cong.Multiply_arrowR A b) o>* (ff_ o>CoMod ff') )

  | MorCoMod_Poly_Param_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                                   (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

        ( ( ff_ ) o>CoMod ( a o>* ff' ) )
          <~~ ( (Cong.Multiply_arrowL B a) o>* (ff_ o>CoMod ff') )

  | MorCoMod_Gen_MorCoMod_Poly_Param : forall (F G : obCoMod_Gen) (A : obIndexer_Param)
                     (gg : @morCoMod_Gen F G A) A' (a : 'Indexer(0 A' ~> A )0 %param),
      forall A'' (a' : 'Indexer(0 A'' ~> A' )0 %param),

        ( ( (a' o>Indexer a)%param ) o>*@ 'MorCoMod_Gen gg )
          <~~ ( ( Cong.MorIndexer_Constant (Cong.MorIndexer_Param.MorIndexer_Param a') )
                o>* ( a o>*@ 'MorCoMod_Gen gg ) )
              
  where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0) : mole_scope.

  Module Export Ex_Notations.
    Export Ex_Notations0.
    Notation "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0) : mole_scope.
    Hint Constructors convMorCoMod.
  End Ex_Notations.
  
End Mole.

(**#+END_SRC

* Grammatical presentation of objects and morphisms multifolded/enriched ref some indexer , by distinguishing parameter-polyarrowing from structure-arrow-action

For multifolded/enriched polymorph mathematics , each object can be touched individually but the morphisms can no longer be touched individually , and many morphisms shall be touched at the same time via some indexing/multiplier .

Each decoding ( "Yoneda" ) of some index-for-morphisms which encodes all the morphisms-at-some-domain-codomain is some metafunctor , which is programmed by the inductive-family-presentation [morCoMod] whose additional/embedded constructors [MorCoMod_Poly_Param] [MorCoMod_Poly_Struc] signify the functoriality ( "arrows-action" ) . Any (computed) index argument of the inductive-family-presentation [morCoMod] of morphisms is named the multiplicity of the morphism .

Each decoding ( "Yoneda" ) of the whatever-is-interesting arrows between the indexes-for-morphisms are metatransformations which are programmed as some grammatical-constructors of the inductive-family-presentation [morCoMod] .

Memo that the functoriality ( "arrows-action" ) of each metafunctor (decoded index-for-morphisms) and the naturality ( "arrows-action" ) of each metatransformation (decoded arrow-between-indexes) is signified via the additional/embedded constructors [MorCoMod_Poly_Param] [MorCoMod_Poly_Struc] of the inductive-family-presentation [morCoMod] or is immediately-accumulated onto the atomic generating morphisms [MorCoMod_Gen] . All this is effected via the conversion relation [convMorCoMod] which relates those grammatical-morphisms . Also memo that here (parameter-polyarrowing)/polymorphism/cut-elimination says that both this cut-constructor for parameter-arrows ( "arrow-action" , "polyarrowing" ) and the common cut-constructor for morphisms ( "composition" , "polymorphism" ) are eliminated/erased . For sure , the structure-arrow-action is not questionable real-cut and does not lack to be eliminated/erased . 

For multifolded-enriched polymorph mathematics , the common operations on the morphisms are multiplicative ; this contrast from internal polymorph mathematics where moreover many objects are touched at the same time and the common operations on the objects or morphisms are coordinatewise/dimensional/pointwise .

#+BEGIN_SRC coq :exports both :results silent **)

Import Mole.Ex_Notations.

Inductive obCoMod : Type := 
| ObCoMod_Mole : Mole.obCoMod -> obCoMod
| Pair : obCoMod -> obCoMod -> obCoMod .

Inductive morCoMod : obCoMod -> obCoMod -> (* THIS IS COMPUTED INDEX *) obIndexer -> Type :=

| MorCoMod_Poly_Param :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A  @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

| PolyCoMod : forall (F F' : obCoMod) A,
      'CoMod(0 A |- F' ~> F )0 -> forall (F'' : obCoMod) B,
        'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Multiply A B |- F'' ~> F )0

| MorCoMod_Poly_Struc :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
      'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

| UnitCoMod : forall (F : obCoMod),
    'CoMod(0 One |- F ~> F )0

| MorCoMod_Mole : forall (F G : Mole.obCoMod) A,
    'CoMod(0 A |- F ~> G )0 %mole -> 'CoMod(0 A |- (ObCoMod_Mole F) ~> (ObCoMod_Mole G) )0

| Project1 : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A,
    'CoMod(0 A |- F1 ~> Z1 )0 ->
    'CoMod(0 Context1 A |- (Pair F1 F2) ~> Z1 )0

| Project2 : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A,
    'CoMod(0 A |- F2 ~> Z2 )0 ->
    'CoMod(0 Context2 A |- (Pair F1 F2) ~> Z2 )0

| Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A,
    'CoMod(0 Context1 A |- L ~> F1 )0 -> 'CoMod(0 Context2 A |- L ~> F2 )0 ->
    'CoMod(0 A |- L ~> (Pair F1 F2) )0

where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : poly_scope. 

(*  *  in  o>*  says multiplication *)
Notation "a o>* ff" :=
  (@MorCoMod_Poly_Param _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : poly_scope.

Notation "ff_ o>CoMod ff'" :=
  (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : poly_scope.

(*  $  in  o>*$  says structural *)
Notation "a o>*$ ff" :=
  (@MorCoMod_Poly_Struc _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : poly_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod F) (at level 10, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : poly_scope.

Notation "''MorCoMod_Mole' ff" :=
      (@MorCoMod_Mole _ _ _ ff) (at level 3) : poly_scope.

(*  @  in  ~_1 @   says argument *)
Notation "~_1 @ F2 o>CoMod zz1" :=
  (@Project1 _ F2 _ _ zz1) (at level 4, F2 at next level) : poly_scope.

Notation "~_1 o>CoMod zz1" :=
  (@Project1 _ _ _ _ zz1) (at level 4) : poly_scope.

(*  @  in  ~_2 @   says argument *)
Notation "~_2 @ F1 o>CoMod zz2" :=
  (@Project2 F1 _ _ _ zz2) (at level 4, F1 at next level) : poly_scope.

Notation "~_2 o>CoMod zz2" :=
  (@Project2 _ _ _ _ zz2) (at level 4) : poly_scope.

Notation "<< ff1 ,CoMod ff2 >>" :=
  (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : poly_scope.

(**#+END_SRC

* Grammatical conversions of morphisms , which infer the same multiplicity-computation

As common , the grammatical conversions are classified into the total/(multi-step) conversions , and the congruences conversions , and the constant conversions which are used in the polyarrowing/polymorphism/cut-elimination lemma , and the constant conversions which are only for the wanted sense of pairing-projections-grammar , and the constant conversions which are only for the confluence lemma , and the constant conversions which are derivable by using the finished cut-elimination lemma .

Also in contrast , because of the embedded/computed multiplicity extra-argument/parameter in the inductive-family-presentation of the morphisms , the conversion-relation would convert across two morphisms whose multiplicities-computation arguments are not syntactically/grammatically-the-same. But oneself does show that , by structure-arrow-action ( metalogic-deduction ) , these two multiplicities are indeed ( symmetric-associative-monoidal-metalogic ) propositionally equal ( "soundness lemma" ) . Therefore oneself successfully avoids converting across non grammatically-same multiplicity indexes , for now ... Anyway the sense-conversions [Project1_Pairing] [Project2_Pairing] , in the polyarrowing-polymorphism terminology and in the solution terminology , are forcing the explicit presence of the structure-arrow-action constructor into the grammar instead of externally , for now ...

Finally , some linear total/asymptotic grade is defined on the morphisms and the tactics-automated degradation lemma shows that each of the conversion indeed degrades the redex morphism . (ERRATA: Memo that this new grade function is simplified in comparison from earlier attempts , because strict-degrading-of-the-conversions is not really required but some form of strict-degrading occurs during the computational/total/asymptotic cut-elimination ... )

** Grammatical conversions of morphisms

#+BEGIN_SRC coq :exports both :results silent **)

Inductive convMorCoMod : forall (F G : obCoMod) (A : obIndexer) (gg gg0 : 'CoMod(0 A |- F ~> G )0 %poly), Prop :=

(**  ----- the total/(multi-step) conversions -----  **)

  
| convMorCoMod_Refl : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
    gg <~~ gg

| convMorCoMod_Trans :
    forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
      (uTrans : 'CoMod(0 A |- F ~> G )0 ),
      uTrans <~~ gg -> forall  (gg00 : 'CoMod(0 A |- F ~> G )0 ),
        gg00 <~~ uTrans -> gg00 <~~ gg


(**  ----- the congruences conversions -----  **)

                             
| MorCoMod_Poly_Param_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
      gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )

| PolyCoMod_cong_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0),
    forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0 )  (ff_0 : 'CoMod(0 B |- F'' ~> F' )0 ),
      ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

| PolyCoMod_cong_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 )
                           (ff'0 : 'CoMod(0 A |- F' ~> F )0 ),
    forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

| MorCoMod_Poly_Struc_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
      forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
      gg0 <~~ gg -> ( a o>*$ gg0 ) <~~ ( a o>*$ gg )

| MorCoMod_Mole_cong : forall (F G : Mole.obCoMod) A (gg gg0 : 'CoMod(0 A |- F ~> G )0 %mole ),
    ( gg0 <~~ gg )%mole -> ( 'MorCoMod_Mole gg0 ) <~~ ( 'MorCoMod_Mole gg )
                                        
| Project1_cong : forall (F1 F2 Z1 : obCoMod) A (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0)
                     (zz1' : 'CoMod(0 A |- F1 ~> Z1 )0),
        zz1' <~~ zz1 ->
        ( ~_1 @ F2 o>CoMod zz1' ) <~~ ( ~_1 @ F2 o>CoMod zz1 )

| Project2_cong : forall (F1 F2 Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0)
                    (zz2' : 'CoMod(0 A |- F2 ~> Z2 )0),
        zz2' <~~ zz2 ->
        ( ~_2 @ F1 o>CoMod zz2' ) <~~ ( ~_2 @ F1 o>CoMod zz2 )

| Pairing_cong_1 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                     (ff1 ff1' : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    ff1' <~~ ff1 -> ( << ff1' ,CoMod ff2 >> ) <~~ ( << ff1 ,CoMod ff2 >> )
    
| Pairing_cong_2 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                     (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 ff2' : 'CoMod(0 Context2 A |- L ~> F2 )0),
    ff2' <~~ ff2 -> ( << ff1 ,CoMod ff2' >> ) <~~ ( << ff1 ,CoMod ff2 >> )


(**  ----- the constant conversions which are used during the polyarrowing elimination -----  **)

                                           
| MorCoMod_Poly_Struc_MorCoMod_Poly_Param : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
      forall (gg : 'CoMod(0 A |- F ~> G )0),
      forall (A'' : obIndexer) (a' : 'Indexer(0 A'' ~> A' @ Cong.MorIndexer_Param.morIndexer )0 %cong),
        ( (snd (projT2 (commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc a a')))
            o>*$ ( (fst (projT2 (commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc a a')))
                    o>* gg ) )
          <~~ ( a' o>* ( a o>*$ gg ) )

| MorCoMod_Mole_MorCoMod_Poly_Param : forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %mole),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ( 'MorCoMod_Mole ( (a o>* gg)%mole ) )%poly )
        <~~ ( ( a o>* ( 'MorCoMod_Mole gg ) )%poly )

| Project1_MorCoMod_Poly_Param : forall (F1 F2 : obCoMod) (Z1 : obCoMod) (A : obIndexer) (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ~_1 @ F2 o>CoMod (a o>* zz1) )
        <~~ ( (Cong.Context1_arrow a) o>* ( ~_1 @ F2 o>CoMod zz1 ) )

| Project2_MorCoMod_Poly_Param : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ~_2 @ F1 o>CoMod (a o>* zz2) )
        <~~ ( (Cong.Context2_arrow a) o>* ( ~_2 @ F1 o>CoMod zz2 ) )

(* memo this non-linearity for the arrow-action *)
| Pairing_MorCoMod_Poly_Param : forall (L : obCoMod) (F1 F2 : obCoMod) A
                    (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      (  << (Cong.Context1_arrow a) o>* ff1 ,CoMod (Cong.Context2_arrow a) o>* ff2 >> )
        <~~ ( a o>* ( << ff1 ,CoMod ff2 >> ) )


(**  ----- the constant conversions which are used during the polymorphism elimination -----  **)

        
| MorCoMod_Poly_Struc_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall B' (b : 'Indexer(0 B' ~> B )0 %oncestruc),
        ( (OnceStruc._Cong.Multiply_arrowR A b) o>*$ (ff_ o>CoMod ff') )
          <~~ ( ( b o>*$ ff_ ) o>CoMod ( ff' ) )

| MorCoMod_Poly_Struc_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall A' (a : 'Indexer(0 A' ~> A )0 %oncestruc),
        ( (OnceStruc._Cong.Multiply_arrowL B a) o>*$ (ff_ o>CoMod ff') )
          <~~ ( ff_ o>CoMod ( a o>*$ ff' ) )

| UnitCoMod_morphism_Pre : forall (F : obCoMod), forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F )0),
      ( (OnceStruc.OneMultiplyL (Cong.MorIndexer_Constant (Cong.OneMultiplyL.OneMultiplyL _)))
         o>*$ ff_ )
        <~~ ( ff_ o>CoMod ( @'UnitCoMod F ) )

| UnitCoMod_morphism_Post : forall (F : obCoMod), forall (F' : obCoMod) B (ff' : 'CoMod(0 B |- F ~> F' )0),
      ( (OnceStruc.OneMultiplyR (Cong.MorIndexer_Constant (Cong.OneMultiplyR.OneMultiplyR _)))
          o>*$ ff' ) <~~ ( (@'UnitCoMod F) o>CoMod ff' )

| MorCoMod_Mole_morphism : forall (F' F : Mole.obCoMod) A
    (gg' : 'CoMod(0 A |- F' ~> F )0 %mole) (F'' : Mole.obCoMod) B
    (gg_ : 'CoMod(0 B |- F'' ~> F' )0 %mole),
    ( 'MorCoMod_Mole ( gg_ o>CoMod gg' )%mole )
      <~~ ( ( 'MorCoMod_Mole gg_ ) o>CoMod ( 'MorCoMod_Mole gg' ) )%poly

| Project1_morphism : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A,
      forall (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0), forall (Y1 : obCoMod) B (yy : 'CoMod(0 B |- Z1 ~> Y1 )0),

          ((OnceStruc.SymMultiplyContext1 (Cong.MorIndexer_Constant (Cong.SymMultiplyContext1.SymMultiplyContext1 _ _)))
             o>*$ ( ~_1 @ F2 o>CoMod (zz1 o>CoMod yy) )) 
              <~~ ( ( ~_1 @ F2 o>CoMod zz1 ) o>CoMod yy ) 

| Project2_morphism : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A,
      forall (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0), forall (Y2 : obCoMod) B (yy : 'CoMod(0 B |- Z2 ~> Y2 )0),

          ((OnceStruc.SymMultiplyContext2 (Cong.MorIndexer_Constant (Cong.SymMultiplyContext2.SymMultiplyContext2 _ _)))
             o>*$ ( ~_2 @ F1 o>CoMod (zz2 o>CoMod yy) ) )
              <~~ ( ( ~_2 @ F1 o>CoMod zz2 ) o>CoMod yy ) 

(* memo this non-linearity for the morphism-action *)
| Pairing_morphism : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (L' : obCoMod) B (ll : 'CoMod(0 B |- L' ~> L )0),

      ( (OnceStruc.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
           o>*$ ( << (OnceStruc.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*$ (ll o>CoMod ff1)
        ,CoMod (OnceStruc.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*$ (ll o>CoMod ff2) >> ) ) 
        <~~ ( ll o>CoMod ( << ff1 ,CoMod ff2 >> ) )

| Pairing_Project1 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (Z1 : obCoMod) B, forall (zz1 : 'CoMod(0 B |- F1 ~> Z1 )0),

        ( (OnceStruc.AssocMultiplyContext1 (Cong.MorIndexer_Constant (Cong.AssocMultiplyContext1.AssocMultiplyContext1 _ _)))
            o>*$ ( ff1 o>CoMod zz1 ) )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1 ) ) 

| Pairing_Project2 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (Z2 : obCoMod) B, forall (zz2 : 'CoMod(0 B |- F2 ~> Z2 )0),

        (  (OnceStruc.AssocMultiplyContext2 (Cong.MorIndexer_Constant (Cong.AssocMultiplyContext2.AssocMultiplyContext2 _ _)))
            o>*$ ( ff2 o>CoMod zz2 ) )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2 ) )


(**  ----- the constant conversions which are only for the wanted sense of pairing-projections-grammar -----  **)

        
(* for sense only , also in the intermediate solution ,  not for reduction  *)
| Project1_MorCoMod_Poly_Struc : forall (F1 F2 : obCoMod) (Z1 : obCoMod) (A : obIndexer) (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),

      ( ~_1 @ F2 o>CoMod (a o>*$ zz1) )
        <~~ ( (OnceStruc._Cong.Context1_arrow a) o>*$ ( ~_1 @ F2 o>CoMod zz1 ) )

(* for sense only , also in the intermediate solution ,  not for reduction  *)
| Project2_MorCoMod_Poly_Struc : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),

      ( ~_2 @ F1 o>CoMod (a o>*$ zz2) )
        <~~ ( (OnceStruc._Cong.Context2_arrow a) o>*$ ( ~_2 @ F1 o>CoMod zz2 ) )

(* for sense only , also in the intermediate solution ,  not for reduction , memo this non-linearity for the arrow-action *)
| Pairing_MorCoMod_Poly_Struc : forall (L : obCoMod) (F1 F2 : obCoMod) A
                    (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall A' (a : 'Indexer(0 A' ~> A )0 %oncestruc),

      (  << (OnceStruc._Cong.Context1_arrow a) o>*$ ff1 ,CoMod (OnceStruc._Cong.Context2_arrow a) o>*$ ff2 >> )
        <~~ ( a o>*$ ( << ff1 ,CoMod ff2 >> ) )

(* for sense only , also in the intermediate solution ,  not for primo reduction , but may for secondo reduction *)
| Project1_Project2_Pairing : forall (F1 F2 : obCoMod),

    ( @ 'UnitCoMod (Pair F1 F2) )
      <~~ ( << ( ~_1 @ F2 o>CoMod ( @ 'UnitCoMod F1 ) )
          ,CoMod ( ~_2 @ F1 o>CoMod ( @ 'UnitCoMod F2 ) ) >> )

(**  ----- the constant conversions which are only for the confluence lemma -----  **)

(* for confluence , also in the intermediate solution , immediately-derivable in the polyarrowing-polymorphism terminology , not for primo reduction , but may for secondo reduction *)
(*ALT: in non-generalized form , change   a o>*$   to   (OnceStruc.SymContext2 (Cong.MorIndexer_Constant (Cong.SymContext2.SymContext2 _ ))) o>*$    ,
but memo that only existence/propositional knowledge is lacked  *)
| Project1_Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0)  (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0) (H : obCoMod),
    forall (a : 'Indexer(0 Context2 (Context1 A) ~> Context1 (Context2 A) )0%oncestruc),
    ( ~_1 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( ~_1 @ H o>CoMod ff1 )
          ,CoMod ( a o>*$ ( ~_1 @ H o>CoMod ff2 ) ) >> )

(* for confluence , also in the intermediate solution , immediately-derivable in the polyarrowing-polymorphism terminology , not for primo reduction , but may for secondo reduction *)
(*ALT: in non-generalized form , change   a o>*$   to   (OnceStruc.SymContext1 (Cong.MorIndexer_Constant (Cong.SymContext1.SymContext1 _ ))) o>*$    ,
but memo that only existence/propositional knowledge is lacked  *)
| Project2_Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0) (H : obCoMod),
    forall (a : 'Indexer(0 Context1 (Context2 A) ~> Context2 (Context1 A) )0%oncestruc),
    ( ~_2 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( a o>*$ ( ~_2 @ H o>CoMod ff1 ) )
          ,CoMod ( ~_2 @ H o>CoMod ff2 ) >> )


(**  ----- the constant conversions which are derivable by using the finished cut-elimination lemma -----  **)

        
(*TODO: COMMENT *)        
(*  derivable by using the finished cut-elimination lemma  , for sense only , not in solution , NOT FOR ANY REDUCTION *)
| MorCoMod_Poly_Param_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall B' (b : 'Indexer(0 B' ~> B @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      ( ( b o>* ff_ ) o>CoMod ( ff' ) )
        <~~ ( (Cong.Multiply_arrowR A b) o>* (ff_ o>CoMod ff') )

(*TODO: COMMENT *)        
(* derivable by using the finished cut-elimination lemma , for sense only , not in solution , NOT FOR ANY REDUCTION  *)
| MorCoMod_Poly_Param_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      ( ( ff_ ) o>CoMod ( a o>* ff' ) )
        <~~ ( (Cong.Multiply_arrowL B a) o>* (ff_ o>CoMod ff') )

(*TODO: COMMENT *)
(** (*  derivable by using the finished cut-elimination lemma , for sense only , not in solution , NOT FOR ANY REDUCTION *)
| PolyCoMod_morphism : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                         (ff_' : 'CoMod(0 B |- F'' ~> F' )0),
    forall (F''' : obCoMod) C (ff__ : 'CoMod(0 C |- F''' ~> F'' )0),
      
      ( (OnceStruc.Assoc (Cong.MorIndexer_Constant (Cong.Assoc.Assoc _ _ _)))
          o>*$ ( ( ff__ o>CoMod ff_' ) o>CoMod ff' ) )
        <~~ ( ff__ o>CoMod ( ff_' o>CoMod ff' ) )   **)


where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0).

Hint Constructors convMorCoMod.

(**#+END_SRC

** Same multiplicity-computation for convertible morphisms

In reality , the resolution to the final solution shall occur in two phases . The primo phase is the (parameter-polyarrowing)/polymorphism/cut-elimination from the polyarrowing-polymorphism terminology to the intermediate-solution terminology ; this is described here . The secondo phase is the erasure/elimination/externalization of the structure-arrow-action constructor ( and all multiplicity knowledge ) from the intermediate-solution terminology to the final-solution terminology ; this secondo phase is some style of "change of coefficients" ( total-reduction style ... ) along some metalogical functor into the trivial (One) metalogic ...

Here the conversion-relation would convert across two morphisms whose multiplicities-computation arguments are not syntactically/grammatically-the-same. But oneself does show that , by structure-arrow-action ( metalogic-deduction ) , these two multiplicities are indeed ( symmetric-associative-monoidal-metalogic ) propositionally equal ( "soundness lemma" ) . Therefore oneself successfully avoids converting across non grammatically-same multiplicity indexes , for now ... Anyway the sense-conversions [Project1_Pairing] [Project2_Pairing] , in the polyarrowing-polymorphism terminology and in the solution terminology , are forcing the explicit presence of the structure-arrow-action constructor into the grammar instead of externally , for now ... 

#+BEGIN_SRC coq :exports both :results silent **)

(**#+END_SRC

** Linear total/asymptotic grade and the degradation lemma

#+BEGIN_SRC coq :exports both :results silent **)

Notation max m n := ((m + (Nat.sub n m))%coq_nat).

Fixpoint grade_Mole (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %mole) {struct gg} : nat . 
Proof.
  case : F G A / gg . 
  - intros ? ? ? ? a gg .
    exact: (S (grade_Mole _ _ _ gg)  + S (grade_Mole _ _ _ gg)  )%coq_nat .
  - intros ? ? ? ff' ? ? ff_ .
    exact: (S (grade_Mole _ _ _ ff' + grade_Mole _ _ _ ff_)%coq_nat )%coq_nat .
  - intros. exact: (S O).
Defined.

Fixpoint grade (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ) {struct gg} : nat . 
Proof.
  case : F G A / gg . 
  - intros ? ? ? ? a gg .
    exact: (S (grade _ _ _ gg) + S (grade _ _ _ gg) )%coq_nat .
  - intros ? ? ? ff' ? ? ff_ .
    exact: (S (grade _ _ _ ff' + grade _ _ _ ff_)%coq_nat + S (grade _ _ _ ff' + grade _ _ _ ff_)%coq_nat)%coq_nat .
  - intros ? ? ? ? a gg .
    exact: (S (grade _ _ _ gg)  )%coq_nat .
  - intros. exact: (S O).
  - intros ? ? ? gg. exact: (S (grade_Mole gg)).
  - intros ? ? ? ? zz1 .
    exact: (S (S (grade _ _ _ zz1))).
  - intros ? ? ? ? zz2 .
    exact: (S (S (grade _ _ _ zz2))).
  - intros ? ? ? ? ff1 ff2 .
    refine (S (S (max (grade _ _ _ ff1) (grade _ _ _ ff2)))).
Defined.

Lemma grade_Mole_gt0 : forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %mole),
     ((S O) <= (grade_Mole gg))%coq_nat.
Proof. intros; case : gg; intros; apply/leP; intros; simpl; auto. Qed.

Lemma grade_gt0 : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
     ((S O) <= (grade gg))%coq_nat.
Proof. intros; case : gg; intros; try exact: grade_Mole_gt0; apply/leP; intros; simpl; auto. Qed.

Ltac tac_grade_Mole_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 %mole |- _ ] =>
    move : (@grade_Mole_gt0 _ _ _ gg1) (@grade_Mole_gt0 _ _ _ gg2)
                                          (@grade_Mole_gt0 _ _ _ gg3)
                                          (@grade_Mole_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 %mole |- _ ] =>
    move : (@grade_Mole_gt0 _ _ _ gg1) (@grade_Mole_gt0 _ _ _ gg2)
                                          (@grade_Mole_gt0 _ _ _ gg3)
                                          (@grade_Mole_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %mole |- _ ] =>
    move : (@grade_Mole_gt0 _ _ _ gg1) (@grade_Mole_gt0 _ _ _ gg2)
                                          (@grade_Mole_gt0 _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %mole ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %mole  |- _ ] =>
    move : (@grade_Mole_gt0 _ _ _ gg1) (@grade_Mole_gt0 _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %mole  |- _ ] =>
    move : (@grade_Mole_gt0 _ _ _ gg1) 
  end.

Ltac tac_grade_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
                                          (@grade_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
                                          (@grade_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)
                                          (@grade_gt0 _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) (@grade_gt0 _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0  |- _ ] =>
    move : (@grade_gt0 _ _ _ gg1) 
  end.

Lemma degrade_Mole
  : ( forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
      (gg0 : 'CoMod(0 A |- F ~> G )0 ),
        gg0 <~~ gg -> ( grade_Mole gg0 <= grade_Mole gg )%coq_nat )%mole .
Proof.
  intros until gg0. intros red_gg.
  elim : F G A gg gg0 / red_gg ;
    try solve [ simpl; intros; abstract intuition Omega.omega ]. 
Qed.

Lemma degrade
  : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
      (gg0 : 'CoMod(0 A |- F ~> G )0 ),
    gg0 <~~ gg -> ( grade gg0 <= grade gg )%coq_nat .
Proof.
  intros until gg0. intros red_gg.
  elim : F G A gg gg0 / red_gg ;
    try solve [ simpl; intros;
                try match goal with
                    | [ Hred : ( _ <~~ _ )%mole |- _ ] =>
                      move : (degrade_Mole Hred) ; clear Hred
                    end;
                abstract intuition Omega.omega ]. 
Qed.

Ltac tac_degrade H_grade :=
  repeat match goal with
         | [ Hred : ( _ <~~ _ )%mole |- _ ] =>
           move : (degrade_Mole Hred) ; clear Hred
         | [ Hred : ( _ <~~ _ ) |- _ ] =>
           move : (degrade Hred) ; clear Hred
         end;
  move: H_grade; simpl; intros;
  try tac_grade_Mole_gt0; try tac_grade_gt0; intros; Omega.omega.

(**#+END_SRC

* Solution

As common, the purely-grammatical (parameter-)polyarrowing [MorCoMod_Poly_Param] cut-constructor and polymorphism cut-constructor [PolyCoMod] are not part of the intermediate-solution terminology . Memo that the structure-arrow action on the morphisms is not real cuts ; therefore it does not lack to be eliminated/erased/externalized for now until the final solution .

For sure , (parameter-polyarrowing)/polymorphism/cut-elimination cannot proceed beyond the (parameter-polyarrowings)/polymorphisms/cuts which are contained in the molecular morphisms generated by the atomic generating data ; but memo that the molecular parameter-polyarrowing [Mole.MorCoMod_Poly_Param] cut-constructor will be pseudo-erased from the solution molecules [Sol.Mole.morCoMod] by accumulating it onto the atomic generating morphisms .

** Solution morphisms without (parameter-polyarrowing)/polymorphism

#+BEGIN_SRC coq :exports both :results silent **)

Module Sol.

  Module Mole.

    Section Section1.
    Delimit Scope sol_mole_scope with sol_mole.

    Inductive morCoMod : Mole.obCoMod -> Mole.obCoMod -> obIndexer -> Type :=

    | PolyCoMod : forall (F F' : Mole.obCoMod) A,
        'CoMod(0 A |- F' ~> F )0 -> forall (F'' : Mole.obCoMod) B,
          'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Multiply A B |- F'' ~> F )0

    | MorCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param),
        @morCoMod_Gen F G A -> forall A' (a : 'Indexer(0 A' ~> A )0 %param),
          'CoMod(0 ObIndexer_Param A' |- (Mole.ObCoMod_Gen F) ~> (Mole.ObCoMod_Gen G) )0

    where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_mole_scope. 

    End Section1.

    Module Export Ex_Notations.
      Delimit Scope sol_mole_scope with sol_mole.

      Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_mole_scope. 

      Notation "ff_ o>CoMod ff'" :=
        (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : sol_mole_scope.

      (*  @  in  o>*@  says atomic or accumulated *)
      Notation "a o>*@ ''MorCoMod_Gen' ff" :=
        (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : sol_mole_scope.
    End Ex_Notations.

  End Mole.

  Section Section1.
  Import Mole.Ex_Notations.
  Delimit Scope sol_scope with sol.

  Inductive morCoMod : obCoMod -> obCoMod -> obIndexer -> Type :=

  | MorCoMod_Poly_Struc :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
        'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

  | UnitCoMod : forall (F : obCoMod),
      'CoMod(0 One |- F ~> F )0

  | MorCoMod_Mole : forall (F G : Mole.obCoMod) A,
      'CoMod(0 A |- F ~> G )0 %sol_mole -> 'CoMod(0 A |- (ObCoMod_Mole F) ~> (ObCoMod_Mole G) )0

  | Project1 : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A,
      'CoMod(0 A |- F1 ~> Z1 )0 ->
      'CoMod(0 Context1 A |- (Pair F1 F2) ~> Z1 )0

  | Project2 : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A,
      'CoMod(0 A |- F2 ~> Z2 )0 ->
      'CoMod(0 Context2 A |- (Pair F1 F2) ~> Z2 )0

  | Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A,
      'CoMod(0 Context1 A |- L ~> F1 )0 -> 'CoMod(0 Context2 A |- L ~> F2 )0 ->
      'CoMod(0 A |- L ~> (Pair F1 F2) )0

  where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_scope. 
  
  End Section1.

  Module Export Ex_Notations.
    Export Mole.Ex_Notations.
    Delimit Scope sol_scope with sol.

    Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_scope. 

    (*  $  in  o>*$  says structural *)
    Notation "a o>*$ ff" :=
      (@MorCoMod_Poly_Struc _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : sol_scope.

    Notation "@ ''UnitCoMod' F" := (@UnitCoMod F) (at level 10, only parsing) : sol_scope.

    Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : sol_scope.

    Notation "''MorCoMod_Mole' ff" :=
      (@MorCoMod_Mole _ _ _ ff) (at level 3) : sol_scope.

    (*  @  in  ~_1 @   says argument *)
    Notation "~_1 @ F2 o>CoMod zz1" :=
      (@Project1 _ F2 _ _ zz1) (at level 4, F2 at next level) : sol_scope.

    Notation "~_1 o>CoMod zz1" :=
      (@Project1 _ _ _ _ zz1) (at level 4) : sol_scope.

    (*  @  in  ~_2 @   says argument *)
    Notation "~_2 @ F1 o>CoMod zz2" :=
      (@Project2 F1 _ _ _ zz2) (at level 4, F1 at next level) : sol_scope.

    Notation "~_2 o>CoMod zz2" :=
      (@Project2 _ _ _ _ zz2) (at level 4) : sol_scope.

    Notation "<< ff1 ,CoMod ff2 >>" :=
      (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : sol_scope.

  End Ex_Notations.

  Fixpoint toPolyMor_Mole (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol_mole)
           {struct gg} : 'CoMod(0 A |- F ~> G )0 %mole . 
  Proof.
    refine match gg with
           | ( ff_ o>CoMod ff' )%sol_mole => ( (toPolyMor_Mole _ _ _ ff_) o>CoMod (toPolyMor_Mole _ _ _ ff') )%mole
           | ( a o>*@ 'MorCoMod_Gen gg )%sol_mole => ( a o>*@ 'MorCoMod_Gen gg )%mole
           end.
  Defined.

  Fixpoint toPolyMor (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol)
           {struct gg} : 'CoMod(0 A |- F ~> G )0 . 
  Proof.
    refine match gg with
           | ( a o>*$ ff )%sol => ( a o>*$ (toPolyMor _ _ _ ff) )%poly
           | ( @'UnitCoMod F )%sol => ( @'UnitCoMod F )%poly
           | ( 'MorCoMod_Mole gg )%sol => ( 'MorCoMod_Mole (toPolyMor_Mole gg) )%poly
           | ( ~_1 @ F2 o>CoMod zz1 )%sol => ( ~_1 @ F2 o>CoMod (toPolyMor _ _ _ zz1) )%poly
           | ( ~_2 @ F1 o>CoMod zz2 )%sol => ( ~_2 @ F1 o>CoMod (toPolyMor _ _ _ zz2) )%poly
           | ( << ff1 ,CoMod ff2 >> )%sol => ( << (toPolyMor _ _ _ ff1) ,CoMod (toPolyMor _ _ _ ff2) >> )%poly
           end.
  Defined.

  (**#+END_SRC

** Destruction of morphisms with inner-instantiation of object-indexes

Regardless the multiplicity extra-argument/parameter in the inductive-family-presentation , oneself easily still-gets the common dependent-destruction of morphisms with inner-instantiation of object-indexes

#+BEGIN_SRC coq :exports both :results silent **)
  
  Module Destruct_domPair.

  Inductive morCoMod_domPair
  : forall (F1 F2 : obCoMod), forall (G : obCoMod) A,
        'CoMod(0 A |- (Pair F1 F2) ~> G )0 %sol -> Type :=

  | MorCoMod_Poly_Struc : forall (M M' G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
        forall (gg : 'CoMod(0 A |- (Pair M M') ~> G )0 %sol ), 
          morCoMod_domPair ( a o>*$ gg )%sol

  | UnitCoMod : forall (M M' : obCoMod),
      morCoMod_domPair ( @'UnitCoMod (Pair M M') )%sol 

  | Project1 : forall (F1 F2 : obCoMod), forall (Z1 : obCoMod) A (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0 %sol),
        morCoMod_domPair ( ~_1 @ F2 o>CoMod zz1 )%sol

  | Project2 : forall (F1 F2 : obCoMod), forall (Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0 %sol),
        morCoMod_domPair ( ~_2 @ F1 o>CoMod zz2 )%sol

  | Pairing : forall (M M' : obCoMod) (F1 F2 : obCoMod) A
                (ff1 : 'CoMod(0 Context1 A |- (Pair M M') ~> F1 )0 %sol) (ff2 : 'CoMod(0 Context2 A |- (Pair M M') ~> F2 )0 %sol),
      morCoMod_domPair ( << ff1 ,CoMod ff2 >> )%sol .

  Definition morCoMod_domPairP_Type
             (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ) :=
    ltac:( destruct F; [ intros; refine (unit : Type)
                       | refine (morCoMod_domPair gg) ] ).

  Lemma morCoMod_domPairP
    : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ), morCoMod_domPairP_Type gg .
  Proof.
    intros. case: F G A / gg.
    - destruct F; [ intros; exact: tt | ].
      constructor 1.
    - destruct F; [ intros; exact: tt | ].
      constructor 2.
    - intros; exact: tt.
    - constructor 3.
    - constructor 4.
    - destruct L; [ intros; exact: tt | ].
      constructor 5.
  Defined.

  End Destruct_domPair.

  Module Destruct_domMole.

  Inductive morCoMod_domMole
  : forall (F : Mole.obCoMod) (G : obCoMod) A,
        'CoMod(0 A |- (ObCoMod_Mole F) ~> G )0 %sol -> Type :=

  | MorCoMod_Poly_Struc : forall (F : Mole.obCoMod) (G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %oncestruc),
        forall (gg : 'CoMod(0 A |- (ObCoMod_Mole F) ~> G )0 %sol ), 
          morCoMod_domMole ( a o>*$ gg )%sol

  | UnitCoMod : forall (F : Mole.obCoMod),
      morCoMod_domMole ( @'UnitCoMod (ObCoMod_Mole F) )%sol 

  | MorCoMod_Mole : forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol_mole ),
      morCoMod_domMole ( 'MorCoMod_Mole gg )%sol

  | Pairing : forall (L : Mole.obCoMod) (F1 F2 : obCoMod) A
                (ff1 : 'CoMod(0 Context1 A |- (ObCoMod_Mole L) ~> F1 )0 %sol)
                (ff2 : 'CoMod(0 Context2 A |- (ObCoMod_Mole L) ~> F2 )0 %sol),
      morCoMod_domMole ( << ff1 ,CoMod ff2 >> )%sol .

  Definition morCoMod_domMoleP_Type
             (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ) :=
    ltac:( destruct F; [ refine (morCoMod_domMole gg)
                       | intros; refine (unit : Type) ] ).

  Lemma morCoMod_domMoleP
    : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ), morCoMod_domMoleP_Type gg .
  Proof.
    intros. case: F G A / gg.
    - destruct F; [ | intros; exact: tt ].
      constructor 1.
    - destruct F; [ | intros; exact: tt ].
      constructor 2.
    - constructor 3.
    - intros; exact: tt. 
    - intros; exact: tt. 
    - destruct L; [ | intros; exact: tt ].
      constructor 4.
  Defined.

  End Destruct_domMole.
  
End Sol.

(**#+END_SRC

* (parameter-polyarrowing)/polymorphism/cut-elimination by computational/total/asymptotic/reduction/(multi-step) resolution

As common , this resolution is by some non-structurally recursive function .

Moreover in contrast , this resolution is made of some outer polymorphism-and-polyarrowing-elimination [solveCoMod] which is then followed by some inner polyarrowing-elimination [solveCoMod_Mole] from molecular morphisms to solution molecular morphisms where the molecular polyarrowing [Mole.MorCoMod_Poly_Param] cut-constructor is pseudo-erased by accumulating it onto the atomic generating morphisms .

This COQ program and deduction is mostly-automated .

#+BEGIN_SRC coq :exports both :results silent **)

Module Resolve.

  Import Mole.Ex_Notations.
  Import Sol.Ex_Notations.
  
  Ltac tac_reduce_eauto12 := simpl in * ; eauto 12.
  Ltac tac_reduce := simpl in * ; eauto.

  Fixpoint solveCoMod_Mole len {struct len} :
     forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %mole),
     forall grade_Mole_gg : (grade_Mole gg <= len)%coq_nat,
       { ggSol : 'CoMod(0 A |- F ~> G )0 %sol_mole | ( (Sol.toPolyMor_Mole ggSol) <~~ gg )%mole } .
  Proof.
    case : len => [ | len ].

    (* len is O *)
    - ( move => F G A gg grade_Mole_gg ); exfalso; abstract tac_degrade grade_Mole_gg.

    (* len is (S len) *)
    - move => F G A gg; case : F G A / gg =>
      [ F G A A' a gg (* a o>* gg *)
      | F F' A ff' F'' B ff_ (* ff_ o>CoMod ff' *)
      | F G A gg A' a (* a o>*@ 'MorCoMod_Gen gg *)
      ] grade_Mole_gg .

      (* gg is a o>* gg *)
      + case: (solveCoMod_Mole len _ _ _ gg)
        => [ | ggSol ggSol_prop ] ;
            first by abstract tac_degrade grade_Mole_gg.

        { destruct ggSol as
              [ F F' A ff'Sol F'' B ff_Sol (* ff_Sol o>CoMod ff'Sol *)
              | F G A ggSol _A' _a (* _a o>*@ 'MorCoMod_Gen ggSol *) ] .

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( ff_Sol o>CoMod ff'Sol ) *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomMultiply.morIndexer_codomMultiplyP a)
            => a_codomMultiplyP .
            destruct a_codomMultiplyP as
                [ B A A' a (* Multiply B a *)
                | A B' B b (* Multiply A b *) ] .

            + case: (solveCoMod_Mole len _ _ _ ((a o>* (Sol.toPolyMor_Mole ff'Sol))%mole))
              => [ | a_o_ff'Sol a_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_Mole_gg.
            
              exists ( ff_Sol o>CoMod a_o_ff'Sol  )%sol_mole .
              clear - ggSol_prop a_o_ff'Sol_prop. tac_reduce.

            + case: (solveCoMod_Mole len _ _ _ ((b o>* (Sol.toPolyMor_Mole ff_Sol))%mole))
            => [ | b_o_ff_Sol b_o_ff_Sol_prop ] ;
                first by abstract tac_degrade grade_Mole_gg.
            
              exists ( b_o_ff_Sol o>CoMod ff'Sol  )%sol_mole . 
              clear - ggSol_prop b_o_ff_Sol_prop. tac_reduce.

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( _a o>*@ 'MorCoMod_Gen ggSol ) *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomObIndexer_Param.morIndexer_codomObIndexer_ParamP a)
            => a_codomObIndexer_ParamP .
            destruct a_codomObIndexer_ParamP as
                [ _A A' a (* MorIndexer_Constant _A A' a *) ] .

            + exists ( ( ( a o>Indexer _a)%param ) o>*@ 'MorCoMod_Gen ggSol )%sol_mole . 
              clear - ggSol_prop . tac_reduce .
        }

      (* gg is  ( ff_ o>CoMod ff' ) *)
      + case: (solveCoMod_Mole len _ _ _ ff_)
        => [ | ff_Sol ff_Sol_prop ] ;
            first by abstract tac_degrade grade_Mole_gg.
        
        case: (solveCoMod_Mole len _ _ _ ff')
        => [ |ff'Sol ff'Sol_prop ] ;
            first by abstract tac_degrade grade_Mole_gg.

        exists ( ff_Sol o>CoMod ff'Sol )%sol_mole.

        clear - ff_Sol_prop ff'Sol_prop. tac_reduce.
              
      (* gg is  ( a o>*@ 'MorCoMod_Gen gg ) *)
      + exists (  a o>*@ 'MorCoMod_Gen gg )%sol_mole. apply: Mole.convMorCoMod_Refl.
  Defined.

  Definition solveCoMod_Mole' :
     forall (F G : Mole.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %mole),
       { ggSol : 'CoMod(0 A |- F ~> G )0 %sol_mole | ( (Sol.toPolyMor_Mole ggSol) <~~ gg )%mole } .
  Proof.
    intros; apply: (@solveCoMod_Mole (grade_Mole gg)); constructor.
  Defined.
  
  Fixpoint solveCoMod len {struct len} :
     forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
     forall grade_gg : (grade gg <= len)%coq_nat,
       { ggSol : 'CoMod(0 A |- F ~> G )0 %sol | (Sol.toPolyMor ggSol) <~~ gg } .
  Proof.
    case : len => [ | len ].

    (* len is O *)
    - ( move => F G A gg grade_gg ); exfalso; abstract tac_degrade grade_gg.

    (* len is (S len) *)
    - move => F G A gg; case : F G A / gg =>
      [ F G A A' a gg (* a o>* gg *)
      | F F' A ff' F'' B ff_ (* ff_ o>CoMod ff' *)
      | F G A A' a gg (* a o>*$ gg *)
      | F (* @'UnitCoMod F *)
      | F G A gg (* 'MorCoMod_Mole gg *)
      | F1 F2 Z1 A zz1 (* ~_1 @ F2 o>CoMod zz1 *)
      | F1 F2 Z2 A zz2 (* ~_2 @ F1 o>CoMod zz2 *)
      | L F1 F2 A ff1 ff2 (* << ff1 ,CoMod ff2 >> *)
      ] grade_gg .

      (* gg is a o>* gg *)
      + all: cycle 1. 
      
      (* gg is ff_ o>CoMod ff' *)
      + all: cycle 1. 
        
      (* gg is a o>*$ gg *)
      + case: (solveCoMod len _ _ _ gg)
        => [ | ggSol ggSol_prop ] ;
            first by abstract tac_degrade grade_gg.

        exists ( a o>*$ ggSol )%sol.
        clear - ggSol_prop. abstract tac_reduce.

      (* gg is @'UnitCoMod F *)
      + exists (@'UnitCoMod F)%sol. apply: convMorCoMod_Refl.

      (* gg is 'MorCoMod_Mole gg *)
      + case: (solveCoMod_Mole' gg) => [ ggSol ggSol_prop ] .

        exists ( 'MorCoMod_Mole ggSol )%sol.
        clear - ggSol_prop. abstract tac_reduce.

      (* gg is ~_1 @ F2 o>CoMod zz1 *)
      + case: (solveCoMod len _ _ _ zz1)
        => [ | zz1Sol zz1Sol_prop ] ;
            first by abstract tac_degrade grade_gg.

        exists ( ~_1 @ F2 o>CoMod zz1Sol )%sol.
        clear - zz1Sol_prop. abstract tac_reduce.

      (* gg is ~_2 @ F1 o>CoMod zz2 *)
      + case: (solveCoMod len _ _ _ zz2)
        => [ | zz2Sol zz2Sol_prop ] ;
            first by abstract tac_degrade grade_gg.

        exists ( ~_2 @ F1 o>CoMod zz2Sol )%sol.
        clear - zz2Sol_prop. abstract tac_reduce.

      (* gg is << ff1 ,CoMod ff2 >> *)
      + case: (solveCoMod len _ _ _ ff1)
        => [ | ff1Sol ff1Sol_prop ] ;
            first by abstract tac_degrade grade_gg.
        
        case: (solveCoMod len _ _ _ ff2)
        => [ |ff2Sol ff2Sol_prop ] ;
            first by abstract tac_degrade grade_gg.

        exists ( << ff1Sol ,CoMod ff2Sol >> )%sol.

        clear - ff1Sol_prop ff2Sol_prop. tac_reduce.

      (* gg is a o>* gg *)
      + case: (solveCoMod len _ _ _ gg)
        => [ | ggSol ggSol_prop ] ;
            first by abstract tac_degrade grade_gg.
        
        { destruct ggSol as
              [ F G A _A' _a ggSol (* _a o>*$ ggSol *)
              | F (* @'UnitCoMod F *)
              | F G A ggSol (* 'MorCoMod_Mole ggSol *)
              | F1 F2 Z1 A zz1Sol (* ~_1 @ F2 o>CoMod zz1Sol *)
              | F1 F2 Z2 A zz2Sol (* ~_2 @ F1 o>CoMod zz2Sol *)
              | L F1 F2 A ff1Sol ff2Sol (* << ff1Sol ,CoMod ff2Sol >> *) ] .

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( a o>*$ ggSol ) *)          
          - case: (solveCoMod len _ _ _ ((fst (projT2 (commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc _a a)))
                                           o>* (Sol.toPolyMor ggSol)))
            => [ | a_o_ggSol a_o_ggSol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ( (snd (projT2 (commute_MorCoMod_Poly_Param_MorCoMod_Poly_Struc _a a))) o>*$ a_o_ggSol )%sol .
            clear - ggSol_prop a_o_ggSol_prop. tac_reduce.

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* ( @'UnitCoMod F ) *)          
          - exfalso. clear - a . inversion_clear a.
            match goal with
            | [ X : Cong.MorIndexer_Param.morIndexer _ One |- _ ] => inversion X
            end.

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* 'MorCoMod_Mole ggSol *)          
          - case: (solveCoMod_Mole' ((a o>* (Sol.toPolyMor_Mole ggSol))%mole))
            => [ a_o_ggSol a_o_ggSol_prop ] .

            exists ( 'MorCoMod_Mole ( a_o_ggSol )%mole )%sol .
            clear - ggSol_prop a_o_ggSol_prop . tac_reduce.
            
          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ~_1 @ F2 o>CoMod zz1Sol *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomContext1.morIndexer_codomContext1P a)
            => a_codomContext1P .
            destruct a_codomContext1P as
                [ A A' a (* Context1_arrow a *) ] .

            case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor zz1Sol)))
            => [ | a_o_zz1Sol a_o_zz1Sol_prop ] ;
                first by abstract tac_degrade grade_gg.
            
            exists ( ~_1 @ F2 o>CoMod a_o_zz1Sol )%sol .
            clear - ggSol_prop a_o_zz1Sol_prop. tac_reduce.

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ~_2 @ F1 o>CoMod zz2Sol *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomContext2.morIndexer_codomContext2P a)
            => a_codomContext2P .
            destruct a_codomContext2P as
                [ A A' a (* Context2_arrow a *) ] .

            case: (solveCoMod len _ _ _ (a o>* (Sol.toPolyMor zz2Sol)))
            => [ | a_o_zz2Sol a_o_zz2Sol_prop ] ;
                first by abstract tac_degrade grade_gg.
            
            exists ( ~_2 @ F1 o>CoMod a_o_zz2Sol )%sol .
            clear - ggSol_prop a_o_zz2Sol_prop. tac_reduce.

          (* gg is a o>* gg , to a o>* ggSol , is  << ff1Sol ,CoMod ff2Sol >> *)          
          - case: (solveCoMod len _ _ _ ((Cong.Context1_arrow a) o>* (Sol.toPolyMor ff1Sol)))
            => [ | a_o_ff1Sol a_o_ff1Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            case: (solveCoMod len _ _ _ ((Cong.Context2_arrow a) o>* (Sol.toPolyMor ff2Sol)))
            => [ |  a_o_ff2Sol a_o_ff2Sol_prop ] ;
                first by abstract tac_degrade grade_gg.
 
            exists ( << a_o_ff1Sol ,CoMod a_o_ff2Sol >> )%sol .
            clear - ggSol_prop a_o_ff1Sol_prop a_o_ff2Sol_prop . tac_reduce_eauto12.
        }

      (* gg is ff_ o>CoMod ff' *)
      + case: (solveCoMod len _ _ _ ff_)
        => [ | ff_Sol ff_Sol_prop ] ;
            first by abstract tac_degrade grade_gg.

        case: (solveCoMod len _ _ _ ff')
        => [ | ff'Sol ff'Sol_prop ] ;
            first by abstract tac_degrade grade_gg.

        (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol)  *)
        { destruct ff_Sol as
              [ _F _G _A A' a ff_Sol (* a o>*$ ff_Sol *)
              | _F (* @'UnitCoMod F *)
              | _F _G _A ff_Sol (* 'MorCoMod_Mole ff_Sol *)
              | F1 F2 Z1 _A zz1_Sol (* ~_1 @ F2 o>CoMod zz1_Sol *)
              | F1 F2 Z2 _A zz2_Sol (* ~_2 @ F1 o>CoMod zz2_Sol *)
              | L F1 F2 _A ff1_Sol ff2_Sol (* << ff1_Sol ,CoMod ff2_Sol >> *) ] .

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( a o>*$ ff_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ( (OnceStruc._Cong.Multiply_arrowR _ a)  o>*$ ff_Sol_o_ff'Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is (@'UnitCoMod _F) o>CoMod ff'Sol  *)
          - exists ( (OnceStruc.OneMultiplyR (Cong.MorIndexer_Constant (Cong.OneMultiplyR.OneMultiplyR _)))
                  o>*$ ff'Sol )%sol . 
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.
          
          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Mole ff_Sol ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domMole.morCoMod_domMoleP ff'Sol) => ff'Sol_domMoleP.
            destruct ff'Sol_domMoleP as
                [ F G A A' a ff'Sol  (*  ( a o>*$ ff'Sol )%sol  *)
                | F (* ( @'UnitCoMod (ObCoMod_Mole F) )%sol *)
                | F G A ff'Sol (* ( 'MorCoMod_Mole ff'Sol )%sol *)
                | L F1 F2 A ff1'Sol ff2'Sol (* << ff1'Sol ,CoMod ff2'Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Mole ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Mole ff_Sol ) o>CoMod (  a o>*$ ff'Sol )   *)
            + case: (solveCoMod len _ _ _ (( Sol.toPolyMor ('MorCoMod_Mole ff_Sol)%sol ) o>CoMod (Sol.toPolyMor ff'Sol)))
              => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (OnceStruc._Cong.Multiply_arrowL _ a) o>*$ ff_Sol_o_ff'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Mole ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Mole ff_Sol ) o>CoMod ( @'UnitCoMod (ObCoMod_Mole F) )  *)
          - exists ( (OnceStruc.OneMultiplyL (Cong.MorIndexer_Constant (Cong.OneMultiplyL.OneMultiplyL _)))
                  o>*$ ( 'MorCoMod_Mole ff_Sol ) )%sol .
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Mole ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Mole ff_Sol ) o>CoMod ( 'MorCoMod_Mole ff'Sol )   *)
            + case: (solveCoMod_Mole' ( ( (Sol.toPolyMor_Mole ff_Sol) o>CoMod (Sol.toPolyMor_Mole ff'Sol) )%mole ))
              => [ ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ].

              exists ( 'MorCoMod_Mole ff_Sol_o_ff'Sol )%sol . 
              clear -ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

              (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Mole ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Mole ff_Sol ) o>CoMod ( << ff1'Sol ,CoMod ff2'Sol >>  )   *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ('MorCoMod_Mole ff_Sol)%sol) o>CoMod (Sol.toPolyMor ff1'Sol) ))
              => [ |ff_Sol_o_ff1'Sol ff_Sol_o_ff1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              case: (solveCoMod len _ _ _ ( (Sol.toPolyMor( 'MorCoMod_Mole ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff2'Sol)))
              => [ | ff_Sol_o_ff2'Sol ff_Sol_o_ff2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.
 
              exists ( (OnceStruc.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
                    o>*$ ( << ( (OnceStruc.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*$ ff_Sol_o_ff1'Sol )
                  ,CoMod ( (OnceStruc.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*$ ff_Sol_o_ff2'Sol ) >> ) )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff1'Sol_prop ff_Sol_o_ff2'Sol_prop .

              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := (Sol.toPolyMor( 'MorCoMod_Mole ff_Sol )%sol) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := (Sol.toPolyMor( 'MorCoMod_Mole ff_Sol )%sol) o>CoMod ( << Sol.toPolyMor ff1'Sol ,CoMod Sol.toPolyMor ff2'Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( _ o>*$ ( << _ o>*$ ((Sol.toPolyMor( 'MorCoMod_Mole ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff1'Sol)) ,CoMod _ o>*$ ((Sol.toPolyMor( 'MorCoMod_Mole ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff2'Sol)) >> ) )); by eauto 12).

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_1 @ F2 o>CoMod zz1_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz1_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | zz1_Sol_o_ff'Sol zz1_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ((OnceStruc.SymMultiplyContext1 (Cong.MorIndexer_Constant (Cong.SymMultiplyContext1.SymMultiplyContext1 _ _)))
                 o>*$ ( ~_1 @ F2 o>CoMod zz1_Sol_o_ff'Sol ) )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz1_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_2 @ F1 o>CoMod zz2_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz2_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | zz2_Sol_o_ff'Sol zz2_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ((OnceStruc.SymMultiplyContext2 (Cong.MorIndexer_Constant (Cong.SymMultiplyContext2.SymMultiplyContext2 _ _)))
                 o>*$ ( ~_2 @ F1 o>CoMod zz2_Sol_o_ff'Sol ) )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz2_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domPair.morCoMod_domPairP ff'Sol) => ff'Sol_domPairP.
            destruct ff'Sol_domPairP as
                [ M M' G A A' a ff'Sol (* ( a o>*$ ff'Sol )%sol *)
                | M M' (*  ( @'UnitCoMod (Pair M M') )%sol  *)
                | F1 F2 Z1 A zz1'Sol (*  ~_1 @ F2 o>CoMod zz1'Sol %sol *)
                | F1 F2 Z2 A zz2'Sol (*  ~_2 @ F1 o>CoMod zz2'Sol %sol *)
                | M M' F1 F2 A ff1'Sol ff2'Sol (* << ff1'Sol ,CoMod ff2'Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol , is  (  << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod (  a o>*$ ff'Sol )   *)
            + case: (solveCoMod len _ _ _ (( << (Sol.toPolyMor ff1_Sol) ,CoMod (Sol.toPolyMor ff2_Sol) >> ) o>CoMod (Sol.toPolyMor ff'Sol)))
              => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (OnceStruc._Cong.Multiply_arrowL _ a) o>*$ ff_Sol_o_ff'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol , is  (  << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( @'UnitCoMod (Pair M M') )   *)
          - exists ( (OnceStruc.OneMultiplyL (Cong.MorIndexer_Constant (Cong.OneMultiplyL.OneMultiplyL _)))
                  o>*$ ( << ff1_Sol ,CoMod ff2_Sol >> ) )%sol .
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1'Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff1_Sol) o>CoMod (Sol.toPolyMor zz1'Sol) ))
              => [ | ff1_Sol_o_zz1'Sol ff1_Sol_o_zz1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ((OnceStruc.AssocMultiplyContext1 (Cong.MorIndexer_Constant (Cong.AssocMultiplyContext1.AssocMultiplyContext1 _ _)))
                   o>*$ ff1_Sol_o_zz1'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop  ff1_Sol_o_zz1'Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2'Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff2_Sol) o>CoMod (Sol.toPolyMor zz2'Sol) ))
              => [ | ff2_Sol_o_zz2'Sol ff2_Sol_o_zz2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ((OnceStruc.AssocMultiplyContext2 (Cong.MorIndexer_Constant (Cong.AssocMultiplyContext2.AssocMultiplyContext2 _ _)))
                   o>*$ ff2_Sol_o_zz2'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop  ff2_Sol_o_zz2'Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( << ff1'Sol ,CoMod ff2'Sol >> )  *)
            + case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff1'Sol)))
              => [ | ff_Sol_off1'Sol ff_Sol_off1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff2'Sol)))
              => [ | ff_Sol_off2'Sol ff_Sol_off2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (OnceStruc.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
                    o>*$ ( << ( (OnceStruc.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*$ ff_Sol_off1'Sol )
                           ,CoMod ( (OnceStruc.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*$ ff_Sol_off2'Sol ) >> ) )%sol .

              clear - ff_Sol_prop ff'Sol_prop ff_Sol_off1'Sol_prop ff_Sol_off2'Sol_prop .
              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod ( << Sol.toPolyMor ff1'Sol ,CoMod Sol.toPolyMor ff2'Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( _ o>*$ ( << _ o>*$ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff1'Sol)) ,CoMod _ o>*$ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff2'Sol)) >> ) )); by eauto 12).
        }

  Defined.

End Resolve.

End MULTIFOLD.

(**#+END_SRC

Voila. **)
