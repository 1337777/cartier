(**#+TITLE: cartierSolution5.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution5.v

solves half of some question of Cartier which is how to program grammatical polymorph multifold ( "enriched" ) functors ...


#+BEGIN_EXAMPLE
#+END_EXAMPLE

KEYWORDS : 1337777.OOO ; COQ ; cut-elimination ; enriched functors ; enriched product ; polymorph metafunctors-grammar ; modos

OUTLINE :

  * BLA
  ** BLA

  * BLA
  ** BLA

-----

BUY RECURSIVE T-SQUARE paypal.me/1337777 ; 微信支付 2796386464@qq.com ; eth 0x54810dcb93b37DBE874694407f78959Fa222D920 ; amazon amazon.com/hz/wishlist/ls/28SN02HR4EB8W ; irc #OOO1337777


**)


(**

* BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Omega.

Require Import Equality.

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
  | Tensor : obIndexer -> obIndexer -> obIndexer
  | Iden : obIndexer
  | Context1 : obIndexer -> obIndexer
  | Context2 : obIndexer -> obIndexer.

  Module Cong.

    Module MorIndexer_Param.

      Variant morIndexer : obIndexer -> obIndexer -> Type :=
      | MorIndexer_Param : forall A B : obIndexer_Param, 'Indexer(0 A ~> B )0 %param -> 'Indexer(0 (ObIndexer_Param A) ~> (ObIndexer_Param B) )0 
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End MorIndexer_Param.

    Module Assoc.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Assoc : forall A B C : obIndexer, 'Indexer(0 (Tensor (Tensor A B) C) ~> (Tensor A (Tensor B C)) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Assoc.

    Module Sym.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | Sym : forall A B : obIndexer, 'Indexer(0 (Tensor A B) ~> (Tensor B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Sym.

    Module IdenTensorL.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | IdenTensorL : forall A : obIndexer, 'Indexer(0 (Tensor Iden A) ~> A )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End IdenTensorL.

    Module IdenTensorR.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | IdenTensorR : forall A : obIndexer, 'Indexer(0 (Tensor A Iden) ~> A )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End IdenTensorR.

    Module IdenTensorL_Rev.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | IdenTensorL_Rev : forall A : obIndexer, 'Indexer(0 A ~> (Tensor Iden A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End IdenTensorL_Rev.

    Module IdenTensorR_Rev.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | IdenTensorR_Rev : forall A : obIndexer, 'Indexer(0 A ~> (Tensor A Iden) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End IdenTensorR_Rev.

    Module SymContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymContext1 : forall A : obIndexer, 'Indexer(0 Context1 (Context2 A) ~> Context2 (Context1 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymContext1.

    Module SymContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymContext2 : forall A : obIndexer, 'Indexer(0 Context2 (Context1 A) ~> Context1 (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymContext2.

    Module AssocContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocContext1 : forall A B : obIndexer, 'Indexer(0 Context1 (Tensor B A) ~> Tensor (Context1 A) B )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocContext1.

    Module AssocContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocContext2 : forall A B : obIndexer, 'Indexer(0 Context2 (Tensor B A) ~> Tensor (Context2 A) B )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocContext2.

    Module AssocTensorContext1.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocTensorContext1 : forall A B : obIndexer, 'Indexer(0 Tensor (Context1 B) A ~> Tensor B (Context1 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocTensorContext1.

    Module AssocTensorContext2.

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | AssocTensorContext2 : forall A B : obIndexer, 'Indexer(0 Tensor (Context2 B) A ~> Tensor B (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End AssocTensorContext2.

    Module SymTensorContext1.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymTensorContext1 : forall A B : obIndexer, 'Indexer(0 Tensor B (Context1 A) ~> Context1 (Tensor B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End SymTensorContext1.
    
    Module SymTensorContext2.
      
      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | SymTensorContext2 : forall A B : obIndexer, 'Indexer(0 Tensor B (Context2 A) ~> Context2 (Tensor B A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End  SymTensorContext2.
 
    Section Section1.

      Variable morIndexer_Constant : obIndexer -> obIndexer -> Type .

      Inductive morIndexer : obIndexer -> obIndexer -> Type :=
      | MorIndexer_Constant : forall A B : obIndexer, @morIndexer_Constant A B -> 'Indexer(0 A ~> B )0 
      | Tensor_arrow1 : forall B A A' : obIndexer, 'Indexer(0 A' ~>  A )0 ->
                                              'Indexer(0 (Tensor A' B) ~> (Tensor A B) )0
      | Tensor_arrow2 : forall A B B' : obIndexer, 'Indexer(0 B' ~>  B )0 ->
                                              'Indexer(0 (Tensor A B') ~> (Tensor A B) )0
      | Context1_arrow : forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                             'Indexer(0 (Context1 A') ~> (Context1 A) )0
      | Context2_arrow : forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                             'Indexer(0 (Context2 A') ~> (Context2 A) )0
      where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Section1.
    
    Module Export Ex_Notations.
      Delimit Scope cong_scope with cong.
      Hint Constructors MorIndexer_Param.morIndexer.
      Hint Constructors Assoc.morIndexer.
      Hint Constructors Sym.morIndexer.
      Hint Constructors IdenTensorL.morIndexer.
      Hint Constructors IdenTensorR.morIndexer.
      Hint Constructors IdenTensorL_Rev.morIndexer.
      Hint Constructors IdenTensorR_Rev.morIndexer.
      Hint Constructors AssocContext1.morIndexer.
      Hint Constructors AssocContext2.morIndexer.
      Hint Constructors SymContext1.morIndexer.
      Hint Constructors SymContext2.morIndexer.
      Hint Constructors AssocContext1.morIndexer.
      Hint Constructors AssocContext2.morIndexer.
      Hint Constructors SymTensorContext1.morIndexer.
      Hint Constructors SymTensorContext2.morIndexer.
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

    Module Destruct_MorIndexer_Param_codomTensor.

      Inductive morIndexer_codomTensor : forall (A B A' : obIndexer),
        'Indexer(0 A' ~> Tensor A B @ MorIndexer_Param.morIndexer )0 %cong -> Type :=
      | Tensor_arrow1 : forall (B A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomTensor ( Tensor_arrow1 B a ) 
      | Tensor_arrow2 : forall (A B B' : obIndexer) (b : 'Indexer(0 B' ~> B @ MorIndexer_Param.morIndexer )0 %cong ),
          morIndexer_codomTensor ( Tensor_arrow2 A b ) .

      Definition morIndexer_codomTensorP_Type
                 (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %cong)  :=
        ltac:( destruct A; [ intros; refine (unit : Type)
                           | refine (morIndexer_codomTensor a)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type)
                           | intros; refine (unit : Type) ] ).

      Lemma morIndexer_codomTensorP
        : forall A A' ( a : 'Indexer(0 A' ~> A @ MorIndexer_Param.morIndexer )0 %cong ), morIndexer_codomTensorP_Type a .
      Proof.
        intros. case: A' A / a .
        - destruct m . intros; exact: tt.
        - constructor 1.
        - constructor 2.
        - intros; exact: tt.
        - intros; exact: tt.
      Defined.

    End Destruct_MorIndexer_Param_codomTensor.

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

  Module Once.
    
    Section Section1.
    Import Cong.Ex_Notations.
  
    Variant morIndexer : obIndexer -> obIndexer -> Type :=
    | Assoc : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Assoc.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | Sym : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.Sym.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | IdenTensorL : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.IdenTensorL.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | IdenTensorR : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.IdenTensorR.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | IdenTensorL_Rev : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.IdenTensorL_Rev.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | IdenTensorR_Rev : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.IdenTensorR_Rev.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | SymContext1 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | SymContext2 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | AssocContext1 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | AssocContext2 : forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | AssocTensorContext1 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocTensorContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | AssocTensorContext2 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.AssocTensorContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | SymTensorContext1 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymTensorContext1.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    | SymTensorContext2 :  forall A B : obIndexer, 'Indexer(0 A ~>  B @ Cong.SymTensorContext2.morIndexer )0 %cong -> 'Indexer(0 A  ~> B )0
    where  "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A).

    End Section1.

    Module Export Ex_Notations.
      Export Cong.Ex_Notations.
      Delimit Scope once_scope with once.
      Hint Constructors morIndexer.

      Notation "''Indexer' (0 A' ~> A )0" := (@morIndexer A' A) : once_scope.
    End Ex_Notations.

    Module _Cong.

      Lemma Tensor_arrow1 : ( forall B A A' : obIndexer, 'Indexer(0 A' ~>  A )0 ->
                                              'Indexer(0 (Tensor A' B) ~> (Tensor A B) )0 )%once.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14];
        apply: Cong.Tensor_arrow1; eassumption.
      Defined.
      Lemma Tensor_arrow2 : ( forall A B B' : obIndexer, 'Indexer(0 B' ~>  B )0 ->
                                                    'Indexer(0 (Tensor A B') ~> (Tensor A B) )0 )%once.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14];
        apply: Cong.Tensor_arrow2; eassumption.
      Defined.

      Lemma Context1_arrow : ( forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                                   'Indexer(0 (Context1 A') ~> (Context1 A) )0 )%once.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14];
        apply: Cong.Context1_arrow; eassumption.
      Defined.
      Lemma Context2_arrow : ( forall A A' : obIndexer, 'Indexer(0 A' ~> A )0 ->
                                                   'Indexer(0 (Context2 A') ~> (Context2 A) )0 )%once.
      Proof.
        destruct 1; [constructor 1| constructor 2| constructor 3| constructor 4
                     | constructor 5 | constructor 6 | constructor 7 | constructor 8 | constructor 9 | constructor 10 | constructor 11 | constructor 12 | constructor 13 | constructor 14];
        apply: Cong.Context2_arrow; eassumption.
      Defined.

    End _Cong.

  End Once.

End Indexer.

Import Indexer.Once.Ex_Notations.

Parameter obCoMod_Gen : Type.
Parameter morCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param), Type.

Reserved Notation "''CoMod' (0 A |- F' ~> F )0" (at level 0, format "''CoMod' (0  A  |-  F'  ~>  F  )0").

Reserved Notation "gg0 <~~ gg" (at level 70).

Module Atom.

  Inductive obCoMod : Type := 
  | ObCoMod_Gen : obCoMod_Gen -> obCoMod .

  Section Section1.
  Delimit Scope atom_scope with atom.

  Inductive morCoMod : obCoMod -> obCoMod -> obIndexer -> Type :=

  | MorCoMod_Poly : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A  @ Cong.MorIndexer_Param.morIndexer )0 % cong),
        'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

  | PolyCoMod : forall (F F' : obCoMod) A,
      'CoMod(0 A |- F' ~> F )0 -> forall (F'' : obCoMod) B,
        'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Tensor A B |- F'' ~> F )0

  | MorCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param),
      @morCoMod_Gen F G A -> forall A' (a : 'Indexer(0 A' ~> A )0 %param),
        'CoMod(0 ObIndexer_Param A' |- (ObCoMod_Gen F) ~> (ObCoMod_Gen G) )0

  where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : atom_scope. 

  End Section1.

  Module Import Ex_Notations0.
    Delimit Scope atom_scope with atom.

    Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : atom_scope. 

    Notation "a o>* ff" :=
      (@MorCoMod_Poly _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : atom_scope.

    Notation "ff_ o>CoMod ff'" :=
      (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : atom_scope.

    Notation "a o>| ''MorCoMod_Gen' ff" :=
      (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : atom_scope.
  End Ex_Notations0.

  Local Open Scope atom_scope.

  Inductive convMorCoMod : forall (F G : obCoMod) (A : obIndexer) (gg gg0 : 'CoMod(0 A |- F ~> G )0), Prop :=

  | convMorCoMod_Refl : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
      gg <~~ gg

  | convMorCoMod_Trans :
      forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
        (uTrans : 'CoMod(0 A |- F ~> G )0 ),
        uTrans <~~ gg -> forall  (gg00 : 'CoMod(0 A |- F ~> G )0 ),
          gg00 <~~ uTrans -> gg00 <~~ gg

  | MorCoMod_Poly_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
        forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
          gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )
                                    
  | PolyCoMod_cong_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0),
      forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0 )  (ff_0 : 'CoMod(0 B |- F'' ~> F' )0 ),
        ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

  | PolyCoMod_cong_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 )
                            (ff'0 : 'CoMod(0 A |- F' ~> F )0 ),
      forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
        ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

  | MorCoMod_Poly_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 ) (F'' : obCoMod) B
                                    (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      forall B' (b : 'Indexer(0 B' ~> B @ Cong.MorIndexer_Param.morIndexer )0 %cong),

        ( ( b o>* ff_ ) o>CoMod ( ff' ) )
          <~~ ( (Cong.Tensor_arrow2 A b) o>* (ff_ o>CoMod ff') )

  | MorCoMod_Poly_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                                   (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

        ( ( ff_ ) o>CoMod ( a o>* ff' ) )
          <~~ ( (Cong.Tensor_arrow1 B a) o>* (ff_ o>CoMod ff') )

  | MorCoMod_Gen_arrow : forall (F G : obCoMod_Gen) (A : obIndexer_Param)
                     (gg : @morCoMod_Gen F G A) A' (a : 'Indexer(0 A' ~> A )0 %param),
      forall A'' (a' : 'Indexer(0 A'' ~> A' )0 %param),

        ( ( (a' o>Indexer a)%param ) o>| 'MorCoMod_Gen gg )
          <~~ ( ( Cong.MorIndexer_Constant (Cong.MorIndexer_Param.MorIndexer_Param a') )
                o>* ( a o>| 'MorCoMod_Gen gg ) )
              
  where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0) : atom_scope.

  Module Export Ex_Notations.
    Export Ex_Notations0.
    Notation "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0) : atom_scope.
    Hint Constructors convMorCoMod.
  End Ex_Notations.
  
End Atom.

(**#+END_SRC

* BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)

Import Atom.Ex_Notations.

Inductive obCoMod : Type := 
| ObCoMod_Atom : Atom.obCoMod -> obCoMod
| Pair : obCoMod -> obCoMod -> obCoMod .


(**#+END_SRC

** BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)

Inductive morCoMod : obCoMod -> obCoMod -> (*TODO: THIS IS COMPUTED INDEX *) obIndexer -> Type :=

| MorCoMod_Poly :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A  @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

| PolyCoMod : forall (F F' : obCoMod) A,
      'CoMod(0 A |- F' ~> F )0 -> forall (F'' : obCoMod) B,
        'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Tensor A B |- F'' ~> F )0

| MorCoMod_Poly_Struc :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
      'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

| UnitCoMod : forall (F : obCoMod),
    'CoMod(0 Iden |- F ~> F )0

| MorCoMod_Atom : forall (F G : Atom.obCoMod) A,
    'CoMod(0 A |- F ~> G )0 %atom -> 'CoMod(0 A |- (ObCoMod_Atom F) ~> (ObCoMod_Atom G) )0

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

Notation "a o>* ff" :=
  (@MorCoMod_Poly _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : poly_scope.

Notation "ff_ o>CoMod ff'" :=
  (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : poly_scope.

Notation "a o>*| ff" :=
  (@MorCoMod_Poly_Struc _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : poly_scope.

Notation "@ ''UnitCoMod' F" := (@UnitCoMod F) (at level 10, only parsing) : poly_scope.

Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : poly_scope.

Notation "''MorCoMod_Atom' ff" :=
      (@MorCoMod_Atom _ _ _ ff) (at level 3) : poly_scope.

Notation "~_1 @ F2 o>CoMod zz1" :=
  (@Project1 _ F2 _ _ zz1) (at level 4, F2 at next level) : poly_scope.

Notation "~_1 o>CoMod zz1" :=
  (@Project1 _ _ _ _ zz1) (at level 4) : poly_scope.

Notation "~_2 @ F1 o>CoMod zz2" :=
  (@Project2 F1 _ _ _ zz2) (at level 4, F1 at next level) : poly_scope.

Notation "~_2 o>CoMod zz2" :=
  (@Project2 _ _ _ _ zz2) (at level 4) : poly_scope.

Notation "<< ff1 ,CoMod ff2 >>" :=
  (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : poly_scope.

(**#+END_SRC

* BLA

BLA

** BLA

#+BEGIN_SRC coq :exports both :results silent **)

Lemma MorCoMod_Poly_arrowStruc0' :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA @ Cong.Assoc.morIndexer )0 %cong),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 @ Cong.Assoc.morIndexer )0 %cong ) } .
Proof.
  intros AA BB aa. induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ].
  - { destruct aa. intros. inversion_clear bb. 
      + solve [inversion X]. 
      + { inversion_clear X.
          * solve [inversion X0].
          * eexists. eauto. 
          * eexists. eauto.  }
      + eexists. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor IHBB0 B). clear X. eauto.
      + exists (Tensor A B').  clear IHaa. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + exists (Tensor A' B).  clear IHaa. eauto.
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor A IHBB0). clear X. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context1 IHBB0).  clear X. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context2 IHBB0). clear X. eauto. }
Defined.

Lemma MorCoMod_Poly_arrowStruc' :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA @ Cong.Sym.morIndexer )0 %cong),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 @ Cong.Sym.morIndexer )0 %cong ) } .
Proof.
  intros AA BB aa. induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ].
  - { destruct aa. intros. inversion_clear bb. 
      + solve [inversion X]. 
      + eexists. eauto.
      + eexists. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor IHBB0 B). clear X. eauto.
      + exists (Tensor A B').  clear IHaa. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + exists (Tensor A' B).  clear IHaa. eauto.
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor A IHBB0). clear X. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context1 IHBB0).  clear X. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context2 IHBB0). clear X. eauto. }
Defined.

Lemma MorCoMod_Poly_arrowStruc'' :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA @ Cong.AssocContext1.morIndexer )0 %cong),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 @ Cong.AssocContext1.morIndexer )0 %cong ) } .
Proof.
  intros AA BB aa. induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ].
  - { destruct aa. intros. inversion_clear bb.
      + solve [inversion X]. 
      + { inversion_clear X.
          * solve [inversion X0].
          * eexists. eauto. 
          * eexists. eauto.  } }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor IHBB0 B). clear X. eauto.
      + exists (Tensor A B').  clear IHaa. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + exists (Tensor A' B).  clear IHaa. eauto.
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor A IHBB0). clear X. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context1 IHBB0).  clear X. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context2 IHBB0). clear X. eauto. }
Defined.

Lemma MorCoMod_Poly_arrowStruc''' :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA @ Cong.IdenTensorL.morIndexer )0 %cong),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 @ Cong.IdenTensorL.morIndexer )0 %cong ) } .
Proof.
  intros AA BB aa. induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ].
  - { destruct aa. intros. inversion_clear bb.
      + solve [inversion X]. 
      + { inversion_clear X.
          * solve [inversion X0]. }
      + eexists. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor IHBB0 B). clear X. eauto.
      + exists (Tensor A B').  clear IHaa. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + exists (Tensor A' B).  clear IHaa. eauto.
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor A IHBB0). clear X. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context1 IHBB0).  clear X. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context2 IHBB0). clear X. eauto. }
Defined.

Lemma MorCoMod_Poly_arrowStruc'''' :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA @ Cong.IdenTensorL_Rev.morIndexer )0 %cong),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 @ Cong.IdenTensorL_Rev.morIndexer )0 %cong ) } .
Proof.
  intros AA BB aa. induction aa as [ A B aa | B A A' aa IHaa | A B B' aa IHaa | A A' aa IHaa |  A A' aa IHaa ].
  - { destruct aa. intros. eexists. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor IHBB0 B). clear X. eauto.
      + exists (Tensor A B').  clear IHaa. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + exists (Tensor A' B).  clear IHaa. eauto.
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Tensor A IHBB0). clear X. eauto. } 
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context1 IHBB0).  clear X. eauto. }
  - { intros. inversion_clear bb. 
      + solve [inversion X].
      + destruct (IHaa _ X) as [IHBB0 [IHaa' IHbb'] ].
        exists (Context2 IHBB0). clear X. eauto. }
Defined.

Lemma MorCoMod_Poly_arrowStruc0 :
    forall (AA BB : obIndexer) (aa : 'Indexer(0 BB ~> AA )0 %once),
    forall (CC : obIndexer) (bb : 'Indexer(0 CC ~> BB @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      { BB0 : obIndexer & prod ( 'Indexer(0 BB0 ~> AA @ Cong.MorIndexer_Param.morIndexer )0 %cong )
                              ( 'Indexer(0 CC ~> BB0 )0 %once ) } .
Admitted.

(*TODO: this version infer that irrelevance of particular structural-adjustment arrow

Inductive convMorCoMod : forall (F G : obCoMod) (A : obIndexer) (gg : 'CoMod(0 A |- F ~> G )0 %poly)
                           (A0 : obIndexer) (gg0 : 'CoMod(0 A0 |- F ~> G )0 %poly), Prop :=*)

Inductive convMorCoMod : forall (F G : obCoMod) (A : obIndexer) (gg gg0 : 'CoMod(0 A |- F ~> G )0 %poly), Prop :=

| convMorCoMod_Refl : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
    gg <~~ gg

| convMorCoMod_Trans :
    forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
      (uTrans : 'CoMod(0 A |- F ~> G )0 ),
      uTrans <~~ gg -> forall  (gg00 : 'CoMod(0 A |- F ~> G )0 ),
        gg00 <~~ uTrans -> gg00 <~~ gg

(**TODO: uncomment
| convMorCoMod_MorCoMod_Poly_Struc : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
      forall (gg : 'CoMod(0 A |- F ~> G )0),
        (  gg ) <~~ ( a o>*| gg ) **)

| MorCoMod_Poly_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
      gg0 <~~ gg -> ( a o>* gg0 ) <~~ ( a o>* gg )

| MorCoMod_Poly_Struc_cong : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
      forall (gg gg0 : 'CoMod(0 A |- F ~> G )0),
      gg0 <~~ gg -> ( a o>*| gg0 ) <~~ ( a o>*| gg )
                                     
| PolyCoMod_cong_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0),
    forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0 )  (ff_0 : 'CoMod(0 B |- F'' ~> F' )0 ),
      ff_0 <~~ ff_ -> ( ff_0 o>CoMod ff' ) <~~ ( ff_ o>CoMod ff' )

| PolyCoMod_cong_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0 )
                           (ff'0 : 'CoMod(0 A |- F' ~> F )0 ),
    forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
      ff'0 <~~ ff' -> ( ff_ o>CoMod ff'0 ) <~~ ( ff_ o>CoMod ff' )

| MorCoMod_Atom_cong : forall (F G : Atom.obCoMod) A (gg gg0 : 'CoMod(0 A |- F ~> G )0 %atom ),
    ( gg0 <~~ gg )%atom -> ( 'MorCoMod_Atom gg0 ) <~~ ( 'MorCoMod_Atom gg )
                                        
(*TODO: ?ERRATA?: as in cartierSolution3.v Project1_cong ,  shall allow more general : additional F2' with F2' ~~~ F2  *)
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


(*TODO: retrofit - for sense , not in solution,  derivable after cut-elimination , ?maybe? for reduction *)
| MorCoMod_Poly_arrowStruc : forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
      forall (gg : 'CoMod(0 A |- F ~> G )0),
      forall (A'' : obIndexer) (a' : 'Indexer(0 A'' ~> A' @ Cong.MorIndexer_Param.morIndexer )0 %cong),
        ( (snd (projT2 (MorCoMod_Poly_arrowStruc0 a a')))
            o>*| ( (fst (projT2 (MorCoMod_Poly_arrowStruc0 a a')))
                    o>* gg ) )
          <~~ ( a' o>* ( a o>*| gg ) )
     (*  ( (a' o>Indexer a) o>* gg ) <~~ ( a' o>* (a o>* gg) ) *)

(**TODO: what to do?
(*TODO: retrofit - for sense only , not in solution , derivable after cut-elimination , ?maybe? for reduction *)
| MorCoMod_Poly_unitIndexer : forall (F G : obCoMod), forall (A : obIndexer),
      forall (gg : 'CoMod(0 A |- F ~> G )0),
        gg <~~ ( (@MorIndexer_Unit A) o>* gg ) **)

| MorCoMod_Atom_arrow : forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %atom),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ( 'MorCoMod_Atom ( (a o>* gg)%atom ) )%poly )
        <~~ ( ( a o>* ( 'MorCoMod_Atom gg ) )%poly )

| Project1_arrow : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ~_1 @ F2 o>CoMod (a o>* zz1) )
        <~~ ( (Cong.Context1_arrow a) o>* ( ~_1 @ F2 o>CoMod zz1 ) )

(* sense *)
| Project1_arrowStruc : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),

      ( ~_1 @ F2 o>CoMod (a o>*| zz1) )
        <~~ ( (Once._Cong.Context1_arrow a) o>*| ( ~_1 @ F2 o>CoMod zz1 ) )

| Project2_arrow : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( ~_2 @ F1 o>CoMod (a o>* zz2) )
        <~~ ( (Cong.Context2_arrow a) o>* ( ~_2 @ F1 o>CoMod zz2 ) )

(* sense  *)
| Project2_arrowStruc : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0),
    forall (A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),

      ( ~_2 @ F1 o>CoMod (a o>*| zz2) )
        <~~ ( (Once._Cong.Context2_arrow a) o>*| ( ~_2 @ F1 o>CoMod zz2 ) )

(* memo this non-linearity for the arrow-action *)
| Pairing_arrow : forall (L : obCoMod) (F1 F2 : obCoMod) A
                    (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),

      ( (*TODO: INSTEAD ADD PROJ AND ADD CONSTANT-GRADE DIAGONAL o>* *) << (Cong.Context1_arrow a) o>* ff1 ,CoMod (Cong.Context2_arrow a) o>* ff2 >> )
        <~~ ( a o>* ( << ff1 ,CoMod ff2 >> ) )

(* for sense , in solution , memo this non-linearity for the arrow-action *)
| Pairing_arrowStruc : forall (L : obCoMod) (F1 F2 : obCoMod) A
                    (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall A' (a : 'Indexer(0 A' ~> A )0 %once),

      ( (*TODO: INSTEAD ADD PROJ AND ADD CONSTANT-GRADE DIAGONAL o>* *) << (Once._Cong.Context1_arrow a) o>*| ff1 ,CoMod (Once._Cong.Context2_arrow a) o>*| ff2 >> )
        <~~ ( a o>*| ( << ff1 ,CoMod ff2 >> ) )

(* for sense only , not in solution , derivable after cut-elimination , NOT FOR ANY REDUCTION ,
   memo this non-linearity with complex grades which is luckily avoided *)
| MorCoMod_Poly_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall B' (b : 'Indexer(0 B' ~> B @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      ( ( b o>* ff_ ) o>CoMod ( ff' ) )
        <~~ ( (Cong.Tensor_arrow2 A b) o>* (ff_ o>CoMod ff') )

(* for sense only , not in solution , derivable after cut-elimination , NOT FOR ANY REDUCTION ,
   memo this non-linearity with complex grades which is luckily avoided *)
| MorCoMod_Poly_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall A' (a : 'Indexer(0 A' ~> A @ Cong.MorIndexer_Param.morIndexer )0 %cong),
      ( ( ff_ ) o>CoMod ( a o>* ff' ) )
        <~~ ( (Cong.Tensor_arrow1 B a) o>* (ff_ o>CoMod ff') )
        
(**TODO: COMMENT **)
(** (* for sense only , not in solution , derivable after cut-elimination , NOT FOR ANY REDUCTION *)
| PolyCoMod_morphism : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                         (ff_' : 'CoMod(0 B |- F'' ~> F' )0),
    forall (F''' : obCoMod) C (ff__ : 'CoMod(0 C |- F''' ~> F'' )0),
      
      ( (Once.Assoc (Cong.MorIndexer_Constant (Cong.Assoc.Assoc _ _ _)))
          o>*| ( (ff__ o>CoMod ff_') o>CoMod ff' ) )
        <~~ ( ff__ o>CoMod (ff_' o>CoMod ff') ) **)

(**TODO: SEPARATE IN TWO COMPONENTS ;  UNCOMMENT TO HANDLE toCoMod ( 'Twist o> ~_1 o>CoMod ff )%sol , TO SWICH FROM POLYMORPHISM-ELIM TO POLYARROW-ELIM , STRICT-DEGRADING EVEN WHEN POLYARROW-GRADE IS DOUBLE **)
(* for reduction *)
| MorCoMod_Poly_Struc_morphism_Post : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall B' (b : 'Indexer(0 B' ~> B )0 %once),
        ( (Once._Cong.Tensor_arrow2 A b) o>*| (ff_ o>CoMod ff') )
          <~~ ( ( b o>*| ff_ ) o>CoMod ( ff' ) )

(* for reduction *)
| MorCoMod_Poly_Struc_morphism_Pre : forall (F F' : obCoMod) A (ff' : 'CoMod(0 A |- F' ~> F )0) (F'' : obCoMod) B
                      (ff_ : 'CoMod(0 B |- F'' ~> F' )0),
    forall A' (a : 'Indexer(0 A' ~> A )0 %once),
        ( (Once._Cong.Tensor_arrow1 B a) o>*| (ff_ o>CoMod ff') )
          <~~ ( ff_ o>CoMod ( a o>*| ff' ) )

| Project1_morphism : forall (F1 F2 : obCoMod) (Z1 : obCoMod) A,
      forall (zz1 : 'CoMod(0 A |- F1 ~> Z1 )0), forall (Y1 : obCoMod) B (yy : 'CoMod(0 B |- Z1 ~> Y1 )0),

          ((Once.SymTensorContext1 (Cong.MorIndexer_Constant (Cong.SymTensorContext1.SymTensorContext1 _ _)))
             o>*| ( ~_1 @ F2 o>CoMod (zz1 o>CoMod yy) )) 
              <~~ ( ( ~_1 @ F2 o>CoMod zz1 ) o>CoMod yy ) 

| Project2_morphism : forall (F1 F2 : obCoMod) (Z2 : obCoMod) A,
      forall (zz2 : 'CoMod(0 A |- F2 ~> Z2 )0), forall (Y2 : obCoMod) B (yy : 'CoMod(0 B |- Z2 ~> Y2 )0),

          ((Once.SymTensorContext2 (Cong.MorIndexer_Constant (Cong.SymTensorContext2.SymTensorContext2 _ _)))
             o>*| ( ~_2 @ F1 o>CoMod (zz2 o>CoMod yy) ) )
              <~~ ( ( ~_2 @ F1 o>CoMod zz2 ) o>CoMod yy ) 

(* memo this non-linearity for the morphism-action *)
| Pairing_morphism : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (L' : obCoMod) B (ll : 'CoMod(0 B |- L' ~> L )0),

      ( (*TODO: ADD CONSTANT-GRADE DIAGONAL o>* *)
        (Once.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
           o>*| ( << (Once.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*| (ll o>CoMod ff1)
        ,CoMod (Once.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*| (ll o>CoMod ff2) >> ) ) 
        <~~ ( ll o>CoMod ( << ff1 ,CoMod ff2 >> ) )

| UnitCoMod_PolyCoMod : forall (F : obCoMod), forall (F'' : obCoMod) B (ff_ : 'CoMod(0 B |- F'' ~> F )0),
      ( (Once.IdenTensorL (Cong.MorIndexer_Constant (Cong.IdenTensorL.IdenTensorL _)))
         o>*| ff_ )
        <~~ ( ff_ o>CoMod ( @'UnitCoMod F ) )

| PolyCoMod_UnitCoMod : forall (F : obCoMod), forall (F' : obCoMod) B (ff' : 'CoMod(0 B |- F ~> F' )0),
      ( (Once.IdenTensorR (Cong.MorIndexer_Constant (Cong.IdenTensorR.IdenTensorR _)))
          o>*| ff' ) <~~ ( (@'UnitCoMod F) o>CoMod ff' )

| MorCoMod_Atom_MorCoMod_Atom : forall (F' F : Atom.obCoMod) A
    (gg' : 'CoMod(0 A |- F' ~> F )0 %atom) (F'' : Atom.obCoMod) B
    (gg_ : 'CoMod(0 B |- F'' ~> F' )0 %atom),
    ( 'MorCoMod_Atom ( gg_ o>CoMod gg' )%atom )
      <~~ ( ( 'MorCoMod_Atom gg_ ) o>CoMod ( 'MorCoMod_Atom gg' ) )%poly

| Pairing_Project1 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (Z1 : obCoMod) B, forall (zz1 : 'CoMod(0 B |- F1 ~> Z1 )0),

        ( (Once.AssocTensorContext1 (Cong.MorIndexer_Constant (Cong.AssocTensorContext1.AssocTensorContext1 _ _)))
            o>*| ( ff1 o>CoMod zz1 ) )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1 ) ) 

| Pairing_Project2 : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0),
    forall (Z2 : obCoMod) B, forall (zz2 : 'CoMod(0 B |- F2 ~> Z2 )0),

        (  (Once.AssocTensorContext2 (Cong.MorIndexer_Constant (Cong.AssocTensorContext2.AssocTensorContext2 _ _)))
            o>*| ( ff2 o>CoMod zz2 ) )
          <~~ ( ( << ff1 ,CoMod ff2 >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2 ) )

(* for sense , also in solution , not for primo reduction , but may for secondo reduction *)
| Project1_Project2_Pairing : forall (F1 F2 : obCoMod),

    ( @ 'UnitCoMod (Pair F1 F2) )
      <~~ ( << ( ~_1 @ F2 o>CoMod ( @ 'UnitCoMod F1 ) )
          ,CoMod ( ~_2 @ F1 o>CoMod ( @ 'UnitCoMod F2 ) ) >> )

(**TODO: IN POLY INSERT  twist o>*  ; IN SOL USE 'Twist o>| ~_1 o>CoMod ff  *)
(* for confluence , also in solution , immediately-derivable in polymorphism , not for primo reduction , but may for secondo reduction *)
(*ALT: in non-generalized form , change to (Once.SymContext2 (Cong.MorIndexer_Constant (Cong.SymContext2.SymContext2 _ ))) o>*| ,
but memo that only existence/propositional knowledge is   *)
| Project1_Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0)  (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0) (H : obCoMod),
    forall (a : 'Indexer(0 Context2 (Context1 A) ~> Context1 (Context2 A) )0%once),
    ( ~_1 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( ~_1 @ H o>CoMod ff1 )
          ,CoMod ( a o>*| ( ~_1 @ H o>CoMod ff2 ) ) >> )

(* for confluence , also in solution , immediately-derivable in polymorphism , not for primo reduction , but may for secondo reduction *)
| Project2_Pairing : forall (L : obCoMod) (F1 F2 : obCoMod) A
                       (ff1 : 'CoMod(0 Context1 A |- L ~> F1 )0) (ff2 : 'CoMod(0 Context2 A |- L ~> F2 )0) (H : obCoMod),
    forall (a : 'Indexer(0 Context1 (Context2 A) ~> Context2 (Context1 A) )0%once),
    ( ~_2 @ H o>CoMod ( << ff1 ,CoMod ff2 >> ) )
      <~~ ( << ( a o>*| ( ~_2 @ H o>CoMod ff1 ) )
          ,CoMod ( ~_2 @ H o>CoMod ff2 ) >> )

where "gg0 <~~ gg" := (@convMorCoMod _ _ _ gg gg0).

Hint Constructors convMorCoMod.

(**#+END_SRC

** BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)

Notation max m n := ((m + (Nat.sub n m))%coq_nat).

Fixpoint grade_Atom (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %atom) {struct gg} : nat . 
Proof.
  case : F G A / gg . 
  - intros ? ? ? ? a gg .
    exact: (S (grade_Atom _ _ _ gg)  + S (grade_Atom _ _ _ gg)  )%coq_nat .
  - intros ? ? ? ff' ? ? ff_ .
    exact: (S (grade_Atom _ _ _ ff' + grade_Atom _ _ _ ff_)%coq_nat )%coq_nat .
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
  - intros ? ? ? gg. exact: (S (grade_Atom gg)).
  - intros ? ? ? ? zz1 .
    exact: (S (S (grade _ _ _ zz1))).
  - intros ? ? ? ? zz2 .
    exact: (S (S (grade _ _ _ zz2))).
  - intros ? ? ? ? ff1 ff2 .
    refine (S (S (max (grade _ _ _ ff1) (grade _ _ _ ff2)))).
Defined.

Lemma grade_Atom_gt0 : forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %atom),
     ((S O) <= (grade_Atom gg))%coq_nat.
Proof. intros; case : gg; intros; apply/leP; intros; simpl; auto. Qed.

Lemma grade_gt0 : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 ),
     ((S O) <= (grade gg))%coq_nat.
Proof. intros; case : gg; intros; try exact: grade_Atom_gt0; apply/leP; intros; simpl; auto. Qed.

Ltac tac_grade_Atom_gt0 :=
  match goal with
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
                                          (@grade_Atom_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
                        gg4 : 'CoMod(0 _ |- _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
                                          (@grade_Atom_gt0 _ _ _ gg4)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
                  gg3 : 'CoMod(0 _ |- _ ~> _ )0 %atom |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)
                                          (@grade_Atom_gt0 _ _ _ gg3)
  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %atom ,
            gg2 : 'CoMod(0 _ |- _ ~> _ )0 %atom  |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) (@grade_Atom_gt0 _ _ _ gg2)

  | [ gg1 : 'CoMod(0 _ |- _ ~> _ )0 %atom  |- _ ] =>
    move : (@grade_Atom_gt0 _ _ _ gg1) 
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

Lemma degrade_Atom
  : ( forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 )
      (gg0 : 'CoMod(0 A |- F ~> G )0 ),
        gg0 <~~ gg -> ( grade_Atom gg0 <= grade_Atom gg )%coq_nat )%atom .
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

    Inductive morCoMod : Atom.obCoMod -> Atom.obCoMod -> obIndexer -> Type :=

    | PolyCoMod : forall (F F' : Atom.obCoMod) A,
        'CoMod(0 A |- F' ~> F )0 -> forall (F'' : Atom.obCoMod) B,
          'CoMod(0 B |- F'' ~> F' )0 -> 'CoMod(0 Tensor A B |- F'' ~> F )0

    | MorCoMod_Gen : forall (F G : obCoMod_Gen) (A : obIndexer_Param),
        @morCoMod_Gen F G A -> forall A' (a : 'Indexer(0 A' ~> A )0 %param),
          'CoMod(0 ObIndexer_Param A' |- (Atom.ObCoMod_Gen F) ~> (Atom.ObCoMod_Gen G) )0

    where "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_atom_scope. 

    End Section1.

    Module Export Ex_Notations.
      Delimit Scope sol_atom_scope with sol_atom.

      Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_atom_scope. 

      Notation "ff_ o>CoMod ff'" :=
        (@PolyCoMod _ _ _ ff' _ _ ff_) (at level 40 , ff' at next level) : sol_atom_scope.

      Notation "a o>| ''MorCoMod_Gen' ff" :=
        (@MorCoMod_Gen _ _ _ ff _ a) (at level 3) : sol_atom_scope.
    End Ex_Notations.

  End Atom.

  Section Section1.
  Import Atom.Ex_Notations.
  Delimit Scope sol_scope with sol.

  Inductive morCoMod : obCoMod -> obCoMod -> obIndexer -> Type :=

  | MorCoMod_Poly_Struc :  forall (F G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
        'CoMod(0 A |- F ~> G )0 -> 'CoMod(0 A' |- F ~> G )0

  | UnitCoMod : forall (F : obCoMod),
      'CoMod(0 Iden |- F ~> F )0

  | MorCoMod_Atom : forall (F G : Atom.obCoMod) A,
      'CoMod(0 A |- F ~> G )0 %sol_atom -> 'CoMod(0 A |- (ObCoMod_Atom F) ~> (ObCoMod_Atom G) )0

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
    Export Atom.Ex_Notations.
    Delimit Scope sol_scope with sol.

    Notation "''CoMod' (0 A |- F' ~> F )0" := (@morCoMod F' F A) : sol_scope. 

    Notation "a o>*| ff" :=
      (@MorCoMod_Poly_Struc _ _ _ _ a ff) (at level 3 , ff at next level, left associativity) : sol_scope.

    Notation "@ ''UnitCoMod' F" := (@UnitCoMod F) (at level 10, only parsing) : sol_scope.

    Notation "''UnitCoMod'" := (@UnitCoMod _) (at level 0) : sol_scope.

    Notation "''MorCoMod_Atom' ff" :=
      (@MorCoMod_Atom _ _ _ ff) (at level 3) : sol_scope.

    Notation "~_1 @ F2 o>CoMod zz1" :=
      (@Project1 _ F2 _ _ zz1) (at level 4, F2 at next level) : sol_scope.

    Notation "~_1 o>CoMod zz1" :=
      (@Project1 _ _ _ _ zz1) (at level 4) : sol_scope.

    Notation "~_2 @ F1 o>CoMod zz2" :=
      (@Project2 F1 _ _ _ zz2) (at level 4, F1 at next level) : sol_scope.

    Notation "~_2 o>CoMod zz2" :=
      (@Project2 _ _ _ _ zz2) (at level 4) : sol_scope.

    Notation "<< ff1 ,CoMod ff2 >>" :=
      (@Pairing _ _ _ _ ff1 ff2) (at level 4, ff1 at next level, ff2 at next level) : sol_scope.

  End Ex_Notations.

  Fixpoint toPolyMor_Atom (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol_atom)
           {struct gg} : 'CoMod(0 A |- F ~> G )0 %atom . 
  Proof.
    refine match gg with
           | ( ff_ o>CoMod ff' )%sol_atom => ( (toPolyMor_Atom _ _ _ ff_) o>CoMod (toPolyMor_Atom _ _ _ ff') )%atom
           | ( a o>| 'MorCoMod_Gen gg )%sol_atom => ( a o>| 'MorCoMod_Gen gg )%atom
           end.
  Defined.

  Fixpoint toPolyMor (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol)
           {struct gg} : 'CoMod(0 A |- F ~> G )0 . 
  Proof.
    refine match gg with
           | ( a o>*| ff )%sol => ( a o>*| (toPolyMor _ _ _ ff) )%poly
           | ( @'UnitCoMod F )%sol => ( @'UnitCoMod F )%poly
           | ( 'MorCoMod_Atom gg )%sol => ( 'MorCoMod_Atom (toPolyMor_Atom gg) )%poly
           | ( ~_1 @ F2 o>CoMod zz1 )%sol => ( ~_1 @ F2 o>CoMod (toPolyMor _ _ _ zz1) )%poly
           | ( ~_2 @ F1 o>CoMod zz2 )%sol => ( ~_2 @ F1 o>CoMod (toPolyMor _ _ _ zz2) )%poly
           | ( << ff1 ,CoMod ff2 >> )%sol => ( << (toPolyMor _ _ _ ff1) ,CoMod (toPolyMor _ _ _ ff2) >> )%poly
           end.
  Defined.

  (**#+END_SRC

** BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)
  
  Module Destruct_domPair.

  Inductive morCoMod_domPair
  : forall (F1 F2 : obCoMod), forall (G : obCoMod) A,
        'CoMod(0 A |- (Pair F1 F2) ~> G )0 %sol -> Type :=

  | MorCoMod_Poly_Struc : forall (M M' G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
        forall (gg : 'CoMod(0 A |- (Pair M M') ~> G )0 %sol ), 
          morCoMod_domPair ( a o>*| gg )%sol

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

  Module Destruct_domAtom.

  Inductive morCoMod_domAtom
  : forall (F : Atom.obCoMod) (G : obCoMod) A,
        'CoMod(0 A |- (ObCoMod_Atom F) ~> G )0 %sol -> Type :=

  | MorCoMod_Poly_Struc : forall (F : Atom.obCoMod) (G : obCoMod), forall (A A' : obIndexer) (a : 'Indexer(0 A' ~> A )0 %once),
        forall (gg : 'CoMod(0 A |- (ObCoMod_Atom F) ~> G )0 %sol ), 
          morCoMod_domAtom ( a o>*| gg )%sol

  | UnitCoMod : forall (F : Atom.obCoMod),
      morCoMod_domAtom ( @'UnitCoMod (ObCoMod_Atom F) )%sol 

  | MorCoMod_Atom : forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol_atom ),
      morCoMod_domAtom ( 'MorCoMod_Atom gg )%sol

  | Pairing : forall (L : Atom.obCoMod) (F1 F2 : obCoMod) A
                (ff1 : 'CoMod(0 Context1 A |- (ObCoMod_Atom L) ~> F1 )0 %sol)
                (ff2 : 'CoMod(0 Context2 A |- (ObCoMod_Atom L) ~> F2 )0 %sol),
      morCoMod_domAtom ( << ff1 ,CoMod ff2 >> )%sol .

  Definition morCoMod_domAtomP_Type
             (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ) :=
    ltac:( destruct F; [ refine (morCoMod_domAtom gg)
                       | intros; refine (unit : Type) ] ).

  Lemma morCoMod_domAtomP
    : forall (F G : obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %sol ), morCoMod_domAtomP_Type gg .
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

  End Destruct_domAtom.
  
End Sol.

(**#+END_SRC

* BLA

BLA

#+BEGIN_SRC coq :exports both :results silent **)

Module Resolve.

  Import Atom.Ex_Notations.
  Import Sol.Ex_Notations.
  
  Ltac tac_reduce_eauto12 := simpl in * ; eauto 12.
  Ltac tac_reduce := simpl in * ; eauto.

  Fixpoint solveCoMod_Atom len {struct len} :
     forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %atom),
     forall grade_Atom_gg : (grade_Atom gg <= len)%coq_nat,
       { ggSol : 'CoMod(0 A |- F ~> G )0 %sol_atom | ( (Sol.toPolyMor_Atom ggSol) <~~ gg )%atom } .
  Proof.
    case : len => [ | len ].

    (* len is O *)
    - ( move => F G A gg grade_Atom_gg ); exfalso; abstract tac_degrade grade_Atom_gg.

    (* len is (S len) *)
    - move => F G A gg; case : F G A / gg =>
      [ F G A A' a gg (* a o>* gg *)
      | F F' A ff' F'' B ff_ (* ff_ o>CoMod ff' *)
      | F G A gg A' a (* a o>| 'MorCoMod_Gen gg *)
      ] grade_Atom_gg .

      (* gg is a o>* gg *)
      + case: (solveCoMod_Atom len _ _ _ gg)
        => [ | ggSol ggSol_prop ] ;
            first by abstract tac_degrade grade_Atom_gg.

        { destruct ggSol as
              [ F F' A ff'Sol F'' B ff_Sol (* ff_Sol o>CoMod ff'Sol *)
              | F G A ggSol _A' _a (* _a o>| 'MorCoMod_Gen ggSol *) ] .

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( ff_Sol o>CoMod ff'Sol ) *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomTensor.morIndexer_codomTensorP a)
            => a_codomTensorP .
            destruct a_codomTensorP as
                [ B A A' a (* Tensor B a *)
                | A B' B b (* Tensor A b *) ] .

            + case: (solveCoMod_Atom len _ _ _ ((a o>* (Sol.toPolyMor_Atom ff'Sol))%atom))
              => [ | a_o_ff'Sol a_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_Atom_gg.
            
              exists ( ff_Sol o>CoMod a_o_ff'Sol  )%sol_atom .
              clear - ggSol_prop a_o_ff'Sol_prop. tac_reduce.

            + case: (solveCoMod_Atom len _ _ _ ((b o>* (Sol.toPolyMor_Atom ff_Sol))%atom))
            => [ | b_o_ff_Sol b_o_ff_Sol_prop ] ;
                first by abstract tac_degrade grade_Atom_gg.
            
              exists ( b_o_ff_Sol o>CoMod ff'Sol  )%sol_atom . 
              clear - ggSol_prop b_o_ff_Sol_prop. tac_reduce.

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( _a o>| 'MorCoMod_Gen ggSol ) *)          
          - move: (Cong.Destruct_MorIndexer_Param_codomObIndexer_Param.morIndexer_codomObIndexer_ParamP a)
            => a_codomObIndexer_ParamP .
            destruct a_codomObIndexer_ParamP as
                [ _A A' a (* MorIndexer_Constant _A A' a *) ] .

            + exists ( ( ( a o>Indexer _a)%param ) o>| 'MorCoMod_Gen ggSol )%sol_atom . 
              clear - ggSol_prop . tac_reduce .
        }

      (* gg is  ( ff_ o>CoMod ff' ) *)
      + case: (solveCoMod_Atom len _ _ _ ff_)
        => [ | ff_Sol ff_Sol_prop ] ;
            first by abstract tac_degrade grade_Atom_gg.
        
        case: (solveCoMod_Atom len _ _ _ ff')
        => [ |ff'Sol ff'Sol_prop ] ;
            first by abstract tac_degrade grade_Atom_gg.

        exists ( ff_Sol o>CoMod ff'Sol )%sol_atom.

        clear - ff_Sol_prop ff'Sol_prop. tac_reduce.
              
      (* gg is  ( a o>| 'MorCoMod_Gen gg ) *)
      + exists (  a o>| 'MorCoMod_Gen gg )%sol_atom. apply: Atom.convMorCoMod_Refl.
  Defined.

  Definition solveCoMod_Atom' :
     forall (F G : Atom.obCoMod) A (gg : 'CoMod(0 A |- F ~> G )0 %atom),
       { ggSol : 'CoMod(0 A |- F ~> G )0 %sol_atom | ( (Sol.toPolyMor_Atom ggSol) <~~ gg )%atom } .
  Admitted.
  
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
      | F G A A' a gg (* a o>*| gg *)
      | F (* @'UnitCoMod F *)
      | F G A gg (* 'MorCoMod_Atom gg *)
      | F1 F2 Z1 A zz1 (* ~_1 @ F2 o>CoMod zz1 *)
      | F1 F2 Z2 A zz2 (* ~_2 @ F1 o>CoMod zz2 *)
      | L F1 F2 A ff1 ff2 (* << ff1 ,CoMod ff2 >> *)
      ] grade_gg .

      (* gg is a o>* gg *)
      + all: cycle 1. 
      
      (* gg is ff_ o>CoMod ff' *)
      + all: cycle 1. 
        
      (* gg is a o>*| gg *)
      + case: (solveCoMod len _ _ _ gg)
        => [ | ggSol ggSol_prop ] ;
            first by abstract tac_degrade grade_gg.

        exists ( a o>*| ggSol )%sol.
        clear - ggSol_prop. abstract tac_reduce.

      (* gg is @'UnitCoMod F *)
      + exists (@'UnitCoMod F)%sol. apply: convMorCoMod_Refl.

      (* gg is 'MorCoMod_Atom gg *)
      + case: (solveCoMod_Atom' gg) => [ ggSol ggSol_prop ] .

        exists ( 'MorCoMod_Atom ggSol )%sol.
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
              [ F G A _A' _a ggSol (* _a o>*| ggSol *)
              | F (* @'UnitCoMod F *)
              | F G A ggSol (* 'MorCoMod_Atom ggSol *)
              | F1 F2 Z1 A zz1Sol (* ~_1 @ F2 o>CoMod zz1Sol *)
              | F1 F2 Z2 A zz2Sol (* ~_2 @ F1 o>CoMod zz2Sol *)
              | L F1 F2 A ff1Sol ff2Sol (* << ff1Sol ,CoMod ff2Sol >> *) ] .

          (* gg is a o>* gg , to a o>* ggSol , is  a o>* ( a o>*| ggSol ) *)          
          - case: (solveCoMod len _ _ _ ((fst (projT2 (MorCoMod_Poly_arrowStruc0 _a a)))
                                           o>* (Sol.toPolyMor ggSol)))
            => [ | a_o_ggSol a_o_ggSol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ( (snd (projT2 (MorCoMod_Poly_arrowStruc0 _a a))) o>*| a_o_ggSol )%sol .
            clear - ggSol_prop a_o_ggSol_prop. tac_reduce.

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* ( @'UnitCoMod F ) *)          
          - exfalso. clear - a . inversion_clear a.
            match goal with
            | [ X : Cong.MorIndexer_Param.morIndexer _ Iden |- _ ] => inversion X
            end.

          (* gg is  a o>* gg , to  a o>* ggSol , is  a o>* 'MorCoMod_Atom ggSol *)          
          - case: (solveCoMod_Atom' ((a o>* (Sol.toPolyMor_Atom ggSol))%atom))
            => [ a_o_ggSol a_o_ggSol_prop ] .

            exists ( 'MorCoMod_Atom ( a_o_ggSol )%atom )%sol .
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
              [ _F _G _A A' a ff_Sol (* a o>*| ff_Sol *)
              | _F (* @'UnitCoMod F *)
              | _F _G _A ff_Sol (* 'MorCoMod_Atom ff_Sol *)
              | F1 F2 Z1 _A zz1_Sol (* ~_1 @ F2 o>CoMod zz1_Sol *)
              | F1 F2 Z2 _A zz2_Sol (* ~_2 @ F1 o>CoMod zz2_Sol *)
              | L F1 F2 _A ff1_Sol ff2_Sol (* << ff1_Sol ,CoMod ff2_Sol >> *) ] .

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( a o>*| ff_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ( (Once._Cong.Tensor_arrow2 _ a)  o>*| ff_Sol_o_ff'Sol )%sol .
            clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is (@'UnitCoMod _F) o>CoMod ff'Sol  *)
          - exists ( (Once.IdenTensorR (Cong.MorIndexer_Constant (Cong.IdenTensorR.IdenTensorR _)))
                  o>*| ff'Sol )%sol . 
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.
          
          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom ff_Sol ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domAtom.morCoMod_domAtomP ff'Sol) => ff'Sol_domAtomP.
            destruct ff'Sol_domAtomP as
                [ F G A A' a ff'Sol  (*  ( a o>*| ff'Sol )%sol  *)
                | F (* ( @'UnitCoMod (ObCoMod_Atom F) )%sol *)
                | F G A ff'Sol (* ( 'MorCoMod_Atom ff'Sol )%sol *)
                | L F1 F2 A ff1'Sol ff2'Sol (* << ff1'Sol ,CoMod ff2'Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom ff_Sol ) o>CoMod (  a o>*| ff'Sol )   *)
            + case: (solveCoMod len _ _ _ (( Sol.toPolyMor ('MorCoMod_Atom ff_Sol)%sol ) o>CoMod (Sol.toPolyMor ff'Sol)))
              => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (Once._Cong.Tensor_arrow1 _ a) o>*| ff_Sol_o_ff'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom ff_Sol ) o>CoMod ( @'UnitCoMod (ObCoMod_Atom F) )  *)
          - exists ( (Once.IdenTensorL (Cong.MorIndexer_Constant (Cong.IdenTensorL.IdenTensorL _)))
                  o>*| ( 'MorCoMod_Atom ff_Sol ) )%sol .
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom ff_Sol ) o>CoMod ( 'MorCoMod_Atom ff'Sol )   *)
            + case: (solveCoMod_Atom' ( ( (Sol.toPolyMor_Atom ff_Sol) o>CoMod (Sol.toPolyMor_Atom ff'Sol) )%atom ))
              => [ ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ].

              exists ( 'MorCoMod_Atom ff_Sol_o_ff'Sol )%sol . 
              clear -ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

              (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( 'MorCoMod_Atom ff_Sol ) o>CoMod ff'Sol , is  ( 'MorCoMod_Atom ff_Sol ) o>CoMod ( << ff1'Sol ,CoMod ff2'Sol >>  )   *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ('MorCoMod_Atom ff_Sol)%sol) o>CoMod (Sol.toPolyMor ff1'Sol) ))
              => [ |ff_Sol_o_ff1'Sol ff_Sol_o_ff1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              case: (solveCoMod len _ _ _ ( (Sol.toPolyMor( 'MorCoMod_Atom ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff2'Sol)))
              => [ | ff_Sol_o_ff2'Sol ff_Sol_o_ff2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.
 
              exists ( (Once.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
                    o>*| ( << ( (Once.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*| ff_Sol_o_ff1'Sol )
                  ,CoMod ( (Once.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*| ff_Sol_o_ff2'Sol ) >> ) )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff1'Sol_prop ff_Sol_o_ff2'Sol_prop .

              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := (Sol.toPolyMor( 'MorCoMod_Atom ff_Sol )%sol) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := (Sol.toPolyMor( 'MorCoMod_Atom ff_Sol )%sol) o>CoMod ( << Sol.toPolyMor ff1'Sol ,CoMod Sol.toPolyMor ff2'Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( _ o>*| ( << _ o>*| ((Sol.toPolyMor( 'MorCoMod_Atom ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff1'Sol)) ,CoMod _ o>*| ((Sol.toPolyMor( 'MorCoMod_Atom ff_Sol )%sol) o>CoMod (Sol.toPolyMor ff2'Sol)) >> ) )); by eauto 12).

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_1 @ F2 o>CoMod zz1_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz1_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | zz1_Sol_o_ff'Sol zz1_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ((Once.SymTensorContext1 (Cong.MorIndexer_Constant (Cong.SymTensorContext1.SymTensorContext1 _ _)))
                 o>*| ( ~_1 @ F2 o>CoMod zz1_Sol_o_ff'Sol ) )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz1_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( ~_2 @ F1 o>CoMod zz2_Sol ) o>CoMod ff'Sol  *)
          - case: (solveCoMod len _ _ _ ( (Sol.toPolyMor zz2_Sol) o>CoMod (Sol.toPolyMor ff'Sol) ))
            => [ | zz2_Sol_o_ff'Sol zz2_Sol_o_ff'Sol_prop ] ;
                first by abstract tac_degrade grade_gg.

            exists ((Once.SymTensorContext2 (Cong.MorIndexer_Constant (Cong.SymTensorContext2.SymTensorContext2 _ _)))
                 o>*| ( ~_2 @ F1 o>CoMod zz2_Sol_o_ff'Sol ) )%sol .
            clear - ff_Sol_prop ff'Sol_prop zz2_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol  *)
          - move: (Sol.Destruct_domPair.morCoMod_domPairP ff'Sol) => ff'Sol_domPairP.
            destruct ff'Sol_domPairP as
                [ M M' G A A' a ff'Sol (* ( a o>*| ff'Sol )%sol *)
                | M M' (*  ( @'UnitCoMod (Pair M M') )%sol  *)
                | F1 F2 Z1 A zz1'Sol (*  ~_1 @ F2 o>CoMod zz1'Sol %sol *)
                | F1 F2 Z2 A zz2'Sol (*  ~_2 @ F1 o>CoMod zz2'Sol %sol *)
                | M M' F1 F2 A ff1'Sol ff2'Sol (* << ff1'Sol ,CoMod ff2'Sol >> %sol *) ] .

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol , is  (  << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod (  a o>*| ff'Sol )   *)
            + case: (solveCoMod len _ _ _ (( << (Sol.toPolyMor ff1_Sol) ,CoMod (Sol.toPolyMor ff2_Sol) >> ) o>CoMod (Sol.toPolyMor ff'Sol)))
              => [ | ff_Sol_o_ff'Sol ff_Sol_o_ff'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (Once._Cong.Tensor_arrow1 _ a) o>*| ff_Sol_o_ff'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop ff_Sol_o_ff'Sol_prop . tac_reduce_eauto12.

          (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ff'Sol , is  (  << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( @'UnitCoMod (Pair M M') )   *)
          - exists ( (Once.IdenTensorL (Cong.MorIndexer_Constant (Cong.IdenTensorL.IdenTensorL _)))
                  o>*| ( << ff1_Sol ,CoMod ff2_Sol >> ) )%sol .
            clear -ff_Sol_prop ff'Sol_prop. tac_reduce.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( ~_1 @ F2 o>CoMod zz1'Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff1_Sol) o>CoMod (Sol.toPolyMor zz1'Sol) ))
              => [ | ff1_Sol_o_zz1'Sol ff1_Sol_o_zz1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ((Once.AssocTensorContext1 (Cong.MorIndexer_Constant (Cong.AssocTensorContext1.AssocTensorContext1 _ _)))
                   o>*| ff1_Sol_o_zz1'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop  ff1_Sol_o_zz1'Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( ~_2 @ F1 o>CoMod zz2'Sol )  *)
            + case: (solveCoMod len _ _ _ ( (Sol.toPolyMor ff2_Sol) o>CoMod (Sol.toPolyMor zz2'Sol) ))
              => [ | ff2_Sol_o_zz2'Sol ff2_Sol_o_zz2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ((Once.AssocTensorContext2 (Cong.MorIndexer_Constant (Cong.AssocTensorContext2.AssocTensorContext2 _ _)))
                   o>*| ff2_Sol_o_zz2'Sol )%sol .
              clear - ff_Sol_prop ff'Sol_prop  ff2_Sol_o_zz2'Sol_prop . tac_reduce_eauto12.

            (* gg is (ff_ o>CoMod ff') , to  (ff_Sol o>CoMod ff'Sol) , is ( << ff1_Sol ,CoMod ff2_Sol >> ) o>CoMod ( << ff1'Sol ,CoMod ff2'Sol >> )  *)
            + case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff1'Sol)))
              => [ | ff_Sol_off1'Sol ff_Sol_off1'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              case: (solveCoMod len _ _ _ (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff2'Sol)))
              => [ | ff_Sol_off2'Sol ff_Sol_off2'Sol_prop ] ;
                  first by abstract tac_degrade grade_gg.

              exists ( (Once.Sym (Cong.MorIndexer_Constant (Cong.Sym.Sym _ _)))
                    o>*| ( << ( (Once.AssocContext1 (Cong.MorIndexer_Constant (Cong.AssocContext1.AssocContext1 _ _))) o>*| ff_Sol_off1'Sol )
                           ,CoMod ( (Once.AssocContext2 (Cong.MorIndexer_Constant (Cong.AssocContext2.AssocContext2 _ _))) o>*| ff_Sol_off2'Sol ) >> ) )%sol .

              clear - ff_Sol_prop ff'Sol_prop ff_Sol_off1'Sol_prop ff_Sol_off2'Sol_prop .
              abstract (simpl in *; eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod ff'); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod ( << Sol.toPolyMor ff1'Sol ,CoMod Sol.toPolyMor ff2'Sol >> )); first (by eauto);
                        eapply convMorCoMod_Trans with (uTrans := ( _ o>*| ( << _ o>*| (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff1'Sol)) ,CoMod _ o>*| (( << Sol.toPolyMor ff1_Sol ,CoMod Sol.toPolyMor ff2_Sol >> ) o>CoMod (Sol.toPolyMor ff2'Sol)) >> ) )); by eauto 12).
        }

  Defined.

End Resolve.

End MULTIFOLD.

(**#+END_SRC

Voila. **)
