(** 

https://github.com/1337777/cartier/blob/master/cartierSolution12.v

Proof-assistants, sheaves and applications

----- **)
Module Example0.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path fintype tuple finfun bigop ssralg. 
Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.

Parameter Cat : Set.
Parameter Functor : Cat -> Cat -> Set.
Parameter Object : Cat -> Set.
Parameter Rel : Cat -> Cat -> Set.
Parameter Transf : forall C A B: Cat, Rel A B ->  Functor C A ->  Functor C B -> Set.
Parameter Adjunc : forall C D: Cat, Functor C D -> Functor D C -> Set.

Inductive object: forall (C : Cat), Type :=
| Gen_object : forall {C : Cat}, Object C -> object C
| App_object : forall {C D: Cat}, object C -> functor C D ->  object D

with functor: forall (C D : Cat), Type :=
| Gen_functor : forall {C D : Cat}, Functor C D -> functor C D
| Subst_functor : forall {C D E: Cat}, functor C D -> functor D E ->   functor C E
| Id_functor : forall C : Cat, functor C C

with rel: forall (C D : Cat), Type :=
| Gen_rel : forall (C D : Cat), Rel C D -> rel C D
| Tensor_rel : forall A B C, rel C B -> rel B A -> rel C A
| Id_rel :  forall C : Cat,  forall C' (F' : functor C' C), forall D' (G' : functor D' C),  rel C' D'
| Imply_rel : forall  A C B, rel A C -> rel B C -> rel B A
| ImplyCo_rel : forall  C A B, rel C A -> rel C B -> rel A B .

Inductive adjunc : forall C D: Cat, functor C D -> functor D C -> Type := 
| Gen_adjunc : forall (C D: Cat) (LeftAdjunc_functor : Functor C D) (RightAdjunc_functor : Functor D C), 
  adjunc (Gen_functor LeftAdjunc_functor) (Gen_functor RightAdjunc_functor)

with arrow: forall A B: Cat, rel A B -> object A -> object B -> Type :=
| App_arrow : forall C A B: Cat, forall (R : rel A B) (F : functor C A) (G : functor C B),
  forall (X : object C), transf R F G -> arrow R (App_object X F) (App_object X G)

with transf:  forall C A B: Cat, rel A B -> functor C A -> functor C B -> Type :=
| Gen_transf : forall C A B: Cat, forall (F : Functor C A) (R: Rel A B) (G: Functor C B), 
  Transf R F G -> transf (Gen_rel R) (Gen_functor F) (Gen_functor G) 
| Id_transf : forall E C: Cat, forall (F : functor C E),  transf  (Id_rel F (Id_functor _) ) (Id_functor _)  F
| IdCo_transf : forall E C: Cat, forall (F : functor C E),  transf (Id_rel (Id_functor _) F)  F (Id_functor _)
| UnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
    transf   (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_functor C)  (LeftAdjunc_functor)
| CoUnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
    transf  (Id_rel (LeftAdjunc_functor) (Id_functor _)) (RightAdjunc_functor) (Id_functor _)
| App_transf : forall C D: Cat, forall R : rel C D, forall  C' D' (F : functor C C'), forall S : rel C' D', forall (G : functor D D'),
            forall  A (M : functor A C) (N : functor A D), 
    transf R M  N -> funcTransf R S F G -> transf S (Subst_functor M F) (Subst_functor N G)

with funcTransf: forall C D: Cat, rel C D -> forall C' D', rel C' D' -> forall (F : functor C C') (G : functor D D'), Type :=  

| Subst_funcTransf : forall C D: Cat, forall R : rel C D, forall  C' D' (F : functor C C'), forall S : rel C' D', forall (G : functor D D'),
  forall  C'' D'' (F' : functor C' C''), forall T : rel C'' D'', forall (G' : functor D' D''),
  funcTransf R S F G -> funcTransf S T F' G' -> funcTransf R T (Subst_functor F F') (Subst_functor G G')
| Id_funcTransf : forall C D: Cat, forall R : rel C D, 
    funcTransf R R (Id_functor _)  (Id_functor _) 
| AnteceComp_funcTransf : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> funcTransf (Id_rel G (Id_functor B)) R F (Id_functor B)
| ConseqComp_funcTransf : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> funcTransf (Id_rel (Id_functor A) F) R (Id_functor A) G
| CoYoneda_anteceComp_funcTransf : forall C D: Cat, forall D' (H : functor D  D'), forall R : rel C D,
forall  C' (F : functor C C')  (T : rel C' D'),
  funcTransf R T F H ->
  funcTransf (Tensor_rel R (Id_rel H (Id_functor _))) T F (Id_functor _)
| CoYoneda_conseqComp_funcTransf : forall C D: Cat, forall C' (H : functor C C'), forall R : rel C D,
forall  D' (G : functor D D') (T : rel C' D'),
  funcTransf R T H G ->
  funcTransf (Tensor_rel (Id_rel (Id_functor _) H) R) T (Id_functor _) G
| Imply_lambda_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  C' (F : functor C C'), forall S : rel C' D, 
  funcTransf (Tensor_rel R R') S F (Id_functor _) -> 
  funcTransf R (Imply_rel R' S) F (Id_functor _)
| Imply_app_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  C' (F : functor C C'), forall S : rel C' D, 
  funcTransf R (Imply_rel R' S) F (Id_functor _) ->
  funcTransf (Tensor_rel R R') S F (Id_functor _) 
| Imply_eval_funcTransf : forall C E D: Cat, forall R : rel E C, forall S : rel D C,
   forall D' (F : functor D D') C' (G : functor C C') (T : rel D' C'),
  funcTransf S T F G ->
  funcTransf (Tensor_rel (Imply_rel R S) R) T F G
| Imply_pair_funcTransf : forall C E D: Cat, forall R : rel C E, forall  (R' : rel D C), 
  forall D' (F : functor D' D) C' (G : functor C' C) (T : rel D' C'),
  funcTransf T R' F G ->
  funcTransf T (Imply_rel R (Tensor_rel R' R)) F G
| TODO_ImplyCo_lambda_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  D' (G : functor D D'), forall S : rel C D', 
  funcTransf (Tensor_rel R R') S (Id_functor _) G -> 
  funcTransf R' (ImplyCo_rel R S) (Id_functor _) G
| TensorCo_funcTransf : forall (C A B : Cat) (R : rel A B) (G : functor C B)  (D : Cat) (S : rel D A) C' (H : functor C' D) (S' : rel C' C),
  forall (F : functor C A), funcTransf S' S H F -> funcTransf (Id_rel G (Id_functor _) ) R F (Id_functor _) ->
  funcTransf S' (Tensor_rel S R) H G 
| Tensor_funcTransf : forall (C A B : Cat)   (R : rel A B)  C'' (G : functor C'' B)  (R' : rel C C'')  
  (D : Cat) (S : rel D A)  (H : functor C D)  ,
  forall (F (* existential *): functor C A), funcTransf (Id_rel (Id_functor _) H) S (Id_functor _) F -> funcTransf R' R F G ->
  funcTransf R' (Tensor_rel S R) H G  .
End Example0.
