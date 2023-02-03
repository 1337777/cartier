(** # #
#+TITLE: cartierSolution12.v

Proph

https://github.com/1337777/cartier/blob/master/cartierSolution12.v

Proof-assistants, sheaves and applications

NOTE: ONE OF THESE FORMULATIONS WORKS BUT ALL WRONG ATTEMPTS ARE KEPT IN TRE FILE FOR NOW FOR FUTURE REFERENCE

-----

#+BEGIN_SRC coq :exports both :results silent # # **)

Module Example.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path fintype tuple finfun bigop ssralg. 

Set Implicit Arguments. Unset Strict Implicit. Unset Printing Implicit Defensive.

Parameter Cat : Set.
Parameter Functor : Cat -> Cat -> Set.
Parameter Object : Cat -> Set.
Parameter Rel : Cat -> Cat -> Set.
Parameter Transf : forall [C A B: Cat], Rel A B ->  Functor C A ->  Functor C B -> Set.
Parameter Adjunc : forall [C D: Cat], Functor C D -> Functor D C -> Set.

Inductive object: forall (C : Cat), Type :=
| Gen_object : forall [C : Cat], Object C -> object C
| App_object : forall [C D: Cat], object C -> functor C D ->  object D

with functor: forall (C D : Cat), Type :=
| Gen_functor : forall [C D : Cat], Functor C D -> functor C D
| Subst_functor : forall [C D E: Cat], functor C D -> functor D E ->   functor C E
| Id_functor : forall C : Cat, functor C C
| App_functor : forall [C D E: Cat], Functor C D -> functor D E ->   functor C E (* from sol *)

with rel: forall (C D : Cat), Type :=
| Gen_rel : forall [C D : Cat], Rel C D -> rel C D
| Tensor_rel : forall [A B C : Cat], rel C B -> rel B A -> rel C A
| (* OK version *) Tensor_antec_rel' : forall [A B C B' : Cat], rel C B -> functor B B' -> rel B' A -> rel C A
| Tensor_rel' : forall [A B C B' : Cat], rel C B' -> functor B B' -> rel B' A -> rel C A
| Id_rel :  forall [C C' D' : Cat], functor C' C -> functor D' C -> rel C' D'
| Imply_antec_rel : forall  [A C B : Cat], rel A C -> rel B C -> rel B A
| Imply_antec_rel' : forall  [A C B C' : Cat], rel A C -> rel B C' -> functor C C' -> rel B A
| Imply_conse_rel : forall [C A B : Cat], rel C A -> rel C B -> rel A B
| Subst_rel : forall [C D C' D': Cat], rel C D -> functor C' C -> functor D' D ->  rel C' D' .

Inductive adjunc : forall [C D: Cat], functor C D -> functor D C -> Type := 

| Gen_adjunc : forall [C D: Cat] (LeftAdjunc_functor : Functor C D) (RightAdjunc_functor : Functor D C), 
  adjunc (Gen_functor LeftAdjunc_functor) (Gen_functor RightAdjunc_functor)

with arrow: forall [A B: Cat], rel A B -> object A -> object B -> Type :=

| App_arrow : forall [C A B: Cat], forall (R : rel A B) (F : functor C A) (G : functor C B),
  forall (X : object C), transf R F G -> arrow R (App_object X F) (App_object X G)

with transf:  forall [C A B: Cat], rel A B -> functor C A -> functor C B -> Type :=

| Gen_transf : forall C A B: Cat, forall (F : Functor C A) (R: Rel A B) (G: Functor C B), 
  Transf R F G -> forall D (X : functor D C), transf (Gen_rel R) (Subst_functor X (Gen_functor F)) (Subst_functor X (Gen_functor G))

| Subst_transf : forall C A B: Cat, forall (R : rel A B) (F : functor C A) (G : functor C B),
  forall D (X : functor D C), transf R F G -> transf R (Subst_functor X F) (Subst_functor X G)

| Id_antec_transf' : forall [E C: Cat] (F : functor C E),  transf  (Id_rel F (Id_functor _) ) (Id_functor _)  F

| Id_conse_transf' : forall [E C: Cat] (F : functor C E),  transf (Id_rel (Id_functor _) F)  F (Id_functor _)


| Id_antec_transf : forall E C: Cat, forall (F : functor C E), forall D (X : functor D C),
       transf  (Id_rel F (Id_functor _) ) X  (Subst_functor X F)
| Id_conse_transf : forall E C: Cat, forall (F : functor C E),  forall D (X : functor D C),
      transf (Id_rel (Id_functor _) F)   (Subst_functor X F) X

| UnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A C), 
    transf   (Id_rel (Id_functor _) (RightAdjunc_functor) ) X  (Subst_functor X (LeftAdjunc_functor))

| CoUnitAdjunc_transf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A D), 
    transf  (Id_rel (LeftAdjunc_functor) (Id_functor D)) (Subst_functor X (RightAdjunc_functor)) X

| UnitAdjunc_transf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
    transf   (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_functor C)  (LeftAdjunc_functor)

| CoUnitAdjunc_transf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
    transf  (Id_rel (LeftAdjunc_functor) (Id_functor D)) (RightAdjunc_functor) (Id_functor D)

| App_transf : forall [C D C' D' A: Cat], forall [R : rel C D] [F : functor C C'] [S : rel C' D'] [G : functor D D'] [M : functor A C] [N : functor A D], 
    transf R M  N -> funcTransf R S F G -> transf S (Subst_functor M F) (Subst_functor N G)

| App_conse_transf' : forall [C D D' A: Cat], forall [R : rel C D] [S : rel C D'] [G : functor A D'] [M : functor A C] [N : functor A D], 
    transf R M  N -> funcTransf (Subst_rel R (Id_functor _) N) S (Id_functor C) G -> transf S M G
    
with funcTransf: forall [C D C' D': Cat], rel C D -> rel C' D' -> functor C C' -> functor D D' -> Type :=  
   

| Subst_funcTransf : forall [C D C' D' C'' D'': Cat], forall [R : rel C D] [S : rel C' D'] [F : functor C C'] [G : functor D D']
  [T : rel C'' D''] [F' : functor C C''] [G' : functor D D''],
  funcTransf R S F G -> funcTransf (Subst_rel S F G) T F' G' -> funcTransf R T F' G'

| Id_funcTransf : forall C D: Cat, forall R : rel C D, 
  forall (C' D': Cat) (F : functor C' C) (G : functor D' D), 
    funcTransf (Subst_rel R F G) R F G

| Restr_funcTransf (* admissible *): forall C D: Cat,  forall  C' D' (F : functor C C'), forall S : rel C' D', forall (G : functor D D'),
  forall  C'' D'' (F' : functor C' C''), forall T : rel C'' D'', forall (G' : functor D' D''),
   funcTransf S T F' G' -> funcTransf (Subst_rel S F G) T (Subst_functor F F') (Subst_functor G G')

| Comp_antec_funcTransf : forall [C A B: Cat], forall [R: rel A B] [F : functor C A] [G: functor C B],
    transf R F G -> funcTransf (Id_rel G (Id_functor B)) R F (Id_functor B)

| Comp_antec_funcTransf' : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> forall B' (K: functor B' B), funcTransf (Id_rel G K) R F K


| Comp_conse_funcTransf : forall [C A B: Cat], forall [R: rel A B] [F : functor C A] [G: functor C B],
    transf R F G -> funcTransf (Id_rel (Id_functor A) F) R (Id_functor A) G

| Comp_conse_funcTransf' : forall C A B: Cat, forall (F : functor C A)  (R: rel A B)  (G: functor C B) ,
    transf R F G -> forall A' (K: functor A' A), funcTransf (Id_rel K F) R K G


| CoYoneda_antec_funcTransf : forall (C D D' : Cat) (H : functor D D') (R : rel C D) 
    (C' : Cat) (F : functor C C') (T : rel C' D'),
    funcTransf R T F H ->
    funcTransf (Tensor_rel R (Id_rel H (Id_functor D'))) T F (Id_functor D')

| CoYoneda_antec_funcTransf' : forall (C D D' : Cat) (H : functor D D') (R : rel C D) 
    (C' : Cat) (F : functor C C') (T : rel C' D'),
    funcTransf R T F H ->
    forall (D0 : Cat) (K : functor D0 D'),
    funcTransf (Tensor_rel R (Id_rel H K)) T F K

| CoYoneda_antec_funcTransf''_okforcut : forall (C D : Cat) (R : rel C D)  E  (K : functor E D)
    (C' E' : Cat) (S : rel C' E') (F : functor C' C) (G : functor E' E),
    funcTransf S (Tensor_rel R (Id_rel (Id_functor D) K)) F G -> 
     funcTransf S R F (Subst_functor G K)

| TEST_ALT_CoYoneda_antec_appId_funcTransf' (* OK version to derive *): 
forall C D: Cat, forall D0 (H : functor D  D0), forall R : rel C D,
forall  C' (F : functor C C') D' (G : functor D0 D') (T : rel C' D'), (* TODO: should G be Id_functor ? *)
    funcTransf (Tensor_rel R (Id_rel H (Id_functor D0))) T F G -> 
    funcTransf R T F (Subst_functor H G)

| CoYoneda_conse_funcTransf : forall C D: Cat, forall C' (H : functor C C'), forall R : rel C D, (* todo: redo*)
forall  D' (G : functor D D') (T : rel C' D'),
  funcTransf R T H G ->
  funcTransf (Tensor_rel (Id_rel (Id_functor _) H) R) T (Id_functor _) G

| Imply_antec_lambda_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  C' (F : functor C C'), forall S : rel C' D, 
  funcTransf (Tensor_rel R R') S F (Id_functor _) -> 
  funcTransf R (Imply_antec_rel R' S) F (Id_functor _)

| Imply_antec_app_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  C' (F : functor C C'), forall S : rel C' D, 
  funcTransf R (Imply_antec_rel R' S) F (Id_functor _) ->
  funcTransf (Tensor_rel R R') S F (Id_functor _) 

| Imply_antec_app_funcTransf' : forall (C E D : Cat)  (R' : rel E D) 
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' (D'D : functor D' D)  (Q : rel E' D'),
    funcTransf P   (Imply_antec_rel R' S) F   E'E ->
    funcTransf Q    R'                    E'E D'D ->
    funcTransf (Tensor_rel P Q) S F D'D

| Imply_antec_app_funcTransf'' : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' (D'D : functor D' D) (R : rel E D'),
    funcTransf P (Imply_antec_rel' R S D'D) F E'E ->
    funcTransf (Tensor_antec_rel' P E'E R) S F D'D

| Imply_antec_app_funcTransf'''_param (* old *) : forall (C E D : Cat)  
(C' : Cat) (F : functor C C') (S : rel C' D)
E' (E'E : functor E' E) (P : rel C E')
D' (D'D : functor D' D) (R : rel E D') ,
funcTransf P (Imply_antec_rel' R S D'D) F E'E ->
forall D'' (D''D' : functor D'' D') (Q : rel E' D''),
funcTransf Q  R E'E D''D' ->
funcTransf (Tensor_rel P Q) S F (Subst_functor D''D' D'D)

| Imply_antec_app_funcTransf'''_param' (* new  *): forall (C E D : Cat)  
    (C' : Cat) (F : functor C C') (S : rel C' D)
    E' E0 (E0E : functor E0 E) (P : rel C E')
    D' (D'D : functor D' D) (R : rel E D')  (H : functor E' E0),
  funcTransf P (Imply_antec_rel' R S D'D) F (Subst_functor H E0E) ->
  forall D'' (D''D' : functor D'' D') (Q : rel E0 D''),
  funcTransf Q  R E0E D''D' ->
  funcTransf (Tensor_antec_rel' P H Q) S F (Subst_functor D''D' D'D)

| Imply_antec_app_funcTransf'''_param'' (* OK version ; OR USE DINATURALITY ??*): forall (C E D : Cat)  
    (C' : Cat) (F : functor C C') (S : rel C' D)
    E' E0 (E0E : functor E0 E) (P : rel C E0)
    D' (D'D : functor D' D) (R : rel E D')  (H : functor E' E0),
  funcTransf P (Imply_antec_rel' R S D'D) F  E0E ->
  forall D'' (D''D' : functor D'' D') (Q : rel E0 D''),
  funcTransf Q  R E0E D''D' (* unused; should restrict this to H ? also P then general E'E ... nope just nice cast blended ... or yep*) ->
  funcTransf (Tensor_rel' P H Q) S F (Subst_functor D''D' D'D)

| Imply_antec_lambda_funcTransf' (* OK version for skew bif *) : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' (D'D : functor D' D) (R : rel E D'),
    funcTransf (Tensor_antec_rel' P E'E R) S F D'D ->
    funcTransf P (Imply_antec_rel' R S D'D) F E'E

| Imply_antec_lambda_funcTransf''' (* OK version for bif;  todo change of param version; nope use DINATURALITY*) : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E)
      D' (D'D : functor D' D) (R : rel E D'),
    funcTransf (Tensor_rel' P E'E R) S F D'D ->
    funcTransf (Subst_rel P (Id_functor _) E'E) (Imply_antec_rel' R S D'D) F E'E

| Imply_antec_lambda_funcTransf'''_param (* OK version for bif;  param versionl; nope use DINATURALITY  *) : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E)
      D' D0 (D0D : functor D0 D) (R : rel E D0),
    funcTransf (Tensor_rel' P E'E R(* contra subst here *)) S F D0D ->
    forall (T : rel E D') (H : functor D' D0), 
    funcTransf T R (Id_functor _)(* ?must be id? not really, and must change if imply_bif is more general *) 
                H (* on cut-free param-arrow then R is uniquely-recoverable/determined subformula of T  *) -> 
    funcTransf (Subst_rel P (Id_functor _) E'E) (Imply_antec_rel' T S (Subst_functor H D0D)) F E'E

| Imply_antec_lambda_funcTransf'' (* old test *) : forall (C E D : Cat)  
      (C' : Cat) (F : functor C C') (S : rel C' D)
      E' (E'E : functor E' E) (P : rel C E')
      D' D0 (D0D : functor D0 D) (R : rel E D0),
    funcTransf (Tensor_antec_rel' P E'E R) S F D0D ->
    forall (T : rel E D') (H : functor D' D0), funcTransf T R (Id_functor _)(* must be id *) H ->
    funcTransf P (Imply_antec_rel' T S (Subst_functor H D0D)) F E'E



| TODO_Imply_conse_lambda_funcTransf : forall C E D: Cat, forall R : rel C E, forall (R' : rel E D), forall  D' (G : functor D D'), forall S : rel C D', 
  funcTransf (Tensor_rel R R') S (Id_functor _) G -> 
  funcTransf R' (Imply_conse_rel R S) (Id_functor _) G

| Tensor_antec_funcTransf : forall (C A B : Cat) (R : rel A B) (G : functor C B)  (D : Cat) (S : rel D A) C' (H : functor C' D) (S' : rel C' C),
  forall (F : functor C A), funcTransf S' S H F -> funcTransf (Id_rel G (Id_functor _) ) R F (Id_functor _) ->
  funcTransf S' (Tensor_rel S R) H G 

| Tensor_antec_funcTransf' (* OK version *): forall (C A B : Cat) (R : rel A B) B' (G : functor C B')  (K : functor B' B) (D : Cat) (S : rel D A) C' (H : functor C' D) (S' : rel C' C),
forall  (F : functor C A), funcTransf S' S H F -> funcTransf (Id_rel G (Id_functor B') ) R F K ->
  funcTransf S' (Tensor_rel S R) H (Subst_functor G K) 

| Tensor_antec_funcTransf'' (* OK version for skew bif *) : forall (D A  : Cat)  (S : rel D A) C' (H : functor C' D) C (F : functor C A) (S' : rel C' C)
E E' (R : rel E E') (G : functor A E)  A' (K : functor A' E')  (R' : rel A A')  ,
 funcTransf S' S H F -> funcTransf R' R G K ->
  funcTransf (Tensor_antec_rel' S' F R') (Tensor_antec_rel' S G R) H K

| Tensor_antec_funcTransf'''  : forall (D A  E : Cat)  (S : rel D E) C' (H : functor C' D) A0 (F : functor A0 A) (S' : rel C' A)
 E' (R : rel E E') (G : functor A E)  A' (K : functor A' E')  (R' : rel A A')  ,
 funcTransf S' S H G -> funcTransf R' R G K ->
  funcTransf (Tensor_rel' S' F R') (Tensor_rel' S (* (Subst_functor F G) *) G R) H K (* some structural cast is blended here *)

| Tensor_conse_funcTransf : forall (C A B : Cat)   (R : rel A B)  C'' (G : functor C'' B)  (R' : rel C C'')  
  (D : Cat) (S : rel D A)  (H : functor C D)  ,
  forall (F (* existential *): functor C A), funcTransf (Id_rel (Id_functor _) H) S (Id_functor _) F -> funcTransf R' R F G ->
  funcTransf R' (Tensor_rel S R) H G

| Imply_antec_funcTransf :  forall  [A C B C' : Cat] (R : rel A C) (S : rel B C') (K : functor C C')
B' (F : functor B B')  C'' (G : functor C' C'')  (S' : rel B' C''),
funcTransf S S' F G  (* G must be id too ? so adj param D'D dont change *) ->
funcTransf (Imply_antec_rel' R S K) (Imply_antec_rel' R S' (Subst_functor K G)) F (Id_functor _) (* apparently must be id so adj param E'E dont change *)

| Imply_antec_funcTransf''_bif  (* NOPE because contravariance ? *):  forall  [A C0 B C' : Cat] (R' : rel A C0) (S : rel B C') (K : functor C0 C')
B' (F : functor B B')  C'' (G : functor C' C'')  (S' : rel B' C'')
C (H : functor C C0) (R : rel A C),
funcTransf S S' F G (* must G be id ? *) ->  funcTransf R R' (Id_functor _)(* must be id; note this is contra now *) H ->
funcTransf (Imply_antec_rel' R' S K) (Imply_antec_rel' R S' (Subst_functor H (Subst_functor K G))) F (Id_functor _)(* must be id *)

| Imply_antec_funcTransf''_bif'  (* NOPE because contravariance ? *):  forall  [A A0 C0 B C' : Cat] (R' : rel A0 C0) (S : rel B C') (K : functor C0 C')
B' (F : functor B B')  C'' (G : functor C' C'')  (S' : rel B' C'')
C (H : functor C C0) (R : rel A C),
funcTransf S S' F G (* must G be id ? *) -> forall (L : functor A A0),  funcTransf R R' L(* ?? must be id? more general lambda too; note this is contra now; or assume it is id only for cast*) H ->
forall  A1 (M : functor A1 A),  
funcTransf (Imply_antec_rel' (Subst_rel R' (Subst_functor M L) (Id_functor _)) S K) (Imply_antec_rel' R S' (Subst_functor H (Subst_functor K G))) F M(* must be id; or restrict R'? yeo, input M to restrict rr *)

(* from sol *)
| Gen_Comp_antec_funcTransf : forall C A B: Cat, forall (F : Functor C A) (R: Rel A B) (G: Functor C B), 
  Transf R F G -> funcTransf  (Id_rel (Gen_functor G)  (Id_functor _) )  (Gen_rel R) (Gen_functor F) (Id_functor _)

| Gen_Comp_conse_funcTransf : forall C A B: Cat, forall (F : Functor C A) (R: Rel A B) (G: Functor C B), 
  Transf R F G -> funcTransf   (Id_rel  (Id_functor _)  (Gen_functor F))  (Gen_rel R)  (Id_functor _)  (Gen_functor G) 

| Id_antec_Comp_antec_funcTransf' : forall [E C: Cat] (F : functor C E), 
  funcTransf (Id_rel F (Id_functor _)) (Id_rel F (Id_functor _) ) (Id_functor _)  (Id_functor _)

| Id_antec_Comp_conse_funcTransf' : forall [E C: Cat] (F : functor C E), 
  funcTransf (Id_rel (Id_functor _) (Id_functor _)) (Id_rel F (Id_functor _) ) (Id_functor _)  F

| Id_conse_Comp_antec_funcTransf' : forall [E C: Cat] (F : functor C E), 
  funcTransf (Id_rel (Id_functor _) (Id_functor _)) (Id_rel (Id_functor _) F)  F (Id_functor _)

| Id_conse_Comp_conse_funcTransf' : forall [E C: Cat] (F : functor C E), 
  funcTransf (Id_rel (Id_functor _) F) (Id_rel (Id_functor _) F)  (Id_functor _) (Id_functor _)

| Id_antec_Comp_antec_funcTransf : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),
  funcTransf (Id_rel (Subst_functor X F) (Id_functor _)) (Id_rel F (Id_functor _) ) X  (Id_functor _)

| Id_antec_Comp_antec_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),  forall A' (Y : functor A' _),
  funcTransf (Id_rel (Subst_functor X F) Y) (Id_rel F (Id_functor _) ) X  Y

| Id_antec_Comp_conse_funcTransf : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),
  funcTransf (Id_rel (Id_functor _) X) (Id_rel F (Id_functor _) ) (Id_functor _) (Subst_functor X F)

| Id_antec_Comp_conse_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _), forall A' (Y : functor A' _),
  funcTransf (Id_rel Y X) (Id_rel F (Id_functor _) ) Y (Subst_functor X F)

| Id_conse_Comp_antec_funcTransf : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),
  funcTransf (Id_rel X (Id_functor _)) (Id_rel (Id_functor _) F)  (Subst_functor X F) (Id_functor _)

| Id_conse_Comp_conse_funcTransf : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),
  funcTransf (Id_rel (Id_functor _) (Subst_functor X F)) (Id_rel (Id_functor _) F)  (Id_functor _) X

| Id_conse_Comp_conse_funcTransf'' : forall E C: Cat, forall (F : functor C E), forall A (X : functor A _),  forall A' (Y : functor A' _),
  funcTransf (Id_rel Y (Subst_functor X F)) (Id_rel (Id_functor _) F)  Y X

| UnitAdjunc_Comp_antec_funcTransf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
    funcTransf (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_functor C)  (Id_functor _)

| UnitAdjunc_Comp_antec_funcTransf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A C), 
      funcTransf (Id_rel (Subst_functor X (LeftAdjunc_functor)) (Id_functor D)) (Id_rel (Id_functor _) (RightAdjunc_functor) ) X  (Id_functor D)

| UnitAdjunc_Comp_antec_funcTransf'' (* bad  *): forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A C), forall B (Y : functor B D), 
      funcTransf (Id_rel (Subst_functor X (LeftAdjunc_functor)) Y) (Id_rel (Id_functor _) (RightAdjunc_functor) ) X  Y

| UnitAdjunc_Comp_conse_funcTransf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
  funcTransf (Id_rel (Id_functor _) (Id_functor _) ) (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_functor _)  (LeftAdjunc_functor)

| UnitAdjunc_Comp_conse_funcTransf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
      (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), forall A (X : functor A _), 
  funcTransf (Id_rel (Id_functor _) X ) (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_functor _)  (Subst_functor X (LeftAdjunc_functor))

| CoUnitAdjunc_Comp_antec_funcTransf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
  funcTransf (Id_rel (Id_functor _) (Id_functor _) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (RightAdjunc_functor) (Id_functor _)

| CoUnitAdjunc_Comp_conse_funcTransf' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
  funcTransf (Id_rel (Id_functor _) (RightAdjunc_functor) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Id_functor _) (Id_functor _)


| CoUnitAdjunc_Comp_antec_funcTransf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ),
forall A (X : functor A _),  
  funcTransf (Id_rel X (Id_functor _) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Subst_functor X (RightAdjunc_functor)) (Id_functor _)

| CoUnitAdjunc_Comp_antec_funcTransf'' : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ),
forall A (X : functor A _),   forall B (Y : functor B _), 
  funcTransf (Id_rel X Y ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Subst_functor X (RightAdjunc_functor)) Y

| CoUnitAdjunc_Comp_conse_funcTransf : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
forall A (X : functor A _), 
  funcTransf (Id_rel (Id_functor _) (Subst_functor X (RightAdjunc_functor)) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) (Id_functor _) X 

| CoUnitAdjunc_Comp_conse_funcTransf'' (* bad *) : forall (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor ), 
forall A (X : functor A C), forall B (Y : functor B D), 
  funcTransf (Id_rel X (Subst_functor Y (RightAdjunc_functor)) ) (Id_rel (LeftAdjunc_functor) (Id_functor _)) X Y .


(* eval/app dinaturality ; redex *)
Check fun  (C E D : Cat)  
(C' : Cat)   (F : functor C C') (S : rel C' D)
E' (E'E : functor E' E) (P : rel C E')
D' (D'D : functor D' D) (R : rel E D') C0 (C0C : functor C0 C) D0 (D0D' : functor D0 D')
(ff : funcTransf (Subst_rel P C0C (Id_functor _)) (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F) E'E ) 
E0 (E0E' : functor E0 E') 
P' (pp : funcTransf P' P C0C E0E') R' (rr : funcTransf R' R E'E D0D')  =>
( Tensor_antec_funcTransf'' pp rr (* todo in develop form, so one at a time *),
  (Imply_antec_app_funcTransf'' ff)  )
: funcTransf (Tensor_antec_rel' P' E0E' R') (Tensor_antec_rel' P E'E R) C0C D0D' *
funcTransf (Tensor_antec_rel' (Subst_rel P C0C (Id_functor E')) E'E
                (Subst_rel R (Id_functor E) D0D')) S (Subst_functor C0C F) (Subst_functor D0D' D'D) .

(* eval/app dinaturality ; contractum *)
Check fun  (C E D : Cat)  
(C' : Cat)   (F : functor C C') (S : rel C' D)
E' (E'E : functor E' E) (P : rel C E')
D' (D'D : functor D' D) (R : rel E D') C0 (C0C : functor C0 C) D0 (D0D' : functor D0 D')
(ff : funcTransf (Subst_rel P C0C (Id_functor _)) (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F ) E'E ) 
E0 (E0E' : functor E0 E') 
P' (pp : funcTransf P' P C0C E0E') R' (rr : funcTransf R' (Subst_rel R (Id_functor _) D0D') E'E (Id_functor _))  =>
fun (ff_restr (* becaus input is dependent pair (E0E', pp) ; this is first application of E0E' *)
 : funcTransf (Subst_rel P C0C E0E') (Imply_antec_rel' (Subst_rel R (Id_functor _) D0D') S (Subst_functor D0D' D'D)) (Subst_functor C0C F ) (Subst_functor E0E' E'E)) 
(tmp_compo_result_type:  funcTransf P'  (Imply_antec_rel' R' S
                          (Subst_functor (Id_functor D0)
                              (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))))   (Subst_functor C0C F) E0E') =>
( (Subst_funcTransf pp ff_restr (* input E0E' to restrict ff *) ),
 (Imply_antec_funcTransf''_bif' (Subst_functor D0D' D'D) (Id_funcTransf S  (Subst_functor C0C F ) (Id_functor _)) rr E0E' (* input E0E' to restrict rr *) (L:=E'E) ),
 Imply_antec_app_funcTransf'' tmp_compo_result_type )
: funcTransf P'
(Imply_antec_rel' (Subst_rel R (Id_functor E) D0D') S
   (Subst_functor D0D' D'D)) (Subst_functor C0C F)
(Subst_functor E0E' E'E) *
funcTransf (Imply_antec_rel'
   (Subst_rel (Subst_rel R (Id_functor E) D0D')
      (Subst_functor E0E' E'E) (Id_functor D0))
   (Subst_rel S (Subst_functor C0C F) (Id_functor D))
   (Subst_functor D0D' D'D))
(Imply_antec_rel' R' S
   (Subst_functor (Id_functor D0)
      (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))))
(Subst_functor C0C F) E0E' *
funcTransf (Tensor_antec_rel' P' E0E' R') S 
(Subst_functor C0C F)
(Subst_functor (Id_functor D0)
   (Subst_functor (Subst_functor D0D' D'D) (Id_functor D))).



(*** “1∘FX(h)” <∘ “1∘F(g)”  =                     “1∘F(h X<∘ g)”       *) (* OK *)
(*** “1∘F(h)” <∘ “1∘F(g)”  =                     “1∘F(h <∘ “1∘I(g)”)”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y X) M N)  P (K: functor P A) =>
( Id_antec_Comp_conse_funcTransf''  (Subst_functor X F) K N  (* 1∘FX *),
Id_antec_Comp_conse_funcTransf'' F (Subst_functor K X) (Subst_functor N X)   ,
Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' F X Y)) (Subst_functor K (Subst_functor X F)) )
:  funcTransf (Id_rel N K) (Id_rel (Subst_functor X F) (Id_functor E)) N (Subst_functor K (Subst_functor X F)) *
funcTransf (Id_rel (Subst_functor N X) (Subst_functor K X)) (Id_rel F (Id_functor E)) (Subst_functor N X) (Subst_functor (Subst_functor K X) F) *
funcTransf (Id_rel (Subst_functor N (Subst_functor X F)) (Subst_functor K (Subst_functor X F))) 
(Id_rel F (Id_functor E)) (Subst_functor M Y) (Subst_functor K (Subst_functor X F)).

(*** “1∘FX(h)” <∘ “1∘F(g)”                       = “1∘F(h X<∘ g)”       *) (* OK *)
(*** “1∘F(h)” <∘ “1∘F(g)”                       = “1∘F(h <∘ “1∘I(g)”)”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y (Subst_functor X (Id_functor _))) M N) P (K: functor P A) =>
( Comp_antec_funcTransf' g K  (* X<∘ *),
  Comp_antec_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) X Y)) (Subst_functor K X),
  Id_antec_Comp_conse_funcTransf'' F (Subst_functor K X) (Subst_functor M Y)  )
: funcTransf (Id_rel N K) (Id_rel Y (Subst_functor X (Id_functor C))) M K *
 funcTransf (Id_rel (Subst_functor N X) (Subst_functor K X))
(Id_rel (Id_functor C) (Id_functor C)) (Subst_functor M Y) (Subst_functor K X) *
funcTransf (Id_rel (Subst_functor M Y) (Subst_functor K X))
(Id_rel F (Id_functor E)) (Subst_functor M Y) (Subst_functor (Subst_functor K X) F).


(***   “1∘F(g)” ∘>F h =                     “1∘F”( “I∘1(g)” ∘> h )  *) (* OK *)
 Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y X) M N) P (K: functor P C) =>
Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' F X Y)) K
:  funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel F (Id_functor E)) K (Subst_functor N (Subst_functor X F)).

(*   “1∘F(g)” ∘>F h                    = “1∘F”( “I∘1(g)” ∘> h )  *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) A (X : functor A C)
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel Y (Subst_functor X (Id_functor _))) M N) P (K: functor P C) =>
( Comp_conse_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) X Y)) K,
  Id_antec_Comp_conse_funcTransf'' F (Subst_functor N X) K)
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel (Id_functor C) (Id_functor C)) K  (Subst_functor N X) *
funcTransf (Id_rel K (Subst_functor N X)) (Id_rel F (Id_functor E)) K (Subst_functor (Subst_functor N X) F).



(* todo: try  “1(g)∘G”  =  id(g)   then   “1(g)∘G” ∘>G “1∘F(h)” =   g ∘>GFY  ?  *)

(***   “1(g)∘G” ∘>G “1∘F(h)” =                    “1(“1(g)∘GF” ∘>GF h)∘G”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) E' (G : functor E E') A (X : functor A E')
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel  (Subst_functor (Subst_functor Y F) G) X) M N) P (K: functor P _) =>
(  Id_antec_Comp_conse_funcTransf'' F (Subst_functor M Y) K ,
Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' G (Subst_functor Y F) X)) (Subst_functor K F) )
: funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel F (Id_functor E)) K (Subst_functor (Subst_functor M Y) F) *
funcTransf (Id_rel (Subst_functor K F) (Subst_functor M (Subst_functor Y F)))
(Id_rel G (Id_functor E')) (Subst_functor K F)  (Subst_functor N X).

(***   “1(g)∘G” ∘>G “1∘F(h)”                      = “1(“1(g)∘GF” ∘>GF h)∘G”   *) (* OK *)
Check  fun (E C: Cat) (F : functor C E) E' (G : functor E E') A (X : functor A E')
A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
(g : transf (Id_rel  (Subst_functor Y (Subst_functor F G)) X) M N) P (K: functor P _) =>
( Comp_conse_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' (Subst_functor F G) Y X)) K ,
 Id_antec_Comp_antec_funcTransf'' G (Subst_functor K F) (Subst_functor N X) )
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel (Subst_functor F G) (Id_functor E')) K  (Subst_functor N X) *
funcTransf (Id_rel (Subst_functor (Subst_functor K F) G) (Subst_functor N X))
(Id_rel G (Id_functor E')) (Subst_functor K F)  (Subst_functor N X).





(*** “ϕ∘F(g)” ∘>F h =                “ϕ∘F(“I∘1(g)” ∘> h)” *)  (* OK *) (* instance included: “(“ϕ∘F”g)∘FY”h =                   “ϕ∘F”(“g∘Y”h) *)  
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A (X : functor A D)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N)  P (K: functor P C) =>
Comp_conse_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj Y X)) K
: funcTransf (Id_rel K (Subst_functor M Y))
(Id_rel LeftAdjunc_functor (Id_functor D)) K  (Subst_functor N X).

(* “ϕ∘F(g)” ∘>F h                 = “ϕ∘F(“I∘1(g)” ∘> h)” *)  (* OK *) 
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A (X : functor A D)
 A' A''  (M : functor A' A'') (N : functor A' A) (Y : functor A'' C)
 (g : transf (Id_rel Y (Subst_functor (Subst_functor X RightAdjunc_functor) (Id_functor _) )) M N)  P (K: functor P C) =>
( Comp_conse_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' (Id_functor _) (Subst_functor X RightAdjunc_functor) Y)) K ,
CoUnitAdjunc_Comp_conse_funcTransf'' adj K (Subst_functor N X) )
: funcTransf (Id_rel K (Subst_functor M Y)) (Id_rel (Id_functor C) (Id_functor C)) K (Subst_functor N (Subst_functor X RightAdjunc_functor)) *
funcTransf (Id_rel K (Subst_functor (Subst_functor N X) RightAdjunc_functor)) (Id_rel LeftAdjunc_functor (Id_functor D)) K (Subst_functor N X).


(*** alt: “ϕ∘F(g)” <∘ “1∘F(h)” =                “ϕ∘F( g <∘ “I∘1(h)” )” *)  (* OK *)
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A A' (X : functor A' C) (Y : functor A C)
 B (M : functor B A') (N : functor B A) 
 (h: transf (Id_rel X Y) M N  )  P (K: functor P D) =>
 ( CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor N Y) K ,
 Comp_antec_funcTransf' (App_transf h (Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor Y X)) K )
: funcTransf (Id_rel (Subst_functor N Y) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor N Y) K *
funcTransf (Id_rel (Subst_functor N (Subst_functor Y LeftAdjunc_functor)) K)
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M X) K .

(* alt: “ϕ∘F(g)” <∘ “1∘F(h)”                   = “ϕ∘F( g <∘ “I∘1(h)” )” *)  (* OK *)
Check fun  (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
 A A' (X : functor A' C) (Y : functor A C)
 B (M : functor B A') (N : functor B A) 
 (h: transf (Id_rel X (Subst_functor Y (Id_functor _))) M N  )  P (K: functor P D) =>
 ( Comp_antec_funcTransf' (App_transf h (Id_conse_Comp_conse_funcTransf'' (Id_functor _ ) Y X)) (Subst_functor K RightAdjunc_functor),
 CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor M X) K  )
: funcTransf (Id_rel (Subst_functor N Y) (Subst_functor K RightAdjunc_functor))
(Id_rel (Id_functor C) (Id_functor C)) (Subst_functor M X) (Subst_functor K RightAdjunc_functor) *
funcTransf (Id_rel (Subst_functor M X) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M X) K.



(*** h <∘ “ϕ∘F(g)” =                “ϕ∘F( h G<∘ “G∘1(g)” )” *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' C) A''  (M : functor A'' A') (N : functor A'' A)
(g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N) P (K: functor P D)  =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj Y X )) K
: funcTransf (Id_rel (Subst_functor N X) K)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor M Y) K.

                                     (*? old? todo: here subst exact matching only on cotravariant and conversion of subst on covariant*)
(* h <∘ “ϕ∘F(g)”                  = “ϕ∘F( h G<∘ “G∘1(g)” )” *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' C) A''  (M : functor A'' A') (N : functor A'' A)
(g : transf (Id_rel Y (Subst_functor X RightAdjunc_functor)) M N) P (K: functor P D)  =>
( Comp_antec_funcTransf' (App_transf g (Id_conse_Comp_conse_funcTransf'' RightAdjunc_functor X Y)) K ,
CoUnitAdjunc_Comp_conse_funcTransf'' adj (Subst_functor M Y) K )
: funcTransf (Id_rel (Subst_functor N X) K)
(Id_rel (Id_functor C) RightAdjunc_functor)  (Subst_functor M Y) K *
funcTransf (Id_rel (Subst_functor M Y) (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M Y) K .



(*** “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   *) (* OK *)
Check fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C) B (Y : functor B C) =>
(Comp_conse_funcTransf' (UnitAdjunc_transf adj X) Y,
CoUnitAdjunc_Comp_conse_funcTransf'' adj Y (Subst_functor X LeftAdjunc_functor)  )
: funcTransf (Id_rel Y X) (Id_rel (Id_functor C) RightAdjunc_functor) Y (Subst_functor X LeftAdjunc_functor) *
funcTransf (Id_rel Y (Subst_functor (Subst_functor X LeftAdjunc_functor) RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D)) Y (Subst_functor X LeftAdjunc_functor) .

(* “ϕ∘F(“γ∘(g)”)”             = “1∘F(g)”  *) (* OK *)
Check fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C) B (Y : functor B C) =>
Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor  X Y
: funcTransf (Id_rel Y X) (Id_rel LeftAdjunc_functor (Id_functor D)) Y (Subst_functor X LeftAdjunc_functor).


(*** “(f)∘ϕ” <∘ “1∘F(g)” =         f <∘ “ϕ∘F(g)” *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A D)
 A' (K : functor A' C) A'' (M : functor A'' A') (N : functor A'' A) 
 (g : transf (Id_rel K (Subst_functor X (RightAdjunc_functor))) M N ) B (Y : functor B D) =>
( CoUnitAdjunc_Comp_antec_funcTransf'' adj (Subst_functor N X) Y,
 Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_conse_funcTransf'' LeftAdjunc_functor (Subst_functor X RightAdjunc_functor) K)) Y )
: funcTransf (Id_rel (Subst_functor N X) Y)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor (Subst_functor N X) RightAdjunc_functor) Y *
funcTransf (Id_rel (Subst_functor N (Subst_functor (Subst_functor X RightAdjunc_functor) LeftAdjunc_functor)) Y)
(Id_rel LeftAdjunc_functor (Id_functor D))  (Subst_functor M K) Y .

(* “(f)∘ϕ” <∘ “1∘F(g)”             =  f <∘ “ϕ∘F(g)” *) (* OK *) 
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A D)
A' (K : functor A' C) A'' (M : functor A'' A') (N : functor A'' A) 
(g : transf (Id_rel K (Subst_functor X (RightAdjunc_functor))) M N ) B (Y : functor B D) =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_conse_funcTransf'' adj K X)) Y.


(*** “ϕ∘F(“G(f)∘γ”)”  =            id(f) *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D) (* A'' (M : functor A'' A') (N : functor A'' A) 
 (f : transf (Id_rel (Subst_functor X (LeftAdjunc_functor)) K) N M ) *) =>
( UnitAdjunc_Comp_antec_funcTransf'' adj X K,
 CoUnitAdjunc_Comp_conse_funcTransf'' adj X K )
:  funcTransf (Id_rel (Subst_functor X LeftAdjunc_functor) K)
(Id_rel (Id_functor C) RightAdjunc_functor) X K *
funcTransf (Id_rel X (Subst_functor K RightAdjunc_functor))
(Id_rel LeftAdjunc_functor (Id_functor D)) X K .

(* “ϕ∘F(“G(f)∘γ”)”             =  id(f) *) (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D)  =>
Id_funcTransf (Id_rel LeftAdjunc_functor (Id_functor D)) X K
: funcTransf (Subst_rel (Id_rel LeftAdjunc_functor (Id_functor D)) X K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K.


(*** h <∘ “(g)∘ϕ” =                   “(h <∘ g)∘ϕ”    *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' D) A''  (M : functor A'' A) (N : functor A'' A')
(g : transf (Id_rel X Y) M N) B (Z: functor B D)  =>
Comp_antec_funcTransf' (App_transf g (CoUnitAdjunc_Comp_antec_funcTransf'' adj X Y)) Z
: funcTransf (Id_rel (Subst_functor N Y) Z)
(Id_rel LeftAdjunc_functor (Id_functor D)) (Subst_functor M (Subst_functor X RightAdjunc_functor)) Z.

(* h <∘ “(g)∘ϕ”                      =  “(h <∘ “1(g)∘I”)∘ϕ”    *)  (* OK *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) (adj: adjunc LeftAdjunc_functor RightAdjunc_functor )
A (X : functor A D) A' (Y : functor A' D) A''  (M : functor A'' A) (N : functor A'' A')
(g : transf (Id_rel (Subst_functor X (Id_functor _)) Y) M N) B (Z: functor B D)  =>
( Comp_antec_funcTransf' (App_transf g (Id_antec_Comp_antec_funcTransf'' (Id_functor _) X Y)) Z ,
 CoUnitAdjunc_Comp_antec_funcTransf'' adj (Subst_functor M X) Z ).




(* todo: “I∘1(f)” = id(f)   ;  “1(f)∘I” = id(f)* ;  “1(f)∘F” = id(f)(? := ?) *)
Check  fun (C D: Cat) (LeftAdjunc_functor : functor C D) (RightAdjunc_functor : functor D C) 
(adj: adjunc LeftAdjunc_functor RightAdjunc_functor ) A (X : functor A C)
 A' (K : functor A' D)  =>
 ( Id_antec_Comp_antec_funcTransf'' LeftAdjunc_functor X K,
 Id_funcTransf (Id_rel LeftAdjunc_functor (Id_functor D)) X K   )
:  funcTransf (Id_rel (Subst_functor X LeftAdjunc_functor) K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K *
funcTransf (Subst_rel (Id_rel LeftAdjunc_functor (Id_functor D)) X K)
(Id_rel LeftAdjunc_functor (Id_functor D)) X K .


 
End Example.