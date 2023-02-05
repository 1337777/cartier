/* TODO: these are unfinished prototypes for demo that it does work

https://github;com/1337777/cartier/blob/master/cartierSolution12;v (experiment file)
https://github;com/1337777/cartier/blob/master/cartierSolution12;lp (primary file; must use LambdaPi for modulo structural coherence)

In one line: the problem of contextual composition (cut elimination) and monoidal units (J-rule elimination) is solved by alternative formulations of adjunctions;

Context: There is now sufficient evidence (ref [6], [7]) that Kosta Dosen's ideas and techniques (ref [1], [2], [3], [4], [5]) could be implemented for proof-assistants, sheaves and applications; in particular cut-elimination, rewriting and confluence for various enriched, internal, indexed or double categories with adjunctions, monads, negation, quantifiers or additive biproducts; quantitative/quantum linear algebra semantics; presheaf/profunctor semantics; inductive-sheafification and sheaf semantics; sheaf cohomology and duality;;;

[1] Dosen-Petric: Cut Elimination in Categories 1999; 
[2] Proof-Theoretical Coherence 2004; 
[3] Proof-Net Categories 2005; 
[4] Coherence in Linear Predicate Logic 2007; 
[5] Coherence for closed categories with biproducts 2022
 */

 symbol Prop : TYPE;
 injective symbol Prf : Prop → TYPE;
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;

constant symbol Cat : TYPE;

inductive func: Π (C D : Cat), TYPE ≔
| Id_func : Π C : Cat, func C C

with hom: Π (C D : Cat), TYPE ≔
| Unit_hom : Π [C C' D' : Cat], func C' C → func D' C → hom C' D'
| Tensor_cov_hom : Π [A B C B' : Cat], hom C B → func B B' → hom B' A → hom C A
| Imply_cov_hom : Π [A C B C' : Cat], hom B C → func C' C → hom A C' → hom B A;

symbol Subst_func : Π [C D E: Cat], func C D → func D E → func C E;
symbol Subst_hom /* admissible */ : Π [C D C' D': Cat], hom C D → func C' C → func D' D → hom C' D' ;

rule  Subst_func $F (Subst_func $G $H)  ↪ Subst_func (Subst_func $F $G) $H  
with  Subst_func $F (Id_func _) ↪ $F
with  Subst_func  (Id_func _) $F ↪ $F;

rule Subst_hom (Unit_hom $F $G) $H $K ↪  Unit_hom (Subst_func $H $F) (Subst_func $K $G)
with Subst_hom (Tensor_cov_hom $R $H $S) $F $G ↪ Tensor_cov_hom (Subst_hom $R $F (Id_func _) ) $H (Subst_hom $S (Id_func _) $G) 
with Subst_hom (Imply_cov_hom $R $H $S) $F $G ↪  Imply_cov_hom (Subst_hom $R  $F (Id_func _)) $H (Subst_hom $S $G (Id_func _));

inductive adj : Π [C D: Cat], func C D → func D C → TYPE ≔

with transf: Π [C A B: Cat], hom A B → func C A → func C B → TYPE ≔

| Comp_transf /* admissible */ : Π [C D C' D' A : Cat] [R : hom C D] [F : func C C']
[S : hom C' D'] [G : func D D'] [M : func A C] [N : func A D],
transf R M N → morph R S F G → transf S (Subst_func M F) (Subst_func N G)

| Subst_transf /* admissible */ : Π [C A B D : Cat] [R : hom A B] [F : func C A] 
[G : func C B] (X : func D C),
transf R F G → transf R (Subst_func X F) (Subst_func X G)

| Id_transf : Π [E C D: Cat] (F : func C E) (X : func D C),
transf (Unit_hom (Id_func E) F) (Subst_func X F) X

| CoId_transf : Π [E C D : Cat] (F : func C E) (X : func D C),
transf (Unit_hom F (Id_func E)) X (Subst_func X F)

| UnitAdj_transf : Π [C D A : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
adj LAdj_func RAdj_func → Π X : func A C,
transf (Unit_hom (Id_func C) RAdj_func) X (Subst_func X LAdj_func)

| CoUnitAdj_transf : Π [C D A : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
adj LAdj_func RAdj_func → Π X : func A D,
transf (Unit_hom LAdj_func (Id_func D)) (Subst_func X RAdj_func) X

with morph: Π [C D C' D': Cat], hom C D → hom C' D' → func C C' → func D D' → TYPE ≔

| Comp_morph /* admissible */ : Π [C D C' D' C'' D'': Cat], Π [R : hom C D] [S : hom C' D'] [F : func C C'] [G : func D D']
 [T : hom C'' D''] [F' : func C C''] [G' : func D D''],
 morph R S F G → morph (Subst_hom S F G) T F' G' → morph R T F' G'

| Subst_morph /* admissible */ : Π [C D C' D' C'' D'' : Cat] [S : hom C' D'] [F' : func C' C'']
[T : hom C'' D''] [G' : func D' D''] (X : func C C') (Y : func D D'),
morph S T F' G' →
morph (Subst_hom S X Y) T (Subst_func X F') (Subst_func Y G')

| Id_morph : Π [C D C' D' : Cat] (R : hom C D) (F : func C' C) (G : func D' D),
morph (Subst_hom R F G) R F G

| UnitHom_cov_morph : Π [C A B B' : Cat] [F : func C A] [R : hom A B] [G : func C B],
transf R F G → Π K : func B' B, morph (Unit_hom G K) R F K

| UnitHom_con_morph : Π [C A B A' : Cat] [F : func C A] [R : hom A B] [G : func C B],
transf R F G → Π K : func A' A, morph (Unit_hom K F) R K G

| UnitHom_eval_cov_morph : Π [C D D' D0 C' : Cat] [H : func D D'] [R : hom C D] 
[F : func C C'] [T : hom C' D'],
morph R T F H → Π K : func D0 D',
morph (Tensor_cov_hom R H (Unit_hom (Id_func D') K)) T F K

| UnitHom_lam_cov_morph : Π [C D D0 C' D' : Cat] [H : func D D0] [R : hom C D] 
[T : hom C' D'] [F : func C C'] [G : func D D'],
morph (Tensor_cov_hom R H (Unit_hom (Id_func D0) H)) T F G →
morph R T F G

| Imply_eval_cov_morph : Π [C E D C' E' D' : Cat] [P : hom C E'] [R : hom E D'] 
[S : hom C' D] [E'E : func E' E] [F : func C C'] [D'D : func D' D],
morph P (Imply_cov_hom S D'D R) F E'E →
morph (Tensor_cov_hom P E'E R) S F D'D

| Imply_lam_cov_morph : Π [C E D C' E' D' : Cat] [P : hom C E'] [R : hom E D'] 
[S : hom C' D] [E'E : func E' E] [F : func C C'] [D'D : func D' D],
morph (Tensor_cov_hom P E'E R) S F D'D →
morph P (Imply_cov_hom S D'D R) F E'E

| Tensor_cov_morph : Π [D A C' C E E' A' : Cat] [S' : hom C' C] [R' : hom A A'] 
[S : hom D A] [R : hom E E'] [F : func C A] [G : func A E] [H : func C' D] [K : func A' E'],
morph S' S H F → morph R' R G K →
morph (Tensor_cov_hom S' F R') (Tensor_cov_hom S G R) H K

| Imply_cov_morph : Π [A A0 C0 B C' B' C'' C A1 : Cat] [S : hom B C'] 
[R' : hom A0 C0] [S' : hom B' C''] [R : hom A C] 
[L : func A A0] [H : func C C0] [G : func C' C''] [F : func B B'],
morph S S' F G → morph R R' L H →
Π (K : func C0 C') (M : func A1 A),
morph (Imply_cov_hom S K (Subst_hom R' (Subst_func M L) (Id_func C0)))
 (Imply_cov_hom S' (Subst_func H (Subst_func K G)) R) F M

/* from sol */

| CoId_UnitHom_cov_morph : Π [E C A A' : Cat] (F : func C E) (X : func A C) (Y : func A' E),
morph (Unit_hom (Subst_func X F) Y) (Unit_hom F (Id_func E)) X Y

| CoId_UnitHom_con_morph : Π [E C A A' : Cat] (F : func C E) (Y : func A' C) (X : func A C),
morph (Unit_hom Y X) (Unit_hom F (Id_func E)) Y (Subst_func X F)

| Id_UnitHom_con_morph : Π [E C A A' : Cat] (F : func C E) (Y : func A' E) (X : func A C),
morph (Unit_hom Y (Subst_func X F)) (Unit_hom (Id_func E) F) Y X

| UnitAdj_UnitHom_cov_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
adj LAdj_func RAdj_func → Π (X : func A C) (Y : func B D),
morph (Unit_hom (Subst_func X LAdj_func) Y) (Unit_hom (Id_func C) RAdj_func) X Y

| CoUnitAdj_UnitHom_cov_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
adj LAdj_func RAdj_func → Π (X : func A D) (Y : func B D),
morph (Unit_hom X Y) (Unit_hom LAdj_func (Id_func D)) (Subst_func X RAdj_func) Y

| CoUnitAdj_UnitHom_con_morph : Π [C D A B : Cat] [LAdj_func : func C D] [RAdj_func : func D C],
adj LAdj_func RAdj_func → Π (X : func A C) (Y : func B D),
morph (Unit_hom X (Subst_func Y RAdj_func)) (Unit_hom LAdj_func (Id_func D)) X Y;

/* eval/app dinaturality ; redex  */
type λ  (C E D : Cat)
(C' : Cat)   (F : func C C') (S : hom C' D)
E' (E'E : func E' E) (P : hom C E')
D' (D'D : func D' D) (R : hom E D') C0 (C0C : func C0 C) D0 (D0D' : func D0 D')
(ff : morph (Subst_hom P C0C (Id_func _)) (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F) E'E )
E0 (E0E' : func E0 E')
P' (pp : morph P' P C0C E0E') R' (rr : morph R' R E'E D0D') ,
Comp_morph (Tensor_cov_morph pp rr ) (Imply_eval_cov_morph ff);
/* : morph (Tensor_cov_hom P' E0E' R') S (Subst_func C0C F) (Subst_func D0D' D'D)  */

/* eval/app dinaturality ; contractum */
type λ  (C E D : Cat)
(C' : Cat)   (F : func C C') (S : hom C' D)
E' (E'E : func E' E) (P : hom C E')
D' (D'D : func D' D) (R : hom E D') C0 (C0C : func C0 C) D0 (D0D' : func D0 D')
(ff : morph (Subst_hom P C0C (Id_func _)) (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F ) E'E )
E0 (E0E' : func E0 E')
P' (pp : morph P' P C0C E0E') R' (rr : morph R' (Subst_hom R (Id_func _) D0D') E'E (Id_func _))
/* todo: rules for the subst on morphisms */
(ff_restr : morph (Subst_hom P C0C E0E') (Imply_cov_hom S (Subst_func D0D' D'D) (Subst_hom R (Id_func _) D0D')) (Subst_func C0C F ) (Subst_func E0E' E'E))
(tmp_compo_result_type:  morph P'  (Imply_cov_hom S
              (Subst_func (Id_func D0)
                  (Subst_func (Subst_func D0D' D'D) (Id_func D))) R')   (Subst_func C0C F) E0E'),
Imply_eval_cov_morph
(Comp_morph (Comp_morph pp ff_restr ) 
    (Imply_cov_morph  (Id_morph S  (Subst_func C0C F ) (Id_func _)) rr (Subst_func D0D' D'D) E0E' )) ;

/*  : morph (Tensor_cov_hom P' E0E' R') S (Subst_func C0C F) (Subst_func (Id_func D0) (Subst_func (Subst_func D0D' D'D) (Id_func D))) */



