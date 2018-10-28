(** # #
#+TITLE: cartierSolution9.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution9.v

solves half of some question of CARTIER which is how to program grammatical polymorph « modos over » ( "fibration with internal products" , "dependent types" ) ...

SHORT ::

  The ends is to show some formulation/presentation of morphisms for any fibration which is such that this formulation enables the introductions-eliminations correspondences when in the presence of sum/sigma objects and internal product/pi objects  : in other words , for arrows (f0 : X -> Y , q1 : Y -> V , p1 : X -> U , f1 : U -> V ) in the base morphology and for objects (p0 : A -.-> X , q0 : B -.->Y) in the total morphology , then the morphisms of the form  ( p0 |-_f0* q0 ) above f0 would correspond with morphisms of the form ( sigma_p1 p0 |-_f1* pi_q1 q0 ) above f1 , when the fibration has internal products ( which commute with the inverse image functor ) . Moreover oneself may modify these colimits/sigma in the modos of metafunctors over the generating total-morphology ... In the end , such formulation would enable some computational cut-elimination lemma .

A --f---> B
|         |
.         .
| p0      | q0
.         .
|         |
v         v
X --f0--> Y
|         |
| p1      | q1
|         |
v         v
U --f1--> V

HINTT :: ( sigma_p1 p0 |-_f1* pi_q1 q0 ) above f1  <=>  ( sigma_p1 p0 |- f1* pi_q1 q0 ) above 1  <=>  ( p0 |- p1* f1* pi_q1 q0 ) above 1  <=>  ( p0 |- f0* q0 ) above 1  <=>  ( p0 |-_f0* q0 ) above f0 ; moreover given any section s1 of q1 , present some projection morphism above s1 outfrom the internal product along q1 .

#+BEGIN_SRC coq :exports both :results silent # # **)
