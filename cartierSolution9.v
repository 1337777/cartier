(** # #
#+TITLE: cartierSolution9.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution9.v

solves half of some question of CARTIER which is how to program grammatical polymorph « modos-over » ( "fibration with internal products" , "dependent types" ) ...

SHORT ::

  The ends is to show some formulation/presentation of morphisms for any fibration which is such that this formulation enables the introductions-eliminations correspondences when in the presence of sum/sigma objects and internal product/pi objects  : in other words , grammatical morphisms of the form ( A |- B ) over the span-cospan ( /p o> s o> /a o> q ) whose sense is some transformation ( a* sigma_s p* A => q* B  ) over W , would correspond with grammatical morphisms of the form  ( sigma_s p* A |- pi_a q* B  ) over the span-cospan 1_V , when the fibration has internal products ( which commute with the inverse image ) . Moreover such formulation will occur within some modified-colimiting modos of metafunctors over the total-space of the generating fibration ... In the end , such formulation would enable some computational cut-elimination lemma .

A --------f-------> B
|                   |
.                   .
|                   | 
.                   .
|                   |
v                   v
X                   Y
^                   ^
|                   |
| p                 | q
|                   |
|                   |
U ---s--> V <--a--- W

HINTT :: for the internal product only , when p and s are identity : grammatical morphisms of the form ( A |- B ) over the cospan ( /a o> q ) whose sense is some transformation ( a* A => q* B  ) over W , would correspond with grammatical morphisms of the form  ( A |- pi_a q* B  ) over the span-cospan 1_V . And composition of grammatical morphisms uses the commutation of the internal products which the inverse images . And each section of the reference-arrow [a] for the internal product will give some projection morphism out of the internal product .

#+BEGIN_SRC coq :exports both :results silent # # **)
