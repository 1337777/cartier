(** # #
#+TITLE: cartierSolution9.v

Proph

https://gitee.com/OOO1337777/cartier/blob/master/cartierSolution9.v

solves half of some question of CARTIER which is how to program « parametrization modos » ( "parametrized object" , "dependent type" , "fibration with internal products" ) ...

SHORT ::

  The ends is to program some formulation/presentation of morphisms for any parametrization-functor ( "fibration" , "bifibration" ) which is such that this formulation enables the computational-logical introductions-eliminations correspondences and cut-elimination lemma when in the presence of pullback/substitution objects or sum/sigma objects or internal-product/pi objects . In other words , grammatical morphisms of the form [ A |- B ] over the span-cospan [ s o> /a o> p ] whose sensible transformation is some [ a* sigma_s A => p* B ] over [ Y' ] : (1) would introduce substitution-objects of the form [ A |- p* B ] over the span [ s o> /a o> 1 ] , (2) or would eliminate sigma-objects of the form [ sigma_s A |- B ] over the cospan [ 1 o> /a o> p ] , (3) or would introduce pi-objects of the form [ A |- pi_a p* B ] over the arrow [ s o> /1 o> 1 ] when the fibration has internal products ( which commute with substitutions around pullback-diagrams ) . In short : how to program the adjunction [ sigma_p a* -| pi_a p* ] ? Moreover such formulation may occur as some parametrized modified-colimiting modos of metafunctors over the total-space of some generating-fibration which hold viewing-data ...

A --------f-------> B
|                   |
.                   .
|                   | 
.                   .
|                   |
v                   v
X                   Y
|                   ^
|                   |
| s                 | p
|                   |
v                   |
X' <-------a------- Y'

HINTT :: for the internal product only , when [ s ] is identity : grammatical morphisms of the form [ A |- B ] over the cospan [ 1 o> /a o> p ] whose sense is some transformation [ a* A => p* B ] over Y' would correspond with grammatical morphisms of the form [ A |- pi_a p* B ] over the arrow [ 1 o> /1 o> 1 ] . And composition of grammatical morphisms holds the commutation of the internal products with substitutions around pullback-diagrams . And each section of the components-arrow [ /a ] for the internal product will give some projection morphism out of the internal product , and such projection morphism should be in polymorph-form by post-composition with some argument morphism .

#+BEGIN_SRC coq :exports both :results silent # # **)
