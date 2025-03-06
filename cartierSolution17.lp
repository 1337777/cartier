/* https://github.com/1337777/cartier/blob/master/cartierSolution17.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_omega_categories.docx

Kosta Dosen simplicial-cubical homotopical functorial programming for omega-categories
  (A short description at the end of this file.)

cartierSolution13.lp : DOSEN'S FUNCTORIAL PROGRAMMING
cartierSolution14.lp : 1+2=3 VIA 3 METHODS: HIGHER DATA TYPE, ADJUNCTION, COLIMIT
cartierSolution15.lp : POLYNOMIAL FUNCTORS AND CATEGORIES AS POLYNOMIAL COMONOIDS
cartierSolution16.lp : COMPUTATIONAL LOGIC (CO-INDUCTIVE) INTERFACE FOR SHEAVES AND SCHEMES
cartierSolution17.lp : SIMPLICIAL-CUBICAL HOMOTOPICAL FUNCTORIAL PROGRAMMING FOR OMEGA-CATEGORIES

https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution14.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution15.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution16.lp 
https://github.com/1337777/cartier/blob/master/cartierSolution17.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.pdf 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.docx 

https://github.com/1337777/cartier/blob/master/Kosta_Dosen_2pages.pdf

OUTLINE OF cartierSolution17.lp :

# SIMPLICIAL-CUBICAL OMEGA-CATEGORIES
## DEPENDENT COMMA/ARROW-CATEGORY OF A DEPENDENT CATEGORY

# SITE TOPOLOGY (ADDENDUM TO cartierSolution16.lp)
## SITE TOPOLOGY FOR A CONCRETE SHEAFIFICATION

# COMMENTS

*/

require open modos.cartierSolution13;

verbose 10; 
flag "print_contexts" on; flag "print_domains" on; flag "print_meta_types" on; 
// flag "print_implicits" on; 
// debug +a; //debug +acdeghiklmoprsyuvxyz;
print coerce_rule; // /!\ BUG, DONT USE, ONLY CONSOLE print unif_rule;
// search "spine = (cartierSolution13.cat → cartierSolution13.cat) , hyp = cartierSolution13.cat";


/*****************************************
* # SIMPLICIAL-CUBICAL OMEGA-CATEGORIES
* ## DEPENDENT COMMA/ARROW-CATEGORY OF A DEPENDENT CATEGORY
******************************************/

constant symbol Commad_cov_catd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX) /*RR : funcd JJ R XX*/: 
catd (Context_cat XX);

constant symbol Commad_cov_elimBase_funcd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX) : 
funcd (Commad_cov_catd RR) (Context_elimCat_func XX) (Comma_cov_catd (Terminal_catd _) R);

// reminder: auxilliaty definition
constant symbol Comma_cov_functorial_funcd : Π [B' B A : cat] [S : mod A B'] [T : mod A B] [G : func B' B],
transf S Id_func T G → funcd (Comma_cov_catd (Terminal_catd _) S) G (Comma_cov_catd (Terminal_catd _) T) ;
constant symbol Comma_con_functorial_funcd : Π [A' B A : cat] [S : mod A' B] [T : mod A B] [F : func A' A],
transf S F T Id_func → funcd (Comma_con_catd S (Terminal_catd _)) F (Comma_con_catd T (Terminal_catd _)) ;

symbol Commad_cov_elimBase_functorial_funcd [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R A) [I] (F : func I (Context_cat (Commad_cov_catd RR))) : 
funcd (Comma_cov_catd (Terminal_catd _) (Unit_mod F Id_func) )
  (Context_intro_func (Commad_cov_elimBase_funcd RR ))
  (Comma_cov_catd (Terminal_catd _) (Unit_mod (F ∘> (Context_intro_func (Commad_cov_elimBase_funcd RR ))) Id_func) )

  ≔ Comma_cov_functorial_funcd ((F) _'∘> (Func_con_hom (Context_intro_func (Commad_cov_elimBase_funcd RR )) Id_func)) ;

constant symbol Commad_baseCov_catd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX): 
catd (Context_cat (Comma_cov_catd (Terminal_catd _) R));

constant symbol Commad_baseCov_elimCov_funcd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX): 
funcd (Commad_baseCov_catd RR) (Context_elimCat_func (Comma_cov_catd (Terminal_catd _) R)) XX;

symbol Commad_baseCov_elimCov_functorial_funcd [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R A) 
[I] (F : func I (Context_cat (Commad_baseCov_catd RR))) : 
funcd (Comma_cov_catd (Terminal_catd _) (Unit_mod F Id_func))
  (Context_intro_func (Commad_baseCov_elimCov_funcd RR ))
  (Comma_cov_catd (Terminal_catd _) (Unit_mod (F ∘> (Context_intro_func (Commad_baseCov_elimCov_funcd RR ))) Id_func))

  ≔ Comma_cov_functorial_funcd ((F) _'∘> (Func_con_hom (Context_intro_func (Commad_baseCov_elimCov_funcd RR )) Id_func)) ;


constant symbol Commad_baseCon_catd [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod X J] (RR : modd A R JJ) /*RR : funcd JJ R A*/: 
catd (Context_cat (Comma_con_catd R (Terminal_catd _)));
constant symbol Commad_baseCon_elimCon_funcd [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod X J] (RR : modd A R JJ): 
funcd (Commad_baseCon_catd RR) (Context_elimCat_func (Comma_con_catd R (Terminal_catd _))) A;


 // reminders:

 //ERRATA OF EARLIER cartierSolution13
//outer natural //NOTE: ERRATA OF EALIER CONFUSED Fibration_con_funcd BECAUSE NOW ALIGNS WITH MOD ACTION _'∘>
// CONSEQUENTLY: ALSO ERRATA Universe_Fibration_con_funcd
symbol Fibration_con_funcd : Π [I X X'  : cat] [x'x : func X X'] [H : func X I] [JJ : catd X] [F : func X' I] [II : catd I] (II_isf : isFibration_con II),
Π (FF : funcd JJ (x'x ∘> F) II) (f : hom H (Unit_mod Id_func F) x'x), 
funcd JJ H II; // aka f*FF
 //ERRATA OF EARLIER cartierSolution13
injective symbol Comma_con_elim_funcd : Π [I A J : cat] [F : func I A] [R : catd A] (R_isF : isFibration_con R),
Π (M : func J A), funcd (Terminal_catd _) F R → funcd (Comma_con_catd (Unit_mod M F) (Terminal_catd _)) M R; 
injective symbol Comma_cov_elim_funcd : Π [I A J : cat] [F : func I A] [R : catd A] (R_isF : isFibration_cov R),
Π (M : func J A), funcd (Terminal_catd _) F R → funcd (Comma_cov_catd (Terminal_catd _) (Unit_mod F M)) M R; 


// composition/action/transport
constant symbol Commad_cov_isFibration_cov [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R A): 
isFibration_cov (Commad_cov_catd RR);
constant symbol Commad_baseCov_isFibration_cov [X : cat] [A : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R A): 
isFibration_cov (Commad_baseCov_catd RR);

// witness of composition
// note:  [A] here could be a [Commad_cov_catd]
constant symbol Comma_cov_elim_witness_funcd [X : cat] [A : catd X] (A_isF : isFibration_cov A) [J : cat] [R : func J X] (RR : funcd (Terminal_catd _) R A) [I] (M : func I X) : 
funcd (Terminal_catd (Context_cat (Comma_cov_catd (Terminal_catd J) (Unit_mod R M))))
  (Context_intro_func (Comma_cov_elim_funcd A_isF M RR)) 
  (Commad_cov_catd (Unit_modd RR Id_funcd));

// stacking along base ( "horizontal composition along base arrow instead of point" )

injective symbol Product_catd : Π [X : cat] (U : catd X) (A : catd X), catd X;

constant symbol Commad_baseCov_stacking_funcd : Π [X : cat] [J : cat] [XX : catd X] [R : func J X]  (RR : funcd (Terminal_catd _) R XX)  [T S : func J X] (g : hom Id_func (Unit_mod R T) Id_func) (b : funcd (Terminal_catd _) S (Comma_cov_catd (Terminal_catd _) (Unit_mod R Id_func))),
(funcd (Terminal_catd _) (Context_intro_func b)
     (Product_catd (Commad_baseCov_catd (Unit_modd (Comma_con_intro_funcd (Terminal_catd J) ((Id_hom R ∘>'_ T) ∘' g)) Id_funcd))
                   (Commad_baseCov_catd (Unit_modd RR Id_funcd)))) →
(funcd (Terminal_catd _) 
 (Context_intro_func (Comma_cov_intro_funcd (Terminal_catd _) ( g '∘ ( R _'∘> Id_hom T) ))) (Commad_baseCov_catd (Unit_modd RR Id_funcd)));
//TODO: compute projection face

/*****************************************
* # SITE TOPOLOGY (ADDENDUM TO cartierSolution16.lp)
* ## SITE TOPOLOGY FOR A CONCRETE SHEAFIFICATION
******************************************/

/* Maclane-Moerdijk. Sheaves in geometry and logic.
Chapter V. Basic Constructions of Topoi
Section 1. Lawvere-Tierney Topologies
Theorem 2. Page 222. Every site topology J on a cate C defines a (propositional-level) sheafification/closure j on the presheaf topos C^op -> Set.
Section 4. Lawvere-Tierney Subsumes Grothendieck
Theorem 1. Page 233. Every (propositional-level) sheafification/closue j on the presheaf topos C^op -> Set defines a site topology J on a cate C.

  FUNDAMENTAL FORMULA OF CATEGORIAL TOPOLOGY:
    arrow f ∈ (sheafification-closure of sieve S)    ⟷    (pullback sieve of S along f) ∈ site-topology

  i.e. for all sieves S on an object F : C, for all arrows f in C with codomain F, then

    f ∈ j(S)    ⟷    f*(S) ∈ J
*/

require open modos.cartierSolution16;

constant symbol site_topology : Π [S : cat] (S_site : site S) [I] [F : func I S], 
  modd (Terminal_catd _) (Unit_mod Id_func F) (Terminal_catd _) → TYPE /*Prop*/;

constant symbol Maximal_site_topology : Π [S : cat] (S_site : site S) [I] [F : func I S],
  site_topology S_site (Terminal_modd (Unit_mod Id_func F));


constant symbol Ssieve_hom_site_topology : Π [S : cat] (S_site : site S) [I] [F : func I S][D] [K : func I D], Π (ff : hom F (sieve S D) K), 
Π [G : func I S] [f : hom G (Unit_mod Id_func F) Id_func /*TODO: gen x*/],
homd f (Fibre_elim_funcd _ G) (sieve_modd (ssieve_sieve S_site (ff '∘ sieve_ssieve S_site _))) (Fibre_elim_funcd _ Id_func)
→ site_topology S_site (sieve_modd (pullback_sieve ff f) );

constant symbol Site_topology_ssieve_homd : Π [S : cat] (S_site : site S) [I] [F : func I S][D] [K : func I D], Π (ff : hom F (sieve S D) K), 
Π [G : func I S] (f : hom G (Unit_mod Id_func F) Id_func /*TODO: gen x*/),
site_topology S_site (sieve_modd (pullback_sieve ff f))
→ homd f (Fibre_elim_funcd _ G) (sieve_modd (ssieve_sieve S_site (ff '∘ sieve_ssieve S_site _))) (Fibre_elim_funcd _ Id_func);


print coerce_rule; // /!\ BUG, DONT USE, ONLY CONSOLE print unif_rule;


// --------------------------------------------
// # COMMENTS
//


/*
Kosta Dosen simplicial-cubical homotopical functorial programming for omega-categories

    [draft] https://github.com/1337777/cartier/blob/master/cartierSolution17.lp 


CfP: Kosta Dosen simplicial-cubical functorial programming for sheaves and schemes (collocated at IWoAT 2025 @ Shenzhen)

    [draft] https://github.com/1337777/cartier/blob/master/cartierSolution17.lp

How do you program a proof-assistant language without using variables names? Answer: you use a “context-extension” operation (ref. “categories with families”, “comprehension categories”, etc.) which is internalized (reflected/computational/strictified) into the language itself. So that syntactically there is only “one” (compound/telescope) variable in the context.

How do you program a higher-dimensional omega-categories proof-assistant language without using arbitrary-long (infinite) number of meta-grammar entities for 1-arrows, 2-arrows, 3-arrows, etc. ? Answer: you use a “comma/arrow-category” operation, together with the “context-extension” (now rebranded as “total category”) operation, to internalize/reflect back the comma/arrow dependent-category (fibration) as a base-category. So that syntactically a 2-arrow is simply an arrow in the comma/arrow category.

To make things precise, not only there should be a comma dependent-category construction if given a base (ordinary) category as input, but also there should be a “dependent comma/arrow” dependent-category (fibration) construction if given a dependent-category (fibration) E → B as input. Now such a dependent comma/arrow dependent-category F would be dependent/fibred over two bases: as F → E over the total category E of the dependent-category E → B, and as F → "arrow"(B) over the comma/arrow category "arrow"(B) of the base-category B. But this is a problem because possibly new meta-grammar entities are needed for 1-fibrations, 2-fibrations (over 2 bases), 3-fibrations, etc. 

# Herbelin solution.

This is essentially the problem that the existing attempts to globular, simplicial, cubical (omega-category) homotopy fail to address explicitly. Their “solutions” simply bypass this mathematics question and try to express things directly, declaratively using variables names, even using the so-called “dimension variables” names (and a constraint/boundary “solver”), with intricate meta-recursions over the dimension, in a very computer-sciencey style. Here is a research article closest to the solution (without the fancy “dimension variables”):  

Hugo Herbelin; Ramkumar Ramachandra: “A parametricity-based formalization of semi-simplicial and semi-cubical sets”

This can be understood as an elaborate dependency/specification/constraint/boundary calculus, where a specification/dependency (“frame” for a “painting” of a cell) can be accumulated into telescopes of specifications, or can be finally discharged to specify/constraint a cell, and where a specification/dependency can be split as two sub-specifications (“restricted”) which are dispatched to the later “paintings” of cells.

So for a truncated cubical set D ∶ "cSetTrunc"_n representing a list X_0, X_1, ..., X_(n-1), of specified/dependent sets of cells, where X_(n-1) ∶ "frame"_(n-1,n-1)( X_0, X_1, ..., X_(n-2)) → "Set"  and where D".tl" = X_(n-1); and for a frame d ∶ "frame"_(n,p)(D) representing a list of layers which specify/constraint the boundaries of subsequent layers and cell, one has mutually recursive definitions:

"frame"_(n,p)(D) ≜ Σ d ∶ ( ...(Σ * ∶ "unit". "layer"_(n,0)(D)(*)) ...). "layer"_(n,p)(D)(d)
"painting"_(n,p)(D)(d) ≜ Σ l_p ∶ "layer"_(n,p)(D)(d). ( ...(Σ l_n ∶ "layer"_(n,n-1)(D)(d,l_p,...,l_(n-1)). D".tl" (d, l_p, ..., l_n)) ...)
"layer"_(n,p)(D)(d) ≜ "painting"_(n-1,p)(D".hd")("restrFrame"_("left",p)(d)) × "painting"_(n-1,p)(D".hd")("restrFrame"_("right",p)(d))

The problem with this solution is that each n-cell of the cubical set must be specified/“indexed” by a “fullframe” ( ≜ "frame"_(n,n) ), that is, by all of its (n-1)-dim faces; instead of just by the usual target face (with fixed source face parameter) except the remainder of the faces being sigma-packed as components of/with the cell which can be later projected out.

# Mathematics solution.

But there is an alternative elementary solution which makes uses of the mathematics/algebra within the problem: the functoriality of the comma/arrow construction, that is if E → B then "arrow"(E) → "arrow"(B), and the observation that it is sufficient that an arrow (a cell/volume) be “pre-specified/indexed” only by its source-and-target, while the other faces of the arrow become “post-projections/components” out of such a specified arrow. That is, one of the legs of the would-be 2-fibration, say the leg F → E, is regarded as an indexing e : E ↦ F(e) ∶ "Type" , while the other leg F → "arrow"(B) is regarded as an actual map/projection, indeed as a fibred map/projection from the fibration (F → E) to the fibration ("arrow"(B) → B) over the map/projection E → B. Also, there are versions where the roles of index or projection are switched between the legs of the 2-fibrations, and there are versions with contravariant fibrations and covariant fibrations.

Diagram 1 - composition at target: https://cutt.cx/fTL
Diagram 2 - composition at base: https://cutt.cx/WxRn
Diagram 3 - stacking along bases: https://cutt.cx/48RQ
Diagram 4 - cubical vs simplicial: https://cutt.cx/JqeNB

For example, for the 3-dimensional tetrahedra Τ:V where (V → F → E → B) which witnesses the composition of two 2-dimensional triangles, then one (front) face σ is the source parameter (a fixed external parameter, not really a variable index which acts, used to define the arrow/slice category V≔F(σ,-)), and one (diagonal) side face ξ : F is the target index used to pre-specify the volume T : F(σ,ξ), and one (right) side face τ ∶ "arrow"(E) is a direct projection (via V → "arrow"(E)) from T : V which had acted on the source face σ to output the composite target face ξ ≡ τ∘σ, and one (bottom) face τ' ∶ "arrow"("arrow"(B)) is a functorial/recursive projection from the volume T : V via the functoriality of the arrow construction V ≔ "arrow"(F) → "arrow"("arrow"(B)) applied to the earlier/inner projection F → "arrow"(B). More precisely:

constant symbol Commad_cov_catd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX): 
catd (Context_cat XX);

constant symbol Commad_cov_elimBase_funcd [X : cat] [XX : catd X] [J : cat] [JJ : catd J] [R : mod J X] (RR : modd JJ R XX): 
funcd (Commad_cov_catd RR) (Context_elimCat_func XX) (Comma_cov_catd R);

# Composition of cells

This action/composition/transport on a cell at its target or at its base are the more basic operations from which some of the usual operations are definable. For example, the whisker operation by a line is definable as the composition operation with a higher-dimensional composition-witness surface; and the simultaneous composition of multiple faces of an “open box” is defined by first factoring each extra face through a cartesian (composition-witness) face. The implementation of the “action/transport” for fibrations has an external formulation and an internalized formulation (via the comma/arrow category):

injective symbol Comma_cov_elim_funcd : Π [I A J : cat] [F : func I A] [R : catd A] (R_isF : isFibration_cov R), Π (M : func J A), funcd (Terminal_catd _) F R → funcd (Comma_cov_catd (Terminal_catd _) (Unit_mod F M)) M R;

constant symbol Comma_cov_elim_witness_funcd [X : cat] [A : catd X] (A_isF : isFibration_cov A) [J : cat] [R : func J X] (RR : funcd (Terminal_catd _) R A) [I] (M : func I X): 
funcd (Terminal_catd (Context_cat (Comma_cov_catd (Terminal_catd J) (Unit_mod R M))))
  (Context_intro_func (Comma_cov_elim_funcd A_isF M RR)) 
  (Commad_cov_catd (Unit_modd RR Id_funcd));

# Stacking of cells

Besides these (“vertical”) composition/action operations, there must be a new “stacking along base” operation which generalizes the usual horizontal composition of 2-cells where now the two 2-cells share a common base 1-cell instead of a 0-cell (p.s. these are “relative dimensions”). This is the preliminary implementation (whose ability to effectively compute has not yet been tested):

constant symbol Commad_baseCov_stacking_funcd : Π [X : cat] [J : cat] [XX : catd X] [R : func J X]  (RR : funcd (Terminal_catd _) R XX)  [T S : func J X] (g : hom Id_func (Unit_mod R T) Id_func) (b : funcd (Terminal_catd _) S (Comma_cov_catd (Unit_mod R Id_func))),
(funcd (Terminal_catd _) (Context_intro_func b)
  (Product_catd (Commad_baseCov_catd (Unit_modd (Comma_con_intro_funcd ((Id_hom R ∘>'_ T) ∘' g)) Id_funcd))
    (Commad_baseCov_catd (Unit_modd RR Id_funcd)))) →
(funcd (Terminal_catd _) (Context_intro_func (Comma_cov_intro_funcd ( g '∘ ( R _'∘> Id_hom T) ))) (Commad_baseCov_catd (Unit_modd RR Id_funcd)));


# Site topology and sheafification, revisited (Concrete examples).

Often concrete examples of such (omega-)categories are more laborious to express, than the general theory. To illustrate this idea, here is an errata about a missing definition of “site topology” in an earlier implementation about sheaves and schemes; such a “site topology” concept is the (only) way to generate a concrete sheafification operation (Lawvere-Tierney operation). Refer to Maclane-Moerdijk. “Sheaves in geometry and logic”. (Chapter V, Section 1, Theorem 2 and Section 4, Theorem 1): Every (propositional-level) sheafification/closure j on the presheaf topos C^op -> Set defines a site topology J on a category C.

  FUNDAMENTAL FORMULA OF CATEGORIAL TOPOLOGY:
    arrow f ∈ (sheafification-closure of sieve S)    ⟷    (pullback sieve of S along f) ∈ site-topology

  i.e. for all sieves S on an object F : C, for all arrows f in C with codomain F, then
    f ∈ j(S)    ⟷    f*(S) ∈ J

constant symbol site_topology : Π [S : cat] (S_site : site S) [I] [F : func I S], 
  modd (Terminal_catd _) (Unit_mod Id_func F) (Terminal_catd _) → TYPE;

  constant symbol Maximal_site_topology : Π [S : cat] (S_site : site S) [I] [F : func I S],
  site_topology S_site (Terminal_modd (Unit_mod Id_func F));

constant symbol Site_topology_ssieve_homd : Π [S : cat] (S_site : site S) [I] [F : func I S][D] [K : func I D], Π (ff : hom F (sieve S D) K), Π [G : func I S] (f : hom G (Unit_mod Id_func F) Id_func),
site_topology S_site (sieve_modd (pullback_sieve ff f))
→ homd f (Fibre_elim_funcd _ G) (sieve_modd (ssieve_sieve S_site (ff '∘ sieve_ssieve S_site _))) (Fibre_elim_funcd _ Id_func);


# References

[1]   Kosta Dosen; Zoran Petric. “Cut Elimination in Categories” (1999) 
[2]   Pierre Cartier.

*/
