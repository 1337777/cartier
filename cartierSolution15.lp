/* https://github.com/1337777/cartier/blob/master/cartierSolution15.lp
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_polynomial_univalence.pdf

Kosta Dosen's univalent polynomial functorial programming

DRAFT OUTLINE:

on implementing Kosta Dosen's functorial programming with higher groupoidal symmetry (homotopy types, univalent higher categories) and with polynomial algebra (polynomial monads, databases, effects, and dynamics).

The basis for this implementation is the ideas and techniques from Kosta Dosen’s book « Cut-elimination in categories » (1999), which essentially is about the substructural logic of category theory, in particular how some good substructural formulation of the Yoneda lemma allows for computation and automatic-decidability of categorial equations.

Polynomials truly arise from the dualities in the many ways to store the data info of a category, i.e., the substructural logic of category theory, whereas Univalence is what would unify Voevodsky's homotopy type theory (symmetry) along Dosen's functorial programming.
*/

require open modos.cartierSolution13;

/* OUTLINE:
1. SECTION 1: POLYNOMIALS
2. SECTION 2: UNIVALENCE AND SYMMETRY
 */

// # SECTION 1 : POLYNOMIALS

// plain polynomials
constant symbol poly : Π (PB : Set), TYPE ;
constant symbol poly_Set : Π (PB: Set), Set ;
rule τ (@poly_Set $PB) ↪ @poly $PB;

constant symbol polyhom : Π [PB : Set], τ PB → Π (P : poly PB), TYPE ;
constant symbol polyhom_Set : Π [PB : Set], τ PB → Π (P : poly PB), Set ;
rule τ (@polyhom_Set $PB $b $P) ↪ @polyhom $PB $b $P;

symbol cat_set : cat → Set;
symbol cat_poly : Π A : cat, poly (cat_set A);
//todo: ...comonoid

// polynomial modules
constant symbol pmod_cov : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), TYPE ;
constant symbol pmod_cov_Set : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), Set ;
rule τ (@pmod_cov_Set $A $PA $B) ↪ @pmod_cov $A $PA $B;

constant symbol pmod_con : Π (A : cat) [B : cat] (PB : mod B Terminal_cat), TYPE ;
constant symbol pmod_con_Set : Π (A : cat) [B : cat] (PB : mod B Terminal_cat), Set ;
rule τ (@pmod_con_Set $A $B $PB) ↪ @pmod_con $A $B $PB;

constant symbol phom_cov : Π [I A B : cat] [PA : mod Terminal_cat A], Π [F : func I A], hom (Terminal_func I) PA F → Π (R : pmod_cov PA B), func I B → TYPE ;
constant symbol phom_cov_Set : Π [I A B : cat] [PA : mod Terminal_cat A], Π [F : func I A], hom (Terminal_func I) PA F → Π (R : pmod_cov PA B), func I B → Set ;
rule τ (@phom_cov_Set $I $A $B $PA $F $f $R $G) ↪ @phom_cov $I $A $B $PA $F $f $R $G;

constant symbol phom_con : Π [I A B : cat], Π [PB : mod B Terminal_cat], Π F : func I A, Π (R : pmod_con A PB),  Π [G : func I B], hom G PB (Terminal_func I) → TYPE ;
constant symbol phom_con_Set : Π [I A B : cat], Π [PB : mod B Terminal_cat], Π F : func I A, Π (R : pmod_con A PB),  Π [G : func I B], hom G PB (Terminal_func I) → Set ;
rule τ (@phom_cov_Set $I $A $B $PB $F $R $G $f) ↪ @phom_cov $I $A $B $PB $F $R $G $f;

constant symbol Unit_pmod_cov : Π [X A B : cat] [PX : mod Terminal_cat X]  [PA : mod Terminal_cat A] [F : func A X] (ff : transf PA Id_func PX F),
  Π [G : func B X] (g : hom (Terminal_func B) PX G), pmod_cov PA B;

constant  symbol ptransf_cov : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A], pmod_cov PA' B' → Π [F : func A' A] (f : transf PA' Id_func PA F), pmod_cov PA B → func B' B → TYPE ;

symbol ∘>>pmod_cov : Π [X B C: cat] [PX : mod Terminal_cat X] [PC : mod Terminal_cat C] [F : func C X] (f : transf PC Id_func PX F),  pmod_cov PX B → pmod_cov PC B;
notation ∘>>pmod_cov infix right 80;

// polynomial module actions

/* OK */ injective symbol _'∘>phom_cov : Π [I A B J : cat] [PA : mod Terminal_cat A] [R : pmod_cov PA B] [F : func I A] [f : hom (Terminal_func I) PA F] [G : func I B],
Π [M : func J A] [PJ : mod Terminal_cat J] (mm : transf PJ Id_func PA M), 
phom_cov f R G → ptransf_cov (Unit_pmod_cov mm f) (Id_transf PJ) (mm ∘>>pmod_cov R) G;

constant  symbol ptransf_phom_cov : Π [A' B' A B: cat] [PA : mod Terminal_cat A], mod A' B' → Π [F : func A' A] (f : hom (Terminal_func A') PA F), pmod_cov PA B → func B' B → TYPE ;

symbol pmod_cov<<∘ : Π [A X C: cat] [PA : mod Terminal_cat A], pmod_cov PA X → func C X → pmod_cov PA C;
notation pmod_cov<<∘ infix left 80; 

// polynomial module actions

/* OK */ injective symbol phom_cov∘>'_ : Π [I A B J : cat] [PA : mod Terminal_cat A] [R : pmod_cov PA B] [F : func I A] [f : hom (Terminal_func I) PA F] [G : func I B],
phom_cov f R G → Π (N: func J B), ptransf_phom_cov (Unit_mod G N) f (R pmod_cov<<∘ N) Id_func;

constant symbol ⇐pmod_cov : Π [B' B A : cat] (PB : mod B' B), Π [PA : mod Terminal_cat A], pmod_cov PA B → pmod_con B' (Op_mod PA);
notation ⇐pmod_cov infix left 60;

// tensor as prof  ... alt: PA as both cov and con, both cart and cocart arrows?
constant symbol ×pmod : Π [A B : cat] [PA : mod Terminal_cat A], pmod_con Terminal_cat (Op_mod PA) → pmod_cov PA B → mod Terminal_cat B;
notation ×pmod infix left 70;

//todo because this problem use projection func instead?... nope that not solve, not the problem
constant symbol ×pmod_hom  : Π [A B : cat] [PA : mod Terminal_cat A] [P : pmod_con Terminal_cat (Op_mod PA)] [Q : pmod_cov PA B]
[I] [F : func I A] [f : hom (Terminal_func I) PA F] [G : func I B],
phom_con (Terminal_func (Op_cat I)) P (Op_hom f) →  phom_cov f Q G → hom (Terminal_func I) (P ×pmod Q) G;

// symbol ×pmod_cov_rmod : Π [A B X : cat] [PA : rmod A], pmod_cov PA B → Π (PB : rmod B), rmod A;
// notation ×pmod_cov_rmod infix left 70;

constant symbol Proj_pmod_cov : Π [A: cat] (PA : mod Terminal_cat A), pmod_cov PA A; 
constant symbol Proj_pmod_cov_hom : Π [A I: cat] [PA : mod Terminal_cat A], Π [F : func I A], Π [G : func I A], hom F (Unit_mod Id_func Id_func) G → Π (f : hom (Terminal_func I) PA F), phom_cov f (Proj_pmod_cov PA) G; 


// polynomial module composition/substitution

constant symbol ◁pmod_cov : Π [A B X : cat] [PA : mod Terminal_cat A], Π (R : pmod_cov PA B), Π [PB : mod Terminal_cat B], Π (S : pmod_cov PB X),  
///ALT: pmod_cov ((PB ⇐pmod_cov R) ×pmod ((rmod_tfunc PA)∘>>mod_pmod_cov (Unit_mod Id_func Id_func))) X; 
pmod_cov ((PB ⇐pmod_cov R) ×pmod (Proj_pmod_cov PA)) X; 
notation ◁pmod_cov infix left 70;

//TODO: NOT FINISHED!! still exploring best ways to write all this
symbol ◁pmod_cov_hom : Π [A B X : cat] [PA : mod Terminal_cat A], Π (R : pmod_cov PA B), Π [PB : mod Terminal_cat B], Π (S : pmod_cov PB X), 
 Π [I] [F : func I A] [f : hom (Terminal_func I) PA F] [G : func I A]  (k : phom_con (Terminal_func _) (PB ⇐pmod_cov R) (Op_hom f))

 (a : phom_cov f (Proj_pmod_cov PA) G /* todo : hom F A G ? */),  Π [K : func I X], 
 Π [H : func I B], phom_cov f R H →
 Π [h : hom (Terminal_func I) PB H] /* todo = k' r ? so dependent pair */, phom_cov h S K →
 phom_cov (×pmod_hom k a) (R  ◁pmod_cov S) K;

// double category of polynomial modules with cofunctors as vertical arrows

constant symbol cofunc : Π (A B : cat), TYPE ;
constant symbol cofunc_Set : Π (A B : cat), Set ;
rule τ (@cofunc_Set $A $B) ↪ @cofunc $A $B ;

constant symbol Id_cofunc : Π (A : cat), cofunc A A ;

constant  symbol transf_cofunc : Π [A' A B' B: cat], mod A' B' → cofunc A' A → mod A B → cofunc B' B → TYPE ;

constant  symbol ptransf_cofunc_cov : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A], pmod_cov PA' B' → Π [F : cofunc A' A] (f : transf_cofunc PA' (Id_cofunc Terminal_cat) PA F), pmod_cov PA B → cofunc B' B → TYPE ;

// TODO: etc... experiment before cleaning up

// ----------------------------------------------------------------------------------

// # SECTION 2: UNIVALENCE AND SYMMETRY

// ## transport along equivalences

// TODO: very draft version, etc... experiment before cleaning up

constant symbol equiv : Π [A I : cat], func I A → func I A →  TYPE ;
constant symbol equiv_Set : Π [A I : cat], func I A → func I A → Set ;
rule τ (@equiv_Set $A $I $F $G) ↪ @equiv $A $I $F $G;

constant symbol equivfuncd : Π [X : cat] (A : catd X) (B : catd X), TYPE ;
constant symbol equivfuncd_Set : Π [X : cat] (A : catd X) (B : catd X), Set ;
rule τ (@equivfuncd_Set $X $A $B) ↪ (@equivfuncd $X $A $B);

constant symbol Equivfuncd_funcd : Π [X : cat] [A : catd X] [B : catd X], equivfuncd A B → funcd A Id_func B;
constant symbol Equivfuncd_inv_funcd : Π [X : cat] [A : catd X] [B : catd X], equivfuncd A B → funcd B Id_func A;
rule (Equivfuncd_funcd $F) ∘>d (Equivfuncd_inv_funcd $F) ↪ Id_funcd;
rule (Equivfuncd_inv_funcd $F) ∘>d (Equivfuncd_funcd $F) ↪ Id_funcd;

// aka isofibration transport
symbol Dependent_con_equivfuncd : Π [A J  : cat] [G : func J A] [JJ : catd J] [F : func J A] [AA : catd A],
Π (FF : funcd JJ F AA) (f : equiv G F), 
equivfuncd JJ (Fibre_catd AA G); // aka f*FF

constant symbol Equiv_hom : Π [A I: cat] [F : func I A] [G : func I A], equiv F G → hom Id_func (Unit_mod F Id_func) G;
constant symbol Equiv_inv_hom : Π [A I: cat] [F : func I A] [G : func I A], equiv F G → hom Id_func (Unit_mod G Id_func) F;
rule ((Equiv_hom $h) ∘>'_(_)) ∘' (Equiv_inv_hom $h) ↪ Func_con_hom _ _;
rule ((Equiv_inv_hom $h) ∘>'_(_)) ∘' (Equiv_hom $h) ↪ Func_con_hom _ _;

rule Fibration_con_funcd _ $FF (Equiv_hom $h) ↪ Equivfuncd_funcd (Dependent_con_equivfuncd $FF $h); 

// //TODO REVIEW
// constant symbol isEquiv : Π [A I: cat] [F : func I A] [G : func I A], hom Id_func (Unit_mod F Id_func) G → TYPE;
// constant symbol isEquiv_Inv : Π [A I: cat] [F : func I A] [G : func I A] (h : hom Id_func (Unit_mod F Id_func) G), isEquiv h → hom Id_func (Unit_mod G Id_func) F;
// ///WARNING: SLOW STUCK
// // rule ((@isEquiv_Inv $A $I $F $G $h _) ∘>'_(Id_func)) ∘' $h ↪ Func_con_hom $G Id_func;
// type @func;

// ## univalent universe

// universe univalence for equivalences;  refer also to universe univalence for general arrows
injective symbol Universe_Fibration_con_equivfuncd_inv : Π [X : cat] (F : func X Universe_con_cat) (G : func X Universe_con_cat), equivfuncd (Fibre_catd Universe_con_catd F)  (Fibre_catd Universe_con_catd G) 
→ equiv G F;

injective symbol Universe_Fibration_con_equivfuncd  [X : cat] [F : func X Universe_con_cat] [G : func X Universe_con_cat] (h : equiv G F) :
equivfuncd (Fibre_catd Universe_con_catd F) (Fibre_catd Universe_con_catd G) ≔ 
 Dependent_con_equivfuncd (Fibre_elim_funcd Universe_con_catd F) h;

rule Dependent_con_equivfuncd (Fibre_elim_funcd Universe_con_catd $F) (Universe_Fibration_con_equivfuncd_inv $F $G $HH) ↪ $HH;
rule (Universe_Fibration_con_equivfuncd_inv $F $G (@Dependent_con_equivfuncd _ _ $G _ _ _ (Fibre_elim_funcd Universe_con_catd $F) $h)) ↪ $h;


// ## univalent categories

constant symbol ∧ : Prop → Prop → Prop; // \wedge
notation ∧ infix left 7;
constant symbol ∧ᵢ p q : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ p q : π (p ∧ q) → π p;
symbol ∧ₑ₂ p q : π (p ∧ q) → π q;

constant symbol ∀ [a : Set] : (τ a → Prop) → Prop; notation ∀ quantifier;
rule π (∀ $p) ↪ Π x, π ($p x);
constant symbol ∃ [a : Set] : (τ a → Prop) → Prop; notation ∃ quantifier;
rule π (∃ $p) ↪ Π r, (Π x, π ($p x) → π r) → π r;

symbol hasEquiv  [A I: cat] [F : func I A] [G : func I A] 
 (f : hom Id_func (Unit_mod F Id_func) G) : Set ≔
 `sub_ g : hom Id_func (Unit_mod G Id_func) F,
  f ∘>'_(_) ∘' g = Func_con_hom _ _ ∧ 
  g ∘>'_(_) ∘' f = Func_con_hom _ _;

symbol hom_hasEquiv [A I: cat] (F : func I A) (G : func I A) : Set ≔
 `Σ_ f : hom Id_func (Unit_mod F Id_func) G, hasEquiv f;

symbol equiv_hom_hasEquiv : Π [A I: cat] [F : func I A] [G : func I A], equiv F G → τ (hom_hasEquiv F G)
≔ begin
assume A I F G h;
refine (Struct_sigma (Equiv_hom h) _ );
refine (Struct_sub (Equiv_inv_hom h) (∧ᵢ _ _ (eq_refl _) (eq_refl _)));
end;

symbol hasUnivalenceCat [A : cat] : Set ≔ 
`sub_ (s : τ `Π_ [I : cat], `Π_ [F : func I A], `Π_ [G : func I A], hom_hasEquiv F G →_ equiv_Set F G),
        (`∀ I : cat, `∀ F : func I A, `∀ G : func I A, `∀ h : equiv F G, (s _ _ _ (equiv_hom_hasEquiv  h) = h))
      ∧ (`∀ I : cat, `∀ F : func I A, `∀ G : func I A, `∀ h : τ (hom_hasEquiv F G), (equiv_hom_hasEquiv (s _ _ _ h)) = h) ;


// ## list category fibred over natural numbers category, and tail function as transport
constant symbol nat_cat : cat;
constant symbol Zero_inj_nat_func  : func Terminal_cat nat_cat;
// constant symbol Succ_inj_nat_func :  Π [I], func I nat_cat →  func I nat_cat;
constant symbol Succ_inj_nat_func :  func nat_cat nat_cat;
symbol case_nat_func [L0 : cat]
  (L0_zero : func Terminal_cat L0)
  (L0_succ : func L0 L0 ) :  func nat_cat L0;
// constant symbol Succ_inj_nat_hom  : Π [I] (F : func I nat_cat), hom Id_func (Unit_mod F Id_func) (Succ_inj_nat_func F);
constant symbol Succ_inj_nat_hom  : Π [I] (F : func I nat_cat), hom Id_func (Unit_mod F Id_func) (F ∘> Succ_inj_nat_func);
constant symbol list_catd : catd nat_cat;
constant symbol list_isFibration_con : isFibration_con list_catd;
constant symbol Nil_inj_list_funcd  : funcd (Terminal_catd _) Zero_inj_nat_func list_catd;
constant symbol Cons_inj_list_funcd : funcd list_catd Succ_inj_nat_func list_catd ;
// Π [I], func I nat_cat →  func I nat_cat;
// symbol case_nat_func [L0 : cat]
//   (L0_zero : func Terminal_cat L0)
//   (L0_succ : func L0 L0 ) :  func nat_cat L0;

type Fibration_con_funcd list_isFibration_con (Nil_inj_list_funcd ∘>d Cons_inj_list_funcd) (Succ_inj_nat_hom Zero_inj_nat_func);

type Fibration_con_funcd list_isFibration_con (Nil_inj_list_funcd ∘>d (Cons_inj_list_funcd ∘>d Cons_inj_list_funcd)) (Succ_inj_nat_hom (Zero_inj_nat_func ∘> Succ_inj_nat_func))
= (Fibre_intro_funcd list_catd (Zero_inj_nat_func ∘> Succ_inj_nat_func) Id_func (Nil_inj_list_funcd ∘>d Cons_inj_list_funcd));
