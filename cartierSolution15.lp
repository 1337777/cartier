/* https://github.com/1337777/cartier/blob/master/cartierSolution15.lp
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_polynomial_univalence.pdf

Kosta Dosen's univalent polynomial functorial programming

DRAFT OUTLINE:

Kosta Dosen’s book « Cut-elimination in categories » (1999) is how some good substructural formulation of the Yoneda lemma, via profunctors, allows for computation and automatic-decidability of categorial equations. For example, the profunctor C[F-,_] is a distinct computer type than the hom-profunctor C[-,_] of the category C applied to outer objects of the form F- ...

This new stricter typing discipline is still successful to compute with polynomials (morphisms of polynomial-bicomodules along cofunctors of categories, substitution of polynomials, and their prafunctor semantics) via their underlying profunctors. It is conjectured that these computations can be extended to analytic functors and their automatic differentiation (via linear-logic's exponential comonad on the underlying profunctors) in reverse-mode (differential categories) for gradient-based neural-learning...

And now this updated implementation of fibred profunctors has a draft application to inductively-constructed covering sieves and sheaf topology: a sieve is a fibred profunctor dependent over the hom-profunctor; and the Yoneda action and lemma (gluing) still holds when the hom-profunctor (the total sieve) is replaced by any covering sieve and the presheaf is replaced by a sheaf.
*/

require open modos.cartierSolution13;


// OUTLINE
// # SECTION 1: POLYNOMIALS
// # SECTION 2: UNIVALENT CATEGORIES
// # SECTION 3: COVERING SIEVES

/// ----------- BEGIN PRELIMINARIES--------------------

// ---------------- BEGIN WARNING ------------
// THIS ATTEMPTED APPROACH TO ELEMENTS-CATEGORY BY DIRECT HAS BEEN CORRECTED 
// IN A LATER ERRATA FILE WHERE IT USES Context_cat CONTEXT-EXTENSION INSTEAD
// (TOGETHER WITH COMMA CATEGORY)
// BUT APPARENTLY THIS DIRECT APPROACH STILL WORKS AND IS LIGHTWEIGHT
// SO IT IS INTERESTING TO REMEMBER AND KEEP A COPY HERE FOR REFERENCE
// ----------------------

constant symbol Elements_cat : Π [B : cat] (R : mod Terminal_cat B), cat;
constant symbol Elements_proj_func : Π [B : cat] (R : mod Terminal_cat B),
func (Elements_cat R) B;
//todo : relax (Terminal_func I) to any x ?
constant symbol Elements_intro_func : Π [B I : cat] [R : mod Terminal_cat B]  [y : func I B] (r : hom (Terminal_func I) R y),
func I (Elements_cat R);
rule $F ∘> (@Elements_intro_func _ _ _ $y $r) ↪ (@Elements_intro_func _ _ _ ($F ∘> $y) ($r ∘↓ $F));

rule  (@Elements_intro_func _ _ _ $y $r ∘> Elements_proj_func _) ↪  $y;

constant symbol Elements_comp_func : Π [B I : cat] (R : mod Terminal_cat B) (G : func I B),
func (Elements_cat (R <<∘ G )) (Elements_cat R);

rule  (Elements_comp_func $R $G ∘> (Elements_proj_func _)) ↪ (Elements_proj_func ($R <<∘ $G)) ∘> $G;

//todo erase the less general Elements_intro_hom
constant symbol Elements_intro_hom : Π [B I : cat] [R : mod Terminal_cat B]  [y : func I B] (r : hom (Terminal_func I) R y),
Π [K] [y' : func K I] [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y' (Unit_mod y G) y'y) ,
hom y' (Unit_mod (Elements_intro_func r) (Elements_comp_func R G)) (Elements_intro_func( (r ∘>'_(G)) ∘' y'y_ ));

rule (Elements_intro_hom $r $y'y_) '∘ (_)_'∘> (Func_con_hom (Elements_proj_func $R) _) ↪ $y'y_ '∘ (_)_'∘> (Id_hom _);

/// ----------- END PRELIMINARIES--------------------

// polynomial modules
constant symbol poly : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), TYPE ;
constant symbol poly_Set : Π [A : cat] (PA : mod Terminal_cat A) (B : cat), Set ;
rule τ (@poly_Set $A $PA $B) ↪ @poly $A $PA $B;
// underlying profunctor of polynomial module
symbol poly_mod : Π [A : cat] [PA : mod Terminal_cat A] [B : cat], poly PA B → mod (Elements_cat PA) B;

// polynomial module substitution/composition ↘poly
// prafunctor semantics (non-internalized version) of substitution 
symbol ↘poly_base [A B : cat] [PA : mod Terminal_cat A] (R : poly PA B): 
      mod Terminal_cat B → mod Terminal_cat A
≔ λ PB, ((PB ⇐ (poly_mod R)) ⊗ (Unit_mod (Elements_proj_func PA) Id_func));
notation ↘poly_base infix left 70;
// substitution
constant symbol ↘poly : Π [A B X : cat] [PA : mod Terminal_cat A], Π (R : poly PA B), Π [PB : mod Terminal_cat B], Π (S : poly PB X),
poly (R ↘poly_base PB) X; 
notation ↘poly infix left 70;

constant symbol ↘poly_intro_hom : Π [A B C : cat] [PA : mod Terminal_cat A], Π (R : poly PA B),
Π [PB : mod Terminal_cat B], Π (S : poly PB C), 
Π [I] [F : func I A] [f : hom (Terminal_func I) PA F]   
(k : hom (Terminal_func I) (PB ⇐ ((Elements_intro_func f) ∘>> (poly_mod R)) ) Id_func)
[G : func I A] (a : hom (Elements_intro_func f) (Unit_mod (Elements_proj_func PA) Id_func) G) /* more relaxed/general than a : hom Id Unit(F,Id) G */,  
Π [K : func I C], Π [H : func I B] (r : hom Id_func ((Elements_intro_func f) ∘>> (poly_mod R)) H),
   hom Id_func (((Elements_intro_func ((Eval_cov_hom_transf k) ∘' r))) ∘>> (poly_mod S)) K →
hom (Elements_intro_func (Tensor_cov_hom_hom _ k a)) (poly_mod (R ↘poly S)) K;

/// -------------------------------

symbol cat_set : cat → Set;
constant symbol set_cat : Set → cat;
rule cat_set (set_cat $X) ↪ $X;

//memo: whether should distinct grammatical entry: func (set_cat _) _
symbol func_fun : Π [B : Set] [C: cat], func (set_cat B) C → (τ B → τ (cat_set C));
constant symbol fun_func : Π [B : Set] [C: cat], (τ B → τ (cat_set C)) → func (set_cat B) C;
rule func_fun (fun_func $F) ↪ $F;

constant symbol cofunc : Π (A B : cat), TYPE ;
constant symbol cofunc_Set : Π (A B : cat), Set ;
rule τ (@cofunc_Set $A $B) ↪ @cofunc $A $B ;

constant symbol Id_cofunc : Π [A : cat], cofunc A A ;
symbol ∘>c : Π [A B C: cat], cofunc A B → cofunc B C → cofunc A C;
notation ∘>c infix left 90;

rule $X ∘>c ($G ∘>c $H) ↪ ($X ∘>c $G) ∘>c $H
with $F ∘>c Id_cofunc ↪ $F
with Id_cofunc ∘>c $F ↪ $F;

symbol ∘>cb : Π [B C: cat] [I : Set], func (set_cat I) B → cofunc B C → func (set_cat I) C;
notation ∘>cb infix right 80;

rule @∘> (set_cat _) _ _ $X ($G ∘>cb $H) ↪ ($X ∘> $G) ∘>cb $H
with $F ∘>cb Id_cofunc ↪ $F
with $X ∘>cb ($F ∘>c $G) ↪ ($X ∘>cb $F) ∘>cb $G;

symbol cofunc_transp_func : Π [A B : cat] (M : cofunc A B) [I : Set] [F : func (set_cat I) B] 
[I' : Set] [X : func (set_cat I) (set_cat I')] (G : func (set_cat I') A),
hom X (Unit_mod (G ∘>cb M) Id_func) F → func (set_cat I) A;

rule (@cofunc_transp_func _ _ $M _ $F _ _ $G $h) ∘>cb $M  ↪  $F ;

constant symbol cofunc_transp :  Π [A B : cat] (M : cofunc A B) [I : Set] [F : func (set_cat I) B]
[I' : Set] [X : func (set_cat I) (set_cat I')] (G : func (set_cat I') A),
Π (h : hom X (Unit_mod (G ∘>cb M) Id_func) F),  
hom X (Unit_mod G Id_func) (cofunc_transp_func M G h);

rule (cofunc_transp_func $M (cofunc_transp_func $M $G $h) $h')
↪ (cofunc_transp_func $M $G (($h ∘>'_(_)) ∘' $h'));

assert [A B : cat] (M : cofunc A B) [I : Set] [F : func (set_cat I) B]
[I' : Set] [X : func (set_cat I) (set_cat I')] (G : func (set_cat I') A)
 (h : hom X (Unit_mod (G ∘>cb M) Id_func) F)
[I1] [X'] [F' : func (set_cat I1) B] (h' : hom X' (Unit_mod F Id_func) F') ⊢ eq_refl _ : π (
(cofunc_transp_func M (cofunc_transp_func M G h) h')
= (cofunc_transp_func M G ((h ∘>'_ Id_func) ∘' h')));

rule (cofunc_transp $M $G $h ∘>'_(_) ) ∘' (cofunc_transp $M /*DO NOT: (cofunc_transp_func $M $G $h)*/ _ $h')
↪ cofunc_transp $M $G ($h ∘>'_(_)  ∘' $h');

assert [A B : cat] (M : cofunc A B) [I : Set] [F : func (set_cat I) B]
[I' : Set] [X : func (set_cat I) (set_cat I')] (G : func (set_cat I') A)
 (h : hom X (Unit_mod (G ∘>cb M) Id_func) F)
 [I1] [X'] [F' : func (set_cat I1) B] (h' : hom X' (Unit_mod F Id_func) F') ⊢ eq_refl _ : π (
(cofunc_transp M G h ∘>'_(_) ) ∘' (cofunc_transp M (cofunc_transp_func M G h) h')
= cofunc_transp M G (h ∘>'_(_)  ∘' h'));

//memo: forward app
constant symbol cotransf_base : Π [A' A B' B: cat], mod A' B' → cofunc A' A → mod A B → cofunc B' B → TYPE ;
//memo: reverse app
constant symbol cotransf : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A], 
poly PA' B' → Π [F : cofunc A' A] (f : cotransf_base PA' Id_cofunc PA F), poly PA B → cofunc B' B → TYPE ;

//TODO update ealier file with this more general accumulation
rule $m '∘ ($M)_'∘> ($g '∘ $t)
↪ ($m '∘ ($M)_'∘> $g) '∘ ($M 1∘>> $t);
// alt: the other pointwide version necessary?
// rule ($M)_'∘> ($g '∘ $t)
// ↪ (($M)_'∘> $g) ''∘ ($M 1∘>> $t);
// assert [A B' B I : cat] [S : mod A B'] [T : mod A B]
// [X : func I A] [Y : func I B']  [G : func B' B]
// (h : hom X S Y) (t : transf S Id_func T G) [J] (M : func J A) ⊢ eq_refl _ : π (
// (M)_'∘> (h '∘ t)  = ((M)_'∘> h)  ''∘  (M 1∘>> t) ); //→ hom X T (G <∘ Y);
assert [A B' B I : cat] [S : mod A B'] [T : mod A B]
[X : func I A] [Y : func I B']  [G : func B' B]
(h : hom X S Y) (t : transf S Id_func T G) [J] (M : func J A)
 [J'] [K : func J' J] [L : func J' I] (m : hom K (Unit_mod M X) L) ⊢ eq_refl _ : π (
m '∘ (M)_'∘> (h '∘ t) = ( m '∘ (M)_'∘> h)  '∘  (M 1∘>> t) );

symbol '∘cb : Π [A B' B : cat] [I : Set] [S : mod A B'] [T : mod A B]
[X : func (set_cat I) A] [Y : func (set_cat I) B']  [G : cofunc B' B],
hom X S Y → cotransf_base S Id_cofunc T G → hom X T (Y ∘>cb G);
notation '∘cb infix right 80;

symbol ''∘cb [ B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
[Y : cofunc B'' B']  [G : cofunc B' B] :
cotransf_base R Id_cofunc S Y → cotransf_base S Id_cofunc T G →  cotransf_base R Id_cofunc T (Y ∘>c G);
notation ''∘cb infix right 80;

rule  $rs ''∘cb ($st ''∘cb $tu) ↪ ($rs ''∘cb $st) ''∘cb $tu;
rule  $r '∘cb ($rs ''∘cb $st)
↪ ($r '∘cb $rs) '∘cb $st;

symbol 1∘>>cb : Π [X Y Y' : cat] [G : cofunc Y Y'] [R' : mod X Y'] [R : mod X Y] [Z : cat] (H : func Z X) (r : cotransf_base R Id_cofunc R' G) , 
cotransf_base (H ∘>> R) Id_cofunc (H ∘>> R') G;
notation 1∘>>cb infix right 80;

rule Id_func 1∘>>cb  $t  ↪ $t 
with $K 1∘>>cb ($H 1∘>>cb $t) ↪ ($K ∘> $H) 1∘>>cb $t; 

rule @∘'  _ _ _ (set_cat _) _ _ _ _ _ ((@'∘cb _ _ _ _ _ _ _ $Y $G $h $t) ∘>'_(Id_func)) $k ↪
($h ∘>'_(Id_func) ∘' (cofunc_transp $G $Y $k)) '∘cb $t;

rule @∘↓ _ _ _ (set_cat _) _ _ _  ($a '∘cb $f)  $F  ↪ ($a ∘↓ $F) '∘cb $f;

assert [A B' B : cat] [I : Set] [S : mod A B'] [T : mod A B]
[X : func (set_cat I) A] [Y : func (set_cat I) B'] [G : cofunc B' B]
(h : hom X S Y) (t : cotransf_base S Id_cofunc T G) 
[J : Set] [K : func (set_cat J) (set_cat I)]  [L : func (set_cat J) B] (k : hom K (Unit_mod (Y ∘>cb G) Id_func) L) ⊢ eq_refl _ : π (
((h '∘cb t) ∘>'_(Id_func)) ∘' k =
(h ∘>'_(Id_func) ∘' (cofunc_transp G Y k)) '∘cb t );

//todo: as rule later
type λ [A B' B : cat] [I : Set] [S : mod A B'] [T : mod A B]
[X : func (set_cat I) A] [Y : func (set_cat I) B'] [G : cofunc B' B]
(h : hom X S Y) (t : cotransf_base S Id_cofunc T G) [J] (M : func J A)
[J'] [K : func (set_cat J') J] [L : func (set_cat J') (set_cat I)] (m : hom K (Unit_mod M X) L),
(m '∘ (M)_'∘>  (h '∘cb t)) 
 = (m '∘ (M)_'∘> h) '∘cb  (M 1∘>>cb t);

 symbol cotransf_transp : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
 [R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B], 
 cotransf R f S G → Π [I : Set]  [Y : func (set_cat I) A']  //conversions uses explicit Terminal_func
 (a : hom (Terminal_func (set_cat I)) PA' Y) (K: func (set_cat I) B'), 
 hom (Elements_intro_func (a '∘cb f)) (poly_mod S) (K ∘>cb G)
 → hom (Elements_intro_func a) (poly_mod R) K;

rule  (@cotransf_transp _ _ _ _ _ _ _ _ _ _ /*explicit $G bcause lost not shared*/ $G $ct _ _ $a $K $s ∘>'_(Id_func) )
       ∘' (@cofunc_transp _ _ $G _ _ _ $X1 $K $x)  
↪ (cotransf_transp $ct ($a ∘↓ $X1) (cofunc_transp_func $G $K $x) ($s ∘>'_(_)  ∘' $x))  ;

assert [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B] 
( ct : cotransf R f S G) [I : Set]  [Y : func (set_cat I) A'] 
(a : hom (Terminal_func (set_cat I)) PA' Y) (K: func (set_cat I) B')
(s : hom (Elements_intro_func (a '∘cb f)) (poly_mod S) (K ∘>cb G)) 
I2 (X1: func (set_cat I2) (set_cat I)) (X2: func (set_cat I2) B )
(x : hom X1 (Unit_mod (K ∘>cb G) Id_func) X2 )  ⊢ eq_refl _ : π (
 (cotransf_transp ct a K s ∘>'_(_) ) ∘' (@cofunc_transp _ _ G _ _ _ X1 K x)  
= (cotransf_transp ct (a ∘↓ X1) (cofunc_transp_func G K x) (s ∘>'_(_)  ∘' x))  );

symbol ''∘c : Π [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B]
[A0 B0 : cat] [PA0 : mod Terminal_cat A0]  [F0 : cofunc A A0] [f0 : cotransf_base PA Id_cofunc PA0 F0] [S0 : poly PA0 B0]  [G0 : cofunc B B0],  
cotransf R f S G →  cotransf S f0 S0 G0 → cotransf R (f ''∘cb f0) S0 (G ∘>c G0); 
notation ''∘c infix right 80;

rule cotransf_transp (@''∘c _ _ _ _ _ _ _ _ $f _ $G _ _ _ _ _ _ _  $ct $ct0) $a $K $s 
↪ cotransf_transp $ct $a $K  (cotransf_transp $ct0 ($a '∘cb $f) ($K ∘>cb $G) $s);

assert [A' B' A B: cat] [PA' : mod Terminal_cat A'] [PA : mod Terminal_cat A] 
[R : poly PA' B']  [F : cofunc A' A] [f : cotransf_base PA' Id_cofunc PA F] [S : poly PA B]  [G : cofunc B' B]
[A0 B0 : cat] [PA0 : mod Terminal_cat A0]  [F0 : cofunc A A0] [f0 : cotransf_base PA Id_cofunc PA0 F0] [S0 : poly PA0 B0]  [G0 : cofunc B B0]
(ct : cotransf R f S G) (ct0 : cotransf S f0 S0 G0)
[I : Set]  [Y : func (set_cat I) A'] 
(a : hom (Terminal_func (set_cat I)) PA' Y) (K: func (set_cat I) B')
(s : hom (Elements_intro_func (a '∘cb (f ''∘cb f0))) (poly_mod S0) (K ∘>cb (G ∘>c G0))) ⊢ eq_refl _ : π (
cotransf_transp (ct ''∘c ct0) a K s 
= cotransf_transp ct a K  (cotransf_transp ct0 (a '∘cb f) (K ∘>cb G) s) );
// : hom (Elements_intro_func a) (poly_mod R) K

/// -------------------------------

// GOAL: cat_poly is substitution-comonoid

constant symbol cat_mod : Π A : cat, mod Terminal_cat A;
constant symbol cat_mod_intro_hom : Π [A : cat] [I : Set] (F : func (set_cat I) A), 
  hom (Terminal_func _) (cat_mod A) F;

rule  @∘' _ _ _ (set_cat _) _ _ _ $Y _ ((cat_mod_intro_hom $F) ∘>'_(Id_func))  $h 
↪ (cat_mod_intro_hom $Y)  ;

assert [A : cat] [I : Set] (F : func (set_cat I) A) [J] [X : func (set_cat J) _] [Y] (h : hom X (Unit_mod F Id_func) Y) ⊢ eq_refl _ : π (
 (cat_mod_intro_hom F) ∘>'_(Id_func) ∘' h 
 = (cat_mod_intro_hom Y) ) ;

constant symbol cat_poly : Π A : cat, poly (cat_mod A) A;
rule poly_mod (cat_poly $A)
  ↪ Unit_mod (Elements_proj_func (cat_mod $A)) Id_func; 

constant symbol cat_comonoid_base : Π A : cat, cotransf_base (cat_mod A) Id_cofunc ((cat_poly A) ↘poly_base (cat_mod A)) Id_cofunc;
constant symbol cat_comonoid : Π A : cat, cotransf (cat_poly A) (cat_comonoid_base A) ((cat_poly A) ↘poly (cat_poly A)) Id_cofunc; 

rule (cat_mod_intro_hom $F) '∘cb (cat_comonoid_base $A)
↪ Tensor_cov_hom_hom (Elements_intro_func (cat_mod_intro_hom $F))
  (Lambda_cov_transf_hom ((cat_mod_intro_hom $F) ∘>'_(Id_func))) 
  (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F)));

assert [A : cat] [I : Set] [F : func (set_cat I) A] ⊢ eq_refl _ : π (
(cat_mod_intro_hom F) '∘cb (cat_comonoid_base A)
= Tensor_cov_hom_hom (Elements_intro_func (cat_mod_intro_hom F))
    (Lambda_cov_transf_hom ((cat_mod_intro_hom F) ∘>'_(Id_func))) 
    (Func_con_hom (Elements_proj_func (cat_mod A)) (Elements_intro_func (cat_mod_intro_hom F))));
// : hom (Terminal_func (set_cat I)) (cat_poly A ↘poly_base cat_mod A) F

rule cotransf_transp (cat_comonoid $A) (cat_mod_intro_hom $F) $K
  (↘poly_intro_hom (cat_poly $A) (cat_poly $A) 
    (Lambda_cov_transf_hom ((cat_mod_intro_hom $F) ∘>'_(Id_func))) 
    (Func_con_hom (Elements_proj_func (cat_mod $A)) (Elements_intro_func (cat_mod_intro_hom $F)))
    $r' $s') 
↪ (Func_con_hom _ _) ∘>'_(_) ∘' ($r' ∘>'_(_) ∘' $s');

assert  [A : cat] [I : Set] [F : func (set_cat I) A] [K: func (set_cat I) A] [H : func (set_cat I) A]
(r': hom Id_func (Elements_intro_func (cat_mod_intro_hom F) ∘>> poly_mod (cat_poly A)) H) 
(s' : hom Id_func ((Elements_intro_func (Eval_cov_hom_transf (Lambda_cov_transf_hom (cat_mod_intro_hom F ∘>'_ Id_func)) ∘' r')) ∘>> (poly_mod (cat_poly A))) K ) ⊢ eq_refl _ : π (
cotransf_transp (cat_comonoid A) (cat_mod_intro_hom F) K
  (↘poly_intro_hom (cat_poly A) (cat_poly A) 
      (Lambda_cov_transf_hom ((cat_mod_intro_hom F) ∘>'_(Id_func))) 
      (Func_con_hom (Elements_proj_func (cat_mod A)) (Elements_intro_func (cat_mod_intro_hom F)))
      r' s') 
= (Func_con_hom _ _) ∘>'_(_) ∘' (r' ∘>'_(_) ∘' s'));
// : hom (Elements_intro_func (cat_mod_intro_hom F)) (poly_mod (cat_poly A)) K


// ----------------------------------------------------------------------------------

// # SECTION 2: UNIVALENT CATEGORIES


  constant symbol == [a] : τ a → τ a → Set;
notation == infix 10;
constant symbol eeq_refl [a] (x:τ a) : τ (x == x);
constant symbol ind_eeq [a] [x y:τ a] : τ (x == y) → Π p, τ (p y) → τ (p x);

constant symbol core_cat : Π (A : cat) , cat;
rule cat_set (core_cat $C) ↪ cat_set $C;

constant symbol core_func : Π (A: cat), func (core_cat A) A;

constant symbol core_inv_hom: Π [A: cat]  [J] [X : func (set_cat J) (core_cat A)] [Y : func (set_cat J) (core_cat A)],
hom Id_func (Unit_mod X Id_func) Y →  hom Id_func (Unit_mod Y Id_func) X;
rule (($h) ∘>'_(_)) ∘' (core_inv_hom $h) ↪ Func_con_hom _ _;
rule ((core_inv_hom $h) ∘>'_(_)) ∘' ($h) ↪ Func_con_hom _ _;
//prop: prove also holds in whole A

symbol univalent_hom: Π [A: cat]  [J] [X : func (set_cat J) (core_cat A)] [Y : func (set_cat J) (core_cat A)],
hom Id_func (Unit_mod X Id_func) Y → τ ( func_fun X  == func_fun Y );
symbol eeq_iso'  [A : cat] [I : Set] (F : τ I → τ (cat_set A)) (G : τ I → τ (cat_set A)) :
τ ( F  == G ) → hom Id_func (Unit_mod (@fun_func _ (core_cat A) F) Id_func) (@fun_func _ (core_cat A) G) 
≔ λ e, ind_eeq e (λ F, hom_Set Id_func (Unit_mod (@fun_func _ (core_cat A) F) Id_func) (@fun_func _ (core_cat A) G) ) 
      (Func_con_hom  (@fun_func _ (core_cat A) G) Id_func) ; // (Π i : τ I, π ( F i = G i) ) ;

rule univalent_hom (eeq_iso' $F $G $e) ↪ $e;


// ----------------------------------------------------------------------------------

// ---------------- BEGIN WARNING ------------
// THIS ATTEMPTED APPROACH TO SIEVES, COVERING, SITES AND SHEAFIFICATION
// HAS BEEN CORRECTED IN A LATER ERRATA FILE WHERE IT USES sieve 
// SIEVES/SUBOBJECT CLASSIFIER INTERNALLY INSTEAD OF EXTENTIONAL ATTEMPT HERE
// BUT SOMETHING SIMILAR AS HERE SHOULD BE POSSIBLE
// SO IT IS INTERESTING TO REMEMBER AND KEEP A COPY HERE FOR REFERENCE
// ----------------------


// # SECTION 3: COVERING SIEVES

// / for sheave use transf from sigma/total_cat of modd covering ... nope... in fact depenent profunctors is precisely to allow
// to express dependent yoneda action with a choice of covering sieve profunctor dependent on hom-profunctor and
// when the module is a sheaf (trivially dependent) then can reverse yoneda action as a yoneda glue

constant symbol covering : Π [X : cat] (F : func Terminal_cat X), TYPE;

constant symbol covering_modd : Π [X : cat] [F : func Terminal_cat X], covering F → 
 modd (Terminal_catd X) (Unit_mod Id_func F) (Terminal_catd (Terminal_cat));
 constant symbol pullback_covering : Π [X : cat] [F : func Terminal_cat X], covering F → 
Π [G],  hom G (Unit_mod Id_func F) Id_func → covering G;

//todo generators
//constant symbol generators_covering : Π [X : cat] [F : func Terminal_cat X], /* ... covering_gen F  → */ covering F;

constant symbol pullback_covering_intro_homd : Π [X : cat] [F : func Terminal_cat X] (R : covering F)  ,
Π [G : func Terminal_cat X]  (h : hom G (Unit_mod Id_func F) Id_func)
[G' : func Terminal_cat X]  (h' : hom G' (Unit_mod Id_func G) Id_func),  
homd (h' '∘ (_)_'∘> h) (Funcs_funcd (Func_funcs G')) (covering_modd R) Id_funcd → 
homd h' (Funcs_funcd (Func_funcs G')) (covering_modd (pullback_covering R h)) Id_funcd ; 

constant symbol sum_covering : Π [X : cat] [F : func Terminal_cat X] (R : covering F)  ,
 (Π [G] [h : hom G (Unit_mod Id_func F) Id_func], 
 homd h (Funcs_funcd (Func_funcs G)) (covering_modd R) Id_funcd → covering G) 
 → covering F;
 
 constant symbol sum_covering_intro_homd : Π [X : cat] [F : func Terminal_cat X] (R : covering F)
(S_ : (Π [G] [h : hom G (Unit_mod Id_func F) Id_func], 
 homd h (Funcs_funcd (Func_funcs G)) (covering_modd R) Id_funcd → covering G) ),

 Π [G] [h : hom G (Unit_mod Id_func F) Id_func] 
 (r: homd h (Funcs_funcd (Func_funcs G)) (covering_modd R) Id_funcd),
 Π [G']  (h' : hom G' (Unit_mod Id_func G) Id_func),  
 homd h' (Funcs_funcd (Func_funcs G')) (covering_modd (S_ G h r)) Id_funcd →
  homd (h' '∘ (_)_'∘> h) (Funcs_funcd (Func_funcs G')) (covering_modd (sum_covering R S_)) Id_funcd  ;

constant symbol total_covering : Π [X : cat] (F : func Terminal_cat X), covering F;

//alt: convert its covering_modd as Unit_modd (Terminal_catd _)... 
constant symbol total_covering_intro_homd : Π [X : cat] [F : func Terminal_cat X], 
Π [G] (h : hom G (Unit_mod Id_func F) Id_func), 
homd h (Funcs_funcd (Func_funcs G)) (covering_modd (total_covering F)) Id_funcd ;

// memo should Total_cat only for catd Terminal_cat 

// second try
constant symbol covering2 : Π [X I: cat] [F : func I X] [A : catd X] [II] (FF : funcd II F A), TYPE;

constant symbol covering2_modd : Π [X I: cat] [F : func I X] [A : catd X] [II] [FF : funcd II F A], covering2 FF → 
Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), 
 modd JJ (Unit_mod M F) II;

// yoneda action can be reverted (yoneda glue) when RR is sheaf
symbol _'∘>yoneda2 : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
[A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
Π (S : covering2 FF), Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), 
homd r FF RR GG → transfd ((M)_'∘> r) (covering2_modd S MM) Id_funcd (MM ∘>>d RR) GG; 

/* typing not completed... */
constant symbol pullback_covering2 : Π [X I: cat] [F : func I X] [A : catd X] [II] [FF : funcd II F A], covering2 FF → 
Π [G : func I X]  [GG : funcd II G A] [x z] [h : hom G (Unit_mod x F) z] [xx zz] (hh : homd h GG (Unit_modd xx FF) zz),  covering2 GG;

constant symbol pullback_covering2_intro_homd : Π [X I: cat] [F : func I X] [A : catd X] [II] [FF : funcd II F A] (R : covering2 FF)  ,
Π [G : func I X]  [GG : funcd II G A] [x z] [h : hom G (Unit_mod x F) z] [xx zz] (hh : homd h GG (Unit_modd xx FF) zz)
[G' : func I X]  [GG' : funcd II G' A] [x' z'] [h' : hom G' (Unit_mod x' G) z'] [xx' zz'] (hh' : homd h' GG' (Unit_modd xx' GG) zz'),
homd (h' '∘ (_)_'∘> h) GG' (covering2_modd R (xx' ∘>d xx)) (zz' ∘>d zz) → 
homd h' GG' (covering2_modd (pullback_covering2 R hh) xx')  zz'; 



/// third try
// // V1
// constant symbol site : cat → TYPE ; 
// constant symbol site_Set : cat → Set; rule τ (site_Set $C) ↪ site $C;
// constant symbol sieves : Π [S : cat] (S_site : site S), mod S Terminal_cat;
//     // constant (constructor), not defined symbol, no rewrites from it... especially because of sum_sieve...
//   constant symbol sieve_mod : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π (ff : hom F (sieves S_site) Id_func), mod S Terminal_cat;
//   // sieve as subfunctor ... as fibration instead? or as prof (in groupoids) over elements-cat of base? (because of intersection operation)
//   constant symbol sieve_transf : Π [S : cat] [S_site : site S] [F : func Terminal_cat S],
//   Π (ff : hom F (sieves S_site) Id_func), transf (sieve_mod ff) Id_func (Unit_mod Id_func F) Id_func;


//   // max sieve
//   constant  symbol maximal_sieve : Π [S : cat] (S_site : site S) (F : func Terminal_cat S), hom F (sieves S_site) Id_func;

//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
//   (g '∘ (_)_'∘> (maximal_sieve S_site F))
//   = (maximal_sieve S_site G);
//   rule   (@'∘ _ _ _ _  _ _ _ Id_func _ $g  ((Id_func)_'∘> (maximal_sieve $S_site $F)))
//   ↪ (maximal_sieve $S_site _);

 
//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (sieve_mod ff) Id_func),
//   (g '∘ (sieve_transf ff)) '∘ (_)_'∘> ff
//   = (maximal_sieve S_site G);

// rule   (@'∘ _ _ _ _  _ _ _ Id_func _  $g (sieve_transf $ff)) '∘ (_)_'∘> $ff
// ↪ (maximal_sieve _ _);

// // elements of max sieve
// constant symbol maximal_sieve_hom : Π [S : cat] (S_site : site S) [F : func Terminal_cat S]
// [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
//   hom G (sieve_mod (maximal_sieve S_site F)) Id_func;
// type  λ [S : cat] (S_site : site S) [F : func Terminal_cat S]
// [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
// (maximal_sieve_hom S_site g)  '∘ (sieve_transf (maximal_sieve S_site F))
// = g;
// rule (maximal_sieve_hom $S_site $g)  '∘ (sieve_transf (maximal_sieve $S_site $F))
// ↪ $g;

//    // pullback of sieve, defined symbol
//   symbol pullback_sieve  [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func)
//   :  hom G (Id_func ∘>> sieves S_site) Id_func
//   ≔ (g '∘ (_)_'∘> ff);

//    /// no constructor of elements of pullback sieve, only projection out of elements
//   constant symbol pullback_sieve_proj_transf : Π [S : cat] [S_site : site S] [F : func Terminal_cat S],
//   Π (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
//   transf (sieve_mod (pullback_sieve ff g)) Id_func (sieve_mod ff) Id_func;

//   rule ($h '∘ (pullback_sieve_proj_transf $ff $g)) '∘ (sieve_transf $ff)
//   ↪ ($h '∘ (sieve_transf (pullback_sieve $ff $g))) '∘ (_)_'∘> $g ;

//   assert [S : cat] [S_site : site S] [F : func Terminal_cat S]
//    (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func)
//   [H : func Terminal_cat S] (h : hom H (sieve_mod (pullback_sieve ff g)) Id_func) ⊢
//   (h '∘ (pullback_sieve_proj_transf ff g)) '∘ (sieve_transf ff)
//   ≡ (h '∘ (sieve_transf (g '∘ (_)_'∘> ff))) '∘ (_)_'∘> g ;

 
//  // intersection sieve, todo? via product of presheaves
//  constant symbol intersection_sieve :Π [S : cat] [S_site : site S] [F : func Terminal_cat S]
//  (ff ff' : hom F (sieves S_site) Id_func), hom F (sieves S_site) Id_func; 
//  // sum of sieve

//   constant symbol sum_sieve : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π [ff : hom F (sieves S_site) Id_func], transf (sieve_mod ff) Id_func (sieves S_site) Id_func
//   → hom F (sieves S_site) (Terminal_func _);

//   constant symbol sum_sieve_hom : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π (ff : hom F (sieves S_site) Id_func) (T_ : transf (sieve_mod ff) Id_func (sieves S_site) Id_func),
//   Π [G : func Terminal_cat S]
//   (f : hom G (sieve_mod ff) (Terminal_func _)) [ H : func Terminal_cat S](g : hom H (sieve_mod (f '∘ T_)) (Terminal_func _)),  //   (g : hom H (f '∘ sieve_transf ff) (Terminal_func _))  ;
//    hom H (sieve_mod (sum_sieve T_)) (Terminal_func _);

//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   λ [ff : hom F (sieves S_site) Id_func] (T_ : transf (sieve_mod ff) Id_func (sieves S_site) Id_func),
//   λ [G : func Terminal_cat S]
//    (f : hom G (sieve_mod ff) (Terminal_func _)) [ H : func Terminal_cat S](g : hom H (sieve_mod (f '∘ T_)) (Terminal_func _)), 
// (g '∘ (sieve_transf (f '∘ T_))) '∘ (_)_'∘> (f '∘ (sieve_transf ff))
//  = (sum_sieve_hom ff T_ f g) '∘ (sieve_transf (sum_sieve T_));

//  rule (sum_sieve_hom $ff $T_ $f $g) '∘ (sieve_transf (sum_sieve $T_))
// ↪ ($g '∘ (sieve_transf ($f '∘ $T_))) '∘ (_)_'∘> ($f '∘ (sieve_transf $ff)) ;
// //hom H (Id_func ∘>> Unit_mod Id_func F) ((Id_func <∘ Terminal_func Terminal_cat) <∘ (Id_func <∘ Terminal_func Terminal_cat))

// /// for testing: all sites are ringed... and no modular API interface for rings, ring-modules, ...
// constant symbol ringed : Π [S : cat] (S_site : site S), mod S Terminal_cat;
// symbol ringed_mult : Π [S : cat] [S_site : site S] [G : func Terminal_cat S] //todo? via product of presheaves
//   (g g' : hom G (ringed S_site) Id_func), hom G (ringed S_site) Id_func;

// // ringed_locally is similar as some general D(f) ... 
// // outputs sieve where the function is invertible (for affine is singleton sieve on primitive Zarisky D(r) affineScheme_func below)
// constant symbol ringed_locally : Π [S : cat] (S_site : site S),
//   transf (ringed S_site) Id_func (sieves S_site) Id_func; 

// /// for testing: ...
// constant symbol ring : TYPE ; 
// constant symbol ring_type: ring → TYPE;
// constant symbol ring_mult : Π [R : ring] (r s : ring_type R), ring_type R;

// //todo? via concrete cat instead?  (because must use Terminal_cat ?)
// constant symbol affineScheme_cat : Π (R : ring), cat;
// constant symbol affineScheme_site : Π (R : ring), site (affineScheme_cat R);
//  // primitive Zarisky  D(r)... for affine ringed_locally is singleton sieve on this 
// constant symbol affineScheme_func : Π [R : ring] (r : ring_type R), func Terminal_cat (affineScheme_cat R);
// constant symbol affineScheme_hom : Π [R : ring] (r s: ring_type R), 
//  hom (affineScheme_func (ring_mult s r)) (Unit_mod Id_func (affineScheme_func r)) Id_func;


//  constant  symbol isCovering : Π [S : cat] (S_site : site S),
//  transf (sieves S_site) Id_func (sieves S_site) Id_func;

//  type λ [S : cat] (S_site : site S), 
//   (isCovering S_site) ''∘ (isCovering S_site) 
//   = isCovering S_site;

// type λ [S : cat] (S_site : site S) (F : func Terminal_cat S),
// (maximal_sieve S_site F) '∘ (isCovering S_site) 
// = (maximal_sieve S_site F);


//V2

// constant symbol Elements_con_cat : Π [B : cat] (R : mod B Terminal_cat), cat;
// constant symbol Elements_con_proj_func : Π [B : cat] (R : mod B Terminal_cat),
// func (Elements_con_cat R) B;
// //todo : relax (Terminal_func I) to any x ?
// constant symbol Elements_con_intro_func : Π [B I : cat] [R : mod B Terminal_cat]  [y : func I B] (r : hom y R (Terminal_func I)),
// func I (Elements_con_cat R);
// rule $F ∘> (@Elements_con_intro_func _ _ _ $y $r) ↪ (@Elements_con_intro_func _ _ _ ($F ∘> $y) ($r ∘↓ $F));

// rule  (@Elements_con_intro_func _ _ _ $y $r ∘> Elements_con_proj_func _) ↪  $y;

// constant symbol Elements_con_comp_func : Π [B I : cat] (R : mod B Terminal_cat) (G : func I B),
// func (Elements_con_cat (G ∘>> R)) (Elements_con_cat R);

// rule  (Elements_con_comp_func $R $G ∘> (Elements_con_proj_func _)) ↪ (Elements_con_proj_func ($G ∘>> $R)) ∘> $G;

// //todo erase the less general Elements_con_intro_hom
// constant symbol Elements_con_intro_hom : Π [B I : cat] [R : mod B Terminal_cat]  [y : func I B] (r : hom y R (Terminal_func I)),
// Π [K] [y' : func K I] [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y'y (Unit_mod G y) y') ,
// hom (Elements_con_intro_func( y'y_ '∘  ((G)_'∘> r)  )) (Unit_mod (Elements_con_comp_func R G) (Elements_con_intro_func r)) y';

// rule (Func_cov_hom (Elements_con_proj_func $R) _) ∘>'_(_) ∘'  (Elements_con_intro_hom $r $y'y_) ↪ (Id_hom _) ∘>'_(_) ∘' $y'y_ ;

// ////another instance of yoneda is by precompose yoneda with Elements_con_proj_transf
// constant symbol Elements_con_proj_transf : Π [B  : cat] [R : mod B Terminal_cat]  (E : mod (Elements_con_cat R) Terminal_cat),
// transf E (Elements_con_proj_func R) R Id_func;
// constant symbol Elements_con_proj_transf' : Π [B  : cat] [R : mod B Terminal_cat]  (E : mod (Elements_con_cat R) Terminal_cat) [I] (G : func I B),
// transf ((Elements_con_comp_func R G) ∘>> E) (Elements_con_proj_func (G ∘>> R)) (G ∘>> R) Id_func;

// // 
// symbol Elements_con_functorial_func : Π [B : cat] [R R' : mod B Terminal_cat] 
// (t : transf R Id_func R' Id_func) ,
//  func (Elements_con_cat R) (Elements_con_cat R');

// rule (Elements_con_intro_func ($g_)) ∘> Elements_con_functorial_func $t
//   ↪ (Elements_con_intro_func ($g_ '∘ $t) );

// constant symbol site : cat → TYPE ; 
// constant symbol site_Set : cat → Set; rule τ (site_Set $C) ↪ site $C;
// constant symbol sieves : Π [S : cat] (S_site : site S), mod S Terminal_cat;
//     // constant (constructor), not defined symbol, no rewrites from it... especially because of sum_sieve...
//   constant symbol sieve_mod : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π (ff : hom F (sieves S_site) (Terminal_func _)), mod (Elements_con_cat (Unit_mod Id_func F)) Terminal_cat;
//   // sieve as subfunctor ... as fibration instead? or as prof (in groupoids) over elements-cat of base? (because of intersection operation)
//   // constant symbol sieve_transf : Π [S : cat] [S_site : site S] [F : func Terminal_cat S],
//   // Π (ff : hom F (sieves S_site) Id_func), transf (sieve_mod ff) Id_func (Unit_mod Id_func F) Id_func;

// //when R will be sheaf
// symbol gluing_when_covering_and_sheaves : Π [A  : cat] [A_site : site A] [F : func Terminal_cat A] [R : mod A Terminal_cat] 
// (ff : hom F (sieves A_site) (Terminal_func _)),
// transf ( sieve_mod ff) (Elements_con_proj_func _) ( R) Id_func →  hom F R Id_func  ;


//   // max sieve
//   constant  symbol maximal_sieve : Π [S : cat] (S_site : site S) (F : func Terminal_cat S), hom F (sieves S_site) (Terminal_func _);

//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
//   (g '∘ (_)_'∘> (maximal_sieve S_site F))
//   = (maximal_sieve S_site G);
//   rule   (@'∘ _ _ _ Terminal_cat  _ _ _ (Terminal_func _) _ $g  ((Id_func)_'∘> (maximal_sieve $S_site $F)))
//   ↪ (maximal_sieve $S_site _);

 
//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] 
//   (g_ : hom G (Unit_mod Id_func F) Id_func) (g : hom (Elements_con_intro_func g_) (sieve_mod ff) (Terminal_func _)),
//   (g_ ) '∘ (_)_'∘> ff
//   = (maximal_sieve S_site G);

// // rule   (@'∘ _ _ _ _  _ _ _ Id_func _  $g (sieve_transf $ff)) '∘ (_)_'∘> $ff
// // ↪ (maximal_sieve _ _);

// // // elements of max sieve
// constant symbol maximal_sieve_hom : Π [S : cat] (S_site : site S) [F : func Terminal_cat S]
// [G : func Terminal_cat S] (g_ : hom G (Unit_mod Id_func F) Id_func),
// hom (Elements_con_intro_func g_) (sieve_mod (maximal_sieve S_site F)) (Terminal_func _);
// // type  λ [S : cat] (S_site : site S) [F : func Terminal_cat S]
// // [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
// // (maximal_sieve_hom S_site g)  '∘ (sieve_transf (maximal_sieve S_site F))
// // = g;
// // rule (maximal_sieve_hom $S_site $g)  '∘ (sieve_transf (maximal_sieve $S_site $F))
// // ↪ $g;

// //    // pullback of sieve, defined symbol
//   symbol pullback_sieve  [S : cat] [S_site : site S] [F : func Terminal_cat S]
//   (ff : hom F (sieves S_site) (Terminal_func _)) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func)
//   :  hom G (Id_func ∘>> sieves S_site) (Terminal_func _)
//   ≔ (g '∘ (_)_'∘> ff);

// //    /// no constructor of elements of pullback sieve, only projection out of elements
//   constant symbol pullback_sieve_proj_transf : Π [S : cat] [S_site : site S] [F : func Terminal_cat S],
//   Π (ff : hom F (sieves S_site) (Terminal_func _)) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func) ,
//   transf (sieve_mod (pullback_sieve ff g)) (Elements_con_functorial_func ( (_)_'∘> g ) ) (sieve_mod ff) Id_func;

// //   rule ($h '∘ (pullback_sieve_proj_transf $ff $g)) '∘ (sieve_transf $ff)
// //   ↪ ($h '∘ (sieve_transf (pullback_sieve $ff $g))) '∘ (_)_'∘> $g ;

// //   assert [S : cat] [S_site : site S] [F : func Terminal_cat S]
// //    (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func)
// //   [H : func Terminal_cat S] (h : hom H (sieve_mod (pullback_sieve ff g)) Id_func) ⊢
// //   (h '∘ (pullback_sieve_proj_transf ff g)) '∘ (sieve_transf ff)
// //   ≡ (h '∘ (sieve_transf (g '∘ (_)_'∘> ff))) '∘ (_)_'∘> g ;

 
// //  // intersection sieve, todo? via product of presheaves
//  constant symbol intersection_sieve :Π [S : cat] [S_site : site S] [F : func Terminal_cat S]
//  (ff ff' : hom F (sieves S_site) (Terminal_func _)), hom F (sieves S_site) (Terminal_func _); 
// //  // sum of sieve

//   constant symbol sum_sieve : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π [ff : hom F (sieves S_site) (Terminal_func _)], transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site) Id_func
//   → hom F (sieves S_site) (Terminal_func _);

//   constant symbol sum_sieve_hom : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π (ff : hom F (sieves S_site) (Terminal_func _)) (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site) Id_func),
//   Π [G : func Terminal_cat S]
//   (f_ : hom G (Unit_mod Id_func F) Id_func) (f : hom (Elements_con_intro_func f_) (sieve_mod ff) (Terminal_func _))
//   [ H : func Terminal_cat S] (g_ : hom H (Unit_mod Id_func G) Id_func)  (g : hom ((Elements_con_intro_func g_)) 
//   /* TODO: should allow '∘ along non Id_func, merge cov and con and enforce implicit Id_func in rules if required */
//   (sieve_mod (T_ ∘' f)) (Terminal_func _)),  //   (g : hom H (f '∘ sieve_transf ff) (Terminal_func _))  ;
//    hom (Elements_con_intro_func (g_ '∘ (_)_'∘> f_) ) (sieve_mod (sum_sieve T_)) (Terminal_func _);
//   constant symbol sum_sieve_hom' : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   Π (ff : hom F (sieves S_site) (Terminal_func _)) (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site) Id_func),
//   Π [G : func Terminal_cat S]
//   (f_ : hom G (Unit_mod Id_func F) Id_func) (f : hom (Elements_con_intro_func f_) (sieve_mod ff) (Terminal_func _))
//    (g_ : func Terminal_cat (Elements_con_cat (Unit_mod Id_func G)) )  (g : hom g_
//   /* TODO: should allow '∘ along non Id_func, merge cov and con and enforce implicit Id_func in rules if required */
//   (sieve_mod (T_ ∘' f)) (Terminal_func _)),  //   (g : hom H (f '∘ sieve_transf ff) (Terminal_func _))  ;
//    hom (g_ ∘> (Elements_con_functorial_func ( (_)_'∘> f_ ) )) (sieve_mod (sum_sieve T_)) (Terminal_func _);

// //   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S], 
// //   λ [ff : hom F (sieves S_site) Id_func] (T_ : transf (sieve_mod ff) Id_func (sieves S_site) Id_func),
// //   λ [G : func Terminal_cat S]
// //    (f : hom G (sieve_mod ff) (Terminal_func _)) [ H : func Terminal_cat S](g : hom H (sieve_mod (f '∘ T_)) (Terminal_func _)), 
// // (g '∘ (sieve_transf (f '∘ T_))) '∘ (_)_'∘> (f '∘ (sieve_transf ff))
// //  = (sum_sieve_hom ff T_ f g) '∘ (sieve_transf (sum_sieve T_));

// //  rule (sum_sieve_hom $ff $T_ $f $g) '∘ (sieve_transf (sum_sieve $T_))
// // ↪ ($g '∘ (sieve_transf ($f '∘ $T_))) '∘ (_)_'∘> ($f '∘ (sieve_transf $ff)) ;
// // //hom H (Id_func ∘>> Unit_mod Id_func F) ((Id_func <∘ Terminal_func Terminal_cat) <∘ (Id_func <∘ Terminal_func Terminal_cat))

// // /// for testing: all sites are ringed... and no modular API interface for rings, ring-modules, ...
// // constant symbol ringed : Π [S : cat] (S_site : site S), mod S Terminal_cat;
// // symbol ringed_mult : Π [S : cat] [S_site : site S] [G : func Terminal_cat S] //todo? via product of presheaves
// //   (g g' : hom G (ringed S_site) Id_func), hom G (ringed S_site) Id_func;

// // // ringed_locally is similar as some general D(f) ... 
// // // outputs sieve where the function is invertible (for affine is singleton sieve on primitive Zarisky D(r) affineScheme_func below)
// // constant symbol ringed_locally : Π [S : cat] (S_site : site S),
// //   transf (ringed S_site) Id_func (sieves S_site) Id_func; 

// /// for testing: ...
// constant symbol ring : TYPE ; 
// constant symbol ring_type: ring → TYPE;
// constant symbol ring_mult : Π [R : ring] (r s : ring_type R), ring_type R;

// //todo? via concrete cat instead?  (because must use Terminal_cat ?)
// constant symbol affineScheme_cat : Π (R : ring), cat;
// constant symbol affineScheme_site : Π (R : ring), site (affineScheme_cat R);
//  // primitive Zarisky  D(r)... for affine ringed_locally is singleton sieve on this 
// constant symbol affineScheme_func : Π [R : ring] (r : ring_type R), func Terminal_cat (affineScheme_cat R);
// constant symbol affineScheme_hom : Π [R : ring] (r s: ring_type R), 
//  hom (affineScheme_func (ring_mult s r)) (Unit_mod Id_func (affineScheme_func r)) Id_func;
//  constant symbol affineScheme_nilradical_hom : Π [R : ring] (s r: ring_type R), 
//  hom (affineScheme_func (ring_mult s r)) (Unit_mod Id_func (affineScheme_func (ring_mult s (ring_mult r r)))) Id_func;


//  constant  symbol isCovering : Π [S : cat] (S_site : site S),
//  transf (sieves S_site) Id_func (sieves S_site) Id_func;

//  type λ [S : cat] (S_site : site S), 
//   (isCovering S_site) ''∘ (isCovering S_site) 
//   = isCovering S_site;

// type λ [S : cat] (S_site : site S) (F : func Terminal_cat S),
// (maximal_sieve S_site F) '∘ (isCovering S_site) 
// = (maximal_sieve S_site F);

// type λ  [S : cat] [S_site : site S] [F : func Terminal_cat S]
// (ff ff' : hom F (sieves S_site) (Terminal_func _)),
// (intersection_sieve ff ff') '∘ (isCovering S_site) 
// = (intersection_sieve (ff '∘ (isCovering S_site)) (ff' '∘ (isCovering S_site) )); 


// V3


constant symbol Elements_con_cat : Π [B C : cat] (R : mod B C), cat;
constant symbol Elements_con_proj_func : Π [B C : cat] (R : mod B C),
func (Elements_con_cat R) B;
//todo : relax (Terminal_func I) to any x ?
constant symbol Elements_con_intro_func : Π [B C I : cat] [R : mod B C]  [y : func I B]  [x : func I C]  (r : hom y R x),
func I (Elements_con_cat R);
rule $F ∘> (@Elements_con_intro_func _ _ _ _ $y $x $r) ↪ (@Elements_con_intro_func _ _ _ _ ($F ∘> $y) ($F ∘> $x) ($r ∘↓ $F));

rule  (@Elements_con_intro_func _ _ _ _ $y  $x $r ∘> Elements_con_proj_func _) ↪  $y;

constant symbol Elements_con_comp_func : Π [B C I : cat] (R : mod B C) (G : func I B),
func (Elements_con_cat (G ∘>> R)) (Elements_con_cat R);

rule  (Elements_con_comp_func $R $G ∘> (Elements_con_proj_func _)) ↪ (Elements_con_proj_func ($G ∘>> $R)) ∘> $G;

//todo erase the less general Elements_con_intro_hom
constant symbol Elements_con_intro_hom : Π [B C I : cat] [R : mod B C]  [y : func I B] [x : func I C]   (r : hom y R x),
Π [K] [y' : func K I] [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y'y (Unit_mod G y) y') ,
hom (Elements_con_intro_func( y'y_ '∘  ((G)_'∘> r)  )) (Unit_mod (Elements_con_comp_func R G) (Elements_con_intro_func r)) y';

rule (Func_cov_hom (Elements_con_proj_func $R) _) ∘>'_(_) ∘'  (Elements_con_intro_hom $r $y'y_) ↪ (Id_hom _) ∘>'_(_) ∘' $y'y_ ;

////another instance of yoneda is by precompose yoneda with Elements_con_proj_transf
constant symbol Elements_con_proj_transf : Π [B  C : cat] [R : mod B C]  (E : mod (Elements_con_cat R) C),
transf E (Elements_con_proj_func R) R Id_func;
constant symbol Elements_con_proj_transf' : Π [B C : cat] [R : mod B C]  (E : mod (Elements_con_cat R) C) [I] (G : func I B),
transf ((Elements_con_comp_func R G) ∘>> E) (Elements_con_proj_func (G ∘>> R)) (G ∘>> R) Id_func;

// 
symbol Elements_con_functorial_func : Π [B C : cat] [R R' : mod B C]  [ G]
(t : transf R Id_func /* generalize Id_func */ R' G) ,
 func (Elements_con_cat R) (Elements_con_cat R');

rule (Elements_con_intro_func ($g_)) ∘> Elements_con_functorial_func $t
  ↪ (Elements_con_intro_func ($g_ '∘ $t) );

constant symbol site : cat → TYPE ; 
constant symbol site_Set : cat → Set; rule τ (site_Set $C) ↪ site $C;
constant symbol sieves : Π [S : cat] (S_site : site S) I /* I could be site too... then classifier is locally constant */, mod S I;
    // constant (constructor), not defined symbol, no rewrites from it... especially because of sum_sieve...

  //bad version v2: many batches of  singlesieves (...somewhat multi the J in (func J I) maybe non terminal cat,  so kinda ok)
  constant symbol sieve_mod : Π [S : cat] [S_site : site S]  [I] [F : func I S] , 
  Π (ff : hom F (sieves S_site I) Id_func), mod (Elements_con_cat (Unit_mod Id_func F)) I;

  // good version v3: many batches of  multisieves... or nope, the cov part allows to keep track of which object (func J D) was picked in the (contra of the) contra part
  constant symbol sieve_mod_v3 : Π [S : cat] [S_site : site S]  [I] [F : func I S] [D] [K : func I D], Π (ff : hom F (sieves S_site D) K), 
  mod (Elements_con_cat ((Unit_mod Id_func F) ⊗ (Unit_mod K Id_func) )) D;

  // bad version v1: single batch of singlesieves
  constant symbol sieve_mod_v1 : Π [S : cat] [S_site : site S] [F : func Terminal_cat S], 
    Π (ff : hom F (sieves S_site Terminal_cat) (Terminal_func _)), mod (Elements_con_cat (Unit_mod Id_func F)) Terminal_cat;

  // sieve as subfunctor ... as fibration instead? or as prof (in groupoids) over elements-cat of base? (because of intersection operation)
  // constant symbol sieve_transf : Π [S : cat] [S_site : site S] [F : func Terminal_cat S],
  // Π (ff : hom F (sieves S_site) Id_func), transf (sieve_mod ff) Id_func (Unit_mod Id_func F) Id_func;

//when R will be sheaf
symbol gluing_when_covering_and_sheaves : Π [A B : cat] [A_site : site A] [I] [F : func I A]  [R : mod A B]  [G : func I B]
(ff : hom F (sieves A_site I) Id_func),
transf ( sieve_mod ff) (Elements_con_proj_func _) ( R) G →  hom F R G  ;
// symbol gluing_when_covering_and_sheaves : Π [A B : cat] [A_site : site A] [I] [F : func I A]  [R : mod A B]  [G : func I B]
// (ff : hom F (sieves A_site I) Id_func),
// transf ( sieve_mod ff) (Elements_con_proj_func _) ( R) G →  hom F R G  ;


  // max sieve
  constant  symbol maximal_sieve : Π [S : cat] (S_site : site S) [I] (F : func I S), hom F (sieves S_site I) Id_func;

  type λ [S : cat] [S_site : site S] [F : func Terminal_cat S]
  [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
  (g '∘ (_)_'∘> (maximal_sieve S_site F))
  = (maximal_sieve S_site G);
  rule   (@'∘ _ _ _ Terminal_cat  _ _ _ (Terminal_func _) _ $g  ((Id_func)_'∘> (maximal_sieve $S_site $F)))
  ↪ (maximal_sieve $S_site _);

 
  type λ [S : cat] [S_site : site S] [I] [F : func I S]
  (ff : hom F (sieves S_site I) Id_func) [G : func I S] 
  (g_ : hom G (Unit_mod Id_func F) Id_func) (g : hom (Elements_con_intro_func g_) (sieve_mod ff) Id_func),
  (g_ ) '∘ (_)_'∘> ff
  = (maximal_sieve S_site G);

// rule   (@'∘ _ _ _ _  _ _ _ Id_func _  $g (sieve_transf $ff)) '∘ (_)_'∘> $ff
// ↪ (maximal_sieve _ _);

// // elements of max sieve
constant symbol maximal_sieve_hom : Π [S : cat] (S_site : site S) [I] [F : func I S]
[G : func I S] (g_ : hom G (Unit_mod Id_func F) Id_func),
hom (Elements_con_intro_func g_) (sieve_mod (maximal_sieve S_site F)) Id_func /* generalize this Id_func */;
// type  λ [S : cat] (S_site : site S) [F : func Terminal_cat S]
// [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func),
// (maximal_sieve_hom S_site g)  '∘ (sieve_transf (maximal_sieve S_site F))
// = g;
// rule (maximal_sieve_hom $S_site $g)  '∘ (sieve_transf (maximal_sieve $S_site $F))
// ↪ $g;

//    // pullback of sieve, defined symbol
  symbol pullback_sieve  [S : cat] [S_site : site S] [I] [F : func I S]
  (ff : hom F (sieves S_site I) Id_func) [G : func I S] (g : hom G (Unit_mod Id_func F) Id_func)
  :  hom G (Id_func ∘>> sieves S_site I) Id_func
  ≔ (g '∘ (_)_'∘> ff);

//    /// no constructor of elements of pullback sieve, only projection out of elements
  constant symbol pullback_sieve_proj_transf : Π [S : cat] [S_site : site S] [I] [F : func I S],
  Π (ff : hom F (sieves S_site I) Id_func) [G : func I S] (g : hom G (Unit_mod Id_func F) Id_func) ,
  transf (sieve_mod (pullback_sieve ff g)) (Elements_con_functorial_func ( (_)_'∘> g ) ) (sieve_mod ff) Id_func ;

//   rule ($h '∘ (pullback_sieve_proj_transf $ff $g)) '∘ (sieve_transf $ff)
//   ↪ ($h '∘ (sieve_transf (pullback_sieve $ff $g))) '∘ (_)_'∘> $g ;

//   assert [S : cat] [S_site : site S] [F : func Terminal_cat S]
//    (ff : hom F (sieves S_site) Id_func) [G : func Terminal_cat S] (g : hom G (Unit_mod Id_func F) Id_func)
//   [H : func Terminal_cat S] (h : hom H (sieve_mod (pullback_sieve ff g)) Id_func) ⊢
//   (h '∘ (pullback_sieve_proj_transf ff g)) '∘ (sieve_transf ff)
//   ≡ (h '∘ (sieve_transf (g '∘ (_)_'∘> ff))) '∘ (_)_'∘> g ;

 
//  // intersection sieve, todo? via product of presheaves
// intersection is ("non-dependent") instance of sum (of pullbacks of single sieve) along another sieve
 constant symbol intersection_sieve :Π [S : cat] [S_site : site S] [I] [F : func I S]
 (ff ff' : hom F (sieves S_site I) Id_func), hom F (sieves S_site I) Id_func; 

//  // sum of sieve

  constant symbol sum_sieve : Π [S : cat] [S_site : site S] [I] [F : func I S], 
  Π [ff : hom F (sieves S_site I) Id_func], transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site I) Id_func
  → hom F (sieves S_site I) Id_func;

  /// is there simpler version as instance of general sigma type/presheaf?
  constant symbol sum_sieve_hom : Π [S : cat] [S_site : site S] [I] [F : func I S], 
  Π (ff : hom F (sieves S_site I) Id_func) (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site I) Id_func),
  Π [G : func I S]
  (f_ : hom G (Unit_mod Id_func F) Id_func) (f : hom (Elements_con_intro_func f_) (sieve_mod ff) Id_func)
  [ H : func I S] (g_ : hom H (Unit_mod Id_func G) Id_func)  (g : hom ((Elements_con_intro_func g_)) 
  /* TODO: should allow '∘ along non Id_func, merge cov and con and enforce implicit Id_func in rules if required */
  (sieve_mod (T_ ∘' f)) Id_func),  //   (g : hom H (f '∘ sieve_transf ff) (Terminal_func _))  ;
   hom (Elements_con_intro_func (g_ '∘ (_)_'∘> f_) ) (sieve_mod (sum_sieve T_)) Id_func /* generalize this Id_func */;
  constant symbol sum_sieve_hom' : Π [S : cat] [S_site : site S] [I] [F : func I S], 
  Π (ff : hom F (sieves S_site I) Id_func) (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site I) Id_func),
  Π [G : func I S]
  (f_ : hom G (Unit_mod Id_func F) Id_func) (f : hom (Elements_con_intro_func f_) (sieve_mod ff) Id_func)
   (g_ : func I (Elements_con_cat (Unit_mod Id_func G)) )  (g : hom g_
  /* TODO: should allow '∘ along non Id_func, merge cov and con and enforce implicit Id_func in rules if required */
  (sieve_mod (T_ ∘' f)) Id_func),  //   (g : hom H (f '∘ sieve_transf ff) (Terminal_func _))  ;
   hom (g_ ∘> (Elements_con_functorial_func ( (_)_'∘> f_ ) )) (sieve_mod (sum_sieve T_)) Id_func;

//   type λ [S : cat] [S_site : site S] [F : func Terminal_cat S], 
//   λ [ff : hom F (sieves S_site) Id_func] (T_ : transf (sieve_mod ff) Id_func (sieves S_site) Id_func),
//   λ [G : func Terminal_cat S]
//    (f : hom G (sieve_mod ff) (Terminal_func _)) [ H : func Terminal_cat S](g : hom H (sieve_mod (f '∘ T_)) (Terminal_func _)), 
// (g '∘ (sieve_transf (f '∘ T_))) '∘ (_)_'∘> (f '∘ (sieve_transf ff))
//  = (sum_sieve_hom ff T_ f g) '∘ (sieve_transf (sum_sieve T_));

//  rule (sum_sieve_hom $ff $T_ $f $g) '∘ (sieve_transf (sum_sieve $T_))
// ↪ ($g '∘ (sieve_transf ($f '∘ $T_))) '∘ (_)_'∘> ($f '∘ (sieve_transf $ff)) ;
// //hom H (Id_func ∘>> Unit_mod Id_func F) ((Id_func <∘ Terminal_func Terminal_cat) <∘ (Id_func <∘ Terminal_func Terminal_cat))

// /// for testing: all sites are ringed... and no modular API interface for rings, ring-modules, ...
// constant symbol ringed : Π [S : cat] (S_site : site S), mod S Terminal_cat;
// symbol ringed_mult : Π [S : cat] [S_site : site S] [G : func Terminal_cat S] //todo? via product of presheaves
//   (g g' : hom G (ringed S_site) Id_func), hom G (ringed S_site) Id_func;

// // ringed_locally is similar as some general D(f) ... 
// // outputs sieve where the function is invertible (for affine is singleton sieve on primitive Zarisky D(r) affineScheme_func below)
// constant symbol ringed_locally : Π [S : cat] (S_site : site S),
//   transf (ringed S_site) Id_func (sieves S_site) Id_func; 

/// for testing: ...
constant symbol ring : TYPE ; 
constant symbol ring_type: ring → TYPE;
constant symbol ring_mult : Π [R : ring] (r s : ring_type R), ring_type R;

//todo? via concrete cat instead?  (because must use Terminal_cat ?)
constant symbol affineScheme_cat : Π (R : ring), cat;
constant symbol affineScheme_site : Π (R : ring), site (affineScheme_cat R);
 // primitive Zarisky  D(r)... for affine ringed_locally is singleton sieve on this 
constant symbol affineScheme_func : Π [R : ring] (r : ring_type R), func Terminal_cat (affineScheme_cat R);
constant symbol affineScheme_hom : Π [R : ring] (r s: ring_type R), 
 hom (affineScheme_func (ring_mult s r)) (Unit_mod Id_func (affineScheme_func r)) Id_func;
 constant symbol affineScheme_nilradical_hom : Π [R : ring] (s r: ring_type R), 
 hom (affineScheme_func (ring_mult s r)) (Unit_mod Id_func (affineScheme_func (ring_mult s (ring_mult r r)))) Id_func;


 constant  symbol isCovering : Π [S : cat] (S_site : site S) I,
 transf (sieves S_site I) Id_func (sieves S_site I) Id_func;

 type λ [S : cat] (S_site : site S) I, 
  (isCovering S_site I) ''∘ (isCovering S_site I) 
  = isCovering S_site I;

type λ [S : cat] (S_site : site S) I (F : func I S),
(maximal_sieve S_site F) '∘ (isCovering S_site I) 
= (maximal_sieve S_site F);

type λ  [S : cat] [S_site : site S] [I] [F : func I S]
(ff ff' : hom F (sieves S_site I) Id_func),
(intersection_sieve ff ff') '∘ (isCovering S_site I) 
= (intersection_sieve (ff '∘ (isCovering S_site I)) (ff' '∘ (isCovering S_site I) )); 
// todo: isCovering for sum sieve
type λ [S : cat] [S_site : site S] [I] [F : func I S], 
λ [ff : hom F (sieves S_site I) Id_func] (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site I) Id_func),
   (sum_sieve T_) '∘ (isCovering S_site I)
   = ( sum_sieve ( (isCovering S_site I) ∘'' T_ /* /1\ WARNING modal extend this to closure  ff' =  ff '∘ (isCovering S_site I) to get T_' : transf (sieve_mod ff') */) ) ;

//external relation:  isCoveringMax ff ≔   isCovering ff = maximal_sive
// usable in the reverse-yoneda gluing
constant  symbol isCoveringMax : Π [S : cat] [S_site : site S] 
[I] [F : func I S] (ff : hom F (sieves S_site I) Id_func), TYPE;

type λ [S : cat] (S_site : site S) I (F : func I S),
isCoveringMax  (maximal_sieve S_site F) ;

type λ [S : cat] [S_site : site S] [I] [F : func I S],
λ (ff : hom F (sieves S_site I) Id_func) [G : func I S] (g : hom G (Unit_mod Id_func F) Id_func) ,
isCoveringMax  ff →
isCoveringMax  (pullback_sieve ff g);

type λ [S : cat] [S_site : site S] [I] [F : func I S], 
λ [ff : hom F (sieves S_site I) Id_func] (T_ : transf (sieve_mod ff) (Elements_con_proj_func _) (sieves S_site I) Id_func),
(Π [G : func I S]
  (f_ : hom G (Unit_mod Id_func F) Id_func) (f : hom (Elements_con_intro_func f_) (sieve_mod ff) Id_func) ,
  isCoveringMax  (T_ ∘' f)) →
   isCoveringMax (sum_sieve T_);

