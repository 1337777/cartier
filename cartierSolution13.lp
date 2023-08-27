/* https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.pdf 
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_outline_alt.docx 


Re: [Agda] position in Deducteam — Lawvere/Dosen session on categorial logic/programming @ CT2023

Salut Louis Auguste « L'Enfermé » Blanqui,

  A new implementation of dependent types via Dosen's substructural categorial programming: example of the Yoneda lemma for fibrations

This closes the open problem of implementing a dependent-types computer for category theory, where types are categories and dependent types are fibrations of categories. The basis for this implementation are the ideas and techniques from Kosta Dosen's book « Cut-elimination in categories » (1999), which essentially is about the substructural logic of category theory, in particular about how some good substructural formulation of the Yoneda lemma allows for computation and automatic-decidability of categorial equations.

The core of dependent types/fibrations in category theory is the Lawvere's comma/slice construction and the corresponding Yoneda lemma for fibrations (https://stacks.math.columbia.edu/tag/0GWH), thereby its implementation essentially closes this open problem also investigated by Cisinski's directed types or Garner's 2-dimensional types. What qualifies as a solution is subtle and the thesis here is that Dosen's substructural techniques cannot be bypassed.

In summary, this text implements, using Blanqui's LambdaPi metaframework software tool, an (outer) cut-elimination in the double category of fibred profunctors with (inner) cut-eliminated adjunctions. The outer cut-elimination essentially is a new functorial lambda calculus via the « dinaturality » of evaluation and the monoidal bi-closed structure of profunctors, without need for multicategories because (outer) contexts are expressed via dependent types. This text also implements (higher) inductive datatypes such as the join-category (interval simplex), with its introduction/elimination/computation rules. This text also implements Sigma-categories/types and categories-of-functors and more generally Pi-categories-of-functors, but an alternative more-intrinsic formulation using functors fibred over spans or over Kock's polynomial-functors will be investigated. This text also implements a dualizing Op operations, and it can computationally-prove that left-adjoint functors preserve profunctor-weighted colimits from the proof that right-adjoint functors preserve profunctor-weighted limits. This text also implements a grammatical (univalent) universe and the universal fibration classifying small fibrations, together with the dual universal opfibration. Finally, there is an experimental implementation of covering (co)sieves towards grammatical sheaf cohomology and towards a description of algebraic geometry's schemes in their formulation as locally affine ringed sites (structured topos), instead of via their Coquand's formulation as underlying topological space...

References:

[1] Dosen-Petric: Cut Elimination in Categories 1999; 
[2] Proof-Theoretical Coherence 2004; 
[3] Proof-Net Categories 2005; 
[4] Coherence in Linear Predicate Logic 2007; 
[5] Coherence for closed categories with biproducts 2022 
[6] Cut-elimination in the double category of fibred profunctors with inner cut-eliminated adjunctions: 
https://github.com/1337777/cartier/blob/master/cartierSolution13.lp 
[7] Pierre Cartier

Subscribe for live updates, WorkSchool365.com : https://www.youtube.com/@workschool365

FAQ:

* How is « substructural » contrasted vs « synthetic » ? The substructural Yoneda lemma for fibrations is expressed via a blend of the universality/introduction rule of the transported/pulledback objects inside fibred categories:

  constant symbol Fibration_con_intro_homd : Π [I X X'  : cat] [x'x : func X' X] (G : func X I) [KK : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II) (FF : funcd KK F II) (f : hom x'x (Unit_mod G Id_func) F) [X'0 : cat] [x'0x : func X'0 X] [X'' : cat] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] (x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x') [JJ : catd X'0] (MM : funcd JJ x'0x (Fibre_catd II G)) [HH : funcd (Fibre_catd KK x''x') x''x'0 JJ],
homd ((x'0x' '∘ ((x'0x)_'∘> f))) HH (Unit_modd (MM ∘>d (Fibre_elim_funcd II G)) Id_funcd) ((Fibre_elim_funcd KK (x''x')) ∘>d FF) →  
homd x'0x' HH (Unit_modd MM (Fibration_con_funcd G II_isf FF f)) (Fibre_elim_funcd KK (x''x')) ;

together with the composition operation (in Yoneda formulation) inside fibred categories:

  constant symbol ∘>d'_ : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G] [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], homd r FF RR GG → 
Π [J: cat] [M : func J Y] [JJ : catd J] (MM : funcd JJ M B), 
transfd ( r ∘>'_(M) ) (Unit_modd GG MM) FF (RR d<<∘ MM ) Id_funcd;                

* How is « J-rule arrow induction » contrasted vs « fibrational transport » ? The above intrinsic/structural universality formulation comes with a corresponding reflected/internalized algebra formulation, which is the comma category where the J-rule elimination ("equality/path/arrow induction") occurs. Similarly, pullbacks have a universal formulation (fibre of fibration), an algebraic formulation (composition of spans), or mixed (product of fibration-objects in the slice category).

  constant symbol Comma_con_intro_funcd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd BB y) x (Comma_con_catd R BB);

  constant symbol Comma_con_elim_funcd : Π [I X : cat] (G : func X I)  [II : catd I] (II_isf : isFibration_con II) [KK : catd I] (FF : funcd KK Id_func II), 
funcd (Comma_con_catd (Unit_mod G Id_func) KK) G II;

* Are substitutions explicit or intrinsic/structural? Ordinary (non-fibred) cut-elimination considers pairs of composable arrows p : X → Y then q : Y → Z, but fibred cut-elimination should also consider pairs of arrows p : X → f*Y then q : g*Y → Z, where f*Y is the pullback of Y along f, and such a pair is not manifestly/grammatically/syntactically-composable but only semantically-composable as g'*p : g'*X → g'*(f*Y) then f'*q : f'*(g*Y) → f'*Z, where f' = g*f is the pullback of f along g and g' = f*g is the pullback of g along f. The remedy is to make those pullback intrinsic/implicit in the implementation's grammar, so that p : X → f*Y is really notation for a judgment with 3 parameters X, Y and f, which can be read as « p is a fibred arrow forward-above the arrow f », and similarly q : g*Y → Z is read as « q is a fibred arrow backward-above the arrow g », and more generally r : g*X → f*Z is read as « r is a fibred arrow above the span of arrows g backward with f forward ». Ultimately it should be possible to express arrows fibred over polynomial-functors, so that the distributivity (ΠΣ = ΣΠε*) in the composition of polynomial-functors is intrinsic in the implementation's grammar... Finally, all of these intrinsic structures are reflected/internalized as an explicit substitution/pullback-type-former for any fibration.

* What is the difference between the Pi-type of sections and the category-of-functors? Ordinary Pi/product-types consider only the sections of some fibration, but Pi-categories should consider all the category-of-functors to some fibration, this leads to the new construction of Pi-category-of-functors. The preliminary implementation in this text does not yet use the more-intrinsic formulation using functors fibred-above-a-span of functors. It should be noted that Sigma/sum-categories can be already intrinsically-implemented using only functors fibred-forward-above a single functor.

* And why profunctors (of sets)? The primary motivation is that they form a monoidal bi-closed double category (functorial lambda calculus). Another motivation is that the subclass of fibrations called discrete/groupoidal fibrations can only be computationally-recognized/expressed instead via (indexed) presheaves/profunctors of sets. And the comma construction is how to recover the intended discrete fibration. Ultimately profunctors enriched in preorders/quantales instead of mere sets could be investigated (Tholen's TV, lol).

* What is a fibred profunctor anyway? The comma/slice categories are only fibred categories (of triangles of arrows fibred by their base), not really fibred profunctors. One example of fibred profunctor from the coslice category to the slice category is the set of squares fibred by their diagonal which witnesses that this square is constructed by pasting two triangles. This text implements such fibred profunctor of (cubical) squares (thereby validating the hypothesis that computational-cubes should have connections/diagonals...). For witnessing the (no-computational-content) pasting along the diagonal, this implementation uses for the first time the LambdaPi-metaframework's equality predicate which internally-reflects all the conversion-rules; in particular the implementation uses here the categorial-associativity equation axiom, which is a provable metatheorem which must *not* be added as a rewrite rule!

*/

// require open Blanqui.Lib.Set Blanqui.Lib.Prop Blanqui.Lib.Eq;

constant symbol Set : TYPE;
injective symbol τ : Set → TYPE;
builtin "T" ≔ τ;

constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;

constant symbol = [a] : τ a → τ a → Prop;
notation = infix 10;
constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);
builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

constant symbol × : Set → Set → Set; notation × infix right 10; 
symbol & [a b] : τ a → τ b → τ (a × b); notation & infix right 30;
symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;
rule ($x & _)₁ ↪ $x;
symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;
rule (_ & $x)₂ ↪ $x;

constant symbol ⊤ : Prop;
constant symbol top : π ⊤;

constant symbol ⊥ : Prop;
constant symbol ⊥ₑ [p] : π ⊥ → π p;

constant symbol Π_ : Π [a], (τ a → Set) → Set; notation Π_ quantifier;
rule τ (@Π_ $a $b) ↪ Π x : τ $a, τ ($b x);

constant symbol →_ : Set → Set → Set; notation →_ infix right 10;
rule τ ($x →_ $y) ↪ τ $x → τ $y;

inductive τΣ_ [a : Set] (P : τ a → Set) : TYPE ≔
| Struct_sigma [a P] : Π
(sigma_Fst : τ a)
(sigma_Snd : τ (P sigma_Fst) ), @τΣ_ a P;
notation τΣ_ quantifier;
constant symbol Σ_ [a : Set] (P : τ a → Set) : Set; notation Σ_ quantifier;
rule τ (Σ_ $P) ↪ τΣ_ $P;
injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s)) ;
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

inductive τsub_ [a : Set] (P : τ a → Prop) : TYPE ≔
| Struct_sub [a P] : Π
(sub_Fst : τ a)
(sub_Snd : π (P sub_Fst) ), @τsub_ a P;
notation τsub_ quantifier;
constant symbol sub_ [a : Set] (P : τ a → Prop) : Set; notation sub_ quantifier;
rule τ (sub_ $P) ↪ τsub_ $P;
injective symbol sub_Fst [a P] (s : @τsub_ a P) : τ a;
rule sub_Fst (Struct_sub $1 $2) ↪ $1;
injective symbol sub_Snd [a P] (s : @τsub_ a P) : π (P (sub_Fst s)) ;
rule sub_Snd (Struct_sub $1 $2) ↪ $2;

inductive 𝔹 : TYPE ≔
| true : 𝔹
| false : 𝔹;
constant symbol bool : Set;
rule τ bool ↪ 𝔹;

symbol istrue : 𝔹 → Prop;
rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

symbol or : 𝔹 → 𝔹 → 𝔹; notation or infix left 20;
rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

symbol and : 𝔹 → 𝔹 → 𝔹; notation and infix left 7;
rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;
rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;

inductive ℕ : TYPE ≔
| zero : ℕ
| s : ℕ → ℕ;
builtin "0"  ≔ zero;
builtin "+1" ≔ s;
constant symbol nat : Set;
rule τ nat ↪ ℕ;

symbol eqn : ℕ → ℕ → 𝔹;
rule eqn 0 0 ↪ true
with eqn (s $x) (s $y) ↪ eqn $x $y
with eqn 0 (s _) ↪ false
with eqn (s _) 0 ↪ false;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::
notation ⸬ infix right 20;
constant symbol list : Set → Set;
rule τ (list $a) ↪ 𝕃 $a;

symbol ⋅ [a] : 𝕃 a → 𝕃 a → 𝕃 a; notation ⋅ infix right 30; // \cdot
rule □ ⋅ $m ↪ $m
with ($x ⸬ $l) ⋅ $m ↪ $x ⸬ ($l ⋅ $m);

symbol filter [a] : (τ a → 𝔹) → 𝕃 a → 𝕃 a;
rule filter _ □ ↪ □
with filter $p ($x ⸬ $l) ↪ if ($p $x) ($x ⸬ (filter $p $l)) (filter $p $l);

symbol ∈ [a] : (τ a → τ a → 𝔹) → τ a → 𝕃 a → 𝔹;
rule ∈ _ _ □ ↪ false
with ∈ $beq $x ($y ⸬ $l) ↪ $beq $x $y or ∈ $beq $x $l;

symbol map [a b] : (τ a → τ b) → 𝕃 a → 𝕃 b;
rule map _ □ ↪ □
with map $f ($x ⸬ $l) ↪ $f $x ⸬ map $f $l;

constant symbol DEBUG_ADMIT [a : Set] : τ a;
injective symbol DEBUG_TAG1 [a : Set] : τ a → τ a; rule DEBUG_TAG1 $x ↪ $x;
injective symbol DEBUG_TAG2 [a : Set] : τ a → τ a; rule DEBUG_TAG2 $x ↪ $x;

 /* (A) INTERFACE ========================== */

 constant symbol cat : TYPE ;
 constant symbol cat_Set : Set ;
 rule τ (cat_Set) ↪ cat;
 
 constant symbol func : Π (A B : cat), TYPE ;
 constant symbol func_Set : Π (A B : cat), Set ;
 rule τ (@func_Set $A $B) ↪ @func $A $B ;

 constant symbol mod : Π (A B : cat), TYPE ;
 constant symbol mod_Set : Π (A B : cat), Set ;
 rule τ (@mod_Set $A $B) ↪ @mod $A $B;
 
 constant symbol hom : Π [I A B : cat], func I A → mod A B → func I B →  TYPE ;
 constant symbol hom_Set : Π [I A B : cat], func I A → mod A B → func I B → Set ;
 rule τ (@hom_Set $I $A $B $F $R $G) ↪ @hom $I $A $B $F $R $G;

 //TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR DEPENDENT MORPHISM OF FIBRATIONS
 // AND FOR COMPOSIITON OF SPANS USE ALGEBRAIC PULLBACKS NOT UNIVERSAL VERSION
 constant  symbol transf : Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → TYPE ;
 constant symbol transf_Set : Π [A' B' A B: cat], mod A' B' → func A' A → mod A B → func B' B → Set  ;
 rule τ (@transf_Set $A' $B' $A $B $R' $F $R $G) ↪ @transf $A' $B' $A $B $R' $F $R $G;
 
 constant symbol adj : Π [R L : cat], func R L → func L R → TYPE  ;
 constant symbol adj_Set : Π [R L : cat], func R L → func L R → Set  ;
 rule τ (@adj_Set $R $L $F $G) ↪ (@adj $R $L $F $G);

 constant symbol limit_cov : Π [B J J' : cat] (F : func J B) (W : mod J' J) (F_⇐_W : func J' B), TYPE  ;
 constant symbol limit_cov_Set : Π [B J J' : cat] (F : func J B) (W : mod J' J) (F_⇐_W : func J' B), Set  ;
 rule τ (@limit_cov_Set $B $J $J' $F $W $F_⇐_W) ↪ @limit_cov $B $J $J' $F $W $F_⇐_W;

 constant symbol limit_con: Π [B J J' : cat] (F : func J B) (W : mod J J') (W_⊗_F : func J' B), TYPE  ;
 
 constant symbol catd: Π (X : cat), TYPE ; 
 constant symbol catd_Set: Π (X : cat), Set ; 
 rule τ (@catd_Set $X) ↪ (@catd $X);

 constant symbol isFibration_con: Π [X : cat] (XX : catd X), TYPE; 
 constant symbol isFibration_con_Set: Π [X : cat] (XX : catd X), Set; 
 rule τ (@isFibration_con_Set $X $XX) ↪ (@isFibration_con $X $XX);

 constant symbol isFibration_cov: Π [X : cat] (XX : catd X), TYPE; 

 constant symbol funcd : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), TYPE ;
 constant symbol funcd_Set : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), Set ;
 rule τ (@funcd_Set $X $Y $A $F $B) ↪ (@funcd $X $Y $A $F $B);

 constant symbol funcs : Π [X Y : cat] (F : func X Y) (B : catd Y), TYPE ;
 constant symbol funcs_Set : Π [X Y : cat] (F : func X Y) (B : catd Y), Set ;
 rule τ (@funcs_Set $X $Y $F $B) ↪ (@funcs $X $Y $F $B);

 constant symbol funci : Π [X : cat] (A : catd X), TYPE ;
 constant symbol funci_Set : Π [X : cat] (A : catd X),  Set ;
 rule τ (@funci_Set $X $A) ↪ (@funci $X $A);
 
//TODO: erase, instead declare the Total_func $FF $u as isFuncEquiv
 constant symbol isEquiv : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → TYPE ;
 
 constant symbol modd : Π [X Y : cat], catd X → mod X Y → catd Y → TYPE ;
 constant symbol modd_Set : Π [X Y : cat], catd X → mod X Y → catd Y → Set ;
 rule τ (@modd_Set $X $Y $A $R $B) ↪ (@modd $X $Y $A $R $B);

 constant symbol homd : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
 Π [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), TYPE ;
 constant symbol homd_Set : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y], hom F R G → 
Π [A : catd X] [B : catd Y] [II : catd I] (FF : funcd II F A) (RR : modd A R B) (GG : funcd II G B), Set ; 
 rule τ (@homd_Set $X $Y $I $F $R $G $r $A $B $II $FF $RR $GG) ↪ @homd $X $Y $I $F $R $G $r $A $B $II $FF $RR $GG; 

constant symbol transfd : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [F : func X X'] [G : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
(r : transf R F R' G) (RR: modd A R B) (FF : funcd A F A') (RR' : modd A' R' B') (GG : funcd B G B'), TYPE ;
constant symbol transfd_Set : Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [F : func X X'] [G : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
(r : transf R F R' G) (RR: modd A R B) (FF : funcd A F A') (RR' : modd A' R' B') (GG : funcd B G B'), Set ;
rule τ (@transfd_Set $X $Y $X' $Y' $A' $A $B' $B $F $G $R' $R $r $RR $FF $RR' $GG) ↪ @transfd $X $Y $X' $Y' $A' $A $B' $B $F $G $R' $R $r $RR $FF $RR' $GG; 
   
 constant symbol Id_func : Π [A : cat], func A A;
 
 constant symbol moddu : Π [I : cat], catd I → catd I → TYPE ;
 
 constant symbol homdu: Π [I: cat] [A : catd I] [B : catd I] [II : catd I]
(FF : funcd II Id_func A) (RR : moddu A B) (GG : funcd II Id_func B), TYPE ;
 
 constant symbol transfdu: Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I], 
 moddu A B → funcd A Id_func A' → moddu A' B' → funcd B Id_func B' → TYPE ; 

 ///experimental grammatical topology covering (co)sieves, for sheaf cohomology
 constant symbol coveringu : Π [I : cat] [A : catd I] [B : catd I]
 (RR : moddu A B), funcs Id_func B → TYPE ;
 
 constant symbol covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [y : func I Y], funcs y B → TYPE ;

/* (B) cat ========================== */

injective symbol Op_cat : cat → cat;

symbol Pullback_cat : Π [U X Y : cat] (F : func X U) (G : func Y U), cat;

constant symbol Terminal_cat : cat;
//not as datatype; and both pullback and product required...
symbol Product_cat : Π (U : cat) (A : cat), cat; 

constant symbol Sigma_cat : Π [X : cat], catd X → cat;
constant symbol Pit_cat : Π [X Y : cat] (A : catd X) (F : func X Y) (B : catd Y), cat;


rule Op_cat (Op_cat $A) ↪ $A
with Op_cat (Terminal_cat) ↪ Terminal_cat ;

rule Product_cat $A Terminal_cat ↪  $A
with Product_cat Terminal_cat $A  ↪  $A
with Product_cat (Product_cat $A $B ) $C  ↪  Product_cat $A (Product_cat $B $C ) ;

/* (C) func ========================== */


//Subst_func
symbol ∘> : Π [A B C: cat], func A B → func B C → func A C;
notation ∘> infix left 90;
symbol <∘ [A B C: cat] : func B C → func A B → func A C ≔ λ G F, F ∘> G;
notation <∘ infix right 90;

rule $X ∘> ($G ∘> $H) ↪ ($X ∘> $G) ∘> $H
//($F ∘> $G) ∘> $H ↪ $F ∘> ($G ∘> $H)
with $F ∘> Id_func ↪ $F
with Id_func ∘> $F ↪ $F;

injective symbol Op_func : Π [A B: cat], func A B → func (Op_cat A) (Op_cat B);

rule Op_func (Op_func $F) ↪ $F
with Op_func Id_func ↪ Id_func
with Op_func ($F ∘> $G) ↪  ((Op_func $F) ∘> (Op_func $G));

symbol Pullback_fst_func : Π [U X Y : cat] (F : func X U) (G : func Y U), func (Pullback_cat F G) X;
symbol Pullback_snd_func : Π [U X Y : cat] (F : func X U) (G : func Y U), func (Pullback_cat F G) Y;

injective symbol Terminal_func :  Π (A : cat), func A Terminal_cat;

constant symbol Product_intro_func : Π [T X I : cat] (F : func I T) (G : func I X),
  func I (Product_cat T X);
constant symbol Product_fst_func : Π [T : cat] (X : cat) [T' : cat],
func T T' → func (Product_cat T X) T' ; 
constant symbol Product_snd_func : Π (T : cat) [X X': cat],
func X X' → func (Product_cat T X) X' ; 


rule (Product_fst_func $T $F) ∘> $H ↪ (Product_fst_func $T ($F ∘> $H))
with (Product_snd_func $T $F) ∘> $H ↪ (Product_snd_func $T ($F ∘> $H))
with $H ∘> (Product_intro_func $F $G) ↪ (Product_intro_func ($H ∘> $F) ($H ∘> $G));

rule (@Product_intro_func $T $X $I $F $G) ∘> (@Product_fst_func $T $X _ $H) ↪ $F ∘> $H 
with (@Product_intro_func $T $X $I $F $G) ∘> (@Product_snd_func $T $X _ $H) ↪ $G ∘> $H ;
//todo add extensionality? requires definable func symbols
 
//TODO: REVIEW THIS, NOT USED? ?ok semantic rule?
rule (Pullback_fst_func $F $G) ∘> $F ↪ (Pullback_snd_func $F $G) ∘> $G ;
symbol Pullback_func  [U X Y : cat] (F : func X U) (G : func Y U):
  func (Pullback_cat F G) U ≔ (Pullback_snd_func F G) ∘> G;


// this reversal of rewrite direction and symmetric versions of rewrites are required later at Total_func of @∘>d
// this rewrite direction will use associativity of ∘>
rule Pullback_cat (Pullback_snd_func $F $G) $H  ↪ Pullback_cat $F ($H ∘> $G)
with Pullback_cat $H (Pullback_fst_func $F $G) ↪  Pullback_cat ($H ∘> $F) $G ;
//symmetry
rule Pullback_cat $H (Pullback_snd_func $F $G)   ↪ Pullback_cat $F ($H ∘> $G)
with Pullback_cat (Pullback_fst_func $F $G) $H ↪  Pullback_cat ($H ∘> $F) $G ;

//TODO: REVIEW THIS associativity to right ?  NOT USED? 
// rule Pullback_cat (Pullback_snd_func $F $G) $H ↪ Pullback_cat $H (Pullback_snd_func $F $G)
//  with Pullback_cat $H (Pullback_fst_func $F $G)  ↪ Pullback_cat (Pullback_fst_func $F $G) $H ;

//reverse direction?
rule (Pullback_fst_func (Pullback_snd_func $F $G) $H) ∘> (Pullback_fst_func $F $G) ↪ Pullback_fst_func $F ($H ∘> $G) ;
rule (Pullback_snd_func $H (Pullback_fst_func $F $G)) ∘> (Pullback_snd_func $F $G) ↪ Pullback_snd_func ($H ∘> $F) $G;

rule @Pullback_cat $U $X $Y $F Id_func ↪ $X
with @Pullback_cat $U $X $Y Id_func $G ↪ $Y;
rule Pullback_fst_func $F Id_func ↪ Id_func;
rule Pullback_snd_func Id_func $G ↪ Id_func;

rule Pullback_fst_func ($H ∘> $F) $G ↪ (Pullback_fst_func $H (Pullback_fst_func $F $G));
rule Pullback_snd_func $F ($H ∘> $G) ↪ (Pullback_snd_func (Pullback_snd_func $F $G) $H);

rule Pullback_fst_func Id_func $F ↪ $F;
rule Pullback_snd_func $G Id_func ↪ $G;

//get only algebraic functor instead of universality
symbol Pullback_functor_func [U X Y : cat] (F : func X U) (G : func Y U) [Y'] (G' : func Y' Y)
 : func (Pullback_cat F (G' ∘> G)) (Pullback_cat F G)
   ≔  (Pullback_fst_func (Pullback_snd_func F G) G') ;

// naturality/functoriality is automatically derivable by computation
type λ F G H G', Pullback_functor_func F G (H ∘> G');  
//func (Pullback_cat F ((H ∘> G') ∘> G)) (Pullback_cat F G)
type λ F G H G', Pullback_functor_func F (G' ∘> G) H ∘> Pullback_functor_func F G G'; 
//func (Pullback_cat F (H ∘> (G' ∘> G))) (Pullback_cat F G)
assert  F G H G' ⊢ Pullback_functor_func F G (H ∘> G') ≡ 
        Pullback_functor_func F (G' ∘> G) H ∘> Pullback_functor_func F G G';
 
 rule Op_func (Terminal_func $A) ↪ (Terminal_func (Op_cat $A));
 
rule (@∘> $A $B $C $F (Terminal_func $B)) ↪ (Terminal_func $A) ; 

rule (Terminal_func (Terminal_cat)) ↪ Id_func;

/* (D) mod ========================== */

injective symbol Op_mod : Π [A B : cat], mod A B → mod (Op_cat B) (Op_cat A); //Tensor_mod;
 
constant symbol Unit_mod : Π [X A B : cat], func A X → func B X → mod A B;
 
 //TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR PULLBACK-PRODUCT OF FIBRATIONS
 constant symbol ⊗ : Π [A B X : cat], mod A B → mod B X → mod A X; //Tensor_mod;
 notation ⊗ infix left 70;
 
 //Imply_cov_mod
 constant symbol ⇐ : Π [A B X : cat], mod A B → mod X B → mod A X;
 notation ⇐ infix left 60;

 //Imply_con_mod
 constant symbol ⇒ : Π [A B X : cat], mod A X → mod A B → mod X B;
 notation ⇒ infix right 60;

 constant symbol Terminal_mod : Π (A B : cat), mod A B;

 rule Op_mod (Op_mod $A) ↪ $A
with Op_mod (Unit_mod $F $G) ↪   (Unit_mod (Op_func $G) (Op_func $F)) 
with Op_mod ( $R ⊗ $S ) ↪   (Op_mod $S) ⊗ (Op_mod $R)  
 with Op_mod ( $R ⇐ $S ) ↪   (Op_mod $S) ⇒ (Op_mod $R) 
 with Op_mod ( $R ⇒ $S ) ↪  (Op_mod $S) ⇐ (Op_mod $R)   ;

 //Subst_cov_mod
 symbol <<∘ : Π [A X C: cat], mod A X → func C X → mod A C;
 //Subst_con_mod
 symbol ∘>> : Π [X B C: cat], func C X → mod X B → mod C B;
 notation <<∘ infix left 80; notation ∘>> infix right 80;
 
 rule  (Unit_mod $F $G) <<∘ $K ↪ Unit_mod $F ($G <∘ $K) 
 with ($R ⊗ $S) <<∘ $G ↪ $R ⊗ ($S <<∘ $G)
 with ($R ⇐ $S) <<∘ $G ↪ $R ⇐ ($G ∘>> $S)
 with ($R ⇒ $S) <<∘ $G ↪ $R ⇒ ($S <<∘ $G);
 
 rule  $K ∘>> (Unit_mod $F $G) ↪ Unit_mod ($K ∘> $F) $G 
 with  $G ∘>> ($R ⊗ $S) ↪ ($G ∘>> $R) ⊗ $S
 with $G ∘>> ($R ⇒ $S) ↪ ($R <<∘ $G) ⇒ $S
 with $G ∘>> ($R ⇐ $S) ↪ ($G ∘>> $R) ⇐ $S;
 
 rule $R <<∘ Id_func ↪ $R 
// with $R <<∘ ($K ∘> $H  ) ↪ ($R <<∘ $H) <<∘ $K; 
  with ($R <<∘ $H) <<∘ $K ↪ $R <<∘ ($H <∘ $K); 
 
 rule Id_func ∘>> $R ↪ $R 
// with ($K ∘> $H) ∘>> $R  ↪  $K ∘>> ($H ∘>> $R); 
 with $K ∘>> ($H ∘>> $R) ↪ ($K ∘> $H) ∘>> $R; 
 
 rule ($F ∘>> $R) <<∘ $G ↪ ($F ∘>> ($R <<∘ $G));

rule Op_mod ($F ∘>> $R)  ↪ ((Op_mod $R) <<∘ (Op_func $F))
with Op_mod ($R <<∘ $G)  ↪ ((Op_func $G) ∘>> (Op_mod $R));


//CHANGED
rule Terminal_mod _ _ <<∘ $H ↪ Terminal_mod _ _
with $H ∘>> Terminal_mod _ _ ↪ Terminal_mod _ _;

 
/* (E) hom ========================== */

injective symbol Op_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] (r : hom F R G), hom (Op_func G) (Op_mod R) (Op_func F); 


//TODO: GENERALIZE TO (RELATIVE) MONADS AND MODULES, GET GENERAL VERSION OF CASTING (X0)_'∘> (Id_hom Y0) or Func_con_hom
//QUESTION: SHOULD HAVE PRIMITIVE SUCH CASTING OPERATION, WITH REDUCTIONS TO IT ?
constant symbol Id_hom : Π [A B : cat] (F : func B A),
hom F (Unit_mod Id_func Id_func ) F;

 // seems important to accumulate, especialy when the tests become actual rewrite rules
symbol Func_con_hom : Π [A B A' : cat] (Z : func A A') (F : func B A) ,
 hom F (Unit_mod Z Id_func) (Z <∘ F);
symbol Func_cov_hom : Π [A B A' : cat] (Z : func A A') (F : func B A) ,
 hom (F ∘> Z) (Unit_mod Id_func Z) F;

 rule Op_hom (Op_hom $A) ↪ $A
 with Op_hom (Id_hom $F) ↪ (Id_hom (Op_func $F))
 with Op_hom (Func_con_hom $Z $F) ↪ Func_cov_hom (Op_func $Z) (Op_func $F)
 with Op_hom (Func_cov_hom $Z $F) ↪ Func_con_hom (Op_func $Z) (Op_func $F);


 //todo reduce Terminal_mod Terminal_cat Terminal_cat to Unit_mod ?
 constant symbol Terminal_hom : Π [A B I : cat] (F : func I A) (G : func I B),  hom F (Terminal_mod A B) G;
 
 constant symbol Tensor_hom_hom  : Π [A  X I : cat] [P : mod A I] [Q : mod I X]
 [F : func I A] [G : func I X],
 hom F P Id_func → hom Id_func Q G → hom F (P ⊗ Q) G;
 
 rule (Op_hom (Tensor_hom_hom $p $q)) ↪ Tensor_hom_hom (Op_hom $q) (Op_hom $p); 

 injective symbol Lambda_cov_transf_hom : Π [A  X A'  : cat] [Q : mod A X] 
 [O : mod A' X]  [F : func A A'] ,
 transf Q  F O                     Id_func  →
 hom                       F (O ⇐ Q) Id_func;
 
  //Comp_func_hom
 symbol ∘↓ : Π [I A B I' : cat] [R : mod A B] [F : func I A] 
 [G : func I B], hom F R G → Π (X : func I' I), hom (X ∘> F) R (G <∘ X);
 notation ∘↓ infix left 120;
 
 rule $r ∘↓ Id_func ↪ $r
 //reverse direction?
 //with $r ∘↓ ($H <∘ $K) ↪ ($r ∘↓ $H) ∘↓ $K
 //with $r ∘↓ ($K ∘> $H  ) ↪ ($r ∘↓ $H) ∘↓ $K
 with ($r ∘↓ $H) ∘↓ $K ↪ $r ∘↓ ($K ∘> $H  )
 with (Id_hom $F) ∘↓ $H  ↪ Id_hom ($F <∘ $H)
 with (Func_con_hom $Z $F) ∘↓ $H  ↪ Func_con_hom $Z ($F <∘ $H)
 with (Func_cov_hom $Z $F) ∘↓ $H  ↪ Func_cov_hom $Z ($F <∘ $H); 
 
rule Op_hom ($r ∘↓ $H) ↪ (Op_hom $r) ∘↓ (Op_func $H); 
 
/* (F) transf ========================== */

injective symbol Op_transf :Π [X Y X' Y': cat]  [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y], 
 transf R xx' R' yy'  → transf (Op_mod R) (Op_func yy') (Op_mod R') (Op_func xx');

 constant symbol Id_transf : Π [A X : cat] (R : mod A X) ,
 transf R Id_func R Id_func;

 rule Op_transf (Op_transf $A) ↪ $A
 with Op_transf (Id_transf $R) ↪ (Id_transf (Op_mod $R)); 
 
// constant symbol Terminal_transf : Π [A B : cat] (R : mod A B), transf R (Terminal_func A) (Unit_mod Id_func Id_func) (Terminal_func B);
constant symbol Terminal_transf : Π [A B : cat] (R : mod A B), transf R Id_func (Terminal_mod A B) Id_func;

//TODO ERASE
constant symbol Unit_Tensor_cov_transf : Π [A B A' X : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] ,
transf P F P' Id_func → 
transf (P ⊗ (Unit_mod Id_func Id_func)) F P' Id_func;

constant symbol coyoneda_Unit_Tensor_cov_transf : Π [A B A' B' : cat] [P : mod A B] [P' : mod A' B'] [F : func A A'] [G : func B B'] ,
transf P F P' G → Π [J : cat] (N : func J B'),
transf ((⊗) P (Unit_mod G N)) F (P' <<∘ N) Id_func;
 //todo eval-lambda with unit, so between hom and transf 
 //todo eval-lambda dependent over —/Γ context? or prefixed under Γ⊗— context?
 injective symbol  Eval_cov_transf : Π [A B  X A'  : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X]  [F : func A A'] ,
 transf P                       F (O ⇐ Q) Id_func →
 transf (P ⊗ Q)  F O                     Id_func;
 
//TODO ALLOW OVER SPAN OF FUNC, SIMILAR AS FOR DEPENDENT MORPHISM OF FIBRATIONS
// THEREFORE TENSOR ABSORB THE SPAN WHICH WOULD REPLACE Id_func AND SOLVES EARLIER PROBLEMS
injective symbol Lambda_cov_transf : Π [A B  X A' : cat] [P : mod A B] [Q : mod B X] 
 [O : mod A' X]  [F : func A A'] ,
 transf (P ⊗ Q)  F O                     Id_func →
 transf P                       F (O ⇐ Q) Id_func;
 
 injective symbol Eval_cov_hom_transf : Π [A  X A' : cat] [Q : mod A X] 
 [O : mod A' X]  [F : func A A'] ,
 hom                       F (O ⇐ Q) Id_func →
 transf Q  F O                     Id_func;
 
//  constant symbol Tensor_cov_transf : Π [A' I X' A X: cat] [P' : mod A' I] [Q' : mod I X'] 
//  [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func X' X],
//  transf P' F P Id_func → transf Q' Id_func Q G →
//  transf (P' ⊗ Q') F (P ⊗ Q) G;
constant symbol Tensor_cov_transf : Π [A' I I' X' A X: cat] [P' : mod A' I'] [Q' : mod I' X'] 
[P : mod A I] [Q : mod I X] [F : func A' A]  [G : func X' X] , Π (M : func I' I),
transf P' F (P <<∘ M) Id_func →  transf ( Q') Id_func (M ∘>> Q) G →
transf ((⊗) P' Q') F ((⊗) P Q) G;

//rule Op_transf (Tensor_cov_transf $rr $ss) ↪ (Tensor_cov_transf (Op_transf $ss) (Op_transf $rr)); 
rule Op_transf (Tensor_cov_transf $M $rr $ss) ↪ (Tensor_cov_transf (Op_func $M) (Op_transf $ss) (Op_transf $rr)); 

 constant symbol Tensor_cov_hom_transf : Π [A' I A X: cat] [P' : mod A' I] 
 [P : mod A I] [Q : mod I X] [F : func A' A]  [G : func I X],
 transf P' F P Id_func → hom Id_func Q G →
 transf P' F (P ⊗ Q) G;
 
 constant symbol Imply_cov_transf : Π [A B A' C  : cat] [O : mod A B] [O' : mod A' B]
  [Q : mod C B] [Q' : mod C B] [F : func A A']  ,
 transf O F O' Id_func → transf Q Id_func Q' Id_func → 
 transf   (O ⇐ Q')
        F (O' ⇐ Q) Id_func;
 
 constant symbol Imply_cov_hom_transf : Π [A B A' C  : cat] [O : mod A B] [O' : mod A' B]
   [Q' : mod C B] [F : func A A']   [L : func C B],
 transf O F O' Id_func → hom Id_func Q' L → 
 transf   (O ⇐ Q')
        F O' L;
 
 
 // "J-rule" , admissible/eliminated until accumulation onto basic constructors
 //Unit_cov_transf
 injective symbol ∘>'_ : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 hom F R G → Π (N: func J B), transf (Unit_mod G N) F (R <<∘ N) Id_func;
 //Unit_con_transf
 injective symbol _'∘> : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
 Π (M : func J A), hom F R G → transf ( Unit_mod M F) Id_func (M ∘>> R) G;
 
 notation _'∘> infix right 80; notation ∘>'_ infix left 80;
 
rule Op_transf (($M)_'∘> $r) ↪ (Op_hom $r) ∘>'_ (Op_func $M);
rule Op_transf ($r ∘>'_ ($M)) ↪ (Op_func $M) _'∘> (Op_hom $r);

 // (substitution) admissible/eliminated until accumulation onto basic constructors
 //Comp_hom
 symbol '∘ : Π [A B' B I : cat] [S : mod A B'] [T : mod A B]
 [X : func I A] [Y : func I B']  [G : func B' B],
 hom X S Y → transf S Id_func T G → hom X T (G <∘ Y);
 notation '∘ infix right 80;
 
 symbol ∘' [A' B A I : cat] [S : mod A' B] [T : mod A B]
 [X : func I A'] [Y : func I B] [F : func A' A] :
 transf S F T Id_func → hom X S Y → hom (X ∘> F) T Y;
 notation ∘' infix left 80;

rule Op_hom ($s '∘ $st) ↪  (Op_transf $st) ∘' (Op_hom $s)
with Op_hom ($st ∘' $s) ↪  (Op_hom $s) '∘ (Op_transf $st);

 rule ($a '∘  $t) ∘↓ $Z ↪ (($a ∘↓ $Z) '∘  $t)
with ($t ∘' $a) ∘↓ $Z ↪ ($t ∘' ($a ∘↓ $Z)) ; //check SIMILAR RULE below possibly in reverse and re-correct
 
 //TODO: REVIEW no lack for Comp_transfd because it is always applied to Total_transf ? so no separate cut case analysis
 //Comp_transf
//  symbol ''∘ : Π [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
//  [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B],
//  transf R X S Y → transf S F T G → transf R (X ∘> F) T (G <∘ Y);
//  notation ''∘ infix right 80;
 
//  symbol ∘'' [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
//  [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B] :
//  transf S F T G → transf R X S Y → transf R (X ∘> F) T (G <∘ Y)
//    ≔ λ st rs, rs ''∘ st;
//  notation ∘'' infix left 80;
 

 symbol ''∘ [ B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
  [Y : func B'' B']  [G : func B' B] :
  transf R Id_func S Y → transf S Id_func T G →  transf R Id_func T (G <∘ Y);
  notation ''∘ infix right 80;
 
symbol ∘'' : Π [A'' A' B A  : cat] [R : mod A'' B] [S : mod A' B] [T : mod A B] 
[X : func A'' A'] [F : func A' A],
transf S F T Id_func → transf R X S Id_func → transf R (X ∘> F) T Id_func;
notation ∘'' infix left 80;

rule Op_transf ($rs ''∘ $st) ↪  (Op_transf $st) ∘'' (Op_transf $rs);
 rule Op_transf ($rs ∘'' $st) ↪  (Op_transf $st) ''∘ (Op_transf $rs);

 rule  $rs ''∘ ($st ''∘ $tu) ↪ ($rs ''∘ $st) ''∘ $tu
 with  ($tu ∘'' $st) ∘'' $rs ↪  $tu ∘'' ($st ∘'' $rs);

//  //ERASE
//  rule $rs ''∘ ($tu ∘'' $st) ↪  $tu ∘'' ($rs ''∘ $st) ;
//  rule ($st ''∘ $tu ) ∘'' $rs ↪  ($st ∘'' $rs) ''∘ $tu ;

 rule  (Id_transf _) ''∘ $r'r ↪ $r'r
 with  $r'r ''∘ (Id_transf _) ↪ $r'r;
 rule  (Id_transf _) ∘'' $r'r ↪ $r'r
 with  $r'r ∘'' (Id_transf _) ↪ $r'r;

 // assoc comp_transf then comp_hom
 //reverse?
 rule  $r '∘ ($rs ''∘ $st)
 ↪ ($r '∘ $rs) '∘ $st
 with ($st ∘'' $rs) ∘' $r
 ↪  $st ∘' ($rs ∘' $r);

// assert [A'' B'' A' B' A B : cat] [R : mod A'' B''] [S : mod A' B'] [T : mod A B] 
// [X : func A'' A'] [Y : func B'' B'] [F : func A' A] [G : func B' B]
// (rs : transf R X S Y) (st : transf S F T G) K (M' : func K A'') N'  (r : hom M' R N') ⊢ eq_refl _ : π (
//   r '∘ (rs ''∘ st)
//    = (r '∘ rs) '∘ st  );

// it is a metatheorem by cases induction that the associativity propositional-equation is derivable,
// and it must not be assumed as rewrite/conversion rule
 constant symbol associativity_con_metatheorem : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
 Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
 Π  (s : hom x R y), 
 Π   [K0] [F' : func K0 A] [x''x' : func I K0] (x''x'_ : hom x''x' (Unit_mod F' x) Id_func) , 
 π (( (( x''x'_ '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' y'y_  ) 
   =  (x''x'_ '∘ ((F')_'∘> ( (s ∘>'_(G)) ∘' y'y_ ))));
 
//TODO  constant symbol associativity_cov_metatheorem 


symbol <<∘1 : Π [X Y X' : cat] [F : func X X'] [R' : mod X' Y] [R : mod X Y] (r : transf R F R' Id_func) [Z : cat] (H : func Z Y), 
transf (R <<∘ H) F (R' <<∘ H) Id_func;
notation <<∘1 infix left 80;
rule  ($r ∘>'_($N)) <<∘1 $H ↪ $r ∘>'_($N <∘ $H);
rule $t <<∘1 Id_func ↪ $t 
with ($t <<∘1 $H) <<∘1 $K ↪ $t <<∘1 ($H <∘ $K); 

symbol 1∘>> : Π [X Y Y' : cat] [G : func Y Y'] [R' : mod X Y'] [R : mod X Y] [Z : cat] (H : func Z X) (r : transf R Id_func R' G) , 
transf (H ∘>> R) Id_func (H ∘>> R') G;
notation 1∘>> infix right 80;
rule  $H 1∘>> (($M) _'∘> $r ) ↪ ($H ∘> $M) _'∘> $r;
rule Id_func 1∘>>  $t  ↪ $t 
with $K 1∘>> ($H 1∘>> $t) ↪ ($K ∘> $H) 1∘>> $t; 

rule ($F 1∘>> $t) <<∘1 $G ↪ ($F 1∘>> ($t <<∘1 $G));

rule (Tensor_cov_transf $M $t $s) <<∘1 $H ↪ (Tensor_cov_transf $M $t ($s <<∘1 $H))
with $H 1∘>> (Tensor_cov_transf $M $t $s) ↪ (Tensor_cov_transf $M ($H 1∘>> $t) $s);
rule  (Id_transf $R) <<∘1 $K ↪ Id_transf ($R <<∘ $K) 
with $K 1∘>> (Id_transf $R) ↪  (Id_transf ($K ∘>> $R)) ;

symbol subst_Imply_cov_mod : 
Π [A B X : cat] [R : mod A B] [W : mod X B]
[I] (Z : func I B),
transf (R ⇐ W) Id_func ((R <<∘ Z) ⇐ (W <<∘ Z)) Id_func ≔
begin
  assume A B X R W I Z;
  refine (Lambda_cov_transf _);
  refine ( (Eval_cov_transf (Id_transf _)) <<∘1 Z);
end;

// covariant yoneda action by cone of arrows, including functor image of cone  (remember: covariant yoneda action = contravariant yoneda embedding...)
injective symbol comp_Imply_cov_mod : Π [I A B J : cat] [F : func I A] [R : mod A B] [G : func I B],
hom F R G → Π [K : cat] [N: func K B] [W : mod J K], 
transf ((Unit_mod G N) ⇐ W) F ((R <<∘ N) ⇐ W) Id_func  ≔
begin
assume I A B J F R G h K N W;
refine (Lambda_cov_transf _);
refine ( (h ∘>'_(N)) ∘'' (Eval_cov_transf (Id_transf _))  );
end;


//TODO replaced this by multiple equations
 rule Func_con_hom Id_func $F ↪ (Id_hom $F)
 with Func_cov_hom Id_func $F ↪ (Id_hom $F);

rule  (Func_cov_hom _ $G ) '∘ ((_) _'∘> Id_hom $F) ↪ Id_hom ($G ∘> $F);
rule  (Id_hom $F ∘>'_ (_) ) ∘' (Func_con_hom _ $G )  ↪ Id_hom ($G ∘> $F);
//TODO: REVIEW NECESSITY OF ID_HOM. both cov id and con id without id_hom are ok because would never mix anyway ?
// or maybe formulation where all converge to id noop only in applied form ?
rule  ($f '∘ ($M)_'∘> (Id_hom Id_func) )  ↪ $f;  
//WARNING slow in transf formulation
//WARNING rule ($M)_'∘> (Id_hom Id_func)  ↪ (Id_transf _);
// rule  ($f '∘ ($M)_'∘> (Func_con_hom Id_func Id_func) ) ↪ $f  ;
// rule  ($f '∘ ($M)_'∘> (Func_cov_hom Id_func Id_func) ) ↪ $f  ;
rule  (($M)_'∘> (Func_cov_hom $F Id_func) ) ↪ (Id_transf _)  ; 
rule  ((Func_con_hom $F Id_func) ∘>'_($M)) ↪ (Id_transf _)  ;


 // idhom ''∘ funchom = idhom
 rule (($M)_'∘> ((Func_con_hom $F $Z)) ) ''∘ (($M ∘> $F)_'∘> (Func_con_hom $F' Id_func)) 
 ↪ (($M)_'∘> ((Func_con_hom ($F ∘> $F') $Z))) ; 
 
assert [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ⊢ eq_refl _ : π (

 ((M)_'∘> ((Func_con_hom F Z)) ) ''∘ ((M ∘> F)_'∘> (Func_con_hom F' Id_func)) 
 = ((M)_'∘> ((Func_con_hom (F ∘> F') Z))) ); 
 // : ransf (Unit_mod M (Z ∘> Id_func)) (Id_func ∘> Id_func) ((M ∘> F) ∘>> Unit_mod F' Id_func) (F' <∘ (F <∘ Z))
 

 
//yoneda bijection half
 // j-rule then applied to id_hom, both cov and con
 //  todo solved, erase this comment: note for confluence that already exists another rewrite that jrule of restr 
 rule (((Func_cov_hom $F $Z)) '∘ ((Id_func)_'∘> $r)) 
  ↪ $r ∘↓ $Z;

assert [I A B : cat] [F : func I A] [R : mod A B] [G : func I B]
 (r : hom F R G ) J (Z : func J _ ) ⊢ eq_refl _ : π (

   (((Func_cov_hom F Z)) '∘ ((Id_func)_'∘> r)) 
 = r ∘↓ Z  );

//yoneda bijection half
// SOLVED: now can  solve $Z ∘> $dom_t ≡ $Z
rule (Id_func)_'∘> (((Func_cov_hom $Z Id_func)) '∘ $t) 
  ↪ $t;

  assert [B : cat] I (M : func I B) f ⊢ eq_refl _ : π ( //note as transf fail because reduction to Id_hom
  (f '∘ (M)_'∘> (Func_con_hom Id_func Id_func) )  = f  );
  
 //todo: derivable restr ?
 // type λ [A B : cat] (F : func B A) B' (Z : func B' B) I (M : func I B) C (F' : func A C) ,
 // ((M)_'∘> ((Func_con_hom F) ∘↓ Z) ) ;
 
 // id_cov_hom on id_func is id_transf
 //nope todo erase see id_hom
//  rule  (($M)_'∘> (Func_con_hom Id_func Id_func) )
// ↪ (Id_transf _)  ;
//  assert [B : cat] I (M : func I B) ⊢ eq_refl _ : π (
//  ((M)_'∘> (Func_con_hom Id_func Id_func) )
//  = (Id_transf (Unit_mod M Id_func))  );

/* (G) limit_cov ========================== */

 // inductive transf
 injective symbol Op_limit_con : Π  [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
 (isl : limit_cov F W F_⇐_W), limit_con (Op_func F) (Op_mod W) (Op_func F_⇐_W); 
 injective symbol Op_limit_cov : Π  [B J J' : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
 (isl : limit_con F W W_⊗_F), limit_cov (Op_func F) (Op_mod W) (Op_func W_⊗_F);

 rule Op_limit_con (Op_limit_cov $isl) ↪ $isl
 with Op_limit_cov (Op_limit_con $isl) ↪ $isl ;
 
injective symbol limit_cov_univ_transf : Π  [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
 (isl : limit_cov F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (((Unit_mod M F)) ⇐ W) Id_func (Unit_mod M F_⇐_W) Id_func;

injective symbol limit_con_univ_transf : Π  [B J J' : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
 (isl : limit_con F W W_⊗_F), Π [I : cat] (M : func I B),
 transf (W ⇒ ((Unit_mod F M ))) Id_func (Unit_mod W_⊗_F M) Id_func;

 injective symbol limit_cov_cone_transf : Π  [B J J' : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
 (isl : limit_cov F W F_⇐_W), Π [I : cat] (M : func I B),
 transf (Unit_mod M F_⇐_W) Id_func (((Unit_mod M F)) ⇐ W) Id_func;

 //naturality
rule ($Z)_'∘> ($h '∘ limit_cov_cone_transf $isl $M) 
↪ (($Z)_'∘> $h) ''∘ limit_cov_cone_transf $isl ($Z ∘> $M);
rule ($Z)_'∘> ($f '∘  (limit_cov_univ_transf $isl $M)) 
↪  ( (_)_'∘> $f ) ''∘ (limit_cov_univ_transf $isl ($Z ∘> $M));

//beta
rule (limit_cov_cone_transf $isl $M) ∘'' (limit_cov_univ_transf $isl $M) ↪ Id_transf _ ;
//eta
rule (limit_cov_univ_transf $isl $M) ∘'' (limit_cov_cone_transf $isl $M)  ↪ Id_transf _ ;

rule Op_transf (Op_transf $A) ↪ $A
with (Op_transf (limit_cov_univ_transf $isl $M) ) ↪ limit_con_univ_transf (Op_limit_con $isl) (Op_func $M);
 
//  /* (1) ========================== */
 
 // naturality and dinaturality of evaluation
 
//  rule  (Eval_cov_transf $pq_o) ∘'' (Tensor_cov_transf $p'p $q'q)
//    ↪ Eval_cov_transf ((Imply_cov_transf (Id_transf _) $q'q) ∘'' ($pq_o ∘'' $p'p)); 
rule  (Eval_cov_transf $pq_o) ∘'' (Tensor_cov_transf $M $p'p $q'q)
↪ Eval_cov_transf ((Imply_cov_transf (Id_transf _) $q'q) ∘'' (($pq_o <<∘1 $M) ∘'' $p'p)); 

rule Lambda_cov_transf_hom (Eval_cov_hom_transf $t) ↪ $t;
//beta
rule (Eval_cov_hom_transf (Lambda_cov_transf_hom $t)) ↪ $t;
//eta
rule Lambda_cov_transf (Eval_cov_transf $t) ↪ $t;
//beta
rule (Eval_cov_transf (Lambda_cov_transf $t)) ↪ $t;

//  assert [A B X A' X' : cat] [P : mod A B] [Q : mod B X] 
//  (O : mod A' X')  [F : func A A'] (L : func X X')
//  (pq_o : transf P                       F (⇐ O L Q) Id_func)
//  A0  X0 (M: func A0 A)  (Z : func X0 X) 
//  (P': mod A0 B) (Q' : mod B X0) 
//  (p'p : transf P' M P Id_func) (q'q : transf Q' Id_func Q Z) ⊢ eq_refl _ : π (
//  (Eval_cov_transf  pq_o)  ∘'' (Tensor_cov_transf p'p q'q)
//  = Eval_cov_transf  ((pq_o ∘'' p'p) ''∘ (Imply_cov_transf (Id_transf O) L q'q)) ); 

//TODO as rewrite rule
//  type λ [A X A' X' : cat] [Q : mod A X] 
//  (O : mod A' X')  [F : func A A'] (L : func X X')
//  (pq_o : hom                       F (⇐ O L Q) Id_func)
//   X0  (Z : func X0 X) 
//   (Q' : mod A X0) 
//   (q'q : transf Q' Id_func Q Z),
//  (Eval_cov_hom_transf  pq_o)  ∘'' q'q
// = Eval_cov_hom_transf  (pq_o '∘ (Imply_cov_transf (Id_transf O) L q'q)); 
 
 // evaluation of coyoneda at identity hom
 
 type λ [A B A' : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] 
 (pp : transf P F P' Id_func),
 (Unit_Tensor_cov_transf pp)  ∘'' (Tensor_cov_hom_transf (Id_transf P) (Func_cov_hom Id_func Id_func))
  = pp;
 // transf P (Id_func ∘> F) P' (Id_func <∘ Id_func)
 
 
 rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘'' (Tensor_cov_hom_transf $qq (Func_con_hom _ _))
 ↪  $pp ∘'' $qq;
 rule (coyoneda_Unit_Tensor_cov_transf $pp _)  ∘'' (Tensor_cov_hom_transf $qq (Id_hom _))
 ↪  $pp ∘'' $qq;

 assert [A B A' : cat] [P : mod A B] [P' : mod A' B] [F : func A A'] 
 (pp : transf P F P' Id_func )  A0 (Q: mod A0 B) H (qq : transf Q H P Id_func ) ⊢ eq_refl _ : π(
(coyoneda_Unit_Tensor_cov_transf pp Id_func)  ∘'' (Tensor_cov_hom_transf qq (Func_con_hom _ _))
 =  pp ∘'' qq  ); 

 // functos and adjunctions 
 
 constant symbol Adj_cov_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), Π [I] (Z : func I L) [J] (M : func J I),
 hom (M ∘> (Z ∘> RAdj_func)) (Unit_mod LAdj_func Z) M;

constant symbol Adj_con_hom : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func), Π [I] (Z : func I R) [J] (N : func J I),
hom N (Unit_mod Z RAdj_func) (N ∘> (Z ∘> LAdj_func));

rule (Adj_cov_hom $aj $Z $N) ∘↓ $X ↪ Adj_cov_hom $aj $Z ($N <∘ $X);
rule (Adj_con_hom $aj $Z $N) ∘↓ $X ↪ Adj_con_hom $aj $Z ($X ∘> $N);

 injective symbol Op_adj : Π [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func), adj (Op_func RAdj_func) (Op_func LAdj_func);
 
 rule Op_adj (Op_adj $aj) ↪ $aj;
 
 rule Op_hom (Adj_cov_hom $aj $Z $X) ↪ Adj_con_hom (Op_adj $aj) (Op_func $Z) (Op_func $X);



 /* (6) misc ========================== */
 
 
 
 /* (2) ========================== */
 
 // accumulation
 
//accumulation contravariant ; accumulation not really naturality, therefore can be dealt with generically
 // t∘(g) ∘X0 -  =  t∘(g ∘X0 -) 
 rule ($M)_'∘> ($g '∘ (($X0)_'∘> $t))
 ↪ (($M)_'∘> $g) ''∘ (($M ∘> $X0)_'∘> $t)
 with  (($t ∘>'_ ($X0) ∘' $g)) ∘>'_($M)
 ↪  ($t ∘>'_($M ∘> $X0)) ∘'' ($g ∘>'_($M));

 assert [L R J I I' I1 : cat] [T : mod R L]
 [Y0 : func I1 R] [Y: func I' I1] [Z : func I1 L]
 (M : func J I) [X: func I' I] (X0: func I R) 
 (t : hom Y0 T Z)
 (g : hom X (Unit_mod X0 Y0) Y) ⊢ eq_refl _ : π (

 (M)_'∘> (g '∘ ((X0)_'∘> t))
 = ((M)_'∘> g) ''∘ ((M ∘> X0)_'∘> t)    );

assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) [I] (Z : func I R)
  [J I1 I2 : cat] (X: func J I1) (X0: func I1 I) (Y: func J I2) (Y0 : func I2 I) 
  (g : hom X (Unit_mod X0 Y0) Y) J' (M: func J' I1) ⊢ eq_refl _ : π (

 (M)_'∘>  (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0)))
  =  ((M)_'∘>  g) ''∘ ((M ∘> X0)_'∘> (Adj_con_hom aj Z Y0)) );
 
//small todo: assert that accumulation for functors was well registered

//accumulation  covariant ; accumulation not really naturality, therefore can be dealt with generically
 //  - ∘X0 (g)∘t   =  (- ∘X0 g)∘t 
//  rule  ($g '∘ ($t ∘>'_($X0))) ∘>'_($M)
//  ↪ ($t ∘>'_($X0 <∘ $M)) ∘'' ($g ∘>'_($M));
 rule  (($t ∘>'_($X0)) ∘' $g) ∘>'_($M)
 ↪ ($t ∘>'_($X0 <∘ $M)) ∘'' ($g ∘>'_($M));

assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) [I] (Z : func I R)
 [J I1 I2 : cat] (X: func J I1) (X0: func I1 I) (Y: func J I2) (Y0 : func I2 L) 
 (g : hom X (Unit_mod (X0 ∘> (Z ∘> LAdj_func)) Y0) Y) J' (M: func J' I2) ⊢ eq_refl _ : π (

    (((Adj_con_hom aj Z X0) ∘>'_(Y0)) ∘' g) ∘>'_(M)
 =   ((Adj_con_hom aj Z X0) ∘>'_(Y0 <∘ M)) ∘'' (g ∘>'_(M)) );


 /* (2') ========================== */
 
 // naturality

//TODO: ERASE this is actual naturality where commuation occurs, not mere accumulation, therefore canNOT be dealt with generically
//  symbol naturality2_con_cov : Π [L I : cat] [Z_LAdj_func : func I L] [Unit_mod_Z_RAdj_func : mod I L]
//  (Adj_con_hom_Z : hom Id_func Unit_mod_Z_RAdj_func Z_LAdj_func)
//   [J I1 I2 : cat] [X: func J I1] (X0: func I1 I) [Y: func J I2] (Y0 : func I2 I) 
//   (g : hom X (Unit_mod X0 Y0) Y) [J' : cat] (N : func J' I), /* N is more general */
 
//   (g '∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ Y0))) ∘>'_(Id_func)
//      ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func)) ∘↓ N))
//   = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
//             ''∘ ((X0)_'∘> ((Adj_con_hom_Z) ∘↓ N)) ;

// naturality (unit, covariant eq),  similar with naturality (counit, contravariant eq)
// rule 
//WARNING subtle, g must be (hom Id_func _ _)
//        (@'∘ _ _ _ _ _ _ _ $Y _ $g  (($X0)_'∘> ((@Adj_con_hom _ _ $LAdj_func _ $aj _ $Z _ $Y0)))) ∘>'_(Id_func)
//        ∘'' (( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z ∘> $LAdj_func) $N)))
//   ↪  (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_ ($N))
//    ''∘ (($X0)_'∘> ((Adj_con_hom $aj $Z $N) ));
rule
(( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z ∘> $LAdj_func) $N))) ''∘
((@'∘ _ _ _ _ _ _ _ $Y _ $g  (($X0)_'∘> ((@Adj_con_hom _ _ $LAdj_func _ $aj _ $Z _ $Y0)))) ∘>'_(Id_func))
       
  ↪  (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_ ($N))
   ''∘ (($X0)_'∘> ((Adj_con_hom $aj $Z $N) ));
type cat;
 
         
// assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R] [aj : adj LAdj_func RAdj_func] [I] [Z : func I R]
//  [J I1 I2 : cat] [X: func J I1] [X0: func I1 I] [Y: func J I2] [Y0 : func I2 I] 
//  [g : hom X (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : π (

//  (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0))) ∘>'_(Id_func)
//     ∘''  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z ∘> LAdj_func) N)))
//  = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
//            ''∘ ((X0)_'∘> (Adj_con_hom aj Z N)) );
assert [L R : cat] [LAdj_func : func R L] [RAdj_func : func L R] [aj : adj LAdj_func RAdj_func] [I] [Z : func I R]
 [J I2 : cat]  [X0: func J I] [Y: func J I2] [Y0 : func I2 I] 
 [g : hom Id_func (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : π (

 (( (Y ∘> Y0)_'∘> (Func_con_hom (Z ∘> LAdj_func) N)))
  ''∘ (g '∘ ((X0)_'∘> (Adj_con_hom aj Z Y0))) ∘>'_(Id_func)  
 = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
           ''∘ ((X0)_'∘> (Adj_con_hom aj Z N)) );
 
//functoriality/naturality covariant     
// rule  
//   (@'∘ _ _ _ _ _ _ _ $Y _ $g   (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $Y0)))) ∘>'_(Id_func)
//   ∘'' (( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z_LAdj_func) $N)))
// ↪ (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_($N))
//        ''∘ (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $N))) ;
rule  
(( ($Y ∘> $Y0)_'∘> (Func_con_hom ($Z_LAdj_func) $N)))
  ''∘ ((@'∘ _ _ _ _ _ _ _ $Y _ $g   (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $Y0)))) ∘>'_(Id_func))
↪ (($g '∘ (($X0)_'∘> (Id_hom $Y0))) ∘>'_($N))
       ''∘ (($X0)_'∘> ((Func_con_hom $Z_LAdj_func $N))) ;

assert  [L I : cat] [Z_LAdj_func : func I L]
  [J I1 I2 : cat] [X0: func J I] [Y: func J I2] [Y0 : func I2 I] 
  [g : hom Id_func (Unit_mod X0 Y0) Y] [J' : cat] [N : func J' I] ⊢ eq_refl _ : π (
 
  (( (Y ∘> Y0)_'∘> (Func_con_hom (Z_LAdj_func) N)))
  ''∘ ((g '∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func Y0)))) ∘>'_(Id_func))
 = ((g '∘ ((X0)_'∘> (Id_hom Y0))) ∘>'_(N))
            ''∘ ((X0)_'∘> ((Func_con_hom Z_LAdj_func N))) );
 
//small todo: functoriality/naturality contravariant
 

 
// naturality (counit, covariant eq),   similar with naturality (unit, contravariant eq)
// rule ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L) 
// ↪ (($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L))
//           ''∘ (($M)_'∘> (Adj_cov_hom $aj ($N <∘ $L) Id_func)) ;
rule ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L) 
↪ (($M)_'∘> (Adj_cov_hom $aj ($N <∘ $L) Id_func)) ∘''
(($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L))  ;

assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
  [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
  [C''] [L : func C'' C']   ⊢ eq_refl _ : π (

 (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L) 
= ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) ∘''
  ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L))    );

// //TODO REVIEW IF SHOULD BE THIS REVERSED DIRECTION? nope rule redex has patterns, not registered, assertion fails
// rule (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ ($N <∘ $L) _ Id_func)) ∘''
// (($d '∘ (($M)_'∘> (Func_cov_hom ($G <∘ $N) $X))) ∘>'_($L))
// ↪ ($d '∘ (($M)_'∘> (@Adj_cov_hom _ _ $F $G $aj _ $N _ $X))) ∘>'_($L)           ;
// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
//   [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
//   [C''] [L : func C'' C']   ⊢ eq_refl _ : π (
// ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) ∘''
//   ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L))
// = (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L)  );


// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] [C'] [N : func C' C] [I] [X : func I C']
//   [E] [M : func E D] [J] [Z : func J E] [Y : func J I] (d : hom Z (Unit_mod M ((G <∘ N) <∘ X)) Y)
//   [C''] [L : func C'' C']   ⊢ eq_refl _ : π (

// (d '∘ ((M)_'∘> (Adj_cov_hom aj N X))) ∘>'_(L) 
// = ((d '∘ ((M)_'∘> (Func_cov_hom (G <∘ N) X))) ∘>'_(L))
//           ''∘ ((M)_'∘> (Adj_cov_hom aj (N <∘ L) Id_func)) );


//  /* (3) ========================== */
 
 // adjunction inverses beta cancellation

 // simple instance version , besides general version because no eta expansion of ϕ into (1)∘ϕ ...
 // “ϕ∘F(“G(f)∘γ”)”  =                  id∘1( 1(-)∘F ) 
 rule  (((@Adj_con_hom _ _ $LAdj_func $RAdj_func $aj _ $Z _ $M)) ∘>'_($N ∘> $W)) 
 ''∘ (($Z)_'∘> ((Adj_cov_hom $aj $W $N)))
↪  (((Func_con_hom ($Z ∘> $LAdj_func) $M)) ∘>'_($N ∘> $W) ) 
  ''∘ (($Z ∘> $LAdj_func)_'∘> ((Func_cov_hom $W $N)));
///WARNING M must be Id_func by new ''∘
// assert [L R I J I0 J0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
// (aj : adj LAdj_func RAdj_func) (Z : func I0 R) (M : func I I0)  (N : func J J0) (W: func J0 L) ⊢ eq_refl _ : π (
// (((Adj_con_hom aj Z M)) ∘>'_(N ∘> W)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj W N)))
// = (((Func_con_hom (Z ∘> LAdj_func) M)) ∘>'_(N ∘> W) ) ''∘ ((Z ∘> LAdj_func)_'∘> ((Func_cov_hom W N)))  );
// // : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) (N ∘> W)) M (Unit_mod (Z ∘> LAdj_func) W) N
assert [L R I J J0 : cat] [LAdj_func : func R L] [RAdj_func : func L R]
(aj : adj LAdj_func RAdj_func) (Z : func I R) (N : func J J0) (W: func J0 L) ⊢ eq_refl _ : π (
(((Adj_con_hom aj Z Id_func)) ∘>'_(N ∘> W)) ''∘ ((Z)_'∘> ((Adj_cov_hom aj W N)))
= (((Func_con_hom (Z ∘> LAdj_func) Id_func)) ∘>'_(N ∘> W) ) ''∘ ((Z ∘> LAdj_func)_'∘> ((Func_cov_hom W N)))  );
// : transf (Unit_mod (M ∘> (Z ∘> LAdj_func)) (N ∘> W)) M (Unit_mod (Z ∘> LAdj_func) W) N

// general version  SLOW HEAVY RULE - COMMENT THIS RULE DURING DEV, UNCOMMENT BEFORE COMPILATION (time lambdapi check -c test.lp)
 // f“ϕ∘F(“G(-)∘γ”g)”  =                  f"id∘1"( "1(-)∘F"g ) 
 //WARNING g must be (hom Id_func _ _)
rule  (($g '∘ (($M')_'∘> (@Adj_con_hom _ _ $F $G $aj _ $M _ $Y))) ∘>'_($X' ∘> $X ∘> $N)) 
           ''∘ (($M' ∘> $M)_'∘> (@∘' _ _ _ _ _ _ $X' _ _ ((Adj_cov_hom $aj $N $X) ∘>'_($N')) $f))
↪ (($g '∘ ($M')_'∘> (Func_con_hom ($M ∘> $F) $Y)) ∘>'_($N <∘ $X <∘ $X')) 
           ''∘ (($M' ∘> $M ∘> $F)_'∘> ((Func_cov_hom $N $X) ∘>'_($N') ∘' $f));
assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] 
[C'] [N : func C' C] [I] [X : func I C']
[C''] [N' : func C'' C'] [I'] [X' : func I' I] [Z : func I' C''] (f : hom X' (Unit_mod X N') Z)
[D'] [M : func D' D] [J] [Y : func J D']
[D''] [M' : func D'' D'] [Y' : func D'' J]  (g : hom Id_func (Unit_mod M' Y) Y')   ⊢ eq_refl _ : π (

 ((g '∘ (M')_'∘> (Adj_con_hom aj M Y)) ∘>'_(N <∘ X <∘ X')) 
      ''∘ ((M' ∘> M)_'∘> ((Adj_cov_hom aj  N X) ∘>'_(N') ∘' f))
 =  ((g '∘ (M')_'∘> (Func_con_hom (M ∘> F) Y)) ∘>'_(N <∘ X <∘ X')) 
      ''∘ ((M' ∘> M ∘> F)_'∘> ((Func_cov_hom N X) ∘>'_(N') ∘' f))  );
//  : transf (Unit_mod (Y' ∘> (Y ∘> (M ∘> F))) (N <∘ X <∘ X'))  W (Unit_mod (M' ∘> M ∘> F) (N <∘ N')) Z
// assert [C D : cat] [F : func D C] [G : func C D] [aj : adj F G] 
// [C'] [N : func C' C] [I] [X : func I C']
// [C''] [N' : func C'' C'] [I'] [X' : func I' I] [Z : func I' C''] (f : hom X' (Unit_mod X N') Z)
// [D'] [M : func D' D] [J] [Y : func J D']
// [D''] [M' : func D'' D'] [J'] [Y' : func J' J] [W : func J' D''] (g : hom W (Unit_mod M' Y) Y')   ⊢ eq_refl _ : π (

//  ((g '∘ (M')_'∘> (Adj_con_hom aj M Y)) ∘>'_(N <∘ X <∘ X')) 
//       ''∘ ((M' ∘> M)_'∘> ((Adj_cov_hom aj  N X) ∘>'_(N') ∘' f))
//  =  ((g '∘ (M')_'∘> (Func_con_hom (M ∘> F) Y)) ∘>'_(N <∘ X <∘ X')) 
//       ''∘ ((M' ∘> M ∘> F)_'∘> ((Func_cov_hom N X) ∘>'_(N') ∘' f))  );
// //  : transf (Unit_mod (Y' ∘> (Y ∘> (M ∘> F))) (N <∘ X <∘ X'))  W (Unit_mod (M' ∘> M ∘> F) (N <∘ N')) Z

//TODO REVIEW THIS ALT DIRECTION ... same problem of Id_func for $f
// rule   (($M' ∘> $M)_'∘> (@∘' _ _ _ _ _ _ $X' _ _ ((Adj_cov_hom $aj $N $X) ∘>'_($N')) $f)) ∘''
//           (($g '∘ (($M')_'∘> (@Adj_con_hom _ _ $F $G $aj _ $M _ $Y))) ∘>'_($X' ∘> $X ∘> $N))
// ↪   (($M' ∘> $M ∘> $F)_'∘> ((Func_cov_hom $N $X) ∘>'_($N') ∘' $f)) ∘''
//          (($g '∘ ($M')_'∘> (Func_con_hom ($M ∘> $F) $Y)) ∘>'_($N <∘ $X <∘ $X'));


// beta cancelation, covariant eq   (small todo: general version “(f)∘ϕ∘F(“γ∘(-)”)”)
 // “ϕ∘F(“γ∘(g)”)” =            “1∘F(g)”   

rule  ( ($M)_'∘> ((@Adj_con_hom _ _ $LAdj_func $RAdj_func  $aj _ $Z _ $N)) )
     ''∘ ( ($M ∘> $Z )_'∘> (Adj_cov_hom $aj Id_func Id_func) )
↪ ( ($M)_'∘> ((Func_con_hom ($Z ∘> $LAdj_func) $N)) ); 

assert [L R I J : cat] [LAdj_func : func R L] [RAdj_func : func L R]
 (aj : adj LAdj_func RAdj_func) Z (N : func I R) (M : func J R)  ⊢ eq_refl _ : π (

 ( (M)_'∘> ((Adj_con_hom aj Z N)) )   ''∘ ( (M ∘> Z )_'∘> (Adj_cov_hom aj Id_func Id_func) )
=  ( (M)_'∘> ((Func_con_hom (Z ∘> LAdj_func) N)) ) ); 
 // : transf (Unit_mod M N) Id_func (Unit_mod (M ∘> (Z ∘> LAdj_func)) Id_func) ((Z ∘> LAdj_func) <∘ N)
 
 
//  /* (4) ========================== */
 
//  // right adjoint preserves weighted limit_covs
 

  symbol righ_adjoint_preserves_limit_cov  [B J J' A : cat]  [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
  (isl : limit_cov F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) :
  transf ((Unit_mod M (F ∘> R)) ⇐ W) Id_func (Unit_mod M R <<∘ F_⇐_W) Id_func
  ≔ ((Adj_con_hom isa M Id_func) ∘>'_(F_⇐_W)) ∘''
  ((limit_cov_univ_transf isl (M ∘> L)) ∘'' (Imply_cov_transf ((M)_'∘> Adj_cov_hom isa F Id_func) (Id_transf W)) )
  ;

// assert [B J0 J J' A : cat] [K : func J J0] [W : mod J' J] [F : func J0 B] [F_⇐_W : func J' B]
// (isl : limit_cov K F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
// Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
// transf (⇒ (Op_mod W) (Op_func K) ((Op_func F ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M))) 
//          Id_func ((Op_func F_⇐_W ∘> Op_func R) ∘>> (Unit_mod0 (Op_cat A) <<∘ Op_func M)) Id_func;
assert [B J J' A : cat] [W : mod J' J] [F : func J B] [F_⇐_W : func J' B]
(isl : limit_cov F W F_⇐_W) [R : func B A] [L : func A B] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov isl isa M) :
transf ((Op_mod W) ⇒ ( (Unit_mod (Op_func F ∘> Op_func R) (Op_func M)))) 
         Id_func ((Unit_mod (Op_func F_⇐_W ∘> Op_func R) (Op_func M))) Id_func;

assert [B J J' A : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
(isl : limit_con F W W_⊗_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) ⊢
Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M)) :
transf (Op_mod ((Unit_mod (Op_func M) (Op_func F ∘> Op_func L)) ⇐ (Op_mod W)))
   (Op_func Id_func) (Op_mod (Unit_mod (Op_func M) (Op_func L) <<∘ Op_func W_⊗_F)) (Op_func Id_func) ;

symbol left_adjoint_preserves_limit_con [B J J' A : cat] [W : mod J J'] [F : func J B] [W_⊗_F : func J' B]
(isl : limit_con F W W_⊗_F) [R : func A B] [L : func B A] (isa : adj L R) [I : cat] (M : func I A) :
  transf (W ⇒ (Unit_mod (F ∘> L) M)) Id_func (W_⊗_F ∘>> Unit_mod L M) Id_func
  ≔ Op_transf (righ_adjoint_preserves_limit_cov (Op_limit_cov isl) (Op_adj isa) (Op_func M));

//  /* (5) ========================== */
 
//  // concrete example and inductive data type
 
//OK ONR
symbol join_cat : Π (A B : cat), cat;
symbol join_fst_func : Π (A B : cat), func A (join_cat A B);
symbol join_snd_func : Π (A B : cat), func B (join_cat A B);
symbol join_hom :  Π (A B : cat) [I : cat] (a : func I A) (b : func I B), hom a (Unit_mod (join_fst_func A B) (join_snd_func A B)) b ;

rule @'∘ _ _ _ _ _ _ $a' Id_func _ $r (( Id_func ) _'∘> (join_hom $A $B $a $b)) ↪ (join_hom $A $B $a' $b);
assert (A B : cat) [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) ⊢ 
        eq_refl _  : π (r  '∘ (( _ ) _'∘> (join_hom A B a b)) = (join_hom A B a' b));

symbol join_elim_con_func : Π (A B : cat) [E : cat] (first_func : func A E)  (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b)) //note extensionality second_func outside
(natural_eq : Π [I : cat] (a : func I A) (b : func I B) [a'] (r : hom a' (Unit_mod Id_func a) Id_func) , 
      π (r  '∘ (( _ ) _'∘> (one_hom I a b)) = (one_hom I a' b))), 
  func (join_cat A B) E;

rule  join_fst_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F0
with  join_snd_func $A $B ∘> (join_elim_con_func $A $B $F0 $F1 $r _) ↪ $F1;


rule ((join_hom $A $B $a $b) '∘ ((join_fst_func $A $B) _'∘> (Func_con_hom (join_elim_con_func $A $B $first_func $second_func $one_hom _) 
              (join_snd_func $A $B)))) ↪ $one_hom _ $a $b ;

assert (A B : cat) [E : cat] (first_func : func A E) (second_func : func B E) 
(one_hom : Π (I : cat) (a : func I A) (b : func I B), hom a (Unit_mod (first_func) Id_func) (second_func <∘ b))
[I : cat] (a : func I A) (b : func I B) ⊢ eq_refl _ : π (

((join_hom A B a b) '∘ ((join_fst_func A B) _'∘> (Func_con_hom (join_elim_con_func A B first_func second_func one_hom _) 
                            (join_snd_func A B)))) = one_hom _ a b );



 /* PART 2 Fibrations and dependency */

/* (ad) catd ========================== */

 injective symbol Op_catd : Π [X : cat] (A : catd X), catd (Op_cat X);
 injective symbol Op_isFibration_cov : Π [X : cat] [A : catd X], isFibration_con A → isFibration_cov (Op_catd A);
 injective symbol Op_isFibration_con : Π [X : cat] [A : catd X], isFibration_cov A → isFibration_con (Op_catd A);

 rule Op_catd (Op_catd $A) ↪ $A;
 rule Op_isFibration_cov (Op_isFibration_con $A_isf) ↪ $A_isf
 with Op_isFibration_con (Op_isFibration_cov $A_isf) ↪ $A_isf;

 constant symbol Universe_con_cat : cat; 
 constant symbol Universe_cov_cat : cat;
 constant symbol Universe_con_catd : catd Universe_con_cat;
 constant symbol Universe_cov_catd : catd Universe_cov_cat;
 constant symbol Universe_con_isFibration_con : isFibration_con Universe_con_catd;
constant symbol Universe_cov_isFibration_cov : isFibration_cov Universe_cov_catd;

 rule Op_cat (Universe_cov_cat) ↪ Universe_con_cat
// this inverse necessary? yes for confluence and for the rule for Op_catd below
 with Op_cat (Universe_con_cat) ↪ Universe_cov_cat;

 rule Op_catd (Universe_cov_catd) ↪ Universe_con_catd
 with Op_catd (Universe_con_catd) ↪ Universe_cov_catd;

 rule Op_isFibration_cov (Universe_con_isFibration_con) ↪ Universe_cov_isFibration_cov
 with Op_isFibration_con (Universe_cov_isFibration_cov) ↪ Universe_con_isFibration_con;

 // todo both cov catd and con catd
 
 symbol Fibre_catd : Π [X I : cat] (A : catd X) (x : func I X), catd I;
 constant symbol Fibre_isFibration_con : Π [X I : cat] (A : catd X) (A_isf : isFibration_con A) (x : func I X),
    isFibration_con (Fibre_catd A x);
 constant symbol Fibre_isFibration_cov : Π [X I : cat] (A : catd X) (A_isf : isFibration_cov A) (x : func I X),
     isFibration_cov (Fibre_catd A x);

constant symbol Terminal_catd : Π (A : cat), catd A;

//TODO: use Productdt_ instead of Cast_ ?  or add each and all the intermediate versions ?
 constant symbol Cast_catd : Π (A : cat) , catd Terminal_cat;
 constant symbol Productdt_catd : Π [U : cat] (UU : catd U) (A : cat), catd U;

constant symbol Productd_catd : Π [U : cat] (X : catd U) (Y : catd U), catd U;

 constant symbol Sigma_catd : Π [Y X : cat] (Z : catd Y) (F : func Y X), catd X;

constant symbol Pi_catd : Π [X' X Y : cat] (K : func X X') (A : catd X) (F : func X Y) (B : catd Y), catd X';

 constant symbol Comma_con_catd : Π [A B : cat] (R : mod A B) (BB : catd B) , catd A;
  constant symbol Comma_cov_catd : Π [A B : cat] (AA : catd A) (R : mod A B), catd B;

rule Op_catd (Fibre_catd $A $x) ↪ (Fibre_catd (Op_catd $A) (Op_func $x))
with Op_catd (Productdt_catd $T $A) ↪ (Productdt_catd (Op_catd $T) (Op_cat $A))
with Op_catd (Productd_catd $X $Y) ↪ (Productd_catd (Op_catd $Y) (Op_catd $X))
with Op_catd (Terminal_catd $X)  ↪ Terminal_catd (Op_cat $X)
with Op_catd (Comma_con_catd $R $BB) ↪ (Comma_cov_catd  (Op_catd $BB) (Op_mod $R))
with Op_catd (Comma_cov_catd $AA $R) ↪ (Comma_con_catd (Op_mod $R) (Op_catd $AA));
 
 rule Fibre_catd $A Id_func ↪ $A
 with Fibre_catd $A ($x ∘> $y)  ↪ Fibre_catd (Fibre_catd $A $y) $x
 // reverse direction ?
// with  Fibre_catd (Fibre_catd $A $y) $x ↪ Fibre_catd $A ($x ∘> $y)  
with Fibre_catd (Terminal_catd _) _ ↪ (Terminal_catd _)
 with Fibre_catd (Comma_con_catd $R $BB) $F ↪ (Comma_con_catd ($F ∘>> $R) $BB)  //todo review this?
 with Fibre_catd (Comma_cov_catd $AA $R) $G ↪ (Comma_cov_catd $AA ($R <<∘ $G)) ;

// NOTE: contrast Sigma_cat vs Total_cat: Total_cat is defined by rules, 
// Sigma_cat is constant constructor adjoint to Cast_catd
symbol Total_cat : Π [X : cat], catd X → Π [X'] (x : func X' X), cat;
symbol Total_proj_func : Π [X : cat] (A : catd X), Π [X'] (x : func X' X) , func (Total_cat A x) X';

//this direction to collect associativity
rule Pullback_cat (Total_proj_func $A $F) $G
↪ Total_cat $A ($G ∘> $F);
rule Pullback_snd_func (Total_proj_func $A $F) $G
↪ Total_proj_func $A ($G ∘> $F);


rule Total_cat (Fibre_catd $A $F) $G  ↪ Total_cat $A ($G ∘> $F) // = Pullback_cat (Total_proj_func $A $F) $G
with @Total_cat _ (Terminal_catd $A) $B $F ↪ $B
with @Total_cat _ (Cast_catd $A) $U' $F  ↪  (Product_cat $U' $A) 
 with Total_cat (Productdt_catd $UU $A) $F  ↪  (Product_cat (Total_cat $UU $F) $A)  
with Total_cat (Productd_catd $X $Y) $H ↪  
(Pullback_cat (Total_proj_func $X $H) (Total_proj_func $Y $H)) 
// these are instances of fibre rule above
with Total_cat (Comma_con_catd ($F ∘>> $R) $BB) $F' ↪ Total_cat (Comma_con_catd $R $BB) ($F' ∘> $F)
with Total_cat (Comma_cov_catd $AA ($R <<∘ $G)) $G' ↪ Total_cat (Comma_cov_catd $AA $R) ($G' ∘> $G)
;



rule Total_proj_func (Fibre_catd $A $F) $G ↪ Total_proj_func $A ($G ∘> $F) // = Pullback_snd_func (Total_proj_func $A $F) $G
with Total_proj_func (Terminal_catd $A) $F ↪ Id_func
with @Total_proj_func _ (Cast_catd $A) $U' $F ↪ @Product_fst_func $U' $A _ Id_func 
 with Total_proj_func (Productdt_catd $UU $A) $F  ↪  (Product_fst_func $A (Total_proj_func $UU $F))
with Total_proj_func (Productd_catd $X $Y) $H  ↪  
(Pullback_func (Total_proj_func $X $H) (Total_proj_func $Y $H)) 
;


/* (bd) funcd ========================== */

constant symbol  Id_funcd : Π [X : cat] [A : catd X], funcd A Id_func A;

constant symbol  Func_funcs :  Π [X Y : cat] (xy : func X Y), funcs xy (Terminal_catd Y);


symbol ∘>d: Π [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcd A F B → funcd B G C → funcd A (F ∘> G) C;
notation ∘>d infix left 90;
symbol d<∘ [X Y Z : cat] [A : catd X] [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z] : funcd B G C → funcd A F B → funcd A (F ∘> G) C ≔ λ G F, F ∘>d G;
notation d<∘ infix right 90;

rule $X ∘>d ($G ∘>d $H) ↪ ($X ∘>d $G) ∘>d $H
// ($F ∘>d $G) ∘>d $H ↪ $F ∘>d ($G ∘>d $H)
with $F ∘>d Id_funcd ↪ $F
with Id_funcd ∘>d $F ↪ $F; 

symbol ∘>sd: Π [X Y Z : cat]  [B : catd Y] [C : catd Z] [F : func X Y]
[G : func Y Z], funcs F B → funcd B G C → funcs (F ∘> G) C;
notation ∘>sd infix left 90;

symbol ∘>s: Π [X Y Z : cat] [C : catd Z] (F : func X Y)
[G : func Y Z], funcs G C → funcs (F ∘> G) C;
notation ∘>s infix left 90;

rule $X ∘>sd ($G ∘>d $H) ↪ ($X ∘>sd $G) ∘>sd $H
with $F ∘>sd Id_funcd ↪ $F;

// this direction because ∘>s is some kind of accumulated elim
rule ($X ∘>s $G) ∘>sd $H ↪  $X ∘>s ($G ∘>sd $H) 
//$X ∘>s ($G ∘>sd $H) ↪ ($X ∘>s $G) ∘>sd $H
with $F ∘>s (Func_funcs $G) ↪ (Func_funcs ($F ∘> $G))
with Id_func ∘>s $G ↪ $G
with $X ∘>s ($G ∘>s $H) ↪ ($X ∘> $G) ∘>s $H;


///--


// constant symbol  Id_funci :  Π [X : cat] , funci (Terminal_catd X);
// constant symbol  Funcs_funci :  Π [X Y : cat] (xy : func X Y), funcs xy (Terminal_catd Y);

// symbol ∘>id: Π [X Z : cat]  [B : catd X] [C : catd Z] 
// [G : func X Z], funci B → funcd B G C → funcs G C;
// notation ∘>id infix left 90;
// symbol ∘>i: Π [X Y : cat] [C : catd Y] (F : func X Y), funci C → funcs F C;
// notation ∘>i infix left 90;

// rule $X ∘>id ($G ∘>d $H) ↪ ($X ∘>id $G) ∘>sd $H;

// type cat;
// type cat cat;

///---



injective symbol Op_funcd : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y], funcd A F B → funcd (Op_catd A) (Op_func F) (Op_catd B);

injective symbol Op_funcs : Π [X Y : cat] [F : func X Y] [B : catd Y], 
funcs F B → funcs (Op_func F) (Op_catd B);

rule Op_funcd (Op_funcd $F) ↪ $F
with Op_funcd (Id_funcd) ↪ (Id_funcd)
with Op_funcd ($F ∘>d $G) ↪ ((Op_funcd $F) ∘>d (Op_funcd $G)) ;

rule Op_funcs (Func_funcs $F) ↪ (Func_funcs (Op_func $F));

injective symbol Terminal_funcd :  Π [X : cat] (A : catd X), funcd A Id_func (Terminal_catd X);

rule Op_funcd (Terminal_funcd $A) ↪ (Terminal_funcd (Op_catd $A));
rule (@∘>d _ _ _ $A $B _ Id_func _ $F (Terminal_funcd $B)) ↪ (Terminal_funcd $A) ;
rule (Terminal_funcd (Terminal_catd _)) ↪ Id_funcd;

//todo review injective?
injective symbol Funcs_funcd : Π [X Y : cat] [F : func X Y] [B : catd Y],  
funcs F B → funcd (Terminal_catd X) F B ;

rule Op_funcd (Funcs_funcd $FF) ↪ (Funcs_funcd (Op_funcs $FF));

rule (Func_funcs $G) ∘>sd (Funcs_funcd $FF) ↪ $G ∘>s $FF;
// rule (Funcs_funcd $FF) ∘>d $HH ↪ (Funcs_funcd ($FF ∘>sd $HH));
// rule Funcs_funcd (Func_funcs Id_func ∘>sd $HH) ↪ $HH;
//todo: review, reverse direction? yes reversed, because of datatype eliminations
rule (Funcs_funcd $FF) ∘>d $HH ↪ (Funcs_funcd ($FF ∘>sd $HH));
rule Funcs_funcd (Func_funcs Id_func) ↪ Id_funcd;

symbol Total_func : Π [X Y : cat] [A : catd X] [B : catd Y] [xy : func X Y],
funcd A xy B → Π [X'] (x : func X' X), func (Total_cat A x) (Total_cat B (x ∘> xy));

rule (@Total_func _ _ $A $B $F $FF $X' $x) ∘> (@Total_proj_func _ $B $X' $x ) ↪ (Total_proj_func $A $x) ;
//TODO REVIEW THIS, ACCUMULATOR VERSION?
// rule (@Total_func _ _ $A $B $F $FF $X' $x) ∘> ((@Total_proj_func _ $B $X' $x ) ∘> $K) ↪ (Total_proj_func $A $x) ∘> $K ;

//REMINDER this rule must be at top of section, otherwise confluence checks are too much
//this  Total_func of @∘>d requires above earlier Pullback_cat reversal of rewrite direction and symmetric versions of rewrites
rule  Total_func ( @∘>d _ _ _ $A $B $C $F $G $FF $GG) $x ↪ 
   (Total_func $FF $x) ∘> (Total_func $GG ($x ∘> $F)) ;

//TODO: use Productdt_ instead of Cast_ ?
constant symbol Cast_intro_funcd : Π [U A : cat] (I : catd U) [U'] (u : func U' U) (G : func (Total_cat I u) A), 
funcd (Fibre_catd I u) (Terminal_func U') (Cast_catd A);

//TODO: will be clearly motivated when spans are used instead
constant symbol Productdt_intro_funcd' : Π [U : cat] [UU : catd U] [A : cat] [U'] [u : func U' U] 
[U''] [u' : func U' U''] [I : catd U''] (F : funcd (Fibre_catd I u') u UU)  
(G : func (Total_cat I u') A) , 
funcd (Fibre_catd I u') u (Productdt_catd UU A);

//TODO erase Cast_ use instead Productdt_
constant symbol Cast_funcd : Π  [A B : cat] (F : func A B), funcd (Cast_catd A) Id_func (Cast_catd B); 

constant symbol Productdt_funcd : Π [U : cat] (UU : catd U) [A B : cat] (F : func A B), funcd (Productdt_catd UU A) Id_func (Productdt_catd UU B); 
constant symbol Productdt_base_funcd : Π [U V : cat] [F : func U V] [UU : catd U] [VV : catd V] (FF : funcd UU F VV) (A : cat) , funcd (Productdt_catd UU A) F (Productdt_catd VV A); // ?used?

//TODO: REVIEW, IS THIS USED ANYMORE
// symbol  Triv_funcd :  Π [X Y : cat] (xy : func X Y), funcd (Terminal_catd X) xy (Terminal_catd Y);
 
symbol Fibre_intro_funcd : Π [X I I' : cat] (A : catd X) (x : func I X) [J : catd I'] (i : func I' I) ,
 funcd J (i ∘> x) A  → funcd J i (Fibre_catd A x);
 //TODO: REVIEW both are required in different grammatical/syntactical entries (implementation datatype), 
 ///together with cancelation against the same elim
 constant symbol Fibre_intro_funcd' : Π [X I : cat] (A : catd X) (x : func I X) [J : catd I]  ,
 funcd J x A  → funcd J Id_func (Fibre_catd A x);

 symbol Fibre_intro_funcs : Π [X I I' : cat] (A : catd X) (x : func I X) (i : func I' I) ,
 funcs (i ∘> x) A  → funcs i (Fibre_catd A x);

constant symbol Fibre_intro_funcs' : Π [X I : cat] (A : catd X) (x : func I X),
 funcs x A  → funcs Id_func (Fibre_catd A x);

 symbol Fibre_elim_funcd : Π [X I : cat] (A : catd X) (x : func I X), funcd (Fibre_catd A x) x A;
 
 
//rule Op_funcd (Triv_funcd $xy) ↪ (Triv_funcd (Op_func $xy));
rule Op_funcd (Fibre_intro_funcd $A $x $i $FF) ↪ (Fibre_intro_funcd (Op_catd $A) (Op_func $x) (Op_func $i) (Op_funcd $FF))
 with Op_funcd (Fibre_elim_funcd $A $x) ↪ (Fibre_elim_funcd (Op_catd $A) (Op_func $x));

rule  Op_funcs (Fibre_intro_funcs $A $x $i $FF) ↪ (Fibre_intro_funcs (Op_catd $A) (Op_func $x) (Op_func $i) (Op_funcs $FF));

 rule (Fibre_intro_funcd $A $x _ $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF ;
 rule $HH ∘>d (Fibre_intro_funcd $A $x _ $FF) ↪ (Fibre_intro_funcd $A $x _ ($HH ∘>d $FF)) ;
 
 rule (Fibre_intro_funcs $A $x _ $FF) ∘>sd (Fibre_elim_funcd $A $x) ↪ $FF ;
 rule $HH ∘>s (Fibre_intro_funcs $A $x _ $FF) ↪ (Fibre_intro_funcs $A $x _ ($HH ∘>s $FF)) ;
 
 rule Fibre_elim_funcd $A Id_func ↪ Id_funcd
 // reverse direction? yes composition in contractum, 
 with (Fibre_elim_funcd /* (Fibre_catd $A $y) */ _ $x) ∘>d Fibre_elim_funcd $A $y  ↪ Fibre_elim_funcd $A ($x ∘> $y)
// with Fibre_elim_funcd $A ($x ∘> $y) ↪ (Fibre_elim_funcd (Fibre_catd $A $y) $x) ∘>d Fibre_elim_funcd $A $y 
 with Fibre_elim_funcd (Terminal_catd _) _ ↪ Funcs_funcd (Func_funcs _) ;// (Triv_funcd _);
 
 rule Fibre_intro_funcd $A Id_func $i $FF ↪ $FF
 // reverse direction? yes composition in contractum, otherwise confluence problems with Fibre_functor_funcd
 with (Fibre_intro_funcd /* (Fibre_catd $A $y) */ _ $x $i (Fibre_intro_funcd $A $y /* ($i ∘> $x) */ _ $FF)) 
 ↪  (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
 // with (Fibre_intro_funcd $A ($x ∘> $y) $i $FF) 
 // ↪ (Fibre_intro_funcd (Fibre_catd $A $y) $x $i (Fibre_intro_funcd $A $y ($i ∘> $x) $FF))
 ;
 
 rule Fibre_intro_funcs $A Id_func $i $FF ↪ $FF
 with (Fibre_intro_funcs /* (Fibre_catd $A $y) */ _ $x $i (Fibre_intro_funcs $A $y /* ($i ∘> $x) */ _ $FF)) 
 ↪  (Fibre_intro_funcs $A ($x ∘> $y) $i $FF)  ;


constant symbol Comma_con_intro_funcd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd BB y) x (Comma_con_catd R BB);
constant symbol Comma_cov_intro_funcd : Π [A B I : cat] (AA : catd A) [R : mod A B]  [x : func I A] [y : func I B] (r : hom x R y),
funcd (Fibre_catd AA x) y (Comma_cov_catd AA R);
 
 
constant symbol Comma_con_comp_funcd : Π [A B I : cat] (R : mod A B) (BB : catd B) (F : func I A),
funcd (Comma_con_catd (F ∘>> R) BB) F (Comma_con_catd R BB);
constant symbol Comma_cov_comp_funcd : Π [A B I : cat] (AA : catd A) (R : mod A B) (G : func I B),
funcd (Comma_cov_catd AA (R <<∘ G )) G (Comma_cov_catd AA R);

rule (Comma_con_comp_funcd _ _ $F') ∘>d (Comma_con_comp_funcd $R $BB $F)
↪ (Comma_con_comp_funcd $R $BB ($F' ∘> $F));

//SIGNIFICANT: note no use of explicit Op_cat contravariance or of extra notion of contravariant functor, 
// here the contravariance is intrinsic baked into the contravariant universe, 
// and each independent development of the two universes need not interact via Op_ ,
// better: each don't even need the existance of Op_
symbol Universe_con_func : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), func  X Universe_con_cat; 
symbol Universe_cov_func : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), func X Universe_cov_cat;

symbol Universe_con_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_con A), funcd A (Universe_con_func A A_isf) Universe_con_catd;
symbol Universe_cov_funcd : Π [X : cat] (A : catd X) (A_isf : isFibration_cov A), funcd A (Universe_cov_func A A_isf) Universe_cov_catd;

rule Op_func (Universe_cov_func $A $A_isf) ↪ (Universe_con_func (Op_catd $A) (Op_isFibration_con $A_isf))
with Op_func (Universe_con_func $A $A_isf) ↪ Universe_cov_func (Op_catd $A) (Op_isFibration_cov $A_isf);

rule Op_funcd (Universe_cov_funcd $A $A_isf) ↪ Universe_con_funcd (Op_catd $A) (Op_isFibration_con $A_isf)
with Op_funcd (Universe_con_funcd $A $A_isf) ↪ Universe_cov_funcd (Op_catd $A) (Op_isFibration_cov $A_isf);
 
//todo review  necessary
// constant symbol Catd_funcd : Π [X : cat] (A : catd X), funcd A Id_func (Terminal_catd X); //as funchd ?;
 
 constant symbol SigmaIntro_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X), funcd Z F (Sigma_catd Z F);
 
 
 constant symbol SigmaElim_funcd : Π [Y X : cat] (Z : catd Y) (F : func Y X),
 Π [X' : cat] [C : catd X'] (G : func X X'),
   funcd Z (F ∘> G) C → funcd (Sigma_catd Z F) G C;
 
// naturality
rule (SigmaElim_funcd $Z $F $G $GG) ∘>d $HH ↪ (SigmaElim_funcd $Z $F _ ($GG ∘>d $HH));
// beta
rule (SigmaIntro_funcd $Z $F) ∘>d (SigmaElim_funcd $Z $F $G $GG) ↪ $GG;



rule Op_funcd (Productdt_funcd $UU $F) ↪ (Productdt_funcd (Op_catd $UU) (Op_func $F))
with Op_funcd (Productdt_base_funcd $FF $A) ↪ (Productdt_base_funcd (Op_funcd $FF) (Op_cat $A));

rule (Cast_funcd $F) ∘>d (Cast_funcd $G) ↪ Cast_funcd ($F ∘> $G);


//DONE: ADD THIS FUNCTOR AS INTERMEDIATE LOGICAL SYMBOL WITH OWN RULES, WITH ITS OLDER DEFINITION CONTENT WHICH REWRITE TO THIS SYMBOL
symbol Fibre_functor_funcd  [X Y Z] [B: catd Y] [C: catd Z] [G: func Y Z] (GG : funcd B G C) (F: func X Y) :
 funcd (Fibre_catd B F) Id_func (Fibre_catd C (F ∘> G));

rule Fibre_intro_funcd $C /* (F ∘> G) */ _ Id_func ( @∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) 
↪ Fibre_functor_funcd $GG $F ;

rule Op_funcd (Fibre_functor_funcd $GG $F) ↪ (Fibre_functor_funcd (Op_funcd $GG) (Op_func $F));

rule (@Fibre_functor_funcd _ _ _ $B $C $G $GG $F) ∘>d (Fibre_elim_funcd $C ($F ∘> $G))
↪ (Fibre_elim_funcd $B $F) ∘>d $GG;

rule (@Fibre_intro_funcd _ _ _ $B $F _ _ $HH) ∘>d (@Fibre_functor_funcd _ _ _ $B $C $G $GG $F)
↪ Fibre_intro_funcd $C ($F ∘> $G) _ ($HH ∘>d $GG) ;

rule (@Fibre_functor_funcd _ _ _ $B $C $G $GG $F) ∘>d (@Fibre_functor_funcd _ _ _ $C $D $H $HH ($F ∘> $G))
↪ @Fibre_functor_funcd _ _ _ $B $D ($G ∘> $H) ($GG ∘>d $HH) $F;

rule (Fibre_functor_funcd Id_funcd _) ↪ Id_funcd;

//this comes from naturality, less prime
symbol Fibre_functor_funcd'  [X Y Z] [B: catd Y] [C: catd Z]  [G: func Y Z] (GG : funcd B G C) (F: func X Y):
funcd (Fibre_catd B F) F (Fibre_catd C G) ≔ 
 Fibre_intro_funcd C G F (@∘>d _ _ _ _ B C F G (Fibre_elim_funcd B F) GG ) ;

 //TODO: REVIEW THIS, functor on sections, necessary? used?
symbol Fibre_functor_funcs  [X Y Z] [C: catd Z] [G: func Y Z] (GG : funcs G C) (F: func X Y) :
funcs Id_func (Fibre_catd C (F ∘> G));
rule Fibre_intro_funcs $C /* (F ∘> G) */ _ Id_func ( $F ∘>s $GG ) 
↪ Fibre_functor_funcs $GG $F ;

rule Op_funcs (Fibre_functor_funcs $GG $F) ↪ (Fibre_functor_funcs (Op_funcs $GG) (Op_func $F));

rule (@Fibre_functor_funcs _ _ _ $C $G $GG $F) ∘>sd (Fibre_elim_funcd $C ($F ∘> $G))
↪ $F ∘>s $GG;

rule $H ∘>s (@Fibre_functor_funcs _ _ _  $C $G $GG $F)
↪ Fibre_intro_funcs $C ($F ∘> $G) _ ($H ∘>s ($F ∘>s $GG)) ;

rule (Fibre_functor_funcs (Func_funcs _) _) ↪ Func_funcs _;

symbol Productd_intro_funcd : Π [U] [T X : catd U] [V] [I : catd V]
[u : func V U] (FF : funcd I u T)  (GG : funcd I u X),
 funcd I u (Productd_catd T X);
constant symbol Productd_fst_funcd : Π [U] (T X : catd U) ,
funcd (Productd_catd T X) Id_func T ; 
constant symbol Productd_snd_funcd : Π [U] (T X : catd U),
funcd (Productd_catd T X) Id_func X ; 

rule $H ∘>d (Productd_intro_funcd $F $G) ↪ (Productd_intro_funcd ($H ∘>d $F) ($H ∘>d $G));
rule (@Productd_intro_funcd _ $T $X _ _ _ $F $G) ∘>d (Productd_fst_funcd $T $X) ↪ $F  
with (@Productd_intro_funcd _ $T $X _ _ _ $F $G) ∘>d (Productd_snd_funcd $T $X) ↪ $G  ;

//DONE: ADD THIS FUNCTOR AS INTERMEDIATE LOGICAL SYMBOL WITH OWN RULES, WITH ITS OLDER DEFINITION CONTENT WHICH REWRITE TO THIS SYMBOL
symbol Productd_functor_snd_funcd [U] T [X X' : catd U] (HH : funcd X Id_func X'):
funcd (Productd_catd T X) Id_func (Productd_catd T X') ;

rule Productd_intro_funcd (Productd_fst_funcd $T $X) ((Productd_snd_funcd $T $X) ∘>d $HH)
↪ Productd_functor_snd_funcd $T $HH;

rule (@Productd_functor_snd_funcd _ $T $X $X' $HH) ∘>d (Productd_fst_funcd $T $X) 
  ↪ (Productd_fst_funcd $T $X) 
with (@Productd_functor_snd_funcd _ $T $X $X' $HH) ∘>d (Productd_snd_funcd $T $X) 
  ↪ ((Productd_snd_funcd $T $X) ∘>d $HH) ;

rule (Productd_intro_funcd $FF $GG) ∘>d (Productd_functor_snd_funcd $T $HH)
↪ Productd_intro_funcd $FF ($GG ∘>d $HH) ;

rule (Productd_functor_snd_funcd $T $GG) ∘>d (Productd_functor_snd_funcd $T $HH)
↪ Productd_functor_snd_funcd $T ($GG ∘>d $HH) ;

rule (Productd_functor_snd_funcd $T Id_funcd) 
↪ Id_funcd ;

 constant symbol Pit_intro_func : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y] (D : cat) 
(FF : funcd (Productdt_catd A D) F B), func D (Pit_cat A F B);
constant symbol Pit_elim_funcd : Π [X Y : cat] [A : catd X] [F : func X Y] [B : catd Y] (D : cat) ,
 funcd (Productdt_catd A (Pit_cat A F B)) F B;

constant symbol Pi_intro_funcd_alt : Π [X' X Y : cat] (K : func X X') [A : catd X] [F : func X Y] [B : catd Y] (D : catd X') 
(FF : funcd (Productd_catd A (Fibre_catd D K)) F B), funcd D Id_func (Pi_catd K A F B);

constant symbol Pi_intro_funcd : Π [X' X Y : cat] 
(K : func X X') (A : catd X)  (F : func X Y) (B : catd Y) [X''] (D : catd X'') (L : func X'' X') 
(FF : funcd (Productd_catd (Fibre_catd A (Pullback_snd_func L K)) (Fibre_catd D (Pullback_fst_func L K)))
  ((Pullback_snd_func L K) ∘> F) B), 
funcd D L (Pi_catd K A F B);

constant symbol Pi_elim_funcd : Π [X' X Y : cat] (K : func X X') (A : catd X)  (F : func X Y) (B : catd Y),
funcd (Productd_catd A (Fibre_catd (Pi_catd K A F B) K)) F B;

rule (Productd_functor_snd_funcd $A (Fibre_functor_funcd (@Pi_intro_funcd_alt _ _ _ $K $A $F $B $D $FF) $K)) ∘>d (Pi_elim_funcd $K $A $F $B) 
↪ $FF;

//TODO FIbre_intro and FIbre_elim  over comp and id
assert [X' X Y : cat] 
[K : func X X'] [A : catd X]  [F : func X Y] [B : catd Y] (D : catd X') 
(FF : funcd (Productd_catd A (Fibre_catd D K)) F B) ⊢ 
(Productd_functor_snd_funcd A (Fibre_functor_funcd (Pi_intro_funcd_alt K D FF) K)) ∘>d (Pi_elim_funcd K A  F B )
≡ FF;

rule (Fibre_catd (Pi_catd $K $A $F $B) $L) ↪ 
(Pi_catd (Pullback_fst_func $L $K) (Fibre_catd $A (Pullback_snd_func $L $K)) 
   ((Pullback_snd_func $L $K) ∘> $F) $B);

// this require the above rewrite on fibre of pid
type λ [X' X Y : cat] 
(K : func X X') [A : catd X]  [F : func X Y] [B : catd Y] [X''] (D : catd X'') (L : func X'' X') 
(FF : funcd (Productd_catd (Fibre_catd A (Pullback_snd_func L K)) (Fibre_catd D (Pullback_fst_func L K)))
  ((Pullback_snd_func L K) ∘> F) B), 
(Productd_functor_snd_funcd (Fibre_catd  A (Pullback_snd_func  L  K)) (Fibre_functor_funcd (Pi_intro_funcd K A F B D L FF) (Pullback_fst_func  L  K)))  ∘>d 
(Pi_elim_funcd (Pullback_fst_func  L  K) (Fibre_catd  A (Pullback_snd_func  L  K)) ((Pullback_snd_func L K) ∘> F) B ) ;




//HERE ERASE? SLOW
//rule @Fibre_intro_funcd $X $X _ $A (@Id_func $X) _ $F $MM ↪ $MM;

 // naturality
 rule (Fibre_elim_funcd (Fibre_catd $BB $y) $zz) ∘>d (@Comma_con_intro_funcd _ _ _ _ $BB _ $y $r) 
   ↪ (Comma_con_intro_funcd $BB ($r ∘↓ $zz));
 rule (Fibre_elim_funcd (Fibre_catd $AA $x) $zz) ∘>d (@Comma_cov_intro_funcd _ _ _ $AA _  $x _ $r) 
  ↪ (Comma_cov_intro_funcd $AA ($r ∘↓ $zz));
 
 //TODO: REVIEW, or reverse, conversion on non-constant Triv_funcd instead?
//  rule Triv_funcd ($F ∘> $G) ↪ (Triv_funcd $F) ∘>d (Triv_funcd $G)  //TODO accumulator version of Triv_funcd?
//  with  (Triv_funcd Id_func) ↪ Id_funcd; //note in fact the left is section so both lacked, and no need for convertibility
  

 
//  rule (Fibre_intro_funcd' $A $x $FF) ∘>d (Fibre_elim_funcd $A $x) ↪ $FF ;
//FAILS INDEED: rule $HH ∘>d (Fibre_intro_funcd' $A $x $FF) ↪ (Fibre_intro_funcd' $A $x ($HH ∘>d $FF)) ;

//TODO: REVIEW SLOW  ... in retrospect, this would be id-functoriality of Fibre_functor_funcd
//rule (@Fibre_intro_funcd $X $I $I $A $x (Fibre_catd $A $x) (@Id_func $I) (Fibre_elim_funcd $A $x))  ↪ @Id_funcd _ (Fibre_catd $A $x) ;

 rule $F ∘> (Universe_con_func $A $A_isf)  ↪ (Universe_con_func (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));
 rule (Fibre_elim_funcd $A $F) ∘>d (Universe_con_funcd $A $A_isf)  ↪ (Universe_con_funcd (Fibre_catd $A $F) (Fibre_isFibration_con $A $A_isf $F));

 rule (Universe_con_func (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F))  ↪ $F;
 rule (Universe_con_funcd (Fibre_catd Universe_con_catd $F) (Fibre_isFibration_con Universe_con_catd Universe_con_isFibration_con $F))  ↪ Fibre_elim_funcd Universe_con_catd $F;
 
 //strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
 rule (Fibre_catd Universe_con_catd (Universe_con_func $A _))  ↪ $A;
 rule (Fibre_elim_funcd Universe_con_catd (Universe_con_func $A $A_isf))  ↪ (Universe_con_funcd $A $A_isf);

 //note: these below are copy-paste replace _con_ by _cov_
 rule $F ∘> (Universe_cov_func $A $A_isf)  ↪ (Universe_cov_func (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));
 rule (Fibre_elim_funcd $A $F) ∘>d (Universe_cov_funcd $A $A_isf)  ↪ (Universe_cov_funcd (Fibre_catd $A $F) (Fibre_isFibration_cov $A $A_isf $F));

 rule (Universe_cov_func (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F))  ↪ $F;
 rule (Universe_cov_funcd (Fibre_catd Universe_cov_catd $F) (Fibre_isFibration_cov Universe_cov_catd Universe_cov_isFibration_cov $F))  ↪ Fibre_elim_funcd Universe_cov_catd $F;
 
 //strict universe, optional? or use Fibre_intro isEquiv instead of declaring it identity 
 rule (Fibre_catd Universe_cov_catd (Universe_cov_func $A _))  ↪ $A;
 rule (Fibre_elim_funcd Universe_cov_catd (Universe_cov_func $A $A_isf))  ↪ (Universe_cov_funcd $A $A_isf);



rule Total_func (Id_funcd) _  ↪ Id_func
with Total_func (Fibre_elim_funcd $A $F) _ ↪ Id_func

//todo replace with section version
// with Total_func (Triv_funcd $F) _ ↪ Id_func

//todo problem with @Total_func _ _ _ _ _ (Product_funcd $A $F) $A' $x ↪ Total_func (Product_funcd $A' $F) Id_func
//nope more general 
//with Total_func (SigmaIntro_funcd $Z $F) ↪ (Id_func)
;

//this should use the intro over Id so that the _ is inferred otherwise inconsistent...
// rule Total_func ( Fibre_intro_funcd $C _ Id_func (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
// ↪ (Pullback_functor_func ($K ∘> $F) (Total_proj_func (Fibre_catd $C $G)) (Total_func $GG))  ;
// rule Total_func ( Fibre_intro_funcd $C _ Id_func (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
// ↪ (Total_func $GG ($K ∘> $F))  ;
rule Total_func (Fibre_functor_funcd $GG $F) $K 
↪ (Total_func $GG ($K ∘> $F));
//new commmenting because reassociativity of o> causes  problems here
// rule Total_func ( Fibre_intro_funcd $C $G $F (@∘>d _ _ _ _ $B $C $F $G (Fibre_elim_funcd $B $F) $GG ) ) $K 
// ↪ (Total_func $GG ($K ∘> $F))  ;

 
 //TODO: erase, instead declare their Total_func $FF $u as isFuncEquiv
 constant symbol  Id_funcd_isEquiv : Π [X : cat] [A : catd X], isEquiv (@Id_funcd _ A);
 constant symbol Sigma_isEquiv : Π [Y X : cat] (Z : catd Y) (F : func Y X), isEquiv (SigmaIntro_funcd Z F);
 
 
 /* (d) modd moddu ========================== */

 injective symbol Op_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B), modd (Op_catd B) (Op_mod R) (Op_catd A);
 
 injective symbol Op_moddu : Π [I : cat] [A : catd I] [B : catd I]
 (RR : moddu A B), moddu (Op_catd B) (Op_catd A);

constant symbol Unit_modd : Π [I X Y : cat] [xi : func X I] [yi : func Y I] 
[XX : catd X] [YY : catd Y] [II : catd I] (F : funcd XX xi II)  (G : funcd YY yi II), 
modd XX (Unit_mod xi yi) YY;

 constant symbol Unit_moddu : Π [I : cat] [XX : catd I] [YY : catd I] [II : catd I]
 (F : funcd XX Id_func II) (G : funcd YY Id_func II), 
 moddu XX YY;
 
 constant symbol Terminal_modd : Π [X Y : cat] (R : mod X Y) ,
 modd (Terminal_catd X) R (Terminal_catd Y);
 
 constant symbol Terminal_moddu : Π (X : cat), moddu (Terminal_catd X) (Terminal_catd X);
 
 //example of fibred profunctor: squares fibred by their diagonal
 constant symbol Comma_modd : Π [A B : cat] (AA : catd A) (R : mod A B) (BB : catd B),
    modd (Comma_con_catd R BB) R (Comma_cov_catd AA R);
 
 
 symbol Fibre_func_moddu : Π [I: cat] [A : catd I] [B : catd I] (RR : moddu A B),
  Π [J: cat] (i : func J I), moddu (Fibre_catd A i) (Fibre_catd B i);
 
 rule Fibre_func_moddu $A Id_func ↪ $A
 with Fibre_func_moddu $A ($x ∘> $y)  ↪ Fibre_func_moddu (Fibre_func_moddu $A $y) $x
with Fibre_func_moddu (Unit_moddu $FF $GG) $F ↪ Unit_moddu (Fibre_functor_funcd $FF $F) (Fibre_functor_funcd $GG $F)
with Fibre_func_moddu (Terminal_moddu _) $F ↪ Terminal_moddu _;
 
 //TODO: REVIEW this, use instead Fibre_functor_funcd ? yep
 // symbol Fibre_homdu : Π [I: cat] [A : catd I] [B : catd I] [II: catd I] 
 // [FF : funchd II A] [RR : moddu A B] [GG : funchd II B],
 // homdu FF RR GG →  Π [J: cat] (i : func J I),
 // homdu (Fibre_funchd FF i)  (Fibre_func_moddu RR i) (Fibre_funchd GG i) ;
 
 symbol Fibre_transf_modd : Π [X Y X' Y' : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [S : mod X' Y'] [x : func X' X] [y : func Y' Y], transf S x R y → 
  modd (Fibre_catd A x) S (Fibre_catd B y);
 
 rule Fibre_transf_modd $A (Id_transf _) ↪ $A
 with Fibre_transf_modd $A ($x ''∘ $y)  ↪ Fibre_transf_modd (Fibre_transf_modd $A $y) $x
 with Fibre_transf_modd $A ($y ∘'' $x)  ↪ Fibre_transf_modd (Fibre_transf_modd $A $y) $x
 with Fibre_transf_modd (Terminal_modd _) $F ↪ Terminal_modd _ ;
 
 
 symbol Fibre_hom_moddu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
 (RR : modd A R B) [x : func I X] [y : func I Y], hom x R y → 
  moddu (Fibre_catd A x) (Fibre_catd B y);
 
rule  Fibre_hom_moddu (Unit_modd $FF $GG) (Id_hom $F) ↪ Unit_moddu (Fibre_functor_funcd $FF $F) (Fibre_functor_funcd $GG $F)
with Fibre_hom_moddu $A ($r ∘↓ $F)  ↪ Fibre_func_moddu (Fibre_hom_moddu $A $r) $F
 with Fibre_hom_moddu (Terminal_modd _) $r ↪ Terminal_moddu _ ;

  
 constant symbol Sheaf_con_mod : Π [A B : cat], mod A B → mod A B;

constant symbol Productdt_moddu : Π [T : cat] (TT : catd T) [X Y : cat] (R : mod X Y), moddu (Productdt_catd TT X) (Productdt_catd TT Y);
  
constant symbol  Productdt_modd : Π [A B : cat] [T : mod A B] [AA : catd A] [BB : catd B] (TT : modd AA T BB) [X Y : cat] (R : mod X Y), modd (Productdt_catd AA X) T (Productdt_catd BB Y);
 
 
 constant symbol ⊗d : Π [A B X : cat] [AA : catd A][BB : catd B][XX : catd X]
  [R :mod A B] [S :mod B X], modd AA R BB → modd BB S XX →
  modd AA (R ⊗ S) XX;  //Tensor_modd;
 notation ⊗d infix left 70;
 
 
 constant symbol Sheaf_con_modd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
  modd A R B → modd A R B;
 
 //Subst_cov_modd
 symbol d<<∘ : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], modd AA R BB → Π [B' : cat] [b : func B' B] [BB' : catd B'], funcd BB' b BB → modd AA (R <<∘ b) BB';
 //Subst_con_modd
 symbol ∘>>d : Π [A B : cat] [AA : catd A] [BB : catd B] [R : mod A B], Π [A' : cat] [a : func A' A] [AA' : catd A'], funcd AA' a AA →  modd AA R BB →  modd AA' (a ∘>> R) BB;
 //Subst_cov_moddu
 symbol du<<∘ : Π [I : cat] [AA : catd I] [BB : catd I], moddu AA BB → Π [BB' : catd I], funcd BB' Id_func BB → moddu AA BB';
 //Subst_con_moddu
 symbol ∘>>du : Π [I : cat] [AA : catd I] [BB : catd I], Π [AA' : catd I], funcd AA' Id_func AA →  moddu AA BB →  moddu AA' BB;
 notation d<<∘ infix left 80; notation ∘>>d infix right 80;
 notation du<<∘ infix left 80; notation ∘>>du infix right 80;
 
  
 rule $R d<<∘ Id_funcd ↪ $R 
// with $R d<<∘ ($H d<∘ $K)  ↪ ($R d<<∘ $H) d<<∘ $K;
  with ($R d<<∘ $H) d<<∘ $K ↪ $R d<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>d $R ↪ $R 
// with ($K ∘>d $H) ∘>>d $R ↪ $K ∘>>d ($H ∘>>d $R);  
  with $K ∘>>d ($H ∘>>d $R) ↪ ($K ∘>d $H) ∘>>d $R; 
 
 rule ($F ∘>>d $R) d<<∘ $G ↪ ($F ∘>>d ($R d<<∘ $G));

rule  (Unit_modd $F $G) d<<∘ $K ↪ Unit_modd $F ($G d<∘ $K) 
with $K ∘>>d (Unit_modd $F $G) ↪ Unit_modd ($K ∘>d $F) $G ;

 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));

 rule $R du<<∘ Id_funcd ↪ $R 
// with $R du<<∘ ($K ∘>d $H ) ↪ ($R du<<∘ $H) du<<∘ $K; // error ∘>d is not manifestly over Id_func
  with ($R du<<∘ $H) du<<∘ $K ↪ $R du<<∘ ($H d<∘ $K); 
 
 rule Id_funcd ∘>>du $R ↪ $R 
// with ($K ∘>d $H) ∘>>du $R ↪ $K ∘>>du ($H ∘>>du $R); // error ∘>d is not manifestly over Id_func
  with $K ∘>>du ($H ∘>>du $R) ↪ ($K ∘>d $H) ∘>>du $R; 
 
 rule ($F ∘>>du $R) du<<∘ $G ↪ ($F ∘>>du ($R du<<∘ $G));
 
 rule  (Unit_moddu $F $G) du<<∘ $K ↪ Unit_moddu $F ($G d<∘ $K) 
 with $K ∘>>du (Unit_moddu $F $G) ↪ Unit_moddu ($K ∘>d $F) $G ;
  
 
 rule Op_modd (Op_modd $RR) ↪ $RR
with Op_modd (Unit_modd $FF $GG) ↪   (Unit_modd (Op_funcd $GG) (Op_funcd $FF)) 
with Op_modd ( Terminal_modd $R ) ↪   Terminal_modd (Op_mod $R)
 with Op_modd ( Fibre_transf_modd $RR $sr ) ↪   Fibre_transf_modd (Op_modd $RR) (Op_transf $sr) 
 with Op_modd ( Productdt_modd $T  $R ) ↪   Productdt_modd (Op_modd $T)  (Op_mod $R) 
 with Op_modd ( $RR ⊗d $SS ) ↪   (Op_modd $SS) ⊗d (Op_modd $RR)   ;

rule Op_modd ($F ∘>>d $R)  ↪ ((Op_modd $R) d<<∘ (Op_funcd $F))
with Op_modd ($R d<<∘ $G)  ↪ ((Op_funcd $G) ∘>>d (Op_modd $R));

rule Op_moddu (Op_moddu $RR) ↪ $RR
// with Op_moddu (Unit_moddu0 $A) ↪   (Unit_moddu0 (Op_catd $A)) 
with Op_moddu (Unit_moddu $FF $GG) ↪   (Unit_moddu (Op_funcd $GG) (Op_funcd $FF)) 
with Op_moddu ( Terminal_moddu $I ) ↪   Terminal_moddu (Op_cat $I)
with Op_moddu ( Fibre_func_moddu $RR $i ) ↪   Fibre_func_moddu (Op_moddu $RR) (Op_func $i) 
with Op_moddu ( Fibre_hom_moddu $RR $r ) ↪   Fibre_hom_moddu (Op_modd $RR) (Op_hom $r) 
with Op_moddu ( Productdt_moddu $T  $R ) ↪   Productdt_moddu (Op_catd $T)  (Op_mod $R)  
;

rule Op_moddu ($F ∘>>du $R)  ↪ ((Op_moddu $R) du<<∘ (Op_funcd $F))
with Op_moddu ($R du<<∘ $G)  ↪ ((Op_funcd $G) ∘>>du (Op_moddu $R));

/* (e) homdd homddu ========================== */
 
injective symbol Op_homd: Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
   [A : catd X] [B : catd Y] [II : catd I]  [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
   homd r FF RR GG →  homd (Op_hom r) (Op_funcd GG) (Op_modd RR) (Op_funcd FF); 

constant symbol Id_homd : Π [I X : cat] [xi : func X I]  [II : catd I] [XX] (F : funcd XX xi II) ,
homd  (Id_hom xi) F (Unit_modd Id_funcd Id_funcd) F;

 constant symbol Id_homdu : Π [I : cat] [A : catd I] [II] (F : funcd II Id_func A),
 homdu F (Unit_moddu Id_funcd Id_funcd) F;
 
 constant symbol Func_con_homd : Π [I X : cat] [F : func X I]  [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX F II),
homd  (Func_con_hom Z F)   FF (Unit_modd ZZ Id_funcd) (FF ∘>d ZZ) ;

constant symbol Func_cov_homd : Π [I X : cat] [xi : func X I]  [II : catd I] 
 [I'] [II'] [Z : func I I'] (ZZ : funcd II Z II') [XX] (FF : funcd XX xi II),
homd  (Func_cov_hom Z xi)  (FF ∘>d ZZ) (Unit_modd Id_funcd ZZ) FF ;

 //Comp_funcd_homd
 symbol ∘↓d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
  homd r FF RR GG → Π [I'] [Z : func I' I] [I'I'] (ZZ : funcd I'I' Z II) ,
  homd (r ∘↓ Z) (ZZ ∘>d FF) RR (ZZ ∘>d GG);
 notation ∘↓d infix left 120;
 
 rule $r ∘↓d Id_funcd ↪ $r
 // with $r ∘↓d ($K ∘> $H  )  ↪ ($r ∘↓d $H) ∘↓d $K
 with ($r ∘↓d $H) ∘↓d $K  ↪ $r ∘↓d ($K ∘>d $H  )
 with (Id_homd $F) ∘↓d $H  ↪ Id_homd ($F d<∘ $H)
 with (Func_con_homd $Z $F) ∘↓d $H  ↪ Func_con_homd $Z ($F d<∘ $H)
 with (Func_cov_homd $Z $F) ∘↓d $H  ↪ Func_cov_homd $Z ($F d<∘ $H);
 
 rule Op_homd (Op_homd $F) ↪ $F
 with Op_homd (Id_homd $F) ↪ (Id_homd (Op_funcd $F))
 with Op_homd (Func_con_homd $Z $F) ↪ Func_cov_homd (Op_funcd $Z) (Op_funcd $F)
 with Op_homd (Func_cov_homd $Z $F) ↪ Func_con_homd (Op_funcd $Z) (Op_funcd $F); 
rule Op_homd ($r ∘↓d $H) ↪ (Op_homd $r) ∘↓d (Op_funcd $H); 

// /* (f) transfd transfdu ========================== */

 injective symbol Op_transfd: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
 [r : transf R xx' R' yy'] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
  transfd r RR FF RR' GG →  transfd (Op_transf r) (Op_modd RR) (Op_funcd GG) (Op_modd RR') (Op_funcd FF);
 
constant symbol Id_transfd : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y] (RR : modd A R B),
 transfd (Id_transf R) RR Id_funcd RR Id_funcd;
  
//TODO: redo this only after def of  transfs  for sections
// constant symbol Triv_transfduu : Π (I : cat), transfdu (Terminal_moddu I) Id_funcd (Terminal_moddu I) Id_funcd; // is Id ?
//  constant symbol Triv_transfd : Π [A' B' A B: cat] [R' : mod A' B'] [F : func A' A] [R : mod A B] [G : func B' B]
//  (r'r : transf R' F R G),  transfd r'r (Terminal_modd R') (Triv_funcd F) (Terminal_modd R) (Triv_funcd G)    ;
 
 
  //Unit_con_transfd
 symbol _'∘>d : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
  Π [J: cat] [M : func J X] [JJ : catd J] (MM : funcd JJ M A), 
 homd r FF RR GG → transfd ((M)_'∘> r) (Unit_modd MM FF) Id_funcd (MM ∘>>d RR) GG; 
 notation _'∘>d infix right 80; 

 symbol ∘>d'_ : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
  [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B], 
 homd r FF RR GG → Π [J: cat] [M : func J Y] [JJ : catd J] (MM : funcd JJ M B), 
 transfd ( r ∘>'_(M) ) (Unit_modd GG MM) FF (RR d<<∘ MM ) Id_funcd;                
 notation ∘>d'_ infix left 80;
 
 rule Op_transfd (Op_transfd $rr) ↪ $rr
 with Op_transfd (Id_transfd $RR) ↪ (Id_transfd (Op_modd $RR))
 with Op_transfd (($MM)_'∘>d $rr) ↪ (Op_homd $rr) ∘>d'_ (Op_funcd $MM);
 rule Op_transfd ($rr ∘>d'_ ($MM)) ↪ (Op_funcd $MM) _'∘>d (Op_homd $rr);
 
 
 //Unit_con_transfdu
 constant symbol _'∘>du : Π [I: cat] [A : catd I] [B : catd I] [II]
 [FF : funcd II Id_func A] [RR : moddu A B] [GG : funcd II Id_func B], 
 Π [JJ : catd I] (MM : funcd JJ Id_func A),
 homdu FF RR GG → transfdu (Unit_moddu MM FF) Id_funcd (MM ∘>>du RR) GG;
 notation _'∘>du infix right 80; 
 

 //Comp_homd_transfd
 symbol '∘d : Π [A'' B' A B : cat] [S : mod A B'] [T : mod A B] 
 [X : func A'' A] [Y : func A'' B'] [G : func B' B],
 Π  [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA S BB'] [TT : modd AA T BB] [t : transf S Id_func T G]
 [A''A''] [XX : funcd A''A'' X AA] [YY : funcd A''A'' Y BB'] [GG : funcd BB' G BB]  [s : hom X S Y],
 homd s XX SS YY → transfd t SS Id_funcd TT GG → homd (s '∘ t) XX TT (YY ∘>d GG);
 notation '∘d infix right 80;

symbol ∘d' [A'' A'  A B : cat] [S : mod A' B] [T : mod A B] 
 [X : func A'' A'] [Y : func A'' B] [F : func A' A] 
 [AA' : catd A'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB] [TT : modd AA T BB] [t : transf S F T Id_func]
 [A''A''] [XX : funcd A''A'' X AA'] [YY : funcd A''A'' Y BB] [FF : funcd AA' F AA]  [s : hom X S Y]:
transfd t SS FF TT Id_funcd →  homd s XX SS YY →  homd (t ∘' s) (XX ∘>d FF) TT YY;

//  symbol ∘d' [A'' A' B' A B : cat] [S : mod A' B'] [T : mod A B] 
//  [X : func A'' A'] [Y : func A'' B'] [F : func A' A] [G : func B' B]
//  [AA' : catd A'] [BB' : catd B'] [AA : catd A] [BB : catd B] [SS : modd AA' S BB'] [TT : modd AA T BB] [t : transf S F T G]
//  [A''A''] [XX : funcd A''A'' X AA'] [YY : funcd A''A'' Y BB'] [FF : funcd AA' F AA] [GG : funcd BB' G BB]  [s : hom X S Y]:
// transfd t SS FF TT GG →  homd s XX SS YY →  homd (s '∘ t) (XX ∘>d FF) TT (YY ∘>d GG)
 notation ∘d' infix left 80;


rule Op_homd ($s '∘d $st) ↪ (Op_transfd $st) ∘d' (Op_homd $s)
with Op_homd ($st ∘d' $s) ↪ (Op_homd $s) '∘d (Op_transfd $st);

//TODO: REVIEW //SEE RULE somewhere in reverse. already solved..?
//reverse?
rule ($a '∘d  $t) ∘↓d $Z ↪ (($a ∘↓d $Z) '∘d  $t)
with ($t ∘d' $a) ∘↓d $Z ↪ ($t ∘d' ($a ∘↓d $Z)) ; 

 //Comp_homdu_transfduu
 symbol '∘du : Π [A : cat] ,
 Π [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [SS : moddu AA' BB'] [TT : moddu AA BB] 
 [AA0] [XX : funcd AA0 Id_func AA'] [YY : funcd AA0 Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
 homdu XX SS YY → transfdu SS FF TT GG → homdu (XX ∘>d FF) TT (YY ∘>d GG);
 notation '∘du infix right 80;

//  //Comp_transfduu_transfduu
//  symbol ''∘du : Π [ A : cat]
//  [AA'' : catd A] [BB'' : catd A] [AA' : catd A] [BB' : catd A] [AA : catd A] [BB : catd A] [RR : moddu AA'' BB''] [SS : moddu AA' BB'] [TT : moddu AA BB] 
//  [XX : funcd AA'' Id_func AA'] [YY : funcd BB'' Id_func BB'] [FF : funcd AA' Id_func AA] [GG : funcd BB' Id_func BB],
//  transfdu RR XX SS YY → transfdu SS FF TT GG → transfdu RR (XX ∘>d FF) TT (YY ∘>d GG);
//  notation ''∘du infix right 80;


//Comp_transfd
symbol ''∘d : Π [B'' B' A B : cat] [R : mod A B''] [S : mod A B'] [T : mod A B] 
 [Y : func B'' B']  [G : func B' B],
Π [BB'' : catd B'']  [BB' : catd B'] [AA : catd A] [BB : catd B]  [s : transf R Id_func S Y] [RR : modd AA R BB''] [t : transf S Id_func T G] [SS : modd AA S BB'] [TT : modd AA T BB] 
 [YY : funcd BB'' Y BB']  [GG : funcd BB' G BB],
transfd s RR Id_funcd SS YY → transfd t SS Id_funcd TT GG → 
transfd (s ''∘ t) RR Id_funcd TT (YY ∘>d GG);
notation ''∘d infix right 80;

symbol ∘d'' : Π [A'' A' A B : cat] [R : mod A'' B] [S : mod A' B] [T : mod A B] 
[X : func A'' A']  [F : func A' A] ,
Π [AA'' : catd A'']  [AA' : catd A']  [AA : catd A] [BB : catd B]  [s : transf R X S Id_func] [RR : modd AA'' R BB] [t : transf S F T Id_func] [SS : modd AA' S BB] [TT : modd AA T BB] 
[XX : funcd AA'' X AA'] [FF : funcd AA' F AA] ,
transfd t SS FF TT Id_funcd → transfd s RR XX SS Id_funcd → transfd (t ∘'' s) RR (XX ∘>d FF) TT Id_funcd;
notation ∘d'' infix left 80;

rule Op_transfd ($rs ''∘d $st) ↪  (Op_transfd $st) ∘d'' (Op_transfd $rs);

rule  $rs ''∘d ($st ''∘d $tu) ↪ ($rs ''∘d $st) ''∘d $tu
with  ($tu ∘d'' $st) ∘d'' $rs ↪  $tu ∘d'' ($st ∘d'' $rs);

rule  (Id_transfd _) ''∘d $r'r ↪ $r'r
with  $r'r ''∘d (Id_transfd _) ↪ $r'r;
rule  (Id_transfd _) ∘d'' $r'r ↪ $r'r
with  $r'r ∘d'' (Id_transfd _) ↪ $r'r;

 // assoc comp_transf then comp_hom
 //reverse?
 rule  $r '∘d ($rs ''∘d $st)
 ↪ ($r '∘d $rs) '∘d $st
 with ($st ∘d'' $rs) ∘d' $r
 ↪  $st ∘d' ($rs ∘d' $r);

 rule  (Func_cov_homd _ $G ) '∘d ((_) _'∘>d Id_homd $F) ↪ Id_homd ($G ∘>d $F);
 rule  (Id_homd $F ∘>d'_ (_) ) ∘d' (Func_con_homd _ $G )  ↪ Id_homd ($G ∘>d $F);
 rule  ($f '∘d ($M)_'∘>d (Id_homd Id_funcd) )  ↪ $f; 
 rule  (($M)_'∘>d (Func_cov_homd $F Id_funcd) ) ↪ (Id_transfd _)  ; 
 rule  ((Func_con_homd $F Id_funcd) ∘>d'_($M)) ↪ (Id_transfd _)  ;
 
//yoneda bijection half
rule (((Func_cov_homd $F $Z)) '∘d ((Id_funcd)_'∘>d $r)) 
↪ $r ∘↓d $Z;

//yoneda bijection half
rule (Id_funcd)_'∘>d (((Func_cov_homd $Z Id_funcd)) '∘d $t) 
↪ $t;


 // t∘(g) ∘X0 -  =  t∘(g ∘X0 -) 
 rule ($M)_'∘>d ($g '∘d (($X0)_'∘>d $t))
 ↪ (($M)_'∘>d $g) ''∘d (($M ∘>d $X0)_'∘>d $t)
 with  (($t ∘>'_ ($X0) ∘' $g)) ∘>'_($M)
 ↪  ($t ∘>'_($M ∘> $X0)) ∘'' ($g ∘>'_($M));

 
// //  /* (8) fibrations: cartesian transport / fibred yoneda ========================== */

constant symbol Comma_con_homd : Π [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y),
Π [J] [x' : func J I]  [J0] [F : func J0 A] [x'x : func J J0] (x'x_ : hom x'x (Unit_mod F x) x') , 
homd ( x'x_ ) (Comma_con_intro_funcd BB ( x'x_ '∘  ((F)_'∘> r) )) (Unit_modd (Comma_con_comp_funcd R BB F) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB y) x');
constant symbol Comma_cov_homd' : Π [A B I : cat] (AA : catd A) [R : mod A B]  [x : func I A] [y : func I B] (r : hom x R y),
Π [K] [y' : func K I]  [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y' (Unit_mod y G) y'y) ,
homd ( y'y_ ) (Fibre_elim_funcd (Fibre_catd AA x) y') (Unit_modd (Comma_cov_intro_funcd AA r) (Comma_cov_comp_funcd AA R G) ) (Comma_cov_intro_funcd AA ( (r ∘>'_(G)) ∘' y'y_ ));


type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I]  [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J]  [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
  (((Comma_con_homd BB (x'x_ '∘  ((F)_'∘> r)) x''x'_) ) '∘d  (( _ ) _'∘>d  (Comma_con_homd BB r x'x_))) ;
//Π A: cat, Π B: cat, Π I: cat, Π R: mod A B, Π BB: catd B, Π x: func I A, Π y: func I B, Π r: hom x R y, Π J: cat, Π x': func J I, Π J0: cat, Π F: func J0 A, Π x'x: func J J0, Π x'x_: hom x'x (Unit_mod F x) x', Π J': cat, Π x'': func J' J, Π J0': cat, Π F': func J0' J0, Π x''x': func J' J0', Π x''x'_: hom x''x' (Unit_mod F' x'x) x'', homd (x''x'_ '∘ (F' _'∘> x'x_)) (Comma_con_intro_funcd BB (x''x'_ '∘ (F' _'∘> (x'x_ '∘ (F _'∘> r))))) (Comma_con_comp_funcd (F ∘>> R) BB F' ∘>>d Unit_modd (Comma_con_comp_funcd R BB F) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB (y <∘ x')) x'' ∘>d Fibre_elim_funcd (Fibre_catd BB y) x')

type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I]  [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J]  [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
 ((Comma_con_homd BB r (x''x'_ '∘  ((F')_'∘> x'x_ ))) ) ;
//Π A: cat, Π B: cat, Π I: cat, Π R: mod A B, Π BB: catd B, Π x: func I A, Π y: func I B, Π r: hom x R y, Π J: cat, Π x': func J I, Π J0: cat, Π F: func J0 A, Π x'x: func J J0, Π x'x_: hom x'x (Unit_mod F x) x', Π J': cat, Π x'': func J' J, Π J0': cat, Π F': func J0' J0, Π x''x': func J' J0', Π x''x'_: hom x''x' (Unit_mod F' x'x) x'', homd (x''x'_ '∘ (F' _'∘> x'x_)) (Comma_con_intro_funcd BB ((x''x'_ '∘ (F' _'∘> x'x_)) '∘ ((F' ∘> F) _'∘> r))) (Unit_modd (Comma_con_comp_funcd R BB (F' ∘> F)) (Comma_con_intro_funcd BB r)) (Fibre_elim_funcd (Fibre_catd BB y) (x' <∘ x''))

//Cannot solve x''x'_ '∘ (F' _'∘> (x'x_ '∘ (F _'∘> r))) ≡ (x''x'_ '∘ (F' _'∘> x'x_)) '∘ ((F' ∘> F) _'∘> r).

//PROBLEM REVIEW  
type λ [A B I : cat] [R : mod A B] (BB : catd B) [x : func I A] [y : func I B] (r : hom x R y)
 [J] [x' : func J I]  [J0] [F : func J0 A] [x'x] (x'x_ : hom x'x (Unit_mod F x) x')
 [J'] [x'' : func J' J]  [J0'] [F' : func J0' J0] [x''x'] (x''x'_ : hom x''x' (Unit_mod F' x'x) x''),
  (((Comma_con_homd BB (x'x_ '∘  ((F)_'∘> r)) x''x'_) ) '∘d  (( _ ) _'∘>d  (Comma_con_homd BB r x'x_)))
       = ((Comma_con_homd BB r (x''x'_ '∘  ((F')_'∘> x'x_ ))) ); 


//TODO: REVIEW NOPE, too general ?
//  .constant symbol Comma_homd : Π [A B I : cat] (AA : catd A) [R : mod A B] (BB : catd B) 
// [x : func I A] [y : func I B],
// Π   [J0] [F : func J0 A] [x'x : func I J0] (x'x_ : hom x'x (Unit_mod F x) Id_func) , 
// Π   [J1] [G : func J1 B] [y'y : func I J1] (y'y_ : hom Id_func (Unit_mod y G) y'y) ,
// Π  (s : hom x'x (F ∘>> R) y) (t : hom x (R <<∘ G) y'y) (r : hom x'x (F ∘>> (R <<∘ G)) y'y), 
// homd r (Comma_con_intro_funcd BB s) 
// ((Comma_con_comp_funcd R BB F) ∘>>d ((Comma_modd AA R BB) d<<∘ (Comma_cov_comp_funcd AA R G))) 
//  (Comma_cov_intro_funcd AA t); //redo

 //example of fibred profunctor: squares fibred by their diagonal
constant symbol Comma_homd : Π [A B I : cat] (R : mod A B) [x : func I A] [y : func I B],
Π [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func), 
Π [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y'),
Π (s : hom x' (F ∘>> R) y) (t : hom x (R <<∘ G) y') (r : hom x' (F ∘>> (R <<∘ G)) y'), 
π (( x'x '∘  ((F)_'∘> t) ) = r) → π (( (s ∘>'_(G)) ∘' yy' ) = r) → 
homd r (Comma_con_intro_funcd (Terminal_catd B) s) 
 ((Comma_con_comp_funcd R (Terminal_catd B) F) ∘>>d ((Comma_modd (Terminal_catd A) R (Terminal_catd B)) d<<∘ (Comma_cov_comp_funcd (Terminal_catd A) R G)))
 (Comma_cov_intro_funcd (Terminal_catd A) t);

opaque symbol Comma_homd'_lemma1 : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
Π   [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func) , 
Π   (t : hom x R y) (r : hom x' (F ∘>> R) y), 
Π   [K0] [F' : func K0 J0] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x') Id_func) , 
π (( x'x '∘  ((F)_'∘> t) ) = r) →  π (( ( x''x' '∘ ( (F')_'∘> x'x)  ) '∘  ((_)_'∘> t) ) = (x''x' '∘ ((F')_'∘> r))) ≔
begin 
  assume _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; assume prf;
  rewrite left prf; reflexivity;
end;

opaque symbol Comma_homd'_lemma2 : Π [A B I : cat]  [R : mod A B]  [x : func I A] [y : func I B],
Π   [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y') ,
Π  (s : hom x R y)  (r : hom x (R <<∘ G) y'), 
Π   [K0] [F' : func K0 A] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x) Id_func) , 
π (( (s ∘>'_(G)) ∘' yy' ) = r) →  
π (( (( x''x' '∘ ( (F')_'∘> s) ) ∘>'_(G)) ∘' yy'  ) =  (x''x' '∘ ((F')_'∘> r))) ≔
begin 
  assume A B I R x y J1 G y' yy' s r K0 F' x'' x''x'; assume prf;
  rewrite left prf; apply (associativity_con_metatheorem yy' s x''x');
end;

symbol todo_rule_Comma_homd'_Comma_con_homd' ≔ λ [A B I : cat]  (R : mod A B)  [x : func I A] [y : func I B],
λ   [J0] [F : func J0 A] [x' : func I J0] (x'x : hom x' (Unit_mod F x) Id_func) , 
λ   [J1] [G : func J1 B] [y' : func I J1] (yy' : hom Id_func (Unit_mod y G) y') ,
λ  (s : hom x' (F ∘>> R) y) (t : hom x (R <<∘ G) y') (r : hom x' (F ∘>> (R <<∘ G)) y'), 
λ   [K0] [F' : func K0 J0] [x'' : func I K0] (x''x' : hom x'' (Unit_mod F' x') Id_func) , 
λ (prf : π (( x'x '∘  ((F)_'∘> t) ) = r) ) (prf2 : π (( (s ∘>'_(G)) ∘' yy' ) = r)),
 (Comma_con_homd (Terminal_catd B) s x''x' )  '∘d 
   (( _ ) _'∘>d (Comma_homd R x'x yy' s t r ) prf prf2)
= (Comma_homd R ( x''x' '∘ ( (F')_'∘> x'x)  ) yy' (x''x' '∘ ((F')_'∘> s)) t (x''x' '∘ ((F')_'∘> r)) 
     (Comma_homd'_lemma1 x'x t r x''x' prf) 
     (Comma_homd'_lemma2 yy' s  r x''x' prf2) );


constant symbol Comma_con_elim_funcd : Π [I X : cat] (G : func X I) [II : catd I] (II_isf : isFibration_con II) [JJ : catd I] /* JJ is non cart */
(FF : funcd JJ Id_func II), //OK
funcd (Comma_con_catd (Unit_mod G Id_func) JJ) G II;

constant symbol Comma_con_elim_homd : Π [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F),
homd f (Comma_con_intro_funcd JJ f) (Unit_modd (Comma_con_elim_funcd G II_isf FF) Id_funcd) ((Fibre_elim_funcd JJ F) ∘>d FF);

rule (Comma_con_comp_funcd _ _ $H) ∘>d (Comma_con_elim_funcd $G $II_isf $FF) 
   ↪  (Comma_con_elim_funcd ($H ∘> $G) $II_isf $FF);


type λ [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F)
[X'0] (x'0x : func X'0 X) [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 

 ((Comma_con_homd JJ f x'0x' ) '∘d
 (( _ ) _'∘>d (Comma_con_elim_homd G II_isf FF f))) 
 = (Comma_con_elim_homd (x'0x ∘> G) II_isf FF (x'0x' '∘ ( (_ ) _'∘> f)));

symbol Fibration_con_funcd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] [JJ : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II),
Π (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F), 
funcd JJ x'x (Fibre_catd II G); // aka f*FF

symbol Fibration_cov_funcd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] 
[JJ : catd X'] [F : func X' I]  [II : catd I] /* II coCart */
(FF : funcd JJ F II) (f : hom F (Unit_mod Id_func G) x'x ), 
funcd JJ x'x  (Fibre_catd II G); // aka f!FF

constant symbol Fibration_con_elim_homd :  Π [I X X'  : cat] [x'x : func X' X] [G : func X I] 
 [JJ : catd X'] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
 (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F),
  homd f (Fibration_con_funcd II_isf FF f) (Unit_modd (Fibre_elim_funcd II G)  Id_funcd) FF;
 
constant symbol Fibration_con_intro_homd : Π [I X X'  : cat] [x'x : func X' X] [G : func X I] [JJ : catd X'] [F : func X' I] [II : catd I] (II_isf : isFibration_con II)
 (FF : funcd JJ F II) (f : hom x'x (Unit_mod G Id_func) F) 
 [X'0 : cat] [x'0x : func X'0 X] [X'' : cat] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
 (x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x') [KK : catd X'0] (GG : funcd KK x'0x (Fibre_catd II G)) [HH : funcd (Fibre_catd JJ x''x') x''x'0 KK],
homd ((x'0x' '∘ ((x'0x)_'∘> f))) HH (Unit_modd (GG ∘>d (Fibre_elim_funcd II G)) Id_funcd) ((Fibre_elim_funcd JJ (x''x')) ∘>d FF) →  
homd x'0x' HH (Unit_modd GG (Fibration_con_funcd II_isf FF f)) (Fibre_elim_funcd JJ (x''x'));


// naturality
rule @∘>d _ _ _ _ _ _ $Z _ $ZZ  (Fibration_con_funcd $II_isf $FF $f)  ↪ (Fibration_con_funcd $II_isf ($ZZ ∘>d $FF) ($f ∘↓ $Z)) ;
rule (Fibration_con_intro_homd $II_isf $FF $f  $x'0x' $GG $ii) ∘↓d (Fibre_elim_funcd _ $zz) 
  ↪ (Fibration_con_intro_homd $II_isf $FF  $f  ($x'0x' ∘↓ $zz) $GG ($ii ∘↓d (Fibre_elim_funcd _ $zz))) ;

// rule (@∘↓d _ _ _ _ _ _ _ _ _ _ _ _ _ (Fibration_con_intro_homd $G $FF $f $x'0x $x'0x' $GG $ii) _ $z _ $zz) 
//    ↪ (Fibration_con_intro_homd $G $FF  $f $x'0x ($x'0x' ∘↓ $z) $GG ($ii ∘↓d $zz)) ;

// ??TODO outer naturality of fibred yoneda: Fibration_con_intro_homd''' applied to Fibration_con_intro_homd''' (xyz ∘> $f) to relate Fibration_con_funcd''' (xyz ∘> $f)  to Fibration_con_funcd''' $f
// so that so that composing with it is the corresponding action, which is then obviously natural (that is, the component-wise-specified output transf as univhoms is then natural)

// universality/deformation
rule (Fibration_con_intro_homd $II_isf $FF $f  $x'0x' $GG $ii) '∘d (($GG)_'∘>d (Fibration_con_elim_homd $II_isf $FF $f)) ↪ $ii;

//TODO: normality, lift id to id




//TODO: REVIEW SLOW
//-NOPE-->-FAILS ONLY BECAUSE LACKING THIS WHICH IS SLOW , FAILS ALSO BECAUSE NO BETA RULE
// rule (@Fibration_con_funcd _ _ _ _ $x'x $G $FF ((Func_con_hom $G $x'0x ∘>'_ $F) ∘' $f) )
//  ↪ (Fibration_con_funcd $G $FF $f ) ;
// rule (@Fibration_con_funcd _ _ _ _ ($x'x ∘> $x'0x)  $G $x'y $F $II $FF (@∘' _ _ _ _ _ (Unit_mod ($x'0x ∘> $G) $F) _ $x'x $x'y _ _ (Func_con_hom $G $x'0x ∘>'_ $F)  $f) )
//  ↪ (@Fibration_con_funcd _ _ _ _ $x'x ($x'0x ∘> $G) $x'y $F $II $FF $f ) ;

rule (Comma_con_intro_funcd $JJ $f) ∘>d (Comma_con_elim_funcd $G $II_isf $FF)
↪ (Fibration_con_funcd $II_isf ((Fibre_elim_funcd $JJ _) ∘>d $FF) $f) ∘>d (Fibre_elim_funcd _ $G) ;

assert [I X : cat] [G : func X I]  [II : catd I] (II_isf : isFibration_con II) [JJ : catd I] (FF : funcd JJ Id_func II)
 [J : cat] [x: func J X] [F : func J I] (f : hom x (Unit_mod G Id_func) F) ⊢
(Comma_con_intro_funcd JJ f) ∘>d (Comma_con_elim_funcd G II_isf FF)
≡ (Fibration_con_funcd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f) ∘>d (Fibre_elim_funcd II G);
// : funcd (Fibre_catd JJ F) (x ∘> G) II

//funcd (Fibre_catd JJ F) x (Comma_con_catd (Unit_mod G Id_func) JJ)
//funcd (Comma_con_catd (Unit_mod G Id_func) JJ) G II

// funcd (Fibre_catd JJ F) x (Fibre_catd II G)
//funcd (Fibre_catd II G) G II

//NOTE this says that the universal comparaison morphism for the algebraic Comma_con_elim_homd,
// which would use some absent universal intro rule similar as Fibration_con_intro_homd, is still definable
type λ [I X X'  : cat] [x'x : func X' X] (G : func X I) //OK
[JJ : catd I] [F : func X' I]  [II : catd I] (II_isf : isFibration_con II)
(FF : funcd JJ Id_func II) (f : hom x'x (Unit_mod G Id_func) F)
[X'0] [x'0x : func X'0 X] [X''] [x''x' : func X'' X'] [x''x'0 : func X'' X'0] 
(x'0x' :  hom x''x'0 (Unit_mod x'0x x'x) x''x'), 
((Comma_con_homd JJ f x'0x' ) '∘d
((_) _'∘>d (Func_con_homd (Comma_con_elim_funcd G II_isf FF) (Comma_con_intro_funcd JJ f)))) 
=  ((Fibration_con_intro_homd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f x'0x' (Fibre_intro_funcd _ G x'0x (Comma_con_elim_funcd (x'0x ∘> G) II_isf FF))
                  (Comma_con_elim_homd (x'0x ∘> G) II_isf FF (x'0x' '∘ (x'0x _'∘> f))))
     '∘d (( _ ) _'∘>d 
               (Func_con_homd (Fibre_elim_funcd II G) (Fibration_con_funcd II_isf ((Fibre_elim_funcd JJ F) ∘>d FF) f))));


//rewrite rule to make concrete how is the derived transport for the pullback of fibration,
// definable from the transport for the original fibration
symbol Pullback_Fibration_con_funcd [I X X'  : cat] [x'x : func X' X] [G : func X I] 
[JJ : catd X'] [F : func X' I] [I0] (i0 : func I I0) (II0 : catd I0) (II0_isf : isFibration_con II0)
(FF : funcd JJ F (Fibre_catd II0 i0)) (f : hom x'x (Unit_mod G Id_func) F):
funcd JJ x'x  (Fibre_catd (Fibre_catd II0 i0) G)
≔ Fibration_con_funcd II0_isf (FF ∘>d (Fibre_elim_funcd II0 i0))
      (f '∘ ( ( G ) _'∘> (Func_con_hom i0 Id_func) ) );

rule @Fibration_con_funcd _ _ _ _ $G _ _ (Fibre_catd $II0 $i0) (Fibre_isFibration_con $II0 $II0_isf $i0) $FF $f
 ↪  Pullback_Fibration_con_funcd $i0 $II0 $II0_isf $FF $f;

// grammatical (univalent) universe by declaring an inverse to the transport for the universe fibration
injective symbol Universe_Fibration_con_funcd_inv : Π [X Y: cat] (F : func X Universe_con_cat) (G : func Y Universe_con_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) 
→ hom xy (Unit_mod G Id_func) F;

injective symbol Universe_Fibration_cov_funcd_inv : Π [X Y: cat] (F : func X Universe_cov_cat) (G : func Y Universe_cov_cat) 
[xy : func X Y], funcd (Fibre_catd Universe_cov_catd F) xy (Fibre_catd Universe_cov_catd G) 
→ hom F (Unit_mod Id_func G) xy;

injective symbol Universe_Fibration_con_funcd  [X Y: cat] [F : func X Universe_con_cat] [G : func Y Universe_con_cat] 
[xy : func X Y] (h : hom xy (Unit_mod G Id_func) F) :
funcd (Fibre_catd Universe_con_catd F) xy (Fibre_catd Universe_con_catd G) ≔ 
 Fibration_con_funcd Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd F) h;

rule Fibration_con_funcd Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) (Universe_Fibration_con_funcd_inv $F $G $HH) ↪ $HH;
rule (Universe_Fibration_con_funcd_inv $F $G (@Fibration_con_funcd _ _ _ _ $G _ _ _ Universe_con_isFibration_con (Fibre_elim_funcd Universe_con_catd $F) $h)) ↪ $h;


// //  /* (10) fibrations: topology ========================== */
 
constant symbol Triv_covering : Π [X Y I : cat] [R : mod X Y] [G : func I Y] , 
covering (Terminal_modd R) (Func_funcs G);

constant symbol Triv_coveringu : Π (I : cat), 
coveringu (Terminal_moddu I) (Func_funcs Id_func);

constant symbol Fibre_coveringu : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
[RR : modd A R B]  [G : func I Y] [H : funcs G B],
 covering RR H →  Π [F : func I X] (r : hom F R G),
 coveringu (Fibre_hom_moddu RR r)  (Fibre_intro_funcs _ G Id_func H );

  constant symbol Total_covering : Π [X Y I : cat] [A : catd X] [R : mod X Y] [B : catd Y]
[RR : modd A R B]  [G : func I Y] [H : funcs G B],
(Π [F : func I X] (r : hom F R G), coveringu (Fibre_hom_moddu RR r)  (Fibre_intro_funcs _ G Id_func H )) → 
 covering RR H ;

constant symbol Glue_transfd : Π [X Y Y': cat] [A' : catd X] [A : catd X] [B' : catd Y'] [B: catd Y]  [yy' : func Y Y'] [R' : mod X Y'] [R : mod X Y]
[rr' : transf R Id_func R' yy'] [RR : modd A R B] [FF : funcd A Id_func A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'],
Π [I : cat] [G : func I Y] [H : funcs G B] , covering RR H →
(Π [F : func I X] (r : hom F R G), transfdu  (Fibre_hom_moddu RR r) (Fibre_functor_funcd FF F)  
  (Fibre_hom_moddu (Sheaf_con_modd  RR') (r '∘ rr')) (Fibre_functor_funcd GG G)) → 
transfd rr' RR FF (Sheaf_con_modd RR') GG;

















//TODO: /!\ /!\  REVIEW ALL THIS SECTION /!\  /!\ 
//  /* (7) fibrations: semantics ========================== */
//TODO: /!\ /!\  REVIEW ALL THIS SECTION /!\  /!\ 

symbol Total_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
modd A R B → Π [X'] [x : func X' X] [Y'] [y : func Y' Y] [S : mod X' Y'] (r : transf S x R y), mod (Total_cat A x) (Total_cat B y);

symbol Total_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
(RR : modd A R B), Π [X'] [x : func X' X] [Y'] [y : func Y' Y] [S : mod X' Y'] (r : transf S x R y), transf (Total_mod RR r) (Total_proj_func A x ) S (Total_proj_func B y );

symbol Total_hom_mod : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y],
modd A R B → Π [I] [I'] (i : func I' I) [x : func I X]  [y : func I Y] (r : hom x R y), 
mod (Total_cat A (i ∘> x)) (Total_cat B (i ∘> y));
//TODO Total_hom_modd_proj_transf  ??

rule Total_hom_mod $648696 ($648732 ∘> $648728) $648712 ↪ Total_hom_mod $648696 $648732 ($648712 ∘↓ $648728);

symbol Total_hom_modd_proj_transf : Π [X Y : cat] [A : catd X] [R : mod X Y] [B : catd Y]
(RR : modd A R B), Π [I] [I'] (i : func I' I) [x : func I X]  [y : func I Y] (r : hom x R y), 
transf (Total_hom_mod RR i r) (Total_proj_func A (i ∘> x) ∘> (i ∘> x)) R (Total_proj_func B (i ∘> y) ∘> (i ∘> y));

symbol Total_moddu_mod : Π [I : cat] [A : catd I] [B : catd I],
moddu A B → Π [I'] (i : func I' I) , mod (Total_cat A i) (Total_cat B i);


//lacked? could use Total_modd_proj_transf
//  symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
//  (RR : moddu A B), Π [I'] (i : func I' I), transf (Total_moddu_mod RR i) (Total_proj_func A i Id_func) (Unit_mod0 I') (Total_proj_func B i Id_func);
symbol Total_moddu_proj_transf : Π [I : cat] [A : catd I] [B : catd I]
(RR : moddu A B), Π [I'] (i : func I' I), 
transf (Total_moddu_mod RR i) Id_func (Unit_mod (Total_proj_func A i) Id_func) (Total_proj_func B i);

//  symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
//   [A : catd X] [B : catd Y] [FF : funcd (Terminal_catd I) F A] [RR : modd A R B] [GG : funcd (Terminal_catd I) G B],
//  homd r FF RR GG  → Π [I'] (i : func I' I), hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);
symbol Total_hom : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
[A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
homd r FF RR GG  → //Π [I'] [i : func I' I][I'I'] (ii : funcd I'I' i II), 
Π [I'] (i : func I' I), 
hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);
//  symbol Total_hom' : Π [X Y I: cat] [F : func I X] [R : mod X Y] [G : func I Y] [r : hom F R G]
//   [A : catd X] [B : catd Y] [II] [FF : funcd II F A] [RR : modd A R B] [GG : funcd II G B],
//  homd r FF RR GG  → Π [I'] [i : func I' I][I'I'] (ii : funcd I'I' i II), 
//  hom (Total_func FF i) (Total_hom_mod RR i r) (Total_func GG i);

//  symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
//  [FF : funcd (Terminal_catd I) Id_func A] [RR : moddu A B] [GG : funcd (Terminal_catd I) Id_func B], homdu FF RR GG → Π [I'] (i : func I' I), 
//  hom (Total_func FF i) (Total_moddu_mod RR i) (Total_func GG i);
symbol Total_homdu_hom: Π [I: cat] [A : catd I] [B : catd I]
[II] [FF : funcd II Id_func A] [RR : moddu A B] [GG : funcd II Id_func B], homdu FF RR GG → Π [I'] (i : func I' I), 
hom (Total_func FF i) (Total_moddu_mod RR i) (Total_func GG i);

//  symbol Total_transf: Π [X Y X' Y': cat] [A' : catd X'] [A : catd X] [B' : catd Y'] [B: catd Y] [xx' : func X X'] [yy' : func Y Y'] [R' : mod X' Y'] [R : mod X Y]
//  [t : transf R xx' R' yy' ] [RR : modd A R B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B'] ,
//  transfd t RR FF RR' GG → transf (Total_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);

//  // symbol Total_transfdu_transf : Π [I X' Y': cat] [A' : catd X'] [A : catd I] [B' : catd Y'] [B: catd I] [xx' : func I X'] [yy' : func I Y'] [R' : mod X' Y']
//  // [r : hom xx' R' yy' ] [RR : moddu A B] [FF : funcd A xx' A'] [RR' : modd A' R' B'] [GG : funcd B yy' B' ],
//  // transfdu r RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_mod RR') (Total_func GG);

//  //com
// //  symbol Total_transfduu_transf : Π [I : cat] [A' : catd I] [A : catd I] [B' : catd I] [B: catd I]
// //  [RR : moddu A B] [FF : funcd A Id_func A'] [RR' : moddu A' B'] [GG : funcd B Id_func B'],
// //  transfdu RR FF RR' GG → transf (Total_moddu_mod RR) (Total_func FF) (Total_moddu_mod RR') (Total_func GG);

//  rule Total_moddu_mod (Terminal_moddu $I) $i ↪ (Unit_mod0 _)
rule Total_moddu_mod (Terminal_moddu $I) $i ↪ (Unit_mod Id_func Id_func)
//TODO with Total_moddu_mod (Productdt_moddu $R) Id_func ↪ $R
//with Total_moddu_mod (Unit_moddu $F $G) ↪ (Unit_mod (Total_func $F) (Total_func $G));
//  with Total_moddu_mod (Unit_moddu0 $AA) $i ↪ (Unit_mod0 (Total_cat $AA $i))
with Total_moddu_mod (Unit_moddu (@Id_funcd _ $AA) Id_funcd) $i ↪ (Unit_mod (@Id_func (Total_cat $AA $i)) Id_func)
with  Total_moddu_mod ($FF ∘>>du $RR) $i ↪ (Total_func $FF $i) ∘>> (Total_moddu_mod $RR $i)
with  Total_moddu_mod ($RR du<<∘ $GG ) $i ↪ (Total_moddu_mod $RR $i) <<∘ (Total_func $GG $i);

//  rule Total_moddu_proj_transf (Terminal_moddu $X) $i ↪ (Id_transf (Unit_mod0 _))
rule Total_moddu_proj_transf (Terminal_moddu $X) $i ↪ (Id_transf (Unit_mod Id_func Id_func))
//TODO with Total_moddu_proj_transf (Productdt_moddu $R) Id_func ↪ (Terminal_transf $R)
;

rule @Total_mod _ _ _ _ _ (Terminal_modd $R) _ _ _ _ $S $r ↪ $S
//with Total_mod (Unit_modd $FF $GG) ↪ (Unit_mod (Total_func $FF) (Total_func $GG))
//with Total_mod (Unit_modd0 $AA) ↪ (Unit_mod0 (Total_cat $AA))
//with Total_mod (Comma_modd $R) ↪ (Comma_mod $R)

//TODO review this generalize Id_func
with Total_mod ($R ⊗d $S) (Tensor_cov_transf Id_func $p $q) ↪ (Total_mod $R $p) ⊗ (Total_mod $S $q)
//with  Total_mod ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR)
//with  Total_mod ($RR d<<∘ $GG ) ↪ (Total_mod $RR) <<∘ (Total_func $GG)
;

rule Total_modd_proj_transf (Terminal_modd $R) $r ↪ (Id_transf _)
//with Total_modd_proj_transf (Comma_modd $R) ↪ (Comma_transf $R)
//.?with  Total_mod_proj ($FF ∘>>d $RR) ↪ (Total_func $FF) ∘>> (Total_mod $RR);
;


//  rule Total_hom_mod (Unit_modd0 $AA)  $i (Id_hom $F) ↪ (Unit_mod0 (Total_cat $AA ($i ∘> $F)));
// rule Total_hom_mod (Unit_modd0 $AA)  $i (Id_hom $F) ↪ (Unit_mod  (@Id_func (Total_cat $AA ($i ∘> $F))) Id_func );
rule Total_hom_mod (Unit_modd (@Id_funcd _ $AA) Id_funcd)  $i (Id_hom $F) 
 ↪ (Unit_mod  (@Id_func (Total_cat $AA ($i ∘> $F))) Id_func );


//   rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr _ $i) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
//   ($r ∘↓ $i);


//TODO: REVIEW THIS AND UNCOMMENT
// rule (@Total_hom _ _ _ _ _ _ $r _ _ $II _ $RR _ $rr _ $i ) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
// ($r ∘↓ (Total_proj_func $II $i ∘> $i  ));



// rule (@Total_hom' _ _ _ _ _ _ $r _ _ $II _ $RR _ $rr _ $i $I'I' $ii ) '∘ (Total_hom_modd_proj_transf $RR $i $r) ↪ 
// ($r ∘↓ (Total_proj_func $I'I' Id_func $i  ));

//rule (@Total_hom _ _ _ _ _ _ $r _ _ _ $RR _ $rr) '∘ (Total_modd_proj_transf $RR) ↪  $r;==

//  rule //Total_hom (Comma_homd $r) ↪ Comma_hom $r
//   Total_hom ($rr ∘↓d $Z) $i ↪ (Total_hom $rr ($i ∘> $Z)) ;
rule //Total_hom (Comma_homd $r) ↪ Comma_hom $r
//todo erase
//Total_hom ($rr ∘↓d (Triv_funcd $Z)) $i ↪ (Total_hom $rr ($i ∘> $Z)) 
Total_hom ($rr ∘↓d (Fibre_elim_funcd _ $Z)) $i ↪ (Total_hom $rr ($i ∘> $Z))  ;

rule Total_hom (Id_homd $F) $i ↪ Id_hom (Total_func $F $i);

//rule (@Total_homdu_hom $I _ _ _ $RR _ $rr _  $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Id_hom Id_func;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?

//  rule (@Total_homdu_hom $I _ _ _ _$RR _ $rr _ $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Id_hom Id_func;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?
rule (@Total_homdu_hom $I _ _ $II _ $RR $GG $rr _ $i) '∘ (Total_moddu_proj_transf $RR $i) ↪  Func_con_hom _ _;//TODO: INSTEAD Id_hom or Func_con_hom or Id_hom ?

rule Total_homdu_hom (Id_homdu $F)$i ↪ Id_hom (Total_func $F $i);



/* Voila */