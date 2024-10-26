/* https://github.com/1337777/cartier/blob/master/cartierSolution16.lp
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_polynomial_univalence.pdf

Kosta Dosen's univalent polynomial functorial programming, 
   with locally ringed sites schemes and their functorial-of-points semantics
*/

require open modos.cartierSolution13;

// OUTLINE
// # SECTION 3: COVERING SIEVES
      // ATTENPT 1 VERSION
      // ATTEMPT 2 VERSION
      // ATTEMPT 3 VERSION
      // ATTEMPT 4 VERSION

///------------------------ ATTENPT 4 VERSION - TO BE CONTINUED ---------------------

/* I could be a site too... then collection of classifiers is locally constant */
constant symbol sieve : Π (S : cat) (I : cat), mod S I;

// this is instance of predicate version sum_mod with E : mod S I ≔ Unit_mod Id_func F
/* constant */ symbol sieve_mod : Π [S : cat]  
[I] [F : func I S] [D] [K : func I D], Π (ff : hom F (sieve S D) K), 
mod S I /* this cov index is intended to be same/invariant remembering the cov subindex in the contra index */;

//subobject predicatess version
symbol sum_mod : Π [S : cat]  
[I ] [E : mod S I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K), 
mod S I /* this cov index is intended to be same/invariant remembering the cov subindex in the contra index */;

// some form of adjunction transpose
constant symbol sum_mod_intro_transf : Π [S : cat]  
[I ] [E : mod S I ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve S D) K)
[J] [G  : func J S] [i : func J I] (e : hom G E i ),
transf (sieve_mod (e '∘ ff)) Id_func (sum_mod ff) i; 

// note that _'sieve∘> becomes instance of _'sieveCtx∘>
constant symbol _'sieve∘> : Π [A B : cat]  [I] [F : func I A]  [R : mod A B]  [G : func I B]
[D] [K : func I D], Π (ff : hom F (sieve A D) K),
hom F R G → transf (sieve_mod ff) Id_func R G;
notation _'sieve∘> infix right 80; 
//todo add two naturalities, one:   (g o> s) .> r =  g o> (s .> r)   .... 
rule ($g '∘ (Id_func)_'∘> $s) '∘ ($ff _'sieve∘> $r)
  ↪ $g '∘ (_)_'∘> ($s '∘ ($ff _'sieve∘> $r));
///   s .> (g o> r) =  (s .> g) o> r 
rule $s '∘ ($ff _'sieve∘> ($g '∘ (_)_'∘> $r))
  ↪ ($s '∘ ($ff _'sieve∘> $g)) '∘ (_)_'∘> $r ;

  // nope? ... note R is still non-dependent type over E...
constant symbol _'sieveCtx∘> : Π [A B : cat]  [R : mod A B] 
[I ]  [G : func I B] [E : mod A I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D], Π (ff : transf E Id_func (sieve A D) K),
transf E Id_func R G → transf (sum_mod ff) Id_func R G;
notation _'sieveCtx∘> infix right 80; 
// so _'sieveCtx∘> will only compute when its input is constructored, and thereafter according to the rules of _'sieve∘> , so no need to duplicate corresponding rules
rule ($x '∘ (sum_mod_intro_transf $ff $e)) '∘ ( $ff _'sieveCtx∘> $r) 
↪ $x '∘ (($e '∘ $ff) _'sieve∘> ($e '∘ $r));
// rule ( ($g '∘ (Id_func)_'∘> $s) '∘ (sum_mod_intro_transf $ff $e) ) '∘ ( $ff _'sieveCtx∘> $r) 
// ↪ $g '∘ (_)_'∘>  ($s '∘ (($e '∘ $ff) _'sieve∘> ($e '∘ $r))); // no need to duplicate

// now add rules as above pointwise at each e : E  ??
//   (g o> s_(e)) .> r_(e) =  g o> (s_(e) .> r_(e)) but that would not use the general operation .... 
// or necessary to have new versions of operations in-context for each of the ealier ones? they wouldd look useless like instance of the above for maximal sieve? .. like a tensor   E tensor (Unit_mod Id_func F?) ? or rather dependent sum over E ?    (e : L -> E x Unit_mod Id_func L)  ... requires (internal) classifiers?... 
/// anyway is this general operation necessary yet unless go all the way to the dependent versions of everything (here: (dependnt-term r, dependent-type R, dependent-type-nonprop ff)) q
/// well the above is already the term-contextual (dependnt-term r, non-dependent-type R, dependent-type ff) version of the earlier operations .. so in addition to the tensor-contextual (dependnt-term r, non-dependent-type R and ff) versions half-done

  // max sieve
  constant  symbol maximal_sieve : Π [S : cat] [I] (F : func I S) [D] (K : func I D), hom F (sieve S D) K;

  constant  symbol maximal_sieve_ctx : Π [S : cat] [I] (E : mod S I /* ≔ Unit_mod Id_func F */ )  [D] (K : func I D), transf E Id_func (sieve S D) K;

  rule $e '∘ (maximal_sieve_ctx $E $K)
  ↪ maximal_sieve _ _ ;

  type λ [S : cat] [I] [F : func I S] [D] (K : func I D)
  [J] [G : func J S] [x : func J I] (g : hom G (Unit_mod Id_func F) x),
  (g '∘ (_)_'∘> (maximal_sieve F K))
  = (maximal_sieve G (x ∘> K));

  rule ($g '∘ (Id_func)_'∘> (maximal_sieve $F $K))
 ↪ (maximal_sieve _ _);

  type λ [S : cat] [I] [F : func I S] [D] [K : func I D]
  (ff : hom F (sieve S D) K) [J] [G : func J S]  [x : func J I]
  (g_ : hom G (sieve_mod ff) x), 
  g_ '∘ (ff _'sieve∘> ff)
  = (maximal_sieve G (x ∘> K));

  rule $g_ '∘ ($ff _'sieve∘> $ff)
  ↪ (maximal_sieve _ _);

constant symbol maximal_sieve_intro_hom : Π [S : cat] [I] (F : func I S) [D] (K : func I D)
[J] [G : func J S] [x : func J I] (g_ : hom G (Unit_mod Id_func F) x),
hom G (sieve_mod (maximal_sieve F K)) x /* generalize this Id_func */;

//UNCOMMENT
rule (maximal_sieve_intro_hom $F $K $g_) '∘ ((maximal_sieve $F $K) _'sieve∘> $r)
↪ $g_ '∘ (_)_'∘> $r;

//    // pullback of sieve, defined symbol, could eventually compute to concrete sieve
  symbol pullback_sieve  [S : cat] [I] [F : func I S] [D] [K : func I D]
  (ff : hom F (sieve S D) K) [J] [G : func J S] [x : func J I] (g : hom G (Unit_mod Id_func F) x)
  :  hom G (sieve S D) (x ∘> K)
  ≔ (g '∘ (_)_'∘> ff);



/// should be as instance of general pullback of mod ? so sieve_mod computes... or nope, only implicitly/semantically fibred...
constant symbol pullback_sieve_elim_transf : Π [S : cat] [I] [F : func I S] [D] [K : func I D]
(ff : hom F (sieve S D) K) [J] [G : func J S] [x : func J I] (g : hom G (Unit_mod Id_func F) x), 
transf (sieve_mod (pullback_sieve ff g)) Id_func (sieve_mod ff) x ;

//extensional form necessary? (similar as for adjunctions)
// note this is commutation of groundings for sieves as dependent types over representatable

//UNCOMMENT
 rule ($x '∘ (pullback_sieve_elim_transf  $ff $g)) '∘ ($ff _'sieve∘> $r)
↪  $x '∘ ((pullback_sieve $ff $g) _'sieve∘> ($g '∘ (_)_'∘> $r));


//  // intersection sieve, todo? via product of presheaves
// intersection is ("non-dependent") instance of sum (of pullbacks of single sieve) along another sieve
constant symbol intersection_sieve : Π [S : cat] [I] [F : func I S] [D] [K : func I D]
(ff ff' : hom F (sieve S D) K /* need not share same K... when sum form */), hom F (sieve S D) K; 

/* constant? */ constant symbol intersection_sieve_projL_transf : Π [S : cat] [I] [F : func I S] [D] [K : func I D]
(ff ff' : hom F (sieve S D) K),
transf (sieve_mod (intersection_sieve ff ff')) Id_func  (sieve_mod ff) Id_func;

//extensional form necessary? (similar as for adjunctions)
// note this is commutation of groundings for sieves as dependent types over representatable

//UNCOMMENT
rule ($x '∘ (intersection_sieve_projL_transf  $ff $ff')) '∘  ($ff _'sieve∘>  $r)
↪  $x '∘  ((intersection_sieve  $ff $ff') _'sieve∘>  $r) ;

// wait... this looks like reverse of sieve-yoneda.. but sieve classifer would need to be sheaf, so somehow sheafify first.. implicitly sheafified?... and maybe gluing into sieve-classifier doesnt need the domain sieve to be covering ? .. or this sum_sieve_v0 operation (even untruncated) means that sieve-classifier is a sheaf for atomic topology where all sieve-closures are maximal ?
// in fact gluing from transf should not be direct to hom element, instead it should modalextend to closure of sieve... and when this closure is max sieve then can apply indentity hom and reduce to hom element
//..so because gluing is already present then sheafification of the sieve-classifier won't need more than the separation step (the step where sieves are collapsed to their closure)

  constant symbol sum_sieve : Π [S : cat] [I] [F : func I S] [D] [K : func I D], 
 Π (ff : hom F (sieve S D) K) [D'] [H : func I D'], 
 transf (sieve_mod ff) Id_func (sieve S D') H
 → hom F (sieve S D') (   H);

 constant symbol sum_sieve_intro_transf : Π [S : cat] [I] [F : func I S][D] [K : func I D], 
Π (ff : hom F (sieve S D) K) [D'] [H : func I D'] (T_ : transf (sieve_mod ff) Id_func (sieve S D') H),
Π [J] [G : func J S] [f_i: func J I] (f : hom G (sieve_mod ff) f_i),
transf (sieve_mod (f '∘ T_)) Id_func (sieve_mod (sum_sieve ff T_)) f_i;

//UNCOMMENT COMMENT DURING DEV
//SLOW 10 seconds
rule ($g '∘ (sum_sieve_intro_transf $ff $T_ $f)) '∘ ((sum_sieve $ff _ /* $T_ DONT SPECIFY */ ) _'sieve∘> $r)
↪  $g '∘ ( ($f '∘ $T_) _'sieve∘> ($f '∘ ( $ff _'sieve∘> $r)));

/// alternative definition of intersection sieve (positive/negative form ... similar as primitive product vs inductive sum... so both ok)
symbol intersection_as_sum_pullback_sieve [S : cat] [I] [F : func I S] 
[D] [K : func I D] (ff : hom F (sieve S D) K) 
[D'] [H : func I D'] (T_ : hom F (sieve S D') H) : hom F (sieve S D') (   H)
 ≔ sum_sieve ff (ff _'sieve∘> T_) ;
 

/// covering, sheaves

constant symbol site : cat → TYPE ; 
constant symbol site_Set : cat → Set; rule τ (site_Set $C) ↪ site $C;

 //classifier for sheaves, not internalized
 constant symbol smod : Π [S : cat] (S_site : site S) (I : cat), TYPE ;
 constant symbol smod_Set : Π [S : cat] (S_site : site S) (I : cat), Set ;
 rule τ (@smod_Set $S $A $B) ↪ @smod $S $A $B;

 /// unlike smod_mod the internal ssieve_sieve can be non-constant
 constant symbol smod_mod : Π [S : cat] [S_site : site S] [I : cat], smod S_site I → mod S I ;

symbol mod_smod : Π [S : cat] (S_site : site S) [I : cat], mod S I → smod S_site I ;
 constant symbol eta_smod_transf : Π [S : cat] (S_site : site S) [I : cat] (R : mod S I),
   transf R Id_func (smod_mod (mod_smod S_site R)) Id_func ;

rule  (mod_smod $S_site (@smod_mod _ $S_site _ $R)) ↪ $R;

constant symbol glue : Π [A B : cat] (A_site : site A)  [R : smod A_site B] [I] [G : func I B] 
(L : mod A I),
transf L Id_func (smod_mod R) G
→  transf (smod_mod (mod_smod A_site L)) Id_func (smod_mod R) G;

rule ($x '∘ (eta_smod_transf $A_site $L)) '∘ (glue  $A_site $L $rr)
↪ $x '∘ $rr;
// rule ($x '∘ (eta_smod_transf $A_site $L)) '∘ (glue  $A_site $L ($rr ''∘ sieve_ssieve $B_site $D))
// ↪ ($x '∘ $rr) '∘ sieve_ssieve $B_site $D;
//todo abstract this then glue along sieves becomes instance

// classifier for closed sieves, internalized
/// does anything gained from viewing it as a smod of sieve?
constant symbol ssieve [S : cat] (S_site : site S) (I : cat) : smod S_site I;
// ≔ mod_smod S_site (sieve S I) ;

/// unlike smod_mod the internal ssieve_sieve can be non-constant
 /*  constant */  symbol ssieve_sieve : Π [S : cat] (S_site : site S) [I : cat],
 //todo allow I to vary
 Π [J] [F : func J S] [K], hom F (smod_mod (ssieve S_site I))  K → hom F (sieve S I) K;

constant symbol sieve_ssieve /* eta of sheafification (here is only separation step) */  [S : cat] (S_site : site S) (I : cat):
 transf (sieve S I) Id_func (smod_mod (ssieve S_site I)) Id_func ;
//   ≔ eta_smod_transf S_site (sieve S I) ;

rule (ssieve_sieve $S_site $ff) '∘ sieve_ssieve $S_site _ ↪  $ff;

constant symbol ssieve_smod : Π [S : cat] [S_site : site S]  [I] [F : func I S] [D] [K : func I D], Π (ff : hom F (smod_mod (ssieve S_site D)) K), 
smod S_site I;

rule mod_smod $S_site (sieve_mod $ff) 
  ↪ (ssieve_smod (($ff '∘ (sieve_ssieve $S_site _))));

/* this cov index is intended to be same/invariant remembering the cov subindex in the contra index */
// this rule not work (slow)
// .rule (sieve_mod ($ff '∘ (ssieve_sieve_v0 $A_site $D)))
// ↪ (smod_mod (ssieve_smod $ff));
rule (sieve_mod (ssieve_sieve _ $ff))
 ↪ (smod_mod (ssieve_smod $ff));

symbol glue_sieve_mod_def  [A B : cat] (A_site : site A) [I] [F : func I A]  [R : smod A_site B]  [G : func I B] [D] [K : func I D] (ff : hom F (sieve A D) K)
(rr : transf (sieve_mod ff) Id_func (smod_mod R) G) :
 transf (smod_mod (ssieve_smod ((ff '∘ (sieve_ssieve A_site _))))) Id_func (smod_mod R) G 
 ≔ glue A_site (sieve_mod ff) rr;


 symbol glue_sieve_mod_endo_def  [A B : cat] (A_site : site A) [I] [F : func I A]  [R : smod A_site B]  [G : func I B] [D] [K : func I D] (ff : hom F (sieve A D) K)
 (rr : transf (sieve_mod ff) Id_func (smod_mod R) G)
 : transf (sieve_mod (ssieve_sieve A_site (ff '∘ (sieve_ssieve A_site D)))) Id_func (smod_mod R) G
 ≔  glue_sieve_mod_def A_site ff rr ;

 symbol glue_sieve_mod_closed_def  [A  : cat] [A_site : site A] [I] [F : func I A]  [D] [K : func I D] [ff : hom F (sieve A D) K] [J] [G : func J A] [D'] [K' : func J D'] [gg : hom G (smod_mod (ssieve A_site D')) K'] [H : func I J]
 (t_ : transf (sieve_mod ff) Id_func (smod_mod (ssieve_smod gg)) H)
: transf (sieve_mod ((ssieve_sieve A_site (ff '∘ (sieve_ssieve A_site D)))) ) Id_func (smod_mod (ssieve_smod gg)) H ≔ glue A_site (sieve_mod ff) t_;


/// ======== with context ===============
 
 constant  symbol ssieve_sieve_ctx : Π [S : cat] (S_site : site S) [I : cat],
 //todo allow I to vary
 Π [J] [E : mod S J] [K], transf E Id_func (smod_mod (ssieve S_site I)) K → transf E Id_func (sieve S I) K;

 rule  $e '∘ (ssieve_sieve_ctx $S_site $T_)
 ↪ (ssieve_sieve $S_site ($e '∘ $T_));
 

/* non-constnant ? */
constant /* constant? */ symbol sum_smod : Π [S : cat] [S_site : site S] 
[I ] [E : mod S I ] /* not necessarily smod base */ [D] [K : func I D], 
Π (ff : transf E Id_func (smod_mod (ssieve S_site D)) K), 
smod S_site I ;

// some form of adjunction transpose ... nope, slow rule with nested 'o, try ssieve_smod_ctx_v7''_transf as combinator
constant symbol sum_smod_intro_transf : Π [S : cat]  (S_site : site S) 
[I ] [E : mod S I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D], Π (ff : transf E /* understood E is already smod */ Id_func (smod_mod (ssieve S_site D)) K)
[J] [G  : func J S] [i : func J I] (e : hom G E i ),
transf (smod_mod (ssieve_smod (e  '∘ (/* glue S_site E */ ff) ))) Id_func (smod_mod (sum_smod ff)) i; 

rule mod_smod $S_site (sum_mod $ff_) 
↪ (sum_smod ( glue $S_site _ ($ff_ ''∘ (sieve_ssieve $S_site _))));


rule (sum_mod (ssieve_sieve_ctx _ $ff))
↪ (smod_mod (sum_smod $ff));

// definable in terms of glue  (glue_sieve_mod_def)
symbol glue_sieve_mod_ctx [A B : cat] (A_site : site A) [I]  [R : smod A_site B]  [G : func I B] [E : mod A I ]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sum_mod ff) Id_func (smod_mod R) G)
: transf (smod_mod (mod_smod A_site (sum_mod ff))) Id_func (smod_mod R) G ≔ glue A_site (sum_mod ff) rr;

symbol glue_sieve_mod_ctx_endo [A B : cat] (A_site : site A) [I]   [R : smod A_site B]  [G : func I B] [E : mod A I  ]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sum_mod ff) Id_func (smod_mod R) G)
: transf (sum_mod ((ssieve_sieve_ctx A_site (glue A_site _  (ff ''∘ (sieve_ssieve A_site D)) )) )) Id_func (smod_mod R) G
≔ glue_sieve_mod_ctx A_site ff rr  ;


//eta as operation?  .. or reverae to previoua with trick in _op
/// /!\ YESSSS!
 rule ($x '∘ ((sum_smod_intro_transf $A_site (  ( ( _ /* DON'T SPECIFY THIS (glue $A_site $E ($ff ''∘ sieve_ssieve $A_site $D)) */)) ) (@'∘ _ _ _ _ $E _ _ _ _  $e  (eta_smod_transf $A_site $E))))) '∘  (glue $A_site (@sum_mod  _ _ $E _ _  $ff) $rr)
↪  $x '∘ (glue $A_site (sieve_mod ($e '∘ $ff)) ((sum_mod_intro_transf $ff $e) ''∘ $rr));

assert [A B : cat] [A_site : site A] [I]   [R : smod A_site B]  [G : func I B] [E : mod A I /* ≔ Unit_mod Id_func F */ ]  [D] [K : func I D] (ff : transf E Id_func (sieve A D) K)
(rr : transf (sum_mod ff) Id_func (smod_mod R) G) [J] (e_X: func J A) (e_Y: func J I) (e: hom e_X E e_Y) 
[J'] [X : func J' _] [Y : func J' _] (x : hom X (smod_mod (mod_smod A_site (sieve_mod (e '∘ ff)))) Y) ⊢
(x '∘ ((sum_smod_intro_transf A_site (  ( (/* DON'T SPECIFY THIS IN RULE */ (glue A_site E (ff ''∘ sieve_ssieve A_site D)))) ) (@'∘ _ _ _ _ E _ _ _ _  e  (eta_smod_transf A_site E))))) '∘  (glue A_site (@sum_mod  _ _ E _ _  ff) rr)
≡ x '∘ (glue A_site (sieve_mod (e '∘ ff)) ((sum_mod_intro_transf ff e) ''∘ rr));
verbose 3;

///above had earlier problems
// Cannot solve $254537 ≡ $254567
// Cannot solve $254537 ≡ $254567
// Cannot solve sum_mod $254573 ≡ sum_mod $254573
// Cannot solve sieve_mod ($254547 '∘ $254573) ≡ sieve_mod ($254547 '∘ $254573)
// Cannot solve $254567 ≡ $254537
// Cannot solve $254537 ≡ $254567
// Cannot solve ($254547 '∘ eta_smod_transf $254511 $254537) '∘ glue $254511 $254567 ($254573 ''∘ sieve_ssieve $254511 $254569) ≡ ($254547 '∘ $254573) '∘ sieve_ssieve $254511 $254569
// Unable to prove type preservation.


// no intro rules, just a rule to compute the underlying sieve where intros happen
constant  symbol maximal_ssieve : Π [S : cat] (S_site : site S) [I] (F : func I S) [D] (K : func I D), hom F (smod_mod (ssieve S_site D)) K;


// type λ [S : cat] (S_site : site S) I (F : func I S) [D] (K : func I D),
// (ssieve_sieve S_site ((maximal_sieve F K) '∘ (sieve_ssieve S_site D)))  
// = (maximal_sieve F K);

// rule (ssieve_sieve $S_site ((maximal_sieve $F $K) '∘ (sieve_ssieve $S_site $D))) 
// ↪ (maximal_sieve $F $K);

rule ((maximal_sieve $F $K) '∘ (sieve_ssieve $S_site $D))
↪ (maximal_ssieve $S_site $F $K);


//HERE
///UNCOMMENT
// .rule (ssieve_sieve _ (maximal_ssieve $S_site $F $K))  
// ↪ (maximal_sieve $F $K); 

constant symbol intersection_ssieve : Π [S : cat] (S_site : site S) [I] [F : func I S] [D] [K : func I D]
(ff ff' : hom F (smod_mod (ssieve S_site D)) K /* need not share same K... when sum form */), hom F (smod_mod (ssieve S_site D)) K; 

rule ((intersection_sieve $ff $ff') '∘ (sieve_ssieve $S_site $I)) 
↪ (intersection_ssieve $S_site (($ff '∘ (sieve_ssieve $S_site $I))) (($ff' '∘ (sieve_ssieve $S_site $I)) )); 

rule (ssieve_sieve $S_site (intersection_ssieve $S_site $ff $ff'))
↪  (intersection_sieve (ssieve_sieve $S_site $ff) (ssieve_sieve $S_site $ff')) ; 

  constant symbol sum_ssieve : Π [S : cat] (S_site : site S) [I] [F : func I S] [D] [K : func I D], 
Π (ff : hom F (sieve S D) K) /* not necessarily ssieve base */ [D'] [H : func I D'], 
transf (sieve_mod ff) Id_func (smod_mod (ssieve S_site D')) H
→ hom F (smod_mod (ssieve S_site D')) (   H);

rule (sum_sieve $ff $gg_ ) '∘ (sieve_ssieve $S_site _)
↪ (sum_ssieve $S_site (ssieve_sieve _ ($ff '∘ (sieve_ssieve $S_site _))) ( glue $S_site _ ($gg_ ''∘ (sieve_ssieve $S_site _))));

rule (ssieve_sieve $S_site (sum_ssieve $S_site $ff $gg_))
↪ (sum_sieve $ff (ssieve_sieve_ctx $S_site $gg_));


//// ======================== affine schemes

// // ringed_locally is similar as some general D(f) ... 
// // outputs sieve where the function is invertible (for affine is singleton sieve on primitive Zarisky D(r) ascheme_basic_func below)

//rings 
constant symbol ring : Set → TYPE ; 
symbol ring_type [R_Set : Set] (R : ring R_Set) : TYPE ≔ τ R_Set;

symbol ring_one : Π [R_Set : Set] (R : ring R_Set), ring_type R;
symbol ring_mult : Π [R_Set : Set] (R : ring R_Set) (r s : ring_type R), ring_type R;
symbol ring_inv [R_Set : Set] (R : ring R_Set) (r : ring_type R): TYPE 
 ≔ τsub_ (λ r_inv, ring_mult R r r_inv = ring_one R);

//role appear only later, for unimodular sieve
symbol ring_add : Π [R_Set : Set] (R : ring R_Set) (r s : ring_type R), ring_type R;

constant symbol ring_morph : Π [R_Set : Set] (R : ring R_Set) [T_Set : Set] (T : ring T_Set), TYPE;
constant symbol ring_morph_Set : Π [R_Set : Set] (R : ring R_Set) [T_Set : Set] (T : ring T_Set), Set;
rule τ (ring_morph_Set $R $T) ↪ ring_morph $R $T;
symbol ring_morph_fun : Π [R_Set : Set] [R : ring R_Set] [T_Set : Set] [T : ring T_Set], ring_morph R T → ring_type R → ring_type T;

// ring modules

constant symbol ringmod : Π [A B : cat] (M : mod A B), TYPE ;
constant symbol ringmod_Set : Π [A B : cat] (M : mod A B), Set ;
rule τ (ringmod_Set $M) ↪ ringmod $M;

symbol ringmod_ring : Π [A B : cat] [I] (U : func I A) [M_mod : mod A B] (M : ringmod M_mod) (G : func I B), ring (hom_Set U M_mod G);
symbol ringmod_con_ring_morph : Π [A B : cat] [I] [U : func I A] 
[V : func I A] (v : hom V (Unit_mod Id_func U) Id_func) [M_mod : mod A B] (M : ringmod M_mod) (G : func I B), ring_morph (ringmod_ring U M G) (ringmod_ring V M G) ;
rule ring_morph_fun (ringmod_con_ring_morph $v $M $G) $m 
↪ $v '∘ (_)_'∘> $m ;

//localization of rings

 constant symbol ring_loc : Π [R_Set : Set] (R : ring R_Set) (f : ring_type R) [Rf_Set : Set] (Rf : ring Rf_Set), TYPE;
 constant symbol ring_loc_intro : Π [R_Set : Set] [R : ring R_Set] [f : ring_type R] [Rf_Set : Set] [Rf : ring Rf_Set], ring_loc R f Rf → 
 ring_type R →  /* /!\ TODO: bool or nat denominator → */ ring_type Rf;
 constant symbol ring_loc_intro_rel : Π [R_Set : Set] [R : ring R_Set] [f : ring_type R] [Rf_Set : Set] [Rf : ring Rf_Set] (Rf_ring_loc : ring_loc R f Rf), 
Π (r s : ring_type R), π (r = s) → /* /!\ TODO:  f^k f^n r = f^k f^m s → */  
π (ring_loc_intro Rf_ring_loc r = ring_loc_intro Rf_ring_loc s);
// ?should skip inductive-set elimination and go directly to univ algebra? and should be univ formulation for rings or for  R-algebras?
constant symbol ring_loc_elim : Π [R_Set : Set] [R : ring R_Set] [f : ring_type R] [Rf_Set : Set] [Rf : ring Rf_Set], ring_loc R f Rf → 
 Π [T_Set : Set] [T :  ring T_Set],
 /* ring map (by the way making T into R-alg), not present when univ for R-algebras */
 Π (m :  ring_morph R T),
  ring_inv T (ring_morph_fun m f) → 
 ring_morph Rf T;
// /!\ TODO: add two computation rules for both hypothesis: when input is (r,0) = r/f^0 ; when input is (r, 1) = r/f^1
rule ring_morph_fun (ring_loc_elim $Rf_loc $m $mf_inv) (ring_loc_intro $Rf_loc $r)
↪ ring_morph_fun $m $r;

//TODO obvious definition
symbol ring_loc_ring_inv [R_Set : Set] [R : ring R_Set] [f : ring_type R] [Rf_Set : Set] [Rf : ring Rf_Set] (Rf_loc : ring_loc R f Rf): ring_inv Rf (ring_loc_intro Rf_loc f) ≔ /*TODO: ring_loc_intro Rf_loc ring_one 1 */ DEBUG_ADMIT;


//affine schemes TODO: CHANGE THIS TO AN INTERFACE WITH (CAT,SITE,STRUCT SHEAF)-PARAMETERS SO THAT SLICES OF GENERAL SCHEME CAN SATISFY THIS AFFINE INTERFACE ... (I.E WITHOUT USING MORPHISMS OF SCHEMES...)

//todo? via concrete cat instead?  (because must use Terminal_cat ?)
constant symbol ascheme_cat : Π [R_Set : Set] (R : ring R_Set), cat;
 // primitive Zarisky  D(r)... for affine ringed_locally is singleton sieve on this 
constant symbol ascheme_basic_func : Π [R_Set : Set] (R : ring R_Set) (r : ring_type R), func Terminal_cat (ascheme_cat R);
constant symbol ascheme_join_func : Π [R_Set : Set] [R : ring R_Set] (U V : func Terminal_cat (ascheme_cat R)), func Terminal_cat (ascheme_cat R);
constant symbol ascheme_mult_hom : Π [R_Set : Set] (R : ring R_Set) (s r: ring_type R), 
 hom (ascheme_basic_func R (ring_mult R s r)) (Unit_mod Id_func (ascheme_basic_func R r)) Id_func;
 constant symbol ascheme_mult_hom' : Π [R_Set : Set] (R : ring R_Set) (s r: ring_type R), 
 hom (ascheme_basic_func R (ring_mult R s r)) (Unit_mod Id_func (ascheme_basic_func R s)) Id_func;
 constant symbol ascheme_radical_hom' : Π [R_Set : Set] (R : ring R_Set) (s r: ring_type R), 
 hom (ascheme_basic_func R (ring_mult R s r)) (Unit_mod Id_func (ascheme_basic_func R (ring_mult R s (ring_mult R r r)))) Id_func;
 constant symbol ascheme_radical_hom : Π [R_Set : Set] (R : ring R_Set) (r: ring_type R), 
 hom (ascheme_basic_func R r) (Unit_mod Id_func (ascheme_basic_func R (ring_mult R r r))) Id_func;

 ///extensional (non intrinsically-manifest) truncation. question: truncate only in the base subcat?
 // used to extensionally manually prove the compatibility of cocones over diagrams of joins
 constant symbol ascheme_poset_truncate : Π [R_Set : Set] [R : ring R_Set] [r s: ring_type R]
 (f f' : hom (ascheme_basic_func R r) (Unit_mod Id_func (ascheme_basic_func R s)) Id_func),
  π  (f = f');

  constant symbol ascheme_site : Π [R_Set : Set] (R : ring R_Set), site (ascheme_cat R);
 constant symbol ascheme_smod : Π [R_Set : Set] (R : ring R_Set), smod (ascheme_site R) Terminal_cat;
 constant symbol ascheme_ring : Π [R_Set : Set] (R : ring R_Set) (U : func Terminal_cat (ascheme_cat R)), ring (hom_Set U (smod_mod (ascheme_smod R)) Id_func);
constant symbol ascheme_ring_loc : Π [R_Set : Set] (R : ring R_Set) (f : ring_type R), ring_loc R f (ascheme_ring R (ascheme_basic_func R f));


type  λ [R_Set : Set] (R : ring R_Set) (r s: ring_type R) (x : ring_type R),
(ascheme_mult_hom R s r) '∘ (_) _'∘> (ring_loc_intro (ascheme_ring_loc R r) x)
= ring_loc_intro (ascheme_ring_loc R (ring_mult R s r)) (ring_mult R s x) ;

rule (ascheme_mult_hom $R $s $r) '∘ (_) _'∘> (ring_loc_intro (ascheme_ring_loc $R $r) $x)
↪ ring_loc_intro (ascheme_ring_loc $R (ring_mult $R $s $r)) (ring_mult $R $s $x) ;

type  λ [R_Set : Set] (R : ring R_Set) (r s: ring_type R) (x : ring_type (ascheme_ring R (ascheme_basic_func R r)) ),
(ascheme_mult_hom R s r) '∘ (_) _'∘> x;

type  λ [R_Set : Set] (R : ring R_Set) (r s: ring_type R) (x : hom (ascheme_basic_func R r) (smod_mod (ascheme_smod R)) Id_func),
(ascheme_mult_hom R s r) '∘ (_) _'∘> x;


// locally ringed sites

constant symbol loc : Π [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
 (O_ring : ringmod (smod_mod O)), TYPE;
constant symbol loc_inv_sieve : Π [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
[O_ring : ringmod (smod_mod O)],
loc O_ring →
Π [U : func Terminal_cat S] (f : hom U (smod_mod O) Id_func), hom U (sieve S Terminal_cat) Id_func;

constant symbol loc_inv_sieve_intro_hom : Π [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
[O_ring : ringmod (smod_mod O)] (D : loc O_ring)  [U : func Terminal_cat S] (f : hom U (smod_mod O) Id_func),
Π [V : func Terminal_cat S] (v : hom V (Unit_mod Id_func U) Id_func) (f_inv : ring_inv (ringmod_ring V O_ring Id_func) (v '∘ (_)_'∘> f )),
hom V (sieve_mod (loc_inv_sieve D f)) Id_func;
//?todo: add that projection to underlying arrow is inv ?

// analogue of Vakil's qcqs-sheme lemma:  ( compat family = ) lim_V_a (O_X(V_a : DD(f))) =  O_X(U)[1/f]    
constant symbol loc_inv_elim : Π [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
[O_ring : ringmod (smod_mod O)] (D : loc O_ring) [U : func Terminal_cat S] (f : hom U (smod_mod O) Id_func)
[OU_f_Set : Set] [OU_f : ring OU_f_Set] (Of_loc : ring_loc (ringmod_ring U O_ring Id_func) f OU_f) ,
// 1. ?should be ring morphisms? how? make transf a ring when target is a ringmod
// 2. ?should instead generalize to any target where f is inv?
transf (sieve_mod (loc_inv_sieve D f)) Id_func (smod_mod O) Id_func → ring_type OU_f; 

//TODO: when loc_inv_elim is given as input to loc-extensions of restriction maps then the output is the corresponding componet of loc_inv_elim's transf

type λ [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
[O_ring : ringmod (smod_mod O)] (D : loc O_ring) [U : func Terminal_cat S] (f : hom U (smod_mod O) Id_func)
[OU_f_Set : Set] [OU_f : ring OU_f_Set] (Of_loc : ring_loc (ringmod_ring U O_ring Id_func) f OU_f)
(g_ : transf (sieve_mod (loc_inv_sieve D f)) Id_func (smod_mod O) Id_func )
// instead? (v : hom V (sieve_mod (loc_inv_sieve D f)) Id_func)
[V : func Terminal_cat S] (v : hom V (Unit_mod Id_func U) Id_func) (f_inv : ring_inv (ringmod_ring V O_ring Id_func) (v '∘ (_)_'∘> f )),
ring_morph_fun (ring_loc_elim  Of_loc (ringmod_con_ring_morph v O_ring Id_func) f_inv) (loc_inv_elim D f Of_loc g_ )
 = (loc_inv_sieve_intro_hom D f v f_inv) '∘ g_ ; 
// . rule ring_loc_elim  $Of_loc $O_ringV) (λ x_u, (v '∘ (_)_'∘> f )) f_inv (loc_inv_elim D f Of_loc g_ )
// = (loc_inv_sieve_intro_hom D f v f_inv) '∘ g_ ; 

//schemes 

//NOTE: DO NOT USE ISOMORPHISMS TO AFFINE SCHEMES, INSTEAD REPEAT THE AFFINE STORY IN THE RELATIVE SLICE UNDER EACH OPEN OF THE (COVERING) SIEVE OF THE SCHEME ... SO ON AN AFFINE OPEN, The SCHEME'S DD(f) SIEVE BECOMES A SINGLETON SIEVE GENERATED BY AN AFFINE-LIKE D(f) OBJECT
//ASK THAT RESTRICTIONS OF smod O|_U TO SLICES SATISFIES THE AFFINE SCHEME INTERFACE
constant symbol scheme : Π [S : cat] [S_site : site S] [O : smod S_site Terminal_cat] 
[O_ring : ringmod (smod_mod O)] (D : loc O_ring)
[T : func Terminal_cat S] (C :/* may not cover? */ hom T (sieve S Terminal_cat) Id_func), TYPE;

//TODO: how glue in slice relate to glue in base, via commuting with adjunction-transposes coming from sigma-pullpack-pushforward topos-morphism produced by continuous (and cocontinuous) site-morphism with continuous right adjoint

// note use Elements cat to express commutative   diagrams, but commutativity must hold definitionally (by computation)

constant symbol Elements_con_cat : Π [B C : cat] (R : mod B C), cat;
constant symbol Elements_con_proj_func : Π [B C : cat] (R : mod B C),
func (Elements_con_cat R) B;

constant symbol Elements_con_proj_cov_func : Π [B C : cat] (R : mod B C),
func (Elements_con_cat R) C;

symbol Elements_con_proj_hom : Π [B C : cat] [R : mod B C] [J]
(r : func J (Elements_con_cat R)),  hom (r ∘> Elements_con_proj_func _ ) R (r ∘> Elements_con_proj_cov_func _ );

//todo : relax (Terminal_func I) to any x ?
constant symbol Elements_con_intro_func : Π [B C I : cat] [R : mod B C]  [y : func I B]  [x : func I C]  (r : hom y R x),
func I (Elements_con_cat R);
rule $F ∘> (@Elements_con_intro_func _ _ _ _ $y $x $r) ↪ (@Elements_con_intro_func _ _ _ _ ($F ∘> $y) ($F ∘> $x) ($r ∘↓ $F));

rule  (@Elements_con_intro_func _ _ _ _ $y  $x $r ∘> Elements_con_proj_func _) ↪  $y;

rule  (@Elements_con_intro_func _ _ _ _ $y  $x $r ∘> Elements_con_proj_cov_func _) ↪  $x;

rule (Elements_con_proj_hom ((@Elements_con_intro_func _ _ _ _ $y  $x $r))) ↪  $r;
rule (Elements_con_proj_hom $rr) ∘↓ $F ↪   (Elements_con_proj_hom ($F ∘> $rr));

//TODO: this should not be constant ... it should rewrite to id when G is id
constant symbol Elements_con_comp_func : Π [B C I : cat] (R : mod B C) (G : func I B),
func (Elements_con_cat (G ∘>> R)) (Elements_con_cat R);

rule  (Elements_con_comp_func $R $G ∘> (Elements_con_proj_func _)) ↪ (Elements_con_proj_func ($G ∘>> $R)) ∘> $G;

//todo erase the less general Elements_con_intro_hom ? or while Unit_mod should be general to accomodate both con and cov, then in individual instances of con (cov) should use only the corresponding version of Unit_mod Id_func X (Unit_mod X Id_func)
//todo both triangles version separately, which when combined (definitionally or via equation\|) give a square
//constant symbol Elements_con_intro_cov_hom
constant symbol Elements_con_intro_hom : Π [B C I : cat] [R : mod B C]  [y : func I B] [x : func I C]   (r : hom y R x),
Π [K] [y' : func K I] [K0] [G : func K0 B] [y'y : func K K0] (y'y_ : hom y'y (Unit_mod G y) y') ,
hom (Elements_con_intro_func( y'y_ '∘  ((G)_'∘> r)  )) (Unit_mod (Elements_con_comp_func R G) (Elements_con_intro_func r)) y';

/// the extra (Id_hom _) ∘>'_(_) ∘' is used to pull G out
rule (Func_cov_hom (Elements_con_proj_func $R) _) ∘>'_(_) ∘'  (Elements_con_intro_hom $r $y'y_) ↪ (Id_hom _) ∘>'_(_) ∘' $y'y_ ;

// v2 looks better, without pulling extra contra G out 
constant symbol Elements_con_intro_hom_v2 : Π [B C I : cat] [R : mod B C]  (r : func I (Elements_con_cat R)),
Π [K] [y' : func K I] [y'y : func K B] (y'y_ : hom y'y (Unit_mod Id_func (r ∘> Elements_con_proj_func _)) y') ,
hom (Elements_con_intro_func( y'y_ '∘  ((_)_'∘> (Elements_con_proj_hom r))  )) (Unit_mod Id_func r) y';

rule (Func_cov_hom (Elements_con_proj_func $R) _) ∘>'_(_) ∘'  (Elements_con_intro_hom_v2 $r $y'y_) ↪  $y'y_ ;

symbol Elements_con_functorial_func : Π [B C C' : cat] [R : mod B C]  [R' : mod B C']  [G : func C C']
(t : transf R Id_func /* generalize Id_func */ R' G) ,
 func (Elements_con_cat R) (Elements_con_cat R');

rule (Elements_con_intro_func ($g_)) ∘> Elements_con_functorial_func $t
  ↪ (Elements_con_intro_func ($g_ '∘ $t) );

rule  Elements_con_functorial_func $g ∘> Elements_con_proj_func _
↪  Elements_con_proj_func  _ ;


///slice site

// nope not via Elements ... hmm yep
constant symbol slice_site : Π [S : cat] (S_site : site S) [I] (U : func I S), site (Elements_con_cat (Unit_mod Id_func U));
// this description works only because slice projection is cocontinuous and continuous site morphism
constant symbol slice_pullback_smod : Π [S : cat] [S_site : site S] [J : cat] [I] (U : func I S) , smod S_site J → smod (slice_site S_site U) J ;
//  constant symbol slice_pullback_smod_proj_hom : Π [S : cat] [S_site : site S] [J : cat] [I] (U : func I S) (M : smod S_site J),
// transf (smod_mod (slice_pullback_smod U M)) Id_func ((Elements_con_proj_func _) ∘>> (smod_mod M)) Id_func;
constant symbol slice_pullback_smod_intro_hom : Π [S : cat] [S_site : site S] [J : cat] [I] (U : func I S) (M : smod S_site J)
[J'] [F : func J' _ ] [G : func J' _ ],
hom (F ∘> (Elements_con_proj_func _)) (smod_mod M) G →  hom F (smod_mod (slice_pullback_smod U M)) G;
//TODO: add naturalities

//TODO: how glue in slice relate to glue in base, via commuting with adjunction-transposes coming from sigma-pullpack-pushforward topos-morphism produced by continuous (and cocontinuous) site-morphism with continuous right adjoint


//=======================

// REST OF THE INTERFACE OF AFFINE SCHEME

//TODO: USE SLICE CATEGORY TO EXPERESS UNIVERSALITY FOR INTERSECTION (AND UNION), BUT THESE ARE OPTIONAL?

// skewed arguments: general left argument but basic right argument in the join/meet (necessarily both) operations, for easier confluence/metatheoretical analysis, but computationally the alternative should be feasible
// maybe join is misleading word, it is not the limit/universal property directly which is of interest, but the covering sieve property whis is of interest
constant symbol ascheme_join'_func : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  func Terminal_cat (ascheme_cat R);

  //definable as in image of sieve? or say that the sieve element action reduces to this arrow action?
constant symbol ascheme_join'_introL_hom :
  Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom U (Unit_mod Id_func (ascheme_join'_func U r)) Id_func;

constant symbol ascheme_join'_introR_hom :
  Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom (ascheme_basic_func R r) (Unit_mod Id_func (ascheme_join'_func U r)) Id_func;

constant symbol ascheme_join'_sieve : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom (ascheme_join'_func U r) (sieve (ascheme_cat R) Terminal_cat) Id_func;

rule (ascheme_join'_sieve $U $r) '∘ (sieve_ssieve (ascheme_site $R) Terminal_cat)
↪ maximal_ssieve (ascheme_site $R) ((ascheme_join'_func $U $r)) Id_func;

// see ascheme_join'_sieve_introR_hom
constant symbol ascheme_join'_sieve_introL_hom : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
hom U (sieve_mod (ascheme_join'_sieve U r)) Id_func ;
constant symbol ascheme_join'_sieve_introR_hom : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
hom (ascheme_basic_func R r) (sieve_mod (ascheme_join'_sieve U r)) Id_func ;

rule (@ascheme_join'_sieve_introL_hom _ $R $U $r) '∘ ((ascheme_join'_sieve $U $r) _'sieve∘> $t)
↪ (ascheme_join'_introL_hom $U $r) '∘ ((_)_'∘> $t) ;
rule (@ascheme_join'_sieve_introR_hom _ $R $U $r) '∘ ((ascheme_join'_sieve $U $r) _'sieve∘> $t)
↪ (ascheme_join'_introR_hom $U $r) '∘ ((_)_'∘> $t) ;

//TODO: REDO ALL THIS USING SLICE CATEGORY
symbol ascheme_baseMeet_el : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
   ring_type R;
symbol ascheme_baseMeet_elimL_hom :
  Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom (ascheme_basic_func R (ascheme_baseMeet_el U r)) (Unit_mod Id_func U) Id_func;

symbol ascheme_baseMeet_elimR_hom :
  Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom (ascheme_basic_func R (ascheme_baseMeet_el U r)) (Unit_mod Id_func (ascheme_basic_func R r)) Id_func;

symbol ascheme_baseMeet_elimM_hom :
  Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
  hom (ascheme_basic_func R (ascheme_baseMeet_el U r)) (Unit_mod Id_func (ascheme_join'_func U r)) Id_func;

rule (@ascheme_baseMeet_elimL_hom _ $R $U $r)
        '∘ (_)_'∘> (ascheme_join'_introL_hom $U $r)  
↪ (@ascheme_baseMeet_elimM_hom _ $R $U $r);

rule (@ascheme_baseMeet_elimR_hom _ $R $U $r)
        '∘ (_)_'∘> (ascheme_join'_introR_hom $U $r)  
↪ (@ascheme_baseMeet_elimM_hom _ $R $U $r);

// rule @ascheme_baseMeet_el $R (ascheme_join'_func $U $s) $r
// ↪ (ring_mult $R (@ascheme_baseMeet_el $R $U $r) $s);

// skew arguments sizes for easier confluence?
rule @ascheme_baseMeet_el _ $R (ascheme_join'_func $U $s) $r
↪ (ring_mult $R (@ascheme_baseMeet_el _ $R $U $s) $r);


//TODO yoneda action of a base arrow on an arrow in the slice
rule @ascheme_baseMeet_elimL_hom _ $R (ascheme_join'_func $U $s) $r
↪  ((ascheme_mult_hom' $R (@ascheme_baseMeet_el _ $R $U $s) $r) 
    '∘ (_)_'∘> (@ascheme_baseMeet_elimM_hom _ $R $U $s)) ;

//ascheme_baseMeet_elimM_hom would be used here, if right argument was general
rule @ascheme_baseMeet_elimR_hom _ $R (ascheme_join'_func $U $s) $r
↪  (ascheme_mult_hom $R (@ascheme_baseMeet_el _ $R $U $s) $r)  ;

constant symbol ascheme_join'_sieve_introM_hom : Π [R_Set : Set] [R : ring R_Set] (U : func Terminal_cat (ascheme_cat R)) (r : ring_type R),
hom (ascheme_basic_func R (ascheme_baseMeet_el U r))  (sieve_mod (ascheme_join'_sieve U r)) Id_func ;


rule (@ascheme_join'_sieve_introM_hom _ $R $U $r) '∘ ((ascheme_join'_sieve $U $r) _'sieve∘> $t)
↪ (ascheme_baseMeet_elimM_hom $U $r) '∘ ((_)_'∘> $t) ;

constant symbol ascheme_join'_sieve_induction : Π [R_Set : Set] [R : ring R_Set] [U : func Terminal_cat (ascheme_cat R)] [r : ring_type R]
[B] [T : smod (ascheme_site R) B] [G : func Terminal_cat B]  
(t_l : hom U (smod_mod T) G ) 
(t_m : hom (ascheme_basic_func R (ascheme_baseMeet_el U r)) (smod_mod T) G )
(t_r: hom (ascheme_basic_func R r) (smod_mod T) G),
//TODO?  SHOULD USE SLICE CATEGORY TO REQUIRE THAT THIS EQUATION CONDITION BE DEFINITIONAL/COMPUTATIONAL ? (THE MIDDLE MORPHISM WONT BE EXPLICIT ANYMORE)
// BUT THEREAFTER EVEM WITH A (METAFRAMEWORK's) PROPOSITIONAL EQUALITY IT IS STILL POSSIBLE TO BUILD A SLICE CONE (WITH TRANSPORTED GROUNDING) BUT WITHOUT GUARANTY OF COMPUTATION 
π ( ((ascheme_baseMeet_elimL_hom U r) '∘ (_)_'∘> t_l) = t_m )  →
π ( ((ascheme_baseMeet_elimR_hom U r) '∘ (_)_'∘> t_r) = t_m )  →
transf (sieve_mod (ascheme_join'_sieve U r)) Id_func (smod_mod T) G;

rule  (ascheme_join'_sieve_introM_hom $U $r) '∘ (@ascheme_join'_sieve_induction _ _  $U $r _ _ _ $t_l $t_m $t_r _ _)
↪ $t_m;
rule  (ascheme_join'_sieve_introL_hom $U $r) '∘ (@ascheme_join'_sieve_induction _ _  $U $r _ _ _ $t_l $t_m $t_r _ _)
↪ $t_l;
rule  (ascheme_join'_sieve_introR_hom $U $r) '∘ (@ascheme_join'_sieve_induction _ _  $U $r _ _ _ $t_l $t_m $t_r _ _)
↪ $t_r;

constant symbol ascheme_unimodular_sieve : Π [R_Set : Set] (R : ring R_Set) /* here parameter j for r_j */ (r1 r2 : ring_type R) /* (s_inv : ring_type R ≔ √^n ( a1 r1 + a2 r2)) ... but simplified for now */,
hom (ascheme_basic_func R (ring_add R r1 r2)) (sieve (ascheme_cat R) Terminal_cat) Id_func;

rule (ascheme_unimodular_sieve $R $r1 $r2) '∘ (sieve_ssieve (ascheme_site $R) Terminal_cat)
↪ maximal_ssieve (ascheme_site $R) (ascheme_basic_func $R (ring_add $R $r1 $r2)) Id_func;

constant symbol ascheme_unimodular_sieve_intro1_hom : Π [R_Set : Set] (R : ring R_Set) (r1 r2 : ring_type R) /* here parameter j for r_j */,
hom (ascheme_basic_func R (ring_mult R r1 (ring_add R r1 r2))) (sieve_mod (ascheme_unimodular_sieve R r1 r2)) Id_func ;

constant symbol ascheme_unimodular_sieve_intro2_hom : Π [R_Set : Set] (R : ring R_Set) (r1 r2 : ring_type R),
hom (ascheme_basic_func R (ring_mult R r2 (ring_add R r1 r2))) (sieve_mod (ascheme_unimodular_sieve R r1 r2)) Id_func ;


/* here parameter j for r_j */
rule (@ascheme_unimodular_sieve_intro1_hom _ $R  $r1 $r2) '∘ ((ascheme_unimodular_sieve $R $r1 $r2) _'sieve∘> $t)
↪ (ascheme_mult_hom $R $r1 (ring_add $R $r1 $r2) ) '∘ ((_)_'∘> $t) ;

rule (@ascheme_unimodular_sieve_intro2_hom _ $R  $r1 $r2) '∘ ((ascheme_unimodular_sieve $R $r1 $r2) _'sieve∘> $t)
↪ (ascheme_mult_hom $R $r2 (ring_add $R $r1 $r2) ) '∘ ((_)_'∘> $t) ;


//TODO REDO THIS, INVESTIGATE AND FIX SOME ERROR STUFF HERE
 symbol maximal_sieve'  [S : cat] (S_site : site S) [I] (F : func I S) [D] (K : func I D): hom F (sieve S D) K
≔ (ssieve_sieve _ (maximal_ssieve S_site F K))   ;

constant symbol maximal_sieve_intro_hom' : Π [S : cat] (S_site : site S) [I] (F : func I S) [D] (K : func I D)
[J] [G : func J S] [x : func J I] (g_ : hom G (Unit_mod Id_func F) x),
hom G (sieve_mod (maximal_sieve' S_site F K)) x /* generalize this Id_func */;

symbol TODO_REDO_tmp_debug_to_fix'  [R_Set : Set] [R : ring R_Set] [B : cat] [T : smod (ascheme_site R) B] [G : func Terminal_cat B] (r1 r2 : ring_type R)
(t_ : transf (sieve_mod (ascheme_unimodular_sieve R r1 r2)) Id_func (smod_mod T) G) ≔
(maximal_sieve_intro_hom' (ascheme_site R) (ascheme_basic_func R (ring_add R r1 r2)) Id_func (Func_cov_hom (ascheme_basic_func R (ring_add R r1 r2)) Id_func))
 '∘ 
 (glue (ascheme_site R) (sieve_mod (ascheme_unimodular_sieve R r1 r2)) t_ );
///ERROR TO SOLVE
// 0. sieve_mod (maximal_sieve (ascheme_basic_func R (ring_add R r1 r2)) Id_func) ≡ 
//    smod_mod (mod_smod (ascheme_site R) (sieve_mod (ascheme_unimodular_sieve R r1 r2)))
// 1. sieve_mod (maximal_sieve (ascheme_basic_func R (ring_add R r1 r2)) Id_func) ≡ smod_mod (mod_smod (ascheme_site R) (sieve_mod (ascheme_unimodular_sieve R r1 r2)))


/*
*
* ---------- voila ----------
*
*/
