/* https://github.com/1337777/cartier/blob/master/cartierSolution16.lp
https://github.com/1337777/cartier/blob/master/Kosta_Dosen_polynomial_univalence.pdf

Kosta Dosen's univalent polynomial functorial programming, 
   and locally ringed sites schemes and functorial schemes
*/

require open modos.cartierSolution13;


// OUTLINE
// # SECTION 3: COVERING SIEVES
      // ATTENPT 1 VERSION
      // ATTEMPT 2 VERSION
      // ATTEMPT 3 VERSION


///----------------------------------------------------------------
///------------------------ ATTENPT 1 VERSION ---------------------
///----------------------------------------------------------------


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




///----------------------------------------------------------------
///------------------------ ATTENPT 2 VERSION ---------------------
///----------------------------------------------------------------




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



///----------------------------------------------------------------
///------------------------ ATTENPT 3 VERSION ---------------------
///----------------------------------------------------------------


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



///----------------------------------------------------------------
///------------------------ ATTENPT 4 VERSION - TO BE CONTINUED ---------------------
///----------------------------------------------------------------

