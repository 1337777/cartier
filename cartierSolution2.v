(**#+TITLE: cartierSolution2.v

Proph

https://gitlab.com/1337777/cartier/blob/master/cartierSolution2.v

solves half of some question of Cartier which is how to program grammatical meta (metafunctors) ...

Outline : Primo, it is sufficient for now to touch only product-preserving retractive reflection into subgraph instead of metafunctors-grammar localization ( <=> "Galois-topology"  <=> "universal closure operations" <=?> "calculus of fractions" <=> "special factorization systems" ); the case of finite-limit will require some new elimination-scheme (?diaconescu-scheme?) which may still-be avoided for the purely-computational questions : the cone property and pairing-through-the-limit-subobject property are corresponding logical properties/invariants which may be erased. Secondo, it is possible for now to verify by pencil-and-paper (+) that these terminating reduction relations satisfy local confluence (commutation of basic reductions) by discovering-and-appending whatever derivable solution-conversions lemma are needed and (++) that this solution terminology permit the derivability of the associativity-conversion. Therefore relative-decidability of the (data) coherence question (sameness-of-arrows) will follow from this cut-elimination, although the (logical) theoremhood question (presence-of-arrow) is lost. Tertio, the coreflection (right adjoint) is some (invisible) inclusion functor, such that the reflection is some endofunctor inside one single graph. Also the reverse-isomorphisms for expressing the retraction (reversibility of the counit-morphism and more) and the product-preservation (reversibility of those pairings-morphisms which arise from the known computation of the product inside the subreflective subgraph) are explicit data :

| ( 'RevCoUnit o>Mod (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0) )   :   'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0

| ( (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0) o>Mod 'RevLimit1Unit )   :   'CoMod(0 Reflection0 L ~> Reflection0 (Limit A1 A2) )0

Quarto, the resolution/cut-elimination now proceeds by two phases : (+) first into some intermediate-solution, where only the subgraph-projection morphisms are eliminated and (++) then into some final-solution where also the subgraph-pairing morphisms are eliminated. Again the formulation is such that all the senses/semantic of « product-preserving retractive reflection » is still-expressible in the terminology of the solution, and any more needed derivable solution-conversion will be discovered-and-appended during the local confluence deduction. And the degradation lemma is more technical : (+) the choice of the grades for the morphisms is more constrained such that some two-phases-resolution is now required (++) and for the pairings-morphisms, on shall require simultaneous/parametric full reduction of every reductible morphisms in the pairings. This COQ program and deduction is mostly automated, and is necessary instead of pencil-and-paper if there are no prior expectations.

Keywords : 1337777.OOO//cartierSolution2.v ; metafunctors-grammar ; localization

POSTSCRIPT : the earlier file [[1337777.OOO//cartierSolution.v]] shall not have the hidden cut PolyMetaTransf in the final solution, for sure :

| View1 a : 'Modos(0 (View0 A) ~> (View0 A') )0

| PolyMetaFunctor func1 x : 'Modos(0 (View0 A) ~> (MetaFunctor func1) )0)

| f o>Modos_ transf : 'Modos(0 (View0 A) ~> (MetaFunctor func'1) )0)

| [[ v_ ]] : 'Modos(0 (MetaFunctor func1) ~> F )0


-----

eth 0x54810dcb93b37DBE874694407f78959Fa222D920 , paypal 1337777.OOO@gmail.com , wechatpay 2796386464@qq.com , irc #OOO1337777

**)

(**
USER-MANUAL
____________________

COMOD
-----
g_ o>CoMod g'  :  B1 ~> B3
UnitCoMod  :  B ~> B
'Unit o>CoMod g  :  B1 ~> B1
~_1 o>CoMod b1  :  (Limit B1 B2) ~> B1'
~_2 o>CoMod b2  :  (Limit B1 B2) ~> B2'
<< g_1 ,CoMod g_2 >>  :  L ~> (Limit B1 B2)

MOD
-----
f_ o>Mod f'  :  A1 ~> A3
Reflection1 g  :  Reflection0 B1 ~> Reflection0 B2
f o>Mod 'CoUnit  :  Reflection0 A1 ~> Reflection0 A2
~_1 o>Mod a1  :  Reflection0 Lim (Reflection0 B1) (Reflection0 B2) ~> (Reflection0 B1')
~_2 o>Mod a2  :  Reflection0 Lim (Reflection0 B1) (Reflection0 B2) ~> (Reflection0 B2')
<< f_1 ,Mod f_2 >>  :  Reflection0 L ~> Reflection0 (Limit (Reflection0 B1) (Reflection0 B2))
'RevCoUnitRefl o>Mod g  :  Reflection0 A ~> Reflection0 B
f o>Mod 'RevLimit1Unit  :  Reflection0 (Limit (Reflection0 B1) (Reflection0 B2)) ~> Reflection0 (Limit B1 B2)

-----
<< f_1 ,Mod f_2 >>  :=  Reflection1 << 'Unit o>CoMod f_1 ,CoMod 'Unit o>CoMod f_2 >>
        : Reflection0 L ~> Reflection0 Lim (Reflection0 A1') (Reflection0 A2')
~_1 o>Mod a1  :=  Reflection1 (~_1 o>CoMod a1) o>Mod 'CoUnit
        : Reflection0 Lim (Reflection0 B1) (Reflection0 B2) ~> (Reflection0 B1')

-----
Reflection1 << g_1 ,CoMod g_2 >>  ~~>  << Reflection1 g_1 ,Mod Reflection1 g_2 >> o>Mod 'RevLimit1Unit
        (post-time post-fix)
(f o>Mod 'RevLimit1Unit) o>Mod Reflection1 (~_2 @ A1 o>CoMod g)  >~>  f o>Mod (~_2 o>Mod (Reflection1 g))  ~~>  (f o>Mod Reflection1 (~_2 o>CoMod (Reflection1 g))) o>Mod 'CoUnit
        (pre-time pre-fix)

      ,CoMod > 'RevLimit1Unit > ~_1 o>Mod > 'CoUnit   ; no ~_1 o>Mod in Sol ;
      ( 'RevCoUnit o>Mod (Reflection1 (f1 o>Mod a2)) )
          <~~ ( << f1 ,Mod f2 >> o>Mod Reflection1 (~_2 @ (Reflection0 A1) o>CoMod a2)
-----
<< f_1 ,Mod f_2 >> o>Mod (~_1 o>Mod a1)
 =  (Reflection1 << 'Unit o>CoMod f_1 ,CoMod 'Unit o>CoMod f_2 >>) o>Mod (Reflection1 (~_1 o>CoMod a1) o>Mod 'CoUnit)
 =  Reflection1 (<< 'Unit o>CoMod f_1 ,CoMod 'Unit o>CoMod f_2 >> o>CoMod (~_1 o>CoMod a1)) o>Mod 'CoUnit
 = Reflection1 ('Unit o>CoMod (f_1 o>Mod a1))) o>Mod 'CoUnit
 = (f_1 o>Mod a1) ;

<< (~_1 o>Mod uCoMod) ,Mod (~_2 o>Mod uCoMod) >>
 = (Reflection1 << 'Unit o>CoMod (Reflection1 (~_1 o>CoMod uCoMod) o>Mod 'CoUnit) ,CoMod 'Unit o>CoMod (  Reflection1 (~_2 o>CoMod uCoMod) o>Mod 'CoUnit) >>)
 = (Reflection1 <<  (~_1 o>CoMod uCoMod) ,CoMod (~_2 o>CoMod uCoMod) >>)
 = (Reflection1 uCoMod )
 = uCoMod

-----
~_1 o>Mod (uCoMod (Reflection0 B1)) = Reflection1 (~_1 o>CoMod (uCoMod (Reflection0 B1))) o>Mod 'CoUnit
        : Reflection0 Lim (Reflection0 B1) (Reflection0 B2) ~> (Reflection0 B1)
Reflection1 (~_1 o>CoMod (uCoMod (Reflection0 B1))) = 'RevCoUnitRefl o>Mod (~_1 o>Mod (uCoMod (Reflection0 B1)))
        : Reflection0 (Lim (Reflection0 B1) (Reflection0 B2)) ~> Reflection0 (Reflection0 B1)
Reflection1 (~_1 o>CoMod a1) = 'RevCoUnitRefl o>Mod (~_1 o>Mod a1)
        : Reflection0 (Lim (Reflection0 B1) (Reflection0 B2)) ~> Reflection0 (Reflection0 B1)
Reflection1 << g_1 ,CoMod g_2 >> = << Reflection1 g_1 ,Mod Reflection1 g_2 >> o>Mod 'RevLimit1Unit
<< Reflection1 g_1 ,Mod Reflection1 g_2 >> = Reflection1 << g_1 ,CoMod g_2 >> o>Mod Reflection1 << ~_1 @ B2 o>CoMod 'Unit o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod 'Unit o>CoMod uCoMod >> = Reflection1 << g_1 ,CoMod g_2 >> o>Mod 'Limit1Unit

**)

(**

#+BEGIN_SRC coq :exports both :results silent **)

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import Setoid.
Require Omega. 

Module LOCALIZATION.

Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.

Inductive obCoMod : Type :=
| Reflection0 : forall B : obCoMod, obCoMod
| Limit : forall B1 B2 : obCoMod, obCoMod.

Reserved Notation "''CoMod' (0 B1 ~> B2 )0"
         (at level 25, format "''CoMod' (0  B1  ~>  B2  )0").

Parameter obMod : obCoMod -> Prop.

(* (Unit o>CoMod g) antecedent , (f o>Mod CoUnit) consequent , (RevCoUnitRefl o>Mod Reflection g) antecedent , f_ o>Mod 'RevLimit1unit consequent  and all senses expressible as cut-free in the solution-conversions and any additional solution-conversion to be discovered during the confluence deduction  - NOPRED *)
Inductive CoMod00 : obCoMod -> obCoMod -> Type :=

| PolyCoMod : forall (B2 : obCoMod) (B1 : obCoMod)
  , 'CoMod(0 B2 ~> B1 )0 -> forall B1' : obCoMod,
      'CoMod(0 B1 ~> B1' )0 -> 'CoMod(0 B2 ~> B1' )0


| UnitCoMod : forall {B : obCoMod}, 'CoMod(0 B ~> B )0

| Unit : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0), 'CoMod(0 B1 ~> B2 )0

| Project_1 : forall B1 B2,
      forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0), 'CoMod(0 (Limit B1 B2) ~> B1' )0

| Project_2 : forall B1 B2,
      forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0), 'CoMod(0 (Limit B1 B2) ~> B2' )0

| Limitator : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
      'CoMod(0 M ~> (Limit B1 B2) )0


| Reflection1 : forall B1 B2 (g : 'CoMod(0 B1 ~> B2 )0), 'CoMod(0 Reflection0 B1 ~> Reflection0 B2 )0

| CoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0), 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0

| ProjectMod_1 : forall A1 A2,
      forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0), 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> (Reflection0 A1') )0

| ProjectMod_2 : forall A1 A2,
      forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0), 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> (Reflection0 A2') )0

| LimitatorMod : forall A1 A2 L,
    forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
      'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0

| RevCoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0), 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0

(* single-instance-of-some-pairing *)
| RevLimit1Unit : forall A1 A2 L
                    (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
    'CoMod(0 Reflection0 L ~> Reflection0 (Limit A1 A2) )0

where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

Notation "'Refl0 B" :=
  (@Reflection0 B) (at level 25, right associativity).

Notation "g_ o>CoMod g'" :=
  (@PolyCoMod _ _ g_ _ g') (at level 25, right associativity).

Notation "f_ o>Mod f'" :=
  (@PolyCoMod _ _ f_ _ f') (at level 25, right associativity, only parsing).

Notation "'uCoMod'" := (@UnitCoMod _) (at level 0).

Notation "@ 'uCoMod' B" :=
  (@UnitCoMod B) (at level 11, only parsing).

Notation "'Unit o>CoMod g" :=
  (@Unit _ _ g) (at level 25, right associativity).

Notation "~_1 @ B2 o>CoMod b1" :=
  (@Project_1 _ B2 _ b1) (at level 25, B2 at next level).

Notation "~_1 o>CoMod b1" :=
  (@Project_1 _ _ _ b1) (at level 25).

Notation "~_2 @ B1 o>CoMod b2" :=
  (@Project_2 B1 _ _ b2) (at level 25, B1 at next level).

Notation "~_2 o>CoMod b2" :=
  (@Project_2 _ _ _ b2) (at level 25).

Notation "<< g_1 ,CoMod g_2 >>" :=
  (@Limitator _ _ _ g_1 g_2) (at level 0).

Notation "'Refl1 g" :=
  (@Reflection1 _ _ g) (at level 25, right associativity).

Notation "f o>Mod 'CoUnit" :=
  (@CoUnit _ _ f) (at level 25, right associativity).

Notation "~_1 @ B2 o>Mod a1" :=
  (@ProjectMod_1 _ B2 _ a1) (at level 25, B2 at next level).

Notation "~_1 o>Mod a1" :=
  (@ProjectMod_1 _ _ _ a1) (at level 25).

Notation "~_2 @ B1 o>Mod a2" :=
  (@ProjectMod_2 B1 _ _ a2) (at level 25, B1 at next level).

Notation "~_2 o>Mod a2" :=
  (@ProjectMod_2 _ _ _ a2) (at level 25).

Notation "<< f_1 ,Mod f_2 >>" :=
  (@LimitatorMod _ _ _ f_1 f_2) (at level 0).

Notation "'RevCoUnit o>Mod f" :=
  (@RevCoUnit _ _ f) (at level 25, right associativity).

Notation "f o>Mod 'RevLimit1Unit" :=
  (@RevLimit1Unit _ _ _ f) (at level 25, right associativity).

Definition Limit1Unit := fun {A1 A2} => Reflection1 << ~_1 @ A2 o>CoMod ('Unit o>CoMod (@uCoMod (Reflection0 A1))) ,CoMod ~_2 @ A1 o>CoMod ('Unit o>CoMod (@uCoMod (Reflection0 A2))) >>.

Reserved Notation "g2 ~~~ g1"  (at level 70).

Inductive convCoMod : forall (B1 B2 : obCoMod),
    'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Prop :=

(* 1 -- equivalence *)
  
| CoMod_Refl : forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0),
    g ~~~ g
      
| CoMod_Trans : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0),
    uTrans ~~~ g -> forall (g0 : 'CoMod(0 B1 ~> B2 )0),
      g0 ~~~ uTrans -> g0 ~~~ g
                         
| CoMod_Sym : forall (B1 B2 : obCoMod) (g g0 : 'CoMod(0 B1 ~> B2 )0),
    g ~~~ g0 -> g0 ~~~ g


(* 2 -- congruences *)
                  
| PolyCoMod_cong :
    forall (B B' : obCoMod) (g_ g_0 : 'CoMod(0 B ~> B' )0),
    forall (B'' : obCoMod) (g' g'0 : 'CoMod(0 B' ~> B'' )0),
      g_0 ~~~ g_ -> g'0 ~~~ g' -> ( g_0 o>CoMod g'0 ) ~~~ ( g_ o>CoMod g' )

| Unit_cong : forall B1 B2 (g g0 : 'CoMod(0 Reflection0 B1 ~> B2 )0),
    g0 ~~~ g -> ( 'Unit o>CoMod g0 ) ~~~ ( 'Unit o>CoMod g )

| Project_1_cong : forall B1 B2,
    forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
      b1' ~~~ b1 -> ( ~_1 @ B2 o>CoMod b1' ) ~~~ ( ~_1 @ B2 o>CoMod b1 )

| Project_2_cong : forall B1 B2,
      forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
      b2' ~~~ b2 -> ( ~_2 @ B1 o>CoMod b2' ) ~~~ ( ~_2 @ B1 o>CoMod b2 )

| Limitator_cong : forall B1 B2 L,
    forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
      g'_1 ~~~ g_1 -> g'_2 ~~~ g_2 -> << g'_1 ,CoMod g'_2 >> ~~~ << g_1 ,CoMod g_2 >>

| Reflection1_cong : forall B1 B2 (g g0 : 'CoMod(0 B1 ~> B2 )0),
    g0 ~~~ g -> ( Reflection1 g0 ) ~~~ ( Reflection1 g )

| CoUnit_cong : forall A1 A2 (f f0 : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0),
    f0 ~~~ f -> ( f0 o>Mod 'CoUnit ) ~~~ ( f o>Mod 'CoUnit )

| ProjectMod_1_cong : forall A1 A2,
    forall A1' (a1 a1' : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
      a1' ~~~ a1 -> ( ~_1 @ A2 o>Mod a1' ) ~~~ ( ~_1 @ A2 o>Mod a1 )
      
| ProjectMod_2_cong : forall A1 A2,
    forall A2' (a2 a2' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
      a2' ~~~ a2 -> ( ~_2 @ A1 o>Mod a2' ) ~~~ ( ~_2 @ A1 o>Mod a2 )

| LimitatorMod_cong : forall B1 B2 L,
    forall (f_1 f'_1 : 'CoMod(0 Reflection0 L ~> Reflection0 B1 )0) (f_2 f'_2: 'CoMod(0 Reflection0 L ~> Reflection0 B2 )0),
      f'_1 ~~~ f_1 -> f'_2 ~~~ f_2 -> << f'_1 ,Mod f'_2 >> ~~~ << f_1 ,Mod f_2 >>

| RevCoUnit_cong : forall A1 A2 (f f0 : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0),
    f0 ~~~ f -> ( 'RevCoUnit o>Mod f0 ) ~~~ ( 'RevCoUnit o>Mod f )

| RevLimit1Unit_cong : forall A1 A2 L
                    (f f0 : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
    f0 ~~~ f -> ( f0 o>Mod 'RevLimit1Unit ) ~~~ ( f o>Mod 'RevLimit1Unit )


(* 3 -- units *)

| CoMod_unit :
    forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
      ( f )
        ~~~ ( ( uCoMod ) o>CoMod f
              : 'CoMod(0 B ~> B' )0 )

| CoMod_inputUnitCoMod :
    forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
      ( g )
        ~~~  ( g o>CoMod ( uCoMod )
               : 'CoMod(0 B' ~> B )0 )

(* for secondo reduction only *)
| Reflection1_unit : forall B,
    @uCoMod (Reflection0 B)
    ~~~ ( Reflection1 (@uCoMod B)
          : 'CoMod(0 Reflection0 B ~> Reflection0 B )0 )

(* necessary for primo reduction *)
| Reflection1_unit_PolyMod : forall B B' (f : 'CoMod(0 Reflection0 B' ~> Reflection0 B )0),
  ( f )
    ~~~ ( f o>Mod (Reflection1 (@uCoMod B))
          : 'CoMod(0 Reflection0 B' ~> Reflection0 B )0 )


(* 4 -- polymorphisms *)

(* non for primo reduction *)
| CoMod_morphism :
    forall (B0 B : obCoMod) (g : 'CoMod(0 B0 ~> B )0)
      (B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0)
      (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
      ( g o>CoMod ( g_ o>CoMod g' ) )
        ~~~ ( ( g o>CoMod g_ ) o>CoMod g'
              : 'CoMod(0 B0 ~> B'' )0 )

| Unit_morphismPre : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0)
                              B1' (g_ : 'CoMod(0 B1' ~> B1 )0),
    ( 'Unit o>CoMod ( (Reflection1 g_) o>CoMod g ) )
      ~~~ ( g_ o>CoMod ( 'Unit o>CoMod g )
            : 'CoMod(0 B1' ~> B2 )0 )

| Unit_morphismPost : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0)
                               B2' (g' : 'CoMod(0 B2 ~> B2' )0),
    ( 'Unit o>CoMod ( g o>CoMod g' ) )
      ~~~ ( ( 'Unit o>CoMod g ) o>CoMod ( g' )
          : 'CoMod(0 B1 ~> B2' )0 )
                              
| Project_1_morphism : forall B1 B2,
    forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
      B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
      ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
        ~~~ ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
              : 'CoMod(0 Limit B1 B2 ~> B1'' )0 )

| Project_2_morphism : forall B1 B2,
    forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
      B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
      ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
        ~~~ ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
              : 'CoMod(0 Limit B1 B2 ~> B2'' )0 )

| Limitator_morphism : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
      M' (m : 'CoMod(0 M' ~> M )0),
      ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )
        ~~~ ( m o>CoMod << g_1 ,CoMod g_2 >>
              : 'CoMod(0 M' ~> Limit B1 B2 )0 )

| Reflection1_morphism : forall B1 B2 (g_ : 'CoMod(0 B1 ~> B2 )0)
                           B3 (g' : 'CoMod(0 B2 ~> B3 )0),
    (Reflection1 (g_ o>CoMod g'))
      ~~~ (Reflection1 g_ o>Mod Reflection1 g'
           : 'CoMod(0 Reflection0 B1 ~> Reflection0 B3 )0 )
                                                          
| CoUnit_morphismPre : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0)
                          A1' (f_ : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1 )0),
    ((f_ o>Mod f) o>Mod 'CoUnit)
      ~~~ ( f_ o>Mod (f o>Mod 'CoUnit)
            : 'CoMod(0 'Refl0 A1' ~> 'Refl0 A2 )0 )

| CoUnit_morphismPost : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0)
                          A2' ( f' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
    ( (f o>Mod (Reflection1 f')) o>Mod 'CoUnit)
      ~~~ ( (f o>Mod 'CoUnit) o>Mod f'
          : 'CoMod(0 'Refl0 A1 ~> 'Refl0 A2' )0 )

| ProjectMod_1_morphism : forall A1 A2,
    forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0)
      A1'' (a1' : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1'' )0),
      ( ~_1 @ A2 o>Mod (a1 o>Mod a1') )
        ~~~ ( ( ~_1 @ A2 o>Mod a1 ) o>Mod a1'
              : 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> Reflection0 A1'' )0 )

| ProjectMod_2_morphism : forall A1 A2,
    forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0)
      A2'' (a2' : 'CoMod(0 Reflection0 A2' ~> Reflection0 A2'' )0),
      ( ~_2 @ A1 o>Mod (a2 o>Mod a2') )
        ~~~ ( ( ~_2 @ A1 o>Mod a2 ) o>Mod a2'
              : 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> Reflection0 A2'' )0 )

| LimitatorMod_morphism : forall A1 A2 L,
    forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0)
      L' (l : 'CoMod(0 Reflection0 L' ~> Reflection0 L )0),
      ( << l o>CoMod f_1 ,Mod l o>CoMod f_2 >> )
        ~~~ ( l o>CoMod << f_1 ,Mod f_2 >>
              : 'CoMod(0 Reflection0 L' ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0 )

| RevCoUnit_morphismPre : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0)
                            A1' (f_ : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1 )0),
    ( 'RevCoUnit o>Mod ((Reflection1 f_) o>Mod f) )
      ~~~ ( f_ o>Mod ('RevCoUnit o>Mod f)
            : 'CoMod(0 'Refl0 A1' ~> 'Refl0 A2 )0 )

| RevCoUnit_morphismPost : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0)
                             A2' (f' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
    ( 'RevCoUnit o>Mod (f o>Mod f') )
      ~~~ ( ('RevCoUnit o>Mod f) o>Mod f'
            : 'CoMod(0 'Refl0 A1 ~> 'Refl0 A2' )0 )

| RevLimit1Unit_morphism :
    forall A1 A2 L
      (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
      L' (f_ : 'CoMod(0 Reflection0 L' ~> Reflection0 L )0),
      ( (f_ o>Mod f) o>Mod 'RevLimit1Unit )
        ~~~ ( f_ o>Mod (f o>Mod 'RevLimit1Unit)
              : 'CoMod(0 Reflection0 L' ~> Reflection0 (Limit A1 A2) )0 )

(* logically-derivable from definition-conversion , necessary for primo reduction
   see also Unit_RevCoUnit_PolyCoMod alias Reflection1_Unit_morphism below *)
| Reflection1_Project_1_morphism : forall A1 A2,
      forall B1 (b1 : 'CoMod(0 Reflection0 A1 ~> B1 )0),
      forall A1'' (f_1 : 'CoMod(0 Reflection0 A1'' ~> ('Refl0 A1) )0)
        (f_2 : 'CoMod(0 Reflection0 A1'' ~> ('Refl0 A2) )0),
        ( 'RevCoUnit o>Mod (Reflection1 (f_1 o>Mod b1)) )
          ~~~ ( << f_1 ,Mod f_2 >> o>Mod Reflection1 (~_1 @ (Reflection0 A2) o>CoMod b1)
                : 'CoMod(0 'Refl0 A1'' ~> 'Refl0 B1 )0 )

(* logically-derivable from definition-conversion , necessary for primo reduction *)
| Reflection1_Project_2_morphism : forall A1 A2,
      forall B2 (b2 : 'CoMod(0 Reflection0 A2 ~> B2 )0),
      forall A2'' (f_1 : 'CoMod(0 Reflection0 A2'' ~> ('Refl0 A1) )0)
        (f_2 : 'CoMod(0 Reflection0 A2'' ~> ('Refl0 A2) )0),
        ( 'RevCoUnit o>Mod (Reflection1 (f_2 o>Mod b2)) )
          ~~~ ( << f_1 ,Mod f_2 >> o>Mod Reflection1 (~_2 @ (Reflection0 A1) o>CoMod b2)
                : 'CoMod(0 'Refl0 A2'' ~> 'Refl0 B2 )0 )

(* logically-derivable from definition-conversion , necessary for primo reduction *)
| Reflection1_Limitator_morphism : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
      M' (m : 'CoMod(0 Reflection0 M' ~> Reflection0 M )0),
      ( << m o>Mod Reflection1 g_1 ,Mod m o>Mod Reflection1 g_2 >> o>Mod 'RevLimit1Unit )
        ~~~ ( m o>CoMod Reflection1 << g_1 ,CoMod g_2 >>
              : 'CoMod(0 Reflection0 M' ~> Reflection0 (Limit B1 B2) )0 )

(* 5 -- counit-cancellations *)
      
(* non for primo reduction : outer counit-cancellation  *)
| CoUnitReflection_Unit : forall B1 B2 (g : 'CoMod(0 B1 ~> B2 )0),
    ( Reflection1 g  )
      ~~~ ( (Reflection1 ( 'Unit o>CoMod (Reflection1 g) )) o>Mod 'CoUnit
            : 'CoMod(0 'Refl0 B1 ~> 'Refl0 B2 )0 )

(* non for primo reduction : inner counit-cancellation *)
| Unit_CoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0),
    ( f )
      ~~~ ( 'Unit o>CoMod ((Reflection1 f) o>Mod 'CoUnit)
            : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0)


(* 6 -- retractive reflection *)

(* non for primo reduction :  counit , reverse counit *)
| CoUnit_RevCoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0),
    ( f )
      ~~~ ( 'RevCoUnit o>Mod (Reflection1 (f o>Mod 'CoUnit))
            : 'CoMod(0 'Refl0 A1 ~> 'Refl0 'Refl0 A2 )0 )

(* non for primo reduction : reverse counit , counit *)
| RevCoUnit_CoUnit : forall A1 A2 (g : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0),
    ( g )
      ~~~ ( ('RevCoUnit o>Mod (Reflection1 g)) o>Mod 'CoUnit
            : 'CoMod(0 'Refl0 A1 ~> 'Refl0 A2 )0 )

(* logically-derivable , non primo reduction ,
   maybe for solution and confluence only :
   lemma that reflection1 of unit is reversible *)
| Unit_RevCoUnit : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
    ( 'RevCoUnit o>Mod (Reflection1 g) )
      ~~~ ( Reflection1 ('Unit o>CoMod g)
            : 'CoMod(0 Reflection0 A ~> Reflection0 B )0 )

(* logically-derivable , necessary for primo reduction
  this Unit_RevCoUnit_PolyCoMod may be named Reflection1_Unit_morphism  *)
| Unit_RevCoUnit_PolyCoMod : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
     forall A' (f : 'CoMod(0 Reflection0 A' ~> Reflection0 A )0),
    ( f o>Mod ('RevCoUnit o>Mod (Reflection1 g)) )
      ~~~ ( f o>Mod (Reflection1 ('Unit o>CoMod g))
            : 'CoMod(0 Reflection0 A' ~> Reflection0 B )0 )

(* logically-derivable , non primo reduction ,
   maybe for solution and confluence only :
   lemma that unit over reflection0 is reversible *)
| RevCoUnit_Unit : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
    ( 'RevCoUnit o>Mod (Reflection1 g) )
      ~~~ ( 'Unit o>CoMod (Reflection1 g)
           : 'CoMod(0 Reflection0 A ~> Reflection0 B )0 )


(* 7 -- projection cancel particular-pairing *)

| Limitator_Project_1 : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
    forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
      ( g_1 o>CoMod b1 )
        ~~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
              : 'CoMod(0 M ~> B1' )0 )

| Limitator_Project_2 : forall B1 B2 M,
    forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
    forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
      ( g_2 o>CoMod b2 )
        ~~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
              : 'CoMod(0 M ~> B2' )0 )

| LimitatorMod_Project_1 : forall A1 A2 L,
    forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
    forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
      ( f_1 o>Mod a1 )
        ~~~ ( << f_1 ,Mod f_2 >> o>Mod ( ~_1 @ A2 o>Mod a1 )
              : 'CoMod(0 'Refl0 L ~> 'Refl0 A1' )0 )

| LimitatorMod_Project_2 : forall A1 A2 L,
    forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
    forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
      ( f_2 o>Mod a2 )
        ~~~ ( << f_1 ,Mod f_2 >> o>Mod ( ~_2 @ A1 o>Mod a2 )
              : 'CoMod(0 'Refl0 L ~> 'Refl0 A2' )0 )


(* 8 -- Limit1_id is reversible via being id *)

| Limitator_Project_1_Project_2 : forall B1 B2,
    ( uCoMod )
      ~~~ ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
            : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 )

| LimitatorMod_Project_1_Project_2 : forall B1 B2,
    ( uCoMod )
      ~~~ ( << ~_1 @ B2 o>Mod uCoMod ,Mod ~_2 @ B1 o>Mod uCoMod >>
          : 'CoMod(0 'Refl0 Limit ('Refl0 B1) ('Refl0 B2) ~> 'Refl0 Limit ('Refl0 B1) ('Refl0 B2) )0 )


(* 9 -- projection cancel single-instance-of-some-pairing RevLimit1Unit *)

| RevLimit1Unit_ReflectionProject1 : forall A1 A2 L
                                       (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
                                       B (g : 'CoMod(0 A1 ~> B )0),
    ( (f o>Mod Reflection1 ( ~_1 o>CoMod (Reflection1 g) )) o>Mod 'CoUnit )
      ~~~ ( (f o>Mod 'RevLimit1Unit) o>Mod Reflection1 (~_1 @ A2 o>CoMod g)
            : 'CoMod(0 'Refl0 L ~> 'Refl0 B )0 )

| RevLimit1Unit_ReflectionProject2 : forall A1 A2 L
                                       (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
                                       B (g : 'CoMod(0 A2 ~> B )0),
    ( (f o>Mod Reflection1 ( ~_2 o>CoMod (Reflection1 g) )) o>Mod 'CoUnit )
      ~~~ ( (f o>Mod 'RevLimit1Unit) o>Mod Reflection1 ( ~_2 @ A1 o>CoMod g )
            : 'CoMod(0 'Refl0 L ~> 'Refl0 B )0 )

(* logically-derivable, but necessary for primo reduction *)
(* TODO: OLD ERASE
| RevLimit1Unit_ReflectionUnitCoMod : forall A1 A2 L
                                       (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
    ( f o>Mod 'RevLimit1Unit )
      ~~~ ( (f o>Mod 'RevLimit1Unit) o>Mod Reflection1 (uCoMod)
            : 'CoMod(0 'Refl0 L ~> 'Refl0 (Limit A1 A2) )0 )
 *)
      
(* 10 -- Limit1Unit is reversible via explicit RevLimit1Unit morphism 
         for sense , non for primo reduction *)

| Limit1Unit_RevLimit1Unit : forall B1 B2,
    ( uCoMod )
      ~~~ ( (@Limit1Unit B1 B2) o>Mod 'RevLimit1Unit
            : 'CoMod(0 'Refl0 Limit B1 B2 ~> 'Refl0 Limit B1 B2 )0 )

| RevLimit1Unit_Limit1Unit : forall A1 A2,
    ( uCoMod )
      ~~~ (  << ( ~_1 @ A2 o>Mod Reflection1 ('Unit o>CoMod (@uCoMod (Reflection0 A1))) ) ,Mod ( ~_2 @ A1 o>Mod Reflection1 ('Unit o>CoMod (@uCoMod (Reflection0 A2))) ) >> o>Mod 'RevLimit1Unit
             : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) )0 )


(* 11 -- for sense , for secondo reduction only,
   alternative for the logically-derivable lemma that [ reflector of [ limit-in-CoMod cone of diagram-in-Mod ] ] is limit-in-Mod cone  *)

| ProjectMod_1_Project_1 : forall A1 A2,
    forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
      ( Reflection1 (~_1 @ (Reflection0 A2) o>CoMod a1) o>Mod 'CoUnit )
        ~~~ ( ~_1 @ A2 o>Mod a1
              : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 A1' )0 )

| ProjectMod_2_Project_2 : forall A1 A2,
    forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
      ( Reflection1 (~_2 @ (Reflection0 A1) o>CoMod a2) o>Mod 'CoUnit )
        ~~~ ( ~_2 @ A1 o>Mod a2
              : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 A2' )0 )

| LimitatorMod_Limitator : forall A1 A2 L,
    forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
      ( Reflection1 << 'Unit o>CoMod f_1 ,CoMod 'Unit o>CoMod f_2 >> )
        ~~~ ( << f_1 ,Mod f_2 >>
              : 'CoMod(0 'Refl0 L ~> 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) )0 )


(* 12 -- logically-derivable, for the solution and confluence only , 
   after elimitations of both ProjectMod LimitatorMod *)

| Project_1_Limitator : 
    forall B1 B2,
    forall B1_ (b1_ : 'CoMod(0 B1 ~> B1_ )0),
    forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
      ( ~_1 o>CoMod << b1_ ,CoMod b1 >> )
        ~~~ ( << ~_1 @ B2 o>CoMod b1_ ,CoMod ~_1 @ B2 o>CoMod b1 >>
              : 'CoMod(0 Limit B1 B2 ~> Limit B1_ B1' )0 )

| Project_2_Limitator : 
    forall B1 B2,
    forall B2_ (b2_ : 'CoMod(0 B2 ~> B2_ )0),
    forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
      ( ~_2 o>CoMod << b2_ ,CoMod b2 >> )
        ~~~ ( << ~_2 @ B1 o>CoMod b2_ ,CoMod ~_2 @ B1 o>CoMod b2 >>
              : 'CoMod(0 Limit B1 B2 ~> Limit B2_ B2' )0 )

where "g2 ~~~ g1" := (@convCoMod _ _ g2 g1).


Hint Constructors convCoMod.

Module Sol.

  Section Section1.

    Inductive CoMod00 : obCoMod -> obCoMod -> Type :=

    | UnitCoMod : forall {B : obCoMod}, 'CoMod(0 B ~> B )0

    | Unit : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0), 'CoMod(0 B1 ~> B2 )0

    | Project_1 : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0), 'CoMod(0 (Limit B1 B2) ~> B1' )0

    | Project_2 : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0), 'CoMod(0 (Limit B1 B2) ~> B2' )0

    | Limitator : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
          'CoMod(0 M ~> (Limit B1 B2) )0


    | Reflection1 : forall B1 B2 (g : 'CoMod(0 B1 ~> B2 )0), 'CoMod(0 Reflection0 B1 ~> Reflection0 B2 )0

    | CoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0), 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0

    | LimitatorMod : forall A1 A2 L,
        forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
          'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0

    | RevCoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0), 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0

    (* single-instance-of-some-pairing *)
    | RevLimit1Unit : forall A1 A2 L
                        (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
        'CoMod(0 Reflection0 L ~> Reflection0 (Limit A1 A2) )0

  where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

  End Section1.

  Module Import Ex_Notations.
    Delimit Scope sol_scope with sol.
    
    Notation "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2) : sol_scope.
    Notation "'Refl0 B" :=
      (@Reflection0 B) (at level 25, right associativity) : sol_scope.

    Notation "g_ o>CoMod g'" :=
      (@PolyCoMod _ _ g_ _ g') (at level 25, right associativity) : sol_scope.

    Notation "f_ o>Mod f'" :=
      (@PolyCoMod _ _ f_ _ f') (at level 25, right associativity, only parsing) : sol_scope.

    Notation "'uCoMod'" := (@UnitCoMod _) (at level 0) : sol_scope.

    Notation "@ 'uCoMod' B" :=
      (@UnitCoMod B) (at level 11, only parsing) : sol_scope.

    Notation "'Unit o>CoMod g" :=
      (@Unit _ _ g) (at level 25, right associativity) : sol_scope.

    Notation "~_1 @ B2 o>CoMod b1" :=
      (@Project_1 _ B2 _ b1) (at level 25, B2 at next level) : sol_scope.

    Notation "~_1 o>CoMod b1" :=
      (@Project_1 _ _ _ b1) (at level 25) : sol_scope.

    Notation "~_2 @ B1 o>CoMod b2" :=
      (@Project_2 B1 _ _ b2) (at level 25, B1 at next level) : sol_scope.

    Notation "~_2 o>CoMod b2" :=
      (@Project_2 _ _ _ b2) (at level 25) : sol_scope.

    Notation "<< g_1 ,CoMod g_2 >>" :=
      (@Limitator _ _ _ g_1 g_2) (at level 0) : sol_scope.

    Notation "'Refl1 g" :=
      (@Reflection1 _ _ g) (at level 25, right associativity) : sol_scope.

    Notation "f o>Mod 'CoUnit" :=
      (@CoUnit _ _ f) (at level 25, right associativity) : sol_scope.

    Notation "<< f_1 ,Mod f_2 >>" :=
      (@LimitatorMod _ _ _ f_1 f_2) (at level 0) : sol_scope.

    Notation "'RevCoUnit o>Mod f" :=
      (@RevCoUnit _ _ f) (at level 25, right associativity) : sol_scope.

    Notation "f o>Mod 'RevLimit1Unit" :=
      (@RevLimit1Unit _ _ _ f) (at level 25, right associativity) : sol_scope.

  End Ex_Notations.

  Module Destruct_domReflection.

    Inductive CoMod00_domReflection : forall (B1 B2 : obCoMod),
      ( 'CoMod(0 Reflection0 B1 ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B : obCoMod}, CoMod00_domReflection (@uCoMod (Reflection0 B))%sol

    | Unit : forall B1 B2 (g : 'CoMod(0 Reflection0 (Reflection0 B1) ~> B2 )0),
        CoMod00_domReflection ('Unit o>CoMod g)%sol 

    | Limitator : forall B1 B2 M,
        forall (g_1 : 'CoMod(0 Reflection0 M ~> B1 )0 %sol) (g_2 : 'CoMod(0 Reflection0 M ~> B2 )0 %sol),
        CoMod00_domReflection (<< g_1 ,CoMod g_2 >>)%sol

    | Reflection1 : forall B1 B2 (g : 'CoMod(0 B1 ~> B2 )0 %sol),
        CoMod00_domReflection (Sol.Reflection1 g)

    | CoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0),
        CoMod00_domReflection (f o>Mod 'CoUnit)%sol

    | LimitatorMod : forall A1 A2 L,
        forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
          CoMod00_domReflection (<< f_1 ,Mod f_2 >>)%sol

    | RevCoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0),
        CoMod00_domReflection ('RevCoUnit o>Mod f)%sol

    | RevLimit1Unit : forall A1 A2 L
                        (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
        CoMod00_domReflection (f o>Mod 'RevLimit1Unit)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domReflectionP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        match B1 as o return ('CoMod(0 o ~> B2 )0 -> Set) with
        | ('Refl0 B0)%sol => [eta CoMod00_domReflection (B2:=B2)]
        | Limit B1_1 B1_2 => fun _ : 'CoMod(0 Limit B1_1 B1_2 ~> B2 )0 => unit
        end g.
      (* ltac:( destruct B1; intros; [ refine (CoMod00_domReflection g)
                                    | refine (unit) ] ). *)
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B.
        constructor 1.
        intros; exact: tt.
      - destruct B1. constructor 2.
        intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - destruct M. constructor 3.
        intros; exact: tt.
      - constructor 4.
      - constructor 5.
      - constructor 6.
      - constructor 7.
      - constructor 8.
    Defined.

  End Destruct_domReflection.
 
  Module Destruct_domLimit.

    Inductive CoMod00_domLimit : forall (B1 B1' B2 : obCoMod),
      ( 'CoMod(0 Limit B1 B1' ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B B' : obCoMod}, CoMod00_domLimit (@uCoMod (Limit B B'))%sol

    | Unit : forall B1 B1' B2 (g : 'CoMod(0 Reflection0 (Limit B1 B1') ~> B2 )0),
        CoMod00_domLimit ('Unit o>CoMod g)%sol 

    | Project_1 : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
          CoMod00_domLimit (~_1 @ B2 o>CoMod b1)%sol 

    | Project_2 : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
          CoMod00_domLimit (~_2 @ B1 o>CoMod b2)%sol 

    | Limitator : forall B1 B2 M M',
        forall (g_1 : 'CoMod(0 Limit M M' ~> B1 )0 %sol) (g_2 : 'CoMod(0 Limit M M' ~> B2 )0 %sol),
          CoMod00_domLimit (<< g_1 ,CoMod g_2 >>)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domLimitP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        ltac:( destruct B1; intros; [ refine (unit)
                                    | refine (CoMod00_domLimit g) ] ).
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B.
        intros; exact: tt.
        constructor 1.
      - destruct B1.
        intros; exact: tt.
        constructor 2.
      - constructor 3.
      - constructor 4.
      - destruct M.
        intros; exact: tt.
        constructor 5.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
    Defined.

  End Destruct_domLimit.

  Module Destruct_domReflectionLimit.

    Inductive CoMod00_domReflectionLimit : forall (B1 B1' B2 : obCoMod),
      ( 'CoMod(0 Reflection0 (Limit B1 B1') ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B B' : obCoMod}, CoMod00_domReflectionLimit (@uCoMod (Reflection0 (Limit B B')))%sol

    | Unit : forall B1 B1' B2 (g : 'CoMod(0 Reflection0 (Reflection0 (Limit B1 B1')) ~> B2 )0),
        CoMod00_domReflectionLimit ('Unit o>CoMod g)%sol 

    | Limitator : forall B1 B2 M M',
        forall (g_1 : 'CoMod(0 Reflection0 (Limit M M') ~> B1 )0 %sol) (g_2 : 'CoMod(0 Reflection0 (Limit M M') ~> B2 )0 %sol),
          CoMod00_domReflectionLimit (<< g_1 ,CoMod g_2 >>)%sol

    | Reflection1 : forall B1 B1' B2 (g : 'CoMod(0 Limit B1 B1' ~> B2 )0 %sol),
        CoMod00_domReflectionLimit (Sol.Reflection1 g)

    | CoUnit : forall A1 A1' A2 (f : 'CoMod(0 Reflection0 (Limit A1 A1') ~> Reflection0 (Reflection0 A2) )0),
        CoMod00_domReflectionLimit (f o>Mod 'CoUnit)%sol

    | LimitatorMod : forall A1 A2 L L',
        forall (f_1 : 'CoMod(0 Reflection0 (Limit L L') ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 (Limit L L') ~> Reflection0 A2 )0),
          CoMod00_domReflectionLimit (<< f_1 ,Mod f_2 >>)%sol

    | RevCoUnit : forall A1 A1' A2 (f : 'CoMod(0 (Reflection0 (Reflection0 (Limit A1 A1'))) ~> Reflection0 A2 )0),
        CoMod00_domReflectionLimit ('RevCoUnit o>Mod f)%sol

    | RevLimit1Unit : forall A1 A2 L L'
                        (f : 'CoMod(0 Reflection0 (Limit L L') ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0 %sol),
        CoMod00_domReflectionLimit (f o>Mod 'RevLimit1Unit)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domReflectionLimitP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        ltac:( destruct B1 as [ B1 |];
                 [ destruct B1; [ refine (unit) |
                                  refine (CoMod00_domReflectionLimit g) ] |
                   refine (unit) ] ).
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B.
        { destruct B. intros; exact: tt.
          constructor 1. }
        intros; exact: tt.
      - destruct B1.
        { destruct B1.
          intros; exact: tt.
          constructor 2. }
        intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - destruct M.
        { destruct M.
          intros; exact: tt.
          constructor 3. }
        intros; exact: tt.
      - destruct B1.
        intros; exact: tt.
        constructor 4.
      - destruct A1.
        intros; exact: tt.
        constructor 5.
      - destruct L.
        intros; exact: tt.
        constructor 6.
      - destruct A1.
        intros; exact: tt.
        constructor 7.
      - destruct L.
        intros; exact: tt.
        constructor 8.
    Defined.

  End Destruct_domReflectionLimit.

  Module Destruct_domReflectionLimitReflection.

    Inductive CoMod00_domReflectionLimitReflection : forall (B1 B1' B2 : obCoMod),
      ( 'CoMod(0 Reflection0 (Limit (Reflection0 B1) (Reflection0 B1')) ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B B' : obCoMod}, CoMod00_domReflectionLimitReflection (@uCoMod (Reflection0 (Limit (Reflection0 B) (Reflection0 B'))))%sol

    | Unit : forall B1 B1' B2 (g : 'CoMod(0 Reflection0 (Reflection0 (Limit (Reflection0 B1) (Reflection0 B1'))) ~> B2 )0),
        CoMod00_domReflectionLimitReflection ('Unit o>CoMod g)%sol 

    | Limitator : forall B1 B2 M M',
        forall (g_1 : 'CoMod(0 Reflection0 (Limit (Reflection0 M) (Reflection0 M')) ~> B1 )0 %sol) (g_2 : 'CoMod(0 Reflection0 (Limit (Reflection0 M) (Reflection0 M')) ~> B2 )0 %sol),
          CoMod00_domReflectionLimitReflection (<< g_1 ,CoMod g_2 >>)%sol

    | Reflection1 : forall B1 B1' B2 (g : 'CoMod(0 Limit (Reflection0 B1) (Reflection0 B1') ~> B2 )0 %sol),
        CoMod00_domReflectionLimitReflection (Sol.Reflection1 g)

    | CoUnit : forall A1 A1' A2 (f : 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A1')) ~> Reflection0 (Reflection0 A2) )0),
        CoMod00_domReflectionLimitReflection (f o>Mod 'CoUnit)%sol

    | LimitatorMod : forall A1 A2 L L',
        forall (f_1 : 'CoMod(0 Reflection0 (Limit (Reflection0 L) (Reflection0 L')) ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 (Limit (Reflection0 L) (Reflection0 L')) ~> Reflection0 A2 )0),
          CoMod00_domReflectionLimitReflection (<< f_1 ,Mod f_2 >>)%sol

    | RevCoUnit : forall A1 A1' A2 (f : 'CoMod(0 (Reflection0 (Reflection0 (Limit (Reflection0 A1) (Reflection0 A1')))) ~> Reflection0 A2 )0),
        CoMod00_domReflectionLimitReflection ('RevCoUnit o>Mod f)%sol

    | RevLimit1Unit : forall A1 A2 L L'
                        (f : 'CoMod(0 Reflection0 (Limit (Reflection0 L) (Reflection0 L')) ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0 %sol),
        CoMod00_domReflectionLimitReflection (f o>Mod 'RevLimit1Unit)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domReflectionLimitReflectionP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        ltac:( destruct B1 as [ B1 |]; [ | intros; refine (unit) ];
                 destruct B1 as [ | B1_1 B1_2]; [ intros; refine (unit) | ];
                   destruct B1_1; [ | intros; refine (unit)];
                     destruct B1_2; [ | intros; refine (unit)];
                       intros; refine (CoMod00_domReflectionLimitReflection g)).
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B; [ | intros; exact: tt ].
        destruct B; [ intros; exact: tt | ].
        destruct B1; [ | intros; exact: tt ].
        destruct B2; [ | intros; exact: tt ].
        constructor 1.
      - destruct B1; [ | intros; exact: tt].
        destruct B1 as [| B1_1 B1_2]; [ intros; exact: tt | ].
        destruct B1_1; [ | intros; exact: tt ].
        destruct B1_2; [ | intros; exact: tt ].
        constructor 2.
      - intros; exact: tt.
      - intros; exact: tt.
      - destruct M as [M | ]; [ | intros; exact: tt ].
        destruct M as [ | M1 M2]; [ intros; exact: tt | ].
        destruct M1; [ | intros; exact: tt ].
        destruct M2; [ | intros; exact: tt ].
        constructor 3.
      - destruct B1 as [| B1_1 B1_2]; [ intros; exact: tt | ].
        destruct B1_1; [ | intros; exact: tt ].
        destruct B1_2; [ | intros; exact: tt ].
        constructor 4.
      - destruct A1 as [| A1_1 A1_2]; [ intros; exact: tt | ].
        destruct A1_1; [ | intros; exact: tt ].
        destruct A1_2; [ | intros; exact: tt ].
        constructor 5.
      - destruct L as [| L1 L2]; [ intros; exact: tt | ].
        destruct L1; [ | intros; exact: tt ].
        destruct L2; [ | intros; exact: tt ].
        constructor 6.
      - destruct A1 as [| A1_1 A1_2]; [ intros; exact: tt | ].
        destruct A1_1; [ | intros; exact: tt ].
        destruct A1_2; [ | intros; exact: tt ].
        constructor 7.
      - destruct L as [| L1 L2]; [ intros; exact: tt | ].
        destruct L1; [ | intros; exact: tt ].
        destruct L2; [ | intros; exact: tt ].
        constructor 8.
    Defined.

  End Destruct_domReflectionLimitReflection.

  Module Destruct_domLimitReflection.

    Inductive CoMod00_domLimitReflection : forall (B1 B1' B2 : obCoMod),
      ( 'CoMod(0 Limit (Reflection0 B1) (Reflection0 B1') ~> B2 )0 %sol ) -> Type :=

    | UnitCoMod : forall {B B' : obCoMod}, CoMod00_domLimitReflection (@uCoMod (Limit (Reflection0 B) (Reflection0 B')))%sol

    | Unit : forall B1 B1' B2 (g : 'CoMod(0 Reflection0 (Limit (Reflection0 B1) (Reflection0 B1')) ~> B2 )0),
        CoMod00_domLimitReflection ('Unit o>CoMod g)%sol 

    | Project_1 : forall B1 B2,
        forall B1' (b1 : 'CoMod(0 (Reflection0 B1) ~> B1' )0),
          CoMod00_domLimitReflection (~_1 @ (Reflection0 B2) o>CoMod b1)%sol 

    | Project_2 : forall B1 B2,
        forall B2' (b2 : 'CoMod(0 (Reflection0 B2) ~> B2' )0),
          CoMod00_domLimitReflection (~_2 @ (Reflection0 B1) o>CoMod b2)%sol 

    | Limitator : forall B1 B2 M M',
        forall (g_1 : 'CoMod(0 Limit (Reflection0 M) (Reflection0 M') ~> B1 )0 %sol) (g_2 : 'CoMod(0 Limit (Reflection0 M) (Reflection0 M') ~> B2 )0 %sol),
          CoMod00_domLimitReflection (<< g_1 ,CoMod g_2 >>)%sol

    where "''CoMod' (0 B1 ~> B2 )0" := (@CoMod00 B1 B2).

    Lemma CoMod00_domLimitReflectionP : forall B1 B2 ( g : 'CoMod(0 B1 ~> B2 )0 %sol ),
        ltac:( destruct B1 as [| B1_1 B1_2]; [ intros; refine (unit) | ];
                 destruct B1_1; [ | intros; refine (unit)];
                   destruct B1_2; [ | intros; refine (unit)];
                     refine (CoMod00_domLimitReflection g) ).
    Proof.
      move => B1 B2 g. case : B1 B2 / g.
      - destruct B as [ | B1 B2]; [ intros; exact: tt |].
        destruct B1; [ | intros; exact: tt ].
        destruct B2; [ | intros; exact: tt ].
        constructor 1.
      - destruct B1 as [ | B1_1 B1_2]; [ intros; exact: tt | ].
        destruct B1_1; [ | intros; exact: tt ].
        destruct B1_2; [ | intros; exact: tt ].
        constructor 2.
      - destruct B1; [ | intros; exact: tt ].
        destruct B2; [ | intros; exact: tt ].
        constructor 3.
      - destruct B1; [ | intros; exact: tt ].
        destruct B2; [ | intros; exact: tt ].
        constructor 4.
      - destruct M as [ | M1 M2]; [ intros; exact: tt | ].
        destruct M1; [ | intros; exact: tt ].
        destruct M2; [ | intros; exact: tt ].
        constructor 5.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
      - intros; exact: tt.
    Defined.

  End Destruct_domLimitReflection.

  Definition toCoMod :
    forall (B1 B2 : obCoMod), 'CoMod(0 B1 ~> B2 )0 %sol -> 'CoMod(0 B1 ~> B2 )0.
  Proof.
    (move => B1 B2 g); elim : B1 B2 / g =>
    [ B
    | B1 B2 g gSol
    | B1 B2 B1' b1 b1Sol
    | B1 B2 B2' b2 b2Sol
    | B1 B2 M g_1 g_1Sol g_2 g_2Sol

    | B1 B2 g gSol
    | A1 A2 f fSol
    | A1 A2 L f_1 f_1Sol f_2 f_2Sol
    | A1 A2 f fSol
    | A1 A2 L f fSol ];
      [ apply: (@uCoMod B)
      | apply: ('Unit o>CoMod gSol)
      | apply: (~_1 @ B2 o>CoMod b1Sol)
      | apply: (~_2 @ B1 o>CoMod b2Sol)
      | apply: (<< g_1Sol ,CoMod g_2Sol >>)

      | apply: ('Refl1 gSol)
      | apply: (fSol o>Mod 'CoUnit)
      | apply: (<< f_1Sol ,Mod f_2Sol >>)
      | apply: ('RevCoUnit o>Mod fSol)
      | apply: (fSol o>Mod 'RevLimit1Unit)].
  Defined.

  Definition isSolb : forall (B1 B2 : obCoMod), forall (g : 'CoMod(0 B1 ~> B2 )0), bool.
  Proof.
    move => B1 B2 g. elim: B1 B2 / g.
    - intros; exact: false.

    - intros; exact: true.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - move => B1 B2 M g_1 IH_g_1 g_2 IH_g_2; refine (IH_g_1 && IH_g_2).
      
    - intros; assumption.
    - intros; assumption.
    - intros; exact: false.
    - intros; exact: false.
    - move => A1 A2 L f_1 IH_f_1 f_2 IH_f_2; refine (IH_f_1 && IH_f_2).
    - intros; assumption.
    - intros; assumption.
  Defined.

  Lemma isSolbN_isSolN : forall (B1 B2 : obCoMod),
      forall fSol : 'CoMod(0 B1 ~> B2 )0 %sol, forall (f : 'CoMod(0 B1 ~> B2 )0), (Sol.toCoMod fSol) = f -> Sol.isSolb f.
  Proof.
    move => B1 B2 fSol ; elim : B1 B2 / fSol ;
             intros; subst; try apply/andP; simpl; auto.
  Qed.

End Sol.

Notation max m n := ((m + (Nat.sub n m))%coq_nat).

Definition grade :
  forall (B1 B2 : obCoMod), 'CoMod(0 B1 ~> B2 )0 -> nat.
Proof.
  move => B1 B2 g; elim : B1 B2 / g.
  - move => B2 B1 g_ grade_g_ B1' g' grade_g' ;
             refine (S  (S (grade_g_ + grade_g')%coq_nat)). (* PolyCoMod *)

  - intros; refine (S O). (* UnitCoMod *)
  - move => B1 B2 g grade_g ; (* one more than Reflection1 , one more than RevCoUnit *)
             refine (S (S (S  (S (grade_g)%coq_nat)))). (* Unit *)
  - move => B1 B2 B1' b1 grade_b1.  (* Project_1  *)
      refine ((S (S grade_b1))).
  - move => B1 B2 B2' b2 grade_b2.  (* Project_2  *)
      refine ((S (S grade_b2))).
  - move => B1 B2 M g_1 grade_g_1 g_2 grade_g_2.  (* Limitator *)
      refine ( ( (* 2 + 7 + 1 *) 10 + (S (S ( ( ( ( ~~ ( (Sol.isSolb g_1 && Sol.isSolb g_2) || (~~ Sol.isSolb g_1 && ~~ Sol.isSolb g_2) ) ) * (grade_g_1 + grade_g_2)%coq_nat)%coq_nat + (( (Sol.isSolb g_1 && Sol.isSolb g_2) || (~~ Sol.isSolb g_1 && ~~ Sol.isSolb g_2) ) * max ( grade_g_1 ) ( grade_g_2 ))%coq_nat)%coq_nat) )))%coq_nat).

  - move => B1 B2 g grade_g ; (* do not count in grade, count only in gradeTotal*)
             refine (  ( (grade_g)%coq_nat)). (* Reflection1 *)
  - move => A1 A2 f grade_f ; (* one more than Reflection1 *)
             refine (S (S  (S (grade_f)%coq_nat))). (* CoUnit *)
  - move => A1 A2 A1' a1 grade_a1.  (* ProjectMod_1  *)
      refine ( (* 2 + 3 + 1 *) 6 + (S (S grade_a1)))%coq_nat.
  - move => A1 A2 A2' a2 grade_a2.  (* ProjectMod_2  *)
      refine ( (* 2 + 3 + 1 *) 6 + (S (S grade_a2)))%coq_nat.
  - move => A1 A2 L f_1 grade_f_1 f_2 grade_f_2.  (* LimitatorMod *)
      refine ( ( (S (S ( ( ( ( ~~ ( (Sol.isSolb f_1 && Sol.isSolb f_2) || (~~ Sol.isSolb f_1 && ~~ Sol.isSolb f_2) ) ) * (grade_f_1 + grade_f_2)%coq_nat)%coq_nat + (( (Sol.isSolb f_1 && Sol.isSolb f_2) || (~~ Sol.isSolb f_1 && ~~ Sol.isSolb f_2) ) * max ( grade_f_1 ) ( grade_f_2 ))%coq_nat)%coq_nat) )))%coq_nat).
  - move => A1 A2 f grade_f ;
             refine ( (S (S  (S (grade_f)%coq_nat)))). (* RevCoUnit *)
  - move => A1 A2 L f grade_f .  (* RevLimit1Unit *)
      refine ( (  ( ( (* 6 + 1 *) 7 + (S (S ( (grade_f)%coq_nat ))))%coq_nat))).
Defined.

Definition gradeTotal :
  forall (B1 B2 : obCoMod), 'CoMod(0 B1 ~> B2 )0 -> nat.
Proof.
  move => B1 B2 g; elim : B1 B2 / g.
  - move => B2 B1 g_ gradeTotal_g_ B1' g' gradeTotal_g' ;
             refine (( (S (S (gradeTotal_g_ + gradeTotal_g')%coq_nat)) + grade (g_ o>CoMod g'))%coq_nat). (* PolyCoMod *)

  - intros; refine (S O). (* UnitCoMod *)
  - move => B1 B2 g gradeTotal_g ; (* one more than Reflection1, one more than RevCoUnit *)
             refine (S (S (S  (S (gradeTotal_g)%coq_nat)))). (* Unit *)
  - move => B1 B2 B1' b1 gradeTotal_b1.  (* Project_1  *)
      refine ((S (S gradeTotal_b1))).
  - move => B1 B2 B2' b2 gradeTotal_b2.  (* Project_2  *)
      refine ((S (S gradeTotal_b2))).
  - move => B1 B2 M g_1 gradeTotal_g_1 g_2 gradeTotal_g_2.  (* Limitator *)
      refine ( ( (* 2 + 7 + 1 *) 10 + (S (S ( ( ( ( ~~ ( (Sol.isSolb g_1 && Sol.isSolb g_2) || (~~ Sol.isSolb g_1 && ~~ Sol.isSolb g_2) ) ) * (gradeTotal_g_1 + gradeTotal_g_2)%coq_nat)%coq_nat + (( (Sol.isSolb g_1 && Sol.isSolb g_2) || (~~ Sol.isSolb g_1 && ~~ Sol.isSolb g_2) ) * max ( gradeTotal_g_1 ) ( gradeTotal_g_2 ))%coq_nat)%coq_nat) )))%coq_nat).

  - move => B1 B2 g gradeTotal_g ; (* count only in gradeTotal*)
             refine (S  (S (gradeTotal_g)%coq_nat)). (* Reflection1 *)
  - move => A1 A2 f gradeTotal_f ; (* one more than Reflection1 *)
             refine (S (S  (S (gradeTotal_f)%coq_nat))). (* CoUnit *)
  - move => A1 A2 A1' a1 gradeTotal_a1.  (* ProjectMod_1  *)
      refine ( (* 2 + 3 + 1 *) 6 + (S (S gradeTotal_a1)))%coq_nat.
  - move => A1 A2 A2' a2 gradeTotal_a2.  (* ProjectMod_2  *)
      refine  ( (* 2 + 3 + 1 *) 6 + (S (S gradeTotal_a2)))%coq_nat.
  - move => A1 A2 L f_1 gradeTotal_f_1 f_2 gradeTotal_f_2.  (* LimitatorMod *)
      refine ( ( (S (S ( ( ( ( ~~ ( (Sol.isSolb f_1 && Sol.isSolb f_2) || (~~ Sol.isSolb f_1 && ~~ Sol.isSolb f_2) ) ) * (gradeTotal_f_1 + gradeTotal_f_2)%coq_nat)%coq_nat + (( (Sol.isSolb f_1 && Sol.isSolb f_2) || (~~ Sol.isSolb f_1 && ~~ Sol.isSolb f_2) ) * max ( gradeTotal_f_1 ) ( gradeTotal_f_2 ))%coq_nat)%coq_nat) )))%coq_nat).
  - move => A1 A2 f gradeTotal_f ;
             refine ( (S (S  (S (gradeTotal_f)%coq_nat)))). (* RevCoUnit *)
  - move => A1 A2 L f gradeTotal_f .  (* RevLimit1Unit *)
      refine ( (  ( ( (* 6 + 1 *) 7 +  (S (S ( (gradeTotal_f)%coq_nat ))))%coq_nat))).
Defined.

Module Red.

  Import Sol.Ex_Notations.
  Reserved Notation "g2 <~~ g1" (at level 70).

  Inductive convCoMod : forall (B1 B2 : obCoMod),
      'CoMod(0 B1 ~> B2 )0 -> 'CoMod(0 B1 ~> B2 )0 -> Prop :=

  (* 1 -- equivalence *)
    
  | CoMod_Trans : forall (B1 B2 : obCoMod) (uTrans g : 'CoMod(0 B1 ~> B2 )0),
      uTrans <~~ g -> forall (g0 : 'CoMod(0 B1 ~> B2 )0),
        g0 <~~ uTrans -> g0 <~~ g
                         

  (* 2 -- congruences *)
                         
  | PolyCoMod_cong_Pre :
      forall (B B' : obCoMod) (g_ g_0 : 'CoMod(0 B ~> B' )0),
      forall (B'' : obCoMod) (g' : 'CoMod(0 B' ~> B'' )0),
        g_0 <~~ g_ -> ( g_0 o>CoMod g' ) <~~ ( g_ o>CoMod g' )

  | PolyCoMod_cong_Post :
      forall (B B' : obCoMod) (g_ : 'CoMod(0 B ~> B' )0),
      forall (B'' : obCoMod) (g' g'0 : 'CoMod(0 B' ~> B'' )0),
        g'0 <~~ g' -> ( g_ o>CoMod g'0 ) <~~ ( g_ o>CoMod g' )

  | Unit_cong : forall B1 B2 (g g0 : 'CoMod(0 Reflection0 B1 ~> B2 )0),
      g0 <~~ g -> ( 'Unit o>CoMod g0 ) <~~ ( 'Unit o>CoMod g )

  | Project_1_cong : forall B1 B2,
      forall B1' (b1 b1' : 'CoMod(0 B1 ~> B1' )0),
        b1' <~~ b1 -> ( ~_1 @ B2 o>CoMod b1' ) <~~ ( ~_1 @ B2 o>CoMod b1 )

  | Project_2_cong : forall B1 B2,
      forall B2' (b2 b2' : 'CoMod(0 B2 ~> B2' )0),
        b2' <~~ b2 -> ( ~_2 @ B1 o>CoMod b2' ) <~~ ( ~_2 @ B1 o>CoMod b2 )

  | Limitator_cong_12 : forall B1 B2 L,
      forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
        g'_1 <~~ g_1 -> g'_2 <~~ g_2 ->
        Sol.isSolb g'_1 -> Sol.isSolb g'_2 -> ( << g'_1 ,CoMod g'_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> )

  | Limitator_cong_1 : forall B1 B2 L,
      forall (g_1 g'_1 : 'CoMod(0 L ~> B1 )0) (g_2 : 'CoMod(0 L ~> B2 )0),
        g'_1 <~~ g_1 ->
        Sol.isSolb g_2 -> Sol.isSolb g'_1 -> ( << g'_1 ,CoMod g_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> )
                                                                
  | Limitator_cong_2 : forall B1 B2 L,
      forall (g_1 : 'CoMod(0 L ~> B1 )0) (g_2 g'_2: 'CoMod(0 L ~> B2 )0),
        g'_2 <~~ g_2 ->
        Sol.isSolb g_1 -> Sol.isSolb g'_2 -> ( << g_1 ,CoMod g'_2 >> ) <~~ ( << g_1 ,CoMod g_2 >> )

  | Reflection1_cong : forall B1 B2 (g g0 : 'CoMod(0 B1 ~> B2 )0),
      g0 <~~ g -> ( Reflection1 g0 ) <~~ ( Reflection1 g )

  | CoUnit_cong : forall A1 A2 (f f0 : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0),
      f0 <~~ f -> ( f0 o>Mod 'CoUnit ) <~~ ( f o>Mod 'CoUnit )


  | ProjectMod_1_cong : forall A1 A2,
      forall A1' (a1 a1' : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
        a1' <~~ a1 -> ( ~_1 @ A2 o>Mod a1' ) <~~ ( ~_1 @ A2 o>Mod a1 )
                                            
  | ProjectMod_2_cong : forall A1 A2,
      forall A2' (a2 a2' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
        a2' <~~ a2 -> ( ~_2 @ A1 o>Mod a2' ) <~~ ( ~_2 @ A1 o>Mod a2 )

  | LimitatorMod_cong_12 : forall B1 B2 L,
      forall (f_1 f'_1 : 'CoMod(0 Reflection0 L ~> Reflection0 B1 )0) (f_2 f'_2: 'CoMod(0 Reflection0 L ~> Reflection0 B2 )0),
        f'_1 <~~ f_1 -> f'_2 <~~ f_2 ->
        Sol.isSolb f'_1 -> Sol.isSolb f'_2 -> ( << f'_1 ,Mod f'_2 >> ) <~~ (<< f_1 ,Mod f_2 >> )

  | LimitatorMod_cong_1 : forall B1 B2 L,
      forall (f_1 f'_1 : 'CoMod(0 Reflection0 L ~> Reflection0 B1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 B2 )0),
        f'_1 <~~ f_1 ->
        Sol.isSolb f_2 -> Sol.isSolb f'_1 -> ( << f'_1 ,Mod f_2 >> ) <~~ (<< f_1 ,Mod f_2 >> )

  | LimitatorMod_cong_2 : forall B1 B2 L,
      forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 B1 )0) (f_2 f'_2: 'CoMod(0 Reflection0 L ~> Reflection0 B2 )0),
        f'_2 <~~ f_2 ->
        Sol.isSolb f_1 -> Sol.isSolb f'_2 -> ( << f_1 ,Mod f'_2 >> ) <~~ (<< f_1 ,Mod f_2 >> )

  | RevCoUnit_cong : forall A1 A2 (f f0 : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0),
      f0 <~~ f -> ( 'RevCoUnit o>Mod f0 ) <~~ ( 'RevCoUnit o>Mod f )

  | RevLimit1Unit_cong : forall A1 A2 L
                           (f f0 : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0),
      f0 <~~ f -> ( f0 o>Mod 'RevLimit1Unit ) <~~ ( f o>Mod 'RevLimit1Unit )
                                                        
  (* 3 -- units *)

  | CoMod_unit :
      forall (B B' : obCoMod) (f : 'CoMod(0 B ~> B' )0),
        ( f )
          <~~ ( ( uCoMod ) o>CoMod f
              : 'CoMod(0 B ~> B' )0 )

  | CoMod_inputUnitCoMod :
      forall (B' B : obCoMod) (g : 'CoMod(0 B' ~> B )0),
        ( g )
          <~~  ( g o>CoMod ( uCoMod )
               : 'CoMod(0 B' ~> B )0 )

  (* for secondo reduction only *)
  (**
  | Reflection1_unit : forall B,
      @uCoMod (Reflection0 B)
              <~~ ( Reflection1 (@uCoMod B)
                    : 'CoMod(0 Reflection0 B ~> Reflection0 B )0 )
   **)

  (* necessary for primo reduction *)
  | Reflection1_unit_PolyMod : forall B B' (f : 'CoMod(0 Reflection0 B' ~> Reflection0 B )0),
      ( f )
        <~~ ( f o>Mod (Reflection1 (@uCoMod B))
              : 'CoMod(0 Reflection0 B' ~> Reflection0 B )0 )

  (* 4 -- polymorphisms *)

  | Unit_morphismPre : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0)
                         B1' (g_ : 'CoMod(0 B1' ~> B1 )0),
      ( 'Unit o>CoMod ( (Reflection1 g_) o>Mod g ) )
        <~~ ( g_ o>CoMod ( 'Unit o>CoMod g )
              : 'CoMod(0 B1' ~> B2 )0 )

  | Unit_morphismPost : forall B1 B2 (g : 'CoMod(0 Reflection0 B1 ~> B2 )0)
                          B2' (g' : 'CoMod(0 B2 ~> B2' )0),
      ( 'Unit o>CoMod ( g o>Mod g' ) )
        <~~ ( ( 'Unit o>CoMod g ) o>CoMod ( g' )
              : 'CoMod(0 B1 ~> B2' )0 )

  | Project_1_morphism : forall B1 B2,
      forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0)
        B1'' (b1' : 'CoMod(0 B1' ~> B1'' )0),
        ( ~_1 @ B2 o>CoMod (b1 o>CoMod b1') )
          <~~ ( ( ~_1 @ B2 o>CoMod b1 ) o>CoMod b1'
              : 'CoMod(0 Limit B1 B2 ~> B1'' )0 )

  | Project_2_morphism : forall B1 B2,
      forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0)
        B2'' (b2' : 'CoMod(0 B2' ~> B2'' )0),
        ( ~_2 @ B1 o>CoMod (b2 o>CoMod b2') )
          <~~ ( ( ~_2 @ B1 o>CoMod b2 ) o>CoMod b2'
                : 'CoMod(0 Limit B1 B2 ~> B2'' )0 )

  | Limitator_morphism : forall B1 B2 M,
      forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
        M' (m : 'CoMod(0 M' ~> M )0),
        ( << m o>CoMod g_1 ,CoMod m o>CoMod g_2 >> )
          <~~ ( m o>CoMod << g_1 ,CoMod g_2 >>
                : 'CoMod(0 M' ~> Limit B1 B2 )0 )


  | Reflection1_morphism : forall B1 B2 (g_ : 'CoMod(0 B1 ~> B2 )0)
                             B3 (g' : 'CoMod(0 B2 ~> B3 )0),
      (Reflection1 (g_ o>CoMod g'))
        <~~ (Reflection1 g_ o>Mod Reflection1 g'
           : 'CoMod(0 Reflection0 B1 ~> Reflection0 B3 )0 )
        

  | CoUnit_morphismPre : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0)
                           A1' (f_ : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1 )0),
      ((f_ o>Mod f) o>Mod 'CoUnit)
        <~~ ( f_ o>Mod (f o>Mod 'CoUnit) )

  | CoUnit_morphismPost : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0)
                            A2' ( f' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
      ( (f o>Mod (Reflection1 f')) o>Mod 'CoUnit)
        <~~ ( (f o>Mod 'CoUnit) o>Mod f'  )

  | ProjectMod_1_morphism : forall A1 A2,
      forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0)
        A1'' (a1' : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1'' )0),
        ( ~_1 @ A2 o>Mod (a1 o>Mod a1') )
          <~~ ( ( ~_1 @ A2 o>Mod a1 ) o>Mod a1'
                : 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> Reflection0 A1'' )0 )

  | ProjectMod_2_morphism : forall A1 A2,
      forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0)
        A2'' (a2' : 'CoMod(0 Reflection0 A2' ~> Reflection0 A2'' )0),
        ( ~_2 @ A1 o>Mod (a2 o>Mod a2') )
          <~~ ( ( ~_2 @ A1 o>Mod a2 ) o>Mod a2'
                : 'CoMod(0 Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) ~> Reflection0 A2'' )0 )

  | LimitatorMod_morphism : forall A1 A2 L,
      forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0)
        L' (l : 'CoMod(0 Reflection0 L' ~> Reflection0 L )0),
        ( << l o>CoMod f_1 ,Mod l o>CoMod f_2 >> )
          <~~ ( l o>CoMod << f_1 ,Mod f_2 >>
                : 'CoMod(0 Reflection0 L' ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0 )

  | RevCoUnit_morphismPre : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0)
                              A1' (f_ : 'CoMod(0 Reflection0 A1' ~> Reflection0 A1 )0),
      ( 'RevCoUnit o>Mod ((Reflection1 f_) o>Mod f) )
        <~~ ( f_ o>Mod ('RevCoUnit o>Mod f)
              : 'CoMod(0 'Refl0 A1' ~> 'Refl0 A2 )0 )

  | RevCoUnit_morphismPost : forall A1 A2 (f : 'CoMod(0 Reflection0 (Reflection0 A1) ~> Reflection0 A2 )0)
                               A2' (f' : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
      ( 'RevCoUnit o>Mod (f o>Mod f') )
        <~~ ( ('RevCoUnit o>Mod f) o>Mod f'
              : 'CoMod(0 'Refl0 A1 ~> 'Refl0 A2' )0 )

  | RevLimit1Unit_morphism :
      forall A1 A2 L
        (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
        L' (f_ : 'CoMod(0 Reflection0 L' ~> Reflection0 L )0),
        ( (f_ o>Mod f) o>Mod 'RevLimit1Unit )
          <~~ ( f_ o>Mod (f o>Mod 'RevLimit1Unit)
                : 'CoMod(0 Reflection0 L' ~> Reflection0 (Limit A1 A2) )0 )

  (* logically-derivable from definition-conversion , necessary for primo reduction *)
  | Reflection1_Project_1_morphism : forall A1 A2,
      forall B1 (b1 : 'CoMod(0 Reflection0 A1 ~> B1 )0),
      forall A1'' (f_1 : 'CoMod(0 Reflection0 A1'' ~> ('Refl0 A1) )0)
        (f_2 : 'CoMod(0 Reflection0 A1'' ~> ('Refl0 A2) )0),
        ( 'RevCoUnit o>Mod (Reflection1 (f_1 o>Mod b1)) )
          <~~ ( << f_1 ,Mod f_2 >> o>Mod Reflection1 (~_1 @ (Reflection0 A2) o>CoMod b1)
                : 'CoMod(0 'Refl0 A1'' ~> 'Refl0 B1 )0 )

  (* logically-derivable from definition-conversion , necessary for primo reduction *)
  | Reflection1_Project_2_morphism : forall A1 A2,
      forall B2 (b2 : 'CoMod(0 Reflection0 A2 ~> B2 )0),
      forall A2'' (f_1 : 'CoMod(0 Reflection0 A2'' ~> ('Refl0 A1) )0)
        (f_2 : 'CoMod(0 Reflection0 A2'' ~> ('Refl0 A2) )0),
        ( 'RevCoUnit o>Mod (Reflection1 (f_2 o>Mod b2)) )
          <~~ ( << f_1 ,Mod f_2 >> o>Mod Reflection1 (~_2 @ (Reflection0 A1) o>CoMod b2)
                : 'CoMod(0 'Refl0 A2'' ~> 'Refl0 B2 )0 )

  (* logically-derivable from definition-conversion , necessary for primo reduction *)
  | Reflection1_Limitator_morphism : forall B1 B2 M,
      forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0)
        M' (m : 'CoMod(0 Reflection0 M' ~> Reflection0 M )0),
        ( << m o>Mod Reflection1 g_1 ,Mod m o>Mod Reflection1 g_2 >> o>Mod 'RevLimit1Unit )
          <~~ ( m o>CoMod Reflection1 << g_1 ,CoMod g_2 >>
                : 'CoMod(0 Reflection0 M' ~> Reflection0 (Limit B1 B2) )0 )

  (* 5 -- counit-cancellations *)
          
  (* for secondo reduction only :
     outer counit-cancellation  *)
  (**
  | CoUnitReflection_Unit : forall B1 B2 (g : 'CoMod(0 B1 ~> B2 )0),
      ( Reflection1 g  )
        <~~ ( (Reflection1 ( 'Unit o>CoMod (Reflection1 g) )) o>Mod 'CoUnit
              : 'CoMod(0 'Refl0 B1 ~> 'Refl0 B2 )0 )
   **)
  (* for secondo reduction only : 
     inner counit-cancellation *)
  (**
  | Unit_CoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0),
      ( f )
        <~~ ( 'Unit o>CoMod ((Reflection1 f) o>Mod 'CoUnit)
              : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0)
   **)

  (* 6 -- retractive reflection *)

  (* for secondo reduction only :
     counit , reverse counit *)
  (**
  | CoUnit_RevCoUnit : forall A1 A2 (f : 'CoMod(0 Reflection0 A1 ~> Reflection0 (Reflection0 A2) )0),
      ( f )
        <~~ ( 'RevCoUnit o>Mod (Reflection1 (f o>Mod 'CoUnit))
              : 'CoMod(0 'Refl0 A1 ~> 'Refl0 'Refl0 A2 )0 )
   **)

  (* for secondo reduction only : 
     reverse counit , counit *)
  (**
  | RevCoUnit_CoUnit : forall A1 A2 (g : 'CoMod(0 Reflection0 A1 ~> Reflection0 A2 )0),
      ( g )
        <~~ ( ('RevCoUnit o>Mod (Reflection1 g)) o>Mod 'CoUnit
              : 'CoMod(0 'Refl0 A1 ~> 'Refl0 A2 )0 )
   **)

  (* logically-derivable , non primo reduction ,
   maybe for solution and confluence only :
   lemma that reflection1 of unit is reversible *)
  (**
  | Unit_RevCoUnit : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
      ( 'RevCoUnit o>Mod (Reflection1 g) )
        <~~ ( Reflection1 ('Unit o>CoMod g)
              : 'CoMod(0 Reflection0 A ~> Reflection0 B )0 )
   **)

  (* logically-derivable , necessary for primo reduction *)
  | Unit_RevCoUnit_PolyCoMod : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
      forall A' (f : 'CoMod(0 Reflection0 A' ~> Reflection0 A )0),
        ( f o>Mod ('RevCoUnit o>Mod (Reflection1 g)) )
          <~~ ( f o>Mod (Reflection1 ('Unit o>CoMod g))
                : 'CoMod(0 Reflection0 A' ~> Reflection0 B )0 )

  (* logically-derivable , non primo reduction ,
   maybe for solution and confluence only :
   lemma that unit over reflection0 is reversible *)
  (**
  | RevCoUnit_Unit : forall A B (g : 'CoMod(0 Reflection0 A ~> B )0),
      ( 'RevCoUnit o>Mod (Reflection1 g) )
        <~~ ( 'Unit o>CoMod (Reflection1 g)
              : 'CoMod(0 Reflection0 A ~> Reflection0 B )0 )
   **)


  (* 7 -- projection cancel particular-pairing *)

  | Limitator_Project_1 : forall B1 B2 M,
      forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
      forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
        ( g_1 o>CoMod b1 )
          <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_1 @ B2 o>CoMod b1)
                : 'CoMod(0 M ~> B1' )0 )

  | Limitator_Project_2 : forall B1 B2 M,
      forall (g_1 : 'CoMod(0 M ~> B1 )0) (g_2 : 'CoMod(0 M ~> B2 )0),
      forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
        ( g_2 o>CoMod b2 )
          <~~ ( << g_1 ,CoMod g_2 >> o>CoMod ( ~_2 @ B1 o>CoMod b2)
                : 'CoMod(0 M ~> B2' )0 )

  | LimitatorMod_Project_1 : forall A1 A2 L,
      forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
      forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
        ( f_1 o>Mod a1 )
          <~~ ( << f_1 ,Mod f_2 >> o>Mod ( ~_1 @ A2 o>Mod a1 )
                : 'CoMod(0 'Refl0 L ~> 'Refl0 A1' )0 )

  | LimitatorMod_Project_2 : forall A1 A2 L,
      forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
      forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
        ( f_2 o>Mod a2 )
          <~~ ( << f_1 ,Mod f_2 >> o>Mod ( ~_2 @ A1 o>Mod a2 )
                : 'CoMod(0 'Refl0 L ~> 'Refl0 A2' )0 )


  (* 8 -- Limit1_id is reversible via being id *)

  (* for secondo reduction only *)
  (**
  | Limitator_Project_1_Project_2 : forall B1 B2,
      ( uCoMod )
        <~~ ( << ~_1 @ B2 o>CoMod uCoMod ,CoMod ~_2 @ B1 o>CoMod uCoMod >>
              : 'CoMod(0 Limit B1 B2 ~> Limit B1 B2 )0 )

   **)

  (* for secondo reduction only *)
  (**
  | LimitatorMod_Project_1_Project_2 : forall B1 B2,
      ( uCoMod )
        <~~ ( << ~_1 @ B2 o>Mod uCoMod ,Mod ~_2 @ B1 o>Mod uCoMod >>
              : 'CoMod(0 'Refl0 Limit ('Refl0 B1) ('Refl0 B2) ~> 'Refl0 Limit ('Refl0 B1) ('Refl0 B2) )0 )
   **)

  (* 9 -- projection cancel single-instance-of-some-pairing RevLimit1Unit *)

  | RevLimit1Unit_ReflectionProject1 : forall A1 A2 L
                                         (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
                                         B (g : 'CoMod(0 A1 ~> B )0),
      ( f o>Mod ( ~_1 o>Mod (Reflection1 g) ) )
        <~~ ( (f o>Mod 'RevLimit1Unit) o>Mod Reflection1 (~_1 @ A2 o>CoMod g)
              : 'CoMod(0 'Refl0 L ~> 'Refl0 B )0 )

  | RevLimit1Unit_ReflectionProject2 : forall A1 A2 L
                                         (f : 'CoMod(0 Reflection0 L ~> Reflection0 (Limit (Reflection0 A1) (Reflection0 A2)) )0)
                                         B (g : 'CoMod(0 A2 ~> B )0),
      ( f o>Mod ( ~_2 o>Mod (Reflection1 g) ) )
        <~~ ( (f o>Mod 'RevLimit1Unit) o>Mod Reflection1 ( ~_2 @ A1 o>CoMod g )
              : 'CoMod(0 'Refl0 L ~> 'Refl0 B )0 )

  (* 10 -- Limit1Unit is reversible via explicit RevLimit1Unit morphism 
         for sense , non for primo reduction *)

  (* for secondo reduction only *)
  (**
  | Limit1Unit_RevLimit1Unit : forall B1 B2,
      ( uCoMod )
        <~~ ( (@Limit1Unit B1 B2) o>Mod 'RevLimit1Unit
              : 'CoMod(0 'Refl0 Limit B1 B2 ~> 'Refl0 Limit B1 B2 )0 )
   **)

  (* for secondo reduction only *)
  (**
  | RevLimit1Unit_Limit1Unit : forall A1 A2,
      ( uCoMod )
        <~~ (  << ( ~_1 @ A2 o>Mod Reflection1 ('Unit o>CoMod (@uCoMod (Reflection0 A1))) ) ,Mod ( ~_2 @ A1 o>Mod Reflection1 ('Unit o>CoMod (@uCoMod (Reflection0 A2))) ) >> o>Mod 'RevLimit1Unit
               : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) )0 )
   **)

  (* 11 -- for sense , for secondo reduction only,
   alternative for the logically-derivable lemma that [ reflector of [ limit-in-CoMod cone of diagram-in-Mod ] ] is limit-in-Mod cone  *)

  | ProjectMod_1_Project_1 : forall A1 A2,
      forall A1' (a1 : 'CoMod(0 Reflection0 A1 ~> Reflection0 A1' )0),
        ( Reflection1 (~_1 @ (Reflection0 A2) o>CoMod a1) o>Mod 'CoUnit )
          <~~ ( ~_1 @ A2 o>Mod a1
                : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 A1' )0 )

  | ProjectMod_2_Project_2 : forall A1 A2,
      forall A2' (a2 : 'CoMod(0 Reflection0 A2 ~> Reflection0 A2' )0),
        ( Reflection1 (~_2 @ (Reflection0 A1) o>CoMod a2) o>Mod 'CoUnit )
          <~~ ( ~_2 @ A1 o>Mod a2
                : 'CoMod(0 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) ~> 'Refl0 A2' )0 )

  (* for secondo reduction degradation only , REALLY ONLY *)
  (**
  | LimitatorMod_Limitator : forall A1 A2 L,
      forall (f_1 : 'CoMod(0 Reflection0 L ~> Reflection0 A1 )0) (f_2 : 'CoMod(0 Reflection0 L ~> Reflection0 A2 )0),
        ( Reflection1 << 'Unit o>CoMod f_1 ,CoMod 'Unit o>CoMod f_2 >> )
          <~~ ( << f_1 ,Mod f_2 >>
                : 'CoMod(0 'Refl0 L ~> 'Refl0 Limit ('Refl0 A1) ('Refl0 A2) )0 )
   **)
          
(**
  (* 12 -- logically-derivable, for tertio reduction degradation, 
   for the solution and confluence only , 
   after elimitations of both ProjectMod LimitatorMod *)

  | Project_1_Limitator : 
      forall B1 B2,
      forall B1_ (b1_ : 'CoMod(0 B1 ~> B1_ )0),
      forall B1' (b1 : 'CoMod(0 B1 ~> B1' )0),
        ( ~_1 o>CoMod << b1_ ,CoMod b1 >> )
          <~~ ( << ~_1 @ B2 o>CoMod b1_ ,CoMod ~_1 @ B2 o>CoMod b1 >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B1_ B1' )0 )

  | Project_2_Limitator : 
      forall B1 B2,
      forall B2_ (b2_ : 'CoMod(0 B2 ~> B2_ )0),
      forall B2' (b2 : 'CoMod(0 B2 ~> B2' )0),
        ( ~_2 o>CoMod << b2_ ,CoMod b2 >> )
          <~~ ( << ~_2 @ B1 o>CoMod b2_ ,CoMod ~_2 @ B1 o>CoMod b2 >>
                : 'CoMod(0 Limit B1 B2 ~> Limit B2_ B2' )0 )
**)
  where "g2 <~~ g1" := (@convCoMod _ _ g2 g1).

                         
  Module Export Ex_Notations.

    Notation "g2 <~~ g1" := (@convCoMod _ _ g2 g1).
    Hint Constructors convCoMod.

  End Ex_Notations.
  
  Lemma Red_convCoMod_convCoMod :
  forall (B1 B2 : obCoMod) (gDeg g : 'CoMod(0 B1 ~> B2 )0),
    gDeg <~~ g -> gDeg ~~~ g.
  Proof.
    move => B1 B2 g gDeg. elim; eauto.
  Qed.

  Lemma isSolb_isRed_False_alt : forall (B1 B2 : obCoMod) (f : 'CoMod(0 B1 ~> B2 )0),
      forall fRed, fRed <~~ f ->
              ~~ Sol.isSolb f .
    induction 1 ; ( move => //= ) ;
      repeat match goal with
             | [ HH : is_true (Sol.isSolb _)  |- _ ] =>
               try rewrite -> HH in *; clear HH
             | [   |- context [Sol.isSolb ?ggg]  ] => destruct (Sol.isSolb ggg)
             end;
      simpl; move => //= .
  Qed. 

  Ltac tac_isSolb :=
    repeat match goal with
           | [ HH : _ <~~ ?fff  |- _ ] =>
             move : (isSolb_isRed_False_alt HH) ; clear HH
           | [ HH : is_true (Sol.isSolb _)  |- _ ] =>
             try rewrite -> HH in *; clear HH
           | [ HH : is_true (~~ Sol.isSolb _)  |- _ ] =>
             try rewrite -> (negbTE HH) in *; clear HH
           | [   |- context [Sol.isSolb ?ggg]  ] => destruct (Sol.isSolb ggg)
           end.

  Lemma degrade :
    forall (B1 B2 : obCoMod) (gDeg g : 'CoMod(0 B1 ~> B2 )0),
      gDeg <~~ g ->
      ((grade gDeg) <= (grade g))%coq_nat
      /\ ((gradeTotal gDeg) < (gradeTotal g))%coq_nat.
  Proof.
    move => B1 B2 gDeg g red_g; elim : B1 B2 gDeg g / red_g;
             try solve [ ( rewrite (* for alt /gradeTotal *)
                           /=  => * ; tac_isSolb; move => //= ) ;
                         abstract intuition Omega.omega ].
  Qed.
  (* /!\ YES /!\ *)

  Lemma degradeTotal_gt0 :
    forall (B1 B2 : obCoMod) (f : 'CoMod(0 B1 ~> B2 )0),
      ((S O) <= (gradeTotal f))%coq_nat.
  Proof.
    move=> B1 B2 f; case : f => /= * ; tac_isSolb; move => //= ; Omega.omega.
  Qed.

End Red.

Section Section1.

  Import Sol.Ex_Notations.
  Import Red.Ex_Notations.

  Ltac rewriterCoMod :=
    repeat match goal with
           | [ HH : @eq (CoMod00 _ _) _ _  |- _ ] =>
             try rewrite -> HH in *; clear HH
           end.

  Ltac tac_reduce :=
    simpl in *; abstract (
                    intuition (eauto; try subst; rewriterCoMod; try congruence;
                               eauto 12)).

  Ltac tac_reduce_eauto :=
    simpl in *; abstract (
                    intuition (eauto; try subst; rewriterCoMod; try congruence;
                               eauto )).

  Ltac tac_degrade H_gradeTotal a_Sol_prop a'Sol_prop :=
    destruct a_Sol_prop as [a_Sol_prop |a_Sol_prop];
    [ move : (Red.degrade a_Sol_prop);
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    | subst;
      destruct a'Sol_prop as [a'Sol_prop |a'Sol_prop];
      [ move : (Red.degrade a'Sol_prop)
      | subst ]
    ];
    move : H_gradeTotal; clear; rewrite /= ;
    Red.tac_isSolb; move => //= * ; abstract intuition Omega.omega.


  Fixpoint solveCoMod len {struct len} :
    forall (B1 B2 : obCoMod) (g : 'CoMod(0 B1 ~> B2 )0)
      (H_gradeTotal : (gradeTotal g <= len)%coq_nat),
      { gSol : 'CoMod(0 B1 ~> B2 )0 %sol
      & {( (Sol.toCoMod gSol) <~~ g )} + {( (Sol.toCoMod gSol) = g )} }.
  Proof.
    case : len => [ | len ].

    (* n is O *)
    - clear; ( move => B1 B2 g H_gradeTotal ); exfalso;
        move : (Red.degradeTotal_gt0 g) => H_degradeTotal_gt0; abstract Omega.omega.

    (* n is (S n) *)
    - move => B1 B2 g; case : B1 B2 / g =>
      [ B2 B1 g_ B1' g'  (* g_ o>CoMod g' *)
      | B  (* @uCoMod B*)
      | B1 B2 g (* 'Unit o>CoMod g *)
      | B1 B2 B1' b1 (* ~_1 @ B2 o>CoMod b1 *)
      | B1 B2 B2' b2 (* ~_2 @ B1 o>CoMod b2 *)
      | B1 B2 M g_1 g_2 (* << g_1 ,CoMod g_2 >> *)
      | B1 B2 g (* Reflection1 g *)
      | A1 A2 f (* f o>Mod 'CoUnit *)
      | A1 A2 A1' a1 (* ~_1 @ A2 o>Mod a1 *)
      | A1 A2 A2' a2 (* ~_2 @ A1 o>Mod a2 *)
      | A1 A2 L f_1 f_2 (* << f_1 ,Mod f_2 >> *)
      | A1 A2 f (* 'RevCoUnit o>Mod f *)
      | A1 A2 L f (* f o>Mod 'RevLimit1Unit *) ].

      (* g is g_ o>CoMod g' *)
      + all: cycle 1. 

      (* g is @uCoMod B *)
      + move => H_gradeTotal. exists (@uCoMod B)%sol. right. reflexivity.

      (* g is 'Unit o>CoMod g *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ g) =>
        [ | gSol gSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists ('Unit o>CoMod gSol)%sol .
          clear -gSol_prop. tac_reduce.

      (* g is ~_1 @ B2 o>CoMod b1 *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ b1) =>
        [ | b1Sol b1Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (~_1 @ B2 o>CoMod b1Sol)%sol .
          clear -b1Sol_prop. tac_reduce.

      (* g is ~_2 @ B1 o>CoMod b2 *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ b2) =>
        [ | b2Sol b2Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (~_2 @ B1 o>CoMod b2Sol)%sol .
          clear -b2Sol_prop. tac_reduce.

      (* g is << g_1 ,CoMod g_2 >> *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ g_1) =>
        [ | g_1Sol g_1Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; Red.tac_isSolb; move => //= *; abstract Omega.omega.
          case : (solveCoMod len _ _ g_2) =>
          [ | g_2Sol g_2Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; Red.tac_isSolb; move => //= *; abstract Omega.omega.
        * exists ( << g_1Sol ,CoMod g_2Sol >> )%sol .
          clear - g_1Sol_prop g_1Sol_prop g_2Sol_prop g_2Sol_prop.
          move: (@Sol.isSolbN_isSolN _ _ g_1Sol _ Logic.eq_refl).
          move: (@Sol.isSolbN_isSolN _ _ g_2Sol _ Logic.eq_refl).
          tac_reduce_eauto.

      (* g is Reflection1 g *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ g) =>
        [ | gSol gSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (Sol.Reflection1 gSol).
          clear -gSol_prop. tac_reduce.
        
      (* g is f o>Mod 'CoUnit *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ f) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (fSol o>Mod 'CoUnit)%sol .
          clear -fSol_prop. tac_reduce.

      (* g is ~_1 o>Mod a1 *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ ( ( Reflection1 (~_1 @ (Reflection0 A2) o>CoMod a1) o>Mod 'CoUnit ))) =>
        [ | gSol gSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (gSol)%sol .
          clear -gSol_prop. tac_reduce.

      (* g is ~_2 o>Mod a2 *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ ( ( Reflection1 (~_2 @ (Reflection0 A1) o>CoMod a2) o>Mod 'CoUnit ))) =>
        [ | gSol gSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (gSol)%sol .
          clear -gSol_prop. tac_reduce.

      (* g is << f_1 ,Mod f_2 >> *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ f_1) =>
        [ | f_1Sol f_1Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; Red.tac_isSolb; move => //= *; abstract Omega.omega.
          case : (solveCoMod len _ _ f_2) =>
          [ | f_2Sol f_2Sol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; Red.tac_isSolb; move => //= *; abstract Omega.omega.
        * exists ( << f_1Sol ,Mod f_2Sol >> )%sol .
          clear - f_1Sol_prop f_1Sol_prop f_2Sol_prop f_2Sol_prop.
          move: (@Sol.isSolbN_isSolN _ _ f_1Sol _ Logic.eq_refl).
          move: (@Sol.isSolbN_isSolN _ _ f_2Sol _ Logic.eq_refl).
          tac_reduce_eauto.

      (* g is 'RevCoUnit o>Mod f *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ f) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists ('RevCoUnit o>Mod fSol)%sol .
          clear -fSol_prop. tac_reduce.

      (* g is f o>Mod 'RevLimit1Unit *)
      + move => H_gradeTotal.
        case : (solveCoMod len _ _ f) =>
        [ | fSol fSol_prop ].
        * move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega.
        * exists (fSol o>Mod 'RevLimit1Unit)%sol .
          clear - fSol_prop. tac_reduce.

      (* g is g_ o>CoMod g' *)
      + move => H_gradeTotal.
      case : (solveCoMod len _ _ g_) =>
        [ | g_Sol g_Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega | ].
        case : (solveCoMod len _ _ g') =>
        [ | g'Sol g'Sol_prop ];
          [ move : H_gradeTotal; clear;
            rewrite (* /gradeTotal *) /=; move => *; abstract Omega.omega | ].

        (* g is (g_ o>Mod g') , to (g_Sol o>Mod g'Sol) *)
        destruct g_Sol as
            [ B  (* @uCoMod B %sol *)
            | B1 B2 g_Sol (* 'Unit o>CoMod g_Sol %sol *)
            | B1 B2 _B1' b1_Sol (* ~_1 @ B2 o>CoMod b1_Sol *)
            | B1 B2 B2' b2_Sol (* ~_2 @ B1 o>CoMod b2_Sol *)
            | B1 B2 M g__1Sol g__2Sol (* << g__1Sol ,CoMod g__2Sol >> %sol *)
            | B1 B2 g_Sol (* 'Refl1 g_Sol %sol *)
            | A1 A2 f_Sol (* f_Sol o>Mod 'CoUnit %sol *)
            | A1 A2 L f__1Sol f__2Sol (* << f__1Sol ,Mod f__2Sol >> %sol *)
            | A1 A2 f_Sol (* 'RevCoUnit o>Mod f_Sol %sol *)
            | A1 A2 L f_Sol (* f_Sol o>Mod 'RevLimit1Unit %sol *) ].

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((@uCoMod B) o>CoMod g'Sol) *)
      + case : (solveCoMod len _ _ ((Sol.toCoMod g'Sol))) =>
        [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
        * tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
        * exists (g_Sol_o_g'Sol).
          clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('Unit o>CoMod g_Sol) o>CoMod g'Sol) *)
      + case : (solveCoMod len _ _ (( (Sol.toCoMod g_Sol) o>CoMod (Sol.toCoMod g'Sol)))) =>
        [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
        * tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
        * exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
          clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((~_1 o>CoMod b1_Sol) o>CoMod g'Sol) *)
      + case : (solveCoMod len _ _ (( (Sol.toCoMod (b1_Sol)) o>CoMod (Sol.toCoMod g'Sol)))) =>
        [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
        * tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
        * exists (~_1 o>CoMod g_Sol_o_g'Sol)%sol.
          clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((~_2 o>CoMod b2_Sol) o>CoMod g'Sol) *)
      + case : (solveCoMod len _ _ (( (Sol.toCoMod (b2_Sol)) o>CoMod (Sol.toCoMod g'Sol)))) =>
        [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
        * tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
        * exists (~_2 o>CoMod g_Sol_o_g'Sol)%sol.
          clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          
      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domLimit.CoMod00_domLimitP g'Sol) => g'Sol_domLimitP.
        destruct g'Sol_domLimitP as
            [ B B' (* @uCoMod (Limit B B') %sol *)
            | B1 B1' B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | B1 B2 B1' b1'Sol (* ~_1 @ B2 o>CoMod b1'Sol *)
            | B1 B2 B2' b2'Sol (* ~_2 @ B1 o>CoMod b2'Sol *)
            | B1 B2 _M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod (@uCoMod B)) *)
        * exists ((<< g__1Sol ,CoMod g__2Sol >>)%sol).
          clear -g_Sol_prop g'Sol_prop. tac_reduce.

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  ('Unit o>CoMod g'Sol) ) *)
        * { case : (solveCoMod len _ _ (Reflection1 (Sol.toCoMod (<< g__1Sol ,CoMod g__2Sol >>%sol)) o>CoMod Sol.toCoMod g'Sol)) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMOd g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (~_1 o>CoMod b1'Sol) ) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod g__1Sol) o>CoMod (Sol.toCoMod b1'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol).
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (~_2 o>CoMod b2'Sol) ) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod g__2Sol) o>CoMod (Sol.toCoMod b2'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol).
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod g'Sol) , is  ((<< g__1Sol ,CoMod g__2Sol >>) o>CoMod  (<< g'_1Sol ,CoMod g'_2Sol >>) ) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod (<< g__1Sol ,CoMod g__2Sol >> %sol)) o>CoMod (Sol.toCoMod g'_1Sol))) =>
            [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
            - move: (@Sol.isSolbN_isSolN _ _ g__1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ g__2Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
              Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ ((Sol.toCoMod (<< g__1Sol ,CoMod g__2Sol >> %sol)) o>CoMod (Sol.toCoMod g'_2Sol))) =>
              [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
              + move: (@Sol.isSolbN_isSolN _ _ g__1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g__2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              + exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >> %sol).
                clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                move: (@Sol.isSolbN_isSolN _ _ g__1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g__2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                simpl in *; abstract (
                                intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                           try eapply (Red.CoMod_Trans (uTrans := (<< Sol.toCoMod g__1Sol ,CoMod Sol.toCoMod g__2Sol >>) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                           eauto )).
          }
          
      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domReflection.CoMod00_domReflectionP g'Sol) => g'Sol_domReflectionP. simpl in *.
        destruct g'Sol_domReflectionP as
            [ B  (* @uCoMod B %sol *)
            | _B1 B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | _B1 B2 M g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *)
            | _B1 B2 g'Sol (* 'Refl1 g'Sol %sol *)
            | A1 A2 f'Sol (* f'Sol o>Mod 'CoUnit %sol *)
            | A1 A2 L f'_1Sol f'_2Sol (* << f'_1Sol ,Mod f'_2Sol >> %sol *)
            | A1 A2 f'Sol (* 'RevCoUnit o>Mod f'Sol %sol *)
            | A1 A2 L f'Sol (* f'Sol o>Mod 'RevLimit1Unit %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod (@uCoMod B)) *)
        * exists ( ('Refl1 g_Sol)%sol ) .
          clear -g_Sol_prop g'Sol_prop. tac_reduce.
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod ('Unit o>CoMod g'Sol)) *)
        * { case : (solveCoMod len _ _ (( ('Refl1 ('Refl1 (Sol.toCoMod g_Sol))) o>CoMod Sol.toCoMod g'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod (<< g'_1Sol ,CoMod g'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ ( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod g'_1Sol)) =>
            [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
            - (*move: (@Sol.isSolbN_isSolN _ _ g_Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl). *)
              tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod g'_2Sol))) =>
              [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              + exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >>)%sol.
                clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                move: (@Sol.isSolbN_isSolN _ _ g_Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                simpl in *; abstract (
                                intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                           try eapply (Red.CoMod_Trans (uTrans := Reflection1 (Sol.toCoMod g_Sol) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                           eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod 'Refl1 g'Sol) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod g_Sol o>CoMod Sol.toCoMod g'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Refl1 g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod (f'Sol o>Mod 'CoUnit)) *)
        * { case : (solveCoMod len _ _ (( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod (<< f'_1Sol ,Mod f'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ ( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod f'_1Sol)) =>
            [ | g_Sol_o_f'_1Sol g_Sol_o_f'_1Sol_prop ].
            - (*move: (@Sol.isSolbN_isSolN _ _ g_Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl). *)
              tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod f'_2Sol))) =>
              [ | g_Sol_o_f'_2Sol g_Sol_o_f'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              + exists (<< g_Sol_o_f'_1Sol ,Mod g_Sol_o_f'_2Sol >>)%sol.
                clear -g_Sol_prop g'Sol_prop g_Sol_o_f'_1Sol_prop g_Sol_o_f'_2Sol_prop.
                move: (@Sol.isSolbN_isSolN _ _ g_Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_2Sol _ Logic.eq_refl).
                simpl in *; abstract (
                                intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                           try eapply (Red.CoMod_Trans (uTrans := Reflection1 (Sol.toCoMod g_Sol) o>CoMod  << Sol.toCoMod f'_1Sol ,Mod Sol.toCoMod f'_2Sol >> ));
                                           eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod ('RevCoUnit o>Mod f'Sol)) *)
        * { case : (solveCoMod len _ _ (( ('Refl1 ('Refl1 (Sol.toCoMod g_Sol))) o>CoMod Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
        
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ('Refl1 g_Sol o>CoMod (f'Sol o>Mod 'RevLimit1Unit)) *)
        * { case : (solveCoMod len _ _ (( ('Refl1 (Sol.toCoMod g_Sol)) o>CoMod Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'RevLimit1Unit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domReflection.CoMod00_domReflectionP g'Sol) => g'Sol_domReflectionP.
        destruct g'Sol_domReflectionP as
            [ B  (* @uCoMod B %sol *)
            | B1 B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | B1 B2 M g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *)
            | B1 B2 g'Sol (* 'Refl1 g'Sol %sol *)
            | _A1 A2 f'Sol (* f'Sol o>Mod 'CoUnit %sol *)
            | _A1 A2 L f'_1Sol f'_2Sol (* << f'_1Sol ,Mod f'_2Sol >> %sol *)
            | _A1 A2 f'Sol (* 'RevCoUnit o>Mod f'Sol %sol *)
            | _A1 A2 L f'Sol (* f'Sol o>Mod 'RevLimit1Unit %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod (@uCoMod B)) *)
        * exists ( (f_Sol o>Mod 'CoUnit)%sol ) .
          clear -g_Sol_prop g'Sol_prop. tac_reduce.
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod ('Unit o>CoMod g'Sol)) *)
        (* only Unit_morphismPre is possible *)
        * { case : (solveCoMod len _ _ ((Reflection1 (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod g'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod (<< g'_1Sol ,CoMod g'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ (( (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod g'_1Sol))) =>
            [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod g'_2Sol))) =>
              [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              +  exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >>)%sol.
                 clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                 move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                 simpl in *; abstract (
                                 intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                            try eapply (Red.CoMod_Trans (uTrans := (Sol.toCoMod f_Sol o>Mod 'CoUnit) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                            eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod Refl1 g'Sol) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol o>CoMod ('Refl1 (Sol.toCoMod (Sol.Reflection1 g'Sol)))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod (f'Sol o>Mod 'CoUnit)) *)
        (* both CoUnit_morphismPost CoUnit_morphismPre possible , CoUnit_morphismPost chosen *)
        * { (* by CoUnit_morphismPre *)
            (* case : (solveCoMod len _ _ (( (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod f'Sol))) => *)
            case : (solveCoMod len _ _ (( (Sol.toCoMod f_Sol) o>Mod ('Refl1 ((Sol.toCoMod f'Sol) o>Mod 'CoUnit))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod (<< f'_1Sol ,CoMod f'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ (( (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod f'_1Sol))) =>
            [ | g_Sol_o_f'_1Sol g_Sol_o_f'_1Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( (Sol.toCoMod (f_Sol o>Mod 'CoUnit)%sol) o>CoMod Sol.toCoMod f'_2Sol))) =>
              [ | g_Sol_o_f'_2Sol g_Sol_o_f'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              +  exists (<< g_Sol_o_f'_1Sol ,Mod g_Sol_o_f'_2Sol >>)%sol.
                 clear -g_Sol_prop g'Sol_prop g_Sol_o_f'_1Sol_prop g_Sol_o_f'_2Sol_prop.
                 move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_2Sol _ Logic.eq_refl).
                 simpl in *; abstract (
                                 intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                            try eapply (Red.CoMod_Trans (uTrans := (Sol.toCoMod f_Sol o>Mod 'CoUnit) o>CoMod  << Sol.toCoMod f'_1Sol ,Mod Sol.toCoMod f'_2Sol >> ));
                                            eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod ('RevCoUnit o>Mod f'Sol)) *)
        (* either reduction by pre or post polymorphism is possible , Unit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ (( (Sol.toCoMod f_Sol) o>CoMod ('Refl1 ('RevCoUnit o>Mod (Sol.toCoMod f'Sol)))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'CoUnit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'CoUnit) o>CoMod (f_Sol o>Mod 'RevLimit1Unit)) *)
        * { case : (solveCoMod len _ _ (( (Sol.toCoMod f_Sol) o>CoMod ('Refl1 (((Sol.toCoMod f'Sol) o>Mod 'RevLimit1Unit)))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domReflectionLimitReflection.CoMod00_domReflectionLimitReflectionP g'Sol) => g'Sol_domReflectionLimitReflectionP.
        destruct g'Sol_domReflectionLimitReflectionP as
            [ B B' (* @uCoMod (Reflection0 (Limit (Reflection0 B) (Reflection0 B'))) %sol *)
            | B1 B1' B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | B1 B2 M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *)
            | B1 B1' B2 g'Sol (* 'Refl1 g'Sol %sol *)
            | A1 A1' A2 f'Sol (* f'Sol o>Mod 'CoUnit %sol *)
            | A1 A2 _L L' f'_1Sol f'_2Sol (* << f'_1Sol ,CoMod f'_2Sol >> %sol *)
            | A1 A1' A2 f'Sol (* 'RevCoUnit o>Mod f'Sol %sol *)
            | A1 A2 _L L' f'Sol  (* f'Sol o>Mod 'RevLimit1Unit %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod uCoMod) *)
        * exists ( (<< f__1Sol ,Mod f__2Sol >>)%sol ) .
          clear -g_Sol_prop g'Sol_prop. tac_reduce.

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Unit o>CoMod g'Sol)) *)
        * { case : (solveCoMod len _ _ ((Reflection1 (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>)) o>CoMod Sol.toCoMod g'Sol)) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod (<< g'_1Sol ,CoMod g'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Sol.toCoMod g'_1Sol))) =>
            [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Sol.toCoMod g'_2Sol))) =>
              [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              +  exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >>)%sol.
                 clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                 move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                 move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                 simpl in *; abstract (
                                 intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                            try eapply (Red.CoMod_Trans (uTrans := (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                            eauto )).
          }

        (** HERE BEGIN **)
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 g'Sol)) *)
        * { clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
            move: (Sol.Destruct_domLimitReflection.CoMod00_domLimitReflectionP g'Sol) => g'Sol_domLimitReflectionP.
            destruct g'Sol_domLimitReflectionP as
                [ B B' (* @uCoMod (Limit (Reflection0 B) (Reflection0 B')) %sol *)
                | B1 B1' B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
                | B1 B2 B1' b1'Sol (* ~_1 @ B2 o>CoMod b1'Sol *)
                | B1 B2 B2' b2'Sol (* ~_2 @ B1 o>CoMod b2'Sol *)
                | B1 B2 _M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *) ].

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 uCoMod)) *)
            - exists ( (<< f__1Sol ,Mod f__2Sol >>)%sol ) .
              clear -g_Sol_prop g'Sol_prop. tac_reduce.

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 ('Unit o>CoMod g'Sol))) *)
            - { case : (solveCoMod len _ _ ( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod ('RevCoUnit o>Mod (Reflection1 (Sol.toCoMod g'Sol))) )) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists ( g_Sol_o_g'Sol)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 (~_1 o>CoMod b1'Sol))) *)
            - { case : (solveCoMod len _ _ ( (Sol.toCoMod f__1Sol o>Mod Sol.toCoMod b1'Sol) )) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists ('RevCoUnit o>Mod ('Refl1 g_Sol_o_g'Sol))%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 (~_2 o>CoMod b2'Sol))) *)
            - { case : (solveCoMod len _ _ ( (Sol.toCoMod f__2Sol o>Mod Sol.toCoMod b2'Sol) )) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists ('RevCoUnit o>Mod ('Refl1 g_Sol_o_g'Sol))%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('Refl1 (<< g'_1Sol ,CoMod g'_2Sol >>))) *)
            - { case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Reflection1 (Sol.toCoMod g'_1Sol)))) =>
                [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
                - move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                  Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Reflection1 (Sol.toCoMod g'_2Sol)))) =>
                  [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
                  + move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                    move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                    move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                    move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                    Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                  +  exists (<< g_Sol_o_g'_1Sol ,Mod g_Sol_o_g'_2Sol >> o>Mod 'RevLimit1Unit)%sol.
                     clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                     move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                     simpl in *; abstract (
                                     intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                                try eapply (Red.CoMod_Trans (uTrans := (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod  ('Refl1 << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >>) ));
                                                eauto )).
              }
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod (f'Sol o>Mod 'CoUnit)) *)
        * { case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod (<< f'_1Sol ,Mod f'_2Sol >>)) *)
        * { case : (solveCoMod len _ _ ( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Sol.toCoMod f'_1Sol)) =>
            [ | g_Sol_o_f'_1Sol g_Sol_o_f'_1Sol_prop ].
            - move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
              move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
              Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod Sol.toCoMod f'_2Sol))) =>
              [ | g_Sol_o_f'_2Sol g_Sol_o_f'_2Sol_prop ].
              + move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              + exists (<< g_Sol_o_f'_1Sol ,Mod g_Sol_o_f'_2Sol >>)%sol.
                clear -g_Sol_prop g'Sol_prop g_Sol_o_f'_1Sol_prop g_Sol_o_f'_2Sol_prop.
                move: (@Sol.isSolbN_isSolN _ _ f__1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f__2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_2Sol _ Logic.eq_refl).
                simpl in *; abstract (
                                intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                           try eapply (Red.CoMod_Trans (uTrans := (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>) o>CoMod  << Sol.toCoMod f'_1Sol ,Mod Sol.toCoMod f'_2Sol >> ));
                                           eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod ('RevCoUnit o>Mod f'Sol)) *)
        * { case : (solveCoMod len _ _ (( ('Refl1 (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>)) o>CoMod Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
        
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ('Refl1 g_Sol o>CoMod g'Sol) , is  ((<< f__1Sol ,Mod f__2Sol >>) o>CoMod (f'Sol o>Mod 'RevLimit1Unit)) *)
        * { case : (solveCoMod len _ _ (( (<< Sol.toCoMod f__1Sol ,Mod Sol.toCoMod f__2Sol >>)) o>CoMod Sol.toCoMod f'Sol)) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'RevLimit1Unit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
          
      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domReflection.CoMod00_domReflectionP g'Sol) => g'Sol_domReflectionP.
        destruct g'Sol_domReflectionP as
            [ B  (* @uCoMod (Reflection B) %sol *)
            | B1 B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | B1 B2 M g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *)
            | B1 B2 g'Sol (* 'Refl1 g'Sol %sol *)
            | _A1 A2 f'Sol (* f'Sol o>Mod 'CoUnit %sol *)
            | _A1 A2 L f'_1Sol f'_2Sol (* << f'_1Sol ,Mod f'_2Sol >> %sol *)
            | _A1 A2 f'Sol (* 'RevCoUnit o>Mod f'Sol %sol *)
            | _A1 A2 L f'Sol  (* f'Sol o>Mod 'RevLimit1Unit %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod (@uCoMod B)) *)
        * exists ( ('RevCoUnit o>Mod f_Sol)%sol ) .
          clear -g_Sol_prop g'Sol_prop. tac_reduce.
          
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod ('Unit o>CoMod g'Sol)) *)
        * { case : (solveCoMod len _ _ ( ('Refl1 ('RevCoUnit o>Mod (Sol.toCoMod f_Sol))) o>CoMod Sol.toCoMod g'Sol) ) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod (<< g'_1Sol ,CoMod g'_2Sol >>)) *)
        *  { case : (solveCoMod len _ _ (( (Sol.toCoMod ('RevCoUnit o>Mod f_Sol)%sol) o>CoMod Sol.toCoMod g'_1Sol))) =>
             [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
             - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
             - case : (solveCoMod len _ _ (( (Sol.toCoMod ('RevCoUnit o>Mod f_Sol)%sol) o>CoMod Sol.toCoMod g'_2Sol))) =>
               [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
               + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
               +  exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >>)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                  move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                  simpl in *; abstract (
                                  intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                             try eapply (Red.CoMod_Trans (uTrans := ('RevCoUnit o>Mod Sol.toCoMod f_Sol) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                             eauto )).
           }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod 'Refl1 g'Sol) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol o>CoMod ('Refl1 (Sol.toCoMod g'Sol))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }


        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod (f'Sol o>Mod 'CoUnit)) *)
        (* both RevCoUnit_morphismPost CoUnit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ ( (Sol.toCoMod f_Sol) o>CoMod ((Sol.toCoMod f'Sol) o>Mod 'CoUnit))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod (<< f'_1Sol ,Mod f'_2Sol >>)) *)
        *  { case : (solveCoMod len _ _ (( (Sol.toCoMod ('RevCoUnit o>Mod f_Sol)%sol) o>CoMod Sol.toCoMod f'_1Sol))) =>
             [ | g_Sol_o_f'_1Sol g_Sol_o_f'_1Sol_prop ].
             - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
             - case : (solveCoMod len _ _ (( (Sol.toCoMod ('RevCoUnit o>Mod f_Sol)%sol) o>CoMod Sol.toCoMod f'_2Sol))) =>
               [ | g_Sol_o_f'_2Sol g_Sol_o_f'_2Sol_prop ].
               + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
               +  exists (<< g_Sol_o_f'_1Sol ,Mod g_Sol_o_f'_2Sol >>)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_f'_1Sol_prop g_Sol_o_f'_2Sol_prop.
                  move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_2Sol _ Logic.eq_refl).
                  simpl in *; abstract (
                                  intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                             try eapply (Red.CoMod_Trans (uTrans := ('RevCoUnit o>Mod Sol.toCoMod f_Sol) o>CoMod  << Sol.toCoMod f'_1Sol ,Mod Sol.toCoMod f'_2Sol >> ));
                                             eauto )).
           }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod ('RevCoUnit o>Mod f'Sol)) *)
        (* both RevCoUnit_morphismPost RevCoUnit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol) o>CoMod (('RevCoUnit o>Mod (Sol.toCoMod f'Sol))))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is (('RevCoUnit o>Mod f_Sol) o>CoMod g'Sol) , is  (('RevCoUnit o>Mod f_Sol) o>CoMod (f'Sol o>Mod 'RevLimit1Unit)) *)
        (* both RevCoUnit_morphismPost RevLimit1Unit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol) o>CoMod (((Sol.toCoMod f'Sol) o>Mod 'RevLimit1Unit)))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }
          
      (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol)  *)
      + clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
        move: (Sol.Destruct_domReflectionLimit.CoMod00_domReflectionLimitP g'Sol) => g'Sol_domReflectionLimitP.
        destruct g'Sol_domReflectionLimitP as
            [ B B' (* @uCoMod (Reflection0 (Limit B B')) %sol *)
            | B1 B1' B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
            | B1 B2 M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *)
            | B1 B1' B2 g'Sol (* 'Refl1 g'Sol %sol *)
            | A1 A1' A2 f'Sol (* f'Sol o>Mod 'CoUnit %sol *)
            | A1 A2 _L L' f'_1Sol f'_2Sol (* << f'_1Sol ,Mod f'_2Sol >> %sol *)
            | A1 A1' A2 f'Sol (* 'RevCoUnit o>Mod f'Sol %sol *)
            | A1 A2 _L L' f'Sol  (* f'Sol o>Mod 'RevLimit1Unit %sol *) ].

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit ) o>CoMod (@uCoMod (Reflection0 (Limit B B')))) *)
        * exists ((f_Sol o>Mod 'RevLimit1Unit)%sol).
          clear -g_Sol_prop g'Sol_prop. tac_reduce.

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Unit o>CoMod g'Sol)) *)
        * { case : (solveCoMod len _ _ ( ('Refl1 (Sol.toCoMod f_Sol o>Mod 'RevLimit1Unit)) o>CoMod (Sol.toCoMod g'Sol) )) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('Unit o>CoMod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod (<< g'_1Sol ,CoMod g'_2Sol >>) *)
        * { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol o>Mod 'RevLimit1Unit) o>CoMod (Sol.toCoMod g'_1Sol))) =>
            [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol o>Mod 'RevLimit1Unit) o>CoMod (Sol.toCoMod g'_2Sol))) =>
              [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
              + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
              + exists (<< g_Sol_o_g'_1Sol ,CoMod g_Sol_o_g'_2Sol >> )%sol.
                clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                simpl in *; abstract (
                                intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                           try eapply (Red.CoMod_Trans (uTrans := (Sol.toCoMod f_Sol o>Mod 'RevLimit1Unit) o>CoMod  << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >> ));
                                           eauto )).
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 g'Sol)) *)
        * { clear - solveCoMod H_gradeTotal g_Sol_prop g'Sol_prop.
            move: (Sol.Destruct_domLimit.CoMod00_domLimitP g'Sol) => g'Sol_domLimitP.
            destruct g'Sol_domLimitP as
                [ B B' (* @uCoMod (Limit B B') %sol *)
                | B1 B1' B2 g'Sol (* 'Unit o>CoMod g'Sol %sol *)
                | B1 B2 B1' b1'Sol (* ~_1 @ B2 o>CoMod b1'Sol *)
                | B1 B2 B2' b2'Sol (* ~_2 @ B1 o>CoMod b2'Sol *)
                | B1 B2 M M' g'_1Sol g'_2Sol (* << g'_1Sol ,CoMod g'_2Sol >> %sol *) ].

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 (uCoMod))) *)
            (* memo Reflection1_unit_PolyMod is held here and also somewhere above *)
            + exists ((f_Sol o>Mod 'RevLimit1Unit)%sol).
              clear -g_Sol_prop g'Sol_prop. tac_reduce.

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 ('Unit o>CoMod g'Sol)) *)
            (* memo Unit_RevCoUnit_PolyCoMod is held here and also somewhere above *)
            + { case : (solveCoMod len _ _ (((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod ('RevCoUnit o>Mod ('Refl1 (Sol.toCoMod g'Sol))))) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists (g_Sol_o_g'Sol)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 (~_1 @ B2 o>CoMod b1'Sol))) *)
            + { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol) o>Mod (~_1 o>Mod ('Refl1 (Sol.toCoMod b1'Sol))))) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists (g_Sol_o_g'Sol)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }

            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 (~_2 @ B1 o>CoMod b2'Sol))) *)
            + { case : (solveCoMod len _ _ ((Sol.toCoMod f_Sol) o>Mod (~_2 o>Mod ('Refl1 (Sol.toCoMod b2'Sol))))) =>
                [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
                - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - exists (g_Sol_o_g'Sol)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
              }
              
            (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('Refl1 << g'_1Sol ,CoMod g'_2Sol >>)) *)
            + { case : (solveCoMod len _ _ (( ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod Reflection1 (Sol.toCoMod g'_1Sol)))) =>
                [ | g_Sol_o_g'_1Sol g_Sol_o_g'_1Sol_prop ].
                - move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                  Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                - case : (solveCoMod len _ _ (( ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod Reflection1 (Sol.toCoMod g'_2Sol)))) =>
                  [ | g_Sol_o_g'_2Sol g_Sol_o_g'_2Sol_prop ].
                  + move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                    move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                    move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                    Time tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
                  +  exists (<< g_Sol_o_g'_1Sol ,Mod g_Sol_o_g'_2Sol >> o>Mod 'RevLimit1Unit)%sol.
                     clear -g_Sol_prop g'Sol_prop g_Sol_o_g'_1Sol_prop g_Sol_o_g'_2Sol_prop.
                     move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g'_1Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g'_2Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_1Sol _ Logic.eq_refl).
                     move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_g'_2Sol _ Logic.eq_refl).
                     simpl in *; abstract (
                                     intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                                try eapply (Red.CoMod_Trans (uTrans := ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod  ('Refl1 << Sol.toCoMod g'_1Sol ,CoMod Sol.toCoMod g'_2Sol >>) ));
                                                eauto )).
              }
          }
              
        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod (f'Sol o>Mod 'CoUnit)) *)
        (* both RevCoUnit_morphismPost CoUnit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ ( ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod (Sol.toCoMod f'Sol) )) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'CoUnit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod (<< f'_1Sol ,Mod f'_2Sol >>)) *)
        *  { case : (solveCoMod len _ _ (( (Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod Sol.toCoMod f'_1Sol)) =>
             [ | g_Sol_o_f'_1Sol g_Sol_o_f'_1Sol_prop ].
             - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
             - case : (solveCoMod len _ _ (( (Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod Sol.toCoMod f'_2Sol)) =>
               [ | g_Sol_o_f'_2Sol g_Sol_o_f'_2Sol_prop ].
               + tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
               +  exists (<< g_Sol_o_f'_1Sol ,Mod g_Sol_o_f'_2Sol >>)%sol.
                  clear -g_Sol_prop g'Sol_prop g_Sol_o_f'_1Sol_prop g_Sol_o_f'_2Sol_prop.
                  move: (@Sol.isSolbN_isSolN _ _ f_Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ f'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ f'_2Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_1Sol _ Logic.eq_refl).
                  move: (@Sol.isSolbN_isSolN _ _ g_Sol_o_f'_2Sol _ Logic.eq_refl).
                  simpl in *; abstract (
                                  intuition (eauto; try subst; simpl in *; rewriterCoMod; try congruence;
                                             try eapply (Red.CoMod_Trans (uTrans := ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod  << Sol.toCoMod f'_1Sol ,Mod Sol.toCoMod f'_2Sol >> ));
                                             eauto )).
           }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod ('RevCoUnit o>Mod f'Sol)) *)
        (* both RevCoUnit_morphismPost RevCoUnit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ (('Refl1 ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit)) o>CoMod (Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists ('RevCoUnit o>Mod g_Sol_o_g'Sol)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

        (* g is (g_ o>CoMod g') , to (g_Sol o>CoMod g'Sol)  , is ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod g'Sol) , is  ((f_Sol o>Mod 'RevLimit1Unit) o>CoMod (f'Sol o>Mod 'RevLimit1Unit)) *)
        (* both RevCoUnit_morphismPost RevLimit1Unit_morphismPre possible, RevCoUnit_morphismPost chosen *)
        * { case : (solveCoMod len _ _ ( ((Sol.toCoMod f_Sol) o>Mod 'RevLimit1Unit) o>CoMod (Sol.toCoMod f'Sol))) =>
            [ | g_Sol_o_g'Sol g_Sol_o_g'Sol_prop ].
            - tac_degrade H_gradeTotal g_Sol_prop g'Sol_prop.
            - exists (g_Sol_o_g'Sol o>Mod 'RevLimit1Unit)%sol.
              clear -g_Sol_prop g'Sol_prop g_Sol_o_g'Sol_prop. tac_reduce.
          }

  Defined.

End Section1.

End LOCALIZATION.

(**#+END_SRC

Voila. **)
