
(* monad: reecriture dans le sens associatif a droite *
monad': reecriture dans l'autre sens
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

    Definition ofCourse {A : Type} (x : A) := True.
Section MonadicEq.

Context (ob : Type).
Context (mor : ob -> ob -> Type).

Context (id : forall a, mor a a).
Arguments id {a}.



  (* these entries allow interpret S f or S x differently
   *)
  (* Declare Custom Entry obj. *)
(* entries allow to interpret 'x y' differently, and right associatively
 *)
  Declare Custom Entry mor.
  Declare Custom Entry obj.
  Notation "< x >" := (x) (x custom mor).
  Notation "x" := x (in custom mor at level 0, x global).
  Notation "x" := x (in custom obj at level 0, x global).
  Notation "| x |" := (x) (x custom obj).
  Notation "| x |" := (@id x) (x custom obj, in custom mor).
  Notation "{ x }" := (x) (x constr, in custom mor).
  Notation "{ x }" := (x) (x constr, in custom obj).
  Notation "( x )" := (x) (in custom mor).
  Notation "( x )" := (x) (in custom obj).

  Notation "{ x = y }" := (x = y) (x custom mor, y custom mor, at level 70).

Context (comp : forall a b c, mor a b -> mor b c -> mor a c).

Infix "·" := comp (in custom mor at level 32, left associativity).

Context (assoc : forall `(a : mor x3 x4)
                        `(b : mor x2 x3)
                        `(c : mor x1 x2),
                        { c · (b · a) = (c · b) · a }).

Hint Rewrite assoc : monad.

      Ltac etrans := etransitivity.
    Lemma assoc' :  forall `(a : mor x3 x4)
                        `(b : mor x2 x3)
                        `(c : mor x1 x2),
                        {c · b · a = c · (b · a)}.
      intros.
      repeat rewrite assoc.
      reflexivity.
    Qed.
    Lemma cancel_precomposition `(f : mor x y) `(g : mor y z) (g' : mor y z) : g = g' -> { f · g = f · g' }.
      congruence.
      Qed.
    Lemma cancel_postcomposition `(f : mor z x) `(g : mor y z) (g' : mor y z) : g = g' -> { g · f = g' · f }.
      congruence.
      Qed.
    Definition idpath := @eq_refl.


Context (idl: forall `(b : mor x y), { id · b = b }).
Hint Rewrite idl : monad.

Context (idr: forall `(b : mor x y), { b · id = b }).
Hint Rewrite idr : monad.

Context (sumo : ob -> ob -> ob).
Infix "+" := sumo (in custom obj at level 50, left associativity).

Context (copairm : forall a b c, mor a c -> mor b c -> mor |a + b| c).
(* Notation "[ x , y , .. , z ]" := (copairm .. (copairm x y) .. z) . *)
Notation "[ x , y , .. , z ]" := (copairm .. (copairm x y) .. z) (in custom mor).

Context (in_1 : forall x y, mor x |x + y|).
Arguments in_1 {x} {y}.

Context (in_2 : forall x y, mor y |x + y|).
Arguments in_2 {x} {y}.

Definition summ {a b a' b'} (s1 : mor a b) (s2 : mor a' b') : mor |a + a'| |b + b'|
  := < [ s1 · in_1 , s2 · in_2 ] >.
(* Infix "+" := summ. *)
Infix "+" := summ (in custom mor at level 50, left associativity).

Hint Unfold summ : monad.

Definition O Y Z := |Z + Y|.
Definition Of `(f : mor A B) `(g : mor A' B') : mor (O A A') (O B B') := < g + f >.
  Notation "'O_{' a } b" := (O a b)  (in custom obj at level 1, right associativity).
  Notation "'O_{' f } g" := (Of f g) (in custom mor at level 1, right associativity).

Hint Unfold O Of : monad.

Ltac solve_ctxt lem :=
      intros; rewrite !assoc'; apply cancel_precomposition; rewrite ? assoc; apply lem.

Context (mor_copairm : forall
            `(m : mor c b)
           `(t1 : mor x1 c)
           `(t2 : mor x2 c),
              {[t1 , t2] · m = [t1 · m , t2 · m]}).

Lemma mor_copairm_ctxt : forall
            `(m : mor c b)
           `(t1 : mor x1 c)
           `(t2 : mor x2 c)
           `(x : mor d _) ,
             { x · [t1 , t2] · m = x · [t1 · m ,  t2 · m] }.
Proof.
  solve_ctxt mor_copairm.
  Qed.

Hint Rewrite mor_copairm @mor_copairm_ctxt : monad.

Context (copairm_in_1 : forall `(s1 : mor x1 c) `(s2 : mor x2 c), { in_1 · [s1 , s2]  = s1 }).
Context (copairm_in_2 : forall `(s1 : mor x1 c) `(s2 : mor x2 c), { in_2 · [s1 , s2]  = s2 }).

Lemma copairm_in_1_ctxt : forall
           `(x : mor a x1)
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             { x · in_1 · [s1 , s2]  = x · s1 }.
Proof.
  solve_ctxt copairm_in_1.
Qed.
Lemma copairm_in_2_ctxt : forall
           `(x : mor a x2)
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             { x · in_2 · [s1 , s2]  = x · s2 }.
Proof.
  solve_ctxt copairm_in_2.
Qed.
Hint Rewrite copairm_in_1 @copairm_in_1_ctxt : monad.
Hint Rewrite copairm_in_2 @copairm_in_2_ctxt : monad.





  Record monad :=
    {
    M : ob -> ob ;
    bind : forall a b, mor a (M b) -> mor (M a) (M b) ;
    η : forall x, mor x (M x) ;
    (* mon_laws : is_monad bind η *)
    bind_eta : forall X, bind (@η X) = id ;
    bind_bind : forall `(s : mor b (M c))
                  `(s' : mor c (M d)),
        { {bind s} · {bind s'}  = {bind < s · {bind s'} >} } ;
    η_bind : forall `(s : mor b (M c)) , { {η b} · {bind s} = s}
    }.

  (* Arguments M _ x%object_scope. *)
Arguments η {m} {x}.

Notation "[ x ]" := (bind x) (in custom mor).
Notation "P x " := (M P x) (in custom obj at level 1, right associativity).
Notation "P x " := ( < [ x · {η (m := P)} ] >  ) (in custom mor at level 1, right associativity).


Lemma bind_bind_ctxt {S : monad}: forall `(x : mor a |S b|)
                       `(s : mor b |S c|)
                       `(s' : mor c |S d|),
                       { x · [ s ] · [ s' ]  = x · [ s · [ s' ]  ] }.
Proof.
  solve_ctxt bind_bind.
Qed.

Lemma η_bind_ctxt {S : monad} : forall `(x : mor a b)
                    `(s : mor b |S c|) 
          , {x · η · [ s ] = x · s}.
Proof.
  solve_ctxt η_bind.
Qed.

Hint Rewrite @bind_eta : monad.
Hint Rewrite @bind_bind @bind_bind_ctxt : monad.
Hint Rewrite @η_bind @η_bind_ctxt : monad.


Definition μ {P : monad}{X} := < [ | P X | ] >.
Hint Unfold μ : monad.


  Definition up {R : monad}{x y : ob} : mor | x + R y | | R (x + y) |
                    :=  < [ in_1 · η ,  R in_2 ] > .
  Hint Unfold up : monad.
  Notation "↑" := up (in custom mor).


  Class algebre (P : monad) (X : ob) :=
    {
    bindA : forall a , mor a X -> mor |P a| X ;
    (* mon_laws : is_monad bind η *)
    bind_bindA : forall `(s : mor b |P c|)
                  `(s' : mor c X),
        { [ s ] · {bindA s'}  = {bindA  < s · {bindA s'} >} } ;
    η_bindA : forall `(s : mor b X) , { η · {bindA s} = s}
    }.

Notation "⦇ x ⦈" := (bindA x) (in custom mor).

Lemma bind_bindA_ctxt `{_ : algebre T X} : forall `(x : mor a |T b|)
                       `(s : mor b |T c|)
                       `(s' : mor c X),
                       { x · [ s ] · ⦇ s' ⦈  = x · ⦇ s · ⦇ s' ⦈  ⦈ }.
Proof.
  solve_ctxt @bind_bindA.
Qed.

Lemma η_bindA_ctxt  `{_ : algebre T X} : forall `(x : mor a b)
                    `(s : mor b X)
          , {x · η · ⦇ s ⦈ = x · s}.
Proof.
  solve_ctxt @η_bindA.
Qed.

Hint Rewrite @bind_bindA @bind_bindA_ctxt : monad.
Hint Rewrite @η_bindA @η_bindA_ctxt : monad.

(* *************

This section consists of lemmas and tactics and notations to turn
a statement into something that the graph editor can parse.

Usage:
norm_graph.
Open Scope myscope.

********* *)
  Declare Scope myscope.
Definition comp' : forall a b c, mor a b -> mor b c -> mor a c := @comp.
  Notation " f - g > z" := (@comp' _ _ z f g )  (z custom obj, in custom mor at level 40, left associativity).
    Lemma add_id_left {x y : ob}(f g : mor x  y) :   comp' id f  = comp' id g -> f = g.
      autorewrite with monad.
      easy.
    Qed.

    Lemma comp'_comp `(a : mor x3 x4)
                        `(b : mor x2 x3)
                        `(c : mor x1 x2):
                         comp' c  <b · a> = comp' (comp' c b) a .
    autorewrite with monad.
    reflexivity.
    Qed.
    Hint Rewrite @comp'_comp : fold_monad.


    Definition mon_functor (M : monad) `(f : mor x y) : mor |M x| |M y| := < M f >.
  Notation "x y" := (mon_functor x y)  (y custom mor, in custom mor at level 1, right associativity, only printing) : myscope.

Lemma monad_comp (M : monad) `(f : mor A B) `(g : mor B C) :
  mon_functor M (comp f g) = comp (mon_functor M f) (mon_functor M g).
  unfold mon_functor.
  autorewrite with monad.
  reflexivity.
Qed.

Hint Rewrite monad_comp : fold_monad.




  Lemma bind_μ (M : monad): forall `(f : mor x | M y |) , bind f  = < { mon_functor M f} · μ >.
  intros.
  unfold mon_functor.
  autounfold with monad.
  autorewrite with monad.
  reflexivity.
  Qed.
Hint Rewrite bind_μ : fold_monad.

Definition alg `{_ : algebre P A} : mor |P A| A := < ⦇ id ⦈ >.

  Lemma bind_a `(_ : algebre P A) `(f : mor y | A |) : { ⦇ f ⦈  =  P f · alg }.
  intros.
  unfold alg.
  autorewrite with monad.
  reflexivity.
  Qed.

Hint Rewrite @bind_a : fold_monad.

(*
usage:
    norm_graph.
    Open Scope myscope.

*)
    Ltac norm_graph := apply add_id_left;  autorewrite with fold_monad.


    (* ***

End of graph utilities

    **** *)

Context (Γ : ob -> ob -> ob) 
        (Γ' : forall `(mor a b) `(mor a' b'), mor (Γ a a') (Γ b b') ).

Notation "'Γ_{' a } b" := (Γ b a)  (in custom obj at level 1, right associativity).
Notation "'Γ_{' f } g" := (Γ' g f) (in custom mor at level 1, right associativity).

Context (Γ_comp : forall
            `(f1 : mor a1 b1) `(g1 : mor a'1 b'1)
            `(f2 : mor b1 c2) `(g2 : mor b'1 c'2),
            { Γ_{ f1 } g1 · Γ_{ f2} g2  = Γ_{ f1 · f2 }  (g1 · g2) }
        ).
Lemma Γ_comp_ctxt : forall 
            `(f1 : mor a1 b1) `(g1 : mor a'1 b'1)
            `(f2 : mor b1 c2) `(g2 : mor b'1 c'2)
    `(x : mor o _),
            { x · Γ_{ f1 } g1 · Γ_{ f2} g2  = x · Γ_{ f1 · f2 }  (g1 · g2) }.
Proof.
  solve_ctxt Γ_comp.
Qed.

Hint Rewrite Γ_comp @Γ_comp_ctxt : monad.

Context (Γ_id : forall X Y, { Γ_{ | X |} | Y | = id }).

Hint Rewrite Γ_id: monad.


(* based on Proposition 6.2 de Monads as extension systems *)

Context (S T : monad).

Context (bindST : forall Y, algebre T |S T Y|).
Notation "⟦ f ⟧" := (bindA (algebre := bindST _) f) (in custom mor).

Context (dist_alg_mor : forall `(g : mor X |S T Y|) `(f : mor Y |S T Z|),
            { ⟦ g ⟧ · [ ⟦ f ⟧ ] = ⟦ g  · [ ⟦ f ⟧ ] ⟧ }).

Lemma dist_alg_mor_ctxt : forall `(g : mor X |S T Y|) `(f : mor Y |S T Z|) `(k : mor a _),
            { k · ⟦ g ⟧ · [ ⟦ f ⟧ ] = k · ⟦ g  · [ ⟦ f ⟧ ] ⟧ }.
  solve_ctxt dist_alg_mor.
Qed.

Hint Rewrite dist_alg_mor @dist_alg_mor_ctxt : monad.

Context (bindST_etaS : forall `(g : mor X |T Y|), { ⟦ g · η⟧ = [ g ] · η }).

Lemma bindST_etaS_id : forall X, { ⟦ η ⟧ = [ | T X|  ] · η }.
  etrans; revgoals.
  apply bindST_etaS.
  rewrite idl.
  reflexivity.
Qed.

Hint Rewrite bindST_etaS bindST_etaS_id : monad.

(* deuxieme paire critique *)

Ltac critic t :=
  transitivity  t;
  [rewrite ?assoc';
  try apply cancel_precomposition;
   rewrite ?assoc
   |
      try apply cancel_postcomposition
  ];
  autorewrite with monad;
  try reflexivity.


Lemma critic2 : forall `(f : mor a |S T Y|)
                     `(g : mor Y |S T Z|)
                     `(h : mor |T Z| |S b|)
          ,
          { ⟦ f ⟧· [ ⟦ g ⟧ · [ h ] ]
            =
              ⟦ f · [ ⟦ g ⟧ ] ⟧ · [h]
          }.
  intros.
  critic <⟦ f ⟧ · [ ⟦ g ⟧ ] · [ h ]>.
  Qed.
(* transitivity  (<⟦ f ⟧ · [ ⟦ g · {η (m := S)} ⟧ ]>). *)

Lemma critic2_ctxt  `(f : mor a |S T Y|)
                     `(g : mor Y |S T Z|)
                     `(h : mor |T Z| |S b|)
                     `(u : mor x _)
          :
          { u · ⟦ f ⟧· [ ⟦ g ⟧ · [ h ] ]
            =
              u · ⟦ f · [ ⟦ g ⟧ ] ⟧ · [h]
          }.
  solve_ctxt @critic2.
  Qed.

Hint Rewrite @critic2 @critic2_ctxt: monad.

Lemma critic3 `(f : mor a1 | S T a2|)
      `(g : mor a2 |T a3| ) :
  (* { ⟦ f · S [g]⟧ = ⟦ f ⟧ · S [ g ] } . *)
  { ⟦ f ⟧ · S [ g ] = ⟦ f · S [g]⟧  } .
  transitivity  < ⟦ f ⟧ · [ ⟦ g · η ⟧ ] >.
  autorewrite with monad.
  reflexivity.
  rewrite dist_alg_mor.
  autorewrite with monad.
  reflexivity.
  Qed.

Lemma critic3_ctx `(f : mor a1 | S T a2|)
      `(g : mor a2 |T a3| )
  `(u : mor x _):
  (* { ⟦ f · S [g]⟧ = ⟦ f ⟧ · S [ g ] } . *)
  { u · ⟦ f ⟧ · S [ g ] = u · ⟦ f · S [g]⟧  } .
  solve_ctxt @critic3.
  Qed.

(*
Lemma critic3_id 
      `(g : mor a2 |T a3| )
  :
  { ⟦ S [g]⟧ = ⟦ id ⟧ · S [ g ] } .
  rewrite <- critic3, idl.
  reflexivity.
  Qed.
*)


Hint Rewrite @critic3 @critic3_ctx: monad.

Definition δ {X} : mor |T S X| |S T X| :=
  < ⟦ S η ⟧ >.
Hint Unfold δ : monad.

Definition μST {X} : mor |S T S T X| |S T X| :=
   < [⟦ id ⟧] >.

Hint Unfold μST : monad.


Context (X : ob)(algX : algebre T X).

Definition 𝐚 : mor |T X| X := < ⦇ id ⦈ >.
Hint Unfold 𝐚 : monad.


  Notation "in_{13}" := (< in_1 · in_1 >).
  Notation "in_{23}" := (< in_2 · in_1 >).
  Notation "in_{33}" := (@in_2 (sumo _ _) _) .



